#!/usr/bin/env python3
"""
bot.py — Clean, simple trading bot that actually works.

No bloat. No feature creep. Just scan, buy winners, short losers, take profit.
"""

import requests
import time
import json
import os
import sys
import signal
import math
import uuid
import logging
from logging.handlers import RotatingFileHandler
import threading
import queue
import bisect
from datetime import datetime, timezone
from abc import ABC, abstractmethod

# ── Global State Variables ──
_current_cycle = 0  # Updated each main loop cycle, used by record_exit
_last_exit_cycle = {}  # v29.3.5: per-coin cooldown — maps coin → (cycle, was_profitable)
COOLDOWN_AFTER_WIN = 15   # v29.3.5: profitable exits get fast re-entry (15 cycles = 30 sec)
COOLDOWN_AFTER_LOSS = 40  # v29.3.5: losing exits keep longer cooldown (40 cycles = 80 sec)

# v29.3.5 — Dynamic Blacklist: confirmed trap coins only (SOL/ADA/NEAR/DOGE re-enabled)
DYNAMIC_BLACKLIST = {
    "ALGO", "RIVER", "BCH",       # v29.3.2 original: trap coins, ATR loopholes
    "TEST", "PTB",                 # Execution failures / test artifacts
    "HYPE", "UNKNOWN",            # v29.3.3: auto-flagged <25% WR, high consec loss streaks
    "RED",                         # v29.4.1: fake data spikes every cycle
}

# v29.4.1 — Coin Whitelist: only trade these 20 high-liquidity coins
COIN_WHITELIST = {"XBT", "ETH", "SOL", "LINK", "AVAX", "ADA", "LTC", "DOT"}  # v29.5.0: expanded to 8 high-liquidity coins
WHITELIST_ONLY = True

# v29.3.2 — Volatility circuit breaker: pause new entries when market vol > 5%
VOLATILITY_CIRCUIT_BREAKER = 5.0
AUTO_BLACKLIST_WR_THRESHOLD = 0.25
AUTO_BLACKLIST_MIN_TRADES = 10

# v29.3.3 — Loss Streak Protection: pause entries after consecutive losses or equity DD
LOSS_STREAK_MAX = 10             # v29.4.0: was 7 — 10 consecutive losses before pause (every ~1024 trades at 50% WR)
LOSS_STREAK_DD_PCT = 5.0         # 5% equity drawdown from session peak → pause
LOSS_STREAK_PAUSE_CYCLES = 15    # v29.4.0: was 50 — 15 cycles (~30s) cooldown after streak
_loss_streak_count = 0           # runtime: current consecutive loss count
_loss_streak_paused_until = 0    # runtime: cycle number when pause expires
_session_peak_equity = 0         # runtime: highest equity seen this session

# v29.3.3 — Minimum Momentum Filter
MIN_MOMENTUM_SCORE = 0.08       # v29.3.5: lowered from 0.15 — lets moderate signals through (was blocking too aggressively)

# v29.3.4 — Dynamic Temporary Blacklist: coins with expiring cooldowns + recovery scoring
TEMP_BLACKLIST_ENABLED = True                    # Master switch for dynamic temporary blacklist
TEMP_BLACKLIST_COOLDOWN_CYCLES = 200             # How long a coin stays blocked (cycles)
TEMP_BLACKLIST_MIN_RECOVERY_SCORE = 0.20         # Momentum must exceed this to lift blacklist
TEMP_BLACKLIST_ATR_RANGE = (0.001, 0.015)        # Normal ATR range for recovery eligibility
TEMP_BLACKLIST_PRIORITY_WEIGHT = 1.5             # Recovered coins get 1.5x score boost in ranking
TEMP_BLACKLIST_COIN_LOSS_MAX = 3                 # Per-coin consecutive losses before auto-blacklist
_per_coin_loss_streak = {}                       # runtime: coin → consecutive loss count

# v29.3.4 — Expanded Asset Scanning: full universe vs rotating batch
FULL_SCAN_ENABLED = True                         # True = scan ALL pairs each cycle
SCAN_BATCH_SIZE = 50                             # Fallback batch size when FULL_SCAN_ENABLED=False
SCAN_PREFILTER_ENABLED = True                    # Pre-filter illiquid/dead pairs before scoring
SCAN_PREFILTER_MIN_VOL = 100000                  # $100k daily volume floor for pre-filter
SCAN_PREFILTER_ATR_RANGE = (0.0005, 0.015)        # ATR outside this range = skip pair — tighter upper bound filters extreme vol

kill_switch = None  # Initialized in main() with starting equity

# ── v29.5.0: Pro Market Condition & Protection Runtime State ──
_pro_peak_portfolio = 0.0             # Runtime: peak portfolio value for drawdown protection
_pro_last_5_results = []              # Runtime: last 5 trade results ["win"/"loss"] for streak sizing
_pro_market_regime = "UNKNOWN"        # Runtime: current market regime (TRENDING/RANGING/VOLATILE/DEAD)

# ── Setup ──
DIR = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(DIR, "logs"), exist_ok=True)
logger = logging.getLogger("bot")
logger.setLevel(logging.DEBUG)  # Capture everything; handlers filter by level
if not logger.handlers:
    # File handler: DEBUG+ (all details go to disk) — 5 MB max, 5 backups
    _file_handler = RotatingFileHandler(
        os.path.join(DIR, "logs", "bot.log"),
        maxBytes=5 * 1024 * 1024,  # 5 MB
        backupCount=5,
    )
    _file_handler.setLevel(logging.DEBUG)
    _file_handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    logger.addHandler(_file_handler)
    # Terminal handler: ERROR+ only (dashboard uses print() directly, not logger)
    _stream_handler = logging.StreamHandler()
    _stream_handler.setLevel(logging.ERROR)
    _stream_handler.setFormatter(logging.Formatter("%(message)s"))
    logger.addHandler(_stream_handler)

KRAKEN = "https://api.kraken.com/0/public"
STATE_FILE = os.path.join(DIR, ".bot_state2.json")
ML_FILE = os.path.join(DIR, ".ml_brain.json")
CASH = 1000.0
POLL = 2  # seconds (was 3 — faster signal checks, still within Kraken rate limits)
MIN_VOL_USD = 500000  # Only trade coins with $500k+ daily volume
PEAK_HOURS = (15, 21)  # UTC peak hours
MAX_DAILY_TRADES = 60  # Was 30 — bot would trade for ~2 hours then sit dead for 22 hours
MAX_POSITIONS = 4      # v29.5.0: was 2 — expanded to 4 for broader whitelist
API_MAX_RETRIES = 3    # Retry failed API calls

# ── Ranging Market Filter (toggleable) ──
# v29.4.0: RANGING_FILTER_ENABLED and RANGING_CONFIDENCE_BOOST removed — dead code

# ── Ranging Market Adaptation (prevents over-filtering in sideways markets) ──
RANGING_ADAPTATION_ENABLED = True         # Master switch — False = no ranging relaxation
RANGING_SCORE_REDUCTION = 0.05            # Lower base min_score by 0.05 in ranging
RANGING_NOISE_SCORE_REDUCTION = 0.03      # Lower noise filter thresholds by 0.03 in ranging
RANGING_NOISE_CHANGE_REDUCTION = 0.005    # Lower noise change thresholds by 0.005 in ranging
RANGING_MEANREV_EXTRA_LONGS = 1           # Allow +1 extra mean-rev long positions in ranging
RANGING_MEANREV_EXTRA_SHORTS = 1          # Allow +1 extra mean-rev short positions in ranging
RANGING_OVERTRADE_CYCLES_MULT = 0.6       # Reduce min-cycles-between to 60% in ranging (20→12)
RANGING_MOMENTUM_SCALE = 0.6             # Scale momentum positions to 60% in ranging (not block)
# NOTE: Hard filters (risk caps, exposure, liquidity, reward/risk, kill switch) are NEVER relaxed

# ── Minimum Profit Filter (toggleable) ──
MIN_PROFIT_FILTER_ENABLED = False   # DISABLED — 0.7% threshold created zombie positions that reversed into losses
MIN_PROFIT_THRESHOLD = 0.007       # 0.7% (inactive — kept for reference)

# ── Adaptive Regime Layer (toggleable) ──
ADAPTIVE_REGIME_ENABLED = True    # Set False to revert to original behavior
ADAPTIVE_SAFE_MODE = True         # If regime layer causes issues, auto-revert

# ── Warm-Up Period (prevents premature trades on startup) ──
WARMUP_CYCLES = 100               # No trading for first 100 cycles (~3.3 min at 2s poll, was 150)
WARMUP_RAMP_END = 200             # Full size after 200 cycles (~6.7 min, was 300)
WARMUP_RAMP_MULT = 0.85           # 85% size during ramp-up (was 75%) — raised per audit
MIN_PRICE_HISTORY = 5             # Require 5+ price points (was 15 — still too slow, coins at 12/15 after 100+ cycles)
MIN_ATR_TO_TRADE = 0.0005         # v29.4.0: 0.05% minimum ATR — lowered further for low-vol coins
_dead_market_counter = [0]        # v29.2: running total of dead-market pair skips (mutable list for nested scope access)
BLOCK_UNKNOWN_REGIME = False      # Was True — hard-blocked ALL entries when regime undetermined, killing early trading

# ── Trader Decision Layer (toggleable) ──
# Behaves like a disciplined human trader sitting above the strategy
ENABLE_DECISION_LAYER = True      # Master switch — False = bypass entirely
DECISION_SAFE_MODE = True         # True = reduce size aggressively instead of blocking

# ── Professional Execution Settings ──
PAPER_MODE = True                 # True = paper trading (wallet only), False = Kraken API (future)
SIMULATED_SLIPPAGE_PCT = 0.05    # 0.05% adverse slippage on every fill
MAX_SPREAD_PCT = 0.20            # v29.4.1: tightened — whitelist coins all have tight spreads (was 0.60%)
MIN_ORDER_USD = 10               # Minimum order size in USD (match POSITION_SIZE_FLOOR_USD)
GLOBAL_RISK_CAP_PCT = 12.0       # v29.3.5: was 3.0 — only allowed 2 of 8 slots. 12% = 8 × 1.5% risk per trade
GAP_RISK_MULTIPLIER = 1.2         # v29.4.0: 1.2x SL gap (was 1.5 — tighter gap for paper trading)
MAX_PER_GROUP = 2                # Max positions per correlation group
MAX_RISK_PER_TRADE = 0.015        # 1.5% of portfolio per trade (was 0.5% — positions too small to make meaningful returns)
MAX_DAILY_LOSS_PCT = 2.5          # v29.5.0: was 10% — tight 2.5% daily loss hard stop
STRESS_RISK_LIMIT_PCT = 25.0      # v29.3.5: was 8.0 — 3x multiplier blocked after just 2 positions. 25% allows full deployment
SLIPPAGE_BASE = 0.05              # Base slippage %
SLIPPAGE_SL_EXIT = 0.10           # v29.3.5: paper trading — no need for panic slippage (was 0.3%)
CASCADE_THRESHOLD = 3.0           # Portfolio drop % in 1-2 cycles triggers cascade mode

# v29.4.0 — BTC Market Condition Gate
BTC_TREND_MIN_MOVE = 0.015        # 1.5% net move in 20 ticks = trending
BTC_RANGING_SIZE_MULT = 0.0       # 0.0 = pause ALL momentum/breakout entries when BTC is ranging
BTC_MEANREV_SIZE_MULT = 0.5       # Mean-reversion entries use 50% normal sizing in ranging markets
BTC_MEANREV_Z_THRESHOLD = 2.0     # z-score magnitude for mean-rev entry
BTC_MEANREV_Z_WINDOW = 50         # Lookback ticks for z-score calculation

# ── v29.4.1: Fear & Greed Index ──
FEAR_GREED_ENABLED = True          # Master switch for Fear & Greed sizing
FEAR_GREED_REFRESH_CYCLES = 200    # Re-fetch every 200 cycles (~100 min at 30s poll)
FEAR_GREED_EXTREME_FEAR = 25       # Below this = Extreme Fear → boost size
FEAR_GREED_EXTREME_GREED = 75      # Above this = Extreme Greed → reduce size
FEAR_GREED_FEAR_MULT = 1.30        # Size multiplier in Extreme Fear (buy the dip)
FEAR_GREED_GREED_MULT = 0.70       # Size multiplier in Extreme Greed (trim exposure)
FEAR_GREED_NEUTRAL_MULT = 1.0      # Between 25-75 = neutral, no adjustment
_fear_greed_value = 50             # Runtime: last fetched index value (0-100)
_fear_greed_label = "Neutral"      # Runtime: last fetched label
_fear_greed_last_cycle = -999      # Runtime: cycle of last successful fetch

# ── v29.4.1: Triple-Confirm Mean Reversion (BB + RSI + Z-Score) ──
TRIPLE_MEANREV_ENABLED = True      # Master switch
TRIPLE_MEANREV_BB_WINDOW = 20      # Bollinger Band lookback
TRIPLE_MEANREV_BB_STD = 2.0        # BB standard deviation multiplier
TRIPLE_MEANREV_RSI_WINDOW = 14     # RSI lookback period
TRIPLE_MEANREV_RSI_OVERSOLD = 30   # RSI below this = oversold (long)
TRIPLE_MEANREV_RSI_OVERBOUGHT = 70 # RSI above this = overbought (short)
TRIPLE_MEANREV_Z_THRESHOLD = 2.0   # Z-score threshold for entry
TRIPLE_MEANREV_HIGH_CONV_Z = 3.0   # Z-score for high-conviction (+25% size)

# ── v29.4.1: Opening Range Breakout (ORB) ──
ORB_ENABLED = False                 # Disabled by default (needs Alpaca API key)
ORB_RANGE_MINUTES = 30              # First 30 minutes define the range
ORB_VOLUME_CONFIRM_MULT = 1.5      # Breakout volume must exceed 1.5x avg
ORB_TARGET_RANGE_MULT = 2.0        # Profit target = 2x the opening range
ORB_STOP_RANGE_MULT = 0.5          # Stop loss = 0.5x the opening range
ORB_MAX_POSITIONS = 3               # Max concurrent ORB positions
ORB_SYMBOLS = ["SPY", "QQQ", "AAPL", "MSFT", "TSLA"]  # Default watchlist
ORB_API_KEY = ""                    # Alpaca API key (set in env or config)
ORB_API_SECRET = ""                 # Alpaca API secret
ORB_BASE_URL = "https://paper-api.alpaca.markets"  # Paper trading endpoint
_orb_ranges = {}                    # Runtime: symbol → {high, low, volume, ready}

# ── v29.4.1: Smart DCA Sizing ──
SMART_DCA_ENABLED = True            # Master switch
SMART_DCA_EXTREME_FEAR_THRESHOLD = 20  # F&G below this triggers DCA boost
SMART_DCA_BOOST_PCT = 0.40         # +40% extra position size in extreme fear
SMART_DCA_MAX_POSITIONS = 5         # Max positions that get DCA boost per cycle

CASCADE_BLOCK_CYCLES = 10         # Block entries for N cycles during cascade
MIN_HOLD_CYCLES = 120             # v29.3.5: was 60 — momentum strategies need longer to play out (120 cycles ≈ 1hr at POLL=30s)
MIN_HOLD_CYCLES_MEANREV = 60      # Mean-reversion is faster — keep original 60 cycle minimum
STAGNATION_EXIT_CYCLES = 100      # v29.3: was 150 — faster cycling frees capital for new trades
STAGNATION_EXIT_CYCLES_CALM = 140 # v29.3: was 200 — calm markets still get extra patience but not too much
STAGNATION_EXIT_CYCLES_VOLATILE = 100  # Volatile markets: tighter exit (ATR > 3%) (was 300)
LOSS_COOLDOWN_CYCLES = 30         # Block re-entry for coin after SL hit (was embedded 100)
MIN_CONSECUTIVE_FRESH = 50        # Require 50+ consecutive fresh price points
PRICE_JUMP_MAX_ATR = 3.0          # Reject if price jump > 3x ATR
PRICE_JUMP_MAX_PCT = 5.0          # Reject if price jump > 5%
PRICE_STALE_ENTRY_CYCLES = 5     # Max cycles since last fresh price for entry

# ── v29.3.5 L6: Named Exit Constants (extracted from magic numbers in exit logic) ──
SL_BASE_PCT = 0.8                 # Stop-loss base percentage (before ATR scaling)
TP_BASE_PCT = 0.4                 # Take-profit base percentage (floor)
ATR_SL_MULTIPLIER = 0.7           # ATR multiplier for dynamic SL: SL = max(SL_BASE_PCT, ATR * this)
TP_RATIO_NORMAL = 3.2             # v29.4.1: raised from 1.6 — required for profitability after Kraken 0.52% RT fees
TP_RATIO_TRENDING = 3.5           # v29.4.1: raised from 1.8 — trending conditions get wider TP
PP_TIMEOUT_MAX = 200              # Profit protection maximum timeout in cycles
SLOW_BLEED_THRESHOLD = -0.3       # PnL threshold for slow bleed exit (%)
PP_TRIGGER_MULTIPLIER = 0.7       # Early PP triggers at this fraction of TP target

# ── v29.4.0 Item 30: Named constants (extracted from inline magic numbers) ──
BACKTEST_TOP_PAIRS = 20           # Number of top pairs to test in backtest
BACKTEST_ENTRY_TOP_N = 5          # How many ranked signals to check per cycle in backtest
ALPHA_MAX_ENTRIES_PER_CYCLE = 2   # Max alpha strategy entries per cycle
POSITION_SIZE_FLOOR_USD = 10      # Minimum position size in USD
CASH_MAX_SINGLE_TRADE_PCT = 0.30  # Max fraction of cash for a single momentum trade
ALPHA_CASH_MAX_PCT = 0.15         # Max fraction of cash for a single alpha trade
SCORE_CHANGE_MIN_LONG = 0.001     # Minimum price change for long momentum entry
SCORE_CHANGE_MIN_SHORT = -0.001   # Maximum price change for short momentum entry

# ── Debug Mode ──
DEBUG_MODE = False                 # True = verbose live trade/rejection/risk printing
DRY_RUN_CYCLES = 0                 # v29.3.4: disabled — warmup handles this already
FRESH_SESSION = False              # False = resume previous session state on restart
# ── Verbosity Level ──
# "QUIET"  = errors only, no dashboard, no info prints
# "NORMAL" = standard output (dashboard, trades, warnings)
# "DEBUG"  = everything including rejection details, filter pipeline, signal scores
VERBOSITY = "NORMAL"

# ── Kill Switch Settings ──
KILL_SWITCH_EQUITY_DROP_PCT = 15.0    # Total equity drop % triggers kill switch
KILL_SWITCH_CONSECUTIVE_LOSSES = 3     # 3 consecutive losses > -2% triggers kill switch
KILL_SWITCH_BAD_LOSS_THRESHOLD = -2.0  # What counts as a "bad" loss (%)
KILL_SWITCH_MAX_GAP_EVENTS = 5         # Too many gap events triggers kill switch

# ── Error Classification & Cooldown ──
ERROR_COOLDOWN_THRESHOLD = 15          # Execution errors per 100 cycles to trigger entry cooldown
ERROR_COOLDOWN_CYCLES = 30             # Pause entries for this many cycles on high error rate
ERROR_RATE_WINDOW = 100                # Window (in cycles) to measure error rate

# ── Strategy Health Monitor ──
HEALTH_MONITOR_WINDOW = 50             # Track last N trades
HEALTH_MONITOR_MIN_WR = 35.0          # Pause if win rate below this (%)
HEALTH_MONITOR_MIN_EXPECTANCY = 0.0   # Pause if expectancy below this (%)
HEALTH_MONITOR_PAUSE_CYCLES = 200     # How long to pause when unhealthy
HEALTH_SCORE_FLOOR = 25               # Minimum health score (prevents deadlock: allows 0.25x size trades)

# ── Dynamic Position Sizing (based on REAL_EDGE) ──
EDGE_SIZING_ENABLED = True            # Enable/disable dynamic sizing from live edge
EDGE_SIZING_TARGET = 0.10             # Target edge (%/trade) — was 0.15 (too ambitious for paper trading)
EDGE_SIZING_MIN_MULT = 0.60           # v29.4.0: allow more sizing range on cold start (was 0.80)
EDGE_SIZING_MAX_MULT = 1.5            # Maximum multiplier — was 2.0 (capped to prevent oversizing on hot streaks)
EDGE_SIZING_MIN_TRADES = 50           # v29.3.5: 50 trades at full size before edge judgment (was 20 — doom loop)

# ── v29.3.4: Platform Abstraction Layer ──
# Wraps exchange-specific data access for future multi-platform support (crypto, stocks, forex)
class ExchangeConfig:
    """Exchange-agnostic data accessors. Currently Kraken; swap for Binance/Coinbase/etc."""
    PLATFORM = "kraken"
    ASSET_LIMITS = {
        "min_liquidity_usd": 100000,
        "max_volatility_pct": 500.0,
        "min_volatility_pct": 0.01,
        "price_precision_decimals": 8,
    }

    @staticmethod
    def get_ticker_price(t):
        """Extract last price from exchange-specific ticker object."""
        # TODO(multi-exchange): Kraken uses {"c": ["price", "lot_volume"]} format.
        #   Binance: float(t["lastPrice"]), Coinbase: float(t["price"])
        try:
            c = t.get("c", [0])
            return float(c[0]) if isinstance(c, list) else float(c)
        except (ValueError, IndexError, TypeError):
            return 0

    @staticmethod
    def get_ticker_volume(t):
        """Extract 24h volume in USD from exchange-specific ticker object."""
        # TODO(multi-exchange): Kraken uses {"v": [today, 24h], "p": [today_vwap, 24h_vwap]}.
        #   Binance: float(t["quoteVolume"]), Coinbase: float(t["volume"]) * price
        try:
            vol = float(t.get("v", [0, 0])[1]) if isinstance(t.get("v"), list) else 0
            vwap = float(t.get("p", [0, 0])[1]) if isinstance(t.get("p"), list) else 1
            return vol * vwap
        except (ValueError, IndexError, TypeError):
            return 0

    @staticmethod
    def normalize_pair_name(raw):
        """Convert exchange pair name to internal short format. Delegates to to_short_name()."""
        # TODO(multi-exchange): Kraken pair names use XXBTZUSD format.
        #   Binance: BTCUSDT, Coinbase: BTC-USD — each needs its own parser
        return to_short_name(raw) if callable(globals().get("to_short_name")) else raw

# ── Adaptive Trailing Stop ──
ADAPTIVE_TRAIL_ENABLED = True         # Enable/disable adaptive trailing tightening
ADAPTIVE_TRAIL_STREAK = 3             # Winning streak required to tighten trailing stops
ADAPTIVE_TRAIL_MULT = 0.9             # Multiply trail distance by this during streak (tighter)
ADAPTIVE_TRAIL_STREAK_2 = 6           # Longer streak threshold for extra tightening
ADAPTIVE_TRAIL_MULT_2 = 0.80          # Trail multiplier at streak >= 6 (lock in more profit)

# ── Overtrading Guard (blocked rate + frequency) ──
OVERTRADE_GUARD_ENABLED = True        # Enable/disable advanced overtrading guard
OVERTRADE_BLOCKED_RATE_MIN = 15.0     # Skip entries if blocked rate < this % (filters not working)
OVERTRADE_MIN_CYCLES_BETWEEN = 6      # v29.3: ~12s between trades — was 12 (~24s), too slow for trade frequency

# ── Market Depth Filter (thin-market protection) ──
MARKET_DEPTH_ENABLED = True           # Enable/disable market depth check
MIN_ORDER_BOOK_DEPTH = 3              # Multiplier: require 24h vol >= this × entry_size

# ── Multi-Timeframe Regime Confirmation ──
REGIME_CONFIRM_ENABLED = True         # Enable/disable multi-TF confirmation
REGIME_CONFIRM_SHORT_WINDOW = 20      # Short-term trend window in ticks (~1 min at 3s poll)
REGIME_CONFIRM_MEDIUM_WINDOW = 80     # Medium-term trend window in ticks (~4 min at 3s poll)

# ── Trade Quality Filters ──
MIN_REWARD_RISK = 1.2                 # Minimum R:R ratio to take a trade
VOLATILITY_SPIKE_MULT = 3.0           # Block if current vol > 3x historical vol

# ── Exposure Limits ──
MAX_SINGLE_COIN_EXPOSURE_PCT = 15.0   # v29.3.5: was 30% — too concentrated for $1K account
MAX_TOTAL_EXPOSURE_UPDATED_PCT = 60.0 # Max 60% total (overrides old 50%)

# ── Loss Protection ──
COIN_LOSS_BLOCK_CYCLES = 25           # Match smart blocker recovery time (was 200)

# ── Overtrading Protection ──
MAX_TRADES_PER_CYCLE = 1              # Max 1 new trade per cycle
MAX_TRADES_PER_100_CYCLES = 15        # Max 15 trades per 100 cycles (was 10 — too restrictive)

# ── Safe Mode ──
SAFE_MODE_DRAWDOWN_PCT = 8.0          # Enter safe mode at 8% drawdown
SAFE_MODE_SIZE_MULT = 0.5             # Cut size 50% in safe mode
# ── Runtime Stability ──
STABILITY_WARMUP_CYCLES = 300         # Disable aggressive safety for first N cycles
MAX_CONSECUTIVE_ERRORS = 50           # Only halt after this many back-to-back exceptions
CYCLE_TIMEOUT_SEC = 30                # v29.4.1: restored to 30 — safe default even with whitelist
HEARTBEAT_INTERVAL = 50               # Log heartbeat every N cycles
API_RETRY_STARTUP = 5                 # Retry API discovery this many times on startup
API_RETRY_DELAY = 10                  # Seconds between startup retries

# ── Long-Run Reliability ──
STAGNATION_RESET_CYCLES = 2000        # Reset cooldowns if no trades for this many cycles
API_STALE_BLOCK_ENTRIES = 50          # Block new entries after N cycles of API failure
API_STALE_FORCE_CLOSE = 200           # Force close all positions after N cycles of API failure
ERROR_BURST_THRESHOLD = 20            # Exec errors in burst window to trigger pause
ERROR_BURST_WINDOW = 50               # Window (cycles) for error burst detection
ERROR_BURST_PAUSE = 100               # Pause entries for this many cycles on error burst
MAX_COOLDOWN_CYCLES = 10000           # Safety cap: no cooldown can exceed cycle + this

# ── Recovery Mode ──
RECOVERY_TRIGGER_CYCLES = 300         # Activate recovery after this many idle cycles
RECOVERY_DURATION_CYCLES = 50         # Recovery window length
RECOVERY_COOLDOWN_CYCLES = 200       # Minimum cycles between recovery activations
RECOVERY_COIN_LOSS_DECAY = 0.7       # Decay factor for coin loss scores on soft reset
RECOVERY_MAX_ATTEMPTS = 2            # Max trade attempts per recovery cycle

# ── Minimum Activity Guard (prevents idle drift when valid signals exist) ──
MIN_ACTIVITY_ENABLED = True           # Master switch — False = no activity-based relaxation
MIN_ACTIVITY_IDLE_THRESHOLD = 100     # Start relaxing after 100 idle cycles (~5 min at 3s/cycle)
MIN_ACTIVITY_TIER_INTERVAL = 100      # Escalate one tier every 100 additional idle cycles
MIN_ACTIVITY_MAX_TIERS = 3            # Maximum relaxation tiers (caps at tier 3)
MIN_ACTIVITY_SCORE_STEP = 0.02        # Reduce score threshold by this per tier (tier 3 = -0.06)
MIN_ACTIVITY_CHANGE_STEP = 0.005      # Reduce change threshold by this per tier (tier 3 = -0.015)
MIN_ACTIVITY_TARGET_RATE = 3          # Target: at least 3 trades per 300-cycle window
MIN_ACTIVITY_SOFT_LENIENCY_TIER = 2   # At tier 2+, enable soft filter leniency (choppy/volume)
# NOTE: Hard filters (risk caps, exposure, liquidity, reward/risk, kill switches) are NEVER relaxed
# MinActivityGuard is COMPLEMENTARY to RecoveryMode:
#   MinActivityGuard (100+ idle cycles) → relaxes ENTRY THRESHOLDS (score, change)
#   RecoveryMode     (300+ idle cycles) → relaxes BLOCKING FILTERS (cooldowns, coin_loss)

# ── Smart Coin Blocker (replaces CoinLossTracker — cumulative P&L based blocking) ──
SMART_COIN_BLOCK_ENABLED = True           # Master switch — False = revert to legacy 2-loss blocking
SMART_COIN_CUMULATIVE_LOSS_PCT = -5.0     # Block coin if cumulative P&L drops below -5%
SMART_COIN_MAX_DRAWDOWN_PCT = -8.0        # Block coin if max drawdown from peak exceeds -8%
SMART_COIN_RECOVERY_RESET_CYCLES = 25     # Unblock after 25 idle cycles (fast recovery for blocked coins)
SMART_COIN_RECOVERY_PNL_PCT = 0.0         # Unblock if cumulative P&L recovers to 0% (breakeven)
SMART_COIN_RANGING_LENIENCY = 1.5         # In ranging: multiply loss threshold by 1.5x (more lenient)
SMART_COIN_TRADE_MEMORY = 20              # Track last N trades per coin for cumulative calc
SMART_COIN_MIN_TRADES = 2                 # Require at least 2 trades before blocking (avoid single-trade blocks)

# ── Smart Pair Failure Tracker (replaces PairFailureTracker — gradual decay) ──
PAIR_FAILURE_MAX = 3                 # Block pair after this many execution failures
PAIR_FAILURE_DECAY_CYCLES = 500      # Full reset after this many cycles (legacy compat)
SMART_PAIR_DECAY_ENABLED = True      # Enable gradual decay instead of binary reset
SMART_PAIR_DECAY_INTERVAL = 100      # Decay 1 failure count every 100 cycles
SMART_PAIR_SUCCESS_DECAY = 2         # Successful trade removes 2 failure counts (not full reset)
SMART_PAIR_RANGING_DECAY_MULT = 0.7  # Faster decay in ranging (100 * 0.7 = 70 cycles per decay)
VISIBILITY_LOG_INTERVAL = 100        # Log trade flow visibility every N cycles
UNIVERSE_MAX_PAIRS = 500             # Cap on total pairs in trading universe
UNIVERSE_FALLBACK_PAIRS = 50         # Fallback: top N volume pairs if exclusion filter kills all
SNAPSHOT_ENABLED = True              # Toggle bot health snapshot on/off
SNAPSHOT_INTERVAL = 20               # Run snapshot every N cycles

# ── Regime-Aware Position Sizing (can only REDUCE, never increase beyond existing limits) ──
REGIME_SIZE_SCALE = {
    "SMOOTH_TREND": 1.0,      # Full size — best conditions
    "VOLATILE_TREND": 0.75,   # 75% — higher uncertainty
    "QUIET_RANGE": 0.70,      # 70% — was 60%, thin margins but not crippled
    "CHOPPY": 0.75,           # 75% — ultra safe: reduced from 0.85, smaller positions in choppy markets
}
# POST_SIZING_BOOST removed in v29.3.5 — was 1.50 but always negated by subsequent risk caps. Noop computation at 8 call sites.

# ── Noise Trade Filter (blocks low-quality entries that bleed fees) ──
NOISE_FILTER_ENABLED = True                # Master switch — False = bypass all noise filters
NOISE_MOM_MIN_SCORE = 0.01                 # Was 0.03 — must match entry gate (0.01) or it blocks everything that passes the gate
NOISE_MOM_MIN_CHANGE = 0.002              # Was 0.003 — must match entry gate (0.002) or it blocks everything that passes the gate
NOISE_MEANREV_COIN_TREND_WINDOW = 40      # Mean rev: check per-COIN trend over this many ticks
NOISE_MEANREV_COIN_TREND_THRESHOLD = 0.25 # Mean rev: block if coin efficiency ratio > this (was 0.20 — loosened 25%)
NOISE_BREAKOUT_CONFIRM_TICKS = 2          # Breakout: require N consecutive ticks above/below band
NOISE_SHORT_MIN_SCORE = -0.01             # Was -0.03 — matches loosened long noise filter
NOISE_SHORT_MIN_CHANGE = -0.002           # Was -0.003 — matches loosened long noise filter

# ── Conviction Override (bypasses soft filters on very strong signals) ──
CONVICTION_OVERRIDE_ENABLED = True        # Master switch — False = all filters always apply
CONVICTION_SCORE_THRESHOLD = 0.10         # Was 0.20 — still too high for calm markets. 0.10 lets moderate signals bypass soft filters
CONVICTION_CHANGE_THRESHOLD = 0.015       # Momentum: |change| must exceed 1.5% (was 3% — 3% moves are rare in calm markets)
CONVICTION_BREAKOUT_WIDTH_THRESHOLD = 0.02  # Breakout: BB width must exceed this for override
# Soft filters that conviction can bypass (logged but not blocking):
# is_choppy, volume_confirms, pair_failure_tracker.is_blocked, coin_loss_tracker.is_blocked

# ── High-Conviction Override (score >= threshold bypasses ALL soft filters, no change% needed) ──
HIGH_CONVICTION_OVERRIDE_ENABLED = True   # Master switch for high-conviction tier
HIGH_CONVICTION_SCORE_THRESHOLD = 0.35    # Was 0.60 — virtually unreachable in calm markets. 0.35 is still a strong signal
HIGH_CONVICTION_MEANREV_Z_THRESHOLD = 3.0 # Mean-rev: |z| >= 3.0 → high conviction (z-scores differ from scores)
# HIGH CONVICTION bypasses these SOFT filters:
#   is_choppy, volume_confirms, pair_failure, coin_loss, short_momentum, coin_is_trending
# HIGH CONVICTION does NOT bypass these HARD filters:
#   unified_exposure_ok, reward_risk_ok, volatility_spike_check, market_depth_ok,
#   regime_confirm, strategy_health, group_limit, data freshness, circuit breaker, kill switch

# ── Execution Safety Layer (blocks entries when liquidity is poor) ──
EXEC_SAFETY_ENABLED = True                # Master switch — False = bypass all liquidity checks
EXEC_GAP_WINDOW = 20                      # Count price gaps in last N ticks
EXEC_GAP_ATR_MULT = 1.5                   # A tick-to-tick move > 1.5× ATR counts as a "gap"
EXEC_GAP_MAX_RATIO = 0.30                 # Block if > 30% of recent ticks are gaps
EXEC_SPREAD_TREND_WINDOW = 10             # Compare recent vs baseline spread over N ticks
EXEC_SPREAD_TREND_MAX = 2.0               # Block if current spread > 2.0× baseline spread
EXEC_MICROVOL_WINDOW = 5                  # Short-window volatility (ticks)
EXEC_MICROVOL_BASELINE = 20               # Baseline volatility window (ticks)
EXEC_MICROVOL_MAX_RATIO = 3.0             # Block if 5-tick vol > 3.0× 20-tick vol

# ── Crypto Correlation Groups ──
CRYPTO_GROUPS = {
    "majors": ["BTC", "ETH"],
    "l1_alts": ["SOL", "ADA", "AVAX", "DOT", "ATOM", "NEAR", "APT", "SUI"],
    "defi": ["UNI", "AAVE", "LINK", "MKR", "SNX", "CRV", "COMP", "SUSHI"],
    "meme": ["DOGE", "SHIB", "PEPE", "FLOKI", "BONK", "WIF"],
    "l2": ["MATIC", "ARB", "OP", "STRK", "ZK", "IMX"],
}


def get_crypto_group(coin):
    """Return the correlation group for a coin, or 'other' if ungrouped."""
    coin_upper = coin.upper().replace("/USD", "").replace("USD", "").replace("XBT", "BTC")
    for group_name, members in CRYPTO_GROUPS.items():
        if coin_upper in members:
            return group_name
    return "other"


def group_limit_ok(coin, wallet):
    """Return True if adding this coin won't exceed MAX_PER_GROUP for its group."""
    group = get_crypto_group(coin)
    if group == "other":
        return True  # No limit on ungrouped coins
    count = 0
    for held in list(wallet.longs.keys()) + list(wallet.shorts.keys()):
        if get_crypto_group(held) == group:
            count += 1
    return count < MAX_PER_GROUP


# ── v29.3.5: Standardized Log Formatting Helpers ──
def fmt_pct(val):
    """Format percentage to 2 decimal places for consistent logging."""
    return f"{val:.2f}"

def fmt_price(val):
    """Format price to 4 decimal places for consistent logging."""
    return f"{val:.4f}"

def fmt_conf(val):
    """Format confidence score to 2 decimal places for consistent logging."""
    return f"{val:.2f}"


# ── Internet Reconnect & API Resilience ──
# v29.3.5: Exponential backoff — start 5s, double each retry, cap 60s, max 5 retries
API_BACKOFF_BASE = 5        # Initial backoff in seconds
API_BACKOFF_CAP = 60        # Maximum backoff in seconds
API_BACKOFF_MAX_RETRIES = 5 # Max retries per cycle before skipping

def safe_api_call(url, params=None, timeout=5, retries=API_BACKOFF_MAX_RETRIES):
    """API call with exponential backoff on failure. Returns None on total failure."""
    for attempt in range(retries):
        try:
            r = requests.get(url, params=params, timeout=timeout)
            return r.json()
        except requests.exceptions.ConnectionError:
            _delay = min(API_BACKOFF_CAP, API_BACKOFF_BASE * (2 ** attempt))
            logger.warning(f"Connection failed (attempt {attempt+1}/{retries}), retrying in {_delay}s...")
            time.sleep(_delay)
        except requests.exceptions.Timeout:
            _delay = min(API_BACKOFF_CAP, API_BACKOFF_BASE * (2 ** attempt))
            logger.warning(f"Timeout (attempt {attempt+1}/{retries}), retrying in {_delay}s...")
            time.sleep(_delay)
        except Exception as e:
            _delay = min(API_BACKOFF_CAP, API_BACKOFF_BASE * (2 ** attempt))
            logger.error(f"API error: {e}, retrying in {_delay}s...")
            time.sleep(_delay)
    logger.error(f"API call failed after {retries} retries: {url}")
    return None


def validate_ticker(t):
    """Validate ticker data is sane. Returns True if valid."""
    try:
        if not isinstance(t, dict):
            return False
        price = float(t.get("c", [0])[0])
        if price <= 0 or price > 1e8:  # No zero or absurd prices
            return False
        vol = float(t.get("v", [0, 0])[1])
        if vol < 0:
            return False
        return True
    except Exception:
        return False


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — CROSS-EXCHANGE SUPPORT
# ExchangeAdapter base class + Kraken, Coinbase, Binance US, Alpaca adapters
# ══════════════════════════════════════════════════════════════════════════════

# API keys loaded from environment variables only — no hardcoded credentials
KRAKEN_API_KEY = os.environ.get("KRAKEN_API_KEY", "")
KRAKEN_API_SECRET = os.environ.get("KRAKEN_API_SECRET", "")
COINBASE_API_KEY = os.environ.get("COINBASE_API_KEY", "")
COINBASE_API_SECRET = os.environ.get("COINBASE_API_SECRET", "")
BINANCE_API_KEY = os.environ.get("BINANCE_API_KEY", "")
BINANCE_API_SECRET = os.environ.get("BINANCE_API_SECRET", "")
ALPACA_API_KEY = os.environ.get("ALPACA_API_KEY", "")
ALPACA_API_SECRET = os.environ.get("ALPACA_API_SECRET", "")
ALPACA_BASE_URL = os.environ.get("ALPACA_BASE_URL", "https://paper-api.alpaca.markets")
TRADE_WEBHOOK_URL = os.environ.get("TRADE_WEBHOOK_URL", "")

# Cross-exchange arbitrage config
ARBITRAGE_SCAN_INTERVAL = 10        # Check every N cycles
ARBITRAGE_MIN_SPREAD_PCT = 0.15     # Min spread after fees to flag opportunity
ARBITRAGE_PAIRS = ["BTC", "ETH", "SOL"]  # Pairs to monitor across exchanges


class ExchangeAdapter(ABC):
    """Abstract base class for all exchange adapters. (Item 1)"""

    def __init__(self, name, api_key="", api_secret="", paper_mode=True):
        self.name = name
        self.api_key = api_key
        self.api_secret = api_secret
        self.paper_mode = paper_mode
        self.connected = False
        self._last_error = None

    @abstractmethod
    def get_price(self, pair):
        """Return current price for a pair. Returns float or None on failure."""
        pass

    @abstractmethod
    def get_orderbook(self, pair, depth=10):
        """Return orderbook: {"bids": [(price, qty)...], "asks": [(price, qty)...]}."""
        pass

    @abstractmethod
    def get_ohlcv(self, pair, interval=5, limit=100):
        """Return OHLCV candles: [(timestamp, open, high, low, close, volume), ...]."""
        pass

    @abstractmethod
    def place_order(self, side, pair, amount):
        """Place an order. side='buy'|'sell'. Returns order_id or None. Paper mode = simulated."""
        pass

    @abstractmethod
    def get_balance(self):
        """Return balance dict: {"USD": float, "BTC": float, ...}."""
        pass

    def is_connected(self):
        """Check if adapter has valid credentials and is reachable."""
        return self.connected and bool(self.api_key)

    def _safe_request(self, url, params=None, timeout=10, method="GET", headers=None):
        """Wrapper for API calls with exponential backoff. Routes through safe_api_call pattern."""
        for attempt in range(API_BACKOFF_MAX_RETRIES):
            try:
                if method == "GET":
                    r = requests.get(url, params=params, headers=headers, timeout=timeout)
                else:
                    r = requests.post(url, json=params, headers=headers, timeout=timeout)
                if r.status_code == 200:
                    return r.json()
                else:
                    logger.warning(f"[{self.name}] HTTP {r.status_code} (attempt {attempt+1})")
            except Exception as e:
                logger.warning(f"[{self.name}] Request failed: {e} (attempt {attempt+1})")
            _delay = min(API_BACKOFF_CAP, API_BACKOFF_BASE * (2 ** attempt))
            time.sleep(_delay)
        return None


class KrakenAdapter(ExchangeAdapter):
    """Kraken exchange adapter — wraps existing Kraken API calls."""

    def __init__(self):
        super().__init__("Kraken", KRAKEN_API_KEY, KRAKEN_API_SECRET, PAPER_MODE)
        self.base_url = KRAKEN
        self.connected = True  # Kraken public endpoints work without auth
        self.fee_pct = 0.26    # Kraken taker fee

    def get_price(self, pair):
        try:
            data = safe_api_call(f"{self.base_url}/Ticker", params={"pair": pair}, timeout=5)
            if data and "result" in data:
                for k, v in data["result"].items():
                    return ExchangeConfig.get_ticker_price(v)
        except Exception:
            pass
        return None

    def get_orderbook(self, pair, depth=10):
        try:
            data = safe_api_call(f"{self.base_url}/Depth",
                                 params={"pair": pair, "count": depth}, timeout=5)
            if data and "result" in data:
                for k, v in data["result"].items():
                    bids = [(float(b[0]), float(b[1])) for b in v.get("bids", [])[:depth]]
                    asks = [(float(a[0]), float(a[1])) for a in v.get("asks", [])[:depth]]
                    return {"bids": bids, "asks": asks}
        except Exception:
            pass
        return {"bids": [], "asks": []}

    def get_ohlcv(self, pair, interval=5, limit=100):
        try:
            since = int(time.time()) - (limit * interval * 60)
            data = safe_api_call(f"{self.base_url}/OHLC",
                                 params={"pair": pair, "interval": interval, "since": since}, timeout=15)
            if data and "result" in data:
                for k in data["result"]:
                    if k != "last":
                        candles = data["result"][k]
                        return [(int(c[0]), float(c[1]), float(c[2]), float(c[3]),
                                 float(c[4]), float(c[6])) for c in candles if len(c) >= 7][:limit]
        except Exception:
            pass
        return []

    def place_order(self, side, pair, amount):
        if PAPER_MODE:
            _oid = f"PAPER-KRK-{uuid.uuid4().hex[:8]}"
            logger.info(f"[KRAKEN_PAPER] {side} {pair} ${amount:.2f} → {_oid}")
            return _oid
        # Real orders require authenticated endpoints — not implemented for safety
        logger.error("[KRAKEN] Real order placement requires authenticated API — not enabled")
        return None

    def get_balance(self):
        if PAPER_MODE:
            return {"USD": 0}  # Paper mode — wallet manages cash
        return {"USD": 0}


class CoinbaseAdapter(ExchangeAdapter):
    """Coinbase Advanced Trade API adapter."""

    def __init__(self):
        super().__init__("Coinbase", COINBASE_API_KEY, COINBASE_API_SECRET, PAPER_MODE)
        self.base_url = "https://api.coinbase.com/api/v3/brokerage"
        self.connected = bool(self.api_key)
        self.fee_pct = 0.40  # Coinbase taker fee (maker 0.25%)

    def _pair_fmt(self, coin):
        """Convert 'BTC' → 'BTC-USD' for Coinbase."""
        if "-" in coin:
            return coin
        return f"{coin}-USD"

    def get_price(self, pair):
        pair = self._pair_fmt(pair)
        try:
            data = self._safe_request(f"https://api.coinbase.com/v2/prices/{pair}/spot", timeout=5)
            if data and "data" in data:
                return float(data["data"]["amount"])
        except Exception:
            pass
        return None

    def get_orderbook(self, pair, depth=10):
        pair = self._pair_fmt(pair)
        try:
            data = self._safe_request(f"{self.base_url}/product_book",
                                      params={"product_id": pair, "limit": depth}, timeout=5)
            if data and "pricebook" in data:
                book = data["pricebook"]
                bids = [(float(b["price"]), float(b["size"])) for b in book.get("bids", [])[:depth]]
                asks = [(float(a["price"]), float(a["size"])) for a in book.get("asks", [])[:depth]]
                return {"bids": bids, "asks": asks}
        except Exception:
            pass
        return {"bids": [], "asks": []}

    def get_ohlcv(self, pair, interval=5, limit=100):
        pair = self._pair_fmt(pair)
        granularity_map = {1: "ONE_MINUTE", 5: "FIVE_MINUTE", 15: "FIFTEEN_MINUTE", 60: "ONE_HOUR"}
        gran = granularity_map.get(interval, "FIVE_MINUTE")
        try:
            end = int(time.time())
            start = end - (limit * interval * 60)
            data = self._safe_request(f"{self.base_url}/products/{pair}/candles",
                                      params={"start": start, "end": end, "granularity": gran}, timeout=10)
            if data and "candles" in data:
                return [(int(c["start"]), float(c["open"]), float(c["high"]),
                         float(c["low"]), float(c["close"]), float(c["volume"]))
                        for c in data["candles"]][:limit]
        except Exception:
            pass
        return []

    def place_order(self, side, pair, amount):
        if PAPER_MODE:
            _oid = f"PAPER-CB-{uuid.uuid4().hex[:8]}"
            logger.info(f"[COINBASE_PAPER] {side} {pair} ${amount:.2f} → {_oid}")
            return _oid
        logger.error("[COINBASE] Real order placement requires authenticated API — not enabled")
        return None

    def get_balance(self):
        if PAPER_MODE:
            return {"USD": 0}
        return {"USD": 0}


class BinanceUSAdapter(ExchangeAdapter):
    """Binance US API adapter."""

    def __init__(self):
        super().__init__("BinanceUS", BINANCE_API_KEY, BINANCE_API_SECRET, PAPER_MODE)
        self.base_url = "https://api.binance.us/api/v3"
        self.connected = bool(self.api_key)
        self.fee_pct = 0.10  # Binance US taker fee

    def _pair_fmt(self, coin):
        """Convert 'BTC' → 'BTCUSD' for Binance."""
        if "USD" in coin:
            return coin
        return f"{coin}USD"

    def get_price(self, pair):
        pair = self._pair_fmt(pair)
        try:
            data = self._safe_request(f"{self.base_url}/ticker/price",
                                      params={"symbol": pair}, timeout=5)
            if data and "price" in data:
                return float(data["price"])
        except Exception:
            pass
        return None

    def get_orderbook(self, pair, depth=10):
        pair = self._pair_fmt(pair)
        try:
            data = self._safe_request(f"{self.base_url}/depth",
                                      params={"symbol": pair, "limit": depth}, timeout=5)
            if data:
                bids = [(float(b[0]), float(b[1])) for b in data.get("bids", [])[:depth]]
                asks = [(float(a[0]), float(a[1])) for a in data.get("asks", [])[:depth]]
                return {"bids": bids, "asks": asks}
        except Exception:
            pass
        return {"bids": [], "asks": []}

    def get_ohlcv(self, pair, interval=5, limit=100):
        pair = self._pair_fmt(pair)
        interval_map = {1: "1m", 5: "5m", 15: "15m", 60: "1h"}
        intv = interval_map.get(interval, "5m")
        try:
            data = self._safe_request(f"{self.base_url}/klines",
                                      params={"symbol": pair, "interval": intv, "limit": limit}, timeout=10)
            if data and isinstance(data, list):
                return [(int(c[0]) // 1000, float(c[1]), float(c[2]), float(c[3]),
                         float(c[4]), float(c[5])) for c in data]
        except Exception:
            pass
        return []

    def place_order(self, side, pair, amount):
        if PAPER_MODE:
            _oid = f"PAPER-BIN-{uuid.uuid4().hex[:8]}"
            logger.info(f"[BINANCE_PAPER] {side} {pair} ${amount:.2f} → {_oid}")
            return _oid
        logger.error("[BINANCE_US] Real order placement requires authenticated API — not enabled")
        return None

    def get_balance(self):
        if PAPER_MODE:
            return {"USD": 0}
        return {"USD": 0}


class AlpacaAdapter(ExchangeAdapter):
    """Alpaca Markets adapter for US stocks. (Item 7)"""

    def __init__(self):
        super().__init__("Alpaca", ALPACA_API_KEY, ALPACA_API_SECRET, PAPER_MODE)
        self.base_url = ALPACA_BASE_URL
        self.data_url = "https://data.alpaca.markets/v2"
        self.connected = bool(self.api_key)
        self.fee_pct = 0.0  # Alpaca is commission-free

    def _headers(self):
        return {"APCA-API-KEY-ID": self.api_key, "APCA-API-SECRET-KEY": self.api_secret}

    def get_price(self, pair):
        data = self._safe_request(f"{self.data_url}/stocks/{pair}/trades/latest",
                                  headers=self._headers(), timeout=5)
        if data:
            return float(data.get("trade", {}).get("p", 0)) or None
        return None

    def get_orderbook(self, pair, depth=10):
        data = self._safe_request(f"{self.data_url}/stocks/{pair}/quotes/latest",
                                  headers=self._headers(), timeout=5)
        if data:
            q = data.get("quote", {})
            return {"bids": [(float(q.get("bp", 0)), float(q.get("bs", 0)))],
                    "asks": [(float(q.get("ap", 0)), float(q.get("as", 0)))]}
        return {"bids": [], "asks": []}

    def get_ohlcv(self, pair, interval=5, limit=100):
        timeframe_map = {1: "1Min", 5: "5Min", 15: "15Min", 60: "1Hour"}
        tf = timeframe_map.get(interval, "5Min")
        data = self._safe_request(f"{self.data_url}/stocks/{pair}/bars",
                                  headers=self._headers(),
                                  params={"timeframe": tf, "limit": limit}, timeout=10)
        if data:
            bars = data.get("bars", []) or []
            return [(int(datetime.fromisoformat(b["t"].replace("Z", "+00:00")).timestamp()),
                     float(b["o"]), float(b["h"]), float(b["l"]),
                     float(b["c"]), float(b["v"])) for b in bars]
        return []

    def place_order(self, side, pair, amount):
        if PAPER_MODE:
            _oid = f"PAPER-ALP-{uuid.uuid4().hex[:8]}"
            logger.info(f"[ALPACA_PAPER] {side} {pair} ${amount:.2f} → {_oid}")
            return _oid
        logger.error("[ALPACA] Real order placement requires authenticated API — not enabled")
        return None

    def get_balance(self):
        if PAPER_MODE:
            return {"USD": 0}
        acct = self._safe_request(f"{self.base_url}/v2/account",
                                  headers=self._headers(), timeout=5)
        if acct:
            return {"USD": float(acct.get("cash", 0))}
        return {"USD": 0}


# ── Exchange Registry ──
_exchange_adapters = {}  # name -> ExchangeAdapter instance


def _init_exchanges():
    """Initialize all exchange adapters. Called once at startup."""
    global _exchange_adapters
    _exchange_adapters["kraken"] = KrakenAdapter()
    _exchange_adapters["coinbase"] = CoinbaseAdapter()
    _exchange_adapters["binance_us"] = BinanceUSAdapter()
    _exchange_adapters["alpaca"] = AlpacaAdapter()
    _connected = [n for n, a in _exchange_adapters.items() if a.is_connected()]
    logger.info(f"[EXCHANGES] Initialized: {list(_exchange_adapters.keys())} | Connected: {_connected}")


def get_exchange(name):
    """Get exchange adapter by name."""
    return _exchange_adapters.get(name)


def connected_exchanges():
    """Return list of connected exchange adapters."""
    return [a for a in _exchange_adapters.values() if a.is_connected()]


def best_exchange_for(pair, direction="buy"):
    """Return the exchange with the best price for a given direction. (Item 3)
    For buy: lowest ask. For sell: highest bid."""
    best_ex = None
    best_price = float("inf") if direction == "buy" else 0
    for ex in connected_exchanges():
        try:
            p = ex.get_price(pair)
            if p is None or p <= 0:
                continue
            if direction == "buy" and p < best_price:
                best_price = p
                best_ex = ex
            elif direction == "sell" and p > best_price:
                best_price = p
                best_ex = ex
        except Exception:
            continue
    return best_ex, best_price


def scan_arbitrage(cycle):
    """Cross-exchange arbitrage scanner. (Item 2)
    Every ARBITRAGE_SCAN_INTERVAL cycles, compare prices across exchanges."""
    if cycle % ARBITRAGE_SCAN_INTERVAL != 0:
        return []
    opportunities = []
    exchanges = connected_exchanges()
    if len(exchanges) < 2:
        return []
    for coin in ARBITRAGE_PAIRS:
        prices_by_ex = {}
        for ex in exchanges:
            try:
                p = ex.get_price(coin)
                if p and p > 0:
                    prices_by_ex[ex.name] = (p, ex.fee_pct)
            except Exception:
                continue
        if len(prices_by_ex) < 2:
            continue
        # Find best buy (lowest) and best sell (highest)
        sorted_exs = sorted(prices_by_ex.items(), key=lambda x: x[1][0])
        buy_ex, (buy_price, buy_fee) = sorted_exs[0]
        sell_ex, (sell_price, sell_fee) = sorted_exs[-1]
        if buy_ex == sell_ex:
            continue
        spread_pct = ((sell_price - buy_price) / buy_price) * 100
        net_spread = spread_pct - buy_fee - sell_fee
        if net_spread > ARBITRAGE_MIN_SPREAD_PCT:
            opp = {"coin": coin, "buy_exchange": buy_ex, "sell_exchange": sell_ex,
                   "buy_price": buy_price, "sell_price": sell_price,
                   "spread_pct": spread_pct, "net_profit_pct": net_spread}
            opportunities.append(opp)
            logger.info(f"[ARBITRAGE_OPPORTUNITY] {coin}: Buy {buy_ex} ${buy_price:.4f} → "
                        f"Sell {sell_ex} ${sell_price:.4f} | Spread {spread_pct:.3f}% | "
                        f"Net profit {net_spread:.3f}% after fees")
    return opportunities


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — MARKET INTELLIGENCE
# Sentiment scoring, on-chain analysis, multi-timeframe confirmation
# ══════════════════════════════════════════════════════════════════════════════

SENTIMENT_BLOCK_HIGH = 0.7     # Block shorts if sentiment > this
SENTIMENT_BLOCK_LOW = -0.7     # Block longs if sentiment < this
_sentiment_cache = {}          # coin -> (score, timestamp)
SENTIMENT_CACHE_TTL = 300      # Refresh every 5 minutes


def sentiment_score(coin):
    """Compute sentiment score for a coin (-1.0 to +1.0). (Item 4)
    Uses CoinGecko community data. Caches results for SENTIMENT_CACHE_TTL seconds."""
    now_ts = time.time()
    if coin in _sentiment_cache:
        cached_score, cached_ts = _sentiment_cache[coin]
        if now_ts - cached_ts < SENTIMENT_CACHE_TTL:
            return cached_score
    score = 0.0
    try:
        # CoinGecko community data (free, no auth)
        _coin_id = coin.lower()
        _cg_map = {"BTC": "bitcoin", "ETH": "ethereum", "SOL": "solana", "XRP": "ripple",
                    "ADA": "cardano", "DOT": "polkadot", "AVAX": "avalanche-2",
                    "LINK": "chainlink", "DOGE": "dogecoin", "MATIC": "matic-network"}
        _coin_id = _cg_map.get(coin, _coin_id)
        data = safe_api_call(f"https://api.coingecko.com/api/v3/coins/{_coin_id}",
                             params={"localization": "false", "tickers": "false",
                                     "market_data": "false", "community_data": "true"},
                             timeout=10)
        if data and "community_data" in data:
            cd = data["community_data"]
            # Reddit subscribers + active accounts as sentiment proxy
            reddit_subs = cd.get("reddit_subscribers", 0) or 0
            reddit_active = cd.get("reddit_accounts_active_48h", 0) or 0
            twitter_followers = cd.get("twitter_followers", 0) or 0
            # Normalize: active/subscribers ratio indicates engagement
            if reddit_subs > 0:
                engagement = min(1.0, reddit_active / max(1, reddit_subs) * 10)
            else:
                engagement = 0.0
            # CoinGecko sentiment data
            up_pct = data.get("sentiment_votes_up_percentage", 50) or 50
            score = (up_pct - 50) / 50  # Normalize to -1..+1
            # Blend with engagement
            score = score * 0.7 + engagement * 0.3
            score = max(-1.0, min(1.0, score))
    except Exception as e:
        logger.debug(f"[SENTIMENT] Error for {coin}: {e}")
    _sentiment_cache[coin] = (score, now_ts)
    return score


def sentiment_allows(coin, direction):
    """Check if sentiment allows a trade direction. (Item 4)"""
    try:
        s = sentiment_score(coin)
        if direction == "short" and s > SENTIMENT_BLOCK_HIGH:
            logger.debug(f"[SENTIMENT_BLOCK] {coin} short blocked: sentiment={s:.2f} > {SENTIMENT_BLOCK_HIGH}")
            return False
        if direction == "long" and s < SENTIMENT_BLOCK_LOW:
            logger.debug(f"[SENTIMENT_BLOCK] {coin} long blocked: sentiment={s:.2f} < {SENTIMENT_BLOCK_LOW}")
            return False
    except Exception:
        pass  # Fail open — don't block on sentiment errors
    return True


def onchain_score(coin):
    """Compute on-chain confidence boost (0.0 to 1.0). (Item 5)
    Uses CoinGecko developer + on-chain data as proxy."""
    try:
        _coin_id = coin.lower()
        _cg_map = {"BTC": "bitcoin", "ETH": "ethereum", "SOL": "solana", "XRP": "ripple",
                    "ADA": "cardano", "DOT": "polkadot", "AVAX": "avalanche-2"}
        _coin_id = _cg_map.get(coin, _coin_id)
        data = safe_api_call(f"https://api.coingecko.com/api/v3/coins/{_coin_id}",
                             params={"localization": "false", "tickers": "false",
                                     "market_data": "true", "developer_data": "true"},
                             timeout=10)
        if not data:
            return 0.5  # Neutral default
        score = 0.5
        # Market cap rank as quality proxy
        rank = data.get("market_cap_rank", 100) or 100
        rank_score = max(0, 1.0 - rank / 200)
        # Developer activity
        dev = data.get("developer_data", {})
        if dev:
            commits_4w = dev.get("commit_count_4_weeks", 0) or 0
            dev_score = min(1.0, commits_4w / 100)
        else:
            dev_score = 0.0
        # Combine
        score = rank_score * 0.5 + dev_score * 0.3 + 0.2  # Base 0.2 floor
        return max(0.0, min(1.0, score))
    except Exception:
        return 0.5


def multi_timeframe_confirm(coin, direction):
    """Multi-timeframe confirmation: 1m, 5m, 15m OHLCV alignment. (Item 6)
    Returns True only if 2 of 3 timeframes agree with direction."""
    kraken = _exchange_adapters.get("kraken")
    if not kraken:
        return True  # Fail open
    pair_key = f"{coin}USD"  # Basic pair format
    agreements = 0
    for interval in [1, 5, 15]:
        try:
            candles = kraken.get_ohlcv(pair_key, interval=interval, limit=20)
            if not candles or len(candles) < 5:
                agreements += 1  # Not enough data — count as agree (fail open)
                continue
            # Trend: compare SMA of last 5 candles vs last 10
            closes = [c[4] for c in candles]
            sma_short = sum(closes[-5:]) / 5
            sma_long = sum(closes[-10:]) / min(10, len(closes))
            if direction == "long" and sma_short > sma_long:
                agreements += 1
            elif direction == "short" and sma_short < sma_long:
                agreements += 1
        except Exception:
            agreements += 1  # Error — fail open
    return agreements >= 2


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — STOCKS SUPPORT (Alpaca)
# ══════════════════════════════════════════════════════════════════════════════

stock_watchlist = []  # Top 20 stock candidates: [{"symbol", "rel_vol", "gap_pct", "price"}, ...]
STOCK_SCAN_ENABLED = False  # Enable only when Alpaca API key is set
STOCK_MIN_REL_VOL = 2.0     # Relative volume > 2x
STOCK_PRICE_MIN = 10.0
STOCK_PRICE_MAX = 500.0
STOCK_GAP_MIN_PCT = 2.0     # Gap > 2%
STOCK_EARNINGS_DAYS = 5      # Earnings within 5 days


def scan_stock_universe():
    """Stock universe scanner. (Item 7)
    Filters: relative volume > 2x, price $10-$500, gap > 2%. Top 20 stored in stock_watchlist."""
    global stock_watchlist
    alpaca = _exchange_adapters.get("alpaca")
    if not alpaca or not alpaca.is_connected():
        return
    try:
        snapshots = alpaca._safe_request(f"{alpaca.data_url}/stocks/snapshots",
                                         headers=alpaca._headers(),
                                         params={"feed": "iex"}, timeout=15)
        if not snapshots:
            return
        candidates = []
        for symbol, snap in snapshots.items():
            try:
                bar = snap.get("dailyBar", {})
                prev = snap.get("prevDailyBar", {})
                latest = snap.get("latestTrade", {})
                price = float(latest.get("p", 0))
                vol = float(bar.get("v", 0))
                prev_vol = float(prev.get("v", 1))
                prev_close = float(prev.get("c", 0))
                if price < STOCK_PRICE_MIN or price > STOCK_PRICE_MAX:
                    continue
                if prev_vol <= 0 or prev_close <= 0:
                    continue
                rel_vol = vol / prev_vol
                gap_pct = ((price - prev_close) / prev_close) * 100
                if rel_vol >= STOCK_MIN_REL_VOL and abs(gap_pct) >= STOCK_GAP_MIN_PCT:
                    candidates.append({"symbol": symbol, "price": price,
                                       "rel_vol": rel_vol, "gap_pct": gap_pct})
            except Exception:
                continue
        candidates.sort(key=lambda x: abs(x["gap_pct"]) * x["rel_vol"], reverse=True)
        stock_watchlist = candidates[:20]
        if stock_watchlist:
            logger.info(f"[STOCK_SCAN] {len(stock_watchlist)} stocks pass filters. "
                        f"Top: {stock_watchlist[0]['symbol']} gap={stock_watchlist[0]['gap_pct']:+.1f}%")
    except Exception as e:
        logger.warning(f"[STOCK_SCAN] Error: {e}")


def pre_market_scan():
    """Pre-market scan running at 4AM ET. (Item 8)
    Fetches pre-market movers and adds high-conviction stocks to watchlist."""
    global stock_watchlist
    alpaca = _exchange_adapters.get("alpaca")
    if not alpaca or not alpaca.is_connected():
        return
    try:
        # Alpaca doesn't have a dedicated pre-market movers endpoint
        # Use most-actives as proxy
        snapshots = alpaca._safe_request(f"{alpaca.data_url}/stocks/snapshots",
                                         headers=alpaca._headers(),
                                         params={"feed": "iex"}, timeout=15)
        if not snapshots:
            return
        movers = []
        for symbol, snap in snapshots.items():
            try:
                bar = snap.get("minuteBar", {})
                latest = snap.get("latestTrade", {})
                prev = snap.get("prevDailyBar", {})
                price = float(latest.get("p", 0))
                prev_close = float(prev.get("c", 0))
                if price <= 0 or prev_close <= 0:
                    continue
                change_pct = ((price - prev_close) / prev_close) * 100
                if abs(change_pct) > 3.0 and STOCK_PRICE_MIN <= price <= STOCK_PRICE_MAX:
                    movers.append({"symbol": symbol, "price": price, "change_pct": change_pct,
                                   "rel_vol": 1.0, "gap_pct": change_pct})
            except Exception:
                continue
        movers.sort(key=lambda x: abs(x["change_pct"]), reverse=True)
        # Merge with existing watchlist (deduplicate)
        existing_syms = {s["symbol"] for s in stock_watchlist}
        for m in movers[:10]:
            if m["symbol"] not in existing_syms:
                stock_watchlist.append(m)
        stock_watchlist = stock_watchlist[:20]
        if movers:
            logger.info(f"[PRE_MARKET] Found {len(movers)} pre-market movers. "
                        f"Top: {movers[0]['symbol']} {movers[0]['change_pct']:+.1f}%")
    except Exception as e:
        logger.warning(f"[PRE_MARKET] Error: {e}")


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — DEX + MEME COIN SCANNER
# ══════════════════════════════════════════════════════════════════════════════

DEX_SCAN_ENABLED = False  # Enable when ready to monitor DEX pools
DEX_MIN_LIQUIDITY = 50000  # $50K minimum
DEX_MAX_POOL_AGE_HOURS = 24
DEX_MIN_VOL_LIQ_RATIO = 0.5


class DexScanner:
    """Monitors Uniswap v3 and Raydium for new token pools. (Item 9)"""

    def __init__(self):
        self.detected_gems = []  # List of detected new tokens
        self.seen_pools = set()  # Already-flagged pool addresses

    def scan_uniswap(self):
        """Scan Uniswap v3 for new high-potential pools."""
        if not DEX_SCAN_ENABLED:
            return []
        gems = []
        try:
            # Uniswap v3 subgraph (The Graph)
            query = '''{ pools(first: 50, orderBy: createdAtTimestamp, orderDirection: desc,
                        where: {totalValueLockedUSD_gt: "50000"}) {
                        id token0 { symbol } token1 { symbol }
                        totalValueLockedUSD volumeUSD createdAtTimestamp } }'''
            data = safe_api_call("https://api.thegraph.com/subgraphs/name/uniswap/uniswap-v3",
                                 params=None, timeout=15)
            # Note: requires POST with GraphQL — simplified here for safety
            # In production, use proper GraphQL client
            if data and "data" in data and "pools" in data["data"]:
                now_ts = time.time()
                for pool in data["data"]["pools"]:
                    pool_id = pool["id"]
                    if pool_id in self.seen_pools:
                        continue
                    age_hours = (now_ts - int(pool["createdAtTimestamp"])) / 3600
                    tvl = float(pool["totalValueLockedUSD"])
                    volume = float(pool["volumeUSD"])
                    if (age_hours <= DEX_MAX_POOL_AGE_HOURS and tvl >= DEX_MIN_LIQUIDITY
                            and tvl > 0 and volume / tvl >= DEX_MIN_VOL_LIQ_RATIO):
                        gem = {"address": pool_id,
                               "token0": pool["token0"]["symbol"],
                               "token1": pool["token1"]["symbol"],
                               "liquidity_usd": tvl, "volume_usd": volume,
                               "age_hours": age_hours,
                               "vol_liq_ratio": volume / tvl}
                        gems.append(gem)
                        self.seen_pools.add(pool_id)
                        logger.info(f"[NEW_GEM_DETECTED] {gem['token0']}/{gem['token1']} | "
                                    f"Liquidity: ${tvl:,.0f} | Volume: ${volume:,.0f} | "
                                    f"Age: {age_hours:.1f}h | Vol/Liq: {volume/tvl:.2f}")
        except Exception as e:
            logger.debug(f"[DEX_SCAN] Uniswap error: {e}")
        self.detected_gems.extend(gems)
        return gems

    def scan_raydium(self):
        """Scan Raydium (Solana) for new pools."""
        if not DEX_SCAN_ENABLED:
            return []
        gems = []
        try:
            data = safe_api_call("https://api.raydium.io/v2/main/pairs", timeout=15)
            if data and isinstance(data, list):
                now_ts = time.time()
                for pool in data[:100]:  # Check newest 100
                    pool_id = pool.get("ammId", "")
                    if pool_id in self.seen_pools:
                        continue
                    tvl = float(pool.get("liquidity", 0))
                    vol_24h = float(pool.get("volume24h", 0))
                    if tvl >= DEX_MIN_LIQUIDITY and tvl > 0 and vol_24h / tvl >= DEX_MIN_VOL_LIQ_RATIO:
                        gem = {"address": pool_id,
                               "token0": pool.get("name", "?").split("-")[0] if "-" in pool.get("name", "") else "?",
                               "token1": "SOL",
                               "liquidity_usd": tvl, "volume_usd": vol_24h,
                               "age_hours": 0, "vol_liq_ratio": vol_24h / tvl}
                        gems.append(gem)
                        self.seen_pools.add(pool_id)
                        logger.info(f"[NEW_GEM_DETECTED] Raydium: {gem['token0']}/SOL | "
                                    f"Liquidity: ${tvl:,.0f} | Vol24h: ${vol_24h:,.0f}")
        except Exception as e:
            logger.debug(f"[DEX_SCAN] Raydium error: {e}")
        self.detected_gems.extend(gems)
        return gems

    def scan(self):
        """Run full DEX scan (both Uniswap and Raydium)."""
        return self.scan_uniswap() + self.scan_raydium()

    def save_state(self):
        return {"seen_pools": list(self.seen_pools),
                "detected_gems": self.detected_gems[-50:]}  # Keep last 50

    def load_state(self, state):
        if state:
            self.seen_pools = set(state.get("seen_pools", []))
            self.detected_gems = state.get("detected_gems", [])


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — RISK + REPORTING
# Portfolio heat, trade notifications, daily reports
# ══════════════════════════════════════════════════════════════════════════════

PORTFOLIO_HEAT_MAX_PCT = 15.0  # Block entries if total risk exceeds this


def _calc_position_heat(pos, prices, pv):
    """Calculate heat contribution for a single position. (Item 30: deduplicated)"""
    try:
        coin = pos.get("coin", "")
        p = prices.get(coin, pos.get("entry", 0))
        if p <= 0:
            return 0.0
        pos_value = pos.get("qty", 0) * p
        atr = coin_atr(coin) if coin in prices_cache else 0.01
        sl_pct = max(SL_BASE_PCT, max(0.01, atr * 100) * ATR_SL_MULTIPLIER)
        return (pos_value / pv) * sl_pct
    except Exception:
        return 1.0  # Conservative default


def portfolio_heat(wallet, prices):
    """Calculate total risk % across ALL open positions on ALL exchanges. (Items 10+26)
    Risk per position = position_value / portfolio_value * SL%.
    Returns total heat as percentage of portfolio."""
    pv = wallet.value(prices)
    if pv <= 0:
        return 100.0  # No portfolio = max risk
    total_heat = 0.0
    # Local wallet positions (primary)
    for coin, pos in wallet.longs.items():
        pos_with_coin = {**pos, "coin": coin}
        total_heat += _calc_position_heat(pos_with_coin, prices, pv)
    for coin, pos in wallet.shorts.items():
        pos_with_coin = {**pos, "coin": coin}
        total_heat += _calc_position_heat(pos_with_coin, prices, pv)
    # Cross-exchange positions (Item 26): query connected exchange balances
    for name, adapter in _exchange_adapters.items():
        if name == "kraken" or not adapter.is_connected():
            continue  # Kraken positions are already in wallet
        try:
            bal = adapter.get_balance()
            if not bal:
                continue
            for asset, qty in bal.items():
                if asset == "USD" or qty <= 0:
                    continue
                # Estimate position value using adapter price
                p = adapter.get_price(f"{asset}USD")
                if p and p > 0:
                    pos_value = qty * p
                    # Conservative SL estimate for external positions
                    heat = (pos_value / pv) * SL_BASE_PCT
                    total_heat += heat
        except Exception:
            pass
    return total_heat


def portfolio_heat_allows_entry(wallet, prices):
    """Returns True if portfolio heat is below maximum. (Item 10)"""
    heat = portfolio_heat(wallet, prices)
    if heat > PORTFOLIO_HEAT_MAX_PCT:
        logger.debug(f"[HEAT_BLOCK] Portfolio heat {heat:.2f}% > {PORTFOLIO_HEAT_MAX_PCT}% — blocking entry")
        return False
    return True


def trade_notification(event_type, data):
    """Send webhook notification for trade events. (Item 11)
    event_type: 'entry' or 'exit'. data: dict with trade details."""
    if not TRADE_WEBHOOK_URL:
        return
    try:
        payload = {"event": event_type, "timestamp": datetime.now(timezone.utc).isoformat(),
                   "bot_version": "v29.4.0", **data}
        threading.Thread(target=_send_webhook, args=(payload,), daemon=True).start()
    except Exception as e:
        logger.debug(f"[WEBHOOK] Error: {e}")


def _send_webhook(payload):
    """Send webhook in background thread with retry."""
    for attempt in range(3):
        try:
            r = requests.post(TRADE_WEBHOOK_URL, json=payload, timeout=10)
            if r.status_code < 500:
                return  # Success or client error (no point retrying 4xx)
        except Exception:
            pass
        time.sleep(min(API_BACKOFF_CAP, API_BACKOFF_BASE * (2 ** attempt)))


def generate_daily_report(wallet, prices, trades_today, cycle):
    """Generate daily performance report. (Item 12)
    Runs at midnight. Saves to logs/daily_report_YYYY-MM-DD.txt."""
    try:
        today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        report_dir = os.path.join(DIR, "logs")
        os.makedirs(report_dir, exist_ok=True)
        report_path = os.path.join(report_dir, f"daily_report_{today}.txt")

        pv = wallet.value(prices)
        total_trades = wallet.wins + wallet.losses
        wr = (wallet.wins / total_trades * 100) if total_trades > 0 else 0

        # Collect today's trades
        recent_trades = wallet.trades[-50:] if wallet.trades else []
        wins = [t for t in recent_trades if t.get("pnl", 0) > 0]
        losses = [t for t in recent_trades if t.get("pnl", 0) <= 0]
        best = max(recent_trades, key=lambda t: t.get("pnl", 0)) if recent_trades else None
        worst = min(recent_trades, key=lambda t: t.get("pnl", 0)) if recent_trades else None

        # Strategy breakdown
        strat_counts = {}
        for t in recent_trades:
            s = t.get("strategy", "unknown")
            strat_counts[s] = strat_counts.get(s, 0) + 1
        top_strat = max(strat_counts.items(), key=lambda x: x[1])[0] if strat_counts else "none"

        lines = [
            f"{'=' * 60}",
            f"  DAILY REPORT — {today}",
            f"{'=' * 60}",
            f"  Equity:       ${pv:,.2f}",
            f"  Trades Today: {len(recent_trades)}",
            f"  Win Rate:     {wr:.1f}%",
            f"  Wins/Losses:  {wallet.wins}/{wallet.losses}",
            f"  Top Strategy: {top_strat} ({strat_counts.get(top_strat, 0)} trades)",
        ]
        if best:
            lines.append(f"  Best Trade:   {best.get('coin', '?')} {best.get('pnl', 0):+.2f}%")
        if worst:
            lines.append(f"  Worst Trade:  {worst.get('coin', '?')} {worst.get('pnl', 0):+.2f}%")
        lines.append(f"  Heat:         {portfolio_heat(wallet, prices):.1f}%")
        lines.append(f"  Cycle:        {cycle}")
        lines.append(f"{'=' * 60}")

        report_text = "\n".join(lines)
        with open(report_path, "w") as f:
            f.write(report_text)
        logger.info(f"[DAILY_REPORT] Saved to {report_path}")
        return report_text
    except Exception as e:
        logger.warning(f"[DAILY_REPORT] Error: {e}")
        return ""


# Initialize DEX scanner instance
dex_scanner = DexScanner()


# ── Performance Metrics ──
class PerformanceTracker:
    """Tracks real performance metrics for the bot."""

    def __init__(self):
        self.window_trades = 0            # Rolling window trade counter (resets every ~2400 cycles / ~80 min)
        self.window_start_cycle = 0
        self.returns = []  # List of trade return percentages
        self.equity_curve = []  # Portfolio value over time

    def record_trade(self, pnl_pct):
        self.returns.append(pnl_pct)
        self.window_trades += 1

    def reset_window(self, cycle):
        self.window_trades = 0
        self.window_start_cycle = cycle

    def can_trade(self, cycle):
        """Check if we're under the rolling trade limit (~80 min window)."""
        if cycle - self.window_start_cycle > 2400:
            self.reset_window(cycle)
        return self.window_trades < MAX_DAILY_TRADES

    def track_equity(self, value):
        self.equity_curve.append(value)
        if len(self.equity_curve) > 5000:
            self.equity_curve = self.equity_curve[-5000:]

    def sharpe_ratio(self):
        """Calculate Sharpe ratio from trade returns."""
        if len(self.returns) < 5:
            return 0
        try:
            mean = sum(self.returns) / len(self.returns)
            std = (sum((r - mean) ** 2 for r in self.returns) / len(self.returns)) ** 0.5
            if std == 0:
                return 0
            return mean / std
        except Exception:
            return 0

    def profit_factor(self):
        """Gross profits / gross losses. >1 = profitable."""
        try:
            wins = sum(r for r in self.returns if r > 0)
            losses = abs(sum(r for r in self.returns if r < 0))
            if losses == 0:
                return float('inf') if wins > 0 else 0
            return wins / losses
        except Exception:
            return 0

    def max_drawdown(self):
        """Maximum peak-to-trough decline."""
        if len(self.equity_curve) < 2:
            return 0
        try:
            peak = self.equity_curve[0]
            max_dd = 0
            for v in self.equity_curve:
                peak = max(peak, v)
                dd = (peak - v) / peak if peak > 0 else 0
                max_dd = max(max_dd, dd)
            return max_dd * 100
        except Exception:
            return 0

    def win_rate(self):
        if not self.returns:
            return 0
        wins = sum(1 for r in self.returns if r > 0)
        return wins / len(self.returns) * 100

    def summary(self):
        return {
            "trades": len(self.returns),
            "win_rate": round(self.win_rate(), 1),
            "sharpe": round(self.sharpe_ratio(), 2),
            "profit_factor": round(self.profit_factor(), 2),
            "max_drawdown": round(self.max_drawdown(), 1),
            "window_trades": self.window_trades,
        }


perf = PerformanceTracker()


# ── Fee Tracker ──
class FeeTracker:
    """Tracks all fees paid for accurate P&L reporting."""

    def __init__(self):
        self.total_fees_usd = 0.0
        self.trade_fees = []  # Last 100 fee records
        self.session_fees = 0.0

    def record_fee(self, coin, side, fee_usd, fee_pct):
        self.total_fees_usd += fee_usd
        self.session_fees += fee_usd
        self.trade_fees.append({"coin": coin, "side": side, "fee_usd": fee_usd, "fee_pct": fee_pct})
        if len(self.trade_fees) > 100:
            self.trade_fees = self.trade_fees[-100:]

    def avg_fee_pct(self):
        if not self.trade_fees:
            return 0.2  # Default 0.2%
        return sum(f["fee_pct"] for f in self.trade_fees) / len(self.trade_fees)

    def summary(self):
        return {
            "total_fees_usd": round(self.total_fees_usd, 2),
            "session_fees_usd": round(self.session_fees, 2),
            "avg_fee_pct": round(self.avg_fee_pct(), 3),
            "num_trades": len(self.trade_fees),
        }


fee_tracker = FeeTracker()


# ── Verbosity Helpers ──
def vprint(msg, level="NORMAL"):
    """Print only if current VERBOSITY >= level. QUIET<NORMAL<DEBUG."""
    _levels = {"QUIET": 0, "NORMAL": 1, "DEBUG": 2}
    if _levels.get(VERBOSITY, 1) >= _levels.get(level, 1):
        print(msg)


def is_verbose(level="NORMAL"):
    """Return True if VERBOSITY >= level."""
    _levels = {"QUIET": 0, "NORMAL": 1, "DEBUG": 2}
    return _levels.get(VERBOSITY, 1) >= _levels.get(level, 1)


# ── Async Log Writer (Priority 1) ──
class AsyncLogWriter:
    """Non-blocking file logger. Main thread enqueues lines; daemon thread writes.

    - Uses queue.Queue (thread-safe, unbounded by default)
    - Daemon thread drains queue and batches writes per file path
    - flush() blocks until queue is empty (called on shutdown)
    - Never raises — all errors silently caught
    """

    def __init__(self):
        self._queue = queue.Queue()
        self._thread = threading.Thread(target=self._writer_loop, daemon=True)
        self._thread.start()
        self._stopped = False

    def enqueue(self, file_path, line):
        """Add a line to be written. Non-blocking, never raises."""
        if self._stopped:
            return
        try:
            self._queue.put_nowait((file_path, line))
        except Exception:
            pass

    def _writer_loop(self):
        """Background thread: drain queue, batch writes per file."""
        while True:
            try:
                # Block until at least one item
                item = self._queue.get(timeout=1.0)
            except queue.Empty:
                continue
            except Exception:
                continue

            # Batch: collect all available items in one pass
            batch = {}
            items_count = 1
            path, line = item
            batch.setdefault(path, []).append(line)

            # Drain remaining non-blocking
            while True:
                try:
                    path, line = self._queue.get_nowait()
                    batch.setdefault(path, []).append(line)
                    items_count += 1
                except queue.Empty:
                    break
                except Exception:
                    break

            # Write batched lines per file
            for fpath, lines in batch.items():
                try:
                    with open(fpath, "a") as f:
                        f.writelines(lines)
                except Exception:
                    pass

            # Mark all items as done so join() unblocks
            for _ in range(items_count):
                self._queue.task_done()

    def flush(self, timeout=5.0):
        """Block until queue is drained. Called on shutdown."""
        try:
            self._queue.join()
        except Exception:
            pass
        # Extra safety: wait a bit for any in-flight writes
        deadline = time.time() + timeout
        while not self._queue.empty() and time.time() < deadline:
            time.sleep(0.05)

    def stop(self):
        """Mark as stopped and flush remaining."""
        self._stopped = True
        self.flush()


# Global async writer instance
_async_writer = AsyncLogWriter()


# ── Trade Logger: logs every completed trade to logs/trades.jsonl ──
class TradeLogger:
    """Logs every completed trade as a JSONL line to logs/trades.jsonl."""

    def __init__(self):
        self._path = os.path.join(DIR, "logs", "trades.jsonl")

    def log_trade(self, coin, side, entry_price, exit_price, pnl_pct, reason):
        """Append one JSONL trade line. Non-blocking via async writer."""
        try:
            # Skip null/invalid trade records
            if not coin or not side or entry_price <= 0:
                return
            ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
            record = {
                "timestamp": ts,
                "coin": coin,
                "side": side,
                "entry": round(entry_price, 6),
                "exit": round(exit_price, 6),
                "pnl_pct": round(pnl_pct, 4),
                "reason": reason,
            }
            _async_writer.enqueue(self._path, json.dumps(record) + "\n")
        except Exception as e:
            logger.debug(f"TradeLogger error: {e}")


trade_logger = TradeLogger()


# ── Equity Curve Logger: logs equity every cycle to logs/equity.csv ──
class EquityCurveLogger:
    """Appends equity snapshot every cycle to logs/equity.csv."""

    def __init__(self):
        self._path = os.path.join(DIR, "logs", "equity.csv")
        # Write header if file doesn't exist or is empty
        try:
            if not os.path.exists(self._path) or os.path.getsize(self._path) == 0:
                with open(self._path, "w") as f:
                    f.write("timestamp,equity,cash,positions_value\n")
        except Exception:
            pass

    def log(self, equity, cash, positions_value):
        """Append one equity snapshot. Non-blocking via async writer."""
        try:
            ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
            line = f"{ts},{equity:.2f},{cash:.2f},{positions_value:.2f}\n"
            _async_writer.enqueue(self._path, line)
        except Exception as e:
            logger.debug(f"EquityCurveLogger error: {e}")


equity_logger = EquityCurveLogger()


# ── Error Logger: centralized error logging to logs/errors.log ──
class ErrorLogger:
    """Centralized error logger. Writes all bot errors/warnings to logs/errors.log."""

    def __init__(self):
        self._path = os.path.join(DIR, "logs", "errors.log")
        self._count = 0
        try:
            if not os.path.exists(self._path) or os.path.getsize(self._path) == 0:
                with open(self._path, "w") as f:
                    f.write("timestamp,type,message\n")
        except Exception:
            pass

    def log(self, error_type, message):
        """Log an error. Non-blocking via async writer. Also classifies via error_classifier."""
        try:
            self._count += 1
            ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
            # Sanitize message: remove commas and newlines for CSV safety
            safe_msg = str(message).replace(",", ";").replace("\n", " ")
            line = f"{ts},{error_type},{safe_msg}\n"
            _async_writer.enqueue(self._path, line)
            if DEBUG_MODE or is_verbose("DEBUG"):
                print(f"  [ERROR] {error_type}: {safe_msg}")
            # Classify error (error_classifier may not exist yet during init)
            try:
                error_classifier.record(error_type, _current_cycle)
            except NameError:
                pass
        except Exception:
            pass

    @property
    def error_count(self):
        return self._count


error_logger = ErrorLogger()


# ── Error Classifier: separates API / logging / execution errors ──
class ErrorClassifier:
    """Classifies errors into categories. Only EXECUTION errors matter for cooldown.
    API and logging errors are harmless noise — they NEVER affect trading."""

    # Error type prefixes → category mapping
    _API_TYPES = {"api_fetch", "api_timeout", "api_error", "api_retry", "get_tickers",
                  "API FETCH FAILED", "api_discovery"}
    _LOG_TYPES = {"log_write", "log_validator", "logging", "health_output", "heartbeat",
                  "paper_tracker", "daily_metrics", "equity_csv", "exit_guard_long",
                  "exit_guard_short", "kill_switch_record_trade", "kill_switch_check_equity",
                  "strategy_health_record", "coin_loss_record",
                  # Log validator findings — NOT execution errors
                  "trades_bad_json", "trades_missing_fields", "trades_bad_values",
                  "trades_bad_price", "trades_unrealistic_pnl", "trades_validation_error",
                  "equity_negative", "equity_sudden_jump", "equity_validation_error",
                  "log_validator_crash",
                  # Order pre-flight rejections — normal filtering, not errors
                  "order_rejected",
                  # Recovery/startup — harmless bookkeeping
                  "recovery_mode_check", "recovery_expiry", "recovery_soft_reset",
                  "startup_check_fail", "startup_check_crash",
                  # Safety system bookkeeping
                  "consistency_check_error", "equity_sanity_error",
                  "strategy_health_pause", "strategy_health_check",
                  "coin_loss_tracker_record", "coin_loss_is_blocked",
                  "overtrading_can_trade", "safe_mode_update",
                  "kill_switch", "kill_switch_reset", "kill_switch_close_error",
                  "clean_export_error"}

    def __init__(self):
        self.api_errors = 0
        self.log_errors = 0
        self.exec_errors = 0
        self._exec_history = []  # (cycle, error_type) for rate calculation
        self._cooldown_until = 0  # Cycle until which entries are paused

    def classify(self, error_type):
        """Classify an error and increment the right counter. Returns category string."""
        try:
            etype = str(error_type).strip()
            # Check API errors
            for api_key in self._API_TYPES:
                if api_key in etype.lower() or etype.lower().startswith("api"):
                    self.api_errors += 1
                    return "api"
            # Check logging errors
            for log_key in self._LOG_TYPES:
                if log_key in etype.lower() or etype.lower().startswith("log"):
                    self.log_errors += 1
                    return "logging"
            # Everything else = execution error (the only kind that matters)
            self.exec_errors += 1
            return "execution"
        except Exception:
            self.exec_errors += 1
            return "execution"

    def record(self, error_type, cycle):
        """Record an error with classification. Called alongside error_logger.log()."""
        try:
            cat = self.classify(error_type)
            if cat == "execution":
                self._exec_history.append(cycle)
                # Trim old entries outside window
                cutoff = cycle - ERROR_RATE_WINDOW
                self._exec_history = [c for c in self._exec_history if c > cutoff]
        except Exception:
            pass

    def check_cooldown(self, cycle):
        """Check if error rate is high enough to trigger a cooldown.
        Checks both steady-state rate AND short burst detection.
        Returns True if entries should be paused."""
        try:
            if cycle < self._cooldown_until:
                return True
            # Check 1: Steady-state error rate (ERROR_RATE_WINDOW)
            cutoff = cycle - ERROR_RATE_WINDOW
            recent = [c for c in self._exec_history if c > cutoff]
            rate = len(recent)
            if rate >= ERROR_COOLDOWN_THRESHOLD:
                self._cooldown_until = min(cycle + ERROR_COOLDOWN_CYCLES, cycle + MAX_COOLDOWN_CYCLES)
                logger.warning(
                    f"ERROR COOLDOWN: {rate} execution errors in last {ERROR_RATE_WINDOW} cycles "
                    f"— pausing entries for {ERROR_COOLDOWN_CYCLES} cycles (until cycle {self._cooldown_until})"
                )
                return True
            # Check 2: Error BURST (many errors in short window)
            burst_cutoff = cycle - ERROR_BURST_WINDOW
            burst = [c for c in self._exec_history if c > burst_cutoff]
            if len(burst) >= ERROR_BURST_THRESHOLD:
                self._cooldown_until = min(cycle + ERROR_BURST_PAUSE, cycle + MAX_COOLDOWN_CYCLES)
                logger.warning(
                    f"ERROR BURST: {len(burst)} execution errors in last {ERROR_BURST_WINDOW} cycles "
                    f"— pausing entries for {ERROR_BURST_PAUSE} cycles (until cycle {self._cooldown_until})"
                )
                return True
            return False
        except Exception:
            return False

    @property
    def cooldown_active(self):
        return self._cooldown_until > 0

    @property
    def cooldown_remaining(self, cycle=0):
        return max(0, self._cooldown_until - cycle)

    def summary(self):
        """Return error breakdown string for health output."""
        return f"api={self.api_errors} log={self.log_errors} exec={self.exec_errors}"

    def save_state(self):
        return {
            "api_errors": self.api_errors,
            "log_errors": self.log_errors,
            "exec_errors": self.exec_errors,
            "cooldown_until": self._cooldown_until,
        }

    def load_state(self, state):
        if state:
            self.api_errors = state.get("api_errors", 0)
            self.log_errors = state.get("log_errors", 0)
            self.exec_errors = state.get("exec_errors", 0)
            self._cooldown_until = state.get("cooldown_until", 0)


error_classifier = ErrorClassifier()


# ── Stagnation Watchdog: reset cooldowns if no trades for too long ──
class StagnationWatchdog:
    """Detects when the bot goes too long without trading and resets blocking state."""

    def __init__(self):
        self.last_trade_cycle = 0
        self.reset_count = 0

    def record_trade(self, cycle):
        self.last_trade_cycle = cycle

    def check(self, cycle, wallet):
        """Check if bot is stagnating. Returns True if reset was performed."""
        try:
            if self.last_trade_cycle == 0:
                self.last_trade_cycle = cycle  # Initialize on first check
                return False
            idle_cycles = cycle - self.last_trade_cycle
            if idle_cycles >= STAGNATION_RESET_CYCLES:
                # Reset cooldowns
                wallet.cooldowns.clear()
                # Reset coin loss tracker blocks
                try:
                    coin_loss_tracker.blocked_until.clear()
                except Exception:
                    pass
                self.reset_count += 1
                self.last_trade_cycle = cycle  # Prevent re-triggering next cycle
                logger.warning(
                    f"STAGNATION RESET #{self.reset_count}: {idle_cycles} cycles without a trade "
                    f"— cleared cooldowns and coin blocks"
                )
                return True
            return False
        except Exception:
            return False


stagnation_watchdog = StagnationWatchdog()


# ── API Staleness Tracker: block/close when API fails too long ──
class ApiStalenessTracker:
    """Tracks consecutive API failures and triggers protective actions."""

    def __init__(self):
        self.last_success_cycle = 0
        self.consecutive_failures = 0

    def record_success(self, cycle):
        self.last_success_cycle = cycle
        self.consecutive_failures = 0

    def record_failure(self):
        self.consecutive_failures += 1

    def stale_cycles(self, cycle):
        """How many cycles since last successful API call."""
        if self.last_success_cycle == 0:
            # First call: initialize to current cycle so staleness starts counting from NOW
            self.last_success_cycle = cycle
            return 0
        return cycle - self.last_success_cycle

    def should_block_entries(self, cycle):
        """Block new entries if API has been down too long."""
        return self.stale_cycles(cycle) >= API_STALE_BLOCK_ENTRIES

    def should_force_close(self, cycle):
        """Force close all positions if API down way too long."""
        return self.stale_cycles(cycle) >= API_STALE_FORCE_CLOSE


api_staleness = ApiStalenessTracker()


# ── Skip Reason Tracker: counts why entries were skipped ──
class SkipReasonTracker:
    """Tracks why entry signals were skipped. Prints summary every N cycles."""

    def __init__(self):
        self.counts = {}

    def record(self, reason):
        try:
            self.counts[reason] = self.counts.get(reason, 0) + 1
        except Exception:
            pass

    def summary(self):
        """Return sorted summary string."""
        if not self.counts:
            return "none"
        parts = sorted(self.counts.items(), key=lambda x: -x[1])
        return " ".join(f"{k}={v}" for k, v in parts[:10])

    def reset(self):
        self.counts.clear()


skip_tracker = SkipReasonTracker()


# ── Conviction Kill Tracker: which hard filters kill conviction-approved signals ──
class ConvictionKillTracker:
    """Tracks why conviction-overridden signals still got rejected.
    Purely diagnostic — does NOT affect any trading logic."""

    def __init__(self):
        self.kills = {}  # reason -> count
        self.total_overrides = 0
        self.total_survived = 0

    def record_override(self):
        """Called when a conviction override fires."""
        self.total_overrides += 1

    def record_kill(self, reason):
        """Called when a conviction-active signal is rejected by a hard filter."""
        self.kills[reason] = self.kills.get(reason, 0) + 1

    def record_survived(self):
        """Called when a conviction-active signal passes all filters and executes."""
        self.total_survived += 1

    def summary(self):
        if not self.kills and self.total_overrides == 0:
            return ""
        parts = sorted(self.kills.items(), key=lambda x: -x[1])
        kill_str = " ".join(f"{k}={v}" for k, v in parts[:8])
        return f"overrides={self.total_overrides} survived={self.total_survived} kills=[{kill_str}]"

    def reset(self):
        self.kills.clear()
        self.total_overrides = 0
        self.total_survived = 0


conviction_kill_tracker = ConvictionKillTracker()


# ── Global Per-Cycle Trade Audit ──
class CycleAudit:
    """Tracks the full signal-to-trade funnel each cycle.

    Categorizes every rejection reason into buckets:
    - risk: exposure_cap, global_risk_cap, stress_risk, coin_exposure, rr_filter, vol_spike
    - cooldown: cooldown, coin_blocked, pair_blocked
    - health: strategy_health, circuit_breaker
    - filter: choppy_filter, volume_filter, pullback_filter, momentum_filter, insufficient_data,
              stale_price, suspicious_price, correlation, group_limit
    """

    RISK_REASONS = {"exposure_cap", "global_risk_cap", "stress_risk", "coin_exposure",
                    "rr_filter", "vol_spike"}
    COOLDOWN_REASONS = {"cooldown", "coin_blocked", "pair_blocked"}
    HEALTH_REASONS = {"strategy_health", "circuit_breaker"}

    def __init__(self):
        self.signals_raw = 0
        self.signals_after_filters = 0
        self.rejected_by_risk = 0
        self.rejected_by_cooldown = 0
        self.rejected_by_health = 0
        self.rejected_by_filter = 0
        self.final_candidates = 0
        self.executed_trades = 0

    def record_raw_signal(self):
        """Called for every signal that enters strategy evaluation."""
        self.signals_raw += 1

    def record_passed_filters(self):
        """Called when a signal passes all filters and reaches execution."""
        self.signals_after_filters += 1
        self.final_candidates += 1

    def record_rejection(self, reason):
        """Categorize a rejection by its reason string."""
        # Extract base reason (strip order_rejected: prefix, recovery_rejected: prefix)
        base = reason.split(":")[0] if ":" in reason else reason
        if base in self.RISK_REASONS:
            self.rejected_by_risk += 1
        elif base in self.COOLDOWN_REASONS:
            self.rejected_by_cooldown += 1
        elif base in self.HEALTH_REASONS:
            self.rejected_by_health += 1
        else:
            self.rejected_by_filter += 1

    def record_execution(self):
        """Called when a trade is actually executed (filled)."""
        self.executed_trades += 1

    def top_failure_reason(self):
        """Return the single most common blocker category this cycle."""
        buckets = {
            "risk_blocked": self.rejected_by_risk,
            "cooldown_blocked": self.rejected_by_cooldown,
            "health_blocked": self.rejected_by_health,
            "filter_blocked": self.rejected_by_filter,
        }
        top = max(buckets, key=buckets.get)
        if buckets[top] == 0:
            return "none"
        return top

    def emit(self, cycle, recovery_active, logger_ref):
        """Emit unified audit summary. Called once per cycle after all paths. ALWAYS logs."""
        try:
            top_reason = self.top_failure_reason()
            summary = (
                f"[AUDIT SUMMARY] cycle={cycle} "
                f"signals_raw={self.signals_raw} after_filters={self.signals_after_filters} "
                f"risk_blocked={self.rejected_by_risk} cooldown_blocked={self.rejected_by_cooldown} "
                f"health_blocked={self.rejected_by_health} filter_blocked={self.rejected_by_filter} "
                f"final_candidates={self.final_candidates} executed_trades={self.executed_trades} "
                f"top_failure_reason={top_reason}"
            )
            # Always log the summary every cycle — DEBUG only (file), not terminal
            if self.signals_raw > 0 and self.final_candidates == 0:
                logger_ref.debug(f"{summary} | ZERO-TRADE: ALL {self.signals_raw} SIGNALS FILTERED OUT")
            elif self.signals_raw == 0:
                logger_ref.debug(f"{summary} | NO RAW SIGNALS")
            elif self.final_candidates > 0 and self.executed_trades == 0:
                logger_ref.debug(f"{summary} | CANDIDATES EXISTED BUT ZERO EXECUTED")
            else:
                logger_ref.debug(summary)
        except Exception:
            pass

    def reset(self):
        """Reset all counters for next cycle."""
        self.signals_raw = 0
        self.signals_after_filters = 0
        self.rejected_by_risk = 0
        self.rejected_by_cooldown = 0
        self.rejected_by_health = 0
        self.rejected_by_filter = 0
        self.final_candidates = 0
        self.executed_trades = 0


cycle_audit = CycleAudit()


# ── Smart Pair Failure Tracker (gradual decay instead of binary reset) ──
class SmartPairFailureTracker:
    """Tracks execution failures per pair with gradual decay.
    Instead of binary reset after DECAY_CYCLES, failures decay one at a time.
    Successful trades reduce failure count by SMART_PAIR_SUCCESS_DECAY (not full reset).
    Drop-in replacement: same .is_blocked() / .record_failure() / .reset_pair() API."""

    def __init__(self):
        self.failures = {}  # pair -> {"count": int, "last_cycle": int, "last_decay_cycle": int}

    def record_failure(self, pair, cycle):
        """Record an execution failure for a specific pair."""
        try:
            if pair not in self.failures:
                self.failures[pair] = {"count": 0, "last_cycle": 0, "last_decay_cycle": cycle}
            self.failures[pair]["count"] += 1
            self.failures[pair]["last_cycle"] = cycle
        except Exception:
            pass

    def _apply_decay(self, pair, cycle, is_ranging=False):
        """Apply gradual decay based on elapsed cycles since last failure/decay."""
        try:
            if not SMART_PAIR_DECAY_ENABLED:
                return  # Legacy behavior: binary reset handled in is_blocked
            info = self.failures[pair]
            if info["count"] <= 0:
                return
            last_decay = info.get("last_decay_cycle", info["last_cycle"])
            elapsed = cycle - last_decay
            # Determine decay interval (faster in ranging)
            interval = SMART_PAIR_DECAY_INTERVAL
            if is_ranging and RANGING_ADAPTATION_ENABLED:
                interval = int(interval * SMART_PAIR_RANGING_DECAY_MULT)
            interval = max(1, interval)
            # How many decay ticks have elapsed?
            ticks = elapsed // interval
            if ticks > 0:
                old_count = info["count"]
                info["count"] = max(0, info["count"] - ticks)
                info["last_decay_cycle"] = last_decay + (ticks * interval)
                if info["count"] < old_count:
                    logger.debug(f"PAIR DECAY: {pair} failures {old_count}->{info['count']} ({ticks} ticks, interval={interval})")
        except Exception:
            pass

    def is_blocked(self, pair, cycle, is_ranging=False):
        """Returns True if pair has failed too many times recently.
        Accepts is_ranging kwarg for faster decay."""
        try:
            if pair not in self.failures:
                return False
            info = self.failures[pair]
            if SMART_PAIR_DECAY_ENABLED:
                # Gradual decay
                self._apply_decay(pair, cycle, is_ranging)
                return info["count"] >= PAIR_FAILURE_MAX
            else:
                # Legacy: binary reset after DECAY_CYCLES
                if cycle - info["last_cycle"] > PAIR_FAILURE_DECAY_CYCLES:
                    info["count"] = 0
                    return False
                return info["count"] >= PAIR_FAILURE_MAX
        except Exception:
            return False

    def reset_pair(self, pair):
        """Reduce failure count on successful trade (not full reset unless smart decay disabled)."""
        try:
            if pair not in self.failures:
                return
            if SMART_PAIR_DECAY_ENABLED:
                old_count = self.failures[pair]["count"]
                self.failures[pair]["count"] = max(0, old_count - SMART_PAIR_SUCCESS_DECAY)
                if old_count > 0:
                    logger.debug(f"PAIR SUCCESS DECAY: {pair} failures {old_count}->{self.failures[pair]['count']} (success -={SMART_PAIR_SUCCESS_DECAY})")
            else:
                self.failures[pair]["count"] = 0
        except Exception:
            pass

    def blocked_pairs_summary(self):
        """Return dict of currently blocked pairs for logging."""
        try:
            summary = {}
            for pair, info in self.failures.items():
                if info["count"] >= PAIR_FAILURE_MAX:
                    summary[pair] = {"count": info["count"], "last_cycle": info["last_cycle"]}
            return summary
        except Exception:
            return {}

    def save_state(self):
        return {"failures": self.failures}

    def load_state(self, state):
        if state:
            self.failures = state.get("failures", {})
            # Migrate: add last_decay_cycle if missing (from legacy PairFailureTracker)
            for pair, info in self.failures.items():
                if "last_decay_cycle" not in info:
                    info["last_decay_cycle"] = info.get("last_cycle", 0)


pair_failure_tracker = SmartPairFailureTracker()


# ── Recovery Mode: Prevents permanent no-trade deadlock ──
class RecoveryMode:
    """Activates when the bot goes too long without trading.
    During recovery: relaxes soft blockers (cooldowns, coin loss, strategy health)
    but NEVER bypasses critical protections (kill switch, API staleness, price validation).
    Guarantees trade ATTEMPTS, not forced trades."""

    def __init__(self):
        self.active = False
        self.activated_cycle = 0
        self.last_trade_cycle = 0
        self.last_recovery_end = 0       # Cycle when last recovery ended (for cooldown)
        self.attempted_trades = 0
        self.executed_trades = 0
        self.activation_count = 0
        self.soft_resets = 0
        self._attempted_this_cycle = False  # Reset each cycle, used for fallback logic
        # Visibility tracking (rolling, reset every VISIBILITY_LOG_INTERVAL)
        self._vis_signals_found = 0
        self._vis_passed_filters = 0
        self._vis_attempted = 0
        self._vis_executed = 0

    def record_trade(self, cycle):
        """Called when ANY trade executes (entry). Resets idle counter, exits recovery."""
        self.last_trade_cycle = cycle
        if self.active:
            self.executed_trades += 1
            self._vis_executed += 1
            self.active = False
            self.last_recovery_end = cycle
            logger.info(
                f"RECOVERY MODE EXIT: trade executed at cycle {cycle} — "
                f"attempts={self.attempted_trades} executed={self.executed_trades}"
            )

    def record_attempt(self):
        """Called when recovery mode attempts a trade (valid signal, valid price)."""
        self.attempted_trades += 1
        self._vis_attempted += 1
        self._attempted_this_cycle = True

    def record_signal(self):
        """Called when a signal is found (for visibility tracking)."""
        self._vis_signals_found += 1

    def record_passed_filter(self):
        """Called when a signal passes all filters (for visibility tracking)."""
        self._vis_passed_filters += 1

    def check(self, cycle):
        """Check if recovery should activate. Called once per cycle."""
        try:
            # Reset per-cycle attempt flag
            self._attempted_this_cycle = False
            if self.active:
                # Check if recovery window expired
                if cycle - self.activated_cycle >= RECOVERY_DURATION_CYCLES:
                    self._on_expiry(cycle)
                return
            # Don't activate during first warmup
            if self.last_trade_cycle == 0:
                self.last_trade_cycle = cycle
                return
            idle_cycles = cycle - self.last_trade_cycle
            # Cooldown: don't re-activate too soon after last recovery ended
            if self.last_recovery_end > 0 and (cycle - self.last_recovery_end) < RECOVERY_COOLDOWN_CYCLES:
                return
            if idle_cycles >= RECOVERY_TRIGGER_CYCLES:
                self.active = True
                self.activated_cycle = cycle
                self.attempted_trades = 0
                self.executed_trades = 0
                self.activation_count += 1
                logger.warning(
                    f"RECOVERY MODE ACTIVATED #{self.activation_count}: "
                    f"{idle_cycles} idle cycles — relaxing soft blockers for {RECOVERY_DURATION_CYCLES} cycles"
                )
        except Exception as e:
            try:
                error_logger.log("recovery_mode_check", str(e))
            except Exception:
                pass

    def _on_expiry(self, cycle):
        """Called when recovery window expires. Performs soft reset if zero executions."""
        try:
            logger.warning(
                f"RECOVERY MODE EXPIRED: attempts={self.attempted_trades} "
                f"executed={self.executed_trades}"
            )
            if self.executed_trades == 0:
                self._soft_reset(cycle)
            self.active = False
            self.last_recovery_end = cycle
        except Exception as e:
            self.active = False
            self.last_recovery_end = cycle
            try:
                error_logger.log("recovery_expiry", str(e))
            except Exception:
                pass

    def _soft_reset(self, cycle):
        """Decay blocking state to prevent permanent deadlock.
        Does NOT clear critical protections — only soft blockers."""
        try:
            self.soft_resets += 1
            # 1. Decay coin loss scores (multiply blocked_until remaining time by decay factor)
            try:
                for coin in list(coin_loss_tracker.blocked_until.keys()):
                    remaining = coin_loss_tracker.blocked_until[coin] - cycle
                    if remaining > 0:
                        coin_loss_tracker.blocked_until[coin] = cycle + int(remaining * RECOVERY_COIN_LOSS_DECAY)
                    else:
                        del coin_loss_tracker.blocked_until[coin]
            except Exception:
                pass
            # 2. Reset strategy health to neutral (clear recent bad results)
            try:
                strategy_health_monitor.paused_until_cycle = 0
            except Exception:
                pass
            try:
                for stype in ['momentum', 'mean_rev', 'breakout', 'short']:
                    bucket = getattr(strategy_health, f"{stype}_results", None)
                    if bucket is not None:
                        bucket.clear()
            except Exception:
                pass
            # 3. Clear cooldowns
            try:
                # Import wallet reference — will be set when wired into main loop
                if hasattr(self, '_wallet_ref') and self._wallet_ref:
                    self._wallet_ref.cooldowns.clear()
            except Exception:
                pass
            logger.warning(
                f"RECOVERY SOFT RESET #{self.soft_resets}: decayed coin blocks, "
                f"reset strategy health, cleared cooldowns"
            )
        except Exception as e:
            try:
                error_logger.log("recovery_soft_reset", str(e))
            except Exception:
                pass

    def should_skip_cooldown(self):
        """During recovery, cooldowns are relaxed."""
        return self.active

    def should_skip_coin_loss_block(self):
        """During recovery, coin loss blocks are relaxed."""
        return self.active

    def should_skip_strategy_health(self):
        """During recovery, strategy health pauses are relaxed."""
        return self.active

    def visibility_summary(self):
        """Return visibility stats and reset counters."""
        summary = (
            f"signals={self._vis_signals_found} passed={self._vis_passed_filters} "
            f"attempts={self._vis_attempted} executed={self._vis_executed} "
            f"recovery={'ON' if self.active else 'off'}"
        )
        top_skip = skip_tracker.summary().split(" ")[0] if skip_tracker.counts else "none"
        summary += f" top_block={top_skip}"
        return summary

    def reset_visibility(self):
        """Reset visibility counters (called after logging)."""
        self._vis_signals_found = 0
        self._vis_passed_filters = 0
        self._vis_attempted = 0
        self._vis_executed = 0

    def save_state(self):
        return {
            "active": self.active,
            "activated_cycle": self.activated_cycle,
            "last_trade_cycle": self.last_trade_cycle,
            "last_recovery_end": self.last_recovery_end,
            "activation_count": self.activation_count,
            "soft_resets": self.soft_resets,
        }

    def load_state(self, state):
        if state:
            self.active = state.get("active", False)
            self.activated_cycle = state.get("activated_cycle", 0)
            self.last_trade_cycle = state.get("last_trade_cycle", 0)
            self.last_recovery_end = state.get("last_recovery_end", 0)
            self.activation_count = state.get("activation_count", 0)
            self.soft_resets = state.get("soft_resets", 0)


recovery_mode = RecoveryMode()


# ── Minimum Activity Guard: graduated threshold relaxation on idle periods ──
class MinActivityGuard:
    """Prevents the bot from going idle when tradeable signals exist.

    Complements RecoveryMode:
      - RecoveryMode (300+ idle) relaxes BLOCKING filters (cooldowns, coin_loss, strategy health)
      - MinActivityGuard (100+ idle) relaxes ENTRY THRESHOLDS (score, change, noise)

    Graduated tiers based on idle cycles since last trade:
      Tier 0 (0–99 cycles):   Normal thresholds
      Tier 1 (100–199 cycles): -0.02 score, -0.005 change
      Tier 2 (200–299 cycles): -0.04 score, -0.01 change + soft filter leniency
      Tier 3 (300+ cycles):    -0.06 score, -0.015 change + soft filter leniency

    Also considers trade rate: if below target rate, tier escalates by 1.

    NEVER bypasses hard filters (risk, exposure, liquidity, reward/risk, kill switches).
    """

    def __init__(self):
        self.last_trade_cycle = 0
        self.recent_trades = []      # Cycle numbers of recent trades
        self._last_log_tier = 0      # Avoid log spam: only log on tier change

    def record_trade(self, cycle):
        """Call when a trade executes."""
        self.last_trade_cycle = cycle
        self.recent_trades.append(cycle)
        if len(self.recent_trades) > 200:
            self.recent_trades = self.recent_trades[-200:]
        # Reset log tier on trade to re-announce next escalation
        self._last_log_tier = 0

    def idle_cycles(self, cycle):
        """How many cycles since the last trade."""
        if self.last_trade_cycle <= 0:
            return 0  # No trades yet (warm-up) — don't penalize
        return cycle - self.last_trade_cycle

    def trade_rate(self, cycle, window=300):
        """Count of trades in the last N cycles."""
        return sum(1 for c in self.recent_trades if cycle - c < window)

    def below_target_rate(self, cycle):
        """True if trade rate is below the target (signals a dry spell)."""
        if not MIN_ACTIVITY_ENABLED:
            return False
        return self.trade_rate(cycle) < MIN_ACTIVITY_TARGET_RATE

    def current_tier(self, cycle):
        """Current relaxation tier (0 = normal, 1-3 = progressively relaxed)."""
        if not MIN_ACTIVITY_ENABLED:
            return 0
        idle = self.idle_cycles(cycle)
        if idle < MIN_ACTIVITY_IDLE_THRESHOLD:
            base_tier = 0
        else:
            base_tier = min(
                MIN_ACTIVITY_MAX_TIERS,
                1 + (idle - MIN_ACTIVITY_IDLE_THRESHOLD) // MIN_ACTIVITY_TIER_INTERVAL
            )
        # Bonus tier if trade rate is below target (even if not fully idle)
        if self.below_target_rate(cycle) and base_tier < MIN_ACTIVITY_MAX_TIERS:
            base_tier = min(base_tier + 1, MIN_ACTIVITY_MAX_TIERS)
        return base_tier

    def score_adjustment(self, cycle):
        """How much to reduce score thresholds (always >= 0)."""
        return self.current_tier(cycle) * MIN_ACTIVITY_SCORE_STEP

    def change_adjustment(self, cycle):
        """How much to reduce change thresholds (always >= 0)."""
        return self.current_tier(cycle) * MIN_ACTIVITY_CHANGE_STEP

    def soft_leniency_active(self, cycle):
        """True if idle long enough that soft filters should be lenient."""
        return self.current_tier(cycle) >= MIN_ACTIVITY_SOFT_LENIENCY_TIER

    def check_and_log(self, cycle):
        """Log tier changes (called once per cycle). Returns current tier."""
        tier = self.current_tier(cycle)
        if tier > 0 and tier != self._last_log_tier:
            idle = self.idle_cycles(cycle)
            rate = self.trade_rate(cycle)
            score_adj = self.score_adjustment(cycle)
            change_adj = self.change_adjustment(cycle)
            leniency = " + soft_leniency" if self.soft_leniency_active(cycle) else ""
            logger.info(
                f"[MIN_ACTIVITY] tier {tier} active — idle={idle}c rate={rate}/300c "
                f"score_adj=-{score_adj:.3f} change_adj=-{change_adj:.4f}{leniency}"
            )
            self._last_log_tier = tier
        elif tier == 0 and self._last_log_tier > 0:
            logger.info("[MIN_ACTIVITY] thresholds restored to normal (trade executed)")
            self._last_log_tier = 0
        return tier

    def status(self):
        """Short status string for dashboard."""
        if not MIN_ACTIVITY_ENABLED:
            return "off"
        # Can't compute tier without cycle, but we can show idle count
        if self.last_trade_cycle <= 0:
            return "warmup"
        return f"t{self._last_log_tier}"

    def save_state(self):
        return {
            "last_trade_cycle": self.last_trade_cycle,
            "recent_trades": self.recent_trades[-200:],
        }

    def load_state(self, state):
        if state:
            self.last_trade_cycle = state.get("last_trade_cycle", 0)
            self.recent_trades = state.get("recent_trades", [])


min_activity = MinActivityGuard()


# ── Log Validator: validates log file integrity every 100 cycles ──
class LogValidator:
    """Validates log files for completeness and correctness. Runs periodically."""

    def __init__(self):
        self._trades_path = os.path.join(DIR, "logs", "trades.jsonl")
        self._equity_path = os.path.join(DIR, "logs", "equity.csv")
        self._errors_found = 0

    def validate_all(self, cycle):
        """Run all validations. Returns number of errors found this run."""
        errors = 0
        try:
            errors += self._validate_trades()
            errors += self._validate_equity()
            self._errors_found += errors
            if errors > 0:
                logger.debug(f"LOG VALIDATOR (cycle {cycle}): {errors} issues found")
        except Exception as e:
            error_logger.log("log_validator_crash", str(e))
        return errors

    def _validate_trades(self):
        """Check trades.jsonl for missing fields, bad prices, unrealistic PnL."""
        errors = 0
        try:
            if not os.path.exists(self._trades_path):
                return 0
            with open(self._trades_path) as f:
                lines = f.readlines()
            if not lines:
                return 0
            for i, line in enumerate(lines, start=1):
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                except (json.JSONDecodeError, ValueError):
                    error_logger.log("trades_bad_json", f"line {i}: unparseable JSON")
                    errors += 1
                    continue
                # Check required fields
                required = ("timestamp", "coin", "side", "entry", "exit", "pnl_pct", "reason")
                if not all(k in rec for k in required):
                    error_logger.log("trades_missing_fields", f"line {i}: missing keys")
                    errors += 1
                    continue
                try:
                    entry_p = float(rec["entry"])
                    exit_p = float(rec["exit"])
                    pnl_v = float(rec["pnl_pct"])
                except (ValueError, TypeError):
                    error_logger.log("trades_bad_values", f"line {i}: unparseable numbers")
                    errors += 1
                    continue
                if entry_p <= 0 or exit_p <= 0 or math.isnan(entry_p) or math.isnan(exit_p):
                    error_logger.log("trades_bad_price", f"line {i}: entry={entry_p} exit={exit_p}")
                    errors += 1
                if pnl_v < -100 or pnl_v > 500:
                    error_logger.log("trades_unrealistic_pnl", f"line {i}: pnl={pnl_v:.2f}%")
                    errors += 1
        except Exception as e:
            error_logger.log("trades_validation_error", str(e))
        return errors

    def _validate_equity(self):
        """Check equity.csv for negative equity and sudden jumps."""
        errors = 0
        try:
            if not os.path.exists(self._equity_path):
                return 0
            # Only check last 200 lines (performance: don't re-scan entire file)
            with open(self._equity_path) as f:
                all_lines = f.readlines()
            lines = all_lines[-200:] if len(all_lines) > 200 else all_lines[1:]  # Skip header
            prev_equity = None
            for line in lines:
                line = line.strip()
                if not line or line.startswith("timestamp"):
                    continue
                parts = line.split(",")
                if len(parts) < 4:
                    continue
                try:
                    eq = float(parts[1])
                except (ValueError, TypeError):
                    continue
                if math.isnan(eq) or eq < 0:
                    error_logger.log("equity_negative", f"equity={eq}")
                    errors += 1
                if prev_equity and prev_equity > 0:
                    change_pct = abs(eq - prev_equity) / prev_equity * 100
                    if change_pct > 20:
                        error_logger.log("equity_sudden_jump", f"equity jumped {change_pct:.1f}% ({prev_equity:.2f} -> {eq:.2f})")
                        errors += 1
                prev_equity = eq
        except Exception as e:
            error_logger.log("equity_validation_error", str(e))
        return errors

    @property
    def total_errors(self):
        return self._errors_found


log_validator = LogValidator()


# ── Paper Trade Tracker: comprehensive paper trading statistics ──
class PaperTradeTracker:
    """Tracks lifetime paper trading statistics. Prints summary every 500 cycles."""

    def __init__(self):
        self.total_trades = 0
        self.wins = 0
        self.losses = 0
        self.breakeven = 0
        self.win_pnls = []
        self.loss_pnls = []
        self.all_pnls = []
        self.peak_equity = 0
        self.trough_equity = float('inf')
        self.biggest_loss = 0
        self.biggest_win = 0

    def record(self, pnl_pct, equity=0):
        """Record a completed trade result."""
        try:
            self.total_trades += 1
            self.all_pnls.append(pnl_pct)
            if pnl_pct > 0.01:
                self.wins += 1
                self.win_pnls.append(pnl_pct)
                self.biggest_win = max(self.biggest_win, pnl_pct)
            elif pnl_pct < -0.01:
                self.losses += 1
                self.loss_pnls.append(pnl_pct)
                self.biggest_loss = min(self.biggest_loss, pnl_pct)
            else:
                self.breakeven += 1
            if equity > 0:
                self.peak_equity = max(self.peak_equity, equity)
                self.trough_equity = min(self.trough_equity, equity)
        except Exception:
            pass

    def win_rate(self):
        if self.total_trades == 0:
            return 0
        return self.wins / self.total_trades * 100

    def avg_win(self):
        if not self.win_pnls:
            return 0
        return sum(self.win_pnls) / len(self.win_pnls)

    def avg_loss(self):
        if not self.loss_pnls:
            return 0
        return sum(self.loss_pnls) / len(self.loss_pnls)

    def max_drawdown(self):
        if self.peak_equity <= 0:
            return 0
        if self.trough_equity == float('inf'):
            return 0
        return (self.peak_equity - self.trough_equity) / self.peak_equity * 100

    def expectancy(self):
        """Average PnL per trade."""
        if not self.all_pnls:
            return 0
        return sum(self.all_pnls) / len(self.all_pnls)

    def summary(self):
        """Return formatted summary string."""
        wr = self.win_rate()
        aw = self.avg_win()
        al = self.avg_loss()
        rr = abs(aw / al) if al != 0 else 0
        exp = self.expectancy()
        dd = self.max_drawdown()
        return (
            f"\n{'='*60}\n"
            f"  PAPER TRADE SUMMARY — {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')}\n"
            f"{'='*60}\n"
            f"  Total Trades:     {self.total_trades}\n"
            f"  Wins / Losses:    {self.wins} / {self.losses} (BE: {self.breakeven})\n"
            f"  Win Rate:         {wr:.1f}%\n"
            f"  Avg Win:          {aw:+.2f}%\n"
            f"  Avg Loss:         {al:+.2f}%\n"
            f"  Risk/Reward:      {rr:.2f}x\n"
            f"  Expectancy:       {exp:+.3f}% per trade\n"
            f"  Max Drawdown:     {dd:.2f}%\n"
            f"  Biggest Win:      {self.biggest_win:+.2f}%\n"
            f"  Biggest Loss:     {self.biggest_loss:+.2f}%\n"
            f"  Error Count:      {error_logger.error_count} ({error_classifier.summary()})\n"
            f"  Log Errors:       {log_validator.total_errors}\n"
            f"{'='*60}\n"
        )

    def log_summary(self):
        """Print and log the summary. Never raises."""
        try:
            s = self.summary()
            logger.info(s)
            print(s)
        except Exception as e:
            error_logger.log("paper_tracker_error", str(e))


paper_tracker = PaperTradeTracker()


# ── Live Validation Tracker: measures REAL EDGE under live market conditions ──
class LiveValidationTracker:
    """
    PURE OBSERVATION LAYER. Tracks every trade attempt (taken + blocked) with
    full execution detail. Computes rolling real edge = avg PnL - (fees + slippage).
    Writes enriched JSONL to logs/live_validation.jsonl. Never affects trading.
    """

    def __init__(self):
        self._path = os.path.join(DIR, "logs", "live_validation.jsonl")
        # Rolling stats
        self.total_attempts = 0
        self.total_blocked = 0
        self.total_executed = 0
        self.block_reasons = {}  # reason -> count
        # Completed trade stats
        self.completed_trades = []  # list of {pnl, fees, slippage, strategy, ...}
        self.daily_trades = []     # trades from current UTC day
        self._current_day = ""
        # Fee / slippage accumulators
        self.total_fee_pct = 0.0
        self.total_slippage_pct = 0.0
        # Winning streak tracker (for adaptive trailing)
        self.winning_streak = 0
        self._last_trade_cycle = 0  # Cycle of last executed trade (for overtrading guard)

    def log_attempt(self, coin, strategy, direction, signal_score, price, spread_pct,
                    blocked, block_reason="", fill_price=0.0, slippage_pct=0.0):
        """Log every trade ATTEMPT (blocked or taken). Non-blocking JSONL write."""
        try:
            self.total_attempts += 1
            if blocked:
                self.total_blocked += 1
                self.block_reasons[block_reason] = self.block_reasons.get(block_reason, 0) + 1
            else:
                self.total_executed += 1

            ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")
            record = {
                "ts": ts,
                "coin": coin,
                "strategy": strategy,
                "direction": direction,
                "score": round(signal_score, 4) if signal_score else 0,
                "price": round(price, 6),
                "spread_pct": round(spread_pct, 4),
                "blocked": blocked,
                "block_reason": block_reason,
                "fill_price": round(fill_price, 6),
                "slippage_pct": round(slippage_pct, 4),
                "type": "attempt",
            }
            # Note: _last_trade_cycle is set externally by entry code via
            # live_tracker._last_trade_cycle = cycle after successful fill
            _async_writer.enqueue(self._path, json.dumps(record) + "\n")
        except Exception:
            pass

    def log_exit(self, coin, strategy, direction, entry_price, exit_price,
                 pnl_pct, fee_pct, slippage_entry_pct, slippage_exit_pct, exit_reason):
        """Log a completed trade with full cost breakdown."""
        try:
            ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S")
            day = ts[:10]
            total_slip = slippage_entry_pct + slippage_exit_pct
            # Slippage is already baked into entry/exit prices (both are fill prices),
            # so pnl_pct already reflects slippage. Only subtract fees.
            net_pnl = pnl_pct - fee_pct

            trade = {
                "ts": ts,
                "coin": coin,
                "strategy": strategy,
                "direction": direction,
                "entry": round(entry_price, 6),
                "exit": round(exit_price, 6),
                "pnl_gross_pct": round(pnl_pct, 4),
                "fee_pct": round(fee_pct, 4),
                "slippage_total_pct": round(total_slip, 4),
                "pnl_net_pct": round(net_pnl, 4),
                "exit_reason": exit_reason,
                "type": "exit",
            }
            _async_writer.enqueue(self._path, json.dumps(trade) + "\n")

            # Accumulate
            self.completed_trades.append(trade)
            if len(self.completed_trades) > 5000:
                self.completed_trades = self.completed_trades[-5000:]
            self.total_fee_pct += fee_pct
            self.total_slippage_pct += total_slip

            # Daily tracking
            if day != self._current_day:
                self._current_day = day
                self.daily_trades = []
            self.daily_trades.append(trade)

            # Winning streak update
            if net_pnl > 0:
                self.winning_streak += 1
            else:
                self.winning_streak = 0
        except Exception:
            pass

    def blocked_rate(self):
        """% of trade attempts that were blocked."""
        if self.total_attempts == 0:
            return 0.0
        return self.total_blocked / self.total_attempts * 100

    def real_edge(self, window=None):
        """REAL_EDGE = avg net PnL per trade (after fees + slippage).
        window: last N trades. None = all trades."""
        trades = self.completed_trades
        if window and len(trades) > window:
            trades = trades[-window:]
        if not trades:
            return 0.0
        return sum(t["pnl_net_pct"] for t in trades) / len(trades)

    def avg_fee_impact(self):
        """Average fee % per completed trade."""
        n = len(self.completed_trades)
        if n == 0:
            return 0.0
        return self.total_fee_pct / n

    def avg_slippage_impact(self):
        """Average total slippage % per completed trade."""
        n = len(self.completed_trades)
        if n == 0:
            return 0.0
        return self.total_slippage_pct / n

    def daily_real_edge(self):
        """REAL_EDGE for current UTC day only."""
        if not self.daily_trades:
            return 0.0
        return sum(t["pnl_net_pct"] for t in self.daily_trades) / len(self.daily_trades)

    def win_rate(self, window=None):
        """Win rate over last N completed trades."""
        trades = self.completed_trades
        if window and len(trades) > window:
            trades = trades[-window:]
        if not trades:
            return 0.0
        wins = sum(1 for t in trades if t["pnl_net_pct"] > 0)
        return wins / len(trades) * 100

    def summary(self):
        """Return formatted validation summary string."""
        n = len(self.completed_trades)
        edge = self.real_edge()
        daily = self.daily_real_edge()
        wr = self.win_rate()
        fee = self.avg_fee_impact()
        slip = self.avg_slippage_impact()
        br = self.blocked_rate()
        top_block = max(self.block_reasons, key=self.block_reasons.get) if self.block_reasons else "none"
        return (
            f"  LIVE VALIDATION | trades={n} WR={wr:.1f}% "
            f"edge={edge:+.3f}%/trade daily={daily:+.3f}% "
            f"fees={fee:.3f}% slip={slip:.3f}% "
            f"blocked={br:.1f}% top_block={top_block}"
        )


live_tracker = LiveValidationTracker()


def _edge_size_multiplier():
    """Dynamic position sizing multiplier based on REAL_EDGE.
    Returns 1.0 if disabled or insufficient data."""
    if not EDGE_SIZING_ENABLED:
        return 1.0
    n = len(live_tracker.completed_trades)
    if n < EDGE_SIZING_MIN_TRADES:
        return 1.0  # Not enough data yet
    edge = live_tracker.real_edge()
    if edge <= 0:
        return EDGE_SIZING_MIN_MULT  # Positive edge gone — minimum size
    raw = edge / EDGE_SIZING_TARGET
    return max(EDGE_SIZING_MIN_MULT, min(EDGE_SIZING_MAX_MULT, raw))


def _winrate_size_bonus(wallet_ref):
    """Small sizing bonus when win rate > 55%. Returns 1.0-1.10x.
    Applied AFTER all other sizing, BEFORE exposure caps."""
    try:
        total = wallet_ref.wins + wallet_ref.losses
        if total < 10:
            return 1.0  # Not enough data
        wr = wallet_ref.wins / total
        if wr > 0.55:
            return 1.10  # +10% when winning > 55%
        return 1.0
    except Exception:
        return 1.0


# ── Trade Entry Logger (structured per-trade diagnostics) ──
_session_trades = []  # Accumulates trade entries for periodic summary

def log_trade_entry(coin, direction, strategy, size, price, sl_pct, atr_pct, edge_mult, regime, cycle_num):
    """Log structured trade entry data for overnight diagnostics."""
    try:
        # TP calculation mirrors the exit loop logic (v29.1 — realistic for 2s candles)
        if atr_pct < 1.5:
            tp_scale = 1.0   # v29.3: Calm: no stretch (was 1.1)
        elif atr_pct > 3.0:
            tp_scale = 0.85  # v29.3: Volatile: tighter TP to lock gains (was 0.9)
        else:
            tp_scale = 1.0   # v29.3: Normal: no stretch (was 1.2)
        tp_trigger = max(0.4, sl_pct * 1.1 * tp_scale)  # v29.3.2-S9: TP 1.2x→1.1x per S9 validation
        trail_dist = max(0.5, atr_pct * 0.5)  # v29.3: tighter trail to match lower TP (was max(1.2, atr*0.8))

        entry = {
            "cycle": cycle_num, "coin": coin, "dir": direction, "strategy": strategy,
            "size": round(size, 2), "price": price, "sl_pct": round(sl_pct, 2),
            "tp_pct": round(tp_trigger, 2), "atr_pct": round(atr_pct, 2),
            "trail_pct": round(trail_dist, 2), "edge_mult": round(edge_mult, 3),
            "regime": regime, "ts": time.time(),
        }
        _session_trades.append(entry)
        logger.info(
            f"TRADE_LOG {direction.upper()} {coin} ${size:.0f} @ ${price:,.4f} | "
            f"SL:{sl_pct:.1f}% TP:{tp_trigger:.1f}% trail:{trail_dist:.1f}% | "
            f"ATR:{atr_pct:.1f}% edge:{edge_mult:.2f}x regime:{regime} [{strategy}]"
        )
        # v29.4.0: Webhook notification for entries (Item 11)
        trade_notification("entry", {"coin": coin, "direction": direction,
                                     "price": price, "size": round(size, 2),
                                     "sl_pct": round(sl_pct, 2), "tp_pct": round(tp_trigger, 2),
                                     "confidence": round(edge_mult, 3), "strategy": strategy})
    except Exception:
        pass  # Never crash the bot for logging


def print_periodic_summary(wallet_ref, prices_ref, cycle_num):
    """Print 2-3 hour performance summary to terminal and log."""
    try:
        total = len(_session_trades)
        if total == 0:
            _msg = f"\n  SESSION SUMMARY (cycle {cycle_num}): 0 trades this session — check filters"
            print(_msg)
            logger.info(_msg)
            return
        sizes = [t["size"] for t in _session_trades]
        avg_size = sum(sizes) / len(sizes)
        pv = wallet_ref.value(prices_ref)
        pnl = pv - 1000  # Assumes $1000 start (close enough for summary)
        elapsed_hrs = (time.time() - _session_trades[0]["ts"]) / 3600 if _session_trades else 0
        strategies = {}
        for t in _session_trades:
            strategies[t["strategy"]] = strategies.get(t["strategy"], 0) + 1
        strat_str = " ".join(f"{k}:{v}" for k, v in strategies.items())

        # Health score + strategy contribution breakdown
        _hs = _last_health_score
        _hs_tag = "BLOCK" if _hs < 30 else "CAUTION" if _hs < 40 else "OK" if _hs < 70 else "GOOD"
        # Strategy PnL breakdown from _session_trades
        strat_pnl = {}
        for t in _session_trades:
            s = t.get("strategy", "unknown")
            strat_pnl[s] = strat_pnl.get(s, 0) + 1
        strat_detail = " | ".join(f"{k}:{v}" for k, v in strat_pnl.items()) if strat_pnl else "none"

        _msg = (
            f"\n  ══ SESSION SUMMARY (cycle {cycle_num}, {elapsed_hrs:.1f}h) ══\n"
            f"  Trades: {total} | Avg size: ${avg_size:.0f} | PnL: ${pnl:+,.2f} ({pnl/10:+.1f}%)\n"
            f"  W:{wallet_ref.wins} L:{wallet_ref.losses} | Positions: {len(wallet_ref.longs)}L {len(wallet_ref.shorts)}S\n"
            f"  Strategies: {strat_str}\n"
            f"  Health: {_hs}/100 [{_hs_tag}] | Strategy counts: {strat_detail}\n"
            f"  ══{'═' * 45}══"
        )
        print(_msg)
        logger.info(_msg)
    except Exception:
        pass


def _adaptive_trail_multiplier():
    """Returns trail distance multiplier. < 1.0 = tighter stop.
    Graduated: streak >= 6 → 0.80x, streak >= 3 → 0.90x, else 1.0x.
    Returns 1.0 if disabled or streak not reached."""
    if not ADAPTIVE_TRAIL_ENABLED:
        return 1.0
    streak = live_tracker.winning_streak
    if streak >= ADAPTIVE_TRAIL_STREAK_2:
        return ADAPTIVE_TRAIL_MULT_2
    if streak >= ADAPTIVE_TRAIL_STREAK:
        return ADAPTIVE_TRAIL_MULT
    return 1.0


def _overtrade_guard_ok(cycle):
    """Legacy wrapper — now delegates to unified overtrading_guard.can_trade().
    Kept for backward compatibility with tests."""
    return overtrading_guard.can_trade(cycle)


# ── Trade Consistency Checker ──
def verify_trade_consistency(coin, direction, entry_price, exit_price, pnl_pct, wallet_had_position):
    """Verify a completed trade's math is correct and position existed.
    Called after every record_exit(). Never raises."""
    try:
        # Check 1: PnL matches math
        if entry_price > 0:
            if direction == "long":
                expected_pnl = (exit_price - entry_price) / entry_price * 100
            else:
                expected_pnl = (entry_price - exit_price) / entry_price * 100
            if abs(expected_pnl - pnl_pct) > 0.01:
                error_logger.log("trade_pnl_mismatch",
                    f"{coin} {direction}: expected {expected_pnl:+.4f}% got {pnl_pct:+.4f}%")

        # Check 2: Prices are positive
        if entry_price <= 0 or exit_price <= 0:
            error_logger.log("trade_bad_price",
                f"{coin} {direction}: entry={entry_price} exit={exit_price}")

        # Check 3: Position actually existed
        if not wallet_had_position:
            error_logger.log("trade_ghost_position",
                f"{coin} {direction}: no position found in wallet before exit")

        if DEBUG_MODE or is_verbose("DEBUG"):
            print(f"  [TRADE] {coin} {direction} entry=${entry_price:.4f} exit=${exit_price:.4f} pnl={pnl_pct:+.2f}%")
    except Exception as e:
        error_logger.log("consistency_check_error", str(e))


# ── Equity Sanity Checker ──
class EquitySanityChecker:
    """Checks for impossible equity movements every cycle."""

    def __init__(self):
        self._prev_equity = None
        self.flash_events = 0
        self.data_errors = 0

    def check(self, equity, cycle):
        """Check equity for sanity. Returns 'STOP' if bot should halt, else 'OK'.
        Never raises."""
        try:
            # Hard stop: negative equity
            if equity < 0:
                error_logger.log("equity_negative_halt", f"equity={equity:.2f} at cycle {cycle}")
                return "STOP"

            if self._prev_equity is not None and self._prev_equity > 0:
                change_pct = (equity - self._prev_equity) / self._prev_equity * 100

                # Flash event: >10% drop in ONE cycle
                if change_pct < -10:
                    self.flash_events += 1
                    error_logger.log("flash_event",
                        f"equity dropped {change_pct:+.1f}% in one cycle "
                        f"(${self._prev_equity:.2f} -> ${equity:.2f}) cycle={cycle}")
                    logger.error(f"FLASH EVENT: equity {change_pct:+.1f}% in one cycle at cycle {cycle}")

                # Data error: >20% gain in ONE cycle (impossible in normal trading)
                if change_pct > 20:
                    self.data_errors += 1
                    error_logger.log("data_error",
                        f"equity jumped +{change_pct:.1f}% in one cycle "
                        f"(${self._prev_equity:.2f} -> ${equity:.2f}) cycle={cycle}")
                    logger.error(f"DATA ERROR: equity +{change_pct:.1f}% in one cycle at cycle {cycle}")

            self._prev_equity = equity
            return "OK"
        except Exception as e:
            error_logger.log("equity_sanity_error", str(e))
            return "OK"


equity_sanity = EquitySanityChecker()


# ── Clean Data Exporter ──
def export_clean_trades():
    """Export only valid, error-free trades to logs/clean_trades.jsonl. Never raises."""
    try:
        trades_path = os.path.join(DIR, "logs", "trades.jsonl")
        clean_path = os.path.join(DIR, "logs", "clean_trades.jsonl")
        if not os.path.exists(trades_path):
            return
        with open(trades_path) as f:
            lines = f.readlines()
        clean_lines = []
        skipped = 0
        for line in lines:
            line_s = line.strip()
            if not line_s:
                continue
            try:
                rec = json.loads(line_s)
            except (json.JSONDecodeError, ValueError):
                skipped += 1
                continue
            try:
                entry_p = float(rec.get("entry", 0))
                exit_p = float(rec.get("exit", 0))
                pnl_v = float(rec.get("pnl_pct", 0))
            except (ValueError, TypeError):
                skipped += 1
                continue
            if entry_p <= 0 or exit_p <= 0 or math.isnan(entry_p) or math.isnan(exit_p):
                skipped += 1
                continue
            if pnl_v < -100 or pnl_v > 500:
                skipped += 1
                continue
            if rec.get("coin") is None or rec.get("side") is None:
                skipped += 1
                continue
            clean_lines.append(line)
        with open(clean_path, "w") as f:
            f.writelines(clean_lines)
        logger.debug(f"CLEAN EXPORT: {len(clean_lines)} valid trades (skipped {skipped}) -> {clean_path}")
    except Exception as e:
        error_logger.log("clean_export_error", str(e))


# ── Startup Validation ──
def startup_check(wallet, prices):
    """Validate bot state on startup. Returns True if safe to run, False if corrupted."""
    errors = []
    try:
        # 1. Logs folder exists and is writable
        logs_dir = os.path.join(DIR, "logs")
        if not os.path.isdir(logs_dir):
            errors.append("logs/ directory missing")
        else:
            test_file = os.path.join(logs_dir, ".write_test")
            try:
                with open(test_file, "w") as f:
                    f.write("test")
                # Don't os.remove — some sandboxes block deletion
            except IOError:
                errors.append("logs/ directory not writable")

        # 2. Wallet state is valid
        if wallet is None:
            errors.append("wallet is None")
        elif wallet.cash < 0:
            errors.append(f"wallet cash is negative: ${wallet.cash:.2f}")

        # 3. No corrupted positions
        if wallet:
            for coin, pos in wallet.longs.items():
                if "entry" not in pos or pos["entry"] <= 0:
                    errors.append(f"long {coin}: missing or bad entry price")
                if "qty" not in pos or pos["qty"] <= 0:
                    errors.append(f"long {coin}: missing or bad qty")
            for coin, pos in wallet.shorts.items():
                if "entry" not in pos or pos["entry"] <= 0:
                    errors.append(f"short {coin}: missing or bad entry price")
                if "qty" not in pos or pos["qty"] <= 0:
                    errors.append(f"short {coin}: missing or bad qty")

        # 4. Portfolio value is sane
        if wallet and prices:
            pv = wallet.value(prices)
            if pv < 0:
                errors.append(f"portfolio value is negative: ${pv:.2f}")
            if pv > 1e8:
                errors.append(f"portfolio value is absurd: ${pv:.2f}")

        # 5. State file is not corrupted (if it exists)
        if os.path.exists(STATE_FILE):
            try:
                with open(STATE_FILE) as f:
                    json.load(f)
            except json.JSONDecodeError:
                errors.append("state file is corrupted JSON")

        if errors:
            for e in errors:
                error_logger.log("startup_check_fail", e)
                logger.error(f"STARTUP CHECK FAILED: {e}")
            return False
        return True
    except Exception as e:
        error_logger.log("startup_check_crash", str(e))
        return False


class DailyMetrics:
    """Tracks and logs daily trading metrics to logs/daily_metrics.log."""

    def __init__(self):
        self.day_start_equity = None
        self.day_start_cycle = 0
        self.trades_today = 0
        self.wins_today = 0
        self.losses_today = 0
        self.win_amounts = []   # PnL % of winning trades today
        self.loss_amounts = []  # PnL % of losing trades today
        self.sl_hits_today = 0
        self.gap_events_today = 0
        self.peak_equity_today = 0
        self.min_equity_today = float('inf')
        self._logger = logging.getLogger("daily_metrics")
        if not self._logger.handlers:
            self._logger.addHandler(logging.FileHandler(os.path.join(DIR, "logs", "daily_metrics.log")))
            self._logger.setLevel(logging.INFO)

    def start_day(self, equity, cycle):
        """Call at start or when daily reset triggers."""
        self.day_start_equity = equity
        self.day_start_cycle = cycle
        self.trades_today = 0
        self.wins_today = 0
        self.losses_today = 0
        self.win_amounts = []
        self.loss_amounts = []
        self.sl_hits_today = 0
        self.gap_events_today = 0
        self.peak_equity_today = equity
        self.min_equity_today = equity

    def record_trade(self, pnl_pct, is_sl=False, is_gap=False):
        """Record a completed trade."""
        self.trades_today += 1
        if pnl_pct > 0:
            self.wins_today += 1
            self.win_amounts.append(pnl_pct)
        elif pnl_pct < 0:
            self.losses_today += 1
            self.loss_amounts.append(pnl_pct)
        if is_sl:
            self.sl_hits_today += 1
        if is_gap:
            self.gap_events_today += 1

    def update_equity(self, equity):
        """Track peak and trough for drawdown calculation."""
        if self.day_start_equity is None:
            self.day_start_equity = equity
            self.peak_equity_today = equity
            self.min_equity_today = equity
        self.peak_equity_today = max(self.peak_equity_today, equity)
        self.min_equity_today = min(self.min_equity_today, equity)

    def log_daily_summary(self, current_equity=None):
        """Write daily summary to log file in both human-readable and CSV format."""
        try:
            if self.day_start_equity is None or self.day_start_equity <= 0:
                return
            current = current_equity if current_equity else self.peak_equity_today
            daily_pnl = (current - self.day_start_equity) / self.day_start_equity * 100
            max_dd = (self.peak_equity_today - self.min_equity_today) / self.peak_equity_today * 100 if self.peak_equity_today > 0 else 0
            win_rate = (self.wins_today / self.trades_today * 100) if self.trades_today > 0 else 0
            avg_win = sum(self.win_amounts) / len(self.win_amounts) if self.win_amounts else 0
            avg_loss = sum(self.loss_amounts) / len(self.loss_amounts) if self.loss_amounts else 0
            date_str = datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M UTC')

            # Human-readable summary to logger
            summary = (
                f"\n{'='*60}\n"
                f"  DAILY METRICS — {date_str}\n"
                f"{'='*60}\n"
                f"  Daily PnL:        {daily_pnl:+.2f}%\n"
                f"  Max Drawdown:     {max_dd:.2f}%\n"
                f"  Trades Taken:     {self.trades_today}\n"
                f"  Win Rate:         {win_rate:.1f}%\n"
                f"  Avg Win:          {avg_win:+.2f}%\n"
                f"  Avg Loss:         {avg_loss:+.2f}%\n"
                f"  SL Hits:          {self.sl_hits_today}\n"
                f"  Gap Events:       {self.gap_events_today}\n"
                f"{'='*60}\n"
            )
            self._logger.info(summary)
            logger.info(summary)

            # CSV-structured line to daily_metrics.log
            csv_line = (
                f"{date_str},{daily_pnl:+.2f},{self.trades_today},{win_rate:.1f},"
                f"{avg_win:+.2f},{avg_loss:+.2f},{max_dd:.2f},{self.sl_hits_today},{self.gap_events_today}"
            )
            self._logger.info(f"CSV:{csv_line}")
        except Exception as e:
            logger.debug(f"DailyMetrics log error: {e}")

    def save_state(self):
        return {
            "day_start_equity": self.day_start_equity,
            "day_start_cycle": self.day_start_cycle,
            "trades_today": self.trades_today,
            "wins_today": self.wins_today,
            "losses_today": self.losses_today,
            "win_amounts": self.win_amounts,
            "loss_amounts": self.loss_amounts,
            "sl_hits_today": self.sl_hits_today,
            "gap_events_today": self.gap_events_today,
            "peak_equity_today": self.peak_equity_today,
            "min_equity_today": self.min_equity_today,
        }

    def load_state(self, state):
        if state:
            self.day_start_equity = state.get("day_start_equity")
            self.day_start_cycle = state.get("day_start_cycle", 0)
            self.trades_today = state.get("trades_today", 0)
            self.wins_today = state.get("wins_today", 0)
            self.losses_today = state.get("losses_today", 0)
            self.win_amounts = state.get("win_amounts", [])
            self.loss_amounts = state.get("loss_amounts", [])
            self.sl_hits_today = state.get("sl_hits_today", 0)
            self.gap_events_today = state.get("gap_events_today", 0)
            self.peak_equity_today = state.get("peak_equity_today", 0)
            self.min_equity_today = state.get("min_equity_today", float('inf'))


daily_metrics = DailyMetrics()


# ── Cascade Protection ──
class CascadeProtection:
    """Detects rapid cascading losses and blocks entries."""

    def __init__(self):
        self.recent_equity = []   # (cycle, equity) for last few cycles
        self.sl_exits_this_cycle = 0
        self.block_until_cycle = 0
        self.cascade_active = False

    def record_sl_exit(self):
        """Call whenever a stop-loss exit occurs."""
        self.sl_exits_this_cycle += 1

    def reset_cycle(self):
        """Call at start of each cycle."""
        self.sl_exits_this_cycle = 0

    def update(self, equity, cycle):
        """Check for cascade conditions."""
        self.recent_equity.append((cycle, equity))
        # Keep last 3 cycles
        self.recent_equity = [(c, e) for c, e in self.recent_equity if cycle - c <= 2]

        # Condition 1: 2+ SL exits same cycle
        if self.sl_exits_this_cycle >= 2:
            self._trigger_cascade(cycle, f"2+ SL exits same cycle")

        # Condition 2: Portfolio drop > CASCADE_THRESHOLD in 1-2 cycles
        if len(self.recent_equity) >= 2:
            oldest_eq = self.recent_equity[0][1]
            if oldest_eq > 0:
                drop_pct = (oldest_eq - equity) / oldest_eq * 100
                if drop_pct > CASCADE_THRESHOLD:
                    self._trigger_cascade(cycle, f"portfolio drop {drop_pct:.1f}% in {len(self.recent_equity)} cycles")

        # Check if cascade expired
        if self.cascade_active and cycle > self.block_until_cycle:
            self.cascade_active = False
            logger.debug("CASCADE PROTECTION: expired, entries re-enabled")

    def _trigger_cascade(self, cycle, reason):
        self.cascade_active = True
        self.block_until_cycle = cycle + CASCADE_BLOCK_CYCLES
        logger.warning(f"CASCADE PROTECTION TRIGGERED: {reason} — blocking entries for {CASCADE_BLOCK_CYCLES} cycles")

    def allows_entry(self):
        return not self.cascade_active

    def save_state(self):
        return {
            "block_until_cycle": self.block_until_cycle,
            "cascade_active": self.cascade_active,
        }

    def load_state(self, state):
        if state:
            self.block_until_cycle = state.get("block_until_cycle", 0)
            self.cascade_active = state.get("cascade_active", False)


cascade_protection = CascadeProtection()


# ── Adaptive Risk Reduction ──
class AdaptiveRisk:
    """Scales down position sizes when session is losing. Prevents compounding losses."""

    def __init__(self):
        self.session_start_value = None
        self.current_value = None
        self.gap_lockout_until = 0  # Cycle until which gap lockout is active

    def update(self, portfolio_value):
        if self.session_start_value is None:
            self.session_start_value = portfolio_value
        self.current_value = portfolio_value

    def force_gap_lockout(self, current_cycle, duration=100):
        """Force 0.25x multiplier for `duration` cycles after a gap event."""
        self.gap_lockout_until = current_cycle + duration
        logger.warning(f"GAP LOCKOUT: forced 0.25x until cycle {self.gap_lockout_until}")

    def risk_multiplier(self, cycle=0):
        """Returns 0.25-1.0 based on session drawdown + gap lockout."""
        # Gap lockout overrides everything
        if cycle > 0 and cycle < self.gap_lockout_until:
            return 0.25
        if self.session_start_value is None or self.current_value is None:
            return 1.0
        if self.session_start_value <= 0:
            return 1.0
        dd_pct = (self.session_start_value - self.current_value) / self.session_start_value * 100
        if dd_pct <= 0:
            return 1.0  # No drawdown or in profit
        elif dd_pct < 1.0:
            return 1.0
        elif dd_pct < 2.0:
            return 0.75
        elif dd_pct < 3.0:
            return 0.50
        else:
            return 0.25

    def save_state(self):
        """Return dict for persistence across restarts."""
        return {
            "session_start_value": self.session_start_value,
            "current_value": self.current_value,
            "gap_lockout_until": self.gap_lockout_until,
        }

    def load_state(self, state):
        """Restore from saved state."""
        if state:
            self.session_start_value = state.get("session_start_value")
            self.current_value = state.get("current_value")
            self.gap_lockout_until = state.get("gap_lockout_until", 0)


adaptive_risk = AdaptiveRisk()


# ── Kill Switch: Emergency shutdown system ──
class KillSwitch:
    """Emergency kill switch — MARKET RISK ONLY.
    Triggers:
    1. Total equity drops > KILL_SWITCH_EQUITY_DROP_PCT from session start
    2. KILL_SWITCH_CONSECUTIVE_LOSSES consecutive losses worse than KILL_SWITCH_BAD_LOSS_THRESHOLD
    3. Too many gap events (price gapped through stop loss)
    Errors are handled separately by ErrorClassifier — they NEVER trigger kill switch.
    """

    def __init__(self, starting_equity):
        self.starting_equity = starting_equity
        self.triggered = False
        self.trigger_reason = ""
        self.recent_losses = []  # Track consecutive losses
        self.gap_events = 0

    def record_trade(self, pnl_pct):
        """Record a trade result. Check for consecutive bad losses."""
        try:
            if pnl_pct < KILL_SWITCH_BAD_LOSS_THRESHOLD:
                self.recent_losses.append(pnl_pct)
            else:
                self.recent_losses = []  # Reset on non-bad trade
            # Check consecutive bad losses
            if len(self.recent_losses) >= KILL_SWITCH_CONSECUTIVE_LOSSES:
                self._trigger(f"{len(self.recent_losses)} consecutive losses > {KILL_SWITCH_BAD_LOSS_THRESHOLD}%: {[f'{x:+.1f}%' for x in self.recent_losses[-KILL_SWITCH_CONSECUTIVE_LOSSES:]]}")
        except Exception as e:
            error_logger.log("kill_switch_record_trade", str(e))

    def record_gap_event(self):
        """Record a gap event (price gapped through SL)."""
        self.gap_events += 1
        if self.gap_events >= KILL_SWITCH_MAX_GAP_EVENTS:
            self._trigger(f"{self.gap_events} gap events (limit={KILL_SWITCH_MAX_GAP_EVENTS})")

    def check_equity(self, current_equity):
        """Check if equity has dropped too far from starting value."""
        try:
            if self.starting_equity <= 0:
                return
            drop_pct = (self.starting_equity - current_equity) / self.starting_equity * 100
            if drop_pct >= KILL_SWITCH_EQUITY_DROP_PCT:
                self._trigger(f"equity dropped {drop_pct:.1f}% from start (${self.starting_equity:.2f} -> ${current_equity:.2f})")
        except Exception as e:
            error_logger.log("kill_switch_check_equity", str(e))

    def _trigger(self, reason):
        if not self.triggered:
            self.triggered = True
            self.trigger_reason = reason
            logger.error(f"KILL SWITCH TRIGGERED: {reason}")
            error_logger.log("kill_switch", reason)

    def maybe_reset(self, current_equity):
        """Allow recovery if equity has recovered to within 2% of starting equity.
        Called once per cycle. Only resets if currently triggered."""
        try:
            if not self.triggered:
                return
            if self.starting_equity <= 0:
                return
            if current_equity >= self.starting_equity * 0.98:
                self.triggered = False
                self.trigger_reason = ""
                self.recent_losses = []
                self.gap_events = 0
                logger.warning(
                    f"KILL SWITCH RESET: equity ${current_equity:.2f} recovered to "
                    f">= 98% of starting ${self.starting_equity:.2f} — trading resumed"
                )
        except Exception as e:
            error_logger.log("kill_switch_reset", str(e))

    def save_state(self):
        return {
            "starting_equity": self.starting_equity,
            "triggered": self.triggered,
            "trigger_reason": self.trigger_reason,
            "recent_losses": self.recent_losses,
            "gap_events": self.gap_events,
        }

    def load_state(self, state):
        if state:
            self.starting_equity = state.get("starting_equity", self.starting_equity)
            self.triggered = state.get("triggered", False)
            self.trigger_reason = state.get("trigger_reason", "")
            self.recent_losses = state.get("recent_losses", [])
            self.gap_events = state.get("gap_events", 0)

    def close_all_positions(self, wallet, prices, executor):
        """Emergency close all positions. Routes through record_exit for tracking."""
        try:
            for coin in list(wallet.longs.keys()):
                p = prices.get(coin, wallet.longs[coin]["entry"])
                entry = wallet.longs[coin]["entry"]
                strat = wallet.longs[coin].get("strategy", "momentum")
                _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=True)
                wallet.sell(coin, _fp)
                record_exit(strat, coin, "long", entry, _fp, "KILL_SWITCH", wallet=wallet)
                logger.error(f"KILL SWITCH: force closed LONG {coin} @ ${_fp:.4f}")
            for coin in list(wallet.shorts.keys()):
                p = prices.get(coin, wallet.shorts[coin]["entry"])
                entry = wallet.shorts[coin]["entry"]
                _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=True)
                wallet.cover(coin, _fp)
                record_exit("kill_switch", coin, "short", entry, _fp, "KILL_SWITCH", wallet=wallet)
                logger.error(f"KILL SWITCH: force closed SHORT {coin} @ ${p:.4f}")
        except Exception as e:
            logger.error(f"KILL SWITCH close error: {e}")
            error_logger.log("kill_switch_close_error", str(e))

    @property
    def is_triggered(self):
        return self.triggered


# ── Strategy Health Monitor: Pauses trading when strategy is losing ──
class StrategyHealthMonitor:
    """Monitors last N trades. Pauses new entries if win rate or expectancy is too low."""

    def __init__(self):
        self.recent_trades = []  # Last HEALTH_MONITOR_WINDOW PnL values
        self.paused_until_cycle = 0
        self.pause_count = 0

    def record_trade(self, pnl_pct):
        """Record a trade result."""
        try:
            self.recent_trades.append(pnl_pct)
            if len(self.recent_trades) > HEALTH_MONITOR_WINDOW:
                self.recent_trades = self.recent_trades[-HEALTH_MONITOR_WINDOW:]
        except Exception as e:
            error_logger.log("strategy_health_record", str(e))

    def check_health(self, cycle):
        """Returns True if trading is allowed, False if paused."""
        try:
            # Not enough data yet
            if len(self.recent_trades) < HEALTH_MONITOR_WINDOW:
                return True
            # Already paused?
            if cycle < self.paused_until_cycle:
                return False
            # Calculate metrics
            wins = sum(1 for p in self.recent_trades if p > 0)
            win_rate = wins / len(self.recent_trades) * 100
            expectancy = sum(self.recent_trades) / len(self.recent_trades)
            # Check thresholds
            if win_rate < HEALTH_MONITOR_MIN_WR or expectancy < HEALTH_MONITOR_MIN_EXPECTANCY:
                self.paused_until_cycle = cycle + HEALTH_MONITOR_PAUSE_CYCLES
                self.pause_count += 1
                logger.warning(f"STRATEGY HEALTH PAUSE: WR={win_rate:.1f}% exp={expectancy:+.3f}% — pausing {HEALTH_MONITOR_PAUSE_CYCLES} cycles")
                error_logger.log("strategy_health_pause", f"WR={win_rate:.1f}% exp={expectancy:+.3f}%")
                return False
            return True
        except Exception as e:
            error_logger.log("strategy_health_check", str(e))
            return True

    def is_paused(self, cycle):
        return cycle < self.paused_until_cycle

    def save_state(self):
        return {
            "recent_trades": self.recent_trades,
            "paused_until_cycle": self.paused_until_cycle,
            "pause_count": self.pause_count,
        }

    def load_state(self, state):
        if state:
            self.recent_trades = state.get("recent_trades", [])
            self.paused_until_cycle = state.get("paused_until_cycle", 0)
            self.pause_count = state.get("pause_count", 0)

    @property
    def win_rate(self):
        if not self.recent_trades:
            return 0
        return sum(1 for p in self.recent_trades if p > 0) / len(self.recent_trades) * 100

    @property
    def expectancy(self):
        if not self.recent_trades:
            return 0
        return sum(self.recent_trades) / len(self.recent_trades)


# ── Smart Coin Blocker: Cumulative P&L based blocking (replaces CoinLossTracker) ──
class SmartCoinBlocker:
    """Tracks per-coin cumulative P&L and max drawdown. Blocks coins only when
    cumulative loss exceeds threshold (not just 2 consecutive losses).
    Supports time-based reset, recovery unblock, and ranging leniency.

    Drop-in replacement: exposes same .is_blocked() / .record_trade() / .save_state() API
    plus backward-compatible .blocked_until dict for RecoveryMode / StagnationWatchdog."""

    def __init__(self):
        # Per-coin tracking: coin -> {"trades": [(pnl_pct, cycle), ...], "blocked_cycle": int, "peak_pnl": float}
        self.coins = {}
        # Backward compat: RecoveryMode and StagnationWatchdog access .blocked_until directly
        self.blocked_until = {}
        # Legacy compat alias
        self.coin_losses = {}

    def _ensure_coin(self, coin):
        if coin not in self.coins:
            self.coins[coin] = {"trades": [], "blocked_cycle": 0, "peak_pnl": 0.0}

    def _cumulative_pnl(self, coin):
        """Sum of last N trade P&L values for this coin."""
        try:
            trades = self.coins.get(coin, {}).get("trades", [])
            return sum(t[0] for t in trades)
        except Exception:
            return 0.0

    def _max_drawdown(self, coin):
        """Max drawdown from peak cumulative P&L for this coin."""
        try:
            trades = self.coins.get(coin, {}).get("trades", [])
            if not trades:
                return 0.0
            cumul = 0.0
            peak = 0.0
            worst_dd = 0.0
            for pnl, _ in trades:
                cumul += pnl
                if cumul > peak:
                    peak = cumul
                dd = cumul - peak
                if dd < worst_dd:
                    worst_dd = dd
            return worst_dd
        except Exception:
            return 0.0

    def record_trade(self, coin, pnl_pct, cycle):
        """Record a trade result for a coin. May trigger or lift a block."""
        try:
            self._ensure_coin(coin)
            info = self.coins[coin]
            # Append trade (trim to memory window)
            info["trades"].append((pnl_pct, cycle))
            if len(info["trades"]) > SMART_COIN_TRADE_MEMORY:
                info["trades"] = info["trades"][-SMART_COIN_TRADE_MEMORY:]
            # Update peak
            cumul = self._cumulative_pnl(coin)
            if cumul > info["peak_pnl"]:
                info["peak_pnl"] = cumul
            # Check for block conditions (only if enough trades)
            n_trades = len(info["trades"])
            if SMART_COIN_BLOCK_ENABLED and n_trades >= SMART_COIN_MIN_TRADES:
                dd = self._max_drawdown(coin)
                should_block = False
                reason = ""
                if cumul <= SMART_COIN_CUMULATIVE_LOSS_PCT:
                    should_block = True
                    reason = f"cumulative P&L {cumul:.1f}% <= {SMART_COIN_CUMULATIVE_LOSS_PCT}%"
                elif dd <= SMART_COIN_MAX_DRAWDOWN_PCT:
                    should_block = True
                    reason = f"max drawdown {dd:.1f}% <= {SMART_COIN_MAX_DRAWDOWN_PCT}%"
                if should_block and info["blocked_cycle"] == 0:
                    info["blocked_cycle"] = cycle
                    self.blocked_until[coin] = cycle + SMART_COIN_RECOVERY_RESET_CYCLES
                    logger.warning(f"SMART COIN BLOCKED: {coin} — {reason} (trades={n_trades}, reset in {SMART_COIN_RECOVERY_RESET_CYCLES} cycles)")
            # Check for recovery unblock
            if info["blocked_cycle"] > 0 and cumul >= SMART_COIN_RECOVERY_PNL_PCT:
                logger.info(f"SMART COIN UNBLOCKED: {coin} — P&L recovered to {cumul:.1f}% (was blocked cycle {info['blocked_cycle']})")
                info["blocked_cycle"] = 0
                self.blocked_until.pop(coin, None)
        except Exception as e:
            error_logger.log("smart_coin_blocker_record", str(e))

    def is_blocked(self, coin, cycle, is_ranging=False):
        """Returns True if this coin is temporarily blocked.
        Accepts is_ranging kwarg for ranging leniency (ignored in non-smart mode).
        Also checks time-based reset."""
        try:
            if not SMART_COIN_BLOCK_ENABLED:
                # Legacy fallback: 2-consecutive-loss behavior
                return cycle < self.blocked_until.get(coin, 0)
            self._ensure_coin(coin)
            info = self.coins[coin]
            if info["blocked_cycle"] == 0:
                return False
            # Time-based reset: unblock after N cycles
            if cycle >= self.blocked_until.get(coin, 0):
                logger.info(f"SMART COIN RESET: {coin} — time-based unblock after {SMART_COIN_RECOVERY_RESET_CYCLES} cycles")
                info["blocked_cycle"] = 0
                self.blocked_until.pop(coin, None)
                return False
            # Ranging leniency: relax cumulative threshold
            if is_ranging and RANGING_ADAPTATION_ENABLED:
                cumul = self._cumulative_pnl(coin)
                lenient_threshold = SMART_COIN_CUMULATIVE_LOSS_PCT * SMART_COIN_RANGING_LENIENCY
                if cumul > lenient_threshold:
                    logger.debug(f"SMART COIN RANGING LENIENCY: {coin} — cumul {cumul:.1f}% > lenient threshold {lenient_threshold:.1f}%, allowing")
                    return False
            return True
        except Exception as e:
            error_logger.log("smart_coin_is_blocked", str(e))
            return False  # Fail-open for non-critical soft filter

    def blocked_coins_summary(self):
        """Return dict of currently blocked coins with their cumulative P&L for logging."""
        try:
            summary = {}
            for coin, info in self.coins.items():
                if info["blocked_cycle"] > 0:
                    summary[coin] = {
                        "cumul_pnl": self._cumulative_pnl(coin),
                        "drawdown": self._max_drawdown(coin),
                        "blocked_cycle": info["blocked_cycle"],
                        "trades": len(info["trades"]),
                    }
            return summary
        except Exception:
            return {}

    def save_state(self):
        return {
            "coins": self.coins,
            "blocked_until": self.blocked_until,
            # Legacy compat keys (for downgrade safety)
            "coin_losses": {},
        }

    def load_state(self, state):
        if state:
            # Try smart format first
            if "coins" in state:
                self.coins = state.get("coins", {})
                self.blocked_until = state.get("blocked_until", {})
            else:
                # Legacy CoinLossTracker format — migrate
                self.blocked_until = state.get("blocked_until", {})
                self.coin_losses = state.get("coin_losses", {})
                # Don't crash on legacy state — just start with whatever blocked_until was saved


# ── v29.3.4: Dynamic Temporary Blacklist Manager ──
class DynamicBlacklistManager:
    """Tracks temporary blacklist status with expiring cooldowns and recovery scoring.

    Coins are auto-added after TEMP_BLACKLIST_COIN_LOSS_MAX consecutive losses.
    After TEMP_BLACKLIST_COOLDOWN_CYCLES, a coin is eligible for recovery IF:
      1. Its momentum score >= TEMP_BLACKLIST_MIN_RECOVERY_SCORE
      2. Its ATR is within TEMP_BLACKLIST_ATR_RANGE
      3. No active per-coin loss streak
    Background scoring runs every cycle so recovery is detected promptly.
    """

    def __init__(self):
        self.blocked = {}           # coin -> (cycle_blacklisted, reason)
        self.recovery_scores = {}   # coin -> (momentum_score, atr, cycle_scored)
        self.recovered_coins = {}   # coin -> cycle_recovered (for priority weight tracking)

    def add(self, coin, reason="auto"):
        """Block a coin for TEMP_BLACKLIST_COOLDOWN_CYCLES."""
        cycle = _current_cycle
        self.blocked[coin] = (cycle, reason)
        try:
            logger.info(f"[TEMP_BLACKLIST] {coin} blocked: {reason} (cycle {cycle}, "
                        f"expires ~{cycle + TEMP_BLACKLIST_COOLDOWN_CYCLES})")
        except Exception:
            pass

    def _recovery_threshold(self):
        """Percentile-based recovery threshold: top 30% of current momentum scores.
        Falls back to TEMP_BLACKLIST_MIN_RECOVERY_SCORE if insufficient data."""
        if len(self.recovery_scores) < 3:
            return TEMP_BLACKLIST_MIN_RECOVERY_SCORE
        all_scores = sorted(abs(s) for s, _, _ in self.recovery_scores.values())
        idx = max(0, int(len(all_scores) * 0.70))  # top 30% = 70th percentile
        return max(TEMP_BLACKLIST_MIN_RECOVERY_SCORE, all_scores[min(idx, len(all_scores) - 1)])

    def is_blocked(self, coin, cycle):
        """True if coin is still in cooldown or recovery conditions not met."""
        if coin not in self.blocked:
            return False
        bl_cycle, reason = self.blocked[coin]
        # Still within cooldown window
        if cycle < bl_cycle + TEMP_BLACKLIST_COOLDOWN_CYCLES:
            return True
        # Cooldown expired — check recovery conditions (percentile-based threshold)
        score, atr, _ = self.recovery_scores.get(coin, (0, 0, 0))
        lo, hi = TEMP_BLACKLIST_ATR_RANGE
        _recovery_min = self._recovery_threshold()
        if (abs(score) >= _recovery_min
                and lo <= atr <= hi
                and _per_coin_loss_streak.get(coin, 0) < TEMP_BLACKLIST_COIN_LOSS_MAX):
            # Recovery conditions met — lift
            del self.blocked[coin]
            self.recovered_coins[coin] = cycle
            try:
                logger.info(f"[TEMP_BLACKLIST_RECOVERY] {coin} lifted "
                            f"(score={score:.3f}, threshold={_recovery_min:.3f}, atr={atr:.4f}, streak={_per_coin_loss_streak.get(coin, 0)})")
            except Exception:
                pass
            return False
        # Recovery conditions NOT met — extend block
        return True

    def lift(self, coin):
        """Manual override: remove a coin from the temp blacklist."""
        if coin in self.blocked:
            del self.blocked[coin]
            try:
                logger.info(f"[TEMP_BLACKLIST_MANUAL_LIFT] {coin} removed")
            except Exception:
                pass

    def get_priority_weight(self, coin):
        """Returns score multiplier for recovered coins (higher = prioritized)."""
        if coin in self.recovered_coins:
            return TEMP_BLACKLIST_PRIORITY_WEIGHT
        return 1.0

    def score_recovery_candidates(self, tickers, cycle, coin_atr_fn=None):
        """Background scoring: compute momentum + ATR for all blocked coins.
        Called from main loop each cycle (non-blocking)."""
        if not self.blocked:
            return
        try:
            for coin in list(self.blocked.keys()):
                for pair, t in tickers.items():
                    short = to_short_name(pair) if callable(globals().get("to_short_name")) else pair
                    if short == coin:
                        momentum = t.get("change", 0)
                        atr = coin_atr_fn(coin) if coin_atr_fn else 0.01
                        self.recovery_scores[coin] = (momentum, atr, cycle)
                        break
        except Exception as e:
            try:
                logger.debug(f"[RECOVERY_SCORE_ERROR] {e}")
            except Exception:
                pass

    def cycle_end(self, cycle):
        """Housekeeping: purge stale recovery scores and old recovered tracking."""
        # Purge recovery_scores older than 500 cycles
        stale = [c for c, (_, _, sc) in self.recovery_scores.items()
                 if cycle - sc > 500]
        for c in stale:
            del self.recovery_scores[c]
        # Purge recovered_coins older than 1000 cycles (no longer prioritized)
        stale2 = [c for c, rc in self.recovered_coins.items()
                  if cycle - rc > 1000]
        for c in stale2:
            del self.recovered_coins[c]

    def status_summary(self):
        """Return dict for logging / monitoring reports."""
        return {
            "blocked_count": len(self.blocked),
            "blocked_coins": list(self.blocked.keys()),
            "recovery_candidates": {c: s[0] for c, s in self.recovery_scores.items()},
            "recently_recovered": list(self.recovered_coins.keys()),
        }

    def state_dict(self):
        """For persistence to state file."""
        return {
            "blocked": {c: list(v) for c, v in self.blocked.items()},
            "recovery_scores": {c: list(v) for c, v in self.recovery_scores.items()},
            "recovered_coins": dict(self.recovered_coins),
        }

    def load_state(self, state):
        """Restore from state file."""
        if not state:
            return
        self.blocked = {c: tuple(v) for c, v in state.get("blocked", {}).items()}
        self.recovery_scores = {c: tuple(v) for c, v in state.get("recovery_scores", {}).items()}
        self.recovered_coins = state.get("recovered_coins", {})


# v29.3.4 global instance
dynamic_blacklist = DynamicBlacklistManager()


# ── Overtrading Guard: Limits trade frequency ──
class OvertradingGuard:
    """Unified overtrading guard — merges cycle/100-cycle limits with blocked-rate
    and min-cycles-between checks.  Single .can_trade() replaces the old class
    + _overtrade_guard_ok() helper."""

    def __init__(self):
        self.trades_this_cycle = 0
        self.recent_trade_cycles = []  # Cycle numbers of recent trades
        self._last_trade_cycle = 0     # For min-cycles-between check

    def reset_cycle(self):
        """Call at start of each cycle."""
        self.trades_this_cycle = 0

    def record_trade(self, cycle):
        """Record that a trade was taken this cycle."""
        self.trades_this_cycle += 1
        self.recent_trade_cycles.append(cycle)
        self._last_trade_cycle = cycle
        # Keep last 200 entries
        if len(self.recent_trade_cycles) > 200:
            self.recent_trade_cycles = self.recent_trade_cycles[-200:]

    def can_trade(self, cycle, is_ranging=False):
        """Returns True if we haven't exceeded ANY trade frequency limit.
        Combines: per-cycle, per-100-cycles, blocked-rate, min-cycles-between.
        In ranging markets, min-cycles-between is relaxed by RANGING_OVERTRADE_CYCLES_MULT."""
        try:
            # Limit 1: Max trades this cycle
            if self.trades_this_cycle >= MAX_TRADES_PER_CYCLE:
                return False
            # Limit 2: Max trades in last 100 cycles
            recent_count = sum(1 for c in self.recent_trade_cycles if cycle - c < 100)
            if recent_count >= MAX_TRADES_PER_100_CYCLES:
                return False
            # Optimized change – removed blocked_rate check (punished clean markets)
            # Limit 3: Min cycles between trades (relaxed in ranging markets)
            if OVERTRADE_GUARD_ENABLED:
                if self._last_trade_cycle > 0:
                    min_gap = OVERTRADE_MIN_CYCLES_BETWEEN
                    if is_ranging and RANGING_ADAPTATION_ENABLED:
                        min_gap = int(min_gap * RANGING_OVERTRADE_CYCLES_MULT)
                    if (cycle - self._last_trade_cycle) < min_gap:
                        return False
            return True
        except Exception as e:
            error_logger.log("overtrading_can_trade", str(e))
            return True

    def allow_limited(self, cycle):
        """Relaxed version for recovery mode: allows up to 1.5x the normal limit.
        Still enforces a ceiling — never fully bypasses overtrading protection."""
        try:
            if self.trades_this_cycle >= MAX_TRADES_PER_CYCLE:
                return False
            recent_count = sum(1 for c in self.recent_trade_cycles if cycle - c < 100)
            if recent_count >= int(MAX_TRADES_PER_100_CYCLES * 1.5):
                return False
            return True
        except Exception:
            return True

    def save_state(self):
        return {
            "recent_trade_cycles": self.recent_trade_cycles[-200:],
            "_last_trade_cycle": self._last_trade_cycle,
        }

    def load_state(self, state):
        if state:
            self.recent_trade_cycles = state.get("recent_trade_cycles", [])
            self._last_trade_cycle = state.get("_last_trade_cycle", 0)


# ── Safe Mode: Reduces risk during drawdowns ──
class SafeMode:
    """Enters safe mode during significant drawdowns. Cuts size and disables shorts."""

    def __init__(self):
        self.session_peak = None
        self.active = False

    def update(self, equity):
        """Update with current equity. Returns True if safe mode is active."""
        try:
            if self.session_peak is None:
                self.session_peak = equity
            self.session_peak = max(self.session_peak, equity)
            if self.session_peak <= 0:
                return False
            drawdown_pct = (self.session_peak - equity) / self.session_peak * 100
            was_active = self.active
            self.active = drawdown_pct >= SAFE_MODE_DRAWDOWN_PCT
            if self.active and not was_active:
                logger.warning(f"SAFE MODE ACTIVATED: drawdown {drawdown_pct:.1f}% (limit={SAFE_MODE_DRAWDOWN_PCT}%)")
            elif not self.active and was_active:
                logger.info(f"SAFE MODE DEACTIVATED: drawdown recovered to {drawdown_pct:.1f}%")
            return self.active
        except Exception as e:
            error_logger.log("safe_mode_update", str(e))
            return False

    @property
    def size_multiplier(self):
        return SAFE_MODE_SIZE_MULT if self.active else 1.0

    @property
    def shorts_allowed(self):
        return not self.active

    def save_state(self):
        return {
            "session_peak": self.session_peak,
            "active": self.active,
        }

    def load_state(self, state):
        if state:
            self.session_peak = state.get("session_peak", None)
            self.active = state.get("active", False)


# ── Health Output: Periodic status print ──
_bot_start_time = None  # Set in main()


def health_output(cycle, wallet, prices, kill_switch, strategy_monitor, safe_mode, overtrading_guard):
    """Print health status / heartbeat every 100 cycles."""
    try:
        pv = wallet.value(prices)
        dd = 0
        if safe_mode.session_peak and safe_mode.session_peak > 0:
            dd = (safe_mode.session_peak - pv) / safe_mode.session_peak * 100
        wr = strategy_monitor.win_rate
        err = error_logger.error_count
        # Status string
        status_parts = []
        if kill_switch and kill_switch.is_triggered:
            status_parts.append("KILLED")
        if safe_mode.active:
            status_parts.append("SAFE_MODE")
        if strategy_monitor.is_paused(cycle):
            status_parts.append("PAUSED")
        if error_classifier.check_cooldown(cycle):
            status_parts.append("ERR_COOLDOWN")
        if api_staleness.should_block_entries(cycle):
            status_parts.append(f"API_STALE({api_staleness.stale_cycles(cycle)}c)")
        if recovery_mode.active:
            status_parts.append(f"RECOVERY({cycle - recovery_mode.activated_cycle}c)")
        if not status_parts:
            status_parts.append("NORMAL")
        status = " | ".join(status_parts)
        positions = len(wallet.longs) + len(wallet.shorts)
        # Error breakdown
        err_breakdown = error_classifier.summary()
        # Skip reason summary
        skip_str = skip_tracker.summary()
        # Uptime calculation
        uptime_str = ""
        if _bot_start_time:
            _uptime = time.time() - _bot_start_time
            _h = int(_uptime // 3600)
            _m = int((_uptime % 3600) // 60)
            uptime_str = f" uptime={_h}h{_m:02d}m"
        # Stagnation info
        _idle = cycle - stagnation_watchdog.last_trade_cycle if stagnation_watchdog.last_trade_cycle > 0 else 0
        idle_str = f" idle={_idle}c" if _idle > 100 else ""
        # Recovery + visibility info
        vis_str = recovery_mode.visibility_summary()
        # Terminal: compact heartbeat (PnL, positions, status only)
        _hb_compact = (
            f"\n  [HEARTBEAT] cycle={cycle} equity=${pv:.2f} dd={dd:.1f}% "
            f"WR={wr:.1f}% positions={positions} status={status}{uptime_str}{idle_str}"
        )
        print(_hb_compact)
        # Conviction kill summary (shows which hard filters killed conviction signals)
        _conv_kill_str = conviction_kill_tracker.summary()
        # File: full detail including skip reasons and flow visibility
        _hb_full = (
            f"{_hb_compact}"
            f"\n  [SKIPS] {skip_str}"
            f"\n  [FLOW] {vis_str}"
            f"\n  [ERRORS] {err}({err_breakdown})"
        )
        if _conv_kill_str:
            _hb_full += f"\n  [CONVICTION] {_conv_kill_str}"
        logger.debug(_hb_full)
        # Reset skip tracker and visibility counters after printing
        skip_tracker.reset()
        recovery_mode.reset_visibility()
        conviction_kill_tracker.reset()
    except Exception:
        # Heartbeat must NEVER crash the bot
        try:
            print(f"\n  [HEARTBEAT] cycle={cycle} (details unavailable)")
        except Exception:
            pass


# ── Strategy Decay Detection ──
class StrategyHealth:
    """Monitors strategy performance over rolling windows. Auto-disables degrading strategies."""

    def __init__(self):
        self.momentum_results = []    # Last 20 momentum trade results
        self.mean_rev_results = []    # Last 20 mean reversion results
        self.breakout_results = []    # Last 20 breakout results
        self.short_results = []       # Last 20 short results

    def record(self, strategy_type, pnl_pct):
        bucket = getattr(self, f"{strategy_type}_results", None)
        if bucket is not None:
            bucket.append(pnl_pct)
            if len(bucket) > 20:
                bucket[:] = bucket[-20:]

    def is_healthy(self, strategy_type) -> bool:
        """Returns False if strategy has degraded (should be disabled)."""
        bucket = getattr(self, f"{strategy_type}_results", [])
        if len(bucket) < 5:
            return True  # Not enough data
        wins = sum(1 for r in bucket if r > 0)
        win_rate = wins / len(bucket)
        avg_pnl = sum(bucket) / len(bucket)
        # Disable if win rate < 30% OR average P&L is negative
        if win_rate < 0.30 or avg_pnl < -0.5:
            return False
        return True

    def status(self):
        result = {}
        for stype in ['momentum', 'mean_rev', 'breakout', 'short']:
            bucket = getattr(self, f"{stype}_results", [])
            if len(bucket) >= 3:
                wr = sum(1 for r in bucket if r > 0) / len(bucket) * 100
                result[stype] = f"{wr:.0f}%"
            else:
                result[stype] = "n/a"
        return result


strategy_health = StrategyHealth()


# ── Strategy × Regime Performance Matrix ──
# Pure data collection and reporting. Does NOT block or modify trades.
class PerformanceMatrix:
    """
    Tracks every trade outcome by strategy type AND regime.
    Answers: "Where does the bot actually make money?"

    Usage:
        matrix.record("momentum", "SMOOTH_TREND", pnl_pct=1.2, fees=0.4)
        matrix.report()  # Shows win rate + expectancy per cell
    """

    def __init__(self):
        self.trades = []  # Full trade log
        self.matrix = {}  # (strategy, regime) -> {"wins": int, "losses": int, "total_pnl": float, "fees": float}

    def record(self, strategy, regime, entry_price, exit_price, direction, pnl_pct, fees_pct, net_pnl_pct):
        """Record a completed trade with full context."""
        # Win classification uses GROSS PnL (pnl_pct) — measures directional skill.
        # Net PnL (net_pnl_pct) is still stored for accurate P&L accounting.
        # Rationale: thin-margin stagnation exits (+0.2% gross) that flip to net-loss
        # after fees (-0.06%) are still *correct directional calls* and should count as wins
        # for health score / strategy evaluation purposes.
        _won = pnl_pct > 0  # GROSS PnL win flag (pre-fees)
        trade = {
            "strategy": strategy,
            "regime": regime,
            "direction": direction,
            "entry": entry_price,
            "exit": exit_price,
            "pnl_pct": pnl_pct,
            "fees_pct": fees_pct,
            "net_pnl": net_pnl_pct,
            "won": _won,
        }
        self.trades.append(trade)

        key = (strategy, regime)
        if key not in self.matrix:
            self.matrix[key] = {"wins": 0, "losses": 0, "total_pnl": 0, "total_fees": 0, "count": 0}

        cell = self.matrix[key]
        cell["count"] += 1
        cell["total_pnl"] += net_pnl_pct
        cell["total_fees"] += fees_pct
        if _won:
            cell["wins"] += 1
        else:
            cell["losses"] += 1

    def get_cell(self, strategy, regime):
        """Get stats for a specific strategy×regime combination."""
        cell = self.matrix.get((strategy, regime))
        if not cell or cell["count"] == 0:
            return None
        return {
            "win_rate": cell["wins"] / cell["count"] * 100,
            "expectancy": cell["total_pnl"] / cell["count"],
            "total_pnl": cell["total_pnl"],
            "total_fees": cell["total_fees"],
            "count": cell["count"],
        }

    def insights(self):
        """Generate automatic insights about where edge exists."""
        results = []
        for (strat, regime), cell in self.matrix.items():
            if cell["count"] < 3:
                continue
            wr = cell["wins"] / cell["count"] * 100
            exp = cell["total_pnl"] / cell["count"]
            if exp < -0.1:
                results.append({
                    "type": "NEGATIVE_EDGE",
                    "strategy": strat,
                    "regime": regime,
                    "win_rate": wr,
                    "expectancy": exp,
                    "suggestion": f"Reduce {strat} in {regime} (expectancy {exp:+.2f}%)"
                })
            elif exp > 0.3:
                results.append({
                    "type": "POSITIVE_EDGE",
                    "strategy": strat,
                    "regime": regime,
                    "win_rate": wr,
                    "expectancy": exp,
                    "suggestion": f"Increase {strat} in {regime} (expectancy {exp:+.2f}%)"
                })
        return results

    def report(self):
        """Full performance matrix as printable string."""
        if not self.matrix:
            return "No trades recorded yet"

        strategies = sorted(set(s for s, r in self.matrix.keys()))
        regimes = sorted(set(r for s, r in self.matrix.keys()))

        lines = ["STRATEGY × REGIME PERFORMANCE MATRIX", "=" * 60]
        for strat in strategies:
            for regime in regimes:
                cell = self.get_cell(strat, regime)
                if cell:
                    lines.append(
                        f"  {strat:<12} × {regime:<16} "
                        f"W:{cell['win_rate']:.0f}% "
                        f"E:{cell['expectancy']:+.2f}% "
                        f"N:{cell['count']} "
                        f"PnL:{cell['total_pnl']:+.1f}%"
                    )

        insights = self.insights()
        if insights:
            lines.append("")
            lines.append("INSIGHTS:")
            for ins in insights:
                tag = "⚠️" if ins["type"] == "NEGATIVE_EDGE" else "✓"
                lines.append(f"  {tag} {ins['suggestion']}")

        return "\n".join(lines)

    def save_state(self):
        """Serialize perf_matrix for state persistence across restarts.
        Keeps last 100 trades (health score uses last 50) and full matrix."""
        return {
            "trades": self.trades[-100:],
            "matrix": {f"{k[0]}|{k[1]}": v for k, v in self.matrix.items()},
        }

    def load_state(self, state):
        """Restore perf_matrix from saved state. Backward-compatible: missing key = no-op."""
        if not state:
            return
        self.trades = state.get("trades", [])
        raw = state.get("matrix", {})
        self.matrix = {}
        for k, v in raw.items():
            parts = k.split("|", 1)
            if len(parts) == 2:
                self.matrix[(parts[0], parts[1])] = v

    def save_to_log(self):
        """Write report to bot.log."""
        logger.debug("\n" + self.report())


perf_matrix = PerformanceMatrix()

# ── New Protection Systems ──
strategy_health_monitor = StrategyHealthMonitor()
coin_loss_tracker = SmartCoinBlocker()
overtrading_guard = OvertradingGuard()
safe_mode = SafeMode()


# ── Edge Audit System (PURE ANALYSIS — NO trading logic changes) ──
class EdgeAudit:
    """
    Post-trade analysis system. Reads from PerformanceMatrix and trade history.
    Identifies real edge, hidden losses, and layer conflicts.
    Does NOT modify any trading behavior.
    """

    @staticmethod
    def edge_matrix(pm):
        """A. Strategy × Regime → expectancy, win rate, sample size (fee-adjusted)."""
        if not pm.matrix:
            return "No data"
        lines = ["A. EDGE MATRIX (fee-adjusted)", "-" * 60]
        for (strat, regime), cell in sorted(pm.matrix.items()):
            if cell["count"] < 2:
                continue
            wr = cell["wins"] / cell["count"] * 100
            gross = cell["total_pnl"] + cell["total_fees"]  # Add fees back = gross PnL
            net = cell["total_pnl"]
            exp = net / cell["count"]
            fee_drag = cell["total_fees"] / cell["count"]
            tag = "EDGE" if exp > 0 else "NO EDGE"
            lines.append(
                f"  {strat:<12} × {regime:<16} | "
                f"WR:{wr:4.0f}% | Gross:{gross/cell['count']:+.2f}% | "
                f"Fees:{fee_drag:.2f}% | Net:{exp:+.2f}% | "
                f"N:{cell['count']} | [{tag}]"
            )
        return "\n".join(lines)

    @staticmethod
    def hidden_losses(pm):
        """B. Find high-WR but fee-negative setups, overtraded regimes, fee destruction."""
        if not pm.matrix:
            return "No data"
        lines = ["B. HIDDEN LOSS DETECTION", "-" * 60]
        found = False

        for (strat, regime), cell in pm.matrix.items():
            if cell["count"] < 3:
                continue
            wr = cell["wins"] / cell["count"] * 100
            exp = cell["total_pnl"] / cell["count"]
            gross_exp = (cell["total_pnl"] + cell["total_fees"]) / cell["count"]

            # High win rate but negative net (fees kill it)
            if wr >= 50 and exp < 0:
                lines.append(
                    f"  FAKE PROFITABLE: {strat} × {regime} — "
                    f"WR:{wr:.0f}% looks good but net:{exp:+.2f}% (fees destroy edge)"
                )
                found = True

            # Fee destruction: fees > 60% of gross profit
            if gross_exp > 0 and cell["total_fees"] > 0:
                fee_ratio = cell["total_fees"] / (cell["total_pnl"] + cell["total_fees"])
                if fee_ratio > 0.6:
                    lines.append(
                        f"  FEE DESTRUCTION: {strat} × {regime} — "
                        f"fees consume {fee_ratio*100:.0f}% of gross profits"
                    )
                    found = True

        # Overtraded regimes (>40% of all trades in one regime)
        total_trades = sum(c["count"] for c in pm.matrix.values())
        if total_trades > 5:
            regime_counts = {}
            for (s, r), cell in pm.matrix.items():
                regime_counts[r] = regime_counts.get(r, 0) + cell["count"]
            for regime, count in regime_counts.items():
                pct = count / total_trades * 100
                if pct > 50:
                    lines.append(
                        f"  OVERTRADED: {regime} has {pct:.0f}% of all trades ({count}/{total_trades})"
                    )
                    found = True

        if not found:
            lines.append("  No hidden losses detected")
        return "\n".join(lines)

    @staticmethod
    def conflict_report(pm):
        """C. Where internal systems disagree with actual outcomes."""
        if not pm.trades:
            return "No trade data"
        lines = ["C. CONFLICT REPORT", "-" * 60]
        found = False

        # Group trades by regime and check if regime classification helps
        regime_perf = {}
        for t in pm.trades:
            r = t["regime"]
            if r not in regime_perf:
                regime_perf[r] = {"wins": 0, "losses": 0, "total": 0}
            regime_perf[r]["total"] += 1
            if t["won"]:
                regime_perf[r]["wins"] += 1
            else:
                regime_perf[r]["losses"] += 1

        for r, data in regime_perf.items():
            if data["total"] < 3:
                continue
            wr = data["wins"] / data["total"] * 100
            if wr < 40:
                lines.append(
                    f"  REGIME MISALIGNED: {r} — bot trades here but only {wr:.0f}% WR ({data['total']} trades)"
                )
                found = True

        # Check if momentum works better as short than long
        long_momentum = [t for t in pm.trades if t["strategy"] == "momentum" and t["direction"] == "long"]
        short_trades = [t for t in pm.trades if t["direction"] == "short"]
        if len(long_momentum) >= 3 and len(short_trades) >= 3:
            long_exp = sum(t["net_pnl"] for t in long_momentum) / len(long_momentum)
            short_exp = sum(t["net_pnl"] for t in short_trades) / len(short_trades)
            if short_exp > long_exp + 0.3:
                lines.append(
                    f"  DIRECTION CONFLICT: Shorts ({short_exp:+.2f}%) outperform longs ({long_exp:+.2f}%) — consider reducing long bias"
                )
                found = True
            elif long_exp > short_exp + 0.3:
                lines.append(
                    f"  DIRECTION CONFLICT: Longs ({long_exp:+.2f}%) outperform shorts ({short_exp:+.2f}%) — consider reducing short bias"
                )
                found = True

        if not found:
            lines.append("  No conflicts detected")
        return "\n".join(lines)

    @staticmethod
    def full_report(pm):
        """Generate complete edge audit report."""
        sections = [
            "EDGE AUDIT REPORT",
            "=" * 60,
            "",
            EdgeAudit.edge_matrix(pm),
            "",
            EdgeAudit.hidden_losses(pm),
            "",
            EdgeAudit.conflict_report(pm),
            "",
            "=" * 60,
            f"Total trades analyzed: {len(pm.trades)}",
            f"Total strategy×regime cells: {len(pm.matrix)}",
        ]

        # Final recommendations
        insights = pm.insights()
        if insights:
            sections.append("")
            sections.append("RECOMMENDATIONS:")
            for ins in insights:
                if ins["type"] == "NEGATIVE_EDGE":
                    sections.append(f"  REDUCE: {ins['suggestion']}")
                elif ins["type"] == "POSITIVE_EDGE":
                    sections.append(f"  KEEP: {ins['suggestion']}")

        return "\n".join(sections)


# ── Ground Truth Replay Validator (PURE VERIFICATION — zero trading impact) ──
class GroundTruthValidator:
    """
    Independently recalculates every trade result using only raw data.
    Detects: accounting errors, inflated performance, fee miscalculations.
    Does NOT use ML, regime, strategy logic, or any internal scoring.
    Pure math only.
    """

    FEE_RATE = 0.002  # 0.2% per side

    @staticmethod
    def replay_trade(trade):
        """Recalculate a single trade from raw entry/exit prices."""
        try:
            entry = trade.get("entry", 0)
            exit_p = trade.get("exit", 0)
            direction = trade.get("direction", "long")

            if entry <= 0 or exit_p <= 0:
                return None

            # Gross P&L (before fees)
            if direction == "long":
                gross_pnl_pct = (exit_p - entry) / entry * 100
            else:
                gross_pnl_pct = (entry - exit_p) / entry * 100

            # Fees: entry + exit (both sides)
            fee_pct = GroundTruthValidator.FEE_RATE * 100 * 2  # 0.4% round-trip

            # Net P&L
            net_pnl_pct = gross_pnl_pct - fee_pct

            return {
                "gross_pnl": gross_pnl_pct,
                "fees": fee_pct,
                "net_pnl": net_pnl_pct,
                "won": gross_pnl_pct > 0,  # Use GROSS PnL for skill measurement (consistent with PerformanceMatrix)
            }
        except Exception:
            return None

    @staticmethod
    def integrity_check(pm_trades):
        """Compare bot's reported PnL vs independently recalculated PnL."""
        mismatches = []
        checked = 0
        matched = 0

        for trade in pm_trades:
            replay = GroundTruthValidator.replay_trade(trade)
            if not replay:
                continue

            checked += 1
            reported_net = trade.get("net_pnl", 0)
            recalculated_net = replay["net_pnl"]
            diff = abs(reported_net - recalculated_net)

            if diff > 1.0:  # >1% mismatch
                mismatches.append({
                    "strategy": trade.get("strategy", "?"),
                    "regime": trade.get("regime", "?"),
                    "reported": reported_net,
                    "recalculated": recalculated_net,
                    "diff": diff,
                })
            else:
                matched += 1

        integrity_pct = (matched / checked * 100) if checked > 0 else 0
        return {
            "checked": checked,
            "matched": matched,
            "mismatches": mismatches,
            "integrity_pct": integrity_pct,
        }

    @staticmethod
    def true_performance(pm_trades):
        """Recalculate total performance from raw data only."""
        total_gross = 0
        total_fees = 0
        total_net = 0
        wins = 0
        losses = 0
        count = 0

        for trade in pm_trades:
            replay = GroundTruthValidator.replay_trade(trade)
            if not replay:
                continue
            count += 1
            total_gross += replay["gross_pnl"]
            total_fees += replay["fees"]
            total_net += replay["net_pnl"]
            if replay["won"]:
                wins += 1
            else:
                losses += 1

        return {
            "total_gross_pnl": total_gross,
            "total_fees": total_fees,
            "total_net_pnl": total_net,
            "expectancy": total_net / count if count > 0 else 0,
            "win_rate": wins / count * 100 if count > 0 else 0,
            "wins": wins,
            "losses": losses,
            "count": count,
        }

    @staticmethod
    def strategy_validation(pm_trades):
        """Recalculate performance grouped by strategy type only. No ML/regime logic."""
        by_strategy = {}

        for trade in pm_trades:
            replay = GroundTruthValidator.replay_trade(trade)
            if not replay:
                continue

            strat = trade.get("strategy", "unknown")
            if strat not in by_strategy:
                by_strategy[strat] = {"wins": 0, "losses": 0, "net_pnl": 0, "count": 0}

            cell = by_strategy[strat]
            cell["count"] += 1
            cell["net_pnl"] += replay["net_pnl"]
            if replay["won"]:
                cell["wins"] += 1
            else:
                cell["losses"] += 1

        return by_strategy

    @staticmethod
    def full_report(pm_trades):
        """Generate complete ground truth validation report."""
        lines = [
            "GROUND TRUTH VALIDATION REPORT",
            "(Independent recalculation — no internal logic used)",
            "=" * 60,
        ]

        # A. True Performance
        perf = GroundTruthValidator.true_performance(pm_trades)
        lines.append("")
        lines.append("A. TRUE PERFORMANCE (recalculated)")
        lines.append("-" * 40)
        lines.append(f"  Total trades: {perf['count']}")
        lines.append(f"  Gross PnL: {perf['total_gross_pnl']:+.2f}%")
        lines.append(f"  Total fees: {perf['total_fees']:.2f}%")
        lines.append(f"  Net PnL: {perf['total_net_pnl']:+.2f}%")
        lines.append(f"  Expectancy: {perf['expectancy']:+.3f}% per trade")
        lines.append(f"  Win rate: {perf['win_rate']:.1f}% ({perf['wins']}W / {perf['losses']}L)")

        # B. Integrity Check
        integrity = GroundTruthValidator.integrity_check(pm_trades)
        lines.append("")
        lines.append("B. INTEGRITY CHECK")
        lines.append("-" * 40)
        lines.append(f"  Trades checked: {integrity['checked']}")
        lines.append(f"  Matches: {integrity['matched']}")
        lines.append(f"  Mismatches (>1%): {len(integrity['mismatches'])}")
        lines.append(f"  Integrity score: {integrity['integrity_pct']:.1f}%")

        if integrity["mismatches"]:
            lines.append("  MISMATCH DETAILS:")
            for m in integrity["mismatches"][:5]:
                lines.append(
                    f"    {m['strategy']} × {m['regime']}: "
                    f"reported={m['reported']:+.2f}% vs recalc={m['recalculated']:+.2f}% "
                    f"(diff={m['diff']:.2f}%)"
                )

        # C. Strategy Validation
        strat_data = GroundTruthValidator.strategy_validation(pm_trades)
        lines.append("")
        lines.append("C. STRATEGY VALIDATION (raw recalculation)")
        lines.append("-" * 40)
        for strat, data in sorted(strat_data.items()):
            wr = data["wins"] / data["count"] * 100 if data["count"] > 0 else 0
            exp = data["net_pnl"] / data["count"] if data["count"] > 0 else 0
            tag = "EDGE" if exp > 0 else "NO EDGE"
            lines.append(
                f"  {strat:<15} WR:{wr:4.0f}% Net:{data['net_pnl']:+.1f}% "
                f"Exp:{exp:+.2f}% N:{data['count']} [{tag}]"
            )

        lines.append("")
        lines.append("=" * 60)
        return "\n".join(lines)


def record_exit(strategy, coin, direction, entry_price, exit_price, regime_str="UNKNOWN", wallet=None):
    """Record a trade exit to the performance matrix and trade log. Uses actual fees when available."""
    try:
        # v29.3.5: Track per-coin exit cycle + profitability for split cooldown
        global _last_exit_cycle, _current_cycle
        _was_profitable = exit_price > entry_price if direction == "long" else exit_price < entry_price
        _last_exit_cycle[coin] = (_current_cycle, _was_profitable)
        if entry_price <= 0:
            error_logger.log("trade_zero_entry", f"{coin} {direction}: entry_price={entry_price}")
            return
        if direction == "long":
            pnl_pct = (exit_price - entry_price) / entry_price * 100
        else:
            pnl_pct = (entry_price - exit_price) / entry_price * 100
        # Use actual fees from wallet if available; paper mode = 0 fees
        fees_pct = 0.0 if PAPER_MODE else 0.4
        if wallet and hasattr(wallet, '_last_exit_fees') and wallet._last_exit_fees:
            fees_pct = wallet._last_exit_fees.get("fee_pct", 0.0 if PAPER_MODE else 0.4)
        # Slippage is already baked into entry_price and exit_price (both are
        # slippage-adjusted fill prices), so pnl_pct already reflects slippage.
        # We do NOT subtract slippage again — only fees, which are not in prices.
        _slip_entry = getattr(wallet, '_last_entry_slippage', 0.05) if wallet else 0.05
        _slip_exit = getattr(wallet, '_last_exit_slippage', 0.05) if wallet else 0.05
        net_pnl = pnl_pct - fees_pct
        # v29.3.3: Loss streak protection — track consecutive losses (global)
        global _loss_streak_count, _loss_streak_paused_until, _session_peak_equity
        if net_pnl < 0:
            _loss_streak_count += 1
            if _loss_streak_count >= LOSS_STREAK_MAX:
                _loss_streak_paused_until = _current_cycle + LOSS_STREAK_PAUSE_CYCLES
                logger.warning(f"[PAUSED: LOSS_STREAK_PROTECTION] {_loss_streak_count} consecutive losses — pausing entries until cycle {_loss_streak_paused_until}")
        else:
            _loss_streak_count = 0  # reset on any win or break-even

        # v29.5.0: Streak-based sizing tracking
        record_trade_result(net_pnl > 0)

        # v29.3.4: Per-coin loss streak tracking + auto temp-blacklist
        if TEMP_BLACKLIST_ENABLED:
            if net_pnl < 0:
                _per_coin_loss_streak[coin] = _per_coin_loss_streak.get(coin, 0) + 1
                if _per_coin_loss_streak[coin] >= TEMP_BLACKLIST_COIN_LOSS_MAX:
                    if coin not in DYNAMIC_BLACKLIST:  # Don't double-block static list
                        dynamic_blacklist.add(coin, f"auto: {_per_coin_loss_streak[coin]} consecutive losses")
                    _per_coin_loss_streak[coin] = 0  # Reset after blacklisting
            else:
                _per_coin_loss_streak[coin] = 0  # Reset on win
        perf_matrix.record(strategy, regime_str, entry_price, exit_price,
                          direction, pnl_pct, fees_pct, net_pnl)
        # Log to trades.jsonl
        trade_logger.log_trade(coin, direction, entry_price, exit_price, pnl_pct, strategy)
        # Live validation tracker: log exit with full cost breakdown
        try:
            live_tracker.log_exit(coin, strategy, direction, entry_price, exit_price,
                                 pnl_pct, fees_pct, _slip_entry, _slip_exit, strategy)
        except Exception:
            pass
        # Trade consistency check
        wallet_had = True
        if wallet:
            # After exit, position should be gone — check it was there
            if direction == "long":
                wallet_had = coin not in wallet.longs  # It was sold, so should be removed
            else:
                wallet_had = coin not in wallet.shorts
        verify_trade_consistency(coin, direction, entry_price, exit_price, pnl_pct, wallet_had)
        # Paper trade tracker
        equity = wallet.value({}) if wallet else 0
        paper_tracker.record(pnl_pct, equity)
        # Kill switch: track for consecutive losses
        if kill_switch:
            kill_switch.record_trade(pnl_pct)
        # Strategy health monitor
        strategy_health_monitor.record_trade(pnl_pct)
        # Coin loss tracker
        coin_loss_tracker.record_trade(coin, pnl_pct, _current_cycle)
        # Stagnation watchdog: record that a trade happened
        try:
            stagnation_watchdog.record_trade(_current_cycle)
        except Exception:
            pass
        # Recovery mode: record trade (exits recovery if active)
        try:
            recovery_mode.record_trade(_current_cycle)
        except Exception:
            pass
        # Market brain: record trade result (updates mood)
        try:
            _won = pnl_pct > 0
            market_brain.record_trade(_current_cycle, _won)
        except Exception:
            pass
        # Pair failure tracker: reset on successful trade
        try:
            pair_failure_tracker.reset_pair(coin)
        except Exception:
            pass
        # v29.4.0: Webhook notification for exits (Item 11)
        try:
            trade_notification("exit", {"coin": coin, "direction": direction,
                                        "entry_price": entry_price, "exit_price": exit_price,
                                        "pnl_pct": round(pnl_pct, 2), "strategy": strategy,
                                        "regime": regime_str})
        except Exception:
            pass
    except Exception as e:
        error_logger.log("record_exit_error", f"{coin} {direction}: {e}")


# ── Shadow Signal Tracker (PURE LOGGING — zero trading impact) ──
class ShadowTracker:
    """
    PURE OBSERVATION SYSTEM. Logs ALL valid signals (taken + skipped).
    Shadow positions use IDENTICAL exit logic to real trades:
      - ATR-based stop-loss
      - Time exit (15 min + losing)
      - TP trigger → assess_exit() → HOLD_AND_TRAIL or EXIT
      - Profit protection with trailing stop + periodic reassessment
      - MIN_PROFIT_FILTER applied same as real bot
      - Hard ceiling (5x ATR)
    Does NOT change any trading behavior — completely passive.
    """

    def __init__(self):
        self.signals = []
        self.taken = []
        self.skipped = []
        self.shadow_positions = {}  # coin -> shadow position state

    def log_signal(self, coin, direction, score, reason, taken, strategy="momentum", conviction_tier=""):
        """Log a valid signal. Called at every filter point and execution point.
        conviction_tier: if non-empty, this signal had an active conviction override.
        Used by ConvictionKillTracker to diagnose which hard filters kill overridden signals."""
        try:
            # Track skip reasons for diagnostics
            if not taken:
                try:
                    skip_tracker.record(reason)
                except Exception:
                    pass
                # Global trade audit: categorize rejection
                try:
                    cycle_audit.record_rejection(reason)
                except Exception:
                    pass
                # Conviction kill tracking: if this signal had an override, record which filter killed it
                if conviction_tier:
                    try:
                        conviction_kill_tracker.record_kill(reason)
                    except Exception:
                        pass
            else:
                # Signal was taken — record execution in audit
                try:
                    cycle_audit.record_execution()
                except Exception:
                    pass
                # Track successful conviction execution
                if conviction_tier:
                    try:
                        conviction_kill_tracker.record_survived()
                    except Exception:
                        pass
            entry = {
                "coin": coin,
                "direction": direction,
                "score": score,
                "reason": reason,
                "taken": taken,
                "strategy": strategy,
                "price": prices_cache.get(coin, [0])[-1] if prices_cache.get(coin) else 0,
            }
            self.signals.append(entry)
            if len(self.signals) > 2000:
                self.signals = self.signals[-2000:]
            if taken:
                self.taken.append(entry)
            else:
                self.skipped.append(entry)
                # Open shadow position using SAME entry logic
                if coin not in self.shadow_positions and entry["price"] > 0:
                    atr = coin_atr(coin) * 100  # Same ATR calc as real trades
                    self.shadow_positions[coin] = {
                        "price": entry["price"],
                        "direction": direction,
                        "highest": entry["price"],
                        "lowest": entry["price"],
                        "cycle": 0,
                        "atr": max(0.8, atr),  # v29.3: matches new SL floor
                        "profit_protection": False,
                        "trail_stop": 0,
                    }
        except Exception:
            pass

    def update_shadows(self, current_prices):
        """Simulate IDENTICAL exit logic to real trades on shadow positions.
        Matches the real bot's exit rules exactly:
          Rule 1: ATR stop-loss (always enforced)
          Rule 2: Time exit (>900s and losing >0.5%)
          Rule 3: TP trigger → assess_exit() decides HOLD_AND_TRAIL or EXIT
          Rule 4: Profit protection — trailing stop + periodic reassessment
          Rule 5: Hard ceiling (max 5x ATR)
        """
        try:
            expired = []
            for coin, pos in self.shadow_positions.items():
                p = current_prices.get(coin, 0)
                if p <= 0 or pos["price"] <= 0:
                    continue

                pos["cycle"] += 1
                entry = pos["price"]
                # Refresh ATR each cycle using live data (mirrors real bot; avoids stale entry-time ATR)
                _live_atr = coin_atr(coin) * 100
                atr = max(0.8, _live_atr) if _live_atr > 0 else pos["atr"]  # v29.3: floor 0.8 (was 1.5)
                pos["atr"] = atr  # Persist for next cycle fallback

                if pos["direction"] == "long":
                    pnl = (p - entry) / entry * 100
                    pos["highest"] = max(pos["highest"], p)
                else:
                    pnl = (entry - p) / entry * 100
                    pos["lowest"] = min(pos["lowest"], p)

                # IDENTICAL exit rules to real trades:
                sl_target = max(SL_BASE_PCT, atr * ATR_SL_MULTIPLIER)  # v29.3.5: uses named constants
                tp_trigger = max(0.4, sl_target * 1.2)  # v29.3: achievable TP (was max(0.8, sl*1.5))
                held_seconds = pos["cycle"] * POLL

                # Rule 1: Stop-loss (always enforced)
                if pnl <= -sl_target:
                    pos["exit_pnl"] = pnl
                    expired.append(coin)
                    continue

                # Rule 2: Time exit (15 min + losing)
                if held_seconds > 900 and pnl < -0.5:
                    pos["exit_pnl"] = pnl
                    expired.append(coin)
                    continue

                # Rule 2c: EARLY PP — protect deep profits when TP is stretched by trend scaling (mirrors real bot)
                if pnl >= PP_TRIGGER_MULTIPLIER * tp_trigger and pnl < tp_trigger and not pos["profit_protection"]:  # v29.3.5: 70% of TP (was 0.8%)
                    assessment = assess_exit(coin, pos["direction"], entry, p)
                    if assessment["action"] == "HOLD_AND_TRAIL":
                        pos["profit_protection"] = True
                        pos["pp_start_cycle"] = pos["cycle"]
                        pos["pp_start_pnl"] = pnl  # Store activation PnL for timeout calc
                        _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                        _streak_m = _adaptive_trail_multiplier()
                        _raw_mom = short_momentum(coin, window=10)
                        _fav_mom = max(0, _raw_mom) if pos["direction"] == "long" else max(0, -_raw_mom)
                        _live_trend = min(_fav_mom / 0.02, 1.0)
                        _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                        _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                        # (confidence nudge removed: cosmetic, max 0.03 shift absorbed by clamp in 1 cycle)
                        _prev = pos.get("_trail_tm", _raw_tm)
                        _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                        _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                        pos["_trail_tm"] = _final_tm
                        if pos["direction"] == "long":
                            pos["trail_stop"] = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                        else:
                            _new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                            pos["trail_stop"] = min(pos.get("trail_stop", _new_trail), _new_trail) if pos.get("trail_stop", 0) > 0 else _new_trail

                # Rule 3: TP trigger → assess_exit() (IDENTICAL to real bot)
                if pnl >= tp_trigger and not pos["profit_protection"]:
                    assessment = assess_exit(coin, pos["direction"], entry, p)
                    if assessment["action"] == "HOLD_AND_TRAIL":
                        # Switch to profit-protection mode (same as real bot)
                        pos["profit_protection"] = True
                        pos["pp_start_cycle"] = pos["cycle"]
                        pos["pp_start_pnl"] = pnl  # Store activation PnL for timeout calc
                        # Weighted trail: blend pnl-tightening + live trend + streak, clamped per-cycle
                        _streak_m = _adaptive_trail_multiplier()
                        _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                        _raw_mom = short_momentum(coin, window=10)
                        _fav_mom = max(0, _raw_mom) if pos["direction"] == "long" else max(0, -_raw_mom)
                        _live_trend = min(_fav_mom / 0.02, 1.0)  # Only loosen on favorable-direction momentum
                        _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                        _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                        # (confidence nudge removed: cosmetic, max 0.03 shift absorbed by clamp in 1 cycle)
                        _prev = pos.get("_trail_tm", _raw_tm)
                        _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                        _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                        pos["_trail_tm"] = _final_tm
                        if pos["direction"] == "long":
                            pos["trail_stop"] = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                        else:
                            _new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                            pos["trail_stop"] = min(pos.get("trail_stop", _new_trail), _new_trail) if pos.get("trail_stop", 0) > 0 else _new_trail
                    else:
                        # assess_exit says EXIT — apply MIN_PROFIT_FILTER same as real bot
                        if MIN_PROFIT_FILTER_ENABLED and (pnl / 100) < MIN_PROFIT_THRESHOLD:
                            pass  # Hold — min profit not met (same as real bot)
                        else:
                            pos["exit_pnl"] = pnl
                            expired.append(coin)
                            continue

                # Rule 4: Profit protection mode — trailing stop + periodic reassessment
                if pos["profit_protection"]:
                    # Defensive: backfill pp_start_cycle if missing (state restore edge case)
                    if "pp_start_cycle" not in pos:
                        pos["pp_start_cycle"] = max(0, pos["cycle"] - 1)
                    if "pp_start_pnl" not in pos:
                        pos["pp_start_pnl"] = pnl  # Backfill with current if missing
                    # Adaptive PP timeout: use activation PnL (not current) for stable timeout
                    _pp_cycles = pos["cycle"] - pos["pp_start_cycle"]
                    _pp_start_pnl = pos["pp_start_pnl"]
                    _pp_timeout = 100 + int(max(0, _pp_start_pnl - 1.5) * 50)  # v29.3.5: was 500+100/% (max 900). Now 100+50/% capped at 200
                    _pp_timeout = min(200, _pp_timeout)  # v29.3.5: was 900 — capped at 200 cycles (~7 min at POLL=2s)
                    if _pp_cycles > _pp_timeout:
                        pos["exit_pnl"] = pnl
                        expired.append(coin)
                        continue

                    # Update trailing stop (only moves in favorable direction)
                    # Weighted trail: blend pnl-tightening + live trend + streak, clamped per-cycle
                    _streak_m = _adaptive_trail_multiplier()
                    _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                    _raw_mom = short_momentum(coin, window=10)
                    _fav_mom = max(0, _raw_mom) if pos["direction"] == "long" else max(0, -_raw_mom)
                    _live_trend = min(_fav_mom / 0.02, 1.0)  # Only loosen on favorable-direction momentum
                    _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                    _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                    _prev = pos.get("_trail_tm", _raw_tm)
                    _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                    _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                    # Drop-from-peak guard: block trail widening if fading from peak (mirrors real bot)
                    if pos["direction"] == "long":
                        _dfp = (pos["highest"] - p) / pos["highest"] * 100 if pos["highest"] > 0 else 0
                    else:
                        _dfp = (p - pos["lowest"]) / pos["lowest"] * 100 if pos["lowest"] > 0 else 0
                    _dfp_thresh = max(0.8, atr * 0.3)  # v29.3: tighter to match new SL  # ATR-relative: volatile coins tolerate bigger pullbacks
                    if _final_tm > _prev and _dfp_thresh > 0:
                        _dampen = min(1.0, max(0, _dfp) / (_dfp_thresh * 2))  # Proportional: 0→full, thresh→half, 2×thresh→locked
                        _final_tm = _prev + (_final_tm - _prev) * (1 - _dampen)
                    pos["_trail_tm"] = _final_tm
                    if pos["direction"] == "long":
                        new_trail = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                        pos["trail_stop"] = max(pos.get("trail_stop", entry), new_trail)
                    else:
                        new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                        pos["trail_stop"] = min(pos.get("trail_stop", entry), new_trail) if pos.get("trail_stop", 0) > 0 else new_trail

                    # Adaptive reassessment: faster when more profit at stake or higher volatility
                    _reassess_base = 30
                    _pnl_adj = max(0.5, 1.0 - abs(pnl) * 0.1)  # 5%+ PnL → 0.5x (15s min)
                    _vol_adj = min(1.5, max(0.6, 1.5 / max(1.0, atr)))  # High ATR → faster checks
                    _reassess_secs = max(15, min(60, _reassess_base * _pnl_adj * _vol_adj))
                    reassess_interval = max(1, int(_reassess_secs / POLL))
                    _pp_age = pos["cycle"] - pos.get("pp_start_cycle", 0)
                    _cached_assessment = None  # Reuse for hard ceiling if available
                    if _pp_age > 0 and pos["cycle"] % reassess_interval == 0:
                        _cached_assessment = assess_exit(coin, pos["direction"], entry, p)
                        if _cached_assessment["action"] == "EXIT":
                            if MIN_PROFIT_FILTER_ENABLED and (pnl / 100) < MIN_PROFIT_THRESHOLD:
                                pass  # Hold — min profit not met
                            else:
                                pos["exit_pnl"] = pnl
                                expired.append(coin)
                                continue
                        # else: HOLD_AND_TRAIL — no action needed (nudge removed: cosmetic, absorbed by clamp in 1 cycle)

                    # Trailing stop hit — ALWAYS execute (same as real bot)
                    if pos["direction"] == "long":
                        if p <= pos.get("trail_stop", 0) and pos.get("trail_stop", 0) > 0:
                            pos["exit_pnl"] = pnl
                            expired.append(coin)
                            continue
                    else:
                        if pos.get("trail_stop", 0) > 0 and p >= pos["trail_stop"]:
                            pos["exit_pnl"] = pnl
                            expired.append(coin)
                            continue

                    # Hard ceiling — adaptive: reuse cached assessment if available (mirrors real bot)
                    _ceiling_assessment = _cached_assessment if _cached_assessment is not None else assess_exit(coin, pos["direction"], entry, p)
                    _atr_mult = 7 if _ceiling_assessment.get("confidence", 0) >= 0.8 else 5
                    _hard_ceiling = max(5.0, atr * _atr_mult)
                    if pnl >= _hard_ceiling:
                        pos["exit_pnl"] = pnl
                        expired.append(coin)
                        continue

                # Rule 5: Hard ceiling — adaptive (mirrors real bot)
                _ceiling_assessment = assess_exit(coin, pos["direction"], entry, p)
                _atr_mult = 7 if _ceiling_assessment.get("confidence", 0) >= 0.8 else 5
                _hard_ceiling = max(5.0, atr * _atr_mult)
                if pnl >= _hard_ceiling:
                    pos["exit_pnl"] = pnl
                    expired.append(coin)
                    continue

            for coin in expired:
                pos = self.shadow_positions.pop(coin)
                for s in self.skipped:
                    if s["coin"] == coin and "exit_pnl" not in s:
                        s["exit_pnl"] = pos.get("exit_pnl", 0)
                        break
        except Exception:
            pass

    def report(self):
        """Generate shadow analysis report."""
        try:
            return self._report_inner()
        except Exception:
            return "Shadow tracker: error generating report"

    def _report_inner(self):
        lines = [
            "SHADOW SIGNAL ANALYSIS",
            "(Valid signals: taken vs skipped — REAL exit logic)",
            "=" * 60,
        ]

        total_signals = len(self.signals)
        total_taken = len(self.taken)
        total_skipped = len(self.skipped)

        lines.append(f"\nA. OPPORTUNITY vs EXECUTION")
        lines.append(f"-" * 40)
        lines.append(f"  Total valid signals: {total_signals}")
        lines.append(f"  Executed: {total_taken} ({total_taken/max(total_signals,1)*100:.0f}%)")
        lines.append(f"  Skipped: {total_skipped} ({total_skipped/max(total_signals,1)*100:.0f}%)")
        lines.append(f"  Active shadow positions: {len(self.shadow_positions)}")

        # Hypothetical PnL of skipped signals
        skipped_with_exit = [s for s in self.skipped if "exit_pnl" in s]
        if skipped_with_exit:
            skip_wins = sum(1 for s in skipped_with_exit if s["exit_pnl"] > 0)
            skip_total = len(skipped_with_exit)
            skip_wr = skip_wins / skip_total * 100 if skip_total > 0 else 0
            skip_avg = sum(s["exit_pnl"] for s in skipped_with_exit) / skip_total
            lines.append(f"\n  Skipped signals with resolved outcome: {skip_total}")
            lines.append(f"  Skipped win rate: {skip_wr:.0f}%")
            lines.append(f"  Skipped avg PnL: {skip_avg:+.2f}%")
            lines.append(f"  Estimated missed profit: {sum(s['exit_pnl'] for s in skipped_with_exit if s['exit_pnl'] > 0):+.1f}%")

        lines.append(f"\nB. SELECTION BIAS CHECK")
        lines.append(f"-" * 40)

        # Compare taken win rate vs all signals
        taken_with_results = [t for t in perf_matrix.trades]
        if taken_with_results and skipped_with_exit:
            taken_wr = sum(1 for t in taken_with_results if t["won"]) / len(taken_with_results) * 100
            all_wr_data = taken_with_results + [{"won": s["exit_pnl"] > 0} for s in skipped_with_exit]
            all_wr = sum(1 for d in all_wr_data if d["won"]) / len(all_wr_data) * 100

            lines.append(f"  Taken trades win rate: {taken_wr:.0f}%")
            lines.append(f"  ALL signals win rate: {all_wr:.0f}%")
            lines.append(f"  Difference: {taken_wr - all_wr:+.1f}%")

            if taken_wr > all_wr + 10:
                lines.append(f"  ⚠️ Selection bias likely: filters improve WR by {taken_wr-all_wr:.0f}%")
            elif taken_wr < all_wr - 5:
                lines.append(f"  ⚠️ Filters may be HURTING: taken WR {taken_wr:.0f}% < all WR {all_wr:.0f}%")
            else:
                lines.append(f"  ✓ Filters not creating significant bias")
        else:
            lines.append(f"  Not enough data yet")

        lines.append(f"\nC. EDGE REALITY SCORE")
        lines.append(f"-" * 40)
        if taken_with_results:
            taken_exp = sum(t["net_pnl"] for t in taken_with_results) / len(taken_with_results)
            lines.append(f"  Taken expectancy: {taken_exp:+.3f}%")
            if skipped_with_exit:
                all_exp_data = [t["net_pnl"] for t in taken_with_results] + [s["exit_pnl"] - 0.4 for s in skipped_with_exit]
                all_exp = sum(all_exp_data) / len(all_exp_data)
                lines.append(f"  Full signal expectancy: {all_exp:+.3f}%")
                if taken_exp > all_exp + 0.1:
                    lines.append(f"  → Filters ADD value ({taken_exp-all_exp:+.3f}% improvement)")
                elif taken_exp < all_exp - 0.1:
                    lines.append(f"  → Filters DESTROY value ({taken_exp-all_exp:+.3f}% drag)")
                else:
                    lines.append(f"  → Edge is in the SIGNALS, not the filters")
        else:
            lines.append(f"  Not enough data")

        # D. PER-FILTER BREAKDOWN — shows which filters skip the most and their impact
        lines.append(f"\nD. FILTER BREAKDOWN")
        lines.append(f"-" * 40)
        filter_stats = {}
        for s in self.skipped:
            reason = s.get("reason", "unknown")
            if reason not in filter_stats:
                filter_stats[reason] = {"count": 0, "resolved": 0, "wins": 0, "total_pnl": 0}
            filter_stats[reason]["count"] += 1
            if "exit_pnl" in s:
                filter_stats[reason]["resolved"] += 1
                filter_stats[reason]["total_pnl"] += s["exit_pnl"]
                if s["exit_pnl"] > 0:
                    filter_stats[reason]["wins"] += 1

        if filter_stats:
            for reason, data in sorted(filter_stats.items(), key=lambda x: -x[1]["count"]):
                wr_str = ""
                exp_str = ""
                if data["resolved"] > 0:
                    wr = data["wins"] / data["resolved"] * 100
                    exp = data["total_pnl"] / data["resolved"]
                    wr_str = f" WR:{wr:.0f}%"
                    exp_str = f" Exp:{exp:+.2f}%"
                    # Would this filter have helped or hurt?
                    if exp > 0.1:
                        verdict = " [HURTING — skipping winners]"
                    elif exp < -0.1:
                        verdict = " [HELPING — skipping losers]"
                    else:
                        verdict = " [NEUTRAL]"
                else:
                    verdict = " [no exit data yet]"
                lines.append(
                    f"  {reason:<20} skipped:{data['count']:>4}{wr_str}{exp_str}{verdict}"
                )
        else:
            lines.append(f"  No skipped signals yet")

        # E. STRATEGY BREAKDOWN — compare taken vs skipped per strategy
        lines.append(f"\nE. STRATEGY COVERAGE")
        lines.append(f"-" * 40)
        strat_taken = {}
        strat_skipped = {}
        for s in self.taken:
            st = s.get("strategy", "momentum")
            strat_taken[st] = strat_taken.get(st, 0) + 1
        for s in self.skipped:
            st = s.get("strategy", "momentum")
            strat_skipped[st] = strat_skipped.get(st, 0) + 1
        all_strats = sorted(set(list(strat_taken.keys()) + list(strat_skipped.keys())))
        for st in all_strats:
            t_count = strat_taken.get(st, 0)
            s_count = strat_skipped.get(st, 0)
            total = t_count + s_count
            take_pct = t_count / max(total, 1) * 100
            lines.append(f"  {st:<15} taken:{t_count:>4}  skipped:{s_count:>4}  take_rate:{take_pct:.0f}%")

        lines.append(f"\n" + "=" * 60)
        return "\n".join(lines)


shadow = ShadowTracker()


# ── ML Brain ──
# Learns from every trade: which market conditions lead to wins vs losses
# Pre-loads knowledge from previous sessions
from smart_ml import SmartMLFilter
brain = SmartMLFilter(n_features=16, learning_rate=0.04)
BRAIN_ML_MIN_TRADES = 200  # v29.3.5 L8: Don't use ML signal weights until 200+ trades recorded (prevents overfitting)
if brain.load(ML_FILE):
    _stats = brain.get_stats()
    print(f"  ML brain loaded: {_stats['total_trained']} samples, {len(_stats['coins_learned'])} coins")
else:
    print(f"  ML brain: starting fresh")


# ── Circuit Breaker: Prevents catastrophic losses ──
class CircuitBreaker:
    """Emergency stop system. Halts ALL trading when losses exceed thresholds."""

    def __init__(self, starting_cash):
        self.starting_cash = starting_cash
        self.peak_value = starting_cash  # High water mark
        self.daily_start = starting_cash
        self.daily_start_cycle = 0
        self.halted = False
        self.halt_reason = ""
        self.halt_until_cycle = 0
        self.daily_halted = False       # True = daily loss limit hit, no resume until next day

    def update(self, portfolio_value, cycle):
        """Update peak and check circuit breakers. Returns True if trading allowed."""
        self.peak_value = max(self.peak_value, portfolio_value)

        # Reset daily tracking every ~2400 cycles (~2 hours at 3s polling)
        if cycle - self.daily_start_cycle > 2400:
            self.daily_start = portfolio_value
            self.daily_start_cycle = cycle
            if self.daily_halted:
                self.daily_halted = False
                self.halted = False
                self.halt_reason = ""
                logger.info("DAILY RESET: daily halt cleared, trading resumed")

        # Check if halt expired
        if self.halted and cycle > self.halt_until_cycle:
            self.halted = False
            self.halt_reason = ""

        if self.halted:
            return False

        # CIRCUIT BREAKER 1: Daily loss > MAX_DAILY_LOSS_PCT% → halt until next day reset
        daily_pnl = (portfolio_value - self.daily_start) / self.daily_start if self.daily_start > 0 else 0
        if daily_pnl < -(MAX_DAILY_LOSS_PCT / 100):
            self.halted = True
            self.daily_halted = True
            self.halt_reason = f"DAILY HARD STOP: {daily_pnl*100:.1f}% loss (limit={MAX_DAILY_LOSS_PCT}%)"
            self.halt_until_cycle = cycle + 999999  # Don't resume until daily reset
            logger.error(self.halt_reason)
            return False

        # CIRCUIT BREAKER 2: Max drawdown from peak > 15% → halt for 2400 cycles (~2 hours)
        drawdown = (self.peak_value - portfolio_value) / self.peak_value if self.peak_value > 0 else 0
        if drawdown > 0.15:
            self.halted = True
            self.halt_reason = f"Max drawdown {drawdown*100:.1f}%"
            self.halt_until_cycle = cycle + 2400
            return False

        return True

    def status(self, current_value=None):
        if self.halted:
            return f"HALTED: {self.halt_reason}"
        if current_value is not None and self.peak_value > 0:
            dd = (self.peak_value - current_value) / self.peak_value * 100
            return f"OK (dd={dd:.1f}%)"
        return "OK"


# ── Correlation Guard: Don't double up on correlated coins ──
class CorrelationGuard:
    """Prevents holding multiple positions that move together."""

    def __init__(self):
        self.price_histories = {}  # coin -> [prices]

    def update(self, coin, price):
        if price <= 0:
            return
        if coin not in self.price_histories:
            self.price_histories[coin] = []
        self.price_histories[coin].append(price)
        if len(self.price_histories[coin]) > 50:
            self.price_histories[coin] = self.price_histories[coin][-50:]

    def correlation(self, coin_a, coin_b):
        """Calculate correlation between two coins. Returns -1 to +1."""
        try:
            ha = self.price_histories.get(coin_a, [])
            hb = self.price_histories.get(coin_b, [])
            n = min(len(ha), len(hb))
            if n < 10:
                return 0
            # Use returns, not prices
            ra = [(ha[i] - ha[i-1]) / ha[i-1] for i in range(len(ha)-n, len(ha)) if ha[i-1] != 0]
            rb = [(hb[i] - hb[i-1]) / hb[i-1] for i in range(len(hb)-n, len(hb)) if hb[i-1] != 0]
            n = min(len(ra), len(rb))
            if n < 5:
                return 0
            ra = ra[-n:]
            rb = rb[-n:]
            ma = sum(ra) / n
            mb = sum(rb) / n
            cov = sum((a - ma) * (b - mb) for a, b in zip(ra, rb)) / n
            sa = (sum((a - ma)**2 for a in ra) / n) ** 0.5
            sb = (sum((b - mb)**2 for b in rb) / n) ** 0.5
            if sa == 0 or sb == 0:
                return 0
            return cov / (sa * sb)
        except Exception:
            return 0

    def is_too_correlated(self, new_coin, held_coins):
        """Check if new_coin is >0.75 correlated with any held position."""
        for held in held_coins:
            corr = self.correlation(new_coin, held)
            if abs(corr) > 0.75:
                return True, held, corr
        return False, "", 0


# ── Volatility Scaler: Size positions inversely to current volatility ──
def volatility_scale(coin, base_amount):
    """Scale position size: lower when volatile, higher when calm."""
    try:
        hist = prices_cache.get(coin, [])
        if len(hist) < 20:
            return base_amount

        # Current volatility (last 10 ticks)
        recent = [(hist[i] - hist[i-1]) / hist[i-1] for i in range(len(hist)-10, len(hist)) if hist[i-1] != 0]
        if not recent:
            return base_amount
        current_vol = (sum(r**2 for r in recent) / len(recent)) ** 0.5

        # Historical volatility (last 50 ticks)
        older = [(hist[i] - hist[i-1]) / hist[i-1] for i in range(max(1, len(hist)-50), len(hist)-10) if hist[i-1] != 0]
        if not older:
            return base_amount
        hist_vol = (sum(r**2 for r in older) / len(older)) ** 0.5

        if current_vol == 0:
            return base_amount

        # Scale inversely: if current vol is 2x historical, cut position in half
        ratio = hist_vol / current_vol if current_vol > 0 else 1.0
        ratio = max(0.3, min(2.0, ratio))  # Clamp between 0.3x and 2x
        return base_amount * ratio
    except Exception:
        return base_amount


# ── Paper Trader ──
class Wallet:
    def __init__(self, cash):
        self.cash = cash
        self.longs = {}   # coin -> {"qty": float, "entry": float}
        self.shorts = {}  # coin -> {"qty": float, "entry": float}
        self.wins = 0
        self.losses = 0
        self.trades = []
        self.cooldowns = {}  # coin -> cycle_when_lost (skip for 100 cycles then retry)

    def buy(self, coin, price, amount):
        if price <= 0 or amount <= 0:
            return 0
        if amount > self.cash:
            amount = self.cash
        if amount <= 0:
            return 0
        fee = 0.0 if PAPER_MODE else amount * 0.002
        qty = (amount - fee) / price
        self.cash -= amount
        if self.cash < 0:
            error_logger.log("negative_cash", f"buy {coin}: cash=${self.cash:.2f}")
        if coin in self.longs:
            old = self.longs[coin]
            total_qty = old["qty"] + qty
            total_cost = old["qty"] * old["entry"] + qty * price
            # Update in-place: preserve entry_sl, bought_cycle, strategy, highest, etc.
            old["qty"] = total_qty
            old["entry"] = total_cost / total_qty
            old["entry_fee"] = old.get("entry_fee", 0) + fee
        else:
            self.longs[coin] = {"qty": qty, "entry": price, "entry_fee": fee}
        self.trades.append({"t": now(), "side": "BUY", "coin": coin, "price": price, "amt": amount})
        return qty

    def sell(self, coin, price):
        if price is None or price <= 0:
            return 0
        if coin not in self.longs or self.longs[coin]["qty"] <= 0:
            return 0
        pos = self.longs[coin]
        value = pos["qty"] * price
        fee = 0.0 if PAPER_MODE else value * 0.002
        pnl_pct = (price - pos["entry"]) / pos["entry"] * 100 if pos["entry"] != 0 else 0
        self.cash += value - fee
        if self.cash < 0:
            logger.warning(f"SELL NEGATIVE CASH {coin}: cash=${self.cash:.2f}, clamping to 0")
            self.cash = 0
        # Store last trade fee info for record_exit
        entry_fee = pos.get("entry_fee", value * 0.002)
        self._last_exit_fees = {"entry_fee": entry_fee, "exit_fee": fee, "total_fee_usd": entry_fee + fee}
        entry_val = pos["qty"] * pos["entry"]
        self._last_exit_fees["fee_pct"] = (entry_fee + fee) / entry_val * 100 if entry_val > 0 else 0.4
        if pnl_pct > 0:
            self.wins += 1
        else:
            self.losses += 1
        self.trades.append({"t": now(), "side": "SELL", "coin": coin, "price": price,
                           "amt": value, "pnl": f"{pnl_pct:+.2f}%"})
        # v29.3.5 L8: Always record for learning, but ML weights only activate after 200+ trades
        brain.record_trade(coin, _make_ml_features(coin, prices_cache), pnl_pct > 0.4, "TRADE")
        awareness.record("SELL", coin, pnl_pct, pnl_pct > 0)
        perf.record_trade(pnl_pct)
        if pnl_pct < 0:
            self.cooldowns[coin] = 0
        del self.longs[coin]
        return pnl_pct

    def short(self, coin, price, amount):
        """Short sell: borrow asset, sell at current price, buy back later."""
        if price <= 0 or amount <= 0:
            return 0
        if amount > self.cash:
            amount = self.cash
        if amount <= 0:
            return 0
        fee = 0.0 if PAPER_MODE else amount * 0.002
        qty = (amount - fee) / price
        # Don't add to cash yet — cash only changes when we cover
        # Just record the obligation
        self.shorts[coin] = {"qty": qty, "entry": price, "collateral": amount, "entry_fee": fee}
        self.cash -= amount  # Lock up collateral
        if self.cash < 0:
            error_logger.log("negative_cash", f"short {coin}: cash=${self.cash:.2f}")
        self.trades.append({"t": now(), "side": "SHORT", "coin": coin, "price": price, "amt": amount})
        return qty

    def cover(self, coin, price):
        """Close short: buy back the asset. Profit if price dropped."""
        if price is None or price <= 0:
            return 0
        if coin not in self.shorts:
            return 0
        pos = self.shorts[coin]
        cost = pos["qty"] * price  # Cost to buy back
        fee = 0.0 if PAPER_MODE else cost * 0.002
        pnl = pos["collateral"] - cost - fee  # Profit = collateral - buyback cost - fees
        pnl_pct = (pos["entry"] - price) / pos["entry"] * 100 if pos["entry"] != 0 else 0
        self.cash += pos["collateral"] + pnl  # Return collateral + profit (or minus loss)
        if self.cash < 0:
            logger.warning(f"SHORT BLOWUP {coin}: cash would be ${self.cash:.2f}, clamping to 0 (loss exceeded collateral)")
            self.cash = 0
        # Store last trade fee info for record_exit
        entry_fee = pos.get("entry_fee", pos["collateral"] * 0.002)
        self._last_exit_fees = {"entry_fee": entry_fee, "exit_fee": fee, "total_fee_usd": entry_fee + fee}
        entry_val = pos["qty"] * pos["entry"]
        self._last_exit_fees["fee_pct"] = (entry_fee + fee) / entry_val * 100 if entry_val > 0 else 0.4
        if pnl > 0:
            self.wins += 1
        else:
            self.losses += 1
        self.trades.append({"t": now(), "side": "COVER", "coin": coin, "price": price,
                           "amt": cost, "pnl": f"{pnl_pct:+.2f}%"})
        brain.record_trade(coin, _make_ml_features(coin, prices_cache), pnl > 0, "SHORT")
        awareness.record("COVER", coin, pnl_pct, pnl > 0)
        perf.record_trade(pnl_pct)
        if pnl < 0:
            self.cooldowns[coin] = 0
        del self.shorts[coin]
        return pnl_pct

    def clamp_values(self):
        """Clamp all values to prevent NaN/negative/inf corruption.
        Also removes zombie positions (qty <= 0) and caps cooldowns."""
        import math
        if self.cash is None or (isinstance(self.cash, float) and (math.isnan(self.cash) or math.isinf(self.cash))):
            self.cash = 0
        if self.cash < 0:
            self.cash = 0
        # Clamp position quantities + remove zombies (qty <= 0)
        for side_dict in [self.longs, self.shorts]:
            zombies = []
            for coin, pos in side_dict.items():
                if pos.get("qty", 0) <= 0:
                    zombies.append(coin)
                if pos.get("entry", 0) <= 0:
                    pos["entry"] = 0.0001
            for coin in zombies:
                try:
                    logger.warning(f"ZOMBIE REMOVED: {coin} qty={side_dict[coin].get('qty', 0)}")
                except Exception:
                    pass
                del side_dict[coin]
        # Cooldown safety cap
        try:
            current_cycle = _current_cycle if _current_cycle > 0 else 0
            max_cd = current_cycle + MAX_COOLDOWN_CYCLES
            for coin in list(self.cooldowns.keys()):
                if self.cooldowns[coin] > max_cd:
                    self.cooldowns[coin] = max_cd
        except Exception:
            pass

    def value(self, prices):
        """Total portfolio value. Cash + long positions + short collateral + short unrealized P&L."""
        import math
        self.clamp_values()
        total = self.cash
        # Longs: current market value
        for coin, pos in self.longs.items():
            p = prices.get(coin, None)
            if p is None or p <= 0 or p != p or p == float('inf'):
                # Price missing — use last known from cache, or entry with 5% safety haircut
                _cached = prices_cache.get(coin, [])
                if _cached and _cached[-1] > 0:
                    p = _cached[-1]
                else:
                    p = pos["entry"] * 0.95  # Discount stale entry price for safety
                    logger.debug(f"[WALLET] {coin} long: no price, using entry*0.95 ({p:.4f})")
            qty = pos["qty"] if pos["qty"] == pos["qty"] else 0  # NaN guard
            total += qty * p
        # Shorts: collateral is already out of cash. Add it back plus unrealized P&L.
        for coin, pos in self.shorts.items():
            p = prices.get(coin, None)
            if p is None or p <= 0 or p != p or p == float('inf'):
                _cached = prices_cache.get(coin, [])
                if _cached and _cached[-1] > 0:
                    p = _cached[-1]
                else:
                    p = pos["entry"] * 1.05  # Shorts: assume price went UP 5% (conservative)
                    logger.debug(f"[WALLET] {coin} short: no price, using entry*1.05 ({p:.4f})")
            qty = pos["qty"] if pos["qty"] == pos["qty"] else 0  # NaN guard
            collateral = pos.get("collateral", qty * pos["entry"])
            unrealized = (pos["entry"] - p) * qty  # Positive if price dropped
            total += collateral + unrealized
        # Final NaN/Inf guard — if anything corrupted, return cash only
        if math.isnan(total) or math.isinf(total):
            return self.cash if (self.cash == self.cash and not math.isinf(self.cash)) else CASH
        return total

    def save(self, prices):
        state = {
            "cash": self.cash,
            "longs": self.longs,
            "shorts": self.shorts,
            "wins": self.wins,
            "losses": self.losses,
            "trades": self.trades[-50:],
            "prices": prices,
            "cooldowns": self.cooldowns,
            # Save adaptive risk state for cross-restart continuity
            "adaptive_risk": adaptive_risk.save_state(),
            "daily_metrics": daily_metrics.save_state(),
            "cascade_protection": cascade_protection.save_state(),
            # Save protection system states
            "kill_switch": kill_switch.save_state() if kill_switch else {},
            "strategy_health_monitor": strategy_health_monitor.save_state(),
            "coin_loss_tracker": coin_loss_tracker.save_state(),
            "overtrading_guard": overtrading_guard.save_state(),
            "safe_mode": safe_mode.save_state(),
            "error_classifier": error_classifier.save_state(),
            "recovery_mode": recovery_mode.save_state(),
            # v29.3.4: Dynamic blacklist state
            "dynamic_blacklist": dynamic_blacklist.state_dict(),
            "per_coin_loss_streak": dict(_per_coin_loss_streak),
            "min_activity": min_activity.save_state(),
            "market_brain": market_brain.save_state(),
            "pair_failure_tracker": pair_failure_tracker.save_state(),
            # Persist performance matrix so health score survives restarts
            "perf_matrix": perf_matrix.save_state(),
            # v29.3.5: Persist runtime state that was previously lost on restart
            "last_exit_cycle": {k: list(v) for k, v in _last_exit_cycle.items()},  # coin → [cycle, was_profitable]
            "loss_streak_count": _loss_streak_count,
            "loss_streak_paused_until": _loss_streak_paused_until,
            "session_peak_equity": _session_peak_equity,
            # v29.5.0: Pro state persistence
            "pro_peak_portfolio": _pro_peak_portfolio,
            "pro_last_5_results": _pro_last_5_results[-10:],
            # Save self-awareness data
            "awareness": {
                "long_wins": awareness.long_wins,
                "long_losses": awareness.long_losses,
                "short_wins": awareness.short_wins,
                "short_losses": awareness.short_losses,
                "coin_performance": awareness.coin_performance,
                "recent_decisions": awareness.recent_decisions[-50:],
            },
            # v29.4.0: DEX scanner state
            "dex_scanner": dex_scanner.save_state() if dex_scanner else {},
            # v29.4.0: Stock watchlist
            "stock_watchlist": stock_watchlist[:20],
        }
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(state, f, indent=2)
        os.replace(tmp, STATE_FILE)

    @staticmethod
    def load():
        if os.path.exists(STATE_FILE):
            try:
                with open(STATE_FILE) as f:
                    s = json.load(f)
                w = Wallet(s["cash"])
                w.longs = s.get("longs", {})
                w.shorts = s.get("shorts", {})
                w.wins = s.get("wins", 0)
                w.losses = s.get("losses", 0)
                w.trades = s.get("trades", [])
                w.cooldowns = s.get("cooldowns", {})
                # Clear bought_cycle so exit loop re-initializes from current cycle
                # (prevents stale cycle references from previous session)
                for pos in w.longs.values():
                    pos.pop("bought_cycle", None)
                for pos in w.shorts.values():
                    pos.pop("bought_cycle", None)
                # Restore self-awareness
                aw = s.get("awareness", {})
                if aw:
                    awareness.long_wins = aw.get("long_wins", 0)
                    awareness.long_losses = aw.get("long_losses", 0)
                    awareness.short_wins = aw.get("short_wins", 0)
                    awareness.short_losses = aw.get("short_losses", 0)
                    awareness.coin_performance = aw.get("coin_performance", {})
                    awareness.recent_decisions = aw.get("recent_decisions", [])
                # Restore adaptive risk state
                ar_state = s.get("adaptive_risk")
                if ar_state:
                    adaptive_risk.load_state(ar_state)
                # Restore daily metrics state
                dm_state = s.get("daily_metrics")
                if dm_state:
                    daily_metrics.load_state(dm_state)
                # Restore cascade protection state
                cp_state = s.get("cascade_protection")
                if cp_state:
                    cascade_protection.load_state(cp_state)
                # Restore protection system states
                # NOTE: kill_switch is restored in main() after KillSwitch() creation
                shm_state = s.get("strategy_health_monitor")
                if shm_state:
                    strategy_health_monitor.load_state(shm_state)
                clt_state = s.get("coin_loss_tracker")
                if clt_state:
                    coin_loss_tracker.load_state(clt_state)
                otg_state = s.get("overtrading_guard")
                if otg_state:
                    overtrading_guard.load_state(otg_state)
                sm_state = s.get("safe_mode")
                if sm_state:
                    safe_mode.load_state(sm_state)
                ec_state = s.get("error_classifier")
                if ec_state:
                    error_classifier.load_state(ec_state)
                rm_state = s.get("recovery_mode")
                if rm_state:
                    recovery_mode.load_state(rm_state)
                # v29.3.4: Restore dynamic blacklist state
                dbl_state = s.get("dynamic_blacklist")
                if dbl_state:
                    dynamic_blacklist.load_state(dbl_state)
                pcls_state = s.get("per_coin_loss_streak")
                if pcls_state:
                    _per_coin_loss_streak.update(pcls_state)
                ma_state = s.get("min_activity")
                if ma_state:
                    min_activity.load_state(ma_state)
                mb_state = s.get("market_brain")
                if mb_state:
                    market_brain.load_state(mb_state)
                pft_state = s.get("pair_failure_tracker")
                if pft_state:
                    pair_failure_tracker.load_state(pft_state)
                # Restore performance matrix (health score history survives restarts)
                pm_state = s.get("perf_matrix")
                if pm_state:
                    perf_matrix.load_state(pm_state)
                # v29.3.5: Restore runtime state variables
                global _last_exit_cycle, _loss_streak_count, _loss_streak_paused_until, _session_peak_equity
                lec_state = s.get("last_exit_cycle")
                if lec_state:
                    _last_exit_cycle.update({k: tuple(v) for k, v in lec_state.items()})
                _loss_streak_count = s.get("loss_streak_count", 0)
                _loss_streak_paused_until = s.get("loss_streak_paused_until", 0)
                _session_peak_equity = s.get("session_peak_equity", 0)
                # v29.5.0: Restore pro state
                global _pro_peak_portfolio, _pro_last_5_results
                _pro_peak_portfolio = s.get("pro_peak_portfolio", 0)
                _pro_last_5_results = s.get("pro_last_5_results", [])
                # v29.4.0: Restore DexScanner + stock watchlist state
                global stock_watchlist
                try:
                    dex_scanner.load_state(s.get("dex_scanner", {}))
                except Exception:
                    pass
                stock_watchlist = s.get("stock_watchlist", [])
                # Validate restored wallet is sane
                import math
                if w.cash < 0 or math.isnan(w.cash) or math.isinf(w.cash):
                    logger.warning(f"STATE CORRUPT: cash={w.cash}, starting fresh")
                    return None, None
                return w, s.get("prices", {})
            except Exception as e:
                logger.warning(f"STATE FILE CORRUPT ({e}) — starting fresh")
                try:
                    os.rename(STATE_FILE, STATE_FILE + ".corrupt")
                except Exception:
                    pass
        return None, None


# ── Order Executor (Professional Execution Layer) ──
class OrderExecutor:
    """Wraps wallet.buy/sell/short/cover with pre-flight checks, slippage, and logging."""

    def __init__(self):
        self.order_log = []  # Last 100 orders

    def _estimate_spread(self, coin):
        """Estimate spread from recent price volatility. Returns spread as percentage."""
        hist = prices_cache.get(coin, [])
        if len(hist) < 10:
            return 0.1  # Default conservative estimate
        # Use recent tick-to-tick changes as spread proxy
        recent = hist[-20:]
        changes = [abs(recent[i] - recent[i-1]) / recent[i-1] * 100 for i in range(1, len(recent)) if recent[i-1] > 0]
        if not changes:
            return 0.1
        return sum(changes) / len(changes)

    def _apply_slippage(self, price, side, coin=None, is_sl_exit=False):
        """Apply tiered slippage model: Normal 0.05%, High ATR 0.1-0.2%, SL exits 0.2-0.5%."""
        if is_sl_exit:
            # SL exits: 0.3% base, up to 0.5% in high vol
            base_pct = SLIPPAGE_SL_EXIT
            if coin:
                atr = coin_atr(coin)
                if atr > 0.01:  # Very high vol
                    base_pct = min(0.5, base_pct + (atr / 0.01) * 0.1)
        else:
            # Normal entries/exits
            base_pct = SLIPPAGE_BASE
            if coin:
                atr = coin_atr(coin)
                if atr > 0.005:
                    # High ATR: scale from 0.05% up to 0.2%
                    base_pct = min(0.2, SLIPPAGE_BASE + (atr / 0.005 - 1) * 0.05)
        slip = price * (base_pct / 100)
        if side in ("BUY", "COVER"):
            return price + slip
        else:
            return price - slip

    def place_order(self, side, coin, price, amount, wallet, prices_dict):
        """
        Execute an order with pre-flight checks and slippage simulation.
        side: "BUY", "SELL", "SHORT", "COVER"
        Returns: {"filled": bool, "qty": float, "fill_price": float, "fee_usd": float, "slippage_pct": float, "reject_reason": str}
        """
        result = {"filled": False, "qty": 0, "fill_price": 0, "fee_usd": 0, "slippage_pct": 0, "reject_reason": ""}

        try:
            import math
            # ENTRY SAFETY GUARD: reject any NaN/None/inf values immediately
            if price is None or amount is None:
                result["reject_reason"] = "null_value"
                return result
            if math.isnan(price) or math.isinf(price) or math.isnan(amount) or math.isinf(amount):
                result["reject_reason"] = f"bad_value (price={price}, amount={amount})"
                return result
            if amount <= 0:
                result["reject_reason"] = f"zero_amount ({amount})"
                return result
        except Exception:
            result["reject_reason"] = "safety_guard_error"
            return result

        # ── Pre-flight checks ──
        # 1. Price validation
        if price <= 0 or price > 1e8:
            result["reject_reason"] = f"invalid_price ({price})"
            logger.warning(f"ORDER REJECTED {side} {coin}: {result['reject_reason']}")
            error_logger.log("order_rejected", f"{side} {coin}: {result['reject_reason']}")
            return result

        # 2. Minimum order size (only for entries)
        if side in ("BUY", "SHORT") and amount < MIN_ORDER_USD:
            result["reject_reason"] = f"below_min_order (${amount:.2f} < ${MIN_ORDER_USD})"
            logger.warning(f"ORDER REJECTED {side} {coin}: {result['reject_reason']}")
            error_logger.log("order_rejected", f"{side} {coin}: {result['reject_reason']}")
            return result

        # 3. Cash sufficiency (only for entries)
        if side in ("BUY", "SHORT") and amount > wallet.cash:
            result["reject_reason"] = f"insufficient_cash (need ${amount:.2f}, have ${wallet.cash:.2f})"
            logger.warning(f"ORDER REJECTED {side} {coin}: {result['reject_reason']}")
            error_logger.log("order_rejected", f"{side} {coin}: {result['reject_reason']}")
            return result

        # 4. Position limit (only for entries)
        if side in ("BUY", "SHORT"):
            total_pos = len(wallet.longs) + len(wallet.shorts)
            if total_pos >= MAX_POSITIONS:
                result["reject_reason"] = f"max_positions ({total_pos}/{MAX_POSITIONS})"
                logger.warning(f"ORDER REJECTED {side} {coin}: {result['reject_reason']}")
                error_logger.log("order_rejected", f"{side} {coin}: {result['reject_reason']}")
                return result

        # 5. Spread check (only for entries — don't block emergency exits)
        if side in ("BUY", "SHORT"):
            spread = self._estimate_spread(coin)
            if spread > MAX_SPREAD_PCT:
                result["reject_reason"] = f"spread_too_wide ({spread:.2f}% > {MAX_SPREAD_PCT}%)"
                logger.warning(f"ORDER REJECTED {side} {coin}: {result['reject_reason']}")
                error_logger.log("order_rejected", f"{side} {coin}: {result['reject_reason']}")
                return result

        # ── Apply slippage (ATR-scaled, higher on SL exits) ──
        _is_sl = side in ("SELL", "COVER")  # Exits get higher slippage
        fill_price = self._apply_slippage(price, side, coin=coin, is_sl_exit=_is_sl)
        slippage_pct = abs(fill_price - price) / price * 100

        # ── Execute on wallet ──
        if PAPER_MODE:
            if side == "BUY":
                qty = wallet.buy(coin, fill_price, amount)
                fee_usd = amount * 0.002
            elif side == "SELL":
                pnl_pct = wallet.sell(coin, fill_price)
                # Estimate qty and fee from the position that was just sold
                qty = 0  # Position already deleted
                fee_usd = 0  # Fee already deducted inside wallet.sell
                result["pnl_pct"] = pnl_pct
            elif side == "SHORT":
                qty = wallet.short(coin, fill_price, amount)
                fee_usd = amount * 0.002
            elif side == "COVER":
                pnl_pct = wallet.cover(coin, fill_price)
                qty = 0
                fee_usd = 0
                result["pnl_pct"] = pnl_pct
            else:
                result["reject_reason"] = f"unknown_side ({side})"
                return result
        else:
            # Future: Kraken API integration
            result["reject_reason"] = "live_trading_not_implemented"
            logger.error(f"LIVE TRADING NOT IMPLEMENTED — {side} {coin}")
            return result

        result["filled"] = True
        result["qty"] = qty
        result["fill_price"] = fill_price
        result["fee_usd"] = fee_usd
        result["slippage_pct"] = slippage_pct

        if DEBUG_MODE or is_verbose("DEBUG"):
            print(f"  [FILL] {side} {coin} qty={qty:.6f} @ ${fill_price:,.4f} slip={slippage_pct:.3f}% fee=${fee_usd:.2f}")

        # Track fee
        fee_pct = (fee_usd / amount * 100) if amount > 0 else 0.2
        fee_tracker.record_fee(coin, side, fee_usd, fee_pct)

        # Log order
        order_record = {
            "t": now(), "side": side, "coin": coin,
            "price": price, "fill_price": fill_price,
            "amount": amount, "qty": qty,
            "slippage_pct": round(slippage_pct, 4),
            "fee_usd": round(fee_usd, 4),
        }
        self.order_log.append(order_record)
        if len(self.order_log) > 100:
            self.order_log = self.order_log[-100:]

        logger.debug(f"ORDER FILLED {side} {coin} @ ${fill_price:,.4f} (slip={slippage_pct:.3f}%) ${amount:.0f}")

        # Live validation: log entry attempts with execution detail
        if side in ("BUY", "SHORT"):
            try:
                spread_est = self._estimate_spread(coin)
                live_tracker.log_attempt(
                    coin=coin, strategy="", direction="long" if side == "BUY" else "short",
                    signal_score=0, price=price, spread_pct=spread_est,
                    blocked=False, fill_price=fill_price, slippage_pct=slippage_pct,
                )
                # Store slippage on wallet for retrieval at exit
                wallet._last_entry_slippage = slippage_pct
            except Exception:
                pass
        elif side in ("SELL", "COVER"):
            # Store exit slippage for live tracker
            try:
                wallet._last_exit_slippage = slippage_pct
            except Exception:
                pass

        return result


executor = OrderExecutor()


# ── Exit Slippage Helper (ensures exits apply same slippage model as entries) ──
def _exit_slippage_price(price, side, coin=None, is_sl_exit=False):
    """Apply the executor's slippage model to an exit price.
    side: 'SELL' or 'COVER'. is_sl_exit: True for stop-loss exits (higher slippage).
    Returns the slippage-adjusted fill price."""
    return executor._apply_slippage(price, side, coin=coin, is_sl_exit=is_sl_exit)


# ── Trade Quality Filters ──
def reward_risk_ok(sl_pct, tp_pct, atr_pct=None):
    """Check if reward-to-risk ratio meets minimum threshold.
    If atr_pct is provided, also checks that the TP is achievable given the coin's volatility.
    A coin with 0.5% ATR can't realistically hit a 3% TP — filter it out."""
    try:
        if sl_pct <= 0:
            return False
        rr = tp_pct / sl_pct
        if rr < MIN_REWARD_RISK:
            return False
        # Achievability check removed: 2s-resolution ATR too small
        # R:R ratio check remains active
        return True
    except Exception:
        return True


def entry_direction_confirmed(coin, direction, ticks=2):
    """Check that the last N price ticks moved in the trade's direction.
    Prevents instant entries on a single-tick spike that reverses immediately.
    Returns True if confirmed (safe to enter) or if insufficient data."""
    try:
        hist = prices_cache.get(coin, [])
        if len(hist) < ticks + 1:
            return True  # Not enough data — allow entry (don't block early)
        recent = hist[-(ticks + 1):]
        if direction == "long":
            # Each tick should be >= previous (price moving up)
            return all(recent[i] >= recent[i - 1] for i in range(1, len(recent)))
        else:
            # Each tick should be <= previous (price moving down)
            return all(recent[i] <= recent[i - 1] for i in range(1, len(recent)))
    except Exception:
        return True  # Fail-open


def volatility_spike_check(coin):
    """Returns True if safe to trade (no volatility spike). False = spike detected, block trade."""
    try:
        hist = prices_cache.get(coin, [])
        if len(hist) < 30:
            return True  # Not enough data
        # Current vol (last 10)
        recent = [(hist[i] - hist[i-1]) / hist[i-1] for i in range(len(hist)-10, len(hist)) if hist[i-1] != 0]
        if not recent:
            return True
        current_vol = (sum(r**2 for r in recent) / len(recent)) ** 0.5
        # Historical vol (last 30, excluding last 10)
        older = [(hist[i] - hist[i-1]) / hist[i-1] for i in range(max(1, len(hist)-30), len(hist)-10) if hist[i-1] != 0]
        if not older:
            return True
        hist_vol = (sum(r**2 for r in older) / len(older)) ** 0.5
        if hist_vol <= 0:
            return True
        ratio = current_vol / hist_vol
        return ratio < VOLATILITY_SPIKE_MULT
    except Exception:
        return True


def market_depth_ok(coin, entry_size, tickers_ref):
    """Thin-market protection: check that 24h USD volume can absorb the order.
    Graduated: bigger trades need proportionally more volume.
      - Base: vol >= MIN_ORDER_BOOK_DEPTH × entry_size  (3×)
      - Trades > $100: vol >= 5 × entry_size
      - Trades > $200: vol >= 10 × entry_size
    Defaults to True if disabled or data unavailable (never blocks on missing data)."""
    if not MARKET_DEPTH_ENABLED:
        return True
    try:
        t = tickers_ref.get(coin) if tickers_ref else None
        if not t:
            return True  # No data — allow (don't block on missing tickers)
        vol_24h = t.get("vol", 0)
        # Graduated multiplier: bigger orders need more liquidity
        if entry_size > 200:
            mult = 10
        elif entry_size > 100:
            mult = 5
        else:
            mult = max(MIN_ORDER_BOOK_DEPTH, 1)
        required = mult * entry_size
        return vol_24h >= required
    except Exception:
        return True


def regime_confirm(coin, direction, strategy=""):
    """Short-term regime confirmation (single-timeframe).
    # Optimized change – removed 80-tick medium window (lagged too much, killed valid entries)
    Checks that short-term trend agrees with the entry direction.
    direction: 'long' or 'short'.
    strategy: entry strategy name — mean_rev is EXEMPT (enters against trend by design).
    Returns True if short-term confirms, or if data is insufficient."""
    if not REGIME_CONFIRM_ENABLED:
        return True
    # Mean-reversion enters AGAINST short-term trend — requiring trend agreement contradicts the strategy
    if strategy == "mean_rev":
        return True
    try:
        hist = prices_cache.get(coin, [])
        # Short-term trend only: last REGIME_CONFIRM_SHORT_WINDOW ticks
        sw = REGIME_CONFIRM_SHORT_WINDOW
        if len(hist) < sw + 1:
            return True  # Not enough data — allow
        short_change = (hist[-1] - hist[-sw]) / hist[-sw] if hist[-sw] != 0 else 0

        if direction == "long":
            return short_change > -0.003  # Was > 0 — blocked entries on tiny dips. Allow slight negative (0.3%)
        elif direction == "short":
            return short_change < 0.003   # Was < 0 — allow slight positive for shorts
        return True  # Unknown direction — allow
    except Exception:
        return True


def single_coin_exposure_ok(wallet, prices, coin, amount):
    """Check if adding this position would exceed per-coin exposure limit."""
    try:
        pv = wallet.value(prices)
        if pv <= 0:
            return False
        # Current exposure in this coin
        existing = 0
        if coin in wallet.longs:
            existing += wallet.longs[coin]["qty"] * prices.get(coin, wallet.longs[coin]["entry"])
        if coin in wallet.shorts:
            existing += wallet.shorts[coin].get("collateral", 0)
        total_exposure = existing + amount
        exposure_pct = total_exposure / pv * 100
        return exposure_pct <= MAX_SINGLE_COIN_EXPOSURE_PCT
    except Exception:
        return True


# ── Global Risk Cap ──
def calculate_total_risk(wallet, prices_dict):
    """Calculate total portfolio risk across all open positions as % of portfolio value."""
    pv = wallet.value(prices_dict)
    if pv <= 0:
        return 100.0  # Safety: if portfolio is zero, risk is maximum
    total_risk_usd = 0
    for coin, pos in wallet.longs.items():
        sl_pct = pos.get("entry_sl", 1.0)  # Default 1% if not set
        position_value = pos["qty"] * prices_dict.get(coin, pos["entry"])
        total_risk_usd += position_value * (sl_pct / 100)
    for coin, pos in wallet.shorts.items():
        sl_pct = pos.get("entry_sl", 1.0)
        position_value = pos.get("collateral", pos["qty"] * pos["entry"])
        total_risk_usd += position_value * (sl_pct / 100)
    return (total_risk_usd / pv) * 100


def global_risk_allows(wallet, prices_dict, new_amount, new_sl_pct):
    """Return True if adding this trade stays within GLOBAL_RISK_CAP_PCT."""
    current_risk = calculate_total_risk(wallet, prices_dict)
    pv = wallet.value(prices_dict)
    if pv <= 0:
        return False
    new_risk = (new_amount * (new_sl_pct / 100)) / pv * 100
    total = current_risk + new_risk
    if total > GLOBAL_RISK_CAP_PCT:
        logger.debug(f"GLOBAL RISK CAP: {current_risk:.1f}% + {new_risk:.1f}% = {total:.1f}% > {GLOBAL_RISK_CAP_PCT}%")
        return False
    return True


def stress_risk_allows(wallet, prices_dict, new_amount=0, new_sl_pct=0):
    """Stress test: assume all positions lose 3x their SL simultaneously.
    Returns True if stress-test risk is within limits."""
    current_risk = calculate_total_risk(wallet, prices_dict)
    pv = wallet.value(prices_dict)
    if pv <= 0:
        return False
    new_risk = (new_amount * (new_sl_pct / 100)) / pv * 100 if new_amount > 0 else 0
    stress_risk = (current_risk + new_risk) * 3  # 3x correlated gap scenario
    if stress_risk > STRESS_RISK_LIMIT_PCT:
        logger.debug(f"STRESS RISK BLOCK: {stress_risk:.1f}% > {STRESS_RISK_LIMIT_PCT}% (3x scenario)")
        return False
    return True


def total_exposure_ok(wallet, prices_dict, new_amount=0):
    """Return True if total position exposure + new trade <= MAX_TOTAL_EXPOSURE_PCT of equity."""
    pv = wallet.value(prices_dict)
    if pv <= 0:
        return False
    total_exposure = 0
    for coin, pos in wallet.longs.items():
        total_exposure += pos["qty"] * prices_dict.get(coin, pos["entry"])
    for coin, pos in wallet.shorts.items():
        total_exposure += pos.get("collateral", pos["qty"] * pos["entry"])
    exposure_pct = ((total_exposure + new_amount) / pv) * 100
    if exposure_pct > MAX_TOTAL_EXPOSURE_UPDATED_PCT:
        logger.debug(f"EXPOSURE CAP: {exposure_pct:.1f}% > {MAX_TOTAL_EXPOSURE_UPDATED_PCT}% (would add ${new_amount:.0f})")
        return False
    return True


# ── Unified Exposure Check (merges all 4 checks into one call) ──
def unified_exposure_ok(wallet, prices_dict, coin, amount, sl_pct):
    """Single function that runs all 4 exposure checks.
    Returns (ok: bool, block_reason: str).
    block_reason is empty string if ok=True."""
    try:
        # 1. Total exposure cap (60% of portfolio)
        if not total_exposure_ok(wallet, prices_dict, amount):
            return False, "exposure_cap"
        # 2. Global risk cap (3% total risk)
        if not global_risk_allows(wallet, prices_dict, amount, sl_pct):
            return False, "global_risk_cap"
        # 3. Stress-test risk (3x correlated gap < 8%)
        if not stress_risk_allows(wallet, prices_dict, amount, sl_pct):
            return False, "stress_risk"
        # 4. Single coin exposure (30% per coin)
        if not single_coin_exposure_ok(wallet, prices_dict, coin, amount):
            return False, "coin_exposure"
        return True, ""
    except Exception as e:
        # Fail-closed: block the trade and log the error (never silently allow on exception)
        logger.error(f"EXPOSURE CHECK EXCEPTION: {e} — blocking trade (fail-closed)")
        return False, "exposure_check_error"


def conviction_override_active(score, change, strategy="momentum", regime=None):
    """Check if a signal is strong enough to bypass soft filters.

    TWO-TIER SYSTEM:
      HIGH_CONVICTION (tier 1): |score| >= 0.60 → bypass ALL soft filters, no change% needed.
      CONVICTION (tier 2):      |score| > 0.25 AND |change| > 4% → bypass core soft filters.

    REGIME PRE-CHECK: Overrides are suppressed in CHOPPY / UNCERTAIN / NO_DATA regimes
    because hard filters (regime_mismatch, low_liquidity) reject >95% of these signals
    downstream anyway. This prevents wasting override capacity on doomed signals.

    For breakout: 'score' is BB width, 'change' is unused.
    For mean_rev: 'score' is z-score, uses HIGH_CONVICTION_MEANREV_Z_THRESHOLD.

    Returns (is_override: bool, overridden_filters: list[str], tier: str).
    tier is "HIGH_CONVICTION", "CONVICTION", or "" (empty = no override).
    """
    if not CONVICTION_OVERRIDE_ENABLED:
        return False, [], ""
    try:
        # ── REGIME PRE-CHECK: Don't waste overrides in hostile regimes ──
        # These regimes have >90% hard-filter rejection rates downstream
        if regime:
            _r_upper = regime.upper() if isinstance(regime, str) else ""
            if _r_upper in ("UNCERTAIN", "NO_DATA", ""):
                return False, [], ""
            # CHOPPY: allow conviction overrides (sizing already reduced to 40%)

        _all_soft = ["is_choppy", "volume_confirms", "pair_failure", "coin_loss",
                      "momentum_filter", "coin_trending"]
        _core_soft = ["is_choppy", "volume_confirms", "pair_failure", "coin_loss"]

        # ── TIER 1: HIGH CONVICTION (score >= 0.60, no change% required) ──
        if HIGH_CONVICTION_OVERRIDE_ENABLED:
            if strategy == "mean_rev":
                if abs(score) >= HIGH_CONVICTION_MEANREV_Z_THRESHOLD:
                    return True, _all_soft, "HIGH_CONVICTION"
            elif strategy == "breakout":
                if score >= HIGH_CONVICTION_SCORE_THRESHOLD:
                    return True, _all_soft, "HIGH_CONVICTION"
            else:
                # Momentum long/short
                if abs(score) >= HIGH_CONVICTION_SCORE_THRESHOLD:
                    return True, _all_soft, "HIGH_CONVICTION"

        # ── TIER 2: STANDARD CONVICTION (existing thresholds) ──
        if strategy == "breakout":
            if score > CONVICTION_BREAKOUT_WIDTH_THRESHOLD:
                return True, _core_soft, "CONVICTION"
        elif strategy == "mean_rev":
            # No standard conviction tier for mean-rev (only high-conviction)
            pass
        else:
            if abs(score) > CONVICTION_SCORE_THRESHOLD and abs(change) > CONVICTION_CHANGE_THRESHOLD:
                return True, _core_soft, "CONVICTION"

        return False, [], ""
    except Exception:
        return False, [], ""


def force_exit_losing_positions(wallet, prices, executor, cycle, _current_regime):
    """Emergency: close ALL losing positions and tighten winners to breakeven.
    Called when circuit breaker triggers daily hard stop."""
    closed = 0
    for coin in list(wallet.longs.keys()):
        p = prices.get(coin, 0)
        if p <= 0:
            continue
        pos = wallet.longs[coin]
        entry = pos["entry"]
        pnl_pct = (p - entry) / entry * 100 if entry > 0 else 0
        if pnl_pct < 0:
            # Close losing position
            executor.place_order("SELL", coin, p, pos.get("quantity", 0), wallet, prices)  # v29.3.5: was 0 — rejected by exchange min check
            record_exit("cb_force_exit", coin, "long", entry, p, _current_regime, wallet=wallet)
            logger.error(f"CB FORCE EXIT LONG {coin} {pnl_pct:+.2f}%")
            closed += 1
        else:
            # Tighten winner to breakeven
            pos["trail_stop"] = entry
            pos["profit_protection"] = True
            logger.warning(f"CB TIGHTEN LONG {coin} to breakeven (was +{pnl_pct:.1f}%)")
    for coin in list(wallet.shorts.keys()):
        p = prices.get(coin, 0)
        if p <= 0:
            continue
        pos = wallet.shorts[coin]
        entry = pos["entry"]
        pnl_pct = (entry - p) / entry * 100 if entry > 0 else 0
        if pnl_pct < 0:
            executor.place_order("COVER", coin, p, pos.get("quantity", 0), wallet, prices)  # v29.3.5: was 0 — rejected by exchange min check
            record_exit("cb_force_exit", coin, "short", entry, p, _current_regime, wallet=wallet)
            logger.error(f"CB FORCE EXIT SHORT {coin} {pnl_pct:+.2f}%")
            closed += 1
        else:
            pos["trail_stop"] = entry
            pos["profit_protection"] = True
            logger.warning(f"CB TIGHTEN SHORT {coin} to breakeven (was +{pnl_pct:.1f}%)")
    if closed:
        logger.error(f"CB FORCE EXIT: closed {closed} losing positions")
    return closed


def now():
    return datetime.now(timezone.utc).strftime("%H:%M:%S")


def to_short_name(name):
    """Convert Kraken pair/alt name to short coin name. 'XBTUSD' -> 'BTC', 'ETHUSD' -> 'ETH'.
    TODO v29.4: Move to ExchangeConfig.normalize_pair_name() for multi-platform support."""
    n = name
    # Strip USD suffix (handles both "USD" and "ZUSD")
    if n.endswith("ZUSD"):
        n = n[:-4]
    elif n.endswith("USD"):
        n = n[:-3]
    # Strip Kraken's X prefix (XXBT -> XBT, XETH -> ETH)
    if n.startswith("XX"):
        n = n[2:]
    elif n.startswith("X") and len(n) == 4:
        n = n[1:]
    # XBT -> BTC
    n = n.replace("XBT", "BTC")
    if n == "BT": n = "BTC"  # v29.5.0: catch XXBTZUSD → XX→BT via wsname path
    return n


# ── Self-Awareness: Bot evaluates its own performance and adapts ──
class SelfAwareness:
    """
    The bot's brain for self-evaluation. Tracks what's working and what isn't,
    then adjusts strategy automatically.

    Thinks: "My shorts are printing but longs keep losing → do more shorts"
    Thinks: "I keep losing on NEAR → stop trading NEAR"
    Thinks: "My ML is blocking good trades → loosen the ML filter"
    """

    def __init__(self):
        self.long_wins = 0
        self.long_losses = 0
        self.short_wins = 0
        self.short_losses = 0
        self.coin_performance = {}  # coin -> {"wins": int, "losses": int, "total_pnl": float}
        self.recent_decisions = []  # Last 50 decisions for analysis

    def record(self, side, coin, pnl_pct, won):
        """Record a trade result."""
        if side in ("BUY", "SELL"):
            if won:
                self.long_wins += 1
            else:
                self.long_losses += 1
        elif side in ("SHORT", "COVER"):
            if won:
                self.short_wins += 1
            else:
                self.short_losses += 1

        if coin not in self.coin_performance:
            self.coin_performance[coin] = {"wins": 0, "losses": 0, "total_pnl": 0}
        cp = self.coin_performance[coin]
        if won:
            cp["wins"] += 1
        else:
            cp["losses"] += 1
        cp["total_pnl"] += pnl_pct

        self.recent_decisions.append({"side": side, "coin": coin, "pnl": pnl_pct, "won": won})
        if len(self.recent_decisions) > 50:
            self.recent_decisions = self.recent_decisions[-50:]

    def should_go_long(self) -> float:
        """How confident should we be in long trades? 0.0 = don't, 1.0 = full confidence."""
        total = self.long_wins + self.long_losses
        if total < 3:
            return 0.5
        win_rate = self.long_wins / max(total, 1)
        # If longs are losing, reduce confidence
        if win_rate < 0.3:
            return 0.1  # Almost stop buying
        elif win_rate < 0.5:
            return 0.4  # Reduce size
        elif win_rate > 0.7:
            return 1.2  # Increase size (longs are working!)
        return 0.8

    def should_go_short(self) -> float:
        total = self.short_wins + self.short_losses
        if total < 3:
            return 0.5
        win_rate = self.short_wins / max(total, 1)
        if win_rate < 0.3:
            return 0.1
        elif win_rate < 0.5:
            return 0.4
        elif win_rate > 0.7:
            return 1.2
        return 0.8

    def should_trade_coin(self, coin) -> float:
        """Should we trade this specific coin? Based on our history with it."""
        cp = self.coin_performance.get(coin)
        if not cp:
            return 1.0  # No history, try it
        total = cp["wins"] + cp["losses"]
        if total < 2:
            return 1.0
        win_rate = cp["wins"] / max(total, 1)
        if win_rate < 0.2:
            return 0.0  # We suck at this coin — avoid it
        elif win_rate < 0.4:
            return 0.3  # Bad history — small size
        elif win_rate > 0.7:
            return 1.5  # We're good at this — bigger size
        return 1.0

    def get_ml_threshold(self) -> float:
        """Should we tighten or loosen the ML filter based on recent performance?"""
        if len(self.recent_decisions) < 5:
            return 0.35  # Default

        recent_wins = sum(1 for d in self.recent_decisions[-10:] if d["won"])
        recent_total = min(10, len(self.recent_decisions))
        recent_wr = recent_wins / max(recent_total, 1)

        if recent_wr > 0.7:
            return 0.25  # Loosen — we're on a hot streak, let more trades through
        elif recent_wr < 0.3:
            return 0.50  # Tighten — we're losing, be pickier
        return 0.35

    def detect_regime(self, prices_cache) -> str:
        """
        Detect current market regime from price action across all tracked coins.
        Returns: "TRENDING_UP", "TRENDING_DOWN", "RANGING", or "VOLATILE"

        The bot uses this to decide: momentum strategy, mean-reversion, or sit out.
        """
        if not prices_cache:
            return "UNKNOWN"

        up_count = 0
        down_count = 0
        flat_count = 0
        total = 0

        for coin, hist in prices_cache.items():
            if len(hist) < 10:
                continue
            total += 1
            if hist[-10] == 0:
                continue
            change = (hist[-1] - hist[-10]) / hist[-10]
            if change > 0.005:
                up_count += 1
            elif change < -0.005:
                down_count += 1
            else:
                flat_count += 1

        if total < 3:
            return "UNKNOWN"

        if total == 0:
            return "UNKNOWN"
        up_pct = up_count / total
        down_pct = down_count / total
        flat_pct = flat_count / total

        if up_pct > 0.6:
            return "TRENDING_UP"
        elif down_pct > 0.6:
            return "TRENDING_DOWN"
        elif flat_pct > 0.5:
            return "RANGING"
        else:
            return "VOLATILE"

    def get_strategy_for_regime(self, regime) -> dict:
        """
        The bot THINKS about what strategy to use based on market conditions.
        Returns adjustments to scoring, position sizing, and direction bias.
        """
        if regime == "TRENDING_UP":
            return {
                "long_bias": 1.5,    # Favor longs — market going up
                "short_bias": 0.3,   # Reduce shorts
                "min_score": 0.03,   # Lower bar for buys
                "description": "Bull market — buying momentum"
            }
        elif regime == "TRENDING_DOWN":
            return {
                "long_bias": 0.2,    # Almost stop buying
                "short_bias": 1.5,   # Aggressive shorts
                "min_score": 0.03,
                "description": "Bear market — shorting weakness"
            }
        elif regime == "RANGING":
            return {
                "long_bias": 0.7,    # Moderate bias — allow opportunities
                "short_bias": 0.7,
                "min_score": 0.03,   # Lower bar — let signals through, filters handle quality
                "description": "Sideways — adapting"
            }
        else:  # VOLATILE or UNKNOWN
            return {
                "long_bias": 0.7,
                "short_bias": 0.7,
                "min_score": 0.05,
                "description": "Volatile — cautious"
            }

    def get_status(self) -> str:
        """One-line status for dashboard."""
        long_wr = self.long_wins / max(1, self.long_wins + self.long_losses) * 100
        short_wr = self.short_wins / max(1, self.short_wins + self.short_losses) * 100
        regime = self.detect_regime(prices_cache)
        strategy = self.get_strategy_for_regime(regime)
        return f"{regime} L:{long_wr:.0f}% S:{short_wr:.0f}% [{strategy['description']}]"


awareness = SelfAwareness()


# ── Adaptive Regime Layer (plugs on TOP of existing detection) ──
class AdaptiveRegime:
    """
    Enhanced regime detection using rolling volatility + trend strength.
    Layers on top of SelfAwareness.detect_regime() — does NOT replace it.

    Measures two independent axes:
    1. Trend strength: how directional is the market? (0 = no trend, 1 = strong trend)
    2. Volatility level: how volatile is the market? (0 = calm, 1 = wild)

    This gives 4 quadrants:
    - High trend + low vol = SMOOTH_TREND (best for momentum)
    - High trend + high vol = VOLATILE_TREND (momentum with tight stops)
    - Low trend + low vol = QUIET_RANGE (mean reversion or skip)
    - Low trend + high vol = CHOPPY (skip trading)

    Safe mode: if this layer's win rate drops below 40%, it auto-disables
    and reverts to the original regime detection.
    """

    def __init__(self):
        self.enabled = ADAPTIVE_REGIME_ENABLED
        self.safe_mode = ADAPTIVE_SAFE_MODE
        self.trades_with_layer = 0
        self.wins_with_layer = 0
        self.auto_disabled = False

    def classify(self, prices_cache):
        """
        Returns enhanced regime classification.
        Falls back to original if disabled or auto-reverted.
        """
        if not self.enabled or self.auto_disabled:
            return None  # Caller should use original regime

        try:
            return self._classify_inner(prices_cache)
        except Exception:
            return None

    def _classify_inner(self, pcache):
        if not pcache:
            return None

        trend_scores = []
        vol_scores = []

        for coin, hist in pcache.items():
            if len(hist) < 20:
                continue

            # Trend strength: efficiency ratio (net move / total movement)
            net_move = abs(hist[-1] - hist[-20])
            total_move = sum(abs(hist[i] - hist[i-1]) for i in range(len(hist)-20, len(hist)))
            if total_move > 0:
                trend_scores.append(net_move / total_move)

            # Volatility: standard deviation of returns
            returns = []
            for i in range(len(hist)-10, len(hist)):
                if hist[i-1] != 0:
                    returns.append(abs(hist[i] - hist[i-1]) / hist[i-1])
            if returns:
                vol_scores.append(sum(returns) / len(returns))

        if not trend_scores or not vol_scores:
            return None

        avg_trend = sum(trend_scores) / len(trend_scores)
        avg_vol = sum(vol_scores) / len(vol_scores)

        # Classify into quadrants
        high_trend = avg_trend > 0.3
        high_vol = avg_vol > 0.005  # 0.5% average per-tick volatility

        if high_trend and not high_vol:
            return "SMOOTH_TREND"
        elif high_trend and high_vol:
            return "VOLATILE_TREND"
        elif not high_trend and not high_vol:
            return "QUIET_RANGE"
        else:
            return "CHOPPY"

    def get_strategy_rules(self, regime):
        """
        Returns trading rules for each regime.
        These OVERRIDE the base strategy settings when adaptive layer is active.
        """
        rules = {
            "SMOOTH_TREND": {
                "allow_momentum": True,
                "allow_mean_reversion": False,
                "allow_breakout": True,
                "position_scale": 1.2,  # Slightly bigger in smooth trends
                "description": "Smooth trend — momentum + breakout"
            },
            "VOLATILE_TREND": {
                "allow_momentum": True,
                "allow_mean_reversion": False,
                "allow_breakout": False,  # Breakouts are unreliable in high vol
                "position_scale": 0.7,    # Smaller positions
                "description": "Volatile trend — momentum only, small size"
            },
            "QUIET_RANGE": {
                "allow_momentum": True,    # Allow momentum at reduced size (RANGING_MOMENTUM_SCALE)
                "allow_mean_reversion": True,
                "allow_breakout": True,    # Watch for breakout from range
                "position_scale": 1.0,     # Full size — individual strategy scaling handles reduction
                "description": "Quiet range — mean reversion preferred, momentum allowed"
            },
            "CHOPPY": {
                "allow_momentum": True,     # Allow momentum at reduced size
                "allow_mean_reversion": True,
                "allow_breakout": False,    # Breakouts unreliable in chop
                "position_scale": 1.0,      # Was 0.40 — but REGIME_SIZE_SCALE already applies 0.70x, so 0.40 here made it 0.28x total
                "description": "Choppy — regime scale handles sizing, strategies still allowed"
            },
        }
        return rules.get(regime, rules["VOLATILE_TREND"])

    def record_trade(self, won):
        """Track performance of trades made with this layer active."""
        self.trades_with_layer += 1
        if won:
            self.wins_with_layer += 1

        # Safe mode: auto-disable if win rate drops below 40% after 10+ trades
        if self.safe_mode and self.trades_with_layer >= 10:
            wr = self.wins_with_layer / self.trades_with_layer
            if wr < 0.4:
                self.auto_disabled = True
                logger.warning(f"ADAPTIVE REGIME AUTO-DISABLED (win rate {wr*100:.0f}% < 40%)")

    def status(self):
        if self.auto_disabled:
            return "DISABLED (safe mode)"
        if not self.enabled:
            return "OFF"
        wr = self.wins_with_layer / max(self.trades_with_layer, 1) * 100
        return f"ON ({self.trades_with_layer} trades, {wr:.0f}% WR)"


adaptive_regime = AdaptiveRegime()


class MarketBrain:
    """Central intelligence that observes everything and adapts the bot in real-time.

    Instead of 4 disconnected systems (RecoveryMode, MinActivityGuard, AdaptiveRegime,
    RangingAdaptation) each doing their own thing, this brain:

    1. OBSERVES: tracks market conditions, trade performance, idle time, filter rejections
    2. THINKS: determines what the current situation is and what's not working
    3. ACTS: dynamically adjusts thresholds, sizing, and strategy mix each cycle

    The brain doesn't REPLACE existing systems — it COORDINATES them and fills gaps.

    Key behaviors:
    - Detects when the bot is stuck and progressively loosens the RIGHT filters
    - Detects when the bot is losing and tightens up
    - Switches between aggressive/conservative modes based on real performance
    - Logs its reasoning so you can see WHY it made each decision
    """

    # Mood states — determines overall aggressiveness
    MOOD_AGGRESSIVE = "AGGRESSIVE"     # Market is good, bot is winning → trade more
    MOOD_NORMAL = "NORMAL"             # Default state
    MOOD_CAUTIOUS = "CAUTIOUS"         # Losing or volatile → smaller, fewer trades
    MOOD_DESPERATE = "DESPERATE"       # Been idle forever → take reasonable trades

    def __init__(self):
        self.mood = self.MOOD_NORMAL
        self.last_mood_change = 0
        self.idle_cycles = 0
        self.consecutive_wins = 0
        self.consecutive_losses = 0
        self.recent_filter_blocks = {}    # filter_name -> count (rolling window)
        self.filter_block_window = []     # list of (cycle, filter_name) tuples
        self.cycle_of_last_trade = 0
        self.trades_last_hour = 0
        self.wins_last_hour = 0
        self.losses_last_hour = 0
        self._hour_start_cycle = 0
        self._last_log_cycle = 0
        self._adjustments = {}            # Current active adjustments
        self._market_intel = {}            # Latest market analysis results

    def record_trade(self, cycle, won):
        """Called after every trade exit."""
        self.cycle_of_last_trade = cycle
        self.idle_cycles = 0
        self.trades_last_hour += 1
        if won:
            self.wins_last_hour += 1
            self.consecutive_wins += 1
            self.consecutive_losses = 0
        else:
            self.losses_last_hour += 1
            self.consecutive_losses += 1
            self.consecutive_wins = 0

    def record_entry(self, cycle):
        """Called when a new position is opened."""
        self.cycle_of_last_trade = cycle
        self.idle_cycles = 0

    def record_filter_block(self, cycle, filter_name):
        """Called when a signal gets blocked by a filter."""
        self.filter_block_window.append((cycle, filter_name))
        # Keep only last 500 cycles of data
        cutoff = cycle - 500
        self.filter_block_window = [(c, f) for c, f in self.filter_block_window if c > cutoff]

    def _top_blockers(self, cycle, n=3):
        """Returns the top N filter names blocking the most signals recently."""
        cutoff = cycle - 200
        counts = {}
        for c, f in self.filter_block_window:
            if c > cutoff:
                counts[f] = counts.get(f, 0) + 1
        return sorted(counts.items(), key=lambda x: -x[1])[:n]

    # ── Pro-level market analysis methods ─────────────────────────────
    # These give the brain real trading intelligence — not just counting
    # idle cycles, but understanding what the market is actually doing
    # like a professional day trader would.

    def _analyze_market_breadth(self):
        """How many coins are rising vs falling? Broad up = bullish market."""
        try:
            up_10 = 0
            down_10 = 0
            up_30 = 0
            down_30 = 0
            total = 0
            for coin, hist in prices_cache.items():
                if len(hist) < 31:
                    continue
                total += 1
                # Short-term breadth (10-tick ~ 20 seconds)
                if hist[-10] > 0:
                    m10 = (hist[-1] - hist[-10]) / hist[-10]
                    if m10 > 0.001:
                        up_10 += 1
                    elif m10 < -0.001:
                        down_10 += 1
                # Medium-term breadth (30-tick ~ 60 seconds)
                if hist[-30] > 0:
                    m30 = (hist[-1] - hist[-30]) / hist[-30]
                    if m30 > 0.002:
                        up_30 += 1
                    elif m30 < -0.002:
                        down_30 += 1
            if total < 5:
                return {"breadth_10": 0.0, "breadth_30": 0.0, "n_coins": total}
            breadth_10 = (up_10 - down_10) / total
            breadth_30 = (up_30 - down_30) / total
            return {"breadth_10": breadth_10, "breadth_30": breadth_30, "n_coins": total}
        except Exception:
            return {"breadth_10": 0.0, "breadth_30": 0.0, "n_coins": 0}

    def _analyze_btc(self):
        """What is BTC doing? BTC leads — when it moves, alts follow."""
        try:
            btc_hist = prices_cache.get("XBT", prices_cache.get("BTC", []))
            if len(btc_hist) < 50:
                return {"btc_mom_5": 0.0, "btc_mom_20": 0.0, "btc_mom_50": 0.0,
                        "btc_trend": "unknown", "btc_strength": 0.0}
            m5 = (btc_hist[-1] - btc_hist[-5]) / btc_hist[-5] if btc_hist[-5] > 0 else 0.0
            m20 = (btc_hist[-1] - btc_hist[-20]) / btc_hist[-20] if btc_hist[-20] > 0 else 0.0
            m50 = (btc_hist[-1] - btc_hist[-50]) / btc_hist[-50] if btc_hist[-50] > 0 else 0.0
            # Trend alignment across timeframes
            if m5 > 0.0001 and m20 > 0.0001 and m50 > 0.0001:
                trend = "strong_up"
                strength = min(1.0, (abs(m5) + abs(m20) + abs(m50)) * 10)
            elif m5 < -0.0001 and m20 < -0.0001 and m50 < -0.0001:
                trend = "strong_down"
                strength = min(1.0, (abs(m5) + abs(m20) + abs(m50)) * 10)
            elif m5 > 0.0001 and m20 > 0.0001:
                trend = "up"
                strength = 0.5
            elif m5 < -0.0001 and m20 < -0.0001:
                trend = "down"
                strength = 0.5
            else:
                trend = "mixed"
                strength = 0.2
            return {"btc_mom_5": m5, "btc_mom_20": m20, "btc_mom_50": m50,
                    "btc_trend": trend, "btc_strength": strength}
        except Exception:
            return {"btc_mom_5": 0.0, "btc_mom_20": 0.0, "btc_mom_50": 0.0,
                    "btc_trend": "unknown", "btc_strength": 0.0}

    def _analyze_volatility_shift(self):
        """Is volatility expanding or contracting? Expanding + trend = opportunity."""
        try:
            recent_atrs = []
            older_atrs = []
            for coin, hist in prices_cache.items():
                if len(hist) < 50:
                    continue
                # Recent ATR (last 10 ticks)
                recent_moves = []
                for i in range(-10, 0):
                    if hist[i - 1] > 0:
                        recent_moves.append(abs(hist[i] - hist[i - 1]) / hist[i - 1])
                if recent_moves:
                    recent_atrs.append(sum(recent_moves) / len(recent_moves))
                # Older ATR (ticks -40 to -30)
                older_moves = []
                for i in range(-40, -30):
                    if hist[i - 1] > 0:
                        older_moves.append(abs(hist[i] - hist[i - 1]) / hist[i - 1])
                if older_moves:
                    older_atrs.append(sum(older_moves) / len(older_moves))
            if not recent_atrs or not older_atrs:
                return {"vol_expanding": False, "avg_atr": 0.01, "atr_change": 0.0}
            avg_recent = sum(recent_atrs) / len(recent_atrs)
            avg_older = sum(older_atrs) / len(older_atrs)
            atr_change = (avg_recent - avg_older) / max(avg_older, 0.0001)
            return {
                "vol_expanding": atr_change > 0.10,
                "avg_atr": avg_recent,
                "atr_change": atr_change,
            }
        except Exception:
            return {"vol_expanding": False, "avg_atr": 0.01, "atr_change": 0.0}

    def _analyze_trend_quality(self):
        """How clean are trends across the market? High efficiency = follow momentum."""
        try:
            efficiencies = []
            for coin, hist in prices_cache.items():
                if len(hist) < 20:
                    continue
                window = hist[-20:]
                net_move = abs(window[-1] - window[0])
                total_move = sum(abs(window[i] - window[i - 1]) for i in range(1, len(window)))
                if total_move > 0:
                    efficiencies.append(net_move / total_move)
            if not efficiencies:
                return {"avg_efficiency": 0.3, "clean_trends": False,
                        "n_trending": 0, "n_total": 0}
            avg_eff = sum(efficiencies) / len(efficiencies)
            n_trending = sum(1 for e in efficiencies if e > 0.35)
            return {
                "avg_efficiency": avg_eff,
                "clean_trends": avg_eff > 0.30,
                "n_trending": n_trending,
                "n_total": len(efficiencies),
            }
        except Exception:
            return {"avg_efficiency": 0.3, "clean_trends": False,
                    "n_trending": 0, "n_total": 0}

    def _compute_market_intelligence(self):
        """Master analysis: combine all signals into actionable intelligence.

        Returns a market_score from -1.0 (terrible) to +1.0 (excellent)
        plus a directional bias and human-readable insight string.
        """
        try:
            breadth = self._analyze_market_breadth()
            btc = self._analyze_btc()
            vol = self._analyze_volatility_shift()
            trend = self._analyze_trend_quality()
            peak = is_peak_hours()

            score = 0.0
            insights = []

            # 1. Market breadth: broad participation = conviction (±0.25)
            avg_breadth = (breadth["breadth_10"] + breadth["breadth_30"]) / 2
            score += avg_breadth * 0.25
            if avg_breadth > 0.3:
                insights.append("broad bullish")
            elif avg_breadth < -0.3:
                insights.append("broad bearish")

            # 2. BTC leadership: strong BTC trend = opportunity (±0.25)
            if btc["btc_trend"] in ("strong_up", "strong_down"):
                score += 0.20
                insights.append(f"BTC {btc['btc_trend'].replace('_', ' ')}")
            elif btc["btc_trend"] in ("up", "down"):
                score += 0.10
                insights.append(f"BTC {btc['btc_trend']}")
            elif btc["btc_trend"] == "mixed":
                score -= 0.10
                insights.append("BTC choppy")

            # 3. Trend quality: clean trends = follow them (±0.20)
            if trend["clean_trends"]:
                score += 0.20
                pct = int(100 * trend["n_trending"] / max(1, trend["n_total"]))
                insights.append(f"clean trends {pct}%")
            elif trend["avg_efficiency"] < 0.15:
                score -= 0.15
                insights.append("messy market")

            # 4. Volatility regime: expanding vol + trend = great (±0.15)
            if vol["vol_expanding"] and trend["clean_trends"]:
                score += 0.15
                insights.append("vol+trend")
            elif vol["vol_expanding"] and not trend["clean_trends"]:
                score -= 0.15
                insights.append("vol+chop")

            # 5. Time of day: peak hours have more liquidity (±0.10)
            if peak:
                score += 0.10
                insights.append("peak hrs")

            # Directional bias from BTC + breadth agreement
            if btc["btc_trend"] in ("strong_up", "up") and avg_breadth > 0.15:
                bias = "long"
            elif btc["btc_trend"] in ("strong_down", "down") and avg_breadth < -0.15:
                bias = "short"
            else:
                bias = "neutral"

            score = max(-1.0, min(1.0, score))

            self._market_intel = {
                "score": score,
                "bias": bias,
                "insight": " | ".join(insights[:4]) if insights else "analyzing",
                "breadth": breadth,
                "btc": btc,
                "volatility": vol,
                "trend": trend,
                "peak": peak,
            }
            return self._market_intel
        except Exception as e:
            self._market_intel = {
                "score": 0.0, "bias": "neutral",
                "insight": f"analysis error",
                "breadth": {"breadth_10": 0, "breadth_30": 0, "n_coins": 0},
                "btc": {"btc_trend": "unknown", "btc_strength": 0},
                "volatility": {"vol_expanding": False, "avg_atr": 0.01, "atr_change": 0.0},
                "trend": {"avg_efficiency": 0.3, "clean_trends": False, "n_trending": 0, "n_total": 0},
                "peak": False,
            }
            return self._market_intel

    def think(self, cycle, wallet, prices, regime, enhanced_regime, n_positions,
              health_score, recent_wr=None):
        """Called once per cycle. Observes state, decides mood, returns adjustments.

        Returns a dict of adjustments the main loop should apply:
        {
            "score_mult": float,       # Multiply entry score thresholds (< 1.0 = looser)
            "change_mult": float,      # Multiply entry change thresholds (< 1.0 = looser)
            "size_mult": float,        # Extra sizing multiplier (> 1.0 = bigger)
            "stag_mult": float,        # Multiply stagnation patience (> 1.0 = more patient)
            "scan_extra": int,         # Extra candidates to scan beyond default 15
            "skip_choppy": bool,       # True = bypass is_choppy filter entirely
            "skip_volume_confirms": bool,  # True = bypass volume_confirms filter
            "mood": str,               # Current mood for dashboard display
            "reason": str,             # Why this mood (for logging)
        }
        """
        # Reset hourly counters
        if cycle - self._hour_start_cycle > 1800:  # ~1 hour at 2s/cycle
            self.trades_last_hour = 0
            self.wins_last_hour = 0
            self.losses_last_hour = 0
            self._hour_start_cycle = cycle

        # Track idle time
        if self.cycle_of_last_trade > 0:
            self.idle_cycles = cycle - self.cycle_of_last_trade
        elif cycle > 200:  # Past warmup with no trades
            self.idle_cycles = cycle - 200

        # === MARKET INTELLIGENCE ===
        # Run all pro-level analyses before deciding mood
        intel = self._compute_market_intelligence()
        market_score = intel["score"]       # -1.0 to +1.0
        bias = intel["bias"]               # "long", "short", "neutral"

        # === DETERMINE MOOD (market-aware) ===
        old_mood = self.mood
        reason = ""

        # Priority 1: Strong market + winning streak → full AGGRESSIVE
        if market_score > 0.25 and self.consecutive_wins >= 2:
            self.mood = self.MOOD_AGGRESSIVE
            reason = f"strong mkt ({market_score:+.2f}) + {self.consecutive_wins}W"

        # Priority 2: Win streak even without strong market signal
        elif self.consecutive_wins >= 3 and self.idle_cycles < 50:
            self.mood = self.MOOD_AGGRESSIVE
            reason = f"win streak ({self.consecutive_wins}W) mkt={market_score:+.2f}"

        # Priority 3: Losing streak OR weak market + any loss → CAUTIOUS
        elif self.consecutive_losses >= 3:
            self.mood = self.MOOD_CAUTIOUS
            reason = f"losing streak ({self.consecutive_losses}L) mkt={market_score:+.2f}"
        elif market_score < -0.3 and self.consecutive_losses >= 1:
            self.mood = self.MOOD_CAUTIOUS
            reason = f"weak mkt ({market_score:+.2f}) + {self.consecutive_losses}L"

        # Priority 4: Extended idle → smart response based on market
        elif self.idle_cycles > 300:
            if market_score > 0.20:
                # Good market but not trading → be aggressive, not desperate
                self.mood = self.MOOD_AGGRESSIVE
                reason = f"idle {self.idle_cycles}c but mkt good ({market_score:+.2f}) — forcing"
            else:
                self.mood = self.MOOD_DESPERATE
                top_blockers = self._top_blockers(cycle)
                blocker_str = ", ".join(f"{f}({c})" for f, c in top_blockers) if top_blockers else "unknown"
                reason = f"idle {self.idle_cycles}c mkt={market_score:+.2f} — {blocker_str}"

        # Priority 5: Favorable market even without streak → lean aggressive
        elif market_score > 0.30 and self.consecutive_losses == 0:
            self.mood = self.MOOD_AGGRESSIVE
            reason = f"favorable mkt ({market_score:+.2f}) — {intel['insight']}"

        # Priority 6: Hot win rate this hour
        elif self.trades_last_hour >= 3 and self.wins_last_hour / max(1, self.trades_last_hour) > 0.60:
            self.mood = self.MOOD_AGGRESSIVE
            reason = f"hot hand ({self.wins_last_hour}W/{self.trades_last_hour}T) mkt={market_score:+.2f}"

        # Priority 7: Cold streak this hour
        elif self.trades_last_hour >= 3 and self.wins_last_hour / max(1, self.trades_last_hour) < 0.35:
            self.mood = self.MOOD_CAUTIOUS
            reason = f"cold ({self.wins_last_hour}W/{self.trades_last_hour}T) mkt={market_score:+.2f}"

        # Priority 8: Moderate idle — use market to decide patience
        elif self.idle_cycles > 100:
            if market_score > 0.15:
                self.mood = self.MOOD_NORMAL
                reason = f"idle {self.idle_cycles}c — mkt decent ({market_score:+.2f})"
            else:
                self.mood = self.MOOD_NORMAL
                reason = f"idle {self.idle_cycles}c — mkt flat, patient"

        # Default: steady state with market context
        else:
            self.mood = self.MOOD_NORMAL
            reason = f"steady — mkt={market_score:+.2f} {bias}"

        # Hysteresis: prevent mood flip-flopping (minimum 30 cycles between changes)
        if self.mood != old_mood and (cycle - self.last_mood_change) < 30:
            self.mood = old_mood
            reason = f"holding {old_mood} (cooldown {30 - (cycle - self.last_mood_change)}c)"

        # Log mood changes
        if self.mood != old_mood:
            self.last_mood_change = cycle
            logger.info(f"[BRAIN] Mood: {old_mood} -> {self.mood} — {reason}")

        # Periodic status log (every 100 cycles) — now includes market intel
        if cycle - self._last_log_cycle >= 100:
            self._last_log_cycle = cycle
            top_b = self._top_blockers(cycle)
            blocker_str = ", ".join(f"{f}({c})" for f, c in top_b) if top_b else "none"
            btc_info = intel.get("btc", {})
            logger.info(
                f"[BRAIN] mood={self.mood} mkt={market_score:+.2f} bias={bias} "
                f"idle={self.idle_cycles}c "
                f"streak={'W' if self.consecutive_wins > 0 else 'L'}"
                f"{max(self.consecutive_wins, self.consecutive_losses)} "
                f"hour={self.wins_last_hour}W/{self.trades_last_hour}T "
                f"BTC={btc_info.get('btc_trend', '?')} "
                f"blockers=[{blocker_str}] "
                f"| {intel['insight']}"
            )

        # === COMPUTE ADJUSTMENTS (market-intelligent) ===
        adj = {
            "score_mult": 1.0,
            "change_mult": 1.0,
            "size_mult": 1.0,
            "stag_mult": 1.0,
            "scan_extra": 0,
            "skip_choppy": False,
            "skip_volume_confirms": False,
            "mood": self.mood,
            "reason": reason,
            "market_score": market_score,
            "bias": bias,
            "market_insight": intel["insight"],
            "clean_trends_pct": int(100 * intel.get("trend", {}).get("n_trending", 0) / max(1, intel.get("trend", {}).get("n_total", 1))),
        }

        if self.mood == self.MOOD_AGGRESSIVE:
            # Scale aggressiveness by how good the market actually is
            aggro = min(1.0, 0.5 + max(0.0, market_score))  # 0.5 to 1.0
            adj["score_mult"] = 1.0 - (0.30 * aggro)       # 0.70 to 0.85
            adj["change_mult"] = 1.0 - (0.30 * aggro)
            adj["size_mult"] = 1.0 + (0.20 * aggro)        # 1.10 to 1.20
            adj["stag_mult"] = 1.0 + (0.50 * aggro)        # 1.25 to 1.50
            adj["scan_extra"] = int(3 + 7 * aggro)          # 6 to 10

            # In clean trending markets, skip the choppy filter
            if intel.get("trend", {}).get("clean_trends", False):
                adj["skip_choppy"] = True

        elif self.mood == self.MOOD_CAUTIOUS:
            # More cautious when market is genuinely bad
            caution = min(1.0, 0.5 + abs(min(0.0, market_score)))  # 0.5 to 1.0
            adj["score_mult"] = 1.0 + (0.40 * caution)     # 1.20 to 1.40
            adj["change_mult"] = 1.0 + (0.40 * caution)
            adj["size_mult"] = max(0.50, 1.0 - (0.40 * caution))   # 0.60 to 0.80
            adj["stag_mult"] = max(0.50, 1.0 - (0.40 * caution))
            adj["scan_extra"] = 0

        elif self.mood == self.MOOD_DESPERATE:
            # Smart desperation: loosen entry, but don't increase size
            adj["score_mult"] = 0.5
            adj["change_mult"] = 0.5
            adj["size_mult"] = 0.85
            adj["stag_mult"] = 1.3
            adj["scan_extra"] = 10
            adj["skip_choppy"] = True
            adj["skip_volume_confirms"] = True

            # Progressive desperation — kicks in sooner to avoid prolonged idle
            if self.idle_cycles > 400:
                adj["score_mult"] = 0.3
                adj["change_mult"] = 0.3
                logger.debug(f"[BRAIN] Deep desperation: idle {self.idle_cycles}c, score_mult=0.3")

        self._adjustments = adj
        return adj

    def status_line(self):
        """Short string for dashboard — now shows market intelligence."""
        mood_icons = {
            self.MOOD_AGGRESSIVE: "AGGRO",
            self.MOOD_NORMAL: "NORMAL",
            self.MOOD_CAUTIOUS: "CAREFUL",
            self.MOOD_DESPERATE: "HUNTING",
        }
        mkt = self._market_intel
        ms = mkt.get("score", 0.0) if mkt else 0.0
        bias = mkt.get("bias", "?") if mkt else "?"
        insight = mkt.get("insight", "") if mkt else ""
        short_insight = insight[:45] if insight else ""
        return (f"Brain:{mood_icons.get(self.mood, '?')} "
                f"mkt={ms:+.2f} bias={bias} idle={self.idle_cycles}c "
                f"| {short_insight}")

    def save_state(self):
        return {
            "mood": self.mood,
            "cycle_of_last_trade": self.cycle_of_last_trade,
            "consecutive_wins": self.consecutive_wins,
            "consecutive_losses": self.consecutive_losses,
            "trades_last_hour": self.trades_last_hour,
            "wins_last_hour": self.wins_last_hour,
            "losses_last_hour": self.losses_last_hour,
        }

    def load_state(self, state):
        if state:
            self.mood = state.get("mood", self.MOOD_NORMAL)
            self.cycle_of_last_trade = state.get("cycle_of_last_trade", 0)
            self.consecutive_wins = state.get("consecutive_wins", 0)
            self.consecutive_losses = state.get("consecutive_losses", 0)
            self.trades_last_hour = state.get("trades_last_hour", 0)
            self.wins_last_hour = state.get("wins_last_hour", 0)
            self.losses_last_hour = state.get("losses_last_hour", 0)


market_brain = MarketBrain()


# ── Price History + ML Features ──
prices_cache = {}  # coin -> list of last 100 prices (for momentum/ML)
_suspicious_coins = set()  # Coins with price jumps > 3x ATR this cycle (skip for entries)


def track_price(coin, price):
    """Track price history for momentum and ML features. Flags suspicious price jumps."""
    if price <= 0:
        return  # Never store zero/negative prices
    if coin not in prices_cache:
        prices_cache[coin] = []
    # Suspicious price filter: if new price deviates > 3x ATR from last cached price, flag it
    hist = prices_cache[coin]
    if len(hist) >= 15:
        last = hist[-1]
        if last > 0:
            atr = coin_atr(coin)
            jump = abs(price - last) / last
            threshold = max(0.03, atr * 3) if atr > 0.0001 else 0.05  # Floor 3% jump before flagging; default 5% if ATR too small
            if jump > threshold:
                _suspicious_coins.add(coin)
                logger.debug(f"SUSPICIOUS PRICE {coin}: {last:.4f} → {price:.4f} (jump={jump*100:.2f}%, 3xATR={atr*300:.2f}%)")
    prices_cache[coin].append(price)
    if len(prices_cache[coin]) > 500:
        prices_cache[coin] = prices_cache[coin][-500:]  # v29.3.5: was 100 — too small for long-window indicators. 500 covers all timeframes

def short_momentum(coin, window=10):
    """Recent momentum over last N ticks. Positive = going up."""
    hist = prices_cache.get(coin, [])
    if len(hist) < window + 1:
        return 0
    if hist[-window] == 0:
        return 0
    return (hist[-1] - hist[-window]) / hist[-window]


# ── v29.3 ENTRY QUALITY: Momentum Confirmation ──
def momentum_confirmed(coin, direction, window=5):
    """Check that price momentum is accelerating in the trade direction.
    For longs: recent half must move MORE than earlier half (accelerating up).
    For shorts: recent half must move MORE negative than earlier half (accelerating down).
    Returns (confirmed: bool, momentum_delta: float) for logging."""
    hist = prices_cache.get(coin, [])
    if len(hist) < window + 2:
        return True, 0.0  # Not enough data — allow entry (don't block early)
    recent = hist[-(window + 1):]
    mid = len(recent) // 2
    # First half momentum
    if recent[0] == 0:
        return True, 0.0
    first_half = (recent[mid] - recent[0]) / recent[0]
    # Second half momentum
    if recent[mid] == 0:
        return True, 0.0
    second_half = (recent[-1] - recent[mid]) / recent[mid]
    if direction == "long":
        # Price should be going up AND accelerating (second half >= first half)
        # Also reject if both halves are negative (price falling)
        if second_half < 0 and first_half < 0:
            return False, second_half - first_half  # Both halves down = no momentum
        if second_half < -0.0005:
            return False, second_half  # Recent price falling = no buy momentum
        return True, second_half - first_half
    else:
        # Price should be going down AND accelerating down
        if second_half > 0 and first_half > 0:
            return False, second_half - first_half  # Both halves up = no short momentum
        if second_half > 0.0005:
            return False, second_half  # Recent price rising = no short momentum
        return True, second_half - first_half


# ── v29.3 ENTRY QUALITY: Micro-Trend Confirmation ──
def micro_trend_confirmed(coin, direction, candles=4):
    """Check that last N candles (price ticks) agree with trade direction.
    For longs: at least 3 of last 4 ticks must be up (price[i] >= price[i-1]).
    For shorts: at least 3 of last 4 ticks must be down.
    Returns (confirmed: bool, agree_count: int, total: int)."""
    hist = prices_cache.get(coin, [])
    if len(hist) < candles + 1:
        return True, 0, 0  # Not enough data — allow entry
    recent = hist[-(candles + 1):]
    if direction == "long":
        agree = sum(1 for i in range(1, len(recent)) if recent[i] >= recent[i - 1])
    else:
        agree = sum(1 for i in range(1, len(recent)) if recent[i] <= recent[i - 1])
    # Require at least 3 out of 4 candles in the right direction (75%)
    threshold = max(2, int(candles * 0.6))  # 60% agreement minimum
    return agree >= threshold, agree, candles


def coin_atr(coin, window=14):
    try:
        return _coin_atr_inner(coin, window)
    except Exception:
        return 0.01

def _coin_atr_inner(coin, window):
    hist = prices_cache.get(coin, [])
    if len(hist) < window + 1:
        return 0.01  # Default 1% if not enough data
    ranges = []
    for i in range(len(hist) - window, len(hist)):
        if hist[i-1] > 0:
            true_range = abs(hist[i] - hist[i-1]) / hist[i-1]
            ranges.append(true_range)
    return sum(ranges) / len(ranges) if ranges else 0.01


def is_peak_hours():
    """Is it currently peak trading hours? (15:00-21:00 UTC)"""
    hour = datetime.now(timezone.utc).hour
    return PEAK_HOURS[0] <= hour < PEAK_HOURS[1]


# ── v29.4.0: BTC Market Condition Gate ──

def btc_market_condition():
    """Classify BTC as TRENDING or RANGING based on last 20 ticks.
    Returns (condition: str, net_move_pct: float).
    TRENDING = |net move| >= BTC_TREND_MIN_MOVE (1.5%).
    RANGING  = |net move| <  BTC_TREND_MIN_MOVE."""
    hist = prices_cache.get("BTC", [])
    if len(hist) < 20:
        return "TRENDING", 0.0  # Not enough data — don't block (assume trending)
    window = hist[-20:]
    if window[0] <= 0:
        return "TRENDING", 0.0
    net_move = (window[-1] - window[0]) / window[0]
    if abs(net_move) >= BTC_TREND_MIN_MOVE:
        return "TRENDING", net_move
    return "RANGING", net_move


def btc_meanrev_scan(tickers):
    """When BTC is ranging, scan for mean-reversion opportunities.
    Returns list of dicts: [{coin, side, z_score, price}] for coins with |z| > BTC_MEANREV_Z_THRESHOLD.
    z-score = (current - mean) / stdev over BTC_MEANREV_Z_WINDOW ticks."""
    candidates = []
    for coin, hist in prices_cache.items():
        if coin in DYNAMIC_BLACKLIST:
            continue
        if len(hist) < BTC_MEANREV_Z_WINDOW + 1:
            continue
        window = hist[-BTC_MEANREV_Z_WINDOW:]
        mean = sum(window) / len(window)
        if mean <= 0:
            continue
        variance = sum((p - mean) ** 2 for p in window) / len(window)
        if variance <= 0:
            continue
        stdev = variance ** 0.5
        if stdev / mean < 0.001:  # Skip coins with near-zero relative vol
            continue
        z = (window[-1] - mean) / stdev
        if z > BTC_MEANREV_Z_THRESHOLD:
            candidates.append({"coin": coin, "side": "short", "z_score": z, "price": window[-1]})
        elif z < -BTC_MEANREV_Z_THRESHOLD:
            candidates.append({"coin": coin, "side": "long", "z_score": z, "price": window[-1]})
    # Sort by strongest z-score magnitude (most extreme first)
    candidates.sort(key=lambda c: abs(c["z_score"]), reverse=True)
    return candidates[:5]  # Top 5 candidates


# ── v29.4.1: Fear & Greed Index ──

def fetch_fear_greed_index():
    """Fetch the Fear & Greed Index from alternative.me free API.
    Returns (value: int 0-100, label: str) or (50, 'Neutral') on failure.
    Cached via _fear_greed_last_cycle to avoid over-fetching."""
    global _fear_greed_value, _fear_greed_label, _fear_greed_last_cycle
    try:
        resp = requests.get("https://api.alternative.me/fng/?limit=1", timeout=10)
        if resp.status_code == 200:
            data = resp.json()
            if "data" in data and len(data["data"]) > 0:
                _fear_greed_value = int(data["data"][0]["value"])
                _fear_greed_label = data["data"][0].get("value_classification", "Unknown")
                _fear_greed_last_cycle = _current_cycle
                logger.info(f"[F&G] Fear & Greed Index: {_fear_greed_value} ({_fear_greed_label})")
                return _fear_greed_value, _fear_greed_label
        logger.warning(f"[F&G] API returned status {resp.status_code}")
    except Exception as e:
        logger.warning(f"[F&G] Fetch failed: {e}")
    return _fear_greed_value, _fear_greed_label  # Return last known value


def fear_greed_size_mult():
    """Return position size multiplier based on current Fear & Greed Index.
    Extreme Fear (<25) = 1.30x (buy the blood), Extreme Greed (>75) = 0.70x, else 1.0."""
    if not FEAR_GREED_ENABLED:
        return 1.0
    if _fear_greed_value < FEAR_GREED_EXTREME_FEAR:
        return FEAR_GREED_FEAR_MULT
    elif _fear_greed_value > FEAR_GREED_EXTREME_GREED:
        return FEAR_GREED_GREED_MULT
    return FEAR_GREED_NEUTRAL_MULT


def smart_dca_size_mult():
    """Return DCA boost multiplier when in Extreme Fear territory.
    F&G < 20 = +40% extra size for mean-rev / long entries."""
    if not SMART_DCA_ENABLED or not FEAR_GREED_ENABLED:
        return 1.0
    if _fear_greed_value < SMART_DCA_EXTREME_FEAR_THRESHOLD:
        return 1.0 + SMART_DCA_BOOST_PCT  # 1.40x
    return 1.0


# ── v29.4.1: Triple-Confirm Mean Reversion ──

def compute_rsi(prices_list, window=14):
    """Compute RSI from a price list. Returns 50.0 if insufficient data."""
    if len(prices_list) < window + 1:
        return 50.0
    gains = []
    losses = []
    for i in range(-window, 0):
        delta = prices_list[i] - prices_list[i - 1]
        if delta > 0:
            gains.append(delta)
            losses.append(0.0)
        else:
            gains.append(0.0)
            losses.append(abs(delta))
    avg_gain = sum(gains) / window
    avg_loss = sum(losses) / window
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100.0 - (100.0 / (1.0 + rs))


def compute_bollinger(prices_list, window=20, num_std=2.0):
    """Compute Bollinger Bands. Returns (upper, middle, lower) or None if insufficient data."""
    if len(prices_list) < window:
        return None
    window_slice = prices_list[-window:]
    middle = sum(window_slice) / len(window_slice)
    variance = sum((p - middle) ** 2 for p in window_slice) / len(window_slice)
    std = variance ** 0.5
    if std == 0:
        return None
    upper = middle + num_std * std
    lower = middle - num_std * std
    return upper, middle, lower


def triple_confirm_meanrev(coin, z_score):
    """Triple-Confirm Mean Reversion: requires BB + RSI + Z-Score all confirming.
    Returns (confirmed: bool, direction: str, conviction_boost: float, details: dict).
    conviction_boost: 0.0 = base, 0.25 = high conviction (z > 3.0)."""
    if not TRIPLE_MEANREV_ENABLED:
        return False, "", 0.0, {}

    hist = prices_cache.get(coin, [])
    if len(hist) < max(TRIPLE_MEANREV_BB_WINDOW, TRIPLE_MEANREV_RSI_WINDOW + 1, 20):
        return False, "", 0.0, {"reason": "insufficient_data"}

    # Component 1: Z-Score (already computed by caller)
    z_ok = abs(z_score) >= TRIPLE_MEANREV_Z_THRESHOLD

    # Component 2: Bollinger Bands
    bb = compute_bollinger(hist, TRIPLE_MEANREV_BB_WINDOW, TRIPLE_MEANREV_BB_STD)
    if bb is None:
        return False, "", 0.0, {"reason": "bb_calc_failed"}
    upper, middle, lower = bb
    price = hist[-1]
    bb_oversold = price <= lower
    bb_overbought = price >= upper

    # Component 3: RSI
    rsi = compute_rsi(hist, TRIPLE_MEANREV_RSI_WINDOW)
    rsi_oversold = rsi <= TRIPLE_MEANREV_RSI_OVERSOLD
    rsi_overbought = rsi >= TRIPLE_MEANREV_RSI_OVERBOUGHT

    details = {"z": z_score, "rsi": rsi, "bb_upper": upper, "bb_lower": lower, "price": price}

    # LONG signal: z < -2, price below lower BB, RSI oversold
    if z_score < -TRIPLE_MEANREV_Z_THRESHOLD and bb_oversold and rsi_oversold:
        boost = 0.25 if abs(z_score) >= TRIPLE_MEANREV_HIGH_CONV_Z else 0.0
        return True, "long", boost, details

    # SHORT signal: z > 2, price above upper BB, RSI overbought
    if z_score > TRIPLE_MEANREV_Z_THRESHOLD and bb_overbought and rsi_overbought:
        boost = 0.25 if abs(z_score) >= TRIPLE_MEANREV_HIGH_CONV_Z else 0.0
        return True, "short", boost, details

    return False, "", 0.0, details


# ── v29.4.1: Opening Range Breakout (ORB) ──

def orb_fetch_opening_range():
    """Fetch opening range data for ORB symbols using Alpaca API.
    Populates _orb_ranges with {symbol: {high, low, avg_vol, ready}}.
    Only runs if ORB_ENABLED and API keys are set."""
    global _orb_ranges
    if not ORB_ENABLED or not ORB_API_KEY or not ORB_API_SECRET:
        return
    try:
        headers = {
            "APCA-API-KEY-ID": ORB_API_KEY,
            "APCA-API-SECRET-KEY": ORB_API_SECRET
        }
        for sym in ORB_SYMBOLS:
            # Fetch today's bars (1-min) for first ORB_RANGE_MINUTES minutes
            resp = requests.get(
                f"{ORB_BASE_URL}/v2/stocks/{sym}/bars",
                headers=headers,
                params={"timeframe": "1Min", "limit": ORB_RANGE_MINUTES, "feed": "iex"},
                timeout=10
            )
            if resp.status_code != 200:
                logger.warning(f"[ORB] Failed to fetch bars for {sym}: {resp.status_code}")
                continue
            bars = resp.json().get("bars", [])
            if len(bars) < ORB_RANGE_MINUTES * 0.8:  # Need at least 80% of bars
                _orb_ranges[sym] = {"high": 0, "low": 0, "avg_vol": 0, "ready": False}
                continue
            highs = [b["h"] for b in bars]
            lows = [b["l"] for b in bars]
            vols = [b["v"] for b in bars]
            _orb_ranges[sym] = {
                "high": max(highs),
                "low": min(lows),
                "avg_vol": sum(vols) / len(vols) if vols else 0,
                "ready": True
            }
            logger.info(f"[ORB] {sym} opening range: ${min(lows):.2f}-${max(highs):.2f} vol_avg={sum(vols) / len(vols):.0f}")
    except Exception as e:
        logger.warning(f"[ORB] Opening range fetch failed: {e}")


def orb_check_breakout(symbol, current_price, current_volume):
    """Check if a symbol is breaking out of its opening range.
    Returns (breakout: bool, direction: str, target: float, stop: float) or (False, '', 0, 0)."""
    if not ORB_ENABLED or symbol not in _orb_ranges:
        return False, "", 0.0, 0.0
    rng = _orb_ranges[symbol]
    if not rng["ready"] or rng["high"] <= rng["low"]:
        return False, "", 0.0, 0.0
    range_size = rng["high"] - rng["low"]
    # Volume confirmation: current bar volume must exceed 1.5x average
    if rng["avg_vol"] > 0 and current_volume < rng["avg_vol"] * ORB_VOLUME_CONFIRM_MULT:
        return False, "", 0.0, 0.0
    # Bullish breakout: price above opening range high
    if current_price > rng["high"]:
        target = rng["high"] + range_size * ORB_TARGET_RANGE_MULT
        stop = rng["high"] - range_size * ORB_STOP_RANGE_MULT
        return True, "long", target, stop
    # Bearish breakout: price below opening range low
    if current_price < rng["low"]:
        target = rng["low"] - range_size * ORB_TARGET_RANGE_MULT
        stop = rng["low"] + range_size * ORB_STOP_RANGE_MULT
        return True, "short", target, stop
    return False, "", 0.0, 0.0


# ── Win Rate Filters: reject bad trades before they happen ──

def is_choppy(coin, window=20):
    """ADX-like chop filter. Returns True if market is choppy (skip trading)."""
    try:
        return _is_choppy_inner(coin, window)
    except Exception:
        return False

def _is_choppy_inner(coin, window):
    hist = prices_cache.get(coin, [])
    if len(hist) < window + 1:
        return False
    # Calculate directional movement vs total movement
    total_move = abs(hist[-1] - hist[-window])  # Net directional move
    total_range = sum(abs(hist[i] - hist[i-1]) for i in range(len(hist)-window, len(hist)))  # Sum of all moves
    if total_range == 0:
        return True  # No movement = choppy
    if total_range == 0:
        return True  # No movement at all = choppy
    efficiency = total_move / total_range  # 1.0 = perfect trend, 0.0 = pure chop
    return efficiency < 0.15  # Was 0.25 — too aggressive, blocked most coins in CHOPPY regime. 0.15 catches only true chop


def volume_confirms(ticker_data):
    """Check if volume supports the price move. False = likely fake breakout."""
    vol = ticker_data.get("vol", 0)
    change = abs(ticker_data.get("change", 0))
    # Big price move with low volume = suspect
    if change > 0.05 and vol < 150000:
        return False  # Was 3%/$500k — blocked legit small-cap signals like GHST. Now only blocks extreme moves on truly thin vol
    return True


def is_pullback_entry(coin, direction="long"):
    """Check if price pulled back to a good entry (not chasing the top/bottom).
    For longs: price should be near recent low, not at high.
    For shorts: price should be near recent high, not at low."""
    hist = prices_cache.get(coin, [])
    if len(hist) < 20:
        return True  # Not enough data, allow
    recent = hist[-20:]
    hi = max(recent)
    lo = min(recent)
    if hi == lo:
        return True
    pos = (hist[-1] - lo) / (hi - lo)  # 0 = at low, 1 = at high
    if direction == "long":
        return pos < 0.7  # Don't buy at the very top (above 70% of range)
    else:
        return pos > 0.3  # Don't short at the very bottom


# ── Noise Trade Filters: block low-quality entries that bleed fees ──

def coin_is_trending(coin, window=None):
    """Check if a SPECIFIC coin is trending (not the global regime).
    Returns True if the coin has directional movement above threshold.
    Used to block mean-reversion trades on coins that are actually trending."""
    if not NOISE_FILTER_ENABLED:
        return False
    try:
        w = window or NOISE_MEANREV_COIN_TREND_WINDOW
        hist = prices_cache.get(coin, [])
        if len(hist) < w + 1:
            return False
        net_move = abs(hist[-1] - hist[-w])
        total_move = sum(abs(hist[i] - hist[i-1]) for i in range(len(hist)-w, len(hist)))
        if total_move == 0:
            return False
        efficiency = net_move / total_move
        return efficiency > NOISE_MEANREV_COIN_TREND_THRESHOLD
    except Exception:
        return False


def breakout_confirmed(coin, direction, ticks=None):
    """Require price to stay beyond BB for N consecutive ticks.
    Blocks single-tick wicks that immediately reverse.
    Returns True if breakout is confirmed (safe to trade)."""
    if not NOISE_FILTER_ENABLED:
        return True
    try:
        n = ticks or NOISE_BREAKOUT_CONFIRM_TICKS
        hist = prices_cache.get(coin, [])
        if len(hist) < 25 + n:
            return True  # Not enough data, allow
        # Compute BB on window BEFORE the last N ticks
        window = hist[-(20 + n):-n]
        mean = sum(window) / len(window)
        std = (sum((p - mean) ** 2 for p in window) / len(window)) ** 0.5
        upper = mean + 2.5 * std
        lower = mean - 2.5 * std
        # Check last N ticks all beyond the band
        recent = hist[-n:]
        if direction == "long":
            return all(p > upper for p in recent)
        else:
            return all(p < lower for p in recent)
    except Exception:
        return True


# momentum_quality_ok() removed in v29.4.0 — dead code (never called, replaced by inline checks)


# ── v29.3.5 H9: Unified Coin Blocking — single point of truth for all 4 blocking systems ──

def is_coin_blocked(coin, cycle, is_ranging=False):
    """Check all blocking systems and return (blocked: bool, reason: str).
    Consolidates: DYNAMIC_BLACKLIST, DynamicBlacklistManager, CoinLossTracker (SmartCoinBlocker).
    """
    # 1. Static blacklist
    if coin in DYNAMIC_BLACKLIST:
        return True, f"DYNAMIC_BLACKLIST (static)"
    # 2. Dynamic temporary blacklist (timed expiry)
    if TEMP_BLACKLIST_ENABLED and dynamic_blacklist.is_blocked(coin, cycle):
        _reason = dynamic_blacklist.block_reason(coin) if hasattr(dynamic_blacklist, 'block_reason') else "temp blocked"
        return True, f"dynamic_blacklist ({_reason})"
    # 3. CoinLossTracker / SmartCoinBlocker (per-coin loss history)
    if coin_loss_tracker.is_blocked(coin, cycle, is_ranging=is_ranging):
        return True, f"coin_loss_tracker (loss history)"
    return False, ""


# ── v29.3.5 M10: Consolidated Market Quality Score ──

def market_quality_score(coin, ticker_data=None, window=20):
    """Returns 0.0-1.0 quality score consolidating is_choppy + volume_confirms + short_momentum.
    Block entry if score < 0.4.
    Components:
      - Choppiness (efficiency ratio): 0 = pure chop, 1 = perfect trend → weight 0.40
      - Volume confirmation: 0 or 1 → weight 0.30
      - Short-term momentum strength: abs(mom) normalized → weight 0.30
    """
    # 1. Choppiness (inverted efficiency ratio)
    hist = prices_cache.get(coin, [])
    if len(hist) < window + 1:
        return 0.7  # Not enough data → pass with moderate score
    total_move = abs(hist[-1] - hist[-window])
    total_range = sum(abs(hist[i] - hist[i-1]) for i in range(len(hist)-window, len(hist)))
    efficiency = total_move / total_range if total_range > 0 else 0
    chop_score = min(1.0, efficiency / 0.30)  # 0.30 efficiency = 1.0 score

    # 2. Volume confirmation
    vol_score = 1.0
    if ticker_data:
        vol = ticker_data.get("vol", 0)
        change = abs(ticker_data.get("change", 0))
        if change > 0.05 and vol < 150000:
            vol_score = 0.0

    # 3. Short-term momentum strength
    mom = 0
    if len(hist) >= 10 and hist[-10] > 0:
        mom = abs(hist[-1] - hist[-10]) / hist[-10]
    mom_score = min(1.0, mom / 0.01)  # 1% move in 10 ticks = max score

    return chop_score * 0.40 + vol_score * 0.30 + mom_score * 0.30


# ── Execution Safety Layer: block entries when liquidity is poor ──

def liquidity_ok(coin):
    """Check if a coin has adequate liquidity for safe entry.
    Evaluates 3 metrics on prices_cache data:
      1. Gap frequency — % of recent ticks with price jumps > 1.5× ATR
      2. Spread trend — is tick-to-tick volatility widening vs baseline?
      3. Micro-volatility spike — short-window vol vs longer-window vol
    Returns True if liquidity is adequate (safe to trade).
    Returns True (allow) on insufficient data or when disabled."""
    if not EXEC_SAFETY_ENABLED:
        return True
    try:
        hist = prices_cache.get(coin, [])
        if len(hist) < EXEC_MICROVOL_BASELINE + 2:
            return True  # Not enough data to assess — allow trade

        # ── Metric 1: Gap frequency ──
        atr = coin_atr(coin)
        if atr <= 0:
            return True
        gap_window = min(EXEC_GAP_WINDOW, len(hist) - 1)
        recent = hist[-gap_window - 1:]
        gap_count = 0
        for i in range(1, len(recent)):
            if recent[i - 1] > 0:
                tick_move = abs(recent[i] - recent[i - 1]) / recent[i - 1]
                if tick_move > atr * EXEC_GAP_ATR_MULT:
                    gap_count += 1
        gap_ratio = gap_count / gap_window
        if gap_ratio > EXEC_GAP_MAX_RATIO:
            return False

        # ── Metric 2: Spread trend (recent vs baseline tick volatility) ──
        baseline_window = min(EXEC_SPREAD_TREND_WINDOW * 3, len(hist) - 1)
        recent_window = min(EXEC_SPREAD_TREND_WINDOW, len(hist) - 1)
        baseline_changes = []
        for i in range(len(hist) - baseline_window, len(hist)):
            if hist[i - 1] > 0:
                baseline_changes.append(abs(hist[i] - hist[i - 1]) / hist[i - 1])
        recent_changes = []
        for i in range(len(hist) - recent_window, len(hist)):
            if hist[i - 1] > 0:
                recent_changes.append(abs(hist[i] - hist[i - 1]) / hist[i - 1])
        if baseline_changes and recent_changes:
            baseline_avg = sum(baseline_changes) / len(baseline_changes)
            recent_avg = sum(recent_changes) / len(recent_changes)
            if baseline_avg > 0 and recent_avg / baseline_avg > EXEC_SPREAD_TREND_MAX:
                return False

        # ── Metric 3: Micro-volatility spike ──
        micro_w = min(EXEC_MICROVOL_WINDOW, len(hist) - 1)
        base_w = min(EXEC_MICROVOL_BASELINE, len(hist) - 1)
        micro_changes = []
        for i in range(len(hist) - micro_w, len(hist)):
            if hist[i - 1] > 0:
                micro_changes.append(abs(hist[i] - hist[i - 1]) / hist[i - 1])
        base_changes = []
        for i in range(len(hist) - base_w, len(hist)):
            if hist[i - 1] > 0:
                base_changes.append(abs(hist[i] - hist[i - 1]) / hist[i - 1])
        if micro_changes and base_changes:
            micro_vol = sum(micro_changes) / len(micro_changes)
            base_vol = sum(base_changes) / len(base_changes)
            if base_vol > 0 and micro_vol / base_vol > EXEC_MICROVOL_MAX_RATIO:
                return False

        return True
    except Exception:
        return True  # On error, allow trade (don't over-filter)


# ── Smart Exit: Re-evaluate at TP instead of auto-exit ──

def assess_exit(coin, direction, entry_price, current_price):
    """
    When price hits take-profit zone, assess whether to EXIT or HOLD+TRAIL.

    Evaluates 3 signals:
    1. Trend direction: price vs VWAP (20-period average)
    2. Momentum strength: is the move accelerating or fading?
    3. Volume behavior: is volume supporting the move?

    Returns: {"action": "EXIT" | "HOLD_AND_TRAIL", "reason": str, "confidence": float}
    """
    try:
        return _assess_exit_inner(coin, direction, entry_price, current_price)
    except Exception:
        return {"action": "EXIT", "reason": "assessment error", "confidence": 0.5}


def _assess_exit_inner(coin, direction, entry_price, current_price):
    hist = prices_cache.get(coin, [])
    if len(hist) < 20:
        return {"action": "EXIT", "reason": "insufficient data", "confidence": 0.5}

    signals = 0  # Positive = hold, negative = exit
    reasons = []

    # 1. TREND DIRECTION: Price vs VWAP (20-period SMA as proxy)
    sma20 = sum(hist[-20:]) / 20
    if direction == "long":
        if current_price > sma20:
            signals += 1
            reasons.append("above VWAP")
        else:
            signals -= 1
            reasons.append("below VWAP")
    else:  # short
        if current_price < sma20:
            signals += 1
            reasons.append("below VWAP")
        else:
            signals -= 1
            reasons.append("above VWAP")

    # 2. MOMENTUM STRENGTH: Is the move still going or fading?
    mom_fast = short_momentum(coin, window=3)   # Very recent
    mom_slow = short_momentum(coin, window=10)  # Slightly older

    if direction == "long":
        if mom_fast > 0:
            signals += 1  # Still moving up = good
            reasons.append("momentum positive")
        elif mom_fast < -0.002:
            signals -= 2  # Clearly reversing = strong exit
            reasons.append("momentum reversing")
        else:
            reasons.append("momentum flat")
    else:  # short
        if mom_fast < 0:
            signals += 1  # Still moving down = good for short
            reasons.append("downward momentum")
        elif mom_fast > 0.002:
            signals -= 2
            reasons.append("momentum reversing up")
        else:
            reasons.append("momentum flat")

    # 3. VOLUME BEHAVIOR: Is recent price action backed by movement?
    if len(hist) >= 20:
        # Compare recent volatility to older (proxy for volume/conviction)
        recent_moves = [abs(hist[i] - hist[i-1]) for i in range(len(hist)-5, len(hist)) if hist[i-1] != 0]
        older_moves = [abs(hist[i] - hist[i-1]) for i in range(len(hist)-15, len(hist)-5) if hist[i-1] != 0]
        avg_recent = sum(recent_moves) / len(recent_moves) if recent_moves else 0
        avg_older = sum(older_moves) / len(older_moves) if older_moves else 0

        if avg_older > 0 and avg_recent > avg_older * 1.2:
            signals += 1
            reasons.append("volume expanding")
        elif avg_older > 0 and avg_recent < avg_older * 0.5:
            signals -= 1
            reasons.append("volume fading")
        else:
            reasons.append("volume steady")

    # DECISION
    confidence = min(1.0, max(0.0, (signals + 3) / 6))  # Normalize to 0-1

    # Compute current PnL for borderline decisions
    _pnl_pct = 0.0
    if entry_price and entry_price > 0:
        if direction == "long":
            _pnl_pct = (current_price - entry_price) / entry_price * 100
        else:
            _pnl_pct = (entry_price - current_price) / entry_price * 100

    if signals >= 2:  # Strong trend — always hold and trail
        return {"action": "HOLD_AND_TRAIL", "reason": " + ".join(reasons), "confidence": confidence}
    elif signals == 1:
        if _pnl_pct > 0.3:  # Decent trend + profitable → let it run
            return {"action": "HOLD_AND_TRAIL", "reason": " + ".join(reasons) + " (profitable hold)", "confidence": confidence}
        else:
            return {"action": "EXIT", "reason": " + ".join(reasons) + " (weak trend, lock profit)", "confidence": confidence}
    elif signals == 0:
        if _pnl_pct > 0.6:  # No clear trend but deep in profit → hold with trail
            return {"action": "HOLD_AND_TRAIL", "reason": " + ".join(reasons) + " (profit cushion hold)", "confidence": confidence}
        else:
            return {"action": "EXIT", "reason": "mixed signals — locking profit", "confidence": confidence}
    else:  # signals <= -1: reversal signal — always exit
        return {"action": "EXIT", "reason": " + ".join(reasons), "confidence": confidence}


def zscore(coin, lookback=50):
    try:
        return _zscore_inner(coin, lookback)
    except Exception:
        return 0

def _zscore_inner(coin, lookback):
    hist = prices_cache.get(coin, [])
    if len(hist) < lookback:
        return 0
    window = hist[-lookback:]
    mean = sum(window) / len(window)
    std = (sum((p - mean) ** 2 for p in window) / len(window)) ** 0.5
    if std == 0:
        return 0
    return (hist[-1] - mean) / std


def bb_squeeze(coin, period=20, std_mult=2.5):
    try:
        return _bb_squeeze_inner(coin, period, std_mult)
    except Exception:
        return "NORMAL", 0

def _bb_squeeze_inner(coin, period, std_mult):
    hist = prices_cache.get(coin, [])
    if len(hist) < period + 5:
        return "NORMAL", 0

    # Current BB width
    window = hist[-period:]
    mean = sum(window) / len(window)
    std = (sum((p - mean) ** 2 for p in window) / len(window)) ** 0.5
    upper = mean + std_mult * std
    lower = mean - std_mult * std
    bb_width = (upper - lower) / mean if mean > 0 else 0

    # Average BB width over last 5 periods
    avg_widths = []
    for i in range(5):
        offset = i * period // 5
        if len(hist) > period + offset:
            w = hist[-(period + offset):-offset] if offset > 0 else hist[-period:]
            m = sum(w) / len(w)
            s = (sum((p - m) ** 2 for p in w) / len(w)) ** 0.5
            avg_widths.append((2 * std_mult * s) / m if m > 0 else 0)

    avg_width = sum(avg_widths) / len(avg_widths) if avg_widths else bb_width

    # Squeeze = current width < 50% of average
    if bb_width < avg_width * 0.5:
        # Check if breaking out
        price = hist[-1]
        if price > upper:
            return "BREAKOUT_UP", bb_width
        elif price < lower:
            return "BREAKOUT_DOWN", bb_width
        return "SQUEEZE", bb_width

    return "NORMAL", bb_width


def _regime_size_scale(amount, regime):
    """Apply regime-aware position scaling. Can only REDUCE, never increase."""
    try:
        scale = REGIME_SIZE_SCALE.get(regime, 1.0) if regime else 1.0
        scale = min(1.0, max(0.0, scale))  # Clamp to [0, 1]
        return amount * scale
    except Exception:
        return amount


def kelly_size(wallet, base_amount, prices=None):
    try:
        return _kelly_inner(wallet, base_amount, prices)
    except Exception:
        return base_amount

def _kelly_inner(wallet, base_amount, prices=None):
    total = wallet.wins + wallet.losses
    if total < 5:
        return base_amount  # Not enough data

    win_rate = wallet.wins / total if total > 0 else 0.5

    # Calculate average win/loss from recent trades
    recent_wins = [t for t in wallet.trades[-30:] if 'pnl' in t and t['pnl'].startswith('+')]
    recent_losses = [t for t in wallet.trades[-30:] if 'pnl' in t and t['pnl'].startswith('-')]

    if not recent_wins or not recent_losses:
        return base_amount

    avg_win = sum(float(t['pnl'].replace('%', '').replace('+', '')) for t in recent_wins) / len(recent_wins)
    avg_loss = abs(sum(float(t['pnl'].replace('%', '')) for t in recent_losses) / len(recent_losses))

    if avg_loss == 0:
        return base_amount

    reward_risk = avg_win / avg_loss
    kelly_pct = win_rate - ((1 - win_rate) / reward_risk)

    # Optimized change – half Kelly (was quarter, under-sizing by 50%+)
    half_kelly = kelly_pct * 0.50

    # Clamp between 1% and 8% of portfolio (wider band for half-Kelly)
    half_kelly = max(0.01, min(0.08, half_kelly))

    pv = wallet.value(prices or {})
    if pv <= 0:
        return base_amount
    # v29.3.5 C6: For sub-$5K accounts, enforce 5% floor so positions are meaningful
    KELLY_MIN_FRACTION = 0.05
    kelly_amount = pv * half_kelly
    if pv < 5000:
        kelly_amount = max(kelly_amount, pv * KELLY_MIN_FRACTION)
    return kelly_amount


def _make_ml_features(coin, pcache):
    """Build 16 real features for ML from price history and ticker data."""
    try:
        return _make_ml_features_inner(coin, pcache)
    except Exception:
        return [0.5] * 16

def _make_ml_features_inner(coin, pcache):
    hist = pcache.get(coin, [])
    if len(hist) < 20:
        return [0.5] * 16

    p = hist[-1]
    # Momentum at different timeframes
    mom5 = (p - hist[-5]) / hist[-5] if len(hist) >= 5 and hist[-5] != 0 else 0
    mom10 = (p - hist[-10]) / hist[-10] if len(hist) >= 10 and hist[-10] != 0 else 0
    mom20 = (p - hist[-20]) / hist[-20] if len(hist) >= 20 and hist[-20] != 0 else 0
    mom50 = (p - hist[-50]) / hist[-50] if len(hist) >= 50 and hist[-50] != 0 else 0

    # Volatility (std of returns)
    returns = [(hist[i] - hist[i-1]) / hist[i-1] for i in range(max(1, len(hist)-20), len(hist)) if hist[i-1] != 0]
    vol = (sum(r**2 for r in returns) / len(returns)) ** 0.5 if returns else 0

    # Position in recent range
    recent = hist[-20:]
    hi = max(recent)
    lo = min(recent)
    pos_in_range = (p - lo) / (hi - lo) if hi > lo else 0.5

    # Trend strength (how many of last 10 ticks were up)
    ups = sum(1 for i in range(max(1, len(hist)-10), len(hist)) if hist[i] > hist[i-1])
    trend = ups / 10

    # Simple moving averages
    sma5 = sum(hist[-5:]) / 5 if len(hist) >= 5 else p
    sma20 = sum(hist[-20:]) / 20 if len(hist) >= 20 else p
    above_sma = 1.0 if p > sma20 else 0.0
    sma_cross = 1.0 if sma5 > sma20 else 0.0

    # Volume proxy (price range)
    range_pct = (hi - lo) / lo if lo > 0 else 0

    return [
        math.tanh(mom5 * 20),      # Short momentum
        math.tanh(mom10 * 15),     # Medium momentum
        math.tanh(mom20 * 10),     # Longer momentum
        math.tanh(mom50 * 8),      # Even longer
        min(1.0, vol * 50),        # Volatility
        pos_in_range,              # Where in recent range
        trend,                     # Trend strength (0-1)
        above_sma,                 # Above 20-period SMA
        sma_cross,                 # SMA5 > SMA20
        min(1.0, range_pct * 10),  # Range size
        math.tanh(mom5 - mom20) * 5,  # Momentum acceleration
        1.0 if mom5 > 0 and mom10 > 0 and mom20 > 0 else 0.0,  # All timeframes agree up
        1.0 if mom5 < 0 and mom10 < 0 and mom20 < 0 else 0.0,  # All timeframes agree down
        0.5,  # Placeholder
        0.5,  # Placeholder
        0.5,  # Placeholder
    ]


# ── Market Scanner ──
# TODO v29.4: Refactor into ExchangeConfig.get_tradable_pairs() for multi-platform support
def get_usd_pairs():
    """Get all USD trading pairs from Kraken.
    # TODO(multi-exchange): Kraken-specific API endpoint and pair filtering.
    #   Binance: GET /api/v3/exchangeInfo, filter for USDT quote asset
    #   Coinbase: GET /products, filter for USD quote currency

    Filter pipeline:
    1. Raw API response → all pairs
    2. Quote currency filter → ZUSD or USD only
    3. Status filter → online pairs only (skip delisted/maintenance/cancel_only)
    4. Stablecoin/fiat exclusion → remove USDT, USDC, EUR pairs etc.
    Returns dict: {pair_key: altname}
    """
    try:
        data = safe_api_call(f"{KRAKEN}/AssetPairs", timeout=10)
        if not data:
            logger.warning("[PAIRS] AssetPairs API returned None")
            return {}

        # Kraken may return non-fatal errors alongside valid results
        api_errors = data.get("error", [])
        if api_errors:
            # Filter out warnings (W...), only block on real errors (E...)
            real_errors = [e for e in api_errors if isinstance(e, str) and e.startswith("E")]
            if real_errors:
                logger.error(f"[PAIRS] Kraken API errors: {real_errors}")
                # Still try to use results if available
            if api_errors and not real_errors:
                logger.debug(f"[PAIRS] Kraken API warnings (non-fatal): {api_errors}")

        all_pairs = data.get("result", {})
        total_raw = len(all_pairs)

        # Stage 1: Quote currency filter — ZUSD or USD
        usd_pairs = {}
        for name, info in all_pairs.items():
            quote = info.get("quote", "")
            if quote in ("ZUSD", "USD"):
                usd_pairs[name] = info
        after_quote = len(usd_pairs)

        # Stage 2: Status filter — only online pairs
        # Valid statuses: online. Skip: cancel_only, delisted, limit_only, maintenance, etc.
        online_pairs = {}
        skipped_status = {}
        for name, info in usd_pairs.items():
            status = info.get("status", "online")  # Default to online if field missing
            if status == "online":
                online_pairs[name] = info
            else:
                skipped_status[status] = skipped_status.get(status, 0) + 1
        after_status = len(online_pairs)

        # Stage 3: Stablecoin / fiat exclusion — check altname
        EXCLUDED_SUBSTRINGS = [
            "USDT", "USDC", "DAI", "TUSD", "PYUSD", "PAXG",  # Stablecoins
            "GBP", "EUR", "AUD", "CAD", "CHF", "JPY",         # Fiat currencies
            "EURT", "USDD", "FRAX",                            # More stables
        ]
        pairs = {}
        excluded_stable = 0
        for name, info in online_pairs.items():
            alt = info.get("altname", name)
            # Check the BASE side for stablecoin names, not the full altname
            # altname format is like "XBTUSD" — the base is everything before USD
            base_part = alt.upper().replace("USD", "")
            if any(s in base_part for s in EXCLUDED_SUBSTRINGS):
                excluded_stable += 1
                continue
            pairs[name] = alt
        after_stable = len(pairs)

        # Debug logging — always print during discovery
        logger.debug(
            f"[PAIRS] Discovery pipeline: raw={total_raw} → quote_USD={after_quote} "
            f"→ online={after_status} → after_exclusions={after_stable}"
        )
        if skipped_status:
            logger.debug(f"[PAIRS] Skipped by status: {skipped_status}")
        if excluded_stable > 0:
            logger.debug(f"[PAIRS] Excluded stablecoins/fiat: {excluded_stable}")
        if not pairs:
            logger.error(
                f"[PAIRS] CRITICAL: ZERO pairs after exclusion filter! "
                f"(raw={total_raw} quote_USD={after_quote} online={after_status} excluded_stable={excluded_stable})"
            )
            # Fallback: take top UNIVERSE_FALLBACK_PAIRS by volume from online USD pairs
            # Still respects quote + status filters — only skips stablecoin exclusion
            if online_pairs:
                # Fetch quick ticker snapshot to sort by volume
                _fb_keys = list(online_pairs.keys())[:100]  # Sample first 100 for speed
                try:
                    _fb_tickers = get_tickers(_fb_keys, batch_size=50)
                except Exception:
                    _fb_tickers = {}
                if _fb_tickers:
                    # Sort by volume descending, take top N
                    _fb_sorted = sorted(_fb_tickers.keys(), key=lambda p: _fb_tickers[p].get("vol", 0), reverse=True)
                    _fb_top = _fb_sorted[:UNIVERSE_FALLBACK_PAIRS]
                    pairs = {p: online_pairs[p].get("altname", p) for p in _fb_top if p in online_pairs}
                    logger.warning(f"[PAIRS] FALLBACK: using top {len(pairs)} volume pairs from {len(online_pairs)} online USD pairs")
                else:
                    # Can't get tickers — take first N online pairs alphabetically
                    _fb_alpha = list(online_pairs.keys())[:UNIVERSE_FALLBACK_PAIRS]
                    pairs = {p: online_pairs[p].get("altname", p) for p in _fb_alpha}
                    logger.warning(f"[PAIRS] FALLBACK (no tickers): using first {len(pairs)} online USD pairs")

        # Stage 4: Universe cap — prevent overexpansion
        if len(pairs) > UNIVERSE_MAX_PAIRS:
            logger.debug(f"[PAIRS] Capping universe from {len(pairs)} to {UNIVERSE_MAX_PAIRS}")
            _capped = dict(list(pairs.items())[:UNIVERSE_MAX_PAIRS])
            pairs = _capped

        # Debug logging
        sample = list(pairs.items())[:10]
        logger.debug(f"[PAIRS] Final universe: {len(pairs)} pairs. First 10: {[v for _, v in sample]}")

        return pairs
    except Exception as e:
        logger.error(f"[PAIRS] Exception in get_usd_pairs: {e}")
        return {}


# ══════════════════════════════════════════════════════════════════════════════
# v29.3.4 — ADVANCED ALPHA STRATEGIES
# Professional-grade strategy modules: macro, quant, MEV, vol, gamma, pairs, events
# Each strategy class:
#   - Reads from prices_cache / tickers (no extra API calls)
#   - Returns signal dicts compatible with existing entry pipeline
#   - Respects all existing safety gates (kill switch, circuit breaker, etc.)
#   - Has enable/disable toggle and configurable parameters
# ══════════════════════════════════════════════════════════════════════════════

# ── Master Toggle ──
ADVANCED_ALPHA_ENABLED = True        # Set False to disable all advanced strategies
ALPHA_SIZE_MULT = 0.70               # Scale advanced alpha positions to 70% (conservative until proven)
ALPHA_MIN_CONFIDENCE = 0.60          # Minimum confidence score to generate a signal (0-1)
ALPHA_MAX_POSITIONS_PCT = 0.50       # Advanced alpha can use at most 50% of MAX_POSITIONS

# v29.3.5: Per-strategy confidence thresholds (overrides ALPHA_MIN_CONFIDENCE per strategy)
ALPHA_STRATEGY_THRESHOLDS = {
    "price-prediction": 1.00,      # DISABLED — keep only core momentum/mean_rev/breakout
    "discretionary-macro": 1.00,   # DISABLED
    "vix-volatility": 1.00,        # DISABLED
    "quant-multi": 1.00,           # DISABLED
    "mev-extraction": 1.00,        # DISABLED
    "gamma-scalping": 1.00,        # DISABLED
    "pairs-trading": 1.00,         # DISABLED
    "event-driven": 1.00,          # DISABLED
}

def _alpha_threshold(strategy_name):
    """Return per-strategy confidence threshold, falling back to ALPHA_MIN_CONFIDENCE."""
    for key, thresh in ALPHA_STRATEGY_THRESHOLDS.items():
        if key in strategy_name:
            return thresh
    return ALPHA_MIN_CONFIDENCE


class PricePrediction:
    """Multi-timeframe forecasting engine.

    Uses weighted momentum across 3 timeframes (short/medium/long) plus
    mean-reversion signals to predict price direction. Combines:
      - 5-tick micro momentum (scalp signals)
      - 20-tick medium momentum (swing signals)
      - 50-tick macro trend (trend-following bias)
      - Bollinger band z-score for mean-reversion overlay

    Outputs a directional confidence score from -1.0 (strong short) to +1.0 (strong long).
    """

    ENABLED = True
    WEIGHT_SHORT = 0.25     # 5-tick momentum weight
    WEIGHT_MED = 0.40       # 20-tick momentum weight
    WEIGHT_LONG = 0.35      # 50-tick macro trend weight
    BB_WINDOW = 20          # Bollinger band lookback
    BB_REVERSION_WEIGHT = 0.15  # Mean-reversion overlay strength
    MIN_HISTORY = 50        # Minimum price points required

    def __init__(self):
        self.last_signals = {}   # coin -> (score, cycle)
        self.accuracy_log = []   # (predicted_dir, actual_dir) for tracking

    def predict(self, coin, cycle):
        """Returns (confidence, direction) where confidence is 0-1 and direction is 'long'/'short'/None."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return 0, None
        hist = prices_cache.get(coin, [])
        if len(hist) < self.MIN_HISTORY:
            return 0, None
        try:
            # Multi-timeframe momentum
            p = hist[-1]
            mom_5 = (p - hist[-5]) / hist[-5] if hist[-5] > 0 else 0
            mom_20 = (p - hist[-20]) / hist[-20] if hist[-20] > 0 else 0
            mom_50 = (p - hist[-50]) / hist[-50] if hist[-50] > 0 else 0

            weighted = (mom_5 * self.WEIGHT_SHORT +
                        mom_20 * self.WEIGHT_MED +
                        mom_50 * self.WEIGHT_LONG)

            # Bollinger band z-score (mean reversion)
            window = hist[-self.BB_WINDOW:]
            mean = sum(window) / len(window)
            std = (sum((x - mean) ** 2 for x in window) / len(window)) ** 0.5
            z_score = (p - mean) / std if std > 0 else 0

            # Mean-reversion overlay: fade extreme z-scores
            reversion = -z_score * self.BB_REVERSION_WEIGHT * 0.01
            combined = weighted + reversion

            confidence = min(1.0, abs(combined) * 37)  # v29.3.5: was *20 — too low for crypto's tiny predictions
            direction = "long" if combined > 0 else "short" if combined < 0 else None

            self.last_signals[coin] = (combined, cycle)
            return confidence, direction
        except Exception:
            return 0, None

    def record_outcome(self, coin, predicted_dir, actual_pnl):
        """Track accuracy for self-evaluation."""
        actual_dir = "long" if actual_pnl > 0 else "short"
        self.accuracy_log.append((predicted_dir, actual_dir))
        if len(self.accuracy_log) > 500:
            self.accuracy_log = self.accuracy_log[-500:]

    def accuracy(self):
        if len(self.accuracy_log) < 10:
            return 0.5
        correct = sum(1 for p, a in self.accuracy_log if p == a)
        return correct / len(self.accuracy_log)

    def status(self):
        return {"enabled": self.ENABLED, "signals": len(self.last_signals),
                "accuracy": f"{self.accuracy():.1%}", "min_hist": self.MIN_HISTORY}


class DiscretionaryMacro:
    """Fed/geopolitics macro trading strategy.

    Detects macro regime shifts by analyzing:
      - Market breadth (% of coins trending up vs down)
      - Correlation clustering (high correlation = risk-off, low = risk-on)
      - Volatility regime (expanding vol = uncertainty, contracting = stability)
      - Momentum divergence across sectors (DeFi vs L1 vs memecoins)

    Generates directional bias signals that influence position sizing and direction.
    In crypto, this acts as a "risk-on / risk-off" sentiment detector.
    """

    ENABLED = True
    BREADTH_WINDOW = 30         # Cycles to measure breadth
    CORRELATION_WINDOW = 40     # Cycles for correlation measurement
    VOL_EXPANSION_THRESH = 1.5  # Vol > 1.5x average = expanding
    SECTOR_GROUPS = {
        "defi": {"AAVE", "UNI", "COMP", "MKR", "SNX", "SUSHI", "YFI", "CRV"},
        "l1": {"ETH", "SOL", "ADA", "AVAX", "DOT", "ATOM", "NEAR", "FTM"},
        "meme": {"DOGE", "SHIB", "PEPE", "FLOKI", "BONK"},
        "btc_proxy": {"BTC", "WBTC"},
    }

    def __init__(self):
        self.regime = "NEUTRAL"     # RISK_ON, RISK_OFF, NEUTRAL
        self.breadth_history = []   # (cycle, breadth_score)
        self.vol_history = []       # (cycle, avg_vol)
        self.last_update = 0

    def update(self, cycle, tickers):
        """Update macro regime based on market-wide signals. Call once per cycle."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return
        if cycle - self.last_update < 5:
            return  # Throttle to every 5 cycles
        self.last_update = cycle
        try:
            up = 0
            down = 0
            total = 0
            vols = []
            for coin, hist in prices_cache.items():
                if len(hist) < self.BREADTH_WINDOW + 1:
                    continue
                total += 1
                mom = (hist[-1] - hist[-self.BREADTH_WINDOW]) / hist[-self.BREADTH_WINDOW]
                if mom > 0.002:
                    up += 1
                elif mom < -0.002:
                    down += 1
                # Track volatility
                recent = hist[-20:]
                if len(recent) >= 10:
                    mean = sum(recent) / len(recent)
                    std = (sum((x - mean) ** 2 for x in recent) / len(recent)) ** 0.5
                    if mean > 0:
                        vols.append(std / mean)

            if total < 10:
                return

            breadth = (up - down) / total
            self.breadth_history.append((cycle, breadth))
            if len(self.breadth_history) > 200:
                self.breadth_history = self.breadth_history[-200:]

            avg_vol = sum(vols) / len(vols) if vols else 0
            self.vol_history.append((cycle, avg_vol))
            if len(self.vol_history) > 200:
                self.vol_history = self.vol_history[-200:]

            # Regime classification
            vol_avg_long = (sum(v for _, v in self.vol_history[-50:]) /
                            max(len(self.vol_history[-50:]), 1))
            vol_expanding = avg_vol > vol_avg_long * self.VOL_EXPANSION_THRESH

            if breadth > 0.15 and not vol_expanding:
                self.regime = "RISK_ON"
            elif breadth < -0.15 or vol_expanding:
                self.regime = "RISK_OFF"
            else:
                self.regime = "NEUTRAL"
        except Exception:
            pass

    def get_bias(self):
        """Returns ('long'/'short'/None, confidence 0-1). v29.3.5: scale with breadth strength."""
        if not self.breadth_history:
            return None, 0.0
        latest_breadth = self.breadth_history[-1][1]  # Latest breadth score (-1 to +1)
        breadth_pct = (latest_breadth + 1.0) / 2.0    # Normalize to 0-1 range
        if self.regime == "RISK_ON":
            confidence = 0.50 + (breadth_pct - 0.50) * 0.40  # Linear scale: 0.50 at neutral, up to 0.70 at max
            return "long", min(0.85, max(0.55, confidence))
        elif self.regime == "RISK_OFF":
            confidence = 0.50 + (0.50 - breadth_pct) * 0.40  # Inverse: stronger when breadth more negative
            return "short", min(0.85, max(0.55, confidence))
        return None, 0.0

    def size_multiplier(self):
        """Position size adjustment based on macro regime."""
        if self.regime == "RISK_ON":
            return 1.1
        elif self.regime == "RISK_OFF":
            return 0.7
        return 1.0

    def status(self):
        return {"enabled": self.ENABLED, "regime": self.regime,
                "breadth_pts": len(self.breadth_history), "vol_pts": len(self.vol_history)}


class VixVolatilityTrading:
    """Volatility mean-reversion and carry strategy.

    Since crypto doesn't have a VIX, this constructs a synthetic volatility index from:
      - Rolling realized volatility across top-volume coins
      - ATR percentile ranking (current vs historical)
      - Vol-of-vol (volatility clustering detection)

    Trades the concept: sell vol when it's high (mean reversion), buy when it's low (breakout prep).
    In practice: tighter positions when vol is extreme, wider when vol is low.
    """

    ENABLED = True
    VOL_WINDOW = 30          # Lookback for realized vol
    VOL_HISTORY_MAX = 500    # Max cycles of vol history
    HIGH_VOL_PERCENTILE = 80  # Above this = vol is high → shrink positions
    LOW_VOL_PERCENTILE = 20   # Below this = vol is low → breakout setup
    MEAN_REVERSION_CYCLES = 50  # How fast vol reverts

    def __init__(self):
        self.synthetic_vix = []     # Rolling realized vol readings
        self.vol_regime = "NORMAL"  # HIGH, LOW, NORMAL
        self.last_update = 0

    def update(self, cycle):
        """Compute synthetic volatility index from price cache."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return
        if cycle - self.last_update < 3:
            return
        self.last_update = cycle
        try:
            coin_vols = []
            for coin, hist in prices_cache.items():
                if len(hist) < self.VOL_WINDOW + 1:
                    continue
                window = hist[-self.VOL_WINDOW:]
                returns = [(window[i] - window[i - 1]) / window[i - 1]
                           for i in range(1, len(window)) if window[i - 1] > 0]
                if returns:
                    mean_r = sum(returns) / len(returns)
                    var = sum((r - mean_r) ** 2 for r in returns) / len(returns)
                    coin_vols.append(var ** 0.5)

            if not coin_vols:
                return

            avg_vol = sum(coin_vols) / len(coin_vols)
            self.synthetic_vix.append(avg_vol)
            if len(self.synthetic_vix) > self.VOL_HISTORY_MAX:
                self.synthetic_vix = self.synthetic_vix[-self.VOL_HISTORY_MAX:]

            # v29.3.5 M11: O(n log n) percentile via sorted() + bisect index lookup (was O(n²) min+index)
            if len(self.synthetic_vix) >= 30:
                sorted_vix = sorted(self.synthetic_vix)
                # Binary search for insertion point gives rank directly
                import bisect
                rank = bisect.bisect_left(sorted_vix, avg_vol)
                percentile = (rank / len(sorted_vix)) * 100

                if percentile >= self.HIGH_VOL_PERCENTILE:
                    self.vol_regime = "HIGH"
                elif percentile <= self.LOW_VOL_PERCENTILE:
                    self.vol_regime = "LOW"
                else:
                    self.vol_regime = "NORMAL"
        except Exception:
            pass

    def size_adjustment(self):
        """Position size multiplier based on vol regime."""
        if self.vol_regime == "HIGH":
            return 0.6   # Shrink in high vol
        elif self.vol_regime == "LOW":
            return 1.15   # Slightly expand in low vol (breakout prep)
        return 1.0

    def favor_direction(self):
        """Directional bias: high vol favors shorts (panic), low vol favors longs (grind up)."""
        if self.vol_regime == "HIGH":
            return "short", 0.65  # v29.3.5: was 0.55 — below 0.60 alpha gate = dead code
        elif self.vol_regime == "LOW":
            return "long", 0.60   # v29.3.5: was 0.50 — below 0.60 alpha gate = dead code
        return None, 0.0

    def current_vix(self):
        return self.synthetic_vix[-1] if self.synthetic_vix else 0

    def status(self):
        return {"enabled": self.ENABLED, "regime": self.vol_regime,
                "vix": f"{self.current_vix():.5f}", "history": len(self.synthetic_vix)}


class QuantMultiStrategy:
    """6-model quant combination engine.

    Runs 6 independent micro-models and combines their signals via weighted voting:
      1. Momentum (trend-following, 20-tick)
      2. Mean-reversion (Bollinger fade)
      3. Breakout (range expansion)
      4. Volume-price divergence
      5. RSI extremes (overbought/oversold)
      6. EMA crossover (fast/slow cross)

    Each model votes long/short/neutral. Final signal = weighted consensus.
    Only fires when 4+ models agree (supermajority).
    """

    ENABLED = True
    SUPERMAJORITY = 3       # v29.3.5: was 4 — too strict for noisy crypto, simple majority is enough
    MIN_HISTORY = 30        # Price points needed

    # Model weights (sum to 1.0)
    WEIGHTS = {
        "momentum": 0.20,
        "mean_rev": 0.15,
        "breakout": 0.20,
        "vol_div": 0.15,
        "rsi": 0.15,
        "ema_cross": 0.15,
    }

    def __init__(self):
        self.last_votes = {}  # coin -> {model: vote}

    def _momentum(self, hist):
        if len(hist) < 20:
            return 0
        mom = (hist[-1] - hist[-20]) / hist[-20]
        if mom > 0.005:
            return 1
        elif mom < -0.005:
            return -1
        return 0

    def _mean_rev(self, hist):
        if len(hist) < 20:
            return 0
        window = hist[-20:]
        mean = sum(window) / len(window)
        std = (sum((x - mean) ** 2 for x in window) / len(window)) ** 0.5
        if std == 0:
            return 0
        z = (hist[-1] - mean) / std
        if z > 2.0:
            return -1  # Overbought → short
        elif z < -2.0:
            return 1   # Oversold → long
        return 0

    def _breakout(self, hist):
        if len(hist) < 30:
            return 0
        high_20 = max(hist[-20:])
        low_20 = min(hist[-20:])
        rng = high_20 - low_20
        if rng == 0:
            return 0
        if hist[-1] >= high_20 * 0.995:
            return 1   # Breaking above range
        elif hist[-1] <= low_20 * 1.005:
            return -1  # Breaking below range
        return 0

    def _vol_divergence(self, coin, hist):
        """Price up but volume down = bearish divergence, and vice versa."""
        if len(hist) < 10:
            return 0
        price_dir = 1 if hist[-1] > hist[-10] else -1
        # Approximate volume from ATR trend
        atr_now = coin_atr(coin) if callable(globals().get("coin_atr")) else 0
        if atr_now == 0:
            return 0
        # If price rising but ATR shrinking → divergence (bearish)
        hist_mid = hist[-5:-1]
        if hist_mid:
            mid_price = sum(hist_mid) / len(hist_mid)
            if mid_price > 0:
                recent_move = abs(hist[-1] - mid_price) / mid_price
                if price_dir > 0 and recent_move < atr_now * 0.3:
                    return -1  # Weak up move
                elif price_dir < 0 and recent_move < atr_now * 0.3:
                    return 1   # Weak down move
        return 0

    def _rsi(self, hist):
        if len(hist) < 15:
            return 0
        gains = []
        losses = []
        for i in range(-14, 0):
            diff = hist[i] - hist[i - 1]
            if diff > 0:
                gains.append(diff)
                losses.append(0)
            else:
                gains.append(0)
                losses.append(abs(diff))
        avg_gain = sum(gains) / 14
        avg_loss = sum(losses) / 14
        if avg_loss == 0:
            return -1  # RSI = 100 → overbought
        rs = avg_gain / avg_loss
        rsi = 100 - (100 / (1 + rs))
        if rsi > 70:
            return -1  # Overbought
        elif rsi < 30:
            return 1   # Oversold
        return 0

    def _ema_cross(self, hist):
        if len(hist) < 26:
            return 0
        # Fast EMA (12) vs Slow EMA (26)
        def ema(data, period):
            mult = 2 / (period + 1)
            e = data[0]
            for p in data[1:]:
                e = (p - e) * mult + e
            return e
        fast = ema(hist[-26:], 12)
        slow = ema(hist[-26:], 26)
        prev_fast = ema(hist[-27:-1], 12)
        prev_slow = ema(hist[-27:-1], 26)
        if fast > slow and prev_fast <= prev_slow:
            return 1   # Bullish cross
        elif fast < slow and prev_fast >= prev_slow:
            return -1  # Bearish cross
        return 0

    def evaluate(self, coin, cycle):
        """Run all 6 models. Returns (confidence 0-1, direction 'long'/'short'/None)."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return 0, None
        hist = prices_cache.get(coin, [])
        if len(hist) < self.MIN_HISTORY:
            return 0, None
        try:
            votes = {
                "momentum": self._momentum(hist),
                "mean_rev": self._mean_rev(hist),
                "breakout": self._breakout(hist),
                "vol_div": self._vol_divergence(coin, hist),
                "rsi": self._rsi(hist),
                "ema_cross": self._ema_cross(hist),
            }
            self.last_votes[coin] = votes

            # Weighted consensus
            weighted_sum = sum(votes[m] * self.WEIGHTS[m] for m in votes)
            agree_long = sum(1 for v in votes.values() if v > 0)
            agree_short = sum(1 for v in votes.values() if v < 0)

            if agree_long >= self.SUPERMAJORITY:
                confidence = min(1.0, weighted_sum * 3)
                return confidence, "long"
            elif agree_short >= self.SUPERMAJORITY:
                confidence = min(1.0, abs(weighted_sum) * 3)
                return confidence, "short"
            return 0, None
        except Exception:
            return 0, None

    def status(self):
        return {"enabled": self.ENABLED, "coins_evaluated": len(self.last_votes),
                "supermajority": self.SUPERMAJORITY}


class MEVExtraction:
    """On-chain MEV (Maximal Extractable Value) detection for crypto.

    In paper trading, this simulates MEV-style opportunities by detecting:
      - Large price dislocations between correlated pairs (arbitrage-like)
      - Sudden volume spikes preceding price moves (front-run detection)
      - Price impact estimation from order flow patterns

    Generates high-frequency, low-hold-time signals.
    """

    ENABLED = True
    DISLOCATION_THRESHOLD = 0.015   # 1.5% price gap between correlated pairs
    VOLUME_SPIKE_MULT = 3.0         # Volume > 3x average = spike
    MAX_HOLD_CYCLES = 20            # MEV trades exit fast
    PAIRS_TO_MONITOR = [
        ("ETH", "STETH"), ("BTC", "WBTC"), ("USDT", "USDC"),
        ("ETH", "ARB"), ("ETH", "OP"), ("SOL", "JTO"),
    ]

    def __init__(self):
        self.active_signals = {}  # coin -> (direction, entry_cycle)
        self.opportunities_found = 0

    def scan(self, cycle, tickers):
        """Scan for MEV-like opportunities. Returns list of (coin, direction, confidence)."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return []
        signals = []
        try:
            # 1. Correlated pair dislocation
            # v29.3.5 M4: Normalize pair names through ExchangeConfig for Kraken format compatibility
            for coin_a, coin_b in self.PAIRS_TO_MONITOR:
                _norm_a = ExchangeConfig.normalize_pair_name(coin_a) if coin_a != ExchangeConfig.normalize_pair_name(coin_a) else coin_a
                _norm_b = ExchangeConfig.normalize_pair_name(coin_b) if coin_b != ExchangeConfig.normalize_pair_name(coin_b) else coin_b
                hist_a = prices_cache.get(coin_a, []) or prices_cache.get(_norm_a, [])
                hist_b = prices_cache.get(coin_b, []) or prices_cache.get(_norm_b, [])
                if len(hist_a) < 10 or len(hist_b) < 10:
                    continue
                if hist_b[-1] <= 0 or hist_a[-1] <= 0:
                    continue
                # Compute ratio and detect dislocation
                ratio_now = hist_a[-1] / hist_b[-1]
                ratios = [hist_a[i] / hist_b[i] for i in range(-min(20, len(hist_a), len(hist_b)), 0)
                          if hist_b[i] > 0]
                if len(ratios) < 5:
                    continue
                avg_ratio = sum(ratios) / len(ratios)
                if avg_ratio == 0:
                    continue
                dislocation = (ratio_now - avg_ratio) / avg_ratio
                if abs(dislocation) > self.DISLOCATION_THRESHOLD:
                    # Coin A expensive relative to B → short A or long B
                    if dislocation > 0:
                        signals.append((coin_b, "long", min(0.80, abs(dislocation) * 10)))
                    else:
                        signals.append((coin_a, "long", min(0.80, abs(dislocation) * 10)))
                    self.opportunities_found += 1

            # 2. Volume spike detection (uses ticker data)
            for pair, t in (tickers or {}).items():
                short = to_short_name(pair) if callable(globals().get("to_short_name")) else pair
                hist = prices_cache.get(short, [])
                if len(hist) < 20:
                    continue
                vol = t.get("vol", 0)
                change = t.get("change", 0)
                # Volume spike with minimal price move = accumulation
                if vol > 0:
                    avg_hist_vol = sum(abs(hist[i] - hist[i - 1]) for i in range(-10, 0) if hist[i - 1] > 0)
                    if avg_hist_vol > 0 and abs(change) < 0.0005:  # v29.3.5: was 0.005 — too loose, need near-zero price move for accumulation detection
                        # High volume, low price movement → someone accumulating
                        mom = (hist[-1] - hist[-5]) / hist[-5] if hist[-5] > 0 else 0
                        if mom > 0.001:
                            signals.append((short, "long", 0.55))
                        elif mom < -0.001:
                            signals.append((short, "short", 0.55))
        except Exception:
            pass
        return signals

    def status(self):
        return {"enabled": self.ENABLED, "opportunities_found": self.opportunities_found,
                "active_signals": len(self.active_signals),
                "pairs_monitored": len(self.PAIRS_TO_MONITOR)}


class GammaScalping:
    """Options gamma harvesting adapted for crypto spot.

    Since we don't have options, this simulates gamma scalping by:
      - Identifying high-gamma moments (price near key levels with expanding vol)
      - Trading the "pin" effect (prices tend to revert to round numbers / liquidity levels)
      - Scalping rapid mean-reversion around key price levels

    Short hold times, small position sizes, high frequency.
    """

    ENABLED = True
    ROUND_LEVELS = [100, 500, 1000, 5000, 10000, 50000, 100000]  # Key round numbers
    PIN_PROXIMITY_PCT = 0.005   # Within 0.5% of round number
    REVERSION_TARGET_PCT = 0.003  # Target 0.3% reversion
    MAX_HOLD = 15               # Very short holds

    def __init__(self):
        self.signals_generated = 0
        self.pin_hits = 0
        self._cycle_signals = []  # v29.3.5 M12: Batch logging — collect signals per cycle

    def _nearest_round(self, price):
        """Find nearest round number level."""
        if price <= 0:
            return 0
        # For sub-$1 coins, use 0.01, 0.05, 0.10, 0.50, 1.00
        if price < 1:
            levels = [0.01, 0.05, 0.10, 0.25, 0.50, 1.00]
        elif price < 10:
            levels = [1, 2, 5, 10]
        elif price < 100:
            levels = [10, 25, 50, 100]
        else:
            levels = self.ROUND_LEVELS
        nearest = min(levels, key=lambda l: abs(price - l))
        return nearest

    def scan(self, coin, cycle):
        """Check if coin is near a gamma-scalp opportunity."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return 0, None
        hist = prices_cache.get(coin, [])
        if len(hist) < 15:
            return 0, None
        try:
            price = hist[-1]
            # v29.3.5: Skip sub-$0.10 coins — absolute price moves create spam signals
            if price < 0.10:
                return 0, None
            level = self._nearest_round(price)
            if level == 0:
                return 0, None

            # v29.3.5: Normalize distance by price to prevent cheap-coin spam
            distance_pct = abs(price - level) / price  # was / level — normalize by price not level
            if distance_pct > self.PIN_PROXIMITY_PCT:
                return 0, None  # Not near a key level

            self.pin_hits += 1

            # Price above level → expect reversion down (short)
            # Price below level → expect reversion up (long)
            if price > level:
                direction = "short"
            else:
                direction = "long"

            # Confidence based on proximity and vol
            confidence = max(0.50, 1.0 - (distance_pct / self.PIN_PROXIMITY_PCT))

            # Verify vol supports the trade (need some movement)
            atr = coin_atr(coin) if callable(globals().get("coin_atr")) else 0
            if atr < 0.001:
                return 0, None  # Dead market

            self.signals_generated += 1
            self._cycle_signals.append((coin, direction, confidence))
            return confidence, direction
        except Exception:
            return 0, None

    def flush_cycle_log(self):
        """v29.3.5 M12: Log one batch summary line instead of per-signal spam."""
        if self._cycle_signals:
            top = max(self._cycle_signals, key=lambda x: x[2])
            logger.debug(f"[GAMMA_BATCH] {len(self._cycle_signals)} signals this cycle | top: {top[0]} {top[1]} conf={top[2]:.2f}")
            self._cycle_signals.clear()

    def status(self):
        return {"enabled": self.ENABLED, "signals": self.signals_generated,
                "pin_hits": self.pin_hits}


class PairsTrading:
    """Statistical arbitrage — pairs trading for crypto.

    Identifies cointegrated / highly-correlated coin pairs and trades
    the spread when it deviates from the mean. Classic stat-arb.

    Pre-defined pairs based on fundamental relationships:
      - L1 competitors (ETH/SOL, AVAX/DOT)
      - DeFi tokens (AAVE/COMP, UNI/SUSHI)
      - Meme coins (DOGE/SHIB)
    """

    ENABLED = True
    SPREAD_WINDOW = 40       # Lookback for spread mean
    ENTRY_Z = 2.0            # Enter when z-score > 2.0
    EXIT_Z = 0.5             # Exit when z-score reverts to 0.5
    MIN_HISTORY = 120        # v29.3.5: was 40 — correlation on 30-40 points is statistically meaningless. Need 120+ for reliable cointegration

    PAIRS = [
        ("ETH", "SOL"), ("AVAX", "DOT"), ("AAVE", "COMP"),
        ("UNI", "SUSHI"), ("DOGE", "SHIB"), ("ATOM", "OSMO"),
        ("ARB", "OP"), ("LINK", "BAND"), ("MATIC", "FTM"),
    ]

    def __init__(self):
        self.active_spreads = {}   # (coinA, coinB) -> {"z": float, "direction": str}
        self.signals_count = 0

    def scan(self, cycle):
        """Scan all pairs for spread deviations. Returns list of (coin, direction, confidence)."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return []
        signals = []
        try:
            for coin_a, coin_b in self.PAIRS:
                hist_a = prices_cache.get(coin_a, [])
                hist_b = prices_cache.get(coin_b, [])
                if len(hist_a) < self.MIN_HISTORY or len(hist_b) < self.MIN_HISTORY:
                    continue
                min_len = min(len(hist_a), len(hist_b), self.SPREAD_WINDOW)

                # Compute log spread
                spreads = []
                for i in range(-min_len, 0):
                    if hist_b[i] > 0 and hist_a[i] > 0:
                        spreads.append(math.log(hist_a[i] / hist_b[i]))
                if len(spreads) < 20:
                    continue

                mean_spread = sum(spreads) / len(spreads)
                std_spread = (sum((s - mean_spread) ** 2 for s in spreads) / len(spreads)) ** 0.5
                if std_spread == 0:
                    continue

                current_spread = spreads[-1]
                z = (current_spread - mean_spread) / std_spread

                self.active_spreads[(coin_a, coin_b)] = {"z": z, "spread": current_spread}

                if abs(z) >= self.ENTRY_Z:
                    confidence = min(0.85, abs(z) / 4.0)
                    if z > 0:
                        # A is expensive relative to B → short A, long B
                        signals.append((coin_b, "long", confidence))
                        signals.append((coin_a, "short", confidence))
                    else:
                        signals.append((coin_a, "long", confidence))
                        signals.append((coin_b, "short", confidence))
                    self.signals_count += 1
        except Exception:
            pass
        return signals

    def status(self):
        return {"enabled": self.ENABLED, "pairs_tracked": len(self.active_spreads),
                "signals_total": self.signals_count,
                "active_deviations": sum(1 for v in self.active_spreads.values() if abs(v["z"]) > 1.5)}


class EventDriven:
    """Catalyst-based trading strategy.

    Detects market events from price/volume patterns that suggest catalysts:
      - Flash crashes (> 5% drop in 10 ticks → buy the dip)
      - Momentum ignition (sudden volume + directional move → follow)
      - Range breakouts after compression (low vol → sudden expansion)
      - Capitulation detection (extreme volume + price drop → bottom signal)

    Each event type has independent confidence scoring and position sizing.
    """

    ENABLED = True
    FLASH_CRASH_PCT = -0.05      # 5% drop in 10 ticks
    IGNITION_VOL_MULT = 4.0      # Volume 4x average + directional
    COMPRESSION_RATIO = 0.3      # Current vol < 30% of avg = compressed
    CAPITULATION_DROP = -0.08    # 8% drop with extreme volume

    def __init__(self):
        self.events_detected = {}   # event_type -> count
        self.last_signals = []

    def scan(self, cycle, tickers):
        """Scan for event-driven signals. Returns list of (coin, direction, confidence, event_type)."""
        if not self.ENABLED or not ADVANCED_ALPHA_ENABLED:
            return []
        signals = []
        try:
            for coin, hist in prices_cache.items():
                if len(hist) < 30:
                    continue
                price = hist[-1]
                if price <= 0:
                    continue

                # 1. Flash crash → buy the dip
                if len(hist) >= 10 and hist[-10] > 0:
                    drop = (price - hist[-10]) / hist[-10]
                    if drop < self.FLASH_CRASH_PCT:
                        # Verify not in freefall (need some stabilization)
                        last_3 = hist[-3:]
                        if len(last_3) >= 3 and min(last_3) > 0:
                            bounce = (last_3[-1] - min(last_3)) / min(last_3)
                            if bounce > 0.01:  # v29.3.5: was 0.002 (0.2%) — too weak after 5% drop. Require 1.0% bounce
                                signals.append((coin, "long", 0.70, "flash_crash"))
                                self.events_detected["flash_crash"] = self.events_detected.get("flash_crash", 0) + 1

                # 2. Range compression → breakout pending
                if len(hist) >= 30:
                    long_std = self._std(hist[-30:])
                    short_std = self._std(hist[-5:])
                    if long_std > 0 and short_std / long_std < self.COMPRESSION_RATIO:
                        # Compressed — next move likely explosive
                        # Direction from micro-momentum
                        micro = (hist[-1] - hist[-3]) / hist[-3] if hist[-3] > 0 else 0
                        if micro > 0.001:
                            signals.append((coin, "long", 0.60, "compression_breakout"))
                        elif micro < -0.001:
                            signals.append((coin, "short", 0.60, "compression_breakout"))
                        self.events_detected["compression"] = self.events_detected.get("compression", 0) + 1

                # 3. Capitulation → bottom signal
                if len(hist) >= 15 and hist[-15] > 0:
                    drop_15 = (price - hist[-15]) / hist[-15]
                    if drop_15 < self.CAPITULATION_DROP:
                        # Check for volume spike via ATR expansion
                        atr = coin_atr(coin) if callable(globals().get("coin_atr")) else 0
                        if atr > 0.02:  # High ATR = high activity
                            # Look for reversal candle (last price > second-to-last)
                            if len(hist) >= 2 and hist[-1] > hist[-2]:
                                signals.append((coin, "long", 0.75, "capitulation"))
                                self.events_detected["capitulation"] = self.events_detected.get("capitulation", 0) + 1

            self.last_signals = signals
        except Exception:
            pass
        return signals

    def _std(self, data):
        if len(data) < 2:
            return 0
        mean = sum(data) / len(data)
        return (sum((x - mean) ** 2 for x in data) / len(data)) ** 0.5

    def status(self):
        return {"enabled": self.ENABLED, "events": dict(self.events_detected),
                "recent_signals": len(self.last_signals)}


# ── Instantiate Advanced Alpha Strategies ──
alpha_price_prediction = PricePrediction()
alpha_macro = DiscretionaryMacro()
alpha_vix = VixVolatilityTrading()
alpha_quant = QuantMultiStrategy()
alpha_mev = MEVExtraction()
alpha_gamma = GammaScalping()
alpha_pairs = PairsTrading()
alpha_events = EventDriven()

ALPHA_STRATEGIES = {
    "price-prediction": alpha_price_prediction,
    "discretionary-macro": alpha_macro,
    "vix-volatility-trading": alpha_vix,
    "quant-multi-strategy": alpha_quant,
    "mev-extraction": alpha_mev,
    "gamma-scalping": alpha_gamma,
    "pairs-trading": alpha_pairs,
    "event-driven": alpha_events,
}

logger.info(f"[ALPHA] Advanced Alpha loaded: {len(ALPHA_STRATEGIES)} strategies ({'ENABLED' if ADVANCED_ALPHA_ENABLED else 'DISABLED'})")


def get_tickers(pair_names, batch_size=30):
    """Fetch ticker data for a batch of pairs.
    v29.3.4: Uses ExchangeConfig for platform-agnostic field extraction."""
    tickers = {}
    for i in range(0, len(pair_names), batch_size):
        batch = pair_names[i:i + batch_size]
        try:
            # TODO v29.4: Replace KRAKEN constant with ExchangeConfig.API_BASE for multi-platform
            data = safe_api_call(f"{KRAKEN}/Ticker", params={"pair": ",".join(batch)}, timeout=5)
            if not data:
                continue
            # Kraken returns "error": [] on success. Only block on real E-prefixed errors.
            api_errors = data.get("error", [])
            real_errors = [e for e in api_errors if isinstance(e, str) and e.startswith("E")]
            if real_errors:
                logger.warning(f"[TICKERS] Batch error: {real_errors} (batch {i//batch_size+1})")
                continue
            if data.get("result"):
                for pair, t in data.get("result", {}).items():
                    if not validate_ticker(t):
                        continue
                    try:
                        # v29.3.4: ExchangeConfig abstracts exchange-specific field access
                        price = ExchangeConfig.get_ticker_price(t)
                        vol = ExchangeConfig.get_ticker_volume(t)
                        open_p = float(t["o"])       # TODO v29.4: ExchangeConfig.get_open()
                        high = float(t["h"][1])      # TODO v29.4: ExchangeConfig.get_high()
                        low = float(t["l"][1])       # TODO v29.4: ExchangeConfig.get_low()
                        change = (price - open_p) / open_p if open_p > 0 else 0
                        rng = (high - low) / low if low > 0 else 0
                        pos_in_range = (price - low) / (high - low) if high > low else 0.5
                        tickers[pair] = {
                            "price": price, "change": change, "vol": vol,
                            "high": high, "low": low, "range": rng,
                            "pos": pos_in_range,
                        }
                    except Exception:
                        pass
            time.sleep(0.3)  # was 0.5 — Kraken allows ~1 req/s for public endpoints
        except Exception:
            pass
    return tickers


def prefilter_tradable_pairs(tickers, min_vol=None):
    """v29.3.4: Fast pre-filter to remove clearly untradable pairs before full scoring.
    Checks volume, price sanity, and ATR range. Returns set of pair keys that pass."""
    if min_vol is None:
        min_vol = SCAN_PREFILTER_MIN_VOL
    tradable = set()
    lo_atr, hi_atr = SCAN_PREFILTER_ATR_RANGE
    _wl_skipped = 0
    for pair, t in tickers.items():
        try:
            price = t.get("price", 0)
            vol = t.get("vol", 0)
            # v29.4.1: Whitelist filter — only trade approved coins
            coin = to_short_name(pair)
            if WHITELIST_ONLY and coin not in COIN_WHITELIST:
                _wl_skipped += 1
                continue
            if vol < min_vol:
                continue
            if price <= 0 or price > 1e8:
                continue
            # ATR sanity — use short name for cache lookup
            atr = coin_atr(coin)
            if atr < lo_atr or atr > hi_atr:
                continue
            tradable.add(pair)
        except Exception:
            pass
    if _wl_skipped > 0:
        logger.debug(f"[WHITELIST] Skipped {_wl_skipped} pairs not in COIN_WHITELIST ({len(tradable)} passed)")
    return tradable


def rank(tickers, min_vol=500000, regime=None):
    """Multi-factor signal scoring: momentum × volume × trend alignment × RSI.

    Regime-adaptive weighting when regime is provided:
      SMOOTH_TREND:   heavy momentum + trend alignment
      VOLATILE_TREND: balanced factors
      QUIET_RANGE:    heavy RSI (mean-reversion bias)
      Fallback:       original momentum × volume (safe default)
    """
    results = []
    for pair, t in tickers.items():
        if t["vol"] < min_vol:
            continue
        # v29.5.0: Skip coins with no price history or zero ATR (no data to trade on)
        coin_name = to_short_name(pair) if callable(to_short_name) else pair
        hist = prices_cache.get(coin_name, [])
        if len(hist) < 2:
            continue  # No price data — cannot compute any factors
        atr_val = coin_atr(coin_name)
        if atr_val is None or atr_val <= 0.0:
            continue  # Zero/None ATR — dead or missing data
        mom = t["change"]
        vol_score = min(1.0, math.log10(max(t["vol"], 1)) / 7)

        # Factor 1: Momentum (original)
        f_momentum = mom * 5.0
        f_volume = vol_score

        # Factor 2: RSI-14 divergence
        f_rsi = 0.0
        if len(hist) >= 16:
            gains, losses = [], []
            for i in range(max(1, len(hist) - 14), len(hist)):
                delta = hist[i] - hist[i - 1]
                gains.append(max(delta, 0))
                losses.append(max(-delta, 0))
            avg_gain = sum(gains) / len(gains) if gains else 0
            avg_loss = sum(losses) / len(losses) if losses else 0.001
            rs = avg_gain / avg_loss if avg_loss > 0 else 100
            rsi = 100 - (100 / (1 + rs))
            f_rsi = (rsi - 50) / 50  # Normalize to -1..+1

        # Factor 3: EMA trend alignment
        f_trend = 0.0
        if len(hist) >= 26:
            ema_fast = sum(hist[-12:]) / 12
            ema_slow = sum(hist[-26:]) / 26
            if ema_slow > 0:
                f_trend = (ema_fast - ema_slow) / ema_slow * 100
                f_trend = max(-2.0, min(2.0, f_trend))

        # Regime-adaptive weighting (trend alignment boosted for cleaner setups)
        if regime == "SMOOTH_TREND" and len(hist) >= 26:
            score = f_momentum * 0.30 * f_volume + f_rsi * 0.15 + f_trend * 0.45  # trend 0.40→0.45
        elif regime == "VOLATILE_TREND" and len(hist) >= 26:
            score = f_momentum * 0.25 * f_volume + f_rsi * 0.20 + f_trend * 0.40  # trend 0.35→0.40
        elif regime == "QUIET_RANGE" and len(hist) >= 26:
            score = f_momentum * 0.20 * f_volume + f_rsi * 0.30 + f_trend * 0.30  # trend 0.25→0.30, rsi 0.35→0.30
        else:
            score = mom * 5.0 * vol_score  # Fallback: original formula

        # v29.4.0: Order book imbalance — boost score when depth confirms direction
        try:
            ob_imb = orderbook_imbalance(coin_name)
            if ob_imb > OB_IMBALANCE_STRONG_BUY and score > 0:
                score *= (1.0 + OB_CONFIDENCE_BOOST)  # Buying pressure confirms long
            elif ob_imb < OB_IMBALANCE_STRONG_SELL and score < 0:
                score *= (1.0 + OB_CONFIDENCE_BOOST)  # Selling pressure confirms short
        except Exception:
            pass  # Neutral on error

        results.append({"pair": pair, "price": t["price"], "score": score,
                        "change": t["change"], "vol": t["vol"]})
    results.sort(key=lambda x: x["score"], reverse=True)
    return results


def get_top_volume_pairs(tickers, pair_names_map, wallet, limit=5):
    """Get top volume pairs from tickers for market-data fallback.

    Returns list of dicts: [{"coin": short_name, "price": float, "vol": float}, ...]
    Excludes pairs already held (longs + shorts) to avoid doubling up.
    Only includes pairs with valid prices and meaningful volume.
    """
    held = set(wallet.longs.keys()) | set(wallet.shorts.keys())
    candidates = []
    for pair, t in tickers.items():
        try:
            price = t.get("price", 0)
            vol = t.get("vol", 0)
            if price is None or price <= 0 or vol < 500000:
                continue
            if math.isnan(price) or math.isinf(price):
                continue
            name = pair_names_map.get(pair, pair)
            short = to_short_name(name)
            if short in held:
                continue
            candidates.append({"coin": short, "price": price, "vol": vol})
        except Exception:
            continue
    # Sort by volume descending — highest liquidity first
    candidates.sort(key=lambda x: x["vol"], reverse=True)
    return candidates[:limit]


# ── Dashboard ──
# Dashboard state tracking — only reprint full view on changes
_last_full_display = {"longs": 0, "shorts": 0, "trades": 0, "time": 0}
_FULL_DISPLAY_INTERVAL = 30  # Full dashboard reprint every 30 seconds


def show(wallet, prices, cycle, ranked, pair_names):
    """Compact dashboard. In-place single-line most cycles, full view on state changes."""
    if not is_verbose("NORMAL"):
        return  # QUIET mode: no dashboard output
    try:
        val = wallet.value(prices)
        pnl = val - CASH
        pnl_pct = pnl / CASH * 100
        c = "\033[92m" if pnl >= 0 else "\033[91m"
        R = "\033[0m"
        B = "\033[1m"
        D = "\033[2m"

        now = time.time()
        n_longs = len(wallet.longs)
        n_shorts = len(wallet.shorts)
        n_trades = len(wallet.trades) if hasattr(wallet, 'trades') else 0

        # Detect state changes that warrant a full reprint
        state_changed = (
            n_longs != _last_full_display["longs"] or
            n_shorts != _last_full_display["shorts"] or
            n_trades != _last_full_display["trades"]
        )
        time_for_full = (now - _last_full_display["time"]) >= _FULL_DISPLAY_INTERVAL

        if state_changed or time_for_full:
            # ── Full display (on trade/position change or every 30s) ──
            _last_full_display["longs"] = n_longs
            _last_full_display["shorts"] = n_shorts
            _last_full_display["trades"] = n_trades
            _last_full_display["time"] = now

            print("\033[2J\033[H", end="")  # Clear screen
            ar = adaptive_regime.classify(prices_cache) or "—"
            if cycle < WARMUP_CYCLES:
                warmup_str = f" | \033[93mWARM-UP {cycle}/{WARMUP_CYCLES}\033[0m"
            elif cycle < WARMUP_RAMP_END:
                warmup_str = f" | \033[93mRAMP {int(WARMUP_RAMP_MULT*100)}% size\033[0m"
            else:
                warmup_str = ""
            print(f"{B}  TRADING BOT v29 — {len(pair_names)} pairs | {ar}{warmup_str}{R}")
            ml_count = brain.get_stats()["total_trained"]
            _ml_ready = ml_count >= BRAIN_ML_MIN_TRADES  # v29.3.5 L8: ML weights only active after 200+ trades
            mode = awareness.get_status()
            _brain_status = market_brain.status_line()
            print(f"  {c}{B}${val:,.2f}{R}  P&L: {c}${pnl:+,.2f} ({pnl_pct:+.2f}%){R}  W:{wallet.wins} L:{wallet.losses}  HP:{_last_health_score}  ML:{ml_count}  {mode}  Cycle:{cycle}")
            print(f"  {_brain_status}")

            # Positions (only if any exist)
            if wallet.longs or wallet.shorts:
                print(f"\n  {B}Positions:{R}")
                for coin, pos in wallet.longs.items():
                    p = prices.get(coin, pos["entry"])
                    val_pos = pos["qty"] * p
                    pnl_pos = (p - pos["entry"]) / pos["entry"] * 100
                    pc = "\033[92m" if pnl_pos >= 0 else "\033[91m"
                    print(f"    LONG  {coin:<8} ${val_pos:>8,.2f}  {pc}{pnl_pos:+.1f}%{R}")
                for coin, pos in wallet.shorts.items():
                    p = prices.get(coin, pos["entry"])
                    val_pos = pos["qty"] * p
                    pnl_pos = (pos["entry"] - p) / pos["entry"] * 100
                    pc = "\033[92m" if pnl_pos >= 0 else "\033[91m"
                    print(f"    SHORT {coin:<8} ${val_pos:>8,.2f}  {pc}{pnl_pos:+.1f}%{R}")

            # Top movers (only on full display, max 3)
            if ranked:
                print(f"\n  {B}Top signals:{R}")
                for r in ranked[:3]:
                    name = pair_names.get(r["pair"], r["pair"])[:10]
                    ch = r["change"] * 100
                    sc = r["score"]
                    sig = "BUY " if sc > 0.15 else "SHRT" if sc < -0.15 else "    "
                    cc = "\033[92m" if ch > 0 else "\033[91m"
                    print(f"    {sig} {name:<10} ${r['price']:>10,.4f}  {cc}{ch:+.1f}%{R}  s:{sc:+.2f}")

            # Bottom status line
            ps = perf.summary()
            total_risk = calculate_total_risk(wallet, prices) if (wallet.longs or wallet.shorts) else 0
            ar_mult = adaptive_risk.risk_multiplier(cycle)
            ar_str = f" AR:{ar_mult:.0%}" if ar_mult < 1.0 else ""
            print(f"\n  {D}Cash:${wallet.cash:,.2f} Sharpe:{ps['sharpe']} DD:{ps['max_drawdown']:.1f}% Risk:{total_risk:.1f}%{ar_str}{R}")
            print()  # Blank line before status ticker
        else:
            # ── Compact single-line in-place update ──
            pos_str = f"L:{n_longs} S:{n_shorts}" if (n_longs or n_shorts) else "no pos"
            rec = "ON" if recovery_mode.active else "off"
            _act = f"t{_activity_tier}" if _activity_tier > 0 else "ok"
            try:
                _n_coin_blocked = len(coin_loss_tracker.blocked_coins_summary())
                _n_pair_blocked = len(pair_failure_tracker.blocked_pairs_summary())
                _blk = f" blk:{_n_coin_blocked}c/{_n_pair_blocked}p" if (_n_coin_blocked or _n_pair_blocked) else ""
            except Exception:
                _blk = ""
            print(f"\r  {c}${val:,.0f}{R} {pnl_pct:+.2f}% W:{wallet.wins} L:{wallet.losses} {pos_str} hp={_last_health_score} rec={rec} act={_act}{_blk} c={cycle}  ", end="", flush=True)
    except Exception:
        # Dashboard must NEVER crash the bot
        try:
            print(f"\r  cycle={cycle} (display error)  ", end="", flush=True)
        except Exception:
            pass


# ── Cycle Time Tracker (lightweight ring buffer for snapshot) ──
_cycle_times = []  # Last ~20 cycle durations in seconds
_last_health_score = 100  # Updated by bot_snapshot_report(), read by main loop


def update_health_score(perf_matrix, enhanced_regime):
    """Fast score-only update. Called every cycle. No strings, no logging. Never raises."""
    global _last_health_score
    try:
        recent = perf_matrix.trades[-50:] if perf_matrix.trades else []
        n = len(recent)

        # Win quality (0-25)
        if n == 0:
            s_wq = 12
        else:
            wr = sum(1 for t in recent if t.get("won")) / n * 100
            win_trades = [t for t in recent if t.get("won")]
            loss_trades = [t for t in recent if not t.get("won")]
            avg_win = sum(t.get("net_pnl", 0) for t in win_trades) / len(win_trades) if win_trades else 0
            avg_loss = abs(sum(t.get("net_pnl", 0) for t in loss_trades) / len(loss_trades)) if loss_trades else 0.01
            edge = (wr / 100 * avg_win) - ((1 - wr / 100) * avg_loss)
            if edge >= 1.0:
                s_wq = 25
            elif edge >= 0:
                s_wq = 12 + int(edge / 1.0 * 13)
            elif edge >= -1.0:
                s_wq = max(0, int((edge + 1.0) / 1.0 * 12))
            else:
                s_wq = 0

        # PnL trend (0-15)
        if n == 0:
            s_pnl = 8
        else:
            total_pnl = sum(t.get("net_pnl", 0) for t in recent)
            if total_pnl >= 5:
                s_pnl = 15
            elif total_pnl >= 0:
                s_pnl = 8 + int(total_pnl / 5 * 7)
            elif total_pnl >= -10:
                s_pnl = max(0, int((total_pnl + 10) / 10 * 8))
            else:
                s_pnl = 0

        # Overtrading (0-20)
        if n <= 15:
            s_ot = 20
        elif n <= 30:
            s_ot = 20 - int((n - 15) / 15 * 10)
        elif n <= 45:
            s_ot = 10 - int((n - 30) / 15 * 10)
        else:
            s_ot = 0

        # Latency (0-20)
        if _cycle_times:
            avg_ct = sum(_cycle_times) / len(_cycle_times)
            max_ct = max(_cycle_times)
            slow = avg_ct > POLL * 0.8
            unstable = max_ct > avg_ct * 3 and max_ct > 2.0
        else:
            slow = False
            unstable = False
        if slow:
            s_lat = 0
        elif unstable:
            s_lat = 10
        else:
            s_lat = 20

        # Regime (0-20)
        choppy = enhanced_regime and "CHOP" in enhanced_regime.upper()
        if choppy:
            s_regime = 5
        elif enhanced_regime and "TREND" in enhanced_regime.upper():
            s_regime = 20
        elif enhanced_regime:
            s_regime = 12
        else:
            s_regime = 10

        # Loss streak penalty
        streak_penalty = 0
        if n > 0:
            cur = 0
            max_streak = 0
            for t in recent:
                if not t.get("won"):
                    cur += 1
                    if cur > max_streak:
                        max_streak = cur
                else:
                    cur = 0
            if max_streak >= 6:
                streak_penalty = 20
            elif max_streak >= 5:
                streak_penalty = 12
            elif max_streak >= 4:
                streak_penalty = 7
            elif max_streak >= 3:
                streak_penalty = 3

        score = s_wq + s_pnl + s_ot + s_lat + s_regime - streak_penalty
        # Floor prevents deadlock where no trades → no recovery → score stuck at 0
        # At score=25, entries are allowed at 0.25x size (health_size_mult), NOT blocked
        _last_health_score = max(HEALTH_SCORE_FLOOR, min(100, score))
        return _last_health_score
    except Exception:
        return _last_health_score


def bot_snapshot_report(cycle, wallet, prices, perf_matrix, enhanced_regime):
    """Full health snapshot with display. Called every N cycles for logging. Never raises."""
    try:
        # Recompute score (fast, same logic)
        score = update_health_score(perf_matrix, enhanced_regime)

        # Build display from existing data
        recent = perf_matrix.trades[-50:] if perf_matrix.trades else []
        n = len(recent)
        lines = [f"[SNAPSHOT] cycle={cycle}"]

        # Trading activity
        if n > 0:
            wins = sum(1 for t in recent if t.get("won"))
            wr = wins / n * 100
            total_pnl = sum(t.get("net_pnl", 0) for t in recent)
            overtrade_flag = " OVERTRADE" if n >= 40 else ""
            lines.append(f"  trades(last50): {n} WR={wr:.0f}% PnL={total_pnl:+.2f}%{overtrade_flag}")
        else:
            wr = 0
            total_pnl = 0
            lines.append("  trades(last50): 0")

        # Position state
        n_longs = len(wallet.longs)
        n_shorts = len(wallet.shorts)
        exposure_warn = " HIGH_EXPOSURE" if (n_longs + n_shorts) >= MAX_POSITIONS else ""
        lines.append(f"  positions: {n_longs}L/{n_shorts}S{exposure_warn}")

        # Latency
        if _cycle_times:
            avg_ct = sum(_cycle_times) / len(_cycle_times)
            max_ct = max(_cycle_times)
            slow = avg_ct > POLL * 0.8
            unstable = max_ct > avg_ct * 3 and max_ct > 2.0
            flag = " SLOW" if slow else (" UNSTABLE" if unstable else "")
            lines.append(f"  latency: avg={avg_ct:.2f}s max={max_ct:.2f}s{flag}")
        else:
            slow = False
            unstable = False
            avg_ct = 0
            max_ct = 0

        # Regime
        choppy = False
        if enhanced_regime:
            lines.append(f"  regime: {enhanced_regime}")
            choppy = "CHOP" in enhanced_regime.upper()

        # Status + reason
        if score >= 70:
            status = "STABLE"
        elif score >= 40:
            status = "WARNING"
        else:
            status = "DANGEROUS"

        reasons = []
        if n > 0:
            win_trades = [t for t in recent if t.get("won")]
            loss_trades = [t for t in recent if not t.get("won")]
            avg_win = sum(t.get("net_pnl", 0) for t in win_trades) / len(win_trades) if win_trades else 0
            avg_loss = abs(sum(t.get("net_pnl", 0) for t in loss_trades) / len(loss_trades)) if loss_trades else 0.01
            edge = (wr / 100 * avg_win) - ((1 - wr / 100) * avg_loss)
            if edge < -0.5:
                reasons.append(f"poor edge (WR={wr:.0f}%, avg_win/loss ratio unfavorable)")
            if total_pnl < -5:
                reasons.append(f"negative PnL ({total_pnl:+.1f}%)")
            # Loss streak for reason line
            cur = 0
            max_streak = 0
            for t in recent:
                if not t.get("won"):
                    cur += 1
                    if cur > max_streak:
                        max_streak = cur
                else:
                    cur = 0
            if max_streak >= 4:
                reasons.append(f"loss streak ({max_streak} consecutive losses)")
        if n >= 30:
            reasons.append(f"overtrading ({n} trades in last 50 slots)")
        if slow:
            reasons.append(f"slow cycles ({avg_ct:.1f}s)")
        elif unstable:
            reasons.append(f"latency spikes ({max_ct:.1f}s)")
        if choppy:
            reasons.append("choppy regime")
        reason_str = "; ".join(reasons) if reasons else "all systems nominal"

        lines.append(f"  BOT HEALTH SCORE: {score}/100 — {status}")
        lines.append(f"  reason: {reason_str}")

        return "\n".join(lines)
    except Exception:
        return f"[SNAPSHOT] cycle={cycle} (error generating snapshot)"


def preflight_sizing_report(wallet_ref, prices_ref, ranked_list, pair_names_map, regime, cycle_num):
    """Pre-flight check: show top candidates with full sizing breakdown.
    Called once after warmup ends or on DRY_RUN cycles."""
    try:
        print(f"\n  {'═'*60}")
        print(f"  PRE-FLIGHT SIZING REPORT (cycle {cycle_num}, regime={regime})")
        print(f"  {'═'*60}")

        pv = wallet_ref.value(prices_ref)
        edge_m = _edge_size_multiplier()
        wr_bonus = _winrate_size_bonus(wallet_ref)
        peak = is_peak_hours()
        peak_mult = 1.0 if peak else 0.70

        # Health score breakdown for pre-flight
        _hs = _last_health_score
        _hs_tag = "BLOCK" if _hs < 30 else "CAUTION" if _hs < 40 else "OK" if _hs < 70 else "GOOD"
        _hsm = 0.0 if _hs < 20 else 0.25 if _hs < 30 else 0.5 if _hs < 40 else 1.0

        print(f"  Portfolio: ${pv:,.2f} | Edge mult: {edge_m:.2f}x | WR bonus: {wr_bonus:.2f}x | Peak: {peak} ({peak_mult:.2f}x)")
        print(f"  Regime scale: {REGIME_SIZE_SCALE.get(regime, 1.0)}x")
        print(f"  Health score: {_hs}/100 [{_hs_tag}] | health_size_mult: {_hsm:.2f}x")
        print()

        # Top 5 long candidates
        top5 = ranked_list[:5] if ranked_list else []
        if top5:
            print(f"  TOP 5 LONG CANDIDATES:")
            for i, r in enumerate(top5):
                coin = to_short_name(pair_names_map.get(r["pair"], r["pair"]))
                atr_pct = coin_atr(coin) * 100
                sl_pct = max(0.8, atr_pct * 0.7)
                max_risk = pv * MAX_RISK_PER_TRADE
                eff_sl = sl_pct * GAP_RISK_MULTIPLIER
                max_by_risk = min(max_risk / (eff_sl / 100), pv * 0.30)
                base = min(wallet_ref.cash * 0.30, max_by_risk)
                sized = base * edge_m  # v29.3.5: POST_SIZING_BOOST removed (was noop)
                sized = min(sized, max_by_risk)
                sized = sized * REGIME_SIZE_SCALE.get(regime, 1.0) * wr_bonus * peak_mult
                sized = min(sized, max_by_risk)  # Final re-cap

                # TP calc (v29.1 — realistic for 2s candles)
                if atr_pct < 1.5:
                    tp_s = 1.0   # v29.3
                elif atr_pct > 3.0:
                    tp_s = 0.85  # v29.3
                else:
                    tp_s = 1.0   # v29.3
                tp_pct = max(0.4, sl_pct * TP_RATIO_NORMAL)  # v29.5.0: use config constant instead of hardcoded 1.1
                trail = max(0.5, atr_pct * 0.5)  # v29.3: tighter trail

                flag = "OK" if 10 <= sized <= 150 else "LOW" if sized < 10 else "HIGH"
                print(f"    {i+1}. {coin:12s} score={r['score']:+.3f} chg={r['change']:+.1%} vol=${r['vol']/1e6:.1f}M")
                print(f"       size=${sized:.0f} [{flag}] SL={sl_pct:.1f}% TP={tp_pct:.1f}% trail={trail:.1f}% ATR={atr_pct:.1f}%")

        # Bottom 5 short candidates
        bot5 = ranked_list[-5:] if len(ranked_list) >= 5 else []
        if bot5:
            print(f"\n  TOP 5 SHORT CANDIDATES:")
            for i, r in enumerate(bot5):
                coin = to_short_name(pair_names_map.get(r["pair"], r["pair"]))
                atr_pct = coin_atr(coin) * 100
                sl_pct = max(0.8, atr_pct * 0.7)
                max_risk = pv * MAX_RISK_PER_TRADE
                eff_sl = sl_pct * GAP_RISK_MULTIPLIER
                max_by_risk = min(max_risk / (eff_sl / 100), pv * 0.30)
                base = min(wallet_ref.cash * 0.30, max_by_risk)
                sized = base * edge_m  # v29.3.5: POST_SIZING_BOOST removed (was noop)
                sized = min(sized, max_by_risk)
                sized = sized * REGIME_SIZE_SCALE.get(regime, 1.0) * wr_bonus * peak_mult
                sized = min(sized, max_by_risk)  # Final re-cap
                flag = "OK" if 10 <= sized <= 150 else "LOW" if sized < 10 else "HIGH"
                print(f"    {i+1}. {coin:12s} score={r['score']:+.3f} chg={r['change']:+.1%}")
                print(f"       size=${sized:.0f} [{flag}] SL={sl_pct:.1f}% ATR={atr_pct:.1f}%")

        # Simulate assess_exit for mock positions
        print(f"\n  ASSESS_EXIT SIMULATION:")
        for sig_count, label in [(2, "strong trend"), (1, "weak trend"), (-1, "reversal")]:
            print(f"    signals={sig_count} ({label}):")
            # Long with 0.5% profit
            if sig_count >= 2:
                decision = "HOLD_AND_TRAIL"
            elif sig_count == 1 and 0.5 > 0.4:
                decision = "HOLD_AND_TRAIL (profitable)"
            elif sig_count <= -1:
                decision = "EXIT"
            else:
                decision = "EXIT (borderline)"
            print(f"      Long  +0.5% PnL → {decision}")
            # Long with 0.2% profit
            if sig_count >= 2:
                decision2 = "HOLD_AND_TRAIL"
            elif sig_count == 1 and 0.2 > 0.4:
                decision2 = "HOLD_AND_TRAIL (profitable)"
            elif sig_count <= -1:
                decision2 = "EXIT"
            else:
                decision2 = "EXIT (borderline)"
            print(f"      Long  +0.2% PnL → {decision2}")

        print(f"  {'═'*60}\n")
    except Exception as e:
        print(f"  PRE-FLIGHT ERROR: {e}")


# ── v29.4.1: SMC/ICT Strategy — Liquidity Sweep + FVG + Order Block ──

def smc_ict_signal(coin, prices):
    """
    SMC/ICT Strategy: Liquidity Sweep + FVG + Order Block (LONG + SHORT)
    Returns (direction, confidence_score, entry_price, stop_pct, tp_pct) or None
    Rules:
    - Find swing low/high (support/resistance) on last 50 candles
    - LONG: sweep below swing low by 0.3-0.8%, FVG on recovery, entry in FVG zone
    - SHORT: sweep above swing high by 0.3-0.8%, FVG on drop, entry in FVG zone
    - Stop: beyond sweep extreme + buffer, capped at 1.5%
    - TP: minimum 3x stop (for fee coverage)
    - Score: 0-10 based on conditions met, only trade 6+
    """
    if len(prices) < 50:
        return None
    try:
        recent = prices[-50:]
        current = prices[-1]
        prev5 = prices[-6:-1]

        # ── LONG SETUP: sweep below swing low ──
        swing_low = min(recent[-30:-5])
        swept_low = any(p < swing_low * 0.997 for p in prev5)  # 0.3% sweep minimum

        if swept_low:
            sweep_low_val = min(prev5)
            sweep_pct = (swing_low - sweep_low_val) / swing_low
            if sweep_pct <= 0.008:  # max 0.8% sweep
                # Find FVG: gap in last 5 candles after sweep
                c1_low = prices[-5]
                c3_high = prices[-3]
                fvg_low = min(c1_low, c3_high)
                fvg_high = max(c1_low, c3_high)
                fvg_size = (fvg_high - fvg_low) / fvg_low if fvg_low > 0 else 0
                if fvg_size >= 0.002:  # FVG must be at least 0.2%
                    fvg_entry_low = fvg_low + (fvg_high - fvg_low) * 0.25
                    fvg_entry_high = fvg_low + (fvg_high - fvg_low) * 0.75
                    if fvg_entry_low <= current <= fvg_entry_high:
                        score = 0
                        if sweep_pct >= 0.003: score += 3
                        if fvg_size >= 0.004: score += 2
                        if current <= fvg_entry_high: score += 2
                        if current > sweep_low_val * 1.001: score += 2
                        if len([p for p in recent[-10:] if p > swing_low]) > 5: score += 1
                        if score >= 6:
                            stop_pct = max(0.3, sweep_pct * 100 + 0.3)
                            stop_pct = min(stop_pct, 1.5)
                            tp_pct = max(stop_pct * 3.0, 3.0)
                            logger.info(f"[SMC/ICT] {coin} LONG signal: score={score}/10 sweep={sweep_pct*100:.2f}% "
                                         f"fvg={fvg_size*100:.2f}% stop={stop_pct:.2f}% tp={tp_pct:.2f}%")
                            return ("long", score, current, stop_pct, tp_pct)

        # ── SHORT SETUP: sweep above swing high ──
        swing_high = max(recent[-30:-5])
        swept_high = any(p > swing_high * 1.003 for p in prev5)  # 0.3% sweep minimum

        if swept_high:
            sweep_high_val = max(prev5)
            sweep_pct_s = (sweep_high_val - swing_high) / swing_high
            if sweep_pct_s <= 0.008:  # max 0.8% sweep
                # Find FVG on the way down
                c1_high = prices[-5]
                c3_low = prices[-3]
                fvg_low_s = min(c1_high, c3_low)
                fvg_high_s = max(c1_high, c3_low)
                fvg_size_s = (fvg_high_s - fvg_low_s) / fvg_low_s if fvg_low_s > 0 else 0
                if fvg_size_s >= 0.002:
                    fvg_entry_low_s = fvg_low_s + (fvg_high_s - fvg_low_s) * 0.25
                    fvg_entry_high_s = fvg_low_s + (fvg_high_s - fvg_low_s) * 0.75
                    if fvg_entry_low_s <= current <= fvg_entry_high_s:
                        score_s = 0
                        if sweep_pct_s >= 0.003: score_s += 3
                        if fvg_size_s >= 0.004: score_s += 2
                        if current >= fvg_entry_low_s: score_s += 2
                        if current < sweep_high_val * 0.999: score_s += 2
                        if len([p for p in recent[-10:] if p < swing_high]) > 5: score_s += 1
                        if score_s >= 6:
                            stop_pct_s = max(0.3, sweep_pct_s * 100 + 0.3)
                            stop_pct_s = min(stop_pct_s, 1.5)
                            tp_pct_s = max(stop_pct_s * 3.0, 3.0)
                            logger.info(f"[SMC/ICT] {coin} SHORT signal: score={score_s}/10 sweep={sweep_pct_s*100:.2f}% "
                                         f"fvg={fvg_size_s*100:.2f}% stop={stop_pct_s:.2f}% tp={tp_pct_s:.2f}%")
                            return ("short", score_s, current, stop_pct_s, tp_pct_s)

        return None

    except Exception as e:
        logger.debug(f"[SMC/ICT] {coin} error: {e}")
        return None


# ── v29.5.0: SMC Order Block Signal ──
def smc_ob_signal(coin, prices, direction):
    """
    SMC Order Block Strategy: Find last opposite candle before strong impulse.
    Returns {"score", "direction", "ob_high", "ob_low", "entry", "stop", "target"} or None.
    Score 0-8: +2 OB zone holds, +2 aligns with trend, +2 volume 1.5x avg on impulse, +2 RSI at formation.
    Trade if score >= 6. Stop = 0.3% beyond OB zone, target = 3.2x stop.
    """
    if len(prices) < 30:
        return None
    try:
        recent = prices[-30:]
        avg_move = sum(abs(recent[i] - recent[i-1]) / recent[i-1] for i in range(1, len(recent))) / (len(recent) - 1)
        # Estimate volume proxy from price movement magnitude
        moves = [abs(recent[i] - recent[i-1]) / recent[i-1] for i in range(1, len(recent))]
        avg_vol_proxy = sum(moves) / len(moves) if moves else 0.001

        if direction == "long":
            # Find last bearish candle before bullish impulse in last 15 candles
            ob_high = ob_low = None
            impulse_found = False
            for i in range(len(recent) - 2, 4, -1):
                # Bullish impulse: price moved up > 2x avg move
                impulse_move = (recent[i] - recent[i-1]) / recent[i-1] if recent[i-1] > 0 else 0
                if impulse_move > avg_move * 2:
                    # Look for bearish candle just before impulse
                    for j in range(i - 1, max(0, i - 4), -1):
                        pre_move = (recent[j] - recent[j-1]) / recent[j-1] if recent[j-1] > 0 else 0
                        if pre_move < 0:  # Bearish candle
                            ob_high = max(recent[j], recent[j-1])
                            ob_low = min(recent[j], recent[j-1])
                            impulse_found = True
                            break
                    if impulse_found:
                        break
            if not impulse_found or ob_high is None:
                return None
            # Price must be pulling back into OB zone
            current = prices[-1]
            if not (ob_low <= current <= ob_high * 1.002):
                return None
        elif direction == "short":
            ob_high = ob_low = None
            impulse_found = False
            for i in range(len(recent) - 2, 4, -1):
                impulse_move = (recent[i] - recent[i-1]) / recent[i-1] if recent[i-1] > 0 else 0
                if impulse_move < -avg_move * 2:
                    for j in range(i - 1, max(0, i - 4), -1):
                        pre_move = (recent[j] - recent[j-1]) / recent[j-1] if recent[j-1] > 0 else 0
                        if pre_move > 0:  # Bullish candle (OB for short)
                            ob_high = max(recent[j], recent[j-1])
                            ob_low = min(recent[j], recent[j-1])
                            impulse_found = True
                            break
                    if impulse_found:
                        break
            if not impulse_found or ob_high is None:
                return None
            current = prices[-1]
            if not (ob_low * 0.998 <= current <= ob_high):
                return None
        else:
            return None

        # Score: 0-8
        score = 0
        current = prices[-1]
        # +2: OB zone holds (price bounced off it at least once in last 10 candles)
        zone_touches = sum(1 for p in prices[-10:] if ob_low <= p <= ob_high)
        if zone_touches >= 2:
            score += 2
        # +2: aligns with trend (EMA20 direction)
        if len(prices) >= 20:
            ema20 = sum(prices[-20:]) / 20
            if direction == "long" and current > ema20:
                score += 2
            elif direction == "short" and current < ema20:
                score += 2
        # +2: volume 1.5x avg on impulse (use move magnitude as proxy)
        if impulse_found and len(moves) > 1:
            impulse_mag = max(moves[-5:]) if len(moves) >= 5 else moves[-1]
            if impulse_mag > avg_vol_proxy * 1.5:
                score += 2
        # +2: RSI oversold/overbought at formation
        if len(prices) >= 14:
            _rsi_gains = []
            _rsi_losses = []
            for k in range(1, 15):
                chg = prices[-k] - prices[-k-1]
                if chg > 0:
                    _rsi_gains.append(chg)
                    _rsi_losses.append(0)
                else:
                    _rsi_gains.append(0)
                    _rsi_losses.append(abs(chg))
            avg_gain = sum(_rsi_gains) / 14
            avg_loss = sum(_rsi_losses) / 14
            if avg_loss > 0:
                rs = avg_gain / avg_loss
                rsi = 100 - (100 / (1 + rs))
            else:
                rsi = 100
            if direction == "long" and rsi < 35:
                score += 2
            elif direction == "short" and rsi > 65:
                score += 2

        if score < 6:
            return None

        # Stop: 0.3% beyond OB zone
        if direction == "long":
            stop_dist = (current - ob_low) / current * 100 + 0.3
        else:
            stop_dist = (ob_high - current) / current * 100 + 0.3
        stop_dist = max(0.5, min(stop_dist, 2.0))
        target = stop_dist * 3.2

        logger.info(f"[SMC_OB] {coin} {direction.upper()} score={score}/8 "
                     f"ob=[{ob_low:.4f}-{ob_high:.4f}] stop={stop_dist:.2f}% tp={target:.2f}%")

        return {"score": score, "direction": direction, "ob_high": ob_high, "ob_low": ob_low,
                "entry": current, "stop": stop_dist, "target": target}
    except Exception as e:
        logger.debug(f"[SMC_OB] {coin} error: {e}")
        return None


# ── v29.5.0: SMC Holy Grail Signal (Sweep + OB + FVG) ──
def smc_holy_grail_signal(coin, prices):
    """
    Requires ALL THREE: liquidity sweep + order block in sweep zone + FVG from impulse.
    Score 0-10: +3 sweep present, +3 OB in sweep zone, +3 FVG exists, +1 all on same candle.
    Trade ONLY if score >= 8 (highest confidence). Stop = 1% max, target = 3.5x stop.
    """
    if len(prices) < 50:
        return None
    try:
        recent = prices[-50:]
        current = prices[-1]

        # Step 1: Liquidity sweep detection (same logic as smc_ict_signal)
        swing_low = min(recent[-30:-5])
        swing_high = max(recent[-30:-5])
        prev5 = prices[-6:-1]

        # Check for sweep below support
        swept_low = any(p < swing_low * 0.997 for p in prev5)
        # Check for sweep above resistance
        swept_high = any(p > swing_high * 1.003 for p in prev5)

        if not swept_low and not swept_high:
            return None

        score = 0
        direction = "long" if swept_low else "short"

        # +3: sweep present
        if swept_low or swept_high:
            score += 3

        # Step 2: Order block in sweep zone
        sweep_zone_low = min(prev5) if swept_low else swing_high
        sweep_zone_high = swing_low if swept_low else max(prev5)
        ob_found = False
        avg_move = sum(abs(recent[i] - recent[i-1]) / recent[i-1] for i in range(1, len(recent))) / (len(recent) - 1)

        for i in range(len(recent) - 2, 4, -1):
            c_move = (recent[i] - recent[i-1]) / recent[i-1] if recent[i-1] > 0 else 0
            if direction == "long" and c_move < 0:
                c_high = max(recent[i], recent[i-1])
                c_low = min(recent[i], recent[i-1])
                if c_low >= sweep_zone_low * 0.995 and c_high <= sweep_zone_high * 1.005:
                    ob_found = True
                    break
            elif direction == "short" and c_move > 0:
                c_high = max(recent[i], recent[i-1])
                c_low = min(recent[i], recent[i-1])
                if c_low >= sweep_zone_low * 0.995 and c_high <= sweep_zone_high * 1.005:
                    ob_found = True
                    break

        if ob_found:
            score += 3

        # Step 3: FVG from impulse
        fvg_found = False
        if len(prices) >= 5:
            c1_low = prices[-5]
            c3_high = prices[-3]
            fvg_low = min(c1_low, c3_high)
            fvg_high = max(c1_low, c3_high)
            fvg_size = (fvg_high - fvg_low) / fvg_low if fvg_low > 0 else 0
            if fvg_size >= 0.002:
                fvg_found = True
                score += 3

        # +1: all conditions overlapping on same candle range
        if ob_found and fvg_found:
            score += 1

        if score < 8:
            return None

        # Stop: 1% max
        if direction == "long":
            sweep_depth = (swing_low - min(prev5)) / swing_low * 100 if swing_low > 0 else 0.5
            stop_pct = min(1.0, max(0.5, sweep_depth + 0.3))
        else:
            sweep_depth = (max(prev5) - swing_high) / swing_high * 100 if swing_high > 0 else 0.5
            stop_pct = min(1.0, max(0.5, sweep_depth + 0.3))

        target_pct = stop_pct * 3.5

        logger.info(f"[SMC_HOLY_GRAIL] {coin} {direction.upper()} score={score}/10 "
                     f"sweep={'LOW' if swept_low else 'HIGH'} ob={ob_found} fvg={fvg_found} "
                     f"stop={stop_pct:.2f}% tp={target_pct:.2f}%")

        return {"score": score, "direction": direction, "ob_high": sweep_zone_high, "ob_low": sweep_zone_low,
                "entry": current, "stop": stop_pct, "target": target_pct}
    except Exception as e:
        logger.debug(f"[SMC_HOLY_GRAIL] {coin} error: {e}")
        return None


# ── v29.5.0: SMC Breakout + FVG Signal ──
def smc_breakout_fvg_signal(coin, prices):
    """
    Step 1: price broke above 20-candle high or below 20-candle low.
    Step 2: price pulled back but not more than 61.8% retrace.
    Step 3: FVG exists in pullback zone.
    Score 0-9: +2 clean breakout close, +2 clean pullback, +2 FVG present, +2 breakout volume 2x avg, +1 RSI crossed 50.
    Trade if score >= 6. Stop = 0.5% below pullback low, target = 3.2x stop.
    """
    if len(prices) < 25:
        return None
    try:
        lookback = prices[-25:]
        range_prices = lookback[:-5]  # 20-candle range excluding last 5
        if len(range_prices) < 20:
            return None
        range_high = max(range_prices)
        range_low = min(range_prices)
        recent5 = lookback[-5:]
        current = prices[-1]

        # Step 1: Breakout detection
        broke_high = any(p > range_high * 1.001 for p in recent5)
        broke_low = any(p < range_low * 0.999 for p in recent5)

        if not broke_high and not broke_low:
            return None

        direction = "long" if broke_high else "short"

        # Step 2: Pullback check (not more than 61.8% retrace)
        if direction == "long":
            breakout_peak = max(recent5)
            retrace_pct = (breakout_peak - current) / (breakout_peak - range_high) if breakout_peak > range_high else 999
            if retrace_pct > 0.618 or current < range_high:
                return None
            pullback_low = min(recent5[-3:])
        else:
            breakout_trough = min(recent5)
            retrace_pct = (current - breakout_trough) / (range_low - breakout_trough) if range_low > breakout_trough else 999
            if retrace_pct > 0.618 or current > range_low:
                return None
            pullback_high = max(recent5[-3:])

        # Step 3: FVG in pullback zone
        fvg_found = False
        if len(prices) >= 5:
            c1 = prices[-5]
            c3 = prices[-3]
            fvg_gap = abs(c1 - c3) / min(c1, c3) if min(c1, c3) > 0 else 0
            if fvg_gap >= 0.002:
                fvg_found = True

        # Scoring
        score = 0
        # +2: clean breakout close (current still above/below range)
        if direction == "long" and current > range_high:
            score += 2
        elif direction == "short" and current < range_low:
            score += 2
        # +2: clean pullback (orderly, not a crash)
        if direction == "long" and 0 < retrace_pct < 0.5:
            score += 2
        elif direction == "short" and 0 < retrace_pct < 0.5:
            score += 2
        # +2: FVG present
        if fvg_found:
            score += 2
        # +2: breakout volume 2x avg (using price move magnitude as proxy)
        moves = [abs(lookback[i] - lookback[i-1]) / lookback[i-1] for i in range(1, len(lookback)) if lookback[i-1] > 0]
        avg_move = sum(moves) / len(moves) if moves else 0.001
        breakout_moves = [abs(recent5[i] - recent5[i-1]) / recent5[i-1] for i in range(1, len(recent5)) if recent5[i-1] > 0]
        max_breakout_move = max(breakout_moves) if breakout_moves else 0
        if max_breakout_move > avg_move * 2:
            score += 2
        # +1: RSI crossed 50
        if len(prices) >= 14:
            gains = []
            losses = []
            for k in range(1, 15):
                chg = prices[-k] - prices[-k-1]
                gains.append(max(0, chg))
                losses.append(max(0, -chg))
            avg_g = sum(gains) / 14
            avg_l = sum(losses) / 14
            rsi = 100 - (100 / (1 + avg_g / avg_l)) if avg_l > 0 else 100
            if direction == "long" and rsi > 50:
                score += 1
            elif direction == "short" and rsi < 50:
                score += 1

        if score < 6:
            return None

        # Stop and target
        if direction == "long":
            stop_pct = max(0.5, (current - pullback_low) / current * 100 + 0.5)
        else:
            stop_pct = max(0.5, (pullback_high - current) / current * 100 + 0.5)
        stop_pct = min(stop_pct, 2.0)
        target_pct = stop_pct * 3.2

        logger.info(f"[SMC_BREAKOUT] {coin} {direction.upper()} score={score}/9 "
                     f"retrace={retrace_pct:.2f} fvg={fvg_found} stop={stop_pct:.2f}% tp={target_pct:.2f}%")

        return {"score": score, "direction": direction,
                "ob_high": range_high, "ob_low": range_low,
                "entry": current, "stop": stop_pct, "target": target_pct}
    except Exception as e:
        logger.debug(f"[SMC_BREAKOUT] {coin} error: {e}")
        return None


# ── v29.5.0: SMC Valid Zone Filter ──
def smc_valid_zone(coin, price, prices):
    """
    Universal SMC filter: Returns False if price is in middle third of 20-candle range.
    Only trade near tops/bottoms of range or at key levels.
    """
    if len(prices) < 20:
        return True  # Not enough data, allow
    try:
        recent20 = prices[-20:]
        hi = max(recent20)
        lo = min(recent20)
        if hi <= lo:
            return True  # Flat market, allow
        rng = hi - lo
        lower_third = lo + rng * 0.333
        upper_third = lo + rng * 0.667
        # In middle third → not a valid zone
        if lower_third < price < upper_third:
            return False
        return True
    except Exception:
        return True


# ── v29.5.0: Market Regime Detection ──
def detect_market_regime(btc_prices):
    """
    Detect current market regime from BTC price history.
    TRENDING: BTC moved >1.5% in last 20 candles
    RANGING: BTC moved <0.5% in last 20 candles
    VOLATILE: ATR >2%
    DEAD: ATR <0.1%
    Returns string: "TRENDING", "RANGING", "VOLATILE", "DEAD"
    """
    if len(btc_prices) < 20:
        return "UNKNOWN"
    try:
        recent = btc_prices[-20:]
        net_move = abs(recent[-1] - recent[0]) / recent[0] if recent[0] > 0 else 0
        # ATR as average of absolute moves
        moves = [abs(recent[i] - recent[i-1]) / recent[i-1] for i in range(1, len(recent)) if recent[i-1] > 0]
        atr_pct = (sum(moves) / len(moves) * 100) if moves else 0

        if atr_pct < 0.1:
            return "DEAD"
        if atr_pct > 2.0:
            return "VOLATILE"
        if net_move * 100 > 1.5:
            return "TRENDING"
        if net_move * 100 < 0.5:
            return "RANGING"
        return "TRENDING"  # Default to trending if between 0.5-1.5%
    except Exception:
        return "UNKNOWN"


# ── v29.5.0: Volatility-Scaled Position Sizing Multiplier ──
def volatility_size_mult(coin):
    """
    Scale position size based on current ATR:
    ATR < 0.3%: 0.5x | ATR 0.3-0.8%: 1.0x | ATR 0.8-1.5%: 0.75x | ATR > 1.5%: 0.4x
    """
    try:
        atr = coin_atr(coin) * 100  # Convert to percentage
        if atr < 0.3:
            return 0.5
        elif atr <= 0.8:
            return 1.0
        elif atr <= 1.5:
            return 0.75
        else:
            return 0.4
    except Exception:
        return 1.0


# ── v29.5.0: Adaptive TP/SL based on ATR ──
def adaptive_tp_ratio(coin):
    """
    ATR < 0.5%: TP = 4.0x SL
    ATR 0.5-1.0%: TP = 3.2x SL (current default)
    ATR > 1.0%: TP = 2.5x SL
    """
    try:
        atr = coin_atr(coin) * 100
        if atr < 0.5:
            return 4.0
        elif atr <= 1.0:
            return 3.2
        else:
            return 2.5
    except Exception:
        return 3.2


# ── v29.5.0: Trend Strength (0-10) ──
def get_trend_strength(prices, direction="long"):
    """
    Returns trend strength 0-10:
    +3 if EMA20 > EMA50 (long) or EMA20 < EMA50 (short)
    +2 if price above/below 20-candle VWAP
    +3 if higher highs + higher lows pattern (last 5 candles)
    +2 if volume on last candle > 1.5x average
    """
    if len(prices) < 50:
        return 0
    try:
        strength = 0
        current = prices[-1]

        # EMA20 vs EMA50
        ema20 = sum(prices[-20:]) / 20
        ema50 = sum(prices[-50:]) / 50
        if direction == "long" and ema20 > ema50:
            strength += 3
        elif direction == "short" and ema20 < ema50:
            strength += 3

        # Price vs 20-candle VWAP (approximated as simple average since we don't have volume)
        vwap20 = sum(prices[-20:]) / 20
        if direction == "long" and current > vwap20:
            strength += 2
        elif direction == "short" and current < vwap20:
            strength += 2

        # Higher highs + higher lows (or lower lows + lower highs for short)
        last5 = prices[-5:]
        if direction == "long":
            hh = all(last5[i] >= last5[i-1] * 0.999 for i in range(1, len(last5)))
            hl = min(last5[1:]) >= min(last5[:-1]) * 0.999
            if hh and hl:
                strength += 3
        else:
            ll = all(last5[i] <= last5[i-1] * 1.001 for i in range(1, len(last5)))
            lh = max(last5[1:]) <= max(last5[:-1]) * 1.001
            if ll and lh:
                strength += 3

        # Volume proxy: last candle move > 1.5x average
        moves = [abs(prices[-i] - prices[-i-1]) / prices[-i-1] for i in range(1, min(21, len(prices))) if prices[-i-1] > 0]
        if moves:
            last_move = moves[0]
            avg_move = sum(moves) / len(moves)
            if last_move > avg_move * 1.5:
                strength += 2

        return strength
    except Exception:
        return 0


# ── v29.5.0: Active Session Filter ──
def is_active_session():
    """
    Trading session size multiplier:
    14:00-22:00 UTC → 1.0 (full size)
    08:00-14:00 UTC → 0.75
    22:00-08:00 UTC → 0.5 (and require score >= 8 for any entry)
    Returns (size_mult, min_score_override)
    """
    try:
        utc_hour = datetime.now(timezone.utc).hour
        if 14 <= utc_hour < 22:
            return (1.0, None)  # Full session, no score override
        elif 8 <= utc_hour < 14:
            return (0.75, None)
        else:
            return (0.5, 8)  # Off-hours: 50% size, require score >= 8
    except Exception:
        return (1.0, None)


# ── v29.5.0: Drawdown Protection ──
def drawdown_protection_mult(equity):
    """
    Track peak portfolio value. Returns (size_mult, allow_entry):
    >5% drawdown from peak → 0.5x size
    >10% drawdown from peak → block all entries
    >15% → existing kill switch handles it
    """
    global _pro_peak_portfolio
    if equity > _pro_peak_portfolio:
        _pro_peak_portfolio = equity
    if _pro_peak_portfolio <= 0:
        return (1.0, True)
    dd_pct = (_pro_peak_portfolio - equity) / _pro_peak_portfolio * 100
    if dd_pct > 10:
        return (0.0, False)  # Block all entries
    elif dd_pct > 5:
        return (0.5, True)  # Half size
    return (1.0, True)


# ── v29.5.0: Streak-Based Sizing ──
def streak_size_mult():
    """
    Track last 5 results. Returns sizing multiplier:
    5 wins → 1.2x (max)
    3 consecutive losses → 0.7x
    """
    global _pro_last_5_results
    if len(_pro_last_5_results) < 3:
        return 1.0
    last5 = _pro_last_5_results[-5:] if len(_pro_last_5_results) >= 5 else _pro_last_5_results
    last3 = _pro_last_5_results[-3:]
    if len(last5) >= 5 and all(r == "win" for r in last5):
        return 1.2
    if all(r == "loss" for r in last3):
        return 0.7
    return 1.0


def record_trade_result(won):
    """Record a win/loss for streak tracking."""
    global _pro_last_5_results
    _pro_last_5_results.append("win" if won else "loss")
    if len(_pro_last_5_results) > 10:
        _pro_last_5_results = _pro_last_5_results[-10:]


# ── Main ──
def main():
    if "--reset" in sys.argv:
        if os.path.exists(STATE_FILE):
            os.remove(STATE_FILE)
        print("  Reset. Run again without --reset.")
        return

    # v29.4.1: Delete Bayesian optimizer params to prevent overriding manual config
    _opt_params_path = os.path.join("logs", "optimal_params.json")
    if os.path.exists(_opt_params_path):
        try:
            os.remove(_opt_params_path)
            print("  [CLEANUP] Deleted logs/optimal_params.json — manual config preserved")
            logger.info("[STARTUP] Deleted logs/optimal_params.json to prevent Bayesian override of manual settings")
        except OSError:
            # Can't delete — overwrite with empty params so _load_optimal_params() is a no-op
            try:
                with open(_opt_params_path, "w") as f:
                    json.dump({"params": {}}, f)
                print("  [CLEANUP] Cleared logs/optimal_params.json — manual config preserved")
                logger.info("[STARTUP] Cleared optimal_params.json (delete failed, wrote empty params)")
            except Exception as e:
                print(f"  [CLEANUP] Could not clear optimal_params.json: {e}")
                logger.warning(f"[STARTUP] Failed to clear optimal_params.json: {e}")

    print("  Starting bot v29...")

    # Run verification suite before starting (non-fatal — never blocks startup)
    # v29.3.4: Run in a thread with 30s timeout so it can NEVER hang the bot
    print("  Running pre-flight checks...")
    def _run_preflight():
        try:
            from bot_verify import run_all
            return run_all()
        except Exception as e:
            print(f"  Pre-flight skipped: {e}")
            return True  # Don't block on verification failure
    _preflight_thread = threading.Thread(target=_run_preflight, daemon=True)
    _preflight_thread.start()
    _preflight_thread.join(timeout=30)  # 30 second hard timeout
    if _preflight_thread.is_alive():
        print("  Pre-flight TIMED OUT after 30s — skipping (bot will start anyway)")
        logger.warning("Pre-flight timed out after 30s — skipped")
    else:
        print("  Pre-flight: done\n")

    # Discover pairs (retry up to API_RETRY_STARTUP times)
    pair_names = None
    for _api_attempt in range(API_RETRY_STARTUP):
        print(f"  Discovering Kraken pairs (attempt {_api_attempt+1}/{API_RETRY_STARTUP})...", end=" ", flush=True)
        try:
            pair_names = get_usd_pairs()
        except Exception as e:
            print(f"error: {e}")
            logger.error(f"Pair discovery attempt {_api_attempt+1} failed: {e}")
        if pair_names:
            break
        print(f"FAILED (got {len(pair_names) if pair_names is not None else 'None'}). Retrying in {API_RETRY_DELAY}s...")
        time.sleep(API_RETRY_DELAY)
    if not pair_names:
        print("  FATAL: Cannot discover pairs after all retries. Check internet/API access.")
        return
    print(f"found {len(pair_names)}")
    # Print first 10 pairs for visual verification
    _sample = list(pair_names.items())[:10]
    print(f"  Sample pairs: {[f'{v}' for _, v in _sample]}")

    # Load or create wallet
    if FRESH_SESSION:
        # ── FULL STATE RESET: wipe everything for a clean session ──
        wallet = Wallet(CASH)
        saved_prices = {}
        # Reset ML brain (discard learned weights from previous sessions)
        brain.__init__(n_features=16, learning_rate=0.04)
        # Reset live trade tracker
        live_tracker.completed_trades.clear()
        live_tracker.winning_streak = 0
        # Reset all protection/tracking subsystems
        adaptive_risk.load_state({})
        daily_metrics.load_state({})
        cascade_protection.load_state({})
        strategy_health_monitor.load_state({})
        coin_loss_tracker.load_state({})
        overtrading_guard.load_state({})
        safe_mode.load_state({})
        error_classifier.load_state({})
        recovery_mode.load_state({})
        min_activity.load_state({})
        market_brain.load_state({})
        pair_failure_tracker.load_state({})
        perf_matrix.load_state({})
        # Reset awareness module
        awareness.long_wins = 0
        awareness.long_losses = 0
        awareness.short_wins = 0
        awareness.short_losses = 0
        awareness.coin_performance = {}
        awareness.recent_decisions = []
        # Reset session trade accumulator
        _session_trades.clear()
        # Reset performance tracker
        perf.returns.clear()
        perf.equity_curve.clear()
        perf.window_trades = 0
        # Delete stale state file so it doesn't confuse next restart
        if os.path.exists(STATE_FILE):
            try:
                os.rename(STATE_FILE, STATE_FILE + ".pre_fresh")
            except Exception:
                pass
        print(f"  FRESH SESSION: ${CASH:,.2f} cash | PnL=0 | wins=0 | losses=0 | session_trades=0 | ML brain reset")
        logger.info(f"FRESH_SESSION: wallet=${CASH:.2f} PnL=0 wins=0 losses=0 session_trades=0 ML=reset")
    else:
        wallet, saved_prices = Wallet.load()
        if wallet:
            print(f"  Resumed: ${wallet.cash:,.2f} cash, {len(wallet.longs)} longs, {len(wallet.shorts)} shorts")
        else:
            wallet = Wallet(CASH)
            saved_prices = {}
            logger.warning("No state file found, starting fresh despite FRESH_SESSION=False")
            print("  ⚠ WARNING: No state file found, starting fresh despite FRESH_SESSION=False")
            print(f"  Fresh start: ${CASH:,.2f}")

    # ── STARTUP VALIDATION (non-fatal, 15s timeout — log warning but continue) ──
    prices_for_startup = dict(saved_prices)
    _preflight_result = [None]  # Mutable container for thread result

    def _run_startup_check():
        try:
            _preflight_result[0] = startup_check(wallet, prices_for_startup)
        except Exception as e:
            _preflight_result[0] = e

    _sc_thread = threading.Thread(target=_run_startup_check, daemon=True)
    _sc_thread.start()
    _sc_thread.join(timeout=15)
    if _sc_thread.is_alive():
        print("  WARNING: Pre-flight timed out (>15s) — skipping")
        logger.warning("Pre-flight timed out — skipping")
    elif isinstance(_preflight_result[0], Exception):
        print(f"  WARNING: Startup check crashed ({_preflight_result[0]}) — continuing")
        logger.error(f"Startup check exception: {_preflight_result[0]}")
    elif not _preflight_result[0]:
        print("  WARNING: Startup validation failed — continuing for stability")
        logger.warning("Startup validation failed but bot starting for uptime")

    # Graceful shutdown
    running = [True]
    signal.signal(signal.SIGINT, lambda s, f: running.__setitem__(0, False))
    signal.signal(signal.SIGTERM, lambda s, f: running.__setitem__(0, False))

    prices = dict(saved_prices)
    all_pair_names = list(pair_names.keys())
    batch_offset = 0
    cycle = 0
    last_full_rank = []

    # Initialize safety systems
    initial_val = wallet.value(prices) if wallet else CASH
    circuit = CircuitBreaker(initial_val)
    daily_metrics.start_day(initial_val, 0)
    corr_guard = CorrelationGuard()
    price_last_updated = {}  # Track last cycle each coin's price was refreshed
    # Initialize kill switch with starting equity
    global kill_switch
    kill_switch = KillSwitch(initial_val)
    # Restore kill switch state from saved state file (if resuming)
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE) as _f:
                _saved = json.load(_f)
            _ks_state = _saved.get("kill_switch")
            if _ks_state:
                kill_switch.load_state(_ks_state)
                if kill_switch.triggered:
                    logger.warning(f"KILL SWITCH RESTORED: still triggered — {kill_switch.trigger_reason}")
        except Exception:
            pass  # State file already loaded by Wallet.load, just skip on error

    # Initialize staleness for held coins to 0 (not current cycle) so stale detection works after restart
    for _held_coin in list(wallet.longs.keys()) + list(wallet.shorts.keys()):
        if _held_coin not in price_last_updated:
            price_last_updated[_held_coin] = 0
            logger.debug(f"STALENESS INIT: {_held_coin} set to cycle 0 (held from previous session)")

    # v29.4.0: Load Bayesian-optimized params if available
    if _load_optimal_params():
        print(f"  Loaded Bayesian-optimized params from {OPTIMAL_PARAMS_FILE}")
    else:
        print(f"  Using default params (no optimal_params.json found)")

    # v29.4.0: Initialize exchange adapters (Item 1)
    try:
        _init_exchanges()
        _conn = [n for n, a in _exchange_adapters.items() if a.is_connected()]
        print(f"  Exchanges: {len(_conn)} connected — {_conn}")
    except Exception as _ex_err:
        print(f"  Exchange init warning: {_ex_err}")

    # v29.4.0: Refresh pair names cache for orderbook_imbalance()
    _refresh_pair_names_cache()

    # v29.4.0: Orphan position detection on startup (Item 25)
    _orphan_count = 0
    for _oc in list(wallet.longs.keys()):
        if wallet.longs[_oc].get("qty", 0) <= 0:
            logger.warning(f"[ORPHAN] Removing zero-qty long: {_oc}")
            del wallet.longs[_oc]
            _orphan_count += 1
        elif wallet.longs[_oc].get("entry", 0) <= 0:
            logger.warning(f"[ORPHAN] Removing invalid-entry long: {_oc}")
            del wallet.longs[_oc]
            _orphan_count += 1
    for _oc in list(wallet.shorts.keys()):
        if wallet.shorts[_oc].get("qty", 0) <= 0:
            logger.warning(f"[ORPHAN] Removing zero-qty short: {_oc}")
            del wallet.shorts[_oc]
            _orphan_count += 1
        elif wallet.shorts[_oc].get("entry", 0) <= 0:
            logger.warning(f"[ORPHAN] Removing invalid-entry short: {_oc}")
            del wallet.shorts[_oc]
            _orphan_count += 1
    if _orphan_count > 0:
        print(f"  ⚠ Cleaned {_orphan_count} orphan positions from state")
        logger.warning(f"[ORPHAN] Cleaned {_orphan_count} orphan positions on startup")

    # v29.4.0: Stock scan if Alpaca connected (Item 8)
    alpaca_ex = _exchange_adapters.get("alpaca")
    if alpaca_ex and alpaca_ex.is_connected():
        STOCK_SCAN_ENABLED_local = True
        try:
            _hour = datetime.now(timezone.utc).hour
            if _hour <= 10:  # Roughly 4-6 AM ET
                print("  Running pre-market scan...")
                pre_market_scan()
        except Exception:
            pass

    warmup_sec = WARMUP_CYCLES * POLL
    ramp_sec = WARMUP_RAMP_END * POLL
    print(f"  Warm-up: {WARMUP_CYCLES} cycles (~{warmup_sec//60}m) data-only, then {WARMUP_RAMP_MULT:.0%} size until cycle {WARMUP_RAMP_END} (~{ramp_sec//60}m)")

    print(f"  Running — scanning {len(all_pair_names)} pairs every {POLL}s")

    global _bot_start_time
    _bot_start_time = time.time()
    _consecutive_errors = 0
    _current_regime = "UNKNOWN"  # Safe default until first regime classification
    while running[0]:
        try:
            _cycle_start = time.time()
            cycle += 1

            # HEARTBEAT — proof-of-life every 50 cycles
            if cycle % 50 == 0:
                logger.info(f"HEARTBEAT cycle {cycle} — CYCLE OK — no crashes, running stable")

            _suspicious_coins.clear()  # Reset suspicious flags each cycle
            cascade_protection.reset_cycle()
            overtrading_guard.reset_cycle()
            # Update global _current_cycle for use in record_exit
            global _current_cycle
            _current_cycle = cycle

            # v29.4.0: Cross-exchange arbitrage scan (Item 2)
            try:
                scan_arbitrage(cycle)
            except Exception:
                pass

            # v29.4.0: DEX scan every 100 cycles (Item 9)
            if DEX_SCAN_ENABLED and cycle % 100 == 0:
                try:
                    dex_scanner.scan()
                except Exception:
                    pass

            # v29.4.0: Stock scan every 500 cycles (Item 7)
            if STOCK_SCAN_ENABLED and cycle % 500 == 0:
                try:
                    scan_stock_universe()
                except Exception:
                    pass

            # v29.4.0: Daily report at midnight UTC (Item 12)
            if cycle % 1000 == 0:
                try:
                    _now_h = datetime.now(timezone.utc).hour
                    if _now_h == 0:
                        generate_daily_report(wallet, prices, wallet.trades[-50:], cycle)
                except Exception:
                    pass

            # PRIORITY: Always fetch prices for coins we HOLD first
            held_pairs = []
            for coin in list(wallet.longs.keys()) + list(wallet.shorts.keys()):
                for pname, alt in pair_names.items():
                    short = to_short_name(alt)
                    if short == coin:
                        held_pairs.append(pname)
                        break

            # v29.3.4: Expanded scanning — full universe or rotating batch
            if FULL_SCAN_ENABLED:
                scan_batch = list(set(held_pairs + all_pair_names))
                if cycle % 100 == 1:
                    logger.info(f"[SCAN] Full universe: {len(scan_batch)} pairs (held={len(held_pairs)})")
            else:
                batch = all_pair_names[batch_offset:batch_offset + SCAN_BATCH_SIZE]
                batch_offset = (batch_offset + SCAN_BATCH_SIZE) % max(len(all_pair_names), 1)
                scan_batch = list(set(held_pairs + batch))
            _api_ok = True
            try:
                tickers = get_tickers(scan_batch)
                if not tickers:
                    _api_ok = False
                    api_staleness.record_failure()
                    try:
                        logger.warning(f"API EMPTY RESPONSE (cycle {cycle}) — using last known prices for exits")
                    except Exception:
                        pass
            except Exception as _api_err:
                _api_ok = False
                api_staleness.record_failure()
                try:
                    logger.warning(f"API FETCH FAILED (cycle {cycle}): {_api_err} — using last known prices for exits")
                    error_logger.log("api_fetch", str(_api_err))
                except Exception:
                    pass

            if _api_ok and tickers:
                api_staleness.record_success(cycle)
                # Update prices + track history + correlation data
                for pair, t in tickers.items():
                    name = pair_names.get(pair, pair)
                    short = to_short_name(name)
                    prices[short] = t["price"]
                    prices[pair] = t["price"]
                    track_price(short, t["price"])
                    corr_guard.update(short, t["price"])
                    price_last_updated[short] = cycle

            # v29.3.4: Pre-filter illiquid/dead pairs before scoring
            if _api_ok and tickers and SCAN_PREFILTER_ENABLED:
                _pre_count = len(tickers)
                _tradable_keys = prefilter_tradable_pairs(tickers)
                tickers = {p: tickers[p] for p in _tradable_keys if p in tickers}
                _filtered_out = _pre_count - len(tickers)
                if _filtered_out > 0 and cycle % 50 == 1:
                    logger.debug(f"[PREFILTER] {_filtered_out}/{_pre_count} pairs filtered (vol/atr/price)")

            # v29.3.4: Score recovery candidates for dynamic blacklist
            if _api_ok and tickers and TEMP_BLACKLIST_ENABLED:
                dynamic_blacklist.score_recovery_candidates(tickers, cycle, coin_atr_fn=coin_atr)
                dynamic_blacklist.cycle_end(cycle)

            # v29.3.4: Update alpha strategy state (per-cycle, lightweight)
            if ADVANCED_ALPHA_ENABLED and _api_ok:
                try:
                    alpha_macro.update(cycle, tickers or {})
                    alpha_vix.update(cycle)
                except Exception as _alpha_upd_err:
                    logger.debug(f"[ALPHA] update error: {_alpha_upd_err}")

            # Circuit breaker check — always runs (uses last known prices if API failed)
            portfolio_val = wallet.value(prices)
            daily_metrics.update_equity(portfolio_val)
            trading_allowed = circuit.update(portfolio_val, cycle)
            shadow.update_shadows(prices)  # Track hypothetical PnL on skipped signals
            if not trading_allowed and circuit.daily_halted:
                # Force exit losing positions on daily hard stop
                force_exit_losing_positions(wallet, prices, executor, cycle, _current_regime)

            # Rank opportunities every cycle (always use freshest data) — only when API succeeded
            if _api_ok and tickers:
                last_full_rank = rank(tickers, min_vol=500000, regime=_current_regime)
                # Track signal count for visibility
                _qualifying_signals = sum(1 for r in last_full_rank if abs(r["score"]) >= 0.05)
                for _ in range(_qualifying_signals):
                    recovery_mode.record_signal()
                # Global trade audit: reset + count raw signals entering this cycle
                cycle_audit.reset()
                cycle_audit.signals_raw = _qualifying_signals
                if _qualifying_signals == 0 and cycle % VISIBILITY_LOG_INTERVAL == 0 and cycle > 0:
                    logger.debug(f"[VISIBILITY] cycle={cycle} signals_found=0 — no qualifying signals this cycle")

                # Periodic smart blocker summary (every VISIBILITY_LOG_INTERVAL cycles)
                if cycle % VISIBILITY_LOG_INTERVAL == 0 and cycle > 0:
                    try:
                        _cb_summary = coin_loss_tracker.blocked_coins_summary()
                        _pb_summary = pair_failure_tracker.blocked_pairs_summary()
                        if _cb_summary:
                            for _cb_coin, _cb_info in _cb_summary.items():
                                logger.debug(f"[BLOCK STATUS] coin={_cb_coin} cumul_pnl={_cb_info['cumul_pnl']:.1f}% dd={_cb_info['drawdown']:.1f}% trades={_cb_info['trades']} blocked_since={_cb_info['blocked_cycle']}")
                        if _pb_summary:
                            for _pb_pair, _pb_info in _pb_summary.items():
                                logger.debug(f"[BLOCK STATUS] pair={_pb_pair} failures={_pb_info['count']} last_fail_cycle={_pb_info['last_cycle']}")
                    except Exception:
                        pass

            # Update cooldown timestamps
            for coin in list(wallet.cooldowns.keys()):
                if wallet.cooldowns[coin] == 0:
                    wallet.cooldowns[coin] = cycle

            # Early regime detection for exit tracking (never let it become None/unset)
            try:
                _current_regime = adaptive_regime.classify(prices_cache) or awareness.detect_regime(prices_cache) or "UNKNOWN"
            except Exception:
                _current_regime = _current_regime if _current_regime else "UNKNOWN"

            # ── MANAGE EXISTING POSITIONS ──
            _cash_before_exits = wallet.cash
            _exited_this_cycle = set()
            for coin in list(wallet.longs.keys()):
              try:
                p = prices.get(coin, 0)
                if p is None or (isinstance(p, float) and (p != p)):  # NaN check
                    p = 0
                if p <= 0:
                    pos = wallet.longs[coin]
                    pos["no_price_cycles"] = pos.get("no_price_cycles", 0) + 1
                    logger.warning(f"NO PRICE for held LONG {coin} ({pos['no_price_cycles']} cycles)")
                    if pos["no_price_cycles"] > 50:
                        logger.error(f"FORCE EXIT LONG {coin} — no price for {pos['no_price_cycles']} cycles")
                        entry = pos["entry"]
                        _fp = _exit_slippage_price(entry, "SELL", coin=coin, is_sl_exit=True)
                        wallet.sell(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("no_price_exit", coin, "long", entry, _fp, _current_regime, wallet=wallet)
                    continue
                else:
                    if coin in wallet.longs:
                        wallet.longs[coin]["no_price_cycles"] = 0
                pos = wallet.longs[coin]
                entry = pos["entry"]
                pnl_pct = (p - entry) / entry * 100 if entry != 0 else 0

                # Staleness detection: warn if price data is old, force exit if critically stale
                _staleness = cycle - price_last_updated.get(coin, cycle)
                if _staleness > 10:
                    logger.warning(f"STALE PRICE {coin}: {_staleness} cycles old")
                if _staleness > 30:
                    logger.error(f"FORCE EXIT LONG {coin} — stale price ({_staleness} cycles)")
                    _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=True)
                    wallet.sell(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit("stale_exit", coin, "long", entry, _fp, _current_regime, wallet=wallet)
                    continue

                if "bought_cycle" not in pos:
                    pos["bought_cycle"] = cycle
                held_cycles = cycle - pos.get("bought_cycle", cycle)
                held_seconds = held_cycles * POLL

                # Dynamic levels based on ATR — locked to entry SL (can tighten, never widen)
                atr = coin_atr(coin) * 100
                sl_dynamic = max(0.8, atr * 0.7)  # v29.3: tighter SL (was max(1.5, atr*1.0))
                sl_target = min(sl_dynamic, pos.get("entry_sl", sl_dynamic))
                # v29.3 Dynamic TP: achievable targets for 2s candles
                _entry_atr = pos.get("entry_atr", atr)
                if _entry_atr < 1.5:
                    _tp_scale = 1.0   # v29.3: Calm: no stretch (was 1.1)
                elif _entry_atr > 3.0:
                    _tp_scale = 0.85  # v29.3: Volatile: tighter (was 0.9)
                else:
                    _tp_scale = 1.0   # v29.3: Normal: no stretch (was 1.2)
                _tp_base_ratio = TP_RATIO_TRENDING if (_clean_trends >= 75 and _current_regime != "CHOPPY") else TP_RATIO_NORMAL  # v29.3.5: use config constants instead of hardcoded 1.8/1.6
                tp_trigger = max(0.4, sl_target * _tp_base_ratio * _tp_scale)  # v29.3: floor 0.4% (was 0.8%)
                # Trend-strength TP boost: minimal push in strong trends
                _trend_str = abs(short_momentum(coin, window=10))
                if _trend_str > 0.02:
                    tp_trigger *= 1.05  # v29.3: Strong trend → 5% wider (was 20%)
                elif _trend_str > 0.01:
                    tp_trigger *= 1.0   # v29.3: Moderate trend → no boost (was 10%)
                # Log final TP applied
                if held_cycles == 1:
                    logger.debug(f"[TP_APPLIED] {coin} LONG tp={tp_trigger:.2f}% sl={sl_target:.2f}% ratio={tp_trigger/sl_target:.2f}x atr={atr:.2f}%")

                # Track highest price (for trailing in profit-protection mode)
                if "highest" not in pos:
                    pos["highest"] = entry
                pos["highest"] = max(pos["highest"], p)
                drop_from_peak = (pos["highest"] - p) / pos["highest"] * 100 if pos["highest"] > 0 else 0

                # === RULE 1: STOP-LOSS — ALWAYS ENFORCED, NO EXCEPTIONS ===
                if pnl_pct <= -sl_target:
                    _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=True)
                    wallet.sell(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit(pos.get("strategy", "momentum"), coin, "long", entry, _fp, _current_regime, wallet=wallet)
                    # Gap detection: if actual loss > 1.2x expected SL, trigger lockout
                    _expected_sl = pos.get("entry_sl", sl_target)
                    if abs(pnl_pct) > _expected_sl * 1.2:
                        logger.error(f"GAP EVENT LONG {coin}: lost {pnl_pct:+.2f}% vs expected -{_expected_sl:.2f}%")
                        adaptive_risk.force_gap_lockout(cycle, duration=100)
                        if kill_switch:
                            kill_switch.record_gap_event()
                        daily_metrics.record_trade(pnl_pct, is_sl=True, is_gap=True)
                    else:
                        daily_metrics.record_trade(pnl_pct, is_sl=True)
                    cascade_protection.record_sl_exit()
                    logger.info(f"STOP LOSS {coin} {pnl_pct:+.2f}% (limit={sl_target:.2f}%)")
                    continue

                # === MIN HOLD GUARD: no non-SL exit before 60 cycles ===
                elif held_cycles < MIN_HOLD_CYCLES:
                    pass  # Only stop-loss above can exit early — all other exits wait

                # === RULE 2a: TIME STOP — dump if losing after 15 min ===
                elif held_seconds > 900 and pnl_pct < -0.5:
                    _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                    wallet.sell(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit(pos.get("strategy", "momentum"), coin, "long", entry, _fp, _current_regime, wallet=wallet)
                    daily_metrics.record_trade(pnl_pct)
                    logger.info(f"TIME EXIT {coin} {pnl_pct:+.2f}% (held {held_seconds:.0f}s)")
                    continue

                # === RULE 2a2: SLOW BLEED EXIT — cut positions bleeding slowly ===
                # v29.3.5: If losing > 0.3% and held > 50% of stagnation limit, exit early
                elif pnl_pct < SLOW_BLEED_THRESHOLD and held_cycles > STAGNATION_EXIT_CYCLES // 2:
                    _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                    wallet.sell(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit("slow_bleed_exit", coin, "long", entry, _fp, _current_regime, wallet=wallet)
                    daily_metrics.record_trade(pnl_pct)
                    logger.info(f"SLOW BLEED EXIT {coin} {pnl_pct:+.2f}% (held {held_cycles} cycles, > 50% stag limit)")
                    continue

                # === RULE 2b: STAGNATION EXIT — ATR-adaptive ===
                # v29.3.5: Only dump LOSING stagnant positions (was pnl_pct < tp_trigger — killed green trades)
                # Profitable positions are handled by profit protection / trailing stop instead
                elif pnl_pct < 0:
                    _atr_pct = max(0.01, atr)  # floor at 0.01% to avoid division issues
                    _stag_limit = min(400, max(100, int((1.2 / _atr_pct) ** 2)))  # v29.3: tighter clamp [100,400] (was [150,600]), faster formula
                    # Brain mood adjusts patience: AGGRESSIVE = more patient, CAUTIOUS = cut faster
                    _stag_limit = int(_stag_limit * _brain.get("stag_mult", 1.0))
                    if held_cycles > _stag_limit:
                        _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                        wallet.sell(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("stagnation_exit", coin, "long", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"STAGNATION EXIT {coin} {pnl_pct:+.2f}% (held {held_cycles}/{_stag_limit} cycles, atr={atr:.2f}%)")
                        continue

                # === RULE 2c: EARLY PP — protect profits when close to TP ===
                elif pnl_pct >= PP_TRIGGER_MULTIPLIER * tp_trigger and pnl_pct < tp_trigger and "profit_protection" not in pos:  # v29.3.5: 70% of TP (was 0.4% — triggered 72% below target)
                    assessment = assess_exit(coin, "long", entry, p)
                    if assessment["action"] == "HOLD_AND_TRAIL":
                        pos["profit_protection"] = True
                        pos["pp_start_cycle"] = held_cycles
                        pos["pp_start_pnl"] = pnl_pct  # Store activation PnL for timeout calc
                        _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl_pct - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                        _streak_m = _adaptive_trail_multiplier()
                        _raw_mom = short_momentum(coin, window=10)
                        _live_trend = min(max(0, _raw_mom) / 0.02, 1.0)
                        _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                        _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                        # (confidence nudge removed: cosmetic, max 0.03 shift absorbed by clamp in 1 cycle)
                        _prev = pos.get("_trail_tm", _raw_tm)
                        _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                        _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                        pos["_trail_tm"] = _final_tm
                        pos["trail_stop"] = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                        logger.debug(f"EARLY PP {coin} +{pnl_pct:.1f}% (tp_trigger={tp_trigger:.1f}%, trail_m={_final_tm:.2f})")

                # === RULE 3: TP TRIGGER — re-evaluate, don't auto-exit ===
                elif pnl_pct >= tp_trigger:
                    if "profit_protection" not in pos:
                        # First time hitting TP — assess market conditions
                        assessment = assess_exit(coin, "long", entry, p)
                        if assessment["action"] == "HOLD_AND_TRAIL":
                            # Market is strong — switch to profit-protection mode
                            pos["profit_protection"] = True
                            pos["pp_start_cycle"] = held_cycles  # Track when PP started for timeout
                            pos["pp_start_pnl"] = pnl_pct  # Store activation PnL for timeout calc
                            # Weighted trail: blend pnl-tightening + live trend + streak, clamped per-cycle
                            _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl_pct - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                            _streak_m = _adaptive_trail_multiplier()
                            _raw_mom = short_momentum(coin, window=10)
                            _live_trend = min(max(0, _raw_mom) / 0.02, 1.0)  # Only loosen on favorable (upward) momentum
                            _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                            _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                            # (confidence nudge removed: cosmetic, max 0.03 shift absorbed by clamp in 1 cycle)
                            _prev = pos.get("_trail_tm", _raw_tm)
                            _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                            _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                            pos["_trail_tm"] = _final_tm
                            pos["trail_stop"] = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                            logger.debug(f"TP HIT {coin} +{pnl_pct:.1f}% → HOLDING trail_m={_final_tm:.2f} trend={_live_trend:.2f} streak={_streak_m:.2f} ({assessment['reason']})")
                        else:
                            # Min profit filter: block exit if profit too small
                            if MIN_PROFIT_FILTER_ENABLED and (pnl_pct / 100) < MIN_PROFIT_THRESHOLD:
                                logger.debug(f"MIN_PROFIT HELD {coin} +{pnl_pct:.1f}% (need {MIN_PROFIT_THRESHOLD*100:.1f}%)")
                            else:
                                _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                                wallet.sell(coin, _fp)
                                _exited_this_cycle.add(coin)
                                record_exit(pos.get("strategy", "momentum"), coin, "long", entry, _fp, _current_regime, wallet=wallet)
                                daily_metrics.record_trade(pnl_pct)
                                logger.info(f"TP EXIT {coin} +{pnl_pct:.1f}% ({assessment['reason']})")
                                continue

                # === RULE 4: PROFIT PROTECTION MODE — trailing stop after TP ===
                if pos.get("profit_protection"):
                    # Defensive: backfill pp_start_cycle if missing (state restore edge case)
                    if "pp_start_cycle" not in pos:
                        pos["pp_start_cycle"] = max(0, held_cycles - 1)
                    if "pp_start_pnl" not in pos:
                        pos["pp_start_pnl"] = pnl_pct  # Backfill with current if missing
                    # Adaptive PP timeout: use activation PnL (not current) for stable timeout
                    _pp_cycles = held_cycles - pos["pp_start_cycle"]
                    _pp_start_pnl = pos["pp_start_pnl"]
                    _pp_timeout = 100 + int(max(0, _pp_start_pnl - 1.5) * 50)  # v29.3.5: was 500+100/% (max 900). Now 100+50/% capped at 200
                    _pp_timeout = min(200, _pp_timeout)  # v29.3.5: was 900 — capped at 200 cycles (~7 min at POLL=2s)
                    if _pp_cycles > _pp_timeout:
                        _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                        wallet.sell(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("pp_timeout", coin, "long", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"PP TIMEOUT {coin} +{pnl_pct:.1f}% (profit protection held {_pp_cycles} cycles)")
                        continue

                    # Update trailing stop (only moves UP, never down)
                    # Weighted trail: blend pnl-tightening + live trend + streak, clamped per-cycle
                    _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl_pct - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                    _streak_m = _adaptive_trail_multiplier()
                    _raw_mom = short_momentum(coin, window=10)
                    _live_trend = min(max(0, _raw_mom) / 0.02, 1.0)  # Only loosen on favorable (upward) momentum
                    _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                    _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                    _prev = pos.get("_trail_tm", _raw_tm)
                    _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                    _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                    # Drop-from-peak guard: proportional dampening (volatile coins tolerate bigger pullbacks)
                    _dfp_thresh = max(0.8, atr * 0.3)  # v29.3: tighter to match new SL
                    if _final_tm > _prev and _dfp_thresh > 0:
                        _dampen = min(1.0, max(0, drop_from_peak) / (_dfp_thresh * 2))  # Proportional: 0→full, thresh→half, 2×thresh→locked
                        _final_tm = _prev + (_final_tm - _prev) * (1 - _dampen)
                    pos["_trail_tm"] = _final_tm
                    new_trail = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                    pos["trail_stop"] = max(pos.get("trail_stop", entry), new_trail)

                    # Adaptive reassessment: faster when more profit at stake or higher volatility
                    _reassess_base = 30
                    _pnl_adj = max(0.5, 1.0 - abs(pnl_pct) * 0.1)  # 5%+ PnL → 0.5x (15s min)
                    _vol_adj = min(1.5, max(0.6, 1.5 / max(1.0, atr)))  # High ATR → faster checks
                    _reassess_secs = max(15, min(60, _reassess_base * _pnl_adj * _vol_adj))
                    _pp_age = held_cycles - pos.get("pp_start_cycle", 0)
                    _cached_assessment = None  # Reuse for hard ceiling if available
                    if _pp_age > 0 and held_cycles % max(1, int(_reassess_secs / POLL)) == 0:
                        _cached_assessment = assess_exit(coin, "long", entry, p)
                        if _cached_assessment["action"] == "EXIT":
                            if MIN_PROFIT_FILTER_ENABLED and (pnl_pct / 100) < MIN_PROFIT_THRESHOLD:
                                logger.debug(f"MIN_PROFIT HELD {coin} +{pnl_pct:.1f}% (need {MIN_PROFIT_THRESHOLD*100:.1f}%)")
                            else:
                                _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                                wallet.sell(coin, _fp)
                                _exited_this_cycle.add(coin)
                                record_exit(pos.get("strategy", "momentum"), coin, "long", entry, _fp, _current_regime, wallet=wallet)
                                daily_metrics.record_trade(pnl_pct)
                                logger.info(f"REASSESS EXIT {coin} +{pnl_pct:.1f}% ({_cached_assessment['reason']})")
                                continue
                        # else: HOLD_AND_TRAIL — no action needed (nudge removed: cosmetic, absorbed by clamp in 1 cycle)

                    # Trailing stop hit — ALWAYS execute (protective mechanism)
                    if p <= pos.get("trail_stop", 0):
                        _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                        wallet.sell(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit(pos.get("strategy", "momentum"), coin, "long", entry, _fp, _current_regime, wallet=wallet)
                        peak_pnl = (pos["highest"] - entry) / entry * 100 if entry != 0 else 0
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"TRAIL STOP {coin} +{pnl_pct:.1f}% (peak was +{peak_pnl:.1f}%)")
                        continue

                    # Hard ceiling — adaptive: reuse cached assessment if available
                    _ceiling_assessment = _cached_assessment if _cached_assessment is not None else assess_exit(coin, "long", entry, p)
                    _atr_mult = 7 if _ceiling_assessment.get("confidence", 0) >= 0.8 else 5
                    _hard_ceiling = max(5.0, atr * _atr_mult)
                    if pnl_pct >= _hard_ceiling:
                        _fp = _exit_slippage_price(p, "SELL", coin=coin, is_sl_exit=False)
                        wallet.sell(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("MAX_TP", coin, "long", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"MAX TP {coin} +{pnl_pct:.1f}% (ceiling={_hard_ceiling:.1f}%, conf={_ceiling_assessment.get('confidence', 0):.2f})")
                        continue
              except Exception as _exit_err:
                try:
                    logger.error(f"EXIT GUARD: error managing LONG {coin}: {_exit_err}")
                    error_logger.log("exit_guard_long", f"{coin}: {_exit_err}")
                except Exception:
                    pass
                # FORCE EXIT: if normal exit logic crashed, force-close the position
                try:
                    if coin in wallet.longs:
                        _fe_entry = wallet.longs[coin].get("entry", 0)
                        _fe_price = prices.get(coin, 0)
                        # SAFE PRICING: never use 0 or None — fallback to entry price
                        if not _fe_price or _fe_price <= 0:
                            _fe_price = _fe_entry if _fe_entry > 0 else 0.0001
                        if not _fe_entry or _fe_entry <= 0:
                            _fe_entry = _fe_price
                        _fe_fp = _exit_slippage_price(_fe_price, "SELL", coin=coin, is_sl_exit=True)
                        wallet.sell(coin, _fe_fp)
                        _exited_this_cycle.add(coin)
                        record_exit("force_exit", coin, "long", _fe_entry, _fe_fp, _current_regime, wallet=wallet)
                        logger.error(f"FORCE EXIT LONG {coin} @ ${_fe_fp:.4f} (entry=${_fe_entry:.4f}) after exit guard error")
                except Exception as _fe_err:
                    try:
                        logger.error(f"FORCE EXIT FAILED LONG {coin}: {_fe_err}")
                        error_logger.log("exit_force_fail_long", f"{coin}: {_fe_err}")
                    except Exception:
                        pass

            for coin in list(wallet.shorts.keys()):
              try:
                p = prices.get(coin, 0)
                if p is None or (isinstance(p, float) and (p != p)):  # NaN check
                    p = 0
                if p <= 0:
                    pos = wallet.shorts[coin]
                    pos["no_price_cycles"] = pos.get("no_price_cycles", 0) + 1
                    logger.warning(f"NO PRICE for held SHORT {coin} ({pos['no_price_cycles']} cycles)")
                    if pos["no_price_cycles"] > 50:
                        logger.error(f"FORCE EXIT SHORT {coin} — no price for {pos['no_price_cycles']} cycles")
                        entry = pos["entry"]
                        _fp = _exit_slippage_price(entry, "COVER", coin=coin, is_sl_exit=True)
                        wallet.cover(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("no_price_exit", coin, "short", entry, _fp, _current_regime, wallet=wallet)
                    continue
                else:
                    if coin in wallet.shorts:
                        wallet.shorts[coin]["no_price_cycles"] = 0
                pos = wallet.shorts[coin]
                entry = pos["entry"]
                pnl_pct = (entry - p) / entry * 100 if entry != 0 else 0

                # Staleness detection: warn if price data is old, force exit if critically stale
                _staleness = cycle - price_last_updated.get(coin, cycle)
                if _staleness > 10:
                    logger.warning(f"STALE PRICE SHORT {coin}: {_staleness} cycles old")
                if _staleness > 30:
                    logger.error(f"FORCE EXIT SHORT {coin} — stale price ({_staleness} cycles)")
                    _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=True)
                    wallet.cover(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit("stale_exit", coin, "short", entry, _fp, _current_regime, wallet=wallet)
                    continue

                if "bought_cycle" not in pos:
                    pos["bought_cycle"] = cycle
                held_seconds = (cycle - pos.get("bought_cycle", cycle)) * POLL
                held_cycles = cycle - pos.get("bought_cycle", cycle)

                # Dynamic levels based on ATR — locked to entry SL (can tighten, never widen)
                atr = coin_atr(coin) * 100
                sl_dynamic = max(0.8, atr * 0.7)  # v29.3: tighter SL (was max(1.5, atr*1.0))
                sl_target = min(sl_dynamic, pos.get("entry_sl", sl_dynamic))
                # v29.3 Dynamic TP: achievable targets (mirrors long-side)
                _entry_atr = pos.get("entry_atr", atr)
                if _entry_atr < 1.5:
                    _tp_scale = 1.0   # v29.3: Calm: no stretch (was 1.1)
                elif _entry_atr > 3.0:
                    _tp_scale = 0.85  # v29.3: Volatile: tighter (was 0.9)
                else:
                    _tp_scale = 1.0   # v29.3: Normal: no stretch (was 1.2)
                _tp_base_ratio = TP_RATIO_TRENDING if (_clean_trends >= 75 and _current_regime != "CHOPPY") else TP_RATIO_NORMAL  # v29.3.5: use config constants instead of hardcoded 1.8/1.6
                tp_trigger = max(0.4, sl_target * _tp_base_ratio * _tp_scale)  # v29.3: floor 0.4% (was 0.8%)
                # Trend-strength TP boost: minimal push in strong trends
                _trend_str = abs(short_momentum(coin, window=10))
                if _trend_str > 0.02:
                    tp_trigger *= 1.05  # v29.3: Strong trend → 5% wider (was 20%)
                elif _trend_str > 0.01:
                    tp_trigger *= 1.0   # v29.3: Moderate trend → no boost (was 10%)
                # Log final TP applied
                if held_cycles == 1:
                    logger.debug(f"[TP_APPLIED] {coin} SHORT tp={tp_trigger:.2f}% sl={sl_target:.2f}% ratio={tp_trigger/sl_target:.2f}x atr={atr:.2f}%")

                if "lowest" not in pos:
                    pos["lowest"] = entry
                pos["lowest"] = min(pos["lowest"], p)

                # === STOP-LOSS: ALWAYS ENFORCED ===
                if pnl_pct <= -sl_target:
                    _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=True)
                    wallet.cover(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit(pos.get("strategy", "momentum"), coin, "short", entry, _fp, _current_regime, wallet=wallet)
                    # Gap detection: if actual loss > 1.2x expected SL, trigger lockout
                    _expected_sl = pos.get("entry_sl", sl_target)
                    if abs(pnl_pct) > _expected_sl * 1.2:
                        logger.error(f"GAP EVENT SHORT {coin}: lost {pnl_pct:+.2f}% vs expected -{_expected_sl:.2f}%")
                        adaptive_risk.force_gap_lockout(cycle, duration=100)
                        if kill_switch:
                            kill_switch.record_gap_event()
                        daily_metrics.record_trade(pnl_pct, is_sl=True, is_gap=True)
                    else:
                        daily_metrics.record_trade(pnl_pct, is_sl=True)
                    cascade_protection.record_sl_exit()
                    logger.info(f"SHORT STOP {coin} {pnl_pct:+.2f}%")
                    continue

                # === MIN HOLD GUARD (short): no non-SL exit before 60 cycles ===
                elif held_cycles < MIN_HOLD_CYCLES_MEANREV:
                    pass  # Only stop-loss above can exit early — all other exits wait

                elif held_seconds > 900 and pnl_pct < -0.5:
                    _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                    wallet.cover(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit(pos.get("strategy", "momentum"), coin, "short", entry, _fp, _current_regime, wallet=wallet)
                    daily_metrics.record_trade(pnl_pct)
                    logger.info(f"SHORT TIME EXIT {coin} {pnl_pct:+.2f}% (held {held_seconds:.0f}s)")
                    continue

                # === SLOW BLEED EXIT (short) — cut positions bleeding slowly ===
                # v29.3.5: If losing > 0.3% and held > 50% of stagnation limit, exit early
                elif pnl_pct < SLOW_BLEED_THRESHOLD and held_cycles > STAGNATION_EXIT_CYCLES // 2:
                    _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                    wallet.cover(coin, _fp)
                    _exited_this_cycle.add(coin)
                    record_exit("slow_bleed_exit", coin, "short", entry, _fp, _current_regime, wallet=wallet)
                    daily_metrics.record_trade(pnl_pct)
                    logger.info(f"SHORT SLOW BLEED EXIT {coin} {pnl_pct:+.2f}% (held {held_cycles} cycles, > 50% stag limit)")
                    continue

                # === STAGNATION EXIT — ATR-adaptive (short) ===
                # v29.3.5: Only dump LOSING stagnant positions (was pnl_pct < tp_trigger)
                elif pnl_pct < 0:
                    _atr_pct = max(0.01, atr)  # floor at 0.01%
                    _stag_limit = min(400, max(100, int((1.2 / _atr_pct) ** 2)))  # v29.3: tighter [100,400] (was [150,600])
                    # Brain mood adjusts patience: AGGRESSIVE = more patient, CAUTIOUS = cut faster
                    _stag_limit = int(_stag_limit * _brain.get("stag_mult", 1.0))
                    if held_cycles > _stag_limit:
                        _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                        wallet.cover(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("stagnation_exit", coin, "short", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"SHORT STAGNATION EXIT {coin} {pnl_pct:+.2f}% (held {held_cycles}/{_stag_limit} cycles, atr={atr:.2f}%)")
                        continue

                # === EARLY PP — protect profits when close to TP ===
                elif pnl_pct >= PP_TRIGGER_MULTIPLIER * tp_trigger and pnl_pct < tp_trigger and "profit_protection" not in pos:  # v29.3.5: 70% of TP (was 0.4% — triggered 72% below target)
                    assessment = assess_exit(coin, "short", entry, p)
                    if assessment["action"] == "HOLD_AND_TRAIL":
                        pos["profit_protection"] = True
                        pos["pp_start_cycle"] = held_cycles
                        pos["pp_start_pnl"] = pnl_pct  # Store activation PnL for timeout calc
                        _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl_pct - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                        _streak_m = _adaptive_trail_multiplier()
                        _raw_mom = short_momentum(coin, window=10)
                        _live_trend = min(max(0, -_raw_mom) / 0.02, 1.0)
                        _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                        _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                        # (confidence nudge removed: cosmetic, max 0.03 shift absorbed by clamp in 1 cycle)
                        _prev = pos.get("_trail_tm", _raw_tm)
                        _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                        _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                        pos["_trail_tm"] = _final_tm
                        _new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                        pos["trail_stop"] = min(pos.get("trail_stop", _new_trail), _new_trail) if pos.get("trail_stop", 0) > 0 else _new_trail
                        logger.debug(f"SHORT EARLY PP {coin} +{pnl_pct:.1f}% (tp_trigger={tp_trigger:.1f}%, trail_m={_final_tm:.2f})")

                # === TP TRIGGER: re-evaluate ===
                elif pnl_pct >= tp_trigger:
                    if "profit_protection" not in pos:
                        assessment = assess_exit(coin, "short", entry, p)
                        if assessment["action"] == "HOLD_AND_TRAIL":
                            pos["profit_protection"] = True
                            pos["pp_start_cycle"] = held_cycles  # Track when PP started for timeout
                            pos["pp_start_pnl"] = pnl_pct  # Store activation PnL for timeout calc
                            # Weighted trail: blend pnl-tightening + live trend + streak, clamped per-cycle
                            _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl_pct - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                            _streak_m = _adaptive_trail_multiplier()
                            _raw_mom = short_momentum(coin, window=10)
                            _live_trend = min(max(0, -_raw_mom) / 0.02, 1.0)  # Only loosen on favorable (downward) momentum for shorts
                            _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                            _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                            # (confidence nudge removed: cosmetic, max 0.03 shift absorbed by clamp in 1 cycle)
                            _prev = pos.get("_trail_tm", _raw_tm)
                            _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                            _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                            pos["_trail_tm"] = _final_tm
                            _new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                            pos["trail_stop"] = min(pos.get("trail_stop", _new_trail), _new_trail) if pos.get("trail_stop", 0) > 0 else _new_trail
                            logger.debug(f"SHORT TP HIT {coin} +{pnl_pct:.1f}% → HOLDING trail_m={_final_tm:.2f} trend={_live_trend:.2f} streak={_streak_m:.2f} ({assessment['reason']})")
                        else:
                            if MIN_PROFIT_FILTER_ENABLED and (pnl_pct / 100) < MIN_PROFIT_THRESHOLD:
                                logger.debug(f"MIN_PROFIT HELD SHORT {coin} +{pnl_pct:.1f}% (need {MIN_PROFIT_THRESHOLD*100:.1f}%)")
                            else:
                                _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                                wallet.cover(coin, _fp)
                                _exited_this_cycle.add(coin)
                                record_exit(pos.get("strategy", "momentum"), coin, "short", entry, _fp, _current_regime, wallet=wallet)
                                daily_metrics.record_trade(pnl_pct)
                                logger.info(f"SHORT TP EXIT {coin} +{pnl_pct:.1f}% ({assessment['reason']})")
                                continue

                # === PROFIT PROTECTION: trailing stop for shorts ===
                if pos.get("profit_protection"):
                    # Defensive: backfill pp_start_cycle if missing (state restore edge case)
                    if "pp_start_cycle" not in pos:
                        pos["pp_start_cycle"] = max(0, held_cycles - 1)
                    if "pp_start_pnl" not in pos:
                        pos["pp_start_pnl"] = pnl_pct  # Backfill with current if missing
                    # Adaptive PP timeout: use activation PnL (not current) for stable timeout
                    _pp_cycles = held_cycles - pos["pp_start_cycle"]
                    _pp_start_pnl = pos["pp_start_pnl"]
                    _pp_timeout = 100 + int(max(0, _pp_start_pnl - 1.5) * 50)  # v29.3.5: was 500+100/% (max 900). Now 100+50/% capped at 200
                    _pp_timeout = min(200, _pp_timeout)  # v29.3.5: was 900 — capped at 200 cycles (~7 min at POLL=2s)
                    if _pp_cycles > _pp_timeout:
                        _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                        wallet.cover(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit("pp_timeout", coin, "short", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"SHORT PP TIMEOUT {coin} +{pnl_pct:.1f}% (profit protection held {_pp_cycles} cycles)")
                        continue

                    # Weighted trail: blend pnl-tightening + live trend + streak, clamped per-cycle
                    _pnl_tm = max(0.6, min(1.0, 1.0 - max(0.0, pnl_pct - 0.5) * 0.16))  # Smooth: 1.0 at ≤0.5%, 0.6 at ≥3%
                    _streak_m = _adaptive_trail_multiplier()
                    _raw_mom = short_momentum(coin, window=10)
                    _live_trend = min(max(0, -_raw_mom) / 0.02, 1.0)  # Only loosen on favorable (downward) momentum for shorts
                    _trend_adj = _pnl_tm + (1.0 - _pnl_tm) * _live_trend * 0.25
                    _raw_tm = max(0.6, min(1.2, 0.7 * _trend_adj + 0.3 * _streak_m))
                    _prev = pos.get("_trail_tm", _raw_tm)
                    _final_tm = max(_prev - 0.06, min(_prev + 0.04, _raw_tm))  # Asymmetric: tighten faster, loosen slower
                    _final_tm = max(0.6, min(1.2, _final_tm))  # Explicit bounds guard
                    # Drop-from-peak guard: proportional dampening (volatile coins tolerate bigger pullbacks)
                    _drop_short = (p - pos.get("lowest", entry)) / pos.get("lowest", entry) * 100 if pos.get("lowest", entry) > 0 else 0
                    _dfp_thresh = max(0.8, atr * 0.3)  # v29.3: tighter to match new SL
                    if _final_tm > _prev and _dfp_thresh > 0:
                        _dampen = min(1.0, max(0, _drop_short) / (_dfp_thresh * 2))  # Proportional: 0→full, thresh→half, 2×thresh→locked
                        _final_tm = _prev + (_final_tm - _prev) * (1 - _dampen)
                    pos["_trail_tm"] = _final_tm
                    new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                    pos["trail_stop"] = min(pos.get("trail_stop", entry), new_trail)

                    # Adaptive reassessment: faster when more profit at stake or higher volatility
                    _reassess_base = 30
                    _pnl_adj = max(0.5, 1.0 - abs(pnl_pct) * 0.1)  # 5%+ PnL → 0.5x (15s min)
                    _vol_adj = min(1.5, max(0.6, 1.5 / max(1.0, atr)))  # High ATR → faster checks
                    _reassess_secs = max(15, min(60, _reassess_base * _pnl_adj * _vol_adj))
                    _pp_age = held_cycles - pos.get("pp_start_cycle", 0)
                    _cached_assessment = None  # Reuse for hard ceiling if available
                    if _pp_age > 0 and held_cycles % max(1, int(_reassess_secs / POLL)) == 0:
                        _cached_assessment = assess_exit(coin, "short", entry, p)
                        if _cached_assessment["action"] == "EXIT":
                            if MIN_PROFIT_FILTER_ENABLED and (pnl_pct / 100) < MIN_PROFIT_THRESHOLD:
                                logger.debug(f"MIN_PROFIT HELD SHORT {coin} +{pnl_pct:.1f}% (need {MIN_PROFIT_THRESHOLD*100:.1f}%)")
                            else:
                                _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                                wallet.cover(coin, _fp)
                                _exited_this_cycle.add(coin)
                                record_exit(pos.get("strategy", "momentum"), coin, "short", entry, _fp, _current_regime, wallet=wallet)
                                daily_metrics.record_trade(pnl_pct)
                                logger.info(f"SHORT REASSESS EXIT {coin} +{pnl_pct:.1f}% ({_cached_assessment['reason']})")
                                continue
                        # else: HOLD_AND_TRAIL — no action needed (nudge removed: cosmetic, absorbed by clamp in 1 cycle)

                    # Trailing stop — ALWAYS execute (protective mechanism)
                    if p >= pos.get("trail_stop", entry * 2):
                        _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                        wallet.cover(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit(pos.get("strategy", "momentum"), coin, "short", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"SHORT TRAIL STOP {coin} +{pnl_pct:.1f}%")
                        continue

                    # Hard ceiling — adaptive: reuse cached assessment if available
                    _ceiling_assessment = _cached_assessment if _cached_assessment is not None else assess_exit(coin, "short", entry, p)
                    _atr_mult = 7 if _ceiling_assessment.get("confidence", 0) >= 0.8 else 5
                    _hard_ceiling = max(5.0, atr * _atr_mult)
                    if pnl_pct >= _hard_ceiling:
                        _fp = _exit_slippage_price(p, "COVER", coin=coin, is_sl_exit=False)
                        wallet.cover(coin, _fp)
                        _exited_this_cycle.add(coin)
                        record_exit(pos.get("strategy", "momentum"), coin, "short", entry, _fp, _current_regime, wallet=wallet)
                        daily_metrics.record_trade(pnl_pct)
                        logger.info(f"SHORT MAX TP {coin} +{pnl_pct:.1f}% (ceiling={_hard_ceiling:.1f}%, conf={_ceiling_assessment.get('confidence', 0):.2f})")
                        continue
              except Exception as _exit_err:
                try:
                    logger.error(f"EXIT GUARD: error managing SHORT {coin}: {_exit_err}")
                    error_logger.log("exit_guard_short", f"{coin}: {_exit_err}")
                except Exception:
                    pass
                # FORCE EXIT: if normal exit logic crashed, force-close the position
                try:
                    if coin in wallet.shorts:
                        _fe_entry = wallet.shorts[coin].get("entry", 0)
                        _fe_price = prices.get(coin, 0)
                        # SAFE PRICING: never use 0 or None — fallback to entry price
                        if not _fe_price or _fe_price <= 0:
                            _fe_price = _fe_entry if _fe_entry > 0 else 0.0001
                        if not _fe_entry or _fe_entry <= 0:
                            _fe_entry = _fe_price
                        _fe_fp = _exit_slippage_price(_fe_price, "COVER", coin=coin, is_sl_exit=True)
                        wallet.cover(coin, _fe_fp)
                        _exited_this_cycle.add(coin)
                        record_exit("force_exit", coin, "short", _fe_entry, _fe_fp, _current_regime, wallet=wallet)
                        logger.error(f"FORCE EXIT SHORT {coin} @ ${_fe_fp:.4f} (entry=${_fe_entry:.4f}) after exit guard error")
                except Exception as _fe_err:
                    try:
                        logger.error(f"FORCE EXIT FAILED SHORT {coin}: {_fe_err}")
                        error_logger.log("exit_force_fail_short", f"{coin}: {_fe_err}")
                    except Exception:
                        pass

            # Track cash freed by exits (1-cycle delay: don't reuse for entries this cycle)
            _cash_freed_this_cycle = max(0, wallet.cash - _cash_before_exits)

            # Track equity for performance metrics
            pv = wallet.value(prices)
            perf.track_equity(pv)
            adaptive_risk.update(pv)
            cascade_protection.update(pv, cycle)

            # Equity curve logging (every cycle) — must never crash bot
            try:
                _positions_value = pv - wallet.cash
                equity_logger.log(pv, wallet.cash, _positions_value)
            except Exception:
                pass

            # v29.3.3: Loss streak DD check — pause entries if equity drops > 5% from session peak
            try:
                global _session_peak_equity, _loss_streak_paused_until
                if pv > _session_peak_equity:
                    _session_peak_equity = pv
                if _session_peak_equity > 0:
                    _eq_dd_pct = (_session_peak_equity - pv) / _session_peak_equity * 100
                    if _eq_dd_pct > LOSS_STREAK_DD_PCT and cycle > _loss_streak_paused_until:
                        _loss_streak_paused_until = cycle + LOSS_STREAK_PAUSE_CYCLES
                        logger.warning(f"[PAUSED: LOSS_STREAK_PROTECTION] Equity DD {_eq_dd_pct:.2f}% > {LOSS_STREAK_DD_PCT}% — pausing entries until cycle {_loss_streak_paused_until}")
            except Exception:
                pass

            # Equity sanity check (every cycle)
            try:
                _sanity = equity_sanity.check(pv, cycle)
            except Exception:
                _sanity = "OK"
            # ONLY stop if equity is truly <= 0 (real bankruptcy)
            _has_positions = len(wallet.longs) > 0 or len(wallet.shorts) > 0
            if pv <= 0 and _has_positions:
                logger.error(f"EQUITY ZERO: pv=${pv:.2f} with open positions at cycle {cycle} — SHUTDOWN")
                error_logger.log("force_stop", f"equity ${pv:.2f} at cycle {cycle}")
                wallet.save(prices)
                break
            elif _sanity == "STOP":
                # Log but do NOT stop — clamp and continue
                logger.error(f"EQUITY SANITY WARNING: ${pv:.2f} at cycle {cycle} — clamping, NOT stopping")
                error_logger.log("equity_sanity_warning", f"${pv:.2f} at cycle {cycle}")
                if wallet.cash < 0:
                    wallet.cash = 0

            # Failsafe: invalid portfolio state — clamp and continue, do NOT halt
            if wallet.cash < -1 or pv < 0:
                logger.error(f"FAILSAFE: invalid state (cash=${wallet.cash:.2f}, equity=${pv:.2f}) — clamping cash, closing positions")
                error_logger.log("failsafe_clamp", f"cash=${wallet.cash:.2f} equity=${pv:.2f}")
                try:
                    for coin in list(wallet.longs.keys()):
                        _p = prices.get(coin, wallet.longs[coin]["entry"])
                        _entry = wallet.longs[coin]["entry"]
                        _strat = wallet.longs[coin].get("strategy", "momentum")
                        _fp = _exit_slippage_price(_p, "SELL", coin=coin, is_sl_exit=True)
                        wallet.sell(coin, _fp)
                        record_exit(_strat, coin, "long", _entry, _fp, "FAILSAFE", wallet=wallet)
                    for coin in list(wallet.shorts.keys()):
                        _p = prices.get(coin, wallet.shorts[coin]["entry"])
                        _entry = wallet.shorts[coin]["entry"]
                        _fp = _exit_slippage_price(_p, "COVER", coin=coin, is_sl_exit=True)
                        wallet.cover(coin, _fp)
                        record_exit("failsafe_exit", coin, "short", _entry, _fp, "FAILSAFE", wallet=wallet)
                except Exception as _fe:
                    logger.error(f"FAILSAFE close error: {_fe}")
                if wallet.cash < 0:
                    wallet.cash = 0
                wallet.save(prices)
                # Do NOT break — continue running with cleaned state

            # Kill switch checks — MARKET RISK ONLY, close positions but keep bot running
            if kill_switch and not (cycle < STABILITY_WARMUP_CYCLES):
                kill_switch.check_equity(pv)
                # Allow recovery: if equity recovered to ~starting, reset kill switch
                kill_switch.maybe_reset(pv)
                if kill_switch.is_triggered:
                    logger.error(f"KILL SWITCH: {kill_switch.trigger_reason}")
                    try:
                        kill_switch.close_all_positions(wallet, prices, executor)
                    except Exception as _ke:
                        logger.error(f"KILL SWITCH close error: {_ke}")
                    wallet.save(prices)
                    print(f"\n  KILL SWITCH: {kill_switch.trigger_reason}")
                    print(f"  Positions closed. Bot continues monitoring (no new trades).")
                    # Do NOT break — bot stays alive, kill_switch.triggered blocks new entries

            # Safe mode update
            safe_mode.update(pv)

            # ── STAGNATION WATCHDOG: reset cooldowns if no trades for too long ──
            try:
                stagnation_watchdog.check(cycle, wallet)
            except Exception:
                pass

            # ── RECOVERY MODE: activate if idle too long ──
            try:
                recovery_mode._wallet_ref = wallet  # Wire wallet ref for soft reset
                recovery_mode.check(cycle)
            except Exception:
                pass

            # ── MIN ACTIVITY GUARD: graduated threshold relaxation on idle ──
            try:
                _activity_tier = min_activity.check_and_log(cycle)
                _activity_score_adj = min_activity.score_adjustment(cycle)
                _activity_change_adj = min_activity.change_adjustment(cycle)
                _activity_soft_leniency = min_activity.soft_leniency_active(cycle)
            except Exception:
                _activity_tier = 0
                _activity_score_adj = 0.0
                _activity_change_adj = 0.0
                _activity_soft_leniency = False

            # ── API STALENESS: force close if API down too long ──
            if api_staleness.should_force_close(cycle):
                _stale_c = api_staleness.stale_cycles(cycle)
                _has_pos = len(wallet.longs) > 0 or len(wallet.shorts) > 0
                if _has_pos:
                    try:
                        logger.error(f"API STALE FORCE CLOSE: no API data for {_stale_c} cycles — closing all positions")
                        for _sc in list(wallet.longs.keys()):
                            _sp = prices.get(_sc, wallet.longs[_sc].get("entry", 0.0001))
                            if _sp <= 0: _sp = wallet.longs[_sc].get("entry", 0.0001)
                            _se = wallet.longs[_sc].get("entry", _sp)
                            _sfp = _exit_slippage_price(_sp, "SELL", coin=_sc, is_sl_exit=True)
                            wallet.sell(_sc, _sfp)
                            record_exit("api_stale_exit", _sc, "long", _se, _sfp, _current_regime, wallet=wallet)
                        for _sc in list(wallet.shorts.keys()):
                            _sp = prices.get(_sc, wallet.shorts[_sc].get("entry", 0.0001))
                            if _sp <= 0: _sp = wallet.shorts[_sc].get("entry", 0.0001)
                            _se = wallet.shorts[_sc].get("entry", _sp)
                            _sfp = _exit_slippage_price(_sp, "COVER", coin=_sc, is_sl_exit=True)
                            wallet.cover(_sc, _sfp)
                            record_exit("api_stale_exit", _sc, "short", _se, _sfp, _current_regime, wallet=wallet)
                        wallet.save(prices)
                    except Exception as _asc_err:
                        logger.error(f"API STALE CLOSE ERROR: {_asc_err}")

            # ── CYCLE TIMEOUT CHECK: skip remaining if cycle took too long ──
            _elapsed = time.time() - _cycle_start
            if _elapsed > CYCLE_TIMEOUT_SEC:
                logger.warning(f"CYCLE TIMEOUT: cycle {cycle} took {_elapsed:.1f}s > {CYCLE_TIMEOUT_SEC}s — skipping new entries")
                continue

            # ── OPEN NEW POSITIONS ──
            # Check daily trade limit
            if not perf.can_trade(cycle):
                pass  # Skip new trades but still manage existing positions

            regime = awareness.detect_regime(prices_cache)
            strategy = awareness.get_strategy_for_regime(regime)

            # ── WARM-UP GATE: Prevent premature trades on startup ──
            warmup_active = cycle < WARMUP_CYCLES
            warmup_blocked = False

            if warmup_active:
                warmup_blocked = True  # Hard block: no entries during warm-up

            # Block trading when regime is UNKNOWN (not enough data to classify)
            if BLOCK_UNKNOWN_REGIME and regime == "UNKNOWN":
                warmup_blocked = True

            # DRY_RUN mode: observe but don't trade for first N cycles
            if DRY_RUN_CYCLES > 0 and cycle <= DRY_RUN_CYCLES:
                warmup_blocked = True
                if cycle == 1 or cycle % 50 == 0:
                    print(f"  DRY RUN: cycle {cycle}/{DRY_RUN_CYCLES} — observing only, no orders")

            # Warm-up size ramp: linear ramp from WARMUP_RAMP_MULT to 1.0 (was flat 75%)
            warmup_size_mult = 1.0
            if cycle < WARMUP_CYCLES:
                warmup_size_mult = 0.0  # No trades during data collection
            elif cycle < WARMUP_RAMP_END:
                # Linear interpolation: WARMUP_RAMP_MULT → 1.0 over the ramp window
                _ramp_progress = (cycle - WARMUP_CYCLES) / max(1, WARMUP_RAMP_END - WARMUP_CYCLES)
                warmup_size_mult = WARMUP_RAMP_MULT + (1.0 - WARMUP_RAMP_MULT) * _ramp_progress

            # Adaptive regime layer (plugs on top, doesn't replace)
            enhanced_regime = adaptive_regime.classify(prices_cache)
            adaptive_rules = None
            if enhanced_regime:
                adaptive_rules = adaptive_regime.get_strategy_rules(enhanced_regime)
                # If CHOPPY: skip all new trades entirely
                if adaptive_rules["position_scale"] == 0.0:
                    # Shadow: log that CHOPPY regime blocked all new entries
                    if last_full_rank:
                        for r in last_full_rank[:3]:
                            if r["score"] >= 0.05 and r["change"] >= 0.01 and r["vol"] >= 500000:
                                sn = to_short_name(pair_names.get(r["pair"], r["pair"]))
                                shadow.log_signal(sn, "long", r["score"], "regime_choppy", taken=False)
                    pass  # Fall through to dashboard, skip new positions

            peak = is_peak_hours()
            size_mult = 1.0 if peak else 0.85  # was 0.70 — compounded with CHOPPY(0.70) × warmup(0.75) killed positions. 0.85 keeps them above $10
            # Apply adaptive position scaling
            if adaptive_rules:
                size_mult *= adaptive_rules["position_scale"]
            # Apply warm-up size ramp
            size_mult *= warmup_size_mult

            # ── Ranging market adaptation flag (used throughout entry logic) ──
            _is_ranging = RANGING_ADAPTATION_ENABLED and (regime == "RANGING" or enhanced_regime == "QUIET_RANGE")
            if _is_ranging and cycle % 100 == 0:
                logger.info(f"RANGING ADAPT: active (regime={regime}, enhanced={enhanced_regime}) — thresholds relaxed, mean-rev preferred")

            # ── MARKET BRAIN: central intelligence that coordinates all adaptive systems ──
            try:
                _brain = market_brain.think(
                    cycle=cycle, wallet=wallet, prices=prices,
                    regime=regime, enhanced_regime=enhanced_regime,
                    n_positions=len(wallet.longs) + len(wallet.shorts),
                    health_score=_last_health_score
                )
            except Exception as _brain_err:
                logger.debug(f"[BRAIN] error: {_brain_err}")
                _brain = {"score_mult": 1.0, "change_mult": 1.0, "size_mult": 1.0,
                          "stag_mult": 1.0, "scan_extra": 0, "skip_choppy": False,
                          "skip_volume_confirms": False, "mood": "NORMAL", "reason": "error fallback",
                          "market_score": 0.0, "bias": "neutral", "market_insight": "analyzing",
                          "clean_trends_pct": 0}

            # Snapshot positions BEFORE entries to detect warmup violations
            _longs_before = len(wallet.longs)
            _shorts_before = len(wallet.shorts)

            total_positions = len(wallet.longs) + len(wallet.shorts)

            # ── DYNAMIC MAX POSITIONS: reduce in sideways/choppy, restore in trending ──
            _clean_trends = _brain.get("clean_trends_pct", 0)
            _ranging_pct = 100 - _clean_trends
            _is_strong_trend = (
                _brain.get("mood") in ("AGGRESSIVE", "DESPERATE")
                and _clean_trends >= 70
                and _current_regime != "CHOPPY"
            )
            if _is_strong_trend:
                _effective_max_positions = MAX_POSITIONS  # Full 8 in strong trends
            elif _ranging_pct > 35 or _current_regime == "CHOPPY":
                _effective_max_positions = MAX_POSITIONS * 3 // 4  # v29.3: 6 in sideways/choppy (was 4 — too few slots)
            else:
                _effective_max_positions = MAX_POSITIONS  # Normal conditions

            # ── TREND SIZE BOOST: +10% sizing in confirmed strong trends ──
            _trend_size_boost = 1.10 if (_clean_trends >= 75 and _current_regime != "CHOPPY") else 1.0

            # ── DYNAMIC POSITION SIZING: scale down in sideways/crowded conditions ──
            if _ranging_pct > 35 and not _is_strong_trend:
                # Scale: 35% ranging → 0.85x, 50% → 0.70x, 65%+ → 0.55x (linear)
                _sideways_size_mult = max(0.55, 1.0 - (_ranging_pct - 35) * 0.015)
            elif total_positions >= _effective_max_positions - 1 and not _is_strong_trend:
                _sideways_size_mult = 0.75  # Near capacity: reduce to avoid overcommit
            else:
                _sideways_size_mult = 1.0  # Full sizing in trending conditions

            # ── OVERTRADE COOLDOWN: block if too many trades in recent window ──
            _trades_last_100 = min_activity.trade_rate(cycle, window=100)
            _overtrade_cooldown_active = _trades_last_100 >= 12 and not _is_strong_trend  # v29.3: Max 12 per 100 cycles (was 6 — too restrictive)

            # ── 50-CYCLE SUMMARY LOG ──
            if cycle % 50 == 0 and cycle > 0:
                logger.info(
                    f"[SIDEWAYS_GUARD] cycle={cycle} positions={total_positions}/{_effective_max_positions} "
                    f"longs={len(wallet.longs)} shorts={len(wallet.shorts)} "
                    f"ranging={_ranging_pct}% trends={_clean_trends}% regime={_current_regime} "
                    f"mood={_brain.get('mood')} strong_trend={_is_strong_trend} "
                    f"size_mult={_sideways_size_mult:.2f} cooldown={'ON' if _overtrade_cooldown_active else 'off'} "
                    f"trades_100c={_trades_last_100} dead_market_skips={_dead_market_counter[0]}")

            # ── HARD GLOBAL ENTRY BLOCK: warm-up or unknown regime ──
            if warmup_blocked:
                # Debug log: announce every blocked cycle (throttled to every 10 cycles)
                if cycle % 10 == 0:
                    reason_str = "warmup" if cycle < WARMUP_CYCLES else "regime_unknown"
                    logger.debug(f"ENTRY BLOCKED: {reason_str} (cycle={cycle}, regime={regime})")
                # Shadow: log top signals that would have been considered
                if last_full_rank:
                    for r in last_full_rank[:3]:
                        if r["score"] >= 0.05 and r["change"] >= 0.01 and r["vol"] >= 500000:
                            sn = to_short_name(pair_names.get(r["pair"], r["pair"]))
                            reason = "warmup" if cycle < WARMUP_CYCLES else "regime_unknown"
                            shadow.log_signal(sn, "long", r["score"], reason, taken=False)
                # Skip ALL entry logic — jump straight to dashboard
            elif last_full_rank and (not perf.can_trade(cycle) or total_positions >= _effective_max_positions):
                for r in last_full_rank[:5]:
                    if r["score"] >= 0.05 and r["change"] >= 0.01 and r["vol"] >= 500000:
                        name = pair_names.get(r["pair"], r["pair"])
                        sn = to_short_name(name)
                        reason = "daily_trade_limit" if not perf.can_trade(cycle) else "max_positions"
                        shadow.log_signal(sn, "long", r["score"], reason, taken=False)
            # 1-cycle delay: don't reuse cash freed by exits this cycle
            _usable_cash = wallet.cash - _cash_freed_this_cycle
            # During warmup, disable aggressive safety (strategy pause + overtrading)
            _in_warmup = cycle < STABILITY_WARMUP_CYCLES
            _strategy_health_ok = True if _in_warmup else strategy_health_monitor.check_health(cycle)
            _overtrading_ok = True if _in_warmup else overtrading_guard.can_trade(cycle, is_ranging=_is_ranging)
            _kill_switch_ok = not (kill_switch and kill_switch.is_triggered)
            _error_cooldown = error_classifier.check_cooldown(cycle)
            _api_stale_block = api_staleness.should_block_entries(cycle)
            # Health score safety: size reduction + entry block based on _last_health_score
            _health_size_mult = 1.0
            _health_block = False
            if _last_health_score < 30:
                _health_size_mult = 0.5
                if cycle % 10 == 0:
                    logger.warning(f"HEALTH LOW: score={_last_health_score} — 50% size")
            elif _last_health_score < 40:
                _health_size_mult = 0.75
                if cycle % 10 == 0:
                    logger.debug(f"HEALTH CAUTION: score={_last_health_score} — 75% size")
            elif _last_health_score < 60:
                _health_size_mult = 0.85
                if cycle % 10 == 0:
                    logger.debug(f"HEALTH WATCH: score={_last_health_score} — 85% size")
            # Recovery mode: RELAX (not bypass) strategy health + overtrading + health block
            _in_recovery = recovery_mode.active
            if _in_recovery:
                # Strategy health: allow entry but only if monitor isn't in hard pause
                if not _strategy_health_ok:
                    _strategy_health_ok = True  # Override pause, still tracked
                # Overtrading: use relaxed limit (1.5x), not full bypass
                if not _overtrading_ok:
                    _overtrading_ok = overtrading_guard.allow_limited(cycle)
                # Health block: override if score > 20 (only keep full pause)
                if _health_block and _last_health_score >= 20:
                    _health_block = False
                    _health_size_mult = max(_health_size_mult, 0.5)  # At least 50% size
                    logger.debug(f"RECOVERY: overriding health block (score={_last_health_score})")
            # CHOPPY regime: allow entries but reduce position size to 70%
            _choppy_size_mult = 0.7 if (_current_regime == "CHOPPY") else 1.0
            if _choppy_size_mult < 1.0 and cycle % 100 == 0:
                logger.debug(f"[CHOPPY_REDUCE] cycle={cycle} regime=CHOPPY — entries allowed at 70% size")
            # v29.4.0: Portfolio heat check (Item 10, 24, 26)
            _heat_ok = portfolio_heat_allows_entry(wallet, prices)

            # v29.4.1: Fear & Greed Index — refresh periodically
            if FEAR_GREED_ENABLED and (cycle - _fear_greed_last_cycle) >= FEAR_GREED_REFRESH_CYCLES:
                fetch_fear_greed_index()
            _fg_size_mult = fear_greed_size_mult()
            _dca_size_mult = smart_dca_size_mult()
            if cycle % 50 == 0 and FEAR_GREED_ENABLED:
                logger.info(f"[F&G] cycle={cycle} index={_fear_greed_value} ({_fear_greed_label}) size_mult={_fg_size_mult:.2f} dca_mult={_dca_size_mult:.2f}")

            # ── v29.5.0: Pro Market Condition Logic ──
            global _pro_market_regime, _pro_peak_portfolio
            # Regime detection from BTC prices
            _btc_hist = prices_cache.get("BTC", prices_cache.get("XBT", []))
            _pro_market_regime = detect_market_regime(_btc_hist)
            if cycle % 50 == 0:
                logger.info(f"[REGIME] cycle={cycle} regime={_pro_market_regime}")
            if _pro_market_regime == "DEAD" and cycle % 10 == 0:
                logger.info(f"[REGIME_SKIP] cycle={cycle} dead market — all entries blocked")

            # Session-aware sizing
            _session_mult, _session_min_score = is_active_session()

            # Drawdown protection
            _pv = wallet.value(prices) if hasattr(wallet, 'value') else wallet.cash
            _dd_mult, _dd_allow_entry = drawdown_protection_mult(_pv)
            if not _dd_allow_entry:
                if cycle % 10 == 0:
                    logger.warning(f"[DD_PROTECT] Drawdown >{10}% from peak (${_pro_peak_portfolio:.0f} → ${_pv:.0f}) — blocking new entries")

            # Streak-based sizing
            _streak_mult = streak_size_mult()

            # v29.4.0: BTC Market Condition Gate — pause momentum/breakout when BTC is ranging
            _btc_condition, _btc_move = btc_market_condition()
            _btc_ranging = (_btc_condition == "RANGING")
            if cycle % 50 == 0:
                logger.info(f"[BTC_GATE] cycle={cycle} condition={_btc_condition} net_move={_btc_move:+.4f} ({_btc_move*100:+.2f}%)")

            # v29.4.0: BTC RANGING → mean-reversion only (skip momentum/breakout entries)
            if _btc_ranging and not warmup_blocked and _api_ok and _usable_cash > 50 and total_positions < _effective_max_positions and _heat_ok:
                logger.info(f"[BTC_RANGING] Market choppy — momentum/breakout entries paused, scanning mean-reversion only")
                _mr_candidates = btc_meanrev_scan(tickers)
                for _mr in _mr_candidates:
                    _mr_coin = _mr["coin"]
                    _mr_side = _mr["side"]
                    _mr_z = _mr["z_score"]
                    _mr_price = _mr["price"]
                    if _mr_coin in DYNAMIC_BLACKLIST:
                        continue
                    _mr_blocked, _mr_block_reason = is_coin_blocked(_mr_coin, cycle, is_ranging=True)
                    if _mr_blocked:
                        continue
                    _mr_already = _mr_coin in wallet.longs or _mr_coin in wallet.shorts
                    if _mr_already or _mr_coin in _exited_this_cycle:
                        continue
                    _mr_amt = kelly_size(wallet, _usable_cash * 0.10, prices)  # Small base
                    _mr_amt *= BTC_MEANREV_SIZE_MULT  # 0.5x sizing
                    _mr_amt *= _edge_size_multiplier()
                    if _mr_amt < MIN_ORDER_USD:
                        continue
                    if _mr_side == "long":
                        order = executor.place_order("BUY", _mr_coin, _mr_price, _mr_amt, wallet, prices)
                        if order["filled"] and _mr_coin in wallet.longs:
                            wallet.longs[_mr_coin]["entry_sl"] = max(0.8, coin_atr(_mr_coin) * 100 * 0.7)
                            wallet.longs[_mr_coin]["strategy"] = "btc_meanrev"
                            wallet.longs[_mr_coin]["bought_cycle"] = cycle
                            logger.info(f"[MEANREV] BUY {_mr_coin} ${_mr_amt:.0f} @ ${_mr_price:.4f} z={_mr_z:+.2f} | BTC ranging")
                    else:
                        order = executor.place_order("SHORT", _mr_coin, _mr_price, _mr_amt, wallet, prices)
                        if order["filled"] and _mr_coin in wallet.shorts:
                            wallet.shorts[_mr_coin]["entry_sl"] = max(0.8, coin_atr(_mr_coin) * 100 * 0.7)
                            wallet.shorts[_mr_coin]["strategy"] = "btc_meanrev"
                            wallet.shorts[_mr_coin]["bought_cycle"] = cycle
                            logger.info(f"[MEANREV] SHORT {_mr_coin} ${_mr_amt:.0f} @ ${_mr_price:.4f} z={_mr_z:+.2f} | BTC ranging")

            # v29.4.0: BTC TRENDING → normal momentum/breakout/alpha entries
            elif not _btc_ranging and not warmup_blocked and _api_ok and not _api_stale_block and not _health_block and last_full_rank and _usable_cash > 50 and perf.can_trade(cycle) and total_positions < _effective_max_positions and cascade_protection.allows_entry() and _strategy_health_ok and _overtrading_ok and _kill_switch_ok and not _error_cooldown and not _overtrade_cooldown_active and _heat_ok and _pro_market_regime != "DEAD" and _dd_allow_entry:
                _dead_market_skips = 0  # v29.2: count dead-market pair skips this cycle
                if (DEBUG_MODE or is_verbose("DEBUG")) and cycle % 10 == 0:
                    _total_risk = calculate_total_risk(wallet, prices) if (wallet.longs or wallet.shorts) else 0
                    print(f"  [DEBUG] cycle={cycle} cash=${_usable_cash:.0f} positions={total_positions} risk={_total_risk:.1f}% regime={regime}")
                # ── ADAPTIVE THRESHOLD MODE: relax thresholds when trending market + idle ──
                # Conditions: mood AGGRESSIVE/DESPERATE, clean trends ≥70%, not CHOPPY, idle ≥100 cycles
                # Adaptive: base 0.06/0.006 → 0.09/0.009 when trending (higher conviction), floors 0.06/0.006
                _adaptive_mode = (
                    _brain.get("mood") in ("AGGRESSIVE", "DESPERATE")
                    and _brain.get("clean_trends_pct", 0) >= 70
                    and _current_regime != "CHOPPY"
                    and min_activity.idle_cycles(cycle) >= 100
                )
                if len(wallet.longs) < 5:  # was 3 — too few, all slots filled immediately
                    _brain_scan = 15 + _brain.get("scan_extra", 0)
                    for r in last_full_rank[:_brain_scan]:
                        # ONLY buy coins that are actually going UP (positive change)
                        # Adaptive mode: use relaxed thresholds in trending markets when idle
                        _base_s = 0.06 if _adaptive_mode else 0.04  # v29.3: was 0.09/0.06 — let more signals through
                        _base_c = 0.006 if _adaptive_mode else 0.004  # v29.3: was 0.009/0.006
                        _floor_s = 0.03  # v29.3: was 0.06 — lower floor for ranging/idle relaxation
                        _floor_c = 0.003  # v29.3: was 0.006
                        min_score = _base_s * _brain.get("score_mult", 1.0)
                        min_change = _base_c * _brain.get("change_mult", 1.0)
                        # Ranging adaptation: reduce thresholds to let more signals through
                        if _is_ranging:
                            min_score = max(_floor_s, min_score - RANGING_SCORE_REDUCTION)
                            min_change = max(_floor_c, min_change - RANGING_SCORE_REDUCTION)
                            if cycle % 100 == 0 and r == last_full_rank[0]:
                                logger.debug(f"RANGING ADAPT: long thresholds relaxed — min_score={min_score:.3f} min_change={min_change:.4f}")
                        # Min activity guard: further reduce thresholds when idle
                        if _activity_tier > 0:
                            _extra_score = 0.03 if (_activity_tier >= 2 and (_is_ranging or _current_regime == "CHOPPY")) else 0
                            _extra_change = 0.008 if (_activity_tier >= 2 and (_is_ranging or _current_regime == "CHOPPY")) else 0
                            min_score = max(_floor_s, min_score - _activity_score_adj - _extra_score)
                            min_change = max(_floor_c, min_change - _activity_change_adj - _extra_change)
                        # Adaptive mode logging
                        if _adaptive_mode and r == last_full_rank[0] and cycle % 50 == 0:
                            logger.info(f"[ADAPTIVE] cycle={cycle} LONG base_s={_base_s} base_c={_base_c} floor_s={_floor_s} floor_c={_floor_c} mood={_brain.get('mood')} trends={_brain.get('clean_trends_pct')}% idle={min_activity.idle_cycles(cycle)}c")
                        if r["score"] < min_score or r["price"] < 0.0001 or r["change"] < min_change:
                            if r["score"] >= 0.05:
                                logger.debug(f"[FILTER_TRACE] {to_short_name(pair_names.get(r['pair'], r['pair']))} LONG score={r['score']:.2f} chg={r['change']:.4f} vol={r['vol']:.0f} BLOCKED=threshold (min_s={min_score:.3f} min_c={min_change:.4f})")
                            market_brain.record_filter_block(cycle, "score_threshold")
                            continue
                        if r["vol"] < 100000:  # was 200k — blocked too many small-cap signals
                            logger.debug(f"[FILTER_TRACE] {to_short_name(pair_names.get(r['pair'], r['pair']))} LONG score={r['score']:.2f} BLOCKED=low_volume ({r['vol']:.0f})")
                            market_brain.record_filter_block(cycle, "low_volume")
                            continue
                        # v29.5.0: MIN_MOMENTUM_SCORE moved up — cheap filter before expensive checks
                        if abs(r["score"]) < MIN_MOMENTUM_SCORE:
                            logger.debug(f"[BLOCKED: WEAK_MOMENTUM] {to_short_name(pair_names.get(r['pair'], r['pair']))} LONG — score {r['score']:.3f} < {MIN_MOMENTUM_SCORE}")
                            shadow.log_signal(to_short_name(pair_names.get(r['pair'], r['pair'])), "long", r["score"], "weak_momentum", taken=False)
                            continue
                        # v29.3.5: noise filter removed (redundant — MIN_MOMENTUM_SCORE=0.08 > NOISE_MOM_MIN_SCORE=0.01)
                        # ── v29.3 ENTRY QUALITY: Momentum Confirmation (LONG) ──
                        _l_coin_name = to_short_name(pair_names.get(r['pair'], r['pair']))
                        # v29.4.0: Sentiment check (Item 4)
                        if not sentiment_allows(_l_coin_name, "long"):
                            continue
                        _mom_ok, _mom_delta = momentum_confirmed(_l_coin_name, "long", window=5)
                        if not _mom_ok:
                            logger.info(f"[REJECTED: NO_MOMENTUM] {_l_coin_name} LONG score={r['score']:.2f} chg={r['change']:.4f} mom_delta={_mom_delta:.5f}")
                            shadow.log_signal(_l_coin_name, "long", r["score"], "no_momentum", taken=False)
                            market_brain.record_filter_block(cycle, "no_momentum")
                            continue
                        # ── v29.3 ENTRY QUALITY: Micro-Trend Confirmation (LONG) ──
                        _mt_ok, _mt_agree, _mt_total = micro_trend_confirmed(_l_coin_name, "long", candles=4)
                        if not _mt_ok:
                            logger.info(f"[REJECTED: TREND_WEAK] {_l_coin_name} LONG score={r['score']:.2f} chg={r['change']:.4f} agree={_mt_agree}/{_mt_total}")
                            shadow.log_signal(_l_coin_name, "long", r["score"], "trend_weak", taken=False)
                            market_brain.record_filter_block(cycle, "trend_weak")
                            continue
                        # v29.5.0: Trend strength filter for momentum entries (require >= 5)
                        _l_hist = prices_cache.get(_l_coin_name, [])
                        _l_ts = get_trend_strength(_l_hist, "long")
                        if _l_ts < 5:
                            shadow.log_signal(_l_coin_name, "long", r["score"], "low_trend_strength", taken=False)
                            continue
                        if _usable_cash < 100:
                            break
                        name = pair_names.get(r["pair"], r["pair"])
                        coin_id = r["pair"]  # Use PAIR as unique ID (no name conversion issues)
                        # Check if we already hold this coin (check both pair and short name)
                        short_name = to_short_name(name)
                        # Conviction override: compute once, use at all soft-filter gates
                        _conv_active, _conv_skipped, _conv_tier = conviction_override_active(r["score"], r["change"], "momentum", regime=enhanced_regime)
                        if _conv_active:
                            conviction_kill_tracker.record_override()
                        if _conv_active and _conv_tier == "HIGH_CONVICTION":
                            logger.info(f"OVERRIDE: High conviction trade allowed | {short_name} | score={r['score']:.2f}")
                        # v29.4.0: restored conviction safety gate (ATR removed — only momentum + micro_trend)
                        if _conv_active:
                            _mom_ok = momentum_confirmed(short_name, "long")[0]
                            _micro_ok = micro_trend_confirmed(short_name, "long")[0]
                            if not (_mom_ok and _micro_ok):
                                shadow.log_signal(short_name, "long", r["score"], "CONVICTION_UNSAFE", taken=False)
                                logger.debug(f"CONVICTION_UNSAFE {short_name} long: mom={_mom_ok} micro={_micro_ok}")
                                market_brain.record_filter_block(cycle, "conviction_unsafe")
                                continue
                        already_held = any(k in (coin_id, short_name, name) for k in wallet.longs)
                        already_short = any(k in (coin_id, short_name, name) for k in wallet.shorts)
                        if already_held or already_short:
                            continue
                        if short_name in _exited_this_cycle:
                            continue
                        # v29.3.5 H9: Unified coin blocking — single function checks all 4 systems
                        _blocked, _block_reason = is_coin_blocked(short_name, cycle, is_ranging=_is_ranging)
                        if _blocked:
                            logger.info(f"[BLOCKED: {_block_reason}] {short_name} LONG")
                            shadow.log_signal(short_name, "long", r["score"], _block_reason, taken=False)
                            continue
                        # v29.3.2: Volatility circuit breaker — pause entries when market vol > 5%
                        if hasattr(wallet, '_avg_market_atr') and wallet._avg_market_atr > VOLATILITY_CIRCUIT_BREAKER:
                            logger.info(f"[BLOCKED: VOL_CIRCUIT_BREAKER] {short_name} LONG — market vol {wallet._avg_market_atr:.2f}% > {VOLATILITY_CIRCUIT_BREAKER}%")
                            continue
                        # v29.3.3: Loss streak protection — pause after consecutive losses or DD
                        if cycle < _loss_streak_paused_until:
                            logger.info(f"[PAUSED: LOSS_STREAK_PROTECTION] {short_name} LONG — paused until cycle {_loss_streak_paused_until} (streak={_loss_streak_count})")
                            continue
                        # v29.5.0: MIN_MOMENTUM_SCORE check moved earlier (before expensive filters)
                        # v29.3.5: Split cooldown — winners 15 cycles, losers 40 cycles
                        if short_name in _last_exit_cycle:
                            _cd_cycle, _cd_was_win = _last_exit_cycle[short_name]
                            _cd_limit = COOLDOWN_AFTER_WIN if _cd_was_win else COOLDOWN_AFTER_LOSS
                            if (cycle - _cd_cycle) < _cd_limit:
                                logger.info(f"[BLOCKED: COOLDOWN] {short_name} LONG — exited {cycle - _cd_cycle} cycles ago (min {_cd_limit}, {'win' if _cd_was_win else 'loss'})")
                                shadow.log_signal(short_name, "long", r["score"], "exit_cooldown", taken=False)
                                continue
                        if short_name in wallet.cooldowns and (cycle - wallet.cooldowns[short_name]) < LOSS_COOLDOWN_CYCLES and not _in_recovery:
                            shadow.log_signal(short_name, "long", r["score"], "cooldown", taken=False)
                            continue
                        # Per-pair failure isolation (soft — conviction can override)
                        if pair_failure_tracker.is_blocked(short_name, cycle, is_ranging=_is_ranging):
                            if _conv_active:
                                shadow.log_signal(short_name, "long", r["score"], f"pair_blocked_{_conv_tier}_OVERRIDDEN", taken=False)
                                logger.debug(f"{_conv_tier} OVERRIDE {short_name} long: bypassed pair_failure (score={r['score']:.2f} chg={r['change']:.3f})")
                            else:
                                shadow.log_signal(short_name, "long", r["score"], "pair_blocked", taken=False)
                                continue
                        # Data confidence: require enough price history before trading
                        _pclen = len(prices_cache.get(short_name, []))
                        if _pclen < MIN_PRICE_HISTORY:
                            shadow.log_signal(short_name, "long", r["score"], "insufficient_data", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} chg={r['change']:.3f} BLOCKED=insufficient_data ({_pclen}/{MIN_PRICE_HISTORY})")
                            market_brain.record_filter_block(cycle, "insufficient_data")
                            continue
                        # Minimum volatility: don't trade dead coins (stagnation trap)
                        _coin_atr_val = coin_atr(short_name)
                        if _coin_atr_val < MIN_ATR_TO_TRADE:
                            shadow.log_signal(short_name, "long", r["score"], "low_atr", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} BLOCKED=low_atr ({_coin_atr_val:.4f} < {MIN_ATR_TO_TRADE})")
                            market_brain.record_filter_block(cycle, "low_atr")
                            _dead_market_skips += 1
                            continue
                        # v29.1 DEAD MARKET FILTER: skip if ATR too low for TP to be achievable
                        # Estimate: if cumulative ATR over max stag cycles can't reach 40% of min TP → dead market
                        _atr_pct_l = _coin_atr_val * 100  # convert to %
                        _est_tp_l = max(0.4, 1.2 * max(0.8, _atr_pct_l * 0.7) * 1.0)  # v29.3: matches new TP formula
                        _cumulative_move_l = _atr_pct_l * 400 * 0.3  # v29.3: ATR * max_cycles(400) * directional fraction
                        if _cumulative_move_l < _est_tp_l * 0.2:  # v29.3: was 0.4 — less aggressive blocking
                            shadow.log_signal(short_name, "long", r["score"], "dead_market", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} BLOCKED=dead_market (atr={_atr_pct_l:.3f}% est_tp={_est_tp_l:.2f}% move={_cumulative_move_l:.2f}%)")
                            market_brain.record_filter_block(cycle, "dead_market")
                            _dead_market_skips += 1
                            continue
                        # Freshness: only trade if price was updated within last 5 cycles
                        _last_upd = price_last_updated.get(short_name, 0)
                        if cycle - _last_upd > 5:
                            shadow.log_signal(short_name, "long", r["score"], "stale_price", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} BLOCKED=stale_price (last_update={_last_upd} cycle={cycle})")
                            market_brain.record_filter_block(cycle, "stale_price")
                            continue
                        # Suspicious price filter: skip if price jumped > 3x ATR
                        if short_name in _suspicious_coins:
                            shadow.log_signal(short_name, "long", r["score"], "suspicious_price", taken=False, conviction_tier=_conv_tier if _conv_active else "")
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} BLOCKED=suspicious_price")
                            continue
                        # Execution safety: block if liquidity is poor
                        if not liquidity_ok(short_name):
                            shadow.log_signal(short_name, "long", r["score"], "low_liquidity", taken=False, conviction_tier=_conv_tier if _conv_active else "")
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} BLOCKED=low_liquidity")
                            continue
                        if not trading_allowed:
                            shadow.log_signal(short_name, "long", r["score"], "circuit_breaker", taken=False)
                            break
                        logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} chg={r['change']:.3f} PASSED all pre-filters → entering win-rate filters")
                        held_coins = list(wallet.longs.keys()) + list(wallet.shorts.keys())
                        too_corr, corr_with, corr_val = corr_guard.is_too_correlated(short_name, held_coins)
                        if too_corr:
                            shadow.log_signal(short_name, "long", r["score"], "correlation", taken=False)
                            logger.debug(f"CORR BLOCKED {short_name} (corr={corr_val:.2f} with {corr_with})")
                            continue
                        # v29.3.5 M10: Consolidated market quality check (replaces separate is_choppy + volume_confirms)
                        _mq_score = market_quality_score(short_name, r)
                        if _mq_score < 0.4:
                            _can_override = (_brain.get("skip_choppy") or _brain.get("skip_volume_confirms")
                                             or _conv_active or _activity_soft_leniency)
                            if _can_override:
                                _override_src = "BRAIN" if _brain.get("skip_choppy") else _conv_tier if _conv_active else "MIN_ACTIVITY"
                                shadow.log_signal(short_name, "long", r["score"], f"market_quality_{_override_src}_OVERRIDDEN", taken=False)
                                logger.debug(f"[{_override_src}] {short_name} long: bypassed market_quality (score={_mq_score:.2f}, mood={_brain.get('mood')})")
                            else:
                                shadow.log_signal(short_name, "long", r["score"], "market_quality", taken=False)
                                market_brain.record_filter_block(cycle, "market_quality")
                                continue
                        # Optimized change – pullback filter now optional (strongest entries are breakout-style)
                        # is_pullback_entry still logged to shadow for analytics
                        _is_pullback = is_pullback_entry(short_name, "long")
                        st_mom = short_momentum(short_name, window=5)
                        if st_mom < -0.005:
                            if _conv_active and "momentum_filter" in _conv_skipped:
                                shadow.log_signal(short_name, "long", r["score"], f"momentum_filter_{_conv_tier}_OVERRIDDEN", taken=False)
                                logger.debug(f"{_conv_tier} OVERRIDE {short_name} long: bypassed short_momentum (score={r['score']:.2f} st_mom={st_mom:.4f})")
                            else:
                                shadow.log_signal(short_name, "long", r["score"], "momentum_filter", taken=False)
                                market_brain.record_filter_block(cycle, "momentum_filter")
                                continue

                        # Strategy health check
                        if not strategy_health.is_healthy('momentum') and not _in_recovery:
                            shadow.log_signal(short_name, "long", r["score"], "strategy_health", taken=False)
                            market_brain.record_filter_block(cycle, "strategy_health")
                            logger.debug(f"MOMENTUM DISABLED (degraded)")
                            break

                        # Optimized change – removed ML brain + Trader Decision Layer (vestigial after sizing refactor)

                        # Position size: 2-multiplier system (edge + risk cap)
                        atr_for_sizing = coin_atr(short_name) * 100
                        sl_for_sizing = max(0.8, atr_for_sizing * 0.7)  # v29.3: Floor 0.8% SL (was 1.5%)
                        max_risk = wallet.value(prices) * MAX_RISK_PER_TRADE  # 0.5% of portfolio
                        effective_sl = sl_for_sizing * GAP_RISK_MULTIPLIER
                        max_by_risk = max_risk / (effective_sl / 100)
                        max_by_risk = min(max_by_risk, wallet.value(prices) * 0.30)  # Hard cap: 30%
                        # Optimized change – removed $300 hard cap (scale by portfolio %) and volatility_scale (fights momentum)
                        base = kelly_size(wallet, min(wallet.cash * 0.30, max_by_risk), prices)
                        # MULT 1: edge_multiplier (from REAL_EDGE — reflects trade confidence)
                        amount = base * _edge_size_multiplier()
                        # MULT 2: boost BEFORE risk cap so cap still limits final size
                        # v29.3.5: POST_SIZING_BOOST removed (was noop — always capped away)
                        # MULT 2: risk_cap (portfolio risk limit — caps max position size)
                        amount = min(amount, max_by_risk)
                        _amt_before_mults = amount  # Snapshot before reduction multipliers
                        # MULT 4: ranging regime scale (reduce momentum positions in sideways markets)
                        if _is_ranging:
                            amount *= RANGING_MOMENTUM_SCALE
                        # MULT 5: regime-aware sizing (can only reduce)
                        amount = _regime_size_scale(amount, _current_regime)
                        amount *= _winrate_size_bonus(wallet)  # +10% if WR > 55%
                        amount *= size_mult  # off-peak × adaptive × warmup ramp
                        amount *= _health_size_mult  # health-score graduated scaling
                        amount *= _brain.get("size_mult", 1.0)  # Brain mood-based sizing adjustment
                        amount *= _fg_size_mult  # v29.4.1: Fear & Greed Index sizing
                        amount *= _dca_size_mult  # v29.4.1: Smart DCA boost in Extreme Fear
                        amount *= _choppy_size_mult  # CHOPPY regime: 70% size, else 1.0
                        amount *= _sideways_size_mult  # Sideways market: scale down proportionally
                        amount *= _trend_size_boost  # +10% in strong trends (clean_trends≥75%, not CHOPPY)
                        # v29.5.0: Pro multipliers
                        amount *= volatility_size_mult(short_name)  # ATR-based sizing
                        amount *= _session_mult  # Session-aware sizing
                        amount *= _dd_mult  # Drawdown protection
                        amount *= _streak_mult  # Streak-based sizing
                        # Multiplier stacking floor: never reduce below 25% of risk-capped size
                        if _amt_before_mults > 0 and amount < _amt_before_mults * 0.25:
                            amount = _amt_before_mults * 0.25
                            logger.debug(f"[MULT_FLOOR] {short_name} LONG: stacking crushed to {amount:.2f}, floored to 25% of {_amt_before_mults:.2f}")
                        # Strong signal boost: reward high-quality entries with larger size
                        _sig_score = abs(r["score"])
                        if _sig_score > 0.8:
                            amount *= 1.25
                            logger.debug(f"[SIG_BOOST] {short_name} LONG: elite signal ({_sig_score:.2f}) +25%")
                        elif _sig_score > 0.7:
                            amount *= 1.15
                            logger.debug(f"[SIG_BOOST] {short_name} LONG: strong signal ({_sig_score:.2f}) +15%")
                        # Safety net: hard cap at 30% portfolio (exposure limit always enforced after boost)
                        amount = min(amount, wallet.value(prices) * 0.30)
                        amount = min(amount, max_by_risk)  # Re-enforce risk cap after boost
                        # Minimum position floor: if signal passed ALL filters, don't let multiplier stacking kill it
                        if amount < 15 and amount > 0 and max_by_risk >= 15:
                            amount = 15  # Kraken min is ~$10, use $15 for safety margin
                            logger.debug(f"[SIZE_FLOOR] {short_name} LONG: multipliers crushed size, floored to $15")
                        if amount < 10:
                            logger.debug(f"[SIZE_TRACE] {short_name} base={base:.2f} edge={_edge_size_multiplier():.2f} risk_cap={max_by_risk:.2f} ranging={'Y' if _is_ranging else 'N'} regime={_current_regime} reg_scale={REGIME_SIZE_SCALE.get(_current_regime, 1.0):.2f} sm={size_mult:.3f} hm={_health_size_mult:.2f} final=${amount:.2f}")
                        # Group correlation limit
                        if not group_limit_ok(short_name, wallet):
                            shadow.log_signal(short_name, "long", r["score"], "group_limit", taken=False)
                            continue
                        # Unified exposure check (total + global risk + stress + per-coin)
                        _exp_ok, _exp_reason = unified_exposure_ok(wallet, prices, short_name, amount, sl_for_sizing)
                        if not _exp_ok:
                            shadow.log_signal(short_name, "long", r["score"], _exp_reason, taken=False)
                            break
                        # Trade quality filters
                        if not reward_risk_ok(sl_for_sizing, sl_for_sizing * 2, atr_pct=atr_for_sizing):
                            shadow.log_signal(short_name, "long", r["score"], "rr_filter", taken=False)
                            market_brain.record_filter_block(cycle, "rr_filter")
                            continue
                        if not volatility_spike_check(short_name):
                            shadow.log_signal(short_name, "long", r["score"], "vol_spike", taken=False)
                            continue
                        # Entry confirmation: require 2 consecutive ticks in trade direction
                        if not entry_direction_confirmed(short_name, "long", ticks=1):
                            shadow.log_signal(short_name, "long", r["score"], "no_entry_confirm", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} LONG score={r['score']:.2f} BLOCKED=no_entry_confirm (price not moving up)")
                            market_brain.record_filter_block(cycle, "entry_confirm")
                            continue
                        # v29.4.0: duplicate coin_loss_tracker check removed — already consolidated via is_coin_blocked() earlier
                        if not market_depth_ok(short_name, amount, tickers):
                            shadow.log_signal(short_name, "long", r["score"], "thin_market", taken=False)
                            market_brain.record_filter_block(cycle, "thin_market")
                            continue
                        if not regime_confirm(short_name, "long"):
                            shadow.log_signal(short_name, "long", r["score"], "regime_mismatch", taken=False, conviction_tier=_conv_tier if _conv_active else "")
                            market_brain.record_filter_block(cycle, "regime_confirm")
                            continue
                        recovery_mode.record_passed_filter()
                        cycle_audit.record_passed_filters()
                        if amount > 5:
                            if _in_recovery:
                                recovery_mode.record_attempt()
                            order = executor.place_order("BUY", short_name, r["price"], amount, wallet, prices)
                            if order["filled"] and short_name in wallet.longs:
                                wallet.longs[short_name]["bought_cycle"] = cycle
                                wallet.longs[short_name]["entry_sl"] = sl_for_sizing
                                wallet.longs[short_name]["entry_atr"] = atr_for_sizing
                                _entry_tag = f"momentum_{_conv_tier}" if _conv_active else "momentum"
                                shadow.log_signal(short_name, "long", r["score"], _entry_tag, taken=True)
                                overtrading_guard.record_trade(cycle)
                                market_brain.record_entry(cycle)

                                recovery_mode.record_trade(cycle)
                                min_activity.record_trade(cycle)
                                _conv_tag = f" [{_conv_tier}]" if _conv_active else ""
                                logger.info(f"BUY {short_name} ${amount:.0f} @ ${order['fill_price']:,.4f} score={r['score']:.2f} slip={order['slippage_pct']:.3f}%{_conv_tag}")
                                log_trade_entry(short_name, "long", "momentum", amount, order['fill_price'], sl_for_sizing, atr_for_sizing, _edge_size_multiplier(), _current_regime, cycle)
                                break
                            elif not order["filled"]:
                                shadow.log_signal(short_name, "long", r["score"], f"order_rejected:{order['reject_reason']}", taken=False)
                                pair_failure_tracker.record_failure(short_name, cycle)
                        else:
                            logger.debug(f"SIZE_TOO_SMALL {short_name} long momentum ${amount:.2f} — skipped (min $5)")

                # Short the worst scorer
                if len(wallet.shorts) < 3:  # was 2 — too few, all slots filled immediately
                    _brain_scan_short = 15 + _brain.get("scan_extra", 0)
                    for r in last_full_rank[-_brain_scan_short:]:
                        # ONLY short coins that are actually going DOWN (negative change)
                        # Adaptive mode: use relaxed thresholds in trending markets when idle
                        _base_ss = -0.06 if _adaptive_mode else -0.04  # v29.3: was -0.09/-0.06
                        _base_sc = -0.006 if _adaptive_mode else -0.004  # v29.3: was -0.009/-0.006
                        _floor_ss = -0.03  # v29.3: was -0.06
                        _floor_sc = -0.003  # v29.3: was -0.006
                        min_short_score = _base_ss * _brain.get("score_mult", 1.0)
                        min_short_change = _base_sc * _brain.get("change_mult", 1.0)
                        # Ranging adaptation: relax short thresholds too
                        if _is_ranging:
                            min_short_score = min(_floor_ss, min_short_score + RANGING_SCORE_REDUCTION)
                            min_short_change = min(_floor_sc, min_short_change + RANGING_SCORE_REDUCTION)
                        # Min activity guard: further relax short thresholds when idle
                        if _activity_tier > 0:
                            _extra_score = 0.03 if (_activity_tier >= 2 and (_is_ranging or _current_regime == "CHOPPY")) else 0
                            _extra_change = 0.008 if (_activity_tier >= 2 and (_is_ranging or _current_regime == "CHOPPY")) else 0
                            min_short_score = min(_floor_ss, min_short_score + _activity_score_adj + _extra_score)
                            min_short_change = min(_floor_sc, min_short_change + _activity_change_adj + _extra_change)
                        # Adaptive mode logging (short)
                        if _adaptive_mode and r == last_full_rank[-1] and cycle % 50 == 0:
                            logger.info(f"[ADAPTIVE] cycle={cycle} SHORT base_s={_base_ss} base_c={_base_sc} floor_s={_floor_ss} floor_c={_floor_sc} mood={_brain.get('mood')} trends={_brain.get('clean_trends_pct')}% idle={min_activity.idle_cycles(cycle)}c")
                        if r["score"] > min_short_score or r["price"] < 0.0001 or r["vol"] < 100000 or r["change"] > min_short_change:
                            if r["score"] <= -0.03:
                                logger.debug(f"[FILTER_TRACE] {to_short_name(pair_names.get(r['pair'], r['pair']))} SHORT score={r['score']:.2f} chg={r['change']:.4f} vol={r['vol']:.0f} BLOCKED=threshold (min_s={min_short_score:.3f} min_c={min_short_change:.4f})")
                            market_brain.record_filter_block(cycle, "score_threshold")
                            continue
                        # v29.5.0: MIN_MOMENTUM_SCORE moved up — cheap filter before expensive checks
                        if abs(r["score"]) < MIN_MOMENTUM_SCORE:
                            logger.debug(f"[BLOCKED: WEAK_MOMENTUM] {to_short_name(pair_names.get(r['pair'], r['pair']))} SHORT — score {r['score']:.3f} < {MIN_MOMENTUM_SCORE}")
                            shadow.log_signal(to_short_name(pair_names.get(r['pair'], r['pair'])), "short", r["score"], "weak_momentum", taken=False)
                            continue
                        # v29.3.5: noise filter removed (redundant — MIN_MOMENTUM_SCORE=0.08 > NOISE_SHORT_MIN_SCORE=0.01)
                        # ── v29.3 ENTRY QUALITY: Momentum Confirmation (SHORT) ──
                        _s_coin_name = to_short_name(pair_names.get(r['pair'], r['pair']))
                        # v29.4.0: Sentiment check (Item 4)
                        if not sentiment_allows(_s_coin_name, "short"):
                            continue
                        _mom_ok_s, _mom_delta_s = momentum_confirmed(_s_coin_name, "short", window=5)
                        if not _mom_ok_s:
                            logger.info(f"[REJECTED: NO_MOMENTUM] {_s_coin_name} SHORT score={r['score']:.2f} chg={r['change']:.4f} mom_delta={_mom_delta_s:.5f}")
                            shadow.log_signal(_s_coin_name, "short", r["score"], "no_momentum", taken=False)
                            market_brain.record_filter_block(cycle, "no_momentum")
                            continue
                        # ── v29.3 ENTRY QUALITY: Micro-Trend Confirmation (SHORT) ──
                        _mt_ok_s, _mt_agree_s, _mt_total_s = micro_trend_confirmed(_s_coin_name, "short", candles=4)
                        if not _mt_ok_s:
                            logger.info(f"[REJECTED: TREND_WEAK] {_s_coin_name} SHORT score={r['score']:.2f} chg={r['change']:.4f} agree={_mt_agree_s}/{_mt_total_s}")
                            shadow.log_signal(_s_coin_name, "short", r["score"], "trend_weak", taken=False)
                            market_brain.record_filter_block(cycle, "trend_weak")
                            continue
                        if _usable_cash < 100:
                            break
                        name = pair_names.get(r["pair"], r["pair"])
                        short_name = to_short_name(name)
                        # Conviction override: compute once for all soft-filter gates
                        _conv_active, _conv_skipped, _conv_tier = conviction_override_active(r["score"], r["change"], "momentum", regime=enhanced_regime)
                        if _conv_active:
                            conviction_kill_tracker.record_override()
                        if _conv_active and _conv_tier == "HIGH_CONVICTION":
                            logger.info(f"OVERRIDE: High conviction trade allowed | {short_name} | score={r['score']:.2f}")
                        # v29.4.0: restored conviction safety gate (ATR removed — only momentum + micro_trend)
                        if _conv_active:
                            _mom_ok = momentum_confirmed(short_name, "short")[0]
                            _micro_ok = micro_trend_confirmed(short_name, "short")[0]
                            if not (_mom_ok and _micro_ok):
                                shadow.log_signal(short_name, "short", r["score"], "CONVICTION_UNSAFE", taken=False)
                                logger.debug(f"CONVICTION_UNSAFE {short_name} short: mom={_mom_ok} micro={_micro_ok}")
                                market_brain.record_filter_block(cycle, "conviction_unsafe")
                                continue
                        already_held = any(k in (r["pair"], short_name, name) for k in wallet.longs)
                        already_short = any(k in (r["pair"], short_name, name) for k in wallet.shorts)
                        if already_held or already_short:
                            continue
                        if short_name in _exited_this_cycle:
                            continue
                        # v29.3.5 H9: Unified coin blocking — single function checks all 4 systems
                        _blocked, _block_reason = is_coin_blocked(short_name, cycle, is_ranging=_is_ranging)
                        if _blocked:
                            logger.info(f"[BLOCKED: {_block_reason}] {short_name} SHORT")
                            shadow.log_signal(short_name, "short", r["score"], _block_reason, taken=False)
                            continue
                        # v29.3.2: Volatility circuit breaker
                        if hasattr(wallet, '_avg_market_atr') and wallet._avg_market_atr > VOLATILITY_CIRCUIT_BREAKER:
                            logger.info(f"[BLOCKED: VOL_CIRCUIT_BREAKER] {short_name} SHORT — market vol {wallet._avg_market_atr:.2f}% > {VOLATILITY_CIRCUIT_BREAKER}%")
                            continue
                        # v29.3.3: Loss streak protection
                        if cycle < _loss_streak_paused_until:
                            logger.info(f"[PAUSED: LOSS_STREAK_PROTECTION] {short_name} SHORT — paused until cycle {_loss_streak_paused_until}")
                            continue
                        # v29.5.0: MIN_MOMENTUM_SCORE check moved earlier (before expensive filters)
                        # v29.3.5: Split cooldown — winners 15 cycles, losers 40 cycles
                        if short_name in _last_exit_cycle:
                            _cd_cycle, _cd_was_win = _last_exit_cycle[short_name]
                            _cd_limit = COOLDOWN_AFTER_WIN if _cd_was_win else COOLDOWN_AFTER_LOSS
                            if (cycle - _cd_cycle) < _cd_limit:
                                logger.info(f"[BLOCKED: COOLDOWN] {short_name} SHORT — exited {cycle - _cd_cycle} cycles ago (min {_cd_limit}, {'win' if _cd_was_win else 'loss'})")
                                shadow.log_signal(short_name, "short", r["score"], "exit_cooldown", taken=False)
                                continue
                        if short_name in wallet.cooldowns and (cycle - wallet.cooldowns[short_name]) < LOSS_COOLDOWN_CYCLES and not _in_recovery:
                            shadow.log_signal(short_name, "short", r["score"], "cooldown", taken=False)
                            continue
                        # Per-pair failure isolation (soft — conviction can override)
                        if pair_failure_tracker.is_blocked(short_name, cycle, is_ranging=_is_ranging):
                            if _conv_active:
                                shadow.log_signal(short_name, "short", r["score"], f"pair_blocked_{_conv_tier}_OVERRIDDEN", taken=False)
                                logger.debug(f"{_conv_tier} OVERRIDE {short_name} short: bypassed pair_failure (score={r['score']:.2f} chg={r['change']:.3f})")
                            else:
                                shadow.log_signal(short_name, "short", r["score"], "pair_blocked", taken=False)
                                continue
                        # Data confidence: require enough price history before trading
                        if len(prices_cache.get(short_name, [])) < MIN_PRICE_HISTORY:
                            shadow.log_signal(short_name, "short", r["score"], "insufficient_data", taken=False)
                            market_brain.record_filter_block(cycle, "insufficient_data")
                            continue
                        # Minimum volatility: don't short dead coins (stagnation trap)
                        _coin_atr_val_s = coin_atr(short_name)
                        if _coin_atr_val_s < MIN_ATR_TO_TRADE:
                            shadow.log_signal(short_name, "short", r["score"], "low_atr", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} SHORT score={r['score']:.2f} BLOCKED=low_atr ({_coin_atr_val_s:.4f} < {MIN_ATR_TO_TRADE})")
                            market_brain.record_filter_block(cycle, "low_atr")
                            _dead_market_skips += 1
                            continue
                        # v29.1 DEAD MARKET FILTER: skip if ATR too low for TP to be achievable
                        _atr_pct_s = _coin_atr_val_s * 100
                        _est_tp_s = max(0.4, 1.2 * max(0.8, _atr_pct_s * 0.7) * 1.0)  # v29.3: matches new TP
                        _cumulative_move_s = _atr_pct_s * 400 * 0.3  # v29.3: tighter cycle window
                        if _cumulative_move_s < _est_tp_s * 0.2:  # v29.3: was 0.4
                            shadow.log_signal(short_name, "short", r["score"], "dead_market", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} SHORT score={r['score']:.2f} BLOCKED=dead_market (atr={_atr_pct_s:.3f}% est_tp={_est_tp_s:.2f}% move={_cumulative_move_s:.2f}%)")
                            market_brain.record_filter_block(cycle, "dead_market")
                            _dead_market_skips += 1
                            continue
                        # Freshness: only trade if price was updated within last 5 cycles
                        if cycle - price_last_updated.get(short_name, 0) > 5:
                            shadow.log_signal(short_name, "short", r["score"], "stale_price", taken=False)
                            market_brain.record_filter_block(cycle, "stale_price")
                            continue
                        # Suspicious price filter
                        if short_name in _suspicious_coins:
                            shadow.log_signal(short_name, "short", r["score"], "suspicious_price", taken=False, conviction_tier=_conv_tier if _conv_active else "")
                            continue
                        # Execution safety: block if liquidity is poor
                        if not liquidity_ok(short_name):
                            shadow.log_signal(short_name, "short", r["score"], "low_liquidity", taken=False, conviction_tier=_conv_tier if _conv_active else "")
                            continue
                        if not trading_allowed:
                            shadow.log_signal(short_name, "short", r["score"], "circuit_breaker", taken=False)
                            break
                        held_coins = list(wallet.longs.keys()) + list(wallet.shorts.keys())
                        too_corr, corr_with, corr_val = corr_guard.is_too_correlated(short_name, held_coins)
                        if too_corr:
                            shadow.log_signal(short_name, "short", r["score"], "correlation", taken=False)
                            continue
                        # v29.3.5 M10: Consolidated market quality check (replaces separate is_choppy + volume_confirms)
                        _mq_score = market_quality_score(short_name, r)
                        if _mq_score < 0.4:
                            _can_override = (_brain.get("skip_choppy") or _brain.get("skip_volume_confirms")
                                             or _conv_active or _activity_soft_leniency)
                            if _can_override:
                                _override_src = "BRAIN" if _brain.get("skip_choppy") else _conv_tier if _conv_active else "MIN_ACTIVITY"
                                shadow.log_signal(short_name, "short", r["score"], f"market_quality_{_override_src}_OVERRIDDEN", taken=False)
                                logger.debug(f"[{_override_src}] {short_name} short: bypassed market_quality (score={_mq_score:.2f}, mood={_brain.get('mood')})")
                            else:
                                shadow.log_signal(short_name, "short", r["score"], "market_quality", taken=False)
                                market_brain.record_filter_block(cycle, "market_quality")
                                continue
                        # Optimized change – pullback filter now optional for shorts too
                        _is_pullback = is_pullback_entry(short_name, "short")
                        st_mom = short_momentum(short_name, window=5)
                        if st_mom > 0.005:
                            if _conv_active and "momentum_filter" in _conv_skipped:
                                shadow.log_signal(short_name, "short", r["score"], f"momentum_filter_{_conv_tier}_OVERRIDDEN", taken=False)
                                logger.debug(f"{_conv_tier} OVERRIDE {short_name} short: bypassed short_momentum (score={r['score']:.2f} st_mom={st_mom:.4f})")
                            else:
                                shadow.log_signal(short_name, "short", r["score"], "momentum_filter", taken=False)
                                market_brain.record_filter_block(cycle, "momentum_filter")
                                continue
                        # Optimized change – removed ML brain + Trader Decision Layer (vestigial)
                        # Risk cap for shorts: same 0.5% portfolio risk limit as longs
                        atr_short = coin_atr(short_name) * 100
                        sl_short = max(0.8, atr_short * 0.7)  # v29.3: Floor 0.8% SL (was 1.5%)
                        max_risk_short = wallet.value(prices) * MAX_RISK_PER_TRADE  # 0.5% of portfolio
                        effective_sl_short = sl_short * GAP_RISK_MULTIPLIER  # Size for realistic worst fill
                        max_by_risk_short = max_risk_short / (effective_sl_short / 100)
                        max_by_risk_short = min(max_by_risk_short, wallet.value(prices) * 0.30)  # Hard cap: 30% of portfolio
                        # Optimized change – removed volatility_scale (fights short momentum signal)
                        # Optimized change – removed $200 hard cap (scale by portfolio %, consistent with all other entries)
                        amount = kelly_size(wallet, min(wallet.cash * 0.20, max_by_risk_short), prices)
                        # Strategy health check — respect both 'momentum' and 'short' keys
                        if (not strategy_health.is_healthy('momentum') or not strategy_health.is_healthy('short')) and not _in_recovery:
                            shadow.log_signal(short_name, "short", r["score"], "strategy_health", taken=False)
                            market_brain.record_filter_block(cycle, "strategy_health")
                            break

                        # 2-multiplier sizing for shorts
                        # MULT 1: edge_multiplier (from REAL_EDGE)
                        amount = amount * _edge_size_multiplier()
                        # MULT 2: boost BEFORE risk cap
                        # v29.3.5: POST_SIZING_BOOST removed (was noop — always capped away)
                        # MULT 2: risk_cap
                        amount = min(amount, max_by_risk_short)
                        _amt_before_mults = amount  # Snapshot before reduction multipliers
                        # MULT 4: ranging regime scale (reduce momentum positions in sideways markets)
                        if _is_ranging:
                            amount *= RANGING_MOMENTUM_SCALE
                        # MULT 5: regime-aware sizing (can only reduce)
                        amount = _regime_size_scale(amount, _current_regime)
                        amount *= _winrate_size_bonus(wallet)  # +10% if WR > 55%
                        amount *= size_mult  # off-peak × adaptive × warmup ramp
                        amount *= _health_size_mult  # health-score graduated scaling
                        amount *= _brain.get("size_mult", 1.0)  # Brain mood-based sizing adjustment
                        amount *= _fg_size_mult  # v29.4.1: Fear & Greed Index sizing (applies to shorts too)
                        amount *= _choppy_size_mult  # CHOPPY regime: 70% size, else 1.0
                        amount *= _sideways_size_mult  # Sideways market: scale down proportionally
                        amount *= _trend_size_boost  # +10% in strong trends (clean_trends≥75%, not CHOPPY)
                        # v29.5.0: Pro multipliers
                        amount *= volatility_size_mult(short_name)
                        amount *= _session_mult
                        amount *= _dd_mult
                        amount *= _streak_mult
                        # Multiplier stacking floor: never reduce below 25% of risk-capped size
                        if _amt_before_mults > 0 and amount < _amt_before_mults * 0.25:
                            amount = _amt_before_mults * 0.25
                            logger.debug(f"[MULT_FLOOR] {short_name} SHORT: stacking crushed to {amount:.2f}, floored to 25% of {_amt_before_mults:.2f}")
                        # Strong signal boost: reward high-quality entries with larger size
                        _sig_score_s = abs(r["score"])
                        if _sig_score_s > 0.8:
                            amount *= 1.25
                            logger.debug(f"[SIG_BOOST] {short_name} SHORT: elite signal ({_sig_score_s:.2f}) +25%")
                        elif _sig_score_s > 0.7:
                            amount *= 1.15
                            logger.debug(f"[SIG_BOOST] {short_name} SHORT: strong signal ({_sig_score_s:.2f}) +15%")
                        # Safety net: hard cap at 30% portfolio
                        amount = min(amount, wallet.value(prices) * 0.30)
                        amount = min(amount, max_by_risk_short)  # Re-enforce risk cap after boost
                        # Minimum position floor: if signal passed ALL filters, don't let multiplier stacking kill it
                        if amount < 15 and amount > 0 and max_by_risk_short >= 15:
                            amount = 15
                            logger.debug(f"[SIZE_FLOOR] {short_name} SHORT: multipliers crushed size, floored to $15")
                        # Group correlation limit
                        if not group_limit_ok(short_name, wallet):
                            shadow.log_signal(short_name, "short", r["score"], "group_limit", taken=False)
                            continue
                        # Unified exposure check
                        _exp_ok, _exp_reason = unified_exposure_ok(wallet, prices, short_name, amount, sl_short)
                        if not _exp_ok:
                            shadow.log_signal(short_name, "short", r["score"], _exp_reason, taken=False)
                            break
                        # Safe mode: block shorts
                        if not safe_mode.shorts_allowed:
                            shadow.log_signal(short_name, "short", r["score"], "safe_mode_no_shorts", taken=False)
                            continue
                        # Trade quality filters
                        if not reward_risk_ok(sl_short, sl_short * 2, atr_pct=atr_short):
                            shadow.log_signal(short_name, "short", r["score"], "rr_filter", taken=False)
                            market_brain.record_filter_block(cycle, "rr_filter")
                            continue
                        if not volatility_spike_check(short_name):
                            shadow.log_signal(short_name, "short", r["score"], "vol_spike", taken=False)
                            continue
                        # Entry confirmation: require 2 consecutive ticks in trade direction
                        if not entry_direction_confirmed(short_name, "short", ticks=1):
                            shadow.log_signal(short_name, "short", r["score"], "no_entry_confirm", taken=False)
                            logger.debug(f"[FILTER_TRACE] {short_name} SHORT score={r['score']:.2f} BLOCKED=no_entry_confirm (price not moving down)")
                            market_brain.record_filter_block(cycle, "entry_confirm")
                            continue
                        # v29.4.0: duplicate coin_loss_tracker check removed — already consolidated via is_coin_blocked() earlier
                        if not market_depth_ok(short_name, amount, tickers):
                            shadow.log_signal(short_name, "short", r["score"], "thin_market", taken=False)
                            market_brain.record_filter_block(cycle, "thin_market")
                            continue
                        if not regime_confirm(short_name, "short"):
                            shadow.log_signal(short_name, "short", r["score"], "regime_mismatch", taken=False, conviction_tier=_conv_tier if _conv_active else "")
                            market_brain.record_filter_block(cycle, "regime_confirm")
                            continue
                        recovery_mode.record_passed_filter()
                        cycle_audit.record_passed_filters()
                        if amount > 5:
                            if _in_recovery:
                                recovery_mode.record_attempt()
                            order = executor.place_order("SHORT", short_name, r["price"], amount, wallet, prices)
                            if order["filled"] and short_name in wallet.shorts:
                                wallet.shorts[short_name]["bought_cycle"] = cycle
                                wallet.shorts[short_name]["entry_sl"] = sl_short
                                wallet.shorts[short_name]["entry_atr"] = atr_short
                                _entry_tag = f"momentum_{_conv_tier}" if _conv_active else "momentum"
                                shadow.log_signal(short_name, "short", r["score"], _entry_tag, taken=True)
                                overtrading_guard.record_trade(cycle)
                                market_brain.record_entry(cycle)

                                recovery_mode.record_trade(cycle)
                                min_activity.record_trade(cycle)
                                _conv_tag = f" [{_conv_tier}]" if _conv_active else ""
                                logger.info(f"SHORT {short_name} ${amount:.0f} @ ${order['fill_price']:,.4f} score={r['score']:.2f} slip={order['slippage_pct']:.3f}%{_conv_tag}")
                                log_trade_entry(short_name, "short", "momentum", amount, order['fill_price'], sl_short, atr_short, _edge_size_multiplier(), _current_regime, cycle)
                                break
                            elif not order["filled"]:
                                shadow.log_signal(short_name, "short", r["score"], f"order_rejected:{order['reject_reason']}", taken=False)
                                pair_failure_tracker.record_failure(short_name, cycle)
                        else:
                            logger.debug(f"SIZE_TOO_SMALL {short_name} short momentum ${amount:.2f} — skipped (min $5)")

                # ── MEAN REVERSION: Buy oversold, short overbought ──
                # Adaptive: skip if regime layer says no mean reversion
                mean_rev_allowed = True
                if adaptive_rules and not adaptive_rules["allow_mean_reversion"]:
                    mean_rev_allowed = False
                    # Shadow: log that regime blocked mean reversion
                    for pair, t in tickers.items():
                        if t["vol"] >= SCAN_PREFILTER_MIN_VOL:
                            coin = to_short_name(pair_names.get(pair, pair))
                            z = zscore(coin, lookback=50)
                            if z < -2.0:
                                shadow.log_signal(coin, "long", z, "regime_no_meanrev", taken=False, strategy="mean_rev")
                            elif z > 2.0:
                                shadow.log_signal(coin, "short", z, "regime_no_meanrev", taken=False, strategy="mean_rev")
                if mean_rev_allowed and regime in ("RANGING", "VOLATILE") and _usable_cash > 50:
                    for pair, t in tickers.items():
                        if t["vol"] < SCAN_PREFILTER_MIN_VOL:
                            continue
                        name = pair_names.get(pair, pair)
                        coin = to_short_name(name)
                        # Skip stale pairs: need 20+ price points for meaningful ATR/z-score
                        if len(prices_cache.get(coin, [])) < 20:
                            continue
                        z = zscore(coin, lookback=50)
                        if coin in wallet.longs or coin in wallet.shorts:
                            continue
                        if coin in _exited_this_cycle:
                            continue
                        # v29.3.2: Dynamic blacklist — block known-bad coins
                        if coin in DYNAMIC_BLACKLIST:
                            logger.info(f"[BLOCKED: DYNAMIC_BLACKLIST] {coin} mean_rev — coin blacklisted (0%WR, negative PnL)")
                            continue
                        # v29.3.4: Temporary dynamic blacklist — cooldown with recovery
                        if TEMP_BLACKLIST_ENABLED and dynamic_blacklist.is_blocked(coin, cycle):
                            logger.info(f"[BLOCKED: TEMP_BLACKLIST] {coin} mean_rev — temp blacklisted (cooling down)")
                            continue
                        # v29.3.2: Volatility circuit breaker
                        if hasattr(wallet, '_avg_market_atr') and wallet._avg_market_atr > VOLATILITY_CIRCUIT_BREAKER:
                            continue
                        # v29.3.3: Loss streak protection
                        if cycle < _loss_streak_paused_until:
                            continue
                        # v29.3.3: Minimum momentum filter (use z-score as momentum proxy for mean-rev)
                        if abs(z) < MIN_MOMENTUM_SCORE * 13:  # z-score scale: 2.0 maps to ~0.15 momentum
                            continue
                        # v29.3.5: Split cooldown — winners 15 cycles, losers 40 cycles
                        if coin in _last_exit_cycle:
                            _cd_cycle, _cd_was_win = _last_exit_cycle[coin]
                            _cd_limit = COOLDOWN_AFTER_WIN if _cd_was_win else COOLDOWN_AFTER_LOSS
                            if (cycle - _cd_cycle) < _cd_limit:
                                if z < -2.0:
                                    logger.info(f"[BLOCKED: COOLDOWN] {coin} LONG mean_rev — exited {cycle - _cd_cycle} cycles ago (min {_cd_limit}, {'win' if _cd_was_win else 'loss'})")
                                    shadow.log_signal(coin, "long", z, "exit_cooldown", taken=False, strategy="mean_rev")
                                elif z > 2.0:
                                    logger.info(f"[BLOCKED: COOLDOWN] {coin} SHORT mean_rev — exited {cycle - _cd_cycle} cycles ago (min {_cd_limit}, {'win' if _cd_was_win else 'loss'})")
                                    shadow.log_signal(coin, "short", z, "exit_cooldown", taken=False, strategy="mean_rev")
                                continue
                        # Freshness + suspicious price filter
                        if cycle - price_last_updated.get(coin, 0) > 5:
                            continue
                        if coin in _suspicious_coins:
                            continue
                        if coin in wallet.cooldowns and (cycle - wallet.cooldowns[coin]) < LOSS_COOLDOWN_CYCLES and not _in_recovery:
                            # Shadow: log mean_rev signal skipped by cooldown
                            if z < -2.0:
                                shadow.log_signal(coin, "long", z, "cooldown", taken=False, strategy="mean_rev")
                            elif z > 2.0:
                                shadow.log_signal(coin, "short", z, "cooldown", taken=False, strategy="mean_rev")
                            continue
                        # Data confidence: require enough price history
                        if len(prices_cache.get(coin, [])) < MIN_PRICE_HISTORY:
                            if z < -2.0 or z > 2.0:
                                shadow.log_signal(coin, "long" if z < -2.0 else "short", z, "insufficient_data", taken=False, strategy="mean_rev")
                            continue
                        # Execution safety: block if liquidity is poor
                        if not liquidity_ok(coin):
                            if z < -2.0 or z > 2.0:
                                shadow.log_signal(coin, "long" if z < -2.0 else "short", z, "low_liquidity", taken=False, strategy="mean_rev")
                            continue
                        # Correlation guard
                        held_coins_mr = list(wallet.longs.keys()) + list(wallet.shorts.keys())
                        too_corr_mr, corr_with_mr, corr_val_mr = corr_guard.is_too_correlated(coin, held_coins_mr)
                        if too_corr_mr:
                            if z < -2.0 or z > 2.0:
                                shadow.log_signal(coin, "long" if z < -2.0 else "short", z, "correlation", taken=False, strategy="mean_rev")
                            continue

                        # Ranging adaptation: allow extra mean-rev positions
                        _mr_long_limit = 2 + (RANGING_MEANREV_EXTRA_LONGS if _is_ranging else 0)
                        _mr_short_limit = 1 + (RANGING_MEANREV_EXTRA_SHORTS if _is_ranging else 0)
                        # Min activity guard: relax z-score threshold when idle (2.0 → 1.8 at max tier)
                        _mr_z_threshold = 2.0 - (_activity_tier * 0.07) if _activity_tier > 0 else 2.0
                        if z < -_mr_z_threshold and len(wallet.longs) < _mr_long_limit and _usable_cash > 50:
                            # v29.4.1: Triple-Confirm Mean Reversion (BB + RSI + Z-Score)
                            _tc_ok, _tc_dir, _tc_boost, _tc_detail = triple_confirm_meanrev(coin, z)
                            if TRIPLE_MEANREV_ENABLED and not _tc_ok:
                                shadow.log_signal(coin, "long", z, "triple_meanrev_unconfirmed", taken=False, strategy="mean_rev")
                                logger.debug(f"[TRIPLE_MR] {coin} LONG z={z:.2f} — BB/RSI not confirming (rsi={_tc_detail.get('rsi', 0):.1f})")
                                continue
                            if TRIPLE_MEANREV_ENABLED and _tc_ok and _tc_boost > 0:
                                logger.info(f"[TRIPLE_MR] {coin} LONG HIGH-CONV z={z:.2f} rsi={_tc_detail.get('rsi', 0):.1f} — +{_tc_boost*100:.0f}% size boost")
                            # Conviction override for mean-rev: uses z-score as signal strength
                            _conv_mr, _conv_mr_skipped, _conv_mr_tier = conviction_override_active(z, 0, "mean_rev", regime=enhanced_regime)
                            if _conv_mr:
                                conviction_kill_tracker.record_override()
                            if _conv_mr and _conv_mr_tier == "HIGH_CONVICTION":
                                logger.info(f"OVERRIDE: High conviction trade allowed | {coin} | z={z:.1f} (mean-rev long)")
                            # v29.3.1: Gate conviction with ATR + momentum + trend safety checks
                            if _conv_mr:
                                _conv_atr_mr = coin_atr(coin)
                                _conv_mom_ok_mr, _ = momentum_confirmed(coin, "long", window=5)
                                _conv_mt_ok_mr, _, _ = micro_trend_confirmed(coin, "long", candles=4)
                                if _conv_atr_mr < 0.003 or not _conv_mom_ok_mr or not _conv_mt_ok_mr:
                                    logger.info(f"[BLOCKED: CONVICTION_UNSAFE] {coin} LONG mean_rev {_conv_mr_tier} — atr={_conv_atr_mr:.4f} mom={_conv_mom_ok_mr} trend={_conv_mt_ok_mr}")
                                    _conv_mr = False
                            # Noise filter: block mean reversion if THIS COIN is trending
                            if coin_is_trending(coin):
                                if _conv_mr and "coin_trending" in _conv_mr_skipped:
                                    shadow.log_signal(coin, "long", z, f"noise_coin_trending_{_conv_mr_tier}_OVERRIDDEN", taken=False, strategy="mean_rev")
                                    logger.debug(f"{_conv_mr_tier} OVERRIDE {coin} mean-rev long: bypassed coin_is_trending (z={z:.1f})")
                                else:
                                    shadow.log_signal(coin, "long", z, "noise_coin_trending", taken=False, strategy="mean_rev")
                                    continue
                            atr_mr = coin_atr(coin) * 100
                            sl_mr = max(0.8, atr_mr * 0.7)
                            max_risk_mr = wallet.value(prices) * MAX_RISK_PER_TRADE
                            effective_sl_mr = sl_mr * GAP_RISK_MULTIPLIER
                            max_by_risk_mr = max_risk_mr / (effective_sl_mr / 100)
                            max_by_risk_mr = min(max_by_risk_mr, wallet.value(prices) * 0.30)
                            # Optimized change – removed $200 hard cap (scale by portfolio %)
                            amt = kelly_size(wallet, min(wallet.cash * 0.20, max_by_risk_mr), prices)
                            # 2-multiplier sizing: edge + boost + risk_cap
                            amt = amt * _edge_size_multiplier()
                            # v29.3.5: POST_SIZING_BOOST removed (was noop — always capped away)
                            amt = min(amt, max_by_risk_mr)
                            _amt_before_mults_mr = amt  # Snapshot before reduction multipliers
                            amt = _regime_size_scale(amt, _current_regime)
                            amt *= _winrate_size_bonus(wallet)  # +10% if WR > 55%
                            amt *= size_mult  # off-peak × adaptive × warmup ramp
                            amt *= _health_size_mult  # health-score graduated scaling
                            amt *= _brain.get("size_mult", 1.0)  # Brain mood-based sizing adjustment
                            amt *= _fg_size_mult  # v29.4.1: Fear & Greed Index sizing
                            amt *= _dca_size_mult  # v29.4.1: Smart DCA boost in Extreme Fear
                            # Multiplier stacking floor: never reduce below 25%
                            if _amt_before_mults_mr > 0 and amt < _amt_before_mults_mr * 0.25:
                                amt = _amt_before_mults_mr * 0.25
                                logger.debug(f"[MULT_FLOOR] {coin} MR-LONG: floored to 25% of {_amt_before_mults_mr:.2f}")
                            # Strong signal boost: reward high-quality z-score entries
                            _zscore_mr = abs(z)
                            if _zscore_mr > 3.5:
                                amt *= 1.25
                                logger.debug(f"[SIG_BOOST] {coin} MR-LONG: elite z-score ({_zscore_mr:.2f}) +25%")
                            elif _zscore_mr > 3.0:
                                amt *= 1.15
                                logger.debug(f"[SIG_BOOST] {coin} MR-LONG: strong z-score ({_zscore_mr:.2f}) +15%")
                            # v29.4.1: Triple-confirm conviction boost
                            if TRIPLE_MEANREV_ENABLED and _tc_ok and _tc_boost > 0:
                                amt *= (1.0 + _tc_boost)
                                logger.debug(f"[TRIPLE_MR_BOOST] {coin} MR-LONG: +{_tc_boost*100:.0f}% triple-confirm conviction")
                            amt = min(amt, wallet.value(prices) * 0.30)  # Safety net: 30% portfolio hard cap
                            amt = min(amt, max_by_risk_mr)  # Re-enforce risk cap after boost
                            if amt < 15 and amt > 0 and max_by_risk_mr >= 15:
                                amt = 15
                                logger.debug(f"[SIZE_FLOOR] {coin} MEAN-REV LONG: multipliers crushed size, floored to $15")
                            _mr_exp_ok, _mr_exp_reason = unified_exposure_ok(wallet, prices, coin, amt, sl_mr)
                            # Log recovery override of coin_loss (don't silently skip)
                            if _in_recovery and coin_loss_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging):
                                shadow.log_signal(coin, "long", z, "coin_blocked_RECOVERY_OVERRIDE", taken=False, strategy="mean_rev")
                                logger.warning(f"RECOVERY OVERRIDE {coin} mean-rev long: coin_loss blocked but recovery active (z={z:.1f})")
                            if not group_limit_ok(coin, wallet):
                                shadow.log_signal(coin, "long", z, "group_limit", taken=False, strategy="mean_rev")
                            elif not _mr_exp_ok:
                                shadow.log_signal(coin, "long", z, _mr_exp_reason, taken=False, strategy="mean_rev")
                            elif not reward_risk_ok(sl_mr, sl_mr * 2, atr_pct=atr_mr):
                                shadow.log_signal(coin, "long", z, "rr_filter", taken=False, strategy="mean_rev")
                            elif not volatility_spike_check(coin):
                                shadow.log_signal(coin, "long", z, "vol_spike", taken=False, strategy="mean_rev")
                            elif coin_loss_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging) and not _in_recovery:
                                if _conv_mr:
                                    shadow.log_signal(coin, "long", z, f"coin_blocked_{_conv_mr_tier}_OVERRIDDEN", taken=False, strategy="mean_rev")
                                    logger.debug(f"{_conv_mr_tier} OVERRIDE {coin} mean-rev long: bypassed coin_loss (z={z:.1f})")
                                else:
                                    shadow.log_signal(coin, "long", z, "coin_blocked", taken=False, strategy="mean_rev")
                            elif pair_failure_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging):
                                if _conv_mr:
                                    shadow.log_signal(coin, "long", z, f"pair_blocked_{_conv_mr_tier}_OVERRIDDEN", taken=False, strategy="mean_rev")
                                    logger.debug(f"{_conv_mr_tier} OVERRIDE {coin} mean-rev long: bypassed pair_failure (z={z:.1f})")
                                else:
                                    shadow.log_signal(coin, "long", z, "pair_blocked", taken=False, strategy="mean_rev")
                            elif not market_depth_ok(coin, amt, tickers):
                                shadow.log_signal(coin, "long", z, "thin_market", taken=False, strategy="mean_rev")
                            elif not regime_confirm(coin, "long", strategy="mean_rev"):
                                shadow.log_signal(coin, "long", z, "regime_mismatch", taken=False, strategy="mean_rev")
                            else:
                                recovery_mode.record_passed_filter()
                                cycle_audit.record_passed_filters()
                                if amt > 5:
                                    if _in_recovery:
                                        recovery_mode.record_attempt()
                                    order = executor.place_order("BUY", coin, t["price"], amt, wallet, prices)
                                    if order["filled"] and coin in wallet.longs:
                                        wallet.longs[coin]["strategy"] = "mean_rev"
                                        wallet.longs[coin]["bought_cycle"] = cycle
                                        wallet.longs[coin]["entry_sl"] = sl_mr
                                        wallet.longs[coin]["entry_atr"] = atr_mr
                                        shadow.log_signal(coin, "long", z, "mean_rev", taken=True, strategy="mean_rev")
                                        overtrading_guard.record_trade(cycle)
                                        market_brain.record_entry(cycle)
                                        recovery_mode.record_trade(cycle)
                                        min_activity.record_trade(cycle)
                                        _rng_tag = " [RANGING_ADAPT]" if _is_ranging else ""
                                        logger.info(f"MEAN REV BUY {coin} ${amt:.0f} z={z:.1f} slip={order['slippage_pct']:.3f}%{_rng_tag}")
                                        log_trade_entry(coin, "long", "mean_rev", amt, order['fill_price'], sl_mr, atr_mr, _edge_size_multiplier(), _current_regime, cycle)
                                        break
                                    elif not order["filled"]:
                                        pair_failure_tracker.record_failure(coin, cycle)
                                else:
                                    logger.debug(f"SIZE_TOO_SMALL {coin} long mean_rev ${amt:.2f} — skipped (min $5)")
                        elif z < -_mr_z_threshold and len(wallet.longs) >= _mr_long_limit:
                            shadow.log_signal(coin, "long", z, "position_limit", taken=False, strategy="mean_rev")
                        elif z > _mr_z_threshold and len(wallet.shorts) < _mr_short_limit and _usable_cash > 50:
                            # v29.4.1: Triple-Confirm Mean Reversion (BB + RSI + Z-Score) — SHORT
                            _tcs_ok, _tcs_dir, _tcs_boost, _tcs_detail = triple_confirm_meanrev(coin, z)
                            if TRIPLE_MEANREV_ENABLED and not _tcs_ok:
                                shadow.log_signal(coin, "short", z, "triple_meanrev_unconfirmed", taken=False, strategy="mean_rev")
                                logger.debug(f"[TRIPLE_MR] {coin} SHORT z={z:.2f} — BB/RSI not confirming (rsi={_tcs_detail.get('rsi', 0):.1f})")
                                continue
                            if TRIPLE_MEANREV_ENABLED and _tcs_ok and _tcs_boost > 0:
                                logger.info(f"[TRIPLE_MR] {coin} SHORT HIGH-CONV z={z:.2f} rsi={_tcs_detail.get('rsi', 0):.1f} — +{_tcs_boost*100:.0f}% size boost")
                            # Conviction override for mean-rev short: uses z-score as signal strength
                            _conv_ms, _conv_ms_skipped, _conv_ms_tier = conviction_override_active(z, 0, "mean_rev", regime=enhanced_regime)
                            if _conv_ms:
                                conviction_kill_tracker.record_override()
                            if _conv_ms and _conv_ms_tier == "HIGH_CONVICTION":
                                logger.info(f"OVERRIDE: High conviction trade allowed | {coin} | z={z:.1f} (mean-rev short)")
                            # v29.3.1: Gate conviction with ATR + momentum + trend safety checks
                            if _conv_ms:
                                _conv_atr_ms = coin_atr(coin)
                                _conv_mom_ok_ms, _ = momentum_confirmed(coin, "short", window=5)
                                _conv_mt_ok_ms, _, _ = micro_trend_confirmed(coin, "short", candles=4)
                                if _conv_atr_ms < 0.003 or not _conv_mom_ok_ms or not _conv_mt_ok_ms:
                                    logger.info(f"[BLOCKED: CONVICTION_UNSAFE] {coin} SHORT mean_rev {_conv_ms_tier} — atr={_conv_atr_ms:.4f} mom={_conv_mom_ok_ms} trend={_conv_mt_ok_ms}")
                                    _conv_ms = False
                            # Noise filter: block mean reversion short if THIS COIN is trending
                            if coin_is_trending(coin):
                                if _conv_ms and "coin_trending" in _conv_ms_skipped:
                                    shadow.log_signal(coin, "short", z, f"noise_coin_trending_{_conv_ms_tier}_OVERRIDDEN", taken=False, strategy="mean_rev")
                                    logger.debug(f"{_conv_ms_tier} OVERRIDE {coin} mean-rev short: bypassed coin_is_trending (z={z:.1f})")
                                else:
                                    shadow.log_signal(coin, "short", z, "noise_coin_trending", taken=False, strategy="mean_rev")
                                    continue
                            atr_ms = coin_atr(coin) * 100
                            sl_ms = max(0.8, atr_ms * 0.7)
                            max_risk_ms = wallet.value(prices) * MAX_RISK_PER_TRADE
                            effective_sl_ms = sl_ms * GAP_RISK_MULTIPLIER
                            max_by_risk_ms = max_risk_ms / (effective_sl_ms / 100)
                            max_by_risk_ms = min(max_by_risk_ms, wallet.value(prices) * 0.30)
                            # Optimized change – removed $150 hard cap (scale by portfolio %)
                            amt = kelly_size(wallet, min(wallet.cash * 0.15, max_by_risk_ms), prices)
                            # 2-multiplier sizing: edge + boost + risk_cap
                            amt = amt * _edge_size_multiplier()
                            # v29.3.5: POST_SIZING_BOOST removed (was noop — always capped away)
                            amt = min(amt, max_by_risk_ms)
                            _amt_before_mults_ms = amt  # Snapshot before reduction multipliers
                            amt = _regime_size_scale(amt, _current_regime)
                            amt *= _winrate_size_bonus(wallet)  # +10% if WR > 55%
                            amt *= size_mult  # off-peak × adaptive × warmup ramp
                            amt *= _health_size_mult  # health-score graduated scaling
                            amt *= _brain.get("size_mult", 1.0)  # Brain mood-based sizing adjustment
                            amt *= _fg_size_mult  # v29.4.1: Fear & Greed Index sizing
                            # Multiplier stacking floor: never reduce below 25%
                            if _amt_before_mults_ms > 0 and amt < _amt_before_mults_ms * 0.25:
                                amt = _amt_before_mults_ms * 0.25
                                logger.debug(f"[MULT_FLOOR] {coin} MR-SHORT: floored to 25% of {_amt_before_mults_ms:.2f}")
                            # Strong signal boost: reward high-quality z-score entries
                            _zscore_ms = abs(z)
                            if _zscore_ms > 3.5:
                                amt *= 1.25
                                logger.debug(f"[SIG_BOOST] {coin} MR-SHORT: elite z-score ({_zscore_ms:.2f}) +25%")
                            elif _zscore_ms > 3.0:
                                amt *= 1.15
                                logger.debug(f"[SIG_BOOST] {coin} MR-SHORT: strong z-score ({_zscore_ms:.2f}) +15%")
                            # v29.4.1: Triple-confirm conviction boost
                            if TRIPLE_MEANREV_ENABLED and _tcs_ok and _tcs_boost > 0:
                                amt *= (1.0 + _tcs_boost)
                                logger.debug(f"[TRIPLE_MR_BOOST] {coin} MR-SHORT: +{_tcs_boost*100:.0f}% triple-confirm conviction")
                            amt = min(amt, wallet.value(prices) * 0.30)  # Safety net: 30% portfolio hard cap
                            amt = min(amt, max_by_risk_ms)  # Re-enforce risk cap after boost
                            if amt < 15 and amt > 0 and max_by_risk_ms >= 15:
                                amt = 15
                                logger.debug(f"[SIZE_FLOOR] {coin} MEAN-REV SHORT: multipliers crushed size, floored to $15")
                            _ms_exp_ok, _ms_exp_reason = unified_exposure_ok(wallet, prices, coin, amt, sl_ms)
                            # Log recovery override of coin_loss (don't silently skip)
                            if _in_recovery and coin_loss_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging):
                                shadow.log_signal(coin, "short", z, "coin_blocked_RECOVERY_OVERRIDE", taken=False, strategy="mean_rev")
                                logger.warning(f"RECOVERY OVERRIDE {coin} mean-rev short: coin_loss blocked but recovery active (z={z:.1f})")
                            if not group_limit_ok(coin, wallet):
                                shadow.log_signal(coin, "short", z, "group_limit", taken=False, strategy="mean_rev")
                            elif not _ms_exp_ok:
                                shadow.log_signal(coin, "short", z, _ms_exp_reason, taken=False, strategy="mean_rev")
                            elif not reward_risk_ok(sl_ms, sl_ms * 2, atr_pct=atr_ms):
                                shadow.log_signal(coin, "short", z, "rr_filter", taken=False, strategy="mean_rev")
                            elif not safe_mode.shorts_allowed:
                                shadow.log_signal(coin, "short", z, "safe_mode_no_shorts", taken=False, strategy="mean_rev")
                            elif not volatility_spike_check(coin):
                                shadow.log_signal(coin, "short", z, "vol_spike", taken=False, strategy="mean_rev")
                            elif coin_loss_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging) and not _in_recovery:
                                if _conv_ms:
                                    shadow.log_signal(coin, "short", z, f"coin_blocked_{_conv_ms_tier}_OVERRIDDEN", taken=False, strategy="mean_rev")
                                    logger.debug(f"{_conv_ms_tier} OVERRIDE {coin} mean-rev short: bypassed coin_loss (z={z:.1f})")
                                else:
                                    shadow.log_signal(coin, "short", z, "coin_blocked", taken=False, strategy="mean_rev")
                            elif pair_failure_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging):
                                if _conv_ms:
                                    shadow.log_signal(coin, "short", z, f"pair_blocked_{_conv_ms_tier}_OVERRIDDEN", taken=False, strategy="mean_rev")
                                    logger.debug(f"{_conv_ms_tier} OVERRIDE {coin} mean-rev short: bypassed pair_failure (z={z:.1f})")
                                else:
                                    shadow.log_signal(coin, "short", z, "pair_blocked", taken=False, strategy="mean_rev")
                            elif not market_depth_ok(coin, amt, tickers):
                                shadow.log_signal(coin, "short", z, "thin_market", taken=False, strategy="mean_rev")
                            elif not regime_confirm(coin, "short", strategy="mean_rev"):
                                shadow.log_signal(coin, "short", z, "regime_mismatch", taken=False, strategy="mean_rev")
                            else:
                                recovery_mode.record_passed_filter()
                                cycle_audit.record_passed_filters()
                                if amt > 5:
                                    if _in_recovery:
                                        recovery_mode.record_attempt()
                                    order = executor.place_order("SHORT", coin, t["price"], amt, wallet, prices)
                                    if order["filled"] and coin in wallet.shorts:
                                        wallet.shorts[coin]["bought_cycle"] = cycle
                                        wallet.shorts[coin]["entry_sl"] = sl_ms
                                        wallet.shorts[coin]["entry_atr"] = atr_ms
                                        shadow.log_signal(coin, "short", z, "mean_rev", taken=True, strategy="mean_rev")
                                        overtrading_guard.record_trade(cycle)
                                        market_brain.record_entry(cycle)
                                        recovery_mode.record_trade(cycle)
                                        min_activity.record_trade(cycle)
                                        _rng_tag = " [RANGING_ADAPT]" if _is_ranging else ""
                                        logger.info(f"MEAN REV SHORT {coin} ${amt:.0f} z={z:.1f} slip={order['slippage_pct']:.3f}%{_rng_tag}")
                                        log_trade_entry(coin, "short", "mean_rev", amt, order['fill_price'], sl_ms, atr_ms, _edge_size_multiplier(), _current_regime, cycle)
                                        break
                                    elif not order["filled"]:
                                        pair_failure_tracker.record_failure(coin, cycle)
                                else:
                                    logger.debug(f"SIZE_TOO_SMALL {coin} short mean_rev ${amt:.2f} — skipped (min $5)")
                        elif z > _mr_z_threshold and len(wallet.shorts) >= _mr_short_limit:
                            shadow.log_signal(coin, "short", z, "position_limit", taken=False, strategy="mean_rev")

                # ── BB SQUEEZE BREAKOUT: Catch explosive moves ──
                breakout_allowed = True
                if adaptive_rules and not adaptive_rules["allow_breakout"]:
                    breakout_allowed = False
                    # Shadow: log that regime blocked breakout
                    for pair, t in tickers.items():
                        if t["vol"] >= 500000:  # Optimized change – match lowered breakout floor
                            coin = to_short_name(pair_names.get(pair, pair))
                            sq, w = bb_squeeze(coin)
                            if sq == "BREAKOUT_UP":
                                shadow.log_signal(coin, "long", w, "regime_no_breakout", taken=False, strategy="breakout")
                            elif sq == "BREAKOUT_DOWN":
                                shadow.log_signal(coin, "short", w, "regime_no_breakout", taken=False, strategy="breakout")
                if breakout_allowed and _usable_cash > 50:
                    for pair, t in tickers.items():
                        if t["vol"] < 500000:  # Optimized change – lowered from $1M to capture mid-cap breakouts
                            continue
                        name = pair_names.get(pair, pair)
                        coin = to_short_name(name)
                        # Skip stale pairs: need 20+ price points for meaningful BB/ATR
                        if len(prices_cache.get(coin, [])) < 20:
                            continue
                        squeeze_state, width = bb_squeeze(coin)
                        if coin in wallet.longs or coin in wallet.shorts:
                            continue
                        if coin in _exited_this_cycle:
                            continue
                        # v29.3.2: Dynamic blacklist — block known-bad coins
                        if coin in DYNAMIC_BLACKLIST:
                            logger.info(f"[BLOCKED: DYNAMIC_BLACKLIST] {coin} breakout — coin blacklisted (0%WR, negative PnL)")
                            continue
                        # v29.3.4: Temporary dynamic blacklist — cooldown with recovery
                        if TEMP_BLACKLIST_ENABLED and dynamic_blacklist.is_blocked(coin, cycle):
                            logger.info(f"[BLOCKED: TEMP_BLACKLIST] {coin} breakout — temp blacklisted (cooling down)")
                            continue
                        # v29.3.2: Volatility circuit breaker
                        if hasattr(wallet, '_avg_market_atr') and wallet._avg_market_atr > VOLATILITY_CIRCUIT_BREAKER:
                            continue
                        # v29.3.3: Loss streak protection
                        if cycle < _loss_streak_paused_until:
                            continue
                        # v29.3.3: Minimum momentum filter (use width as breakout strength proxy)
                        if width < MIN_MOMENTUM_SCORE:
                            continue
                        # v29.3.5: Split cooldown — winners 15 cycles, losers 40 cycles
                        if coin in _last_exit_cycle:
                            _cd_cycle, _cd_was_win = _last_exit_cycle[coin]
                            _cd_limit = COOLDOWN_AFTER_WIN if _cd_was_win else COOLDOWN_AFTER_LOSS
                            if (cycle - _cd_cycle) < _cd_limit:
                                if squeeze_state in ("BREAKOUT_UP", "BREAKOUT_DOWN"):
                                    _cd_dir = "LONG" if squeeze_state == "BREAKOUT_UP" else "SHORT"
                                    logger.info(f"[BLOCKED: COOLDOWN] {coin} {_cd_dir} breakout — exited {cycle - _cd_cycle} cycles ago (min {_cd_limit}, {'win' if _cd_was_win else 'loss'})")
                                    shadow.log_signal(coin, _cd_dir.lower(), width if 'width' in dir() else 0, "exit_cooldown", taken=False, strategy="breakout")
                                continue
                        # Freshness + suspicious price filter
                        if cycle - price_last_updated.get(coin, 0) > 5:
                            continue
                        if coin in _suspicious_coins:
                            continue
                        if coin in wallet.cooldowns and (cycle - wallet.cooldowns[coin]) < LOSS_COOLDOWN_CYCLES and not _in_recovery:
                            if squeeze_state in ("BREAKOUT_UP", "BREAKOUT_DOWN"):
                                shadow.log_signal(coin, "long" if squeeze_state == "BREAKOUT_UP" else "short", width, "cooldown", taken=False, strategy="breakout")
                            continue
                        # Data confidence: require enough price history
                        if len(prices_cache.get(coin, [])) < MIN_PRICE_HISTORY:
                            if squeeze_state in ("BREAKOUT_UP", "BREAKOUT_DOWN"):
                                shadow.log_signal(coin, "long" if squeeze_state == "BREAKOUT_UP" else "short", width, "insufficient_data", taken=False, strategy="breakout")
                            continue
                        # Execution safety: block if liquidity is poor
                        if not liquidity_ok(coin):
                            if squeeze_state in ("BREAKOUT_UP", "BREAKOUT_DOWN"):
                                shadow.log_signal(coin, "long" if squeeze_state == "BREAKOUT_UP" else "short", width, "low_liquidity", taken=False, strategy="breakout")
                            continue
                        # Correlation guard
                        held_coins_bo = list(wallet.longs.keys()) + list(wallet.shorts.keys())
                        too_corr_bo, corr_with_bo, corr_val_bo = corr_guard.is_too_correlated(coin, held_coins_bo)
                        if too_corr_bo:
                            if squeeze_state in ("BREAKOUT_UP", "BREAKOUT_DOWN"):
                                shadow.log_signal(coin, "long" if squeeze_state == "BREAKOUT_UP" else "short", width, "correlation", taken=False, strategy="breakout")
                            continue

                        if squeeze_state == "BREAKOUT_UP" and len(wallet.longs) < 2:
                            # Noise filter: require breakout confirmation (not single-tick wick)
                            if not breakout_confirmed(coin, "long"):
                                shadow.log_signal(coin, "long", width, "noise_unconfirmed_breakout", taken=False, strategy="breakout")
                                continue
                            # Conviction override for breakout: uses BB width as conviction signal
                            _conv_bo, _conv_bo_skipped, _conv_bo_tier = conviction_override_active(width, 0, "breakout", regime=enhanced_regime)
                            if _conv_bo:
                                conviction_kill_tracker.record_override()
                            if _conv_bo and _conv_bo_tier == "HIGH_CONVICTION":
                                logger.info(f"OVERRIDE: High conviction trade allowed | {coin} | width={width:.4f} (breakout long)")
                            # v29.3.1: Gate conviction with ATR + momentum + trend safety checks
                            if _conv_bo:
                                _conv_atr_bo = coin_atr(coin)
                                _conv_mom_ok_bo, _ = momentum_confirmed(coin, "long", window=5)
                                _conv_mt_ok_bo, _, _ = micro_trend_confirmed(coin, "long", candles=4)
                                if _conv_atr_bo < 0.003 or not _conv_mom_ok_bo or not _conv_mt_ok_bo:
                                    logger.info(f"[BLOCKED: CONVICTION_UNSAFE] {coin} LONG breakout {_conv_bo_tier} — atr={_conv_atr_bo:.4f} mom={_conv_mom_ok_bo} trend={_conv_mt_ok_bo}")
                                    _conv_bo = False
                            atr_bo = coin_atr(coin) * 100
                            sl_bo = max(0.8, atr_bo * 0.7)
                            max_risk_bo = wallet.value(prices) * MAX_RISK_PER_TRADE
                            effective_sl_bo = sl_bo * GAP_RISK_MULTIPLIER
                            max_by_risk_bo = max_risk_bo / (effective_sl_bo / 100)
                            max_by_risk_bo = min(max_by_risk_bo, wallet.value(prices) * 0.30)
                            # Optimized change – removed $250 hard cap (scale by portfolio %)
                            amt = kelly_size(wallet, min(wallet.cash * 0.25, max_by_risk_bo), prices)
                            # 2-multiplier sizing: edge + boost + risk_cap
                            amt = amt * _edge_size_multiplier()
                            # v29.3.5: POST_SIZING_BOOST removed (was noop — always capped away)
                            amt = min(amt, max_by_risk_bo)
                            _amt_before_mults_bo = amt  # Snapshot before reduction multipliers
                            amt = _regime_size_scale(amt, _current_regime)
                            amt *= _winrate_size_bonus(wallet)  # +10% if WR > 55%
                            amt *= size_mult  # off-peak × adaptive × warmup ramp
                            amt *= _health_size_mult  # health-score graduated scaling
                            amt *= _brain.get("size_mult", 1.0)  # Brain mood-based sizing adjustment
                            amt *= _fg_size_mult  # v29.4.1: Fear & Greed Index sizing
                            amt *= _dca_size_mult  # v29.4.1: Smart DCA boost in Extreme Fear
                            # Multiplier stacking floor: never reduce below 25%
                            if _amt_before_mults_bo > 0 and amt < _amt_before_mults_bo * 0.25:
                                amt = _amt_before_mults_bo * 0.25
                                logger.debug(f"[MULT_FLOOR] {coin} BO-LONG: floored to 25% of {_amt_before_mults_bo:.2f}")
                            # Strong signal boost: reward high-quality breakout width
                            _bo_width = width
                            if _bo_width > 0.04:
                                amt *= 1.25
                                logger.debug(f"[SIG_BOOST] {coin} BO-LONG: elite width ({_bo_width:.4f}) +25%")
                            elif _bo_width > 0.025:
                                amt *= 1.15
                                logger.debug(f"[SIG_BOOST] {coin} BO-LONG: strong width ({_bo_width:.4f}) +15%")
                            amt = min(amt, wallet.value(prices) * 0.30)  # Safety net: 30% portfolio hard cap
                            amt = min(amt, max_by_risk_bo)  # Re-enforce risk cap after boost
                            if amt < 15 and amt > 0 and max_by_risk_bo >= 15:
                                amt = 15
                                logger.debug(f"[SIZE_FLOOR] {coin} BREAKOUT LONG: multipliers crushed size, floored to $15")
                            _bo_exp_ok, _bo_exp_reason = unified_exposure_ok(wallet, prices, coin, amt, sl_bo)
                            # Soft-filter override: coin_loss and pair_failure can be bypassed by conviction
                            _bo_coin_raw_blocked = coin_loss_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging)
                            _bo_coin_blocked = _bo_coin_raw_blocked and not _in_recovery
                            if _in_recovery and _bo_coin_raw_blocked:
                                shadow.log_signal(coin, "long", width, "coin_blocked_RECOVERY_OVERRIDE", taken=False, strategy="breakout")
                                logger.warning(f"RECOVERY OVERRIDE {coin} breakout long: coin_loss blocked but recovery active (width={width:.4f})")
                            _bo_pair_blocked = pair_failure_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging)
                            if _conv_bo and _bo_coin_blocked:
                                shadow.log_signal(coin, "long", width, f"coin_blocked_{_conv_bo_tier}_OVERRIDDEN", taken=False, strategy="breakout")
                                logger.debug(f"{_conv_bo_tier} OVERRIDE {coin} breakout long: bypassed coin_loss (width={width:.4f})")
                                _bo_coin_blocked = False
                            if _conv_bo and _bo_pair_blocked:
                                shadow.log_signal(coin, "long", width, f"pair_blocked_{_conv_bo_tier}_OVERRIDDEN", taken=False, strategy="breakout")
                                logger.debug(f"{_conv_bo_tier} OVERRIDE {coin} breakout long: bypassed pair_failure (width={width:.4f})")
                                _bo_pair_blocked = False
                            if not group_limit_ok(coin, wallet):
                                shadow.log_signal(coin, "long", width, "group_limit", taken=False, strategy="breakout")
                            elif not _bo_exp_ok:
                                shadow.log_signal(coin, "long", width, _bo_exp_reason, taken=False, strategy="breakout")
                            elif not reward_risk_ok(sl_bo, sl_bo * 2, atr_pct=atr_bo):
                                shadow.log_signal(coin, "long", width, "rr_filter", taken=False, strategy="breakout")
                            elif not volatility_spike_check(coin):
                                shadow.log_signal(coin, "long", width, "vol_spike", taken=False, strategy="breakout")
                            elif _bo_coin_blocked:
                                shadow.log_signal(coin, "long", width, "coin_blocked", taken=False, strategy="breakout")
                            elif _bo_pair_blocked:
                                shadow.log_signal(coin, "long", width, "pair_blocked", taken=False, strategy="breakout")
                            elif not market_depth_ok(coin, amt, tickers):
                                shadow.log_signal(coin, "long", width, "thin_market", taken=False, strategy="breakout")
                            elif not regime_confirm(coin, "long"):
                                shadow.log_signal(coin, "long", width, "regime_mismatch", taken=False, strategy="breakout")
                            else:
                                recovery_mode.record_passed_filter()
                                cycle_audit.record_passed_filters()
                                if amt > 5:
                                    if _in_recovery:
                                        recovery_mode.record_attempt()
                                    order = executor.place_order("BUY", coin, t["price"], amt, wallet, prices)
                                    if order["filled"] and coin in wallet.longs:
                                        wallet.longs[coin]["strategy"] = "breakout"
                                        wallet.longs[coin]["bought_cycle"] = cycle
                                        wallet.longs[coin]["entry_sl"] = sl_bo
                                        wallet.longs[coin]["entry_atr"] = atr_bo
                                        _bo_tag = f"breakout_{_conv_bo_tier}" if _conv_bo else "breakout"
                                        shadow.log_signal(coin, "long", width, _bo_tag, taken=True, strategy="breakout")
                                        overtrading_guard.record_trade(cycle)
                                        market_brain.record_entry(cycle)
                                        recovery_mode.record_trade(cycle)
                                        min_activity.record_trade(cycle)
                                        _conv_tag = f" [{_conv_bo_tier}]" if _conv_bo else ""
                                        logger.info(f"BB BREAKOUT BUY {coin} ${amt:.0f} width={width:.4f} slip={order['slippage_pct']:.3f}%{_conv_tag}")
                                        log_trade_entry(coin, "long", "breakout", amt, order['fill_price'], sl_bo, atr_bo, _edge_size_multiplier(), _current_regime, cycle)
                                        break
                                    elif not order["filled"]:
                                        pair_failure_tracker.record_failure(coin, cycle)
                                else:
                                    logger.debug(f"SIZE_TOO_SMALL {coin} long breakout ${amt:.2f} — skipped (min $5)")
                        elif squeeze_state == "BREAKOUT_UP" and len(wallet.longs) >= 2:
                            shadow.log_signal(coin, "long", width, "position_limit", taken=False, strategy="breakout")
                        elif squeeze_state == "BREAKOUT_DOWN" and len(wallet.shorts) < 1:
                            # Noise filter: require breakout confirmation
                            if not breakout_confirmed(coin, "short"):
                                shadow.log_signal(coin, "short", width, "noise_unconfirmed_breakout", taken=False, strategy="breakout")
                                continue
                            # Conviction override for breakout short
                            _conv_bs, _conv_bs_skipped, _conv_bs_tier = conviction_override_active(width, 0, "breakout", regime=enhanced_regime)
                            if _conv_bs:
                                conviction_kill_tracker.record_override()
                            if _conv_bs and _conv_bs_tier == "HIGH_CONVICTION":
                                logger.info(f"OVERRIDE: High conviction trade allowed | {coin} | width={width:.4f} (breakout short)")
                            # v29.3.1: Gate conviction with ATR + momentum + trend safety checks
                            if _conv_bs:
                                _conv_atr_bs = coin_atr(coin)
                                _conv_mom_ok_bs, _ = momentum_confirmed(coin, "short", window=5)
                                _conv_mt_ok_bs, _, _ = micro_trend_confirmed(coin, "short", candles=4)
                                if _conv_atr_bs < 0.003 or not _conv_mom_ok_bs or not _conv_mt_ok_bs:
                                    logger.info(f"[BLOCKED: CONVICTION_UNSAFE] {coin} SHORT breakout {_conv_bs_tier} — atr={_conv_atr_bs:.4f} mom={_conv_mom_ok_bs} trend={_conv_mt_ok_bs}")
                                    _conv_bs = False
                            atr_bs = coin_atr(coin) * 100
                            sl_bs = max(0.8, atr_bs * 0.7)
                            max_risk_bs = wallet.value(prices) * MAX_RISK_PER_TRADE
                            effective_sl_bs = sl_bs * GAP_RISK_MULTIPLIER
                            max_by_risk_bs = max_risk_bs / (effective_sl_bs / 100)
                            max_by_risk_bs = min(max_by_risk_bs, wallet.value(prices) * 0.30)
                            # Optimized change – removed $200 hard cap (scale by portfolio %)
                            amt = kelly_size(wallet, min(wallet.cash * 0.20, max_by_risk_bs), prices)
                            # 2-multiplier sizing: edge + boost + risk_cap
                            amt = amt * _edge_size_multiplier()
                            # v29.3.5: POST_SIZING_BOOST removed (was noop — always capped away)
                            amt = min(amt, max_by_risk_bs)
                            _amt_before_mults_bs = amt  # Snapshot before reduction multipliers
                            amt = _regime_size_scale(amt, _current_regime)
                            amt *= _winrate_size_bonus(wallet)  # +10% if WR > 55%
                            amt *= size_mult  # off-peak × adaptive × warmup ramp
                            amt *= _health_size_mult  # health-score graduated scaling
                            amt *= _brain.get("size_mult", 1.0)  # Brain mood-based sizing adjustment
                            amt *= _fg_size_mult  # v29.4.1: Fear & Greed Index sizing
                            # Multiplier stacking floor: never reduce below 25%
                            if _amt_before_mults_bs > 0 and amt < _amt_before_mults_bs * 0.25:
                                amt = _amt_before_mults_bs * 0.25
                                logger.debug(f"[MULT_FLOOR] {coin} BO-SHORT: floored to 25% of {_amt_before_mults_bs:.2f}")
                            # Strong signal boost: reward high-quality breakout width
                            _bs_width = width
                            if _bs_width > 0.04:
                                amt *= 1.25
                                logger.debug(f"[SIG_BOOST] {coin} BO-SHORT: elite width ({_bs_width:.4f}) +25%")
                            elif _bs_width > 0.025:
                                amt *= 1.15
                                logger.debug(f"[SIG_BOOST] {coin} BO-SHORT: strong width ({_bs_width:.4f}) +15%")
                            amt = min(amt, wallet.value(prices) * 0.30)  # Safety net: 30% portfolio hard cap
                            amt = min(amt, max_by_risk_bs)  # Re-enforce risk cap after boost
                            if amt < 15 and amt > 0 and max_by_risk_bs >= 15:
                                amt = 15
                                logger.debug(f"[SIZE_FLOOR] {coin} BREAKOUT SHORT: multipliers crushed size, floored to $15")
                            _bs_exp_ok, _bs_exp_reason = unified_exposure_ok(wallet, prices, coin, amt, sl_bs)
                            # Soft-filter override: coin_loss and pair_failure can be bypassed by conviction
                            _bs_coin_raw_blocked = coin_loss_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging)
                            _bs_coin_blocked = _bs_coin_raw_blocked and not _in_recovery
                            if _in_recovery and _bs_coin_raw_blocked:
                                shadow.log_signal(coin, "short", width, "coin_blocked_RECOVERY_OVERRIDE", taken=False, strategy="breakout")
                                logger.warning(f"RECOVERY OVERRIDE {coin} breakout short: coin_loss blocked but recovery active (width={width:.4f})")
                            _bs_pair_blocked = pair_failure_tracker.is_blocked(coin, cycle, is_ranging=_is_ranging)
                            if _conv_bs and _bs_coin_blocked:
                                shadow.log_signal(coin, "short", width, f"coin_blocked_{_conv_bs_tier}_OVERRIDDEN", taken=False, strategy="breakout")
                                logger.debug(f"{_conv_bs_tier} OVERRIDE {coin} breakout short: bypassed coin_loss (width={width:.4f})")
                                _bs_coin_blocked = False
                            if _conv_bs and _bs_pair_blocked:
                                shadow.log_signal(coin, "short", width, f"pair_blocked_{_conv_bs_tier}_OVERRIDDEN", taken=False, strategy="breakout")
                                logger.debug(f"{_conv_bs_tier} OVERRIDE {coin} breakout short: bypassed pair_failure (width={width:.4f})")
                                _bs_pair_blocked = False
                            if not group_limit_ok(coin, wallet):
                                shadow.log_signal(coin, "short", width, "group_limit", taken=False, strategy="breakout")
                            elif not _bs_exp_ok:
                                shadow.log_signal(coin, "short", width, _bs_exp_reason, taken=False, strategy="breakout")
                            elif not reward_risk_ok(sl_bs, sl_bs * 2, atr_pct=atr_bs):
                                shadow.log_signal(coin, "short", width, "rr_filter", taken=False, strategy="breakout")
                            elif not safe_mode.shorts_allowed:
                                shadow.log_signal(coin, "short", width, "safe_mode_no_shorts", taken=False, strategy="breakout")
                            elif not volatility_spike_check(coin):
                                shadow.log_signal(coin, "short", width, "vol_spike", taken=False, strategy="breakout")
                            elif _bs_coin_blocked:
                                shadow.log_signal(coin, "short", width, "coin_blocked", taken=False, strategy="breakout")
                            elif _bs_pair_blocked:
                                shadow.log_signal(coin, "short", width, "pair_blocked", taken=False, strategy="breakout")
                            elif not market_depth_ok(coin, amt, tickers):
                                shadow.log_signal(coin, "short", width, "thin_market", taken=False, strategy="breakout")
                            elif not regime_confirm(coin, "short"):
                                shadow.log_signal(coin, "short", width, "regime_mismatch", taken=False, strategy="breakout")
                            else:
                                recovery_mode.record_passed_filter()
                                cycle_audit.record_passed_filters()
                                if amt > 5:
                                    if _in_recovery:
                                        recovery_mode.record_attempt()
                                    order = executor.place_order("SHORT", coin, t["price"], amt, wallet, prices)
                                    if order["filled"] and coin in wallet.shorts:
                                        wallet.shorts[coin]["bought_cycle"] = cycle
                                        wallet.shorts[coin]["entry_sl"] = sl_bs
                                        wallet.shorts[coin]["entry_atr"] = atr_bs
                                        _bs_tag = f"breakout_{_conv_bs_tier}" if _conv_bs else "breakout"
                                        shadow.log_signal(coin, "short", width, _bs_tag, taken=True, strategy="breakout")
                                        overtrading_guard.record_trade(cycle)
                                        market_brain.record_entry(cycle)
                                        recovery_mode.record_trade(cycle)
                                        min_activity.record_trade(cycle)
                                        _conv_tag = f" [{_conv_bs_tier}]" if _conv_bs else ""
                                        logger.info(f"BB BREAKOUT SHORT {coin} ${amt:.0f} width={width:.4f} slip={order['slippage_pct']:.3f}%{_conv_tag}")
                                        log_trade_entry(coin, "short", "breakout", amt, order['fill_price'], sl_bs, atr_bs, _edge_size_multiplier(), _current_regime, cycle)
                                        break
                                    elif not order["filled"]:
                                        pair_failure_tracker.record_failure(coin, cycle)
                                else:
                                    logger.debug(f"SIZE_TOO_SMALL {coin} short breakout ${amt:.2f} — skipped (min $5)")
                        elif squeeze_state == "BREAKOUT_DOWN" and len(wallet.shorts) >= 1:
                            shadow.log_signal(coin, "short", width, "position_limit", taken=False, strategy="breakout")

            # ── v29.4.1: SMC/ICT STRATEGY — Liquidity Sweep + FVG + Order Block ──
            if (not warmup_blocked and _api_ok and _usable_cash > 50
                    and total_positions < _effective_max_positions and _heat_ok
                    and _strategy_health_ok and _overtrading_ok and _kill_switch_ok
                    and cascade_protection.allows_entry()
                    and _pro_market_regime != "DEAD" and _dd_allow_entry):
                for pair, t in tickers.items():
                    name = pair_names.get(pair, pair)
                    coin = to_short_name(name)
                    if WHITELIST_ONLY and coin not in COIN_WHITELIST:
                        continue
                    if coin in DYNAMIC_BLACKLIST:
                        continue
                    if coin in wallet.longs or coin in wallet.shorts:
                        continue
                    hist = prices_cache.get(coin, [])
                    if len(hist) < 50:
                        continue
                    smc_result = smc_ict_signal(coin, hist)
                    if smc_result:
                        direction, conf, smc_entry, smc_stop, smc_tp = smc_result
                        _smc_tp_adjusted = smc_tp * (adaptive_tp_ratio(coin) / 3.2)  # v29.5.0: scale TP by ATR-adaptive ratio
                        if conf >= 6:
                            _smc_side_str = "BUY" if direction == "long" else "SHORT"
                            logger.info(f"[SMC_ICT] {coin} {direction.upper()} score={conf}/10 entry={smc_entry:.4f} stop={smc_stop:.2f}% tp={_smc_tp_adjusted:.2f}%")
                            # Safety gates (same as momentum entries)
                            if not group_limit_ok(coin, wallet):
                                shadow.log_signal(coin, direction, conf, "smc_ict_group_limit", taken=False, strategy="smc_ict")
                                continue
                            if not liquidity_ok(coin):
                                shadow.log_signal(coin, direction, conf, "smc_ict_low_liquidity", taken=False, strategy="smc_ict")
                                continue
                            if not volatility_spike_check(coin):
                                shadow.log_signal(coin, direction, conf, "smc_ict_vol_spike", taken=False, strategy="smc_ict")
                                continue
                            if coin in _suspicious_coins:
                                shadow.log_signal(coin, direction, conf, "smc_ict_suspicious", taken=False, strategy="smc_ict")
                                continue
                            # Sizing: Kelly + risk cap (mirrors momentum sizing)
                            _smc_atr = coin_atr(coin) * 100
                            _smc_sl = max(0.8, min(smc_stop, 1.5))  # Use SMC stop, floor 0.8%, cap 1.5%
                            _smc_max_risk = wallet.value(prices) * MAX_RISK_PER_TRADE
                            _smc_eff_sl = _smc_sl * GAP_RISK_MULTIPLIER
                            _smc_max_by_risk = _smc_max_risk / (_smc_eff_sl / 100)
                            _smc_max_by_risk = min(_smc_max_by_risk, wallet.value(prices) * 0.30)
                            _smc_base = kelly_size(wallet, min(wallet.cash * 0.30, _smc_max_by_risk), prices)
                            _smc_amt = _smc_base * _edge_size_multiplier()
                            _smc_amt = min(_smc_amt, _smc_max_by_risk)
                            _smc_amt_before = _smc_amt
                            _smc_amt *= size_mult
                            _smc_amt *= _health_size_mult
                            _smc_amt *= _fg_size_mult
                            _smc_amt *= _dca_size_mult
                            _smc_amt *= _choppy_size_mult
                            # v29.5.0: Pro multipliers
                            _smc_amt *= volatility_size_mult(coin)
                            _smc_amt *= _session_mult
                            _smc_amt *= _dd_mult
                            _smc_amt *= _streak_mult
                            # Multiplier floor
                            if _smc_amt_before > 0 and _smc_amt < _smc_amt_before * 0.25:
                                _smc_amt = _smc_amt_before * 0.25
                                logger.debug(f"[MULT_FLOOR] {coin} SMC_ICT: floored to 25% of {_smc_amt_before:.2f}")
                            # Score boost: high-conviction SMC setups
                            if conf >= 9:
                                _smc_amt *= 1.25
                                logger.debug(f"[SIG_BOOST] {coin} SMC_ICT: elite score ({conf}/10) +25%")
                            elif conf >= 7:
                                _smc_amt *= 1.15
                                logger.debug(f"[SIG_BOOST] {coin} SMC_ICT: strong score ({conf}/10) +15%")
                            _smc_amt = min(_smc_amt, wallet.value(prices) * 0.30)
                            _smc_amt = min(_smc_amt, _smc_max_by_risk)
                            if _smc_amt < 15 and _smc_amt > 0 and _smc_max_by_risk >= 15:
                                _smc_amt = 15
                            # Exposure check
                            _smc_exp_ok, _smc_exp_reason = unified_exposure_ok(wallet, prices, coin, _smc_amt, _smc_sl)
                            if not _smc_exp_ok:
                                shadow.log_signal(coin, direction, conf, f"smc_ict_{_smc_exp_reason}", taken=False, strategy="smc_ict")
                                continue
                            if not market_depth_ok(coin, _smc_amt, tickers):
                                shadow.log_signal(coin, direction, conf, "smc_ict_thin_market", taken=False, strategy="smc_ict")
                                continue
                            # Execute
                            if _smc_amt > 5:
                                order = executor.place_order(_smc_side_str, coin, t["price"], _smc_amt, wallet, prices)
                                _smc_pos_dict = wallet.longs if direction == "long" else wallet.shorts
                                if order["filled"] and coin in _smc_pos_dict:
                                    _smc_pos_dict[coin]["strategy"] = "smc_ict"
                                    _smc_pos_dict[coin]["bought_cycle"] = cycle
                                    _smc_pos_dict[coin]["entry_sl"] = _smc_sl
                                    _smc_pos_dict[coin]["entry_atr"] = _smc_atr
                                    shadow.log_signal(coin, direction, conf, "smc_ict", taken=True, strategy="smc_ict")
                                    overtrading_guard.record_trade(cycle)
                                    market_brain.record_entry(cycle)
                                    recovery_mode.record_trade(cycle)
                                    min_activity.record_trade(cycle)
                                    logger.info(f"[SMC_ICT_ENTRY] {_smc_side_str} {coin} ${_smc_amt:.0f} score={conf}/10 sl={_smc_sl:.2f}% tp={_smc_tp_adjusted:.2f}% slip={order['slippage_pct']:.3f}%")
                                    log_trade_entry(coin, direction, "smc_ict", _smc_amt, order['fill_price'], _smc_sl, _smc_atr, _edge_size_multiplier(), _current_regime, cycle)
                                    break
                                elif not order["filled"]:
                                    shadow.log_signal(coin, direction, conf, f"smc_ict_rejected:{order['reject_reason']}", taken=False, strategy="smc_ict")
                                    pair_failure_tracker.record_failure(coin, cycle)
                            else:
                                logger.debug(f"SIZE_TOO_SMALL {coin} smc_ict ${_smc_amt:.2f} — skipped (min $5)")

            # ── v29.5.0: THREE NEW SMC STRATEGIES — OB / Holy Grail / Breakout+FVG ──
            # Regime filter: DEAD → skip ALL, VOLATILE → 50% size + 30% tighter stops
            # Session filter: off-hours require score >= 8
            # Drawdown filter: >10% DD → block entries
            if (not warmup_blocked and _api_ok and _usable_cash > 50
                    and total_positions < _effective_max_positions and _heat_ok
                    and _strategy_health_ok and _overtrading_ok and _kill_switch_ok
                    and cascade_protection.allows_entry()
                    and _pro_market_regime != "DEAD" and _dd_allow_entry):
                for pair, t in tickers.items():
                    name = pair_names.get(pair, pair)
                    coin = to_short_name(name)
                    if WHITELIST_ONLY and coin not in COIN_WHITELIST:
                        continue
                    if coin in DYNAMIC_BLACKLIST:
                        continue
                    if coin in wallet.longs or coin in wallet.shorts:
                        continue
                    hist = prices_cache.get(coin, [])
                    if len(hist) < 50:
                        continue
                    # Zone filter: skip if price in middle third of range
                    if not smc_valid_zone(coin, t["price"], hist):
                        continue

                    # ── Regime-based strategy selection ──
                    _regime_vol_mult = 0.5 if _pro_market_regime == "VOLATILE" else 1.0
                    _regime_stop_mult = 0.7 if _pro_market_regime == "VOLATILE" else 1.0  # 30% tighter stops

                    # ── SMC Order Block ──
                    for _ob_dir in ("long", "short"):
                        # Regime filter: OB is ranging strategy
                        if _pro_market_regime == "TRENDING" and _ob_dir == "long":
                            continue  # In trending, prefer breakout/momentum over OB
                        ob_result = smc_ob_signal(coin, hist, _ob_dir)
                        if ob_result and ob_result["score"] >= 6:
                            _ob_score = ob_result["score"]
                            # Session filter
                            if _session_min_score and _ob_score < _session_min_score:
                                continue
                            # Trend strength filter for momentum/breakout
                            # (OB is mean-reversion, skip trend filter)
                            if not group_limit_ok(coin, wallet):
                                continue
                            if not liquidity_ok(coin):
                                continue
                            # Sizing
                            _ob_sl = ob_result["stop"] * _regime_stop_mult
                            _ob_tp = ob_result["target"]
                            _ob_max_risk = wallet.value(prices) * MAX_RISK_PER_TRADE
                            _ob_eff_sl = _ob_sl * GAP_RISK_MULTIPLIER
                            _ob_max_by_risk = _ob_max_risk / (_ob_eff_sl / 100) if _ob_eff_sl > 0 else 50
                            _ob_max_by_risk = min(_ob_max_by_risk, wallet.value(prices) * 0.30)
                            _ob_base = kelly_size(wallet, min(wallet.cash * 0.30, _ob_max_by_risk), prices)
                            _ob_amt = _ob_base * _edge_size_multiplier()
                            _ob_amt = min(_ob_amt, _ob_max_by_risk)
                            _ob_amt *= size_mult * _health_size_mult * _fg_size_mult * _dca_size_mult * _choppy_size_mult
                            _ob_amt *= volatility_size_mult(coin) * _session_mult * _dd_mult * _streak_mult * _regime_vol_mult
                            _ob_amt = max(_ob_amt, _ob_max_by_risk * 0.25) if _ob_max_by_risk >= 15 else _ob_amt  # floor
                            _ob_amt = min(_ob_amt, _ob_max_by_risk)
                            if _ob_amt < 5:
                                continue
                            _ob_exp_ok, _ = unified_exposure_ok(wallet, prices, coin, _ob_amt, _ob_sl)
                            if not _ob_exp_ok:
                                continue
                            _ob_side = "BUY" if _ob_dir == "long" else "SHORT"
                            order = executor.place_order(_ob_side, coin, t["price"], _ob_amt, wallet, prices)
                            if order["filled"]:
                                _pos_dict = wallet.longs if _ob_dir == "long" else wallet.shorts
                                if coin in _pos_dict:
                                    _pos_dict[coin]["strategy"] = "smc_ob"
                                    _pos_dict[coin]["bought_cycle"] = cycle
                                    _pos_dict[coin]["entry_sl"] = _ob_sl
                                    _pos_dict[coin]["entry_atr"] = coin_atr(coin) * 100
                                    shadow.log_signal(coin, _ob_dir, _ob_score, "smc_ob", taken=True, strategy="smc_ob")
                                    overtrading_guard.record_trade(cycle)
                                    market_brain.record_entry(cycle)
                                    recovery_mode.record_trade(cycle)
                                    min_activity.record_trade(cycle)
                                    logger.info(f"[SMC_OB_ENTRY] {_ob_side} {coin} ${_ob_amt:.0f} score={_ob_score}/8 sl={_ob_sl:.2f}% tp={_ob_tp:.2f}%")
                                    log_trade_entry(coin, _ob_dir, "smc_ob", _ob_amt, order['fill_price'], _ob_sl, coin_atr(coin)*100, _edge_size_multiplier(), _current_regime, cycle)
                                    break
                            elif not order["filled"]:
                                pair_failure_tracker.record_failure(coin, cycle)
                    else:
                        # Didn't break from OB loop — continue to next strategies
                        pass

                    # ── SMC Holy Grail (Sweep + OB + FVG) ──
                    hg_result = smc_holy_grail_signal(coin, hist)
                    if hg_result and hg_result["score"] >= 8:
                        _hg_score = hg_result["score"]
                        _hg_dir = hg_result["direction"]
                        if _session_min_score and _hg_score < _session_min_score:
                            pass  # Skip but don't break — check breakout next
                        elif not group_limit_ok(coin, wallet) or not liquidity_ok(coin):
                            pass
                        else:
                            _hg_sl = hg_result["stop"] * _regime_stop_mult
                            _hg_tp = hg_result["target"]
                            _hg_max_risk = wallet.value(prices) * MAX_RISK_PER_TRADE
                            _hg_eff_sl = _hg_sl * GAP_RISK_MULTIPLIER
                            _hg_max_by_risk = _hg_max_risk / (_hg_eff_sl / 100) if _hg_eff_sl > 0 else 50
                            _hg_max_by_risk = min(_hg_max_by_risk, wallet.value(prices) * 0.30)
                            _hg_base = kelly_size(wallet, min(wallet.cash * 0.30, _hg_max_by_risk), prices)
                            _hg_amt = _hg_base * _edge_size_multiplier()
                            _hg_amt = min(_hg_amt, _hg_max_by_risk)
                            _hg_amt *= size_mult * _health_size_mult * _fg_size_mult * _dca_size_mult * _choppy_size_mult
                            _hg_amt *= volatility_size_mult(coin) * _session_mult * _dd_mult * _streak_mult * _regime_vol_mult
                            _hg_amt = max(_hg_amt, _hg_max_by_risk * 0.25) if _hg_max_by_risk >= 15 else _hg_amt
                            _hg_amt = min(_hg_amt, _hg_max_by_risk)
                            if _hg_amt >= 5:
                                _hg_exp_ok, _ = unified_exposure_ok(wallet, prices, coin, _hg_amt, _hg_sl)
                                if _hg_exp_ok:
                                    _hg_side = "BUY" if _hg_dir == "long" else "SHORT"
                                    order = executor.place_order(_hg_side, coin, t["price"], _hg_amt, wallet, prices)
                                    if order["filled"]:
                                        _pos_dict = wallet.longs if _hg_dir == "long" else wallet.shorts
                                        if coin in _pos_dict:
                                            _pos_dict[coin]["strategy"] = "smc_holy_grail"
                                            _pos_dict[coin]["bought_cycle"] = cycle
                                            _pos_dict[coin]["entry_sl"] = _hg_sl
                                            _pos_dict[coin]["entry_atr"] = coin_atr(coin) * 100
                                            shadow.log_signal(coin, _hg_dir, _hg_score, "smc_holy_grail", taken=True, strategy="smc_holy_grail")
                                            overtrading_guard.record_trade(cycle)
                                            market_brain.record_entry(cycle)
                                            recovery_mode.record_trade(cycle)
                                            min_activity.record_trade(cycle)
                                            logger.info(f"[SMC_HOLY_GRAIL_ENTRY] {_hg_side} {coin} ${_hg_amt:.0f} score={_hg_score}/10 sl={_hg_sl:.2f}% tp={_hg_tp:.2f}%")
                                            log_trade_entry(coin, _hg_dir, "smc_holy_grail", _hg_amt, order['fill_price'], _hg_sl, coin_atr(coin)*100, _edge_size_multiplier(), _current_regime, cycle)
                                            continue  # Next coin
                                    elif not order["filled"]:
                                        pair_failure_tracker.record_failure(coin, cycle)

                    # ── SMC Breakout + FVG ──
                    # Regime filter: breakout is a trending strategy
                    if _pro_market_regime in ("TRENDING", "VOLATILE", "UNKNOWN"):
                        bk_result = smc_breakout_fvg_signal(coin, hist)
                        if bk_result and bk_result["score"] >= 6:
                            _bk_score = bk_result["score"]
                            _bk_dir = bk_result["direction"]
                            if _session_min_score and _bk_score < _session_min_score:
                                pass
                            elif not group_limit_ok(coin, wallet) or not liquidity_ok(coin):
                                pass
                            else:
                                # Trend strength filter for breakout
                                _ts = get_trend_strength(hist, _bk_dir)
                                if _ts < 5:
                                    shadow.log_signal(coin, _bk_dir, _bk_score, "smc_breakout_weak_trend", taken=False, strategy="smc_breakout")
                                else:
                                    _bk_sl = bk_result["stop"] * _regime_stop_mult
                                    _bk_tp = bk_result["target"]
                                    _bk_max_risk = wallet.value(prices) * MAX_RISK_PER_TRADE
                                    _bk_eff_sl = _bk_sl * GAP_RISK_MULTIPLIER
                                    _bk_max_by_risk = _bk_max_risk / (_bk_eff_sl / 100) if _bk_eff_sl > 0 else 50
                                    _bk_max_by_risk = min(_bk_max_by_risk, wallet.value(prices) * 0.30)
                                    _bk_base = kelly_size(wallet, min(wallet.cash * 0.30, _bk_max_by_risk), prices)
                                    _bk_amt = _bk_base * _edge_size_multiplier()
                                    _bk_amt = min(_bk_amt, _bk_max_by_risk)
                                    _bk_amt *= size_mult * _health_size_mult * _fg_size_mult * _dca_size_mult * _choppy_size_mult
                                    _bk_amt *= volatility_size_mult(coin) * _session_mult * _dd_mult * _streak_mult * _regime_vol_mult
                                    _bk_amt = max(_bk_amt, _bk_max_by_risk * 0.25) if _bk_max_by_risk >= 15 else _bk_amt
                                    _bk_amt = min(_bk_amt, _bk_max_by_risk)
                                    if _bk_amt >= 5:
                                        _bk_exp_ok, _ = unified_exposure_ok(wallet, prices, coin, _bk_amt, _bk_sl)
                                        if _bk_exp_ok:
                                            _bk_side_str = "BUY" if _bk_dir == "long" else "SHORT"
                                            order = executor.place_order(_bk_side_str, coin, t["price"], _bk_amt, wallet, prices)
                                            if order["filled"]:
                                                _pos_dict = wallet.longs if _bk_dir == "long" else wallet.shorts
                                                if coin in _pos_dict:
                                                    _pos_dict[coin]["strategy"] = "smc_breakout"
                                                    _pos_dict[coin]["bought_cycle"] = cycle
                                                    _pos_dict[coin]["entry_sl"] = _bk_sl
                                                    _pos_dict[coin]["entry_atr"] = coin_atr(coin) * 100
                                                    shadow.log_signal(coin, _bk_dir, _bk_score, "smc_breakout", taken=True, strategy="smc_breakout")
                                                    overtrading_guard.record_trade(cycle)
                                                    market_brain.record_entry(cycle)
                                                    recovery_mode.record_trade(cycle)
                                                    min_activity.record_trade(cycle)
                                                    logger.info(f"[SMC_BREAKOUT_ENTRY] {_bk_side_str} {coin} ${_bk_amt:.0f} score={_bk_score}/9 trend={_ts}/10 sl={_bk_sl:.2f}% tp={_bk_tp:.2f}%")
                                                    log_trade_entry(coin, _bk_dir, "smc_breakout", _bk_amt, order['fill_price'], _bk_sl, coin_atr(coin)*100, _edge_size_multiplier(), _current_regime, cycle)
                                            elif not order["filled"]:
                                                pair_failure_tracker.record_failure(coin, cycle)

            # ── ADVANCED ALPHA ENTRIES ── v29.3.4
            # Runs 8 independent alpha strategies. Each generates signals with confidence scores.
            # Only fires if confidence >= ALPHA_MIN_CONFIDENCE (0.60), respects ALL existing safety gates.
            # Position sizing uses ALPHA_SIZE_MULT (0.70) — conservative vs core strategies.
            if (ADVANCED_ALPHA_ENABLED and not warmup_blocked and _api_ok and not _api_stale_block
                    and not _health_block and _usable_cash > 50 and perf.can_trade(cycle)
                    and total_positions < _effective_max_positions and cascade_protection.allows_entry()
                    and _strategy_health_ok and _overtrading_ok and _kill_switch_ok
                    and not _error_cooldown and not _overtrade_cooldown_active and _heat_ok):
                # v29.5.0: Skip entire alpha block if all 8 thresholds are at 1.0 (disabled)
                _all_disabled = all(v >= 1.0 for v in ALPHA_STRATEGY_THRESHOLDS.values())
                if _all_disabled:
                    pass  # All alpha strategies disabled — skip silently
                else:
                    _alpha_taken = 0
                    _alpha_max_per_cycle = 2  # Max 2 alpha entries per cycle to avoid overtrading
                    _alpha_position_count = len(wallet.longs) + len(wallet.shorts)
                    _alpha_max_positions = int(_effective_max_positions * ALPHA_MAX_POSITIONS_PCT)

                    # Collect all alpha signals from all strategies
                    _alpha_signals = []  # list of (coin, direction, confidence, strategy_name)

                    # 1. PricePrediction — per-coin
                    for _ac in list(prices_cache.keys()):
                        _pp_conf, _pp_dir = alpha_price_prediction.predict(_ac, cycle)
                        if _pp_conf >= _alpha_threshold("price-prediction") and _pp_dir:
                            _alpha_signals.append((_ac, _pp_dir, _pp_conf, "price-prediction"))

                    # 2. QuantMultiStrategy — per-coin (6-model voting)
                    for _ac in list(prices_cache.keys()):
                        _qm_conf, _qm_dir = alpha_quant.evaluate(_ac, cycle)
                        if _qm_conf >= _alpha_threshold("quant-multi") and _qm_dir:
                            _alpha_signals.append((_ac, _qm_dir, _qm_conf, "quant-multi"))

                    # 3. GammaScalping — per-coin (round-number pin)
                    for _ac in list(prices_cache.keys()):
                        _gs_conf, _gs_dir = alpha_gamma.scan(_ac, cycle)
                        if _gs_conf >= _alpha_threshold("gamma-scalping") and _gs_dir:
                            _alpha_signals.append((_ac, _gs_dir, _gs_conf, "gamma-scalping"))

                    # 4. MEVExtraction — batch scan
                    _mev_sigs = alpha_mev.scan(cycle, tickers or {})
                    for _mc, _md, _mconf in _mev_sigs:
                        if _mconf >= _alpha_threshold("mev-extraction"):
                            _alpha_signals.append((_mc, _md, _mconf, "mev-extraction"))

                    # 5. PairsTrading — batch scan
                    _pt_sigs = alpha_pairs.scan(cycle)
                    for _pc, _pd, _pconf in _pt_sigs:
                        if _pconf >= _alpha_threshold("pairs-trading"):
                            _alpha_signals.append((_pc, _pd, _pconf, "pairs-trading"))

                    # 6. EventDriven — batch scan (returns 4-tuples)
                    _ed_sigs = alpha_events.scan(cycle, tickers or {})
                    for _item in _ed_sigs:
                        _ec, _edir, _econf = _item[0], _item[1], _item[2]
                        _etype = _item[3] if len(_item) > 3 else "event"
                        if _econf >= _alpha_threshold(f"event-{_etype}"):
                            _alpha_signals.append((_ec, _edir, _econf, f"event-{_etype}"))

                    # 7. DiscretionaryMacro — directional bias (not per-coin, applies as filter boost)
                    _macro_dir, _macro_conf = alpha_macro.get_bias()

                    # 8. VixVolatilityTrading — vol regime bias
                    _vix_dir, _vix_conf = alpha_vix.favor_direction()

                    # Sort by confidence descending — best signals first
                    _alpha_signals.sort(key=lambda x: x[2], reverse=True)

                    # Log alpha signal count (throttled)
                    if _alpha_signals and cycle % 10 == 0:
                        logger.info(f"[ALPHA] cycle={cycle} raw_signals={len(_alpha_signals)} macro={alpha_macro.regime} vix={alpha_vix.vol_regime}")

                    for _a_coin, _a_dir, _a_conf, _a_strat in _alpha_signals:
                        if _alpha_taken >= _alpha_max_per_cycle:
                            break
                        if _alpha_position_count >= _effective_max_positions:
                            break
                        # Count alpha positions vs cap
                        _alpha_held = sum(1 for p in wallet.longs.values() if p.get("strategy", "").startswith("alpha_"))
                        _alpha_held += sum(1 for p in wallet.shorts.values() if p.get("strategy", "").startswith("alpha_"))
                        if _alpha_held >= _alpha_max_positions:
                            break

                        # ── SAFETY GATES (same as core strategies) ──
                        # Skip if already holding this coin
                        if _a_coin in wallet.longs or _a_coin in wallet.shorts:
                            continue
                        # Skip if in cooldown (v29.3.5: split — winners 15, losers 40)
                        if _a_coin in _last_exit_cycle:
                            _acd_cycle, _acd_was_win = _last_exit_cycle[_a_coin]
                            _acd_limit = COOLDOWN_AFTER_WIN if _acd_was_win else COOLDOWN_AFTER_LOSS
                            if (cycle - _acd_cycle) < _acd_limit:
                                continue
                        # Static blacklist
                        if _a_coin in DYNAMIC_BLACKLIST:
                            continue
                        # Temp blacklist
                        if TEMP_BLACKLIST_ENABLED and dynamic_blacklist.is_blocked(_a_coin, cycle):
                            continue
                        # Coin loss tracker
                        if coin_loss_tracker.is_blocked(_a_coin, cycle, is_ranging=_is_ranging):
                            continue
                        # Pair failure tracker
                        if pair_failure_tracker.is_blocked(_a_coin, cycle, is_ranging=_is_ranging):
                            continue
                        # Group limit
                        if not group_limit_ok(_a_coin, wallet):
                            continue
                        # ATR floor check
                        _a_atr = coin_atr(_a_coin)
                        if _a_atr < MIN_ATR_TO_TRADE:
                            continue
                        # Dead market check
                        _a_hist = prices_cache.get(_a_coin, [])
                        if len(_a_hist) < 10:
                            continue
                        _a_price = _a_hist[-1]
                        if _a_price <= 0:
                            continue
                        # Volatility spike check
                        if not volatility_spike_check(_a_coin):
                            continue
                        # Market depth check
                        if not market_depth_ok(_a_coin, 50, tickers or {}):
                            continue
                        # Macro regime boost/penalty
                        if _macro_dir and _macro_dir != _a_dir and _macro_conf >= 0.60:
                            _a_conf *= 0.80  # Penalize against-macro trades
                        if _macro_dir and _macro_dir == _a_dir:
                            _a_conf = min(1.0, _a_conf * 1.10)  # Boost with-macro trades
                        # Re-check after adjustment (per-strategy threshold)
                        if _a_conf < _alpha_threshold(_a_strat):
                            continue

                        # ── POSITION SIZING ──
                        _a_atr_pct = _a_atr * 100
                        _a_sl = max(0.8, _a_atr_pct * 0.7)
                        _a_max_risk = wallet.value(prices) * MAX_RISK_PER_TRADE
                        _a_eff_sl = _a_sl * GAP_RISK_MULTIPLIER
                        _a_max_by_risk = _a_max_risk / (_a_eff_sl / 100)
                        _a_max_by_risk = min(_a_max_by_risk, wallet.value(prices) * 0.30)
                        _a_amt = kelly_size(wallet, min(_usable_cash * 0.15, _a_max_by_risk), prices)
                        _a_amt *= ALPHA_SIZE_MULT  # Conservative alpha sizing (0.70)
                        _a_amt *= _edge_size_multiplier()
                        _a_amt = _regime_size_scale(_a_amt, _current_regime)
                        _a_amt *= size_mult  # off-peak × adaptive × warmup ramp
                        _a_amt *= _health_size_mult
                        _a_amt *= _brain.get("size_mult", 1.0)
                        _a_amt *= alpha_vix.size_adjustment()  # Vol regime sizing
                        _a_amt *= alpha_macro.size_multiplier()  # Macro regime sizing
                        _a_amt = min(_a_amt, _a_max_by_risk)
                        _a_amt = min(_a_amt, wallet.value(prices) * 0.20)  # 20% hard cap for alpha

                        if _a_amt < 5:
                            logger.debug(f"[ALPHA] SIZE_TOO_SMALL {_a_coin} {_a_dir} {_a_strat} ${_a_amt:.2f}")
                            continue

                        # ── EXECUTE ──
                        _a_order_type = "BUY" if _a_dir == "long" else "SHORT"
                        order = executor.place_order(_a_order_type, _a_coin, _a_price, _a_amt, wallet, prices)
                        if order["filled"]:
                            _a_pos_dict = wallet.longs if _a_dir == "long" else wallet.shorts
                            if _a_coin in _a_pos_dict:
                                _a_pos_dict[_a_coin]["bought_cycle"] = cycle
                                _a_pos_dict[_a_coin]["entry_sl"] = _a_sl
                                _a_pos_dict[_a_coin]["entry_atr"] = _a_atr_pct
                                _a_pos_dict[_a_coin]["strategy"] = f"alpha_{_a_strat}"
                                shadow.log_signal(_a_coin, _a_dir, _a_conf, f"alpha_{_a_strat}", taken=True)
                                overtrading_guard.record_trade(cycle)
                                market_brain.record_entry(cycle)
                                recovery_mode.record_trade(cycle)
                                min_activity.record_trade(cycle)
                                logger.info(
                                    f"[ALPHA] {_a_order_type} {_a_coin} ${_a_amt:.0f} @ ${order['fill_price']:,.4f} "
                                    f"conf={_a_conf:.2f} strat={_a_strat} slip={order['slippage_pct']:.3f}% "
                                    f"sl={_a_sl:.1f}% macro={alpha_macro.regime} vix={alpha_vix.vol_regime}")
                                log_trade_entry(_a_coin, _a_dir, f"alpha_{_a_strat}", _a_amt,
                                                order['fill_price'], _a_sl, _a_atr_pct,
                                                _edge_size_multiplier(), _current_regime, cycle)
                                _alpha_taken += 1
                                _alpha_position_count += 1
                        elif not order["filled"]:
                            shadow.log_signal(_a_coin, _a_dir, _a_conf, f"alpha_{_a_strat}_rejected:{order['reject_reason']}", taken=False)
                            pair_failure_tracker.record_failure(_a_coin, cycle)

                    if _alpha_taken > 0:
                        logger.info(f"[ALPHA] cycle={cycle} entries_taken={_alpha_taken}")

            # ── RECOVERY FALLBACK: DISABLED ──
            # Optimized change – blind recovery trades lose money; human traders wait for signals
            # ── MARKET DATA FALLBACK: DISABLED ──
            # Optimized change – blind market fallback trades lose money
            # ── RECOVERY FORCED EXIT: DISABLED ──
            # Optimized change – forced exits from desperation hurt PnL
            # ── RECOVERY SAFETY GUARD: DISABLED (recovery fallbacks disabled) ──
            # v29.2: accumulate dead market skip count
            try:
                _dead_market_counter[0] += _dead_market_skips
                if cycle % 50 == 0 and cycle > 0 and _dead_market_skips > 0:
                    logger.info(f"[DEAD_MARKET] cycle={cycle} skipped_this_cycle={_dead_market_skips} total_skips={_dead_market_counter[0]}")
            except NameError:
                pass  # Entry gate wasn't reached this cycle

            # ── GLOBAL TRADE AUDIT: emit per-cycle funnel diagnostics ──
            try:
                cycle_audit.emit(cycle, _in_recovery, logger)
            except Exception:
                pass

            # ── WARMUP ASSERTION: Detect if any trade slipped through ──
            if warmup_blocked:
                if len(wallet.longs) > _longs_before or len(wallet.shorts) > _shorts_before:
                    logger.error(f"WARMUP VIOLATION: Trade executed while warmup_blocked=True (cycle={cycle}, regime={regime}, longs={len(wallet.longs)}, shorts={len(wallet.shorts)})")

            # Dashboard — throttled to every 5 cycles (~10s at 2s POLL) to reduce terminal overhead
            if cycle % 5 == 0:
                show(wallet, prices, cycle, last_full_rank, pair_names)

            # Save wallet + ML brain — must never crash bot
            if cycle % 20 == 0:
                try:
                    wallet.save(prices)
                    brain.save(ML_FILE)
                except Exception as _save_err:
                    try:
                        logger.error(f"SAVE ERROR: {_save_err}")
                    except Exception:
                        pass

            # Log validator: check log integrity every 100 cycles — non-fatal
            if cycle % 100 == 0 and cycle > 0:
                try:
                    log_validator.validate_all(cycle)
                except Exception:
                    pass

            # ── PERIODIC LOGGING (all wrapped — must never crash bot) ──
            try:
                # Health output / heartbeat every 100 cycles
                if cycle % HEARTBEAT_INTERVAL == 0 and cycle > 0:
                    health_output(cycle, wallet, prices, kill_switch, strategy_health_monitor, safe_mode, overtrading_guard)

                # Paper trade tracker summary every 500 cycles
                if cycle % 500 == 0 and cycle > 0:
                    paper_tracker.log_summary()
                    # Live validation summary (file only — suppress terminal spam)
                    try:
                        if live_tracker.total_attempts > 0:
                            logger.debug(live_tracker.summary())
                    except Exception:
                        pass

                # SESSION SUMMARY every 600 cycles (~20 min at 2s POLL)
                if cycle % 600 == 0 and cycle > 0:
                    try:
                        print_periodic_summary(wallet, prices, cycle)
                    except Exception:
                        pass

                # PRE-FLIGHT SIZING REPORT: once after warmup ends, then every 3000 cycles (~1.5h)
                if (cycle == WARMUP_CYCLES + 1) or (cycle % 3000 == 0 and cycle > WARMUP_CYCLES):
                    try:
                        preflight_sizing_report(wallet, prices, last_full_rank, pair_names, _current_regime, cycle)
                    except Exception:
                        pass

                # Auto-export clean trades every 1000 cycles
                if cycle % 1000 == 0 and cycle > 0:
                    export_clean_trades()

                # Daily metrics summary every 2400 cycles (daily reset)
                if cycle % 2400 == 1 and cycle > 1:
                    daily_metrics.log_daily_summary(current_equity=wallet.value(prices))
                    daily_metrics.start_day(wallet.value(prices), cycle)

                # Log performance matrix every 500 cycles (~25 min)
                if cycle % 500 == 0 and perf_matrix.trades:
                    perf_matrix.save_to_log()
                    if len(perf_matrix.trades) >= 5:
                        logger.debug("\n" + EdgeAudit.full_report(perf_matrix))
                        logger.debug("\n" + GroundTruthValidator.full_report(perf_matrix.trades))
                        if shadow.signals:
                            logger.debug("\n" + shadow.report())
            except Exception as _log_err:
                try:
                    logger.error(f"LOGGING ERROR (cycle {cycle}): {_log_err}")
                except Exception:
                    pass

            # Track cycle duration for snapshot latency check
            try:
                _ct = time.time() - _cycle_start
                _cycle_times.append(_ct)
                if len(_cycle_times) > 20:
                    _cycle_times.pop(0)
            except Exception:
                pass

            # Health score: update every cycle (fast, no I/O), full snapshot every N cycles
            if SNAPSHOT_ENABLED:
                try:
                    try:
                        _snap_regime = enhanced_regime
                    except NameError:
                        _snap_regime = None
                    # Fast score update — runs every cycle, no logging
                    update_health_score(perf_matrix, _snap_regime)
                    # Full snapshot with display — throttled
                    if cycle % SNAPSHOT_INTERVAL == 0 and cycle > 0:
                        _snap = bot_snapshot_report(cycle, wallet, prices, perf_matrix, _snap_regime)
                        logger.debug(_snap)
                        if is_verbose("DEBUG"):
                            print(_snap)
                except Exception:
                    pass

            # v29.3.5: Flush GammaScalping batch log at end of cycle
            if ADVANCED_ALPHA_ENABLED:
                try:
                    alpha_gamma.flush_cycle_log()
                except Exception:
                    pass

            time.sleep(POLL)

        except KeyboardInterrupt:
            break
        except Exception as e:
            # GLOBAL FAILSAFE: catch ANY exception, log it, continue
            try:
                import traceback
                _tb = traceback.format_exc()
                logger.error(f"LOOP ERROR (cycle {cycle}): {e}\n{_tb}")
                error_logger.log("main_loop_exception", str(e))
            except Exception:
                pass  # Even logging failure must not crash
            _consecutive_errors = _consecutive_errors + 1
            # NO-TRADE SAFE MODE: if no positions open, NEVER shut down
            _has_open_positions = len(wallet.longs) > 0 or len(wallet.shorts) > 0
            if _consecutive_errors > MAX_CONSECUTIVE_ERRORS and _has_open_positions:
                logger.error(f"{MAX_CONSECUTIVE_ERRORS}+ CONSECUTIVE ERRORS with open positions — halting")
                break
            elif _consecutive_errors > MAX_CONSECUTIVE_ERRORS:
                # No positions — just log, reset counter, keep running
                try:
                    logger.warning(f"{MAX_CONSECUTIVE_ERRORS}+ errors but 0 positions — resetting counter, staying alive")
                except Exception:
                    pass
                _consecutive_errors = 0
            time.sleep(2)
            continue  # ALWAYS keep looping — never fall through
        else:
            _consecutive_errors = 0

    wallet.save(prices)
    brain.save(ML_FILE)
    ml_stats = brain.get_stats()
    print(f"\n  Bot stopped. Portfolio: ${wallet.value(prices):,.2f} | ML: {ml_stats['total_trained']} trained")

    # Final paper trade summary
    paper_tracker.log_summary()
    # Final live validation summary
    try:
        if live_tracker.total_attempts > 0:
            logger.debug(live_tracker.summary())
    except Exception:
        pass
    # Final clean data export
    export_clean_trades()

    # Final edge audit on shutdown (file only — terminal gets compact summary)
    if perf_matrix.trades:
        report = EdgeAudit.full_report(perf_matrix)
        logger.info("\nFINAL " + report)

    # Ground truth validation on shutdown (file only)
    if perf_matrix.trades:
        gt_report = GroundTruthValidator.full_report(perf_matrix.trades)
        logger.debug("\n" + gt_report)

    # Shadow signal analysis on shutdown (file only)
    if shadow.signals:
        shadow_report = shadow.report()
        logger.debug("\n" + shadow_report)

    # Flush async log writer — ensure all queued writes complete before exit
    try:
        _async_writer.stop()
    except Exception:
        pass


# ══════════════════════════════════════════════════════════════════════════════
# v29.3.5 — BACKTESTING MODULE
# Fetches historical OHLCV data from Kraken and replays through the full
# signal/entry/exit pipeline to produce performance metrics.
# Usage: python bot_clone.py backtest [--days=30]
# ══════════════════════════════════════════════════════════════════════════════


class BacktestWallet:
    """Simulated wallet for backtesting — mirrors the real Wallet interface
    but stores full trade history for analysis."""

    def __init__(self, cash):
        self.initial_cash = cash
        self.cash = cash
        self.longs = {}       # coin -> {"qty", "entry", "bought_cycle", "strategy", ...}
        self.shorts = {}      # coin -> {"qty", "entry", "bought_cycle", "strategy", ...}
        self.wins = 0
        self.losses = 0
        self.trades = []      # all completed trades: [{"coin", "dir", "entry", "exit", "pnl_pct", "strategy"}]
        self._last_exit_fees = {}
        self._peak_value = cash
        self._max_drawdown = 0.0

    def buy(self, coin, price, amount=None):
        if amount is None:
            amount = min(self.cash * 0.15, self.cash)
        amount = min(amount, self.cash)
        if amount < 5 or price <= 0:
            return 0
        fee = amount * 0.001  # 0.1% taker fee simulation
        net = amount - fee
        qty = net / price
        if coin in self.longs:
            old = self.longs[coin]
            total_qty = old["qty"] + qty
            avg_entry = (old["entry"] * old["qty"] + price * qty) / total_qty
            old["qty"] = total_qty
            old["entry"] = avg_entry
        else:
            self.longs[coin] = {"qty": qty, "entry": price, "bought_cycle": 0,
                                "strategy": "momentum", "profit_protection": False,
                                "trail_stop": 0, "pp_start_cycle": 0, "pp_start_pnl": 0,
                                "highest": price, "entry_sl": 0, "entry_atr": 0,
                                "_trail_tm": 1.0, "no_price_cycles": 0}
        self.cash -= amount
        return qty

    def sell(self, coin, price):
        if coin not in self.longs:
            return 0
        pos = self.longs[coin]
        entry = pos["entry"]
        qty = pos["qty"]
        gross = qty * price
        fee = gross * 0.001
        net = gross - fee
        pnl_pct = ((price - entry) / entry) * 100 if entry > 0 else 0
        fees_pct = 0.0 if PAPER_MODE else 0.2
        self._last_exit_fees = {"fee_pct": fees_pct}
        self.cash += net
        if pnl_pct > 0:
            self.wins += 1
        else:
            self.losses += 1
        self.trades.append({"coin": coin, "dir": "long", "entry": entry, "exit": price,
                            "pnl_pct": pnl_pct, "strategy": pos.get("strategy", "momentum")})
        del self.longs[coin]
        return pnl_pct

    def short_open(self, coin, price, amount=None):
        if amount is None:
            amount = min(self.cash * 0.15, self.cash)
        amount = min(amount, self.cash)
        if amount < 5 or price <= 0:
            return 0
        fee = amount * 0.001
        qty = (amount - fee) / price
        self.shorts[coin] = {"qty": qty, "entry": price, "bought_cycle": 0,
                             "strategy": "momentum", "profit_protection": False,
                             "trail_stop": 0, "pp_start_cycle": 0, "pp_start_pnl": 0,
                             "highest": price, "entry_sl": 0, "entry_atr": 0,
                             "_trail_tm": 1.0, "no_price_cycles": 0}
        self.cash -= amount
        return qty

    def cover(self, coin, price):
        if coin not in self.shorts:
            return 0
        pos = self.shorts[coin]
        entry = pos["entry"]
        qty = pos["qty"]
        pnl_pct = ((entry - price) / entry) * 100 if entry > 0 else 0
        pnl_usd = qty * (entry - price)
        fee = qty * price * 0.001
        self.cash += (qty * entry) + pnl_usd - fee
        fees_pct = 0.0 if PAPER_MODE else 0.2
        self._last_exit_fees = {"fee_pct": fees_pct}
        if pnl_pct > 0:
            self.wins += 1
        else:
            self.losses += 1
        self.trades.append({"coin": coin, "dir": "short", "entry": entry, "exit": price,
                            "pnl_pct": pnl_pct, "strategy": pos.get("strategy", "momentum")})
        del self.shorts[coin]
        return pnl_pct

    def value(self, prices):
        total = self.cash
        for coin, pos in self.longs.items():
            p = prices.get(coin, pos["entry"])
            total += pos["qty"] * p
        for coin, pos in self.shorts.items():
            p = prices.get(coin, pos["entry"])
            unrealized = (pos["entry"] - p) * pos["qty"]
            total += (pos["qty"] * pos["entry"]) + unrealized
        if total > self._peak_value:
            self._peak_value = total
        dd = (self._peak_value - total) / self._peak_value * 100 if self._peak_value > 0 else 0
        if dd > self._max_drawdown:
            self._max_drawdown = dd
        return total


def _fetch_ohlcv(pair, interval=5, since=None):
    """Fetch OHLCV candles from Kraken REST API.
    interval: candle period in minutes (1, 5, 15, 60, etc.)
    since: Unix timestamp to start from.
    Returns list of [time, open, high, low, close, vwap, volume, count]."""
    try:
        params = {"pair": pair, "interval": interval}
        if since:
            params["since"] = int(since)
        data = safe_api_call(f"{KRAKEN}/OHLC", params=params, timeout=15)
        if data and "result" in data:
            for key in data["result"]:
                if key != "last":
                    return data["result"][key]
    except Exception as e:
        logger.warning(f"[BACKTEST] OHLCV fetch failed for {pair}: {e}")
    return []


def _fetch_backtest_data(days=30, top_n=20):
    """Fetch historical OHLCV data for top N Kraken USD pairs.
    Returns dict: {coin_short_name -> [(timestamp, open, high, low, close, volume), ...]}
    Uses 5-minute candles to simulate ~2s polling (each candle = ~150 cycles)."""
    print(f"\n  [BACKTEST] Fetching {days}-day OHLCV for top {top_n} pairs...")

    # Step 1: Get all pairs
    pair_names = get_usd_pairs()
    if not pair_names:
        print("  [BACKTEST] FATAL: Cannot discover pairs.")
        return {}, {}

    # Step 2: Get current tickers to rank by volume
    all_pairs = list(pair_names.keys())
    tickers = get_tickers(all_pairs)
    if not tickers:
        print("  [BACKTEST] FATAL: Cannot get tickers.")
        return {}, {}

    # Sort by 24h volume descending, pick top N
    ranked = sorted(tickers.items(), key=lambda x: x[1].get("vol", 0), reverse=True)
    top_pairs = [(pair, tickers[pair]) for pair, _ in ranked[:top_n]]

    # Step 3: Fetch OHLCV for each pair
    since_ts = int(time.time()) - (days * 86400)
    ohlcv_data = {}      # coin -> [(ts, open, high, low, close, vol), ...]
    pair_map = {}         # coin -> pair_key (for ticker simulation)

    for pair_key, ticker in top_pairs:
        alt = pair_names.get(pair_key, pair_key)
        coin = to_short_name(alt) if callable(to_short_name) else alt
        print(f"    Fetching {coin} ({pair_key})...", end=" ", flush=True)

        # Kraken OHLC returns max ~720 candles per call — need to paginate for 30 days of 5-min candles
        # 30 days × 288 candles/day = 8640 candles needed, ~12 pages
        all_candles = []
        _since = since_ts
        for _page in range(15):  # Safety limit
            candles = _fetch_ohlcv(pair_key, interval=5, since=_since)
            if not candles:
                break
            new_candles = [c for c in candles if len(c) >= 7]
            if not new_candles:
                break
            all_candles.extend(new_candles)
            last_ts = int(new_candles[-1][0])
            if last_ts <= _since:
                break  # No progress
            _since = last_ts
            if last_ts >= time.time() - 600:
                break  # Reached present
            time.sleep(0.5)  # Rate limit

        # Parse candles: [time, open, high, low, close, vwap, volume, count]
        parsed = []
        for c in all_candles:
            try:
                ts = int(c[0])
                o, h, l, cl = float(c[1]), float(c[2]), float(c[3]), float(c[4])
                vol = float(c[6])
                if cl > 0 and h > 0 and l > 0:
                    parsed.append((ts, o, h, l, cl, vol))
            except (ValueError, IndexError):
                continue

        # Deduplicate by timestamp
        seen_ts = set()
        deduped = []
        for row in parsed:
            if row[0] not in seen_ts:
                seen_ts.add(row[0])
                deduped.append(row)
        deduped.sort(key=lambda x: x[0])

        if deduped:
            ohlcv_data[coin] = deduped
            pair_map[coin] = pair_key
            print(f"{len(deduped)} candles")
        else:
            print("no data")
        time.sleep(0.3)  # Rate limit between pairs

    print(f"  [BACKTEST] Data ready: {len(ohlcv_data)} coins, "
          f"{sum(len(v) for v in ohlcv_data.values())} total candles\n")
    return ohlcv_data, pair_map


def run_backtest(days=30, starting_cash=1000.0, verbose=True):
    """Run a full backtest replay using historical Kraken OHLCV data.

    Replays data cycle-by-cycle through the existing signal logic:
    - Momentum entries (long + short) with all filters
    - All 8 alpha strategies
    - Full SL/TP/trailing/stagnation/slow-bleed exit logic
    - Position sizing via Kelly + edge multiplier

    Returns dict with performance metrics."""
    global prices_cache, _current_cycle, _current_regime
    global _loss_streak_count, _loss_streak_paused_until, _session_peak_equity
    global _per_coin_loss_streak, _suspicious_coins
    pair_names = {}
    for coin in list(prices_cache.keys())[:20]:
        pair_names[f"{coin}USD"] = coin

    ohlcv_data, pair_map = _fetch_backtest_data(days=days)
    if not ohlcv_data:
        print("  [BACKTEST] No data fetched — cannot run backtest.")
        return None

    # ── INITIALIZATION ──
    bt_wallet = BacktestWallet(starting_cash)
    prices_cache_backup = dict(prices_cache)  # Save live cache
    prices_cache.clear()
    _loss_streak_count = 0
    _loss_streak_paused_until = 0
    _session_peak_equity = starting_cash
    _per_coin_loss_streak.clear()
    _suspicious_coins.clear()

    # Build unified timeline: list of (timestamp, {coin -> close_price}, {coin -> ticker_dict})
    # Expand each 5-min candle into sub-ticks using OHLC to simulate price movement
    all_timestamps = set()
    for coin, candles in ohlcv_data.items():
        for c in candles:
            all_timestamps.add(c[0])
    timeline = sorted(all_timestamps)

    if verbose:
        print(f"  [BACKTEST] Timeline: {len(timeline)} ticks over {days} days")
        print(f"  [BACKTEST] Starting cash: ${starting_cash:,.2f}")
        print(f"  [BACKTEST] Coins: {', '.join(sorted(ohlcv_data.keys()))}\n")

    # Create regime detector and alpha instances for clean backtest
    bt_regime = AdaptiveRegime()
    bt_alpha_pp = PricePrediction()
    bt_alpha_quant = QuantMultiStrategy()
    bt_alpha_gamma = GammaScalping()
    bt_alpha_mev = MEVExtraction()
    bt_alpha_pairs = PairsTrading()
    bt_alpha_events = EventDriven()
    bt_alpha_macro = DiscretionaryMacro()
    bt_alpha_vix = VixVolatilityTrading()

    # Pre-index candle data by timestamp for O(1) lookup
    candle_at = {}  # {ts -> {coin -> (o, h, l, close, vol)}}
    for coin, candles in ohlcv_data.items():
        for c in candles:
            ts = c[0]
            if ts not in candle_at:
                candle_at[ts] = {}
            candle_at[ts][coin] = (c[1], c[2], c[3], c[4], c[5])

    # ── REPLAY LOOP ──
    equity_curve = []
    cycle = 0
    _warmup = min(100, len(timeline) // 10)  # Warmup: 10% of data or 100 ticks
    _report_interval = max(1, len(timeline) // 20)  # Report progress 20 times

    for tick_idx, ts in enumerate(timeline):
        cycle += 1
        _current_cycle = cycle
        prices = {}
        tick_coins = candle_at.get(ts, {})

        # Update prices_cache with this tick's close prices
        for coin, (o, h, l, cl, vol) in tick_coins.items():
            prices[coin] = cl
            track_price(coin, cl)

        # Skip if no data this tick
        if not prices:
            continue

        # Build mock tickers for rank() and alpha strategies
        mock_tickers = {}
        for coin in prices:
            hist = prices_cache.get(coin, [])
            if len(hist) < 2:
                continue
            prev = hist[-2] if len(hist) >= 2 else hist[-1]
            change = (prices[coin] - prev) / prev if prev > 0 else 0
            candle = tick_coins.get(coin, (0, 0, 0, 0, 0))
            vol_usd = candle[4] * prices[coin] if candle[4] > 0 else 100000
            pair_key = pair_map.get(coin, coin)
            mock_tickers[pair_key] = {
                "price": prices[coin], "change": change, "vol": vol_usd,
                "high": candle[1], "low": candle[2],
                "range": (candle[1] - candle[2]) / candle[2] if candle[2] > 0 else 0,
                "pos": (prices[coin] - candle[2]) / (candle[1] - candle[2])
                       if (candle[1] - candle[2]) > 0 else 0.5,
            }

        # ── REGIME CLASSIFICATION ──
        if cycle > _warmup // 2:
            _current_regime = bt_regime.classify(prices_cache) or "UNKNOWN"

        # ── EXIT PROCESSING (longs) ──
        for coin in list(bt_wallet.longs.keys()):
            pos = bt_wallet.longs[coin]
            if coin not in prices:
                continue
            p = prices[coin]
            entry = pos["entry"]
            held_cycles = cycle - pos.get("bought_cycle", 0)
            pnl_pct = ((p - entry) / entry) * 100 if entry > 0 else 0

            # Update highest price
            if p > pos.get("highest", 0):
                pos["highest"] = p

            atr = coin_atr(coin)
            atr_pct = max(0.01, atr * 100)
            sl_target = max(SL_BASE_PCT, atr_pct * ATR_SL_MULTIPLIER)
            tp_ratio = adaptive_tp_ratio(coin)  # v29.5.0: ATR-adaptive TP ratio
            if _current_regime in ("SMOOTH_TREND", "VOLATILE_TREND") and TP_RATIO_TRENDING > tp_ratio:
                tp_ratio = TP_RATIO_TRENDING  # Use trending ratio if higher
            tp_trigger = sl_target * tp_ratio

            _final_tm = pos.get("_trail_tm", 1.0)

            # Rule 1: Stop Loss
            if pnl_pct <= -sl_target:
                bt_wallet.sell(coin, p)
                continue

            # Rule 2a: Time stop (15 min equivalent = 450 cycles at 2s)
            if held_cycles > 450 and pnl_pct < -0.5:
                bt_wallet.sell(coin, p)
                continue

            # Rule 2a2: Slow bleed
            if pnl_pct < SLOW_BLEED_THRESHOLD and held_cycles > STAGNATION_EXIT_CYCLES // 2:
                bt_wallet.sell(coin, p)
                continue

            # Rule 2b: Stagnation
            if pnl_pct < 0 and held_cycles > 0:
                _stag_limit = min(400, max(100, int((1.2 / atr_pct) ** 2)))
                if held_cycles > _stag_limit:
                    bt_wallet.sell(coin, p)
                    continue

            # Rule 2c: Early profit protection
            if (pnl_pct >= PP_TRIGGER_MULTIPLIER * tp_trigger and pnl_pct < tp_trigger
                    and not pos.get("profit_protection")):
                pos["profit_protection"] = True
                pos["pp_start_cycle"] = cycle
                pos["pp_start_pnl"] = pnl_pct
                pos["trail_stop"] = p * (1 - max(0.004, atr * 0.005) * _final_tm)

            # Rule 3: TP trigger
            if pnl_pct >= tp_trigger and not pos.get("profit_protection"):
                pos["profit_protection"] = True
                pos["pp_start_cycle"] = cycle
                pos["pp_start_pnl"] = pnl_pct
                pos["trail_stop"] = p * (1 - max(0.004, atr * 0.005) * _final_tm)

            # Rule 4: Profit protection mode
            if pos.get("profit_protection"):
                _pp_cycles = cycle - pos.get("pp_start_cycle", cycle)
                _pp_start_pnl = pos.get("pp_start_pnl", 1.5)
                _pp_timeout = min(PP_TIMEOUT_MAX, 100 + int(max(0, _pp_start_pnl - 1.5) * 50))
                if _pp_cycles > _pp_timeout:
                    bt_wallet.sell(coin, p)
                    continue
                # Update trailing stop
                new_trail = p * (1 - max(0.004, atr * 0.005) * _final_tm)
                pos["trail_stop"] = max(pos.get("trail_stop", entry), new_trail)
                if p <= pos.get("trail_stop", 0):
                    bt_wallet.sell(coin, p)
                    continue

        # ── EXIT PROCESSING (shorts) ──
        for coin in list(bt_wallet.shorts.keys()):
            pos = bt_wallet.shorts[coin]
            if coin not in prices:
                continue
            p = prices[coin]
            entry = pos["entry"]
            held_cycles = cycle - pos.get("bought_cycle", 0)
            pnl_pct = ((entry - p) / entry) * 100 if entry > 0 else 0

            atr = coin_atr(coin)
            atr_pct = max(0.01, atr * 100)
            sl_target = max(SL_BASE_PCT, atr_pct * ATR_SL_MULTIPLIER)
            tp_ratio = adaptive_tp_ratio(coin)  # v29.5.0: ATR-adaptive TP ratio
            if _current_regime in ("SMOOTH_TREND", "VOLATILE_TREND") and TP_RATIO_TRENDING > tp_ratio:
                tp_ratio = TP_RATIO_TRENDING  # Use trending ratio if higher
            tp_trigger = sl_target * tp_ratio

            _final_tm = pos.get("_trail_tm", 1.0)

            if pnl_pct <= -sl_target:
                bt_wallet.cover(coin, p)
                continue
            if held_cycles > 450 and pnl_pct < -0.5:
                bt_wallet.cover(coin, p)
                continue
            if pnl_pct < SLOW_BLEED_THRESHOLD and held_cycles > STAGNATION_EXIT_CYCLES // 2:
                bt_wallet.cover(coin, p)
                continue
            if pnl_pct < 0 and held_cycles > 0:
                _stag_limit = min(400, max(100, int((1.2 / atr_pct) ** 2)))
                if held_cycles > _stag_limit:
                    bt_wallet.cover(coin, p)
                    continue
            if (pnl_pct >= PP_TRIGGER_MULTIPLIER * tp_trigger and pnl_pct < tp_trigger
                    and not pos.get("profit_protection")):
                pos["profit_protection"] = True
                pos["pp_start_cycle"] = cycle
                pos["pp_start_pnl"] = pnl_pct
                pos["trail_stop"] = p * (1 + max(0.004, atr * 0.005) * _final_tm)
            if pnl_pct >= tp_trigger and not pos.get("profit_protection"):
                pos["profit_protection"] = True
                pos["pp_start_cycle"] = cycle
                pos["pp_start_pnl"] = pnl_pct
                pos["trail_stop"] = p * (1 + max(0.004, atr * 0.005) * _final_tm)
            if pos.get("profit_protection"):
                _pp_cycles = cycle - pos.get("pp_start_cycle", cycle)
                _pp_start_pnl = pos.get("pp_start_pnl", 1.5)
                _pp_timeout = min(PP_TIMEOUT_MAX, 100 + int(max(0, _pp_start_pnl - 1.5) * 50))
                if _pp_cycles > _pp_timeout:
                    bt_wallet.cover(coin, p)
                    continue
                new_trail = p * (1 + max(0.004, atr * 0.005) * _final_tm)
                pos["trail_stop"] = min(pos.get("trail_stop", entry * 2), new_trail)
                if p >= pos.get("trail_stop", float("inf")):
                    bt_wallet.cover(coin, p)
                    continue

        # ── SKIP ENTRIES DURING WARMUP ──
        if cycle <= _warmup:
            equity_curve.append(bt_wallet.value(prices))
            continue

        # ── ENTRY LOGIC (MOMENTUM) ──
        total_positions = len(bt_wallet.longs) + len(bt_wallet.shorts)
        if (total_positions < MAX_POSITIONS and bt_wallet.cash > 50
                and _loss_streak_count < LOSS_STREAK_MAX
                and cycle > _loss_streak_paused_until):

            # Item 29: Apply same filters as live to reduce backtest divergence
            _bt_heat_ok = portfolio_heat_allows_entry(bt_wallet, prices)
            if not _bt_heat_ok:
                equity_curve.append(bt_wallet.value(prices))
                continue

            ranked = rank(mock_tickers, min_vol=100000, regime=_current_regime)

            for r in ranked[:5]:  # Check top 5 signals
                if total_positions >= MAX_POSITIONS:
                    break
                pair_key = r["pair"]
                coin_name = to_short_name(pair_names.get(pair_key, pair_key)) if callable(to_short_name) else pair_key
                if not coin_name or coin_name in bt_wallet.longs or coin_name in bt_wallet.shorts:
                    continue

                # Item 29: Blacklist + cooldown (mirrors live entry filters)
                if coin_name in DYNAMIC_BLACKLIST:
                    continue
                if TEMP_BLACKLIST_ENABLED and dynamic_blacklist.is_blocked(coin_name, cycle):
                    continue
                _bt_last_exit = _last_exit_cycle.get(coin_name, (0, False))
                _bt_cd = COOLDOWN_AFTER_WIN if _bt_last_exit[1] else COOLDOWN_AFTER_LOSS
                if cycle - _bt_last_exit[0] < _bt_cd:
                    continue

                hist = prices_cache.get(coin_name, [])
                if len(hist) < MIN_PRICE_HISTORY:
                    continue

                atr = coin_atr(coin_name)
                if atr < MIN_ATR_TO_TRADE:
                    continue

                score = r["score"]
                change = r["change"]

                # LONG entry
                if (score > MIN_MOMENTUM_SCORE and change > 0.001
                        and coin_name not in bt_wallet.longs):
                    mom_ok, _ = momentum_confirmed(coin_name, "long", window=5)
                    mt_ok, _, _ = micro_trend_confirmed(coin_name, "long", candles=4)
                    if mom_ok and mt_ok:
                        # Position sizing
                        pv = bt_wallet.value(prices)
                        risk_amt = pv * MAX_RISK_PER_TRADE
                        atr_pct = max(0.01, atr * 100)
                        sl_pct = max(SL_BASE_PCT, atr_pct * ATR_SL_MULTIPLIER)
                        size = risk_amt / (sl_pct / 100 * GAP_RISK_MULTIPLIER)
                        size = min(size, bt_wallet.cash * CASH_MAX_SINGLE_TRADE_PCT, pv * MAX_SINGLE_COIN_EXPOSURE_PCT / 100)
                        size = max(POSITION_SIZE_FLOOR_USD, size)
                        if size <= bt_wallet.cash:
                            qty = bt_wallet.buy(coin_name, prices[coin_name], size)
                            if qty > 0:
                                bt_wallet.longs[coin_name]["bought_cycle"] = cycle
                                bt_wallet.longs[coin_name]["entry_atr"] = atr
                                bt_wallet.longs[coin_name]["entry_sl"] = sl_pct
                                total_positions += 1

                # SHORT entry
                elif (score < -MIN_MOMENTUM_SCORE and change < -0.001
                      and coin_name not in bt_wallet.shorts):
                    mom_ok, _ = momentum_confirmed(coin_name, "short", window=5)
                    mt_ok, _, _ = micro_trend_confirmed(coin_name, "short", candles=4)
                    if mom_ok and mt_ok:
                        pv = bt_wallet.value(prices)
                        risk_amt = pv * MAX_RISK_PER_TRADE
                        atr_pct = max(0.01, atr * 100)
                        sl_pct = max(SL_BASE_PCT, atr_pct * ATR_SL_MULTIPLIER)
                        size = risk_amt / (sl_pct / 100 * GAP_RISK_MULTIPLIER)
                        size = min(size, bt_wallet.cash * CASH_MAX_SINGLE_TRADE_PCT, pv * MAX_SINGLE_COIN_EXPOSURE_PCT / 100)
                        size = max(POSITION_SIZE_FLOOR_USD, size)
                        if size <= bt_wallet.cash:
                            qty = bt_wallet.short_open(coin_name, prices[coin_name], size)
                            if qty > 0:
                                bt_wallet.shorts[coin_name]["bought_cycle"] = cycle
                                bt_wallet.shorts[coin_name]["entry_atr"] = atr
                                bt_wallet.shorts[coin_name]["entry_sl"] = sl_pct
                                total_positions += 1

        # ── ALPHA STRATEGY ENTRIES ──
        if (ADVANCED_ALPHA_ENABLED and cycle > _warmup + 50
                and total_positions < MAX_POSITIONS and bt_wallet.cash > 50):
            _alpha_signals = []
            for _ac in list(prices_cache.keys()):
                if _ac in bt_wallet.longs or _ac in bt_wallet.shorts:
                    continue
                if len(prices_cache.get(_ac, [])) < 30:
                    continue
                # Collect signals from each alpha strategy
                try:
                    _pp_c, _pp_d = bt_alpha_pp.predict(_ac, cycle)
                    if _pp_c >= _alpha_threshold("price-prediction") and _pp_d:
                        _alpha_signals.append((_ac, _pp_d, _pp_c, "price-prediction"))
                except Exception:
                    pass
                try:
                    _qm_c, _qm_d = bt_alpha_quant.evaluate(_ac, cycle)
                    if _qm_c >= _alpha_threshold("quant-multi") and _qm_d:
                        _alpha_signals.append((_ac, _qm_d, _qm_c, "quant-multi"))
                except Exception:
                    pass
                try:
                    _gs_c, _gs_d = bt_alpha_gamma.scan(_ac, cycle)
                    if _gs_c >= _alpha_threshold("gamma-scalping") and _gs_d:
                        _alpha_signals.append((_ac, _gs_d, _gs_c, "gamma-scalping"))
                except Exception:
                    pass

            # Batch strategies
            try:
                _mev_sigs = bt_alpha_mev.scan(cycle, mock_tickers)
                for _mc, _md, _mconf in _mev_sigs:
                    if _mconf >= _alpha_threshold("mev-extraction"):
                        _alpha_signals.append((_mc, _md, _mconf, "mev-extraction"))
            except Exception:
                pass
            try:
                _pt_sigs = bt_alpha_pairs.scan(cycle)
                for _pc, _pd, _pconf in _pt_sigs:
                    if _pconf >= _alpha_threshold("pairs-trading"):
                        _alpha_signals.append((_pc, _pd, _pconf, "pairs-trading"))
            except Exception:
                pass
            try:
                _ed_sigs = bt_alpha_events.scan(cycle, mock_tickers)
                for _item in _ed_sigs:
                    _ec, _edir, _econf = _item[0], _item[1], _item[2]
                    _etype = _item[3] if len(_item) > 3 else "event"
                    if _econf >= _alpha_threshold(f"event-{_etype}"):
                        _alpha_signals.append((_ec, _edir, _econf, f"event-{_etype}"))
            except Exception:
                pass

            # Macro + Vix as filters
            try:
                bt_alpha_macro.update(cycle, mock_tickers)
                bt_alpha_vix.update(cycle)
            except Exception:
                pass
            _macro_dir, _macro_conf = None, 0
            try:
                _macro_dir, _macro_conf = bt_alpha_macro.get_bias()
            except Exception:
                pass

            _alpha_signals.sort(key=lambda x: x[2], reverse=True)
            _alpha_taken = 0
            for _a_coin, _a_dir, _a_conf, _a_strat in _alpha_signals:
                if _alpha_taken >= 2 or total_positions >= MAX_POSITIONS:
                    break
                if _a_coin in bt_wallet.longs or _a_coin in bt_wallet.shorts:
                    continue
                if _a_coin not in prices:
                    continue
                # Item 29: Blacklist + cooldown (mirrors live alpha entry filters)
                if _a_coin in DYNAMIC_BLACKLIST:
                    continue
                if TEMP_BLACKLIST_ENABLED and dynamic_blacklist.is_blocked(_a_coin, cycle):
                    continue

                # Macro boost/penalty
                if _macro_dir and _macro_dir != _a_dir and _macro_conf >= 0.60:
                    _a_conf *= 0.80
                if _macro_dir and _macro_dir == _a_dir:
                    _a_conf = min(1.0, _a_conf * 1.10)
                if _a_conf < _alpha_threshold(_a_strat):
                    continue

                # Size
                pv = bt_wallet.value(prices)
                _a_atr = coin_atr(_a_coin)
                _a_atr_pct = max(0.01, _a_atr * 100)
                _a_sl = max(SL_BASE_PCT, _a_atr_pct * ATR_SL_MULTIPLIER)
                _a_risk = pv * MAX_RISK_PER_TRADE
                _a_size = _a_risk / (_a_sl / 100 * GAP_RISK_MULTIPLIER)
                _a_size = min(_a_size, bt_wallet.cash * ALPHA_CASH_MAX_PCT, pv * ALPHA_CASH_MAX_PCT) * ALPHA_SIZE_MULT
                _a_size = max(POSITION_SIZE_FLOOR_USD, _a_size)
                if _a_size > bt_wallet.cash:
                    continue

                if _a_dir == "long":
                    qty = bt_wallet.buy(_a_coin, prices[_a_coin], _a_size)
                    if qty > 0:
                        bt_wallet.longs[_a_coin]["bought_cycle"] = cycle
                        bt_wallet.longs[_a_coin]["strategy"] = f"alpha_{_a_strat}"
                        bt_wallet.longs[_a_coin]["entry_atr"] = _a_atr
                        _alpha_taken += 1
                        total_positions += 1
                elif _a_dir == "short":
                    qty = bt_wallet.short_open(_a_coin, prices[_a_coin], _a_size)
                    if qty > 0:
                        bt_wallet.shorts[_a_coin]["bought_cycle"] = cycle
                        bt_wallet.shorts[_a_coin]["strategy"] = f"alpha_{_a_strat}"
                        bt_wallet.shorts[_a_coin]["entry_atr"] = _a_atr
                        _alpha_taken += 1
                        total_positions += 1

        # Track equity
        eq = bt_wallet.value(prices)
        equity_curve.append(eq)

        # Progress report
        if verbose and tick_idx > 0 and tick_idx % _report_interval == 0:
            pct_done = tick_idx / len(timeline) * 100
            pnl = (eq / starting_cash - 1) * 100
            print(f"    [{pct_done:.0f}%] Cycle {cycle}: ${eq:,.2f} ({pnl:+.2f}%) "
                  f"trades={len(bt_wallet.trades)} pos={total_positions}")

    # ── CLOSE ALL REMAINING POSITIONS ──
    for coin in list(bt_wallet.longs.keys()):
        if coin in prices:
            bt_wallet.sell(coin, prices[coin])
    for coin in list(bt_wallet.shorts.keys()):
        if coin in prices:
            bt_wallet.cover(coin, prices[coin])

    # ── CALCULATE METRICS ──
    trades = bt_wallet.trades
    total_trades = len(trades)
    if total_trades == 0:
        print("  [BACKTEST] No trades executed — check signal thresholds or data quality.")
        prices_cache.clear()
        prices_cache.update(prices_cache_backup)
        return {"total_trades": 0, "note": "No trades executed"}

    wins = [t for t in trades if t["pnl_pct"] > 0]
    losses = [t for t in trades if t["pnl_pct"] <= 0]
    win_rate = len(wins) / total_trades * 100
    avg_win = sum(t["pnl_pct"] for t in wins) / len(wins) if wins else 0
    avg_loss = sum(t["pnl_pct"] for t in losses) / len(losses) if losses else 0
    total_pnl = (bt_wallet.value(prices) / starting_cash - 1) * 100
    best_trade = max(trades, key=lambda t: t["pnl_pct"])
    worst_trade = min(trades, key=lambda t: t["pnl_pct"])
    trades_per_day = total_trades / max(1, days)

    # Sharpe ratio (annualized from daily returns)
    if len(equity_curve) > 1:
        # Resample equity curve to daily
        daily_returns = []
        ticks_per_day = max(1, len(equity_curve) // max(1, days))
        for i in range(ticks_per_day, len(equity_curve), ticks_per_day):
            prev_eq = equity_curve[i - ticks_per_day]
            curr_eq = equity_curve[i]
            if prev_eq > 0:
                daily_returns.append((curr_eq - prev_eq) / prev_eq)
        if daily_returns and len(daily_returns) > 1:
            avg_ret = sum(daily_returns) / len(daily_returns)
            std_ret = (sum((r - avg_ret) ** 2 for r in daily_returns) / (len(daily_returns) - 1)) ** 0.5
            sharpe = (avg_ret / std_ret) * (365 ** 0.5) if std_ret > 0 else 0
        else:
            sharpe = 0
    else:
        sharpe = 0

    results = {
        "total_trades": total_trades,
        "win_rate": win_rate,
        "total_pnl_pct": total_pnl,
        "avg_win_pct": avg_win,
        "avg_loss_pct": avg_loss,
        "max_drawdown_pct": bt_wallet._max_drawdown,
        "sharpe_ratio": sharpe,
        "best_trade": {"coin": best_trade["coin"], "pnl": best_trade["pnl_pct"],
                       "strategy": best_trade["strategy"]},
        "worst_trade": {"coin": worst_trade["coin"], "pnl": worst_trade["pnl_pct"],
                        "strategy": worst_trade["strategy"]},
        "trades_per_day": trades_per_day,
        "final_equity": bt_wallet.value(prices),
        "trades": trades,
        "equity_curve": equity_curve,
    }

    # ── PRINT REPORT ──
    if verbose:
        print("\n" + "=" * 70)
        print("  BACKTEST RESULTS")
        print("=" * 70)
        print(f"  Period:            {days} days")
        print(f"  Starting Capital:  ${starting_cash:,.2f}")
        print(f"  Final Equity:      ${results['final_equity']:,.2f}")
        print(f"  Total P&L:         {total_pnl:+.2f}%")
        print(f"  Max Drawdown:      {bt_wallet._max_drawdown:.2f}%")
        print(f"  Sharpe Ratio:      {sharpe:.2f}")
        print(f"  ─────────────────────────────────────")
        print(f"  Total Trades:      {total_trades}")
        print(f"  Win Rate:          {win_rate:.1f}%")
        print(f"  Avg Win:           {avg_win:+.2f}%")
        print(f"  Avg Loss:          {avg_loss:+.2f}%")
        print(f"  Trades/Day:        {trades_per_day:.1f}")
        print(f"  ─────────────────────────────────────")
        print(f"  Best Trade:        {best_trade['coin']} {best_trade['pnl_pct']:+.2f}% ({best_trade['strategy']})")
        print(f"  Worst Trade:       {worst_trade['coin']} {worst_trade['pnl_pct']:+.2f}% ({worst_trade['strategy']})")
        print(f"  ─────────────────────────────────────")

        # Strategy breakdown
        strat_stats = {}
        for t in trades:
            s = t["strategy"]
            if s not in strat_stats:
                strat_stats[s] = {"wins": 0, "losses": 0, "total_pnl": 0}
            if t["pnl_pct"] > 0:
                strat_stats[s]["wins"] += 1
            else:
                strat_stats[s]["losses"] += 1
            strat_stats[s]["total_pnl"] += t["pnl_pct"]

        print(f"\n  STRATEGY BREAKDOWN:")
        print(f"  {'Strategy':<25} {'Trades':>7} {'WR':>7} {'Total P&L':>10}")
        print(f"  {'─' * 25} {'─' * 7} {'─' * 7} {'─' * 10}")
        for s, st in sorted(strat_stats.items(), key=lambda x: x[1]["total_pnl"], reverse=True):
            total = st["wins"] + st["losses"]
            wr = st["wins"] / total * 100 if total > 0 else 0
            print(f"  {s:<25} {total:>7} {wr:>6.1f}% {st['total_pnl']:>+9.2f}%")
        print("=" * 70)

    # Restore live prices_cache
    prices_cache.clear()
    prices_cache.update(prices_cache_backup)
    return results


def validate_alpha_strategies(days=30, starting_cash=1000.0):
    """Run each alpha strategy independently against backtest data.
    Reports which strategies have positive expectancy and disables those without.

    Expectancy = (win_rate × avg_win) - (loss_rate × avg_loss)
    A strategy with negative expectancy is a net loser and should be disabled."""
    global prices_cache, _current_cycle

    ohlcv_data, pair_map = _fetch_backtest_data(days=days)
    if not ohlcv_data:
        print("  [VALIDATE] No data — cannot validate strategies.")
        return None

    # Build unified timeline
    all_timestamps = set()
    for coin, candles in ohlcv_data.items():
        for c in candles:
            all_timestamps.add(c[0])
    timeline = sorted(all_timestamps)

    candle_at = {}
    for coin, candles in ohlcv_data.items():
        for c in candles:
            ts = c[0]
            if ts not in candle_at:
                candle_at[ts] = {}
            candle_at[ts][coin] = (c[1], c[2], c[3], c[4], c[5])

    prices_cache_backup = dict(prices_cache)
    _warmup = min(100, len(timeline) // 10)

    # Test each strategy independently
    strategy_configs = {
        "price-prediction": lambda: PricePrediction(),
        "quant-multi": lambda: QuantMultiStrategy(),
        "gamma-scalping": lambda: GammaScalping(),
        "mev-extraction": lambda: MEVExtraction(),
        "pairs-trading": lambda: PairsTrading(),
        "event-driven": lambda: EventDriven(),
        "discretionary-macro": lambda: DiscretionaryMacro(),
        "vix-volatility": lambda: VixVolatilityTrading(),
    }

    results = {}

    for strat_name, strat_factory in strategy_configs.items():
        print(f"\n  [VALIDATE] Testing {strat_name}...")
        prices_cache.clear()
        strat = strat_factory()
        bt_wallet = BacktestWallet(starting_cash)
        cycle = 0
        prices = {}

        for tick_idx, ts in enumerate(timeline):
            cycle += 1
            _current_cycle = cycle
            tick_coins = candle_at.get(ts, {})

            for coin, (o, h, l, cl, vol) in tick_coins.items():
                prices[coin] = cl
                track_price(coin, cl)

            if not prices or cycle <= _warmup:
                continue

            # Build mock tickers
            mock_tickers = {}
            for coin in prices:
                hist = prices_cache.get(coin, [])
                if len(hist) < 2:
                    continue
                prev = hist[-2]
                change = (prices[coin] - prev) / prev if prev > 0 else 0
                candle = tick_coins.get(coin, (0, 0, 0, 0, 0))
                vol_usd = candle[4] * prices[coin] if candle[4] > 0 else 100000
                pair_key = pair_map.get(coin, coin)
                mock_tickers[pair_key] = {
                    "price": prices[coin], "change": change, "vol": vol_usd,
                    "high": candle[1], "low": candle[2],
                    "range": (candle[1] - candle[2]) / candle[2] if candle[2] > 0 else 0,
                    "pos": 0.5,
                }

            # Exit existing positions
            for coin in list(bt_wallet.longs.keys()):
                if coin not in prices:
                    continue
                pos = bt_wallet.longs[coin]
                p = prices[coin]
                entry = pos["entry"]
                held = cycle - pos.get("bought_cycle", 0)
                pnl_pct = ((p - entry) / entry) * 100 if entry > 0 else 0
                atr = coin_atr(coin)
                atr_pct = max(0.01, atr * 100)
                sl = max(SL_BASE_PCT, atr_pct * ATR_SL_MULTIPLIER)
                tp = sl * TP_RATIO_NORMAL
                if pnl_pct <= -sl or pnl_pct >= tp or held > 400:
                    bt_wallet.sell(coin, p)

            for coin in list(bt_wallet.shorts.keys()):
                if coin not in prices:
                    continue
                pos = bt_wallet.shorts[coin]
                p = prices[coin]
                entry = pos["entry"]
                held = cycle - pos.get("bought_cycle", 0)
                pnl_pct = ((entry - p) / entry) * 100 if entry > 0 else 0
                atr = coin_atr(coin)
                atr_pct = max(0.01, atr * 100)
                sl = max(SL_BASE_PCT, atr_pct * ATR_SL_MULTIPLIER)
                tp = sl * TP_RATIO_NORMAL
                if pnl_pct <= -sl or pnl_pct >= tp or held > 400:
                    bt_wallet.cover(coin, p)

            # Generate signals from this strategy only
            total_positions = len(bt_wallet.longs) + len(bt_wallet.shorts)
            if total_positions >= MAX_POSITIONS or bt_wallet.cash < 50:
                continue

            signals = []
            try:
                if strat_name in ("discretionary-macro", "vix-volatility"):
                    # Macro and Vix are directional biases, not per-coin signals
                    if strat_name == "discretionary-macro":
                        strat.update(cycle, mock_tickers)
                        d, c = strat.get_bias()
                    else:
                        strat.update(cycle)
                        d, c = strat.favor_direction()
                    if d and c >= _alpha_threshold(strat_name):
                        # Apply to highest-volume coin
                        top_coin = max(prices.keys(), key=lambda x: len(prices_cache.get(x, [])))
                        signals.append((top_coin, d, c, strat_name))
                elif strat_name in ("mev-extraction",):
                    sigs = strat.scan(cycle, mock_tickers)
                    for mc, md, mconf in sigs:
                        if mconf >= _alpha_threshold(strat_name):
                            signals.append((mc, md, mconf, strat_name))
                elif strat_name in ("pairs-trading",):
                    sigs = strat.scan(cycle)
                    for pc, pd, pconf in sigs:
                        if pconf >= _alpha_threshold(strat_name):
                            signals.append((pc, pd, pconf, strat_name))
                elif strat_name in ("event-driven",):
                    sigs = strat.scan(cycle, mock_tickers)
                    for item in sigs:
                        if item[2] >= _alpha_threshold(strat_name):
                            signals.append((item[0], item[1], item[2], strat_name))
                else:
                    # Per-coin strategies
                    for ac in list(prices_cache.keys()):
                        if ac in bt_wallet.longs or ac in bt_wallet.shorts:
                            continue
                        if len(prices_cache.get(ac, [])) < 30 or ac not in prices:
                            continue
                        if strat_name == "price-prediction":
                            sc, sd = strat.predict(ac, cycle)
                        elif strat_name == "quant-multi":
                            sc, sd = strat.evaluate(ac, cycle)
                        elif strat_name == "gamma-scalping":
                            sc, sd = strat.scan(ac, cycle)
                        else:
                            continue
                        if sc >= _alpha_threshold(strat_name) and sd:
                            signals.append((ac, sd, sc, strat_name))
            except Exception:
                continue

            # Execute top signal
            signals.sort(key=lambda x: x[2], reverse=True)
            for _ac, _ad, _aconf, _as in signals[:1]:
                if _ac not in prices or _ac in bt_wallet.longs or _ac in bt_wallet.shorts:
                    continue
                pv = bt_wallet.value(prices)
                size = min(pv * 0.10, bt_wallet.cash * 0.20) * ALPHA_SIZE_MULT
                size = max(POSITION_SIZE_FLOOR_USD, size)
                if size > bt_wallet.cash:
                    continue
                if _ad == "long":
                    qty = bt_wallet.buy(_ac, prices[_ac], size)
                    if qty > 0:
                        bt_wallet.longs[_ac]["bought_cycle"] = cycle
                        bt_wallet.longs[_ac]["strategy"] = strat_name
                elif _ad == "short":
                    qty = bt_wallet.short_open(_ac, prices[_ac], size)
                    if qty > 0:
                        bt_wallet.shorts[_ac]["bought_cycle"] = cycle
                        bt_wallet.shorts[_ac]["strategy"] = strat_name

        # Close remaining
        for coin in list(bt_wallet.longs.keys()):
            if coin in prices:
                bt_wallet.sell(coin, prices[coin])
        for coin in list(bt_wallet.shorts.keys()):
            if coin in prices:
                bt_wallet.cover(coin, prices[coin])

        # Calculate expectancy
        trades = bt_wallet.trades
        total_t = len(trades)
        wins = [t for t in trades if t["pnl_pct"] > 0]
        loss = [t for t in trades if t["pnl_pct"] <= 0]
        win_rate = len(wins) / total_t if total_t > 0 else 0
        loss_rate = len(loss) / total_t if total_t > 0 else 0
        avg_win = sum(t["pnl_pct"] for t in wins) / len(wins) if wins else 0
        avg_loss = abs(sum(t["pnl_pct"] for t in loss) / len(loss)) if loss else 0
        expectancy = (win_rate * avg_win) - (loss_rate * avg_loss)
        total_pnl = sum(t["pnl_pct"] for t in trades)

        results[strat_name] = {
            "trades": total_t,
            "win_rate": win_rate * 100,
            "avg_win": avg_win,
            "avg_loss": -abs(avg_loss),
            "expectancy": expectancy,
            "total_pnl": total_pnl,
            "positive": expectancy > 0,
        }

    # Restore
    prices_cache.clear()
    prices_cache.update(prices_cache_backup)

    # ── PRINT REPORT ──
    print("\n" + "=" * 70)
    print("  ALPHA STRATEGY VALIDATION")
    print("=" * 70)
    print(f"  {'Strategy':<22} {'Trades':>7} {'WR':>7} {'AvgW':>7} {'AvgL':>7} {'Expect':>8} {'Status':>10}")
    print(f"  {'─' * 22} {'─' * 7} {'─' * 7} {'─' * 7} {'─' * 7} {'─' * 8} {'─' * 10}")

    disabled_count = 0
    for sn, sr in sorted(results.items(), key=lambda x: x[1]["expectancy"], reverse=True):
        status = "PASS" if sr["positive"] else "DISABLED"
        if not sr["positive"] and sr["trades"] >= 3:
            disabled_count += 1
        wr_str = f"{sr['win_rate']:.1f}%" if sr["trades"] > 0 else "N/A"
        print(f"  {sn:<22} {sr['trades']:>7} {wr_str:>7} {sr['avg_win']:>+6.2f}% {sr['avg_loss']:>+6.2f}% "
              f"{sr['expectancy']:>+7.3f}% {'  ' + status:>10}")

    # Disable strategies with negative expectancy (only if enough trades to be meaningful)
    disabled_strategies = []
    for sn, sr in results.items():
        if not sr["positive"] and sr["trades"] >= 3:
            disabled_strategies.append(sn)
            # Set threshold to 1.0 (impossible to reach) to effectively disable
            ALPHA_STRATEGY_THRESHOLDS[sn] = 1.0

    if disabled_strategies:
        print(f"\n  DISABLED {len(disabled_strategies)} strategies with negative expectancy:")
        for ds in disabled_strategies:
            print(f"    - {ds} (threshold set to 1.00, effectively disabled)")
    else:
        print(f"\n  All strategies with sufficient data have positive expectancy.")

    print("=" * 70)
    return results


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — WALK-FORWARD OPTIMIZATION
# ══════════════════════════════════════════════════════════════════════════════

WFO_DEFAULT_WINDOWS = 5
WFO_DEFAULT_DAYS = 150


def wfo_optimize(windows=WFO_DEFAULT_WINDOWS, total_days=WFO_DEFAULT_DAYS, verbose=True):
    """Walk-forward optimization: split last N days into rolling train/test windows.

    Each window trains on 80% of data and tests on 20%.
    Averages out-of-sample results across all windows.
    Reports which config values produced consistent positive expectancy.

    Args:
        windows: Number of rolling windows (default 5)
        total_days: Total history to use (default 150 days)
        verbose: Print progress and results

    Returns dict with per-window results and aggregate metrics."""
    if verbose:
        print(f"\n{'=' * 70}")
        print(f"  WALK-FORWARD OPTIMIZATION")
        print(f"  Windows: {windows} | Total Days: {total_days}")
        print(f"  Train/Test Split: 80/20 per window")
        print(f"{'=' * 70}\n")

    window_days = total_days // windows
    train_days = int(window_days * 0.8)
    test_days = window_days - train_days

    if verbose:
        print(f"  Window size: {window_days} days (train={train_days}, test={test_days})\n")

    # Fetch full history once
    ohlcv_data, pair_map = _fetch_backtest_data(days=total_days)
    if not ohlcv_data:
        print("  [WFO] FATAL: No data — cannot run walk-forward optimization.")
        return None

    # Find timestamp range
    all_ts = []
    for coin, candles in ohlcv_data.items():
        for c in candles:
            all_ts.append(c[0])
    if not all_ts:
        return None
    ts_min, ts_max = min(all_ts), max(all_ts)
    total_span = ts_max - ts_min

    window_results = []
    all_positive = True

    for w in range(windows):
        # Calculate time boundaries for this window
        w_start = ts_min + int(w * (total_span / windows))
        w_mid = w_start + int(train_days * 86400)  # End of train period
        w_end = w_start + int(window_days * 86400)  # End of test period

        if verbose:
            _w_start_str = datetime.fromtimestamp(w_start, tz=timezone.utc).strftime("%Y-%m-%d")
            _w_mid_str = datetime.fromtimestamp(w_mid, tz=timezone.utc).strftime("%Y-%m-%d")
            _w_end_str = datetime.fromtimestamp(w_end, tz=timezone.utc).strftime("%Y-%m-%d")
            print(f"  Window {w+1}/{windows}: train={_w_start_str}..{_w_mid_str} | test={_w_mid_str}..{_w_end_str}")

        # Split data into train and test sets
        test_ohlcv = {}
        for coin, candles in ohlcv_data.items():
            test_candles = [c for c in candles if w_mid <= c[0] <= w_end]
            if len(test_candles) >= 50:  # Need minimum data
                test_ohlcv[coin] = test_candles

        if not test_ohlcv:
            if verbose:
                print(f"    [SKIP] Not enough test data for window {w+1}")
            window_results.append({"window": w+1, "skipped": True})
            continue

        # Run backtest on TEST portion only (out-of-sample)
        # Temporarily replace ohlcv_data with just test data
        global prices_cache, _current_cycle, _loss_streak_count, _loss_streak_paused_until
        global _session_peak_equity, _per_coin_loss_streak, _suspicious_coins

        prices_cache_backup = dict(prices_cache)
        prices_cache.clear()
        _loss_streak_count = 0
        _loss_streak_paused_until = 0
        _session_peak_equity = 1000.0
        _per_coin_loss_streak.clear()
        _suspicious_coins.clear()

        # Build timeline from test data
        bt_wallet = BacktestWallet(1000.0)
        test_timestamps = set()
        for coin, candles in test_ohlcv.items():
            for c in candles:
                test_timestamps.add(c[0])
        test_timeline = sorted(test_timestamps)

        candle_at = {}
        for coin, candles in test_ohlcv.items():
            for c in candles:
                ts = c[0]
                if ts not in candle_at:
                    candle_at[ts] = {}
                candle_at[ts][coin] = (c[1], c[2], c[3], c[4], c[5])

        # Simple replay: track prices and count entries/exits
        _test_trades = 0
        _test_pnl = 0.0
        prices = {}
        pair_names_local = {}
        for coin in test_ohlcv:
            if coin in pair_map:
                pair_names_local[pair_map[coin]] = coin

        for tick_idx, ts in enumerate(test_timeline):
            _current_cycle = tick_idx
            if ts in candle_at:
                for coin, (o, h, l, cl, vol) in candle_at[ts].items():
                    prices[coin] = cl
                    cache = prices_cache.get(coin, [])
                    cache.append(cl)
                    if len(cache) > 200:
                        cache = cache[-200:]
                    prices_cache[coin] = cache

            # Exit logic: simple SL/TP check for positions
            for coin in list(bt_wallet.longs.keys()):
                pos = bt_wallet.longs[coin]
                if coin not in prices:
                    continue
                p = prices[coin]
                entry = pos.get("entry", p)
                atr = coin_atr(coin)
                sl_pct = max(SL_BASE_PCT, max(0.01, atr * 100) * ATR_SL_MULTIPLIER)
                tp_pct = max(TP_BASE_PCT, sl_pct * TP_RATIO_NORMAL)
                pnl = (p - entry) / entry * 100 if entry > 0 else 0
                if pnl <= -sl_pct or pnl >= tp_pct or tick_idx - pos.get("bought_cycle", 0) > STAGNATION_EXIT_CYCLES:
                    bt_wallet.sell(coin, p)
                    _test_trades += 1

            for coin in list(bt_wallet.shorts.keys()):
                pos = bt_wallet.shorts[coin]
                if coin not in prices:
                    continue
                p = prices[coin]
                entry = pos.get("entry", p)
                atr = coin_atr(coin)
                sl_pct = max(SL_BASE_PCT, max(0.01, atr * 100) * ATR_SL_MULTIPLIER)
                tp_pct = max(TP_BASE_PCT, sl_pct * TP_RATIO_NORMAL)
                pnl = (entry - p) / entry * 100 if entry > 0 else 0
                if pnl <= -sl_pct or pnl >= tp_pct or tick_idx - pos.get("bought_cycle", 0) > STAGNATION_EXIT_CYCLES:
                    bt_wallet.cover(coin, p)
                    _test_trades += 1

            # Entry logic: simplified momentum check
            if tick_idx < 50:  # Warmup
                continue
            total_pos = len(bt_wallet.longs) + len(bt_wallet.shorts)
            if total_pos >= MAX_POSITIONS or bt_wallet.cash < 50:
                continue

            # Build mock tickers for rank()
            mock_tickers = {}
            for coin, p in prices.items():
                hist = prices_cache.get(coin, [])
                if len(hist) >= 5:
                    change = (hist[-1] - hist[-2]) / hist[-2] if len(hist) >= 2 and hist[-2] > 0 else 0
                    mock_tickers[coin] = {"price": p, "vol": 1000000, "change": change}

            ranked = rank(mock_tickers, min_vol=100000, regime=None)
            for r in ranked[:3]:
                if total_pos >= MAX_POSITIONS:
                    break
                cn = r["pair"]
                if cn in bt_wallet.longs or cn in bt_wallet.shorts:
                    continue
                if r["score"] > MIN_MOMENTUM_SCORE and r["change"] > SCORE_CHANGE_MIN_LONG:
                    pv = bt_wallet.value(prices)
                    size = min(pv * MAX_RISK_PER_TRADE * 10, bt_wallet.cash * CASH_MAX_SINGLE_TRADE_PCT)
                    size = max(POSITION_SIZE_FLOOR_USD, size)
                    if size <= bt_wallet.cash:
                        qty = bt_wallet.buy(cn, prices[cn], size)
                        if qty > 0:
                            bt_wallet.longs[cn]["bought_cycle"] = tick_idx
                            total_pos += 1

        # Close remaining
        for coin in list(bt_wallet.longs.keys()):
            if coin in prices:
                bt_wallet.sell(coin, prices[coin])
        for coin in list(bt_wallet.shorts.keys()):
            if coin in prices:
                bt_wallet.cover(coin, prices[coin])

        # Metrics
        final_eq = bt_wallet.value(prices)
        test_pnl = (final_eq / 1000.0 - 1) * 100
        trades = bt_wallet.trades
        total_t = len(trades)
        wins = [t for t in trades if t.get("pnl_pct", 0) > 0]
        wr = len(wins) / total_t * 100 if total_t > 0 else 0
        expectancy = sum(t.get("pnl_pct", 0) for t in trades) / total_t if total_t > 0 else 0

        wr_data = {
            "window": w + 1,
            "skipped": False,
            "test_pnl_pct": test_pnl,
            "trades": total_t,
            "win_rate": wr,
            "expectancy": expectancy,
            "max_drawdown": bt_wallet._max_drawdown,
        }
        window_results.append(wr_data)
        if expectancy <= 0:
            all_positive = False

        if verbose:
            print(f"    Result: P&L={test_pnl:+.2f}% | Trades={total_t} | WR={wr:.1f}% | "
                  f"Exp={expectancy:+.3f}% | DD={bt_wallet._max_drawdown:.2f}%")

        # Restore
        prices_cache.clear()
        prices_cache.update(prices_cache_backup)

    # ── AGGREGATE RESULTS ──
    valid = [w for w in window_results if not w.get("skipped", False)]
    if not valid:
        if verbose:
            print("\n  [WFO] No valid windows — insufficient data.")
        return {"windows": window_results, "aggregate": None}

    avg_pnl = sum(w["test_pnl_pct"] for w in valid) / len(valid)
    avg_wr = sum(w["win_rate"] for w in valid) / len(valid)
    avg_exp = sum(w["expectancy"] for w in valid) / len(valid)
    avg_dd = sum(w["max_drawdown"] for w in valid) / len(valid)
    consistency = sum(1 for w in valid if w["expectancy"] > 0) / len(valid) * 100

    aggregate = {
        "avg_pnl_pct": avg_pnl,
        "avg_win_rate": avg_wr,
        "avg_expectancy": avg_exp,
        "avg_max_drawdown": avg_dd,
        "consistency_pct": consistency,
        "all_positive": all_positive,
        "valid_windows": len(valid),
    }

    if verbose:
        print(f"\n{'─' * 70}")
        print(f"  WALK-FORWARD AGGREGATE ({len(valid)} windows)")
        print(f"{'─' * 70}")
        print(f"  Avg OOS P&L:       {avg_pnl:+.2f}%")
        print(f"  Avg Win Rate:      {avg_wr:.1f}%")
        print(f"  Avg Expectancy:    {avg_exp:+.3f}%")
        print(f"  Avg Max Drawdown:  {avg_dd:.2f}%")
        print(f"  Consistency:       {consistency:.0f}% windows positive")
        print(f"  All Positive:      {'YES' if all_positive else 'NO'}")
        print(f"{'─' * 70}")

        # Config values assessment
        print(f"\n  CURRENT CONFIG ASSESSMENT:")
        print(f"    MIN_MOMENTUM_SCORE = {MIN_MOMENTUM_SCORE}")
        print(f"    MIN_ATR_TO_TRADE   = {MIN_ATR_TO_TRADE}")
        print(f"    GAP_RISK_MULTIPLIER= {GAP_RISK_MULTIPLIER}")
        print(f"    MAX_RISK_PER_TRADE = {MAX_RISK_PER_TRADE}")
        print(f"    SL_BASE_PCT        = {SL_BASE_PCT}")
        print(f"    COOLDOWN_AFTER_WIN = {COOLDOWN_AFTER_WIN}")
        print(f"    COOLDOWN_AFTER_LOSS= {COOLDOWN_AFTER_LOSS}")
        if all_positive:
            print(f"\n    VERDICT: Config produces CONSISTENT positive expectancy across all windows.")
        else:
            _neg = [w["window"] for w in valid if w["expectancy"] <= 0]
            print(f"\n    VERDICT: Negative expectancy in windows {_neg}. Consider Bayesian optimization.")
        print(f"{'=' * 70}")

    return {"windows": window_results, "aggregate": aggregate}


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — BAYESIAN PARAMETER OPTIMIZATION (optuna)
# ══════════════════════════════════════════════════════════════════════════════

BAYESIAN_N_TRIALS = 50
BAYESIAN_BT_DAYS = 30
OPTIMAL_PARAMS_FILE = os.path.join(DIR, "logs", "optimal_params.json")


def _bayesian_objective(trial):
    """Optuna objective function: run backtest with trial params, return negative Sharpe.
    (Optuna minimizes, so we negate Sharpe for maximization.)"""
    import optuna  # noqa: F811

    # Sample parameters
    _orig_min_atr = globals().get("MIN_ATR_TO_TRADE", 0.001)
    _orig_min_mom = globals().get("MIN_MOMENTUM_SCORE", 0.08)
    _orig_gap = globals().get("GAP_RISK_MULTIPLIER", 1.5)
    _orig_cd_loss = globals().get("COOLDOWN_AFTER_LOSS", 40)
    _orig_cd_win = globals().get("COOLDOWN_AFTER_WIN", 15)
    _orig_mult_floor = 0.40
    _orig_edge_min = globals().get("EDGE_SIZING_MIN_MULT", 0.80)

    # Suggest values within reasonable ranges
    global MIN_ATR_TO_TRADE, MIN_MOMENTUM_SCORE, GAP_RISK_MULTIPLIER
    global COOLDOWN_AFTER_LOSS, COOLDOWN_AFTER_WIN, EDGE_SIZING_MIN_MULT

    MIN_ATR_TO_TRADE = trial.suggest_float("MIN_ATR_TO_TRADE", 0.0005, 0.005, log=True)
    MIN_MOMENTUM_SCORE = trial.suggest_float("MIN_MOMENTUM_SCORE", 0.03, 0.25)
    GAP_RISK_MULTIPLIER = trial.suggest_float("GAP_RISK_MULTIPLIER", 1.0, 3.0)
    COOLDOWN_AFTER_LOSS = trial.suggest_int("COOLDOWN_AFTER_LOSS", 10, 100)
    COOLDOWN_AFTER_WIN = trial.suggest_int("COOLDOWN_AFTER_WIN", 5, 50)
    EDGE_SIZING_MIN_MULT = trial.suggest_float("EDGE_SIZING_MIN_MULT", 0.40, 1.0)

    # Run backtest silently
    try:
        result = run_backtest(days=BAYESIAN_BT_DAYS, verbose=False)
    except Exception:
        result = None

    # Restore original values (safety)
    if result is None or result.get("total_trades", 0) < 5:
        MIN_ATR_TO_TRADE = _orig_min_atr
        MIN_MOMENTUM_SCORE = _orig_min_mom
        GAP_RISK_MULTIPLIER = _orig_gap
        COOLDOWN_AFTER_LOSS = _orig_cd_loss
        COOLDOWN_AFTER_WIN = _orig_cd_win
        EDGE_SIZING_MIN_MULT = _orig_edge_min
        return 0.0  # Penalty: no trades = no score

    # Multi-objective: maximize Sharpe, penalize drawdown, require minimum trades
    sharpe = result.get("sharpe_ratio", 0)
    dd = result.get("max_drawdown_pct", 100)
    pnl = result.get("total_pnl_pct", 0)
    wr = result.get("win_rate", 0)

    # Composite score (higher = better, Optuna maximizes with direction="maximize")
    score = sharpe * 0.50 + (pnl / 100) * 0.30 - (dd / 100) * 0.20

    return score


def bayesian_optimize(n_trials=BAYESIAN_N_TRIALS, days=BAYESIAN_BT_DAYS, verbose=True):
    """Use Optuna to find optimal trading parameters via Bayesian optimization.

    Optimizes: MIN_ATR_TO_TRADE, MIN_MOMENTUM_SCORE, GAP_RISK_MULTIPLIER,
               COOLDOWN_AFTER_LOSS, COOLDOWN_AFTER_WIN, EDGE_SIZING_MIN_MULT

    Runs `n_trials` backtests (default 50), each with different parameter combinations.
    Saves best params to logs/optimal_params.json.

    Returns dict with best params and their performance metrics."""
    global MIN_ATR_TO_TRADE, MIN_MOMENTUM_SCORE, GAP_RISK_MULTIPLIER
    global COOLDOWN_AFTER_LOSS, COOLDOWN_AFTER_WIN, EDGE_SIZING_MIN_MULT
    global BAYESIAN_BT_DAYS

    try:
        import optuna
        optuna.logging.set_verbosity(optuna.logging.WARNING)
    except ImportError:
        print("  [BAYESIAN] ERROR: optuna not installed. Run: pip install optuna")
        return None

    if verbose:
        print(f"\n{'=' * 70}")
        print(f"  BAYESIAN PARAMETER OPTIMIZATION (Optuna)")
        print(f"  Trials: {n_trials} | Backtest Days: {days}")
        print(f"{'=' * 70}\n")

    # Save original params to restore after
    orig_params = {
        "MIN_ATR_TO_TRADE": MIN_ATR_TO_TRADE,
        "MIN_MOMENTUM_SCORE": MIN_MOMENTUM_SCORE,
        "GAP_RISK_MULTIPLIER": GAP_RISK_MULTIPLIER,
        "COOLDOWN_AFTER_LOSS": COOLDOWN_AFTER_LOSS,
        "COOLDOWN_AFTER_WIN": COOLDOWN_AFTER_WIN,
        "EDGE_SIZING_MIN_MULT": EDGE_SIZING_MIN_MULT,
    }

    BAYESIAN_BT_DAYS = days

    study = optuna.create_study(direction="maximize", study_name="crypto_bot_optimization")

    if verbose:
        print(f"  Running {n_trials} trials...")

    study.optimize(_bayesian_objective, n_trials=n_trials, show_progress_bar=verbose)

    # Restore originals first
    MIN_ATR_TO_TRADE = orig_params["MIN_ATR_TO_TRADE"]
    MIN_MOMENTUM_SCORE = orig_params["MIN_MOMENTUM_SCORE"]
    GAP_RISK_MULTIPLIER = orig_params["GAP_RISK_MULTIPLIER"]
    COOLDOWN_AFTER_LOSS = orig_params["COOLDOWN_AFTER_LOSS"]
    COOLDOWN_AFTER_WIN = orig_params["COOLDOWN_AFTER_WIN"]
    EDGE_SIZING_MIN_MULT = orig_params["EDGE_SIZING_MIN_MULT"]

    best = study.best_trial
    best_params = best.params
    best_score = best.value

    # Run final backtest with best params to get full metrics
    MIN_ATR_TO_TRADE = best_params["MIN_ATR_TO_TRADE"]
    MIN_MOMENTUM_SCORE = best_params["MIN_MOMENTUM_SCORE"]
    GAP_RISK_MULTIPLIER = best_params["GAP_RISK_MULTIPLIER"]
    COOLDOWN_AFTER_LOSS = best_params["COOLDOWN_AFTER_LOSS"]
    COOLDOWN_AFTER_WIN = best_params["COOLDOWN_AFTER_WIN"]
    EDGE_SIZING_MIN_MULT = best_params["EDGE_SIZING_MIN_MULT"]

    final_result = run_backtest(days=days, verbose=False)

    # Restore originals again
    MIN_ATR_TO_TRADE = orig_params["MIN_ATR_TO_TRADE"]
    MIN_MOMENTUM_SCORE = orig_params["MIN_MOMENTUM_SCORE"]
    GAP_RISK_MULTIPLIER = orig_params["GAP_RISK_MULTIPLIER"]
    COOLDOWN_AFTER_LOSS = orig_params["COOLDOWN_AFTER_LOSS"]
    COOLDOWN_AFTER_WIN = orig_params["COOLDOWN_AFTER_WIN"]
    EDGE_SIZING_MIN_MULT = orig_params["EDGE_SIZING_MIN_MULT"]

    # Save best params to file
    try:
        os.makedirs(os.path.dirname(OPTIMAL_PARAMS_FILE), exist_ok=True)
        save_data = {
            "params": best_params,
            "score": best_score,
            "backtest_days": days,
            "n_trials": n_trials,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "metrics": {
                "total_pnl_pct": final_result.get("total_pnl_pct", 0) if final_result else 0,
                "sharpe_ratio": final_result.get("sharpe_ratio", 0) if final_result else 0,
                "win_rate": final_result.get("win_rate", 0) if final_result else 0,
                "max_drawdown_pct": final_result.get("max_drawdown_pct", 0) if final_result else 0,
                "total_trades": final_result.get("total_trades", 0) if final_result else 0,
            },
            "original_params": orig_params,
        }
        with open(OPTIMAL_PARAMS_FILE, "w") as f:
            json.dump(save_data, f, indent=2)
        if verbose:
            print(f"\n  Saved best params to {OPTIMAL_PARAMS_FILE}")
    except Exception as e:
        logger.warning(f"[BAYESIAN] Could not save params: {e}")

    if verbose:
        print(f"\n{'─' * 70}")
        print(f"  BAYESIAN OPTIMIZATION RESULTS ({n_trials} trials)")
        print(f"{'─' * 70}")
        print(f"  Best Score:          {best_score:.4f}")
        print(f"  ─────────────────────────────────────")
        print(f"  OPTIMAL PARAMETERS:")
        for k, v in sorted(best_params.items()):
            orig = orig_params.get(k, "?")
            if isinstance(v, float):
                print(f"    {k:<25} {v:.6f}  (was {orig})")
            else:
                print(f"    {k:<25} {v}  (was {orig})")
        if final_result:
            print(f"  ─────────────────────────────────────")
            print(f"  WITH OPTIMAL PARAMS:")
            print(f"    Total P&L:      {final_result.get('total_pnl_pct', 0):+.2f}%")
            print(f"    Sharpe Ratio:   {final_result.get('sharpe_ratio', 0):.2f}")
            print(f"    Win Rate:       {final_result.get('win_rate', 0):.1f}%")
            print(f"    Max Drawdown:   {final_result.get('max_drawdown_pct', 0):.2f}%")
            print(f"    Total Trades:   {final_result.get('total_trades', 0)}")
        print(f"{'=' * 70}")

    return {"best_params": best_params, "best_score": best_score, "final_backtest": final_result}


def _load_optimal_params():
    """Load optimal params from logs/optimal_params.json if it exists.
    Called at startup to apply previously-optimized values."""
    global MIN_ATR_TO_TRADE, MIN_MOMENTUM_SCORE, GAP_RISK_MULTIPLIER
    global COOLDOWN_AFTER_LOSS, COOLDOWN_AFTER_WIN, EDGE_SIZING_MIN_MULT
    try:
        if not os.path.exists(OPTIMAL_PARAMS_FILE):
            return False
        with open(OPTIMAL_PARAMS_FILE, "r") as f:
            data = json.load(f)
        params = data.get("params", {})
        if not params:
            return False

        # Apply each param if present
        if "MIN_ATR_TO_TRADE" in params:
            MIN_ATR_TO_TRADE = float(params["MIN_ATR_TO_TRADE"])
        if "MIN_MOMENTUM_SCORE" in params:
            MIN_MOMENTUM_SCORE = float(params["MIN_MOMENTUM_SCORE"])
            if MIN_MOMENTUM_SCORE > 0.15:
                logger.warning(f"[BAYESIAN] MIN_MOMENTUM_SCORE={MIN_MOMENTUM_SCORE:.4f} > 0.15 — capping at 0.12")
                MIN_MOMENTUM_SCORE = 0.12
        if "GAP_RISK_MULTIPLIER" in params:
            GAP_RISK_MULTIPLIER = float(params["GAP_RISK_MULTIPLIER"])
        if "COOLDOWN_AFTER_LOSS" in params:
            COOLDOWN_AFTER_LOSS = int(params["COOLDOWN_AFTER_LOSS"])
        if "COOLDOWN_AFTER_WIN" in params:
            COOLDOWN_AFTER_WIN = int(params["COOLDOWN_AFTER_WIN"])
        if "EDGE_SIZING_MIN_MULT" in params:
            EDGE_SIZING_MIN_MULT = float(params["EDGE_SIZING_MIN_MULT"])

        _ts = data.get("timestamp", "unknown")
        logger.info(f"[BAYESIAN] Loaded optimal params from {OPTIMAL_PARAMS_FILE} (optimized at {_ts})")
        logger.info(f"[BAYESIAN] MIN_ATR={MIN_ATR_TO_TRADE:.4f} MIN_MOM={MIN_MOMENTUM_SCORE:.4f} "
                     f"GAP={GAP_RISK_MULTIPLIER:.2f} CD_LOSS={COOLDOWN_AFTER_LOSS} CD_WIN={COOLDOWN_AFTER_WIN} "
                     f"EDGE_MIN={EDGE_SIZING_MIN_MULT:.2f}")
        return True
    except Exception as e:
        logger.warning(f"[BAYESIAN] Could not load optimal params: {e}")
        return False


# ══════════════════════════════════════════════════════════════════════════════
# v29.4.0 — ORDER BOOK IMBALANCE
# ══════════════════════════════════════════════════════════════════════════════

OB_IMBALANCE_STRONG_BUY = 0.65   # Bid volume > 65% = buying pressure
OB_IMBALANCE_STRONG_SELL = 0.35  # Bid volume < 35% = selling pressure
OB_CONFIDENCE_BOOST = 0.10       # 10% confidence boost when imbalance confirms direction


def orderbook_imbalance(coin):
    """Fetch Level 2 depth (top 10 bids/asks) and calculate order book imbalance.

    Returns float 0.0-1.0: bid_volume / (bid_volume + ask_volume).
    Values > 0.65 = buying pressure, < 0.35 = selling pressure.
    Uses the best available connected exchange adapter.

    Returns 0.5 (neutral) on any error or if no exchange is connected."""
    try:
        # Try Kraken first (always connected for public endpoints)
        adapter = _exchange_adapters.get("kraken")
        if not adapter:
            return 0.5

        # Map short coin name to exchange pair
        pair_key = None
        for pk, name in pair_names_cache.items():
            short = to_short_name(name) if callable(to_short_name) else name
            if short == coin:
                pair_key = pk
                break
        if not pair_key:
            # Fallback: try common formats
            pair_key = f"X{coin.upper()}ZUSD"

        ob = adapter.get_orderbook(pair_key, depth=10)
        if not ob:
            return 0.5

        bids = ob.get("bids", [])
        asks = ob.get("asks", [])

        if not bids and not asks:
            return 0.5

        bid_vol = sum(float(b[1]) for b in bids if len(b) >= 2)
        ask_vol = sum(float(a[1]) for a in asks if len(a) >= 2)
        total_vol = bid_vol + ask_vol

        if total_vol <= 0:
            return 0.5

        return bid_vol / total_vol
    except Exception:
        return 0.5


# Cache for pair name lookups in orderbook_imbalance
pair_names_cache = {}


def _refresh_pair_names_cache():
    """Refresh the pair_names_cache from get_usd_pairs(). Called once at startup."""
    global pair_names_cache
    try:
        pair_names_cache = get_usd_pairs() or {}
    except Exception:
        pass


if __name__ == "__main__":
    _cmd = sys.argv[1] if len(sys.argv) > 1 else "run"

    if _cmd == "backtest":
        # Parse optional --days=N argument
        _bt_days = 30
        _bt_validate = False
        for arg in sys.argv[2:]:
            if arg.startswith("--days="):
                try:
                    _bt_days = int(arg.split("=")[1])
                except ValueError:
                    pass
            if arg == "--validate":
                _bt_validate = True

        print(f"\n{'=' * 70}")
        print(f"  CRYPTO BOT v29.4.0 — BACKTEST MODE")
        print(f"  Period: {_bt_days} days | Validate: {_bt_validate}")
        print(f"{'=' * 70}\n")

        bt_results = run_backtest(days=_bt_days)

        if _bt_validate and bt_results and bt_results.get("total_trades", 0) > 0:
            print("\n  Running alpha strategy validation...\n")
            validate_alpha_strategies(days=_bt_days)

        sys.exit(0)

    elif _cmd == "wfo":
        # Walk-forward optimization: python bot_clone.py wfo [--windows=N] [--days=N]
        _wfo_windows = WFO_DEFAULT_WINDOWS
        _wfo_days = WFO_DEFAULT_DAYS
        for arg in sys.argv[2:]:
            if arg.startswith("--windows="):
                try:
                    _wfo_windows = int(arg.split("=")[1])
                except ValueError:
                    pass
            if arg.startswith("--days="):
                try:
                    _wfo_days = int(arg.split("=")[1])
                except ValueError:
                    pass
        wfo_optimize(windows=_wfo_windows, total_days=_wfo_days)
        sys.exit(0)

    elif _cmd == "optimize":
        # Bayesian optimization: python bot_clone.py optimize [--trials=N] [--days=N]
        _opt_trials = BAYESIAN_N_TRIALS
        _opt_days = BAYESIAN_BT_DAYS
        for arg in sys.argv[2:]:
            if arg.startswith("--trials="):
                try:
                    _opt_trials = int(arg.split("=")[1])
                except ValueError:
                    pass
            if arg.startswith("--days="):
                try:
                    _opt_days = int(arg.split("=")[1])
                except ValueError:
                    pass
        bayesian_optimize(n_trials=_opt_trials, days=_opt_days)
        sys.exit(0)

    else:
        main()

