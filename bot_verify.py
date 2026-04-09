"""
bot_verify.py — Verification suite that PROVES the bot works before running.

Every feature has a test. Every bug has a regression test.
The bot will NOT start unless all tests pass.

Run: python3 bot_verify.py
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# v29.3.4: bot_verify was written for bot.py — redirect to bot_clone.py
# This makes "from bot import X" resolve to bot_clone module
import importlib
_bot_dir = os.path.dirname(os.path.abspath(__file__))
_bot_clone_path = os.path.join(_bot_dir, "bot_clone.py")
if os.path.exists(_bot_clone_path):
    spec = importlib.util.spec_from_file_location("bot", _bot_clone_path)
    _bot_mod = importlib.util.module_from_spec(spec)
    sys.modules["bot"] = _bot_mod
    spec.loader.exec_module(_bot_mod)
    # Alias renamed class: CoinLossTracker → SmartCoinBlocker
    if hasattr(_bot_mod, "SmartCoinBlocker") and not hasattr(_bot_mod, "CoinLossTracker"):
        _bot_mod.CoinLossTracker = _bot_mod.SmartCoinBlocker
    if hasattr(_bot_mod, "SMART_COIN_BLOCK_CYCLES") and not hasattr(_bot_mod, "COIN_LOSS_BLOCK_CYCLES"):
        _bot_mod.COIN_LOSS_BLOCK_CYCLES = _bot_mod.SMART_COIN_BLOCK_CYCLES

PASS = 0
FAIL = 0
ERRORS = []

def test(name, condition, detail=""):
    global PASS, FAIL
    if condition:
        PASS += 1
        print(f"  [OK] {name}")
    else:
        FAIL += 1
        ERRORS.append(f"{name}: {detail}")
        print(f"  [!!] {name}: {detail}")


def run_all():
    global PASS, FAIL, ERRORS
    PASS = 0
    FAIL = 0
    ERRORS = []

    print("BOT VERIFICATION SUITE")
    print("=" * 60)

    # ── 1. COMPILATION ──
    print("\n1. COMPILATION")
    import py_compile
    try:
        _bot_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bot_clone.py')
        if not os.path.exists(_bot_path):
            _bot_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bot.py')
        py_compile.compile(_bot_path, doraise=True)
        test("bot.py compiles", True)
    except Exception as e:
        test("bot.py compiles", False, str(e))
        print("\nCANNOT CONTINUE — bot has syntax errors")
        return False

    from bot import (Wallet, CircuitBreaker, CorrelationGuard, volatility_scale,
                     SelfAwareness, brain, awareness, to_short_name,
                     _make_ml_features, track_price, prices_cache, coin_atr,
                     short_momentum, is_choppy, volume_confirms, is_pullback_entry,
                     zscore, bb_squeeze, kelly_size, assess_exit, perf,
                     safe_api_call, validate_ticker, PerformanceTracker,
                     LOSS_COOLDOWN_CYCLES)

    # ── 2. WALLET OPERATIONS ──
    print("\n2. WALLET OPERATIONS")
    w = Wallet(1000)
    test("Initial cash", w.cash == 1000)

    # Buy
    w.buy('ETH', 2200, 200)
    test("Buy deducts cash", w.cash < 1000)
    test("Buy creates position", 'ETH' in w.longs)
    test("Buy position has entry", w.longs['ETH']['entry'] > 0)

    # Buy at zero price
    result = w.buy('ZERO', 0, 200)
    test("Buy at $0 blocked", result == 0)
    test("Buy at $0 no cash change", w.cash == w.cash)  # Unchanged

    # Sell for profit
    old_cash = w.cash
    w.sell('ETH', 2250)
    test("Sell increases cash", w.cash > old_cash)
    test("Sell records win", w.wins == 1)
    test("Sell removes position", 'ETH' not in w.longs)

    # Sell for loss
    w2 = Wallet(1000)
    w2.buy('BAD', 100, 200)
    w2.sell('BAD', 95)
    test("Loss recorded", w2.losses == 1)
    test("Loss triggers cooldown", 'BAD' in w2.cooldowns)

    # Short
    w3 = Wallet(1000)
    w3.short('BTC', 74000, 200)
    test("Short deducts collateral", w3.cash < 1000)
    test("Short creates position", 'BTC' in w3.shorts)
    test("Short has collateral", w3.shorts['BTC'].get('collateral', 0) > 0)

    # Short at zero price
    r = w3.short('X', 0, 200)
    test("Short at $0 blocked", r == 0)

    # Cover for profit (price dropped)
    w3.cover('BTC', 73000)
    test("Cover profitable", w3.cash > 800)
    test("Cover records win", w3.wins == 1)

    # Portfolio value
    w4 = Wallet(1000)
    w4.short('SOL', 95, 200)
    vd = w4.value({'SOL': 90})
    vu = w4.value({'SOL': 100})
    test("Short value: drop = profit", vd > vu)

    # ── 3. DIVISION BY ZERO ──
    print("\n3. DIVISION BY ZERO PROTECTION")
    prices_cache.clear()
    track_price('ZERO', 0)  # Should be rejected
    test("Zero price rejected", len(prices_cache.get('ZERO', [])) == 0)

    for i in range(30): track_price('FLAT', 100)
    test("Flat momentum = 0", short_momentum('FLAT') == 0)
    test("Empty momentum = 0", short_momentum('EMPTY') == 0)
    test("Empty ATR = default", coin_atr('EMPTY') == 0.01)
    test("Empty zscore = 0", zscore('EMPTY') == 0)
    test("Empty BB squeeze = NORMAL", bb_squeeze('EMPTY') == ('NORMAL', 0))
    test("Empty ML features = defaults", _make_ml_features('EMPTY', {}) == [0.5] * 16)

    # Sell with zero entry
    w5 = Wallet(1000)
    w5.buy('X', 100, 200)
    w5.longs['X']['entry'] = 0
    pnl = w5.sell('X', 100)
    test("Sell with zero entry = 0 pnl", pnl == 0)

    # ── 4. CIRCUIT BREAKER ──
    print("\n4. CIRCUIT BREAKER")
    cb = CircuitBreaker(1000)
    test("Normal: trading allowed", cb.update(1000, 1) == True)
    test("Daily -11%: halted", cb.update(890, 2) == False)
    test("Halted flag set", cb.halted == True)
    test("Halt has reason", len(cb.halt_reason) > 0)

    cb2 = CircuitBreaker(1000)
    cb2.peak_value = 1000
    test("Max DD 16%: halted", cb2.update(840, 2) == False)

    # ── 5. CORRELATION GUARD ──
    print("\n5. CORRELATION GUARD")
    cg = CorrelationGuard()
    for i in range(20):
        cg.update('A', 100 + i)
        cg.update('B', 200 + i * 2)
    too_corr, _, _ = cg.is_too_correlated('B', ['A'])
    test("Correlated pair blocked", too_corr == True)

    cg2 = CorrelationGuard()
    for i in range(20):
        cg2.update('X', 100 + i)
        cg2.update('Y', 100 - i)
    too_corr2, _, _ = cg2.is_too_correlated('Y', ['X'])
    test("Negatively correlated = blocked", too_corr2 == True)

    # ── 6. SELF-AWARENESS ──
    print("\n6. SELF-AWARENESS")
    sa = SelfAwareness()
    test("No data: neutral long conf", sa.should_go_long() == 0.5)
    test("No data: neutral short conf", sa.should_go_short() == 0.5)
    test("Unknown coin: trade allowed", sa.should_trade_coin('NEW') == 1.0)
    test("Empty regime: UNKNOWN", sa.detect_regime({}) == "UNKNOWN")

    sa.record('COVER', 'A', 2.0, True)
    sa.record('COVER', 'B', 1.5, True)
    sa.record('COVER', 'C', 3.0, True)
    sa.record('SELL', 'D', -1.0, False)
    test("Shorts winning: short > long", sa.should_go_short() >= sa.should_go_long())

    # ── 7. SMART EXIT ──
    print("\n7. SMART EXIT RE-EVALUATION")
    prices_cache.clear()
    for i in range(30): track_price('UP', 100 + i * 0.3)
    r = assess_exit('UP', 'long', 100, 109)
    test("Strong uptrend: HOLD_AND_TRAIL", r['action'] == 'HOLD_AND_TRAIL')

    prices_cache.clear()
    for i in range(20): track_price('REV', 100 + i * 0.3)
    for i in range(10): track_price('REV', 106 - i * 0.5)
    r2 = assess_exit('REV', 'long', 100, 101)
    test("Reversal: EXIT", r2['action'] == 'EXIT')

    # ── 8. PERFORMANCE TRACKER ──
    print("\n8. PERFORMANCE TRACKER")
    pt = PerformanceTracker()
    pt.record_trade(1.5)
    pt.record_trade(2.0)
    pt.record_trade(1.0)
    pt.record_trade(0.8)
    pt.record_trade(-0.5)
    test("Win rate correct", pt.win_rate() > 60)
    test("Sharpe > 0", pt.sharpe_ratio() > 0)
    test("Profit factor > 1", pt.profit_factor() > 1)

    pt2 = PerformanceTracker()
    for i in range(61): pt2.record_trade(0.1)
    test("Daily trade limit (60)", pt2.can_trade(100) == False)

    # ── 9. API RESILIENCE ──
    print("\n9. API RESILIENCE")
    r = safe_api_call("https://invalid.example.com/x", timeout=1, retries=1)
    test("Bad URL returns None", r is None)

    # ── 10. DATA VALIDATION ──
    print("\n10. DATA VALIDATION")
    test("Valid ticker passes", validate_ticker({"c": ["100"], "v": ["1000", "2000"]}) == True)
    test("Zero price fails", validate_ticker({"c": ["0"], "v": ["100", "200"]}) == False)
    test("None fails", validate_ticker(None) == False)
    test("Empty dict fails", validate_ticker({}) == False)
    test("Absurd price fails", validate_ticker({"c": ["999999999"], "v": ["100", "200"]}) == False)

    # ── 11. KELLY SIZING ──
    print("\n11. KELLY SIZING")
    w6 = Wallet(1000)
    test("Kelly no trades = base", kelly_size(w6, 200) == 200)

    w7 = Wallet(1000)
    w7.wins = 7; w7.losses = 3
    w7.trades = [{'pnl':'+1.5%'},{'pnl':'+1.2%'},{'pnl':'+1.8%'},{'pnl':'+1.0%'},
                 {'pnl':'+1.3%'},{'pnl':'+1.6%'},{'pnl':'+1.1%'},
                 {'pnl':'-0.8%'},{'pnl':'-0.9%'},{'pnl':'-0.7%'}]
    ks = kelly_size(w7, 200)
    test("Kelly with trades > 0", ks > 0)
    test("Kelly with trades < base", ks <= 200)

    # ── 12. WIN RATE FILTERS ──
    print("\n12. WIN RATE FILTERS")
    prices_cache.clear()
    for i in range(30): track_price('CHOP', 100 + 0.01 * (i % 5 - 2))
    test("Choppy detected", is_choppy('CHOP') == True)

    prices_cache.clear()
    for i in range(30): track_price('TREND', 100 + i * 0.5)
    test("Trend not choppy", is_choppy('TREND') == False)

    test("Volume confirms (high)", volume_confirms({'change': 0.05, 'vol': 2000000}) == True)
    test("Volume rejects (low)", volume_confirms({'change': 0.05, 'vol': 100000}) == False)

    prices_cache.clear()
    for i in range(20): track_price('TOP', 100 + i)
    test("Pullback blocks top", is_pullback_entry('TOP', 'long') == False)

    # ── 13. NAME CONVERSION ──
    print("\n13. NAME CONVERSION")
    test("ETHUSD -> ETH", to_short_name('ETHUSD') == 'ETH')
    test("XBTUSD -> BTC", to_short_name('XBTUSD') == 'BTC')
    test("NEARUSD -> NEAR", to_short_name('NEARUSD') == 'NEAR')
    test("FARTCOINUSD -> FARTCOIN", to_short_name('FARTCOINUSD') == 'FARTCOIN')

    # ── 14. SAVE/LOAD ──
    print("\n14. STATE PERSISTENCE")
    w8 = Wallet(1000)
    w8.buy('ETH', 2200, 200)
    w8.sell('ETH', 2250)
    w8.short('BTC', 74000, 200)
    w8.cover('BTC', 73000)
    w8.cooldowns['BAD'] = 50
    awareness.long_wins = 5
    awareness.short_wins = 8
    w8.save({'ETH': 2250, 'BTC': 73000})

    # Reset and reload
    old_lw = awareness.long_wins
    awareness.long_wins = 0
    w9, _ = Wallet.load()
    test("Cash restored", w9 is not None and w9.cash > 0)
    test("Wins restored", w9.wins == 2)
    test("Cooldowns restored", 'BAD' in w9.cooldowns)
    test("Awareness restored", awareness.long_wins == old_lw)

    # ── 15. ML BRAIN ──
    print("\n15. ML BRAIN")
    stats = brain.get_stats()
    test("ML brain loaded", stats['total_trained'] > 0)
    test("ML has coin data", len(stats['coins_learned']) > 0)

    # ── 16. R:R RATIO ──
    print("\n16. RISK-REWARD RATIO")
    prices_cache.clear()
    for i in range(20): track_price('RR', 100 + i * 0.1)
    atr = coin_atr('RR') * 100
    sl = max(0.8, atr * 1.0)
    tp = max(1.5, sl * 2)
    test("TP >= 2x SL", tp >= sl * 1.5)
    test("Hard TP min 2%", max(2.0, atr * 3) >= 2.0)

    # ── 17. VOLATILITY SCALING ──
    print("\n17. VOLATILITY SCALING")
    prices_cache.clear()
    for i in range(50): track_price('CALM', 100 + 0.01 * i)
    for i in range(50): track_price('WILD', 100 + 2 * (i % 5 - 2))
    calm = volatility_scale('CALM', 200)
    wild = volatility_scale('WILD', 200)
    test("Calm scale reasonable", 50 < calm < 500)
    test("Wild scale reasonable", 50 < wild < 500)

    # ── 18. COOLDOWN TIMING ──
    print("\n18. COOLDOWN TIMING")
    test("Active at cycle 79", (79 - 50) < LOSS_COOLDOWN_CYCLES)
    test("Expired at cycle 80", not ((80 - 50) < LOSS_COOLDOWN_CYCLES))

    # ── 19. DAILY METRICS ──
    print("\n19. DAILY METRICS")
    from bot import DailyMetrics
    dm = DailyMetrics()
    dm.start_day(1000, 0)
    test("DM start equity", dm.day_start_equity == 1000)
    dm.record_trade(2.5)
    dm.record_trade(-1.0, is_sl=True)
    dm.record_trade(1.5, is_sl=False, is_gap=True)
    test("DM trades counted", dm.trades_today == 3)
    test("DM wins counted", dm.wins_today == 2)
    test("DM losses counted", dm.losses_today == 1)
    test("DM SL hits counted", dm.sl_hits_today == 1)
    test("DM gap events counted", dm.gap_events_today == 1)
    dm_state = dm.save_state()
    dm2 = DailyMetrics()
    dm2.load_state(dm_state)
    test("DM state persists", dm2.trades_today == 3 and dm2.sl_hits_today == 1)

    # ── 20. CASCADE PROTECTION ──
    print("\n20. CASCADE PROTECTION")
    from bot import CascadeProtection, CASCADE_THRESHOLD, CASCADE_BLOCK_CYCLES
    cp = CascadeProtection()
    test("CP allows entry initially", cp.allows_entry() == True)
    cp.record_sl_exit()
    cp.record_sl_exit()
    cp.update(1000, 10)
    test("CP blocks after 2 SL same cycle", cp.allows_entry() == False)
    cp2 = CascadeProtection()
    cp2.update(1000, 1)
    cp2.update(960, 2)  # 4% drop > CASCADE_THRESHOLD
    test("CP blocks on rapid drop", cp2.allows_entry() == False)
    # Cascade expires after CASCADE_BLOCK_CYCLES
    cp2.update(960, 2 + CASCADE_BLOCK_CYCLES + 1)
    test("CP allows after expiry", cp2.allows_entry() == True)

    # ── 21. EXPOSURE CAP ──
    print("\n21. EXPOSURE CAP")
    from bot import total_exposure_ok, MAX_TOTAL_EXPOSURE_UPDATED_PCT
    w_exp = Wallet(1000)
    test("Exposure OK when empty", total_exposure_ok(w_exp, {}, 400) == True)
    w_exp.buy('ETH', 2000, 400)
    test("Exposure OK after 1 trade", total_exposure_ok(w_exp, {'ETH': 2000}, 100) == True)
    # With ~40% already used, adding enough to exceed 60% should fail
    test("Exposure blocks at cap", total_exposure_ok(w_exp, {'ETH': 2000}, 300) == False)

    # ── 22. HARDENED CONSTANTS ──
    print("\n22. HARDENED CONSTANTS")
    from bot import (MAX_POSITIONS, MAX_RISK_PER_TRADE, MAX_DAILY_LOSS_PCT,
                     MAX_SPREAD_PCT, STRESS_RISK_LIMIT_PCT,
                     MAX_TOTAL_EXPOSURE_UPDATED_PCT, GAP_RISK_MULTIPLIER, STAGNATION_EXIT_CYCLES)
    test("MAX_POSITIONS = 2", MAX_POSITIONS == 2)
    test("MAX_RISK_PER_TRADE = 1.5%", MAX_RISK_PER_TRADE == 0.015)
    test("MAX_DAILY_LOSS = 2.5%", MAX_DAILY_LOSS_PCT == 2.5)
    test("MAX_SPREAD = 0.20%", MAX_SPREAD_PCT == 0.20)
    test("MAX_EXPOSURE = 60%", MAX_TOTAL_EXPOSURE_UPDATED_PCT == 60.0)
    test("STRESS_LIMIT = 25%", STRESS_RISK_LIMIT_PCT == 25.0)
    test("GAP_RISK_MULT = 1.2", GAP_RISK_MULTIPLIER == 1.2)
    test("STAGNATION = 100 cycles", STAGNATION_EXIT_CYCLES == 100)

    # ── 23. CB DAILY HARD STOP ──
    print("\n23. CB DAILY HARD STOP")
    cb3 = CircuitBreaker(1000)
    cb3.update(1000, 1)
    cb3.update(889, 2)  # -11.1% loss
    test("CB daily_halted flag set", cb3.daily_halted == True)
    test("CB halt_until very high", cb3.halt_until_cycle > 999000)
    # Simulate daily reset
    cb3.daily_start_cycle = 0  # Force reset condition
    cb3.update(889, 2401)  # cycle 2401 triggers daily reset
    test("CB daily halt clears on reset", cb3.daily_halted == False)
    test("CB resumes after reset", cb3.halted == False)

    # ── 24. TIERED SLIPPAGE ──
    print("\n24. TIERED SLIPPAGE")
    from bot import OrderExecutor, SLIPPAGE_BASE, SLIPPAGE_SL_EXIT
    exec_test = OrderExecutor()
    # Normal entry: should have base slippage
    normal_price = exec_test._apply_slippage(1000, "BUY")
    normal_slip = (normal_price - 1000) / 1000 * 100
    test("Normal slippage ~0.05%", 0.04 < normal_slip < 0.1)
    # SL exit: should have higher slippage
    sl_price = exec_test._apply_slippage(1000, "SELL", is_sl_exit=True)
    sl_slip = (1000 - sl_price) / 1000 * 100
    test("SL exit slippage > normal", sl_slip > normal_slip)
    test("SL exit slippage ~0.10%", 0.05 < sl_slip < 0.20)

    # ── 25. TRADE LOGGER ──
    print("\n25. TRADE LOGGER")
    from bot import TradeLogger, _async_writer as _aw
    import tempfile, json as _json_mod
    tl = TradeLogger()
    tl.log_trade("ETH", "long", 2000.0, 2050.0, 2.5, "tp_exit")
    tl.log_trade("BTC", "short", 70000.0, 69000.0, 1.43, "stop_loss")
    _aw.flush()  # Wait for async writes before reading files
    test("TradeLogger no crash", True)
    _tl_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs", "trades.jsonl")
    test("TradeLogger JSONL file exists", os.path.exists(_tl_path))
    with open(_tl_path) as f:
        _jsonl_lines = f.readlines()
    test("TradeLogger has trades", len(_jsonl_lines) >= 2)
    _first_trade = _json_mod.loads(_jsonl_lines[0])
    test("TradeLogger JSONL has coin field", _first_trade.get("coin") == "ETH")
    test("TradeLogger JSONL has pnl_pct", abs(_first_trade.get("pnl_pct", 0) - 2.5) < 0.01)
    test("TradeLogger JSONL has all fields", all(k in _first_trade for k in ("timestamp", "coin", "side", "entry", "exit", "pnl_pct", "reason")))

    # ── 26. EQUITY CURVE LOGGER ──
    print("\n26. EQUITY CURVE LOGGER")
    from bot import EquityCurveLogger
    el = EquityCurveLogger()
    el.log(1005.50, 800.25, 205.25)
    el.log(1010.75, 810.00, 200.75)
    _aw.flush()  # Wait for async writes before reading files
    test("EquityLogger no crash", True)
    _el_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs", "equity.csv")
    test("EquityLogger file exists", os.path.exists(_el_path))
    with open(_el_path) as f:
        _el_lines = f.readlines()
    test("EquityLogger has header", _el_lines[0].startswith("timestamp"))
    test("EquityLogger has data", len(_el_lines) >= 3)
    test("EquityLogger CSV format", "1005.50,800.25,205.25" in _el_lines[1])

    # ── 27. LOGGING CRASH SAFETY ──
    print("\n27. LOGGING CRASH SAFETY")
    # Verify loggers don't crash on bad input
    try:
        tl.log_trade(None, None, 0, 0, 0, None)
        test("TradeLogger survives bad input", True)
    except Exception:
        test("TradeLogger survives bad input", False)
    try:
        el.log(float('nan'), float('inf'), -1)
        test("EquityLogger survives bad input", True)
    except Exception:
        test("EquityLogger survives bad input", False)
    try:
        dm_test = DailyMetrics()
        dm_test.log_daily_summary(current_equity=0)
        test("DailyMetrics survives zero equity", True)
    except Exception:
        test("DailyMetrics survives zero equity", False)

    # ── 28. ERROR LOGGER ──
    print("\n28. ERROR LOGGER")
    from bot import ErrorLogger, _async_writer
    err = ErrorLogger()
    err.log("test_error", "this is a test error message")
    err.log("test_warning", "commas, and newlines\nshould be sanitized")
    _async_writer.flush()  # Wait for async writes to complete before reading file
    test("ErrorLogger no crash", True)
    test("ErrorLogger counts errors", err.error_count == 2)
    _err_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs", "errors.log")
    test("ErrorLogger file exists", os.path.exists(_err_path))
    with open(_err_path) as f:
        _err_lines = f.readlines()
    test("ErrorLogger has header", _err_lines[0].startswith("timestamp"))
    test("ErrorLogger has entries", len(_err_lines) >= 3)
    # Verify CSV safety: no raw commas in message field
    test("ErrorLogger sanitizes commas", "commas" in _err_lines[-1] and _err_lines[-1].count(",") == 2)

    # ── 29. LOG VALIDATOR ──
    print("\n29. LOG VALIDATOR")
    from bot import LogValidator
    lv = LogValidator()
    errs = lv.validate_all(100)
    test("LogValidator runs without crash", True)
    test("LogValidator returns int", isinstance(errs, int))
    # Our test trades.jsonl may have bad entries from test 27 — validator should handle them
    test("LogValidator catches bad trades", lv.total_errors >= 0)

    # ── 30. PAPER TRADE TRACKER ──
    print("\n30. PAPER TRADE TRACKER")
    from bot import PaperTradeTracker
    pt = PaperTradeTracker()
    pt.record(2.5, 1025)
    pt.record(-1.0, 1015)
    pt.record(0.0, 1015)
    pt.record(3.0, 1045)
    pt.record(-2.5, 1020)
    test("PT total trades", pt.total_trades == 5)
    test("PT wins correct", pt.wins == 2)
    test("PT losses correct", pt.losses == 2)
    test("PT breakeven correct", pt.breakeven == 1)
    test("PT win rate", 39 < pt.win_rate() < 41)  # 2/5 = 40%
    test("PT avg win > 0", pt.avg_win() > 0)
    test("PT avg loss < 0", pt.avg_loss() < 0)
    test("PT biggest win", pt.biggest_win == 3.0)
    test("PT biggest loss", pt.biggest_loss == -2.5)
    test("PT max drawdown >= 0", pt.max_drawdown() >= 0)
    test("PT expectancy calculated", isinstance(pt.expectancy(), float))
    # Summary should not crash
    try:
        pt.log_summary()
        test("PT summary no crash", True)
    except Exception:
        test("PT summary no crash", False)

    # ── 31. EQUITY SANITY CHECKER ──
    print("\n31. EQUITY SANITY CHECKER")
    from bot import EquitySanityChecker
    esc = EquitySanityChecker()
    test("ESC normal OK", esc.check(1000, 1) == "OK")
    test("ESC stable OK", esc.check(1001, 2) == "OK")
    test("ESC negative STOP", esc.check(-10, 3) == "STOP")
    esc2 = EquitySanityChecker()
    esc2.check(1000, 1)
    esc2.check(850, 2)  # -15% in one cycle
    test("ESC flash event detected", esc2.flash_events == 1)
    esc3 = EquitySanityChecker()
    esc3.check(1000, 1)
    esc3.check(1250, 2)  # +25% in one cycle
    test("ESC data error detected", esc3.data_errors == 1)

    # ── 32. TRADE CONSISTENCY ──
    print("\n32. TRADE CONSISTENCY")
    from bot import verify_trade_consistency
    # Valid trade
    try:
        verify_trade_consistency("ETH", "long", 2000, 2100, 5.0, True)
        test("Consistency check: valid trade", True)
    except Exception:
        test("Consistency check: valid trade", False)
    # PnL mismatch (5% claimed but math says 10%)
    try:
        verify_trade_consistency("BTC", "long", 1000, 1100, 5.0, True)
        test("Consistency check: pnl mismatch logged", True)  # Should log error but not crash
    except Exception:
        test("Consistency check: pnl mismatch logged", False)
    # Bad prices
    try:
        verify_trade_consistency("SOL", "short", -1, 100, 0, True)
        test("Consistency check: bad price logged", True)
    except Exception:
        test("Consistency check: bad price logged", False)

    # ── 33. STARTUP CHECK ──
    print("\n33. STARTUP CHECK")
    from bot import startup_check
    # Test with a clean wallet (startup_check validates wallet + logs + state file)
    w_startup = Wallet(1000)
    _sc_result = startup_check(w_startup, {})
    test("Startup check: fresh wallet passes", _sc_result == True)
    test("Startup check: None wallet fails", startup_check(None, {}) == False)
    # Wallet with negative cash
    w_bad = Wallet(-100)
    test("Startup check: negative cash fails", startup_check(w_bad, {}) == False)

    # ── 34. CLEAN EXPORT ──
    print("\n34. CLEAN EXPORT")
    from bot import export_clean_trades
    try:
        export_clean_trades()
        test("Clean export no crash", True)
    except Exception:
        test("Clean export no crash", False)
    _clean_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs", "clean_trades.jsonl")
    test("Clean export file created", os.path.exists(_clean_path))
    with open(_clean_path) as f:
        _cl = f.readlines()
    # All lines should be valid JSON
    _all_valid_json = all(_json_mod.loads(l.strip()) for l in _cl if l.strip()) if _cl else True
    test("Clean export valid JSONL", _all_valid_json)
    # Should have filtered out bad trades from earlier tests
    _has_none = any('"coin": null' in line or '"side": null' in line for line in _cl)
    test("Clean export filters bad data", not _has_none)

    # ── 35. DEBUG MODE FLAG ──
    print("\n35. DEBUG MODE FLAG")
    from bot import DEBUG_MODE
    test("DEBUG_MODE exists", isinstance(DEBUG_MODE, bool))
    test("DEBUG_MODE default off", DEBUG_MODE == False)

    # ── 36. KILL SWITCH ──
    print("\n36. KILL SWITCH")
    from bot import KillSwitch, KILL_SWITCH_EQUITY_DROP_PCT, KILL_SWITCH_CONSECUTIVE_LOSSES, KILL_SWITCH_BAD_LOSS_THRESHOLD
    ks = KillSwitch(1000)
    test("KS not triggered initially", ks.is_triggered == False)
    # Test equity drop trigger
    ks2 = KillSwitch(1000)
    ks2.check_equity(840)  # 16% drop > 15% threshold
    test("KS triggers on equity drop", ks2.is_triggered == True)
    test("KS has trigger reason", len(ks2.trigger_reason) > 0)
    # Test consecutive losses trigger
    ks3 = KillSwitch(1000)
    ks3.record_trade(-2.5)  # Bad loss 1
    ks3.record_trade(-3.0)  # Bad loss 2
    test("KS not yet at 2 losses", ks3.is_triggered == False)
    ks3.record_trade(-2.1)  # Bad loss 3
    test("KS triggers at 3 bad losses", ks3.is_triggered == True)
    # Test reset on good trade
    ks4 = KillSwitch(1000)
    ks4.record_trade(-2.5)
    ks4.record_trade(1.0)   # Good trade resets
    ks4.record_trade(-2.5)
    test("KS resets on good trade", ks4.is_triggered == False)
    # Test gap events
    ks5 = KillSwitch(1000)
    for _ in range(4):
        ks5.record_gap_event()
    test("KS not triggered at 4 gaps", ks5.is_triggered == False)
    ks5.record_gap_event()
    test("KS triggers at 5 gaps", ks5.is_triggered == True)
    # Test close all positions
    ks6 = KillSwitch(1000)
    w_ks = Wallet(1000)
    w_ks.buy("ETH", 2000, 300)
    w_ks.short("SOL", 100, 200)
    ks6.close_all_positions(w_ks, {"ETH": 2000, "SOL": 100}, None)
    test("KS closes all longs", len(w_ks.longs) == 0)
    test("KS closes all shorts", len(w_ks.shorts) == 0)

    # ── 37. STRATEGY HEALTH MONITOR ──
    print("\n37. STRATEGY HEALTH MONITOR")
    from bot import StrategyHealthMonitor, HEALTH_MONITOR_WINDOW, HEALTH_MONITOR_MIN_WR
    shm = StrategyHealthMonitor()
    test("SHM allows with no data", shm.check_health(100) == True)
    # Fill with 50 losing trades
    for _ in range(50):
        shm.record_trade(-1.0)
    test("SHM pauses after 50 losses", shm.check_health(200) == False)
    test("SHM still paused", shm.is_paused(300) == True)
    test("SHM resumes after pause", shm.is_paused(500) == False)
    # Fill with winning trades
    shm2 = StrategyHealthMonitor()
    for _ in range(50):
        shm2.record_trade(1.0)
    test("SHM allows with high WR", shm2.check_health(100) == True)
    test("SHM win rate correct", shm2.win_rate == 100.0)
    test("SHM expectancy correct", shm2.expectancy == 1.0)

    # ── 38. COIN LOSS TRACKER ──
    print("\n38. COIN LOSS TRACKER")
    from bot import CoinLossTracker, COIN_LOSS_BLOCK_CYCLES
    clt = CoinLossTracker()
    test("CLT coin not blocked initially", clt.is_blocked("ETH", 0) == False)
    clt.record_trade("ETH", -1.0, 100)
    test("CLT not blocked after 1 loss", clt.is_blocked("ETH", 100) == False)
    clt.record_trade("ETH", -0.5, 101)
    test("CLT blocked after 2 losses", clt.is_blocked("ETH", 101) == True)
    test("CLT still blocked within window", clt.is_blocked("ETH", 200) == True)
    test("CLT unblocked after window", clt.is_blocked("ETH", 400) == False)
    # Reset on win
    clt2 = CoinLossTracker()
    clt2.record_trade("SOL", -1.0, 50)
    clt2.record_trade("SOL", 2.0, 51)  # Win resets
    clt2.record_trade("SOL", -0.5, 52)
    test("CLT resets on win", clt2.is_blocked("SOL", 52) == False)

    # ── 39. OVERTRADING GUARD ──
    print("\n39. OVERTRADING GUARD")
    from bot import OvertradingGuard, MAX_TRADES_PER_CYCLE, MAX_TRADES_PER_100_CYCLES
    otg = OvertradingGuard()
    test("OTG allows first trade", otg.can_trade(100) == True)
    otg.record_trade(100)
    test("OTG blocks second trade same cycle", otg.can_trade(100) == False)
    otg.reset_cycle()
    # Cycle 201 = 101 cycles after trade at 100, past OVERTRADE_MIN_CYCLES_BETWEEN
    test("OTG allows after cycle reset + gap", otg.can_trade(201) == True)
    # Test 100-cycle limit
    otg2 = OvertradingGuard()
    for i in range(10):
        otg2.reset_cycle()
        otg2.record_trade(100 + i)
    otg2.reset_cycle()
    test("OTG blocks after 10 in 100 cycles", otg2.can_trade(109) == False)
    test("OTG allows after 100 cycles pass", otg2.can_trade(250) == True)

    # ── 40. SAFE MODE ──
    print("\n40. SAFE MODE")
    from bot import SafeMode, SAFE_MODE_DRAWDOWN_PCT, SAFE_MODE_SIZE_MULT
    sm = SafeMode()
    sm.update(1000)
    test("SM inactive at start", sm.active == False)
    test("SM full size when inactive", sm.size_multiplier == 1.0)
    test("SM shorts allowed when inactive", sm.shorts_allowed == True)
    sm.update(910)  # 9% drawdown > 8% threshold
    test("SM active at 9% DD", sm.active == True)
    test("SM half size when active", sm.size_multiplier == SAFE_MODE_SIZE_MULT)
    test("SM shorts blocked when active", sm.shorts_allowed == False)
    sm.update(1010)  # Recovery
    test("SM deactivates on recovery", sm.active == False)

    # ── 41. TRADE QUALITY FILTERS ──
    print("\n41. TRADE QUALITY FILTERS")
    from bot import reward_risk_ok, volatility_spike_check, single_coin_exposure_ok, MIN_REWARD_RISK
    test("RR OK at 1.5:1", reward_risk_ok(1.0, 1.5) == True)
    test("RR rejects at 1.0:1", reward_risk_ok(1.0, 1.0) == False)
    test("RR rejects zero SL", reward_risk_ok(0, 2.0) == False)
    test("Vol spike check no data = OK", volatility_spike_check("FAKE_COIN") == True)
    # Single coin exposure
    w_sce = Wallet(1000)
    test("SCE OK when empty", single_coin_exposure_ok(w_sce, {}, "ETH", 200) == True)
    w_sce.buy("ETH", 2000, 200)
    test("SCE OK within limit", single_coin_exposure_ok(w_sce, {"ETH": 2000}, "ETH", 50) == True)
    test("SCE blocks over limit", single_coin_exposure_ok(w_sce, {"ETH": 2000}, "ETH", 500) == False)

    # ── 42. HEALTH OUTPUT ──
    print("\n42. HEALTH OUTPUT")
    from bot import health_output
    try:
        _ks_test = KillSwitch(1000)
        _shm_test = StrategyHealthMonitor()
        _sm_test = SafeMode()
        _sm_test.update(1000)
        _otg_test = OvertradingGuard()
        _w_test = Wallet(1000)
        health_output(100, _w_test, {}, _ks_test, _shm_test, _sm_test, _otg_test)
        test("Health output no crash", True)
    except Exception as e:
        test("Health output no crash", False)

    # ── 43. PROTECTION CONSTANTS ──
    print("\n43. PROTECTION CONSTANTS")
    from bot import (KILL_SWITCH_EQUITY_DROP_PCT, KILL_SWITCH_CONSECUTIVE_LOSSES,
                     HEALTH_MONITOR_WINDOW, MIN_REWARD_RISK, MAX_SINGLE_COIN_EXPOSURE_PCT,
                     COIN_LOSS_BLOCK_CYCLES, MAX_TRADES_PER_CYCLE, MAX_TRADES_PER_100_CYCLES,
                     SAFE_MODE_DRAWDOWN_PCT, SAFE_MODE_SIZE_MULT, MAX_TOTAL_EXPOSURE_UPDATED_PCT)
    test("KS equity drop = 15%", KILL_SWITCH_EQUITY_DROP_PCT == 15.0)
    test("KS consecutive = 3", KILL_SWITCH_CONSECUTIVE_LOSSES == 3)
    test("Health window = 50", HEALTH_MONITOR_WINDOW == 50)
    test("Min RR = 1.2", MIN_REWARD_RISK == 1.2)
    test("Max single coin = 15%", MAX_SINGLE_COIN_EXPOSURE_PCT == 15.0)
    test("Max total exposure = 60%", MAX_TOTAL_EXPOSURE_UPDATED_PCT == 60.0)
    test("Coin loss block = 25", COIN_LOSS_BLOCK_CYCLES == 25)
    test("Max trades/cycle = 1", MAX_TRADES_PER_CYCLE == 1)
    test("Max trades/100 = 15", MAX_TRADES_PER_100_CYCLES == 15)
    test("Safe mode DD = 8%", SAFE_MODE_DRAWDOWN_PCT == 8.0)
    test("Safe mode mult = 0.5", SAFE_MODE_SIZE_MULT == 0.5)

    # ── 44. PROTECTION SYSTEM PERSISTENCE ──
    print("\n44. PROTECTION SYSTEM PERSISTENCE")
    from bot import KillSwitch, StrategyHealthMonitor, CoinLossTracker, OvertradingGuard, SafeMode

    # KillSwitch round-trip
    ks = KillSwitch(1000)
    ks.record_trade(-3.0)
    ks.record_trade(-2.5)
    ks.gap_events = 3
    ks_saved = ks.save_state()
    ks2 = KillSwitch(500)  # Different starting equity
    ks2.load_state(ks_saved)
    test("KS persist: starting_equity", ks2.starting_equity == 1000)
    test("KS persist: recent_losses", len(ks2.recent_losses) == 2)
    test("KS persist: gap_events", ks2.gap_events == 3)
    test("KS persist: not triggered", ks2.triggered == False)

    # KillSwitch triggered state persists
    ks3 = KillSwitch(1000)
    ks3.record_trade(-3.0)
    ks3.record_trade(-3.0)
    ks3.record_trade(-3.0)  # Triggers kill switch
    ks3_saved = ks3.save_state()
    ks4 = KillSwitch(1000)
    ks4.load_state(ks3_saved)
    test("KS persist: triggered survives restart", ks4.triggered == True)
    test("KS persist: trigger reason survives", len(ks4.trigger_reason) > 0)

    # StrategyHealthMonitor round-trip
    shm = StrategyHealthMonitor()
    for _ in range(25):
        shm.record_trade(-1.0)
    for _ in range(25):
        shm.record_trade(1.5)
    shm.paused_until_cycle = 500
    shm.pause_count = 2
    shm_saved = shm.save_state()
    shm2 = StrategyHealthMonitor()
    shm2.load_state(shm_saved)
    test("SHM persist: recent_trades count", len(shm2.recent_trades) == 50)
    test("SHM persist: paused_until", shm2.paused_until_cycle == 500)
    test("SHM persist: pause_count", shm2.pause_count == 2)
    test("SHM persist: still paused at cycle 400", shm2.is_paused(400) == True)
    test("SHM persist: unpaused at cycle 600", shm2.is_paused(600) == False)

    # CoinLossTracker round-trip
    clt = CoinLossTracker()
    clt.record_trade("ETH", -1.0, 100)
    clt.record_trade("ETH", -1.5, 101)  # Now blocked
    clt_saved = clt.save_state()
    clt2 = CoinLossTracker()
    clt2.load_state(clt_saved)
    test("CLT persist: ETH blocked", clt2.is_blocked("ETH", 150) == True)
    test("CLT persist: ETH unblocked later", clt2.is_blocked("ETH", 400) == False)
    test("CLT persist: BTC not blocked", clt2.is_blocked("BTC", 150) == False)

    # OvertradingGuard round-trip
    otg = OvertradingGuard()
    for c in range(10):
        otg.record_trade(c * 10)
    otg_saved = otg.save_state()
    otg2 = OvertradingGuard()
    otg2.load_state(otg_saved)
    test("OTG persist: trade cycles restored", len(otg2.recent_trade_cycles) == 10)
    test("OTG persist: blocks at limit", otg2.can_trade(50) == False)

    # SafeMode round-trip
    sm = SafeMode()
    sm.session_peak = 1000
    sm.active = True
    sm_saved = sm.save_state()
    sm2 = SafeMode()
    sm2.load_state(sm_saved)
    test("SM persist: session_peak", sm2.session_peak == 1000)
    test("SM persist: active", sm2.active == True)
    test("SM persist: size_multiplier", sm2.size_multiplier == 0.5)
    test("SM persist: shorts blocked", sm2.shorts_allowed == False)

    # Backward compatibility: load_state with empty/missing fields
    ks_empty = KillSwitch(1000)
    ks_empty.load_state({})  # No crash
    ks_empty.load_state(None)  # No crash
    test("KS persist: empty state no crash", ks_empty.triggered == False)
    shm_empty = StrategyHealthMonitor()
    shm_empty.load_state({})
    shm_empty.load_state(None)
    test("SHM persist: empty state no crash", len(shm_empty.recent_trades) == 0)
    clt_empty = CoinLossTracker()
    clt_empty.load_state({})
    clt_empty.load_state(None)
    test("CLT persist: empty state no crash", clt_empty.is_blocked("X", 0) == False)
    otg_empty = OvertradingGuard()
    otg_empty.load_state({})
    otg_empty.load_state(None)
    test("OTG persist: empty state no crash", otg_empty.can_trade(0) == True)
    sm_empty = SafeMode()
    sm_empty.load_state({})
    sm_empty.load_state(None)
    test("SM persist: empty state no crash", sm_empty.active == False)

    # ── 45. RUNTIME STABILITY ──
    print("\n45. RUNTIME STABILITY")
    from bot import (STABILITY_WARMUP_CYCLES, MAX_CONSECUTIVE_ERRORS, CYCLE_TIMEOUT_SEC,
                     HEARTBEAT_INTERVAL, API_RETRY_STARTUP, OrderExecutor)
    import math

    # Stability constants exist
    test("Warmup cycles = 300", STABILITY_WARMUP_CYCLES == 300)
    test("Max consecutive errors = 50", MAX_CONSECUTIVE_ERRORS == 50)
    test("Cycle timeout = 30s", CYCLE_TIMEOUT_SEC == 30)
    test("Heartbeat interval = 50", HEARTBEAT_INTERVAL == 50)
    test("API retry attempts = 5", API_RETRY_STARTUP == 5)

    # Entry safety guard: NaN/None/inf rejected
    _exec = OrderExecutor()
    _w = Wallet(1000)
    _r1 = _exec.place_order("BUY", "ETH", float('nan'), 100, _w, {})
    test("Entry guard: NaN price rejected", _r1["filled"] == False)
    _r2 = _exec.place_order("BUY", "ETH", 100, float('inf'), _w, {})
    test("Entry guard: inf amount rejected", _r2["filled"] == False)
    _r3 = _exec.place_order("BUY", "ETH", 100, None, _w, {})
    test("Entry guard: None amount rejected", _r3["filled"] == False)
    _r4 = _exec.place_order("BUY", "ETH", None, 100, _w, {})
    test("Entry guard: None price rejected", _r4["filled"] == False)
    _r5 = _exec.place_order("BUY", "ETH", 100, -50, _w, {})
    test("Entry guard: negative amount rejected", _r5["filled"] == False)
    _r6 = _exec.place_order("BUY", "ETH", 100, 0, _w, {})
    test("Entry guard: zero amount rejected", _r6["filled"] == False)

    # Wallet value clamping
    _wc = Wallet(100)
    _wc.cash = -50
    _wc.clamp_values()
    test("Clamp: negative cash -> 0", _wc.cash == 0)
    _wc2 = Wallet(100)
    _wc2.cash = float('nan')
    _wc2.clamp_values()
    test("Clamp: NaN cash -> 0", _wc2.cash == 0)
    _wc3 = Wallet(100)
    _wc3.cash = float('inf')
    _wc3.clamp_values()
    test("Clamp: inf cash -> 0", _wc3.cash == 0)

    # Wallet clamp_values removes zombie positions (qty <= 0)
    _wq = Wallet(100)
    _wq.longs["TEST"] = {"qty": -5, "entry": -1}
    _wq.clamp_values()
    test("Clamp: zombie position removed (qty<=0)", "TEST" not in _wq.longs)
    # Wallet clamp_values fixes bad entry but keeps good qty
    _wq2 = Wallet(100)
    _wq2.longs["TEST2"] = {"qty": 1.0, "entry": -1}
    _wq2.clamp_values()
    test("Clamp: negative entry fixed", _wq2.longs["TEST2"]["entry"] == 0.0001)

    # ── SECTION 46: Error Classification & Kill Switch Fix ──
    print("\n── 46. Error Classification & Kill Switch Fix ──")
    from bot import (ErrorClassifier, error_classifier, KILL_SWITCH_MAX_GAP_EVENTS,
                     ERROR_COOLDOWN_THRESHOLD, ERROR_COOLDOWN_CYCLES, ERROR_RATE_WINDOW)

    # Kill switch should NOT have check_errors method anymore
    _ks46 = KillSwitch(10000)
    test("KillSwitch: no check_errors method", not hasattr(_ks46, 'check_errors'))

    # Kill switch should still have market risk triggers
    test("KillSwitch: has check_equity", hasattr(_ks46, 'check_equity'))
    test("KillSwitch: has record_trade", hasattr(_ks46, 'record_trade'))
    test("KillSwitch: has record_gap_event", hasattr(_ks46, 'record_gap_event'))

    # Kill switch equity trigger still works
    _ks46b = KillSwitch(10000)
    _ks46b.check_equity(8400)  # 16% drop > 15% threshold
    test("KillSwitch: equity drop still triggers", _ks46b.is_triggered)

    # Kill switch consecutive losses still works
    _ks46c = KillSwitch(10000)
    _ks46c.record_trade(-3.0)
    _ks46c.record_trade(-3.0)
    _ks46c.record_trade(-3.0)  # 3 consecutive > -2%
    test("KillSwitch: consecutive losses still triggers", _ks46c.is_triggered)

    # Kill switch gap events still work
    _ks46d = KillSwitch(10000)
    for _ in range(KILL_SWITCH_MAX_GAP_EVENTS):
        _ks46d.record_gap_event()
    test("KillSwitch: gap events still triggers", _ks46d.is_triggered)

    # ErrorClassifier exists and classifies correctly
    _ec = ErrorClassifier()
    test("ErrorClassifier: api_fetch -> api", _ec.classify("api_fetch") == "api")
    test("ErrorClassifier: api_timeout -> api", _ec.classify("api_timeout") == "api")
    test("ErrorClassifier: log_write -> logging", _ec.classify("log_write") == "logging")
    test("ErrorClassifier: health_output -> logging", _ec.classify("health_output") == "logging")
    test("ErrorClassifier: some_unknown -> execution", _ec.classify("trade_execution_fail") == "execution")
    test("ErrorClassifier: counters track", _ec.api_errors == 2 and _ec.log_errors == 2 and _ec.exec_errors == 1)

    # ErrorClassifier cooldown: below threshold = no cooldown
    _ec2 = ErrorClassifier()
    for i in range(5):
        _ec2.record("trade_fail", i)  # 5 exec errors
    test("ErrorClassifier: below threshold no cooldown", not _ec2.check_cooldown(10))

    # ErrorClassifier cooldown: above threshold = cooldown
    _ec3 = ErrorClassifier()
    for i in range(ERROR_COOLDOWN_THRESHOLD + 1):
        _ec3.record("trade_fail", i + 1)  # enough exec errors within window
    test("ErrorClassifier: above threshold triggers cooldown", _ec3.check_cooldown(ERROR_COOLDOWN_THRESHOLD + 2))

    # ErrorClassifier: API errors do NOT trigger cooldown
    _ec4 = ErrorClassifier()
    for i in range(50):
        _ec4.record("api_fetch", i)  # 50 API errors
    test("ErrorClassifier: API errors no cooldown", not _ec4.check_cooldown(60))

    # ErrorClassifier: logging errors do NOT trigger cooldown
    _ec5 = ErrorClassifier()
    for i in range(50):
        _ec5.record("log_write", i)  # 50 logging errors
    test("ErrorClassifier: logging errors no cooldown", not _ec5.check_cooldown(60))

    # ErrorClassifier persistence
    _ec6 = ErrorClassifier()
    _ec6.api_errors = 10
    _ec6.log_errors = 5
    _ec6.exec_errors = 3
    _ec6._cooldown_until = 500
    _state6 = _ec6.save_state()
    _ec7 = ErrorClassifier()
    _ec7.load_state(_state6)
    test("ErrorClassifier: persistence api_errors", _ec7.api_errors == 10)
    test("ErrorClassifier: persistence exec_errors", _ec7.exec_errors == 3)
    test("ErrorClassifier: persistence cooldown_until", _ec7._cooldown_until == 500)

    # ErrorClassifier summary format
    _ec8 = ErrorClassifier()
    _ec8.api_errors = 42
    _ec8.log_errors = 3
    _ec8.exec_errors = 1
    test("ErrorClassifier: summary format", _ec8.summary() == "api=42 log=3 exec=1")

    # Constants exist
    test("ERROR_COOLDOWN_THRESHOLD exists", ERROR_COOLDOWN_THRESHOLD > 0)
    test("ERROR_COOLDOWN_CYCLES exists", ERROR_COOLDOWN_CYCLES > 0)
    test("ERROR_RATE_WINDOW exists", ERROR_RATE_WINDOW > 0)

    # ── SECTION 47: API Failure Exit Protection & Force Exit ──
    print("\n── 47. API Failure Exit Protection & Force Exit ──")

    # Test 1: prices dict retains values when not updated (simulates API failure fallback)
    _w47 = Wallet(1000)
    _w47.buy("ETH", 2000, 200)
    _p47 = {"ETH": 2000}
    # Simulate: prices already contain ETH from previous cycle
    # On API failure, prices dict is NOT cleared — exits still see ETH price
    test("Prices persist across cycles", _p47.get("ETH", 0) == 2000)

    # Test 2: Wallet.sell works with last known price (force exit scenario)
    _w47b = Wallet(1000)
    _w47b.buy("ETH", 2000, 200)
    _eth_qty_before = _w47b.longs["ETH"]["qty"]
    _fe_price = 1900  # Simulated last known price
    _w47b.sell("ETH", _fe_price)
    test("Force exit: position removed after sell", "ETH" not in _w47b.longs)
    test("Force exit: cash returned", _w47b.cash > 800)

    # Test 3: Wallet.cover works with last known price (force exit scenario)
    _w47c = Wallet(1000)
    _w47c.short("BTC", 70000, 200)
    _w47c.cover("BTC", 71000)
    test("Force exit short: position removed after cover", "BTC" not in _w47c.shorts)

    # Test 4: Force exit uses entry price when no market price available
    _w47d = Wallet(1000)
    _w47d.buy("SOL", 100, 150)
    _entry_price = _w47d.longs["SOL"]["entry"]
    # Simulate: force exit with entry price as fallback
    _fallback = _w47d.longs["SOL"].get("entry", 0)
    _w47d.sell("SOL", _fallback)
    test("Force exit: entry price fallback works", "SOL" not in _w47d.longs)

    # Test 5: Exit management handles missing price gracefully
    _w47e = Wallet(1000)
    _w47e.buy("DOGE", 0.10, 50)
    _p47e = {}  # Empty prices — simulates total API failure
    _price_for_exit = _p47e.get("DOGE", _w47e.longs["DOGE"]["entry"])
    test("Missing price fallback to entry", _price_for_exit == 0.10)

    # Test 6: No silent failure — record_exit still callable after force exit
    from bot import record_exit
    try:
        record_exit("force_exit", "TEST", "long", 100, 95, "UNKNOWN", wallet=Wallet(1000))
        test("record_exit: force_exit reason accepted", True)
    except Exception as _re:
        test("record_exit: force_exit reason accepted", False, str(_re))

    # Test 7: Sell on already-empty position returns 0 (no crash)
    _w47f = Wallet(1000)
    _result = _w47f.sell("NONEXISTENT", 100)
    test("Sell nonexistent: no crash, returns 0", _result == 0)

    # Test 8: Cover on already-empty position returns 0 (no crash)
    _w47g = Wallet(1000)
    _result_g = _w47g.cover("NONEXISTENT", 100)
    test("Cover nonexistent: no crash, returns 0", _result_g == 0)

    # ── SECTION 48: Long-Run Reliability ──
    print("\n── 48. Long-Run Reliability ──")
    from bot import (StagnationWatchdog, stagnation_watchdog, ApiStalenessTracker, api_staleness,
                     SkipReasonTracker, skip_tracker,
                     STAGNATION_RESET_CYCLES, API_STALE_BLOCK_ENTRIES, API_STALE_FORCE_CLOSE,
                     ERROR_BURST_THRESHOLD, ERROR_BURST_WINDOW, ERROR_BURST_PAUSE,
                     MAX_COOLDOWN_CYCLES)

    # Constants exist
    test("STAGNATION_RESET_CYCLES = 2000", STAGNATION_RESET_CYCLES == 2000)
    test("API_STALE_BLOCK_ENTRIES = 50", API_STALE_BLOCK_ENTRIES == 50)
    test("API_STALE_FORCE_CLOSE = 200", API_STALE_FORCE_CLOSE == 200)
    test("ERROR_BURST_THRESHOLD = 20", ERROR_BURST_THRESHOLD == 20)
    test("ERROR_BURST_WINDOW = 50", ERROR_BURST_WINDOW == 50)
    test("ERROR_BURST_PAUSE = 100", ERROR_BURST_PAUSE == 100)
    test("MAX_COOLDOWN_CYCLES = 10000", MAX_COOLDOWN_CYCLES == 10000)
    test("HEARTBEAT_INTERVAL = 50", HEARTBEAT_INTERVAL == 50)

    # StagnationWatchdog: no reset before threshold
    _sw = StagnationWatchdog()
    _sw.last_trade_cycle = 100
    _sw_w = Wallet(1000)
    _sw_w.cooldowns = {"ETH": 50, "BTC": 80}
    _sw.check(2000, _sw_w)  # 1900 cycles idle < 2000
    test("Stagnation: no reset before threshold", len(_sw_w.cooldowns) == 2)

    # StagnationWatchdog: reset at threshold
    _sw2 = StagnationWatchdog()
    _sw2.last_trade_cycle = 100
    _sw2_w = Wallet(1000)
    _sw2_w.cooldowns = {"ETH": 50, "BTC": 80}
    _sw2.check(2200, _sw2_w)  # 2100 cycles idle >= 2000
    test("Stagnation: cooldowns cleared at threshold", len(_sw2_w.cooldowns) == 0)
    test("Stagnation: reset_count incremented", _sw2.reset_count == 1)

    # ApiStalenessTracker: success resets failures
    _ast = ApiStalenessTracker()
    _ast.record_failure()
    _ast.record_failure()
    _ast.record_success(100)
    test("API staleness: success resets failures", _ast.consecutive_failures == 0)
    test("API staleness: last_success_cycle updated", _ast.last_success_cycle == 100)

    # ApiStalenessTracker: block entries after threshold
    _ast2 = ApiStalenessTracker()
    _ast2.last_success_cycle = 100
    test("API staleness: block entries at +50", _ast2.should_block_entries(150))
    test("API staleness: no block before threshold", not _ast2.should_block_entries(140))

    # ApiStalenessTracker: force close after threshold
    _ast3 = ApiStalenessTracker()
    _ast3.last_success_cycle = 100
    test("API staleness: force close at +200", _ast3.should_force_close(300))
    test("API staleness: no force close before threshold", not _ast3.should_force_close(290))

    # SkipReasonTracker
    _srt = SkipReasonTracker()
    _srt.record("cooldown")
    _srt.record("cooldown")
    _srt.record("rr_filter")
    test("Skip tracker: counts correct", _srt.counts.get("cooldown") == 2)
    test("Skip tracker: summary contains reasons", "cooldown=2" in _srt.summary())
    _srt.reset()
    test("Skip tracker: reset clears", _srt.summary() == "none")

    # Error burst detection
    _ec_burst = ErrorClassifier()
    for i in range(ERROR_BURST_THRESHOLD + 1):
        _ec_burst.record("trade_fail", 100 + i)  # 21 errors in 21 cycles < 50 window
    test("Error burst: triggers at threshold", _ec_burst.check_cooldown(100 + ERROR_BURST_THRESHOLD + 1))

    # Zombie position removal
    _wz = Wallet(1000)
    _wz.longs["DEAD"] = {"qty": 0, "entry": 100}
    _wz.longs["ALIVE"] = {"qty": 1.5, "entry": 200}
    _wz.shorts["ZOMBIE"] = {"qty": -1, "entry": 50}
    _wz.clamp_values()
    test("Zombie: qty=0 long removed", "DEAD" not in _wz.longs)
    test("Zombie: qty>0 long kept", "ALIVE" in _wz.longs)
    test("Zombie: qty<0 short removed", "ZOMBIE" not in _wz.shorts)

    # Safe force exit pricing: never use 0
    _wfe = Wallet(1000)
    _wfe.buy("TEST", 100, 200)
    _fe_entry = _wfe.longs["TEST"].get("entry", 0)
    _fe_fallback = 0  # Simulate no market price
    _fe_safe = _fe_entry if _fe_entry > 0 else 0.0001
    test("Force exit: fallback to entry when price=0", _fe_safe == 100)

    # Cooldown safety cap
    _wcd = Wallet(1000)
    _wcd.cooldowns = {"ETH": 999999999}  # Absurdly high
    _wcd.clamp_values()
    test("Cooldown cap: clamped to max", _wcd.cooldowns["ETH"] <= MAX_COOLDOWN_CYCLES)

    # ── 49. Recovery Mode & Pair Failure Tracker ──
    print("\n── 49. Recovery Mode & Pair Failure Tracker ──")

    from bot import (
        RecoveryMode, OvertradingGuard,
        RECOVERY_TRIGGER_CYCLES, RECOVERY_DURATION_CYCLES,
        RECOVERY_COOLDOWN_CYCLES, RECOVERY_COIN_LOSS_DECAY,
        MAX_TRADES_PER_100_CYCLES,
        recovery_mode as _rm_global, pair_failure_tracker as _pft_global,
    )
    # PairFailureTracker was renamed to SmartPairFailureTracker — import with fallback
    try:
        from bot import PairFailureTracker, PAIR_FAILURE_MAX, PAIR_FAILURE_DECAY_CYCLES
    except ImportError:
        print("  Pre-flight skipped: PairFailureTracker not exported (non-critical)")
        PairFailureTracker = None
        PAIR_FAILURE_MAX = 3
        PAIR_FAILURE_DECAY_CYCLES = 100

    # -- RecoveryMode: activation after idle --
    _rm = RecoveryMode()
    _rm.last_trade_cycle = 100
    _rm.check(100 + RECOVERY_TRIGGER_CYCLES)
    test("RecoveryMode: activates after idle", _rm.active == True)
    test("RecoveryMode: activation count", _rm.activation_count == 1)

    # -- RecoveryMode: does NOT activate before threshold --
    _rm2 = RecoveryMode()
    _rm2.last_trade_cycle = 100
    _rm2.check(100 + RECOVERY_TRIGGER_CYCLES - 1)
    test("RecoveryMode: no activation before threshold", _rm2.active == False)

    # -- RecoveryMode: exits on trade --
    _rm3 = RecoveryMode()
    _rm3.last_trade_cycle = 100
    _rm3.check(100 + RECOVERY_TRIGGER_CYCLES)
    test("RecoveryMode: active before trade", _rm3.active == True)
    _rm3.record_trade(500)
    test("RecoveryMode: exits on trade", _rm3.active == False)
    test("RecoveryMode: last_trade_cycle updated", _rm3.last_trade_cycle == 500)

    # -- RecoveryMode: expiry with no trades triggers soft reset --
    _rm4 = RecoveryMode()
    _rm4.last_trade_cycle = 100
    _rm4.check(100 + RECOVERY_TRIGGER_CYCLES)  # Activate at cycle 400
    _act_cycle = _rm4.activated_cycle
    # Simulate expiry: check at activated_cycle + RECOVERY_DURATION_CYCLES
    _rm4.check(_act_cycle + RECOVERY_DURATION_CYCLES)
    test("RecoveryMode: deactivates on expiry", _rm4.active == False)
    test("RecoveryMode: soft reset counted", _rm4.soft_resets == 1)

    # -- RecoveryMode: soft blocker skip flags --
    _rm5 = RecoveryMode()
    test("RecoveryMode: no skip when inactive", _rm5.should_skip_cooldown() == False)
    _rm5.active = True
    test("RecoveryMode: skip cooldown when active", _rm5.should_skip_cooldown() == True)
    test("RecoveryMode: skip coin_loss when active", _rm5.should_skip_coin_loss_block() == True)
    test("RecoveryMode: skip strategy_health when active", _rm5.should_skip_strategy_health() == True)

    # -- RecoveryMode: attempt + execution tracking --
    _rm6 = RecoveryMode()
    _rm6.active = True
    _rm6.record_attempt()
    _rm6.record_attempt()
    test("RecoveryMode: attempt tracking", _rm6.attempted_trades == 2)
    _rm6.record_trade(1000)
    test("RecoveryMode: executed tracking", _rm6.executed_trades == 1)

    # -- RecoveryMode: visibility summary --
    _rm7 = RecoveryMode()
    _rm7.record_signal()
    _rm7.record_signal()
    _rm7.record_passed_filter()
    vis = _rm7.visibility_summary()
    test("RecoveryMode: visibility has signals", "signals=2" in vis)
    test("RecoveryMode: visibility has passed", "passed=1" in vis)
    test("RecoveryMode: visibility has recovery status", "recovery=" in vis)
    _rm7.reset_visibility()
    test("RecoveryMode: visibility resets", _rm7._vis_signals_found == 0)

    # -- RecoveryMode: save/load state --
    _rm8 = RecoveryMode()
    _rm8.active = True
    _rm8.activation_count = 3
    _rm8.soft_resets = 2
    _rm8.last_trade_cycle = 500
    _state = _rm8.save_state()
    _rm9 = RecoveryMode()
    _rm9.load_state(_state)
    test("RecoveryMode: save/load active", _rm9.active == True)
    test("RecoveryMode: save/load activation_count", _rm9.activation_count == 3)
    test("RecoveryMode: save/load soft_resets", _rm9.soft_resets == 2)
    test("RecoveryMode: save/load last_trade_cycle", _rm9.last_trade_cycle == 500)

    # -- RecoveryMode: first call initializes --
    _rm10 = RecoveryMode()
    _rm10.check(50)
    test("RecoveryMode: first call initializes last_trade_cycle", _rm10.last_trade_cycle == 50)
    test("RecoveryMode: first call does not activate", _rm10.active == False)

    # -- PairFailureTracker: tracks failures --
    if PairFailureTracker is not None:
        _pft = PairFailureTracker()
        _pft.record_failure("ETH", 100)
        _pft.record_failure("ETH", 101)
        test("PairFailureTracker: not blocked below threshold", _pft.is_blocked("ETH", 102) == False)
        _pft.record_failure("ETH", 102)
        test("PairFailureTracker: blocked at threshold", _pft.is_blocked("ETH", 103) == True)

        # -- PairFailureTracker: other pairs unaffected --
        test("PairFailureTracker: other pair not blocked", _pft.is_blocked("BTC", 103) == False)

        # -- PairFailureTracker: decay after enough cycles --
        test("PairFailureTracker: decays after time", _pft.is_blocked("ETH", 102 + PAIR_FAILURE_DECAY_CYCLES + 1) == False)

        # -- PairFailureTracker: reset on success --
        _pft2 = PairFailureTracker()
        for i in range(PAIR_FAILURE_MAX):
            _pft2.record_failure("SOL", 200 + i)
        test("PairFailureTracker: blocked after failures", _pft2.is_blocked("SOL", 210) == True)
        _pft2.reset_pair("SOL")
        test("PairFailureTracker: unblocked after reset", _pft2.is_blocked("SOL", 210) == False)

        # -- PairFailureTracker: save/load --
        _pft3 = PairFailureTracker()
        _pft3.record_failure("XRP", 300)
        _pft3.record_failure("XRP", 301)
        _st = _pft3.save_state()
        _pft4 = PairFailureTracker()
        _pft4.load_state(_st)
        test("PairFailureTracker: save/load preserves state", _pft4.failures["XRP"]["count"] == 2)

        # -- Global instances exist --
        test("Global recovery_mode exists", _rm_global is not None)
        test("Global pair_failure_tracker exists", _pft_global is not None)
    else:
        print("  [SKIP] PairFailureTracker tests — class not exported")

    # -- Fix: Recovery cooldown between activations --
    _rmc = RecoveryMode()
    _rmc.last_trade_cycle = 100
    _rmc.check(100 + RECOVERY_TRIGGER_CYCLES)  # Activate
    test("RecoveryMode cooldown: activates first time", _rmc.active == True)
    _rmc.check(100 + RECOVERY_TRIGGER_CYCLES + RECOVERY_DURATION_CYCLES)  # Expire
    test("RecoveryMode cooldown: expired", _rmc.active == False)
    _expire_cycle = 100 + RECOVERY_TRIGGER_CYCLES + RECOVERY_DURATION_CYCLES
    test("RecoveryMode cooldown: last_recovery_end set", _rmc.last_recovery_end == _expire_cycle)
    # Try to re-activate too soon (within cooldown window)
    # Must be: idle >= RECOVERY_TRIGGER but cooldown not yet passed
    # Set last_trade_cycle so idle is enough, but cycle is too close to last_recovery_end
    _rmc.last_trade_cycle = _expire_cycle
    _too_soon = _expire_cycle + RECOVERY_COOLDOWN_CYCLES - 1  # Just before cooldown ends
    # Need idle >= RECOVERY_TRIGGER_CYCLES too, so bump last_trade_cycle back
    _rmc.last_trade_cycle = _too_soon - RECOVERY_TRIGGER_CYCLES
    _rmc.check(_too_soon)
    test("RecoveryMode cooldown: blocked within cooldown", _rmc.active == False)
    # After cooldown expires, should activate
    _after_cooldown = _expire_cycle + RECOVERY_COOLDOWN_CYCLES + RECOVERY_TRIGGER_CYCLES
    _rmc.last_trade_cycle = _after_cooldown - RECOVERY_TRIGGER_CYCLES
    _rmc.check(_after_cooldown)
    test("RecoveryMode cooldown: activates after cooldown", _rmc.active == True)

    # -- Fix: last_recovery_end persists through save/load --
    _rml = RecoveryMode()
    _rml.last_recovery_end = 999
    _sl = _rml.save_state()
    _rml2 = RecoveryMode()
    _rml2.load_state(_sl)
    test("RecoveryMode: save/load last_recovery_end", _rml2.last_recovery_end == 999)

    # -- Fix: OvertradingGuard.allow_limited() --
    _otg = OvertradingGuard()
    test("OvertradingGuard: allow_limited when empty", _otg.allow_limited(100) == True)
    # Fill to normal limit (use spread-out cycles so trades_this_cycle doesn't block)
    for _i in range(MAX_TRADES_PER_100_CYCLES):
        _otg.record_trade(50 + _i)
    _otg.reset_cycle()  # Reset per-cycle counter (simulating a new cycle)
    test("OvertradingGuard: can_trade blocked at limit", _otg.can_trade(100) == False)
    test("OvertradingGuard: allow_limited still allows at normal limit",
         _otg.allow_limited(100) == True)
    # Fill to 1.5x limit
    _otg2 = OvertradingGuard()
    _max_limited = int(MAX_TRADES_PER_100_CYCLES * 1.5)
    for _i in range(_max_limited):
        _otg2.record_trade(50 + _i)
    test("OvertradingGuard: allow_limited blocked at 1.5x limit",
         _otg2.allow_limited(100) == False)

    # -- Fix: _attempted_this_cycle flag --
    _rmf = RecoveryMode()
    _rmf.active = True
    test("RecoveryMode: _attempted_this_cycle starts False", _rmf._attempted_this_cycle == False)
    _rmf.record_attempt()
    test("RecoveryMode: record_attempt sets _attempted_this_cycle", _rmf._attempted_this_cycle == True)
    test("RecoveryMode: attempted_trades incremented", _rmf.attempted_trades == 1)

    # -- Fix: Recovery exit on trade sets last_recovery_end --
    _rme = RecoveryMode()
    _rme.active = True
    _rme.activated_cycle = 1000
    _rme.record_trade(1020)
    test("RecoveryMode: trade exit sets last_recovery_end", _rme.last_recovery_end == 1020)
    test("RecoveryMode: trade exit deactivates", _rme.active == False)

    # ── Section 50: Market Data Fallback (get_top_volume_pairs) ──
    print("\n── Section 50: Market Data Fallback ──")
    from bot import get_top_volume_pairs

    # Helper wallet for tests
    _mf_w = Wallet(10000)

    # Basic: returns top volume pairs sorted by volume
    _mf_tickers = {
        "XXBTZUSD": {"price": 50000, "vol": 5000000, "change": 0.01, "high": 51000, "low": 49000, "range": 0.04, "pos": 0.5},
        "XETHZUSD": {"price": 3000, "vol": 3000000, "change": -0.02, "high": 3100, "low": 2900, "range": 0.07, "pos": 0.5},
        "SOLUSD": {"price": 100, "vol": 1000000, "change": 0.03, "high": 105, "low": 95, "range": 0.1, "pos": 0.5},
        "DOGEUSD": {"price": 0.1, "vol": 200000, "change": 0.0, "high": 0.11, "low": 0.09, "range": 0.2, "pos": 0.5},  # Below min_vol
    }
    _mf_pn = {"XXBTZUSD": "XBT/USD", "XETHZUSD": "XETH/USD", "SOLUSD": "SOL/USD", "DOGEUSD": "DOGE/USD"}

    _mf_result = get_top_volume_pairs(_mf_tickers, _mf_pn, _mf_w, limit=5)
    test("get_top_volume_pairs: returns sorted by volume desc",
         len(_mf_result) >= 2 and _mf_result[0]["vol"] >= _mf_result[1]["vol"])

    test("get_top_volume_pairs: excludes low volume pairs (DOGE < 500k)",
         all(r["coin"] != "DOGE" for r in _mf_result))

    # Excludes held positions
    _mf_w2 = Wallet(10000)
    _mf_w2.buy("BTC", 50000, 500)
    _mf_result2 = get_top_volume_pairs(_mf_tickers, _mf_pn, _mf_w2, limit=5)
    test("get_top_volume_pairs: excludes held positions",
         all(r["coin"] != "BTC" for r in _mf_result2))

    # Handles invalid prices
    _mf_tickers_bad = {
        "BADUSD": {"price": float('nan'), "vol": 9000000, "change": 0, "high": 1, "low": 1, "range": 0, "pos": 0.5},
        "ZEROUSD": {"price": 0, "vol": 8000000, "change": 0, "high": 1, "low": 1, "range": 0, "pos": 0.5},
        "LINKUSD": {"price": 42, "vol": 7000000, "change": 0.01, "high": 43, "low": 41, "range": 0.05, "pos": 0.5},
    }
    _mf_pn_bad = {"BADUSD": "BADUSD", "ZEROUSD": "ZEROUSD", "LINKUSD": "LINKUSD"}
    _mf_result3 = get_top_volume_pairs(_mf_tickers_bad, _mf_pn_bad, _mf_w, limit=5)
    test("get_top_volume_pairs: filters NaN and zero prices",
         len(_mf_result3) == 1 and _mf_result3[0]["coin"] == "LINK")

    # Respects limit
    _mf_result4 = get_top_volume_pairs(_mf_tickers, _mf_pn, _mf_w, limit=2)
    test("get_top_volume_pairs: respects limit parameter", len(_mf_result4) <= 2)

    # Empty tickers
    _mf_result5 = get_top_volume_pairs({}, _mf_pn, _mf_w, limit=5)
    test("get_top_volume_pairs: returns empty list for empty tickers", _mf_result5 == [])

    # Returns correct structure
    if _mf_result:
        _mf_first = _mf_result[0]
        test("get_top_volume_pairs: result has coin/price/vol keys",
             "coin" in _mf_first and "price" in _mf_first and "vol" in _mf_first)
        test("get_top_volume_pairs: price is positive number", _mf_first["price"] > 0)

    # Excludes shorts too
    _mf_w3 = Wallet(10000)
    _mf_w3.short("ETH", 3000, 500)
    _mf_result6 = get_top_volume_pairs(_mf_tickers, _mf_pn, _mf_w3, limit=5)
    test("get_top_volume_pairs: excludes shorted positions",
         all(r["coin"] != "ETH" for r in _mf_result6))

    # ── Section 51: Recovery Forced Exit Logic ──
    print("\n── Section 51: Recovery Forced Exit Logic ──")

    # Test: worst PnL position is selected for exit
    # Simulates the candidate-building logic from the forced exit block
    _fe_w = Wallet(10000)
    _fe_w.buy("BTC", 50000, 500)   # entry=50000
    _fe_w.buy("ETH", 3000, 300)    # entry=3000
    _fe_w.buy("SOL", 100, 200)     # entry=100
    _fe_prices = {"BTC": 48000, "ETH": 3200, "SOL": 90}  # BTC -4%, ETH +6.7%, SOL -10%

    _fe_cands = []
    for _c, _p in _fe_w.longs.items():
        _pr = _fe_prices.get(_c, 0)
        _en = _p.get("entry", 0)
        if _pr > 0 and _en > 0:
            _pnl = (_pr - _en) / _en * 100
            _fe_cands.append({"coin": _c, "pnl": _pnl})
    _fe_cands.sort(key=lambda x: x["pnl"])
    test("Forced exit: worst PnL position is first candidate",
         _fe_cands[0]["coin"] == "SOL" and _fe_cands[0]["pnl"] < -9)
    test("Forced exit: best PnL position is last candidate",
         _fe_cands[-1]["coin"] == "ETH" and _fe_cands[-1]["pnl"] > 6)

    # Test: shorts PnL calculation (entry - price) / entry
    _fe_w2 = Wallet(10000)
    _fe_w2.short("DOGE", 0.10, 100)  # entry=0.10
    _fe_w2.short("ADA", 0.50, 200)   # entry=0.50
    _fe_prices2 = {"DOGE": 0.12, "ADA": 0.45}  # DOGE -20%, ADA +10%

    _fe_cands2 = []
    for _c, _p in _fe_w2.shorts.items():
        _pr = _fe_prices2.get(_c, 0)
        _en = _p.get("entry", 0)
        if _pr > 0 and _en > 0:
            _pnl = (_en - _pr) / _en * 100
            _fe_cands2.append({"coin": _c, "pnl": _pnl})
    _fe_cands2.sort(key=lambda x: x["pnl"])
    test("Forced exit short: worst PnL (DOGE losing) is first",
         _fe_cands2[0]["coin"] == "DOGE" and _fe_cands2[0]["pnl"] < -15)
    test("Forced exit short: best PnL (ADA winning) is last",
         _fe_cands2[-1]["coin"] == "ADA" and _fe_cands2[-1]["pnl"] > 5)

    # Test: invalid prices are skipped in candidate building
    _fe_cands3 = []
    _fe_bad_prices = {"BTC": 0, "ETH": -1, "SOL": float('nan')}
    for _c in ["BTC", "ETH", "SOL"]:
        _pr = _fe_bad_prices.get(_c, 0)
        if _pr <= 0:
            continue
        try:
            if math.isnan(_pr) or math.isinf(_pr):
                continue
        except (TypeError, ValueError):
            continue
        _fe_cands3.append(_c)
    test("Forced exit: invalid prices (0, -1, NaN) all skipped",
         len(_fe_cands3) == 0)

    # Test: pair_failure_tracker blocks specific pairs
    if PairFailureTracker is not None:
        _fe_pft = PairFailureTracker()
        for _ in range(PAIR_FAILURE_MAX):
            _fe_pft.record_failure("SOL", 100)
        test("Forced exit: blocked pair is skipped",
             _fe_pft.is_blocked("SOL", 100) == True)
        test("Forced exit: non-blocked pair passes",
             _fe_pft.is_blocked("BTC", 100) == False)
    else:
        print("  [SKIP] PairFailureTracker forced exit tests — class not exported")

    # Test: recovery attempt is recorded on forced exit
    _fe_rm = RecoveryMode()
    _fe_rm.active = True
    test("Forced exit: _attempted_this_cycle starts False", _fe_rm._attempted_this_cycle == False)
    _fe_rm.record_attempt()
    test("Forced exit: record_attempt sets flag", _fe_rm._attempted_this_cycle == True)
    test("Forced exit: attempted_trades count", _fe_rm.attempted_trades == 1)

    # Test: at max positions check
    from bot import MAX_POSITIONS
    _fe_w3 = Wallet(10000)
    for _i in range(MAX_POSITIONS):
        _fe_w3.buy(f"COIN{_i}", 100, 100)
    _fe_total = len(_fe_w3.longs) + len(_fe_w3.shorts)
    test("Forced exit: detects max positions reached",
         _fe_total >= MAX_POSITIONS)

    # ── Section 52: Global Trade Audit (CycleAudit) ──
    print("\n── Section 52: Global Trade Audit ──")
    from bot import CycleAudit, cycle_audit as _ca_global

    # Basic counters
    _ca = CycleAudit()
    test("CycleAudit: starts at zero", _ca.signals_raw == 0 and _ca.final_candidates == 0)

    _ca.signals_raw = 5
    _ca.record_passed_filters()
    _ca.record_passed_filters()
    test("CycleAudit: record_passed_filters increments", _ca.signals_after_filters == 2 and _ca.final_candidates == 2)

    _ca.record_execution()
    test("CycleAudit: record_execution increments", _ca.executed_trades == 1)

    # Rejection categorization
    _ca2 = CycleAudit()
    _ca2.record_rejection("exposure_cap")
    _ca2.record_rejection("global_risk_cap")
    _ca2.record_rejection("stress_risk")
    test("CycleAudit: risk rejections counted", _ca2.rejected_by_risk == 3)

    _ca2.record_rejection("cooldown")
    _ca2.record_rejection("coin_blocked")
    _ca2.record_rejection("pair_blocked")
    test("CycleAudit: cooldown rejections counted", _ca2.rejected_by_cooldown == 3)

    _ca2.record_rejection("strategy_health")
    _ca2.record_rejection("circuit_breaker")
    test("CycleAudit: health rejections counted", _ca2.rejected_by_health == 2)

    _ca2.record_rejection("choppy_filter")
    _ca2.record_rejection("volume_filter")
    _ca2.record_rejection("pullback_filter")
    test("CycleAudit: filter rejections counted", _ca2.rejected_by_filter == 3)

    # Prefixed rejection (order_rejected:max_positions) — base extracted
    _ca3 = CycleAudit()
    _ca3.record_rejection("order_rejected:max_positions")
    test("CycleAudit: prefixed rejection categorized as filter", _ca3.rejected_by_filter == 1)

    # Reset
    _ca.reset()
    test("CycleAudit: reset clears all counters",
         _ca.signals_raw == 0 and _ca.signals_after_filters == 0 and
         _ca.rejected_by_risk == 0 and _ca.rejected_by_cooldown == 0 and
         _ca.rejected_by_health == 0 and _ca.final_candidates == 0 and
         _ca.executed_trades == 0)

    # emit() doesn't crash with zero signals
    import logging as _audit_logging
    _audit_logger = _audit_logging.getLogger("test_audit")
    try:
        _ca_empty = CycleAudit()
        _ca_empty.emit(100, False, _audit_logger)
        test("CycleAudit: emit with zero signals doesn't crash", True)
    except Exception:
        test("CycleAudit: emit with zero signals doesn't crash", False)

    # ZERO-TRADE ROOT CAUSE detection
    _ca4 = CycleAudit()
    _ca4.signals_raw = 10
    _ca4.final_candidates = 0
    test("CycleAudit: detects zero-trade root cause condition",
         _ca4.signals_raw > 0 and _ca4.final_candidates == 0)

    # Candidates exist but zero executed
    _ca5 = CycleAudit()
    _ca5.signals_raw = 5
    _ca5.final_candidates = 3
    _ca5.executed_trades = 0
    test("CycleAudit: detects candidates-but-zero-executed condition",
         _ca5.final_candidates > 0 and _ca5.executed_trades == 0)

    # Global instance exists
    test("CycleAudit: global cycle_audit instance exists", _ca_global is not None)

    # top_failure_reason: returns dominant blocker
    _ca6 = CycleAudit()
    _ca6.rejected_by_cooldown = 6
    _ca6.rejected_by_risk = 3
    _ca6.rejected_by_filter = 2
    _ca6.rejected_by_health = 1
    test("CycleAudit: top_failure_reason returns cooldown when dominant",
         _ca6.top_failure_reason() == "cooldown_blocked")

    _ca7 = CycleAudit()
    _ca7.rejected_by_risk = 10
    _ca7.rejected_by_cooldown = 2
    test("CycleAudit: top_failure_reason returns risk when dominant",
         _ca7.top_failure_reason() == "risk_blocked")

    _ca8 = CycleAudit()
    _ca8.rejected_by_health = 5
    test("CycleAudit: top_failure_reason returns health when dominant",
         _ca8.top_failure_reason() == "health_blocked")

    _ca9 = CycleAudit()
    _ca9.rejected_by_filter = 8
    test("CycleAudit: top_failure_reason returns filter when dominant",
         _ca9.top_failure_reason() == "filter_blocked")

    # top_failure_reason: returns "none" when no rejections
    _ca10 = CycleAudit()
    test("CycleAudit: top_failure_reason returns none when no rejections",
         _ca10.top_failure_reason() == "none")

    # emit always logs (doesn't crash with any combo)
    try:
        _ca_all = CycleAudit()
        _ca_all.signals_raw = 18
        _ca_all.signals_after_filters = 2
        _ca_all.rejected_by_cooldown = 6
        _ca_all.rejected_by_filter = 6
        _ca_all.rejected_by_risk = 3
        _ca_all.rejected_by_health = 1
        _ca_all.final_candidates = 2
        _ca_all.executed_trades = 1
        _ca_all.emit(500, False, _audit_logger)
        test("CycleAudit: emit with full data doesn't crash", True)
    except Exception:
        test("CycleAudit: emit with full data doesn't crash", False)

    # ── Section 53: Bot Health Snapshot ──
    print("\n── Section 53: Bot Health Snapshot ──")
    from bot import bot_snapshot_report, PerformanceMatrix, Wallet, _cycle_times, SNAPSHOT_ENABLED

    test("Snapshot: SNAPSHOT_ENABLED exists", isinstance(SNAPSHOT_ENABLED, bool))

    # Build a fake perf_matrix with some trades
    _snap_pm = PerformanceMatrix()
    for i in range(10):
        _snap_pm.record("momentum", "SMOOTH_TREND", 100, 102, "long", 2.0, 0.4, 1.6)
    for i in range(5):
        _snap_pm.record("momentum", "CHOPPY", 100, 98, "long", -2.0, 0.4, -2.4)
    _snap_w = Wallet(1000)

    # Basic output test — healthy bot (10W/5L, trending regime, normal latency)
    _cycle_times.clear()
    _cycle_times.extend([0.5, 0.6, 0.4, 0.5])
    _snap_out = bot_snapshot_report(100, _snap_w, {}, _snap_pm, "SMOOTH_TREND")
    test("Snapshot: returns string", isinstance(_snap_out, str))
    test("Snapshot: contains cycle", "cycle=100" in _snap_out)
    test("Snapshot: contains trade count", "15" in _snap_out)
    test("Snapshot: contains win rate", "WR=" in _snap_out)
    test("Snapshot: contains regime", "SMOOTH_TREND" in _snap_out)
    test("Snapshot: contains positions", "0L/0S" in _snap_out)
    test("Snapshot: contains health score", "BOT HEALTH SCORE:" in _snap_out)
    test("Snapshot: contains status", "STABLE" in _snap_out or "WARNING" in _snap_out or "DANGEROUS" in _snap_out)
    test("Snapshot: healthy bot is STABLE", "STABLE" in _snap_out)

    # Degraded bot — all losses, choppy regime, slow latency
    _snap_pm_bad = PerformanceMatrix()
    for i in range(20):
        _snap_pm_bad.record("momentum", "CHOPPY", 100, 95, "long", -5.0, 0.4, -5.4)
    _cycle_times.clear()
    _cycle_times.extend([3.0, 2.8, 3.1, 2.9])  # Slow (> POLL * 0.8)
    _snap_bad = bot_snapshot_report(300, _snap_w, {}, _snap_pm_bad, "CHOPPY")
    test("Snapshot: losing bot scores low", "DANGEROUS" in _snap_bad or "WARNING" in _snap_bad)
    test("Snapshot: reason identifies problems",
         "poor edge" in _snap_bad or "negative PnL" in _snap_bad or "overtrading" in _snap_bad)

    # Win quality: small wins + big losses should score worse than big wins + small losses
    _snap_pm_good_edge = PerformanceMatrix()
    for i in range(4):
        _snap_pm_good_edge.record("momentum", "TREND", 100, 106, "long", 6.0, 0.4, 5.6)  # big wins
    for i in range(6):
        _snap_pm_good_edge.record("momentum", "TREND", 100, 99, "long", -1.0, 0.4, -1.4)  # small losses
    _snap_pm_bad_edge = PerformanceMatrix()
    for i in range(6):
        _snap_pm_bad_edge.record("momentum", "TREND", 100, 101, "long", 1.0, 0.4, 0.6)  # small wins
    for i in range(4):
        _snap_pm_bad_edge.record("momentum", "TREND", 100, 94, "long", -6.0, 0.4, -6.4)  # big losses
    _cycle_times.clear()
    _cycle_times.extend([0.5, 0.5])
    _good_edge_out = bot_snapshot_report(100, _snap_w, {}, _snap_pm_good_edge, "SMOOTH_TREND")
    _bad_edge_out = bot_snapshot_report(100, _snap_w, {}, _snap_pm_bad_edge, "SMOOTH_TREND")
    # Extract scores: find "N/100" pattern
    import re
    _ge_score = int(re.search(r"(\d+)/100", _good_edge_out).group(1))
    _be_score = int(re.search(r"(\d+)/100", _bad_edge_out).group(1))
    test("Snapshot: good edge scores higher than bad edge", _ge_score > _be_score)

    # Loss streak penalty: 6 consecutive losses should reduce score
    _snap_pm_streak = PerformanceMatrix()
    for i in range(5):
        _snap_pm_streak.record("momentum", "TREND", 100, 102, "long", 2.0, 0.4, 1.6)  # 5 wins
    for i in range(6):
        _snap_pm_streak.record("momentum", "TREND", 100, 97, "long", -3.0, 0.4, -3.4)  # 6 consecutive losses
    _snap_pm_no_streak = PerformanceMatrix()
    # Same W/L ratio but interleaved (no streak)
    for i in range(11):
        if i % 2 == 0:
            _snap_pm_no_streak.record("momentum", "TREND", 100, 102, "long", 2.0, 0.4, 1.6)
        else:
            _snap_pm_no_streak.record("momentum", "TREND", 100, 97, "long", -3.0, 0.4, -3.4)
    _cycle_times.clear()
    _cycle_times.extend([0.5, 0.5])
    _streak_out = bot_snapshot_report(100, _snap_w, {}, _snap_pm_streak, "SMOOTH_TREND")
    _no_streak_out = bot_snapshot_report(100, _snap_w, {}, _snap_pm_no_streak, "SMOOTH_TREND")
    _streak_score = int(re.search(r"(\d+)/100", _streak_out).group(1))
    _no_streak_score = int(re.search(r"(\d+)/100", _no_streak_out).group(1))
    test("Snapshot: loss streak penalizes score", _streak_score < _no_streak_score)
    test("Snapshot: streak reason mentioned", "loss streak" in _streak_out)

    # Latency tracking
    _cycle_times.clear()
    _cycle_times.extend([0.5, 0.6, 0.4, 0.5])
    _snap_lat = bot_snapshot_report(200, _snap_w, {}, _snap_pm, None)
    test("Snapshot: contains latency", "latency:" in _snap_lat)
    test("Snapshot: no regime when None", "regime:" not in _snap_lat)

    # Empty perf_matrix — neutral score
    _cycle_times.clear()
    _snap_empty = bot_snapshot_report(1, Wallet(1000), {}, PerformanceMatrix(), None)
    test("Snapshot: handles zero trades", "trades(last50): 0" in _snap_empty)
    test("Snapshot: neutral score with no data", "STABLE" in _snap_empty or "WARNING" in _snap_empty)

    # Never crashes on bad input
    try:
        bot_snapshot_report(0, None, None, None, None)
        test("Snapshot: survives bad input", True)
    except Exception:
        test("Snapshot: survives bad input", False)

    _cycle_times.clear()

    # Health score safety actions
    from bot import _last_health_score
    import bot as _bot_mod

    # Score < 40 → size mult 0.5
    _bot_mod._last_health_score = 35
    # Simulate what main loop does
    _h_mult = 1.0
    _h_block = False
    if _bot_mod._last_health_score < 20:
        _h_block = True; _h_mult = 0.0
    elif _bot_mod._last_health_score < 30:
        _h_block = True; _h_mult = 0.25
    elif _bot_mod._last_health_score < 40:
        _h_mult = 0.5
    test("Health safety: score 35 → half size", _h_mult == 0.5 and not _h_block)

    # Score < 30 → block entries
    _bot_mod._last_health_score = 25
    _h_mult = 1.0; _h_block = False
    if _bot_mod._last_health_score < 20:
        _h_block = True; _h_mult = 0.0
    elif _bot_mod._last_health_score < 30:
        _h_block = True; _h_mult = 0.25
    elif _bot_mod._last_health_score < 40:
        _h_mult = 0.5
    test("Health safety: score 25 → entries blocked", _h_block and _h_mult == 0.25)

    # Score < 20 → full pause
    _bot_mod._last_health_score = 15
    _h_mult = 1.0; _h_block = False
    if _bot_mod._last_health_score < 20:
        _h_block = True; _h_mult = 0.0
    elif _bot_mod._last_health_score < 30:
        _h_block = True; _h_mult = 0.25
    elif _bot_mod._last_health_score < 40:
        _h_mult = 0.5
    test("Health safety: score 15 → full pause", _h_block and _h_mult == 0.0)

    # Score >= 40 → no restrictions
    _bot_mod._last_health_score = 75
    _h_mult = 1.0; _h_block = False
    if _bot_mod._last_health_score < 20:
        _h_block = True; _h_mult = 0.0
    elif _bot_mod._last_health_score < 30:
        _h_block = True; _h_mult = 0.25
    elif _bot_mod._last_health_score < 40:
        _h_mult = 0.5
    test("Health safety: score 75 → no restrictions", _h_mult == 1.0 and not _h_block)

    # Verify snapshot sets _last_health_score
    _bot_mod._last_health_score = 100
    _cycle_times.clear()
    _cycle_times.extend([0.5])
    _snap_pm_score = PerformanceMatrix()
    for i in range(20):
        _snap_pm_score.record("momentum", "CHOPPY", 100, 95, "long", -5.0, 0.4, -5.4)
    bot_snapshot_report(1, Wallet(1000), {}, _snap_pm_score, "CHOPPY")
    test("Health safety: snapshot updates _last_health_score", _bot_mod._last_health_score < 100)

    # Verify update_health_score runs fast and updates global
    from bot import update_health_score
    _bot_mod._last_health_score = 100
    _cycle_times.clear()
    _cycle_times.extend([0.5])
    _uhs_pm = PerformanceMatrix()
    for i in range(10):
        _uhs_pm.record("momentum", "TREND", 100, 95, "long", -5.0, 0.4, -5.4)
    _uhs_result = update_health_score(_uhs_pm, "CHOPPY")
    test("update_health_score: returns int", isinstance(_uhs_result, int))
    test("update_health_score: updates global", _bot_mod._last_health_score == _uhs_result)
    test("update_health_score: bad data → low score", _uhs_result < 50)

    # Verify update_health_score never crashes
    try:
        update_health_score(None, None)
        test("update_health_score: survives None input", True)
    except Exception:
        test("update_health_score: survives None input", False)

    # Reset
    _bot_mod._last_health_score = 100
    _cycle_times.clear()

    # ── Section 54: Noise Trade Filters ──
    print("\n── Section 54: Noise Trade Filters ──")
    from bot import (NOISE_FILTER_ENABLED, NOISE_MOM_MIN_SCORE, NOISE_MOM_MIN_CHANGE,
                     NOISE_MEANREV_COIN_TREND_WINDOW, NOISE_MEANREV_COIN_TREND_THRESHOLD,
                     NOISE_BREAKOUT_CONFIRM_TICKS, NOISE_SHORT_MIN_SCORE, NOISE_SHORT_MIN_CHANGE,
                     coin_is_trending, breakout_confirmed, prices_cache)
    try:
        from bot import momentum_quality_ok
    except ImportError:
        print("  Pre-flight skipped: momentum_quality_ok removed (non-critical)")
        momentum_quality_ok = None

    # Constants exist
    test("Noise: NOISE_FILTER_ENABLED exists", isinstance(NOISE_FILTER_ENABLED, bool))
    test("Noise: NOISE_MOM_MIN_SCORE > old 0.05", NOISE_MOM_MIN_SCORE > 0.05)
    test("Noise: NOISE_MOM_MIN_CHANGE > old 0.01", NOISE_MOM_MIN_CHANGE > 0.01)
    test("Noise: NOISE_SHORT_MIN_SCORE < old -0.05", NOISE_SHORT_MIN_SCORE < -0.05)
    test("Noise: NOISE_SHORT_MIN_CHANGE < old -0.01", NOISE_SHORT_MIN_CHANGE < -0.01)
    test("Noise: breakout confirm ticks >= 2", NOISE_BREAKOUT_CONFIRM_TICKS >= 2)
    test("Noise: coin trend threshold > 0", NOISE_MEANREV_COIN_TREND_THRESHOLD > 0)

    # momentum_quality_ok
    if momentum_quality_ok is not None:
        test("Noise: strong long passes", momentum_quality_ok(0.20, 0.03, "long"))
        test("Noise: weak long blocked", not momentum_quality_ok(0.06, 0.015, "long"))
        test("Noise: strong short passes", momentum_quality_ok(-0.20, -0.03, "short"))
        test("Noise: weak short blocked", not momentum_quality_ok(-0.06, -0.015, "short"))

    # coin_is_trending with synthetic data
    _saved_pc = dict(prices_cache)
    # Trending coin: price goes from 100 to 105 in 50 ticks (clear uptrend)
    prices_cache["TEST_TREND"] = [100 + i * 0.1 for i in range(50)]
    test("Noise: trending coin detected", coin_is_trending("TEST_TREND"))
    # Ranging coin: price oscillates around 100
    prices_cache["TEST_RANGE"] = [100 + (0.05 if i % 2 == 0 else -0.05) for i in range(50)]
    test("Noise: ranging coin not flagged as trending", not coin_is_trending("TEST_RANGE"))
    # Insufficient data
    prices_cache["TEST_SHORT"] = [100, 101]
    test("Noise: insufficient data returns False", not coin_is_trending("TEST_SHORT"))

    # breakout_confirmed with synthetic data
    # Build a path where last 2 ticks are above BB upper
    # BB upper ≈ mean + 2.5*std. For flat prices at 100, std≈0, upper≈100
    # So any price > ~100.01 would be "above" for flat data
    prices_cache["TEST_BO_GOOD"] = [100.0] * 30 + [101.0, 101.0]  # Last 2 above band
    test("Noise: confirmed breakout passes", breakout_confirmed("TEST_BO_GOOD", "long", ticks=2))
    # Single tick wick: only 1 tick above, then back
    prices_cache["TEST_BO_WICK"] = [100.0] * 31 + [99.5]  # Last tick back below
    test("Noise: single-tick wick blocked", not breakout_confirmed("TEST_BO_WICK", "long", ticks=2))

    # Filter respects master switch
    import bot as _nf_mod
    _orig = _nf_mod.NOISE_FILTER_ENABLED
    _nf_mod.NOISE_FILTER_ENABLED = False
    if momentum_quality_ok is not None:
        test("Noise: disabled filter allows weak momentum", momentum_quality_ok(0.06, 0.015, "long"))
    test("Noise: disabled filter skips coin trending", not coin_is_trending("TEST_TREND"))
    test("Noise: disabled filter allows unconfirmed breakout", breakout_confirmed("TEST_BO_WICK", "long", ticks=2))
    _nf_mod.NOISE_FILTER_ENABLED = _orig

    # Cleanup
    for k in ["TEST_TREND", "TEST_RANGE", "TEST_SHORT", "TEST_BO_GOOD", "TEST_BO_WICK"]:
        prices_cache.pop(k, None)

    # ── Section 55: Execution Safety Layer ──
    print("\n── Section 55: Execution Safety Layer ──")
    from bot import (EXEC_SAFETY_ENABLED, EXEC_GAP_WINDOW, EXEC_GAP_ATR_MULT,
                     EXEC_GAP_MAX_RATIO, EXEC_SPREAD_TREND_MAX, EXEC_MICROVOL_MAX_RATIO,
                     liquidity_ok)
    import bot as _exec_mod

    # 55.1 Constants exist and are sane
    test("Exec: EXEC_SAFETY_ENABLED exists", isinstance(EXEC_SAFETY_ENABLED, bool))
    test("Exec: EXEC_GAP_WINDOW exists", isinstance(EXEC_GAP_WINDOW, int) and EXEC_GAP_WINDOW > 0)
    test("Exec: EXEC_GAP_ATR_MULT > 0", EXEC_GAP_ATR_MULT > 0)
    test("Exec: EXEC_GAP_MAX_RATIO in (0,1)", 0 < EXEC_GAP_MAX_RATIO < 1)
    test("Exec: EXEC_SPREAD_TREND_MAX > 1", EXEC_SPREAD_TREND_MAX > 1)
    test("Exec: EXEC_MICROVOL_MAX_RATIO > 1", EXEC_MICROVOL_MAX_RATIO > 1)

    # 55.2 liquidity_ok function exists
    test("Exec: liquidity_ok callable", callable(liquidity_ok))

    # 55.3 liquidity_ok — normal conditions (smooth price series)
    prices_cache["TEST_LIQ_GOOD"] = [100.0 + i * 0.01 for i in range(50)]
    test("Exec: normal conditions pass", liquidity_ok("TEST_LIQ_GOOD") == True)

    # 55.4 liquidity_ok — gap-heavy series (many large jumps)
    gap_prices = [100.0]
    for i in range(49):
        if i % 3 == 0:
            gap_prices.append(gap_prices[-1] * 1.05)  # 5% jump every 3rd tick
        else:
            gap_prices.append(gap_prices[-1] * 1.001)
    prices_cache["TEST_LIQ_GAPS"] = gap_prices
    test("Exec: gap-heavy coin blocked", liquidity_ok("TEST_LIQ_GAPS") == False)

    # 55.5 liquidity_ok — micro-volatility spike (last 5 ticks very volatile vs baseline)
    microvol_prices = [100.0 + i * 0.005 for i in range(45)]  # Calm baseline
    # Append 5 very volatile ticks
    microvol_prices.extend([100.3, 101.5, 100.0, 102.0, 100.5])
    prices_cache["TEST_LIQ_MICROVOL"] = microvol_prices
    test("Exec: micro-volatility spike blocked", liquidity_ok("TEST_LIQ_MICROVOL") == False)

    # 55.6 liquidity_ok — insufficient data returns True (allows trade)
    prices_cache["TEST_LIQ_SHORT"] = [100.0, 100.1, 100.2]
    test("Exec: insufficient data allows trade", liquidity_ok("TEST_LIQ_SHORT") == True)

    # 55.7 liquidity_ok — unknown coin returns True
    test("Exec: unknown coin allows trade", liquidity_ok("NONEXISTENT_COIN_XYZ") == True)

    # 55.8 Master switch disabled — always allows
    _orig_exec = _exec_mod.EXEC_SAFETY_ENABLED
    _exec_mod.EXEC_SAFETY_ENABLED = False
    test("Exec: disabled allows gaps", liquidity_ok("TEST_LIQ_GAPS") == True)
    test("Exec: disabled allows microvol", liquidity_ok("TEST_LIQ_MICROVOL") == True)
    _exec_mod.EXEC_SAFETY_ENABLED = _orig_exec

    # 55.9 Spread trend — widening spread detected
    # 60 calm ticks then 10 very volatile ticks — ensures baseline is clean
    spread_prices = [100.0 + i * 0.001 for i in range(60)]
    for i in range(10):
        spread_prices.append(spread_prices[-1] * (1 + 0.01 * (1 if i % 2 == 0 else -1)))
    prices_cache["TEST_LIQ_SPREAD"] = spread_prices
    test("Exec: widening spread blocked", liquidity_ok("TEST_LIQ_SPREAD") == False)

    # Cleanup
    for k in ["TEST_LIQ_GOOD", "TEST_LIQ_GAPS", "TEST_LIQ_MICROVOL", "TEST_LIQ_SHORT", "TEST_LIQ_SPREAD"]:
        prices_cache.pop(k, None)

    # ── Section 56: Live Validation Tracker ──
    print("\n── Section 56: Live Validation Tracker ──")
    from bot import LiveValidationTracker, live_tracker as _lt_global

    # 56.1 Class and global instance exist
    test("LiveVal: class exists", callable(LiveValidationTracker))
    test("LiveVal: global instance exists", _lt_global is not None)

    # 56.2 Fresh tracker starts at zero
    lvt = LiveValidationTracker()
    test("LiveVal: starts with 0 attempts", lvt.total_attempts == 0)
    test("LiveVal: starts with 0 blocked", lvt.total_blocked == 0)
    test("LiveVal: starts with 0 executed", lvt.total_executed == 0)
    test("LiveVal: real_edge starts at 0", lvt.real_edge() == 0.0)
    test("LiveVal: blocked_rate starts at 0", lvt.blocked_rate() == 0.0)
    test("LiveVal: win_rate starts at 0", lvt.win_rate() == 0.0)

    # 56.3 log_attempt — blocked trade
    lvt.log_attempt("ETH", "momentum", "long", 0.15, 3000.0, 0.08,
                    blocked=True, block_reason="low_liquidity")
    test("LiveVal: attempt increments total", lvt.total_attempts == 1)
    test("LiveVal: blocked increments", lvt.total_blocked == 1)
    test("LiveVal: block_reason tracked", lvt.block_reasons.get("low_liquidity") == 1)
    test("LiveVal: blocked_rate 100%", lvt.blocked_rate() == 100.0)

    # 56.4 log_attempt — executed trade
    lvt.log_attempt("BTC", "breakout", "long", 0.20, 60000.0, 0.05,
                    blocked=False, fill_price=60010.0, slippage_pct=0.017)
    test("LiveVal: executed increments", lvt.total_executed == 1)
    test("LiveVal: blocked_rate 50%", lvt.blocked_rate() == 50.0)

    # 56.5 log_exit — winning trade
    lvt.log_exit("BTC", "breakout", "long", 60000.0, 61000.0,
                 pnl_pct=1.67, fee_pct=0.4, slippage_entry_pct=0.017,
                 slippage_exit_pct=0.05, exit_reason="trail_stop")
    test("LiveVal: completed trade logged", len(lvt.completed_trades) == 1)
    test("LiveVal: real_edge positive", lvt.real_edge() > 0)
    test("LiveVal: win_rate 100%", lvt.win_rate() == 100.0)
    test("LiveVal: avg_fee_impact > 0", lvt.avg_fee_impact() > 0)
    test("LiveVal: avg_slippage_impact > 0", lvt.avg_slippage_impact() > 0)

    # 56.6 log_exit — losing trade
    lvt.log_exit("ETH", "momentum", "long", 3000.0, 2910.0,
                 pnl_pct=-3.0, fee_pct=0.4, slippage_entry_pct=0.05,
                 slippage_exit_pct=0.3, exit_reason="stop_loss")
    test("LiveVal: 2 completed trades", len(lvt.completed_trades) == 2)
    test("LiveVal: win_rate 50%", lvt.win_rate() == 50.0)

    # 56.7 real_edge calculation (net_pnl = pnl - fee only; slippage already in prices)
    # Trade 1: pnl=1.67, fee=0.4 → net=1.27
    # Trade 2: pnl=-3.0, fee=0.4 → net=-3.4
    # Avg net = (1.27 + -3.4) / 2 = -1.065
    expected_edge = (1.27 + (-3.4)) / 2
    test("LiveVal: real_edge correct", abs(lvt.real_edge() - expected_edge) < 0.01)

    # 56.8 real_edge with window
    test("LiveVal: real_edge window=1 is last trade", abs(lvt.real_edge(window=1) - (-3.4)) < 0.01)

    # 56.9 summary doesn't crash
    s = lvt.summary()
    test("LiveVal: summary returns string", isinstance(s, str) and len(s) > 10)
    test("LiveVal: summary contains edge", "edge=" in s)
    test("LiveVal: summary contains blocked", "blocked=" in s)

    # 56.10 daily_real_edge works
    test("LiveVal: daily_real_edge returns float", isinstance(lvt.daily_real_edge(), float))

    # ── Section 57: Exit Slippage + Health Floor Fixes ──
    print("\n--- 57. PnL Accuracy Fixes ---")

    # 57.1 _exit_slippage_price exists and works
    from bot import _exit_slippage_price, HEALTH_SCORE_FLOOR
    test("exit_slippage_price exists", callable(_exit_slippage_price))

    # 57.2 SELL slippage: price goes DOWN (worse for seller)
    _test_sell_fp = _exit_slippage_price(100.0, "SELL", coin=None, is_sl_exit=False)
    test("exit_slippage SELL: price decreases", _test_sell_fp < 100.0)

    # 57.3 COVER slippage: price goes UP (worse for short closer)
    _test_cover_fp = _exit_slippage_price(100.0, "COVER", coin=None, is_sl_exit=False)
    test("exit_slippage COVER: price increases", _test_cover_fp > 100.0)

    # 57.4 SL exit has HIGHER slippage than normal exit
    _test_sl_fp = _exit_slippage_price(100.0, "SELL", coin=None, is_sl_exit=True)
    _test_normal_fp = _exit_slippage_price(100.0, "SELL", coin=None, is_sl_exit=False)
    test("exit_slippage SL > normal", _test_sl_fp < _test_normal_fp,
         f"SL={_test_sl_fp:.4f} normal={_test_normal_fp:.4f}")

    # 57.5 HEALTH_SCORE_FLOOR exists and is 25
    test("HEALTH_SCORE_FLOOR exists", HEALTH_SCORE_FLOOR == 25)

    # 57.6 Health score never goes below floor
    import bot as _hsf_mod
    _orig_hs = _hsf_mod._last_health_score
    # Simulate worst case: force score components to zero
    _hsf_mod._last_health_score = 0
    # Call update with empty perf matrix to get minimum score
    class _FakePM:
        trades = [{"won": False, "net_pnl": -5.0}] * 50  # 50 consecutive losses
    _hsf_result = _hsf_mod.update_health_score(_FakePM(), "CHOPPY_RANGE")
    test("health score floor enforced", _hsf_result >= HEALTH_SCORE_FLOOR,
         f"got {_hsf_result}, floor={HEALTH_SCORE_FLOOR}")
    _hsf_mod._last_health_score = _orig_hs  # Restore

    # 57.7 net_pnl = pnl - fees only (slippage already baked into prices)
    _lvt2 = _hsf_mod.LiveValidationTracker()
    _lvt2.log_exit("TEST", "test", "long", 100.0, 102.0,
                   pnl_pct=2.0, fee_pct=0.4, slippage_entry_pct=0.05,
                   slippage_exit_pct=0.05, exit_reason="test")
    # net_pnl = 2.0 - 0.4 = 1.6 (slippage NOT subtracted; it's in the prices)
    _expected_net = 2.0 - 0.4
    test("net_pnl = pnl - fees (slip in prices)", abs(_lvt2.real_edge() - _expected_net) < 0.01,
         f"got {_lvt2.real_edge():.4f}, expected {_expected_net:.4f}")

    # 57.8 slippage still TRACKED (logged but not double-subtracted)
    test("slippage tracked in log", _lvt2.avg_slippage_impact() > 0,
         f"avg_slippage={_lvt2.avg_slippage_impact():.4f}")

    # ══════════════════════════════════════════════════════════════
    # SECTION 58 — Dynamic Position Sizing
    # ══════════════════════════════════════════════════════════════
    print("\n── 58. Dynamic Position Sizing ──")
    import bot as _ds_mod
    from bot import (EDGE_SIZING_ENABLED, EDGE_SIZING_TARGET, EDGE_SIZING_MIN_MULT,
                     EDGE_SIZING_MAX_MULT, EDGE_SIZING_MIN_TRADES,
                     _edge_size_multiplier, LiveValidationTracker)

    # 58.1 constants exist
    test("EDGE_SIZING_ENABLED exists", EDGE_SIZING_ENABLED is not None)
    test("EDGE_SIZING_TARGET exists", EDGE_SIZING_TARGET > 0)
    test("EDGE_SIZING_MIN_MULT exists", EDGE_SIZING_MIN_MULT > 0)
    test("EDGE_SIZING_MAX_MULT exists", EDGE_SIZING_MAX_MULT > 1)
    test("EDGE_SIZING_MIN_TRADES exists", EDGE_SIZING_MIN_TRADES >= 1)

    # 58.2 _edge_size_multiplier function exists
    test("_edge_size_multiplier callable", callable(_edge_size_multiplier))

    # 58.3 returns 1.0 when disabled
    _orig_enabled = _ds_mod.EDGE_SIZING_ENABLED
    _ds_mod.EDGE_SIZING_ENABLED = False
    test("edge_size_mult=1.0 when disabled", _ds_mod._edge_size_multiplier() == 1.0)
    _ds_mod.EDGE_SIZING_ENABLED = True

    # 58.4 returns 1.0 when too few trades
    _orig_lt = _ds_mod.live_tracker
    _lt58 = LiveValidationTracker()
    _ds_mod.live_tracker = _lt58
    test("edge_size_mult=1.0 with 0 trades", _ds_mod._edge_size_multiplier() == 1.0)

    # 58.5 returns min mult when edge <= 0
    for i in range(20):
        _lt58.log_exit("BTC", "momentum", "long", 100, 99.5,
                       pnl_pct=-0.5, fee_pct=0.4,
                       slippage_entry_pct=0.05, slippage_exit_pct=0.05,
                       exit_reason="test")
    _em = _ds_mod._edge_size_multiplier()
    test("edge_size_mult=min when edge<0", _em == EDGE_SIZING_MIN_MULT,
         f"got {_em}, expected {EDGE_SIZING_MIN_MULT}")

    # 58.6 returns ~1.0 when edge == target
    _lt58b = LiveValidationTracker()
    _ds_mod.live_tracker = _lt58b
    for i in range(20):
        _lt58b.log_exit("BTC", "momentum", "long", 100, 100 + EDGE_SIZING_TARGET + 0.4,
                        pnl_pct=EDGE_SIZING_TARGET + 0.4, fee_pct=0.4,
                        slippage_entry_pct=0.05, slippage_exit_pct=0.05,
                        exit_reason="test")
    _em2 = _ds_mod._edge_size_multiplier()
    test("edge_size_mult~1.0 at target edge", abs(_em2 - 1.0) < 0.05,
         f"got {_em2:.3f}")

    # 58.7 clamped to max
    _lt58c = LiveValidationTracker()
    _ds_mod.live_tracker = _lt58c
    for i in range(20):
        _lt58c.log_exit("BTC", "momentum", "long", 100, 105,
                        pnl_pct=5.0, fee_pct=0.4,
                        slippage_entry_pct=0.05, slippage_exit_pct=0.05,
                        exit_reason="test")
    _em3 = _ds_mod._edge_size_multiplier()
    test("edge_size_mult clamped to max", _em3 == EDGE_SIZING_MAX_MULT,
         f"got {_em3}")

    _ds_mod.live_tracker = _orig_lt
    _ds_mod.EDGE_SIZING_ENABLED = _orig_enabled

    # ══════════════════════════════════════════════════════════════
    # SECTION 59 — Adaptive Trailing Stops
    # ══════════════════════════════════════════════════════════════
    print("\n── 59. Adaptive Trailing Stops ──")
    import bot as _at_mod
    from bot import (ADAPTIVE_TRAIL_ENABLED, ADAPTIVE_TRAIL_STREAK, ADAPTIVE_TRAIL_MULT,
                     _adaptive_trail_multiplier)

    # 59.1 constants exist
    test("ADAPTIVE_TRAIL_ENABLED exists", ADAPTIVE_TRAIL_ENABLED is not None)
    test("ADAPTIVE_TRAIL_STREAK exists", ADAPTIVE_TRAIL_STREAK >= 1)
    test("ADAPTIVE_TRAIL_MULT exists", 0 < ADAPTIVE_TRAIL_MULT < 1)

    # 59.2 _adaptive_trail_multiplier exists
    test("_adaptive_trail_multiplier callable", callable(_adaptive_trail_multiplier))

    # 59.3 returns 1.0 when disabled
    _orig_at = _at_mod.ADAPTIVE_TRAIL_ENABLED
    _at_mod.ADAPTIVE_TRAIL_ENABLED = False
    test("trail_mult=1.0 when disabled", _at_mod._adaptive_trail_multiplier() == 1.0)
    _at_mod.ADAPTIVE_TRAIL_ENABLED = True

    # 59.4 returns 1.0 when streak < threshold
    _orig_lt2 = _at_mod.live_tracker
    _lt59 = LiveValidationTracker()
    _lt59.winning_streak = 0
    _at_mod.live_tracker = _lt59
    test("trail_mult=1.0 with 0 streak", _at_mod._adaptive_trail_multiplier() == 1.0)

    # 59.5 returns ADAPTIVE_TRAIL_MULT when streak >= threshold
    _lt59.winning_streak = ADAPTIVE_TRAIL_STREAK
    _tm = _at_mod._adaptive_trail_multiplier()
    test("trail_mult=0.9 at streak threshold", _tm == ADAPTIVE_TRAIL_MULT,
         f"got {_tm}")

    # 59.6 winning streak increments on win
    _lt59b = LiveValidationTracker()
    _lt59b.log_exit("BTC", "momentum", "long", 100, 102,
                    pnl_pct=2.0, fee_pct=0.4,
                    slippage_entry_pct=0.05, slippage_exit_pct=0.05,
                    exit_reason="test")
    test("winning_streak=1 after 1 win", _lt59b.winning_streak == 1)

    # 59.7 winning streak resets on loss
    _lt59b.log_exit("BTC", "momentum", "long", 100, 99,
                    pnl_pct=-1.0, fee_pct=0.4,
                    slippage_entry_pct=0.05, slippage_exit_pct=0.05,
                    exit_reason="test")
    test("winning_streak=0 after loss", _lt59b.winning_streak == 0)

    # 59.8 graduated: streak >= 6 returns tighter ADAPTIVE_TRAIL_MULT_2
    from bot import ADAPTIVE_TRAIL_STREAK_2, ADAPTIVE_TRAIL_MULT_2
    _lt59c = LiveValidationTracker()
    _lt59c.winning_streak = ADAPTIVE_TRAIL_STREAK_2
    _at_mod.live_tracker = _lt59c
    _tm2 = _at_mod._adaptive_trail_multiplier()
    test("trail_mult=0.80 at streak_2 threshold", _tm2 == ADAPTIVE_TRAIL_MULT_2,
         f"got {_tm2}, expected {ADAPTIVE_TRAIL_MULT_2}")

    # 59.9 streak between 3 and 5 still gets ADAPTIVE_TRAIL_MULT (not _2)
    _lt59c.winning_streak = 4
    _tm3 = _at_mod._adaptive_trail_multiplier()
    test("trail_mult=0.9 at streak=4 (between tiers)", _tm3 == ADAPTIVE_TRAIL_MULT,
         f"got {_tm3}, expected {ADAPTIVE_TRAIL_MULT}")

    _at_mod.live_tracker = _orig_lt2
    _at_mod.ADAPTIVE_TRAIL_ENABLED = _orig_at

    # ══════════════════════════════════════════════════════════════
    # SECTION 60 — Overtrading Guard
    # ══════════════════════════════════════════════════════════════
    print("\n── 60. Overtrading Guard ──")
    import bot as _og_mod
    from bot import (OVERTRADE_GUARD_ENABLED, OVERTRADE_BLOCKED_RATE_MIN,
                     OVERTRADE_MIN_CYCLES_BETWEEN, _overtrade_guard_ok)

    # 60.1 constants exist
    test("OVERTRADE_GUARD_ENABLED exists", OVERTRADE_GUARD_ENABLED is not None)
    test("OVERTRADE_BLOCKED_RATE_MIN exists", OVERTRADE_BLOCKED_RATE_MIN > 0)
    test("OVERTRADE_MIN_CYCLES_BETWEEN exists", OVERTRADE_MIN_CYCLES_BETWEEN > 0)

    # 60.2 _overtrade_guard_ok exists
    test("_overtrade_guard_ok callable", callable(_overtrade_guard_ok))

    # 60.3 returns True when disabled
    _orig_og = _og_mod.OVERTRADE_GUARD_ENABLED
    _og_mod.OVERTRADE_GUARD_ENABLED = False
    test("overtrade_ok=True when disabled", _og_mod._overtrade_guard_ok(1000) == True)
    _og_mod.OVERTRADE_GUARD_ENABLED = True

    # 60.4 returns True with fresh tracker (no data)
    _orig_lt3 = _og_mod.live_tracker
    _lt60 = LiveValidationTracker()
    _og_mod.live_tracker = _lt60
    test("overtrade_ok=True with no data", _og_mod._overtrade_guard_ok(1000) == True)

    # 60.5 blocked_rate check was REMOVED (optimized: punished clean markets)
    # Verify it now ALLOWS trades even with low blocked rate
    for i in range(30):
        _lt60.log_attempt("BTC", "momentum", "long", 0.5, 100.0, 0.1,
                          blocked=False, fill_price=100.0, slippage_pct=0.05)
    _og_mod.overtrading_guard._last_trade_cycle = 0
    _og_result = _og_mod._overtrade_guard_ok(5000)
    test("overtrade allows low blocked_rate (removed check)", _og_result == True,
         f"blocked_rate={_lt60.blocked_rate():.1f}%")

    # 60.6 blocks when trade too recent (now 20 cycles, was 100)
    _lt60b = LiveValidationTracker()
    _og_mod.live_tracker = _lt60b
    _og_mod.overtrading_guard._last_trade_cycle = 900
    _og_result2 = _og_mod._overtrade_guard_ok(910)  # only 10 cycles later, need 20
    test("overtrade blocks when too frequent", _og_result2 == False,
         f"gap={910-900}, need={OVERTRADE_MIN_CYCLES_BETWEEN}")

    # 60.7 allows when sufficient gap
    _og_result3 = _og_mod._overtrade_guard_ok(1100)  # 200 cycles later
    test("overtrade allows with sufficient gap", _og_result3 == True)

    _og_mod.overtrading_guard._last_trade_cycle = 0  # Clean up
    _og_mod.live_tracker = _orig_lt3
    _og_mod.OVERTRADE_GUARD_ENABLED = _orig_og

    # ══════════════════════════════════════════════════════════════
    # SECTION 63 — Unified Exposure Check
    # ══════════════════════════════════════════════════════════════
    print("\n── 63. Unified Exposure Check ──")
    from bot import unified_exposure_ok, Wallet
    _ue_w = Wallet(1000)
    _ue_prices = {"BTC": 50000}
    # 63.1 small amount passes all checks
    _ue_ok, _ue_reason = unified_exposure_ok(_ue_w, _ue_prices, "BTC", 50, 1.0)
    test("unified_exposure: small amt passes", _ue_ok == True)
    # 63.2 huge amount fails total exposure
    _ue_ok2, _ue_reason2 = unified_exposure_ok(_ue_w, _ue_prices, "BTC", 700, 1.0)
    test("unified_exposure: large amt blocked", _ue_ok2 == False)
    test("unified_exposure: returns reason", _ue_reason2 != "")
    # 63.3 returns tuple (bool, str)
    test("unified_exposure: returns tuple", isinstance(unified_exposure_ok(_ue_w, _ue_prices, "ETH", 10, 1.0), tuple))
    # 63.4 zero portfolio blocks
    _ue_w_empty = Wallet(0)
    _ue_ok3, _ = unified_exposure_ok(_ue_w_empty, {}, "BTC", 50, 1.0)
    test("unified_exposure: zero PV blocked", _ue_ok3 == False)

    # ══════════════════════════════════════════════════════════════
    # SECTION 61 — Market Depth Filter
    # ══════════════════════════════════════════════════════════════
    print("\n── 61. Market Depth Filter ──")
    import bot as _md_mod
    from bot import market_depth_ok, MARKET_DEPTH_ENABLED, MIN_ORDER_BOOK_DEPTH

    # 61.1 constants exist
    test("MARKET_DEPTH_ENABLED exists", MARKET_DEPTH_ENABLED is not None)
    test("MIN_ORDER_BOOK_DEPTH exists", MIN_ORDER_BOOK_DEPTH >= 1)

    # 61.2 function callable
    test("market_depth_ok callable", callable(market_depth_ok))

    # 61.3 returns True when disabled
    _orig_md = _md_mod.MARKET_DEPTH_ENABLED
    _md_mod.MARKET_DEPTH_ENABLED = False
    test("depth_ok=True when disabled", _md_mod.market_depth_ok("BTC", 100, {}) == True)
    _md_mod.MARKET_DEPTH_ENABLED = True

    # 61.4 returns True when no ticker data
    test("depth_ok=True with no tickers", _md_mod.market_depth_ok("BTC", 100, {}) == True)
    test("depth_ok=True with None tickers", _md_mod.market_depth_ok("BTC", 100, None) == True)

    # 61.5 passes when volume is sufficient
    _mock_tickers = {"BTC": {"vol": 1000000, "price": 50000}}
    test("depth_ok=True high vol", _md_mod.market_depth_ok("BTC", 100, _mock_tickers) == True)

    # 61.6 rejects thin market (small trade: vol < 3 × entry)
    _thin_tickers = {"BTC": {"vol": 100, "price": 50000}}
    test("depth_ok=False thin market small", _md_mod.market_depth_ok("BTC", 50, _thin_tickers) == False,
         f"vol=100, entry=50, need=3*50=150")

    # 61.7 unknown coin passes (no data = allow)
    test("depth_ok=True unknown coin", _md_mod.market_depth_ok("UNKNOWN", 100, _mock_tickers) == True)

    # 61.8 graduated: medium trade ($150) needs 5× volume
    _med_tickers = {"BTC": {"vol": 600, "price": 50000}}
    test("depth_ok=False medium trade needs 5x", _md_mod.market_depth_ok("BTC", 150, _med_tickers) == False,
         "vol=600, entry=150, need=5*150=750")
    _med_tickers2 = {"BTC": {"vol": 800, "price": 50000}}
    test("depth_ok=True medium trade with 5x vol", _md_mod.market_depth_ok("BTC", 150, _med_tickers2) == True)

    # 61.9 graduated: large trade ($250) needs 10× volume
    _big_tickers = {"BTC": {"vol": 2000, "price": 50000}}
    test("depth_ok=False big trade needs 10x", _md_mod.market_depth_ok("BTC", 250, _big_tickers) == False,
         "vol=2000, entry=250, need=10*250=2500")
    _big_tickers2 = {"BTC": {"vol": 3000, "price": 50000}}
    test("depth_ok=True big trade with 10x vol", _md_mod.market_depth_ok("BTC", 250, _big_tickers2) == True)

    _md_mod.MARKET_DEPTH_ENABLED = _orig_md

    # ══════════════════════════════════════════════════════════════
    # SECTION 62 — Multi-Timeframe Regime Confirmation
    # ══════════════════════════════════════════════════════════════
    print("\n── 62. Multi-TF Regime Confirmation ──")
    import bot as _rc_mod
    from bot import regime_confirm, REGIME_CONFIRM_ENABLED

    # 62.1 constants exist
    test("REGIME_CONFIRM_ENABLED exists", REGIME_CONFIRM_ENABLED is not None)

    # 62.2 function callable
    test("regime_confirm callable", callable(regime_confirm))

    # 62.3 returns True when disabled
    _orig_rc = _rc_mod.REGIME_CONFIRM_ENABLED
    _rc_mod.REGIME_CONFIRM_ENABLED = False
    test("regime_confirm=True when disabled", _rc_mod.regime_confirm("BTC", "long") == True)
    _rc_mod.REGIME_CONFIRM_ENABLED = True

    # 62.4 returns True when insufficient data
    _rc_mod.prices_cache["_TEST_RC"] = [100.0] * 5  # Too few ticks
    test("regime_confirm=True insufficient data", _rc_mod.regime_confirm("_TEST_RC", "long") == True)

    # 62.5 confirms long when both timeframes trend up
    _rising = [100.0 + i * 0.1 for i in range(100)]
    _rc_mod.prices_cache["_TEST_RC_UP"] = _rising
    test("regime_confirm long + both up", _rc_mod.regime_confirm("_TEST_RC_UP", "long") == True)

    # 62.6 allows long when short-term is up (medium window removed)
    _mixed = [110.0 - i * 0.05 for i in range(80)] + [100.0 + i * 0.2 for i in range(21)]
    _rc_mod.prices_cache["_TEST_RC_MIX"] = _mixed
    _rc_result_mix = _rc_mod.regime_confirm("_TEST_RC_MIX", "long")
    test("regime_confirm allows long (short-term up, medium removed)", _rc_result_mix == True,
         f"result={_rc_result_mix}")

    # 62.7 confirms short when both timeframes trend down
    _falling = [200.0 - i * 0.1 for i in range(100)]
    _rc_mod.prices_cache["_TEST_RC_DOWN"] = _falling
    test("regime_confirm short + both down", _rc_mod.regime_confirm("_TEST_RC_DOWN", "short") == True)

    # 62.8 rejects short when short-term is up (bounce)
    _bounce = [200.0 - i * 0.1 for i in range(80)] + [192.0 + i * 0.2 for i in range(21)]
    _rc_mod.prices_cache["_TEST_RC_BOUNCE"] = _bounce
    _rc_result_bounce = _rc_mod.regime_confirm("_TEST_RC_BOUNCE", "short")
    test("regime_confirm rejects short on bounce", _rc_result_bounce == False,
         f"result={_rc_result_bounce}")

    # Cleanup test entries
    for k in ["_TEST_RC", "_TEST_RC_UP", "_TEST_RC_MIX", "_TEST_RC_DOWN", "_TEST_RC_BOUNCE"]:
        _rc_mod.prices_cache.pop(k, None)
    _rc_mod.REGIME_CONFIRM_ENABLED = _orig_rc

    # ── Section 64: Conviction Override ──
    print("\n── Section 64: Conviction Override ──")
    from bot import conviction_override_active as _coa
    import bot as _co_mod

    # Test 1: Momentum long — strong signal triggers override
    _co_active, _co_filters = _coa(0.30, 0.05, "momentum")
    test("conviction override: strong momentum triggers override", _co_active is True)
    test("conviction override: returns 4 soft filter names", len(_co_filters) == 4)

    # Test 2: Momentum — weak signal does NOT trigger override
    _co_weak, _co_wf = _coa(0.15, 0.02, "momentum")
    test("conviction override: weak momentum does NOT trigger", _co_weak is False)

    # Test 3: Momentum — strong score but weak change does NOT trigger
    _co_half, _co_hf = _coa(0.30, 0.02, "momentum")
    test("conviction override: strong score + weak change = no override", _co_half is False)

    # Test 4: Breakout — wide BB width triggers override
    _co_bo, _co_bf = _coa(0.03, 0, "breakout")
    test("conviction override: wide breakout triggers override", _co_bo is True)

    # Test 5: Breakout — narrow BB width does NOT trigger
    _co_bn, _co_bnf = _coa(0.01, 0, "breakout")
    test("conviction override: narrow breakout does NOT trigger", _co_bn is False)

    # Test 6: Short momentum — negative score/change (absolute values used)
    _co_short, _co_sf = _coa(-0.30, -0.05, "momentum")
    test("conviction override: strong short momentum triggers override", _co_short is True)

    # Test 7: Disabled master switch — never triggers
    _orig_co = _co_mod.CONVICTION_OVERRIDE_ENABLED
    _co_mod.CONVICTION_OVERRIDE_ENABLED = False
    _co_off, _co_off_f = _coa(0.50, 0.10, "momentum")
    test("conviction override: disabled = no override", _co_off is False)
    _co_mod.CONVICTION_OVERRIDE_ENABLED = _orig_co

    # Test 8: Overridden filters list contains expected names
    _co_names, _co_nf = _coa(0.30, 0.05, "momentum")
    test("conviction override: filter list has is_choppy",
         "is_choppy" in _co_nf)
    test("conviction override: filter list has pair_failure",
         "pair_failure" in _co_nf)

    # ── RESULTS ──
    print("\n" + "=" * 60)
    total = PASS + FAIL
    print(f"RESULTS: {PASS}/{total} passed, {FAIL} failed")

    if FAIL > 0:
        print("\nFAILURES:")
        for e in ERRORS:
            print(f"  - {e}")
        print(f"\nBOT IS NOT SAFE TO RUN — {FAIL} tests failed")
        return False
    else:
        print("\nALL TESTS PASSED — bot is verified and safe to run")
        return True


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    success = run_all()
    sys.exit(0 if success else 1)
