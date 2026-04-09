# HYBRID: DeepDenise Webhook + Edison Hedge-Mode Dual Leg (MAIN + INSURANCE)
# PRODUCTION READY v3.1 - FINAL FIXED
# - Dynamic 50/50 capital split based on real balance
# - All guards DISABLED (weekly drawdown, consecutive losses, news guard optional)
# - Insurance leg: NO trailing stop, fixed 0.9R TP / 1R SL
# - Monitor trade: pure detection only (no price management)
# - Removed dead code (RSI, SMA, candle state, etc.)
# - Clean separation of MAIN and INSURANCE logic
# - Webhook: multi-strategy JSON + UID security
# - Fixed missing _check_slippage, insurance SL/TP assignment, Telegram ordering

import argparse
import logging
import time
import hmac
import hashlib
import requests
import os
import signal
import sys
import csv
import threading
import traceback
from decimal import Decimal, ROUND_DOWN, ROUND_UP, ROUND_HALF_EVEN
from datetime import datetime, timezone, timedelta
import schedule
from urllib.parse import urlencode
from typing import Optional, Tuple, Dict, Any, List
import atexit
import websocket
import json
import queue
import socket
import platform
from flask import Flask, request, jsonify
import io
import pickle
import psutil
import gc

# Fix Windows console encoding
if sys.platform == "win32":
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

# ------------------- WEBHOOK SETUP -------------------
app = Flask(__name__)
from werkzeug.middleware.proxy_fix import ProxyFix
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=1)
my_uid = "6e8769164ae8eedf74dcaaeb86000f8e03d166bf5181f8eb283a4bb90e6574a2"

# Global args for webhook access
CMD_ARGS = None

# ------------------- CONFIGURATION -------------------
RISK_PCT = Decimal("0.0378")  # 3.78% per trade (MAIN LEG)
SL_PCT = Decimal("0.0075")    # 0.75%
TP_MULT = Decimal("9")        # MAIN LEG TP multiplier
TRAIL_TRIGGER_MULT = Decimal("1.25")
TRAIL_DISTANCE_MULT = Decimal("2")  # 2R trailing distance
ORDER_FILL_TIMEOUT = 90
POSITION_CHECK_INTERVAL = 30
TRAIL_PRICE_BUFFER = Decimal("0.003")
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RECOVERY_CHECK_INTERVAL = 10
POLLING_INTERVAL = 3

# ==================== INSURANCE / HEDGE MODE CONFIGURATION ====================
INSURANCE_ENABLED = True            # Master switch for insurance leg
INSURANCE_DELAY_MS = 1500           # Delay before opening insurance leg (ms)
SAFETY_FACTOR = Decimal("0.90")     # 90% safety factor

# Dynamic split: 50% of actual balance for MAIN, 50% for INSURANCE
# Calculated at entry time from fetch_balance()
MARGIN_USAGE_PCT = Decimal("0.83")  # Use 83% of virtual capital for margin

# Insurance leg fixed parameters (NO TRAILING)
INSURANCE_SL_MULT = Decimal("1.0")   # 1R SL (same as MAIN)
INSURANCE_TP_MULT = Decimal("0.9")   # 0.9R TP (takes profit faster)
# ========================================================================

# === ALL GUARDS DISABLED ===
ENABLE_WEEKLY_SCALING = False
USE_CONSEC_LOSS_GUARD = False
MAX_CONSEC_LOSSES = 999  # Effectively disabled
NEWS_GUARD_ENABLED = False  # Can be enabled via --news-guard flag if needed

# === CONFIG: BLACKOUT WINDOWS (UTC) - DISABLED BY DEFAULT ===
NEWS_BLACKOUT_WINDOWS = []

# === CONFIG: LIVE API (for optional news guard) ===
LIVE_APIS = [
    "https://nfs.faireconomy.media/ff_calendar_thisweek.json",
    "https://ec.forexprostools.com/?columns=exc_currency,exc_type&timezone=utc"
]
LOCAL_CALENDAR = "high_impact_calendar.json"
LOCAL_OVERRIDE = "news_calendar_override.json"
CACHE_DURATION = 300
HIGH_IMPACT_KEYWORDS = {
    "NFP", "NONFARM", "CPI", "FOMC", "GDP", "UNEMPLOYMENT", "RATE DECISION",
    "PCE", "CORE", "ISM", "JOLTS", "OPEC", "SNB", "BOJ", "GEOPOLITICAL",
    "RETAIL SALES", "ADP", "FLASH", "PRELIMINARY"
}
BUFFER_MINUTES = 5

MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")
LOCK_FILE = os.path.join(os.getenv('TEMP', '/tmp'), 'deepdenise_webhookhedge_bot.lock')
BASE_RISK_PCT = Decimal("0.0378")  # 3.78% when drawdown = 0%
MAX_LEVERAGE = Decimal("5")        # MAIN LEG leverage

# ------------------- FLASK SERVER MANAGEMENT -------------------
class FlaskServer:
    def __init__(self):
        self.thread = None
        self.running = False
        self.port = None
        self.server = None

    def start(self, port):
        self.port = port
        self.running = True
        self.thread = threading.Thread(
            target=self._run_flask,
            args=(port,),
            daemon=False
        )
        self.thread.start()
        log(f"🌐 Flask server starting on port {port}")
        time.sleep(3)
        try:
            requests.get(f"http://localhost:{port}/health", timeout=2)
        except:
            import socket
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            result = sock.connect_ex(('localhost', port))
            if result == 0:
                log(f"✅ Port {port} is now in use - server running")
            sock.close()

    def _run_flask(self, port):
        try:
            from werkzeug.serving import make_server
            self.server = make_server('0.0.0.0', port, app, threaded=True)
            self.server.serve_forever()
        except Exception as e:
            log(f"❌ Flask server error: {e}")

    def stop(self):
        self.running = False
        log("🌐 Stopping Flask server...")
        try:
            requests.post(f"http://localhost:{self.port}/shutdown", timeout=2)
            time.sleep(2)
        except:
            pass
        if self.server:
            try:
                self.server.shutdown()
                time.sleep(1)
            except:
                pass
        log(f"🌐 Flask server stopped on port {self.port}")

flask_server = FlaskServer()

@app.route('/health-hedge', methods=['GET'])
def health():
    return jsonify({"status": "ok", "pid": os.getpid()}), 200

@app.route('/shutdown', methods=['POST'])
def shutdown():
    func = request.environ.get('werkzeug.server.shutdown')
    if func is None:
        raise RuntimeError('Not running with the Werkzeug Server')
    func()
    return 'Server shutting down...'

# ------------------- BOT STATE CLASS -------------------
class BotState:
    """Bundle all global state variables into a single class for better organization."""
    def __init__(self):
        # Core bot state
        self.STOP_REQUESTED = False
        self.client = None
        self.symbol_filters_cache: Dict[str, Dict[str, Decimal]] = {}
        self._position_closure_in_progress = False

        # PNL logging
        self.PNL_LOG_FILE = 'pnl_log.csv'
        self.pnl_data: List[Dict[str, Any]] = []
        self.last_trade_date: Optional[datetime] = None

        # Thread-safe state
        self._stop_lock = threading.Lock()
        self._orders_cancelled = False
        self._trade_lock = threading.Lock()

        # WebSocket state
        self._ws_failed = False
        self._polling_active = False
        self._price_queue = queue.Queue()

        # News guard state (disabled by default but kept for optional use)
        self._news_lock = threading.Lock()
        self._news_cache: List[Dict[str, Any]] = []
        self._cache_ts = Decimal("0.0")
        self.NEWS_LOCK = False
        self.VOLATILITY_ABORT = False
        self.last_news_guard_msg: Optional[str] = None
        self.news_guard_was_active: bool = False
        self._last_news_block_reason: Optional[str] = None

        # Risk management (disabled)
        self.weekly_peak_equity: Optional[Decimal] = None
        self.weekly_start_time: Optional[datetime] = None
        self.CONSEC_LOSSES = 0
        self.weekly_dd_alert_triggered = False

        # Trading state - DUAL LEG STATE
        self.current_trade: Optional['TradeState'] = None   # MAIN leg
        self.insurance_trade: Optional['TradeState'] = None # INSURANCE leg
        self.INSURANCE_ACTIVE = False

        self.is_testnet = True
        self.consec_loss_guard_alert_sent = False
        self.account_size: Optional[Decimal] = None
        self.daily_start_equity: Optional[Decimal] = None
        self._last_symbol_setup: Optional[str] = None
        self._active_websockets: Dict[str, Any] = {}
        self.RESTART_REQUESTED = False
        self._restart_lock = threading.Lock()
        self.start_time = datetime.now(timezone.utc)

bot_state = BotState()

# ------------------- TRADE STATE WITH DECIMAL -------------------
class TradeState:
    def __init__(self):
        self.active = False
        self.leg_type = "MAIN"  # "MAIN" or "INSURANCE"
        self.entry_price: Optional[Decimal] = None
        self.qty: Optional[Decimal] = None
        self.side: Optional[str] = None
        self.entry_close_time: Optional[int] = None
        self.initial_sl: Optional[Decimal] = None
        self.sl: Optional[Decimal] = None
        self.tp: Optional[Decimal] = None
        self.trail_activation_price: Optional[Decimal] = None
        self.current_trail_stop: Optional[Decimal] = None
        self.trail_activated = False
        self.last_trail_alert = Decimal("0.0")
        self.risk: Optional[Decimal] = None
        self.sl_order_id = None
        self.tp_order_id = None
        self.trail_order_id = None
        self.sl_algo_id = None
        self.tp_algo_id = None
        self.trail_algo_id = None

# ------------------- SINGLE INSTANCE LOCK -------------------
def acquire_lock():
    """Acquire single instance lock with PID check to prevent stale locks."""
    global LOCK_HANDLE

    try:
        if os.path.exists(LOCK_FILE):
            try:
                with open(LOCK_FILE, 'r') as f:
                    pid_str = f.read().strip()
                    if pid_str and pid_str.isdigit():
                        pid = int(pid_str)
                        if pid == os.getpid():
                            print(f"Same PID {pid} - this is a restart, continuing...")
                        else:
                            process_exists = False
                            if platform.system() == "Windows":
                                try:
                                    psutil.Process(pid)
                                    process_exists = True
                                except (psutil.NoSuchProcess, psutil.AccessDenied):
                                    process_exists = False
                            else:
                                try:
                                    os.kill(pid, 0)
                                    process_exists = True
                                except OSError:
                                    process_exists = False

                            if process_exists:
                                print(f"Another instance is already running with PID {pid}! Exiting.")
                                sys.exit(1)
                            else:
                                print(f"Removing stale lock file from PID {pid}")
                                os.unlink(LOCK_FILE)
            except Exception as e:
                print(f"Error reading lock file: {e}")
                try:
                    os.unlink(LOCK_FILE)
                except:
                    pass

        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
            f.flush()
            os.fsync(f.fileno())

        print(f"Lock file created with PID {os.getpid()}")

        if platform.system() != "Windows":
            try:
                import fcntl
                lock_handle = open(LOCK_FILE, 'r+')
                fcntl.lockf(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                print(f"Exclusive file lock acquired")
                return lock_handle
            except (IOError, OSError) as e:
                print(f"Failed to acquire file lock: {e}")
                with open(LOCK_FILE, 'r') as f:
                    file_pid = int(f.read().strip())
                    if file_pid == os.getpid():
                        print("Lock file has our PID but couldn't get lock - continuing anyway")
                        return None
                sys.exit(1)
            except Exception as e:
                print(f"Unexpected error acquiring lock: {e}")
                sys.exit(1)

        return None

    except FileExistsError:
        print("Another instance is already running! Exiting.")
        sys.exit(1)
    except FileNotFoundError:
        os.makedirs(os.path.dirname(LOCK_FILE), exist_ok=True)
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
        return None

# ------------------- MEMORY CHECK -------------------
try:
    mem_mb = psutil.Process().memory_info().rss / 1024**2
    print(f"[Startup] Initial memory usage: {mem_mb:.1f} MB")
except:
    pass

# ------------------- FETCHERS & HELPERS -------------------
def get_server_time(client):
    try:
        resp = client.public_request("/fapi/v1/time")
        return int(resp['serverTime'])
    except Exception as e:
        log(f"Server time fetch failed: {e}")
        return int(time.time() * 1000)

def _fetch_json(url: str) -> List[Any] | None:
    try:
        r = requests.get(url, timeout=8)
        if r.status_code == 200:
            return r.json()
    except:
        return None
    return None

def _load_local_calendar() -> List[Any]:
    if os.path.exists(LOCAL_CALENDAR):
        try:
            with open(LOCAL_CALENDAR) as f:
                return json.load(f)
        except:
            pass
    return []

def _load_override() -> List[Any]:
    if os.path.exists(LOCAL_OVERRIDE):
        try:
            with open(LOCAL_OVERRIDE) as f:
                return json.load(f)
        except:
            pass
    return []

def _parse_event(event: Dict[str, Any]) -> Optional[datetime]:
    dt_str = event.get("date") or event.get("timestamp")
    if not dt_str:
        return None
    try:
        if isinstance(dt_str, (int, float)):
            return datetime.fromtimestamp(dt_str, tz=timezone.utc)
        return datetime.fromisoformat(dt_str.replace("Z", "+00:00"))
    except:
        return None

def _time_in_window(now_utc: datetime, start_hm: Tuple[int, int], end_hm: Tuple[int, int]) -> bool:
    start = datetime(now_utc.year, now_utc.month, now_utc.day, *start_hm, tzinfo=timezone.utc)
    end = datetime(now_utc.year, now_utc.month, now_utc.day, *end_hm, tzinfo=timezone.utc)
    if end <= start:
        end += timedelta(days=1)
    return start <= now_utc <= end

def _in_blackout_window(now_utc: Optional[datetime] = None) -> Tuple[bool, Optional[str]]:
    if not NEWS_BLACKOUT_WINDOWS:
        return False, None
    now = now_utc or datetime.now(timezone.utc)
    for wd, start, end in NEWS_BLACKOUT_WINDOWS:
        if wd is None or wd == now.weekday():
            if _time_in_window(now, start, end):
                return True, f"Blackout: {start}–{end} UTC"
    return False, None

# ------------------- NEWS HEARTBEAT (OPTIONAL) -------------------
def _refresh_news():
    global bot_state
    if not NEWS_GUARD_ENABLED:
        return
    now = datetime.now(timezone.utc)
    events: List[Dict[str, Any]] = []
    for api in LIVE_APIS:
        data = _fetch_json(api)
        if data:
            events.extend(data)
            break
    events.extend(_load_local_calendar())
    events.extend(_load_override())
    high: List[Dict[str, Any]] = []
    for e in events:
        title = (e.get("title") or e.get("event") or "").upper()
        impact = (e.get("impact") or "").lower()
        if impact != "high" and not any(k in title for k in HIGH_IMPACT_KEYWORDS):
            continue
        dt = _parse_event(e)
        if dt:
            high.append({"dt": dt, "title": title})
    with bot_state._news_lock:
        bot_state._news_cache = high
        bot_state._cache_ts = Decimal(str(time.time()))

def news_heartbeat():
    global bot_state
    if not NEWS_GUARD_ENABLED:
        return
    while not bot_state.STOP_REQUESTED:
        _refresh_news()
        now = datetime.now(timezone.utc)
        news_lock = False
        with bot_state._news_lock:
            for ev in bot_state._news_cache:
                if (ev["dt"] - timedelta(minutes=BUFFER_MINUTES) <= now <=
                    ev["dt"] + timedelta(minutes=BUFFER_MINUTES)):
                    news_lock = True
                    break
        static_block, _ = _in_blackout_window(now)
        bot_state.NEWS_LOCK = news_lock or static_block
        time.sleep(60)

def is_news_blocked(now_utc: Optional[datetime] = None) -> Tuple[bool, Optional[str]]:
    if not NEWS_GUARD_ENABLED:
        return False, None
    global bot_state
    now = now_utc or datetime.now(timezone.utc)
    with bot_state._news_lock:
        for ev in bot_state._news_cache:
            if (ev["dt"] - timedelta(minutes=BUFFER_MINUTES) <= now <=
                ev["dt"] + timedelta(minutes=BUFFER_MINUTES)):
                return True, f"Live: {ev['title']} @ {ev['dt'].strftime('%H:%M')} UTC"
    blocked, reason = _in_blackout_window(now)
    if blocked:
        return True, reason
    if os.path.exists("FORCE_NO_TRADE_TODAY.txt"):
        return True, "Manual override"
    return False, None

# ------------------- LOGGING -------------------
class CustomFormatter(logging.Formatter):
    def formatTime(self, record, datefmt=None):
        dt = datetime.fromtimestamp(record.created, tz=timezone.utc)
        return dt.strftime('%Y-%m-%dT%H:%M:%S.%f')[:-3] + '+00:00'

logger = logging.getLogger()
logger.handlers.clear()
logger.setLevel(logging.INFO)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(CustomFormatter(fmt='[%(asctime)s] %(message)s'))
logger.addHandler(console_handler)
file_handler = logging.FileHandler('bot_webhook_hedge.log')
file_handler.setFormatter(CustomFormatter(fmt='[%(asctime)s] %(message)s'))
logger.addHandler(file_handler)

def log(message: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    try:
        logger.info(message)
    except:
        print(f"[LOG-FAIL] {message[:200]}")
    if telegram_bot and telegram_chat_id:
        telegram_post(telegram_bot, telegram_chat_id, message)

# ------------------- TELEGRAM -------------------
def telegram_post(token: Optional[str], chat_id: Optional[str], text: str, parse_mode: Optional[str] = None):
    if not token or not chat_id or ':' not in token:
        return
    try:
        if len(text) > 4000:
            text = text[:3900] + "\n...[truncated]"
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        requests.post(url, json={"chat_id": chat_id, "text": text}, timeout=(3, 5))
    except:
        pass

def send_trade_telegram(trade_details: Dict[str, Any], leg_type: str, bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"📈 {leg_type} LEG ENTRY\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"Symbol: {trade_details['symbol']}\n"
        f"Side: {trade_details['side']}\n"
        f"Entry Price: {trade_details['entry']:.4f}\n"
    )
    # Handle possibly None SL/TP
    sl_val = trade_details.get('sl')
    tp_val = trade_details.get('tp')
    if sl_val is not None:
        message += f"SL: {sl_val:.4f}\n"
    else:
        message += f"SL: pending...\n"
    if tp_val is not None:
        message += f"TP: {tp_val:.4f}\n"
    else:
        message += f"TP: pending...\n"
    message += f"Qty: {trade_details['qty']:.5f} SOL\n"
    message += f"Leverage: {trade_details.get('leverage', 5)}x\n"
    if trade_details.get('trail_activation'):
        message += f"Trailing Activation: {trade_details['trail_activation']:.4f}\n"
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol: str, side: str, entry_price: Decimal, exit_price: Decimal,
                          qty: Decimal, pnl_usd: Decimal, pnl_r: Decimal, reason: str,
                          leg_type: str, bot: Optional[str], chat_id: Optional[str]):
    global bot_state
    message = (
        f"🔴 {leg_type} LEG CLOSED\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"Symbol: {symbol}\n"
        f"Side: {side}\n"
        f"Entry Price: {entry_price:.4f}\n"
        f"Exit Price: {exit_price:.4f}\n"
        f"Reason: {reason}\n"
        f"Qty: {qty:.5f}\n"
        f"PNL: {pnl_usd:.2f} USDT ({pnl_r:.2f}R)\n"
        f"Loss Streak: {bot_state.CONSEC_LOSSES}"
    )
    telegram_post(bot, chat_id, message)

def send_trail_placed_telegram(symbol: str, side: str, activation: Decimal, callback: Decimal, leg_type: str, bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"🔄 TRAILING STOP PLACED ({leg_type})\n"
        f"{side} {symbol}\n"
        f"Activation: {activation:.4f} ({TRAIL_TRIGGER_MULT}R)\n"
        f"Callback: {callback:.2f}% ({TRAIL_DISTANCE_MULT}R)"
    )
    telegram_post(bot, chat_id, message)

# ------------------- PNL LOGGING -------------------
PNL_FIELDS = ['date', 'trade_id', 'side', 'leg_type', 'entry', 'exit', 'pnl_usd', 'pnl_r', 'loss_streak']

def init_pnl_log():
    if not os.path.exists(bot_state.PNL_LOG_FILE):
        with open(bot_state.PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
            writer.writeheader()

def log_pnl(trade_id: int, side: str, entry: Decimal, exit_price: Decimal, qty: Decimal, R: Decimal, leg_type: str = "MAIN") -> Dict[str, Any]:
    global bot_state

    if side == 'LONG':
        pnl_usd = (exit_price - entry) * qty
    else:
        pnl_usd = (entry - exit_price) * qty

    total_risk = qty * R
    if total_risk > Decimal("0"):
        pnl_r = pnl_usd / total_risk
    else:
        pnl_r = Decimal("0") if pnl_usd >= Decimal("0") else Decimal("-1")

    denominator = entry * qty if entry and qty else Decimal("1")
    loss_pct = abs(pnl_usd) / denominator if pnl_usd < Decimal("0") else Decimal("0")
    is_full_loss = loss_pct >= Decimal("0.0074")

    if pnl_usd < Decimal("0") and is_full_loss and USE_CONSEC_LOSS_GUARD:
        bot_state.CONSEC_LOSSES += 1
    else:
        if USE_CONSEC_LOSS_GUARD:
            bot_state.CONSEC_LOSSES = 0

    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
        'leg_type': leg_type,
        'entry': float(entry),
        'exit': float(exit_price),
        'pnl_usd': float(pnl_usd),
        'pnl_r': float(pnl_r),
        'loss_streak': bot_state.CONSEC_LOSSES
    }

    bot_state.pnl_data.append(row)

    with open(bot_state.PNL_LOG_FILE, 'a', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
        writer.writerow(row)

    return row

# ------------------- PNL REPORT FUNCTIONS -------------------
def calculate_pnl_report(period: str) -> str:
    global bot_state
    now = datetime.now(timezone.utc)

    if period == 'daily':
        start_time = now.replace(hour=0, minute=0, second=0, microsecond=0)
    elif period == 'weekly':
        start_time = now - timedelta(days=now.weekday())
        start_time = start_time.replace(hour=0, minute=0, second=0, microsecond=0)
    elif period == 'monthly':
        start_time = now.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    else:
        return "Invalid period specified."

    filtered_trades = [
        trade for trade in bot_state.pnl_data
        if datetime.fromisoformat(trade['date']) >= start_time
    ]

    if not filtered_trades:
        return f"No trades recorded for the {period} period."

    total_pnl_usd = Decimal(str(sum(trade['pnl_usd'] for trade in filtered_trades)))
    total_pnl_r = Decimal(str(sum(trade['pnl_r'] for trade in filtered_trades)))
    num_trades = len(filtered_trades)
    avg_pnl_usd = total_pnl_usd / Decimal(str(num_trades)) if num_trades > 0 else Decimal("0")
    wins = sum(1 for trade in filtered_trades if trade['pnl_usd'] > 0)
    losses = num_trades - wins
    win_rate = (Decimal(str(wins)) / Decimal(str(num_trades)) * Decimal("100")) if num_trades > 0 else Decimal("0")

    main_wins = sum(1 for trade in filtered_trades if trade['leg_type'] == 'MAIN' and trade['pnl_usd'] > 0)
    insurance_wins = sum(1 for trade in filtered_trades if trade['leg_type'] == 'INSURANCE' and trade['pnl_usd'] > 0)

    return (
        f"{period.capitalize()} PNL Report:\n"
        f"• Total Trades: {num_trades}\n"
        f"• Total PNL: ${total_pnl_usd:.2f}\n"
        f"• Average PNL: ${avg_pnl_usd:.2f}\n"
        f"• Total PNL (R): {total_pnl_r:.2f}R\n"
        f"• Win Rate: {win_rate:.1f}% ({wins}W/{losses}L)\n"
        f"• MAIN Wins: {main_wins} | INSURANCE Wins: {insurance_wins}\n"
    )

def send_daily_report(bot_token: Optional[str], chat_id: Optional[str]):
    report = calculate_pnl_report('daily')
    subject = f"📊 Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot_token, chat_id, f"{subject}\n{report}")

def send_weekly_report(bot_token: Optional[str], chat_id: Optional[str]):
    report = calculate_pnl_report('weekly')
    subject = f"📈 Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot_token, chat_id, f"{subject}\n{report}")

def send_monthly_report(bot_token: Optional[str], chat_id: Optional[str]):
    report = calculate_pnl_report('monthly')
    subject = f"📉 Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    telegram_post(bot_token, chat_id, f"{subject}\n{report}")

# ------------------- BINANCE CLIENT WITH ALGO ORDERS -------------------
class BinanceAPIError(Exception):
    def __init__(self, message: str, status_code: Optional[int] = None, payload: Optional[str] = None):
        super().__init__(message)
        self.status_code = status_code
        self.payload = payload

class BinanceClient:
    def __init__(self, api_key: str, api_secret: str, use_live: bool = False, base_override: Optional[str] = None):
        self.api_key = api_key
        self.api_secret = api_secret
        self.use_live = use_live
        self.base = base_override or ("https://fapi.binance.com" if use_live else "https://testnet.binancefuture.com")
        self.dual_side = self._check_position_mode()
        log(f"Using base URL: {self.base}, Position Mode: {'Hedge' if self.dual_side else 'One-way'}")

    def set_leverage(self, symbol: str, leverage: int):
        params = {"symbol": symbol, "leverage": leverage}
        return self.send_signed_request("POST", "/fapi/v1/leverage", params)

    def _check_position_mode(self) -> bool:
        try:
            response = self.send_signed_request("GET", "/fapi/v1/positionSide/dual")
            return response.get('dualSidePosition', False)
        except Exception as e:
            log(f"Position mode check failed: {str(e)}. Assuming one-way mode.")
            return False

    def _sign(self, query_string: str) -> str:
        return hmac.new(self.api_secret.encode(), query_string.encode(), hashlib.sha256).hexdigest()

    def send_signed_request(self, method: str, endpoint: str, params: Optional[Dict[str, Any]] = None) -> Any:
        params = params.copy() if params else {}
        params["timestamp"] = get_server_time(self)
        params["recvWindow"] = 60000

        query = urlencode({k: str(params[k]) for k in sorted(params.keys())})
        signature = self._sign(query)
        url = f"{self.base}{endpoint}?{query}&signature={signature}"
        headers = {"X-MBX-APIKEY": self.api_key}

        for attempt in range(MAX_RETRIES):
            try:
                r = requests.request(method, url, headers=headers, timeout=REQUEST_TIMEOUT)
                if r.status_code == 200:
                    return r.json()
                if r.status_code in (429, 503):
                    wait = (2 ** attempt) * 10
                    log(f"Rate limited. Retry in {wait}s")
                    time.sleep(wait)
                    continue
                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", r.status_code, r.text)
            except (requests.exceptions.Timeout, requests.exceptions.ConnectionError) as e:
                if attempt < MAX_RETRIES - 1:
                    wait = (2 ** attempt) * 5
                    time.sleep(wait)
                    continue
                raise BinanceAPIError(f"Network failed after {MAX_RETRIES} retries: {str(e)}")
            except Exception as e:
                raise BinanceAPIError(f"Request failed: {str(e)}", payload=str(e))

        raise BinanceAPIError("Max retries exceeded")

    def public_request(self, path: str, params: Optional[Dict[str, Any]] = None) -> Any:
        url = f"{self.base}{path}"
        try:
            r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                return r.json()
            else:
                raise BinanceAPIError(f"HTTP {r.status_code}: {r.text}", r.status_code, r.text)
        except Exception as e:
            raise BinanceAPIError(f"Public request failed: {str(e)}", payload=str(e))

    def get_latest_trade_details(self, symbol: str) -> Optional[Dict[str, Any]]:
        params = {"symbol": symbol, "limit": 1}
        try:
            response = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            trades = response if isinstance(response, list) else []
            if trades:
                trade = trades[0]
                return {
                    "price": Decimal(str(trade.get("price", "0"))),
                    "orderId": trade.get("orderId"),
                    "qty": Decimal(str(trade.get("qty", "0"))),
                    "side": trade.get("side")
                }
            return None
        except:
            return None

    def get_open_orders(self, symbol: str) -> List[Any]:
        params = {"symbol": symbol}
        response = self.send_signed_request("GET", "/fapi/v1/openOrders", params)
        return response if isinstance(response, list) else []

    def get_open_algo_orders(self, symbol: str) -> List[Any]:
        try:
            response = self.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
            return response if isinstance(response, list) else []
        except:
            return []

    def cancel_all_open_orders(self, symbol: str):
        try:
            self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol, "recvWindow": 60000})
            log(f"[ZOMBIE KILLER] Regular orders cancelled for {symbol}")

            try:
                algo_orders = self.get_open_algo_orders(symbol)
                for order in algo_orders:
                    algo_id = order.get("algoId")
                    if algo_id:
                        self.send_signed_request("DELETE", "/fapi/v1/algoOrder", {
                            "symbol": symbol,
                            "algoId": str(algo_id)
                        })
                        time.sleep(0.1)
                if algo_orders:
                    log(f"[ZOMBIE KILLER] Cancelled {len(algo_orders)} algo orders")
            except:
                pass
        except:
            pass

    def cancel_algo_order(self, symbol: str, algo_id: int) -> Any:
        params = {"symbol": symbol, "algoId": str(algo_id)}
        return self.send_signed_request("DELETE", "/fapi/v1/algoOrder", params)

    def get_latest_fill_price(self, symbol: str, order_id: int) -> Optional[Decimal]:
        params = {"symbol": symbol, "orderId": order_id}
        try:
            trades = self.send_signed_request("GET", "/fapi/v1/userTrades", params)
            if trades and len(trades) > 0:
                return Decimal(str(trades[-1].get("price", "0")))
            return None
        except:
            return None

    def place_algo_order(self, symbol: str, side: str, quantity: Decimal,
                         order_type: str, trigger_price: Optional[Decimal] = None,
                         activation_price: Optional[Decimal] = None, callback_rate: Optional[Decimal] = None,
                         reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        params = {
            "algoType": "CONDITIONAL",
            "symbol": symbol,
            "side": side,
            "type": order_type,
            "quantity": str(quantity),
            "timeInForce": "GTE_GTC",
            "priceProtect": "true"
        }
        if reduce_only:
            params["reduceOnly"] = "true"
        if position_side:
            params["positionSide"] = position_side

        if trigger_price is not None:
            params["triggerPrice"] = str(trigger_price)
            params["workingType"] = "CONTRACT_PRICE"
        if activation_price is not None:
            params["activatePrice"] = str(activation_price)
        if callback_rate is not None:
            params["callbackRate"] = str(callback_rate)

        return self.send_signed_request("POST", "/fapi/v1/algoOrder", params)

    def place_stop_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                          reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "STOP_MARKET", trigger_price=stop_price,
                                     reduce_only=reduce_only, position_side=position_side)

    def place_take_profit_market(self, symbol: str, side: str, quantity: Decimal, stop_price: Decimal,
                                 reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "TAKE_PROFIT_MARKET", trigger_price=stop_price,
                                     reduce_only=reduce_only, position_side=position_side)

    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal,
                                   callback_rate: Decimal, activation_price: Decimal,
                                   reduce_only: bool = False, position_side: Optional[str] = None) -> Any:
        return self.place_algo_order(symbol, side, quantity, "TRAILING_STOP_MARKET",
                                     activation_price=activation_price, callback_rate=callback_rate,
                                     reduce_only=reduce_only, position_side=position_side)

# ------------------- SYMBOL FILTERS -------------------
def get_symbol_filters(client: BinanceClient, symbol: str) -> Dict[str, Decimal]:
    global bot_state
    if symbol in bot_state.symbol_filters_cache:
        return bot_state.symbol_filters_cache[symbol]

    info = client.public_request("/fapi/v1/exchangeInfo")
    s = next((x for x in info.get("symbols", []) if x.get("symbol") == symbol.upper()), None)
    if not s:
        raise ValueError(f"{symbol} not found")

    filters = {f["filterType"]: f for f in s.get("filters", [])}
    lot = filters.get("LOT_SIZE")
    if not lot:
        raise ValueError("LOT_SIZE filter missing")

    step_size = Decimal(str(lot["stepSize"]))
    min_qty = Decimal(str(lot["minQty"]))
    tick_size = Decimal(str(filters.get("PRICE_FILTER", {}).get("tickSize", "0.00000001")))
    min_notional = Decimal(str(filters.get("MIN_NOTIONAL", {}).get("notional", "0")))

    bot_state.symbol_filters_cache[symbol] = {
        "stepSize": step_size, "minQty": min_qty, "tickSize": tick_size, "minNotional": min_notional
    }
    return bot_state.symbol_filters_cache[symbol]

def quantize_qty(qty: Decimal, step_size: Decimal) -> Decimal:
    q = (qty // step_size) * step_size
    return q if q > Decimal("0") else step_size

def quantize_price(p: Decimal, tick_size: Decimal, rounding=ROUND_HALF_EVEN) -> Decimal:
    return p.quantize(tick_size, rounding=rounding)

# ------------------- POSITION HELPERS -------------------
def _retry_with_rate_limit(func, *args, max_retries: int = 3, **kwargs):
    """Wrapper for API calls to handle rate limits."""
    for attempt in range(max_retries):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            error_str = str(e).lower()
            if 'rate limit' in error_str or '429' in error_str or '503' in error_str:
                wait = (2 ** attempt) * 2
                log(f"Rate limited. Retry {attempt+1}/{max_retries} in {wait}s...")
                time.sleep(wait)
                continue
            else:
                raise
    raise Exception(f"Failed after {max_retries} retries")
def fetch_balance(client: BinanceClient) -> Decimal:
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
        return Decimal(str(data.get("totalWalletBalance", "0")))
    except:
        return Decimal("0")

def get_position_amt_for_side(client: BinanceClient, symbol: str, side: str) -> Decimal:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp if isinstance(pos_resp, list) else pos_resp.get('data', []) if isinstance(pos_resp, dict) else []
        for pos in positions:
            if pos.get("symbol") == symbol and pos.get("positionSide") == side.upper():
                return Decimal(str(pos.get("positionAmt", "0")))
        return Decimal('0')
    except:
        return Decimal('0')

def get_position_amt(client: BinanceClient, symbol: str) -> Decimal:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp if isinstance(pos_resp, list) else pos_resp.get('data', []) if isinstance(pos_resp, dict) else []
        net = Decimal('0')
        for pos in positions:
            if pos.get("symbol") == symbol:
                net += Decimal(str(pos.get("positionAmt", "0")))
        return net
    except:
        return Decimal('0')

def fetch_open_positions_details(client: BinanceClient, symbol: str) -> List[Dict[str, Any]]:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp if isinstance(pos_resp, list) else pos_resp.get('data', []) if isinstance(pos_resp, dict) else []
        return [p for p in positions if p.get("symbol") == symbol]
    except:
        return []

def get_current_price(client: BinanceClient, symbol: str) -> Optional[Decimal]:
    try:
        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
        return Decimal(str(ticker.get("price", "0")))
    except:
        return None

def has_any_active_leg() -> bool:
    main_active = bot_state.current_trade is not None and bot_state.current_trade.active
    ins_active = bot_state.insurance_trade is not None and bot_state.insurance_trade.active
    return main_active or ins_active

# ------------------- RISK MANAGEMENT (DISABLED) -------------------
def check_weekly_drawdown_stop(current_equity: Decimal, symbol: str, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> bool:
    """WEEKLY DRAWDOWN GUARD - DISABLED (always returns False)"""
    return False

def trading_allowed(client: BinanceClient, symbol: str, telegram_bot: Optional[str], telegram_chat_id: Optional[str]) -> bool:
    """TRADING ALLOWED CHECK - DISABLED (always returns True)"""
    return True

# ------------------- STOP HANDLER -------------------
def _request_stop(signum: Optional[int] = None, frame: Any = None, symbol: Optional[str] = None,
                  telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    global bot_state

    with bot_state._stop_lock:
        if bot_state.STOP_REQUESTED:
            logger.info("Stop already requested; skipping duplicate cleanup.")
            return
        bot_state.STOP_REQUESTED = True

    bot_state._position_closure_in_progress = True
    log("🛑 STOP REQUESTED — Closing ALL positions...", telegram_bot, telegram_chat_id)

    if not bot_state.client or not symbol:
        log("Client or symbol not available. Skipping closure.", telegram_bot, telegram_chat_id)
        bot_state._position_closure_in_progress = False
        return

    try:
        positions = fetch_open_positions_details(bot_state.client, symbol)
        for pos in positions:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt == Decimal('0'):
                continue

            position_side = pos.get("positionSide")
            entry_price_dec = Decimal(str(pos.get("entryPrice", "0")))
            qty = abs(pos_amt)
            close_side = "SELL" if pos_amt > Decimal('0') else "BUY"

            leg_type = "UNKNOWN"
            if bot_state.current_trade and bot_state.current_trade.active and position_side == bot_state.current_trade.side:
                leg_type = "MAIN"
            elif bot_state.insurance_trade and bot_state.insurance_trade.active and position_side == bot_state.insurance_trade.side:
                leg_type = "INSURANCE"

            log(f"Closing {leg_type} leg → {position_side} | Qty: {qty}", telegram_bot, telegram_chat_id)

            order_params = {
                "symbol": symbol,
                "side": close_side,
                "type": "MARKET",
                "quantity": str(qty)
            }
            if position_side:
                order_params["positionSide"] = position_side

            response = bot_state.client.send_signed_request("POST", "/fapi/v1/order", order_params)
            market_order_id = response.get("orderId")

            time.sleep(1.5)

            exit_price_dec = Decimal("0")
            try:
                trades = bot_state.client.send_signed_request("GET", "/fapi/v1/userTrades", {
                    "symbol": symbol,
                    "orderId": market_order_id,
                    "limit": 10
                })
                filled = [t for t in trades if Decimal(str(t.get("qty", "0"))) > Decimal('0')]
                if filled:
                    exit_price_dec = Decimal(str(filled[-1]["price"]))
            except:
                pass

            if exit_price_dec == Decimal("0"):
                try:
                    ticker = bot_state.client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                    exit_price_dec = Decimal(str(ticker.get("price", "0")))
                except:
                    pass

            R = entry_price_dec * SL_PCT
            pnl_row = log_pnl(
                len(bot_state.pnl_data) + 1,
                "LONG" if pos_amt > Decimal('0') else "SHORT",
                entry_price_dec,
                exit_price_dec,
                qty,
                R,
                leg_type
            )

            send_closure_telegram(
                symbol=symbol,
                side="LONG" if pos_amt > Decimal('0') else "SHORT",
                entry_price=entry_price_dec,
                exit_price=exit_price_dec,
                qty=qty,
                pnl_usd=Decimal(str(pnl_row.get('pnl_usd', 0))),
                pnl_r=Decimal(str(pnl_row.get('pnl_r', 0))),
                reason="Stop Requested",
                leg_type=leg_type,
                bot=telegram_bot,
                chat_id=telegram_chat_id
            )

    except Exception as e:
        log(f"Error while closing positions: {str(e)}", telegram_bot, telegram_chat_id)

    try:
        bot_state.client.cancel_all_open_orders(symbol)
        log(f"All open orders cancelled for {symbol}.", telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"Order cancellation failed: {e}", telegram_bot, telegram_chat_id)

    bot_state._orders_cancelled = True
    bot_state._position_closure_in_progress = False

    bot_state.current_trade = None
    bot_state.insurance_trade = None
    bot_state.INSURANCE_ACTIVE = False

    log("🛑 Stop process completed.", telegram_bot, telegram_chat_id)

# ------------------- ORDERS PLACEMENT -------------------
def place_orders(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal,
                 telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    """
    Place protective orders for a trade leg.
    - MAIN leg: SL + TP + TRAILING STOP (if activation price set)
    - INSURANCE leg: SL + TP only (NO trailing)
    """
    if not trade_state.active or not trade_state.entry_price:
        log("ERROR: place_orders called with incomplete trade_state", telegram_bot, telegram_chat_id)
        return

    # === If SL and TP are already set (e.g., insurance leg with pre‑computed values) ===
    if trade_state.sl is not None and trade_state.tp is not None:
        close_side = "SELL" if trade_state.side == "LONG" else "BUY"
        position_side = trade_state.side.upper()
        qty_dec = trade_state.qty
        failures = 0

        # Place STOP_MARKET SL
        try:
            sl_order = client.place_stop_market(symbol, close_side, qty_dec, trade_state.sl,
                                                reduce_only=False, position_side=position_side)
            if sl_order and sl_order.get("algoId"):
                trade_state.sl_algo_id = sl_order["algoId"]
                log(f"[{trade_state.leg_type}] Placed STOP_MARKET SL at {trade_state.sl:.4f}", telegram_bot, telegram_chat_id)
            else:
                failures += 1
                log(f"[{trade_state.leg_type}] Failed to place SL - no algoId", telegram_bot, telegram_chat_id)
        except Exception as e:
            failures += 1
            log(f"[{trade_state.leg_type}] Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)

        # Place TAKE_PROFIT_MARKET TP
        try:
            tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, trade_state.tp,
                                                       reduce_only=False, position_side=position_side)
            if tp_order and tp_order.get("algoId"):
                trade_state.tp_algo_id = tp_order["algoId"]
                log(f"[{trade_state.leg_type}] Placed TAKE_PROFIT_MARKET TP at {trade_state.tp:.4f}", telegram_bot, telegram_chat_id)
            else:
                failures += 1
                log(f"[{trade_state.leg_type}] Failed to place TP - no algoId", telegram_bot, telegram_chat_id)
        except Exception as e:
            failures += 1
            log(f"[{trade_state.leg_type}] Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)

        # Place trailing stop for MAIN leg if activation exists
        if trade_state.leg_type == "MAIN" and trade_state.trail_activation_price is not None:
            callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
            try:
                trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec,
                                                                callback_rate=callback_rate,
                                                                activation_price=trade_state.trail_activation_price,
                                                                reduce_only=False, position_side=position_side)
                if trail_order and trail_order.get("algoId"):
                    trade_state.trail_algo_id = trail_order["algoId"]
                    trade_state.trail_activated = True
                    log(f"[{trade_state.leg_type}] Placed TRAILING_STOP_MARKET (activation: {trade_state.trail_activation_price:.4f})",
                        telegram_bot, telegram_chat_id)
                else:
                    log(f"[{trade_state.leg_type}] Failed to place trailing stop - no algoId", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"[{trade_state.leg_type}] Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)

        # If both SL and TP failed, disable the leg
        if failures >= 2:
            emergency_msg = f"🚨 CRITICAL: Protective orders failed for {trade_state.leg_type} leg - disabling this leg only"
            log(emergency_msg, telegram_bot, telegram_chat_id)
            trade_state.active = False
            if trade_state.leg_type == "MAIN":
                bot_state.current_trade = None
            else:
                bot_state.insurance_trade = None
                bot_state.INSURANCE_ACTIVE = False
        return

    # --- Below is the original code for when SL/TP are NOT pre‑set (e.g., MAIN leg) ---
    entry_price = trade_state.entry_price
    qty_dec = trade_state.qty
    close_side = "SELL" if trade_state.side == "LONG" else "BUY"
    position_side = trade_state.side.upper()
    R = entry_price * SL_PCT

    failures = 0

    # Calculate SL and TP based on leg type
    if trade_state.leg_type == "INSURANCE":
        # INSURANCE: fixed 1R SL, 0.9R TP (NO trailing)
        if trade_state.side == "LONG":
            sl_price_dec = entry_price - (R * INSURANCE_SL_MULT)
            sl_rounding = ROUND_DOWN
            tp_price_dec = entry_price + (R * INSURANCE_TP_MULT)
            tp_rounding = ROUND_UP
        else:
            sl_price_dec = entry_price + (R * INSURANCE_SL_MULT)
            sl_rounding = ROUND_UP
            tp_price_dec = entry_price - (R * INSURANCE_TP_MULT)
            tp_rounding = ROUND_DOWN
        sl_price_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
        tp_price_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
        use_trailing = False
    else:
        # MAIN: standard SL, 9R TP, trailing stop
        if trade_state.side == "LONG":
            sl_price_dec = entry_price * (Decimal("1") - SL_PCT)
            sl_rounding = ROUND_DOWN
            tp_price_dec = entry_price + (TP_MULT * R)
            tp_rounding = ROUND_UP
        else:
            sl_price_dec = entry_price * (Decimal("1") + SL_PCT)
            sl_rounding = ROUND_UP
            tp_price_dec = entry_price - (TP_MULT * R)
            tp_rounding = ROUND_DOWN
        sl_price_quant = quantize_price(sl_price_dec, tick_size, sl_rounding)
        tp_price_quant = quantize_price(tp_price_dec, tick_size, tp_rounding)
        use_trailing = True

    trade_state.sl = sl_price_quant
    trade_state.tp = tp_price_quant

    # Place STOP_MARKET SL
    try:
        sl_order = client.place_stop_market(symbol, close_side, qty_dec, sl_price_quant,
                                            reduce_only=False, position_side=position_side)
        if sl_order and sl_order.get("algoId"):
            trade_state.sl_algo_id = sl_order["algoId"]
            log(f"[{trade_state.leg_type}] Placed STOP_MARKET SL at {sl_price_quant:.4f}", telegram_bot, telegram_chat_id)
        else:
            failures += 1
            log(f"[{trade_state.leg_type}] Failed to place SL - no algoId", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"[{trade_state.leg_type}] Failed to place SL: {str(e)}", telegram_bot, telegram_chat_id)

    # Place TAKE_PROFIT_MARKET TP
    try:
        tp_order = client.place_take_profit_market(symbol, close_side, qty_dec, tp_price_quant,
                                                   reduce_only=False, position_side=position_side)
        if tp_order and tp_order.get("algoId"):
            trade_state.tp_algo_id = tp_order["algoId"]
            log(f"[{trade_state.leg_type}] Placed TAKE_PROFIT_MARKET TP at {tp_price_quant:.4f}", telegram_bot, telegram_chat_id)
        else:
            failures += 1
            log(f"[{trade_state.leg_type}] Failed to place TP - no algoId", telegram_bot, telegram_chat_id)
    except Exception as e:
        failures += 1
        log(f"[{trade_state.leg_type}] Failed to place TP: {str(e)}", telegram_bot, telegram_chat_id)

    # Place TRAILING STOP (MAIN only)
    if use_trailing and trade_state.leg_type == "MAIN" and trade_state.trail_activation_price is not None:
        callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
        try:
            trail_order = client.place_trailing_stop_market(symbol, close_side, qty_dec,
                                                            callback_rate=callback_rate,
                                                            activation_price=trade_state.trail_activation_price,
                                                            reduce_only=False, position_side=position_side)
            if trail_order and trail_order.get("algoId"):
                trade_state.trail_algo_id = trail_order["algoId"]
                trade_state.trail_activated = True
                log(f"[{trade_state.leg_type}] Placed TRAILING_STOP_MARKET (activation: {trade_state.trail_activation_price:.4f}, callback: {callback_rate:.2f}%)",
                    telegram_bot, telegram_chat_id)
            else:
                log(f"[{trade_state.leg_type}] Failed to place trailing stop - no algoId", telegram_bot, telegram_chat_id)
        except Exception as e:
            log(f"[{trade_state.leg_type}] Failed to place trailing stop: {str(e)}", telegram_bot, telegram_chat_id)

    # Soft emergency: disable only this leg if both SL and TP failed
    if failures >= 2:
        emergency_msg = f"🚨 CRITICAL: Protective orders failed for {trade_state.leg_type} leg - disabling this leg only"
        log(emergency_msg, telegram_bot, telegram_chat_id)
        trade_state.active = False
        if trade_state.leg_type == "MAIN":
            bot_state.current_trade = None
        else:
            bot_state.insurance_trade = None
            bot_state.INSURANCE_ACTIVE = False
# ------------------- RECOVERY FUNCTIONS -------------------
def debug_and_recover_expired_orders(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal,
                                     telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> bool:
    """Recover missing protective algo orders. Idempotent. Thread-safe."""
    global bot_state

    # Early exit guards
    if bot_state.STOP_REQUESTED or bot_state._position_closure_in_progress:
        return False

    if trade_state.leg_type == "INSURANCE":
        return False

    if not trade_state.active:
        return False

    if trade_state.leg_type == "MAIN" and bot_state.current_trade is None:
        return False

    try:
        position_side = trade_state.side.upper()
        pos_amt = get_position_amt_for_side(client, symbol, position_side)
        if pos_amt == Decimal("0"):
            return False

        # Emergency close on 1% adverse move
        current_price = Decimal(str(_retry_with_rate_limit(
            client.public_request, "/fapi/v1/ticker/price", {"symbol": symbol}
        )["price"]))
        entry = trade_state.entry_price

        adverse_move = False
        if trade_state.side == "LONG" and current_price <= entry * Decimal("0.99"):
            adverse_move = True
        elif trade_state.side == "SHORT" and current_price >= entry * Decimal("1.01"):
            adverse_move = True

        if adverse_move:
            log(f"[{trade_state.leg_type}] EMERGENCY CLOSE: 1% adverse move", telegram_bot, telegram_chat_id)
            _request_stop(symbol=symbol, telegram_bot=telegram_bot, telegram_chat_id=telegram_chat_id)
            trade_state.active = False
            return True

        # Fetch open algo orders
        algo_resp = _retry_with_rate_limit(
            client.send_signed_request, "GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol}
        )
        algo_open = algo_resp if isinstance(algo_resp, list) else []
        open_algo_ids = {o.get("algoId") for o in algo_open if o.get("algoId") is not None}

        recovered = False
        close_side = "SELL" if trade_state.side == "LONG" else "BUY"

        # Recover SL
        if trade_state.sl_algo_id and trade_state.sl_algo_id not in open_algo_ids:
            log(f"[{trade_state.leg_type}] SL missing. Re-issuing...", telegram_bot, telegram_chat_id)
            new_sl = client.place_stop_market(symbol, close_side, trade_state.qty, trade_state.sl,
                                              reduce_only=False, position_side=position_side)   # ← FIXED
            if new_sl and new_sl.get("algoId"):
                trade_state.sl_algo_id = new_sl["algoId"]
                log(f"[{trade_state.leg_type}] SL RECOVERED", telegram_bot, telegram_chat_id)
                recovered = True

        # Recover TP
        if trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids:
            log(f"[{trade_state.leg_type}] TP missing. Re-issuing...", telegram_bot, telegram_chat_id)
            new_tp = client.place_take_profit_market(symbol, close_side, trade_state.qty, trade_state.tp,
                                                     reduce_only=False, position_side=position_side)   # ← FIXED
            if new_tp and new_tp.get("algoId"):
                trade_state.tp_algo_id = new_tp["algoId"]
                log(f"[{trade_state.leg_type}] TP RECOVERED", telegram_bot, telegram_chat_id)
                recovered = True

        # Recover trailing (MAIN only)
        if trade_state.leg_type == "MAIN" and trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids:
            log(f"[{trade_state.leg_type}] Trailing missing. Re-issuing...", telegram_bot, telegram_chat_id)
            callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
            new_trail = client.place_trailing_stop_market(symbol, close_side, trade_state.qty,
                                                          callback_rate=callback_rate,
                                                          activation_price=trade_state.trail_activation_price,
                                                          reduce_only=False, position_side=position_side)   # ← FIXED
            if new_trail and new_trail.get("algoId"):
                trade_state.trail_algo_id = new_trail["algoId"]
                log(f"[{trade_state.leg_type}] TRAILING RECOVERED", telegram_bot, telegram_chat_id)
                recovered = True

        return recovered
    except Exception as e:
        log(f"[{trade_state.leg_type}] Recovery failed: {e}", telegram_bot, telegram_chat_id)
        return False

# ------------------- MONITOR TRADE (PURE DETECTION ONLY) -------------------
def monitor_trade(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal,
                  telegram_bot: Optional[str], telegram_chat_id: Optional[str],
                  entry_candle_close_time: int):
    """
    Pure monitoring - only detects when Binance protective orders close the position.
    Does NOT manage trailing stops or price tracking (that's handled by Binance algo orders).
    """
    global bot_state

    log(f"[{trade_state.leg_type}] Monitoring active trade (pure detection mode)...", telegram_bot, telegram_chat_id)

    last_recovery_check = Decimal("0")

    try:
        while trade_state.active and not bot_state.STOP_REQUESTED:
            if bot_state.STOP_REQUESTED or bot_state._position_closure_in_progress:
                trade_state.active = False
                return

            # Periodic recovery check for expired algo orders
            if Decimal(str(time.time())) - last_recovery_check >= Decimal(str(RECOVERY_CHECK_INTERVAL)):
                debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                last_recovery_check = Decimal(str(time.time()))

            # Check if position still exists for this leg
            try:
                pos_amt_side = get_position_amt_for_side(client, symbol, trade_state.side.upper())

                if pos_amt_side == Decimal('0') and trade_state.active:
                    if bot_state._position_closure_in_progress:
                        trade_state.active = False
                        return

                    log(f"[{trade_state.leg_type}] Position closed. Determining exit reason...", telegram_bot, telegram_chat_id)

                    trade_state.active = False
                    time.sleep(1.2)

                    reason = "Unknown"
                    exit_price_dec: Optional[Decimal] = None

                    try:
                        algo_open = client.get_open_algo_orders(symbol)
                        open_algo_ids = {o.get("algoId") for o in algo_open if o.get("algoId") is not None}

                        triggered_id = None
                        if (trade_state.leg_type == "MAIN" and trade_state.trail_activated and
                            trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids):
                            reason = "Trailing Stop"
                            triggered_id = trade_state.trail_algo_id
                        elif trade_state.sl_algo_id and trade_state.sl_algo_id not in open_algo_ids:
                            reason = "Stop Loss"
                            triggered_id = trade_state.sl_algo_id
                        elif trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids:
                            reason = "Take Profit"
                            triggered_id = trade_state.tp_algo_id

                        if triggered_id:
                            exit_price_dec = client.get_latest_fill_price(symbol, triggered_id)
                    except Exception as e:
                        log(f"[{trade_state.leg_type}] Error detecting trigger: {e}", telegram_bot, telegram_chat_id)

                    if exit_price_dec is None:
                        latest = client.get_latest_trade_details(symbol)
                        if latest and latest.get("price"):
                            exit_price_dec = Decimal(str(latest["price"]))
                        else:
                            ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                            exit_price_dec = Decimal(str(ticker.get("price", "0")))

                    entry_price_safe = trade_state.entry_price or Decimal("0")
                    R = entry_price_safe * SL_PCT

                    pnl_row = log_pnl(
                        len(bot_state.pnl_data) + 1,
                        trade_state.side or "UNKNOWN",
                        entry_price_safe,
                        exit_price_dec,
                        trade_state.qty or Decimal("0"),
                        R,
                        trade_state.leg_type
                    )

                    send_closure_telegram(
                        symbol=symbol,
                        side=trade_state.side or "UNKNOWN",
                        entry_price=entry_price_safe,
                        exit_price=exit_price_dec,
                        qty=trade_state.qty or Decimal("0"),
                        pnl_usd=Decimal(str(pnl_row['pnl_usd'])),
                        pnl_r=Decimal(str(pnl_row['pnl_r'])),
                        reason=reason,
                        leg_type=trade_state.leg_type,
                        bot=telegram_bot,
                        chat_id=telegram_chat_id
                    )

                    try:
                        if not has_any_active_leg():
                            client.cancel_all_open_orders(symbol)
                    except Exception as e:
                        pass

                    if trade_state.leg_type == "INSURANCE":
                        bot_state.insurance_trade = None
                        bot_state.INSURANCE_ACTIVE = False
                    else:
                        bot_state.current_trade = None

                    return

            except Exception as e:
                log(f"[{trade_state.leg_type}] Monitor error: {str(e)}", telegram_bot, telegram_chat_id)

            time.sleep(1)

    finally:
        if not trade_state.active:
            pass

# ------------------- POSITION RECOVERY ON STARTUP -------------------
def recover_existing_positions(client, symbol, tick_size, telegram_bot, telegram_chat_id):
    global bot_state
    try:
        positions = fetch_open_positions_details(client, symbol)
        if not positions:
            return

        for pos in positions:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt == Decimal('0'):
                continue

            position_side = pos.get("positionSide")
            entry_price = Decimal(str(pos.get("entryPrice", "0")))
            qty = abs(pos_amt)

            # Determine leg type based on which leg is active
            leg_type = "MAIN"
            if bot_state.insurance_trade and bot_state.insurance_trade.active:
                if (position_side == "LONG" and bot_state.insurance_trade.side == "LONG") or \
                   (position_side == "SHORT" and bot_state.insurance_trade.side == "SHORT"):
                    leg_type = "INSURANCE"
            elif bot_state.current_trade and bot_state.current_trade.active:
                if (position_side == "LONG" and bot_state.current_trade.side == "LONG") or \
                   (position_side == "SHORT" and bot_state.current_trade.side == "SHORT"):
                    leg_type = "MAIN"

            trade_state = TradeState()
            trade_state.active = True
            trade_state.leg_type = leg_type
            trade_state.side = "LONG" if position_side == "LONG" else "SHORT"
            trade_state.qty = qty
            trade_state.entry_price = entry_price
            trade_state.risk = entry_price * SL_PCT

            if leg_type == "INSURANCE":
                trade_state.trail_activation_price = None
                trade_state.trail_activated = False
            else:
                # Recalculate trail activation price for MAIN
                if trade_state.side == "LONG":
                    trail_raw = entry_price + (TRAIL_TRIGGER_MULT * trade_state.risk)
                    trail_buffered = trail_raw + TRAIL_PRICE_BUFFER
                else:
                    trail_raw = entry_price - (TRAIL_TRIGGER_MULT * trade_state.risk)
                    trail_buffered = trail_raw - TRAIL_PRICE_BUFFER
                trade_state.trail_activation_price = quantize_price(trail_buffered, tick_size,
                                                                    ROUND_UP if trade_state.side == "LONG" else ROUND_DOWN)
                trade_state.trail_activated = False

            if leg_type == "INSURANCE":
                bot_state.insurance_trade = trade_state
                bot_state.INSURANCE_ACTIVE = True
            else:
                bot_state.current_trade = trade_state

            threading.Thread(
                target=monitor_trade,
                args=(client, symbol, trade_state, tick_size,
                      telegram_bot, telegram_chat_id, int(time.time() * 1000)),
                daemon=True
            ).start()

            log(f"✅ Position recovery complete - {leg_type} leg ({position_side}) resumed", telegram_bot, telegram_chat_id)

    except Exception as e:
        log(f"❌ Position recovery error: {e}", telegram_bot, telegram_chat_id)

# ------------------- SLIPPAGE CHECK (FIXED) -------------------
def _check_slippage(client: BinanceClient, symbol: str, entry_price: Decimal,
                    telegram_bot: Optional[str], telegram_chat_id: Optional[str]) -> Tuple[bool, Decimal]:
    try:
        ticker = client.public_request("/fapi/v1/ticker/bookTicker", {"symbol": symbol})
        bid = Decimal(str(ticker.get("bidPrice") or "0"))
        ask = Decimal(str(ticker.get("askPrice") or "0"))
        if bid > Decimal("0") and ask > Decimal("0"):
            current_price = (bid + ask) / Decimal("2")
            source = "bookTicker"
        else:
            raise ValueError("Invalid bid/ask")
    except:
        try:
            mark_data = client.public_request("/fapi/v1/premiumIndex", {"symbol": symbol})
            current_price = Decimal(str(mark_data["markPrice"]))
            source = "mark price"
        except:
            return True, entry_price

    slippage_pct = abs(current_price - entry_price) / entry_price
    if slippage_pct > MAX_ENTRY_SLIPPAGE_PCT:
        log(f"ENTRY SKIPPED: Slippage {slippage_pct*100:.3f}% > 0.2% [{source}]", telegram_bot, telegram_chat_id)
        return False, entry_price

    return True, current_price

# ------------------- WEBHOOK PROCESSING -------------------
def process_alert(data: Dict[str, Any]):
    global bot_state, CMD_ARGS
    
    # === EDISON-STYLE: Quick stale state check before processing ===
    # If we think we have a trade but no position on exchange, clear it
    if has_any_active_leg():
        try:
            positions = fetch_open_positions_details(bot_state.client, CMD_ARGS.symbol)
            has_real_position = False
            for pos in positions:
                if Decimal(str(pos.get("positionAmt", "0"))) != Decimal('0'):
                    has_real_position = True
                    break
            
            if not has_real_position:
                log("⚠️ Stale state detected - clearing (no positions on exchange)", 
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                bot_state.current_trade = None
                bot_state.insurance_trade = None
                bot_state.INSURANCE_ACTIVE = False
        except:
            pass  # If check fails, proceed anyway

    symbol = data.get('symbol')
    if symbol != CMD_ARGS.symbol.upper():
        log(f"Symbol mismatch: {symbol} != {CMD_ARGS.symbol.upper()}")
        return

    side = data.get('side', '').upper()
    tv_qty_str = data.get('qty')
    order_type = data.get('type', '').upper()
    reduce_only = data.get('reduceOnly', False)

    client = bot_state.client
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    tick_size = filters['tickSize']
    min_notional = filters['minNotional']

    if order_type == 'MARKET':
        if reduce_only:
            # CLOSE ORDER - determine which leg to close
            with bot_state._trade_lock:
                main_trade = bot_state.current_trade
                ins_trade = bot_state.insurance_trade

            closed_any = False

            # Check MAIN leg
            if main_trade and main_trade.active:
                pos_amt = get_position_amt_for_side(client, symbol, main_trade.side.upper())
                if pos_amt > Decimal('0'):
                    close_side = "SELL" if main_trade.side == "LONG" else "BUY"
                    if side == close_side:
                        response = client.send_signed_request("POST", "/fapi/v1/order", {
                            "symbol": symbol,
                            "side": close_side,
                            "type": "MARKET",
                            "quantity": str(abs(pos_amt)),
                            "positionSide": main_trade.side.upper(),
                            "reduceOnly": True
                        })
                        log(f"MAIN leg close order sent", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                        closed_any = True

            # Check INSURANCE leg
            if ins_trade and ins_trade.active:
                pos_amt = get_position_amt_for_side(client, symbol, ins_trade.side.upper())
                if pos_amt > Decimal('0'):
                    close_side = "SELL" if ins_trade.side == "LONG" else "BUY"
                    if side == close_side:
                        response = client.send_signed_request("POST", "/fapi/v1/order", {
                            "symbol": symbol,
                            "side": close_side,
                            "type": "MARKET",
                            "quantity": str(abs(pos_amt)),
                            "positionSide": ins_trade.side.upper(),
                            "reduceOnly": True
                        })
                        log(f"INSURANCE leg close order sent", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                        closed_any = True

            if not closed_any:
                log("No active leg found to close", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

        else:
            # ENTRY ORDER - NEW SIGNAL
            if has_any_active_leg():
                log("Position already active, ignoring entry", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return

            if NEWS_GUARD_ENABLED:
                blocked, reason = is_news_blocked()
                if blocked:
                    log(f"News blocked: {reason}, ignoring entry", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    return

            current_price = get_current_price(client, symbol)
            if current_price is None or current_price <= Decimal("0"):
                log("Failed to get current price", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return

            entry_price = current_price

            # Determine MAIN leg direction from signal
            original_side = side  # BUY or SELL
            insurance_side = "SELL" if original_side == "BUY" else "BUY"

            log(f"📊 WEBHOOK SIGNAL → MAIN: {original_side} | INSURANCE: {insurance_side}",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

            # SLIPPAGE CHECK
            slippage_passed, _ = _check_slippage(client, symbol, entry_price, CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            if not slippage_passed:
                return

            # === DYNAMIC 50/50 VIRTUAL CAPITAL SPLIT ===
            actual_balance = fetch_balance(client)
            if actual_balance <= Decimal("0"):
                log("Cannot trade: zero balance", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return

            # Split balance 50/50 for MAIN and INSURANCE
            virtual_main = actual_balance / Decimal("2")
            virtual_insurance = actual_balance / Decimal("2")

            log(f"💰 Dynamic split: Total ${actual_balance:.2f} → MAIN: ${virtual_main:.2f} | INSURANCE: ${virtual_insurance:.2f}",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

            # === MAIN LEG CALCULATIONS ===
            R_main = entry_price * SL_PCT
            main_margin = virtual_main * MARGIN_USAGE_PCT * SAFETY_FACTOR
            main_risk_usd = virtual_main * BASE_RISK_PCT

            qty_raw = main_risk_usd / R_main
            max_by_margin = (main_margin * MAX_LEVERAGE) / entry_price
            qty_main = min(qty_raw, max_by_margin, Decimal("25"))
            qty_main = quantize_qty(qty_main, step_size)

            if (qty_main * entry_price) < min_notional:
                log(f"Main leg quantity too small (${qty_main * entry_price:.2f} < ${min_notional}) → skipping",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return

            main_position_side = "LONG" if original_side == "BUY" else "SHORT"

            # Place MAIN order
            order_res_main = client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": original_side,
                "type": "MARKET",
                "quantity": str(qty_main),
                "positionSide": main_position_side
            })

            # Wait for main fill
            start_time = time.time()
            actual_qty_main = None
            while not bot_state.STOP_REQUESTED and (time.time() - start_time) < ORDER_FILL_TIMEOUT:
                pos_amt = get_position_amt_for_side(client, symbol, main_position_side)
                if pos_amt > Decimal('0.001'):
                    actual_qty_main = pos_amt
                    log(f"✅ Main fill detected! Qty: {actual_qty_main:.5f} SOL", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    break
                time.sleep(1)

            if actual_qty_main is None:
                try:
                    order_status = client.send_signed_request("GET", "/fapi/v1/order", {
                        "symbol": symbol,
                        "orderId": order_res_main.get("orderId")
                    })
                    if order_status.get("status") == "FILLED":
                        actual_qty_main = Decimal(str(order_status.get("executedQty", "0")))
                        log(f"✅ Main fill detected via order status! Qty: {actual_qty_main:.5f} SOL", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                except Exception as e:
                    log(f"Order status check failed: {e}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

            if actual_qty_main is None or actual_qty_main <= Decimal('0'):
                log("❌ Main leg fill failed. Aborting trade.", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return

            actual_fill_price_dec = client.get_latest_fill_price(symbol, order_res_main.get("orderId")) or entry_price

            # === CREATE MAIN TRADE STATE ===
            main_trade_state = TradeState()
            main_trade_state.active = True
            main_trade_state.leg_type = "MAIN"
            main_trade_state.entry_price = actual_fill_price_dec
            main_trade_state.qty = actual_qty_main
            main_trade_state.side = "LONG" if original_side == "BUY" else "SHORT"
            main_trade_state.risk = actual_fill_price_dec * SL_PCT

            # Calculate trail activation price for MAIN
            R_main_actual = actual_fill_price_dec * SL_PCT
            if main_trade_state.side == "LONG":
                trail_raw = actual_fill_price_dec + (TRAIL_TRIGGER_MULT * R_main_actual)
                trail_buffered = trail_raw + TRAIL_PRICE_BUFFER
                trail_activation_quant = quantize_price(trail_buffered, tick_size, ROUND_UP)
            else:
                trail_raw = actual_fill_price_dec - (TRAIL_TRIGGER_MULT * R_main_actual)
                trail_buffered = trail_raw - TRAIL_PRICE_BUFFER
                trail_activation_quant = quantize_price(trail_buffered, tick_size, ROUND_DOWN)

            main_trade_state.trail_activation_price = trail_activation_quant
            main_trade_state.trail_activated = False

            # Place protective orders for MAIN (this sets main_trade_state.sl and .tp)
            place_orders(client, symbol, main_trade_state, tick_size, CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

            # Send Telegram with complete details (SL/TP now set)
            send_trade_telegram({
                'symbol': symbol,
                'side': main_trade_state.side,
                'entry': main_trade_state.entry_price,
                'sl': main_trade_state.sl,
                'tp': main_trade_state.tp,
                'qty': main_trade_state.qty,
                'leverage': 5,
                'trail_activation': main_trade_state.trail_activation_price
            }, "MAIN", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

            # Store and start monitoring for MAIN
            bot_state.current_trade = main_trade_state

            threading.Thread(
                target=monitor_trade,
                args=(client, symbol, main_trade_state, tick_size, CMD_ARGS.telegram_token, CMD_ARGS.chat_id, int(time.time() * 1000)),
                daemon=True
            ).start()

            log(f"✅ Main leg monitoring started", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

            # === INSURANCE LEG ===
            if INSURANCE_ENABLED:
                log(f"Waiting {INSURANCE_DELAY_MS}ms before insurance entry...", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                time.sleep(INSURANCE_DELAY_MS / 1000.0)

                # Use the same dynamic virtual capital (already split above)
                ins_margin_available = virtual_insurance * MARGIN_USAGE_PCT * SAFETY_FACTOR

                # Insurance quantity: match MAIN quantity (same size)
                qty_insurance = actual_qty_main
                max_qty_by_margin_ins = (ins_margin_available * MAX_LEVERAGE) / entry_price

                if qty_insurance > max_qty_by_margin_ins:
                    qty_insurance = max_qty_by_margin_ins

                qty_insurance = min(qty_insurance, Decimal("25"))
                qty_insurance = quantize_qty(qty_insurance, step_size)

                log(f"INSURANCE: Virtual=${virtual_insurance:.2f} | Target Qty={qty_insurance:.5f} SOL",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

                if (qty_insurance * entry_price) < min_notional:
                    log(f"Insurance quantity too small (${qty_insurance * entry_price:.2f} < ${min_notional}) → SKIPPING INSURANCE",
                        CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                else:
                    insurance_position_side = "SHORT" if original_side == "BUY" else "LONG"
                    insurance_side_order = "SELL" if original_side == "BUY" else "BUY"

                    actual_qty_insurance = Decimal("0")
                    actual_insurance_entry = actual_fill_price_dec

                    try:
                        order_res_insurance = client.send_signed_request("POST", "/fapi/v1/order", {
                            "symbol": symbol,
                            "side": insurance_side_order,
                            "type": "MARKET",
                            "quantity": str(qty_insurance),
                            "positionSide": insurance_position_side
                        })
                        log(f"Insurance order placed. OrderId: {order_res_insurance.get('orderId')}",
                            CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    except Exception as e:
                        log(f"Insurance order error: {e}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

                    # Wait for insurance fill
                    start_time_ins = time.time()
                    max_wait = 90
                    position_confirmed = False

                    while not bot_state.STOP_REQUESTED and (time.time() - start_time_ins) < max_wait:
                        pos_amt = get_position_amt_for_side(client, symbol, insurance_position_side)
                        if abs(pos_amt) > Decimal('0.0005'):
                            actual_qty_insurance = abs(pos_amt)
                            position_confirmed = True
                            log(f"✅ Insurance fill detected! Qty: {actual_qty_insurance:.5f} SOL",
                                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

                            positions = fetch_open_positions_details(client, symbol)
                            for pos in positions:
                                if pos.get("positionSide") == insurance_position_side:
                                    actual_insurance_entry = Decimal(str(pos.get("entryPrice", "0")))
                                    break
                            break
                        time.sleep(1.5)

                    if not position_confirmed or actual_qty_insurance <= Decimal('0'):
                        final_pos = get_position_amt_for_side(client, symbol, insurance_position_side)
                        if abs(final_pos) > Decimal('0.0005'):   # ✅ Use abs()
                            actual_qty_insurance = abs(final_pos)
                            position_confirmed = True
                            log(f"✅ Insurance found via final check! Qty: {actual_qty_insurance:.5f}",
                                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                            positions = fetch_open_positions_details(client, symbol)
                            for pos in positions:
                                if pos.get("positionSide") == insurance_position_side:
                                    actual_insurance_entry = Decimal(str(pos.get("entryPrice", "0")))
                                    break

                    if position_confirmed and actual_qty_insurance > Decimal('0'):
                        insurance_trade_state = TradeState()
                        insurance_trade_state.active = True
                        insurance_trade_state.leg_type = "INSURANCE"
                        insurance_trade_state.side = "LONG" if insurance_side_order == "BUY" else "SHORT"
                        insurance_trade_state.entry_price = actual_insurance_entry
                        insurance_trade_state.qty = actual_qty_insurance
                        insurance_trade_state.risk = actual_insurance_entry * SL_PCT
                        insurance_trade_state.trail_activation_price = None
                        insurance_trade_state.trail_activated = False

                        # === Compute SL/TP based on MAIN direction (original_side) ===
                        R = actual_insurance_entry * SL_PCT
                        if original_side == "BUY":          # MAIN LONG → insurance SHORT
                            sl_price_dec = actual_insurance_entry + (R * INSURANCE_SL_MULT)
                            tp_price_dec = actual_insurance_entry - (R * INSURANCE_TP_MULT)
                            sl_rounding = ROUND_UP
                            tp_rounding = ROUND_DOWN
                        else:                               # MAIN SHORT → insurance LONG
                            sl_price_dec = actual_insurance_entry - (R * INSURANCE_SL_MULT)
                            tp_price_dec = actual_insurance_entry + (R * INSURANCE_TP_MULT)
                            sl_rounding = ROUND_DOWN
                            tp_rounding = ROUND_UP

                        insurance_trade_state.sl = quantize_price(sl_price_dec, tick_size, sl_rounding)
                        insurance_trade_state.tp = quantize_price(tp_price_dec, tick_size, tp_rounding)

                        # Place protective orders for INSURANCE (SL + TP only, no trailing)
                        place_orders(client, symbol, insurance_trade_state, tick_size, CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

                        # Send telegram for INSURANCE
                        send_trade_telegram({
                            'symbol': symbol,
                            'side': insurance_trade_state.side,
                            'entry': insurance_trade_state.entry_price,
                            'sl': insurance_trade_state.sl,
                            'tp': insurance_trade_state.tp,
                            'qty': insurance_trade_state.qty,
                            'leverage': 5
                        }, "INSURANCE", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

                        bot_state.insurance_trade = insurance_trade_state
                        bot_state.INSURANCE_ACTIVE = True

                        threading.Thread(
                            target=monitor_trade,
                            args=(client, symbol, insurance_trade_state, tick_size,
                                  CMD_ARGS.telegram_token, CMD_ARGS.chat_id, int(time.time() * 1000)),
                            daemon=True
                        ).start()
                        log(f"✅ Insurance leg monitoring started", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    else:
                        log("❌ Insurance leg failed to fill. Continuing with main leg only.",
                            CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

    elif order_type == 'STOP_MARKET':
        # Update SL for the appropriate leg
        stop_price_str = data.get('stopPrice')
        if not stop_price_str:
            log("No stopPrice in alert")
            return

        stop_price = Decimal(stop_price_str)
        stop_price_quant = quantize_price(stop_price, tick_size)

        leg = data.get('leg', 'MAIN').upper()

        with bot_state._trade_lock:
            if leg == "MAIN":
                trade_state = bot_state.current_trade
            else:
                trade_state = bot_state.insurance_trade

        if not trade_state or not trade_state.active:
            log(f"No active {leg} leg position, ignoring SL")
            return

        expected_close_side = "SELL" if trade_state.side == "LONG" else "BUY"
        if side != expected_close_side:
            log(f"SL side mismatch: expected {expected_close_side}, got {side}")
            return

        if trade_state.sl_algo_id:
            try:
                client.cancel_algo_order(symbol, trade_state.sl_algo_id)
            except:
                pass

        sl_order = client.place_stop_market(symbol, side, trade_state.qty, stop_price_quant,
                                            reduce_only=True, position_side=trade_state.side.upper())
        if sl_order and sl_order.get("algoId"):
            trade_state.sl_algo_id = sl_order["algoId"]
            trade_state.sl = stop_price_quant
            log(f"{leg} SL placed/updated at {stop_price_quant}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

    elif order_type == 'TAKE_PROFIT_MARKET':
        # Update TP for the appropriate leg
        tp_price_str = data.get('takeProfit')
        if not tp_price_str:
            log("No takeProfit in alert")
            return

        tp_price = Decimal(tp_price_str)
        tp_price_quant = quantize_price(tp_price, tick_size)

        leg = data.get('leg', 'MAIN').upper()

        with bot_state._trade_lock:
            if leg == "MAIN":
                trade_state = bot_state.current_trade
            else:
                trade_state = bot_state.insurance_trade

        if not trade_state or not trade_state.active:
            log(f"No active {leg} leg position, ignoring TP")
            return

        expected_close_side = "SELL" if trade_state.side == "LONG" else "BUY"
        if side != expected_close_side:
            log(f"TP side mismatch: expected {expected_close_side}, got {side}")
            return

        if trade_state.tp_algo_id:
            try:
                client.cancel_algo_order(symbol, trade_state.tp_algo_id)
            except:
                pass

        tp_order = client.place_take_profit_market(symbol, side, trade_state.qty, tp_price_quant,
                                                   reduce_only=True, position_side=trade_state.side.upper())
        if tp_order and tp_order.get("algoId"):
            trade_state.tp_algo_id = tp_order["algoId"]
            trade_state.tp = tp_price_quant
            log(f"{leg} TP placed/updated at {tp_price_quant}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

# ------------------- WEBHOOK ENDPOINT -------------------
# ------------------- WEBHOOK SETUP (REPLICATED FROM PRODUCTION) -------------------
app = Flask(__name__)

# Removed ProxyFix to match deepdenise33's simplicity

@app.route('/health', methods=['GET', 'HEAD'])
def health():
    return jsonify({"status": "ok", "pid": os.getpid()}), 200

@app.route('/webhook', methods=['POST'])
def webhook():
    if bot_state.STOP_REQUESTED:
        return "Bot stopped", 503

    # Direct data extraction (Replica style)
    data = request.get_json(force=True, silent=True)
    
    if not data:
        raw_body = request.get_data(as_text=True)
        try:
            cleaned = raw_body.strip().lstrip('\ufeff')
            data = json.loads(cleaned)
        except Exception as e:
            log(f"FAILED: No valid JSON - Raw: {raw_body[:100]}")
            return "Invalid JSON payload", 400

    # Security Check
    uid = data.get('uid')
    if uid != my_uid:
        log(f"Invalid UID: {uid}")
        return "Invalid UID", 403

    # Execute Trade Logic
    threading.Thread(target=lambda: (time.sleep(0.1), process_alert(data)), daemon=True).start()

    return jsonify({"status": "ok"}), 200
# ------------------- SCHEDULER -------------------
def run_scheduler(bot_token: Optional[str], chat_id: Optional[str]):
    global bot_state
    last_month: Optional[int] = None

    def daily_reset_job():
        try:
            current_balance = fetch_balance(bot_state.client)
            if current_balance > 0:
                bot_state.account_size = current_balance
                bot_state.daily_start_equity = current_balance
                log(f"DAILY RESET @ 00:00 UTC | New start equity: ${current_balance:.2f}", bot_token, chat_id)
        except Exception as e:
            log(f"Daily reset failed: {e}", bot_token, chat_id)

    def daily_memory_log():
        try:
            process = psutil.Process()
            mem_mb = process.memory_info().rss / 1024 / 1024
            obj_count = len(gc.get_objects())
            log(f"📊 DAILY MEMORY USAGE: {mem_mb:.1f} MB | Objects: {obj_count:,}", bot_token, chat_id)
            if mem_mb > 800:
                log(f"⚠️ High memory warning: {mem_mb:.1f} MB", bot_token, chat_id)
        except Exception as e:
            log(f"❌ Memory log error: {e}", bot_token, chat_id)

    def weekly_reset_job():
        bot_state.CONSEC_LOSSES = 0
        bot_state.consec_loss_guard_alert_sent = False
        log("WEEKLY RESET: Consecutive loss streak cleared.", bot_token, chat_id)

    def check_monthly_report():
        nonlocal last_month
        current_date = datetime.now(timezone.utc)
        if current_date.day == 1 and (last_month is None or current_date.month != last_month):
            send_monthly_report(bot_token, chat_id)
            last_month = current_date.month

    def daily_restart_job():
        global bot_state, CMD_ARGS

        log("🔄 Daily restart triggered...", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

        try:
            save_bot_state()
            log("💾 Bot state saved before restart", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
        except Exception as e:
            log(f"⚠️ State save warning: {e}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

        has_position = has_any_active_leg()

        if has_position:
            msg = f"🔄 Daily restart - Positions + SL/TP orders preserved"
            telegram_post(CMD_ARGS.telegram_token, CMD_ARGS.chat_id, msg)
        else:
            telegram_post(CMD_ARGS.telegram_token, CMD_ARGS.chat_id, "🔄 Daily restart - no active positions")

        time.sleep(3)

        log("🚀 Executing process restart now", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

        import os, sys
        os.execv(sys.executable, [sys.executable] + sys.argv)

    schedule.every().day.at("00:00").do(daily_reset_job)
    schedule.every().monday.at("00:00").do(weekly_reset_job)
    schedule.every().day.at("00:01").do(check_monthly_report)
    schedule.every().day.at("00:01").do(daily_memory_log)
    schedule.every().day.at("00:02").do(daily_restart_job)
    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot_token, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot_token, chat_id))

    log("📅 Scheduler initialized - Daily restart at 00:02 UTC", bot_token, chat_id)

    while not bot_state.STOP_REQUESTED:
        schedule.run_pending()
        time.sleep(1)

# ------------------- STATE PERSISTENCE -------------------
STATE_FILE = 'bot_state.pkl'

def save_bot_state():
    global bot_state
    try:
        persistent_data = {
            'pnl_data': bot_state.pnl_data[-1000:] if hasattr(bot_state, 'pnl_data') else [],
            'last_trade_date': getattr(bot_state, 'last_trade_date', None),
            'CONSEC_LOSSES': getattr(bot_state, 'CONSEC_LOSSES', 0),
            'weekly_peak_equity': getattr(bot_state, 'weekly_peak_equity', None),
            'weekly_start_time': getattr(bot_state, 'weekly_start_time', None),
            'account_size': getattr(bot_state, 'account_size', None),
            'daily_start_equity': getattr(bot_state, 'daily_start_equity', None),
            'INSURANCE_ACTIVE': getattr(bot_state, 'INSURANCE_ACTIVE', False)
        }

        if bot_state.INSURANCE_ACTIVE and bot_state.insurance_trade:
            persistent_data['insurance_trade'] = {
                'active': bot_state.insurance_trade.active,
                'side': bot_state.insurance_trade.side,
                'qty': float(bot_state.insurance_trade.qty) if bot_state.insurance_trade.qty else None,
                'entry_price': float(bot_state.insurance_trade.entry_price) if bot_state.insurance_trade.entry_price else None,
                'sl': float(bot_state.insurance_trade.sl) if bot_state.insurance_trade.sl else None,
                'tp': float(bot_state.insurance_trade.tp) if bot_state.insurance_trade.tp else None,
            }

        with open(STATE_FILE, 'wb') as f:
            pickle.dump(persistent_data, f)
        log("💾 Bot state saved to disk", None, None)
    except Exception as e:
        log(f"❌ Failed to save state: {e}", None, None)

def load_bot_state():
    """Minimal state load - only restore PNL, NOT trade states (EDISON style)"""
    global bot_state
    
    if not os.path.exists(STATE_FILE):
        log("📂 No saved state found - starting fresh", None, None)
        return
    
    try:
        with open(STATE_FILE, 'rb') as f:
            data = pickle.load(f)
        
        # ONLY restore safe data (PNL and statistics)
        bot_state.pnl_data = data.get('pnl_data', [])
        bot_state.last_trade_date = data.get('last_trade_date')
        bot_state.CONSEC_LOSSES = data.get('CONSEC_LOSSES', 0)
        bot_state.weekly_peak_equity = data.get('weekly_peak_equity')
        bot_state.weekly_start_time = data.get('weekly_start_time')
        bot_state.account_size = data.get('account_size')
        bot_state.daily_start_equity = data.get('daily_start_equity')
        
        # CRITICAL: NEVER restore trade states from file
        # Always verify with exchange first
        bot_state.current_trade = None
        bot_state.insurance_trade = None
        bot_state.INSURANCE_ACTIVE = False
        
        log(f"💾 Loaded {len(bot_state.pnl_data)} trades (trade states cleared - will verify with exchange)", 
            None, None)
        
    except Exception as e:
        log(f"❌ Failed to load state: {e} - starting fresh", None, None)
        # Backup corrupted state
        if os.path.exists(STATE_FILE):
            backup_name = f"{STATE_FILE}.corrupted.{int(time.time())}"
            try:
                os.rename(STATE_FILE, backup_name)
            except:
                pass

def verify_and_clear_stale_state(client, symbol, telegram_bot=None, telegram_chat_id=None):
    """
    EDISON-STYLE: Verify positions exist on Binance before trusting saved state.
    If no positions, clear local state. If positions exist, they'll be recovered.
    """
    global bot_state
    
    # Skip if no client yet
    if not client or not symbol:
        return
    
    try:
        # Check REAL positions on Binance
        positions = fetch_open_positions_details(client, symbol)
        has_any_position = False
        
        for pos in positions:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt != Decimal('0'):
                has_any_position = True
                break
        
        # If NO positions on exchange, clear ALL local trade state
        if not has_any_position:
            if bot_state.current_trade or bot_state.insurance_trade or bot_state.INSURANCE_ACTIVE:
                log("🧹 EDISON-STYLE: No positions on Binance - clearing stale local state", 
                    telegram_bot, telegram_chat_id)
                bot_state.current_trade = None
                bot_state.insurance_trade = None
                bot_state.INSURANCE_ACTIVE = False
                
                # Rename stale state file (don't delete, just backup)
                if os.path.exists(STATE_FILE):
                    backup_name = f"{STATE_FILE}.stale.{int(time.time())}"
                    try:
                        os.rename(STATE_FILE, backup_name)
                        log(f"📁 Backed up stale state to {backup_name}", telegram_bot, telegram_chat_id)
                    except:
                        pass
        else:
            log(f"✅ Positions exist on Binance - will recover if needed", telegram_bot, telegram_chat_id)
            
    except Exception as e:
        log(f"⚠️ State verification failed (will assume clean): {e}", telegram_bot, telegram_chat_id)
        # On error, safer to clear state
        bot_state.current_trade = None
        bot_state.insurance_trade = None
        bot_state.INSURANCE_ACTIVE = False
        
# ==================== TELEGRAM COMMAND HANDLERS ====================
import asyncio

async def cmd_restart(update, context):
    global bot_state, CMD_ARGS, LOCK_HANDLE

    chat_id = str(update.effective_chat.id)
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return

    has_position = has_any_active_leg()

    if has_position:
        await update.message.reply_text(
            "🔄 *Safe Restart Initiated*\n\n"
            "📊 Active positions + SL/TP/Trailing orders will be **preserved**\n"
            "Bot will restart and recover monitoring automatically\n\n"
            "Restarting in 3 seconds...",
            parse_mode='Markdown'
        )
    else:
        await update.message.reply_text("🔄 Restarting bot now...")

    try:
        save_bot_state()
        await update.message.reply_text("💾 State saved successfully")
    except Exception as e:
        await update.message.reply_text(f"⚠️ State save warning: {e}")

    log("🔧 Manual safe restart via Telegram", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

    await asyncio.sleep(3)

    try:
        if LOCK_HANDLE:
            LOCK_HANDLE.close()
    except Exception as e:
        print(f"Error closing lock handle: {e}")

    log("🚀 Executing process restart now...", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)

    import os, sys
    os.execv(sys.executable, [sys.executable] + sys.argv)

async def cmd_status(update, context):
    global bot_state, CMD_ARGS

    chat_id = str(update.effective_chat.id)
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return

    balance = fetch_balance(bot_state.client) if bot_state.client else Decimal("0")
    pos_amt = get_position_amt(bot_state.client, CMD_ARGS.symbol) if bot_state.client else Decimal("0")

    process = psutil.Process()
    mem_mb = process.memory_info().rss / 1024 / 1024

    main_status = "No active trade"
    if bot_state.current_trade and bot_state.current_trade.active:
        main_status = f"{bot_state.current_trade.side} @ {bot_state.current_trade.entry_price:.2f} | Qty: {bot_state.current_trade.qty:.4f}"

    insurance_status = "Not active"
    if bot_state.INSURANCE_ACTIVE and bot_state.insurance_trade and bot_state.insurance_trade.active:
        insurance_status = f"{bot_state.insurance_trade.side} @ {bot_state.insurance_trade.entry_price:.2f} | Qty: {bot_state.insurance_trade.qty:.4f}"

    status_lines = [
        f"🤖 *DeepDenise Hedge Bot Status*",
        f"",
        f"📊 *Balance:* `${float(balance):.2f}`",
        f"📈 *Net Position:* `{float(pos_amt):.2f} SOL`",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"📌 *MAIN Leg:* `{main_status}`",
        f"🛡️ *INSURANCE Leg:* `{insurance_status}`",
        f"━━━━━━━━━━━━━━━━━━━━",
        f"💾 *Trades Stored:* `{len(bot_state.pnl_data)}`",
        f"🧠 *Memory:* `{mem_mb:.1f} MB`",
        f"🆔 *PID:* `{os.getpid()}`",
        f"⏰ *Uptime:* `{datetime.now(timezone.utc) - bot_state.start_time}`" if hasattr(bot_state, 'start_time') else ""
    ]

    await update.message.reply_text("\n".join(status_lines), parse_mode='Markdown')

async def cmd_balance(update, context):
    global bot_state, CMD_ARGS

    chat_id = str(update.effective_chat.id)
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return

    balance = fetch_balance(bot_state.client) if bot_state.client else Decimal("0")
    await update.message.reply_text(f"💰 Current Balance: `${float(balance):.2f}` USDT")

async def cmd_help(update, context):
    chat_id = str(update.effective_chat.id)
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return

    help_text = (
        "🤖 *Available Commands:*\n\n"
        "/status - Show bot status (balance, positions, memory)\n"
        "/balance - Show current balance only\n"
        "/restart - Gracefully restart the bot (preserves positions)\n"
        "/help - Show this help message\n\n"
        f"*Insurance Mode:* {'ENABLED' if INSURANCE_ENABLED else 'DISABLED'} (Full Hedge)\n"
        f"*Main Risk:* {BASE_RISK_PCT*100:.1f}% | *Safety Factor:* {SAFETY_FACTOR*100:.0f}%\n"
        f"*Dynamic Split:* 50/50 of actual balance"
    )
    await update.message.reply_text(help_text, parse_mode='Markdown')

async def unknown(update, context):
    chat_id = str(update.effective_chat.id)
    if chat_id != str(CMD_ARGS.chat_id):
        return
    if update.message and update.message.text and update.message.text.startswith('/'):
        await update.message.reply_text("❓ Unknown command. Try /help")

# ------------------- MAIN -------------------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="DeepDenise Hedge Bot - Webhook + Dual Leg (MAIN + INSURANCE)")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", required=True, help="Telegram Bot Token")
    parser.add_argument("--chat-id", required=True, help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol")
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--base-url", default=None)
    parser.add_argument("--news-guard", action="store_true", help="Enable news guard (disabled by default)")
    parser.add_argument("--disable-insurance", action="store_true", help="Disable insurance leg")
    parser.add_argument("--port", type=int, default=8080, help="Webhook port")
    args = parser.parse_args()

    CMD_ARGS = args

    if args.disable_insurance:
        INSURANCE_ENABLED = False
        print("[CONFIG] Insurance leg DISABLED via --disable-insurance")

    if args.news_guard:
        NEWS_GUARD_ENABLED = True
        print("[CONFIG] News Guard ENABLED via --news-guard")

    LOCK_HANDLE = acquire_lock()

    init_pnl_log()
    load_bot_state()

    # Reset weekly DD guard on startup (disabled anyway)
    bot_state.weekly_start_time = None
    bot_state.weekly_peak_equity = None
    bot_state.weekly_dd_alert_triggered = False

    _shutdown_done = False

    def graceful_shutdown(sig=None, frame=None, preserve_positions=True):
        global _shutdown_done, bot_state, args, LOCK_HANDLE, flask_server

        if _shutdown_done:
            return
        _shutdown_done = True

        reason = {
            signal.SIGINT: "Ctrl+C",
            signal.SIGTERM: "SIGTERM",
        }.get(sig, "Clean exit")

        if os.path.exists("/tmp/STOP_BOT_NOW"):
            reason = "KILL FLAG / Manual stop"
            preserve_positions = False

        log(f"🛑 Shutdown requested ({reason}) | Preserve positions: {preserve_positions}",
            args.telegram_token, args.chat_id)

        save_bot_state()

        try:
            flask_server.stop()
            time.sleep(3)
        except Exception as e:
            log(f"Flask server stop error: {e}", args.telegram_token, args.chat_id)

        if preserve_positions and bot_state.client and args.symbol:
            log("🔄 SAFE RESTART — Preserving positions + protective orders on Binance",
                args.telegram_token, args.chat_id)
            try:
                bot_state.client.cancel_all_open_orders(args.symbol)
                log("✅ Loose orders cleaned. SL/TP/Trailing orders preserved.",
                    args.telegram_token, args.chat_id)
            except Exception as e:
                log(f"Order cleanup warning: {e}", args.telegram_token, args.chat_id)
        else:
            log("🛑 FULL STOP — Closing all positions", args.telegram_token, args.chat_id)
            _request_stop(symbol=args.symbol, telegram_bot=args.telegram_token, telegram_chat_id=args.chat_id)

        bot_state.current_trade = None
        bot_state.insurance_trade = None
        bot_state.INSURANCE_ACTIVE = False

        try:
            if LOCK_HANDLE:
                LOCK_HANDLE.close()
            if os.path.exists(LOCK_FILE):
                os.unlink(LOCK_FILE)
        except:
            pass

        log(f"BOT SHUTDOWN COMPLETE - {reason}", args.telegram_token, args.chat_id)
        os._exit(0)

    def signal_handler_wrapper(sig, frame):
        graceful_shutdown(sig, frame, preserve_positions=False)

    signal.signal(signal.SIGINT, signal_handler_wrapper)
    signal.signal(signal.SIGTERM, signal_handler_wrapper)
    atexit.register(lambda: graceful_shutdown(None, None, preserve_positions=False))

    # Immortal loop
    while True:
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            log("STOP_BOT_NOW flag detected – shutting down permanently", args.telegram_token, args.chat_id)
            graceful_shutdown()
            break

        try:
            bot_state.client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)

            # Force Hedge Mode
            try:
                bot_state.client.send_signed_request("POST", "/fapi/v1/positionSide/dual", {"dualSidePosition": "true"})
                log("✅ Hedge Mode enabled for dual legs", args.telegram_token, args.chat_id)
            except Exception as e:
                log(f"⚠️ Could not set Hedge Mode: {e}", args.telegram_token, args.chat_id)

            balance = fetch_balance(bot_state.client)
            bot_state.account_size = balance
            bot_state.daily_start_equity = balance

            leverage_to_set = 5
            bot_state.client.set_leverage(args.symbol, leverage_to_set)
            log(f"Set leverage to {leverage_to_set}x", args.telegram_token, args.chat_id)
            log(f"Balance: ${balance:.2f}", args.telegram_token, args.chat_id)

            if NEWS_GUARD_ENABLED:
                threading.Thread(target=news_heartbeat, daemon=True).start()
                log("News guard: ENABLED", args.telegram_token, args.chat_id)
            else:
                log("News guard: DISABLED", args.telegram_token, args.chat_id)

            log(f"STARTING WEBHOOK HEDGE BOT → {args.symbol} | {'LIVE' if args.live else 'TESTNET'} | Insurance: {'ENABLED' if INSURANCE_ENABLED else 'DISABLED'}",
                args.telegram_token, args.chat_id)
            log(f"Dynamic Split: 50/50 of actual balance | Guards: ALL DISABLED",
                args.telegram_token, args.chat_id)

            filters = get_symbol_filters(bot_state.client, args.symbol)
            tick_size = filters['tickSize']

            recover_existing_positions(bot_state.client, args.symbol, tick_size,
                                      args.telegram_token, args.chat_id)

            mem_mb = psutil.Process().memory_info().rss / 1024 / 1024
            log(f"🧠 Fresh process memory: {mem_mb:.1f} MB", args.telegram_token, args.chat_id)
            log(f"🚀 Bot started - PID: {os.getpid()}", args.telegram_token, args.chat_id)

            threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()

            # Start Flask webhook server
            flask_server.start(args.port)
            log(f"Webhook listening on port {args.port}", args.telegram_token, args.chat_id)

            # Telegram command listener
            if args.telegram_token and args.chat_id:
                try:
                    requests.post(
                        f"https://api.telegram.org/bot{args.telegram_token}/deleteWebhook",
                        timeout=5
                    )
                    log("Cleaned up any old Telegram webhook/polling sessions", args.telegram_token, args.chat_id)
                    time.sleep(2)
                except Exception as e:
                    log(f"Cleanup old Telegram sessions failed: {e}", args.telegram_token, args.chat_id)

                from telegram.ext import Application, CommandHandler, MessageHandler, filters as tg_filters
                from telegram import Update

                application = Application.builder().token(args.telegram_token).build()

                application.add_handler(CommandHandler("restart", cmd_restart))
                application.add_handler(CommandHandler("status", cmd_status))
                application.add_handler(CommandHandler("balance", cmd_balance))
                application.add_handler(CommandHandler("help", cmd_help))
                application.add_handler(MessageHandler(tg_filters.COMMAND, unknown))

                log("📱 Telegram command listener starting in main thread (/restart, /status, /balance, /help)",
                    args.telegram_token, args.chat_id)

                try:
                    application.run_polling(
                        drop_pending_updates=True,
                        stop_signals=None,
                        allowed_updates=Update.ALL_TYPES
                    )
                except Exception as e:
                    log(f"Telegram polling stopped: {e}", args.telegram_token, args.chat_id)

            log("Bot stopped cleanly – exiting.", args.telegram_token, args.chat_id)
            break

        except Exception as e:
            error_msg = f"BOT CRASHED → RESTARTING IN 15s\n{traceback.format_exc()}"
            try:
                log(error_msg, args.telegram_token, args.chat_id)
            except:
                print(error_msg)
            time.sleep(15)
