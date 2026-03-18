## FINAL PRODUCTION VERSION — ALL 22 FIXES + WS → POLLING FALLBACK + WEBHOOK INTEGRATION
## FIXED: Trailing stop placed immediately at entry with correct callback rate
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
import numpy as np
from flask import Flask, request, jsonify
import io
# ==================== TELEGRAM COMMAND LISTENER ====================
from telegram import Update
from telegram.ext import Application, CommandHandler, ContextTypes, MessageHandler, filters
import asyncio
# Fix Windows console encoding
if sys.platform == "win32":
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')
# ------------------- WEBHOOK SETUP -------------------
app = Flask(__name__)
my_uid = "6e8769164ae8eedf74dcaaeb86000f8e03d166bf5181f8eb283a4bb90e6574a2"

# Global args for webhook access
CMD_ARGS = None

# ------------------- CONFIGURATION -------------------
RISK_PCT = Decimal("0.0378")
SL_PCT = Decimal("0.0075")  # 0.75% from Pine Script
TP_MULT = Decimal("9")
TRAIL_TRIGGER_MULT = Decimal("1.25")  # Activate trailing after 1.25R profit
TRAIL_DISTANCE_MULT = Decimal("2")    # Trail by 2R
VOL_SMA_PERIOD = 16
RSI_PERIOD = 14
MAX_TRADES_PER_DAY = 1
INTERVAL_DEFAULT = "45m"
ORDER_FILL_TIMEOUT = 15
POSITION_CHECK_INTERVAL = 60
REQUEST_TIMEOUT = 30
MAX_RETRIES = 5
RECOVERY_CHECK_INTERVAL = 10
POLLING_INTERVAL = 3

# === CONFIG: BLACKOUT WINDOWS (UTC) ===
NEWS_BLACKOUT_WINDOWS = [
    (4, (12, 25), (13, 5)),  # Friday 12:30–13:00 UTC (NFP)
    (2, (18, 55), (19, 35)),  # Wednesday 19:00–19:30 UTC (FOMC)
]

# === CONFIG: LIVE API ===
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

NEWS_GUARD_ENABLED = False
MAX_ENTRY_SLIPPAGE_PCT = Decimal("0.002")
LOCK_FILE = os.path.join(os.getenv('TEMP', '/tmp'), 'sol_rsi_bot_webhook.lock')
BASE_RISK_PCT = Decimal("0.0378")
MAX_LEVERAGE = Decimal("9")
ENABLE_WEEKLY_SCALING = True
HALF_R_THRESHOLD = Decimal("0.00375")

# ------------------- BOT STATE CLASS -------------------
class BotState:
    def __init__(self):
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
        
        # News guard state
        self._news_lock = threading.Lock()
        self._news_cache: List[Dict[str, Any]] = []
        self._cache_ts = Decimal("0.0")
        self.NEWS_LOCK = False
        self._last_news_block_reason: Optional[str] = None
        
        # Risk management
        self.weekly_peak_equity: Optional[Decimal] = None
        self.weekly_start_time: Optional[datetime] = None
        self.CONSEC_LOSSES = 0
        self.USE_CONSEC_LOSS_GUARD = True
        self.MAX_CONSEC_LOSSES = 3
        self.weekly_dd_alert_triggered = False
        
        # Trading state - SINGLE TRADE STATE
        self.current_trade: Optional['TradeState'] = None
        
        self.is_testnet = True
        self.consec_loss_guard_alert_sent = False
        self.account_size: Optional[Decimal] = None

        # ADD THESE MISSING ATTRIBUTES:
        self.daily_start_equity: Optional[Decimal] = None
        self._last_symbol_setup: Optional[str] = None  # For dynamic selection

        self._active_websockets: Dict[str, Any] = {}  # ADD THIS

        # ADD THESE TWO LINES:
        self.RESTART_REQUESTED = False
        self._restart_lock = threading.Lock()

        # ADD THIS LINE:
        self.start_time = datetime.now(timezone.utc)

bot_state = BotState()

# ------------------- TRADE STATE WITH DECIMAL -------------------
class TradeState:
    def __init__(self):
        self.active = False
        self.entry_price: Optional[Decimal] = None
        self.qty: Optional[Decimal] = None
        self.side: Optional[str] = None
        self.entry_close_time: Optional[int] = None
        
        # Order IDs
        self.sl_algo_id: Optional[int] = None
        self.tp_algo_id: Optional[int] = None
        self.trail_algo_id: Optional[int] = None
        
        # Price levels
        self.sl: Optional[Decimal] = None
        self.tp: Optional[Decimal] = None
        self.trail_activation: Optional[Decimal] = None  # Price at which trail activates (1.25R)
        self.current_trail_stop: Optional[Decimal] = None
        
        # Trail tracking
        self.trail_activated = False  # Will be managed by Binance, but we track for info
        self.entry_R: Optional[Decimal] = None  # R value for calculations
        
        # Risk
        self.risk: Optional[Decimal] = None
LOCK_HANDLE = None  # Add this line
# ------------------- SINGLE INSTANCE LOCK WITH PID CHECK (IMPROVED) -------------------
def acquire_lock():
    """Acquire single instance lock with PID check to prevent stale locks."""
    global LOCK_HANDLE
    
    try:
        # Check if lock file exists and contains a valid PID
        if os.path.exists(LOCK_FILE):
            try:
                with open(LOCK_FILE, 'r') as f:
                    pid_str = f.read().strip()
                    if pid_str and pid_str.isdigit():
                        pid = int(pid_str)
                        
                        # Special case: if it's the same PID as current process, it's a restart
                        if pid == os.getpid():
                            print(f"Same PID {pid} - this is a restart, continuing...")
                            # Just use the existing lock file
                            pass
                        else:
                            # Check if process is still running
                            process_exists = False
                            if platform.system() == "Windows":
                                import psutil
                                try:
                                    psutil.Process(pid)
                                    process_exists = True
                                except (psutil.NoSuchProcess, psutil.AccessDenied):
                                    process_exists = False
                            else:
                                # Unix: try sending signal 0 to check if process exists
                                try:
                                    os.kill(pid, 0)
                                    process_exists = True
                                except OSError:
                                    process_exists = False
                            
                            if process_exists:
                                # Process exists, another instance is running
                                print(f"Another instance is already running with PID {pid}! Exiting.")
                                sys.exit(1)
                            else:
                                # Process doesn't exist, stale lock file
                                print(f"Removing stale lock file from PID {pid}")
                                os.unlink(LOCK_FILE)
            except Exception as e:
                print(f"Error reading lock file: {e}")
                # If we can't read/parse the lock file, remove it and continue
                try:
                    os.unlink(LOCK_FILE)
                except:
                    pass
        
        # Create new lock file with current PID
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
            f.flush()
            os.fsync(f.fileno())  # Ensure it's written to disk
        
        print(f"Lock file created with PID {os.getpid()}")
        
        # On Unix systems, add file locking
        if platform.system() != "Windows":
            try:
                import fcntl
                lock_handle = open(LOCK_FILE, 'r+')
                fcntl.lockf(lock_handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                print(f"Exclusive file lock acquired")
                # Keep lock file open while bot runs
                return lock_handle
            except (IOError, OSError) as e:
                print(f"Failed to acquire file lock: {e}")
                # If we can't get the lock, another instance might have it
                # Check if it's our own PID
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
        # Directory may not exist
        os.makedirs(os.path.dirname(LOCK_FILE), exist_ok=True)
        with open(LOCK_FILE, 'w') as f:
            f.write(str(os.getpid()))
        return None
# ------------------- MEMORY CHECK -------------------
try:
    import psutil
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
    now = now_utc or datetime.now(timezone.utc)
    for wd, start, end in NEWS_BLACKOUT_WINDOWS:
        if wd is None or wd == now.weekday():
            if _time_in_window(now, start, end):
                return True, f"Blackout: {start}–{end} UTC"
    return False, None

# ------------------- NEWS HEARTBEAT -------------------
def _refresh_news():
    global bot_state
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
file_handler = logging.FileHandler('bot_webhook.log')  # Instead of 'bot.log'
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

def send_trade_telegram(trade_details: Dict[str, Any], bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"✅ NEW POSITION\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{trade_details['side']} {trade_details['symbol']}\n"
        f"Entry: {trade_details.get('entry', 'N/A'):.4f}\n"
        f"Qty: {trade_details['qty']:.3f}\n"
        f"SL: {trade_details.get('sl', 'N/A'):.4f}\n"
        f"TP: {trade_details.get('tp', 'N/A'):.4f}\n"
        f"Trail Activation: {trade_details.get('trail_activation', 'N/A'):.4f}\n"
        f"Callback Rate: {trade_details.get('callback_rate', 'N/A')}%\n"
        f"━━━━━━━━━━━━━━━━"
    )
    telegram_post(bot, chat_id, message)

def send_closure_telegram(symbol: str, side: str, entry_price: Decimal, exit_price: Decimal, qty: Decimal, pnl_usd: Decimal, pnl_r: Decimal, reason: str, bot: Optional[str], chat_id: Optional[str]):
    global bot_state
    message = (
        f"🔚 POSITION CLOSED\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{side} {symbol}\n"
        f"Entry: {entry_price:.4f}\n"
        f"Exit: {exit_price:.4f}\n"
        f"Reason: {reason}\n"
        f"PnL: ${pnl_usd:.2f} ({pnl_r:.2f}R)\n"
        f"Loss Streak: {bot_state.CONSEC_LOSSES}\n"
        f"━━━━━━━━━━━━━━━━"
    )
    telegram_post(bot, chat_id, message)

def send_trail_placed_telegram(symbol: str, side: str, activation: Decimal, callback: Decimal, bot: Optional[str], chat_id: Optional[str]):
    message = (
        f"🔄 TRAILING STOP PLACED\n"
        f"{side} {symbol}\n"
        f"Activation: {activation:.4f} ({TRAIL_TRIGGER_MULT}R)\n"
        f"Callback: {callback:.2f}% ({TRAIL_DISTANCE_MULT}R)"
    )
    telegram_post(bot, chat_id, message)

# ------------------- PNL LOGGING -------------------
PNL_FIELDS = ['date', 'trade_id', 'side', 'entry', 'exit', 'pnl_usd', 'pnl_r', 'loss_streak']

def init_pnl_log():
    if not os.path.exists(bot_state.PNL_LOG_FILE):
        with open(bot_state.PNL_LOG_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=PNL_FIELDS)
            writer.writeheader()

def log_pnl(trade_id: int, side: str, entry: Decimal, exit_price: Decimal, qty: Decimal, R: Decimal) -> Dict[str, Any]:
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
    
    if pnl_usd < Decimal("0") and is_full_loss:
        bot_state.CONSEC_LOSSES += 1
    else:
        bot_state.CONSEC_LOSSES = 0
    
    row = {
        'date': datetime.now(timezone.utc).isoformat(),
        'trade_id': trade_id,
        'side': side,
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

# ------------------- STOP HANDLER -------------------
def _request_stop(signum: Optional[int] = None, frame: Any = None, symbol: Optional[str] = None, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None):
    global bot_state
    with bot_state._stop_lock:
        if bot_state.STOP_REQUESTED:
            logger.info("Stop already requested; skipping duplicate cleanup.")
            return
        bot_state.STOP_REQUESTED = True
    
    bot_state._position_closure_in_progress = True
    log("Stop requested. Closing positions and cancelling orders...", telegram_bot, telegram_chat_id)
    
    if not bot_state.client or not symbol:
        log("Client or symbol not defined; skipping position closure.", telegram_bot, telegram_chat_id)
        bot_state._position_closure_in_progress = False
        return
    
    try:
        with bot_state._trade_lock:
            if bot_state.current_trade and bot_state.current_trade.active:
                pos_amt = get_position_amt(bot_state.client, symbol)
                if pos_amt != Decimal('0'):
                    side = "SELL" if pos_amt > Decimal('0') else "BUY"
                    qty = abs(pos_amt)
                    entry_price_dec = bot_state.current_trade.entry_price or Decimal('0')
                    
                    response = bot_state.client.send_signed_request("POST", "/fapi/v1/order", {
                        "symbol": symbol,
                        "side": side,
                        "type": "MARKET",
                        "quantity": str(qty)
                    })
                    log(f"Closed position: qty={qty} {side}", telegram_bot, telegram_chat_id)
                    
                    exit_price_dec = None
                    if response.get("orderId"):
                        time.sleep(0.8)
                        try:
                            trades = bot_state.client.send_signed_request("GET", "/fapi/v1/userTrades", {
                                "symbol": symbol,
                                "orderId": response["orderId"],
                                "limit": 10
                            })
                            if trades and len(trades) > 0:
                                exit_price_dec = Decimal(str(trades[-1]["price"]))
                        except:
                            pass
                    
                    if exit_price_dec is None:
                        ticker = bot_state.client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                        exit_price_dec = Decimal(str(ticker.get("price", "0")))
                    
                    pnl_row = log_pnl(
                        len(bot_state.pnl_data) + 1,
                        bot_state.current_trade.side or "UNKNOWN",
                        entry_price_dec,
                        exit_price_dec,
                        qty,
                        entry_price_dec * SL_PCT
                    )
                    
                    send_closure_telegram(
                        symbol=symbol,
                        side=bot_state.current_trade.side or "UNKNOWN",
                        entry_price=entry_price_dec,
                        exit_price=exit_price_dec,
                        qty=qty,
                        pnl_usd=Decimal(str(pnl_row['pnl_usd'])),
                        pnl_r=Decimal(str(pnl_row['pnl_r'])),
                        reason="Stop Requested",
                        bot=telegram_bot,
                        chat_id=telegram_chat_id
                    )
                    
                    bot_state.current_trade.active = False
    except Exception as e:
        log(f"Stop handler error: {str(e)}", telegram_bot, telegram_chat_id)
    
    with bot_state._stop_lock:
        if not bot_state._orders_cancelled:
            try:
                bot_state.client.cancel_all_open_orders(symbol)
                log(f"All open orders cancelled for {symbol}.", telegram_bot, telegram_chat_id)
            except Exception as e:
                log(f"Failed to cancel open orders: {e}", telegram_bot, telegram_chat_id)
            bot_state._orders_cancelled = True
    bot_state._position_closure_in_progress = False

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
        log(f"Using base URL: {self.base}")
    
    def set_leverage(self, symbol: str, leverage: int):
        params = {"symbol": symbol, "leverage": leverage}
        return self.send_signed_request("POST", "/fapi/v1/leverage", params)
    
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
        """Get open algo orders (STOP_MARKET, TAKE_PROFIT_MARKET, TRAILING_STOP_MARKET)"""
        try:
            response = self.send_signed_request("GET", "/fapi/v1/openAlgoOrders", {"symbol": symbol})
            return response if isinstance(response, list) else []
        except:
            return []
    
    def cancel_all_open_orders(self, symbol: str):
        """Cancel all regular and algo orders"""
        try:
            # Cancel regular orders
            self.send_signed_request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol, "recvWindow": 60000})
            log(f"[ZOMBIE KILLER] Regular orders cancelled for {symbol}")
            
            # Cancel algo orders
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
        """Cancel a specific algo order"""
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
    
    # ========== ALGO ORDER PLACEMENT ==========
    
    def place_algo_order(self, symbol: str, side: str, quantity: Decimal,
                         order_type: str, trigger_price: Optional[Decimal] = None,
                         activation_price: Optional[Decimal] = None, callback_rate: Optional[Decimal] = None,
                         reduce_only: bool = True) -> Any:
        params = {
            "algoType": "CONDITIONAL",
            "symbol": symbol,
            "side": side,
            "type": order_type,  # ← FIXED: lowercase 't' — this was the bug
            "quantity": str(quantity),
            "reduceOnly": "true" if reduce_only else "false",
            "timeInForce": "GTE_GTC",
            "priceProtect": "true"  # Add this
        }
        
        if trigger_price is not None:
            params["triggerPrice"] = str(trigger_price)  # ← Docs confirm: triggerPrice for SL/TP
            params["workingType"] = "CONTRACT_PRICE"
        if activation_price is not None:
            params["activatePrice"] = str(activation_price)
        if callback_rate is not None:
            params["callbackRate"] = str(callback_rate)
        
        return self.send_signed_request("POST", "/fapi/v1/algoOrder", params)
    
    def place_stop_market(self, symbol: str, side: str, quantity: Decimal, 
                          stop_price: Decimal, reduce_only: bool = True) -> Any:
        """Place STOP_MARKET algo order"""
        return self.place_algo_order(
            symbol=symbol,
            side=side,
            quantity=quantity,
            order_type="STOP_MARKET",
            trigger_price=stop_price,
            reduce_only=reduce_only
        )
    
    def place_take_profit_market(self, symbol: str, side: str, quantity: Decimal,
                                 stop_price: Decimal, reduce_only: bool = True) -> Any:
        """Place TAKE_PROFIT_MARKET algo order"""
        return self.place_algo_order(
            symbol=symbol,
            side=side,
            quantity=quantity,
            order_type="TAKE_PROFIT_MARKET",
            trigger_price=stop_price,
            reduce_only=reduce_only
        )
    
    def place_trailing_stop_market(self, symbol: str, side: str, quantity: Decimal,
                                   activation_price: Decimal, callback_rate: Decimal,
                                   reduce_only: bool = True) -> Any:
        """Place TRAILING_STOP_MARKET algo order"""
        return self.place_algo_order(
            symbol=symbol,
            side=side,
            quantity=quantity,
            order_type="TRAILING_STOP_MARKET",
            activation_price=activation_price,
            callback_rate=callback_rate,
            reduce_only=reduce_only
        )

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
    tick_size = Decimal(str(filters.get("PRICE_FILTER", {}).get("tickSize", "0.00000001")))
    
    bot_state.symbol_filters_cache[symbol] = {
        "stepSize": step_size,
        "tickSize": tick_size
    }
    return bot_state.symbol_filters_cache[symbol]

def quantize_qty(qty: Decimal, step_size: Decimal) -> Decimal:
    q = (qty // step_size) * step_size
    return q if q > Decimal("0") else step_size

def quantize_price(p: Decimal, tick_size: Decimal, rounding=ROUND_HALF_EVEN) -> Decimal:
    return p.quantize(tick_size, rounding=rounding)

# ------------------- POSITION HELPERS -------------------
def fetch_balance(client: BinanceClient) -> Decimal:
    try:
        data = client.send_signed_request("GET", "/fapi/v2/account")
        return Decimal(str(data.get("totalWalletBalance", "0")))
    except:
        return Decimal("0")

def get_position_amt(client: BinanceClient, symbol: str) -> Decimal:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp if isinstance(pos_resp, list) else pos_resp.get('data', []) if isinstance(pos_resp, dict) else []
        for p in positions:
            if p.get('symbol') == symbol:
                return Decimal(str(p.get('positionAmt', '0')))
        return Decimal('0')
    except:
        return Decimal('0')

def has_active_position(client: BinanceClient, symbol: str) -> bool:
    return get_position_amt(client, symbol) != Decimal('0')

def fetch_open_positions_details(client: BinanceClient, symbol: str) -> Optional[Dict[str, Any]]:
    try:
        pos_resp = client.send_signed_request("GET", "/fapi/v2/positionRisk", {"symbol": symbol})
        positions = pos_resp if isinstance(pos_resp, list) else pos_resp.get('data', []) if isinstance(pos_resp, dict) else []
        for p in positions:
            if p.get("symbol") == symbol:
                return p
        return None
    except:
        return None

def get_current_price(client: BinanceClient, symbol: str) -> Optional[Decimal]:
    try:
        ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
        return Decimal(str(ticker.get("price", "0")))
    except:
        return None

# ------------------- RECOVERY FUNCTIONS -------------------
def debug_and_recover_expired_orders(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, telegram_bot: Optional[str] = None, telegram_chat_id: Optional[str] = None) -> bool:
    global bot_state
    if bot_state._position_closure_in_progress or not trade_state.active:
        return False
    
    try:
        pos_amt = get_position_amt(client, symbol)
        if pos_amt == Decimal("0"):
            return False
        
        # Get open algo orders
        algo_orders = client.get_open_algo_orders(symbol)
        open_algo_ids = {o.get("algoId") for o in algo_orders if o.get("algoId")}
        
        recovered = False
        
        # Recover SL
        if trade_state.sl_algo_id and trade_state.sl_algo_id not in open_algo_ids and trade_state.sl:
            log(f"SL missing. Re-issuing...", telegram_bot, telegram_chat_id)
            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            new_sl = client.place_stop_market(symbol, close_side, trade_state.qty, trade_state.sl, reduce_only=True)
            if new_sl and new_sl.get("algoId"):
                trade_state.sl_algo_id = new_sl["algoId"]
                log(f"SL RECOVERED - algoId: {trade_state.sl_algo_id}", telegram_bot, telegram_chat_id)
                recovered = True
        
        # Recover TP
        if trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids and trade_state.tp:
            log(f"TP missing. Re-issuing...", telegram_bot, telegram_chat_id)
            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            new_tp = client.place_take_profit_market(symbol, close_side, trade_state.qty, trade_state.tp, reduce_only=True)
            if new_tp and new_tp.get("algoId"):
                trade_state.tp_algo_id = new_tp["algoId"]
                log(f"TP RECOVERED - algoId: {trade_state.tp_algo_id}", telegram_bot, telegram_chat_id)
                recovered = True
        
        # Recover Trailing Stop
        if trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids and trade_state.trail_activation:
            log(f"Trailing stop missing. Re-issuing...", telegram_bot, telegram_chat_id)
            close_side = "SELL" if trade_state.side == "LONG" else "BUY"
            callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
            new_trail = client.place_trailing_stop_market(
                symbol, close_side, trade_state.qty,
                activation_price=trade_state.trail_activation,
                callback_rate=callback_rate,
                reduce_only=True
            )
            if new_trail and new_trail.get("algoId"):
                trade_state.trail_algo_id = new_trail["algoId"]
                log(f"TRAILING STOP RECOVERED - algoId: {trade_state.trail_algo_id}", telegram_bot, telegram_chat_id)
                recovered = True
        
        return recovered
    except Exception as e:
        log(f"Recovery failed: {e}", telegram_bot, telegram_chat_id)
        return False

# ------------------- MONITOR TRADE -------------------
def monitor_trade(client: BinanceClient, symbol: str, trade_state: TradeState, tick_size: Decimal, telegram_bot: Optional[str], telegram_chat_id: Optional[str]):
    global bot_state
    last_recovery_check = Decimal("0")
    
    # CRITICAL FIX: Close any existing WebSocket for this symbol
    if hasattr(bot_state, '_active_websockets'):
        if symbol in bot_state._active_websockets:
            try:
                old_ws = bot_state._active_websockets[symbol]
                old_ws.close()
                log(f"Closed existing WebSocket for {symbol}", telegram_bot, telegram_chat_id)
            except:
                pass
    else:
        bot_state._active_websockets = {}
    
    log("Monitoring active trade...", telegram_bot, telegram_chat_id)
    # WebSocket setup for price feed
    ws = None
    ws_running = False
    price_queue = queue.Queue()
    
    def on_open(ws_app):
        try:
            subscribe_msg = {
                "method": "SUBSCRIBE",
                "params": [f"{symbol.lower()}@trade"],
                "id": 1
            }
            ws_app.send(json.dumps(subscribe_msg))
            log(f"WebSocket subscribed to {symbol} trade stream", telegram_bot, telegram_chat_id)
        except Exception as e:
            log(f"WS subscribe failed: {e}", telegram_bot, telegram_chat_id)

    def on_message(ws_app, message):
        try:
            data = json.loads(message)
            if data.get('e') == 'trade' and 'p' in data:
                price = Decimal(str(data['p']))
                if price > 0 and price < Decimal('1000'):
                    price_queue.put(price)
        except:
            pass

    def on_error(ws_app, error):
        if not bot_state._ws_failed:
            log(f"WebSocket error, switching to polling", telegram_bot, telegram_chat_id)
            bot_state._ws_failed = True

    def start_ws():
        nonlocal ws, ws_running
        if ws_running:
            return
        bot_state._active_websockets[symbol] = ws
        base_url = "wss://fstream.binance.com/ws" if client.use_live else "wss://stream.binancefuture.com/ws"
        ws = websocket.WebSocketApp(
            base_url,
            on_open=on_open,
            on_message=on_message,
            on_error=on_error
        )
        def run_ws():
            ws.run_forever(ping_interval=20, ping_timeout=10)
        threading.Thread(target=run_ws, daemon=True).start()
        ws_running = True
        time.sleep(1)  # Give connection time to establish

    start_ws()
    
    while trade_state.active and not bot_state.STOP_REQUESTED:
        try:
            # Recovery check
            if Decimal(str(time.time())) - last_recovery_check >= Decimal(str(RECOVERY_CHECK_INTERVAL)):
                debug_and_recover_expired_orders(client, symbol, trade_state, tick_size, telegram_bot, telegram_chat_id)
                last_recovery_check = Decimal(str(time.time()))
            
            # Position check
            pos_amt = get_position_amt(client, symbol)
            
            if pos_amt == Decimal('0') and trade_state.active:
                if bot_state._position_closure_in_progress:
                    trade_state.active = False
                    return
                
                log("Position closed. Determining exit details...", telegram_bot, telegram_chat_id)
                trade_state.active = False
                time.sleep(1.2)
                
                reason = "Unknown"
                exit_price_dec = None
                
                try:
                    algo_orders = client.get_open_algo_orders(symbol)
                    open_algo_ids = {o.get("algoId") for o in algo_orders if o.get("algoId")}
                    
                    triggered_id = None
                    if trade_state.sl_algo_id and trade_state.sl_algo_id not in open_algo_ids:
                        reason = "Stop Loss"
                        triggered_id = trade_state.sl_algo_id
                    elif trade_state.tp_algo_id and trade_state.tp_algo_id not in open_algo_ids:
                        reason = "Take Profit"
                        triggered_id = trade_state.tp_algo_id
                    elif trade_state.trail_algo_id and trade_state.trail_algo_id not in open_algo_ids:
                        reason = "Trailing Stop"
                        triggered_id = trade_state.trail_algo_id
                    
                    if triggered_id:
                        exit_price_dec = client.get_latest_fill_price(symbol, triggered_id)
                except:
                    pass
                
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
                    R
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
                    bot=telegram_bot,
                    chat_id=telegram_chat_id
                )
                
                try:
                    client.cancel_all_open_orders(symbol)
                except:
                    pass
                
                return
        
        except Exception as e:
            log(f"Monitor error: {str(e)}", telegram_bot, telegram_chat_id)
        
        time.sleep(1)

# ------------------- TRADING LOOP -------------------
def trading_loop(client: BinanceClient, symbol: str, telegram_bot: Optional[str], telegram_chat_id: Optional[str]):
    global bot_state
    filters = get_symbol_filters(client, symbol)
    tick_size = filters['tickSize']
    
    # Check for existing position on startup
    if has_active_position(client, symbol):
        pos = fetch_open_positions_details(client, symbol)
        if pos:
            pos_amt = Decimal(str(pos.get("positionAmt", "0")))
            if pos_amt != Decimal("0"):
                with bot_state._trade_lock:
                    bot_state.current_trade = TradeState()
                    bot_state.current_trade.active = True
                    bot_state.current_trade.side = "LONG" if pos_amt > 0 else "SHORT"
                    bot_state.current_trade.qty = abs(pos_amt)
                    bot_state.current_trade.entry_price = Decimal(str(pos.get("entryPrice", "0")))
                    bot_state.current_trade.entry_R = bot_state.current_trade.entry_price * SL_PCT
                    bot_state.current_trade.risk = bot_state.current_trade.entry_R
                    
                    # Calculate trail activation price
                    if bot_state.current_trade.side == "LONG":
                        bot_state.current_trade.trail_activation = bot_state.current_trade.entry_price + (TRAIL_TRIGGER_MULT * bot_state.current_trade.entry_R)
                    else:
                        bot_state.current_trade.trail_activation = bot_state.current_trade.entry_price - (TRAIL_TRIGGER_MULT * bot_state.current_trade.entry_R)
                
                log(f"Existing position detected on startup: {bot_state.current_trade.side} {bot_state.current_trade.qty} @ {bot_state.current_trade.entry_price}", 
                    telegram_bot, telegram_chat_id)
                
                # Start monitor for existing position
                threading.Thread(
                    target=monitor_trade,
                    args=(client, symbol, bot_state.current_trade, tick_size, telegram_bot, telegram_chat_id),
                    daemon=True
                ).start()
    
    log("Entering trading_loop - monitoring active", telegram_bot, telegram_chat_id)
    
    while not bot_state.STOP_REQUESTED and not os.path.exists("stop.txt"):
        # ONLY CHECK — do NOT reset here!
        with bot_state._restart_lock:
            if bot_state.RESTART_REQUESTED:
                log("🔄 Restart requested inside trading_loop - exiting loop cleanly",
                    telegram_bot, telegram_chat_id)
                return   # ← exit function, leave flag True for main loop to see

        time.sleep(1)

    log("Trading loop exited.", telegram_bot, telegram_chat_id)
# ------------------- PNL REPORT FUNCTIONS -------------------
def calculate_pnl_report(period: str) -> str:
    """Calculate PnL report for daily, weekly, or monthly period"""
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
    
    # Filter trades from the period
    filtered_trades = [
        trade for trade in bot_state.pnl_data
        if datetime.fromisoformat(trade['date']) >= start_time
    ]
    
    if not filtered_trades:
        return f"No trades recorded for the {period} period."
    
    # Calculate statistics
    total_pnl_usd = Decimal(str(sum(trade['pnl_usd'] for trade in filtered_trades)))
    total_pnl_r = Decimal(str(sum(trade['pnl_r'] for trade in filtered_trades)))
    num_trades = len(filtered_trades)
    avg_pnl_usd = total_pnl_usd / Decimal(str(num_trades)) if num_trades > 0 else Decimal("0")
    wins = sum(1 for trade in filtered_trades if trade['pnl_usd'] > 0)
    losses = num_trades - wins
    win_rate = (Decimal(str(wins)) / Decimal(str(num_trades)) * Decimal("100")) if num_trades > 0 else Decimal("0")
    
    return (
        f"{period.capitalize()} PNL Report:\n"
        f"• Total Trades: {num_trades}\n"
        f"• Total PNL: ${total_pnl_usd:.2f}\n"
        f"• Average PNL: ${avg_pnl_usd:.2f}\n"
        f"• Total PNL (R): {total_pnl_r:.2f}R\n"
        f"• Win Rate: {win_rate:.1f}% ({wins}W/{losses}L)\n"
    )

def send_daily_report(bot_token: Optional[str], chat_id: Optional[str]):
    """Send daily PnL report via Telegram"""
    report = calculate_pnl_report('daily')
    subject = f"📊 Daily PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot_token, chat_id, f"{subject}\n{report}")

def send_weekly_report(bot_token: Optional[str], chat_id: Optional[str]):
    """Send weekly PnL report via Telegram"""
    report = calculate_pnl_report('weekly')
    subject = f"📈 Weekly PnL Report - Week of {datetime.now(timezone.utc).strftime('%Y-%m-%d')}"
    telegram_post(bot_token, chat_id, f"{subject}\n{report}")

def send_monthly_report(bot_token: Optional[str], chat_id: Optional[str]):
    """Send monthly PnL report via Telegram"""
    report = calculate_pnl_report('monthly')
    subject = f"📉 Monthly PnL Report - {datetime.now(timezone.utc).strftime('%Y-%m')}"
    telegram_post(bot_token, chat_id, f"{subject}\n{report}")

import pickle

# ------------------- PERSISTENT STATE MANAGEMENT -------------------
STATE_FILE = 'bot_state.pkl'

def save_bot_state():
    """Save critical bot state to disk"""
    global bot_state
    try:
        # Create a dictionary with only what we need to persist
        persistent_data = {
            'pnl_data': bot_state.pnl_data[-1000:] if hasattr(bot_state, 'pnl_data') else [],
            'last_trade_date': getattr(bot_state, 'last_trade_date', None),
            'CONSEC_LOSSES': getattr(bot_state, 'CONSEC_LOSSES', 0),
            'weekly_peak_equity': getattr(bot_state, 'weekly_peak_equity', None),
            'weekly_start_time': getattr(bot_state, 'weekly_start_time', None),
            'account_size': getattr(bot_state, 'account_size', None),
            'daily_start_equity': getattr(bot_state, 'daily_start_equity', None)
        }
        
        with open(STATE_FILE, 'wb') as f:
            pickle.dump(persistent_data, f)
        log("💾 Bot state saved to disk", None, None)
    except Exception as e:
        log(f"❌ Failed to save state: {e}", None, None)

def load_bot_state():
    """Load critical bot state from disk"""
    global bot_state
    if not os.path.exists(STATE_FILE):
        log("📂 No saved state found - starting fresh", None, None)
        return
    
    try:
        with open(STATE_FILE, 'rb') as f:
            data = pickle.load(f)
        
        # Restore the data
        bot_state.pnl_data = data.get('pnl_data', [])
        bot_state.last_trade_date = data.get('last_trade_date')
        bot_state.CONSEC_LOSSES = data.get('CONSEC_LOSSES', 0)
        bot_state.weekly_peak_equity = data.get('weekly_peak_equity')
        bot_state.weekly_start_time = data.get('weekly_start_time')
        bot_state.account_size = data.get('account_size')
        bot_state.daily_start_equity = data.get('daily_start_equity')
        
        log(f"💾 Bot state loaded - {len(bot_state.pnl_data)} trades restored", None, None)
    except Exception as e:
        log(f"❌ Failed to load state: {e}", None, None)

def run_scheduler(bot_token: Optional[str], chat_id: Optional[str]):
    global bot_state
    last_month: Optional[int] = None
    
    def daily_reset_job():
        try:
            current_balance = fetch_balance(bot_state.client)
            if current_balance > 0:
                bot_state.account_size = current_balance
                log(f"DAILY RESET @ 00:00 UTC | New start equity: ${current_balance:.2f}", bot_token, chat_id)
        except Exception as e:
            log(f"Daily reset failed: {e}", bot_token, chat_id)
    
    def daily_memory_log():
        """Log current memory usage once per day at 12:00 UTC"""
        import psutil
        
        try:
            process = psutil.Process()
            mem_mb = process.memory_info().rss / 1024 / 1024
            
            # Get object count (optional)
            import gc
            obj_count = len(gc.get_objects())
            
            log(f"📊 DAILY MEMORY USAGE: {mem_mb:.1f} MB | Objects: {obj_count:,}", 
                bot_token, chat_id)
            
            # Alert if memory is getting high
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
        """Safe daily restart - preserves positions, really restarts process"""
        global bot_state
        
        # Check for active position
        has_position = False
        position_details = ""
        if (bot_state.client and bot_state.current_trade and 
            bot_state.current_trade.active and bot_state.current_trade.qty):
            has_position = True
            position_details = (f"{bot_state.current_trade.side} "
                               f"{bot_state.current_trade.qty} SOL "
                               f"@ {bot_state.current_trade.entry_price:.2f}")
        
        log("🔄 DAILY RESTART: Starting real process restart...", 
            args.telegram_token, args.chat_id)
        
        # Save state
        try:
            save_bot_state()
            log("💾 State saved - trades preserved", args.telegram_token, args.chat_id)
        except Exception as e:
            log(f"⚠️ State save warning: {e}", args.telegram_token, args.chat_id)
        
        # Notify about position status
        if has_position:
            msg = (f"🔄 Daily restart - POSITION PRESERVED!\n"
                   f"{position_details}\n"
                   f"SL/TP orders remain active on Binance")
            telegram_post(args.telegram_token, args.chat_id, msg)
            log(f"✅ Active position preserved: {position_details}", 
                args.telegram_token, args.chat_id)
        else:
            telegram_post(args.telegram_token, args.chat_id, 
                         "🔄 Daily restart - no active positions")
        
        time.sleep(2)  # Let messages send
        
        # ===== REAL PROCESS RESTART =====
        log("🚀 Restarting Python process NOW - positions safe on Binance", 
            args.telegram_token, args.chat_id)
        import os, sys
        os.execv(sys.executable, [sys.executable] + sys.argv)
    
    # Schedule all jobs
    schedule.every().day.at("00:00").do(daily_reset_job)
    schedule.every().monday.at("00:00").do(weekly_reset_job)
    schedule.every().day.at("00:01").do(check_monthly_report)
    schedule.every().day.at("00:01").do(daily_memory_log)  # ← ADD THIS
    schedule.every().day.at("00:02").do(daily_restart_job)  # Daily restart at 00:02
    schedule.every().day.at("23:59").do(lambda: send_daily_report(bot_token, chat_id))
    schedule.every().sunday.at("23:59").do(lambda: send_weekly_report(bot_token, chat_id))
    
    log("📅 Scheduler initialized - Daily restart at 00:02 UTC", bot_token, chat_id)
    
    while not bot_state.STOP_REQUESTED:
        schedule.run_pending()
        time.sleep(1)
# ------------------- WEBHOOK PROCESSING -------------------
def process_alert(data: Dict[str, Any]):
    global bot_state, CMD_ARGS
    
    symbol = data.get('symbol')
    if symbol != CMD_ARGS.symbol.upper():
        log(f"Symbol mismatch: {symbol} != {CMD_ARGS.symbol.upper()}")
        return
    
    side = data.get('side', '').upper()
    tv_qty_str = data.get('qty')  # Only logged — not used for execution
    order_type = data.get('type', '').upper()
    reduce_only = data.get('reduceOnly', False)
    
    # Extract optional SL/TP from combined payload (still useful if present)
    stop_price_str = data.get('stopPrice')
    take_profit_str = data.get('takeProfit')
    
    client = bot_state.client
    filters = get_symbol_filters(client, symbol)
    step_size = filters['stepSize']
    tick_size = filters['tickSize']
    
    with bot_state._trade_lock:
        current_trade = bot_state.current_trade
    
    if order_type == 'MARKET':
        if reduce_only:  # ── EXIT ORDER ────────────────────────────────────────────────
            if not current_trade or not current_trade.active:
                log("No active position to close")
                return
            
            pos_amt = get_position_amt(client, symbol)
            if pos_amt == Decimal('0'):
                log("Position already closed")
                with bot_state._trade_lock:
                    if bot_state.current_trade:
                        bot_state.current_trade.active = False
                return
            
            close_side = "SELL" if pos_amt > Decimal('0') else "BUY"
            if side != close_side:
                log(f"Close side mismatch: expected {close_side}, got {side}")
                return
            
            close_qty = abs(pos_amt)
            response = client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": close_side,
                "type": "MARKET",
                "quantity": str(close_qty),
                "reduceOnly": True
            })
            log(f"Close order sent: {response}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
        
        else:  # ── ENTRY ORDER ────────────────────────────────────────────────────────
            if current_trade and current_trade.active:
                log("Position already active, ignoring entry", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            if NEWS_GUARD_ENABLED:
                blocked, reason = is_news_blocked()
                if blocked:
                    log(f"News blocked: {reason}, ignoring entry", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    return
            
            # ── 1. Real balance check ────────────────────────────────────────────────
            current_balance = fetch_balance(client)
            if current_balance <= Decimal("10"):
                log(f"Balance too low (${current_balance:.2f}) — skipping entry",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            # ── 2. Current market price (for sizing + slippage) ──────────────────────
            current_price = get_current_price(client, symbol)
            if current_price is None or current_price <= Decimal("0"):
                log("Failed to get current price — skipping entry",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            # ── 3. Calculate risk distance (R), SL, TP, trail levels ────────────────
            if side == "BUY":  # LONG
                sl_price_dec = current_price * (Decimal("1") - SL_PCT)
                R = current_price * SL_PCT
                tp_price_dec = current_price + (TP_MULT * R)
                trail_activation = current_price + (TRAIL_TRIGGER_MULT * R)
            else:  # SHORT
                sl_price_dec = current_price * (Decimal("1") + SL_PCT)
                R = current_price * SL_PCT
                tp_price_dec = current_price - (TP_MULT * R)
                trail_activation = current_price - (TRAIL_TRIGGER_MULT * R)
            
            if R <= Decimal('0'):
                log("Invalid risk distance (R <= 0) — skipping",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            # ── 4. Bot recalculates qty (safe, real-balance based) ───────────────────
            risk_amount_usd = current_balance * RISK_PCT
            max_notional_by_leverage = current_balance * MAX_LEVERAGE
            max_qty_by_leverage = max_notional_by_leverage / current_price
            
            qty_raw = risk_amount_usd / R
            qty = min(qty_raw, max_qty_by_leverage)
            qty = qty * Decimal("0.75")           # safety factor
            qty = min(qty, Decimal("25"))         # hard cap
            qty_quant = quantize_qty(qty, step_size)
            
            notional = qty_quant * current_price
            if notional < Decimal("5.0"):
                log(f"Calculated notional too small (${notional:.2f} < $5) — skipping",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            # ── 5. Pre-entry slippage check ─────────────────────────────────────────
            tv_price = current_price  # fallback
            if 'price' in data:
                try:
                    tv_price = Decimal(str(data['price']))
                except:
                    pass
            
            slippage_pct = abs(current_price - tv_price) / tv_price if tv_price > 0 else Decimal("0")
            if slippage_pct > MAX_ENTRY_SLIPPAGE_PCT:
                log(f"Slippage too high: {slippage_pct*100:.3f}% > {MAX_ENTRY_SLIPPAGE_PCT*100:.2f}% "
                    f"(TV: {tv_price:.4f} → Now: {current_price:.4f}) — skipping",
                    CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            # ── 6. Detailed logging for transparency ─────────────────────────────────
            log(f"ENTRY SIGNAL → {side} {symbol}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            log(f"  Balance: ${current_balance:.2f} | Risk: {RISK_PCT*100:.1f}% (${risk_amount_usd:.2f})",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            log(f"  Current price: ${current_price:.4f} | R = ${R:.4f}",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            log(f"  Raw qty: {qty_raw:.4f} → After lev cap: {min(qty_raw, max_qty_by_leverage):.4f}",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            log(f"  After safety 75%: {qty:.4f} → After hard cap: {qty:.4f}",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            log(f"  FINAL QTY: {qty_quant:.4f} SOL | Notional: ${notional:.2f}",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            log(f"  TV suggested qty: {tv_qty_str or 'N/A'}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            
            # ── 7. Place the MARKET order ────────────────────────────────────────────
            response = client.send_signed_request("POST", "/fapi/v1/order", {
                "symbol": symbol,
                "side": side,
                "type": "MARKET",
                "quantity": str(qty_quant)
            })
            
            order_id = response.get("orderId")
            if not order_id:
                log("Entry order failed", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                return
            
            log(f"Entry order placed: {response}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
            
            # ── 8. Wait for fill (your original code — unchanged) ────────────────────
            start_time = time.time()
            filled = False
            while time.time() - start_time < ORDER_FILL_TIMEOUT:
                pos_amt = get_position_amt(client, symbol)
                if pos_amt != Decimal('0'):
                    with bot_state._trade_lock:
                        bot_state.current_trade = TradeState()
                        bot_state.current_trade.active = True
                        bot_state.current_trade.qty = abs(pos_amt)
                        bot_state.current_trade.side = "LONG" if pos_amt > Decimal('0') else "SHORT"
                        
                        actual_fill = client.get_latest_fill_price(symbol, order_id)
                        if actual_fill is None:
                            ticker = client.public_request("/fapi/v1/ticker/price", {"symbol": symbol})
                            actual_fill = Decimal(str(ticker["price"]))
                        
                        bot_state.current_trade.entry_price = actual_fill
                        bot_state.current_trade.entry_R = actual_fill * SL_PCT
                        bot_state.current_trade.risk = bot_state.current_trade.entry_R
                        bot_state.current_trade.entry_close_time = int(time.time() * 1000)
                        
                        if bot_state.current_trade.side == "LONG":
                            bot_state.current_trade.trail_activation = actual_fill + (TRAIL_TRIGGER_MULT * bot_state.current_trade.entry_R)
                        else:
                            bot_state.current_trade.trail_activation = actual_fill - (TRAIL_TRIGGER_MULT * bot_state.current_trade.entry_R)
                        
                        bot_state.current_trade.trail_activation = quantize_price(
                            bot_state.current_trade.trail_activation,
                            tick_size,
                            ROUND_UP if bot_state.current_trade.side == "LONG" else ROUND_DOWN
                        )
                    
                    log(f"Entry filled: {bot_state.current_trade.side}, qty={bot_state.current_trade.qty}, price={actual_fill}",
                        CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    
                    filled = True
                    break
                time.sleep(0.5)
            
            if not filled:
                log("Entry timeout, cancelling", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                try:
                    client.cancel_order(symbol, order_id)
                except:
                    pass
                return
            
            # ── 9. Place protective orders (your original code — unchanged) ──────────
            with bot_state._trade_lock:
                trade = bot_state.current_trade
                if trade and trade.active:
                    callback_rate = TRAIL_DISTANCE_MULT * SL_PCT * Decimal('100')
                    
                    # SL
                    sl_price = None
                    if trade.side == "LONG":
                        sl_price = trade.entry_price * (Decimal("1") - SL_PCT)
                        sl_price = quantize_price(sl_price, tick_size, ROUND_DOWN)
                        sl_side = "SELL"
                    else:
                        sl_price = trade.entry_price * (Decimal("1") + SL_PCT)
                        sl_price = quantize_price(sl_price, tick_size, ROUND_UP)
                        sl_side = "BUY"
                    
                    sl_order = client.place_stop_market(symbol, sl_side, trade.qty, sl_price, reduce_only=True)
                    if sl_order and sl_order.get("algoId"):
                        trade.sl_algo_id = sl_order["algoId"]
                        trade.sl = sl_price
                        log(f"SL placed at {sl_price}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    
                    # TP
                    tp_price = None
                    if trade.side == "LONG":
                        tp_price = trade.entry_price + (TP_MULT * trade.entry_R)
                        tp_price = quantize_price(tp_price, tick_size, ROUND_UP)
                        tp_side = "SELL"
                    else:
                        tp_price = trade.entry_price - (TP_MULT * trade.entry_R)
                        tp_price = quantize_price(tp_price, tick_size, ROUND_DOWN)
                        tp_side = "BUY"
                    
                    tp_order = client.place_take_profit_market(symbol, tp_side, trade.qty, tp_price, reduce_only=True)
                    if tp_order and tp_order.get("algoId"):
                        trade.tp_algo_id = tp_order["algoId"]
                        trade.tp = tp_price
                        log(f"TP placed at {tp_price}", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    
                    # Trailing Stop
                    trail_side = "SELL" if trade.side == "LONG" else "BUY"
                    trail_order = client.place_trailing_stop_market(
                        symbol=symbol,
                        side=trail_side,
                        quantity=trade.qty,
                        activation_price=trade.trail_activation,
                        callback_rate=callback_rate,
                        reduce_only=True
                    )
                    
                    if trail_order and trail_order.get("algoId"):
                        trade.trail_algo_id = trail_order["algoId"]
                        log(f"Trailing stop placed - Activation: {trade.trail_activation}, Callback: {callback_rate}%",
                            CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                        
                        send_trail_placed_telegram(
                            symbol, trade.side,
                            trade.trail_activation, callback_rate,
                            CMD_ARGS.telegram_token, CMD_ARGS.chat_id
                        )
                    
                    # Entry Telegram
                    send_trade_telegram({
                        'symbol': symbol,
                        'side': trade.side,
                        'entry': trade.entry_price,
                        'qty': trade.qty,
                        'sl': trade.sl,
                        'tp': trade.tp,
                        'trail_activation': trade.trail_activation,
                        'callback_rate': callback_rate
                    }, CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    
                    # Start monitoring
                    log("Starting trade monitoring after all protective orders placed",
                        CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
                    threading.Thread(
                        target=monitor_trade,
                        args=(client, symbol, trade, tick_size, CMD_ARGS.telegram_token, CMD_ARGS.chat_id),
                        daemon=True
                    ).start()
    
    elif order_type == 'STOP_MARKET':
        # Your original SL handling code (unchanged)
        stop_price_str = data.get('stopPrice')
        if not stop_price_str:
            log("No stopPrice in alert")
            return
        
        stop_price = Decimal(stop_price_str)
        stop_price_quant = quantize_price(stop_price, tick_size)
        
        with bot_state._trade_lock:
            current_trade = bot_state.current_trade
        
        if not current_trade or not current_trade.active:
            log("No active position, ignoring SL")
            return
        
        expected_close_side = "SELL" if current_trade.side == "LONG" else "BUY"
        if side != expected_close_side:
            log(f"SL side mismatch: expected {expected_close_side}, got {side}")
            return
        
        if abs(qty_quant - current_trade.qty) > Decimal('0.001'):
            log(f"SL qty mismatch: expected {current_trade.qty}, got {qty_quant}")
            return
        
        if current_trade.sl_algo_id:
            try:
                client.cancel_algo_order(symbol, current_trade.sl_algo_id)
                log(f"Cancelled old SL: {current_trade.sl_algo_id}")
            except:
                pass
        
        sl_order = client.place_stop_market(symbol, side, qty_quant, stop_price_quant, reduce_only=True)
        if sl_order and sl_order.get("algoId"):
            with bot_state._trade_lock:
                if bot_state.current_trade:
                    bot_state.current_trade.sl_algo_id = sl_order["algoId"]
                    bot_state.current_trade.sl = stop_price_quant
            log(f"SL placed/updated at {stop_price_quant} (algoId: {sl_order['algoId']})",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
        else:
            log("SL placement failed", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
    
    elif order_type == 'TAKE_PROFIT_MARKET':
        # Your original TP handling code (unchanged)
        tp_price_str = data.get('takeProfit')
        if not tp_price_str:
            log("No takeProfit in alert")
            return
        
        tp_price = Decimal(tp_price_str)
        tp_price_quant = quantize_price(tp_price, tick_size)
        
        with bot_state._trade_lock:
            current_trade = bot_state.current_trade
        
        if not current_trade or not current_trade.active:
            log("No active position, ignoring TP")
            return
        
        expected_close_side = "SELL" if current_trade.side == "LONG" else "BUY"
        if side != expected_close_side:
            log(f"TP side mismatch: expected {expected_close_side}, got {side}")
            return
        
        if abs(qty_quant - current_trade.qty) > Decimal('0.001'):
            log(f"TP qty mismatch: expected {current_trade.qty}, got {qty_quant}")
            return
        
        if current_trade.tp_algo_id:
            try:
                client.cancel_algo_order(symbol, current_trade.tp_algo_id)
                log(f"Cancelled old TP: {current_trade.tp_algo_id}")
            except:
                pass
        
        tp_order = client.place_take_profit_market(symbol, side, qty_quant, tp_price_quant, reduce_only=True)
        if tp_order and tp_order.get("algoId"):
            with bot_state._trade_lock:
                if bot_state.current_trade:
                    bot_state.current_trade.tp_algo_id = tp_order["algoId"]
                    bot_state.current_trade.tp = tp_price_quant
            log(f"TP placed/updated at {tp_price_quant} (algoId: {tp_order['algoId']})",
                CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
        else:
            log("TP placement failed", CMD_ARGS.telegram_token, CMD_ARGS.chat_id)
@app.route('/webhook', methods=['POST'])
def webhook():
    if bot_state.STOP_REQUESTED:
        return "Bot stopped", 503
    
    # === DEBUG LOGGING - CRITICAL FOR DIAGNOSIS ===
    raw_body = request.get_data(as_text=True)
    content_type = request.headers.get('Content-Type', 'MISSING')
    log(f"WEBHOOK RAW - Type: {content_type} | Length: {len(raw_body)} | Preview: {raw_body[:200]}")
    
    # === MULTI-STRATEGY PARSING ===
    data = None
    
    # Strategy 1: Try normal JSON parsing (respects content-type)
    if request.is_json:
        try:
            data = request.get_json()
            log("Parsed via is_json")
        except:
            pass
    
    # Strategy 2: Force JSON parsing (ignores content-type)
    if not data:
        try:
            data = request.get_json(force=True)
            log("Parsed via force=True")
        except:
            pass
    
    # Strategy 3: Manual JSON loading from raw body
    if not data and raw_body:
        try:
            # Clean the raw body (remove BOM, trim)
            cleaned = raw_body.strip().lstrip('\ufeff')
            data = json.loads(cleaned)
            log("Parsed via manual json.loads")
        except Exception as e:
            log(f"Manual parse failed: {e}")
    
    # === VALIDATION ===
    if not data:
        log(f"FAILED: No valid JSON - Raw: {raw_body[:300]}")
        return "Invalid JSON payload", 400
    
    uid = data.get('uid')
    if uid != my_uid:
        log(f"Invalid UID: {uid}")
        return "Invalid UID", 403
    
    # Process in background
    threading.Thread(target=process_alert, args=(data,), daemon=True).start()
    
    return jsonify({"status": "ok"}), 200

def recover_existing_positions(client, symbol, tick_size, telegram_bot, telegram_chat_id):
    """Recover and monitor existing position - orders already on Binance"""
    global bot_state
    try:
        pos_amt = get_position_amt(client, symbol)
        if pos_amt != Decimal('0'):
            log(f"📊 Found existing position: {abs(pos_amt)} SOL (orders active on Binance)", 
                telegram_bot, telegram_chat_id)
            
            # Get position details
            pos = fetch_open_positions_details(client, symbol)
            if pos:
                entry_price = Decimal(str(pos.get('entryPrice', '0')))
                
                # Create trade state for monitoring only
                trade_state = TradeState()
                trade_state.active = True
                trade_state.side = "LONG" if pos_amt > 0 else "SHORT"
                trade_state.qty = abs(pos_amt)
                trade_state.entry_price = entry_price
                
                # Store in bot_state
                with bot_state._trade_lock:
                    bot_state.current_trade = trade_state
                
                # Start monitoring (orders already on Binance!)
                threading.Thread(
                    target=monitor_trade,
                    args=(client, symbol, trade_state, tick_size, 
                          telegram_bot, telegram_chat_id),
                    daemon=True
                ).start()
                
                log("✅ Position recovery complete - monitoring resumed (orders untouched)", 
                    telegram_bot, telegram_chat_id)
    except Exception as e:
        log(f"❌ Position recovery error: {e}", telegram_bot, telegram_chat_id)

# ==================== TELEGRAM COMMAND HANDLERS ====================
async def cmd_restart(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Telegram /restart - safely restarts bot, preserves positions"""
    global bot_state, args, LOCK_HANDLE  # Add LOCK_HANDLE here
    
    chat_id = str(update.effective_chat.id)
    
    # Security check
    if chat_id != str(args.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    # Check for active position
    has_position = False
    position_details = ""
    if (bot_state.client and hasattr(bot_state, 'current_trade') and 
        bot_state.current_trade and bot_state.current_trade.active and bot_state.current_trade.qty):
        has_position = True
        position_details = (f"{bot_state.current_trade.side} "
                           f"{bot_state.current_trade.qty} SOL "
                           f"@ {bot_state.current_trade.entry_price:.2f}")
    
    # Reply with position info
    if has_position:
        await update.message.reply_text(
            f"🔄 *Restarting with ACTIVE POSITION*\n\n"
            f"📊 *Position:* {position_details}\n"
            f"🛡️ *SL/TP orders stay on Binance*\n"
            f"🤖 Bot will resume monitoring after restart\n\n"
            f"Restarting in 2 seconds...",
            parse_mode='Markdown'
        )
    else:
        await update.message.reply_text("🔄 Restarting bot now...")
    
    # Save state
    try:
        save_bot_state()
        await update.message.reply_text("💾 Trade history saved")
    except:
        await update.message.reply_text("⚠️ Save warning - restarting anyway")
    
    log("🔧 Manual restart via Telegram", args.telegram_token, args.chat_id)
    
    await asyncio.sleep(2)  # Let messages send
    
    # ===== CRITICAL: Close the lock handle BEFORE restart =====
    try:
        if LOCK_HANDLE:
            LOCK_HANDLE.close()
            print("Lock handle closed successfully for restart")
        # Don't delete the lock file, just close the handle
    except Exception as e:
        print(f"Error closing lock handle during restart: {e}")
    
    # Small delay to ensure everything is cleaned up
    time.sleep(3)
    
    # ===== REAL PROCESS RESTART =====
    import os, sys
    os.execv(sys.executable, [sys.executable] + sys.argv)
async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Command: /status — quick bot health check"""
    global bot_state, CMD_ARGS
    
    chat_id = str(update.effective_chat.id)
    
    # Security: Only allow your chat ID
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    # Get current status
    balance = fetch_balance(bot_state.client) if bot_state.client else Decimal("0")
    pos_amt = get_position_amt(bot_state.client, CMD_ARGS.symbol) if bot_state.client else Decimal("0")
    
    # Get memory usage
    import psutil
    process = psutil.Process()
    mem_mb = process.memory_info().rss / 1024 / 1024
    
    status_lines = [
        f"🤖 *DeepDenise Status*",
        f"",
        f"📊 *Balance:* `${float(balance):.2f}`",
        f"📈 *Position:* `{float(pos_amt):.2f} SOL`",
        f"🔄 *Active Trade:* `{'Yes' if bot_state.current_trade and bot_state.current_trade.active else 'No'}`",
        f"🚩 *Restart Flag:* `{bot_state.RESTART_REQUESTED}`",
        f"💾 *Trades Stored:* `{len(bot_state.pnl_data)}`",
        f"🧠 *Memory:* `{mem_mb:.1f} MB`",
        f"🆔 *PID:* `{os.getpid()}`",
        f"⏰ *Uptime:* `{datetime.now(timezone.utc) - bot_state.start_time}`" if hasattr(bot_state, 'start_time') else ""
    ]
    
    await update.message.reply_text("\n".join(status_lines), parse_mode='Markdown')

async def cmd_balance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Command: /balance — show current balance only"""
    global bot_state, CMD_ARGS
    
    chat_id = str(update.effective_chat.id)
    
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    balance = fetch_balance(bot_state.client) if bot_state.client else Decimal("0")
    await update.message.reply_text(f"💰 Current Balance: `${float(balance):.2f}` USDT")

async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Command: /help — show available commands"""
    chat_id = str(update.effective_chat.id)
    
    if chat_id != str(CMD_ARGS.chat_id):
        await update.message.reply_text("❌ Unauthorized.")
        return
    
    help_text = (
        "🤖 *Available Commands:*\n\n"
        "/status - Show bot status (balance, position, memory)\n"
        "/balance - Show current balance only\n"
        "/restart - Gracefully restart the bot\n"
        "/help - Show this help message"
    )
    await update.message.reply_text(help_text, parse_mode='Markdown')

async def unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle unknown commands"""
    chat_id = str(update.effective_chat.id)
    
    if chat_id != str(CMD_ARGS.chat_id):
        return
    
    await update.message.reply_text("❓ Unknown command. Try /help")

# ------------------- MAIN -------------------
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Binance Futures Bot - Webhook Mode with Immediate Trailing Stop")
    parser.add_argument("--api-key", required=True, help="Binance API Key")
    parser.add_argument("--api-secret", required=True, help="Binance API Secret")
    parser.add_argument("--telegram-token", required=True, help="Telegram Bot Token")
    parser.add_argument("--chat-id", required=True, help="Telegram Chat ID")
    parser.add_argument("--symbol", default="SOLUSDT", help="Trading symbol")
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--base-url", default=None)
    parser.add_argument("--no-news-guard", action="store_true", help="Disable news guard")
    parser.add_argument("--port", type=int, default=8080, help="Webhook port")
    args = parser.parse_args()
    
    CMD_ARGS = args  # Store for webhook access
    
    # Acquire lock AFTER args (no global needed here)
    LOCK_HANDLE = acquire_lock()
    
    if args.no_news_guard:
        NEWS_GUARD_ENABLED = False
        print("[CONFIG] News Guard DISABLED")
    
    init_pnl_log()
    
    # Load saved state
    load_bot_state()
    
    # Shutdown handler (improved - early lock cleanup, sys.exit)
    _shutdown_done = False
    
    def graceful_shutdown(sig: Optional[int] = None, frame: Any = None, 
                          symbol: Optional[str] = None, 
                          telegram_bot: Optional[str] = None, 
                          telegram_chat_id: Optional[str] = None):
        global _shutdown_done, bot_state, args, LOCK_HANDLE
        
        # Use passed values or fall back to args
        symbol = symbol or args.symbol
        telegram_bot = telegram_bot or args.telegram_token
        telegram_chat_id = telegram_chat_id or args.chat_id
        
        if _shutdown_done:
            return
        _shutdown_done = True
        
        reason = {
            signal.SIGINT: "Ctrl+C",
            signal.SIGTERM: "SIGTERM / systemd",
        }.get(sig, "Clean exit")
        
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            reason = "KILL FLAG / Manual stop"
        
        log(f"🛑 Shutdown requested ({reason}). Cleaning up...", 
            telegram_bot, telegram_chat_id)
        
        # Save state before shutdown
        save_bot_state()
        
        # Check for active position
        has_active_position = False
        pos_amt = Decimal('0')
        
        if bot_state.client and symbol:
            try:
                pos_amt = get_position_amt(bot_state.client, symbol, telegram_bot, telegram_chat_id)
                has_active_position = pos_amt != Decimal('0')
            except:
                pass
        
        if has_active_position:
            log("🔄 RESTARTING WITH ACTIVE POSITION - PRESERVING POSITION", 
                telegram_bot, telegram_chat_id)
            log(f"✅ Position: {abs(float(pos_amt)):.2f} SOL remains open - orders stay on Binance", 
                telegram_bot, telegram_chat_id)
        else:
            log("Normal shutdown - cleaning up orders", telegram_bot, telegram_chat_id)
            if bot_state.client and symbol:
                try:
                    bot_state.client.cancel_all_open_orders(symbol)
                except Exception as e:
                    log(f"Order cleanup error: {e}", telegram_bot, telegram_chat_id)
        
        goodbye = (
            f"RSI BOT STOPPED\n"
            f"Symbol: {symbol}\n"
            f"Reason: {reason}\n"
            f"Time: {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')} UTC"
        )
        
        if has_active_position:
            goodbye += "\n✅ POSITION PRESERVED - Orders remain active"
        
        try:
            log(goodbye, telegram_bot, telegram_chat_id)
        except Exception as e:
            print(f"Error during goodbye log: {e}")
        
        # Only clean lock file on actual shutdown (signal received), not during restart
        # sig is None when called from atexit (restart), not None when from signal
        if sig is not None:
            try:
                if LOCK_HANDLE:
                    try:
                        LOCK_HANDLE.close()
                    except:
                        pass
                if os.path.exists(LOCK_FILE):
                    os.unlink(LOCK_FILE)
                    log(f"Lock file removed: {LOCK_FILE}", telegram_bot, telegram_chat_id)
            except Exception as e:
                print(f"Error cleaning lock file: {e}")
        
        # Remove kill flag
        try:
            if os.path.exists("/tmp/STOP_BOT_NOW"):
                os.unlink("/tmp/STOP_BOT_NOW")
        except Exception as e:
            print(f"Error removing kill flag: {e}")
        
        os._exit(0)
    def signal_handler_wrapper(sig, frame):
        graceful_shutdown(sig, frame, args.symbol, args.telegram_token, args.chat_id)
    
    signal.signal(signal.SIGINT, signal_handler_wrapper)
    signal.signal(signal.SIGTERM, signal_handler_wrapper)
    atexit.register(lambda: graceful_shutdown(None, None, args.symbol, args.telegram_token, args.chat_id))
    
    # Immortal loop
    while True:
        if os.path.exists("/tmp/STOP_BOT_NOW"):
            log("STOP_BOT_NOW flag detected – shutting down permanently", args.telegram_token, args.chat_id)
            graceful_shutdown()
            break
        
        # Check restart flag
        with bot_state._restart_lock:
            if bot_state.RESTART_REQUESTED:
                log("🔄 Restart flag detected - performing clean restart", args.telegram_token, args.chat_id)
                bot_state.RESTART_REQUESTED = False
                
                # Force remove lock before new instance
                try:
                    if os.path.exists(LOCK_FILE):
                        os.unlink(LOCK_FILE)
                        log("Lock file removed for restart", args.telegram_token, args.chat_id)
                except Exception as e:
                    log(f"Force lock cleanup failed: {e}", args.telegram_token, args.chat_id)
                
                save_bot_state()
                log("💾 State saved - restarting...", args.telegram_token, args.chat_id)
                time.sleep(2)
                continue
        
        try:
            bot_state.client = BinanceClient(args.api_key, args.api_secret, use_live=args.live, base_override=args.base_url)
            balance = fetch_balance(bot_state.client)
            bot_state.account_size = balance
            
            leverage_to_set = 5
            bot_state.client.set_leverage(args.symbol, leverage_to_set)
            log(f"Set leverage to {leverage_to_set}x", args.telegram_token, args.chat_id)
            log(f"Balance: ${balance:.2f}", args.telegram_token, args.chat_id)
            
            if NEWS_GUARD_ENABLED:
                threading.Thread(target=news_heartbeat, daemon=True).start()
                log("News guard: ENABLED", args.telegram_token, args.chat_id)
            
            log(f"STARTING WEBHOOK BOT → {args.symbol} | {'LIVE' if args.live else 'TESTNET'}",
                args.telegram_token, args.chat_id)
            
            filters = get_symbol_filters(bot_state.client, args.symbol)
            tick_size = filters['tickSize']
            recover_existing_positions(bot_state.client, args.symbol, tick_size, 
                                      args.telegram_token, args.chat_id)
            log(f"🚀 Bot started - PID: {os.getpid()}", args.telegram_token, args.chat_id)
            
            import psutil
            mem_mb = psutil.Process().memory_info().rss / 1024 / 1024
            log(f"🧠 Fresh process memory: {mem_mb:.1f} MB", args.telegram_token, args.chat_id)
            
            threading.Thread(target=lambda: run_scheduler(args.telegram_token, args.chat_id), daemon=True).start()
            
            # ========== START FLASK WEBHOOK SERVER ==========
            import socket
            from werkzeug.serving import make_server
            
            # Create socket with SO_REUSEADDR
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.bind(('0.0.0.0', args.port))
            sock.listen(128)
            
            # Create server with pre-bound socket
            server = make_server('0.0.0.0', args.port, app, threaded=True, request_handler=None)
            server.socket = sock
            
            # Run in thread
            flask_thread = threading.Thread(target=server.serve_forever, daemon=True)
            flask_thread.start()
            log(f"🌐 Webhook listening on port {args.port} with SO_REUSEADDR enabled", args.telegram_token, args.chat_id)
            # ========== TELEGRAM LISTENER - RUNNING IN MAIN THREAD ==========
            if args.telegram_token and args.chat_id:
                # Clean up old sessions
                try:
                    requests.post(
                        f"https://api.telegram.org/bot{args.telegram_token}/deleteWebhook",
                        timeout=5
                    )
                    log("Cleaned up any old Telegram webhook/polling sessions",
                        args.telegram_token, args.chat_id)
                    time.sleep(2)
                except Exception as e:
                    log(f"Cleanup old Telegram sessions failed (usually harmless): {e}",
                        args.telegram_token, args.chat_id)

                # Build the application
                from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes
                from telegram import Update
                
                application = Application.builder().token(args.telegram_token).build()

                # Add command handlers
                application.add_handler(CommandHandler("restart", cmd_restart))
                application.add_handler(CommandHandler("status", cmd_status))
                application.add_handler(CommandHandler("help", cmd_help))
                
                # Handle unknown commands
                async def unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
                    if update.message and update.message.text and update.message.text.startswith('/'):
                        await update.message.reply_text("❓ Unknown command. Try /help")
                application.add_handler(MessageHandler(filters.COMMAND, unknown))

                log("📱 Telegram command listener starting in main thread (/restart, /status, /help)",
                    args.telegram_token, args.chat_id)

                # Run polling in main thread (blocks until shutdown)
                try:
                    application.run_polling(
                        drop_pending_updates=True,
                        stop_signals=None,
                        allowed_updates=Update.ALL_TYPES
                    )
                except Exception as e:
                    log(f"Telegram polling stopped: {e}", args.telegram_token, args.chat_id)
            
            # This line will only be reached if Telegram polling stops
            log("Bot stopped cleanly – exiting.", args.telegram_token, args.chat_id)
            break
        
        except Exception as e:
            import traceback
            error_msg = f"BOT CRASHED → RESTARTING IN 15s\n{traceback.format_exc()}"
            try:
                log(error_msg, args.telegram_token, args.chat_id)
                telegram_post(args.telegram_token, args.chat_id, "BOT CRASHED – RESTARTING IN 15s")
            except Exception as e2:
                print(f"Error during crash logging: {e2}")
            time.sleep(15)
