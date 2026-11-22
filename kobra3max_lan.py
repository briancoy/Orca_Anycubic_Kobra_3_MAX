# /// script
# requires-python = ">=3.10"
#
# [tool.orcaslicer.plugin]
# name = "Kobra 3 Max LAN"
# description = "Kobra 3 Max stock LAN preview: live dashboard, two ACE Pro units, external spool and upload."
# author = "Community (based on OrcaCubic)"
# version = "0.1.6"
# ///
"""
Anycubic Kobra LAN -- printer agent plugin for OrcaSlicer 2.5+.

Brings, as a Python plugin, the LAN features of the OrcaCubic fork
(https://github.com/marcodiniz/OrcaCubic) to the Kobra 4 and the Kobra X:

  * signed HTTP handshake (port 18910) + AES-128-CBC credentials
  * MQTT 3.1.1 over TLS (port 9883): telemetry, commands, ACE Pro
  * file upload over HTTP (/gcode_upload) with progress and cancellation
  * print start with ACE slot mapping and task options
  * 3MF adjustment (plate_N -> plate_1) and, optionally, replacing the first
    tool change with an initial purge (filament pre-engage)

Python standard library only. The Kobra panel (status, camera, files, ACE) is served to
OrcaSlicer's Device (Web) tab; optional components (printer photos, filament lists, Kobra 4
profiles) are installed from its Setup tab. License: AGPL-3.0-or-later.
"""
from __future__ import annotations

import base64
import hashlib
import http.client
import json
import logging
import os
import queue
import random
import re
import socket
import ssl
import string
import struct
import tempfile
import threading
import time
import urllib.parse
import zipfile
from typing import Any, Callable, Dict, List, Optional, Tuple

PLUGIN_VERSION = "0.1.6"
# Anycubic profile bundle shipped in setup/kobra4-profiles.zip (Kobra 4 / Kobra X from Anycubic Slicer Next)
PROFILE_PACKAGE_VERSION = "02.04.50.01"
AGENT_ID = "kobra3max_lan"
AGENT_NAME = "Kobra 3 Max LAN"
HTTP_PORT = 18910
MQTT_PORT = 9883
BUILTIN_HOSTS: List[str] = []   # IPs always probed during discovery (add yours in "discovery_hosts")

logger = logging.getLogger("anycubic_kobra_lan")

# --------------------------------------------------------------------------
# Return codes (same as bambu_networking.hpp)
# --------------------------------------------------------------------------
ERR_OK = 0
ERR_GENERIC = -1
ERR_CANCELED = -18
ERR_UPLOAD_FAILED = -4020
ERR_CONNECTION_TO_PRINTER_FAILED = -6010
ERR_FILE_NOT_EXIST = -3070
ERR_NOT_SUPPORTED = -7010

# SendingPrintJobStage stages
STAGE_CREATE, STAGE_UPLOAD, STAGE_WAITING, STAGE_SENDING = 0, 1, 2, 3
STAGE_RECORD, STAGE_WAIT_PRINTER, STAGE_FINISHED, STAGE_ERROR = 4, 5, 6, 7

# --------------------------------------------------------------------------
# OrcaSlicer API (with a "shim" to run the tests outside OrcaSlicer)
# --------------------------------------------------------------------------
try:
    import orca  # type: ignore
    IN_ORCA = True
except ImportError:  # pragma: no cover - only used in tests/standalone
    IN_ORCA = False

if IN_ORCA:
    # Inside OrcaSlicer, a failure here must show up as a plugin error. Before, any
    # exception fell back to the "fake" classes below: the plugin loaded without registering anything
    # and simply did not show up as a printer agent.
    _pa = getattr(orca, "printer_agent", None)
    if _pa is None:
        raise ImportError("this OrcaSlicer does not expose orca.printer_agent (it needs 2.5 with printer plugins)")
    AgentInfo = _pa.AgentInfo
    CameraStreamMode = _pa.CameraStreamMode
    FilamentSyncMode = _pa.FilamentSyncMode
    PrinterAgentBase = _pa.PrinterAgentBase
else:

    class _Enum:
        pass

    class FilamentSyncMode(_Enum):  # type: ignore[no-redef]
        None_ = 0
        Subscription = 1
        Pull = 2

    class CameraStreamMode(_Enum):  # type: ignore[no-redef]
        None_ = 0
        HTTP = 1
        HTTPS = 2
        HTTP_SNAPSHOT = 3
        RTSP = 4

    class AgentInfo:  # type: ignore[no-redef]
        def __init__(self, id="", name="", version="", description=""):
            self.id, self.name, self.version, self.description = id, name, version, description

    class PrinterAgentBase:  # type: ignore[no-redef]
        def __init__(self):
            pass

        def get_config(self):
            return "{}"

    class _OrcaStub:
        class base:  # noqa: N801
            pass

        @staticmethod
        def plugin(cls):
            return cls

        @staticmethod
        def register_capability(cls):
            return None

    orca = _OrcaStub()  # type: ignore[assignment]


# --------------------------------------------------------------------------
# Utilities
# --------------------------------------------------------------------------
def _as_int(value: Any, fallback: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        try:
            return int(float(value))
        except (TypeError, ValueError):
            return fallback


def _as_float(value: Any, fallback: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return fallback


def _rand_hex(n: int = 32) -> str:
    return "".join(random.choices(string.hexdigits.lower()[:16], k=n))


def _ascii(text: str) -> str:
    import unicodedata
    return unicodedata.normalize("NFKD", str(text or "")).encode("ascii", "ignore").decode("ascii")


def _rand_alnum(n: int) -> str:
    return "".join(random.choices(string.ascii_letters + string.digits, k=n))

def _tmp_dir() -> str:
    """Temporary folder INSIDE the plugin's allowed area (OrcaSlicer data). The default mkstemp writes
    to %TEMP% and, on Windows, retries with a new name on every PermissionError -- each name becomes a
    permission request in OrcaSlicer (hundreds of prompts in a row and the UI freezes)."""
    try:
        base = os.path.join(_plugin_dir(), "_tmp")
        os.makedirs(base, exist_ok=True)
        return base
    except Exception:  # noqa: BLE001
        return tempfile.gettempdir()

def _find_key(obj: Any, key: str, depth: int = 3) -> str:
    """Looks for `key` (non-empty string) in nested dicts/lists, up to `depth` levels."""
    if depth < 0:
        return ""
    if isinstance(obj, dict):
        v = obj.get(key)
        if isinstance(v, str) and v:
            return v
        for sub in obj.values():
            r = _find_key(sub, key, depth - 1)
            if r:
                return r
    elif isinstance(obj, list):
        for sub in obj:
            r = _find_key(sub, key, depth - 1)
            if r:
                return r
    return ""



def _mkstemp(suffix: str = "", prefix: str = "kobra_") -> Tuple[int, str]:
    """Replaces tempfile.mkstemp: at most 3 attempts, no loop on PermissionError."""
    d = _tmp_dir()
    last: Optional[BaseException] = None
    for _ in range(3):
        path = os.path.join(d, prefix + _rand_alnum(10) + suffix)
        try:
            fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_EXCL | getattr(os, "O_BINARY", 0), 0o600)
            return fd, path
        except FileExistsError:
            continue
        except OSError as exc:
            last = exc
            break
    raise last or OSError("could not create a temporary file")



def _now_ms() -> int:
    return int(time.time() * 1000)


def _spawn(target: Callable[..., Any], name: str, *args: Any) -> Optional[threading.Thread]:
    """Creates a daemon thread. Returns None if the host refuses it (thread permission)."""
    try:
        t = threading.Thread(target=target, args=args, name=name, daemon=True)
        t.start()
        return t
    except BaseException as exc:  # the audit hook refusal arrives as an exception
        logger.warning("could not create thread %s: %s", name, exc)
        return None


def _run_blocking(fn: Callable[[], Any], name: str = "anycubic-job", timeout: Optional[float] = None) -> Any:
    """Runs `fn` in a plugin thread and waits. OrcaSlicer calls the print
    methods from job threads; network I/O has to happen in a thread
    created by the plugin itself to avoid the host permission prompt."""
    box: Dict[str, Any] = {}

    def runner() -> None:
        try:
            box["r"] = fn()
        except BaseException as exc:  # noqa: BLE001
            box["e"] = exc

    t = _spawn(runner, name)
    if t is None:
        runner()  # no thread permission: run inline (may ask for network permissions)
    else:
        # Called from the OrcaSlicer main thread, a join without timeout freezes the UI when the plugin
        # thread waits for a permission prompt (which only appears when the main thread is free).
        t.join(timeout)
        if t.is_alive():
            raise TimeoutError("plugin operation took more than %.0f s (waiting for a permission?)" % (timeout or 0))
    if "e" in box:
        raise box["e"]
    return box.get("r")


# --------------------------------------------------------------------------
# AES-128-CBC (decrypt only) in pure Python -- no "cryptography"
# --------------------------------------------------------------------------
def _build_sbox() -> Tuple[List[int], List[int]]:
    sbox = [0] * 256
    p = q = 1
    while True:
        # p *= 3 in GF(2^8)
        p = (p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)) & 0xFF
        # q /= 3 in GF(2^8)
        q ^= (q << 1) & 0xFF
        q ^= (q << 2) & 0xFF
        q ^= (q << 4) & 0xFF
        if q & 0x80:
            q ^= 0x09
        q &= 0xFF
        rot = lambda v, n: ((v << n) | (v >> (8 - n))) & 0xFF  # noqa: E731
        x = q ^ rot(q, 1) ^ rot(q, 2) ^ rot(q, 3) ^ rot(q, 4)
        sbox[p] = (x ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    return sbox, inv


_SBOX, _INV_SBOX = _build_sbox()


def _xtime(a: int) -> int:
    return ((a << 1) ^ 0x1B) & 0xFF if a & 0x80 else a << 1


def _gmul(a: int, b: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        a = _xtime(a)
        b >>= 1
    return r


_MUL9 = [_gmul(i, 9) for i in range(256)]
_MUL11 = [_gmul(i, 11) for i in range(256)]
_MUL13 = [_gmul(i, 13) for i in range(256)]
_MUL14 = [_gmul(i, 14) for i in range(256)]


def _expand_key_128(key: bytes) -> List[List[int]]:
    if len(key) != 16:
        raise ValueError("the AES key must be 16 bytes")
    w = [list(key[i:i + 4]) for i in range(0, 16, 4)]
    rcon = 1
    for i in range(4, 44):
        t = list(w[i - 1])
        if i % 4 == 0:
            t = t[1:] + t[:1]
            t = [_SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = _xtime(rcon)
        w.append([w[i - 4][j] ^ t[j] for j in range(4)])
    return [sum((w[r * 4 + c] for c in range(4)), []) for r in range(11)]


def _aes_decrypt_block(block: bytes, round_keys: List[List[int]]) -> bytes:
    s = [block[i] ^ round_keys[10][i] for i in range(16)]
    for rnd in range(9, 0, -1):
        # InvShiftRows (state in column-major order)
        s = [
            s[0], s[13], s[10], s[7],
            s[4], s[1], s[14], s[11],
            s[8], s[5], s[2], s[15],
            s[12], s[9], s[6], s[3],
        ]
        s = [_INV_SBOX[b] for b in s]
        s = [s[i] ^ round_keys[rnd][i] for i in range(16)]
        out = []
        for c in range(0, 16, 4):
            a0, a1, a2, a3 = s[c:c + 4]
            out += [
                _MUL14[a0] ^ _MUL11[a1] ^ _MUL13[a2] ^ _MUL9[a3],
                _MUL9[a0] ^ _MUL14[a1] ^ _MUL11[a2] ^ _MUL13[a3],
                _MUL13[a0] ^ _MUL9[a1] ^ _MUL14[a2] ^ _MUL11[a3],
                _MUL11[a0] ^ _MUL13[a1] ^ _MUL9[a2] ^ _MUL14[a3],
            ]
        s = out
    s = [
        s[0], s[13], s[10], s[7],
        s[4], s[1], s[14], s[11],
        s[8], s[5], s[2], s[15],
        s[12], s[9], s[6], s[3],
    ]
    s = [_INV_SBOX[b] for b in s]
    return bytes(s[i] ^ round_keys[0][i] for i in range(16))


def aes128_cbc_decrypt(ciphertext: bytes, key: bytes, iv: bytes, unpad: bool = True) -> bytes:
    if len(iv) != 16:
        raise ValueError("the IV must be 16 bytes")
    if not ciphertext or len(ciphertext) % 16:
        raise ValueError("invalid ciphertext length")
    rks = _expand_key_128(key)
    out = bytearray()
    prev = iv
    for i in range(0, len(ciphertext), 16):
        blk = ciphertext[i:i + 16]
        dec = _aes_decrypt_block(blk, rks)
        out += bytes(a ^ b for a, b in zip(dec, prev))
        prev = blk
    if unpad:
        n = out[-1]
        if n < 1 or n > 16 or out[-n:] != bytes([n]) * n:
            raise ValueError("invalid PKCS#7 padding")
        del out[-n:]
    return bytes(out)


# --------------------------------------------------------------------------
# Minimal MQTT 3.1.1 client (TLS), only what Anycubic uses
# --------------------------------------------------------------------------
class MqttError(Exception):
    pass


def _mqtt_str(s: str) -> bytes:
    b = s.encode("utf-8")
    return struct.pack("!H", len(b)) + b


def _mqtt_varint(n: int) -> bytes:
    out = bytearray()
    while True:
        d = n % 128
        n //= 128
        if n:
            d |= 0x80
        out.append(d)
        if not n:
            return bytes(out)


class MiniMqtt:
    """MQTT 3.1.1: CONNECT, SUBSCRIBE, PUBLISH (QoS 0 to send; QoS 0/1/2 to receive)."""

    def __init__(self, client_id: str, username: str, password: str, keepalive: int = 60):
        self.client_id = client_id
        self.username = username
        self.password = password
        self.keepalive = keepalive
        self.sock: Optional[socket.socket] = None
        self._wlock = threading.Lock()
        self._pid = 0
        self.on_message: Optional[Callable[[str, bytes], None]] = None
        self.on_disconnect: Optional[Callable[[str], None]] = None
        self._stop = threading.Event()
        self.connected = False
        self._rbuf = bytearray()

    # -- low level ----------------------------------------------------------
    def _send(self, data: bytes) -> None:
        s = self.sock
        if s is None:
            raise MqttError("MQTT disconnected")
        with self._wlock:
            s.sendall(data)

    def _try_parse(self) -> Optional[Tuple[int, int, bytes]]:
        """Takes a complete packet from the buffer, or returns None if bytes are still missing."""
        buf = self._rbuf
        if len(buf) < 2:
            return None
        mult, length, pos = 1, 0, 1
        while True:
            if pos >= len(buf):
                return None
            d = buf[pos]
            length += (d & 0x7F) * mult
            pos += 1
            if not d & 0x80:
                break
            mult *= 128
            if pos > 4:
                raise MqttError("invalid MQTT packet length")
        if len(buf) < pos + length:
            return None
        b0 = buf[0]
        body = bytes(buf[pos:pos + length])
        del buf[:pos + length]
        return b0 >> 4, b0 & 0x0F, body

    def _read_packet(self) -> Tuple[int, int, bytes]:
        # Bytes already received stay in the buffer even when recv times out: the previous
        # version lost the piece it had read and desynchronized the stream when a large report
        # (ACE, info) arrived in pieces.
        while True:
            pkt = self._try_parse()
            if pkt is not None:
                return pkt
            s = self.sock
            if s is None:
                raise MqttError("MQTT disconnected")
            chunk = s.recv(65536)
            if not chunk:
                raise MqttError("connection closed by the printer")
            self._rbuf += chunk

    def _next_pid(self) -> int:
        self._pid = self._pid % 65535 + 1
        return self._pid

    # -- API ----------------------------------------------------------------
    def connect(self, host: str, port: int, ctx: ssl.SSLContext, timeout: float = 8.0) -> None:
        raw = socket.create_connection((host, port), timeout=timeout)
        try:
            raw.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        try:
            self.sock = ctx.wrap_socket(raw, server_hostname=None)
        except Exception:
            raw.close()
            raise
        self.sock.settimeout(timeout)
        flags = 0x02  # clean session
        payload = _mqtt_str(self.client_id)
        if self.username:
            flags |= 0x80
            payload += _mqtt_str(self.username)
            if self.password:
                flags |= 0x40
                payload += _mqtt_str(self.password)
        var = _mqtt_str("MQTT") + bytes([4, flags]) + struct.pack("!H", self.keepalive)
        body = var + payload
        self._send(bytes([0x10]) + _mqtt_varint(len(body)) + body)
        ptype, _, data = self._read_packet()
        if ptype != 2 or len(data) < 2:
            raise MqttError("unexpected CONNACK reply")
        if data[1] != 0:
            raise MqttError("CONNACK refused (code %d)" % data[1])
        self.connected = True

    def subscribe(self, topic: str, qos: int = 0) -> None:
        pid = self._next_pid()
        body = struct.pack("!H", pid) + _mqtt_str(topic) + bytes([qos])
        self._send(bytes([0x82]) + _mqtt_varint(len(body)) + body)

    def publish(self, topic: str, payload: Any) -> None:
        if isinstance(payload, str):
            payload = payload.encode("utf-8")
        body = _mqtt_str(topic) + payload
        self._send(bytes([0x30]) + _mqtt_varint(len(body)) + body)

    def run(self, tick: Optional[Callable[[], None]] = None, tick_every: float = 2.5) -> None:
        """BLOCKING read loop (runs in the caller's thread). Calls `tick` every
        `tick_every` seconds -- used to poll the printer periodically."""
        assert self.sock is not None
        self.sock.settimeout(1.0)
        self._stop.clear()
        last_tx = time.time()
        last_tick = 0.0
        reason = "closed"
        try:
            while not self._stop.is_set():
                if time.time() - last_tx > self.keepalive / 2:
                    self._send(b"\xc0\x00")
                    last_tx = time.time()
                if tick is not None and time.time() - last_tick >= tick_every:
                    last_tick = time.time()
                    tick()
                try:
                    ptype, flags, body = self._read_packet()
                except socket.timeout:
                    continue
                if ptype == 3:  # PUBLISH
                    qos = (flags >> 1) & 3
                    tlen = struct.unpack("!H", body[:2])[0]
                    topic = body[2:2 + tlen].decode("utf-8", "replace")
                    pos = 2 + tlen
                    pid = None
                    if qos:
                        pid = struct.unpack("!H", body[pos:pos + 2])[0]
                        pos += 2
                    payload = body[pos:]
                    if qos == 1 and pid is not None:
                        self._send(b"\x40\x02" + struct.pack("!H", pid))
                    elif qos == 2 and pid is not None:
                        self._send(b"\x50\x02" + struct.pack("!H", pid))
                    cb = self.on_message
                    if cb:
                        try:
                            cb(topic, payload)
                        except Exception:  # noqa: BLE001
                            logger.exception("error while handling an MQTT message")
                elif ptype == 6:  # PUBREL
                    if len(body) >= 2:
                        self._send(b"\x70\x02" + body[:2])
                # SUBACK(9), PINGRESP(13), PUBACK(4) etc.: ignored
        except BaseException as exc:  # noqa: BLE001
            reason = str(exc) or exc.__class__.__name__
        finally:
            was = self.connected
            self.connected = False
            self._close_socket()
            if was and not self._stop.is_set() and self.on_disconnect:
                try:
                    self.on_disconnect(reason)
                except Exception:  # noqa: BLE001
                    pass

    def _close_socket(self) -> None:
        s, self.sock = self.sock, None
        if s is not None:
            try:
                s.close()
            except OSError:
                pass

    def close(self) -> None:
        self._stop.set()
        if self.connected:
            try:
                self._send(b"\xe0\x00")
            except Exception:  # noqa: BLE001
                pass
        self.connected = False
        self._close_socket()


# --------------------------------------------------------------------------
# Printer state/telemetry (normalization of the Anycubic MQTT report)
# Based on resources/scripts/anycubic_lan_daemon.py from OrcaCubic.
# --------------------------------------------------------------------------
def rgb_to_hex(r: int, g: int, b: int) -> str:
    return "#%02x%02x%02x" % (r, g, b)


def hex_to_rgb(value: Any, fallback: Tuple[int, int, int] = (175, 175, 175)) -> List[int]:
    if isinstance(value, str):
        h = value.lstrip("#")
        if len(h) >= 6:
            try:
                return [int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)]
            except ValueError:
                pass
    elif isinstance(value, (list, tuple)) and len(value) >= 3:
        return [max(0, min(255, _as_int(value[i], fallback[i]))) for i in range(3)]
    return list(fallback)


def _slot_has_material(slot: Dict[str, Any]) -> bool:
    if not isinstance(slot, dict):
        return False
    if "available" in slot:
        return bool(slot.get("available"))
    if slot.get("_empty") is True:
        return False
    if _as_int(slot.get("status"), -1) in (0, 4) or _as_int(slot.get("edit_status"), -1) == 2:
        return False
    material = str(slot.get("type") or "").strip()
    return material not in ("", "?")


def _normalize_slot(slot: Dict[str, Any], box_id: int, source: str, loaded_slot: int = -1,
                    slot_offset: int = 0) -> Dict[str, Any]:
    local_index = max(0, _as_int(slot.get("index", slot.get("box_slot")), 0))
    color = hex_to_rgb(slot.get("color", [175, 175, 175]))
    material = str(slot.get("type") or "?").strip() or "?"
    group = []
    for gc in slot.get("color_group", []) or []:
        if isinstance(gc, (list, tuple)) and len(gc) >= 3:
            group.append(rgb_to_hex(*hex_to_rgb(gc)))
    icon_type = _as_int(slot.get("icon_type"), 0)
    global_slot = (slot_offset + local_index) if source not in ("external", "external_mcb") else -1
    brand = str(slot.get("brand") or slot.get("brand_name") or "Anycubic").strip() or "Anycubic"
    return {
        "slot": global_slot,
        "box_id": box_id,
        "box_slot": local_index,
        "source": source,
        "color": rgb_to_hex(*color),
        "type": material,
        "temp": 235 if ("PETG" in material.upper() or "+" in material) else 210,
        "loaded": bool(slot.get("loaded")) or local_index == loaded_slot or _as_int(slot.get("status"), -1) == 5,
        "available": _slot_has_material(slot),
        "brand": brand,
        "sku": str(slot.get("sku") or ""),
        "remain": _as_int(slot.get("consumables_percent"), 100),
        "icon_type": icon_type,
        "finish_type": "luminous" if icon_type == 3 else ("gradient" if icon_type in (1, 2) else "solid"),
        "color_group_hex": group or [rgb_to_hex(*color)],
    }


def _merge_reported_slots(existing: List[Dict[str, Any]], reported: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    by_index = {_as_int(s.get("index", s.get("box_slot", 0))): dict(s) for s in existing or []}
    for r in reported or []:
        idx = _as_int(r.get("index"), 0)
        by_index[idx] = {**by_index.get(idx, {}), **r}
    return [by_index[i] for i in sorted(by_index)]


class PrinterState:
    """Accumulated telemetry of one printer. Thread-safe through `lock`."""

    def __init__(self, ip: str):
        self.lock = threading.RLock()
        self.t: Dict[str, Any] = {
            "connected": False, "ip": ip, "model": "Anycubic Printer", "model_id": "",
            "firmware": "", "cn": "", "state": "idle", "progress": 0, "job_name": "",
            "curr_layer": 0, "total_layers": 0, "print_time": 0, "remain_time": 0,
            "nozzle_temp": 0, "target_nozzle_temp": 0, "bed_temp": 0, "target_bed_temp": 0,
            "camera_url": "", "upload_url": "", "light": 1, "fan": 0, "aux_fan": 0,
            "box_fan": 0, "has_aux_fan": False, "has_box_fan": False, "homed": None, "speed_mode": 2, "has_multi_color_box": False, "max_box_num": 0,
            "material_boxes": [], "external_spool": None, "filaments": [],
            "feed_status": {"box_id": None, "slot_index": -1, "type": 0, "current_status": 0, "code": 0},
            "channel_index": -1, "channel_status": 0, "has_filaments": 0,
            "last_error": "", "last_error_code": 0, "last_error_time": 0, "last_update": 0.0,
        }

    def snapshot(self) -> Dict[str, Any]:
        with self.lock:
            return json.loads(json.dumps(self.t))

    # -- ACE / rack ---------------------------------------------------------
    def _apply_box_report(self, data: Dict[str, Any], code: int = 200, replace: bool = True) -> None:
        t = self.t
        box_list = data.get("multi_color_box", []) if isinstance(data, dict) else []
        if not isinstance(box_list, list):
            return
        if replace:
            t["has_multi_color_box"] = len(box_list) > 0
        elif box_list:
            t["has_multi_color_box"] = True
        t["max_box_num"] = _as_int(data.get("max_box_num"), t.get("max_box_num") or len(box_list))
        external_boxes = [dict(b) for b in t.get("material_boxes", []) if b.get("source") == "external"]
        boxes = [] if replace else [dict(b) for b in t.get("material_boxes", []) if b.get("source") != "external"]
        for reported in box_list:
            if not isinstance(reported, dict):
                continue
            box_id = _as_int(reported.get("id"), -1)
            slots = reported.get("slots") or []
            if not isinstance(slots, list):
                slots = []
            loaded_slot = _as_int(reported.get("loaded_slot"), -1)
            all_boxes = list(boxes) + [b for b in box_list if isinstance(b, dict)]
            has_ace_box = any(_as_int(b.get("id"), -1) >= 0 for b in all_boxes)
            has_builtin_rack = any(_as_int(b.get("id"), -1) < 0 and len(b.get("slots") or []) > 1 for b in all_boxes)
            if box_id < 0:
                source = "external_mcb" if (has_ace_box and len(slots) <= 1) else "rack"
                slot_offset = 0
            else:
                source = "ace"
                slot_offset = (4 if has_builtin_rack else 0) + box_id * 4
            previous = next((b for b in boxes if _as_int(b.get("id"), -99) == box_id), None)
            if previous is not None and not replace:
                if previous.get("source") in ("rack", "external_mcb"):
                    source = previous["source"]
                slots = _merge_reported_slots(previous.get("slots", []), slots)
                boxes.remove(previous)
            norm = [_normalize_slot(s, box_id, source, loaded_slot, slot_offset)
                    for s in sorted(slots, key=lambda s: _as_int(s.get("index", s.get("box_slot", 0))))]
            dry = _normalize_drying(reported.get("drying_status"))
            pending = (t.get("pending_drying") or {}).pop(box_id, None) if source == "ace" else None
            if dry is None:
                old = next((b for b in self.t.get("material_boxes", [])
                            if _as_int(b.get("id"), -99) == box_id and b.get("source") == source), None)
                dry = pending if pending is not None else (old.get("drying") if old is not None else None)
            boxes.append({"id": box_id, "source": source, "model_id": reported.get("model_id"),
                          "loaded_slot": loaded_slot, "slots": norm,
                          "temp": _as_int(reported.get("temp"), previous.get("temp", 0) if previous else 0),
                          "humidity": _as_int(reported.get("humidity"), previous.get("humidity", 0) if previous else 0),
                          "drying": dry})
            fs = reported.get("feed_status")
            if fs:
                t["feed_status"] = {"box_id": box_id, "slot_index": _as_int(fs.get("slot_index"), -1),
                                    "type": _as_int(fs.get("type"), 0),
                                    "current_status": _as_int(fs.get("current_status"), 0),
                                    "code": _as_int(fs.get("code"), code)}
        if t.get("external_spool") is not None and not any(b.get("source") == "external" for b in boxes):
            boxes = external_boxes + boxes
        boxes.sort(key=lambda b: (b.get("source") != "external", _as_int(b.get("id"), -1)))
        t["material_boxes"] = boxes
        t["filaments"] = [s for b in boxes for s in b.get("slots", [])]
        if replace and not box_list and t.get("external_spool") is not None:
            ext = t["external_spool"]
            t["material_boxes"] = [{"id": -1, "source": "external", "loaded_slot": ext.get("box_slot", 0), "slots": [ext]}]
            t["filaments"] = [ext]

    def _apply_dry_report(self, data: Dict[str, Any], code: int = 200) -> None:
        """multiColorBox setDry / autoUpdateDryStatus: only the drying fields of each box (the
        report has no slots and, on the ACE 2 Pro, no temperature)."""
        t = self.t
        if code not in (0, 200):
            return
        for reported in data.get("multi_color_box") or []:
            if not isinstance(reported, dict):
                continue
            box_id = _as_int(reported.get("id"), -1)
            dry = _normalize_drying(reported.get("drying_status"))
            box = next((b for b in t.get("material_boxes", [])
                        if _as_int(b.get("id"), -99) == box_id and b.get("source") == "ace"), None)
            if box is None:
                t.setdefault("pending_drying", {})[box_id] = dry
                continue
            if dry is not None:
                if dry.get("humidity") is not None:
                    box["humidity"] = dry["humidity"]
                box["drying"] = dry
            if reported.get("temp") is not None:
                box["temp"] = _as_int(reported.get("temp"), box.get("temp", 0))
            if reported.get("humidity") is not None:
                box["humidity"] = _as_int(reported.get("humidity"), box.get("humidity", 0))

    def _apply_external(self, data: Dict[str, Any], code: int = 200) -> None:
        t = self.t
        prev = t.get("external_spool") or {}
        idx = max(0, _as_int(data.get("loaded_slot"), prev.get("box_slot", 0)))
        loaded = data.get("loaded", prev.get("loaded", True))
        slot = _normalize_slot({
            "index": idx, "type": data.get("type", prev.get("type", "?")),
            "color": data.get("color", prev.get("color", [175, 175, 175])), "loaded": loaded,
            "status": 5 if loaded else 4,
            "edit_status": data.get("edit_status", 1 if prev.get("available") else None),
            "brand_name": data.get("brand_name", prev.get("brand")),
            "color_group": data.get("color_group", prev.get("color_group_hex", [])),
            "icon_type": data.get("icon_type", prev.get("icon_type", 0)),
        }, -1, "external", idx)
        slot["slot"] = -1
        t["external_spool"] = slot
        existing = [b for b in t.get("material_boxes", []) if b.get("source") != "external"]
        existing.insert(0, {"id": -1, "source": "external", "loaded_slot": idx, "slots": [slot]})
        t["material_boxes"] = existing
        t["filaments"] = [s for b in existing for s in b.get("slots", [])]
        if data.get("status_type") is not None or data.get("current_status") is not None:
            t["feed_status"] = {"box_id": -1, "slot_index": idx, "type": _as_int(data.get("status_type"), 0),
                                "current_status": _as_int(data.get("current_status"), 0),
                                "code": _as_int(data.get("code"), code)}

    # -- messages -----------------------------------------------------------
    def ingest(self, ttype: str, payload: Dict[str, Any]) -> None:
        with self.lock:
            t = self.t
            code = payload.get("code", 200)
            msg_str = str(payload.get("msg", "") or "")
            state_str = str(payload.get("state", "") or "")
            # refusals of file requests show up in the Files sub-tab itself, not as a screen alert
            is_file_reply = ttype == "file" or payload.get("type") == "file"
            if not is_file_reply and ((code not in (200, 0)) or state_str in ("failed", "abnormal")):
                if msg_str:
                    shown = msg_str
                    if code == 10901 or "home" in msg_str.lower():
                        shown = "Home the axes before moving (zero not calibrated)."
                        t["homed"] = False
                    t["last_error"], t["last_error_code"], t["last_error_time"] = shown, code, int(time.time())
                    logger.warning("printer reported an error: type=%s action=%s code=%r state=%r msg=%r",
                                   ttype, payload.get("action"), code, state_str, msg_str)
            data = payload.get("data")
            action = payload.get("action")
            cam = _find_key(data, "rtspUrl")
            if cam:
                t["camera_url"] = cam

            if ttype in ("tempature", "temp"):
                if isinstance(data, dict):
                    self._apply_temp(data)
            elif ttype == "info":
                if isinstance(data, dict):
                    temp = data.get("temp") or {}
                    if temp:
                        self._apply_temp(temp)
                    proj = data.get("project") or {}
                    if isinstance(proj, dict) and proj:
                        self._apply_project(proj, proj.get("state"))
                    elif str(t.get("status_state") or "").lower() != "busy":
                        # no job in the info report: the last one ended (finished / stopped) and the
                        # printer is not busy -- do not keep showing the last "printing" state
                        self._end_job_if_stale(force=True)
                    for key in ("modelName", "deviceName"):
                        if data.get(key):
                            t["model"] = data[key]
                    if data.get("version"):
                        t["firmware"] = str(data["version"])
                    urls = data.get("urls") or {}
                    if urls.get("rtspUrl"):
                        t["camera_url"] = urls["rtspUrl"]
                    if urls.get("fileUploadurl"):
                        t["upload_url"] = urls["fileUploadurl"]
            elif ttype == "print":
                # job reports pushed by the printer (start, progress, pause, finish, stop)
                pdata = data if isinstance(data, dict) else {}
                pstate = state_str or str(pdata.get("state") or "")
                if pstate and pstate != t.get("project_state"):
                    logger.info("print report: action=%r state=%r progress=%r", action, pstate, pdata.get("progress"))
                if pstate or pdata:
                    self._apply_project(pdata, pstate or t.get("project_state"))
            elif ttype == "status":
                if state_str:
                    t["status_state"] = state_str
                    t["state"] = state_str
                    if state_str.lower() == "free":
                        self._end_job_if_stale()
            elif ttype == "axis":
                if code != 200 and msg_str:
                    t["last_error"], t["last_error_code"], t["last_error_time"] = msg_str, code, int(time.time())
            elif ttype == "fan":
                if isinstance(data, dict):
                    t["fan"] = data.get("fan_speed_pct", data.get("speed", t["fan"]))
                    t["aux_fan"] = data.get("aux_fan_speed_pct", t["aux_fan"])
                    t["box_fan"] = data.get("box_fan_level", t["box_fan"])
                    # only show the auxiliary/exhaust fan buttons if the printer reports them
                    if "aux_fan_speed_pct" in data:
                        t["has_aux_fan"] = True
                    if "box_fan_level" in data:
                        t["has_box_fan"] = True
            elif ttype == "light":
                if isinstance(data, dict):
                    lights = data.get("lights") or []
                    if lights:
                        t["light"] = lights[0].get("status", t["light"])
            elif ttype == "multiColorBox":
                if isinstance(data, dict):
                    if action == "getInfo":
                        self._apply_box_report(data, code)
                    elif action in ("refresh", "setInfo", "feedFilament"):
                        self._apply_box_report(data, code, replace=False)
                    elif action in ("setDry", "autoUpdateDryStatus"):
                        self._apply_dry_report(data, code)
            elif ttype == "extfilbox" and action in ("reportInfo", "setInfo", "getInfo", None):
                if isinstance(data, dict):
                    self._apply_external(data, code)
            elif ttype == "extrudeControl":
                if isinstance(data, dict):
                    t["channel_index"] = data.get("index", t.get("channel_index", -1))
                    t["channel_status"] = data.get("current_status", t.get("channel_status", 0))
                    t["has_filaments"] = data.get("has_filaments", t.get("has_filaments", 0))
                    t["channel_reports"] = _as_int(t.get("channel_reports"), 0) + 1
            elif ttype == "peripherie":
                if isinstance(data, dict) and data.get("multiColorBox"):
                    t["has_multi_color_box"] = True
            t["last_update"] = time.time()

    def _apply_project(self, proj: Dict[str, Any], state: Any) -> None:
        t = self.t
        st = str(state or "").strip()
        if st:
            t["project_state"] = st
            t["state"] = st
            t["project_ts"] = time.time()
        for key, src in (("progress", "progress"), ("job_name", "filename"), ("curr_layer", "curr_layer"),
                         ("total_layers", "total_layers"), ("remain_time", "remain_time"),
                         ("print_time", "print_time"), ("speed_mode", "print_speed_mode")):
            if proj.get(src) is not None:
                t[key] = proj[src]
        if st.lower() in JOB_DONE_STATES:
            t["progress"] = 100
            t["remain_time"] = 0

    def _end_job_if_stale(self, force: bool = False) -> None:
        """The printer says it is free: a job state still marked as active is left over from a job
        that ended without a final report (the info report simply stops carrying the project)."""
        t = self.t
        proj = str(t.get("project_state") or "").lower()
        if not proj or proj in JOB_DONE_STATES or proj in JOB_ENDED_STATES or "pause" in proj:
            return
        if force or time.time() - _as_float(t.get("project_ts"), 0) > JOB_STALE_SECONDS:
            logger.info("job state %r left over after the job ended; printer is free", proj)
            if proj in ("printing", "print", "running") and _as_int(t.get("progress")) >= 90:
                t["project_state"] = "finished"
                t["progress"], t["remain_time"] = 100, 0
            else:
                t["project_state"] = None

    def _apply_temp(self, d: Dict[str, Any]) -> None:
        t = self.t
        t["nozzle_temp"] = d.get("curr_nozzle_temp", t["nozzle_temp"])
        t["target_nozzle_temp"] = d.get("target_nozzle_temp", t["target_nozzle_temp"])
        t["bed_temp"] = d.get("curr_hotbed_temp", t["bed_temp"])
        t["target_bed_temp"] = d.get("target_hotbed_temp", t["target_bed_temp"])


# --------------------------------------------------------------------------
# Printer client: HTTP handshake, MQTT/TLS, commands, upload
# --------------------------------------------------------------------------
class PrinterError(Exception):
    pass


class UploadCancelled(Exception):
    pass


USER_AGENT = "AnycubicSlicerNext/2.0.0.2"
CLIENT_HEADERS = {
    "User-Agent": USER_AGENT,
    "X-BBL-Client-Name": "AnycubicSlicerNext",
    "X-BBL-Client-Type": "slicer",
    "X-BBL-Client-Version": "01.03.09.04",
}

QUERY_TYPES = ["tempature", "fan", "status", "peripherie", "multiColorBox", "extfilbox",
               "info", "light", "extrudeControl"]


class DetailsUnsupported(Exception):
    """The printer does not provide file images for this storage."""


def _shorten_for_log(value: Any) -> Any:
    """Readable diagnostics: an embedded image becomes '<1234 chars: iVBOR...>'."""
    if isinstance(value, dict):
        return {k: _shorten_for_log(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_shorten_for_log(v) for v in value[:50]]
    if isinstance(value, str) and len(value) > 240:
        return "<%d chars: %s...>" % (len(value), value[:60])
    return value


def _parse_size(v: Any) -> Optional[int]:
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return int(v)
    m = re.match(r"^\s*([\d.]+)\s*([KMGT]?)i?B?\s*$", str(v), re.I)
    if not m:
        return None
    return int(float(m.group(1)) * {"": 1, "K": 1024, "M": 1024 ** 2, "G": 1024 ** 3, "T": 1024 ** 4}[m.group(2).upper()])


def _find_size(value: Any, names: Tuple[str, ...], depth: int = 0) -> Optional[int]:
    if depth > 3 or not isinstance(value, dict):
        return None
    for k, v in value.items():
        if k in names:
            n = _parse_size(v)
            if n is not None:
                return n
    for v in value.values():
        n = _find_size(v, names, depth + 1)
        if n is not None:
            return n
    return None


_IMAGE_PREFIXES = {"iVBOR": "image/png", "/9j/": "image/jpeg", "R0lGOD": "image/gif", "UklGR": "image/webp"}
_THUMB_KEYS = ("thumbnail", "thumb", "image", "img", "preview", "cover", "pic", "png")


def find_thumbnail(value: Any, depth: int = 0) -> str:
    """The image can come with other names or deeper in the reply. Returns an <img> src."""
    if depth > 4 or value is None:
        return ""
    if isinstance(value, str):
        v = value.strip()
        if v.startswith("data:image"):
            return v
        for prefix, mime in _IMAGE_PREFIXES.items():
            if v.startswith(prefix) and len(v) > 8:
                return "data:%s;base64,%s" % (mime, v)
        return ""
    if isinstance(value, dict):
        for k in _THUMB_KEYS:
            if k in value:
                found = find_thumbnail(value[k], depth + 1)
                if found:
                    return found
        for v in value.values():
            found = find_thumbnail(v, depth + 1)
            if found:
                return found
    if isinstance(value, list):
        for v in value[:20]:
            found = find_thumbnail(v, depth + 1)
            if found:
                return found
    return ""


def sanitize_filename(raw: str, default: str = "print.gcode") -> str:
    base = (raw or "").replace("\\", "/").split("/")[-1].strip()
    base = re.sub(r'[<>:"|?*\x00-\x1f]', "_", base)
    return base or default


def start_filename_for_print(filename: str) -> str:
    """A local `.gcode.3mf` task starts with the internal `.gcode` name."""
    name = filename
    if name.lower().endswith(".3mf"):
        name = name[:-4]
    if not name.lower().endswith(".gcode"):
        name += ".gcode"
    return name


class AnycubicClient:
    def __init__(self, ip: str, on_state: Optional[Callable[[], None]] = None,
                 on_link: Optional[Callable[[bool, str], None]] = None,
                 poll_interval: float = 2.5):
        self.ip = ip
        self.state = PrinterState(ip)
        self.on_state = on_state
        self.on_link = on_link
        self.poll_interval = poll_interval
        self.info: Dict[str, Any] = {}
        self.creds: Dict[str, Any] = {}
        self.model_id = ""
        self.device_id = ""
        self.mqtt: Optional[MiniMqtt] = None
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._last_push = 0.0
        self.link_up = False
        self.last_error = ""
        self.ready = threading.Event()  # "set" after the first successful link
        self._file_lock = threading.Lock()          # one file request at a time
        self._file_waiter: Optional[Tuple[str, "queue.Queue[Dict[str, Any]]"]] = None
        self.recent: List[Dict[str, Any]] = []     # latest messages (Files tab diagnostics)
        self._hidden_state: Dict[str, bool] = {}   # hidden memory folders (test_model)
        self._details_variant: Dict[str, int] = {}
        self._details_unsupported: Dict[str, int] = {}
        self._capacity: Dict[str, Optional[Dict[str, int]]] = {}
        self._copy_support: Any = None            # None = not tested, False = not accepted, int = accepted action
        self._delete_variant: Optional[int] = None
        self._rename_variant: Optional[int] = None

    # -- HTTP -----------------------------------------------------------------
    def _http(self, method: str, path: str, timeout: float = 4.0, headers: Optional[Dict[str, str]] = None,
              body: Optional[bytes] = None) -> Tuple[int, bytes]:
        conn = http.client.HTTPConnection(self.ip, HTTP_PORT, timeout=timeout)
        try:
            conn.request(method, path, body=body, headers=headers or {})
            resp = conn.getresponse()
            return resp.status, resp.read()
        finally:
            conn.close()

    def fetch_info(self, timeout: float = 4.0) -> Dict[str, Any]:
        status, data = self._http("GET", "/info", timeout=timeout)
        if status != 200:
            raise PrinterError("/info answered HTTP %d" % status)
        info = json.loads(data.decode("utf-8", "replace"))
        if not isinstance(info, dict):
            raise PrinterError("invalid /info")
        self.info = info
        t = self.state.t
        with self.state.lock:
            t["model"] = info.get("deviceName") or info.get("modelName") or t["model"]
            t["model_id"] = str(info.get("modelId", t["model_id"]))
            t["firmware"] = info.get("firmwareVersion") or info.get("firmware") or info.get("version") or t["firmware"]
            t["cn"] = info.get("cn", t["cn"])
        return info

    def handshake(self) -> Dict[str, Any]:
        info = self.fetch_info()
        token = str(info.get("token", ""))
        if len(token) < 32:
            raise PrinterError("printer token missing/short in /info")
        k1, k2 = token[:16], token[16:32]
        ts = _now_ms()
        nonce = _rand_alnum(6)
        sign = hashlib.md5((hashlib.md5(k1.encode()).hexdigest() + str(ts) + nonce).encode()).hexdigest()
        did = "orca-" + (str(info.get("cn") or "") or _rand_alnum(8))
        path = "/ctrl?ts=%d&nonce=%s&sign=%s&did=%s" % (ts, nonce, sign, urllib.parse.quote(did))
        status, data = self._http("POST", path, timeout=8.0,
                                  headers={"User-Agent": USER_AGENT, "Content-Length": "0"})
        if status != 200:
            raise PrinterError("/ctrl answered HTTP %d" % status)
        res = json.loads(data.decode("utf-8", "replace"))
        d = res.get("data") or {}
        iv = str(d.get("token", "")).encode()
        enc = base64.b64decode(str(d.get("info", "")))
        plain = aes128_cbc_decrypt(enc, k2.encode(), iv)
        creds = json.loads(plain.decode("utf-8"))
        self.creds = creds
        self.model_id = str(creds.get("modelId") or creds.get("modeId") or info.get("modelId") or "")
        self.device_id = str(creds.get("deviceId") or "")
        if not self.model_id or not self.device_id:
            raise PrinterError("credentials without modelId/deviceId")
        return creds

    # -- MQTT -----------------------------------------------------------------
    def _tls_ctx(self, with_cert: bool) -> Tuple[ssl.SSLContext, List[str]]:
        ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        try:
            ctx.set_ciphers("DEFAULT:@SECLEVEL=0")
        except ssl.SSLError:
            pass
        tmp: List[str] = []
        if with_cert:
            crt, key = self.creds.get("devicecrt"), self.creds.get("devicepk")
            if crt and key:
                def pem(v: str) -> bytes:
                    return v.encode() if "BEGIN" in v else base64.b64decode(v)
                paths = []
                for blob in (crt, key):
                    fd, p = _mkstemp(".pem", "k4_")
                    with os.fdopen(fd, "wb") as f:
                        f.write(pem(str(blob)))
                    paths.append(p)
                    tmp.append(p)
                ctx.load_cert_chain(paths[0], paths[1])
        return ctx, tmp

    def topic(self, ns: str, ttype: str) -> str:
        return "anycubic/anycubicCloud/v1/%s/printer/%s/%s/%s" % (ns, self.model_id, self.device_id, ttype)

    def _connect_mqtt(self) -> MiniMqtt:
        port = MQTT_PORT
        broker = str(self.creds.get("broker") or "")
        if ":" in broker:
            port = _as_int(broker.rsplit(":", 1)[1], MQTT_PORT) or MQTT_PORT
        last: Optional[BaseException] = None
        for with_cert in (False, True):
            if with_cert and not (self.creds.get("devicecrt") and self.creds.get("devicepk")):
                break
            ctx, tmp = self._tls_ctx(with_cert)
            m = MiniMqtt("orca-kobra-" + _rand_alnum(8), str(self.creds.get("username") or ""),
                         str(self.creds.get("password") or ""))
            try:
                m.connect(self.ip, port, ctx)
                return m
            except BaseException as exc:  # noqa: BLE001
                last = exc
                m.close()
                logger.info("MQTT without/with certificate failed (cert=%s): %s", with_cert, exc)
            finally:
                for p in tmp:
                    try:
                        os.unlink(p)
                    except OSError:
                        pass
        raise PrinterError("MQTT: %s" % (last,))

    # -- life cycle ---------------------------------------------------------
    def start(self) -> bool:
        self._stop.clear()
        self._thread = _spawn(self._run, "anycubic-link-" + self.ip)
        return self._thread is not None

    def stop(self) -> None:
        self._stop.set()
        m = self.mqtt
        if m:
            m.close()
        self._set_link(False, "disconnected")

    def _set_link(self, up: bool, why: str = "") -> None:
        changed = up != self.link_up
        self.link_up = up
        with self.state.lock:
            self.state.t["connected"] = up
        if up:
            self.ready.set()
        if changed and self.on_link:
            try:
                self.on_link(up, why)
            except Exception:  # noqa: BLE001
                logger.exception("on_link failed")

    def _run(self) -> None:
        backoff = 2.0
        while not self._stop.is_set():
            try:
                self.handshake()
                m = self._connect_mqtt()
                self.mqtt = m
                m.on_message = self._on_message
                m.subscribe("anycubic/anycubicCloud/v1/printer/public/%s/%s/#" % (self.model_id, self.device_id))
                self.last_error = ""
                self._set_link(True, "connected")
                backoff = 2.0
                self.query_all()
                m.run(tick=self._tick, tick_every=self.poll_interval)
                reason = "MQTT connection closed"
            except BaseException as exc:  # noqa: BLE001
                reason = str(exc) or exc.__class__.__name__
                self.last_error = reason
                logger.info("link with %s dropped/failed: %s", self.ip, reason)
            if self.link_up:
                self._set_link(False, reason)
            elif not self.ready.is_set() and self.on_link:
                # first attempt failed: tell the UI once
                try:
                    self.on_link(False, reason)
                except Exception:  # noqa: BLE001
                    pass
            m2, self.mqtt = self.mqtt, None
            if m2:
                m2.close()
            self._stop.wait(backoff)
            backoff = min(backoff * 1.7, 15.0)

    def _tick(self) -> None:
        self.query_all()
        self._notify(force=True)

    def _notify(self, force: bool = False) -> None:
        now = time.time()
        if not force and now - self._last_push < 0.4:
            return
        self._last_push = now
        if self.on_state:
            try:
                self.on_state()
            except Exception:  # noqa: BLE001
                logger.exception("on_state failed")

    def _on_message(self, topic: str, raw: bytes) -> None:
        try:
            payload = json.loads(raw.decode("utf-8", "ignore"))
            parts = topic.split("/")
            ttype = parts[-2] if len(parts) >= 2 else ""
            if isinstance(payload, dict):
                self._remember(topic, payload)
                if ttype == "file" or payload.get("type") == "file":
                    w = self._file_waiter
                    if w is not None and (payload.get("action") == w[0] or
                                          (not payload.get("action") and _as_int(payload.get("code"), 200) not in (0, 200))):
                        w[1].put(payload)
                self.state.ingest(ttype, payload)
                self._notify()
        except Exception:  # noqa: BLE001
            logger.debug("MQTT message ignored", exc_info=True)

    # -- sending commands ---------------------------------------------------
    def send(self, ns: str, ttype: str, action: str, data: Any = None) -> None:
        m = self.mqtt
        if m is None or not m.connected:
            raise PrinterError("printer not connected")
        msg = {"type": ttype, "action": action, "msgid": _rand_hex(32), "timestamp": _now_ms(), "data": data}
        m.publish(self.topic(ns, ttype), json.dumps(msg))
        if ttype not in ("tempature", "info", "status", "fan", "light", "peripherie", "extrudeControl",
                         "multiColorBox", "extfilbox") or action not in ("query", "getInfo"):
            self._remember("sent:" + self.topic(ns, ttype), msg)

    def _remember(self, topic: str, payload: Dict[str, Any]) -> None:
        parts = topic.split("/")
        kind = parts[-2] if len(parts) >= 2 else topic
        ok = _as_int(payload.get("code"), 200) in (0, 200)
        if kind in ("tempature", "temp", "fan", "light") and ok:
            return
        if parts and parts[-1] == "report" and ok and kind in (
                "info", "multiColorBox", "peripherie", "status", "extfilbox", "extrudeControl"):
            return   # periodic reports: they would only push the file messages out
        if not payload.get("type") and ok and not topic.startswith("sent:"):
            return   # empty acknowledgement of a routine query
        self.recent.append({"time": int(time.time()), "topic": ("sent:" if topic.startswith("sent:") else "")
                            + "/".join(parts[-2:]), "payload": _shorten_for_log(payload)})
        del self.recent[:-120]

    def query_all(self) -> None:
        for q in QUERY_TYPES:
            try:
                self.send("slicer", q, "getInfo" if q in ("multiColorBox", "extfilbox", "extrudeControl") else "query")
            except PrinterError:
                return

    # high-level commands (same topics/payloads as the OrcaCubic daemon)
    def print_ctl(self, action: str) -> None:           # pause | resume | stop
        self.send("slicer", "print", action, None)

    def set_speed_mode(self, mode: int) -> None:
        self.send("slicer", "print", "setSpeedMode", {"print_speed_mode": int(mode)})
        self.state.t["speed_mode"] = int(mode)

    def set_light(self, on: bool) -> None:
        self.send("web", "light", "control", {"type": 3, "status": 1 if on else 0, "brightness": 100 if on else 0})
        self.state.t["light"] = 1 if on else 0

    def set_temp(self, heater: str, value: int) -> None:
        if heater == "nozzle":
            data = {"type": 0, "target_hotbed_temp": 0, "target_nozzle_temp": int(value)}
            self.state.t["target_nozzle_temp"] = int(value)
        else:
            data = {"type": 1, "target_hotbed_temp": int(value), "target_nozzle_temp": 0}
            self.state.t["target_bed_temp"] = int(value)
        self.send("web", "tempature", "set", data)

    def set_fan(self, pct: int, which: str = "model") -> None:
        """which: "model" (part), "aux" (auxiliary) or "box" (exhaust/chamber).
        aux/box: the field names come from the printer telemetry (aux_fan_speed_pct,
        box_fan_level); the write command is an assumption and has NOT been confirmed on hardware."""
        pct = max(0, min(100, int(pct)))
        field, key = {"model": ("fan_speed_pct", "fan"), "aux": ("aux_fan_speed_pct", "aux_fan"),
                      "box": ("box_fan_level", "box_fan")}.get(which, ("fan_speed_pct", "fan"))
        self.send("web", "fan", "setSpeed", {field: pct})
        self.state.t[key] = pct
        logger.info("fan %s -> %s%% (field %s)", which, pct, field)

    def jog(self, axis: str, direction: int, dist: float) -> None:
        ax = {"X": 1, "Y": 2, "Z": 3, "XY": 4, "XYZ": 5}.get(axis.upper(), 1)
        self.send("web", "axis", "move", {"axis": ax, "move_type": 1 if direction > 0 else 0, "distance": abs(float(dist))})

    def home(self, axis: str = "XYZ") -> None:
        a = axis.upper()
        ax = 5 if a == "XYZ" else (4 if a == "XY" else (3 if a == "Z" else 1))
        self.send("web", "axis", "move", {"axis": ax, "move_type": 2, "distance": 0})
        self.state.t["homed"] = True

    def motors_off(self) -> None:
        self.send("web", "axis", "turnOff", None)
        self.state.t["homed"] = False

    def switch_channel(self, index: int) -> None:
        self.send("web", "extrudeControl", "switchChannel", {"index": max(0, min(3, int(index)))})

    def feed_filament(self, box_id: int, slot: int, mat: str = "PLA") -> None:
        self.send("web", "multiColorBox", "feedFilament", {"multi_color_box": [
            {"id": int(box_id), "feed_status": {"slot_index": int(slot), "type": 1, "material_type": mat}}]})
        self.send("web", "extrudeControl", "switchChannel", {"index": int(slot)})

    def set_drying(self, box_id: int, on: bool, target_temp: int = 45, minutes: int = 240) -> None:
        """Starts/stops the ACE dryer (multiColorBox/setDry, as Anycubic Slicer Next)."""
        status = {"status": 1 if on else 0, "target_temp": int(target_temp) if on else 0,
                  "duration": int(minutes) if on else 0, "remain_time": None}
        self.send("web", "multiColorBox", "setDry", {"multi_color_box": [{"id": int(box_id), "drying_status": status}]})

    def unfeed_filament(self, box_id: int, slot: int) -> None:
        self.send("web", "multiColorBox", "feedFilament", {"multi_color_box": [
            {"id": int(box_id), "feed_status": {"slot_index": int(slot), "type": 2}}]})

    def set_slot_material(self, box_id: int, index: int, mtype: str, rgb: List[int], brand: str = "Anycubic",
                          external: bool = False) -> None:
        if external:
            self.send("web", "extfilbox", "setInfo", {"type": mtype, "color": rgb})
            return
        self.send("web", "multiColorBox", "setInfo", {"multi_color_box": [{"id": int(box_id), "slots": [{
            "index": int(index), "type": mtype, "brand": brand, "color": rgb,
            "color_group": [rgb + [255]], "icon_type": 0}]}]})

    # -- printer files (protocol confirmed by KX-Bridge on the Kobra X) -----------------------
    def file_request(self, action: str, data: Any, timeout: float = 10.0, ns: str = "slicer",
                     silent_ok: bool = False) -> Optional[Dict[str, Any]]:
        """Sends file/<action> and waits for the file/report of the same action.

        With silent_ok=True, a missing reply returns None instead of raising PrinterError
        (the Kobra 4 deletes folders without sending the report)."""
        with self._file_lock:
            q: "queue.Queue[Dict[str, Any]]" = queue.Queue()
            self._file_waiter = (action, q)
            try:
                self.send(ns, "file", action, data)
                end = time.time() + timeout
                while True:
                    left = end - time.time()
                    if left <= 0:
                        if silent_ok:
                            return None
                        raise PrinterError("the printer did not respond (%s)" % action)
                    try:
                        rep = q.get(timeout=left)
                    except queue.Empty:
                        continue
                    st = str(rep.get("state") or "")
                    code = _as_int(rep.get("code"), 200)
                    if st == "failed" or code not in (0, 200):
                        raise PrinterError("%s refused (code %s: %s)" % (action, code, rep.get("msg") or ""))
                    return rep
            finally:
                self._file_waiter = None

    def list_files(self, root: str, path: str = "/") -> List[Dict[str, Any]]:
        action = "listUdisk" if root == "udisk" else "listLocal"
        out: List[Dict[str, Any]] = []
        page = 1
        while page <= 20:
            rep = self.file_request(action, {"page_num": page, "page_size": 200, "path": path or "/"})
            recs = (rep.get("data") or {}).get("records") or []
            out.extend(r for r in recs if isinstance(r, dict))
            if len(recs) < 200:
                break
            page += 1
        if root == "local" and (path or "/") == "/":
            out.extend(self._hidden_local_folders({str(r.get("filename") or "") for r in out}))
        return out

    # Folders the printer keeps in memory but leaves out of the root list. Anycubic printers
    # ship the sample models in "test_model" (the printer screen shows the folder);
    # listing it by name works even though it does not show up in "/".
    HIDDEN_LOCAL_FOLDERS = ("test_model",)

    def _hidden_local_folders(self, listed: set) -> List[Dict[str, Any]]:
        found = []
        for name in self.HIDDEN_LOCAL_FOLDERS:
            if name in listed or self._hidden_state.get(name) is False:
                continue
            try:
                rep = self.file_request("listLocal", {"page_num": 1, "page_size": 200, "path": "/" + name}, 6.0)
                recs = (rep.get("data") or {}).get("records") or []
            except PrinterError:
                recs = []
            if not recs:
                self._hidden_state[name] = False   # a missing folder can also come back as an empty list
                continue
            self._hidden_state[name] = True
            newest = max([_as_int(r.get("timestamp"), 0) for r in recs if isinstance(r, dict)] or [0])
            found.append({"filename": name, "is_dir": True, "size": 0, "timestamp": newest, "hidden": True})
        return found

    def entry_gone(self, root: str, path: str, filename: str) -> Optional[bool]:
        """True if the folder no longer lists the item (None if it could not be listed)."""
        try:
            names = {str(r.get("filename") or r.get("name") or "") for r in self.list_files(root, path)}
        except PrinterError:
            return None
        return filename not in names

    STORAGE_MOUNTS = {"local": "/useremain/app/gk/gcodes", "udisk": "/mnt/udisk"}

    def file_details(self, root: str, filename: str, count_refusal: bool = True,
                     timeout: float = 8.0) -> Dict[str, Any]:
        """Image and data of a file. The Kobra 4 (firmware 1.2.1.3) accepts the first format in the
        internal memory and refuses all of them on the USB drive; after 2 files refused in every
        format, the storage is treated as having no images until OrcaSlicer restarts."""
        if self._details_unsupported.get(root, 0) >= 2:
            raise DetailsUnsupported(root)
        rel = filename.lstrip("/")
        folder, _, base = rel.rpartition("/")
        variants = [
            ("slicer", {"root": root, "filename": rel}),
            ("slicer", {"root": root, "filename": base}),
            ("slicer", {"root": root, "filename": "/" + rel}),
            ("slicer", {"root": root, "filename": self.STORAGE_MOUNTS[root] + "/" + rel}),
            ("slicer", {"root": root, "path": "/" + folder, "filename": base}),
            ("web", {"root": root, "filename": rel}),
        ]
        best = self._details_variant.get(root)
        order = list(range(len(variants)))
        if best is not None:
            order.remove(best)
            order.insert(0, best)
        last: Optional[Exception] = None
        for i in order:
            ns, data = variants[i]
            try:
                rep = self.file_request("fileDetails", data, timeout=timeout, ns=ns)
            except PrinterError as exc:
                last = exc
                if "did not respond" in str(exc):
                    break   # no reply: the other formats will not get one either
                continue
            self._details_variant[root] = i
            d = rep.get("data") or {}
            return d.get("file_details") if isinstance(d.get("file_details"), dict) else d
        if count_refusal and self._details_variant.get(root) is None and last is not None and "did not respond" not in str(last):
            self._details_unsupported[root] = self._details_unsupported.get(root, 0) + 1
        raise last or PrinterError("fileDetails refused")

    def rename_file(self, root: str, path: str, old: str, new: str) -> None:
        """file/renameFile. Field names from Anycubic Slicer Next (FileRename: path, old_filename,
        new_filename; the Kobra reports file_rename_support). Tries the formats in turn and
        confirms by listing the folder when the printer sends no reply."""
        path = path or "/"
        variants = [
            {"root": root, "path": path, "old_filename": old, "new_filename": new},
            {"path": path, "old_filename": old, "new_filename": new},
            {"root": root, "filename": old, "new_filename": new, "path": path},
        ]
        order = list(range(len(variants)))
        if self._rename_variant is not None:
            order.remove(self._rename_variant)
            order.insert(0, self._rename_variant)

        def renamed() -> Optional[bool]:
            try:
                names = {str(r.get("filename") or r.get("name") or "") for r in self.list_files(root, path)}
            except PrinterError:
                return None
            return new in names and old not in names

        last: Optional[Exception] = None
        for i in order:
            try:
                rep = self.file_request("renameFile", variants[i], 8.0, silent_ok=True)
            except PrinterError as exc:
                last = exc
                if "10112" not in str(exc):
                    break          # a real refusal (not "wrong format"): stop here
                continue
            if rep is None and renamed() is not True:
                last = PrinterError("the printer did not respond (renameFile)")
                continue
            self._rename_variant = i
            logger.info("renamed %s%s -> %s (%s, format %d)", path.rstrip("/") + "/", old, new, root, i)
            return
        raise last or PrinterError("renameFile refused")

    def delete_files(self, root: str, path: str, filenames: List[str]) -> None:
        """Different firmwares accept different formats: tries deleteBatch (KX-Bridge, Kobra X)
        and deleteLocal/deleteUdisk (Anycubic app) and remembers what the printer accepted."""
        path = path or "/"
        act = "deleteUdisk" if root == "udisk" else "deleteLocal"
        variants: List[Callable[[str], Tuple[str, str, Dict[str, Any]]]] = [
            lambda f: ("deleteBatch", "slicer", {"root": root, "files": [{"path": path, "filename": f}]}),
            lambda f: (act, "slicer", {"path": path, "filename": f, "filetype": -1}),
            lambda f: (act, "web", {"path": path, "filename": f, "filetype": -1}),
        ]
        order = list(range(len(variants)))
        if self._delete_variant is not None:
            order.remove(self._delete_variant)
            order.insert(0, self._delete_variant)
        if len(filenames) > 1 and self._delete_variant in (None, 0):
            # a single deleteBatch for all of them (the Kobra 4 reports delete_batch_support)
            try:
                rep = self.file_request("deleteBatch", {"root": root, "files": [{"path": path, "filename": f} for f in filenames]},
                                        6.0 + 0.5 * len(filenames), silent_ok=True)
            except PrinterError:
                rep = {}
            if rep is not None and rep:
                self._delete_variant = 0
                return
            if rep is None:
                filenames = [f for f in filenames if self.entry_gone(root, path, f) is not True]
                if not filenames:
                    self._delete_variant = 0
                    return
        for f in filenames:
            last: Optional[Exception] = None
            for i in order:
                action, ns, data = variants[i](f)
                try:
                    rep = self.file_request(action, data, 6.0, ns=ns, silent_ok=True)
                except PrinterError as exc:
                    last = exc
                    if "10112" not in str(exc):
                        break          # a real refusal (not "wrong format"): stop here
                    continue
                if rep is None and self.entry_gone(root, path, f) is not True:
                    last = PrinterError("the printer did not respond (%s)" % action)
                    continue
                self._delete_variant = i   # it replied, or did not reply but the item is gone
                last = None
                break
            if last is not None:
                if self.entry_gone(root, path, f) is True:
                    continue
                raise last

    # -- storage usage and USB drive -> memory copy --------------------------------------
    # No documented LAN command reports the capacity or copies files. The usage adds up the
    # size of the files in every folder; the capacity and copy requests are
    # tried once, and only count if the printer replies.
    CAPACITY_ACTIONS = ("getStorageInfo", "storageInfo", "diskInfo", "getDiskInfo")
    COPY_ACTIONS = (
        ("copyUdiskToLocal", lambda it: {"files": it}),
        ("udiskToLocal", lambda it: {"files": it}),
        ("copyFile", lambda it: {"src_root": "udisk", "dst_root": "local", "files": it}),
        ("copy", lambda it: {"root": "udisk", "target": "local", "files": it}),
    )

    def storage_usage(self, root: str) -> Dict[str, Any]:
        total, files, folders, truncated = 0, 0, 0, False
        queue_ = ["/"]
        while queue_:
            if folders >= 40:
                truncated = True
                break
            folder = queue_.pop(0)
            try:
                recs = self.list_files(root, folder)
            except PrinterError:
                if folder == "/":
                    raise
                continue
            folders += 1
            for r in recs:
                name = str(r.get("filename") or "")
                if r.get("is_dir"):
                    if name and name != "System Volume Information":
                        queue_.append(("" if folder == "/" else folder) + "/" + name)
                else:
                    total += _as_int(r.get("size"), 0)
                    files += 1
        return {"files_bytes": total, "files": files, "folders": folders, "truncated": truncated,
                "capacity": self._probe_capacity(root)}

    def _probe_capacity(self, root: str) -> Optional[Dict[str, int]]:
        if root in self._capacity:
            return self._capacity[root]
        found = None
        for action in self.CAPACITY_ACTIONS:
            try:
                rep = self.file_request(action, {"root": root}, 3.0, silent_ok=True)
            except PrinterError:
                continue
            if rep is None:
                break      # the printer ignores unknown actions: the others too
            d = rep.get("data") or {}
            tot = _find_size(d, ("total", "total_size", "totalSize", "total_space", "capacity", "disk_total"))
            free = _find_size(d, ("free", "free_size", "freeSize", "free_space", "available", "remain", "remain_size"))
            used = _find_size(d, ("used", "used_size", "usedSize", "used_space"))
            if tot and (free is not None or used is not None):
                free = free if free is not None else max(0, tot - (used or 0))
                found = {"total": tot, "free": free, "used": tot - free}
                break
        self._capacity[root] = found
        return found

    def copy_to_local(self, items: List[Dict[str, str]]) -> Dict[str, Any]:
        if self._copy_support is False:
            return {"status": "unsupported"}
        order = [self._copy_support] if isinstance(self._copy_support, int) else range(len(self.COPY_ACTIONS))
        for i in order:
            action, build = self.COPY_ACTIONS[i]
            try:
                rep = self.file_request(action, build(items), 30.0 if isinstance(self._copy_support, int) else 3.0,
                                        silent_ok=True)
            except PrinterError:
                continue
            if rep is not None:
                self._copy_support = i
                return {"status": "ok", "copied": len(items), "action": action}
            if not isinstance(self._copy_support, int):
                break      # the printer ignores unknown actions: the others too
        self._copy_support = False
        return {"status": "unsupported"}

    def start_existing(self, root: str, path: str, filename: str, auto_leveling: bool = True) -> None:
        """Prints a file that is already on the printer. Without ams_settings the printer uses the
        filament mapping stored with the file (as KX-Bridge does)."""
        self.send("slicer", "print", "start", {
            "filename": filename, "filepath": path or "/", "taskid": str(random.randint(1, 999999)),
            "task_mode": 1, "filetype": 2 if root == "udisk" else 1,
            "task_settings": {"auto_leveling": 1 if auto_leveling else 0, "vibration_compensation": 0,
                              "flow_calibration": 0},
        })

    def camera(self, start: bool) -> None:
        self.send("web", "video", "startCapture" if start else "stopCapture", None)

    # -- upload ---------------------------------------------------------------
    def upload_token(self, wait: float = 5.0) -> str:
        def token() -> str:
            url = self.state.snapshot().get("upload_url") or ""
            return urllib.parse.parse_qs(urllib.parse.urlparse(url).query).get("s", [""])[0]
        end = time.time() + wait
        tok = token()
        while not tok and time.time() < end:
            try:
                self.send("slicer", "info", "query")
            except PrinterError:
                break
            time.sleep(0.5)
            tok = token()
        return tok or str(self.info.get("token", ""))

    def upload_file(self, path: str, remote_name: str,
                    progress: Optional[Callable[[int], None]] = None,
                    cancelled: Optional[Callable[[], bool]] = None) -> Tuple[str, int]:
        """Sends `path` as multipart to /gcode_upload. Returns (md5, size)."""
        size = os.path.getsize(path)
        token = self.upload_token()
        endpoint = "/gcode_upload" + ("?s=" + urllib.parse.quote(token) if token else "")
        boundary = "----WebKitFormBoundary" + _rand_alnum(16)
        pre = ('--%s\r\nContent-Disposition: form-data; name="filename"\r\n\r\n%s\r\n'
               '--%s\r\nContent-Disposition: form-data; name="gcode"; filename="%s"\r\n'
               'Content-Type: application/octet-stream\r\n\r\n') % (boundary, remote_name, boundary, remote_name)
        pre_b = pre.encode("utf-8")
        post_b = ("\r\n--%s--\r\n" % boundary).encode("utf-8")
        headers = dict(CLIENT_HEADERS)
        headers.update({
            "Content-Type": "multipart/form-data; boundary=" + boundary,
            "Content-Length": str(len(pre_b) + size + len(post_b)),
            "X-File-Length": str(size),
        })
        md5 = hashlib.md5()
        conn = http.client.HTTPConnection(self.ip, HTTP_PORT, timeout=60)
        try:
            conn.putrequest("POST", endpoint, skip_accept_encoding=True)
            for k, v in headers.items():
                conn.putheader(k, v)
            conn.endheaders()
            conn.send(pre_b)
            sent, last_pct = 0, -1
            with open(path, "rb") as f:
                while True:
                    if cancelled and cancelled():
                        raise UploadCancelled()
                    chunk = f.read(64 * 1024)
                    if not chunk:
                        break
                    md5.update(chunk)
                    conn.send(chunk)
                    sent += len(chunk)
                    pct = int(sent * 100 / size) if size else 100
                    if progress and pct != last_pct:
                        last_pct = pct
                        progress(pct)
            conn.send(post_b)
            resp = conn.getresponse()
            body = resp.read().decode("utf-8", "ignore")
            if resp.status != 200:
                raise PrinterError("upload HTTP %d: %s" % (resp.status, body[:200]))
            try:
                j = json.loads(body)
                if isinstance(j, dict) and "code" in j and _as_int(j.get("code"), 200) != 200:
                    raise PrinterError("the printer refused the upload: %s" % (j.get("message") or j.get("msg") or j))
            except ValueError:
                pass
        finally:
            conn.close()
        return md5.hexdigest().lower(), size

    def start_print(self, filename: str, md5: str, size: int, use_ams: bool,
                    ams_mapping: List[Dict[str, Any]], tasks: Dict[str, bool]) -> None:
        data = {
            "taskid": "-1", "filename": filename, "url": "", "md5": md5, "filepath": None,
            "filetype": 1, "project_type": 1, "filesize": size,
            "ams_settings": {"use_ams": bool(use_ams), "ams_box_mapping": ams_mapping},
            "task_settings": {
                "auto_leveling": 1 if tasks.get("auto_leveling", True) else 0,
                "vibration_compensation": 1 if tasks.get("vibration_compensation") else 0,
                "flow_calibration": 1 if tasks.get("flow_calibration") else 0,
                "dry_mode": 0,
                "ai_settings": {"status": 0, "count": 0, "type": 0},
                "timelapse": {"status": 1 if tasks.get("timelapse") else 0, "count": 0, "type": 0},
                "drying_settings": {"status": 0, "target_temp": 0, "duration": 0, "remain_time": 0},
                "model_objects_skip_parts": [],
            },
        }
        self.send("slicer", "print", "start", data)


# --------------------------------------------------------------------------
# Print file adjustments (3MF / G-code) -- port of AnycubicLink.cpp
# --------------------------------------------------------------------------
_TOOL_RE = re.compile(r"^[ \t]*(T\d+)(?=[ \t\r\n;]|$)")
DEFAULT_PURGE_SCRIPT = "M83\nG28 X\nG1 E40 F300\nM106 S229\nM400 P2000\nG1 X20 F15000\nG28 X\n"


def skip_first_toolchange_in_gcode(text: str, script: str = "") -> Tuple[str, bool]:
    """Replaces the FIRST tool change (Tn) with an initial purge at the purge box.
    Same logic as OrcaCubic: takes the ; FLUSH_START .. ; FLUSH_END blocks into account."""
    script = script or DEFAULT_PURGE_SCRIPT
    if not script.endswith("\n"):
        script += "\n"
    out: List[str] = []
    replaced = False
    in_flush = False
    flush_block: List[str] = []
    found_tool = ""

    def repl(tool: str) -> str:
        return "; [Anycubic LAN plugin] first tool change (%s) replaced with an initial purge\n%s" % (tool, script)

    for line in text.splitlines(keepends=False):
        if not replaced:
            if not in_flush:
                if "; FLUSH_START" in line or ";FLUSH_START" in line:
                    in_flush, flush_block, found_tool = True, [line], ""
                    continue
                m = _TOOL_RE.match(line)
                if m:
                    replaced = True
                    out.append(repl(m.group(1)).rstrip("\n"))
                    continue
            else:
                flush_block.append(line)
                m = _TOOL_RE.match(line)
                if m:
                    found_tool = m.group(1)
                if "; FLUSH_END" in line or ";FLUSH_END" in line:
                    in_flush = False
                    if found_tool:
                        replaced = True
                        out.append(repl(found_tool).rstrip("\n"))
                    else:
                        out.extend(flush_block)
                    flush_block = []
                    continue
                continue
        out.append(line)
    if in_flush and not replaced:
        out.extend(flush_block)
    return "\n".join(out) + "\n", replaced


_PLATE_RE = re.compile(r"^Metadata/plate_(\d+)\.gcode$")


def _pick_plate_entry(names: List[str], plate_index: Optional[int]) -> Optional[str]:
    plates = {int(m.group(1)): n for n in names for m in [_PLATE_RE.match(n)] if m}
    if not plates:
        return None
    if plate_index is not None:
        for cand in (plate_index, plate_index + 1):
            if cand in plates:
                return plates[cand]
    if len(plates) == 1:
        return next(iter(plates.values()))
    return plates[max(plates)]


def first_tool_in_source(path: str, plate_index: Optional[int] = None, limit: int = 8 * 1024 * 1024) -> Optional[int]:
    """Number of the first Tn in the G-code (for the filament pre-engage)."""
    try:
        if path.lower().endswith(".3mf"):
            with zipfile.ZipFile(path) as zf:
                name = _pick_plate_entry(zf.namelist(), plate_index)
                if not name:
                    return None
                stream = zf.open(name)
        else:
            stream = open(path, "rb")
        with stream:
            read = 0
            for raw in stream:
                read += len(raw)
                m = _TOOL_RE.match(raw.decode("utf-8", "ignore"))
                if m:
                    return int(m.group(1)[1:])
                if read > limit:
                    break
    except Exception:  # noqa: BLE001
        logger.debug("first_tool_in_source failed", exc_info=True)
    return None


_SLICE_FIL_RE = re.compile(r"<filament\b([^>]*)/?>", re.I)
_ATTR_RE = re.compile(r'(\w+)\s*=\s*"([^"]*)"')
_PLATE_BLOCK_RE = re.compile(r"<plate>(.*?)</plate>", re.S | re.I)


def _norm_color(value: Any) -> str:
    v = str(value or "").strip().strip('"')
    if v.startswith("#") and len(v) >= 7:
        return v[:7].upper()
    return ""


def _filaments_from_slice_info(xml: str, plate_index: Optional[int]) -> List[Dict[str, Any]]:
    blocks = _PLATE_BLOCK_RE.findall(xml) or [xml]
    chosen = blocks[0]
    if plate_index is not None and len(blocks) > 1:
        for b in blocks:
            m = re.search(r'key="index"\s+value="(\d+)"', b)
            if m and int(m.group(1)) in (plate_index, plate_index + 1):
                chosen = b
                break
    out = []
    for attrs in _SLICE_FIL_RE.findall(chosen):
        a = dict(_ATTR_RE.findall(attrs))
        idx = _as_int(a.get("id"), 0) - 1
        if idx < 0:
            continue
        if a.get("used_g") is not None and _as_float(a.get("used_g"), 0) <= 0 and _as_float(a.get("used_m"), 0) <= 0:
            continue
        out.append({"index": idx, "type": str(a.get("type") or "PLA"), "color": _norm_color(a.get("color")) or "#AFAFAF",
                    "grams": round(_as_float(a.get("used_g"), 0), 2)})
    return sorted(out, key=lambda f: f["index"])


def _filaments_from_gcode_text(text: str) -> List[Dict[str, Any]]:
    def setting(key: str) -> List[str]:
        m = re.findall(r"^;\s*" + re.escape(key) + r"\s*=\s*(.*)$", text, re.M)
        if not m:
            return []
        raw = m[-1].strip()
        sep = ";" if ";" in raw else ","
        return [x.strip().strip('"') for x in raw.split(sep)]
    colours = setting("filament_colour") or setting("extruder_colour")
    types = setting("filament_type")
    used = setting("filament used [g]") or setting("filament used [mm]")
    n = max(len(colours), len(types))
    out = []
    for i in range(n):
        if used and i < len(used) and _as_float(used[i], 0) <= 0:
            continue
        out.append({"index": i, "type": (types[i] if i < len(types) and types[i] else "PLA"),
                    "color": _norm_color(colours[i] if i < len(colours) else "") or "#AFAFAF",
                    "grams": round(_as_float(used[i], 0), 2) if used and i < len(used) else 0})
    if used and not out and n:
        out = [{"index": 0, "type": types[0] if types else "PLA", "color": _norm_color(colours[0] if colours else "") or "#AFAFAF", "grams": 0}]
    return out


def _read_head_tail(stream: Any, size: int = 1024 * 1024) -> str:
    data = stream.read()
    if len(data) > 2 * size:
        data = data[:size] + b"\n" + data[-size:]
    return data.decode("utf-8", "ignore")


def parse_file_filaments(path: str, plate_index: Optional[int] = None) -> List[Dict[str, Any]]:
    """Filaments (index in the file, type, color) used by a .gcode / .gcode.3mf."""
    try:
        if path.lower().endswith(".3mf"):
            with zipfile.ZipFile(path) as zf:
                names = zf.namelist()
                info = next((n for n in names if n.lower().endswith("metadata/slice_info.config")), None)
                if info:
                    fils = _filaments_from_slice_info(zf.read(info).decode("utf-8", "ignore"), plate_index)
                    if fils:
                        return fils
                name = _pick_plate_entry(names, plate_index)
                if name:
                    with zf.open(name) as st:
                        return _filaments_from_gcode_text(_read_head_tail(st))
            return []
        with open(path, "rb") as st:
            return _filaments_from_gcode_text(_read_head_tail(st))
    except Exception:  # noqa: BLE001
        logger.debug("parse_file_filaments failed", exc_info=True)
        return []


_FILE_FIL_LOCK = threading.Lock()


def _file_fil_path() -> str:
    return os.path.join(_tmp_dir(), "file_filaments.json")


def _file_fil_key(ip: str, filename: str) -> str:
    base = os.path.basename(str(filename or "").replace("\\", "/")).lower()
    for ext in (".gcode.3mf", ".3mf", ".gcode"):
        if base.endswith(ext):
            base = base[:-len(ext)]
            break
    return "%s|%s" % (ip, base)


def remember_file_filaments(ip: str, filename: str, fils: List[Dict[str, Any]]) -> None:
    if not fils or not filename:
        return
    with _FILE_FIL_LOCK:
        try:
            with open(_file_fil_path(), "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                data = {}
        except (OSError, ValueError):
            data = {}
        key = _file_fil_key(ip, filename)
        data.pop(key, None)
        data[key] = fils
        while len(data) > 600:
            data.pop(next(iter(data)))
        try:
            with open(_file_fil_path(), "w", encoding="utf-8") as f:
                json.dump(data, f)
        except OSError as exc:
            logger.debug("could not save the file filaments: %s", exc)


def lookup_file_filaments(ip: str, filename: str) -> List[Dict[str, Any]]:
    with _FILE_FIL_LOCK:
        try:
            with open(_file_fil_path(), "r", encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, ValueError):
            return []
    v = data.get(_file_fil_key(ip, filename)) if isinstance(data, dict) else None
    return v if isinstance(v, list) else []


_THUMB_LOCK = threading.Lock()
_THUMB_MAX = 250
_THUMB_BLOCK_RE = re.compile(r"^;\s*thumbnail(?:_PNG)?\s+begin\s+(\d+)x(\d+)\s+\d+\s*$(.*?)^;\s*thumbnail(?:_PNG)?\s+end",
                             re.M | re.S)


def _thumb_path() -> str:
    return os.path.join(_tmp_dir(), "thumbnails.json")


def _thumb_load() -> Dict[str, Any]:
    try:
        with open(_thumb_path(), "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def remember_thumbnail(ip: str, filename: str, thumbnail: str, info: Optional[Dict[str, Any]] = None,
                       size: int = 0) -> None:
    """Keeps a file preview on disk (key: printer + file name without extension), so the Files
    tab can show it while the printer is busy printing and after OrcaSlicer restarts."""
    if not thumbnail or not filename:
        return
    with _THUMB_LOCK:
        data = _thumb_load()
        key = _file_fil_key(ip, filename)
        data.pop(key, None)
        data[key] = {"thumbnail": thumbnail, "info": info or {}, "size": int(size or 0)}
        while len(data) > _THUMB_MAX:
            data.pop(next(iter(data)))
        try:
            with open(_thumb_path(), "w", encoding="utf-8") as f:
                json.dump(data, f)
        except OSError as exc:
            logger.debug("could not save the preview: %s", exc)


def lookup_thumbnail(ip: str, filename: str, size: int = 0) -> Optional[Dict[str, Any]]:
    with _THUMB_LOCK:
        v = _thumb_load().get(_file_fil_key(ip, filename))
    if not isinstance(v, dict) or not v.get("thumbnail"):
        return None
    if size and _as_int(v.get("size"), 0) and _as_int(v.get("size"), 0) != size:
        return None   # another file with the same name
    return v


def parse_file_thumbnail(path: str, plate_index: Optional[int] = None) -> str:
    """The preview OrcaSlicer embeds in the file: plate PNG of a .gcode.3mf, or the largest
    "; thumbnail begin" block of a .gcode. Returns an <img> src or ""."""
    try:
        if path.lower().endswith(".3mf"):
            with zipfile.ZipFile(path) as zf:
                names = zf.namelist()
                pngs = {}
                for n in names:
                    m = re.match(r"(?i)^metadata/plate_(\d+)\.png$", n)
                    if m:
                        pngs[int(m.group(1))] = n
                pick = None
                if plate_index is not None:
                    pick = pngs.get(plate_index) or pngs.get(plate_index + 1)
                if pick is None and pngs:
                    pick = pngs[min(pngs)] if len(pngs) == 1 else None
                if pick is None:
                    gname = _pick_plate_entry(names, plate_index)
                    m = re.search(r"plate_(\d+)", gname or "")
                    if m:
                        pick = pngs.get(int(m.group(1)))
                if pick:
                    return "data:image/png;base64," + base64.b64encode(zf.read(pick)).decode("ascii")
                gname = _pick_plate_entry(names, plate_index)
                if gname:
                    with zf.open(gname) as st:
                        return _thumb_from_gcode(st.read(1024 * 1024).decode("utf-8", "ignore"))
            return ""
        with open(path, "rb") as st:
            return _thumb_from_gcode(st.read(1024 * 1024).decode("utf-8", "ignore"))
    except Exception:  # noqa: BLE001
        logger.debug("parse_file_thumbnail failed", exc_info=True)
        return ""


def _thumb_from_gcode(text: str) -> str:
    best, best_area = "", 0
    for m in _THUMB_BLOCK_RE.finditer(text):
        area = int(m.group(1)) * int(m.group(2))
        b64 = "".join(line.lstrip("; ").strip() for line in m.group(3).splitlines())
        if b64.startswith("iVBOR") and area > best_area:
            best, best_area = b64, area
    return "data:image/png;base64," + best if best else ""


def remember_file_preview(ip: str, filename: str, path: str, plate_index: Optional[int] = None,
                          size: int = 0) -> None:
    try:
        thumb = parse_file_thumbnail(path, plate_index)
        if thumb:
            remember_thumbnail(ip, filename, thumb, size=size)
    except Exception:  # noqa: BLE001
        logger.debug("file preview not recorded", exc_info=True)


_DETAILS_LOGGED: set = set()


def log_details_once(fname: str, d: Any) -> None:
    """Writes the fileDetails reply to the log (once per file), without the image."""
    if fname in _DETAILS_LOGGED:
        return
    _DETAILS_LOGGED.add(fname)

    def short(v: Any, depth: int = 0) -> Any:
        if isinstance(v, str):
            return v if len(v) <= 160 else "<text of %d characters>" % len(v)
        if isinstance(v, dict) and depth < 4:
            return {k: short(x, depth + 1) for k, x in v.items()}
        if isinstance(v, list) and depth < 4:
            return [short(x, depth + 1) for x in v[:16]]
        return v
    try:
        logger.info("panel: fileDetails of %s: %s", fname, json.dumps(short(d), ensure_ascii=False)[:4000])
    except Exception:  # noqa: BLE001
        pass


def filaments_from_details(d: Any) -> List[Dict[str, Any]]:
    """Tries to find the filament list in the fileDetails reply (the format varies by firmware)."""
    if not isinstance(d, dict):
        return []
    # Kobra 4 (firmware 1.2.1.3): "paint_infos": [{paint_index, material_type, paint_color: [r,g,b], filament_used (g)}]
    pi = d.get("paint_infos")
    if isinstance(pi, list) and pi:
        out = []
        for i, x in enumerate(pi):
            if not isinstance(x, dict):
                continue
            col = x.get("paint_color")
            if isinstance(col, (list, tuple)) and len(col) >= 3:
                col = rgb_to_hex(*[int(c) for c in col[:3]])
            out.append({"index": _as_int(x.get("paint_index"), i), "type": str(x.get("material_type") or "PLA"),
                        "color": _norm_color(col) or "#AFAFAF", "grams": round(_as_float(x.get("filament_used"), 0), 1)})
        if out:
            return sorted(out, key=lambda f: f["index"])
    if isinstance(pi, list):
        return []   # the printer replied, but the file has no filament list
    for key, val in d.items():
        if isinstance(val, list) and val and all(isinstance(x, dict) for x in val):
            out = []
            for i, x in enumerate(val):
                col = next((x[k] for k in x if "colo" in k.lower()), None)
                if col is None:
                    break
                if isinstance(col, (list, tuple)) and len(col) >= 3:
                    col = rgb_to_hex(*[int(c) for c in col[:3]])
                typ = next((x[k] for k in x if k.lower() in ("type", "material_type", "filament_type", "material")), "PLA")
                idx = _as_int(next((x[k] for k in x if k.lower() in ("index", "paint_index", "id", "extruder")), i), i)
                out.append({"index": idx, "type": str(typ or "PLA"), "color": _norm_color(col) or "#AFAFAF", "grams": 0})
            if out:
                return out
    cols = next((v for k, v in d.items() if "colo" in k.lower() and isinstance(v, list)), None)
    types = next((v for k, v in d.items() if ("material" in k.lower() or "type" in k.lower()) and isinstance(v, list)), None)
    if cols:
        out = []
        for i, c in enumerate(cols):
            if isinstance(c, (list, tuple)) and len(c) >= 3:
                c = rgb_to_hex(*[int(x) for x in c[:3]])
            out.append({"index": i, "type": str(types[i]) if types and i < len(types) else "PLA",
                        "color": _norm_color(c) or "#AFAFAF", "grams": 0})
        return out
    return []


def mapping_from_choice(choice: List[Dict[str, Any]], snap: Dict[str, Any]) -> List[Dict[str, Any]]:
    """[{paint_index, slot, paint_color, paint_type}] chosen in the panel -> ams_box_mapping."""
    slots = {s["slot"]: s for s in snap.get("filaments", []) if isinstance(s, dict) and _as_int(s.get("slot"), -1) >= 0}
    out = []
    for c in choice or []:
        if not isinstance(c, dict):
            continue
        slot = slots.get(_as_int(c.get("slot"), -1))
        if slot is None:
            continue
        paint = _norm_color(c.get("paint_color")) or slot.get("color")
        out.append({"ams_index": slot["slot"], "paint_index": max(0, _as_int(c.get("paint_index"), 0)),
                    "material_type": str(c.get("paint_type") or slot.get("type") or "PLA"),
                    "ams_color": hex_to_rgb(slot.get("color"), (35, 163, 199)),
                    "paint_color": hex_to_rgb(paint, (35, 163, 199))})
    return out


def build_paint_info(fils: List[Dict[str, Any]]) -> str:
    """The filament list Anycubic Slicer Next writes into its G-code, e.g.
    [{"material_type":"PLA","paint_color":[146,121,104],"paint_index":0}] -- only the filaments the
    plate uses. The printer reads it for its color mapping (fileDetails "paint_infos", its screen).
    OrcaSlicer does not write it, so the printer offered every filament of the project."""
    items = [{"material_type": str(f.get("type") or "PLA"),
              "paint_color": list(hex_to_rgb(f.get("color"), (175, 175, 175))),
              "paint_index": _as_int(f.get("index"), 0)} for f in fils]
    return json.dumps(items, separators=(",", ":"), sort_keys=True)


def add_ams_info(text: str, fils: List[Dict[str, Any]]) -> Tuple[str, bool]:
    """Writes the filament list like Anycubic Slicer Next 2.0: a "; paint_info = [...]" line inside
    the header block and an "; ams_info = begin/end" block at the end of the file."""
    if not fils or "; paint_info =" in text[:200000]:
        return text, False
    nl = "\r\n" if "\r\n" in text[:4096] else "\n"
    line = "; paint_info = " + build_paint_info(fils)
    head = text[:200000]
    i = head.find("; HEADER_BLOCK_END")
    if i >= 0:
        text = text[:i] + line + nl + text[i:]
    else:
        text = line + nl + text
    if not text.endswith(("\n", "\r")):
        text += nl
    text += nl + nl + "; ams_info = begin" + nl + line + nl + "; ams_info = end" + nl
    return text, True


def prepare_upload_file(src: str, rename_plate: bool, skip_first_toolchange: bool, purge_script: str,
                        plate_index: Optional[int] = None,
                        used_filaments: Optional[List[Dict[str, Any]]] = None) -> Tuple[str, bool, str]:
    """Returns (path_to_send, is_temporary, description). Does not change the original file.
    `used_filaments` (from parse_file_filaments) adds the Anycubic "; ams_info" block, so the printer
    only offers the filaments this plate uses."""
    notes: List[str] = []
    fils = list(used_filaments or [])
    is_3mf = src.lower().endswith(".3mf")
    if not is_3mf:
        if not skip_first_toolchange and not fils:
            return src, False, ""
        with open(src, "r", encoding="utf-8", errors="replace", newline="") as f:
            new = f.read()
        changed = False
        if skip_first_toolchange:
            new, did = skip_first_toolchange_in_gcode(new, purge_script)
            if did:
                changed = True
                notes.append("first tool change replaced")
            else:
                notes.append("no tool change found")
        new, did = add_ams_info(new, fils)
        if did:
            changed = True
            notes.append("filament list for the printer: %d filament(s)" % len(fils))
        if not changed:
            return src, False, "; ".join(notes)
        fd, tmp = _mkstemp(".gcode", "kobra_")
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            f.write(new)
        return tmp, True, "; ".join(notes)

    with zipfile.ZipFile(src) as zin:
        names = zin.namelist()
        target = _pick_plate_entry(names, plate_index)
        need_rename = bool(rename_plate and target and target != "Metadata/plate_1.gcode")
        need_edit = bool((skip_first_toolchange or fils) and target)
        if not (need_rename or need_edit):
            return src, False, ""
        new_gcode: Optional[bytes] = None
        if need_edit:
            text = zin.read(target).decode("utf-8", "replace")
            new_text, edited = text, False
            if skip_first_toolchange:
                new_text, did = skip_first_toolchange_in_gcode(new_text, purge_script)
                if did:
                    edited = True
                    notes.append("first tool change replaced")
            new_text, did = add_ams_info(new_text, fils)
            if did:
                edited = True
                notes.append("filament list for the printer: %d filament(s)" % len(fils))
            if edited:
                new_gcode = new_text.encode("utf-8")
            else:
                need_edit = False
        if not (need_rename or need_edit):
            return src, False, ""
        fd, tmp = _mkstemp(".3mf", "kobra_")
        os.close(fd)
        try:
            with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as zout:
                for item in zin.infolist():
                    data = zin.read(item.filename)
                    name = item.filename
                    if name == target:
                        if new_gcode is not None:
                            data = new_gcode
                        if need_rename:
                            name = "Metadata/plate_1.gcode"
                    elif target and name == target + ".md5":
                        if new_gcode is not None:
                            old = data.decode("ascii", "ignore").strip()
                            h = hashlib.md5(new_gcode).hexdigest()
                            data = (h.upper() if old.isupper() else h).encode("ascii")
                        if need_rename:
                            name = "Metadata/plate_1.gcode.md5"
                    zout.writestr(name, data)
            if need_rename:
                notes.append("%s -> plate_1.gcode" % os.path.basename(target))
        except BaseException:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise
        return tmp, True, "; ".join(notes)


# --------------------------------------------------------------------------
# Translation of the Anycubic telemetry -> "Bambu-style" JSON read by MachineObject
# --------------------------------------------------------------------------
# printer filament id (Bambu "generic") <-> OrcaSlicer generic preset id
FILAMENT_PRINTER_TO_ORCA: Dict[str, str] = {
    "GFL99": "OFDSrzZ8", "GFG99": "OFYPdQJh", "GFB99": "OFY9muEs", "GFB98": "OFLPAxz3",
    "GFU99": "OFgbpcy9", "GFC99": "OFLakOUI", "GFN99": "OFg8ndtj", "GFS99": "OFDvXujf",
    "GFA98": "OFWbdGsC", "GFG97": "OFgVn32e",
}
FILAMENT_ORCA_TO_PRINTER: Dict[str, str] = {v: k for k, v in FILAMENT_PRINTER_TO_ORCA.items()}

# base type -> (generic id, min temp, max temp)
_MATERIALS: List[Tuple[str, str, str, str]] = [
    ("PETG-CF", "GFG97", "220", "260"), ("PLA-CF", "GFA98", "190", "240"), ("PETG", "GFG99", "220", "250"),
    ("PLA", "GFL99", "190", "230"), ("ABS", "GFB99", "230", "260"), ("ASA", "GFB98", "240", "270"),
    ("TPU", "GFU99", "200", "230"), ("PVA", "GFS99", "190", "220"), ("PC", "GFC99", "250", "280"),
    ("PA", "GFN99", "250", "280"),
]


# The OrcaSlicer filament window (AMSMaterialsSetting) refuses "Confirm" with "Please input a valid
# value (K in 0.0~2.0)" when the slot reports K = 0. The Kobra does not report K per slot; a typical
# pressure advance value is reported only to unlock the window (the plugin does not send it to the printer).
DEFAULT_PA_K = 0.02


def _orca_id(printer_id: str) -> str:
    """OrcaSlicer identifies filaments by its own library ids ("OFDSrzZ8" = Generic PLA).
    The agent's to_orca_filament_id translation does not reach Python plugins, so the ids already
    leave here translated; with the Bambu id ("GFL99") the filament window did not find the preset."""
    return FILAMENT_PRINTER_TO_ORCA.get(printer_id, printer_id)


def resolve_material(raw_type: str) -> Dict[str, str]:
    up = (raw_type or "").upper().replace(" ", "")
    for base, gid, tmin, tmax in _MATERIALS:
        if base.replace("-", "") in up.replace("-", ""):
            return {"base": base.split("-")[0], "id": gid, "min": tmin, "max": tmax,
                    "sub": (raw_type or base).strip()}
    return {"base": "PLA", "id": "GFL99", "min": "190", "max": "230", "sub": (raw_type or "PLA").strip() or "PLA"}


def normalize_material(value: str) -> str:
    """Normalizes the material name to compare slot vs. slicer filament."""
    v = (value or "").upper()
    for prefix in ("ANYCUBIC", "GENERIC", "BAMBU"):
        if v.startswith(prefix):
            v = v[len(prefix):].strip()
    return re.sub(r"[^A-Z0-9]", "", v)


def ace_units(t: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Units visible to OrcaSlicer, in order: internal rack (if any) and ACEs.
    The OrcaSlicer tray (unit*4+slot) matches the Anycubic global slot number."""
    boxes = [b for b in t.get("material_boxes", []) if b.get("source") in ("rack", "ace")]
    boxes.sort(key=lambda b: _as_int(b.get("id"), -1))
    return boxes


def _empty_tray(i: int) -> Dict[str, Any]:
    return {"id": str(i), "tray_info_idx": "", "tray_type": "", "tray_sub_brands": "",
            "tray_color": "00000000", "setting_id": "", "cali_idx": -1, "remain": 0, "tag_uid": "0",
            "k": DEFAULT_PA_K, "n": 1.0,
            "nozzle_temp_min": "190", "nozzle_temp_max": "230", "tray_temp": "0",
            "tray_weight": "0", "tray_diameter": "1.75"}


def _tray_from_slot(i: int, s: Dict[str, Any]) -> Dict[str, Any]:
    mat = resolve_material(s.get("type", ""))
    r, g, b = hex_to_rgb(s.get("color"), (255, 255, 255))
    remain = _as_int(s.get("remain"), 100)
    return {"id": str(i), "tray_info_idx": _orca_id(mat["id"]), "tray_type": mat["base"],
            "tray_sub_brands": mat["sub"], "tray_color": "%02X%02X%02XFF" % (r, g, b),
            "setting_id": _orca_id(mat["id"]), "cali_idx": -1, "remain": remain if remain > 0 else 100,
            "k": DEFAULT_PA_K, "n": 1.0,
            "tag_uid": s.get("sku") or "0", "nozzle_temp_min": mat["min"], "nozzle_temp_max": mat["max"],
            "tray_temp": "45", "tray_weight": "1000", "tray_diameter": "1.75"}


JOB_DONE_STATES = ("finish", "finished", "complete", "completed", "done")
JOB_ENDED_STATES = ("stoped", "stopped", "stop", "canceled", "cancelled", "failed", "fail", "abnormal", "free", "idle")
JOB_STALE_SECONDS = 20


def _normalize_drying(raw: Any) -> Optional[Dict[str, Any]]:
    """ACE drying status -> {active, target_temp, duration, remain_time, humidity} (minutes).
    Anycubic Slicer Next sends the duration in minutes; some ACE 2 Pro reports give it in
    seconds (e.g. 14400 for 4 h), so large values are converted."""
    if not isinstance(raw, dict):
        return None
    duration = _as_int(raw.get("duration"), 0)
    remain = _as_int(raw.get("remain_time"), 0)
    if duration > 24 * 60:
        duration //= 60
    if remain > max(duration, 24 * 60):
        remain //= 60
    out = {"active": _as_int(raw.get("status"), 0) == 1, "status": _as_int(raw.get("status"), 0),
           "target_temp": _as_int(raw.get("target_temp"), 0), "duration": duration, "remain_time": remain}
    if raw.get("humidity") is not None:
        out["humidity"] = _as_int(raw.get("humidity"), 0)
    return out


def map_gcode_state(state: str, progress: int) -> str:
    s = (state or "").lower()
    if s in JOB_DONE_STATES:
        return "FINISH"
    if s in ("printing", "print", "running", "busy"):
        return "RUNNING"
    if any(k in s for k in ("level", "heat", "preheat", "feed", "load", "homing", "prepar")):
        return "PREPARE"
    if "pause" in s:
        return "PAUSE"
    if s in ("finish", "finished", "complete", "completed", "done"):
        return "FINISH"
    if s in ("failed", "fail", "error", "abnormal"):
        return "FAILED"
    return "IDLE"


ANYCUBIC_TO_ORCA_SPEED = {1: 1, 2: 2, 3: 3}   # silent/standard/sport


_LAST_STATE_LOGGED: List[str] = [""]


def job_state(t: Dict[str, Any]) -> str:
    """State of the print JOB. The `status` report ("busy"/"free") says whether the printer
    is busy with anything (heating, feeding filament, moving an axis) and arrived in the same
    field as the project state, so OrcaSlicer saw "printing" and "idle" alternating -- and
    blocked slot editing with "not possible while printing". The project state
    (info report, polled every few seconds) wins; status only counts without it."""
    proj = str(t.get("project_state") or "").strip()
    if proj:
        return proj
    st = str(t.get("status_state") or t.get("state") or "").strip()
    return "" if st.lower() == "busy" else st


def build_push_status(t: Dict[str, Any], ip: str) -> Dict[str, Any]:
    gstate = map_gcode_state(job_state(t), _as_int(t.get("progress")))
    key = "%s -> %s" % (job_state(t), gstate)
    if key != _LAST_STATE_LOGGED[0]:
        _LAST_STATE_LOGGED[0] = key
        logger.info("printer state: %s (status=%r project=%r)", key, t.get("status_state"), t.get("project_state"))
    fan_pct = _as_int(t.get("fan"))
    aux_pct = _as_int(t.get("aux_fan"))
    box_pct = _as_int(t.get("box_fan"))
    fan_gear = ((box_pct * 255 // 100) << 16) | ((aux_pct * 255 // 100) << 8) | (fan_pct * 255 // 100)

    units = ace_units(t)
    ams: Dict[str, Any] = {"version": 1, "ams_exist_bits": "0", "tray_exist_bits": "0", "tray_is_bbl_bits": "0",
                           "tray_read_done_bits": "0", "tray_reading_bits": "0", "tray_now": "255",
                           "tray_tar": "255", "ams": []}
    if units:
        exist_mask = tray_mask = 0
        tray_now = 255
        for u_idx, box in enumerate(units):
            exist_mask |= 1 << u_idx
            by_idx = {_as_int(s.get("box_slot"), k): s for k, s in enumerate(box.get("slots", []))}
            trays = []
            for s_idx in range(4):
                s = by_idx.get(s_idx)
                if s and s.get("available"):
                    tray_mask |= 1 << (u_idx * 4 + s_idx)
                    trays.append(_tray_from_slot(s_idx, s))
                    if s.get("loaded") and tray_now == 255:
                        tray_now = u_idx * 4 + s_idx
                else:
                    trays.append(_empty_tray(s_idx))
            ams["ams"].append({"id": str(u_idx), "humidity": str(box.get("humidity", 0)),
                               "temp": str(box.get("temp", 0)), "tray": trays})
        ams["ams_exist_bits"] = "%x" % exist_mask
        ams["tray_exist_bits"] = "%x" % tray_mask
        ams["tray_read_done_bits"] = "%x" % tray_mask
        ams["tray_now"] = ams["tray_tar"] = str(tray_now)

    lights = [{"node": "chamber_light", "mode": "on" if t.get("light") else "off"}]
    print_msg: Dict[str, Any] = {
        "command": "push_status", "msg": 0, "sequence_id": "0",
        "gcode_state": gstate,
        "mc_percent": _as_int(t.get("progress")),
        "mc_remaining_time": _as_int(t.get("remain_time")),
        "nozzle_temper": _as_float(t.get("nozzle_temp")),
        "nozzle_target_temper": _as_float(t.get("target_nozzle_temp")),
        "bed_temper": _as_float(t.get("bed_temp")),
        "bed_target_temper": _as_float(t.get("target_bed_temp")),
        "layer_num": _as_int(t.get("curr_layer")),
        "total_layer_num": _as_int(t.get("total_layers")),
        "subtask_name": str(t.get("job_name") or ""),
        "gcode_file": str(t.get("job_name") or ""),
        "spd_lvl": ANYCUBIC_TO_ORCA_SPEED.get(_as_int(t.get("speed_mode"), 1), 2),
        "fan_gear": fan_gear,
        "cooling_fan_speed": str(fan_pct * 15 // 100),
        "big_fan1_speed": str(aux_pct * 15 // 100),
        "big_fan2_speed": str(box_pct * 15 // 100),
        "support_aux_fan": bool(t.get("has_aux_fan")), "support_chamber_fan": bool(t.get("has_box_fan")),
        "lights_report": lights,
        "sdcard": True, "support_send_to_sd": True,
        # without this the filament window only lists system presets (your presets are left out)
        "support_user_preset": True,
        # bits 0..2 = X/Y/Z homed; bits 8..9 = SD card present (OrcaSlicer reads the storage state from
        # THIS field; with the bits cleared it blocks sending with "Storage needs to be inserted").
        # Unknown homing state (None) counts as "homed" so it does not ask for homing for no reason.
        "home_flag": (256 if t.get("homed") is False else 263),
        "nozzle_diameter": "0.4", "nozzle_type": "hardened_steel",
        "ams": ams,
        "ipcam": {"ipcam_dev": "1", "ipcam_record": "enable", "timelapse": "enable",
                  "resolution": "1080p", "resolution_supported": ["1080p", "720p"],
                  "rtsp_url": t.get("camera_url") or ("http://%s:18088/flv" % ip),
                  "liveview": {"local": "http", "remote": "none"}},
    }
    # OrcaSlicer only knows how to show Bambu HMS codes: a Kobra code becomes "Unknown error" and the red
    # bar stays until the user clears it. So the error is only passed on while it is recent
    # (reply to a command) or while the printer is really in a fault state.
    err_fresh = (time.time() - float(t.get("last_error_time") or 0)) < 20.0
    err_state = job_state(t).lower() in ("failed", "abnormal", "error")
    if t.get("last_error") and (err_fresh or err_state):
        print_msg["print_error"] = _as_int(t.get("last_error_code"))
        print_msg["mc_print_error_code"] = str(_as_int(t.get("last_error_code")))
    ext = t.get("external_spool")
    if ext or not units or MATERIAL_SOURCE[0] == "external":
        mat = resolve_material((ext or {}).get("type", "PLA"))
        r, g, b = hex_to_rgb((ext or {}).get("color", "#FFFFFF"), (255, 255, 255))
        print_msg["vt_tray"] = {
            "id": "254", "tag_uid": "0", "tray_id_name": "", "tray_info_idx": _orca_id(mat["id"]),
            "tray_type": mat["base"], "tray_sub_brands": mat["sub"],
            "tray_color": "%02X%02X%02XFF" % (r, g, b), "setting_id": _orca_id(mat["id"]), "cali_idx": -1,
            "k": DEFAULT_PA_K, "n": 1.0,
            "nozzle_temp_min": mat["min"], "nozzle_temp_max": mat["max"], "tray_temp": "0",
            "tray_weight": "0", "tray_diameter": "1.75"}
    return {"print": print_msg}


def build_version_msg(t: Dict[str, Any], dev_id: str, seq: str = "0") -> Dict[str, Any]:
    return {"info": {"command": "get_version", "sequence_id": str(seq), "result": "success", "module": [{
        "name": "ota", "product_name": t.get("model") or "Anycubic Kobra",
        "sw_ver": str(t.get("firmware") or "1.0.0"), "hw_ver": "1.0.0", "sn": dev_id}]}}


def build_announce(ip: str, info: Dict[str, Any], dev_type: str = "") -> Dict[str, str]:
    """'SSDP' message understood by DeviceManager. dev_id = IP (host convention).

    dev_type becomes the machine printer_type and the send dialog compares it with the model of the
    selected printer preset (Preset::get_printer_type). The name the printer
    reports in /info ("Kobra X", a numeric modelId...) does not match "Anycubic Kobra X", and
    OrcaSlicer blocked sending with "the selected printer is incompatible". That is why we use the
    preset printer_model; empty counts as "any model" for OrcaSlicer."""
    return {
        "dev_name": str(info.get("deviceName") or info.get("name") or "Anycubic Kobra"),
        "dev_id": ip, "dev_ip": ip,
        "dev_type": dev_type or "",
        "dev_signal": "100", "connect_type": "lan", "bind_state": "free",
        "sec_link": "secure", "ssdp_version": "v1",
    }


def build_ams_mapping(params_mapping: str, params_mapping_info: str, state: Dict[str, Any]) -> Tuple[bool, List[Dict[str, Any]]]:
    """Converts the OrcaSlicer mapping to the Anycubic `ams_box_mapping`.
    OrcaSlicer: `ams_mapping` = [tray_id per filament] (-1 = unused/external) and
    `ams_mapping_info` = [{ams, sourceColor, targetColor, filamentType, ...}]."""
    try:
        v0 = json.loads(params_mapping) if params_mapping else []
    except ValueError:
        v0 = []
    try:
        info = json.loads(params_mapping_info) if params_mapping_info else []
    except ValueError:
        info = []
    slots_by_global = {s["slot"]: s for s in state.get("filaments", []) if s.get("slot", -1) >= 0}
    out: List[Dict[str, Any]] = []
    for i, tray in enumerate(v0):
        tray = _as_int(tray, -1)
        if tray < 0 or tray >= 254:
            continue
        item = info[i] if i < len(info) and isinstance(info[i], dict) else {}
        slot = slots_by_global.get(tray, {})
        target = item.get("targetColor") or slot.get("color") or "#23a3c7"
        source = item.get("sourceColor") or target
        mtype = item.get("filamentType") or slot.get("type") or "PLA"
        out.append({"ams_index": tray, "paint_index": i, "material_type": mtype,
                    "ams_color": hex_to_rgb(target, (35, 163, 199)),
                    "paint_color": hex_to_rgb(source, (35, 163, 199))})
    return bool(out), out


# --------------------------------------------------------------------------
# Running a single G-code snippet (used by the extrude button): uploads a minimal .gcode and runs it
# --------------------------------------------------------------------------
def run_gcode_snippet(client: AnycubicClient, gcode_text: str) -> None:
    ts = int(time.time())
    fname = "_orca_kobra_cmd_%d_%s.gcode" % (ts, _rand_alnum(4).lower())
    content = (
        "; HEADER_BLOCK_START\n; generated by AnycubicSlicerNext 2.0.0.2\n; total layer number: 1\n"
        "; filament_density: 1.24\n; filament_diameter: 1.75\n; max_z_height: 10.0\n; HEADER_BLOCK_END\n\n"
        + gcode_text.strip() + "\nM400\n\n; statistics = begin\n; used_filament = 0.00\n"
        "; print_time = 0m 10s\n; model_size = 10.00,10.00,10.00\n; total_layers = 1\n; statistics = end\n")
    fd, tmp = _mkstemp(".gcode", "kobra_cmd_")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            f.write(content)
        md5, size = client.upload_file(tmp, fname)
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass
    time.sleep(0.5)
    # Uses the slot already loaded in the nozzle (it used to be fixed to slot 3, the yellow one on the
    # plugin author's printer, which changed the filament on any other printer).
    snap = client.state.snapshot()
    loaded = next((s for s in snap.get("filaments", []) if s.get("loaded") and _as_int(s.get("slot"), -1) >= 0), None)
    if loaded:
        rgb = hex_to_rgb(loaded.get("color"))
        mapping = [{"ams_index": _as_int(loaded["slot"]), "paint_index": 0,
                    "material_type": str(loaded.get("type") or "PLA"), "ams_color": rgb, "paint_color": rgb}]
        client.start_print(fname, md5, size, True, mapping, {"auto_leveling": False})
    else:
        client.start_print(fname, md5, size, False, [], {"auto_leveling": False})


# --------------------------------------------------------------------------
# Plugin configuration
# --------------------------------------------------------------------------
DEFAULT_MODEL_ALIASES: Dict[str, str] = {
    "Anycubic Kobra 4": "Anycubic Kobra X",
}

DEFAULT_CONFIG: Dict[str, Any] = {
    # print task options (the OrcaSlicer dialog can also turn them on)
    "auto_leveling": True,
    "vibration_compensation": False,
    "flow_calibration": False,
    "timelapse": False,
    # adjustments to the uploaded file
    "rename_plate_to_first": True,       # Metadata/plate_N.gcode -> plate_1.gcode
    "pre_engage_filament": False,         # engages the starting ACE slot before sending
    "pre_engage_timeout": 60,            # seconds waiting for the printer to confirm the engage
    "pre_engage_no_reaction_timeout": 8,  # seconds without ANY printer reaction -> give up the pre-engage
    "pre_engage_strict": False,          # True: abort sending if the engage is not confirmed; False: continue and note it in the log
    "skip_first_toolchange": False,      # replaces the 1st tool change with an initial purge
    "skip_first_toolchange_script": DEFAULT_PURGE_SCRIPT,
    # network
    "poll_interval": 2.5,
    "connect_timeout": 20,
    "discovery_hosts": ["192.168.0.37"],               # extra IPs for discovery, e.g. ["192.168.0.50"]
    "ssdp": True,
    "invert_y": True,                    # inverts the Y jog direction (Kobra 4: moving bed)
    "scan_subnet": False,                # do NOT turn on: each scanned IP creates a permission prompt in OrcaSlicer
    # model announced to OrcaSlicer by the preset printer_model (e.g. {"Anycubic Kobra 4": "Anycubic Kobra X"})
    "orca_model_alias": {},
    # Kobra panel local server for the Device (Web) tab (127.0.0.1 only)
    "workbench_port": 18989,
}


def _host_only(addr: str) -> str:
    s = (addr or "").strip()
    if "://" in s:
        s = s.split("://", 1)[1]
    s = s.split("/", 1)[0]
    if s.count(":") == 1:
        s = s.split(":", 1)[0]
    return s


def dev_id_from_address(host: str, port: str = "") -> str:
    """Same rule as OrcaSlicer MachineObject::dev_id_from_address ("host" or "host:port")."""
    r = (host or "").strip()
    for pre in ("http://", "https://"):
        if r.startswith(pre):
            r = r[len(pre):]
            break
    r = r.split("/", 1)[0]
    if port:
        r = r.split(":", 1)[0] + ":" + str(port)
    return r


# --------------------------------------------------------------------------
# OrcaSlicer permissions
# --------------------------------------------------------------------------
# OrcaSlicer audits network, threads, processes and files of plugins. Outside the main thread, an
# operation without permission is DENIED right away and the prompt only shows up later -- that is why the first
# connection failed ("Connect ... failed"), sending failed the check and the 3MF reader was
# blocked. The fix is to declare everything at once with orca.request_permissions() while
# loading (a single prompt), and to handle new IPs on the main thread (connect_printer).
_PERM_TOUCHED: set = set()


def _orca_model_tmp_dirs() -> List[str]:
    """Folders where OrcaSlicer writes the .3mf that goes to the printer (Model::get_backup_path)."""
    out: List[str] = []
    if os.name == "nt":
        base = os.environ.get("TMP") or os.environ.get("TEMP") or os.environ.get("USERPROFILE") or ""
        if base:
            out.append(os.path.join(base, "orcaslicer_model"))
    else:
        bases = [os.environ.get("TMPDIR") or "", "/tmp"]
        uid = str(os.getuid()) if hasattr(os, "getuid") else ""
        for base in dict.fromkeys(b.rstrip("/") for b in bases if b):
            out.append(base + "/orcaslicer_model")
            if uid:
                out.append(base + "/orcaslicer_" + uid + "/orcaslicer_model")
    return out


def _orca_program_dir() -> str:
    """Folder of orca-slicer.exe (inside OrcaSlicer, sys.executable is the Orca executable)."""
    import sys as _sys
    exe = _sys.executable or ""
    if IN_ORCA and exe and os.path.basename(exe).lower().startswith("orca"):
        return os.path.dirname(exe)
    return ""


def setup_script_path() -> str:
    return os.path.join(_resource_dir(), "setup", "install-dependencies.ps1")


def setup_command() -> List[str]:
    """The one command the Setup tab runs. It must stay identical to the one declared in
    _declare_permissions(), because OrcaSlicer approves the exact command line."""
    root = os.environ.get("SystemRoot") or r"C:\Windows"
    ps = os.path.join(root, "System32", "WindowsPowerShell", "v1.0", "powershell.exe")
    return [ps, "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", setup_script_path(), "-PluginDir", _plugin_dir(),
            "-DataDir", _orca_data_dir()]


def setup_components() -> List[Dict[str, Any]]:
    """What the Setup tab shows: each dependency and whether it is installed."""
    prog = _orca_program_dir()

    def prog_has(*rel: str) -> bool:
        return bool(prog) and all(os.path.isfile(os.path.join(prog, *r.split("/"))) for r in rel)
    return [
        {"id": "photos", "name": "Printer photos",
         "description": "Kobra 4 / Kobra X photo in OrcaSlicer's \"Send print job\" window (instead of a Bambu X1).",
         "installed": prog_has("resources/images/printer_preview_Anycubic Kobra 4.png",
                               "resources/images/printer_preview_Anycubic Kobra X.png")},
        {"id": "filament_lists", "name": "Filament lists",
         "description": "Lets the send window list the Kobra filaments and map them to the ACE.",
         "installed": prog_has("resources/printers/Anycubic Kobra 4.json", "resources/printers/Anycubic Kobra X.json")},
        {"id": "profiles", "name": "Kobra 4 / Kobra X system profiles",
         "description": "Kobra 4 and Kobra X in Add/Remove printers > Anycubic, with the qualities and filaments of "
                        "Anycubic Slicer Next for every nozzle.",
         "installed": _system_has_model("Anycubic Kobra 4")
                      and _version_tuple(_system_bundle_version()) >= _version_tuple(PROFILE_PACKAGE_VERSION)},
    ]


def _declare_permissions() -> None:
    req = getattr(orca, "request_permissions", None)
    if not IN_ORCA or not callable(req):
        return
    hosts = list(dict.fromkeys([h for h in BUILTIN_HOSTS + list(DEFAULT_CONFIG.get("discovery_hosts") or []) if h]))
    network = ["http://%s" % h for h in hosts] + ["http://127.0.0.1", "http://239.255.255.250"]
    fs_read = [d.rstrip("\\/") + "/*" for d in _orca_model_tmp_dirs()]
    process: List[str] = []
    if os.name == "nt" and os.path.isfile(setup_script_path()):
        process.append(command_audit_target(setup_command()))   # Setup tab: dependency installer
    try:
        req(fs_read=fs_read, process=process, threading=True, network=network)
    except TypeError:
        # versions that do not have the "network" parameter yet: use the HTTP list
        req(fs_read=fs_read, process=process, threading=True, network_http=network)


def _ensure_network_permission(host: str) -> None:
    """Touches the host with a cheap audited operation (getaddrinfo of an IP does not use DNS). On the
    main thread, OrcaSlicer shows the prompt right away and stores the permission for the whole host;
    so the connection threads are not denied later."""
    host = _host_only(host)
    if not IN_ORCA or not host or host in _PERM_TOUCHED:
        return
    _PERM_TOUCHED.add(host)
    try:
        socket.getaddrinfo(host, HTTP_PORT, socket.AF_INET, socket.SOCK_STREAM)
    except Exception as exc:  # noqa: BLE001
        logger.warning("network permission for %s not granted (%s)", host, exc)


_LOG_READY = False


def _setup_file_log() -> None:
    """Writes the plugin log to _tmp/anycubic_kobra_lan.log (OrcaSlicer does not capture Python logging)."""
    global _LOG_READY
    if _LOG_READY:
        return
    _LOG_READY = True
    try:
        from logging.handlers import RotatingFileHandler
        for old in list(logger.handlers):   # OrcaSlicer may reload the module: avoids duplicated lines
            logger.removeHandler(old)
            try:
                old.close()
            except Exception:  # noqa: BLE001
                pass
        h = RotatingFileHandler(os.path.join(_tmp_dir(), "anycubic_kobra_lan.log"), maxBytes=1_000_000,
                                backupCount=1, encoding="utf-8")
        h.setFormatter(logging.Formatter("%(asctime)s %(levelname)s [%(threadName)s] %(message)s"))
        logger.addHandler(h)
        logger.setLevel(logging.INFO)
    except Exception:  # noqa: BLE001
        pass


# --------------------------------------------------------------------------
# Plugin folder helpers
# --------------------------------------------------------------------------
def _code_dir() -> str:
    """Folder of this file: the plugin folder for a .py install, the extracted package for a .whl."""
    return os.path.dirname(os.path.abspath(globals().get("__file__") or ""))


def _resource_dir() -> str:
    """Read-only files shipped with the plugin (kobra_workbench/, setup/)."""
    return _code_dir()


def _install_dir() -> str:
    """Folder OrcaSlicer installed the plugin into (holds the .py / .whl). OrcaSlicer deletes and
    rewrites it on every update, so nothing of ours may live there."""
    here = _code_dir()
    d = here
    for _ in range(6):
        if os.path.basename(d) == "__whl_extracted__":
            return os.path.dirname(d)
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return here


def _orca_data_dir() -> str:
    """OrcaSlicer data folder: the parent of orca_plugins/ (works for local and cloud installs)."""
    d = _code_dir()
    for _ in range(10):
        parent = os.path.dirname(d)
        if os.path.basename(d).lower() == "orca_plugins":
            return parent
        if parent == d:
            break
        d = parent
    return os.path.dirname(os.path.dirname(_install_dir()))


_DATA_DIR: List[str] = []


def _plugin_dir() -> str:
    """Writable folder for the printer list, caches and log: OrcaSlicer's per-plugin storage folder
    (orca.host.plugin.storage(): <data>/orca_plugins/plugin_data/[_subscribed/<user>/]<plugin key>).
    It is outside the install folder, so updates can replace the install folder freely (an open log
    file in there made an update fail on Windows) and the saved printers survive updates."""
    if _DATA_DIR:
        return _DATA_DIR[0]
    target = ""
    install = _install_dir()
    plugins_root = os.path.join(_orca_data_dir(), "orca_plugins")
    try:
        rel = os.path.relpath(install, plugins_root)
        if not rel.startswith("..") and rel not in (".", ""):
            target = os.path.join(plugins_root, "plugin_data", rel)   # same path OrcaSlicer computes
    except ValueError:
        target = ""
    if not target:
        try:
            target = str(orca.host.plugin.storage())
        except Exception:  # noqa: BLE001
            target = ""
    try:
        if not target:
            raise OSError("no storage folder")
        os.makedirs(target, exist_ok=True)
        _migrate_old_data(target)
    except Exception:  # noqa: BLE001
        target = install
    _DATA_DIR.append(target)
    return target


def _migrate_old_data(target: str) -> None:
    """Copies the printer list and caches kept by older versions inside the install folder."""
    import shutil
    old = _install_dir()
    for rel in ("kobra_printers.json", os.path.join("_tmp", "file_filaments.json"), os.path.join("_tmp", "thumbnails.json")):
        src, dst = os.path.join(old, rel), os.path.join(target, rel)
        if os.path.isfile(src) and not os.path.exists(dst):
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy2(src, dst)


def _system_has_model(model: str, vendor: str = "Anycubic") -> bool:
    """True if the OrcaSlicer data folder (<data>/orca_plugins/<plugin>/ -> <data>) has a system
    profile for `model` (e.g. the Kobra 4 installed by the profile package)."""
    data = _orca_data_dir()
    return os.path.isfile(os.path.join(data, "system", vendor, "machine", model + ".json"))


def _system_bundle_version(vendor: str = "Anycubic") -> str:
    data = _orca_data_dir()
    try:
        with open(os.path.join(data, "system", vendor + ".json"), encoding="utf-8") as f:
            return str(json.load(f).get("version") or "")
    except Exception:
        return ""


def _version_tuple(v: str) -> tuple:
    out = []
    for part in str(v or "").split("."):
        try:
            out.append(int(part))
        except ValueError:
            out.append(0)
    return tuple(out)


def command_line(cmd: List[str]) -> Any:
    """On Windows passes the already built line (it is the text the OrcaSlicer auditor sees and the
    one approved in the permission prompt); on POSIX, the list."""
    if os.name == "nt":
        import subprocess
        return subprocess.list2cmdline(cmd)
    return cmd


def command_audit_target(cmd: List[str]) -> str:
    """Text exposed by the subprocess.Popen audit event for this command."""
    arg = command_line(cmd)
    return arg if isinstance(arg, str) else str(list(arg))


class _CmdWorker:
    """Command queue run in a plugin thread (avoids network I/O on the UI thread)."""

    def __init__(self) -> None:
        self.q: "queue.Queue[Optional[Callable[[], None]]]" = queue.Queue()
        self.thread = _spawn(self._loop, "anycubic-cmd")

    def _loop(self) -> None:
        while True:
            fn = self.q.get()
            if fn is None:
                return
            try:
                fn()
            except BaseException:  # noqa: BLE001
                logger.exception("command failed")

    def submit(self, fn: Callable[[], None]) -> None:
        if self.thread is not None and self.thread.is_alive():
            self.q.put(fn)
        else:
            try:
                fn()
            except BaseException:  # noqa: BLE001
                logger.exception("command failed")

    def stop(self) -> None:
        self.q.put(None)


# --------------------------------------------------------------------------
# The printer agent
# --------------------------------------------------------------------------
class AnycubicKobraAgent(PrinterAgentBase):
    def __init__(self) -> None:
        super().__init__()
        self._client: Optional[AnycubicClient] = None
        self._dev_id = ""
        self._access_code = ""
        self._selected = ""
        self._ever_up = False
        self._cmd: Optional[_CmdWorker] = None
        self._cfg_cache: Dict[str, Any] = dict(DEFAULT_CONFIG)
        self._lock = threading.RLock()
        # host callbacks
        self._on_ssdp: Optional[Callable[[str], None]] = None
        self._on_local_connect: Optional[Callable[[int, str, str], None]] = None
        self._on_local_message: Optional[Callable[[str, str], None]] = None
        self._on_message: Optional[Callable[[str, str], None]] = None
        self._on_printer_connected: Optional[Callable[[str], None]] = None
        self._queue_main: Optional[Callable[[Callable[[], None]], None]] = None
        self._known_hosts: List[str] = []
        self._discovery_thread: Optional[threading.Thread] = None
        self._printer_model = ""     # preset printer_model (becomes the announced dev_type)
        _ACTIVE_AGENT[0] = self      # the panel uses this agent's connection
        self._preset_dev_id = ""     # dev_id OrcaSlicer creates from the preset print_host
        _setup_file_log()
        try:
            self._cfg()
            workbench_server()       # 0.7.0: panel at http://127.0.0.1:18988/ for the Device (Web) tab
        except Exception:  # noqa: BLE001
            logger.exception("panel: failed to start the local server")

    # -- identification -----------------------------------------------------
    def get_name(self) -> str:
        return AGENT_ID

    def get_default_config(self) -> Dict[str, Any]:
        return dict(DEFAULT_CONFIG)

    def get_agent_info(self) -> Any:
        return AgentInfo(AGENT_ID, AGENT_NAME, PLUGIN_VERSION,
                         "Kobra 3 Max stock LAN: status, two ACE Pro units, upload and explicit print start")

    def get_filament_sync_mode(self) -> Any:
        return getattr(FilamentSyncMode, "Subscription", getattr(FilamentSyncMode, "subscription", 1))

    # The camera is shown by the Kobra panel (Device (Web) tab), which plays the printer video itself.
    # OrcaSlicer's native Device tab is not used, so it gets no camera.
    def get_camera_stream_mode(self) -> Any:
        return getattr(CameraStreamMode, "None_", getattr(CameraStreamMode, "none", 0))

    def get_camera_url(self) -> str:
        return ""

    # -- configuration ------------------------------------------------------
    def _cfg(self) -> Dict[str, Any]:
        cfg = dict(DEFAULT_CONFIG)
        try:
            raw = self.get_config()
            if raw:
                data = json.loads(raw) if isinstance(raw, str) else dict(raw)
                if isinstance(data, dict):
                    cfg.update({k: v for k, v in data.items() if v is not None})
        except Exception:  # noqa: BLE001
            pass
        self._cfg_cache = cfg
        return cfg

    # -- callbacks registered by the host -----------------------------------
    def set_on_ssdp_msg_fn(self, fn: Any) -> int:
        self._on_ssdp = fn
        return 0

    def set_on_local_connect_fn(self, fn: Any) -> int:
        self._on_local_connect = fn
        return 0

    def set_on_local_message_fn(self, fn: Any) -> int:
        self._on_local_message = fn
        return 0

    def set_on_message_fn(self, fn: Any) -> int:
        self._on_message = fn
        return 0

    def set_on_user_message_fn(self, fn: Any) -> int:
        return 0

    def set_on_printer_connected_fn(self, fn: Any) -> int:
        self._on_printer_connected = fn
        return 0

    def set_on_subscribe_failure_fn(self, fn: Any) -> int:
        return 0

    def set_queue_on_main_fn(self, fn: Any) -> int:
        self._queue_main = fn
        return 0

    def set_server_callback(self, fn: Any) -> int:
        return 0

    def _emit_local_connect(self, state: int, msg: str) -> None:
        fn = self._on_local_connect
        if fn:
            try:
                fn(state, self._dev_id, msg)
            except Exception:  # noqa: BLE001
                logger.exception("on_local_connect failed")

    def _emit_local_message(self, obj: Dict[str, Any]) -> None:
        fn = self._on_local_message
        if fn and self._dev_id:
            try:
                fn(self._dev_id, json.dumps(obj))
            except Exception:  # noqa: BLE001
                logger.exception("on_local_message failed")

    def _emit_ssdp(self, announce: Dict[str, str]) -> None:
        fn = self._on_ssdp
        if not fn:
            return
        payload = json.dumps(announce)
        # on_machine_alive touches UI maps without a lock: it must run on the main thread.
        q = self._queue_main
        try:
            if q:
                q(lambda: fn(payload))
            else:
                fn(payload)
        except Exception:  # noqa: BLE001
            logger.exception("on_ssdp failed")

    # -- selection/connection -----------------------------------------------
    def get_user_selected_machine(self) -> str:
        return self._selected or self._dev_id

    def set_user_selected_machine(self, dev_id: str) -> int:
        self._selected = dev_id or ""
        return 0

    def connect_printer(self, params: Any = None, *args: Any, **kwargs: Any) -> int:
        # Current signature: PrinterConnectionParams. Also accepts the old one (dev_id, ip, user, pwd, ssl).
        if isinstance(params, str):
            dev_id = params
            host = args[0] if args and isinstance(args[0], str) else params
            password = args[2] if len(args) > 2 and isinstance(args[2], str) else ""
        else:
            dev_id = str(getattr(params, "dev_id", "") or "")
            host = str(getattr(params, "host", "") or "")
            password = str(getattr(params, "password", "") or "")
        ip = _host_only(host or dev_id)
        if not ip:
            self._emit_local_connect(1, "printer address is empty")
            return ERR_GENERIC
        cfg = self._cfg()
        # Both run here because OrcaSlicer calls connect_printer on the main thread: it is the only
        # place where a permission prompt shows up right away instead of being denied.
        self._refresh_preset_identity()
        _ensure_network_permission(ip)
        with self._lock:
            self._teardown_client()
            self._dev_id = dev_id or ip
            self._access_code = password
            self._ever_up = False
            if ip not in self._known_hosts:
                self._known_hosts.append(ip)
            self._cmd = _CmdWorker()
            client = AnycubicClient(ip, on_state=self._push_state, on_link=self._on_link,
                                    poll_interval=_as_float(cfg.get("poll_interval"), 2.5))
            self._client = client
            if not client.start():
                self._client = None
                self._emit_local_connect(
                    1, "OrcaSlicer refused to let the plugin create threads. Accept the permission in the plugin "
                       "prompt (or reinstall it under Plugins) and try again.")
                return ERR_GENERIC
        return 0

    def _refresh_preset_identity(self) -> None:
        """Reads the model and the dev_id OrcaSlicer itself uses from the selected printer preset
        (GUI_App::select_machine). Only reads memory; preferably call it on the main thread."""
        try:
            preset = orca.host.preset_bundle().current_printer_preset()

            def val(key: str) -> str:
                v = preset.config_value(key)
                return "" if v is None else str(v)

            model = val("printer_model")
            # OrcaSlicer only builds the ACE window filament list from a SYSTEM preset
            # of the same model (get_printer_names_by_printer_type_and_nozzle, system_only=true) and there
            # is no Kobra 4 system profile. Announcing it as a Kobra X (same family, same nozzle,
            # existing system profile) makes the list show up. Configurable in "orca_model_alias".
            aliases = dict(DEFAULT_MODEL_ALIASES)
            # With the Kobra 4 system profile installed (Setup tab / "Kobra 4 for OrcaSlicer" package), OrcaSlicer
            # already has its filament list: announce the real model.
            for m in [m for m in aliases if _system_has_model(m)]:
                aliases.pop(m)
            extra = self._cfg_cache.get("orca_model_alias")
            if isinstance(extra, dict):
                aliases.update({str(k): str(v) for k, v in extra.items()})
            self._printer_model = aliases.get(model, model)
            host = val("print_host")
            self._preset_dev_id = dev_id_from_address(host, val("printhost_port")) if host else ""
        except Exception as exc:  # noqa: BLE001
            logger.debug("could not read the printer preset: %s", exc)

    def _announce_for(self, ip: str, info: Dict[str, Any]) -> Dict[str, str]:
        a = build_announce(ip, info, self._printer_model)
        name = saved_printer_name(ip)
        if name:
            a["dev_name"] = name
        # Uses the same dev_id as the machine OrcaSlicer created from the preset print_host (or from the
        # current connection), so a second "ghost" printer does not show up in the list.
        for cand in (self._dev_id if (self._client and self._client.ip == ip) else "", self._preset_dev_id):
            if cand and _host_only(cand) == ip:
                a["dev_id"] = a["dev_ip"] = cand
                break
        return a

    def _teardown_client(self) -> None:
        c, self._client = self._client, None
        if c:
            c.on_link = None
            c.on_state = None
            c.stop()
        w, self._cmd = self._cmd, None
        if w:
            w.stop()

    def disconnect_printer(self) -> int:
        with self._lock:
            self._teardown_client()
        return 0

    def _on_link(self, up: bool, why: str) -> None:
        c = self._client
        if up:
            self._ever_up = True
            if c:
                a = self._announce_for(c.ip, c.info)
                # the host stores the machine created by select_machine with dev_id == dev_ip == "host[:port]"
                a["dev_id"] = a["dev_ip"] = self._dev_id or c.ip
                self._emit_ssdp(a)
            self._emit_local_connect(0, "")
            self._push_version()
            self._push_state()
        else:
            self._emit_local_connect(2 if self._ever_up else 1, why or "connection failed")

    def _push_state(self) -> None:
        c = self._client
        if c is None:
            return
        self._emit_local_message(build_push_status(c.state.snapshot(), c.ip))

    def _push_version(self, seq: str = "0") -> None:
        c = self._client
        if c is None:
            return
        self._emit_local_message(build_version_msg(c.state.snapshot(), self._dev_id, seq))

    def fetch_filament_info(self, dev_id: str = "", sync_mode: Any = None) -> bool:
        c = self._client
        if c is None or not c.link_up:
            return False
        self._push_state()
        return True

    # -- no account/cloud ---------------------------------------------------
    def check_cert(self) -> int:
        return 0

    def install_device_cert(self, dev_id: str = "", lan_only: bool = True) -> None:
        return None

    def ping_bind(self, ping_code: str = "") -> int:
        return 0

    def bind(self, *args: Any, **kwargs: Any) -> int:
        return 0

    def unbind(self, dev_id: str = "") -> int:
        return 0

    def request_bind_ticket(self, *args: Any, **kwargs: Any) -> Tuple[int, str]:
        return (0, "")

    def to_orca_filament_id(self, printer_filament_id: str) -> str:
        return FILAMENT_PRINTER_TO_ORCA.get(printer_filament_id, printer_filament_id)

    def from_orca_filament_id(self, orca_filament_id: str) -> str:
        return FILAMENT_ORCA_TO_PRINTER.get(orca_filament_id, orca_filament_id)

    def start_sdcard_print(self, *args: Any, **kwargs: Any) -> int:
        return ERR_NOT_SUPPORTED

    def get_hms_snapshot(self, *args: Any, **kwargs: Any) -> int:
        return ERR_NOT_SUPPORTED

    # -- discovery -----------------------------------------------------------
    def start_discovery(self, start: bool = True, sending: bool = False) -> bool:
        if not start:
            return True
        cfg = self._cfg()
        self._refresh_preset_identity()
        hosts = [h for h in list(cfg.get("discovery_hosts") or []) + list(self._known_hosts) + saved_printer_hosts() if h]
        if self._preset_dev_id:
            hosts.append(_host_only(self._preset_dev_id))
        for h in dict.fromkeys(_host_only(x) for x in hosts):
            _ensure_network_permission(h)
        t = self._discovery_thread
        if t is not None and t.is_alive():
            return True   # a discovery is already running; do not stack another one
        use_ssdp = bool(cfg.get("ssdp", True))
        t = _spawn(self._discover, "anycubic-discovery", hosts, use_ssdp)
        self._discovery_thread = t
        return t is not None

    def reannounce(self, ip: str) -> None:
        """After renaming in the panel: sends the new name to the OrcaSlicer list."""
        c = self._client
        info = c.info if (c is not None and c.ip == ip and c.info) else self._probe(ip)
        if info:
            a = self._announce_for(ip, info)
            if c is not None and c.ip == ip and self._dev_id:
                a["dev_id"] = a["dev_ip"] = self._dev_id
            self._emit_ssdp(a)

    def _probe(self, ip: str) -> Optional[Dict[str, Any]]:
        try:
            return AnycubicClient(ip).fetch_info(timeout=2.0)
        except Exception:  # noqa: BLE001
            return None

    def _discover(self, hosts: List[str], use_ssdp: bool) -> None:
        seen = set()

        def announce(ip: str, info: Dict[str, Any]) -> None:
            if ip in seen:
                return
            seen.add(ip)
            self._emit_ssdp(self._announce_for(ip, info))

        # Built-in hosts: the config stored by OrcaSlicer (from a previous install) may come with an
        # empty list and override the default; that is why the known IP is always added here.
        hosts = list(dict.fromkeys([h for h in list(hosts) + list(BUILTIN_HOSTS) if h]))
        # Several passes: on the first one OrcaSlicer usually denies for lack of permission and only then shows
        # the prompt; after the user clicks "Yes", a following pass works. Long waits
        # between the passes so repeated prompts do not pile up.
        for delay in (0.0, 20.0, 30.0, 40.0):
            if delay:
                time.sleep(delay)
            for ip in hosts:
                h = _host_only(ip)
                if h in seen:
                    continue
                info = self._probe(h)
                if info:
                    announce(h, info)
            if not seen and use_ssdp:
                self._ssdp_pass(seen, announce)
            if seen:
                break
        # Plan B: SSDP is often blocked (Windows firewall, Wi-Fi isolation,
        # several network cards). If nothing showed up, scan the /24 subnet looking for port 18910.
        # Polite with the other plugins (e.g. Open Bambu): at most 1 scan every 5 min and
        # never while there is already an active connection to the Kobra.
        now = time.time()
        idle = not (self._client is not None and self._client.link_up)
        if (not seen and idle and self._cfg_cache.get("scan_subnet", False)
                and now - getattr(self, "_last_scan", 0.0) > 300):
            self._last_scan = now
            try:
                self._scan_subnet(announce)
            except Exception as exc:  # noqa: BLE001
                logger.debug("subnet scan failed: %s", exc)

    def _ssdp_pass(self, seen: set, announce: Callable[[str, Dict[str, Any]], None]) -> None:
        sock = None
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            sock.settimeout(1.0)
            req = ("M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: \"ssdp:discover\"\r\n"
                   "MX: 2\r\nST: ssdp:all\r\n\r\n").encode()
            sock.sendto(req, ("239.255.255.250", 1900))
            end = time.time() + 3.0
            while time.time() < end:
                try:
                    data, addr = sock.recvfrom(4096)
                except socket.timeout:
                    continue
                ip = addr[0]
                text = data.decode("utf-8", "replace")
                if ip in seen or not ("18910" in text or "anycubic" in text.lower()):
                    continue
                info = self._probe(ip)
                if info:
                    announce(ip, info)
        except Exception as exc:  # noqa: BLE001
            logger.debug("SSDP failed: %s", exc)
        finally:
            if sock:
                sock.close()

    @staticmethod
    def _local_prefixes() -> List[str]:
        prefixes: List[str] = []
        ips: List[str] = []
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("192.0.2.1", 9))      # sends nothing; only finds the outgoing interface
            ips.append(s.getsockname()[0])
            s.close()
        except Exception:  # noqa: BLE001
            pass
        try:
            for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
                ips.append(info[4][0])
        except Exception:  # noqa: BLE001
            pass
        for ip in ips:
            parts = ip.split(".")
            if len(parts) == 4 and not ip.startswith(("127.", "169.254.", "0.")):
                p = ".".join(parts[:3])
                if p not in prefixes:
                    prefixes.append(p)
        return prefixes

    def _scan_subnet(self, announce: Callable[[str, Dict[str, Any]], None]) -> None:
        from concurrent.futures import ThreadPoolExecutor

        def open_port(ip: str) -> Optional[str]:
            try:
                with socket.create_connection((ip, HTTP_PORT), timeout=0.6):
                    return ip
            except Exception:  # noqa: BLE001
                return None

        for prefix in self._local_prefixes():
            cands = ["%s.%d" % (prefix, i) for i in range(1, 255)]
            with ThreadPoolExecutor(max_workers=64) as pool:
                found = [ip for ip in pool.map(open_port, cands) if ip]
            for ip in found:
                info = self._probe(ip)
                if info:
                    self._known_hosts.append(ip)
                    announce(ip, info)

    def bind_detect(self, dev_ip: str, sec_link: str, detect: Any) -> int:
        ip = _host_only(dev_ip)
        self._refresh_preset_identity()
        _ensure_network_permission(ip)

        def work() -> Optional[Dict[str, Any]]:
            return self._probe(ip)

        try:
            info = _run_blocking(work, "anycubic-detect", timeout=6.0)
        except Exception:  # noqa: BLE001
            info = None
        if not info:
            try:
                detect.result_msg = "printer did not respond at %s:%d" % (ip, HTTP_PORT)
            except Exception:  # noqa: BLE001
                pass
            return ERR_CONNECTION_TO_PRINTER_FAILED
        try:
            detect.command = "bind_detect"
            detect.result_msg = "success"
            detect.dev_id = dev_ip
            detect.dev_name = str(info.get("deviceName") or info.get("name") or "Anycubic Kobra")
            detect.model_id = self._printer_model   # must match the preset (see build_announce)
            detect.version = str(info.get("firmwareVersion") or info.get("version") or PLUGIN_VERSION)
            detect.connect_type = "lan"
            detect.bind_state = "free"
        except Exception:  # noqa: BLE001
            return ERR_GENERIC
        return 0

    # -- commands coming from the OrcaSlicer UI --------------------------------
    def _submit(self, fn: Callable[[], None]) -> None:
        w = self._cmd
        if w is not None:
            w.submit(fn)
        else:
            try:
                fn()
            except BaseException:  # noqa: BLE001
                logger.exception("command failed")

    def send_message(self, dev_id: str, json_str: str, qos: int = 0, flag: int = 0) -> int:
        return self.send_message_to_printer(dev_id, json_str, qos, flag)

    def send_message_to_printer(self, dev_id: str, json_str: str, qos: int = 0, flag: int = 0) -> int:
        try:
            cmd = json.loads(json_str)
        except Exception:  # noqa: BLE001
            return ERR_GENERIC
        if not isinstance(cmd, dict):
            return ERR_GENERIC
        c = self._client

        # queries the host expects to see answered
        info = cmd.get("info")
        if isinstance(info, dict) and info.get("command") == "get_version":
            self._push_version(str(info.get("sequence_id", "0")))
            return 0
        system = cmd.get("system")
        if isinstance(system, dict) and system.get("command") == "get_access_code":
            self._emit_local_message({"system": {"command": "get_access_code", "result": "success",
                                                 "sequence_id": str(system.get("sequence_id", "0")),
                                                 "access_code": self._access_code or "88888888"}})
            return 0
        if "pushing" in cmd:
            self._push_version()
            self._push_state()
            return 0
        # Controls sent by OrcaSlicer's native Device tab (jog, temperatures, light, pause...) are not
        # handled: printer control lives in the Kobra panel (Device (Web) tab).
        return 0 if (c is not None and c.link_up) else ERR_CONNECTION_TO_PRINTER_FAILED

    # -- printing -----------------------------------------------------------
    def _resolve_ip(self, params: Any) -> str:
        for attr in ("dev_ip", "dev_id"):
            v = _host_only(str(getattr(params, attr, "") or ""))
            if v:
                return v
        return self._client.ip if self._client else ""

    def _remote_name(self, params: Any, src: str) -> str:
        base = sanitize_filename(str(getattr(params, "task_name", "") or getattr(params, "project_name", "")
                                     or os.path.basename(src)))
        for ext in (".gcode.3mf", ".3mf", ".gcode"):
            if base.lower().endswith(ext):
                base = base[:-len(ext)]
                break
        base = (base or "print")[:100]
        return base + (".gcode.3mf" if src.lower().endswith(".3mf") else ".gcode")

    def start_send_gcode_to_sdcard(self, params: Any, update_fn: Any = None, cancel_fn: Any = None,
                                   wait_fn: Any = None) -> int:
        verify = str(getattr(params, "project_name", "")) == "verify_job"
        return self._job(params, update_fn, cancel_fn, start=False, verify=verify)

    def start_local_print(self, params: Any, update_fn: Any = None, cancel_fn: Any = None) -> int:
        return self._job(params, update_fn, cancel_fn, start=True)

    def start_print(self, params: Any, update_fn: Any = None, cancel_fn: Any = None, wait_fn: Any = None) -> int:
        return self._job(params, update_fn, cancel_fn, start=True)

    def start_local_print_with_record(self, params: Any, update_fn: Any = None, cancel_fn: Any = None,
                                      wait_fn: Any = None) -> int:
        return self._job(params, update_fn, cancel_fn, start=True)

    def _job(self, params: Any, update_fn: Any, cancel_fn: Any, start: bool, verify: bool = False) -> int:
        cfg = self._cfg()
        ip = self._resolve_ip(params)

        def upd(stage: int, code: int, msg: str = "") -> None:
            if callable(update_fn):
                try:
                    # OrcaSlicer decodes the text as Latin-1/ANSI: UTF-8 accents become "Ã©" -> ASCII only
                    update_fn(stage, code, _ascii(msg))
                except Exception:  # noqa: BLE001
                    pass

        def cancelled() -> bool:
            if callable(cancel_fn):
                try:
                    return bool(cancel_fn())
                except Exception:  # noqa: BLE001
                    return False
            return False

        def fail(code: int, msg: str) -> int:
            logger.warning("job failed (%d): %s", code, msg)
            upd(STAGE_ERROR, code, msg)
            return code

        if not ip:
            return fail(ERR_CONNECTION_TO_PRINTER_FAILED, "unknown printer address")

        def work() -> int:
            own = False
            client = self._client
            if client is None or client.ip != ip or not client.link_up:
                client = AnycubicClient(ip, poll_interval=_as_float(cfg.get("poll_interval"), 2.5))
                own = True
                if not client.start():
                    return fail(ERR_GENERIC, "no permission to create threads (accept the plugin permission)")
            try:
                upd(STAGE_CREATE, 0, "")
                if not client.ready.wait(_as_float(cfg.get("connect_timeout"), 20)) or not client.link_up:
                    return fail(ERR_CONNECTION_TO_PRINTER_FAILED,
                                "could not connect to the printer: %s" % (client.last_error or "timed out"))
                if verify:
                    return 0 if client.upload_token(wait=3.0) else fail(ERR_CONNECTION_TO_PRINTER_FAILED,
                                                                       "the printer did not report the upload token")
                return self._run_job(client, params, cfg, start, upd, cancelled, fail)
            finally:
                if own:
                    client.stop()

        try:
            return int(_run_blocking(work, "anycubic-print-job") or 0)
        except PermissionError as exc:
            logger.exception("job blocked by OrcaSlicer permissions")
            return fail(ERR_GENERIC, "OrcaSlicer denied the plugin the access it needs (%s). Accept the plugin "
                                     "permission prompt and send again." % exc)
        except BaseException as exc:  # noqa: BLE001
            logger.exception("job failed")
            return fail(ERR_GENERIC, str(exc))

    def _run_job(self, client: AnycubicClient, params: Any, cfg: Dict[str, Any], start: bool,
                 upd: Callable[..., None], cancelled: Callable[[], bool], fail: Callable[[int, str], int]) -> int:
        src = str(getattr(params, "filename", "") or "")
        if not src or not os.path.isfile(src):
            return fail(ERR_FILE_NOT_EXIST, "print file not found: %s" % src)
        # The .3mf is in the OrcaSlicer temp folder, outside the allowed folders. In this thread OrcaSlicer
        # DENIES the read right away and only later shows the permission prompt; before, sending failed and
        # had to be repeated. Now the read waits for the answer to the prompt and tries again.
        # Spaced attempts: each denied attempt queues a new prompt.
        waited = 0.0
        for delay in (0.0, 10.0, 15.0, 20.0, 30.0, 45.0):
            if delay:
                upd(STAGE_CREATE, 0, "Waiting for OrcaSlicer permission to read the file...")
                end = time.time() + delay
                while time.time() < end:
                    if cancelled():
                        return fail(ERR_CANCELED, "cancelled")
                    time.sleep(0.25)
                waited += delay
            try:
                with open(src, "rb") as fh:
                    fh.read(1)
                break
            except PermissionError:
                logger.info("reading %s denied by OrcaSlicer; waiting for the permission prompt", os.path.basename(src))
        else:
            return fail(ERR_GENERIC, "OrcaSlicer did not allow reading the file (permission prompt not "
                                     "answered in %.0f s). Accept the prompt and send again." % waited)
        plate_raw = getattr(params, "plate_index", None)
        plate_index = _as_int(plate_raw, -1) if plate_raw is not None else -1
        plate_index_opt = plate_index if plate_index >= 0 else None
        snap = client.state.snapshot()

        # --- ACE mapping and task options ---
        use_ams = False
        mapping: List[Dict[str, Any]] = []
        if start:
            has_map, mapping = build_ams_mapping(str(getattr(params, "ams_mapping", "") or ""),
                                                 str(getattr(params, "ams_mapping_info", "") or ""), snap)
            if has_map:
                # OrcaSlicer maps every filament of the project; the printer must only get the ones
                # this plate really uses (otherwise a one-color model asks for all four ACE slots).
                used = {f["index"] for f in parse_file_filaments(src, plate_index_opt)}
                kept = [m for m in mapping if m["paint_index"] in used] if used else mapping
                if kept and len(kept) < len(mapping):
                    logger.info("ACE mapping: the project has %d filaments, the plate uses %s -> sending %d",
                                len(mapping), sorted(used), len(kept))
                    mapping = kept
                logger.info("ACE mapping sent (filament -> slot): %s",
                            [(m["paint_index"] + 1, m["ams_index"] + 1) for m in mapping])
            use_ams = has_map
            if MATERIAL_SOURCE[0] == "ace" and not has_map:
                return fail(ERR_GENERIC, "ACE mode requires an explicit filament mapping")
            if not has_map and ace_units(snap):
                avail = [s for s in snap.get("filaments", []) if s.get("slot", -1) >= 0 and s.get("available")]
                avail.sort(key=lambda s: (not s.get("loaded"), s["slot"]))
                if avail:
                    s = avail[0]
                    mapping = [{"ams_index": s["slot"], "paint_index": 0, "material_type": s.get("type", "PLA"),
                                "ams_color": hex_to_rgb(s.get("color")), "paint_color": hex_to_rgb(s.get("color"))}]
                    use_ams = True
        tasks = {
            "auto_leveling": bool(getattr(params, "task_bed_leveling", False) or cfg.get("auto_leveling")),
            "vibration_compensation": bool(getattr(params, "task_vibration_cali", False) or cfg.get("vibration_compensation")),
            "flow_calibration": bool(getattr(params, "task_flow_cali", False) or cfg.get("flow_calibration")),
            "timelapse": bool(getattr(params, "task_record_timelapse", False) or cfg.get("timelapse")),
        }

        if MATERIAL_SOURCE[0] == "external":
            use_ams, mapping = False, []

        # --- filament pre-engage on the starting slot ---
        engaged = False
        pre_engage = bool(start and use_ams and cfg.get("pre_engage_filament"))
        if pre_engage:
            tool = first_tool_in_source(src, plate_index_opt)
            tool = 0 if tool is None else tool
            entry = next((m for m in mapping if m["paint_index"] == tool), mapping[0] if mapping else None)
            slot_idx = _as_int(entry["ams_index"], -1) if entry else -1
            if 0 <= slot_idx <= 3:
                upd(STAGE_CREATE, 0, "engaging slot %d" % (slot_idx + 1))
                reports0 = _as_int(client.state.snapshot().get("channel_reports"), 0)
                client.switch_channel(slot_idx)
                time.sleep(2.0)
                start_t = time.time()
                end = start_t + _as_float(cfg.get("pre_engage_timeout"), 60)
                no_reaction_s = _as_float(cfg.get("pre_engage_no_reaction_timeout"), 8)
                last_log = 0.0
                t = client.state.snapshot()
                while time.time() < end:
                    if cancelled():
                        return fail(ERR_CANCELED, "cancelled")
                    t = client.state.snapshot()
                    # Some printers/firmwares (seen on the Kobra 4) never answer
                    # switchChannel: the channel stays at -1 and sending was stuck at 20% until the
                    # timeout (120 s). With no reaction within a few seconds, continue without pre-engage.
                    reacted = (_as_int(t.get("channel_reports"), 0) > reports0
                               or _as_int(t.get("channel_index"), -1) == slot_idx
                               or 1 <= _as_int((t.get("feed_status") or {}).get("current_status"), 0) <= 3
                               or str(t.get("state", "")).lower() in ("feeding", "loading"))
                    if not reacted and time.time() - start_t > no_reaction_s:
                        logger.warning("pre-engage: the printer did not react to switchChannel within %.0f s; "
                                       "sending without pre-engage", no_reaction_s)
                        break
                    if time.time() - last_log >= 10.0:
                        last_log = time.time()
                        logger.warning("pre-engage slot %d: state=%r channel_index=%r channel_status=%r feed_status=%r",
                                       slot_idx, t.get("state"), t.get("channel_index"), t.get("channel_status"),
                                       t.get("feed_status"))
                    feed = _as_int((t.get("feed_status") or {}).get("current_status"), 0)
                    ch_st = _as_int(t.get("channel_status"), 0)
                    loading = (1 <= feed <= 3) or ch_st == 3 or str(t.get("state", "")).lower() in ("feeding", "loading")
                    if (_as_int(t.get("channel_index"), -1) == slot_idx and ch_st == 0 and not loading
                            and str(t.get("state", "")).lower() in ("free", "ready", "idle", "")):
                        engaged = True
                        break
                    time.sleep(0.3)
                if not engaged:
                    logger.warning("pre-engage NOT confirmed: state=%r channel_index=%r channel_status=%r feed_status=%r",
                                   t.get("state"), t.get("channel_index"), t.get("channel_status"), t.get("feed_status"))
                    if cfg.get("pre_engage_strict", False):
                        return fail(ERR_CONNECTION_TO_PRINTER_FAILED,
                                    "the filament pre-engage was not confirmed by the printer; sending aborted "
                                    "so it does not cancel the job in the middle of feeding")
                    logger.warning("continuing with the upload anyway (pre_engage_strict=false)")

        # --- adjust the file ---
        tmp_path = ""
        try:
            upd(STAGE_CREATE, 0, "")
            path, is_tmp, note = prepare_upload_file(
                src, bool(cfg.get("rename_plate_to_first")),
                bool(start and engaged and cfg.get("skip_first_toolchange")),
                str(cfg.get("skip_first_toolchange_script") or ""), plate_index_opt,
                used_filaments=parse_file_filaments(src, plate_index_opt))
            if is_tmp:
                tmp_path = path
            if note:
                logger.info("file adjusted: %s", note)
            remote = self._remote_name(params, src)

            def progress(pct: int) -> None:
                upd(STAGE_UPLOAD, pct, "%d%%" % pct)

            try:
                md5, size = client.upload_file(path, remote, progress, cancelled)
                try:
                    remember_file_filaments(client.ip, remote, parse_file_filaments(src, plate_index_opt))
                    remember_file_preview(client.ip, remote, src, plate_index_opt, _as_int(size, 0))
                except Exception:  # noqa: BLE001
                    logger.debug("file filaments not recorded", exc_info=True)
            except UploadCancelled:
                return fail(ERR_CANCELED, "cancelled")
            except (PrinterError, OSError, http.client.HTTPException, socket.timeout) as exc:
                return fail(ERR_UPLOAD_FAILED, "upload failed: %s" % exc)
            upd(STAGE_WAITING, 0, "")
            if start:
                time.sleep(0.5)
                upd(STAGE_SENDING, 0, "")
                try:
                    client.start_print(start_filename_for_print(remote), md5, size, use_ams, mapping, tasks)
                except PrinterError as exc:
                    return fail(ERR_CONNECTION_TO_PRINTER_FAILED, "file uploaded, but starting the print failed: %s" % exc)
            upd(STAGE_FINISHED, 100, "")
            return 0
        finally:
            if tmp_path:
                try:
                    os.unlink(tmp_path)
                except OSError:
                    pass


# --------------------------------------------------------------------------
# Panel shared state
# --------------------------------------------------------------------------
_ACTIVE_AGENT: List[Any] = [None]

WORKBENCH_DIR = "kobra_workbench"
WORKBENCH_PORT = 18989
_WB_ASSET_TYPES = {".js": "application/javascript; charset=utf-8", ".css": "text/css; charset=utf-8",
                   ".png": "image/png", ".svg": "image/svg+xml", ".jpg": "image/jpeg", ".gif": "image/gif",
                   ".webp": "image/webp", ".woff2": "font/woff2"}
_WB_MAX_UPLOAD = 300 * 1024 * 1024


def _workbench_dir() -> str:
    return os.path.join(_resource_dir(), WORKBENCH_DIR)


def build_material_update_messages(slots: List[Dict[str, Any]]) -> List[Tuple[str, str, Dict[str, Any]]]:
    """(type, action, data) per slot -- the Kobra X accepts one material update per message.
    Same format as the OrcaCubic daemon (color, color group, finish, brand)."""
    out: List[Tuple[str, str, Dict[str, Any]]] = []
    for s in slots or []:
        if not isinstance(s, dict):
            continue
        idx = _as_int(s.get("index"), 0)
        box_id = _as_int(s.get("box_id"), -1)
        mtype = str(s.get("type") or "PLA")
        rgb = hex_to_rgb(s.get("color"), (35, 163, 199))
        if s.get("source") == "external":
            out.append(("extfilbox", "setInfo", {"type": mtype, "color": rgb}))
            continue
        finish = str(s.get("finish_type") or "solid")
        icon = _as_int(s.get("icon_type"), 3 if finish == "luminous" else (1 if finish == "gradient" else 0))
        group = [hex_to_rgb(g) + [255] for g in (s.get("color_group") or [])
                 if (isinstance(g, str) and g.startswith("#") and len(g) >= 7) or (isinstance(g, list) and len(g) >= 3)]
        if not group:
            group = [rgb + [255]]
        out.append(("multiColorBox", "setInfo", {"multi_color_box": [{"id": box_id, "slots": [{
            "index": idx, "type": mtype, "brand": str(s.get("brand") or "Anycubic"), "color": group[0][:3],
            "color_group": group, "icon_type": icon}]}]}))
    return out


def mapping_for_used(t: Dict[str, Any], fils: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """ACE mapping with only the filaments a file uses (each to the slot of the same number when it is
    loaded, otherwise to the best free slot of the same material). Unknown filaments: one slot."""
    slots = [f for f in t.get("filaments", []) if f.get("source") not in ("external", "external_mcb")
             and f.get("available", True) and _as_int(f.get("slot"), -1) >= 0]
    if not slots:
        return []
    if not fils:
        s = next((x for x in slots if x.get("loaded")), slots[0])
        rgb = hex_to_rgb(s.get("color"), (35, 163, 199))
        return [{"ams_index": _as_int(s.get("slot"), 0), "paint_index": 0,
                 "material_type": str(s.get("type") or "PLA"), "ams_color": rgb, "paint_color": rgb}]
    by_slot = {_as_int(s.get("slot"), -1): s for s in slots}
    taken: set = set()
    out = []
    for f in sorted(fils, key=lambda x: _as_int(x.get("index"), 0)):
        idx = _as_int(f.get("index"), 0)
        s = by_slot.get(idx) if idx not in taken else None
        if s is None:
            want = str(f.get("type") or "").upper()
            free = [x for x in slots if _as_int(x.get("slot"), -1) not in taken] or slots
            s = next((x for x in free if str(x.get("type") or "").upper() == want), free[0])
        taken.add(_as_int(s.get("slot"), 0))
        out.append({"ams_index": _as_int(s.get("slot"), 0), "paint_index": idx,
                    "material_type": str(f.get("type") or s.get("type") or "PLA"),
                    "ams_color": hex_to_rgb(s.get("color"), (35, 163, 199)),
                    "paint_color": hex_to_rgb(f.get("color") or s.get("color"), (35, 163, 199))})
    return out


def default_ams_mapping(t: Dict[str, Any], use_ams: bool = True) -> List[Dict[str, Any]]:
    """1:1 mapping of the ACE slots (as the OrcaCubic daemon does for standalone files)."""
    fils = [f for f in t.get("filaments", []) if f.get("source") not in ("external", "external_mcb")
            and f.get("available", True)]
    out = []
    for i in range(len(fils) if fils else (4 if use_ams else 0)):
        f = fils[i] if i < len(fils) else {}
        rgb = hex_to_rgb(f.get("color"), (35, 163, 199))
        out.append({"ams_index": _as_int(f.get("slot"), i), "paint_index": i,
                    "material_type": str(f.get("type") or "PLA"), "ams_color": rgb, "paint_color": rgb})
    return out


def _slicer_filaments() -> List[Dict[str, str]]:
    """Filaments (type + color) of the project open in OrcaSlicer, in extruder order."""
    try:
        bundle = orca.host.preset_bundle()
        colours = str(bundle.full_config_value("filament_colour") or "")
        types = str(bundle.full_config_value("filament_type") or "")
    except Exception as exc:  # noqa: BLE001
        logger.info("panel: could not read the project filaments (%s)", exc)
        return []
    cl = [c.strip().strip('"') for c in colours.split(";")] if colours else []
    tl = [x.strip().strip('"') for x in types.split(";")] if types else []
    n = max(len(cl), len(tl))
    return [{"type": (tl[i] if i < len(tl) and tl[i] else "PLA"),
             "color": (cl[i][:7] if i < len(cl) and cl[i].startswith("#") else "#00d2ff")} for i in range(n)]


def workbench_slicer_reply(body: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """Answers the messages the panel used to send to the OrcaCubic C++ code."""
    cmd = str(body.get("command") or body.get("method") or "")
    rid = body.get("id") or body.get("sequence_id") or ""
    base: Dict[str, Any] = {"type": "response", "command": cmd, "id": rid, "sequence_id": rid, "code": 0,
                            "message": "success", "data": {}}
    if cmd == "get_anycubic_printers":
        base["data"] = {"printers": workbench_server().printer_list()}
        return base
    if cmd == "save_anycubic_printer":
        ok, msg, pid = workbench_server().save_printer(body.get("data") or {})
        if not ok:
            base["code"], base["message"] = 1, msg
        base["data"] = {"id": pid, "printers": workbench_server().printer_list()}
        return base
    if cmd == "delete_anycubic_printer":
        workbench_server().delete_printer(str((body.get("data") or {}).get("preset_name") or ""))
        base["data"] = {"printers": workbench_server().printer_list()}
        return base
    if cmd == "monitor_anycubic_printer":
        ok, msg = workbench_server().monitor_printer(str((body.get("data") or {}).get("preset_name") or ""))
        if not ok:
            base["code"], base["message"] = 1, msg
        return base
    if cmd == "activate_anycubic_printer":
        return base
    if cmd == "request_plate_filaments_to_printer":
        base["data"] = {"filaments": _slicer_filaments()}
        return base
    return None   # open_anycubic_printer_settings, sync_filaments_to_slicer: handled by the panel itself


class WorkbenchServer:
    """Local HTTP server that emulates the OrcaCubic daemon using the active agent connection."""

    def __init__(self, port: Optional[int] = None) -> None:
        import secrets
        self.token = secrets.token_urlsafe(18)
        self.port = 0
        self._details_cache: Dict[Tuple[Any, ...], Dict[str, Any]] = {}
        self._details_busy_refused: set = set()   # printers that refused previews during the current print
        # Printers saved in the panel itself (name + IP), independent of the OrcaSlicer presets.
        self._plock = threading.RLock()
        self._printers: List[Dict[str, str]] = []
        self._monitored = ""                       # id of the printer shown in the panel
        self._own: Optional[AnycubicClient] = None # panel connection when it is not the agent one
        self._load_printers()
        if port:
            self._start(port)

    # -- saved printers -----------------------------------------------------------
    @staticmethod
    def _store_path() -> str:
        return os.path.join(_plugin_dir(), "kobra_printers.json")

    def _load_printers(self) -> None:
        try:
            with open(self._store_path(), "r", encoding="utf-8") as f:
                data = json.load(f)
        except (OSError, ValueError):
            return
        items = data.get("printers") if isinstance(data, dict) else None
        out: List[Dict[str, str]] = []
        for it in items or []:
            if not isinstance(it, dict):
                continue
            host = _host_only(str(it.get("host") or ""))
            if not host:
                continue
            out.append({"id": str(it.get("id") or _rand_hex(8)), "name": str(it.get("name") or host)[:80],
                        "host": host, "model": str(it.get("model") or "Anycubic Kobra 4")[:80]})
        self._printers = out
        self._monitored = str(data.get("monitored") or "") if isinstance(data, dict) else ""

    def _save_printers(self) -> None:
        path = self._store_path()
        tmp = path + ".tmp"
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({"printers": self._printers, "monitored": self._monitored}, f, ensure_ascii=False, indent=1)
            os.replace(tmp, path)
        except OSError as exc:
            logger.warning("panel: could not save the printer list (%s)", exc)

    def _agent_ip(self) -> str:
        a = self._agent()
        c = getattr(a, "_client", None) if a is not None else None
        return c.ip if c is not None else ""

    def _agent_preset_name(self) -> str:
        try:
            p = orca.host.preset_bundle().current_printer_preset()
            for attr in ("name", "label"):
                v = getattr(p, attr, None)
                v = v() if callable(v) else v
                if v:
                    return str(v)
        except Exception:  # noqa: BLE001
            pass
        return ""

    def _seed_from_agent(self) -> None:
        """The first time, adds the printer OrcaSlicer is already using to the list."""
        ip = self._agent_ip()
        if not ip or any(p["host"] == ip for p in self._printers):
            return
        a = self._agent()
        snap = a._client.state.snapshot() if a is not None and a._client is not None else {}
        model = str(snap.get("model") or getattr(a, "_printer_model", "") or "Anycubic Kobra 4")
        self._printers.append({"id": _rand_hex(8), "name": self._agent_preset_name() or model,
                               "host": ip, "model": model})
        self._save_printers()

    def _find(self, pid: str) -> Optional[Dict[str, str]]:
        return next((p for p in self._printers if p["id"] == pid), None)

    def _monitored_host(self) -> str:
        p = self._find(self._monitored)
        return p["host"] if p else self._agent_ip()

    def printer_list(self) -> List[Dict[str, Any]]:
        with self._plock:
            self._seed_from_agent()
            agent_ip = self._agent_ip()
            mon = self._monitored_host()
            out = []
            for p in self._printers:
                out.append({"preset_name": p["id"], "name": p["name"], "model": p["model"], "host": p["host"],
                            "active": bool(agent_ip) and p["host"] == agent_ip,
                            "selected": p["host"] == agent_ip, "monitored": p["host"] == mon})
            return out

    def save_printer(self, data: Dict[str, Any]) -> Tuple[bool, str, str]:
        name = str(data.get("name") or "").strip()[:80]
        host = _host_only(str(data.get("host") or "").strip())
        model = str(data.get("model") or "").strip()[:80] or "Anycubic Kobra 4"
        if not name or not host:
            return False, "Enter a printer name and IP address.", ""
        if not re.match(r"^[A-Za-z0-9.\-]+$", host):
            return False, "Invalid IP address.", ""
        with self._plock:
            pid = str(data.get("preset_name") or data.get("id") or "")
            if any(p["host"] == host and p["id"] != pid for p in self._printers):
                return False, "This IP address is already in the list.", ""
            cur = self._find(pid) if pid else None
            if cur is not None:
                host_changed = cur["host"] != host
                cur.update(name=name, host=host, model=model)
                if host_changed and pid == self._monitored:
                    self._drop_own()
            else:
                pid = _rand_hex(8)
                self._printers.append({"id": pid, "name": name, "host": host, "model": model})
            self._save_printers()
        logger.info("panel: printer saved %s (%s)", name, host)
        a = self._agent()
        if a is not None and hasattr(a, "reannounce"):
            _ensure_network_permission(host)
            _spawn(a.reannounce, "kobra-reannounce", host)
        return True, "", pid

    def delete_printer(self, pid: str) -> None:
        with self._plock:
            self._printers = [p for p in self._printers if p["id"] != pid]
            if self._monitored == pid:
                self._monitored = ""
                self._drop_own()
            self._save_printers()

    @staticmethod
    def preset_host() -> str:
        """IP of the selected printer preset (main thread only)."""
        try:
            v = orca.host.preset_bundle().current_printer_preset().config_value("print_host")
            return _host_only("" if v is None else str(v))
        except Exception:  # noqa: BLE001
            return ""

    # -- Setup tab ----------------------------------------------------------------
    def setup_status(self) -> Dict[str, Any]:
        comps = setup_components()
        run: Dict[str, Any] = {}
        try:
            with open(os.path.join(_tmp_dir(), "setup_status.json"), "r", encoding="utf-8-sig") as f:
                run = json.load(f)
        except (OSError, ValueError):
            run = {}
        proc = getattr(self, "_setup_proc", None)
        running = proc is not None and proc.poll() is None
        started = getattr(self, "_setup_started", 0.0)
        # "fresh": the last run happened in this session (old results are not shown again)
        run["fresh"] = bool(started) and _as_float(run.get("time"), 0) >= started - 5
        supported = os.name == "nt" and os.path.isfile(setup_script_path())
        msg = "" if supported else ("Automatic installation only works on Windows." if os.name != "nt"
                                    else "The setup folder is missing next to the plugin; copy it from the plugin package.")
        return {"status": "ok", "components": comps, "running": running, "run": run if run.get("fresh") else {},
                "supported": supported, "message": msg}

    def launch_setup(self) -> Dict[str, Any]:
        """Runs the dependency installer in its own console window. Called on the main thread, so
        OrcaSlicer can show its permission prompt right away."""
        if os.name != "nt" or not os.path.isfile(setup_script_path()):
            return {"status": "error", "message": "The setup folder is missing next to the plugin."}
        proc = getattr(self, "_setup_proc", None)
        if proc is not None and proc.poll() is None:
            return {"status": "ok", "message": "already running"}
        import subprocess
        try:
            os.remove(os.path.join(_tmp_dir(), "setup_status.json"))
        except OSError:
            pass
        self._setup_started = time.time()
        try:
            self._setup_proc = subprocess.Popen(command_line(setup_command()),
                                                creationflags=0x00000010)   # CREATE_NEW_CONSOLE
        except Exception as exc:  # noqa: BLE001
            self._setup_started = 0.0
            logger.warning("setup: could not start the installer: %s", exc)
            return {"status": "error", "message": "OrcaSlicer did not allow the plugin to start the installer (%s). "
                                                  "Accept the plugin permission prompt and try again." % exc}
        logger.info("setup: installer started")
        return {"status": "ok"}

    def select_from_preset(self, ip: str, name: str = "") -> None:
        """The Device (Web) tab opened the panel for the IP of the selected preset: shows that printer
        (and adds it to the list if it is not there yet)."""
        ip = _host_only(ip)
        if not ip or not re.match(r"^[A-Za-z0-9.\-]+$", ip):
            return
        with self._plock:
            p = next((x for x in self._printers if x["host"] == ip), None)
            if p is None:
                pid = _rand_hex(8)
                self._printers.append({"id": pid, "name": (name or self._agent_preset_name() or "Anycubic Kobra")[:80],
                                       "host": ip, "model": "Anycubic Kobra 4"})
                self._save_printers()
            else:
                pid = p["id"]
        self.monitor_printer(pid)

    def monitor_printer(self, pid: str) -> Tuple[bool, str]:
        """Switches the printer shown in the panel. Called on the main thread (permission prompt)."""
        with self._plock:
            p = self._find(pid)
            if p is None:
                return False, "Printer not found"
            self._monitored = pid
            self._save_printers()
            if p["host"] == self._agent_ip():
                self._drop_own()
                return True, ""
            if self._own is not None and self._own.ip == p["host"]:
                return True, ""
            self._drop_own()
            _ensure_network_permission(p["host"])
            a = self._agent()
            poll = _as_float(getattr(a, "_cfg_cache", {}).get("poll_interval"), 2.5) if a is not None else 2.5
            c = AnycubicClient(p["host"], poll_interval=poll)
            if not c.start():
                return False, "The slicer did not allow the plugin to start a connection."
            self._own = c
            self._details_cache.clear()
            logger.info("panel: monitoring %s (%s) with its own connection", p["name"], p["host"])
            return True, ""

    def _drop_own(self) -> None:
        c, self._own = self._own, None
        if c is not None:
            _spawn(c.stop, "kobra-wb-stop")
        self._details_cache.clear()

    def _current(self) -> Tuple[Optional[AnycubicClient], bool]:
        """(client of the printer shown in the panel, is it the agent connection?)."""
        mon = self._monitored_host()
        a = self._agent()
        ac = getattr(a, "_client", None) if a is not None else None
        if ac is not None and (not mon or ac.ip == mon):
            if self._own is not None:
                self._drop_own()
            return ac, True
        if self._own is not None and self._own.ip == mon:
            return self._own, False
        return None, False

    # -- camera -------------------------------------------------------------------
    def camera_source(self, c: AnycubicClient) -> str:
        """Current FLV URL of the printer camera (asks for startCapture if there is none yet)."""
        url = c.state.snapshot().get("camera_url") or ""
        if url:
            return url
        c.camera(True)
        time.sleep(1.0)
        c.send("slicer", "info", "query")
        c.send("web", "peripherie", "query")
        end = time.time() + 7.0
        while time.time() < end:
            url = c.state.snapshot().get("camera_url") or ""
            if url:
                return url
            time.sleep(0.25)
        raise PrinterError("the printer did not report the camera URL")

    def stream_camera(self, handler: Any) -> None:
        """Forwards the printer FLV video (H.264) to the panel page, which plays it with flv.js.
        Same origin as the page, so no CORS is needed and the camera token never reaches the page."""
        c = self._client()
        if c is None:
            handler.send_error(503, "printer not connected")
            return
        try:
            src = self.camera_source(c)
        except Exception as exc:  # noqa: BLE001
            logger.warning("camera: %s", exc)
            handler.send_error(503, "camera unavailable")
            return
        u = urllib.parse.urlsplit(src)
        if u.scheme not in ("http", "") or not u.hostname:
            handler.send_error(502, "invalid camera url")
            return
        # the path (/live/<token>) is a credential: only host and port go to the log
        logger.info("camera: streaming from %s://%s", u.scheme or "http", u.netloc)
        conn = http.client.HTTPConnection(u.hostname, u.port or 80, timeout=15)
        total = 0
        try:
            conn.request("GET", (u.path or "/") + ("?" + u.query if u.query else ""), headers={"User-Agent": USER_AGENT})
            resp = conn.getresponse()
            # The Kobra answers 206 (Partial Content) to the /live/<token> stream; it is regular video.
            if not 200 <= resp.status < 300:
                with c.state.lock:
                    c.state.t["camera_url"] = ""          # stale token: ask for a new one next time
                handler.send_error(502, "camera HTTP %d" % resp.status)
                return
            handler.send_response(200)
            handler.send_header("Content-Type", "video/x-flv")
            handler.send_header("Cache-Control", "no-store")
            handler.end_headers()
            while True:
                chunk = resp.read1(65536) if hasattr(resp, "read1") else resp.read(65536)
                if not chunk:
                    break
                handler.wfile.write(chunk)
                total += len(chunk)
        except (BrokenPipeError, ConnectionError):
            pass
        except Exception as exc:  # noqa: BLE001
            logger.warning("camera: error reading the video: %s", exc)
        finally:
            conn.close()
            logger.info("camera: stream closed (%d bytes)", total)

    def handle(self, method: str, path: str, data: Dict[str, Any]) -> Tuple[int, Any]:
        """One panel API request (over the local HTTP server)."""
        path = urllib.parse.urlparse(path).path
        if method == "GET":
            if path in ("/status", "/") or path.startswith("/api/v1"):
                return 200, self.status()
            if path == "/health":
                return 200, {"status": "ok"}
            if path == "/setup":
                return 200, self.setup_status()
            if path == "/recent_messages":
                c = self._client()
                return 200, {"model_id": c.state.snapshot().get("model_id", "") if c else "",
                             "messages": list(c.recent[-60:]) if c else []}
            return 404, {"error": "not found"}
        if path == "/control":
            return 200, self.control(data)
        if path == "/run_gcode":
            return 200, self.run_gcode(data)
        if path == "/upload_print_file":
            return 200, self.upload_print_file(data)
        if path == "/sync_to_printer":
            return 200, self.sync_to_printer(data)
        if path == "/slicer":
            return 200, workbench_slicer_reply(data) or {"type": "response", "code": 0}
        if path == "/files":
            return 200, self.files(data)
        return 404, {"error": "not found"}

    def files(self, data: Dict[str, Any]) -> Dict[str, Any]:
        """Files sub-tab: list, delete and print files from the printer memory / USB drive."""
        c = self._client()
        if c is None:
            return {"status": "error", "message": "Printer not connected (select the Kobra in the printer list)."}
        op = str(data.get("op") or "list")
        storage = str(data.get("storage") or "local")
        if storage not in ("local", "udisk"):
            return {"status": "error", "message": "Unknown storage"}
        parts = [x for x in str(data.get("path") or "/").replace("\\", "/").split("/") if x not in ("", ".")]
        if any(x == ".." for x in parts):
            return {"status": "error", "message": "Invalid path"}
        path = "/" + "/".join(parts)
        try:
            if op == "list":
                out = []
                for r in c.list_files(storage, path):
                    name = str(r.get("filename") or r.get("name") or "").strip()
                    if not name:
                        continue
                    ts = _as_int(r.get("timestamp", r.get("time", r.get("create_time"))), 0)
                    if ts > 10_000_000_000:
                        ts //= 1000
                    out.append({"name": name, "path": path, "size": _as_int(r.get("size", r.get("filesize")), 0),
                                "timestamp": ts, "is_dir": bool(r.get("is_dir")), "hidden": bool(r.get("hidden"))})
                out.sort(key=lambda f: (not f["is_dir"], -f["timestamp"], f["name"].lower()))
                return {"status": "ok", "storage": storage, "path": path, "files": out}
            if op == "usage":
                return dict(c.storage_usage(storage), status="ok", storage=storage)
            if op in ("delete_many", "copy_to_local"):
                items = []
                for it in data.get("items") or []:
                    ip = [x for x in str(it.get("path") or "/").replace("\\", "/").split("/") if x not in ("", ".")]
                    fn = sanitize_filename(str(it.get("filename") or ""), "")
                    if fn and ".." not in ip:
                        items.append({"path": "/" + "/".join(ip), "filename": fn})
                if not items:
                    return {"status": "error", "message": "Nothing selected"}
                if op == "copy_to_local":
                    if storage != "udisk":
                        return {"status": "error", "message": "Copy works from the USB drive to the printer."}
                    res = c.copy_to_local(items)
                    if res.get("status") == "unsupported":
                        res["message"] = "This printer does not accept copy commands over the network."
                    return res
                failed = []
                by_folder: Dict[str, List[str]] = {}
                for it in items:
                    by_folder.setdefault(it["path"], []).append(it["filename"])
                deleted = 0
                for folder, names in by_folder.items():
                    try:
                        c.delete_files(storage, folder, names)
                        deleted += len(names)
                    except PrinterError as exc:
                        failed.extend({"filename": n, "message": str(exc)} for n in names)
                if not deleted:
                    return {"status": "error", "message": failed[0]["message"] if failed else "Delete refused", "failed": failed}
                return {"status": "ok", "deleted": deleted, "failed": failed}
            fname = sanitize_filename(str(data.get("filename") or ""), "")
            if not fname:
                return {"status": "error", "message": "Missing file name"}
            if op == "filaments":
                fils = lookup_file_filaments(c.ip, fname)
                source = "file" if fils else ""
                if not fils:
                    for k, v in self._details_cache.items():
                        if k[0] == storage and k[1] == path and k[2] == fname and isinstance(v.get("raw"), dict):
                            fils = filaments_from_details(v["raw"])
                            break
                    if fils:
                        source = "printer"
                if not fils and job_state(c.state.snapshot()).lower() not in ("printing", "paused", "auto_leveling", "heating", "busy", "preheating"):
                    try:
                        rel = fname if path == "/" else path.strip("/") + "/" + fname
                        d = c.file_details(storage, rel)
                        log_details_once(fname, d)
                        fils = filaments_from_details(d)
                        source = "printer" if fils else ""
                    except (PrinterError, DetailsUnsupported):
                        pass
                logger.info("panel: filaments of %s: %s (source: %s)", fname, [(f.get("index"), f.get("type"), f.get("color")) for f in fils], source or "unknown")
                return {"status": "ok", "filename": fname, "filaments": fils, "source": source or "unknown"}
            if op == "rename":
                new = str(data.get("new_name") or "").strip()
                if not new or new in (".", "..") or any(ch in new for ch in '/\\:*?"<>|'):
                    return {"status": "error", "message": "Invalid name. Do not use / \\ : * ? \" < > |"}
                if new == fname:
                    return {"status": "ok", "storage": storage, "path": path, "filename": fname}
                st = job_state(c.state.snapshot()).lower()
                if st in ("printing", "busy", "paused", "pausing", "heating", "auto_leveling", "preheating"):
                    return {"status": "error", "message": "The printer is busy. Rename the file when the print is over."}
                c.rename_file(storage, path, fname, new)
                return {"status": "ok", "storage": storage, "path": path, "filename": new}
            if op == "delete":
                c.delete_files(storage, path, [fname])
                return {"status": "ok", "storage": storage, "path": path, "filename": fname}
            if op == "details":
                key = (storage, path, fname, _as_int(data.get("size"), 0), _as_int(data.get("timestamp"), 0))
                cached = self._details_cache.get(key)
                if cached is not None:
                    return {k: v for k, v in dict(cached, cached=True).items() if k != "raw"}
                busy = job_state(c.state.snapshot()).lower() in ("printing", "paused", "preheating", "auto_leveling", "busy", "heating")
                if not busy:
                    self._details_busy_refused.discard(c.ip)
                saved = lookup_thumbnail(c.ip, fname, _as_int(data.get("size"), 0))
                if saved and (busy or saved.get("info")):
                    # preview saved on disk (from an earlier read, or taken from the file sent by
                    # OrcaSlicer): no request to the printer
                    return {"status": "ok", "storage": storage, "path": path, "filename": fname,
                            "thumbnail": saved["thumbnail"], "info": saved.get("info") or {}, "cached": True}
                if busy and c.ip in self._details_busy_refused:
                    return {"status": "busy", "message": "The printer does not send previews while it prints."}
                rel = fname if path == "/" else path.strip("/") + "/" + fname
                try:
                    d = c.file_details(storage, rel, count_refusal=not busy, timeout=5.0 if busy else 8.0)
                except DetailsUnsupported:
                    return {"status": "unsupported", "message": "The printer does not provide previews for these files."}
                except PrinterError as exc:
                    if busy:
                        self._details_busy_refused.add(c.ip)
                        logger.info("panel: previews not available while printing (%s)", exc)
                        return {"status": "busy", "message": "The printer does not send previews while it prints."}
                    raise
                log_details_once(fname, d)
                fields = ("print_time", "estimate", "material_type", "layer_height", "filament_used", "total_layers")
                res = {"status": "ok", "storage": storage, "path": path, "filename": fname,
                       "thumbnail": find_thumbnail(d), "raw": {k: v for k, v in d.items() if not isinstance(v, str) or len(v) < 512} if isinstance(d, dict) else {},
                       "info": {k: d[k] for k in fields if isinstance(d, dict) and d.get(k) not in (None, "")}}
                self._details_cache[key] = res
                if res["thumbnail"]:
                    remember_thumbnail(c.ip, fname, res["thumbnail"], res["info"], _as_int(data.get("size"), 0))
                if len(self._details_cache) > 400:
                    self._details_cache.pop(next(iter(self._details_cache)))
                return {k: v for k, v in res.items() if k != "raw"}
            if op == "print":
                st = job_state(c.state.snapshot()).lower()
                if st in ("printing", "busy", "paused", "pausing", "heating", "auto_leveling", "preheating"):
                    return {"status": "error", "message": "The printer is busy. Wait for the current job to finish."}
                use_ams = bool(data.get("use_ams", True))
                ts = data.get("task_settings") or {}
                chosen = data.get("mapping")
                if use_ams and isinstance(chosen, list) and chosen:
                    mapping = mapping_from_choice(chosen, c.state.snapshot())
                    if not mapping:
                        return {"status": "error", "message": "The selected ACE slots are not available."}
                else:
                    mapping = mapping_for_used(c.state.snapshot(), lookup_file_filaments(c.ip, fname)) if use_ams else []
                c.send("slicer", "print", "start", {
                    "taskid": "-1", "filename": fname, "filepath": path, "filetype": 2 if storage == "udisk" else 1,
                    "task_mode": 1, "project_type": 1, "url": "", "md5": "",
                    "filesize": _as_int(data.get("filesize"), 0),
                    "ams_settings": {"use_ams": use_ams and bool(mapping), "ams_box_mapping": mapping},
                    "task_settings": {
                        "auto_leveling": 1 if ts.get("auto_leveling", 1) else 0,
                        "vibration_compensation": 1 if ts.get("vibration_compensation", 0) else 0,
                        "flow_calibration": 1 if ts.get("flow_calibration", 0) else 0,
                        "dry_mode": 0, "ai_settings": {"status": 0, "count": 0, "type": 0},
                        "timelapse": {"status": 1 if ts.get("timelapse", 0) else 0, "count": 0, "type": 0},
                        "drying_settings": {"status": 0, "target_temp": 0, "duration": 0, "remain_time": 0},
                        "model_objects_skip_parts": []}})
                logger.info("panel: printing %s%s (%s, ACE=%s, map=%s)", path.rstrip("/") + "/", fname, storage, use_ams,
                            [(m["paint_index"], m["ams_index"]) for m in mapping])
                return {"status": "ok", "storage": storage, "path": path, "filename": fname}
            return {"status": "error", "message": "Unknown operation"}
        except PrinterError as exc:
            msg = str(exc)
            if "did not respond" in msg:
                msg = "The printer did not answer. Check that it is on and in LAN mode."
            return {"status": "error", "message": msg}

    # -- utilities ----------------------------------------------------------------
    @property
    def base(self) -> str:
        return "http://127.0.0.1:%d" % self.port

    @staticmethod
    def _agent() -> Any:
        return _ACTIVE_AGENT[0]

    def _client(self) -> Optional[AnycubicClient]:
        c = self._current()[0]
        return c if (c is not None and c.link_up) else None

    def status(self) -> Dict[str, Any]:
        c = self._current()[0]
        if c is None:
            mon = self._monitored_host()
            return {"connected": False, "ip": mon, "state": "offline",
                    "model": "Kobra not connected",
                    "job_name": "Connecting..." if mon else "Add a printer with the + button in the list",
                    "material_boxes": [], "filaments": []}
        with c.state.lock:
            t = c.state.t
            if t.get("last_error"):
                age = time.time() - _as_float(t.get("last_error_time"), 0)
                if age > 20 or job_state(t).lower() in ("printing", "auto_leveling", "heating"):
                    t["last_error"], t["last_error_code"] = "", 0
        snap = c.state.snapshot()
        snap.pop("upload_url", None)
        snap["connected"] = bool(c.link_up)
        st = job_state(snap) or "free"
        snap["state"] = st
        snap["print_state"] = st
        snap["ip"] = c.ip
        snap["camera_url"] = "%s/camera.flv?k=%s" % (self.base, self.token) if c.link_up and self.port else ""
        if snap.get("job_name") in (None, ""):
            snap["job_name"] = "Ready"
        return snap

    def control(self, data: Dict[str, Any]) -> Dict[str, Any]:
        action = str(data.get("action") or "")
        c = self._client()
        if action == "clear_alert":
            if c is not None:
                with c.state.lock:
                    c.state.t["last_error"], c.state.t["last_error_code"] = "", 0
            return {"status": "ok"}
        if c is None:
            return {"status": "error", "message": "Printer not connected (select the Kobra in the printer list)"}
        if action in ("pause", "resume", "stop"):
            c.print_ctl(action)
        elif action == "light":
            c.set_light(_as_int(data.get("status"), 1) == 1)
        elif action in ("start_capture", "video_start"):
            c.camera(True)
        elif action in ("stop_capture", "video_stop"):
            c.camera(False)
        elif action == "speed":
            c.set_speed_mode(_as_int(data.get("mode"), 2))
        elif action == "jog":
            axis = str(data.get("axis") or "X").upper()
            d = 1 if _as_int(data.get("dir"), 1) > 0 else -1
            a = self._agent()
            if axis == "Y" and a is not None and a._cfg_cache.get("invert_y", True):
                d = -d
            c.jog(axis, d, abs(_as_float(data.get("dist"), 10.0)))
        elif action == "home":
            c.home(str(data.get("axis") or "XYZ"))
        elif action in ("motor_off", "turnOff"):
            c.motors_off()
        elif action == "switch_channel":
            c.switch_channel(_as_int(data.get("index", data.get("slot", 0)), 0))
        elif action == "feed_filament":
            c.feed_filament(_as_int(data.get("box_id"), -1), _as_int(data.get("slot"), 0), str(data.get("type") or "PLA"))
            with c.state.lock:
                c.state.t["feed_status"] = {"box_id": _as_int(data.get("box_id"), -1), "slot_index": _as_int(data.get("slot"), 0),
                                            "type": 1, "current_status": 1, "code": 0}
        elif action == "drying":
            on = bool(data.get("on"))
            temp = max(35, min(65, _as_int(data.get("target_temp"), 45)))
            minutes = max(30, min(24 * 60, _as_int(data.get("minutes"), 240)))
            box_id = _as_int(data.get("box_id"), 0)
            c.set_drying(box_id, on, temp, minutes)
            logger.info("panel: ACE %d drying %s%s", box_id + 1, "on" if on else "off",
                        " (%d C, %d min)" % (temp, minutes) if on else "")
            with c.state.lock:
                box = next((b for b in c.state.t.get("material_boxes", [])
                            if _as_int(b.get("id"), -99) == box_id and b.get("source") == "ace"), None)
                if box is not None:   # show the change at once; the printer report confirms it
                    box["drying"] = dict(box.get("drying") or {}, active=on, status=1 if on else 0,
                                         target_temp=temp if on else 0, duration=minutes if on else 0,
                                         remain_time=minutes if on else 0)
        elif action == "unfeed_filament":
            c.unfeed_filament(_as_int(data.get("box_id"), -1), _as_int(data.get("slot"), 0))
            with c.state.lock:
                c.state.t["feed_status"] = {"box_id": _as_int(data.get("box_id"), -1), "slot_index": _as_int(data.get("slot"), 0),
                                            "type": 2, "current_status": 1, "code": 0}
        elif action == "fan":
            c.set_fan(_as_int(data.get("value"), 0))
        elif action == "temp":
            c.set_temp("nozzle" if data.get("heater", "nozzle") == "nozzle" else "bed", _as_int(data.get("value"), 0))
        elif action == "extrude":
            dist = abs(_as_float(data.get("dist"), 10.0))
            sign = 1 if data.get("dir", "extrude") == "extrude" else -1
            run_gcode_snippet(c, "; Extrude filament\nM83\nG1 E%.1f F150\n" % (sign * dist))
        elif action:
            return {"status": "error", "message": "unsupported action: " + action}
        return {"status": "ok", "ip": c.ip}

    def run_gcode(self, data: Dict[str, Any]) -> Dict[str, Any]:
        c = self._client()
        if c is None:
            return {"status": "error", "message": "Printer not connected"}
        g = str(data.get("gcode") or "")
        if not g.strip():
            return {"status": "error", "message": "Empty G-code"}
        run_gcode_snippet(c, g)
        return {"status": "ok"}

    def upload_print_file(self, data: Dict[str, Any]) -> Dict[str, Any]:
        c = self._client()
        if c is None:
            return {"status": "error", "message": "Printer not connected"}
        try:
            content = base64.b64decode(str(data.get("content_base64") or ""), validate=True)
        except (ValueError, TypeError):
            content = b""
        fname = sanitize_filename(str(data.get("filename") or ""), "print.gcode")
        if not content:
            return {"status": "error", "message": "Empty or unreadable file"}
        if len(content) > _WB_MAX_UPLOAD:
            return {"status": "error", "message": "File too large"}
        fd, tmp = _mkstemp(os.path.splitext(fname)[1] or ".gcode", "kobra_wb_")
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(content)
            fils = parse_file_filaments(tmp)
            send, send_tmp, note = prepare_upload_file(tmp, False, False, "", None, used_filaments=fils)
            if note:
                logger.info("panel: %s adjusted: %s", fname, note)
            try:
                md5, size = c.upload_file(send, fname)
            finally:
                if send_tmp:
                    try:
                        os.unlink(send)
                    except OSError:
                        pass
            remember_file_filaments(c.ip, fname, fils)
            remember_file_preview(c.ip, fname, tmp, size=_as_int(size, 0))
        finally:
            try:
                os.unlink(tmp)
            except OSError:
                pass
        if data.get("start") is False:
            logger.info("panel: %s uploaded (%d bytes) without printing", fname, size)
            return {"status": "ok", "filename": fname, "filesize": size, "started": False}
        use_ams = bool(data.get("use_ams", True))
        tasks = data.get("task_settings") or {}
        mapping = mapping_for_used(c.state.snapshot(), fils) if use_ams else []
        start = start_filename_for_print(fname)
        c.start_print(start, md5, size, use_ams and bool(mapping), mapping,
                      {"auto_leveling": bool(tasks.get("auto_leveling", 1)),
                       "vibration_compensation": bool(tasks.get("vibration_compensation", 0)),
                       "flow_calibration": bool(tasks.get("flow_calibration", 0)),
                       "timelapse": bool(tasks.get("timelapse", 0))})
        logger.info("panel: %s uploaded (%d bytes) and started as %s", fname, size, start)
        return {"status": "ok", "filename": fname, "start_filename": start, "filesize": size, "started": True}

    def sync_to_printer(self, data: Dict[str, Any]) -> Dict[str, Any]:
        c = self._client()
        if c is None:
            return {"status": "error", "message": "Printer not connected"}
        for ttype, action, payload in build_material_update_messages(data.get("slots") or []):
            c.send("web", ttype, action, payload)
            time.sleep(0.15)
        time.sleep(0.4)
        c.query_all()
        return {"status": "ok", "ip": c.ip}

    # -- HTML ------------------------------------------------------------------
    def page_html(self, http_mode: bool = False) -> str:
        """The panel page with scripts and images embedded, served to the Device (Web) tab. The page talks
        to the plugin through a window.orca-style bridge (WB_HTTP_BRIDGE) that uses the local server."""
        wdir = _workbench_dir()
        path = os.path.join(wdir, "workbench.html")
        try:
            with open(path, "r", encoding="utf-8") as f:
                html = f.read()
        except OSError as exc:
            return WB_MISSING_HTML.replace("%PATH%", path).replace("%ERR%", str(exc))

        def inline_script(m: "re.Match[str]") -> str:
            name = m.group(1)
            try:
                with open(os.path.join(wdir, *name.split("/")), "r", encoding="utf-8") as f:
                    code = f.read().replace("</script", "<\\/script")
                return "<script>\n" + code + "\n</script>"
            except OSError:
                logger.warning("panel: script %s not found", name)
                return ""

        def inline_img(m: "re.Match[str]") -> str:
            name = m.group(2)
            mime = _WB_ASSET_TYPES.get(os.path.splitext(name)[1].lower())
            if not mime:
                return m.group(0)
            try:
                with open(os.path.join(wdir, *name.split("/")), "rb") as f:
                    data = base64.b64encode(f.read()).decode("ascii")
            except OSError:
                logger.warning("panel: image %s not found", name)
                return m.group(0)
            return '%s="data:%s;base64,%s"' % (m.group(1), mime.split(";")[0], data)

        html = re.sub(r'<script src="(?!https?:)([^"]+)"></script>', inline_script, html)
        html = re.sub(r'(src)="(?!https?:|data:|#|/)([^"]+)"', inline_img, html)
        html = html.replace("http://127.0.0.1:18988", WB_API_BASE)
        head = WB_HEAD_SHIM
        if http_mode:
            head = WB_HTTP_BRIDGE.replace("%TOKEN%", self.token) + head
        html = html.replace("<head>", "<head>" + head, 1) if "<head>" in html else head + html
        idx = html.rfind("</body>")
        return html[:idx] + WB_TAIL_SHIM + html[idx:] if idx >= 0 else html + WB_TAIL_SHIM

    # -- server -----------------------------------------------------------------
    def _start(self, port: int) -> None:
        import http.server
        import socketserver
        wb = self

        class H(http.server.BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"

            def log_message(self, *a: Any) -> None:
                pass

            def _host_ok(self) -> bool:   # against DNS rebinding
                host = (self.headers.get("Host") or "").lower()
                return host in ("127.0.0.1:%d" % wb.port, "localhost:%d" % wb.port)

            def _authorized(self) -> bool:
                if self.headers.get("X-Kobra-Token", "") == wb.token:
                    return True
                q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                return q.get("k", [""])[0] == wb.token

            def _cors(self) -> None:
                # No CORS: only the page itself (same origin) uses the API; sites open in a
                # browser cannot read the replies or send the header with the key.
                pass

            def _json(self, obj: Any, code: int = 200) -> None:
                b = json.dumps(obj).encode("utf-8")
                self.send_response(code)
                self._cors()
                self.send_header("Content-Type", "application/json")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(b)))
                self.end_headers()
                self.wfile.write(b)

            def do_OPTIONS(self) -> None:  # noqa: N802
                self.send_error(403)

            def do_GET(self) -> None:  # noqa: N802
                path = urllib.parse.urlparse(self.path).path
                try:
                    if not self._host_ok():
                        return self.send_error(403)
                    if path == "/health":
                        return self._json({"status": "ok"})
                    if path.startswith("/wb/"):
                        return self._asset(path[4:])
                    if path in ("/", "/panel", "/index.html"):
                        q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                        ip = _host_only(q.get("printer", [""])[0])
                        try:
                            # without ?printer=: uses the IP (print_host) of the printer preset selected in OrcaSlicer
                            run_on_main(lambda: wb.select_from_preset(ip or wb.preset_host(), q.get("name", [""])[0]), 15.0)
                        except Exception as exc:  # noqa: BLE001
                            logger.warning("panel: could not select the preset printer (%s)", exc)
                        b = wb.page_html(http_mode=True).encode("utf-8")
                        self.send_response(200)
                        self.send_header("Content-Type", "text/html; charset=utf-8")
                        self.send_header("Cache-Control", "no-store")
                        self.send_header("X-Frame-Options", "DENY")
                        self.send_header("Content-Length", str(len(b)))
                        self.end_headers()
                        self.wfile.write(b)
                        return
                    if not self._authorized():
                        return self._json({"error": "forbidden"}, 403)
                    if path == "/camera.flv":
                        return wb.stream_camera(self)
                    code, obj = wb.handle("GET", path, {})
                    return self._json(obj, code)
                except (BrokenPipeError, ConnectionError):
                    pass
                except Exception as exc:  # noqa: BLE001
                    logger.exception("panel: error in GET %s", path)
                    try:
                        self._json({"status": "error", "message": str(exc)}, 500)
                    except OSError:
                        pass

            def _asset(self, rel: str) -> None:
                rel = urllib.parse.unquote(rel).replace("\\", "/")
                parts = [p for p in rel.split("/") if p]
                ext = os.path.splitext(rel)[1].lower()
                if not parts or any(p in (".", "..") or ":" in p for p in parts) or ext not in _WB_ASSET_TYPES:
                    return self.send_error(404)
                full = os.path.join(_workbench_dir(), *parts)
                try:
                    with open(full, "rb") as f:
                        b = f.read()
                except OSError:
                    return self.send_error(404)
                self.send_response(200)
                self.send_header("Content-Type", _WB_ASSET_TYPES[ext])
                self.send_header("Cache-Control", "max-age=3600")
                self.send_header("Content-Length", str(len(b)))
                self.end_headers()
                self.wfile.write(b)

            def do_POST(self) -> None:  # noqa: N802
                path = urllib.parse.urlparse(self.path).path
                try:
                    if not self._host_ok():
                        return self.send_error(403)
                    if not self._authorized():
                        return self._json({"error": "forbidden"}, 403)
                    n = _as_int(self.headers.get("Content-Length"), 0)
                    if n > _WB_MAX_UPLOAD * 2:
                        return self._json({"status": "error", "message": "Request too large"}, 413)
                    raw = self.rfile.read(n) if n > 0 else b"{}"
                    try:
                        data = json.loads(raw.decode("utf-8") or "{}")
                    except ValueError:
                        data = {}
                    if not isinstance(data, dict):
                        data = {}
                    if path == "/log":
                        logger.info("panel (page): %s", str(data.get("msg"))[:500])
                        return self._json({"status": "ok"})
                    if path == "/setup":
                        if str(data.get("op") or "") == "install":
                            return self._json(run_on_main(wb.launch_setup, 30.0), 200)
                        return self._json(wb.setup_status(), 200)
                    if path == "/slicer":
                        # reads OrcaSlicer presets and may ask for a network permission: needs the main thread
                        res = run_on_main(lambda: workbench_slicer_reply(data) or {"type": "response", "code": 0}, 20.0)
                        return self._json(res, 200)
                    code, res = wb.handle("POST", path, data)
                    self._json(res, code)
                except (BrokenPipeError, ConnectionError):
                    pass
                except Exception as exc:  # noqa: BLE001
                    logger.exception("panel: error in POST %s", path)
                    try:
                        self._json({"status": "error", "message": str(exc)}, 200)
                    except OSError:
                        pass

        class S(socketserver.ThreadingMixIn, http.server.HTTPServer):
            daemon_threads = True
            allow_reuse_address = os.name != "nt"

            def server_bind(self) -> None:
                socketserver.TCPServer.server_bind(self)
                self.server_name = "127.0.0.1"
                self.server_port = self.server_address[1]

        srv = None
        for p in [port + i for i in range(0, 6)]:
            try:
                srv = S(("127.0.0.1", p), H)
                break
            except OSError:
                continue
        if srv is None:
            raise OSError("panel: no free port")
        self._server = srv
        self.port = srv.server_address[1]
        threading.Thread(target=srv.serve_forever, kwargs={"poll_interval": 0.5},
                         name="kobra-workbench-http", daemon=True).start()
        logger.info("panel: local server at %s", self.base)
        if self.port != port:
            logger.warning("panel: port %d was busy; the panel is at %s. Change the Device UI address "
                           "of the Kobra presets to that port.", port, self.base)


_WORKBENCH: List[Optional[WorkbenchServer]] = [None]
_WORKBENCH_LOCK = threading.Lock()


def saved_printer_name(ip: str) -> str:
    try:
        srv = workbench_server()
        with srv._plock:
            p = next((p for p in srv._printers if p["host"] == _host_only(ip)), None)
        return p["name"] if p else ""
    except Exception:  # noqa: BLE001
        return ""


def saved_printer_hosts() -> List[str]:
    try:
        srv = workbench_server()
        with srv._plock:
            return [p["host"] for p in srv._printers]
    except Exception:  # noqa: BLE001
        return []


def workbench_server() -> WorkbenchServer:
    with _WORKBENCH_LOCK:
        if _WORKBENCH[0] is None:
            agent = _ACTIVE_AGENT[0]
            cfg = getattr(agent, "_cfg_cache", None) or {}
            # 0.7.0: the panel is served at http://127.0.0.1:<port>/ for the Device (Web) tab
            port = _as_int(cfg.get("workbench_port"), WORKBENCH_PORT)
            try:
                _WORKBENCH[0] = WorkbenchServer(port)
            except OSError as exc:
                logger.warning("panel: local server did not start (%s)", exc)
                _WORKBENCH[0] = WorkbenchServer(None)
        return _WORKBENCH[0]


def run_on_main(fn: Callable[[], Any], timeout: float = 10.0) -> Any:
    """Runs fn on the OrcaSlicer main thread (agent queue) and waits for the result."""
    agent = _ACTIVE_AGENT[0]
    q = getattr(agent, "_queue_main", None) if agent is not None else None
    if not q or threading.current_thread() is threading.main_thread():
        return fn()
    done = threading.Event()
    box: Dict[str, Any] = {}

    def work() -> None:
        try:
            box["r"] = fn()
        except BaseException as exc:  # noqa: BLE001
            box["e"] = exc
        finally:
            done.set()
    q(work)
    if not done.wait(timeout):
        raise TimeoutError("OrcaSlicer did not answer in time")
    if "e" in box:
        raise box["e"]
    return box.get("r")


# 0.7.0 -- the page served over HTTP (Device (Web) tab) does not have the window.orca bridge of plugin
# tabs: this snippet creates one with the same interface, using fetch to the local server.
WB_HTTP_BRIDGE = r"""
<script>
(function () {
  if (window.orca && typeof window.orca.postMessage === "function") return;
  var TOKEN = "%TOKEN%", cbs = [];
  function deliver(d) { cbs.forEach(function (cb) { try { cb(d); } catch (e) {} }); }
  function post(path, body) {
    return fetch(path, { method: "POST", headers: { "Content-Type": "application/json", "X-Kobra-Token": TOKEN },
                         body: JSON.stringify(body || {}) }).then(function (r) { return r.json(); });
  }
  window.orca = {
    postMessage: function (m) {
      if (typeof m === "string") { try { m = JSON.parse(m); } catch (e) { return; } }
      if (!m || typeof m !== "object") return;
      if (m.wblog) { post("/log", { msg: m.wblog }).catch(function () {}); return; }
      if (m.wb) { post("/slicer", m.wb).then(function (rep) { if (rep && rep.type) deliver({ wb_reply: rep }); }).catch(function () {}); return; }
      if (m.wbapi) {
        var a = m.wbapi, opt = { method: a.method || "GET", headers: { "X-Kobra-Token": TOKEN } };
        if (opt.method !== "GET") { opt.headers["Content-Type"] = "application/json"; opt.body = a.body || "{}"; }
        fetch(a.path, opt).then(function (r) {
          return r.text().then(function (t) { var b = null; try { b = JSON.parse(t); } catch (e) {}
            deliver({ wbapi_reply: { id: a.id, status: r.status, body: b } }); });
        }).catch(function () {
          deliver({ wbapi_reply: { id: a.id, status: 502, body: { status: "error", message: "The plugin is not responding." } } });
        });
      }
    },
    onMessage: function (cb) { cbs.push(cb); }
  };
  window.__kobraHttpMode = true;
})();
</script>
"""

WB_API_BASE = "kobra://api"

# Injected into <head>: the panel fetch() calls to the "daemon API" become messages through the
# window.orca bridge (WB_HTTP_BRIDGE, answered by the local server). Page errors go
# to the plugin log.
WB_HEAD_SHIM = r"""
<script>
(function () {
  // If localStorage is not available (blocked storage), the panel script would die while loading.
  // Replaces it with in-memory storage when access is denied.
  (function () {
    var ok = false;
    try { ok = !!window.localStorage; window.localStorage.getItem("x"); } catch (e) { ok = false; }
    if (ok) return;
    var data = {};
    var mem = {
      getItem: function (k) { k = String(k); return Object.prototype.hasOwnProperty.call(data, k) ? data[k] : null; },
      setItem: function (k, v) { data[String(k)] = String(v); },
      removeItem: function (k) { delete data[String(k)]; },
      clear: function () { data = {}; },
      key: function (i) { return Object.keys(data)[i] || null; },
      get length() { return Object.keys(data).length; }
    };
    try { Object.defineProperty(window, "localStorage", { value: mem, configurable: true, writable: true }); }
    catch (e) { try { window.__defineGetter__("localStorage", function () { return mem; }); } catch (e2) {} }
    try { Object.defineProperty(window, "sessionStorage", { value: mem, configurable: true, writable: true }); } catch (e) {}
  })();
  var BASE = "kobra://api", seq = 0, pending = {};
  var bridge = window.orca && typeof window.orca.postMessage === "function";
  function log(msg) { try { if (bridge) window.orca.postMessage({ wblog: String(msg) }); } catch (e) {} }
  window.__kobraLog = log;
  window.addEventListener("error", function (e) { log("JS error: " + (e.message || e) + " @" + (e.lineno || "")); });
  window.addEventListener("unhandledrejection", function (e) { log("promise: " + (e.reason && e.reason.message || e.reason)); });
  if (bridge) {
    window.orca.onMessage(function (d) {
      if (!d || !d.wbapi_reply) return;
      var r = d.wbapi_reply, p = pending[r.id];
      if (!p) return;
      delete pending[r.id]; clearTimeout(p.timer);
      p.resolve(new Response(JSON.stringify(r.body === undefined ? null : r.body),
        { status: r.status || 200, headers: { "Content-Type": "application/json" } }));
    });
  } else {
    log("window.orca bridge unavailable");
  }
  window.__kobraApi = function (method, path, body, timeoutMs) {
    return new Promise(function (resolve, reject) {
      if (!bridge) { reject(new TypeError("Orca bridge unavailable")); return; }
      var id = "k" + (++seq);
      pending[id] = { resolve: resolve, timer: setTimeout(function () {
        delete pending[id]; reject(new TypeError("timeout " + path)); }, timeoutMs || 30000) };
      window.orca.postMessage({ wbapi: { id: id, method: method, path: path, body: body || null } });
    });
  };
  var nativeFetch = window.fetch ? window.fetch.bind(window) : null;
  window.fetch = function (input, init) {
    var url = typeof input === "string" ? input : (input && input.url) || "";
    if (url.indexOf(BASE) === 0) {
      init = init || {};
      var method = (init.method || "GET").toUpperCase();
      var path = url.slice(BASE.length) || "/";
      var big = path.indexOf("/upload_print_file") === 0 || path.indexOf("/run_gcode") === 0;
      return window.__kobraApi(method, path, typeof init.body === "string" ? init.body : null, big ? 600000 : 30000);
    }
    return nativeFetch(input, init);
  };
})();
</script>
<style>
  #printer-make-active, .printer-tabs { display: none !important; }
  .printer-list { padding-top: 14px; }
  #cam-mjpeg { width: 100%; height: 100%; object-fit: contain; display: none; background: #000; }
</style>
"""

# Injected before </body>: printer list / project filaments through the bridge, and camera full screen.
WB_TAIL_SHIM = r"""
<script>
(function () {
  var log = window.__kobraLog || function () {};
  function reply(m) {
    if (!m || typeof m !== "object") return;
    if (m.command === "request_plate_filaments_to_printer") {
      window.orcacubic_filaments = (m.data && m.data.filaments) || [];
      return;
    }
    if (window.__orcacubicHandlePrinterMessage) window.__orcacubicHandlePrinterMessage(m);
  }
  var bridge = window.orca && typeof window.orca.postMessage === "function";
  if (bridge) window.orca.onMessage(function (d) { if (d && d.wb_reply) reply(d.wb_reply); });
  function toSlicer(body) { if (bridge) window.orca.postMessage({ wb: body }); }
  window.sendToSlicer = function (command, data, requestId) {
    var body = { command: command, data: data || {} };
    if (requestId) { body.id = requestId; body.sequence_id = requestId; }
    toSlicer(body);
  };
  window.syncFilamentsToSlicer = function () {
    alert("To bring the ACE filaments into the project, use OrcaSlicer's filament sync button " +
          "(Prepare tab, sync icon next to the printer).");
  };
  function pullFilaments() { toSlicer({ command: "request_plate_filaments_to_printer", data: {} }); }
  pullFilaments(); setInterval(pullFilaments, 3000);
  if (typeof requestPrinterList === "function") requestPrinterList();

  // ---- camera: the page plays the printer FLV (H.264) with flv.js through /camera.flv ----
  window.openCamFull = function () {
    var v = document.getElementById("cam-video");
    if (v && v.requestFullscreen && v.style.display !== "none") v.requestFullscreen();
  };
  log("panel loaded");
})();
</script>
"""


WB_MISSING_HTML = r"""<!doctype html><html><head><meta charset="utf-8"><style>
body{font-family:system-ui,sans-serif;padding:24px;line-height:1.5}code{background:rgba(127,127,127,.15);padding:2px 5px;border-radius:4px}
</style></head><body><h2>Kobra panel: files not found</h2>
<p>Copy the <code>kobra_workbench</code> folder from the plugin package into the plugin folder, next to
<code>anycubic_kobra_lan.py</code>, and restart OrcaSlicer.</p><p>Looked in: <code>%PATH%</code><br><small>%ERR%</small></p>
</body></html>"""


# --------------------------------------------------------------------------
# Plugin registration in OrcaSlicer
# --------------------------------------------------------------------------

# Kobra 3 Max adaptation, 2026-11-19. See NOTICE and README.md.
import base64 as _camera_b64
import uuid as _camera_uuid

# The embedded page cannot fetch the printer's HTTP-FLV directly. Pass bounded
# chunks through the same native message bridge used by the dashboard controls.
# No listening socket, cloud endpoint, or camera credential is exposed to the page.
class MaxCameraSession:
    def __init__(self, server, client):
        self.server, self.client = server, client
        self.id = _camera_uuid.uuid4().hex
        self.lock = threading.Lock()
        self.buffer = bytearray()
        self.arrival = threading.Condition(self.lock)
        self.stop = threading.Event()
        self.last_read = time.monotonic()
        self.error = ''
        self.done = False
        self.conn = None

    def close(self):
        self.stop.set()
        if self.conn:
            try:
                self.conn.close()
            except Exception:
                pass

    def run(self):
        try:
            self.client.camera(True)
            url = self.server.camera_source(self.client)
            u = urllib.parse.urlsplit(url)
            if u.scheme != 'http' or u.hostname != self.client.ip or u.username or u.password:
                raise PrinterError('Camera URL does not point to this printer')
            if self.stop.is_set():
                return
            self.conn = http.client.HTTPConnection(u.hostname, u.port or 80, timeout=8)
            self.conn.request('GET', (u.path or '/') + ('?' + u.query if u.query else ''),
                              headers={'User-Agent': USER_AGENT})
            response = self.conn.getresponse()
            if not 200 <= response.status < 300:
                with self.client.state.lock:
                    self.client.state.t['camera_url'] = ''
                raise PrinterError('Camera stream refused; try opening the camera again')
            while not self.stop.is_set():
                if time.monotonic() - self.last_read > 15:
                    break
                chunk = response.read1(65536)
                if not chunk:
                    break
                with self.lock:
                    if len(self.buffer) + len(chunk) > 2 * 1024 * 1024:
                        raise PrinterError('Camera viewer fell behind; open the camera again')
                    self.buffer.extend(chunk)
                    self.arrival.notify_all()
        except Exception as exc:
            # Never include the signed camera URL in a UI error or log.
            self.error = str(exc) if isinstance(exc, PrinterError) else 'Camera stream unavailable or timed out'
        finally:
            self.done = True
            with self.arrival:
                self.arrival.notify_all()
            self.close()

    def read(self):
        self.last_read = time.monotonic()
        with self.arrival:
            if not self.buffer and not self.done and not self.stop.is_set():
                self.arrival.wait(timeout=0.4)
            chunk = bytes(self.buffer[:524288])
            del self.buffer[:len(chunk)]
            return {'chunk': _camera_b64.b64encode(chunk).decode('ascii'),
                    'done': self.done and not self.buffer, 'error': self.error}

_MAX_CAMERA_LOCK = threading.Lock()
_MAX_CAMERA = [None]

def max_camera_api(server, path, data):
    with _MAX_CAMERA_LOCK:
        session = _MAX_CAMERA[0]
        if path == '/camera_start':
            client = server._client()
            if client is None or not client.link_up:
                return 409, {'status':'error', 'message':'Printer disconnected'}
            if session:
                session.close()
            session = MaxCameraSession(server, client)
            _MAX_CAMERA[0] = session
            if _spawn(session.run, 'kobra-max-camera') is None:
                session.close()
                return 503, {'status':'error', 'message':'Camera worker permission denied'}
            return 200, {'session':session.id}
        if not session or data.get('session') != session.id:
            return 409, {'status':'error', 'message':'Camera session expired; open the camera again'}
        if path == '/camera_close':
            session.close()
            _MAX_CAMERA[0] = None
            # Close only this viewer. Do not stop capture for Anycubic Next.
            return 200, {'status':'ok'}
        return 200, session.read()

def _max_speed_mode(self, mode):
    if mode not in (1, 2, 3):
        raise PrinterError('Choose Silent, Standard or Sport')
    snap = self.state.snapshot()
    if job_state(snap).lower() not in ('printing', 'paused', 'heating', 'busy', 'preparing', 'preheating'):
        raise PrinterError('Speed modes are available during a print')
    data = {'settings': {'print_speed_mode': mode}}
    if snap.get('max_taskid') is not None:
        data['taskid'] = str(snap['max_taskid'])
    self.send('web', 'print', 'update', data)
    # Display only telemetry-confirmed state, not an optimistic local assignment.

AnycubicClient.set_speed_mode = _max_speed_mode

def _max_light(self, on):
    self.send('web', 'light', 'control', {'type':3, 'status':int(bool(on)),
                                        'brightness':100 if on else 0})
AnycubicClient.set_light = _max_light

_max_original_ingest = PrinterState.ingest
def _max_ingest(self, ttype, payload):
    # state=done belongs to the COMMAND for getSliceParam, not the print job.
    # Real logs show this reply every ~11s, between start/printing reports.
    action = str(payload.get('action') or '')
    lifecycle = ('start','update','progress','pause','resume','stop','finish','report')
    if ttype == 'print' and (action == 'getSliceParam' or
            (action and action not in lifecycle and str(payload.get('state') or '').lower() in JOB_DONE_STATES)):
        _max_original_ingest(self, 'print_metadata', payload)
        return
    _max_original_ingest(self, ttype, payload)
    if payload.get('code', 200) not in (0, 200):
        return
    data = payload.get('data') or {}
    if not isinstance(data, dict):
        return
    with self.lock:
        project = data.get('project') if ttype == 'info' else data if ttype == 'print' else None
        if isinstance(project, dict):
            if 'taskid' in project:
                self.t['max_taskid'] = project['taskid']
            settings = project.get('settings') or {}
            mode = settings.get('print_speed_mode', project.get('print_speed_mode'))
            if mode in (1, 2, 3):
                self.t['max_speed_mode'] = mode
            if project.get('remain_time') is not None:
                self.t['max_remaining_report_time'] = time.time()
        if ttype == 'light':
            lights = data.get('lights') or [data]
            for light in lights:
                if isinstance(light, dict) and str(light.get('type')) == '3' and light.get('status') in (0, 1):
                    self.t['max_camera_light'] = light['status']
PrinterState.ingest = _max_ingest

# A generic info/query response can omit project while a print is running.
# Absence is not a completion report. Keep the job briefly for controls; after
# telemetry expires mark it unknown, but retain its last metrics for the UI.
def _max_expire_job(self, force=False):
    state = str(self.t.get('project_state') or '').lower()
    if state in JOB_DONE_STATES or state in JOB_ENDED_STATES:
        return
    if state and time.time() - _as_float(self.t.get('project_ts'), 0) > 90:
        self.t['project_state'] = None
        self.t['max_job_stale'] = True
PrinterState._end_job_if_stale = _max_expire_job

_max_original_apply_project = PrinterState._apply_project
def _max_apply_project(self, project, state):
    old_id, new_id = self.t.get('max_taskid'), project.get('taskid')
    old_name, new_name = self.t.get('job_name'), project.get('filename')
    new_job = ((old_id is not None and new_id is not None and str(old_id) != str(new_id)) or
               (old_name and new_name and old_name != new_name))
    if new_job:
        for key in ('progress', 'print_time', 'remain_time', 'curr_layer', 'total_layers'):
            self.t[key] = 0
        self.t.pop('max_remaining_report_time', None)
    _max_original_apply_project(self, project, state)
    if project or state:
        self.t['max_job_stale'] = False
PrinterState._apply_project = _max_apply_project

MATERIAL_SOURCE = ["external"]
MAX_DASHBOARD_HTML = '<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Kobra Max</title><style>\nhtml,body{margin:0!important;padding:0!important;width:100%;height:100%;overflow:hidden!important}\n#max-app{--bg:#f4f5f6;--panel:#fff;--fg:#30383c;--muted:#738087;--line:#dfe4e7;--accent:#009e92;--soft:#e7f6f3;box-sizing:border-box;height:100vh;width:100%;display:flex;flex-direction:column;background:var(--bg);color:var(--fg);font:14px/1.45 \'Segoe UI\',Arial,sans-serif;overflow:hidden}\n#max-app *{box-sizing:border-box}#max-app h1,#max-app h2,#max-app h3,#max-app p{margin:0;color:inherit;font-family:inherit}#max-app h1{font-size:18px;font-weight:600}#max-app h2{font-size:14px;font-weight:600}#max-app h3{font-size:13px;font-weight:600}#max-app small,#max-app .muted{color:var(--muted);font-size:12px}#max-app button,#max-app select,#max-app input{font:inherit;color:var(--fg);border:1px solid var(--line);border-radius:4px;background:var(--panel);padding:6px 10px;margin:0;min-height:32px}#max-app button{cursor:pointer;white-space:nowrap}#max-app button:hover{border-color:var(--accent);color:var(--accent)}#max-app button:disabled{opacity:.45;cursor:default}#max-app button.primary{background:var(--accent);border-color:var(--accent);color:white}#max-app button.danger{color:#b6403b}#max-app input[type=number]{width:76px;font-variant-numeric:tabular-nums}#max-app input:focus,#max-app select:focus{outline:2px solid #009e9240;outline-offset:1px}#max-app .header{flex:none;min-height:64px;padding:13px 24px;display:flex;align-items:center;gap:20px;border-bottom:1px solid var(--line);background:var(--panel)}#max-app .identity{display:flex;align-items:center;gap:12px;min-width:0}#max-app .printer-icon{width:32px;height:32px;color:var(--accent)}#max-app .subline{font-size:12px;color:var(--muted)}#max-app .badge{margin-left:auto;min-width:100px;text-align:center;color:var(--muted);font-size:12px;white-space:nowrap}#max-app .badge.ok{color:var(--accent)}#max-app .badge:before{content:\'\';display:inline-block;width:7px;height:7px;border-radius:50%;background:currentColor;margin-right:7px}#max-app .navigation{display:flex;align-items:center;gap:4px;margin-left:30px}#max-app .nav{border:0;background:transparent;border-radius:0;padding:9px 16px}#max-app .nav.active{color:var(--accent);box-shadow:inset 0 -2px var(--accent)}#max-app .body{flex:1;min-height:0;overflow:auto;scrollbar-gutter:stable;padding:20px 24px;overflow-anchor:none}#max-app .page{max-width:1640px;margin:auto}#max-app .page[hidden]{display:none!important}#max-app .layout{display:grid;grid-template-columns:minmax(420px,1.45fr) minmax(365px,1fr);gap:18px;align-items:start}#max-app .panel{background:var(--panel);border:1px solid var(--line);border-radius:5px;min-width:0;overflow:hidden}#max-app .panel-title{height:43px;display:flex;align-items:center;padding:0 18px;border-bottom:1px solid var(--line);gap:12px}#max-app .panel-title .muted{margin-left:auto}#max-app .panel-content{padding:18px}#max-app .job{height:292px}#max-app .job-main{display:grid;grid-template-columns:110px minmax(0,1fr);gap:22px;align-items:center;height:143px}#max-app .job-glyph{height:110px;border:1px solid var(--line);border-radius:4px;background:var(--bg);display:grid;place-items:center;color:var(--accent)}#max-app .job-glyph svg{width:64px;height:64px}#max-app #filename{height:21px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600}#max-app .job-meta{display:flex;gap:26px;margin-top:14px;font-size:12px;color:var(--muted)}#max-app .job-meta strong{display:block;font-size:20px;font-weight:500;color:var(--fg);font-variant-numeric:tabular-nums;line-height:30px;min-width:94px}#max-app #finish{height:20px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-size:12px;color:var(--muted);font-variant-numeric:tabular-nums}#max-app #layers{height:19px;margin-top:8px;font-size:12px;color:var(--muted)}#max-app .progress-line{display:flex;gap:14px;align-items:center}#max-app progress{appearance:none;width:100%;height:6px;border:0;background:var(--line);border-radius:3px;accent-color:var(--accent)}#max-app progress::-webkit-progress-bar{background:var(--line);border-radius:3px}#max-app progress::-webkit-progress-value{background:var(--accent);border-radius:3px;transition:width .4s}#max-app #percent{font-variant-numeric:tabular-nums;min-width:40px;text-align:right;font-size:12px}#max-app .actions{display:flex;gap:8px;margin-top:18px}#max-app .temperature{height:292px}#max-app .temp-row{display:grid;grid-template-columns:minmax(65px,1fr) 82px 92px 104px;align-items:center;gap:8px;height:66px;border-bottom:1px solid var(--line)}#max-app .temp-value{font-size:24px;font-weight:500;white-space:nowrap;text-align:right;font-variant-numeric:tabular-nums}#max-app .target{font-size:12px;color:var(--muted);white-space:nowrap;text-align:right}#max-app .temp-edit{display:flex;gap:4px;justify-content:flex-end}#max-app .temp-edit input{width:57px;padding:5px}#max-app .temp-edit button{padding:5px 9px}#max-app .fan-row{display:flex;align-items:center;gap:10px;height:63px}#max-app .fan-row .muted{margin-right:auto}#max-app .source-row{display:flex;align-items:center;gap:12px}#max-app .source-row select{flex:1;max-width:370px}#max-app .source-hint{height:38px;margin-top:10px;font-size:12px;color:var(--muted)}#max-app .materials{grid-column:1/-1}#max-app .material-toolbar{padding:14px 18px 0}#max-app .ace-grid{display:grid;grid-template-columns:1fr 1fr;gap:18px;padding:0 18px 18px}#max-app .ace{border:1px solid var(--line);border-radius:4px;min-height:218px;padding:14px}#max-app .ace-heading{display:flex;align-items:center;justify-content:space-between;height:22px;gap:10px}#max-app .ace-heading span{font-size:12px;color:var(--muted);font-variant-numeric:tabular-nums;white-space:nowrap}#max-app .trays{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:9px;margin:12px 0}#max-app .tray{border:1px solid var(--line);border-radius:4px;text-align:center;padding:10px 4px;height:105px;position:relative}#max-app .tray.fed{border-color:var(--accent);box-shadow:inset 0 0 0 1px var(--accent)}#max-app .tray-label{font-size:11px;color:var(--muted)}#max-app .swatch{display:block;width:23px;height:23px;margin:7px auto;border:1px solid #8a979d80;border-radius:50%}#max-app .tray-material{font-size:12px;white-space:nowrap;text-overflow:ellipsis;overflow:hidden;height:18px}#max-app .tray-feed{font-size:10px;color:var(--muted);height:15px}#max-app .ace-actions{display:flex;align-items:center;gap:8px}#max-app .ace-actions button{font-size:12px;min-height:28px;padding:4px 8px}#max-app .ace-actions span{margin-left:auto;font-size:11px;color:var(--muted)}#max-app .notice{flex:none;min-height:40px;border-top:1px solid var(--line);background:var(--panel);padding:9px 24px;font-size:12px;display:flex;gap:20px;align-items:center}#max-app #message{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1;color:var(--muted)}#max-app #printerAlert{font-size:12px;border:1px solid var(--line);border-radius:4px;min-height:42px;padding:10px 14px;margin-bottom:18px;display:flex;align-items:center;color:var(--muted);background:var(--panel)}#max-app #printerAlert.error{color:#9f342e;border-color:#e5b9b5;background:#fff5f4}#max-app .files-tools{display:flex;align-items:center;gap:10px;flex-wrap:wrap}#max-app .file-list{height:440px;overflow:auto;scrollbar-gutter:stable;margin-top:16px;border-top:1px solid var(--line)}#max-app .file{display:flex;align-items:center;gap:16px;min-height:52px;border-bottom:1px solid var(--line);padding:9px 5px}#max-app .file span{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}#max-app .file button{font-size:12px}#max-app .upload{margin-bottom:18px}#max-app .upload .panel-content p{margin-bottom:12px;font-size:12px;color:var(--muted)}#max-app #uploadFile{max-width:70%;font-size:12px}#max-app .footer-version{white-space:nowrap;color:var(--muted);font-size:11px}#max-app .waiting{opacity:.55}#max-app .nozzle-select{margin-left:auto;display:flex;align-items:center;gap:8px;font-size:12px;color:var(--muted)}\n@media(prefers-color-scheme:dark){#max-app[data-theme=system]{--bg:#262a2c;--panel:#303538;--fg:#e2e6e8;--muted:#a8b2b8;--line:#464e53;--soft:#20443f}#max-app[data-theme=system] #printerAlert.error{background:#442e2c;color:#ffc6c0;border-color:#86514a}}\n#max-app[data-theme=dark]{--bg:#262a2c;--panel:#303538;--fg:#e2e6e8;--muted:#a8b2b8;--line:#464e53;--soft:#20443f}#max-app[data-theme=dark] #printerAlert.error{background:#442e2c;color:#ffc6c0;border-color:#86514a}#max-app #theme{min-width:86px;font-size:12px}\n@media(max-width:1050px){#max-app .layout{grid-template-columns:1fr}#max-app .materials{grid-column:auto}#max-app .header{flex-wrap:wrap;gap:8px}#max-app .navigation{margin-left:0}#max-app .ace-grid{grid-template-columns:1fr 1fr}#max-app .body{padding:14px}#max-app .job,#max-app .temperature{height:292px}}\n@media(max-width:650px){#max-app .ace-grid{grid-template-columns:1fr}#max-app .job-glyph{display:none}#max-app .job-main{grid-template-columns:1fr}#max-app .temp-row{grid-template-columns:1fr 74px 82px 104px}#max-app .header{padding:10px 14px}}\n#max-app .speed-panel,#max-app .camera-panel{grid-column:1/-1}#max-app .speed-controls{display:flex;align-items:center;gap:10px;min-height:72px;padding:14px 18px}#max-app .speed-controls .muted{margin-left:auto}#max-app button.selected{color:var(--accent);border-color:var(--accent);background:var(--bg)}#max-app .camera-tools{display:flex;align-items:center;gap:8px;padding:12px 18px;min-height:58px}#max-app .camera-tools .muted{margin-left:auto}#max-app .camera-screen{height:clamp(260px,38vw,420px);background:#15191d;position:relative;display:grid;place-items:center;overflow:hidden}#max-app #cameraVideo{position:absolute!important;inset:0;display:block;width:100%!important;height:100%!important;min-width:0;min-height:0;max-width:100%;max-height:100%;object-fit:contain!important;transform:none}#max-app #cameraHint{position:absolute;left:18px;right:18px;text-align:center;color:#c8d1d6;font-size:13px;pointer-events:none}#max-app #cameraStatus{min-width:170px;white-space:nowrap}#max-app .job-with-speed{display:grid;grid-template-columns:minmax(0,1fr) 100px;height:247px}#max-app .speed-side{border-left:1px solid var(--line);padding:14px 10px;display:flex;flex-direction:column;gap:8px;min-width:0}#max-app .speed-side h3{font-size:12px;color:var(--muted)}#max-app .speed-side button{width:100%;padding:5px 3px}#max-app .speed-side span{font-size:10px;line-height:14px;height:28px;overflow:hidden}#max-app .job-main{grid-template-columns:72px minmax(0,1fr);gap:14px}#max-app .job-glyph{height:80px}#max-app .job-meta{gap:16px}#max-app .job-meta strong{min-width:74px;font-size:18px}@media(max-width:650px){#max-app .job-main{grid-template-columns:minmax(0,1fr)}#max-app .job-with-speed{grid-template-columns:minmax(0,1fr) 92px}#max-app .job .panel-content{padding:12px}#max-app .camera-tools{flex-wrap:wrap}}\n#max-app #cameraHeight{width:140px;min-height:0;padding:0;accent-color:var(--accent)}#max-app #cameraHeightValue{min-width:48px;font-size:12px;color:var(--muted)}#max-app .camera-tools{flex-wrap:wrap}#max-app .camera-screen{resize:vertical;min-height:220px;max-height:900px;overflow:hidden}#max-app .camera-tools label{font-size:12px}#max-app .tray{height:242px;padding:10px 5px}#max-app .swatch{position:relative;width:68px;height:68px;max-width:95%;margin:10px auto;border:3px solid #8a979d80;box-shadow:inset 0 0 0 5px #ffffff35}#max-app .swatch:after{content:\'\';position:absolute;width:19px;height:19px;left:50%;top:50%;transform:translate(-50%,-50%);border-radius:50%;background:var(--panel);border:1px solid #8a979d80}#max-app .tray-color-name{font-size:12px;font-weight:600;height:18px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}#max-app .tray-color-hex{font-size:10px;color:var(--muted);height:17px;font-variant-numeric:tabular-nums}#max-app .tray-origin{font-size:10px;color:var(--muted);height:16px}#max-app .tray button{font-size:11px;padding:4px 5px;min-height:27px;margin-top:5px}#max-app dialog{background:var(--panel);color:var(--fg);border:1px solid var(--line);border-radius:6px;width:370px;padding:22px;max-width:90vw}#max-app dialog::backdrop{background:#0007}#max-app .color-form{display:flex;gap:12px;align-items:center;margin:18px 0}#max-app #slotColorPicker{height:48px;width:65px;padding:3px}#max-app #slotColorHex{width:120px}#max-app .color-dialog-actions{display:flex;justify-content:flex-end;gap:10px}#max-app #colorEditNote{min-height:44px;font-size:12px;color:var(--muted);margin-top:10px}\n</style></head><body><div id="max-app" data-theme="light">\n<header class="header"><div class="identity"><div class="printer-icon"><svg viewBox="0 0 64 64" fill="none" stroke="currentColor" stroke-width="2.5"><path d="M12 51V12h40v39M9 51h46v7H9zM18 18h28M32 18v14m-6 0h12v9H26zM20 49h24M29 41l3 4 3-4"/></svg></div><div><h1>Kobra 3 Max</h1><div class="subline"><span id="ip">192.168.0.37</span> · Firmware <span id="firmware">—</span></div></div></div><nav class="navigation"><button class="nav active" data-page="statusPage">Status</button><button class="nav" data-page="filesPage">Printer files</button></nav><span id="connection" class="badge">Connecting</span><select id="theme" aria-label="Interface theme"><option value="light">Light</option><option value="dark">Dark</option><option value="system">System</option></select></header>\n<main class="body"><div class="page" id="statusPage"><div id="printerAlert" role="status">Waiting for a live printer report.</div><div class="layout">\n<section class="panel job"><div class="panel-title"><h2>Printing progress</h2><span class="muted" id="state">Connecting</span></div><div class="job-with-speed"><div class="panel-content"><div class="job-main"><div class="job-glyph"><svg viewBox="0 0 64 64" fill="none" stroke="currentColor" stroke-width="2.5"><path d="M12 51V12h40v39M9 51h46v7H9zM18 18h28M32 18v14m-6 0h12v9H26zM20 49h24M29 41l3 4 3-4"/></svg></div><div><div id="filename">Waiting for printer</div><div class="job-meta"><div>Remaining<strong id="eta">—</strong></div><div>Elapsed<strong id="elapsed">—</strong></div></div><p id="layers">—</p><p id="finish">Estimated finish: —</p></div></div><div class="progress-line"><progress id="progress" max="100" value="0"></progress><span id="percent">0%</span></div><div class="actions"><button data-action="pause">Pause</button><button data-action="resume">Resume</button><button data-action="stop" class="danger">Cancel print</button></div></div><aside class="speed-side" aria-label="Print speed"><h3>Speed</h3><button data-speed="2">Standard</button><button data-speed="3">Sport</button><button data-speed="1">Silent</button><span id="speedLive" class="muted">Waiting for report</span></aside></div></section>\n<section class="panel temperature"><div class="panel-title"><h2>Temperature & fan</h2><span class="muted">Live readings</span></div><div class="panel-content" style="padding-top:3px"><div class="temp-row"><span>Nozzle</span><span id="nozzle" class="temp-value">—</span><span id="nozzleTarget" class="target">Target —</span><div class="temp-edit"><input id="setNozzle" aria-label="Nozzle target temperature" type="number" min="0" max="300" value="0"><button id="applyNozzle">Set</button></div></div><div class="temp-row"><span>Bed</span><span id="bed" class="temp-value">—</span><span id="bedTarget" class="target">Target —</span><div class="temp-edit"><input id="setBed" aria-label="Bed target temperature" type="number" min="0" max="90" value="0"><button id="applyBed">Set</button></div></div><div class="fan-row"><span>Part fan</span><span class="muted" id="fanLive">—</span><input id="setFan" aria-label="Fan speed percent" type="number" min="0" max="100" value="0"><span class="muted">%</span><button id="applyFan">Set</button></div><small>Targets stay editable while live readings update.</small></div></section>\n\n<section class="panel camera-panel"><div class="panel-title"><h2>Camera</h2><span id="cameraStatus" class="muted" role="status">Viewer closed</span></div><div class="camera-screen" id="cameraScreen"><video id="cameraVideo" muted autoplay playsinline controls aria-label="Printer camera"></video><span id="cameraHint">Open camera to view the printer’s live feed.</span></div><div class="camera-tools"><button id="openCamera">Open camera</button><button id="closeCamera" disabled>Close viewer</button><label for="cameraHeight">Height</label><input id="cameraHeight" aria-label="Camera panel height" type="range" min="220" max="900" step="10" value="420"><output id="cameraHeightValue">420 px</output><span>Camera light</span><button id="lightOn">On</button><button id="lightOff">Off</button><span id="lightLive" class="muted">State unknown</span></div></section>\n<section class="panel materials"><div class="panel-title"><h2>Filament system</h2><span class="muted">Assigned materials · 2 ACE Pro units</span></div><div class="material-toolbar"><div class="source-row"><span>Feed source</span><select id="source" aria-label="Filament source"><option value="external">External spool</option><option value="ace">ACE Pro — mapped slots</option></select></div><div id="sourceNote" class="source-hint">External spool mode requires a firmware-supported physical feed configuration.</div></div><div id="boxes" class="ace-grid"></div></section>\n</div></div>\n<div class="page" id="filesPage" hidden><section class="panel upload"><div class="panel-title"><h2>Upload sliced file</h2><span class="muted">Upload only</span></div><div class="panel-content"><p>Export .gcode or .gcode.3mf from your working Max profile. Upload and print start are separate actions.</p><div class="files-tools"><input id="uploadFile" type="file" aria-label="Sliced print file" accept=".gcode,.3mf"><button id="upload" class="primary">Upload only</button></div></div></section><section class="panel"><div class="panel-title"><h2>Printer files</h2><span class="muted">Internal memory & USB</span></div><div class="panel-content"><div class="files-tools"><select id="storage" aria-label="Printer storage"><option value="local">Internal storage</option><option value="udisk">USB drive</option></select><button id="refreshFiles">Refresh</button><small>ACE jobs use Orca’s print dialog for slot mapping.</small></div><div id="files" class="file-list">Refresh to list files.</div></div></section></div></main>\n<dialog id="slotColorDialog"><h2 id="slotColorTitle">Edit spool color</h2><p class="muted">Send this color to the printer’s manual filament assignment.</p><div class="color-form"><input id="slotColorPicker" type="color" aria-label="Spool color"><input id="slotColorHex" aria-label="Spool color hex" maxlength="7"><span id="slotColorName"></span></div><p id="colorEditNote" role="status">Material type stays unchanged. Autodetected slots are protected.</p><div class="color-dialog-actions"><button id="cancelSlotColor">Cancel</button><button id="saveSlotColor" class="primary">Save to printer</button></div></dialog><footer class="notice"><span id="message" role="status">Connected controls are ready when the printer reports its state.</span><span class="footer-version">Kobra Max LAN · 0.1.6</span></footer></div><script>!function(e,t){"object"==typeof exports&&"object"==typeof module?module.exports=t():"function"==typeof define&&define.amd?define([],t):"object"==typeof exports?exports.flvjs=t():e.flvjs=t()}(self,(function(){return function(){var e={264:function(e,t,i){\n/*!\n * @overview es6-promise - a tiny implementation of Promises/A+.\n * @copyright Copyright (c) 2014 Yehuda Katz, Tom Dale, Stefan Penner and contributors (Conversion to ES6 API by Jake Archibald)\n * @license   Licensed under MIT license\n *            See https://raw.githubusercontent.com/stefanpenner/es6-promise/master/LICENSE\n * @version   v4.2.8+1e68dce6\n */\ne.exports=function(){"use strict";function e(e){var t=typeof e;return null!==e&&("object"===t||"function"===t)}function t(e){return"function"==typeof e}var n=Array.isArray?Array.isArray:function(e){return"[object Array]"===Object.prototype.toString.call(e)},r=0,s=void 0,o=void 0,a=function(e,t){b[r]=e,b[r+1]=t,2===(r+=2)&&(o?o(E):A())};function h(e){o=e}function u(e){a=e}var l="undefined"!=typeof window?window:void 0,d=l||{},c=d.MutationObserver||d.WebKitMutationObserver,f="undefined"==typeof self&&"undefined"!=typeof process&&"[object process]"==={}.toString.call(process),_="undefined"!=typeof Uint8ClampedArray&&"undefined"!=typeof importScripts&&"undefined"!=typeof MessageChannel;function p(){return function(){return process.nextTick(E)}}function m(){return void 0!==s?function(){s(E)}:y()}function g(){var e=0,t=new c(E),i=document.createTextNode("");return t.observe(i,{characterData:!0}),function(){i.data=e=++e%2}}function v(){var e=new MessageChannel;return e.port1.onmessage=E,function(){return e.port2.postMessage(0)}}function y(){var e=setTimeout;return function(){return e(E,1)}}var b=new Array(1e3);function E(){for(var e=0;e<r;e+=2)(0,b[e])(b[e+1]),b[e]=void 0,b[e+1]=void 0;r=0}function S(){try{var e=Function("return this")().require("vertx");return s=e.runOnLoop||e.runOnContext,m()}catch(e){return y()}}var A=void 0;function L(e,t){var i=this,n=new this.constructor(O);void 0===n[w]&&W(n);var r=i._state;if(r){var s=arguments[r-1];a((function(){return V(r,n,s,i._result)}))}else G(i,n,e,t);return n}function R(e){var t=this;if(e&&"object"==typeof e&&e.constructor===t)return e;var i=new t(O);return U(i,e),i}A=f?p():c?g():_?v():void 0===l?S():y();var w=Math.random().toString(36).substring(2);function O(){}var T=void 0,C=1,k=2;function D(){return new TypeError("You cannot resolve a promise with itself")}function I(){return new TypeError("A promises callback cannot return that same promise.")}function M(e,t,i,n){try{e.call(t,i,n)}catch(e){return e}}function B(e,t,i){a((function(e){var n=!1,r=M(i,t,(function(i){n||(n=!0,t!==i?U(e,i):Z(e,i))}),(function(t){n||(n=!0,F(e,t))}),"Settle: "+(e._label||" unknown promise"));!n&&r&&(n=!0,F(e,r))}),e)}function x(e,t){t._state===C?Z(e,t._result):t._state===k?F(e,t._result):G(t,void 0,(function(t){return U(e,t)}),(function(t){return F(e,t)}))}function P(e,i,n){i.constructor===e.constructor&&n===L&&i.constructor.resolve===R?x(e,i):void 0===n?Z(e,i):t(n)?B(e,i,n):Z(e,i)}function U(t,i){if(t===i)F(t,D());else if(e(i)){var n=void 0;try{n=i.then}catch(e){return void F(t,e)}P(t,i,n)}else Z(t,i)}function N(e){e._onerror&&e._onerror(e._result),j(e)}function Z(e,t){e._state===T&&(e._result=t,e._state=C,0!==e._subscribers.length&&a(j,e))}function F(e,t){e._state===T&&(e._state=k,e._result=t,a(N,e))}function G(e,t,i,n){var r=e._subscribers,s=r.length;e._onerror=null,r[s]=t,r[s+C]=i,r[s+k]=n,0===s&&e._state&&a(j,e)}function j(e){var t=e._subscribers,i=e._state;if(0!==t.length){for(var n=void 0,r=void 0,s=e._result,o=0;o<t.length;o+=3)n=t[o],r=t[o+i],n?V(i,n,r,s):r(s);e._subscribers.length=0}}function V(e,i,n,r){var s=t(n),o=void 0,a=void 0,h=!0;if(s){try{o=n(r)}catch(e){h=!1,a=e}if(i===o)return void F(i,I())}else o=r;i._state!==T||(s&&h?U(i,o):!1===h?F(i,a):e===C?Z(i,o):e===k&&F(i,o))}function z(e,t){try{t((function(t){U(e,t)}),(function(t){F(e,t)}))}catch(t){F(e,t)}}var K=0;function H(){return K++}function W(e){e[w]=K++,e._state=void 0,e._result=void 0,e._subscribers=[]}function q(){return new Error("Array Methods must be provided an Array")}var Y=function(){function e(e,t){this._instanceConstructor=e,this.promise=new e(O),this.promise[w]||W(this.promise),n(t)?(this.length=t.length,this._remaining=t.length,this._result=new Array(this.length),0===this.length?Z(this.promise,this._result):(this.length=this.length||0,this._enumerate(t),0===this._remaining&&Z(this.promise,this._result))):F(this.promise,q())}return e.prototype._enumerate=function(e){for(var t=0;this._state===T&&t<e.length;t++)this._eachEntry(e[t],t)},e.prototype._eachEntry=function(e,t){var i=this._instanceConstructor,n=i.resolve;if(n===R){var r=void 0,s=void 0,o=!1;try{r=e.then}catch(e){o=!0,s=e}if(r===L&&e._state!==T)this._settledAt(e._state,t,e._result);else if("function"!=typeof r)this._remaining--,this._result[t]=e;else if(i===te){var a=new i(O);o?F(a,s):P(a,e,r),this._willSettleAt(a,t)}else this._willSettleAt(new i((function(t){return t(e)})),t)}else this._willSettleAt(n(e),t)},e.prototype._settledAt=function(e,t,i){var n=this.promise;n._state===T&&(this._remaining--,e===k?F(n,i):this._result[t]=i),0===this._remaining&&Z(n,this._result)},e.prototype._willSettleAt=function(e,t){var i=this;G(e,void 0,(function(e){return i._settledAt(C,t,e)}),(function(e){return i._settledAt(k,t,e)}))},e}();function X(e){return new Y(this,e).promise}function J(e){var t=this;return n(e)?new t((function(i,n){for(var r=e.length,s=0;s<r;s++)t.resolve(e[s]).then(i,n)})):new t((function(e,t){return t(new TypeError("You must pass an array to race."))}))}function Q(e){var t=new this(O);return F(t,e),t}function $(){throw new TypeError("You must pass a resolver function as the first argument to the promise constructor")}function ee(){throw new TypeError("Failed to construct \'Promise\': Please use the \'new\' operator, this object constructor cannot be called as a function.")}var te=function(){function e(t){this[w]=H(),this._result=this._state=void 0,this._subscribers=[],O!==t&&("function"!=typeof t&&$(),this instanceof e?z(this,t):ee())}return e.prototype.catch=function(e){return this.then(null,e)},e.prototype.finally=function(e){var i=this,n=i.constructor;return t(e)?i.then((function(t){return n.resolve(e()).then((function(){return t}))}),(function(t){return n.resolve(e()).then((function(){throw t}))})):i.then(e,e)},e}();function ie(){var e=void 0;if(void 0!==i.g)e=i.g;else if("undefined"!=typeof self)e=self;else try{e=Function("return this")()}catch(e){throw new Error("polyfill failed because global object is unavailable in this environment")}var t=e.Promise;if(t){var n=null;try{n=Object.prototype.toString.call(t.resolve())}catch(e){}if("[object Promise]"===n&&!t.cast)return}e.Promise=te}return te.prototype.then=L,te.all=X,te.race=J,te.resolve=R,te.reject=Q,te._setScheduler=h,te._setAsap=u,te._asap=a,te.polyfill=ie,te.Promise=te,te}()},716:function(e){"use strict";var t,i="object"==typeof Reflect?Reflect:null,n=i&&"function"==typeof i.apply?i.apply:function(e,t,i){return Function.prototype.apply.call(e,t,i)};t=i&&"function"==typeof i.ownKeys?i.ownKeys:Object.getOwnPropertySymbols?function(e){return Object.getOwnPropertyNames(e).concat(Object.getOwnPropertySymbols(e))}:function(e){return Object.getOwnPropertyNames(e)};var r=Number.isNaN||function(e){return e!=e};function s(){s.init.call(this)}e.exports=s,e.exports.once=function(e,t){return new Promise((function(i,n){function r(i){e.removeListener(t,s),n(i)}function s(){"function"==typeof e.removeListener&&e.removeListener("error",r),i([].slice.call(arguments))}p(e,t,s,{once:!0}),"error"!==t&&function(e,t,i){"function"==typeof e.on&&p(e,"error",t,i)}(e,r,{once:!0})}))},s.EventEmitter=s,s.prototype._events=void 0,s.prototype._eventsCount=0,s.prototype._maxListeners=void 0;var o=10;function a(e){if("function"!=typeof e)throw new TypeError(\'The "listener" argument must be of type Function. Received type \'+typeof e)}function h(e){return void 0===e._maxListeners?s.defaultMaxListeners:e._maxListeners}function u(e,t,i,n){var r,s,o,u;if(a(i),void 0===(s=e._events)?(s=e._events=Object.create(null),e._eventsCount=0):(void 0!==s.newListener&&(e.emit("newListener",t,i.listener?i.listener:i),s=e._events),o=s[t]),void 0===o)o=s[t]=i,++e._eventsCount;else if("function"==typeof o?o=s[t]=n?[i,o]:[o,i]:n?o.unshift(i):o.push(i),(r=h(e))>0&&o.length>r&&!o.warned){o.warned=!0;var l=new Error("Possible EventEmitter memory leak detected. "+o.length+" "+String(t)+" listeners added. Use emitter.setMaxListeners() to increase limit");l.name="MaxListenersExceededWarning",l.emitter=e,l.type=t,l.count=o.length,u=l,console&&console.warn&&console.warn(u)}return e}function l(){if(!this.fired)return this.target.removeListener(this.type,this.wrapFn),this.fired=!0,0===arguments.length?this.listener.call(this.target):this.listener.apply(this.target,arguments)}function d(e,t,i){var n={fired:!1,wrapFn:void 0,target:e,type:t,listener:i},r=l.bind(n);return r.listener=i,n.wrapFn=r,r}function c(e,t,i){var n=e._events;if(void 0===n)return[];var r=n[t];return void 0===r?[]:"function"==typeof r?i?[r.listener||r]:[r]:i?function(e){for(var t=new Array(e.length),i=0;i<t.length;++i)t[i]=e[i].listener||e[i];return t}(r):_(r,r.length)}function f(e){var t=this._events;if(void 0!==t){var i=t[e];if("function"==typeof i)return 1;if(void 0!==i)return i.length}return 0}function _(e,t){for(var i=new Array(t),n=0;n<t;++n)i[n]=e[n];return i}function p(e,t,i,n){if("function"==typeof e.on)n.once?e.once(t,i):e.on(t,i);else{if("function"!=typeof e.addEventListener)throw new TypeError(\'The "emitter" argument must be of type EventEmitter. Received type \'+typeof e);e.addEventListener(t,(function r(s){n.once&&e.removeEventListener(t,r),i(s)}))}}Object.defineProperty(s,"defaultMaxListeners",{enumerable:!0,get:function(){return o},set:function(e){if("number"!=typeof e||e<0||r(e))throw new RangeError(\'The value of "defaultMaxListeners" is out of range. It must be a non-negative number. Received \'+e+".");o=e}}),s.init=function(){void 0!==this._events&&this._events!==Object.getPrototypeOf(this)._events||(this._events=Object.create(null),this._eventsCount=0),this._maxListeners=this._maxListeners||void 0},s.prototype.setMaxListeners=function(e){if("number"!=typeof e||e<0||r(e))throw new RangeError(\'The value of "n" is out of range. It must be a non-negative number. Received \'+e+".");return this._maxListeners=e,this},s.prototype.getMaxListeners=function(){return h(this)},s.prototype.emit=function(e){for(var t=[],i=1;i<arguments.length;i++)t.push(arguments[i]);var r="error"===e,s=this._events;if(void 0!==s)r=r&&void 0===s.error;else if(!r)return!1;if(r){var o;if(t.length>0&&(o=t[0]),o instanceof Error)throw o;var a=new Error("Unhandled error."+(o?" ("+o.message+")":""));throw a.context=o,a}var h=s[e];if(void 0===h)return!1;if("function"==typeof h)n(h,this,t);else{var u=h.length,l=_(h,u);for(i=0;i<u;++i)n(l[i],this,t)}return!0},s.prototype.addListener=function(e,t){return u(this,e,t,!1)},s.prototype.on=s.prototype.addListener,s.prototype.prependListener=function(e,t){return u(this,e,t,!0)},s.prototype.once=function(e,t){return a(t),this.on(e,d(this,e,t)),this},s.prototype.prependOnceListener=function(e,t){return a(t),this.prependListener(e,d(this,e,t)),this},s.prototype.removeListener=function(e,t){var i,n,r,s,o;if(a(t),void 0===(n=this._events))return this;if(void 0===(i=n[e]))return this;if(i===t||i.listener===t)0==--this._eventsCount?this._events=Object.create(null):(delete n[e],n.removeListener&&this.emit("removeListener",e,i.listener||t));else if("function"!=typeof i){for(r=-1,s=i.length-1;s>=0;s--)if(i[s]===t||i[s].listener===t){o=i[s].listener,r=s;break}if(r<0)return this;0===r?i.shift():function(e,t){for(;t+1<e.length;t++)e[t]=e[t+1];e.pop()}(i,r),1===i.length&&(n[e]=i[0]),void 0!==n.removeListener&&this.emit("removeListener",e,o||t)}return this},s.prototype.off=s.prototype.removeListener,s.prototype.removeAllListeners=function(e){var t,i,n;if(void 0===(i=this._events))return this;if(void 0===i.removeListener)return 0===arguments.length?(this._events=Object.create(null),this._eventsCount=0):void 0!==i[e]&&(0==--this._eventsCount?this._events=Object.create(null):delete i[e]),this;if(0===arguments.length){var r,s=Object.keys(i);for(n=0;n<s.length;++n)"removeListener"!==(r=s[n])&&this.removeAllListeners(r);return this.removeAllListeners("removeListener"),this._events=Object.create(null),this._eventsCount=0,this}if("function"==typeof(t=i[e]))this.removeListener(e,t);else if(void 0!==t)for(n=t.length-1;n>=0;n--)this.removeListener(e,t[n]);return this},s.prototype.listeners=function(e){return c(this,e,!0)},s.prototype.rawListeners=function(e){return c(this,e,!1)},s.listenerCount=function(e,t){return"function"==typeof e.listenerCount?e.listenerCount(t):f.call(e,t)},s.prototype.listenerCount=f,s.prototype.eventNames=function(){return this._eventsCount>0?t(this._events):[]}},397:function(e,t,i){function n(e){var t={};function i(n){if(t[n])return t[n].exports;var r=t[n]={i:n,l:!1,exports:{}};return e[n].call(r.exports,r,r.exports,i),r.l=!0,r.exports}i.m=e,i.c=t,i.i=function(e){return e},i.d=function(e,t,n){i.o(e,t)||Object.defineProperty(e,t,{configurable:!1,enumerable:!0,get:n})},i.r=function(e){Object.defineProperty(e,"__esModule",{value:!0})},i.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return i.d(t,"a",t),t},i.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)},i.p="/",i.oe=function(e){throw console.error(e),e};var n=i(i.s=ENTRY_MODULE);return n.default||n}var r="[\\\\.|\\\\-|\\\\+|\\\\w|/|@]+",s="\\\\(\\\\s*(/\\\\*.*?\\\\*/)?\\\\s*.*?([\\\\.|\\\\-|\\\\+|\\\\w|/|@]+).*?\\\\)";function o(e){return(e+"").replace(/[.?*+^$[\\]\\\\(){}|-]/g,"\\\\$&")}function a(e,t,n){var a={};a[n]=[];var h=t.toString(),u=h.match(/^function\\s?\\w*\\(\\w+,\\s*\\w+,\\s*(\\w+)\\)/);if(!u)return a;for(var l,d=u[1],c=new RegExp("(\\\\\\\\n|\\\\W)"+o(d)+s,"g");l=c.exec(h);)"dll-reference"!==l[3]&&a[n].push(l[3]);for(c=new RegExp("\\\\("+o(d)+\'\\\\("(dll-reference\\\\s(\'+r+\'))"\\\\)\\\\)\'+s,"g");l=c.exec(h);)e[l[2]]||(a[n].push(l[1]),e[l[2]]=i(l[1]).m),a[l[2]]=a[l[2]]||[],a[l[2]].push(l[4]);for(var f,_=Object.keys(a),p=0;p<_.length;p++)for(var m=0;m<a[_[p]].length;m++)f=a[_[p]][m],isNaN(1*f)||(a[_[p]][m]=1*a[_[p]][m]);return a}function h(e){return Object.keys(e).reduce((function(t,i){return t||e[i].length>0}),!1)}e.exports=function(e,t){t=t||{};var r={main:i.m},s=t.all?{main:Object.keys(r.main)}:function(e,t){for(var i={main:[t]},n={main:[]},r={main:{}};h(i);)for(var s=Object.keys(i),o=0;o<s.length;o++){var u=s[o],l=i[u].pop();if(r[u]=r[u]||{},!r[u][l]&&e[u][l]){r[u][l]=!0,n[u]=n[u]||[],n[u].push(l);for(var d=a(e,e[u][l],u),c=Object.keys(d),f=0;f<c.length;f++)i[c[f]]=i[c[f]]||[],i[c[f]]=i[c[f]].concat(d[c[f]])}}return n}(r,e),o="";Object.keys(s).filter((function(e){return"main"!==e})).forEach((function(e){for(var t=0;s[e][t];)t++;s[e].push(t),r[e][t]="(function(module, exports, __webpack_require__) { module.exports = __webpack_require__; })",o=o+"var "+e+" = ("+n.toString().replace("ENTRY_MODULE",JSON.stringify(t))+")({"+s[e].map((function(t){return JSON.stringify(t)+": "+r[e][t].toString()})).join(",")+"});\\n"})),o=o+"new (("+n.toString().replace("ENTRY_MODULE",JSON.stringify(e))+")({"+s.main.map((function(e){return JSON.stringify(e)+": "+r.main[e].toString()})).join(",")+"}))(self);";var u=new window.Blob([o],{type:"text/javascript"});if(t.bare)return u;var l=(window.URL||window.webkitURL||window.mozURL||window.msURL).createObjectURL(u),d=new window.Worker(l);return d.objectURL=l,d}},118:function(e,t){"use strict";var i=function(){function e(){this.mimeType=null,this.duration=null,this.hasAudio=null,this.hasVideo=null,this.audioCodec=null,this.videoCodec=null,this.audioDataRate=null,this.videoDataRate=null,this.audioSampleRate=null,this.audioChannelCount=null,this.width=null,this.height=null,this.fps=null,this.profile=null,this.level=null,this.refFrames=null,this.chromaFormat=null,this.sarNum=null,this.sarDen=null,this.metadata=null,this.segments=null,this.segmentCount=null,this.hasKeyframesIndex=null,this.keyframesIndex=null}return e.prototype.isComplete=function(){var e=!1===this.hasAudio||!0===this.hasAudio&&null!=this.audioCodec&&null!=this.audioSampleRate&&null!=this.audioChannelCount,t=!1===this.hasVideo||!0===this.hasVideo&&null!=this.videoCodec&&null!=this.width&&null!=this.height&&null!=this.fps&&null!=this.profile&&null!=this.level&&null!=this.refFrames&&null!=this.chromaFormat&&null!=this.sarNum&&null!=this.sarDen;return null!=this.mimeType&&null!=this.duration&&null!=this.metadata&&null!=this.hasKeyframesIndex&&e&&t},e.prototype.isSeekable=function(){return!0===this.hasKeyframesIndex},e.prototype.getNearestKeyframe=function(e){if(null==this.keyframesIndex)return null;var t=this.keyframesIndex,i=this._search(t.times,e);return{index:i,milliseconds:t.times[i],fileposition:t.filepositions[i]}},e.prototype._search=function(e,t){var i=0,n=e.length-1,r=0,s=0,o=n;for(t<e[0]&&(i=0,s=o+1);s<=o;){if((r=s+Math.floor((o-s)/2))===n||t>=e[r]&&t<e[r+1]){i=r;break}e[r]<t?s=r+1:o=r-1}return i},e}();t.Z=i},51:function(e,t,i){"use strict";i.d(t,{Wk:function(){return n},Yy:function(){return r},Vn:function(){return s},J1:function(){return o}});var n=function(e,t,i,n,r){this.dts=e,this.pts=t,this.duration=i,this.originalDts=n,this.isSyncPoint=r,this.fileposition=null},r=function(){function e(){this.beginDts=0,this.endDts=0,this.beginPts=0,this.endPts=0,this.originalBeginDts=0,this.originalEndDts=0,this.syncPoints=[],this.firstSample=null,this.lastSample=null}return e.prototype.appendSyncPoint=function(e){e.isSyncPoint=!0,this.syncPoints.push(e)},e}(),s=function(){function e(){this._list=[]}return e.prototype.clear=function(){this._list=[]},e.prototype.appendArray=function(e){var t=this._list;0!==e.length&&(t.length>0&&e[0].originalDts<t[t.length-1].originalDts&&this.clear(),Array.prototype.push.apply(t,e))},e.prototype.getLastSyncPointBeforeDts=function(e){if(0==this._list.length)return null;var t=this._list,i=0,n=t.length-1,r=0,s=0,o=n;for(e<t[0].dts&&(i=0,s=o+1);s<=o;){if((r=s+Math.floor((o-s)/2))===n||e>=t[r].dts&&e<t[r+1].dts){i=r;break}t[r].dts<e?s=r+1:o=r-1}return this._list[i]},e}(),o=function(){function e(e){this._type=e,this._list=[],this._lastAppendLocation=-1}return Object.defineProperty(e.prototype,"type",{get:function(){return this._type},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"length",{get:function(){return this._list.length},enumerable:!1,configurable:!0}),e.prototype.isEmpty=function(){return 0===this._list.length},e.prototype.clear=function(){this._list=[],this._lastAppendLocation=-1},e.prototype._searchNearestSegmentBefore=function(e){var t=this._list;if(0===t.length)return-2;var i=t.length-1,n=0,r=0,s=i,o=0;if(e<t[0].originalBeginDts)return o=-1;for(;r<=s;){if((n=r+Math.floor((s-r)/2))===i||e>t[n].lastSample.originalDts&&e<t[n+1].originalBeginDts){o=n;break}t[n].originalBeginDts<e?r=n+1:s=n-1}return o},e.prototype._searchNearestSegmentAfter=function(e){return this._searchNearestSegmentBefore(e)+1},e.prototype.append=function(e){var t=this._list,i=e,n=this._lastAppendLocation,r=0;-1!==n&&n<t.length&&i.originalBeginDts>=t[n].lastSample.originalDts&&(n===t.length-1||n<t.length-1&&i.originalBeginDts<t[n+1].originalBeginDts)?r=n+1:t.length>0&&(r=this._searchNearestSegmentBefore(i.originalBeginDts)+1),this._lastAppendLocation=r,this._list.splice(r,0,i)},e.prototype.getLastSegmentBefore=function(e){var t=this._searchNearestSegmentBefore(e);return t>=0?this._list[t]:null},e.prototype.getLastSampleBefore=function(e){var t=this.getLastSegmentBefore(e);return null!=t?t.lastSample:null},e.prototype.getLastSyncPointBefore=function(e){for(var t=this._searchNearestSegmentBefore(e),i=this._list[t].syncPoints;0===i.length&&t>0;)t--,i=this._list[t].syncPoints;return i.length>0?i[i.length-1]:null},e}()},949:function(e,t,i){"use strict";i.d(t,{Z:function(){return R}});var n=i(716),r=i.n(n),s=i(300),o=i(538),a=i(118);function h(e,t,i){var n=e;if(t+i<n.length){for(;i--;)if(128!=(192&n[++t]))return!1;return!0}return!1}var u,l=function(e){for(var t=[],i=e,n=0,r=e.length;n<r;)if(i[n]<128)t.push(String.fromCharCode(i[n])),++n;else{if(i[n]<192);else if(i[n]<224){if(h(i,n,1))if((s=(31&i[n])<<6|63&i[n+1])>=128){t.push(String.fromCharCode(65535&s)),n+=2;continue}}else if(i[n]<240){if(h(i,n,2))if((s=(15&i[n])<<12|(63&i[n+1])<<6|63&i[n+2])>=2048&&55296!=(63488&s)){t.push(String.fromCharCode(65535&s)),n+=3;continue}}else if(i[n]<248){var s;if(h(i,n,3))if((s=(7&i[n])<<18|(63&i[n+1])<<12|(63&i[n+2])<<6|63&i[n+3])>65536&&s<1114112){s-=65536,t.push(String.fromCharCode(s>>>10|55296)),t.push(String.fromCharCode(1023&s|56320)),n+=4;continue}}t.push(String.fromCharCode(65533)),++n}return t.join("")},d=i(29),c=(u=new ArrayBuffer(2),new DataView(u).setInt16(0,256,!0),256===new Int16Array(u)[0]),f=function(){function e(){}return e.parseScriptData=function(t,i,n){var r={};try{var o=e.parseValue(t,i,n),a=e.parseValue(t,i+o.size,n-o.size);r[o.data]=a.data}catch(e){s.Z.e("AMF",e.toString())}return r},e.parseObject=function(t,i,n){if(n<3)throw new d.rT("Data not enough when parse ScriptDataObject");var r=e.parseString(t,i,n),s=e.parseValue(t,i+r.size,n-r.size),o=s.objectEnd;return{data:{name:r.data,value:s.data},size:r.size+s.size,objectEnd:o}},e.parseVariable=function(t,i,n){return e.parseObject(t,i,n)},e.parseString=function(e,t,i){if(i<2)throw new d.rT("Data not enough when parse String");var n=new DataView(e,t,i).getUint16(0,!c);return{data:n>0?l(new Uint8Array(e,t+2,n)):"",size:2+n}},e.parseLongString=function(e,t,i){if(i<4)throw new d.rT("Data not enough when parse LongString");var n=new DataView(e,t,i).getUint32(0,!c);return{data:n>0?l(new Uint8Array(e,t+4,n)):"",size:4+n}},e.parseDate=function(e,t,i){if(i<10)throw new d.rT("Data size invalid when parse Date");var n=new DataView(e,t,i),r=n.getFloat64(0,!c),s=n.getInt16(8,!c);return{data:new Date(r+=60*s*1e3),size:10}},e.parseValue=function(t,i,n){if(n<1)throw new d.rT("Data not enough when parse Value");var r,o=new DataView(t,i,n),a=1,h=o.getUint8(0),u=!1;try{switch(h){case 0:r=o.getFloat64(1,!c),a+=8;break;case 1:r=!!o.getUint8(1),a+=1;break;case 2:var l=e.parseString(t,i+1,n-1);r=l.data,a+=l.size;break;case 3:r={};var f=0;for(9==(16777215&o.getUint32(n-4,!c))&&(f=3);a<n-4;){var _=e.parseObject(t,i+a,n-a-f);if(_.objectEnd)break;r[_.data.name]=_.data.value,a+=_.size}if(a<=n-3)9===(16777215&o.getUint32(a-1,!c))&&(a+=3);break;case 8:r={},a+=4;f=0;for(9==(16777215&o.getUint32(n-4,!c))&&(f=3);a<n-8;){var p=e.parseVariable(t,i+a,n-a-f);if(p.objectEnd)break;r[p.data.name]=p.data.value,a+=p.size}if(a<=n-3)9===(16777215&o.getUint32(a-1,!c))&&(a+=3);break;case 9:r=void 0,a=1,u=!0;break;case 10:r=[];var m=o.getUint32(1,!c);a+=4;for(var g=0;g<m;g++){var v=e.parseValue(t,i+a,n-a);r.push(v.data),a+=v.size}break;case 11:var y=e.parseDate(t,i+1,n-1);r=y.data,a+=y.size;break;case 12:var b=e.parseString(t,i+1,n-1);r=b.data,a+=b.size;break;default:a=n,s.Z.w("AMF","Unsupported AMF value type "+h)}}catch(e){s.Z.e("AMF",e.toString())}return{data:r,size:a,objectEnd:u}},e}(),_=function(){function e(e){this.TAG="ExpGolomb",this._buffer=e,this._buffer_index=0,this._total_bytes=e.byteLength,this._total_bits=8*e.byteLength,this._current_word=0,this._current_word_bits_left=0}return e.prototype.destroy=function(){this._buffer=null},e.prototype._fillCurrentWord=function(){var e=this._total_bytes-this._buffer_index;if(e<=0)throw new d.rT("ExpGolomb: _fillCurrentWord() but no bytes available");var t=Math.min(4,e),i=new Uint8Array(4);i.set(this._buffer.subarray(this._buffer_index,this._buffer_index+t)),this._current_word=new DataView(i.buffer).getUint32(0,!1),this._buffer_index+=t,this._current_word_bits_left=8*t},e.prototype.readBits=function(e){if(e>32)throw new d.OC("ExpGolomb: readBits() bits exceeded max 32bits!");if(e<=this._current_word_bits_left){var t=this._current_word>>>32-e;return this._current_word<<=e,this._current_word_bits_left-=e,t}var i=this._current_word_bits_left?this._current_word:0;i>>>=32-this._current_word_bits_left;var n=e-this._current_word_bits_left;this._fillCurrentWord();var r=Math.min(n,this._current_word_bits_left),s=this._current_word>>>32-r;return this._current_word<<=r,this._current_word_bits_left-=r,i=i<<r|s},e.prototype.readBool=function(){return 1===this.readBits(1)},e.prototype.readByte=function(){return this.readBits(8)},e.prototype._skipLeadingZero=function(){var e;for(e=0;e<this._current_word_bits_left;e++)if(0!=(this._current_word&2147483648>>>e))return this._current_word<<=e,this._current_word_bits_left-=e,e;return this._fillCurrentWord(),e+this._skipLeadingZero()},e.prototype.readUEG=function(){var e=this._skipLeadingZero();return this.readBits(e+1)-1},e.prototype.readSEG=function(){var e=this.readUEG();return 1&e?e+1>>>1:-1*(e>>>1)},e}(),p=function(){function e(){}return e._ebsp2rbsp=function(e){for(var t=e,i=t.byteLength,n=new Uint8Array(i),r=0,s=0;s<i;s++)s>=2&&3===t[s]&&0===t[s-1]&&0===t[s-2]||(n[r]=t[s],r++);return new Uint8Array(n.buffer,0,r)},e.parseSPS=function(t){var i=e._ebsp2rbsp(t),n=new _(i);n.readByte();var r=n.readByte();n.readByte();var s=n.readByte();n.readUEG();var o=e.getProfileString(r),a=e.getLevelString(s),h=1,u=420,l=8;if((100===r||110===r||122===r||244===r||44===r||83===r||86===r||118===r||128===r||138===r||144===r)&&(3===(h=n.readUEG())&&n.readBits(1),h<=3&&(u=[0,420,422,444][h]),l=n.readUEG()+8,n.readUEG(),n.readBits(1),n.readBool()))for(var d=3!==h?8:12,c=0;c<d;c++)n.readBool()&&(c<6?e._skipScalingList(n,16):e._skipScalingList(n,64));n.readUEG();var f=n.readUEG();if(0===f)n.readUEG();else if(1===f){n.readBits(1),n.readSEG(),n.readSEG();var p=n.readUEG();for(c=0;c<p;c++)n.readSEG()}var m=n.readUEG();n.readBits(1);var g=n.readUEG(),v=n.readUEG(),y=n.readBits(1);0===y&&n.readBits(1),n.readBits(1);var b=0,E=0,S=0,A=0;n.readBool()&&(b=n.readUEG(),E=n.readUEG(),S=n.readUEG(),A=n.readUEG());var L=1,R=1,w=0,O=!0,T=0,C=0;if(n.readBool()){if(n.readBool()){var k=n.readByte();k>0&&k<16?(L=[1,12,10,16,40,24,20,32,80,18,15,64,160,4,3,2][k-1],R=[1,11,11,11,33,11,11,11,33,11,11,33,99,3,2,1][k-1]):255===k&&(L=n.readByte()<<8|n.readByte(),R=n.readByte()<<8|n.readByte())}if(n.readBool()&&n.readBool(),n.readBool()&&(n.readBits(4),n.readBool()&&n.readBits(24)),n.readBool()&&(n.readUEG(),n.readUEG()),n.readBool()){var D=n.readBits(32),I=n.readBits(32);O=n.readBool(),w=(T=I)/(C=2*D)}}var M=1;1===L&&1===R||(M=L/R);var B=0,x=0;0===h?(B=1,x=2-y):(B=3===h?1:2,x=(1===h?2:1)*(2-y));var P=16*(g+1),U=16*(v+1)*(2-y);P-=(b+E)*B,U-=(S+A)*x;var N=Math.ceil(P*M);return n.destroy(),n=null,{profile_string:o,level_string:a,bit_depth:l,ref_frames:m,chroma_format:u,chroma_format_string:e.getChromaFormatString(u),frame_rate:{fixed:O,fps:w,fps_den:C,fps_num:T},sar_ratio:{width:L,height:R},codec_size:{width:P,height:U},present_size:{width:N,height:U}}},e._skipScalingList=function(e,t){for(var i=8,n=8,r=0;r<t;r++)0!==n&&(n=(i+e.readSEG()+256)%256),i=0===n?i:n},e.getProfileString=function(e){switch(e){case 66:return"Baseline";case 77:return"Main";case 88:return"Extended";case 100:return"High";case 110:return"High10";case 122:return"High422";case 244:return"High444";default:return"Unknown"}},e.getLevelString=function(e){return(e/10).toFixed(1)},e.getChromaFormatString=function(e){switch(e){case 420:return"4:2:0";case 422:return"4:2:2";case 444:return"4:4:4";default:return"Unknown"}},e}(),m=i(600);var g=function(){function e(e,t){this.TAG="FLVDemuxer",this._config=t,this._onError=null,this._onMediaInfo=null,this._onMetaDataArrived=null,this._onScriptDataArrived=null,this._onTrackMetadata=null,this._onDataAvailable=null,this._dataOffset=e.dataOffset,this._firstParse=!0,this._dispatch=!1,this._hasAudio=e.hasAudioTrack,this._hasVideo=e.hasVideoTrack,this._hasAudioFlagOverrided=!1,this._hasVideoFlagOverrided=!1,this._audioInitialMetadataDispatched=!1,this._videoInitialMetadataDispatched=!1,this._mediaInfo=new a.Z,this._mediaInfo.hasAudio=this._hasAudio,this._mediaInfo.hasVideo=this._hasVideo,this._metadata=null,this._audioMetadata=null,this._videoMetadata=null,this._naluLengthSize=4,this._timestampBase=0,this._timescale=1e3,this._duration=0,this._durationOverrided=!1,this._referenceFrameRate={fixed:!0,fps:23.976,fps_num:23976,fps_den:1e3},this._flvSoundRateTable=[5500,11025,22050,44100,48e3],this._mpegSamplingRates=[96e3,88200,64e3,48e3,44100,32e3,24e3,22050,16e3,12e3,11025,8e3,7350],this._mpegAudioV10SampleRateTable=[44100,48e3,32e3,0],this._mpegAudioV20SampleRateTable=[22050,24e3,16e3,0],this._mpegAudioV25SampleRateTable=[11025,12e3,8e3,0],this._mpegAudioL1BitRateTable=[0,32,64,96,128,160,192,224,256,288,320,352,384,416,448,-1],this._mpegAudioL2BitRateTable=[0,32,48,56,64,80,96,112,128,160,192,224,256,320,384,-1],this._mpegAudioL3BitRateTable=[0,32,40,48,56,64,80,96,112,128,160,192,224,256,320,-1],this._videoTrack={type:"video",id:1,sequenceNumber:0,samples:[],length:0},this._audioTrack={type:"audio",id:2,sequenceNumber:0,samples:[],length:0},this._littleEndian=function(){var e=new ArrayBuffer(2);return new DataView(e).setInt16(0,256,!0),256===new Int16Array(e)[0]}()}return e.prototype.destroy=function(){this._mediaInfo=null,this._metadata=null,this._audioMetadata=null,this._videoMetadata=null,this._videoTrack=null,this._audioTrack=null,this._onError=null,this._onMediaInfo=null,this._onMetaDataArrived=null,this._onScriptDataArrived=null,this._onTrackMetadata=null,this._onDataAvailable=null},e.probe=function(e){var t=new Uint8Array(e),i={match:!1};if(70!==t[0]||76!==t[1]||86!==t[2]||1!==t[3])return i;var n,r,s=(4&t[4])>>>2!=0,o=0!=(1&t[4]),a=(n=t)[r=5]<<24|n[r+1]<<16|n[r+2]<<8|n[r+3];return a<9?i:{match:!0,consumed:a,dataOffset:a,hasAudioTrack:s,hasVideoTrack:o}},e.prototype.bindDataSource=function(e){return e.onDataArrival=this.parseChunks.bind(this),this},Object.defineProperty(e.prototype,"onTrackMetadata",{get:function(){return this._onTrackMetadata},set:function(e){this._onTrackMetadata=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onMediaInfo",{get:function(){return this._onMediaInfo},set:function(e){this._onMediaInfo=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onMetaDataArrived",{get:function(){return this._onMetaDataArrived},set:function(e){this._onMetaDataArrived=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onScriptDataArrived",{get:function(){return this._onScriptDataArrived},set:function(e){this._onScriptDataArrived=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onError",{get:function(){return this._onError},set:function(e){this._onError=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onDataAvailable",{get:function(){return this._onDataAvailable},set:function(e){this._onDataAvailable=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"timestampBase",{get:function(){return this._timestampBase},set:function(e){this._timestampBase=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"overridedDuration",{get:function(){return this._duration},set:function(e){this._durationOverrided=!0,this._duration=e,this._mediaInfo.duration=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"overridedHasAudio",{set:function(e){this._hasAudioFlagOverrided=!0,this._hasAudio=e,this._mediaInfo.hasAudio=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"overridedHasVideo",{set:function(e){this._hasVideoFlagOverrided=!0,this._hasVideo=e,this._mediaInfo.hasVideo=e},enumerable:!1,configurable:!0}),e.prototype.resetMediaInfo=function(){this._mediaInfo=new a.Z},e.prototype._isInitialMetadataDispatched=function(){return this._hasAudio&&this._hasVideo?this._audioInitialMetadataDispatched&&this._videoInitialMetadataDispatched:this._hasAudio&&!this._hasVideo?this._audioInitialMetadataDispatched:!(this._hasAudio||!this._hasVideo)&&this._videoInitialMetadataDispatched},e.prototype.parseChunks=function(t,i){if(!(this._onError&&this._onMediaInfo&&this._onTrackMetadata&&this._onDataAvailable))throw new d.rT("Flv: onError & onMediaInfo & onTrackMetadata & onDataAvailable callback must be specified");var n=0,r=this._littleEndian;if(0===i){if(!(t.byteLength>13))return 0;n=e.probe(t).dataOffset}this._firstParse&&(this._firstParse=!1,i+n!==this._dataOffset&&s.Z.w(this.TAG,"First time parsing but chunk byteStart invalid!"),0!==(o=new DataView(t,n)).getUint32(0,!r)&&s.Z.w(this.TAG,"PrevTagSize0 !== 0 !!!"),n+=4);for(;n<t.byteLength;){this._dispatch=!0;var o=new DataView(t,n);if(n+11+4>t.byteLength)break;var a=o.getUint8(0),h=16777215&o.getUint32(0,!r);if(n+11+h+4>t.byteLength)break;if(8===a||9===a||18===a){var u=o.getUint8(4),l=o.getUint8(5),c=o.getUint8(6)|l<<8|u<<16|o.getUint8(7)<<24;0!==(16777215&o.getUint32(7,!r))&&s.Z.w(this.TAG,"Meet tag which has StreamID != 0!");var f=n+11;switch(a){case 8:this._parseAudioData(t,f,h,c);break;case 9:this._parseVideoData(t,f,h,c,i+n);break;case 18:this._parseScriptData(t,f,h)}var _=o.getUint32(11+h,!r);_!==11+h&&s.Z.w(this.TAG,"Invalid PrevTagSize "+_),n+=11+h+4}else s.Z.w(this.TAG,"Unsupported tag type "+a+", skipped"),n+=11+h+4}return this._isInitialMetadataDispatched()&&this._dispatch&&(this._audioTrack.length||this._videoTrack.length)&&this._onDataAvailable(this._audioTrack,this._videoTrack),n},e.prototype._parseScriptData=function(e,t,i){var n=f.parseScriptData(e,t,i);if(n.hasOwnProperty("onMetaData")){if(null==n.onMetaData||"object"!=typeof n.onMetaData)return void s.Z.w(this.TAG,"Invalid onMetaData structure!");this._metadata&&s.Z.w(this.TAG,"Found another onMetaData tag!"),this._metadata=n;var r=this._metadata.onMetaData;if(this._onMetaDataArrived&&this._onMetaDataArrived(Object.assign({},r)),"boolean"==typeof r.hasAudio&&!1===this._hasAudioFlagOverrided&&(this._hasAudio=r.hasAudio,this._mediaInfo.hasAudio=this._hasAudio),"boolean"==typeof r.hasVideo&&!1===this._hasVideoFlagOverrided&&(this._hasVideo=r.hasVideo,this._mediaInfo.hasVideo=this._hasVideo),"number"==typeof r.audiodatarate&&(this._mediaInfo.audioDataRate=r.audiodatarate),"number"==typeof r.videodatarate&&(this._mediaInfo.videoDataRate=r.videodatarate),"number"==typeof r.width&&(this._mediaInfo.width=r.width),"number"==typeof r.height&&(this._mediaInfo.height=r.height),"number"==typeof r.duration){if(!this._durationOverrided){var o=Math.floor(r.duration*this._timescale);this._duration=o,this._mediaInfo.duration=o}}else this._mediaInfo.duration=0;if("number"==typeof r.framerate){var a=Math.floor(1e3*r.framerate);if(a>0){var h=a/1e3;this._referenceFrameRate.fixed=!0,this._referenceFrameRate.fps=h,this._referenceFrameRate.fps_num=a,this._referenceFrameRate.fps_den=1e3,this._mediaInfo.fps=h}}if("object"==typeof r.keyframes){this._mediaInfo.hasKeyframesIndex=!0;var u=r.keyframes;this._mediaInfo.keyframesIndex=this._parseKeyframesIndex(u),r.keyframes=null}else this._mediaInfo.hasKeyframesIndex=!1;this._dispatch=!1,this._mediaInfo.metadata=r,s.Z.v(this.TAG,"Parsed onMetaData"),this._mediaInfo.isComplete()&&this._onMediaInfo(this._mediaInfo)}Object.keys(n).length>0&&this._onScriptDataArrived&&this._onScriptDataArrived(Object.assign({},n))},e.prototype._parseKeyframesIndex=function(e){for(var t=[],i=[],n=1;n<e.times.length;n++){var r=this._timestampBase+Math.floor(1e3*e.times[n]);t.push(r),i.push(e.filepositions[n])}return{times:t,filepositions:i}},e.prototype._parseAudioData=function(e,t,i,n){if(i<=1)s.Z.w(this.TAG,"Flv: Invalid audio packet, missing SoundData payload!");else if(!0!==this._hasAudioFlagOverrided||!1!==this._hasAudio){this._littleEndian;var r=new DataView(e,t,i).getUint8(0),o=r>>>4;if(2===o||10===o){var a=0,h=(12&r)>>>2;if(h>=0&&h<=4){a=this._flvSoundRateTable[h];var u=1&r,l=this._audioMetadata,d=this._audioTrack;if(l||(!1===this._hasAudio&&!1===this._hasAudioFlagOverrided&&(this._hasAudio=!0,this._mediaInfo.hasAudio=!0),(l=this._audioMetadata={}).type="audio",l.id=d.id,l.timescale=this._timescale,l.duration=this._duration,l.audioSampleRate=a,l.channelCount=0===u?1:2),10===o){var c=this._parseAACAudioData(e,t+1,i-1);if(null==c)return;if(0===c.packetType){l.config&&s.Z.w(this.TAG,"Found another AudioSpecificConfig!");var f=c.data;l.audioSampleRate=f.samplingRate,l.channelCount=f.channelCount,l.codec=f.codec,l.originalCodec=f.originalCodec,l.config=f.config,l.refSampleDuration=1024/l.audioSampleRate*l.timescale,s.Z.v(this.TAG,"Parsed AudioSpecificConfig"),this._isInitialMetadataDispatched()?this._dispatch&&(this._audioTrack.length||this._videoTrack.length)&&this._onDataAvailable(this._audioTrack,this._videoTrack):this._audioInitialMetadataDispatched=!0,this._dispatch=!1,this._onTrackMetadata("audio",l),(g=this._mediaInfo).audioCodec=l.originalCodec,g.audioSampleRate=l.audioSampleRate,g.audioChannelCount=l.channelCount,g.hasVideo?null!=g.videoCodec&&(g.mimeType=\'video/x-flv; codecs="\'+g.videoCodec+","+g.audioCodec+\'"\'):g.mimeType=\'video/x-flv; codecs="\'+g.audioCodec+\'"\',g.isComplete()&&this._onMediaInfo(g)}else if(1===c.packetType){var _=this._timestampBase+n,p={unit:c.data,length:c.data.byteLength,dts:_,pts:_};d.samples.push(p),d.length+=c.data.length}else s.Z.e(this.TAG,"Flv: Unsupported AAC data type "+c.packetType)}else if(2===o){if(!l.codec){var g;if(null==(f=this._parseMP3AudioData(e,t+1,i-1,!0)))return;l.audioSampleRate=f.samplingRate,l.channelCount=f.channelCount,l.codec=f.codec,l.originalCodec=f.originalCodec,l.refSampleDuration=1152/l.audioSampleRate*l.timescale,s.Z.v(this.TAG,"Parsed MPEG Audio Frame Header"),this._audioInitialMetadataDispatched=!0,this._onTrackMetadata("audio",l),(g=this._mediaInfo).audioCodec=l.codec,g.audioSampleRate=l.audioSampleRate,g.audioChannelCount=l.channelCount,g.audioDataRate=f.bitRate,g.hasVideo?null!=g.videoCodec&&(g.mimeType=\'video/x-flv; codecs="\'+g.videoCodec+","+g.audioCodec+\'"\'):g.mimeType=\'video/x-flv; codecs="\'+g.audioCodec+\'"\',g.isComplete()&&this._onMediaInfo(g)}var v=this._parseMP3AudioData(e,t+1,i-1,!1);if(null==v)return;_=this._timestampBase+n;var y={unit:v,length:v.byteLength,dts:_,pts:_};d.samples.push(y),d.length+=v.length}}else this._onError(m.Z.FORMAT_ERROR,"Flv: Invalid audio sample rate idx: "+h)}else this._onError(m.Z.CODEC_UNSUPPORTED,"Flv: Unsupported audio codec idx: "+o)}},e.prototype._parseAACAudioData=function(e,t,i){if(!(i<=1)){var n={},r=new Uint8Array(e,t,i);return n.packetType=r[0],0===r[0]?n.data=this._parseAACAudioSpecificConfig(e,t+1,i-1):n.data=r.subarray(1),n}s.Z.w(this.TAG,"Flv: Invalid AAC packet, missing AACPacketType or/and Data!")},e.prototype._parseAACAudioSpecificConfig=function(e,t,i){var n,r,s=new Uint8Array(e,t,i),o=null,a=0,h=null;if(a=n=s[0]>>>3,(r=(7&s[0])<<1|s[1]>>>7)<0||r>=this._mpegSamplingRates.length)this._onError(m.Z.FORMAT_ERROR,"Flv: AAC invalid sampling frequency index!");else{var u=this._mpegSamplingRates[r],l=(120&s[1])>>>3;if(!(l<0||l>=8)){5===a&&(h=(7&s[1])<<1|s[2]>>>7,(124&s[2])>>>2);var d=self.navigator.userAgent.toLowerCase();return-1!==d.indexOf("firefox")?r>=6?(a=5,o=new Array(4),h=r-3):(a=2,o=new Array(2),h=r):-1!==d.indexOf("android")?(a=2,o=new Array(2),h=r):(a=5,h=r,o=new Array(4),r>=6?h=r-3:1===l&&(a=2,o=new Array(2),h=r)),o[0]=a<<3,o[0]|=(15&r)>>>1,o[1]=(15&r)<<7,o[1]|=(15&l)<<3,5===a&&(o[1]|=(15&h)>>>1,o[2]=(1&h)<<7,o[2]|=8,o[3]=0),{config:o,samplingRate:u,channelCount:l,codec:"mp4a.40."+a,originalCodec:"mp4a.40."+n}}this._onError(m.Z.FORMAT_ERROR,"Flv: AAC invalid channel configuration")}},e.prototype._parseMP3AudioData=function(e,t,i,n){if(!(i<4)){this._littleEndian;var r=new Uint8Array(e,t,i),o=null;if(n){if(255!==r[0])return;var a=r[1]>>>3&3,h=(6&r[1])>>1,u=(240&r[2])>>>4,l=(12&r[2])>>>2,d=3!==(r[3]>>>6&3)?2:1,c=0,f=0;switch(a){case 0:c=this._mpegAudioV25SampleRateTable[l];break;case 2:c=this._mpegAudioV20SampleRateTable[l];break;case 3:c=this._mpegAudioV10SampleRateTable[l]}switch(h){case 1:34,u<this._mpegAudioL3BitRateTable.length&&(f=this._mpegAudioL3BitRateTable[u]);break;case 2:33,u<this._mpegAudioL2BitRateTable.length&&(f=this._mpegAudioL2BitRateTable[u]);break;case 3:32,u<this._mpegAudioL1BitRateTable.length&&(f=this._mpegAudioL1BitRateTable[u])}o={bitRate:f,samplingRate:c,channelCount:d,codec:"mp3",originalCodec:"mp3"}}else o=r;return o}s.Z.w(this.TAG,"Flv: Invalid MP3 packet, header missing!")},e.prototype._parseVideoData=function(e,t,i,n,r){if(i<=1)s.Z.w(this.TAG,"Flv: Invalid video packet, missing VideoData payload!");else if(!0!==this._hasVideoFlagOverrided||!1!==this._hasVideo){var o=new Uint8Array(e,t,i)[0],a=(240&o)>>>4,h=15&o;7===h?this._parseAVCVideoPacket(e,t+1,i-1,n,r,a):this._onError(m.Z.CODEC_UNSUPPORTED,"Flv: Unsupported codec in video frame: "+h)}},e.prototype._parseAVCVideoPacket=function(e,t,i,n,r,o){if(i<4)s.Z.w(this.TAG,"Flv: Invalid AVC packet, missing AVCPacketType or/and CompositionTime");else{var a=this._littleEndian,h=new DataView(e,t,i),u=h.getUint8(0),l=(16777215&h.getUint32(0,!a))<<8>>8;if(0===u)this._parseAVCDecoderConfigurationRecord(e,t+4,i-4);else if(1===u)this._parseAVCVideoData(e,t+4,i-4,n,r,o,l);else if(2!==u)return void this._onError(m.Z.FORMAT_ERROR,"Flv: Invalid video packet type "+u)}},e.prototype._parseAVCDecoderConfigurationRecord=function(e,t,i){if(i<7)s.Z.w(this.TAG,"Flv: Invalid AVCDecoderConfigurationRecord, lack of data!");else{var n=this._videoMetadata,r=this._videoTrack,o=this._littleEndian,a=new DataView(e,t,i);n?void 0!==n.avcc&&s.Z.w(this.TAG,"Found another AVCDecoderConfigurationRecord!"):(!1===this._hasVideo&&!1===this._hasVideoFlagOverrided&&(this._hasVideo=!0,this._mediaInfo.hasVideo=!0),(n=this._videoMetadata={}).type="video",n.id=r.id,n.timescale=this._timescale,n.duration=this._duration);var h=a.getUint8(0),u=a.getUint8(1);a.getUint8(2),a.getUint8(3);if(1===h&&0!==u)if(this._naluLengthSize=1+(3&a.getUint8(4)),3===this._naluLengthSize||4===this._naluLengthSize){var l=31&a.getUint8(5);if(0!==l){l>1&&s.Z.w(this.TAG,"Flv: Strange AVCDecoderConfigurationRecord: SPS Count = "+l);for(var d=6,c=0;c<l;c++){var f=a.getUint16(d,!o);if(d+=2,0!==f){var _=new Uint8Array(e,t+d,f);d+=f;var g=p.parseSPS(_);if(0===c){n.codecWidth=g.codec_size.width,n.codecHeight=g.codec_size.height,n.presentWidth=g.present_size.width,n.presentHeight=g.present_size.height,n.profile=g.profile_string,n.level=g.level_string,n.bitDepth=g.bit_depth,n.chromaFormat=g.chroma_format,n.sarRatio=g.sar_ratio,n.frameRate=g.frame_rate,!1!==g.frame_rate.fixed&&0!==g.frame_rate.fps_num&&0!==g.frame_rate.fps_den||(n.frameRate=this._referenceFrameRate);var v=n.frameRate.fps_den,y=n.frameRate.fps_num;n.refSampleDuration=n.timescale*(v/y);for(var b=_.subarray(1,4),E="avc1.",S=0;S<3;S++){var A=b[S].toString(16);A.length<2&&(A="0"+A),E+=A}n.codec=E;var L=this._mediaInfo;L.width=n.codecWidth,L.height=n.codecHeight,L.fps=n.frameRate.fps,L.profile=n.profile,L.level=n.level,L.refFrames=g.ref_frames,L.chromaFormat=g.chroma_format_string,L.sarNum=n.sarRatio.width,L.sarDen=n.sarRatio.height,L.videoCodec=E,L.hasAudio?null!=L.audioCodec&&(L.mimeType=\'video/x-flv; codecs="\'+L.videoCodec+","+L.audioCodec+\'"\'):L.mimeType=\'video/x-flv; codecs="\'+L.videoCodec+\'"\',L.isComplete()&&this._onMediaInfo(L)}}}var R=a.getUint8(d);if(0!==R){R>1&&s.Z.w(this.TAG,"Flv: Strange AVCDecoderConfigurationRecord: PPS Count = "+R),d++;for(c=0;c<R;c++){f=a.getUint16(d,!o);d+=2,0!==f&&(d+=f)}n.avcc=new Uint8Array(i),n.avcc.set(new Uint8Array(e,t,i),0),s.Z.v(this.TAG,"Parsed AVCDecoderConfigurationRecord"),this._isInitialMetadataDispatched()?this._dispatch&&(this._audioTrack.length||this._videoTrack.length)&&this._onDataAvailable(this._audioTrack,this._videoTrack):this._videoInitialMetadataDispatched=!0,this._dispatch=!1,this._onTrackMetadata("video",n)}else this._onError(m.Z.FORMAT_ERROR,"Flv: Invalid AVCDecoderConfigurationRecord: No PPS")}else this._onError(m.Z.FORMAT_ERROR,"Flv: Invalid AVCDecoderConfigurationRecord: No SPS")}else this._onError(m.Z.FORMAT_ERROR,"Flv: Strange NaluLengthSizeMinusOne: "+(this._naluLengthSize-1));else this._onError(m.Z.FORMAT_ERROR,"Flv: Invalid AVCDecoderConfigurationRecord")}},e.prototype._parseAVCVideoData=function(e,t,i,n,r,o,a){for(var h=this._littleEndian,u=new DataView(e,t,i),l=[],d=0,c=0,f=this._naluLengthSize,_=this._timestampBase+n,p=1===o;c<i;){if(c+4>=i){s.Z.w(this.TAG,"Malformed Nalu near timestamp "+_+", offset = "+c+", dataSize = "+i);break}var m=u.getUint32(c,!h);if(3===f&&(m>>>=8),m>i-f)return void s.Z.w(this.TAG,"Malformed Nalus near timestamp "+_+", NaluSize > DataSize!");var g=31&u.getUint8(c+f);5===g&&(p=!0);var v=new Uint8Array(e,t+c,f+m),y={type:g,data:v};l.push(y),d+=v.byteLength,c+=f+m}if(l.length){var b=this._videoTrack,E={units:l,length:d,isKeyframe:p,dts:_,cts:a,pts:_+a};p&&(E.fileposition=r),b.samples.push(E),b.length+=d}},e}(),v=function(){function e(){}return e.init=function(){for(var t in e.types={avc1:[],avcC:[],btrt:[],dinf:[],dref:[],esds:[],ftyp:[],hdlr:[],mdat:[],mdhd:[],mdia:[],mfhd:[],minf:[],moof:[],moov:[],mp4a:[],mvex:[],mvhd:[],sdtp:[],stbl:[],stco:[],stsc:[],stsd:[],stsz:[],stts:[],tfdt:[],tfhd:[],traf:[],trak:[],trun:[],trex:[],tkhd:[],vmhd:[],smhd:[],".mp3":[]},e.types)e.types.hasOwnProperty(t)&&(e.types[t]=[t.charCodeAt(0),t.charCodeAt(1),t.charCodeAt(2),t.charCodeAt(3)]);var i=e.constants={};i.FTYP=new Uint8Array([105,115,111,109,0,0,0,1,105,115,111,109,97,118,99,49]),i.STSD_PREFIX=new Uint8Array([0,0,0,0,0,0,0,1]),i.STTS=new Uint8Array([0,0,0,0,0,0,0,0]),i.STSC=i.STCO=i.STTS,i.STSZ=new Uint8Array([0,0,0,0,0,0,0,0,0,0,0,0]),i.HDLR_VIDEO=new Uint8Array([0,0,0,0,0,0,0,0,118,105,100,101,0,0,0,0,0,0,0,0,0,0,0,0,86,105,100,101,111,72,97,110,100,108,101,114,0]),i.HDLR_AUDIO=new Uint8Array([0,0,0,0,0,0,0,0,115,111,117,110,0,0,0,0,0,0,0,0,0,0,0,0,83,111,117,110,100,72,97,110,100,108,101,114,0]),i.DREF=new Uint8Array([0,0,0,0,0,0,0,1,0,0,0,12,117,114,108,32,0,0,0,1]),i.SMHD=new Uint8Array([0,0,0,0,0,0,0,0]),i.VMHD=new Uint8Array([0,0,0,1,0,0,0,0,0,0,0,0])},e.box=function(e){for(var t=8,i=null,n=Array.prototype.slice.call(arguments,1),r=n.length,s=0;s<r;s++)t+=n[s].byteLength;(i=new Uint8Array(t))[0]=t>>>24&255,i[1]=t>>>16&255,i[2]=t>>>8&255,i[3]=255&t,i.set(e,4);var o=8;for(s=0;s<r;s++)i.set(n[s],o),o+=n[s].byteLength;return i},e.generateInitSegment=function(t){var i=e.box(e.types.ftyp,e.constants.FTYP),n=e.moov(t),r=new Uint8Array(i.byteLength+n.byteLength);return r.set(i,0),r.set(n,i.byteLength),r},e.moov=function(t){var i=e.mvhd(t.timescale,t.duration),n=e.trak(t),r=e.mvex(t);return e.box(e.types.moov,i,n,r)},e.mvhd=function(t,i){return e.box(e.types.mvhd,new Uint8Array([0,0,0,0,0,0,0,0,0,0,0,0,t>>>24&255,t>>>16&255,t>>>8&255,255&t,i>>>24&255,i>>>16&255,i>>>8&255,255&i,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,255,255,255,255]))},e.trak=function(t){return e.box(e.types.trak,e.tkhd(t),e.mdia(t))},e.tkhd=function(t){var i=t.id,n=t.duration,r=t.presentWidth,s=t.presentHeight;return e.box(e.types.tkhd,new Uint8Array([0,0,0,7,0,0,0,0,0,0,0,0,i>>>24&255,i>>>16&255,i>>>8&255,255&i,0,0,0,0,n>>>24&255,n>>>16&255,n>>>8&255,255&n,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,r>>>8&255,255&r,0,0,s>>>8&255,255&s,0,0]))},e.mdia=function(t){return e.box(e.types.mdia,e.mdhd(t),e.hdlr(t),e.minf(t))},e.mdhd=function(t){var i=t.timescale,n=t.duration;return e.box(e.types.mdhd,new Uint8Array([0,0,0,0,0,0,0,0,0,0,0,0,i>>>24&255,i>>>16&255,i>>>8&255,255&i,n>>>24&255,n>>>16&255,n>>>8&255,255&n,85,196,0,0]))},e.hdlr=function(t){var i=null;return i="audio"===t.type?e.constants.HDLR_AUDIO:e.constants.HDLR_VIDEO,e.box(e.types.hdlr,i)},e.minf=function(t){var i=null;return i="audio"===t.type?e.box(e.types.smhd,e.constants.SMHD):e.box(e.types.vmhd,e.constants.VMHD),e.box(e.types.minf,i,e.dinf(),e.stbl(t))},e.dinf=function(){return e.box(e.types.dinf,e.box(e.types.dref,e.constants.DREF))},e.stbl=function(t){return e.box(e.types.stbl,e.stsd(t),e.box(e.types.stts,e.constants.STTS),e.box(e.types.stsc,e.constants.STSC),e.box(e.types.stsz,e.constants.STSZ),e.box(e.types.stco,e.constants.STCO))},e.stsd=function(t){return"audio"===t.type?"mp3"===t.codec?e.box(e.types.stsd,e.constants.STSD_PREFIX,e.mp3(t)):e.box(e.types.stsd,e.constants.STSD_PREFIX,e.mp4a(t)):e.box(e.types.stsd,e.constants.STSD_PREFIX,e.avc1(t))},e.mp3=function(t){var i=t.channelCount,n=t.audioSampleRate,r=new Uint8Array([0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,i,0,16,0,0,0,0,n>>>8&255,255&n,0,0]);return e.box(e.types[".mp3"],r)},e.mp4a=function(t){var i=t.channelCount,n=t.audioSampleRate,r=new Uint8Array([0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,i,0,16,0,0,0,0,n>>>8&255,255&n,0,0]);return e.box(e.types.mp4a,r,e.esds(t))},e.esds=function(t){var i=t.config||[],n=i.length,r=new Uint8Array([0,0,0,0,3,23+n,0,1,0,4,15+n,64,21,0,0,0,0,0,0,0,0,0,0,0,5].concat([n]).concat(i).concat([6,1,2]));return e.box(e.types.esds,r)},e.avc1=function(t){var i=t.avcc,n=t.codecWidth,r=t.codecHeight,s=new Uint8Array([0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,n>>>8&255,255&n,r>>>8&255,255&r,0,72,0,0,0,72,0,0,0,0,0,0,0,1,10,120,113,113,47,102,108,118,46,106,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,255,255]);return e.box(e.types.avc1,s,e.box(e.types.avcC,i))},e.mvex=function(t){return e.box(e.types.mvex,e.trex(t))},e.trex=function(t){var i=t.id,n=new Uint8Array([0,0,0,0,i>>>24&255,i>>>16&255,i>>>8&255,255&i,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1]);return e.box(e.types.trex,n)},e.moof=function(t,i){return e.box(e.types.moof,e.mfhd(t.sequenceNumber),e.traf(t,i))},e.mfhd=function(t){var i=new Uint8Array([0,0,0,0,t>>>24&255,t>>>16&255,t>>>8&255,255&t]);return e.box(e.types.mfhd,i)},e.traf=function(t,i){var n=t.id,r=e.box(e.types.tfhd,new Uint8Array([0,0,0,0,n>>>24&255,n>>>16&255,n>>>8&255,255&n])),s=e.box(e.types.tfdt,new Uint8Array([0,0,0,0,i>>>24&255,i>>>16&255,i>>>8&255,255&i])),o=e.sdtp(t),a=e.trun(t,o.byteLength+16+16+8+16+8+8);return e.box(e.types.traf,r,s,a,o)},e.sdtp=function(t){for(var i=t.samples||[],n=i.length,r=new Uint8Array(4+n),s=0;s<n;s++){var o=i[s].flags;r[s+4]=o.isLeading<<6|o.dependsOn<<4|o.isDependedOn<<2|o.hasRedundancy}return e.box(e.types.sdtp,r)},e.trun=function(t,i){var n=t.samples||[],r=n.length,s=12+16*r,o=new Uint8Array(s);i+=8+s,o.set([0,0,15,1,r>>>24&255,r>>>16&255,r>>>8&255,255&r,i>>>24&255,i>>>16&255,i>>>8&255,255&i],0);for(var a=0;a<r;a++){var h=n[a].duration,u=n[a].size,l=n[a].flags,d=n[a].cts;o.set([h>>>24&255,h>>>16&255,h>>>8&255,255&h,u>>>24&255,u>>>16&255,u>>>8&255,255&u,l.isLeading<<2|l.dependsOn,l.isDependedOn<<6|l.hasRedundancy<<4|l.isNonSync,0,0,d>>>24&255,d>>>16&255,d>>>8&255,255&d],12+16*a)}return e.box(e.types.trun,o)},e.mdat=function(t){return e.box(e.types.mdat,t)},e}();v.init();var y=v,b=function(){function e(){}return e.getSilentFrame=function(e,t){if("mp4a.40.2"===e){if(1===t)return new Uint8Array([0,200,0,128,35,128]);if(2===t)return new Uint8Array([33,0,73,144,2,25,0,35,128]);if(3===t)return new Uint8Array([0,200,0,128,32,132,1,38,64,8,100,0,142]);if(4===t)return new Uint8Array([0,200,0,128,32,132,1,38,64,8,100,0,128,44,128,8,2,56]);if(5===t)return new Uint8Array([0,200,0,128,32,132,1,38,64,8,100,0,130,48,4,153,0,33,144,2,56]);if(6===t)return new Uint8Array([0,200,0,128,32,132,1,38,64,8,100,0,130,48,4,153,0,33,144,2,0,178,0,32,8,224])}else{if(1===t)return new Uint8Array([1,64,34,128,163,78,230,128,186,8,0,0,0,28,6,241,193,10,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,94]);if(2===t)return new Uint8Array([1,64,34,128,163,94,230,128,186,8,0,0,0,0,149,0,6,241,161,10,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,94]);if(3===t)return new Uint8Array([1,64,34,128,163,94,230,128,186,8,0,0,0,0,149,0,6,241,161,10,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,90,94])}return null},e}(),E=i(51),S=function(){function e(e){this.TAG="MP4Remuxer",this._config=e,this._isLive=!0===e.isLive,this._dtsBase=-1,this._dtsBaseInited=!1,this._audioDtsBase=1/0,this._videoDtsBase=1/0,this._audioNextDts=void 0,this._videoNextDts=void 0,this._audioStashedLastSample=null,this._videoStashedLastSample=null,this._audioMeta=null,this._videoMeta=null,this._audioSegmentInfoList=new E.J1("audio"),this._videoSegmentInfoList=new E.J1("video"),this._onInitSegment=null,this._onMediaSegment=null,this._forceFirstIDR=!(!o.Z.chrome||!(o.Z.version.major<50||50===o.Z.version.major&&o.Z.version.build<2661)),this._fillSilentAfterSeek=o.Z.msedge||o.Z.msie,this._mp3UseMpegAudio=!o.Z.firefox,this._fillAudioTimestampGap=this._config.fixAudioTimestampGap}return e.prototype.destroy=function(){this._dtsBase=-1,this._dtsBaseInited=!1,this._audioMeta=null,this._videoMeta=null,this._audioSegmentInfoList.clear(),this._audioSegmentInfoList=null,this._videoSegmentInfoList.clear(),this._videoSegmentInfoList=null,this._onInitSegment=null,this._onMediaSegment=null},e.prototype.bindDataSource=function(e){return e.onDataAvailable=this.remux.bind(this),e.onTrackMetadata=this._onTrackMetadataReceived.bind(this),this},Object.defineProperty(e.prototype,"onInitSegment",{get:function(){return this._onInitSegment},set:function(e){this._onInitSegment=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onMediaSegment",{get:function(){return this._onMediaSegment},set:function(e){this._onMediaSegment=e},enumerable:!1,configurable:!0}),e.prototype.insertDiscontinuity=function(){this._audioNextDts=this._videoNextDts=void 0},e.prototype.seek=function(e){this._audioStashedLastSample=null,this._videoStashedLastSample=null,this._videoSegmentInfoList.clear(),this._audioSegmentInfoList.clear()},e.prototype.remux=function(e,t){if(!this._onMediaSegment)throw new d.rT("MP4Remuxer: onMediaSegment callback must be specificed!");this._dtsBaseInited||this._calculateDtsBase(e,t),this._remuxVideo(t),this._remuxAudio(e)},e.prototype._onTrackMetadataReceived=function(e,t){var i=null,n="mp4",r=t.codec;if("audio"===e)this._audioMeta=t,"mp3"===t.codec&&this._mp3UseMpegAudio?(n="mpeg",r="",i=new Uint8Array):i=y.generateInitSegment(t);else{if("video"!==e)return;this._videoMeta=t,i=y.generateInitSegment(t)}if(!this._onInitSegment)throw new d.rT("MP4Remuxer: onInitSegment callback must be specified!");this._onInitSegment(e,{type:e,data:i.buffer,codec:r,container:e+"/"+n,mediaDuration:t.duration})},e.prototype._calculateDtsBase=function(e,t){this._dtsBaseInited||(e.samples&&e.samples.length&&(this._audioDtsBase=e.samples[0].dts),t.samples&&t.samples.length&&(this._videoDtsBase=t.samples[0].dts),this._dtsBase=Math.min(this._audioDtsBase,this._videoDtsBase),this._dtsBaseInited=!0)},e.prototype.flushStashedSamples=function(){var e=this._videoStashedLastSample,t=this._audioStashedLastSample,i={type:"video",id:1,sequenceNumber:0,samples:[],length:0};null!=e&&(i.samples.push(e),i.length=e.length);var n={type:"audio",id:2,sequenceNumber:0,samples:[],length:0};null!=t&&(n.samples.push(t),n.length=t.length),this._videoStashedLastSample=null,this._audioStashedLastSample=null,this._remuxVideo(i,!0),this._remuxAudio(n,!0)},e.prototype._remuxAudio=function(e,t){if(null!=this._audioMeta){var i,n=e,r=n.samples,a=void 0,h=-1,u=this._audioMeta.refSampleDuration,l="mp3"===this._audioMeta.codec&&this._mp3UseMpegAudio,d=this._dtsBaseInited&&void 0===this._audioNextDts,c=!1;if(r&&0!==r.length&&(1!==r.length||t)){var f=0,_=null,p=0;l?(f=0,p=n.length):(f=8,p=8+n.length);var m=null;if(r.length>1&&(p-=(m=r.pop()).length),null!=this._audioStashedLastSample){var g=this._audioStashedLastSample;this._audioStashedLastSample=null,r.unshift(g),p+=g.length}null!=m&&(this._audioStashedLastSample=m);var v=r[0].dts-this._dtsBase;if(this._audioNextDts)a=v-this._audioNextDts;else if(this._audioSegmentInfoList.isEmpty())a=0,this._fillSilentAfterSeek&&!this._videoSegmentInfoList.isEmpty()&&"mp3"!==this._audioMeta.originalCodec&&(c=!0);else{var S=this._audioSegmentInfoList.getLastSampleBefore(v);if(null!=S){var A=v-(S.originalDts+S.duration);A<=3&&(A=0),a=v-(S.dts+S.duration+A)}else a=0}if(c){var L=v-a,R=this._videoSegmentInfoList.getLastSegmentBefore(v);if(null!=R&&R.beginDts<L){if(P=b.getSilentFrame(this._audioMeta.originalCodec,this._audioMeta.channelCount)){var w=R.beginDts,O=L-R.beginDts;s.Z.v(this.TAG,"InsertPrefixSilentAudio: dts: "+w+", duration: "+O),r.unshift({unit:P,dts:w,pts:w}),p+=P.byteLength}}else c=!1}for(var T=[],C=0;C<r.length;C++){var k=(g=r[C]).unit,D=g.dts-this._dtsBase,I=(w=D,!1),M=null,B=0;if(!(D<-.001)){if("mp3"!==this._audioMeta.codec){var x=D;if(this._audioNextDts&&(x=this._audioNextDts),(a=D-x)<=-3*u){s.Z.w(this.TAG,"Dropping 1 audio frame (originalDts: "+D+" ms ,curRefDts: "+x+" ms)  due to dtsCorrection: "+a+" ms overlap.");continue}if(a>=3*u&&this._fillAudioTimestampGap&&!o.Z.safari){I=!0;var P,U=Math.floor(a/u);s.Z.w(this.TAG,"Large audio timestamp gap detected, may cause AV sync to drift. Silent frames will be generated to avoid unsync.\\noriginalDts: "+D+" ms, curRefDts: "+x+" ms, dtsCorrection: "+Math.round(a)+" ms, generate: "+U+" frames"),w=Math.floor(x),B=Math.floor(x+u)-w,null==(P=b.getSilentFrame(this._audioMeta.originalCodec,this._audioMeta.channelCount))&&(s.Z.w(this.TAG,"Unable to generate silent frame for "+this._audioMeta.originalCodec+" with "+this._audioMeta.channelCount+" channels, repeat last frame"),P=k),M=[];for(var N=0;N<U;N++){x+=u;var Z=Math.floor(x),F=Math.floor(x+u)-Z,G={dts:Z,pts:Z,cts:0,unit:P,size:P.byteLength,duration:F,originalDts:D,flags:{isLeading:0,dependsOn:1,isDependedOn:0,hasRedundancy:0}};M.push(G),p+=G.size}this._audioNextDts=x+u}else w=Math.floor(x),B=Math.floor(x+u)-w,this._audioNextDts=x+u}else{if(w=D-a,C!==r.length-1)B=r[C+1].dts-this._dtsBase-a-w;else if(null!=m)B=m.dts-this._dtsBase-a-w;else B=T.length>=1?T[T.length-1].duration:Math.floor(u);this._audioNextDts=w+B}-1===h&&(h=w),T.push({dts:w,pts:w,cts:0,unit:g.unit,size:g.unit.byteLength,duration:B,originalDts:D,flags:{isLeading:0,dependsOn:1,isDependedOn:0,hasRedundancy:0}}),I&&T.push.apply(T,M)}}if(0===T.length)return n.samples=[],void(n.length=0);l?_=new Uint8Array(p):((_=new Uint8Array(p))[0]=p>>>24&255,_[1]=p>>>16&255,_[2]=p>>>8&255,_[3]=255&p,_.set(y.types.mdat,4));for(C=0;C<T.length;C++){k=T[C].unit;_.set(k,f),f+=k.byteLength}var j=T[T.length-1];i=j.dts+j.duration;var V=new E.Yy;V.beginDts=h,V.endDts=i,V.beginPts=h,V.endPts=i,V.originalBeginDts=T[0].originalDts,V.originalEndDts=j.originalDts+j.duration,V.firstSample=new E.Wk(T[0].dts,T[0].pts,T[0].duration,T[0].originalDts,!1),V.lastSample=new E.Wk(j.dts,j.pts,j.duration,j.originalDts,!1),this._isLive||this._audioSegmentInfoList.append(V),n.samples=T,n.sequenceNumber++;var z=null;z=l?new Uint8Array:y.moof(n,h),n.samples=[],n.length=0;var K={type:"audio",data:this._mergeBoxes(z,_).buffer,sampleCount:T.length,info:V};l&&d&&(K.timestampOffset=h),this._onMediaSegment("audio",K)}}},e.prototype._remuxVideo=function(e,t){if(null!=this._videoMeta){var i,n,r=e,s=r.samples,o=void 0,a=-1,h=-1;if(s&&0!==s.length&&(1!==s.length||t)){var u=8,l=null,d=8+e.length,c=null;if(s.length>1&&(d-=(c=s.pop()).length),null!=this._videoStashedLastSample){var f=this._videoStashedLastSample;this._videoStashedLastSample=null,s.unshift(f),d+=f.length}null!=c&&(this._videoStashedLastSample=c);var _=s[0].dts-this._dtsBase;if(this._videoNextDts)o=_-this._videoNextDts;else if(this._videoSegmentInfoList.isEmpty())o=0;else{var p=this._videoSegmentInfoList.getLastSampleBefore(_);if(null!=p){var m=_-(p.originalDts+p.duration);m<=3&&(m=0),o=_-(p.dts+p.duration+m)}else o=0}for(var g=new E.Yy,v=[],b=0;b<s.length;b++){var S=(f=s[b]).dts-this._dtsBase,A=f.isKeyframe,L=S-o,R=f.cts,w=L+R;-1===a&&(a=L,h=w);var O=0;if(b!==s.length-1)O=s[b+1].dts-this._dtsBase-o-L;else if(null!=c)O=c.dts-this._dtsBase-o-L;else O=v.length>=1?v[v.length-1].duration:Math.floor(this._videoMeta.refSampleDuration);if(A){var T=new E.Wk(L,w,O,f.dts,!0);T.fileposition=f.fileposition,g.appendSyncPoint(T)}v.push({dts:L,pts:w,cts:R,units:f.units,size:f.length,isKeyframe:A,duration:O,originalDts:S,flags:{isLeading:0,dependsOn:A?2:1,isDependedOn:A?1:0,hasRedundancy:0,isNonSync:A?0:1}})}(l=new Uint8Array(d))[0]=d>>>24&255,l[1]=d>>>16&255,l[2]=d>>>8&255,l[3]=255&d,l.set(y.types.mdat,4);for(b=0;b<v.length;b++)for(var C=v[b].units;C.length;){var k=C.shift().data;l.set(k,u),u+=k.byteLength}var D=v[v.length-1];if(i=D.dts+D.duration,n=D.pts+D.duration,this._videoNextDts=i,g.beginDts=a,g.endDts=i,g.beginPts=h,g.endPts=n,g.originalBeginDts=v[0].originalDts,g.originalEndDts=D.originalDts+D.duration,g.firstSample=new E.Wk(v[0].dts,v[0].pts,v[0].duration,v[0].originalDts,v[0].isKeyframe),g.lastSample=new E.Wk(D.dts,D.pts,D.duration,D.originalDts,D.isKeyframe),this._isLive||this._videoSegmentInfoList.append(g),r.samples=v,r.sequenceNumber++,this._forceFirstIDR){var I=v[0].flags;I.dependsOn=2,I.isNonSync=0}var M=y.moof(r,a);r.samples=[],r.length=0,this._onMediaSegment("video",{type:"video",data:this._mergeBoxes(M,l).buffer,sampleCount:v.length,info:g})}}},e.prototype._mergeBoxes=function(e,t){var i=new Uint8Array(e.byteLength+t.byteLength);return i.set(e,0),i.set(t,e.byteLength),i},e}(),A=i(191),L=i(257),R=function(){function e(e,t){this.TAG="TransmuxingController",this._emitter=new(r()),this._config=t,e.segments||(e.segments=[{duration:e.duration,filesize:e.filesize,url:e.url}]),"boolean"!=typeof e.cors&&(e.cors=!0),"boolean"!=typeof e.withCredentials&&(e.withCredentials=!1),this._mediaDataSource=e,this._currentSegmentIndex=0;var i=0;this._mediaDataSource.segments.forEach((function(n){n.timestampBase=i,i+=n.duration,n.cors=e.cors,n.withCredentials=e.withCredentials,t.referrerPolicy&&(n.referrerPolicy=t.referrerPolicy)})),isNaN(i)||this._mediaDataSource.duration===i||(this._mediaDataSource.duration=i),this._mediaInfo=null,this._demuxer=null,this._remuxer=null,this._ioctl=null,this._pendingSeekTime=null,this._pendingResolveSeekPoint=null,this._statisticsReporter=null}return e.prototype.destroy=function(){this._mediaInfo=null,this._mediaDataSource=null,this._statisticsReporter&&this._disableStatisticsReporter(),this._ioctl&&(this._ioctl.destroy(),this._ioctl=null),this._demuxer&&(this._demuxer.destroy(),this._demuxer=null),this._remuxer&&(this._remuxer.destroy(),this._remuxer=null),this._emitter.removeAllListeners(),this._emitter=null},e.prototype.on=function(e,t){this._emitter.addListener(e,t)},e.prototype.off=function(e,t){this._emitter.removeListener(e,t)},e.prototype.start=function(){this._loadSegment(0),this._enableStatisticsReporter()},e.prototype._loadSegment=function(e,t){this._currentSegmentIndex=e;var i=this._mediaDataSource.segments[e],n=this._ioctl=new A.Z(i,this._config,e);n.onError=this._onIOException.bind(this),n.onSeeked=this._onIOSeeked.bind(this),n.onComplete=this._onIOComplete.bind(this),n.onRedirect=this._onIORedirect.bind(this),n.onRecoveredEarlyEof=this._onIORecoveredEarlyEof.bind(this),t?this._demuxer.bindDataSource(this._ioctl):n.onDataArrival=this._onInitChunkArrival.bind(this),n.open(t)},e.prototype.stop=function(){this._internalAbort(),this._disableStatisticsReporter()},e.prototype._internalAbort=function(){this._ioctl&&(this._ioctl.destroy(),this._ioctl=null)},e.prototype.pause=function(){this._ioctl&&this._ioctl.isWorking()&&(this._ioctl.pause(),this._disableStatisticsReporter())},e.prototype.resume=function(){this._ioctl&&this._ioctl.isPaused()&&(this._ioctl.resume(),this._enableStatisticsReporter())},e.prototype.seek=function(e){if(null!=this._mediaInfo&&this._mediaInfo.isSeekable()){var t=this._searchSegmentIndexContains(e);if(t===this._currentSegmentIndex){var i=this._mediaInfo.segments[t];if(null==i)this._pendingSeekTime=e;else{var n=i.getNearestKeyframe(e);this._remuxer.seek(n.milliseconds),this._ioctl.seek(n.fileposition),this._pendingResolveSeekPoint=n.milliseconds}}else{var r=this._mediaInfo.segments[t];if(null==r)this._pendingSeekTime=e,this._internalAbort(),this._remuxer.seek(),this._remuxer.insertDiscontinuity(),this._loadSegment(t);else{n=r.getNearestKeyframe(e);this._internalAbort(),this._remuxer.seek(e),this._remuxer.insertDiscontinuity(),this._demuxer.resetMediaInfo(),this._demuxer.timestampBase=this._mediaDataSource.segments[t].timestampBase,this._loadSegment(t,n.fileposition),this._pendingResolveSeekPoint=n.milliseconds,this._reportSegmentMediaInfo(t)}}this._enableStatisticsReporter()}},e.prototype._searchSegmentIndexContains=function(e){for(var t=this._mediaDataSource.segments,i=t.length-1,n=0;n<t.length;n++)if(e<t[n].timestampBase){i=n-1;break}return i},e.prototype._onInitChunkArrival=function(e,t){var i=this,n=null,r=0;if(t>0)this._demuxer.bindDataSource(this._ioctl),this._demuxer.timestampBase=this._mediaDataSource.segments[this._currentSegmentIndex].timestampBase,r=this._demuxer.parseChunks(e,t);else if((n=g.probe(e)).match){this._demuxer=new g(n,this._config),this._remuxer||(this._remuxer=new S(this._config));var o=this._mediaDataSource;null==o.duration||isNaN(o.duration)||(this._demuxer.overridedDuration=o.duration),"boolean"==typeof o.hasAudio&&(this._demuxer.overridedHasAudio=o.hasAudio),"boolean"==typeof o.hasVideo&&(this._demuxer.overridedHasVideo=o.hasVideo),this._demuxer.timestampBase=o.segments[this._currentSegmentIndex].timestampBase,this._demuxer.onError=this._onDemuxException.bind(this),this._demuxer.onMediaInfo=this._onMediaInfo.bind(this),this._demuxer.onMetaDataArrived=this._onMetaDataArrived.bind(this),this._demuxer.onScriptDataArrived=this._onScriptDataArrived.bind(this),this._remuxer.bindDataSource(this._demuxer.bindDataSource(this._ioctl)),this._remuxer.onInitSegment=this._onRemuxerInitSegmentArrival.bind(this),this._remuxer.onMediaSegment=this._onRemuxerMediaSegmentArrival.bind(this),r=this._demuxer.parseChunks(e,t)}else n=null,s.Z.e(this.TAG,"Non-FLV, Unsupported media type!"),Promise.resolve().then((function(){i._internalAbort()})),this._emitter.emit(L.Z.DEMUX_ERROR,m.Z.FORMAT_UNSUPPORTED,"Non-FLV, Unsupported media type"),r=0;return r},e.prototype._onMediaInfo=function(e){var t=this;null==this._mediaInfo&&(this._mediaInfo=Object.assign({},e),this._mediaInfo.keyframesIndex=null,this._mediaInfo.segments=[],this._mediaInfo.segmentCount=this._mediaDataSource.segments.length,Object.setPrototypeOf(this._mediaInfo,a.Z.prototype));var i=Object.assign({},e);Object.setPrototypeOf(i,a.Z.prototype),this._mediaInfo.segments[this._currentSegmentIndex]=i,this._reportSegmentMediaInfo(this._currentSegmentIndex),null!=this._pendingSeekTime&&Promise.resolve().then((function(){var e=t._pendingSeekTime;t._pendingSeekTime=null,t.seek(e)}))},e.prototype._onMetaDataArrived=function(e){this._emitter.emit(L.Z.METADATA_ARRIVED,e)},e.prototype._onScriptDataArrived=function(e){this._emitter.emit(L.Z.SCRIPTDATA_ARRIVED,e)},e.prototype._onIOSeeked=function(){this._remuxer.insertDiscontinuity()},e.prototype._onIOComplete=function(e){var t=e+1;t<this._mediaDataSource.segments.length?(this._internalAbort(),this._remuxer.flushStashedSamples(),this._loadSegment(t)):(this._remuxer.flushStashedSamples(),this._emitter.emit(L.Z.LOADING_COMPLETE),this._disableStatisticsReporter())},e.prototype._onIORedirect=function(e){var t=this._ioctl.extraData;this._mediaDataSource.segments[t].redirectedURL=e},e.prototype._onIORecoveredEarlyEof=function(){this._emitter.emit(L.Z.RECOVERED_EARLY_EOF)},e.prototype._onIOException=function(e,t){s.Z.e(this.TAG,"IOException: type = "+e+", code = "+t.code+", msg = "+t.msg),this._emitter.emit(L.Z.IO_ERROR,e,t),this._disableStatisticsReporter()},e.prototype._onDemuxException=function(e,t){s.Z.e(this.TAG,"DemuxException: type = "+e+", info = "+t),this._emitter.emit(L.Z.DEMUX_ERROR,e,t)},e.prototype._onRemuxerInitSegmentArrival=function(e,t){this._emitter.emit(L.Z.INIT_SEGMENT,e,t)},e.prototype._onRemuxerMediaSegmentArrival=function(e,t){if(null==this._pendingSeekTime&&(this._emitter.emit(L.Z.MEDIA_SEGMENT,e,t),null!=this._pendingResolveSeekPoint&&"video"===e)){var i=t.info.syncPoints,n=this._pendingResolveSeekPoint;this._pendingResolveSeekPoint=null,o.Z.safari&&i.length>0&&i[0].originalDts===n&&(n=i[0].pts),this._emitter.emit(L.Z.RECOMMEND_SEEKPOINT,n)}},e.prototype._enableStatisticsReporter=function(){null==this._statisticsReporter&&(this._statisticsReporter=self.setInterval(this._reportStatisticsInfo.bind(this),this._config.statisticsInfoReportInterval))},e.prototype._disableStatisticsReporter=function(){this._statisticsReporter&&(self.clearInterval(this._statisticsReporter),this._statisticsReporter=null)},e.prototype._reportSegmentMediaInfo=function(e){var t=this._mediaInfo.segments[e],i=Object.assign({},t);i.duration=this._mediaInfo.duration,i.segmentCount=this._mediaInfo.segmentCount,delete i.segments,delete i.keyframesIndex,this._emitter.emit(L.Z.MEDIA_INFO,i)},e.prototype._reportStatisticsInfo=function(){var e={};e.url=this._ioctl.currentURL,e.hasRedirect=this._ioctl.hasRedirect,e.hasRedirect&&(e.redirectedURL=this._ioctl.currentRedirectedURL),e.speed=this._ioctl.currentSpeed,e.loaderType=this._ioctl.loaderType,e.currentSegmentIndex=this._currentSegmentIndex,e.totalSegmentCount=this._mediaDataSource.segments.length,this._emitter.emit(L.Z.STATISTICS_INFO,e)},e}()},257:function(e,t){"use strict";t.Z={IO_ERROR:"io_error",DEMUX_ERROR:"demux_error",INIT_SEGMENT:"init_segment",MEDIA_SEGMENT:"media_segment",LOADING_COMPLETE:"loading_complete",RECOVERED_EARLY_EOF:"recovered_early_eof",MEDIA_INFO:"media_info",METADATA_ARRIVED:"metadata_arrived",SCRIPTDATA_ARRIVED:"scriptdata_arrived",STATISTICS_INFO:"statistics_info",RECOMMEND_SEEKPOINT:"recommend_seekpoint"}},82:function(e,t,i){"use strict";i(846),i(219),i(949),i(257)},600:function(e,t){"use strict";t.Z={OK:"OK",FORMAT_ERROR:"FormatError",FORMAT_UNSUPPORTED:"FormatUnsupported",CODEC_UNSUPPORTED:"CodecUnsupported"}},60:function(e,t,i){"use strict";i.d(t,{default:function(){return D}});var n=i(219),r=i(191),s={enableWorker:!1,enableStashBuffer:!0,stashInitialSize:void 0,isLive:!1,lazyLoad:!0,lazyLoadMaxDuration:180,lazyLoadRecoverDuration:30,deferLoadAfterSourceOpen:!0,autoCleanupMaxBackwardDuration:180,autoCleanupMinBackwardDuration:120,statisticsInfoReportInterval:600,fixAudioTimestampGap:!0,accurateSeek:!1,seekType:"range",seekParamStart:"bstart",seekParamEnd:"bend",rangeLoadZeroStart:!1,customSeekHandler:void 0,reuseRedirectedURL:!1,headers:void 0,customLoader:void 0};function o(){return Object.assign({},s)}var a=function(){function e(){}return e.supportMSEH264Playback=function(){return window.MediaSource&&window.MediaSource.isTypeSupported(\'video/mp4; codecs="avc1.42E01E,mp4a.40.2"\')},e.supportNetworkStreamIO=function(){var e=new r.Z({},o()),t=e.loaderType;return e.destroy(),"fetch-stream-loader"==t||"xhr-moz-chunked-loader"==t},e.getNetworkLoaderTypeName=function(){var e=new r.Z({},o()),t=e.loaderType;return e.destroy(),t},e.supportNativeMediaPlayback=function(t){null==e.videoElement&&(e.videoElement=window.document.createElement("video"));var i=e.videoElement.canPlayType(t);return"probably"===i||"maybe"==i},e.getFeatureList=function(){var t={mseFlvPlayback:!1,mseLiveFlvPlayback:!1,networkStreamIO:!1,networkLoaderName:"",nativeMP4H264Playback:!1,nativeWebmVP8Playback:!1,nativeWebmVP9Playback:!1};return t.mseFlvPlayback=e.supportMSEH264Playback(),t.networkStreamIO=e.supportNetworkStreamIO(),t.networkLoaderName=e.getNetworkLoaderTypeName(),t.mseLiveFlvPlayback=t.mseFlvPlayback&&t.networkStreamIO,t.nativeMP4H264Playback=e.supportNativeMediaPlayback(\'video/mp4; codecs="avc1.42001E, mp4a.40.2"\'),t.nativeWebmVP8Playback=e.supportNativeMediaPlayback(\'video/webm; codecs="vp8.0, vorbis"\'),t.nativeWebmVP9Playback=e.supportNativeMediaPlayback(\'video/webm; codecs="vp9"\'),t},e}(),h=i(939),u=i(716),l=i.n(u),d=i(300),c=i(538),f={ERROR:"error",LOADING_COMPLETE:"loading_complete",RECOVERED_EARLY_EOF:"recovered_early_eof",MEDIA_INFO:"media_info",METADATA_ARRIVED:"metadata_arrived",SCRIPTDATA_ARRIVED:"scriptdata_arrived",STATISTICS_INFO:"statistics_info"},_=i(397),p=i.n(_),m=i(846),g=i(949),v=i(257),y=i(118),b=function(){function e(e,t){if(this.TAG="Transmuxer",this._emitter=new(l()),t.enableWorker&&"undefined"!=typeof Worker)try{this._worker=p()(82),this._workerDestroying=!1,this._worker.addEventListener("message",this._onWorkerMessage.bind(this)),this._worker.postMessage({cmd:"init",param:[e,t]}),this.e={onLoggingConfigChanged:this._onLoggingConfigChanged.bind(this)},m.Z.registerListener(this.e.onLoggingConfigChanged),this._worker.postMessage({cmd:"logging_config",param:m.Z.getConfig()})}catch(i){d.Z.e(this.TAG,"Error while initialize transmuxing worker, fallback to inline transmuxing"),this._worker=null,this._controller=new g.Z(e,t)}else this._controller=new g.Z(e,t);if(this._controller){var i=this._controller;i.on(v.Z.IO_ERROR,this._onIOError.bind(this)),i.on(v.Z.DEMUX_ERROR,this._onDemuxError.bind(this)),i.on(v.Z.INIT_SEGMENT,this._onInitSegment.bind(this)),i.on(v.Z.MEDIA_SEGMENT,this._onMediaSegment.bind(this)),i.on(v.Z.LOADING_COMPLETE,this._onLoadingComplete.bind(this)),i.on(v.Z.RECOVERED_EARLY_EOF,this._onRecoveredEarlyEof.bind(this)),i.on(v.Z.MEDIA_INFO,this._onMediaInfo.bind(this)),i.on(v.Z.METADATA_ARRIVED,this._onMetaDataArrived.bind(this)),i.on(v.Z.SCRIPTDATA_ARRIVED,this._onScriptDataArrived.bind(this)),i.on(v.Z.STATISTICS_INFO,this._onStatisticsInfo.bind(this)),i.on(v.Z.RECOMMEND_SEEKPOINT,this._onRecommendSeekpoint.bind(this))}}return e.prototype.destroy=function(){this._worker?this._workerDestroying||(this._workerDestroying=!0,this._worker.postMessage({cmd:"destroy"}),m.Z.removeListener(this.e.onLoggingConfigChanged),this.e=null):(this._controller.destroy(),this._controller=null),this._emitter.removeAllListeners(),this._emitter=null},e.prototype.on=function(e,t){this._emitter.addListener(e,t)},e.prototype.off=function(e,t){this._emitter.removeListener(e,t)},e.prototype.hasWorker=function(){return null!=this._worker},e.prototype.open=function(){this._worker?this._worker.postMessage({cmd:"start"}):this._controller.start()},e.prototype.close=function(){this._worker?this._worker.postMessage({cmd:"stop"}):this._controller.stop()},e.prototype.seek=function(e){this._worker?this._worker.postMessage({cmd:"seek",param:e}):this._controller.seek(e)},e.prototype.pause=function(){this._worker?this._worker.postMessage({cmd:"pause"}):this._controller.pause()},e.prototype.resume=function(){this._worker?this._worker.postMessage({cmd:"resume"}):this._controller.resume()},e.prototype._onInitSegment=function(e,t){var i=this;Promise.resolve().then((function(){i._emitter.emit(v.Z.INIT_SEGMENT,e,t)}))},e.prototype._onMediaSegment=function(e,t){var i=this;Promise.resolve().then((function(){i._emitter.emit(v.Z.MEDIA_SEGMENT,e,t)}))},e.prototype._onLoadingComplete=function(){var e=this;Promise.resolve().then((function(){e._emitter.emit(v.Z.LOADING_COMPLETE)}))},e.prototype._onRecoveredEarlyEof=function(){var e=this;Promise.resolve().then((function(){e._emitter.emit(v.Z.RECOVERED_EARLY_EOF)}))},e.prototype._onMediaInfo=function(e){var t=this;Promise.resolve().then((function(){t._emitter.emit(v.Z.MEDIA_INFO,e)}))},e.prototype._onMetaDataArrived=function(e){var t=this;Promise.resolve().then((function(){t._emitter.emit(v.Z.METADATA_ARRIVED,e)}))},e.prototype._onScriptDataArrived=function(e){var t=this;Promise.resolve().then((function(){t._emitter.emit(v.Z.SCRIPTDATA_ARRIVED,e)}))},e.prototype._onStatisticsInfo=function(e){var t=this;Promise.resolve().then((function(){t._emitter.emit(v.Z.STATISTICS_INFO,e)}))},e.prototype._onIOError=function(e,t){var i=this;Promise.resolve().then((function(){i._emitter.emit(v.Z.IO_ERROR,e,t)}))},e.prototype._onDemuxError=function(e,t){var i=this;Promise.resolve().then((function(){i._emitter.emit(v.Z.DEMUX_ERROR,e,t)}))},e.prototype._onRecommendSeekpoint=function(e){var t=this;Promise.resolve().then((function(){t._emitter.emit(v.Z.RECOMMEND_SEEKPOINT,e)}))},e.prototype._onLoggingConfigChanged=function(e){this._worker&&this._worker.postMessage({cmd:"logging_config",param:e})},e.prototype._onWorkerMessage=function(e){var t=e.data,i=t.data;if("destroyed"===t.msg||this._workerDestroying)return this._workerDestroying=!1,this._worker.terminate(),void(this._worker=null);switch(t.msg){case v.Z.INIT_SEGMENT:case v.Z.MEDIA_SEGMENT:this._emitter.emit(t.msg,i.type,i.data);break;case v.Z.LOADING_COMPLETE:case v.Z.RECOVERED_EARLY_EOF:this._emitter.emit(t.msg);break;case v.Z.MEDIA_INFO:Object.setPrototypeOf(i,y.Z.prototype),this._emitter.emit(t.msg,i);break;case v.Z.METADATA_ARRIVED:case v.Z.SCRIPTDATA_ARRIVED:case v.Z.STATISTICS_INFO:this._emitter.emit(t.msg,i);break;case v.Z.IO_ERROR:case v.Z.DEMUX_ERROR:this._emitter.emit(t.msg,i.type,i.info);break;case v.Z.RECOMMEND_SEEKPOINT:this._emitter.emit(t.msg,i);break;case"logcat_callback":d.Z.emitter.emit("log",i.type,i.logcat)}},e}(),E={ERROR:"error",SOURCE_OPEN:"source_open",UPDATE_END:"update_end",BUFFER_FULL:"buffer_full"},S=i(51),A=i(29),L=function(){function e(e){this.TAG="MSEController",this._config=e,this._emitter=new(l()),this._config.isLive&&null==this._config.autoCleanupSourceBuffer&&(this._config.autoCleanupSourceBuffer=!0),this.e={onSourceOpen:this._onSourceOpen.bind(this),onSourceEnded:this._onSourceEnded.bind(this),onSourceClose:this._onSourceClose.bind(this),onSourceBufferError:this._onSourceBufferError.bind(this),onSourceBufferUpdateEnd:this._onSourceBufferUpdateEnd.bind(this)},this._mediaSource=null,this._mediaSourceObjectURL=null,this._mediaElement=null,this._isBufferFull=!1,this._hasPendingEos=!1,this._requireSetMediaDuration=!1,this._pendingMediaDuration=0,this._pendingSourceBufferInit=[],this._mimeTypes={video:null,audio:null},this._sourceBuffers={video:null,audio:null},this._lastInitSegments={video:null,audio:null},this._pendingSegments={video:[],audio:[]},this._pendingRemoveRanges={video:[],audio:[]},this._idrList=new S.Vn}return e.prototype.destroy=function(){(this._mediaElement||this._mediaSource)&&this.detachMediaElement(),this.e=null,this._emitter.removeAllListeners(),this._emitter=null},e.prototype.on=function(e,t){this._emitter.addListener(e,t)},e.prototype.off=function(e,t){this._emitter.removeListener(e,t)},e.prototype.attachMediaElement=function(e){if(this._mediaSource)throw new A.rT("MediaSource has been attached to an HTMLMediaElement!");var t=this._mediaSource=new window.MediaSource;t.addEventListener("sourceopen",this.e.onSourceOpen),t.addEventListener("sourceended",this.e.onSourceEnded),t.addEventListener("sourceclose",this.e.onSourceClose),this._mediaElement=e,this._mediaSourceObjectURL=window.URL.createObjectURL(this._mediaSource),e.src=this._mediaSourceObjectURL},e.prototype.detachMediaElement=function(){if(this._mediaSource){var e=this._mediaSource;for(var t in this._sourceBuffers){var i=this._pendingSegments[t];i.splice(0,i.length),this._pendingSegments[t]=null,this._pendingRemoveRanges[t]=null,this._lastInitSegments[t]=null;var n=this._sourceBuffers[t];if(n){if("closed"!==e.readyState){try{e.removeSourceBuffer(n)}catch(e){d.Z.e(this.TAG,e.message)}n.removeEventListener("error",this.e.onSourceBufferError),n.removeEventListener("updateend",this.e.onSourceBufferUpdateEnd)}this._mimeTypes[t]=null,this._sourceBuffers[t]=null}}if("open"===e.readyState)try{e.endOfStream()}catch(e){d.Z.e(this.TAG,e.message)}e.removeEventListener("sourceopen",this.e.onSourceOpen),e.removeEventListener("sourceended",this.e.onSourceEnded),e.removeEventListener("sourceclose",this.e.onSourceClose),this._pendingSourceBufferInit=[],this._isBufferFull=!1,this._idrList.clear(),this._mediaSource=null}this._mediaElement&&(this._mediaElement.src="",this._mediaElement.removeAttribute("src"),this._mediaElement=null),this._mediaSourceObjectURL&&(window.URL.revokeObjectURL(this._mediaSourceObjectURL),this._mediaSourceObjectURL=null)},e.prototype.appendInitSegment=function(e,t){if(!this._mediaSource||"open"!==this._mediaSource.readyState)return this._pendingSourceBufferInit.push(e),void this._pendingSegments[e.type].push(e);var i=e,n=""+i.container;i.codec&&i.codec.length>0&&(n+=";codecs="+i.codec);var r=!1;if(d.Z.v(this.TAG,"Received Initialization Segment, mimeType: "+n),this._lastInitSegments[i.type]=i,n!==this._mimeTypes[i.type]){if(this._mimeTypes[i.type])d.Z.v(this.TAG,"Notice: "+i.type+" mimeType changed, origin: "+this._mimeTypes[i.type]+", target: "+n);else{r=!0;try{var s=this._sourceBuffers[i.type]=this._mediaSource.addSourceBuffer(n);s.addEventListener("error",this.e.onSourceBufferError),s.addEventListener("updateend",this.e.onSourceBufferUpdateEnd)}catch(e){return d.Z.e(this.TAG,e.message),void this._emitter.emit(E.ERROR,{code:e.code,msg:e.message})}}this._mimeTypes[i.type]=n}t||this._pendingSegments[i.type].push(i),r||this._sourceBuffers[i.type]&&!this._sourceBuffers[i.type].updating&&this._doAppendSegments(),c.Z.safari&&"audio/mpeg"===i.container&&i.mediaDuration>0&&(this._requireSetMediaDuration=!0,this._pendingMediaDuration=i.mediaDuration/1e3,this._updateMediaSourceDuration())},e.prototype.appendMediaSegment=function(e){var t=e;this._pendingSegments[t.type].push(t),this._config.autoCleanupSourceBuffer&&this._needCleanupSourceBuffer()&&this._doCleanupSourceBuffer();var i=this._sourceBuffers[t.type];!i||i.updating||this._hasPendingRemoveRanges()||this._doAppendSegments()},e.prototype.seek=function(e){for(var t in this._sourceBuffers)if(this._sourceBuffers[t]){var i=this._sourceBuffers[t];if("open"===this._mediaSource.readyState)try{i.abort()}catch(e){d.Z.e(this.TAG,e.message)}this._idrList.clear();var n=this._pendingSegments[t];if(n.splice(0,n.length),"closed"!==this._mediaSource.readyState){for(var r=0;r<i.buffered.length;r++){var s=i.buffered.start(r),o=i.buffered.end(r);this._pendingRemoveRanges[t].push({start:s,end:o})}if(i.updating||this._doRemoveRanges(),c.Z.safari){var a=this._lastInitSegments[t];a&&(this._pendingSegments[t].push(a),i.updating||this._doAppendSegments())}}}},e.prototype.endOfStream=function(){var e=this._mediaSource,t=this._sourceBuffers;e&&"open"===e.readyState?t.video&&t.video.updating||t.audio&&t.audio.updating?this._hasPendingEos=!0:(this._hasPendingEos=!1,e.endOfStream()):e&&"closed"===e.readyState&&this._hasPendingSegments()&&(this._hasPendingEos=!0)},e.prototype.getNearestKeyframe=function(e){return this._idrList.getLastSyncPointBeforeDts(e)},e.prototype._needCleanupSourceBuffer=function(){if(!this._config.autoCleanupSourceBuffer)return!1;var e=this._mediaElement.currentTime;for(var t in this._sourceBuffers){var i=this._sourceBuffers[t];if(i){var n=i.buffered;if(n.length>=1&&e-n.start(0)>=this._config.autoCleanupMaxBackwardDuration)return!0}}return!1},e.prototype._doCleanupSourceBuffer=function(){var e=this._mediaElement.currentTime;for(var t in this._sourceBuffers){var i=this._sourceBuffers[t];if(i){for(var n=i.buffered,r=!1,s=0;s<n.length;s++){var o=n.start(s),a=n.end(s);if(o<=e&&e<a+3){if(e-o>=this._config.autoCleanupMaxBackwardDuration){r=!0;var h=e-this._config.autoCleanupMinBackwardDuration;this._pendingRemoveRanges[t].push({start:o,end:h})}}else a<e&&(r=!0,this._pendingRemoveRanges[t].push({start:o,end:a}))}r&&!i.updating&&this._doRemoveRanges()}}},e.prototype._updateMediaSourceDuration=function(){var e=this._sourceBuffers;if(0!==this._mediaElement.readyState&&"open"===this._mediaSource.readyState&&!(e.video&&e.video.updating||e.audio&&e.audio.updating)){var t=this._mediaSource.duration,i=this._pendingMediaDuration;i>0&&(isNaN(t)||i>t)&&(d.Z.v(this.TAG,"Update MediaSource duration from "+t+" to "+i),this._mediaSource.duration=i),this._requireSetMediaDuration=!1,this._pendingMediaDuration=0}},e.prototype._doRemoveRanges=function(){for(var e in this._pendingRemoveRanges)if(this._sourceBuffers[e]&&!this._sourceBuffers[e].updating)for(var t=this._sourceBuffers[e],i=this._pendingRemoveRanges[e];i.length&&!t.updating;){var n=i.shift();t.remove(n.start,n.end)}},e.prototype._doAppendSegments=function(){var e=this._pendingSegments;for(var t in e)if(this._sourceBuffers[t]&&!this._sourceBuffers[t].updating&&e[t].length>0){var i=e[t].shift();if(i.timestampOffset){var n=this._sourceBuffers[t].timestampOffset,r=i.timestampOffset/1e3;Math.abs(n-r)>.1&&(d.Z.v(this.TAG,"Update MPEG audio timestampOffset from "+n+" to "+r),this._sourceBuffers[t].timestampOffset=r),delete i.timestampOffset}if(!i.data||0===i.data.byteLength)continue;try{this._sourceBuffers[t].appendBuffer(i.data),this._isBufferFull=!1,"video"===t&&i.hasOwnProperty("info")&&this._idrList.appendArray(i.info.syncPoints)}catch(e){this._pendingSegments[t].unshift(i),22===e.code?(this._isBufferFull||this._emitter.emit(E.BUFFER_FULL),this._isBufferFull=!0):(d.Z.e(this.TAG,e.message),this._emitter.emit(E.ERROR,{code:e.code,msg:e.message}))}}},e.prototype._onSourceOpen=function(){if(d.Z.v(this.TAG,"MediaSource onSourceOpen"),this._mediaSource.removeEventListener("sourceopen",this.e.onSourceOpen),this._pendingSourceBufferInit.length>0)for(var e=this._pendingSourceBufferInit;e.length;){var t=e.shift();this.appendInitSegment(t,!0)}this._hasPendingSegments()&&this._doAppendSegments(),this._emitter.emit(E.SOURCE_OPEN)},e.prototype._onSourceEnded=function(){d.Z.v(this.TAG,"MediaSource onSourceEnded")},e.prototype._onSourceClose=function(){d.Z.v(this.TAG,"MediaSource onSourceClose"),this._mediaSource&&null!=this.e&&(this._mediaSource.removeEventListener("sourceopen",this.e.onSourceOpen),this._mediaSource.removeEventListener("sourceended",this.e.onSourceEnded),this._mediaSource.removeEventListener("sourceclose",this.e.onSourceClose))},e.prototype._hasPendingSegments=function(){var e=this._pendingSegments;return e.video.length>0||e.audio.length>0},e.prototype._hasPendingRemoveRanges=function(){var e=this._pendingRemoveRanges;return e.video.length>0||e.audio.length>0},e.prototype._onSourceBufferUpdateEnd=function(){this._requireSetMediaDuration?this._updateMediaSourceDuration():this._hasPendingRemoveRanges()?this._doRemoveRanges():this._hasPendingSegments()?this._doAppendSegments():this._hasPendingEos&&this.endOfStream(),this._emitter.emit(E.UPDATE_END)},e.prototype._onSourceBufferError=function(e){d.Z.e(this.TAG,"SourceBuffer Error: "+e)},e}(),R=i(600),w={NETWORK_ERROR:"NetworkError",MEDIA_ERROR:"MediaError",OTHER_ERROR:"OtherError"},O={NETWORK_EXCEPTION:h.nm.EXCEPTION,NETWORK_STATUS_CODE_INVALID:h.nm.HTTP_STATUS_CODE_INVALID,NETWORK_TIMEOUT:h.nm.CONNECTING_TIMEOUT,NETWORK_UNRECOVERABLE_EARLY_EOF:h.nm.UNRECOVERABLE_EARLY_EOF,MEDIA_MSE_ERROR:"MediaMSEError",MEDIA_FORMAT_ERROR:R.Z.FORMAT_ERROR,MEDIA_FORMAT_UNSUPPORTED:R.Z.FORMAT_UNSUPPORTED,MEDIA_CODEC_UNSUPPORTED:R.Z.CODEC_UNSUPPORTED},T=function(){function e(e,t){if(this.TAG="FlvPlayer",this._type="FlvPlayer",this._emitter=new(l()),this._config=o(),"object"==typeof t&&Object.assign(this._config,t),"flv"!==e.type.toLowerCase())throw new A.OC("FlvPlayer requires an flv MediaDataSource input!");!0===e.isLive&&(this._config.isLive=!0),this.e={onvLoadedMetadata:this._onvLoadedMetadata.bind(this),onvSeeking:this._onvSeeking.bind(this),onvCanPlay:this._onvCanPlay.bind(this),onvStalled:this._onvStalled.bind(this),onvProgress:this._onvProgress.bind(this)},self.performance&&self.performance.now?this._now=self.performance.now.bind(self.performance):this._now=Date.now,this._pendingSeekTime=null,this._requestSetTime=!1,this._seekpointRecord=null,this._progressChecker=null,this._mediaDataSource=e,this._mediaElement=null,this._msectl=null,this._transmuxer=null,this._mseSourceOpened=!1,this._hasPendingLoad=!1,this._receivedCanPlay=!1,this._mediaInfo=null,this._statisticsInfo=null;var i=c.Z.chrome&&(c.Z.version.major<50||50===c.Z.version.major&&c.Z.version.build<2661);this._alwaysSeekKeyframe=!!(i||c.Z.msedge||c.Z.msie),this._alwaysSeekKeyframe&&(this._config.accurateSeek=!1)}return e.prototype.destroy=function(){null!=this._progressChecker&&(window.clearInterval(this._progressChecker),this._progressChecker=null),this._transmuxer&&this.unload(),this._mediaElement&&this.detachMediaElement(),this.e=null,this._mediaDataSource=null,this._emitter.removeAllListeners(),this._emitter=null},e.prototype.on=function(e,t){var i=this;e===f.MEDIA_INFO?null!=this._mediaInfo&&Promise.resolve().then((function(){i._emitter.emit(f.MEDIA_INFO,i.mediaInfo)})):e===f.STATISTICS_INFO&&null!=this._statisticsInfo&&Promise.resolve().then((function(){i._emitter.emit(f.STATISTICS_INFO,i.statisticsInfo)})),this._emitter.addListener(e,t)},e.prototype.off=function(e,t){this._emitter.removeListener(e,t)},e.prototype.attachMediaElement=function(e){var t=this;if(this._mediaElement=e,e.addEventListener("loadedmetadata",this.e.onvLoadedMetadata),e.addEventListener("seeking",this.e.onvSeeking),e.addEventListener("canplay",this.e.onvCanPlay),e.addEventListener("stalled",this.e.onvStalled),e.addEventListener("progress",this.e.onvProgress),this._msectl=new L(this._config),this._msectl.on(E.UPDATE_END,this._onmseUpdateEnd.bind(this)),this._msectl.on(E.BUFFER_FULL,this._onmseBufferFull.bind(this)),this._msectl.on(E.SOURCE_OPEN,(function(){t._mseSourceOpened=!0,t._hasPendingLoad&&(t._hasPendingLoad=!1,t.load())})),this._msectl.on(E.ERROR,(function(e){t._emitter.emit(f.ERROR,w.MEDIA_ERROR,O.MEDIA_MSE_ERROR,e)})),this._msectl.attachMediaElement(e),null!=this._pendingSeekTime)try{e.currentTime=this._pendingSeekTime,this._pendingSeekTime=null}catch(e){}},e.prototype.detachMediaElement=function(){this._mediaElement&&(this._msectl.detachMediaElement(),this._mediaElement.removeEventListener("loadedmetadata",this.e.onvLoadedMetadata),this._mediaElement.removeEventListener("seeking",this.e.onvSeeking),this._mediaElement.removeEventListener("canplay",this.e.onvCanPlay),this._mediaElement.removeEventListener("stalled",this.e.onvStalled),this._mediaElement.removeEventListener("progress",this.e.onvProgress),this._mediaElement=null),this._msectl&&(this._msectl.destroy(),this._msectl=null)},e.prototype.load=function(){var e=this;if(!this._mediaElement)throw new A.rT("HTMLMediaElement must be attached before load()!");if(this._transmuxer)throw new A.rT("FlvPlayer.load() has been called, please call unload() first!");this._hasPendingLoad||(this._config.deferLoadAfterSourceOpen&&!1===this._mseSourceOpened?this._hasPendingLoad=!0:(this._mediaElement.readyState>0&&(this._requestSetTime=!0,this._mediaElement.currentTime=0),this._transmuxer=new b(this._mediaDataSource,this._config),this._transmuxer.on(v.Z.INIT_SEGMENT,(function(t,i){e._msectl.appendInitSegment(i)})),this._transmuxer.on(v.Z.MEDIA_SEGMENT,(function(t,i){if(e._msectl.appendMediaSegment(i),e._config.lazyLoad&&!e._config.isLive){var n=e._mediaElement.currentTime;i.info.endDts>=1e3*(n+e._config.lazyLoadMaxDuration)&&null==e._progressChecker&&(d.Z.v(e.TAG,"Maximum buffering duration exceeded, suspend transmuxing task"),e._suspendTransmuxer())}})),this._transmuxer.on(v.Z.LOADING_COMPLETE,(function(){e._msectl.endOfStream(),e._emitter.emit(f.LOADING_COMPLETE)})),this._transmuxer.on(v.Z.RECOVERED_EARLY_EOF,(function(){e._emitter.emit(f.RECOVERED_EARLY_EOF)})),this._transmuxer.on(v.Z.IO_ERROR,(function(t,i){e._emitter.emit(f.ERROR,w.NETWORK_ERROR,t,i)})),this._transmuxer.on(v.Z.DEMUX_ERROR,(function(t,i){e._emitter.emit(f.ERROR,w.MEDIA_ERROR,t,{code:-1,msg:i})})),this._transmuxer.on(v.Z.MEDIA_INFO,(function(t){e._mediaInfo=t,e._emitter.emit(f.MEDIA_INFO,Object.assign({},t))})),this._transmuxer.on(v.Z.METADATA_ARRIVED,(function(t){e._emitter.emit(f.METADATA_ARRIVED,t)})),this._transmuxer.on(v.Z.SCRIPTDATA_ARRIVED,(function(t){e._emitter.emit(f.SCRIPTDATA_ARRIVED,t)})),this._transmuxer.on(v.Z.STATISTICS_INFO,(function(t){e._statisticsInfo=e._fillStatisticsInfo(t),e._emitter.emit(f.STATISTICS_INFO,Object.assign({},e._statisticsInfo))})),this._transmuxer.on(v.Z.RECOMMEND_SEEKPOINT,(function(t){e._mediaElement&&!e._config.accurateSeek&&(e._requestSetTime=!0,e._mediaElement.currentTime=t/1e3)})),this._transmuxer.open()))},e.prototype.unload=function(){this._mediaElement&&this._mediaElement.pause(),this._msectl&&this._msectl.seek(0),this._transmuxer&&(this._transmuxer.close(),this._transmuxer.destroy(),this._transmuxer=null)},e.prototype.play=function(){return this._mediaElement.play()},e.prototype.pause=function(){this._mediaElement.pause()},Object.defineProperty(e.prototype,"type",{get:function(){return this._type},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"buffered",{get:function(){return this._mediaElement.buffered},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"duration",{get:function(){return this._mediaElement.duration},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"volume",{get:function(){return this._mediaElement.volume},set:function(e){this._mediaElement.volume=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"muted",{get:function(){return this._mediaElement.muted},set:function(e){this._mediaElement.muted=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"currentTime",{get:function(){return this._mediaElement?this._mediaElement.currentTime:0},set:function(e){this._mediaElement?this._internalSeek(e):this._pendingSeekTime=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"mediaInfo",{get:function(){return Object.assign({},this._mediaInfo)},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"statisticsInfo",{get:function(){return null==this._statisticsInfo&&(this._statisticsInfo={}),this._statisticsInfo=this._fillStatisticsInfo(this._statisticsInfo),Object.assign({},this._statisticsInfo)},enumerable:!1,configurable:!0}),e.prototype._fillStatisticsInfo=function(e){if(e.playerType=this._type,!(this._mediaElement instanceof HTMLVideoElement))return e;var t=!0,i=0,n=0;if(this._mediaElement.getVideoPlaybackQuality){var r=this._mediaElement.getVideoPlaybackQuality();i=r.totalVideoFrames,n=r.droppedVideoFrames}else null!=this._mediaElement.webkitDecodedFrameCount?(i=this._mediaElement.webkitDecodedFrameCount,n=this._mediaElement.webkitDroppedFrameCount):t=!1;return t&&(e.decodedFrames=i,e.droppedFrames=n),e},e.prototype._onmseUpdateEnd=function(){if(this._config.lazyLoad&&!this._config.isLive){for(var e=this._mediaElement.buffered,t=this._mediaElement.currentTime,i=0,n=0;n<e.length;n++){var r=e.start(n),s=e.end(n);if(r<=t&&t<s){r,i=s;break}}i>=t+this._config.lazyLoadMaxDuration&&null==this._progressChecker&&(d.Z.v(this.TAG,"Maximum buffering duration exceeded, suspend transmuxing task"),this._suspendTransmuxer())}},e.prototype._onmseBufferFull=function(){d.Z.v(this.TAG,"MSE SourceBuffer is full, suspend transmuxing task"),null==this._progressChecker&&this._suspendTransmuxer()},e.prototype._suspendTransmuxer=function(){this._transmuxer&&(this._transmuxer.pause(),null==this._progressChecker&&(this._progressChecker=window.setInterval(this._checkProgressAndResume.bind(this),1e3)))},e.prototype._checkProgressAndResume=function(){for(var e=this._mediaElement.currentTime,t=this._mediaElement.buffered,i=!1,n=0;n<t.length;n++){var r=t.start(n),s=t.end(n);if(e>=r&&e<s){e>=s-this._config.lazyLoadRecoverDuration&&(i=!0);break}}i&&(window.clearInterval(this._progressChecker),this._progressChecker=null,i&&(d.Z.v(this.TAG,"Continue loading from paused position"),this._transmuxer.resume()))},e.prototype._isTimepointBuffered=function(e){for(var t=this._mediaElement.buffered,i=0;i<t.length;i++){var n=t.start(i),r=t.end(i);if(e>=n&&e<r)return!0}return!1},e.prototype._internalSeek=function(e){var t=this._isTimepointBuffered(e),i=!1,n=0;if(e<1&&this._mediaElement.buffered.length>0){var r=this._mediaElement.buffered.start(0);(r<1&&e<r||c.Z.safari)&&(i=!0,n=c.Z.safari?.1:r)}if(i)this._requestSetTime=!0,this._mediaElement.currentTime=n;else if(t){if(this._alwaysSeekKeyframe){var s=this._msectl.getNearestKeyframe(Math.floor(1e3*e));this._requestSetTime=!0,this._mediaElement.currentTime=null!=s?s.dts/1e3:e}else this._requestSetTime=!0,this._mediaElement.currentTime=e;null!=this._progressChecker&&this._checkProgressAndResume()}else null!=this._progressChecker&&(window.clearInterval(this._progressChecker),this._progressChecker=null),this._msectl.seek(e),this._transmuxer.seek(Math.floor(1e3*e)),this._config.accurateSeek&&(this._requestSetTime=!0,this._mediaElement.currentTime=e)},e.prototype._checkAndApplyUnbufferedSeekpoint=function(){if(this._seekpointRecord)if(this._seekpointRecord.recordTime<=this._now()-100){var e=this._mediaElement.currentTime;this._seekpointRecord=null,this._isTimepointBuffered(e)||(null!=this._progressChecker&&(window.clearTimeout(this._progressChecker),this._progressChecker=null),this._msectl.seek(e),this._transmuxer.seek(Math.floor(1e3*e)),this._config.accurateSeek&&(this._requestSetTime=!0,this._mediaElement.currentTime=e))}else window.setTimeout(this._checkAndApplyUnbufferedSeekpoint.bind(this),50)},e.prototype._checkAndResumeStuckPlayback=function(e){var t=this._mediaElement;if(e||!this._receivedCanPlay||t.readyState<2){var i=t.buffered;i.length>0&&t.currentTime<i.start(0)&&(d.Z.w(this.TAG,"Playback seems stuck at "+t.currentTime+", seek to "+i.start(0)),this._requestSetTime=!0,this._mediaElement.currentTime=i.start(0),this._mediaElement.removeEventListener("progress",this.e.onvProgress))}else this._mediaElement.removeEventListener("progress",this.e.onvProgress)},e.prototype._onvLoadedMetadata=function(e){null!=this._pendingSeekTime&&(this._mediaElement.currentTime=this._pendingSeekTime,this._pendingSeekTime=null)},e.prototype._onvSeeking=function(e){var t=this._mediaElement.currentTime,i=this._mediaElement.buffered;if(this._requestSetTime)this._requestSetTime=!1;else{if(t<1&&i.length>0){var n=i.start(0);if(n<1&&t<n||c.Z.safari)return this._requestSetTime=!0,void(this._mediaElement.currentTime=c.Z.safari?.1:n)}if(this._isTimepointBuffered(t)){if(this._alwaysSeekKeyframe){var r=this._msectl.getNearestKeyframe(Math.floor(1e3*t));null!=r&&(this._requestSetTime=!0,this._mediaElement.currentTime=r.dts/1e3)}null!=this._progressChecker&&this._checkProgressAndResume()}else this._seekpointRecord={seekPoint:t,recordTime:this._now()},window.setTimeout(this._checkAndApplyUnbufferedSeekpoint.bind(this),50)}},e.prototype._onvCanPlay=function(e){this._receivedCanPlay=!0,this._mediaElement.removeEventListener("canplay",this.e.onvCanPlay)},e.prototype._onvStalled=function(e){this._checkAndResumeStuckPlayback(!0)},e.prototype._onvProgress=function(e){this._checkAndResumeStuckPlayback()},e}(),C=function(){function e(e,t){if(this.TAG="NativePlayer",this._type="NativePlayer",this._emitter=new(l()),this._config=o(),"object"==typeof t&&Object.assign(this._config,t),"flv"===e.type.toLowerCase())throw new A.OC("NativePlayer does\'t support flv MediaDataSource input!");if(e.hasOwnProperty("segments"))throw new A.OC("NativePlayer("+e.type+") doesn\'t support multipart playback!");this.e={onvLoadedMetadata:this._onvLoadedMetadata.bind(this)},this._pendingSeekTime=null,this._statisticsReporter=null,this._mediaDataSource=e,this._mediaElement=null}return e.prototype.destroy=function(){this._mediaElement&&(this.unload(),this.detachMediaElement()),this.e=null,this._mediaDataSource=null,this._emitter.removeAllListeners(),this._emitter=null},e.prototype.on=function(e,t){var i=this;e===f.MEDIA_INFO?null!=this._mediaElement&&0!==this._mediaElement.readyState&&Promise.resolve().then((function(){i._emitter.emit(f.MEDIA_INFO,i.mediaInfo)})):e===f.STATISTICS_INFO&&null!=this._mediaElement&&0!==this._mediaElement.readyState&&Promise.resolve().then((function(){i._emitter.emit(f.STATISTICS_INFO,i.statisticsInfo)})),this._emitter.addListener(e,t)},e.prototype.off=function(e,t){this._emitter.removeListener(e,t)},e.prototype.attachMediaElement=function(e){if(this._mediaElement=e,e.addEventListener("loadedmetadata",this.e.onvLoadedMetadata),null!=this._pendingSeekTime)try{e.currentTime=this._pendingSeekTime,this._pendingSeekTime=null}catch(e){}},e.prototype.detachMediaElement=function(){this._mediaElement&&(this._mediaElement.src="",this._mediaElement.removeAttribute("src"),this._mediaElement.removeEventListener("loadedmetadata",this.e.onvLoadedMetadata),this._mediaElement=null),null!=this._statisticsReporter&&(window.clearInterval(this._statisticsReporter),this._statisticsReporter=null)},e.prototype.load=function(){if(!this._mediaElement)throw new A.rT("HTMLMediaElement must be attached before load()!");this._mediaElement.src=this._mediaDataSource.url,this._mediaElement.readyState>0&&(this._mediaElement.currentTime=0),this._mediaElement.preload="auto",this._mediaElement.load(),this._statisticsReporter=window.setInterval(this._reportStatisticsInfo.bind(this),this._config.statisticsInfoReportInterval)},e.prototype.unload=function(){this._mediaElement&&(this._mediaElement.src="",this._mediaElement.removeAttribute("src")),null!=this._statisticsReporter&&(window.clearInterval(this._statisticsReporter),this._statisticsReporter=null)},e.prototype.play=function(){return this._mediaElement.play()},e.prototype.pause=function(){this._mediaElement.pause()},Object.defineProperty(e.prototype,"type",{get:function(){return this._type},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"buffered",{get:function(){return this._mediaElement.buffered},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"duration",{get:function(){return this._mediaElement.duration},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"volume",{get:function(){return this._mediaElement.volume},set:function(e){this._mediaElement.volume=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"muted",{get:function(){return this._mediaElement.muted},set:function(e){this._mediaElement.muted=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"currentTime",{get:function(){return this._mediaElement?this._mediaElement.currentTime:0},set:function(e){this._mediaElement?this._mediaElement.currentTime=e:this._pendingSeekTime=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"mediaInfo",{get:function(){var e={mimeType:(this._mediaElement instanceof HTMLAudioElement?"audio/":"video/")+this._mediaDataSource.type};return this._mediaElement&&(e.duration=Math.floor(1e3*this._mediaElement.duration),this._mediaElement instanceof HTMLVideoElement&&(e.width=this._mediaElement.videoWidth,e.height=this._mediaElement.videoHeight)),e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"statisticsInfo",{get:function(){var e={playerType:this._type,url:this._mediaDataSource.url};if(!(this._mediaElement instanceof HTMLVideoElement))return e;var t=!0,i=0,n=0;if(this._mediaElement.getVideoPlaybackQuality){var r=this._mediaElement.getVideoPlaybackQuality();i=r.totalVideoFrames,n=r.droppedVideoFrames}else null!=this._mediaElement.webkitDecodedFrameCount?(i=this._mediaElement.webkitDecodedFrameCount,n=this._mediaElement.webkitDroppedFrameCount):t=!1;return t&&(e.decodedFrames=i,e.droppedFrames=n),e},enumerable:!1,configurable:!0}),e.prototype._onvLoadedMetadata=function(e){null!=this._pendingSeekTime&&(this._mediaElement.currentTime=this._pendingSeekTime,this._pendingSeekTime=null),this._emitter.emit(f.MEDIA_INFO,this.mediaInfo)},e.prototype._reportStatisticsInfo=function(){this._emitter.emit(f.STATISTICS_INFO,this.statisticsInfo)},e}();n.Z.install();var k={createPlayer:function(e,t){var i=e;if(null==i||"object"!=typeof i)throw new A.OC("MediaDataSource must be an javascript object!");if(!i.hasOwnProperty("type"))throw new A.OC("MediaDataSource must has type field to indicate video file type!");switch(i.type){case"flv":return new T(i,t);default:return new C(i,t)}},isSupported:function(){return a.supportMSEH264Playback()},getFeatureList:function(){return a.getFeatureList()}};k.BaseLoader=h.fp,k.LoaderStatus=h.GM,k.LoaderErrors=h.nm,k.Events=f,k.ErrorTypes=w,k.ErrorDetails=O,k.FlvPlayer=T,k.NativePlayer=C,k.LoggingControl=m.Z,Object.defineProperty(k,"version",{enumerable:!0,get:function(){return"1.6.2"}});var D=k},324:function(e,t,i){e.exports=i(60).default},191:function(e,t,i){"use strict";i.d(t,{Z:function(){return y}});var n,r=i(300),s=function(){function e(){this._firstCheckpoint=0,this._lastCheckpoint=0,this._intervalBytes=0,this._totalBytes=0,this._lastSecondBytes=0,self.performance&&self.performance.now?this._now=self.performance.now.bind(self.performance):this._now=Date.now}return e.prototype.reset=function(){this._firstCheckpoint=this._lastCheckpoint=0,this._totalBytes=this._intervalBytes=0,this._lastSecondBytes=0},e.prototype.addBytes=function(e){0===this._firstCheckpoint?(this._firstCheckpoint=this._now(),this._lastCheckpoint=this._firstCheckpoint,this._intervalBytes+=e,this._totalBytes+=e):this._now()-this._lastCheckpoint<1e3?(this._intervalBytes+=e,this._totalBytes+=e):(this._lastSecondBytes=this._intervalBytes,this._intervalBytes=e,this._totalBytes+=e,this._lastCheckpoint=this._now())},Object.defineProperty(e.prototype,"currentKBps",{get:function(){this.addBytes(0);var e=(this._now()-this._lastCheckpoint)/1e3;return 0==e&&(e=1),this._intervalBytes/e/1024},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"lastSecondKBps",{get:function(){return this.addBytes(0),0!==this._lastSecondBytes?this._lastSecondBytes/1024:this._now()-this._lastCheckpoint>=500?this.currentKBps:0},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"averageKBps",{get:function(){var e=(this._now()-this._firstCheckpoint)/1e3;return this._totalBytes/e/1024},enumerable:!1,configurable:!0}),e}(),o=i(939),a=i(538),h=i(29),u=(n=function(e,t){return(n=Object.setPrototypeOf||{__proto__:[]}instanceof Array&&function(e,t){e.__proto__=t}||function(e,t){for(var i in t)Object.prototype.hasOwnProperty.call(t,i)&&(e[i]=t[i])})(e,t)},function(e,t){if("function"!=typeof t&&null!==t)throw new TypeError("Class extends value "+String(t)+" is not a constructor or null");function i(){this.constructor=e}n(e,t),e.prototype=null===t?Object.create(t):(i.prototype=t.prototype,new i)}),l=function(e){function t(t,i){var n=e.call(this,"fetch-stream-loader")||this;return n.TAG="FetchStreamLoader",n._seekHandler=t,n._config=i,n._needStash=!0,n._requestAbort=!1,n._contentLength=null,n._receivedLength=0,n}return u(t,e),t.isSupported=function(){try{var e=a.Z.msedge&&a.Z.version.minor>=15048,t=!a.Z.msedge||e;return self.fetch&&self.ReadableStream&&t}catch(e){return!1}},t.prototype.destroy=function(){this.isWorking()&&this.abort(),e.prototype.destroy.call(this)},t.prototype.open=function(e,t){var i=this;this._dataSource=e,this._range=t;var n=e.url;this._config.reuseRedirectedURL&&null!=e.redirectedURL&&(n=e.redirectedURL);var r=this._seekHandler.getConfig(n,t),s=new self.Headers;if("object"==typeof r.headers){var a=r.headers;for(var u in a)a.hasOwnProperty(u)&&s.append(u,a[u])}var l={method:"GET",headers:s,mode:"cors",cache:"default",referrerPolicy:"no-referrer-when-downgrade"};if("object"==typeof this._config.headers)for(var u in this._config.headers)s.append(u,this._config.headers[u]);!1===e.cors&&(l.mode="same-origin"),e.withCredentials&&(l.credentials="include"),e.referrerPolicy&&(l.referrerPolicy=e.referrerPolicy),self.AbortController&&(this._abortController=new self.AbortController,l.signal=this._abortController.signal),this._status=o.GM.kConnecting,self.fetch(r.url,l).then((function(e){if(i._requestAbort)return i._status=o.GM.kIdle,void e.body.cancel();if(e.ok&&e.status>=200&&e.status<=299){if(e.url!==r.url&&i._onURLRedirect){var t=i._seekHandler.removeURLParameters(e.url);i._onURLRedirect(t)}var n=e.headers.get("Content-Length");return null!=n&&(i._contentLength=parseInt(n),0!==i._contentLength&&i._onContentLengthKnown&&i._onContentLengthKnown(i._contentLength)),i._pump.call(i,e.body.getReader())}if(i._status=o.GM.kError,!i._onError)throw new h.OZ("FetchStreamLoader: Http code invalid, "+e.status+" "+e.statusText);i._onError(o.nm.HTTP_STATUS_CODE_INVALID,{code:e.status,msg:e.statusText})})).catch((function(e){if(!i._abortController||!i._abortController.signal.aborted){if(i._status=o.GM.kError,!i._onError)throw e;i._onError(o.nm.EXCEPTION,{code:-1,msg:e.message})}}))},t.prototype.abort=function(){if(this._requestAbort=!0,(this._status!==o.GM.kBuffering||!a.Z.chrome)&&this._abortController)try{this._abortController.abort()}catch(e){}},t.prototype._pump=function(e){var t=this;return e.read().then((function(i){if(i.done)if(null!==t._contentLength&&t._receivedLength<t._contentLength){t._status=o.GM.kError;var n=o.nm.EARLY_EOF,r={code:-1,msg:"Fetch stream meet Early-EOF"};if(!t._onError)throw new h.OZ(r.msg);t._onError(n,r)}else t._status=o.GM.kComplete,t._onComplete&&t._onComplete(t._range.from,t._range.from+t._receivedLength-1);else{if(t._abortController&&t._abortController.signal.aborted)return void(t._status=o.GM.kComplete);if(!0===t._requestAbort)return t._status=o.GM.kComplete,e.cancel();t._status=o.GM.kBuffering;var s=i.value.buffer,a=t._range.from+t._receivedLength;t._receivedLength+=s.byteLength,t._onDataArrival&&t._onDataArrival(s,a,t._receivedLength),t._pump(e)}})).catch((function(e){if(t._abortController&&t._abortController.signal.aborted)t._status=o.GM.kComplete;else if(11!==e.code||!a.Z.msedge){t._status=o.GM.kError;var i=0,n=null;if(19!==e.code&&"network error"!==e.message||!(null===t._contentLength||null!==t._contentLength&&t._receivedLength<t._contentLength)?(i=o.nm.EXCEPTION,n={code:e.code,msg:e.message}):(i=o.nm.EARLY_EOF,n={code:e.code,msg:"Fetch stream meet Early-EOF"}),!t._onError)throw new h.OZ(n.msg);t._onError(i,n)}}))},t}(o.fp),d=function(){var e=function(t,i){return(e=Object.setPrototypeOf||{__proto__:[]}instanceof Array&&function(e,t){e.__proto__=t}||function(e,t){for(var i in t)Object.prototype.hasOwnProperty.call(t,i)&&(e[i]=t[i])})(t,i)};return function(t,i){if("function"!=typeof i&&null!==i)throw new TypeError("Class extends value "+String(i)+" is not a constructor or null");function n(){this.constructor=t}e(t,i),t.prototype=null===i?Object.create(i):(n.prototype=i.prototype,new n)}}(),c=function(e){function t(t,i){var n=e.call(this,"xhr-moz-chunked-loader")||this;return n.TAG="MozChunkedLoader",n._seekHandler=t,n._config=i,n._needStash=!0,n._xhr=null,n._requestAbort=!1,n._contentLength=null,n._receivedLength=0,n}return d(t,e),t.isSupported=function(){try{var e=new XMLHttpRequest;return e.open("GET","https://example.com",!0),e.responseType="moz-chunked-arraybuffer","moz-chunked-arraybuffer"===e.responseType}catch(e){return r.Z.w("MozChunkedLoader",e.message),!1}},t.prototype.destroy=function(){this.isWorking()&&this.abort(),this._xhr&&(this._xhr.onreadystatechange=null,this._xhr.onprogress=null,this._xhr.onloadend=null,this._xhr.onerror=null,this._xhr=null),e.prototype.destroy.call(this)},t.prototype.open=function(e,t){this._dataSource=e,this._range=t;var i=e.url;this._config.reuseRedirectedURL&&null!=e.redirectedURL&&(i=e.redirectedURL);var n=this._seekHandler.getConfig(i,t);this._requestURL=n.url;var r=this._xhr=new XMLHttpRequest;if(r.open("GET",n.url,!0),r.responseType="moz-chunked-arraybuffer",r.onreadystatechange=this._onReadyStateChange.bind(this),r.onprogress=this._onProgress.bind(this),r.onloadend=this._onLoadEnd.bind(this),r.onerror=this._onXhrError.bind(this),e.withCredentials&&(r.withCredentials=!0),"object"==typeof n.headers){var s=n.headers;for(var a in s)s.hasOwnProperty(a)&&r.setRequestHeader(a,s[a])}if("object"==typeof this._config.headers){s=this._config.headers;for(var a in s)s.hasOwnProperty(a)&&r.setRequestHeader(a,s[a])}this._status=o.GM.kConnecting,r.send()},t.prototype.abort=function(){this._requestAbort=!0,this._xhr&&this._xhr.abort(),this._status=o.GM.kComplete},t.prototype._onReadyStateChange=function(e){var t=e.target;if(2===t.readyState){if(null!=t.responseURL&&t.responseURL!==this._requestURL&&this._onURLRedirect){var i=this._seekHandler.removeURLParameters(t.responseURL);this._onURLRedirect(i)}if(0!==t.status&&(t.status<200||t.status>299)){if(this._status=o.GM.kError,!this._onError)throw new h.OZ("MozChunkedLoader: Http code invalid, "+t.status+" "+t.statusText);this._onError(o.nm.HTTP_STATUS_CODE_INVALID,{code:t.status,msg:t.statusText})}else this._status=o.GM.kBuffering}},t.prototype._onProgress=function(e){if(this._status!==o.GM.kError){null===this._contentLength&&null!==e.total&&0!==e.total&&(this._contentLength=e.total,this._onContentLengthKnown&&this._onContentLengthKnown(this._contentLength));var t=e.target.response,i=this._range.from+this._receivedLength;this._receivedLength+=t.byteLength,this._onDataArrival&&this._onDataArrival(t,i,this._receivedLength)}},t.prototype._onLoadEnd=function(e){!0!==this._requestAbort?this._status!==o.GM.kError&&(this._status=o.GM.kComplete,this._onComplete&&this._onComplete(this._range.from,this._range.from+this._receivedLength-1)):this._requestAbort=!1},t.prototype._onXhrError=function(e){this._status=o.GM.kError;var t=0,i=null;if(this._contentLength&&e.loaded<this._contentLength?(t=o.nm.EARLY_EOF,i={code:-1,msg:"Moz-Chunked stream meet Early-Eof"}):(t=o.nm.EXCEPTION,i={code:-1,msg:e.constructor.name+" "+e.type}),!this._onError)throw new h.OZ(i.msg);this._onError(t,i)},t}(o.fp),f=function(){var e=function(t,i){return(e=Object.setPrototypeOf||{__proto__:[]}instanceof Array&&function(e,t){e.__proto__=t}||function(e,t){for(var i in t)Object.prototype.hasOwnProperty.call(t,i)&&(e[i]=t[i])})(t,i)};return function(t,i){if("function"!=typeof i&&null!==i)throw new TypeError("Class extends value "+String(i)+" is not a constructor or null");function n(){this.constructor=t}e(t,i),t.prototype=null===i?Object.create(i):(n.prototype=i.prototype,new n)}}(),_=function(e){function t(t,i){var n=e.call(this,"xhr-range-loader")||this;return n.TAG="RangeLoader",n._seekHandler=t,n._config=i,n._needStash=!1,n._chunkSizeKBList=[128,256,384,512,768,1024,1536,2048,3072,4096,5120,6144,7168,8192],n._currentChunkSizeKB=384,n._currentSpeedNormalized=0,n._zeroSpeedChunkCount=0,n._xhr=null,n._speedSampler=new s,n._requestAbort=!1,n._waitForTotalLength=!1,n._totalLengthReceived=!1,n._currentRequestURL=null,n._currentRedirectedURL=null,n._currentRequestRange=null,n._totalLength=null,n._contentLength=null,n._receivedLength=0,n._lastTimeLoaded=0,n}return f(t,e),t.isSupported=function(){try{var e=new XMLHttpRequest;return e.open("GET","https://example.com",!0),e.responseType="arraybuffer","arraybuffer"===e.responseType}catch(e){return r.Z.w("RangeLoader",e.message),!1}},t.prototype.destroy=function(){this.isWorking()&&this.abort(),this._xhr&&(this._xhr.onreadystatechange=null,this._xhr.onprogress=null,this._xhr.onload=null,this._xhr.onerror=null,this._xhr=null),e.prototype.destroy.call(this)},Object.defineProperty(t.prototype,"currentSpeed",{get:function(){return this._speedSampler.lastSecondKBps},enumerable:!1,configurable:!0}),t.prototype.open=function(e,t){this._dataSource=e,this._range=t,this._status=o.GM.kConnecting;var i=!1;null!=this._dataSource.filesize&&0!==this._dataSource.filesize&&(i=!0,this._totalLength=this._dataSource.filesize),this._totalLengthReceived||i?this._openSubRange():(this._waitForTotalLength=!0,this._internalOpen(this._dataSource,{from:0,to:-1}))},t.prototype._openSubRange=function(){var e=1024*this._currentChunkSizeKB,t=this._range.from+this._receivedLength,i=t+e;null!=this._contentLength&&i-this._range.from>=this._contentLength&&(i=this._range.from+this._contentLength-1),this._currentRequestRange={from:t,to:i},this._internalOpen(this._dataSource,this._currentRequestRange)},t.prototype._internalOpen=function(e,t){this._lastTimeLoaded=0;var i=e.url;this._config.reuseRedirectedURL&&(null!=this._currentRedirectedURL?i=this._currentRedirectedURL:null!=e.redirectedURL&&(i=e.redirectedURL));var n=this._seekHandler.getConfig(i,t);this._currentRequestURL=n.url;var r=this._xhr=new XMLHttpRequest;if(r.open("GET",n.url,!0),r.responseType="arraybuffer",r.onreadystatechange=this._onReadyStateChange.bind(this),r.onprogress=this._onProgress.bind(this),r.onload=this._onLoad.bind(this),r.onerror=this._onXhrError.bind(this),e.withCredentials&&(r.withCredentials=!0),"object"==typeof n.headers){var s=n.headers;for(var o in s)s.hasOwnProperty(o)&&r.setRequestHeader(o,s[o])}if("object"==typeof this._config.headers){s=this._config.headers;for(var o in s)s.hasOwnProperty(o)&&r.setRequestHeader(o,s[o])}r.send()},t.prototype.abort=function(){this._requestAbort=!0,this._internalAbort(),this._status=o.GM.kComplete},t.prototype._internalAbort=function(){this._xhr&&(this._xhr.onreadystatechange=null,this._xhr.onprogress=null,this._xhr.onload=null,this._xhr.onerror=null,this._xhr.abort(),this._xhr=null)},t.prototype._onReadyStateChange=function(e){var t=e.target;if(2===t.readyState){if(null!=t.responseURL){var i=this._seekHandler.removeURLParameters(t.responseURL);t.responseURL!==this._currentRequestURL&&i!==this._currentRedirectedURL&&(this._currentRedirectedURL=i,this._onURLRedirect&&this._onURLRedirect(i))}if(t.status>=200&&t.status<=299){if(this._waitForTotalLength)return;this._status=o.GM.kBuffering}else{if(this._status=o.GM.kError,!this._onError)throw new h.OZ("RangeLoader: Http code invalid, "+t.status+" "+t.statusText);this._onError(o.nm.HTTP_STATUS_CODE_INVALID,{code:t.status,msg:t.statusText})}}},t.prototype._onProgress=function(e){if(this._status!==o.GM.kError){if(null===this._contentLength){var t=!1;if(this._waitForTotalLength){this._waitForTotalLength=!1,this._totalLengthReceived=!0,t=!0;var i=e.total;this._internalAbort(),null!=i&0!==i&&(this._totalLength=i)}if(-1===this._range.to?this._contentLength=this._totalLength-this._range.from:this._contentLength=this._range.to-this._range.from+1,t)return void this._openSubRange();this._onContentLengthKnown&&this._onContentLengthKnown(this._contentLength)}var n=e.loaded-this._lastTimeLoaded;this._lastTimeLoaded=e.loaded,this._speedSampler.addBytes(n)}},t.prototype._normalizeSpeed=function(e){var t=this._chunkSizeKBList,i=t.length-1,n=0,r=0,s=i;if(e<t[0])return t[0];for(;r<=s;){if((n=r+Math.floor((s-r)/2))===i||e>=t[n]&&e<t[n+1])return t[n];t[n]<e?r=n+1:s=n-1}},t.prototype._onLoad=function(e){if(this._status!==o.GM.kError)if(this._waitForTotalLength)this._waitForTotalLength=!1;else{this._lastTimeLoaded=0;var t=this._speedSampler.lastSecondKBps;if(0===t&&(this._zeroSpeedChunkCount++,this._zeroSpeedChunkCount>=3&&(t=this._speedSampler.currentKBps)),0!==t){var i=this._normalizeSpeed(t);this._currentSpeedNormalized!==i&&(this._currentSpeedNormalized=i,this._currentChunkSizeKB=i)}var n=e.target.response,r=this._range.from+this._receivedLength;this._receivedLength+=n.byteLength;var s=!1;null!=this._contentLength&&this._receivedLength<this._contentLength?this._openSubRange():s=!0,this._onDataArrival&&this._onDataArrival(n,r,this._receivedLength),s&&(this._status=o.GM.kComplete,this._onComplete&&this._onComplete(this._range.from,this._range.from+this._receivedLength-1))}},t.prototype._onXhrError=function(e){this._status=o.GM.kError;var t=0,i=null;if(this._contentLength&&this._receivedLength>0&&this._receivedLength<this._contentLength?(t=o.nm.EARLY_EOF,i={code:-1,msg:"RangeLoader meet Early-Eof"}):(t=o.nm.EXCEPTION,i={code:-1,msg:e.constructor.name+" "+e.type}),!this._onError)throw new h.OZ(i.msg);this._onError(t,i)},t}(o.fp),p=function(){var e=function(t,i){return(e=Object.setPrototypeOf||{__proto__:[]}instanceof Array&&function(e,t){e.__proto__=t}||function(e,t){for(var i in t)Object.prototype.hasOwnProperty.call(t,i)&&(e[i]=t[i])})(t,i)};return function(t,i){if("function"!=typeof i&&null!==i)throw new TypeError("Class extends value "+String(i)+" is not a constructor or null");function n(){this.constructor=t}e(t,i),t.prototype=null===i?Object.create(i):(n.prototype=i.prototype,new n)}}(),m=function(e){function t(){var t=e.call(this,"websocket-loader")||this;return t.TAG="WebSocketLoader",t._needStash=!0,t._ws=null,t._requestAbort=!1,t._receivedLength=0,t}return p(t,e),t.isSupported=function(){try{return void 0!==self.WebSocket}catch(e){return!1}},t.prototype.destroy=function(){this._ws&&this.abort(),e.prototype.destroy.call(this)},t.prototype.open=function(e){try{var t=this._ws=new self.WebSocket(e.url);t.binaryType="arraybuffer",t.onopen=this._onWebSocketOpen.bind(this),t.onclose=this._onWebSocketClose.bind(this),t.onmessage=this._onWebSocketMessage.bind(this),t.onerror=this._onWebSocketError.bind(this),this._status=o.GM.kConnecting}catch(e){this._status=o.GM.kError;var i={code:e.code,msg:e.message};if(!this._onError)throw new h.OZ(i.msg);this._onError(o.nm.EXCEPTION,i)}},t.prototype.abort=function(){var e=this._ws;!e||0!==e.readyState&&1!==e.readyState||(this._requestAbort=!0,e.close()),this._ws=null,this._status=o.GM.kComplete},t.prototype._onWebSocketOpen=function(e){this._status=o.GM.kBuffering},t.prototype._onWebSocketClose=function(e){!0!==this._requestAbort?(this._status=o.GM.kComplete,this._onComplete&&this._onComplete(0,this._receivedLength-1)):this._requestAbort=!1},t.prototype._onWebSocketMessage=function(e){var t=this;if(e.data instanceof ArrayBuffer)this._dispatchArrayBuffer(e.data);else if(e.data instanceof Blob){var i=new FileReader;i.onload=function(){t._dispatchArrayBuffer(i.result)},i.readAsArrayBuffer(e.data)}else{this._status=o.GM.kError;var n={code:-1,msg:"Unsupported WebSocket message type: "+e.data.constructor.name};if(!this._onError)throw new h.OZ(n.msg);this._onError(o.nm.EXCEPTION,n)}},t.prototype._dispatchArrayBuffer=function(e){var t=e,i=this._receivedLength;this._receivedLength+=t.byteLength,this._onDataArrival&&this._onDataArrival(t,i,this._receivedLength)},t.prototype._onWebSocketError=function(e){this._status=o.GM.kError;var t={code:e.code,msg:e.message};if(!this._onError)throw new h.OZ(t.msg);this._onError(o.nm.EXCEPTION,t)},t}(o.fp),g=function(){function e(e){this._zeroStart=e||!1}return e.prototype.getConfig=function(e,t){var i={};if(0!==t.from||-1!==t.to){var n=void 0;n=-1!==t.to?"bytes="+t.from.toString()+"-"+t.to.toString():"bytes="+t.from.toString()+"-",i.Range=n}else this._zeroStart&&(i.Range="bytes=0-");return{url:e,headers:i}},e.prototype.removeURLParameters=function(e){return e},e}(),v=function(){function e(e,t){this._startName=e,this._endName=t}return e.prototype.getConfig=function(e,t){var i=e;if(0!==t.from||-1!==t.to){var n=!0;-1===i.indexOf("?")&&(i+="?",n=!1),n&&(i+="&"),i+=this._startName+"="+t.from.toString(),-1!==t.to&&(i+="&"+this._endName+"="+t.to.toString())}return{url:i,headers:{}}},e.prototype.removeURLParameters=function(e){var t=e.split("?")[0],i=void 0,n=e.indexOf("?");-1!==n&&(i=e.substring(n+1));var r="";if(null!=i&&i.length>0)for(var s=i.split("&"),o=0;o<s.length;o++){var a=s[o].split("="),h=o>0;a[0]!==this._startName&&a[0]!==this._endName&&(h&&(r+="&"),r+=s[o])}return 0===r.length?t:t+"?"+r},e}(),y=function(){function e(e,t,i){this.TAG="IOController",this._config=t,this._extraData=i,this._stashInitialSize=393216,null!=t.stashInitialSize&&t.stashInitialSize>0&&(this._stashInitialSize=t.stashInitialSize),this._stashUsed=0,this._stashSize=this._stashInitialSize,this._bufferSize=3145728,this._stashBuffer=new ArrayBuffer(this._bufferSize),this._stashByteStart=0,this._enableStash=!0,!1===t.enableStashBuffer&&(this._enableStash=!1),this._loader=null,this._loaderClass=null,this._seekHandler=null,this._dataSource=e,this._isWebSocketURL=/wss?:\\/\\/(.+?)/.test(e.url),this._refTotalLength=e.filesize?e.filesize:null,this._totalLength=this._refTotalLength,this._fullRequestFlag=!1,this._currentRange=null,this._redirectedURL=null,this._speedNormalized=0,this._speedSampler=new s,this._speedNormalizeList=[64,128,256,384,512,768,1024,1536,2048,3072,4096],this._isEarlyEofReconnecting=!1,this._paused=!1,this._resumeFrom=0,this._onDataArrival=null,this._onSeeked=null,this._onError=null,this._onComplete=null,this._onRedirect=null,this._onRecoveredEarlyEof=null,this._selectSeekHandler(),this._selectLoader(),this._createLoader()}return e.prototype.destroy=function(){this._loader.isWorking()&&this._loader.abort(),this._loader.destroy(),this._loader=null,this._loaderClass=null,this._dataSource=null,this._stashBuffer=null,this._stashUsed=this._stashSize=this._bufferSize=this._stashByteStart=0,this._currentRange=null,this._speedSampler=null,this._isEarlyEofReconnecting=!1,this._onDataArrival=null,this._onSeeked=null,this._onError=null,this._onComplete=null,this._onRedirect=null,this._onRecoveredEarlyEof=null,this._extraData=null},e.prototype.isWorking=function(){return this._loader&&this._loader.isWorking()&&!this._paused},e.prototype.isPaused=function(){return this._paused},Object.defineProperty(e.prototype,"status",{get:function(){return this._loader.status},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"extraData",{get:function(){return this._extraData},set:function(e){this._extraData=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onDataArrival",{get:function(){return this._onDataArrival},set:function(e){this._onDataArrival=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onSeeked",{get:function(){return this._onSeeked},set:function(e){this._onSeeked=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onError",{get:function(){return this._onError},set:function(e){this._onError=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onComplete",{get:function(){return this._onComplete},set:function(e){this._onComplete=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onRedirect",{get:function(){return this._onRedirect},set:function(e){this._onRedirect=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onRecoveredEarlyEof",{get:function(){return this._onRecoveredEarlyEof},set:function(e){this._onRecoveredEarlyEof=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"currentURL",{get:function(){return this._dataSource.url},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"hasRedirect",{get:function(){return null!=this._redirectedURL||null!=this._dataSource.redirectedURL},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"currentRedirectedURL",{get:function(){return this._redirectedURL||this._dataSource.redirectedURL},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"currentSpeed",{get:function(){return this._loaderClass===_?this._loader.currentSpeed:this._speedSampler.lastSecondKBps},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"loaderType",{get:function(){return this._loader.type},enumerable:!1,configurable:!0}),e.prototype._selectSeekHandler=function(){var e=this._config;if("range"===e.seekType)this._seekHandler=new g(this._config.rangeLoadZeroStart);else if("param"===e.seekType){var t=e.seekParamStart||"bstart",i=e.seekParamEnd||"bend";this._seekHandler=new v(t,i)}else{if("custom"!==e.seekType)throw new h.OC("Invalid seekType in config: "+e.seekType);if("function"!=typeof e.customSeekHandler)throw new h.OC("Custom seekType specified in config but invalid customSeekHandler!");this._seekHandler=new e.customSeekHandler}},e.prototype._selectLoader=function(){if(null!=this._config.customLoader)this._loaderClass=this._config.customLoader;else if(this._isWebSocketURL)this._loaderClass=m;else if(l.isSupported())this._loaderClass=l;else if(c.isSupported())this._loaderClass=c;else{if(!_.isSupported())throw new h.OZ("Your browser doesn\'t support xhr with arraybuffer responseType!");this._loaderClass=_}},e.prototype._createLoader=function(){this._loader=new this._loaderClass(this._seekHandler,this._config),!1===this._loader.needStashBuffer&&(this._enableStash=!1),this._loader.onContentLengthKnown=this._onContentLengthKnown.bind(this),this._loader.onURLRedirect=this._onURLRedirect.bind(this),this._loader.onDataArrival=this._onLoaderChunkArrival.bind(this),this._loader.onComplete=this._onLoaderComplete.bind(this),this._loader.onError=this._onLoaderError.bind(this)},e.prototype.open=function(e){this._currentRange={from:0,to:-1},e&&(this._currentRange.from=e),this._speedSampler.reset(),e||(this._fullRequestFlag=!0),this._loader.open(this._dataSource,Object.assign({},this._currentRange))},e.prototype.abort=function(){this._loader.abort(),this._paused&&(this._paused=!1,this._resumeFrom=0)},e.prototype.pause=function(){this.isWorking()&&(this._loader.abort(),0!==this._stashUsed?(this._resumeFrom=this._stashByteStart,this._currentRange.to=this._stashByteStart-1):this._resumeFrom=this._currentRange.to+1,this._stashUsed=0,this._stashByteStart=0,this._paused=!0)},e.prototype.resume=function(){if(this._paused){this._paused=!1;var e=this._resumeFrom;this._resumeFrom=0,this._internalSeek(e,!0)}},e.prototype.seek=function(e){this._paused=!1,this._stashUsed=0,this._stashByteStart=0,this._internalSeek(e,!0)},e.prototype._internalSeek=function(e,t){this._loader.isWorking()&&this._loader.abort(),this._flushStashBuffer(t),this._loader.destroy(),this._loader=null;var i={from:e,to:-1};this._currentRange={from:i.from,to:-1},this._speedSampler.reset(),this._stashSize=this._stashInitialSize,this._createLoader(),this._loader.open(this._dataSource,i),this._onSeeked&&this._onSeeked()},e.prototype.updateUrl=function(e){if(!e||"string"!=typeof e||0===e.length)throw new h.OC("Url must be a non-empty string!");this._dataSource.url=e},e.prototype._expandBuffer=function(e){for(var t=this._stashSize;t+1048576<e;)t*=2;if((t+=1048576)!==this._bufferSize){var i=new ArrayBuffer(t);if(this._stashUsed>0){var n=new Uint8Array(this._stashBuffer,0,this._stashUsed);new Uint8Array(i,0,t).set(n,0)}this._stashBuffer=i,this._bufferSize=t}},e.prototype._normalizeSpeed=function(e){var t=this._speedNormalizeList,i=t.length-1,n=0,r=0,s=i;if(e<t[0])return t[0];for(;r<=s;){if((n=r+Math.floor((s-r)/2))===i||e>=t[n]&&e<t[n+1])return t[n];t[n]<e?r=n+1:s=n-1}},e.prototype._adjustStashSize=function(e){var t=0;(t=this._config.isLive||e<512?e:e>=512&&e<=1024?Math.floor(1.5*e):2*e)>8192&&(t=8192);var i=1024*t+1048576;this._bufferSize<i&&this._expandBuffer(i),this._stashSize=1024*t},e.prototype._dispatchChunks=function(e,t){return this._currentRange.to=t+e.byteLength-1,this._onDataArrival(e,t)},e.prototype._onURLRedirect=function(e){this._redirectedURL=e,this._onRedirect&&this._onRedirect(e)},e.prototype._onContentLengthKnown=function(e){e&&this._fullRequestFlag&&(this._totalLength=e,this._fullRequestFlag=!1)},e.prototype._onLoaderChunkArrival=function(e,t,i){if(!this._onDataArrival)throw new h.rT("IOController: No existing consumer (onDataArrival) callback!");if(!this._paused){this._isEarlyEofReconnecting&&(this._isEarlyEofReconnecting=!1,this._onRecoveredEarlyEof&&this._onRecoveredEarlyEof()),this._speedSampler.addBytes(e.byteLength);var n=this._speedSampler.lastSecondKBps;if(0!==n){var r=this._normalizeSpeed(n);this._speedNormalized!==r&&(this._speedNormalized=r,this._adjustStashSize(r))}if(this._enableStash)if(0===this._stashUsed&&0===this._stashByteStart&&(this._stashByteStart=t),this._stashUsed+e.byteLength<=this._stashSize){(a=new Uint8Array(this._stashBuffer,0,this._stashSize)).set(new Uint8Array(e),this._stashUsed),this._stashUsed+=e.byteLength}else{a=new Uint8Array(this._stashBuffer,0,this._bufferSize);if(this._stashUsed>0){var s=this._stashBuffer.slice(0,this._stashUsed);if((u=this._dispatchChunks(s,this._stashByteStart))<s.byteLength){if(u>0){l=new Uint8Array(s,u);a.set(l,0),this._stashUsed=l.byteLength,this._stashByteStart+=u}}else this._stashUsed=0,this._stashByteStart+=u;this._stashUsed+e.byteLength>this._bufferSize&&(this._expandBuffer(this._stashUsed+e.byteLength),a=new Uint8Array(this._stashBuffer,0,this._bufferSize)),a.set(new Uint8Array(e),this._stashUsed),this._stashUsed+=e.byteLength}else{if((u=this._dispatchChunks(e,t))<e.byteLength)(o=e.byteLength-u)>this._bufferSize&&(this._expandBuffer(o),a=new Uint8Array(this._stashBuffer,0,this._bufferSize)),a.set(new Uint8Array(e,u),0),this._stashUsed+=o,this._stashByteStart=t+u}}else if(0===this._stashUsed){var o;if((u=this._dispatchChunks(e,t))<e.byteLength)(o=e.byteLength-u)>this._bufferSize&&this._expandBuffer(o),(a=new Uint8Array(this._stashBuffer,0,this._bufferSize)).set(new Uint8Array(e,u),0),this._stashUsed+=o,this._stashByteStart=t+u}else{var a,u;if(this._stashUsed+e.byteLength>this._bufferSize&&this._expandBuffer(this._stashUsed+e.byteLength),(a=new Uint8Array(this._stashBuffer,0,this._bufferSize)).set(new Uint8Array(e),this._stashUsed),this._stashUsed+=e.byteLength,(u=this._dispatchChunks(this._stashBuffer.slice(0,this._stashUsed),this._stashByteStart))<this._stashUsed&&u>0){var l=new Uint8Array(this._stashBuffer,u);a.set(l,0)}this._stashUsed-=u,this._stashByteStart+=u}}},e.prototype._flushStashBuffer=function(e){if(this._stashUsed>0){var t=this._stashBuffer.slice(0,this._stashUsed),i=this._dispatchChunks(t,this._stashByteStart),n=t.byteLength-i;if(i<t.byteLength){if(!e){if(i>0){var s=new Uint8Array(this._stashBuffer,0,this._bufferSize),o=new Uint8Array(t,i);s.set(o,0),this._stashUsed=o.byteLength,this._stashByteStart+=i}return 0}r.Z.w(this.TAG,n+" bytes unconsumed data remain when flush buffer, dropped")}return this._stashUsed=0,this._stashByteStart=0,n}return 0},e.prototype._onLoaderComplete=function(e,t){this._flushStashBuffer(!0),this._onComplete&&this._onComplete(this._extraData)},e.prototype._onLoaderError=function(e,t){switch(r.Z.e(this.TAG,"Loader error, code = "+t.code+", msg = "+t.msg),this._flushStashBuffer(!1),this._isEarlyEofReconnecting&&(this._isEarlyEofReconnecting=!1,e=o.nm.UNRECOVERABLE_EARLY_EOF),e){case o.nm.EARLY_EOF:if(!this._config.isLive&&this._totalLength){var i=this._currentRange.to+1;return void(i<this._totalLength&&(r.Z.w(this.TAG,"Connection lost, trying reconnect..."),this._isEarlyEofReconnecting=!0,this._internalSeek(i,!1)))}e=o.nm.UNRECOVERABLE_EARLY_EOF;break;case o.nm.UNRECOVERABLE_EARLY_EOF:case o.nm.CONNECTING_TIMEOUT:case o.nm.HTTP_STATUS_CODE_INVALID:case o.nm.EXCEPTION:}if(!this._onError)throw new h.OZ("IOException: "+t.msg);this._onError(e,t)},e}()},939:function(e,t,i){"use strict";i.d(t,{GM:function(){return r},nm:function(){return s},fp:function(){return o}});var n=i(29),r={kIdle:0,kConnecting:1,kBuffering:2,kError:3,kComplete:4},s={OK:"OK",EXCEPTION:"Exception",HTTP_STATUS_CODE_INVALID:"HttpStatusCodeInvalid",CONNECTING_TIMEOUT:"ConnectingTimeout",EARLY_EOF:"EarlyEof",UNRECOVERABLE_EARLY_EOF:"UnrecoverableEarlyEof"},o=function(){function e(e){this._type=e||"undefined",this._status=r.kIdle,this._needStash=!1,this._onContentLengthKnown=null,this._onURLRedirect=null,this._onDataArrival=null,this._onError=null,this._onComplete=null}return e.prototype.destroy=function(){this._status=r.kIdle,this._onContentLengthKnown=null,this._onURLRedirect=null,this._onDataArrival=null,this._onError=null,this._onComplete=null},e.prototype.isWorking=function(){return this._status===r.kConnecting||this._status===r.kBuffering},Object.defineProperty(e.prototype,"type",{get:function(){return this._type},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"status",{get:function(){return this._status},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"needStashBuffer",{get:function(){return this._needStash},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onContentLengthKnown",{get:function(){return this._onContentLengthKnown},set:function(e){this._onContentLengthKnown=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onURLRedirect",{get:function(){return this._onURLRedirect},set:function(e){this._onURLRedirect=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onDataArrival",{get:function(){return this._onDataArrival},set:function(e){this._onDataArrival=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onError",{get:function(){return this._onError},set:function(e){this._onError=e},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"onComplete",{get:function(){return this._onComplete},set:function(e){this._onComplete=e},enumerable:!1,configurable:!0}),e.prototype.open=function(e,t){throw new n.do("Unimplemented abstract function!")},e.prototype.abort=function(){throw new n.do("Unimplemented abstract function!")},e}()},538:function(e,t){"use strict";var i={};!function(){var e=self.navigator.userAgent.toLowerCase(),t=/(edge)\\/([\\w.]+)/.exec(e)||/(opr)[\\/]([\\w.]+)/.exec(e)||/(chrome)[ \\/]([\\w.]+)/.exec(e)||/(iemobile)[\\/]([\\w.]+)/.exec(e)||/(version)(applewebkit)[ \\/]([\\w.]+).*(safari)[ \\/]([\\w.]+)/.exec(e)||/(webkit)[ \\/]([\\w.]+).*(version)[ \\/]([\\w.]+).*(safari)[ \\/]([\\w.]+)/.exec(e)||/(webkit)[ \\/]([\\w.]+)/.exec(e)||/(opera)(?:.*version|)[ \\/]([\\w.]+)/.exec(e)||/(msie) ([\\w.]+)/.exec(e)||e.indexOf("trident")>=0&&/(rv)(?::| )([\\w.]+)/.exec(e)||e.indexOf("compatible")<0&&/(firefox)[ \\/]([\\w.]+)/.exec(e)||[],n=/(ipad)/.exec(e)||/(ipod)/.exec(e)||/(windows phone)/.exec(e)||/(iphone)/.exec(e)||/(kindle)/.exec(e)||/(android)/.exec(e)||/(windows)/.exec(e)||/(mac)/.exec(e)||/(linux)/.exec(e)||/(cros)/.exec(e)||[],r={browser:t[5]||t[3]||t[1]||"",version:t[2]||t[4]||"0",majorVersion:t[4]||t[2]||"0",platform:n[0]||""},s={};if(r.browser){s[r.browser]=!0;var o=r.majorVersion.split(".");s.version={major:parseInt(r.majorVersion,10),string:r.version},o.length>1&&(s.version.minor=parseInt(o[1],10)),o.length>2&&(s.version.build=parseInt(o[2],10))}if(r.platform&&(s[r.platform]=!0),(s.chrome||s.opr||s.safari)&&(s.webkit=!0),s.rv||s.iemobile){s.rv&&delete s.rv;var a="msie";r.browser=a,s.msie=!0}if(s.edge){delete s.edge;var h="msedge";r.browser=h,s.msedge=!0}if(s.opr){var u="opera";r.browser=u,s.opera=!0}if(s.safari&&s.android){var l="android";r.browser=l,s.android=!0}for(var d in s.name=r.browser,s.platform=r.platform,i)i.hasOwnProperty(d)&&delete i[d];Object.assign(i,s)}(),t.Z=i},29:function(e,t,i){"use strict";i.d(t,{OZ:function(){return s},rT:function(){return o},OC:function(){return a},do:function(){return h}});var n,r=(n=function(e,t){return(n=Object.setPrototypeOf||{__proto__:[]}instanceof Array&&function(e,t){e.__proto__=t}||function(e,t){for(var i in t)Object.prototype.hasOwnProperty.call(t,i)&&(e[i]=t[i])})(e,t)},function(e,t){if("function"!=typeof t&&null!==t)throw new TypeError("Class extends value "+String(t)+" is not a constructor or null");function i(){this.constructor=e}n(e,t),e.prototype=null===t?Object.create(t):(i.prototype=t.prototype,new i)}),s=function(){function e(e){this._message=e}return Object.defineProperty(e.prototype,"name",{get:function(){return"RuntimeException"},enumerable:!1,configurable:!0}),Object.defineProperty(e.prototype,"message",{get:function(){return this._message},enumerable:!1,configurable:!0}),e.prototype.toString=function(){return this.name+": "+this.message},e}(),o=function(e){function t(t){return e.call(this,t)||this}return r(t,e),Object.defineProperty(t.prototype,"name",{get:function(){return"IllegalStateException"},enumerable:!1,configurable:!0}),t}(s),a=function(e){function t(t){return e.call(this,t)||this}return r(t,e),Object.defineProperty(t.prototype,"name",{get:function(){return"InvalidArgumentException"},enumerable:!1,configurable:!0}),t}(s),h=function(e){function t(t){return e.call(this,t)||this}return r(t,e),Object.defineProperty(t.prototype,"name",{get:function(){return"NotImplementedException"},enumerable:!1,configurable:!0}),t}(s)},300:function(e,t,i){"use strict";var n=i(716),r=i.n(n),s=function(){function e(){}return e.e=function(t,i){t&&!e.FORCE_GLOBAL_TAG||(t=e.GLOBAL_TAG);var n="["+t+"] > "+i;e.ENABLE_CALLBACK&&e.emitter.emit("log","error",n),e.ENABLE_ERROR&&(console.error?console.error(n):console.warn?console.warn(n):console.log(n))},e.i=function(t,i){t&&!e.FORCE_GLOBAL_TAG||(t=e.GLOBAL_TAG);var n="["+t+"] > "+i;e.ENABLE_CALLBACK&&e.emitter.emit("log","info",n),e.ENABLE_INFO&&(console.info?console.info(n):console.log(n))},e.w=function(t,i){t&&!e.FORCE_GLOBAL_TAG||(t=e.GLOBAL_TAG);var n="["+t+"] > "+i;e.ENABLE_CALLBACK&&e.emitter.emit("log","warn",n),e.ENABLE_WARN&&(console.warn?console.warn(n):console.log(n))},e.d=function(t,i){t&&!e.FORCE_GLOBAL_TAG||(t=e.GLOBAL_TAG);var n="["+t+"] > "+i;e.ENABLE_CALLBACK&&e.emitter.emit("log","debug",n),e.ENABLE_DEBUG&&(console.debug?console.debug(n):console.log(n))},e.v=function(t,i){t&&!e.FORCE_GLOBAL_TAG||(t=e.GLOBAL_TAG);var n="["+t+"] > "+i;e.ENABLE_CALLBACK&&e.emitter.emit("log","verbose",n),e.ENABLE_VERBOSE&&console.log(n)},e}();s.GLOBAL_TAG="flv.js",s.FORCE_GLOBAL_TAG=!1,s.ENABLE_ERROR=!0,s.ENABLE_INFO=!0,s.ENABLE_WARN=!0,s.ENABLE_DEBUG=!0,s.ENABLE_VERBOSE=!0,s.ENABLE_CALLBACK=!1,s.emitter=new(r()),t.Z=s},846:function(e,t,i){"use strict";var n=i(716),r=i.n(n),s=i(300),o=function(){function e(){}return Object.defineProperty(e,"forceGlobalTag",{get:function(){return s.Z.FORCE_GLOBAL_TAG},set:function(t){s.Z.FORCE_GLOBAL_TAG=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"globalTag",{get:function(){return s.Z.GLOBAL_TAG},set:function(t){s.Z.GLOBAL_TAG=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"enableAll",{get:function(){return s.Z.ENABLE_VERBOSE&&s.Z.ENABLE_DEBUG&&s.Z.ENABLE_INFO&&s.Z.ENABLE_WARN&&s.Z.ENABLE_ERROR},set:function(t){s.Z.ENABLE_VERBOSE=t,s.Z.ENABLE_DEBUG=t,s.Z.ENABLE_INFO=t,s.Z.ENABLE_WARN=t,s.Z.ENABLE_ERROR=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"enableDebug",{get:function(){return s.Z.ENABLE_DEBUG},set:function(t){s.Z.ENABLE_DEBUG=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"enableVerbose",{get:function(){return s.Z.ENABLE_VERBOSE},set:function(t){s.Z.ENABLE_VERBOSE=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"enableInfo",{get:function(){return s.Z.ENABLE_INFO},set:function(t){s.Z.ENABLE_INFO=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"enableWarn",{get:function(){return s.Z.ENABLE_WARN},set:function(t){s.Z.ENABLE_WARN=t,e._notifyChange()},enumerable:!1,configurable:!0}),Object.defineProperty(e,"enableError",{get:function(){return s.Z.ENABLE_ERROR},set:function(t){s.Z.ENABLE_ERROR=t,e._notifyChange()},enumerable:!1,configurable:!0}),e.getConfig=function(){return{globalTag:s.Z.GLOBAL_TAG,forceGlobalTag:s.Z.FORCE_GLOBAL_TAG,enableVerbose:s.Z.ENABLE_VERBOSE,enableDebug:s.Z.ENABLE_DEBUG,enableInfo:s.Z.ENABLE_INFO,enableWarn:s.Z.ENABLE_WARN,enableError:s.Z.ENABLE_ERROR,enableCallback:s.Z.ENABLE_CALLBACK}},e.applyConfig=function(e){s.Z.GLOBAL_TAG=e.globalTag,s.Z.FORCE_GLOBAL_TAG=e.forceGlobalTag,s.Z.ENABLE_VERBOSE=e.enableVerbose,s.Z.ENABLE_DEBUG=e.enableDebug,s.Z.ENABLE_INFO=e.enableInfo,s.Z.ENABLE_WARN=e.enableWarn,s.Z.ENABLE_ERROR=e.enableError,s.Z.ENABLE_CALLBACK=e.enableCallback},e._notifyChange=function(){var t=e.emitter;if(t.listenerCount("change")>0){var i=e.getConfig();t.emit("change",i)}},e.registerListener=function(t){e.emitter.addListener("change",t)},e.removeListener=function(t){e.emitter.removeListener("change",t)},e.addLogListener=function(t){s.Z.emitter.addListener("log",t),s.Z.emitter.listenerCount("log")>0&&(s.Z.ENABLE_CALLBACK=!0,e._notifyChange())},e.removeLogListener=function(t){s.Z.emitter.removeListener("log",t),0===s.Z.emitter.listenerCount("log")&&(s.Z.ENABLE_CALLBACK=!1,e._notifyChange())},e}();o.emitter=new(r()),t.Z=o},219:function(e,t,i){"use strict";var n=function(){function e(){}return e.install=function(){Object.setPrototypeOf=Object.setPrototypeOf||function(e,t){return e.__proto__=t,e},Object.assign=Object.assign||function(e){if(null==e)throw new TypeError("Cannot convert undefined or null to object");for(var t=Object(e),i=1;i<arguments.length;i++){var n=arguments[i];if(null!=n)for(var r in n)n.hasOwnProperty(r)&&(t[r]=n[r])}return t},"function"!=typeof self.Promise&&i(264).polyfill()},e}();n.install(),t.Z=n}},t={};function i(n){var r=t[n];if(void 0!==r)return r.exports;var s=t[n]={exports:{}};return e[n].call(s.exports,s,s.exports,i),s.exports}return i.m=e,i.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return i.d(t,{a:t}),t},i.d=function(e,t){for(var n in t)i.o(t,n)&&!i.o(e,n)&&Object.defineProperty(e,n,{enumerable:!0,get:t[n]})},i.g=function(){if("object"==typeof globalThis)return globalThis;try{return this||new Function("return this")()}catch(e){if("object"==typeof window)return window}}(),i.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)},i(324)}()}));\n//# sourceMappingURL=flv.min.js.map</script><script>\nconst token=\'__TOKEN__\';let latest={},polling=false;const el=id=>document.getElementById(id);\nfunction note(s){el(\'message\').textContent=s}function text(id,s){setText(el(id),s)}\nconst nativeBridge=window.orca&&typeof window.orca.postMessage===\'function\'&&typeof window.orca.onMessage===\'function\';const pending=new Map();let requestSequence=0;\nif(nativeBridge)window.orca.onMessage(msg=>{if(typeof msg===\'string\'){try{msg=JSON.parse(msg)}catch{return}}if(msg?.type!==\'max_api_result\')return;const entry=pending.get(msg.id);if(!entry)return;pending.delete(msg.id);clearTimeout(entry.timer);if(msg.code>=400||msg.data?.status===\'error\'||msg.data?.error)entry.reject(Error(msg.data?.message||msg.data?.error||msg.code));else entry.resolve(msg.data)});\nasync function api(path,data){if(nativeBridge)return new Promise((resolve,reject)=>{const id=++requestSequence;const timer=setTimeout(()=>{pending.delete(id);reject(Error(\'Orca did not reply. Check the plugin Diagnostics tab and permissions.\'))},120000);pending.set(id,{resolve,reject,timer});window.orca.postMessage({type:\'max_api\',id,path,method:data?\'POST\':\'GET\',data:data||{}})});const r=await fetch(path,{method:data?\'POST\':\'GET\',headers:{\'X-Kobra-Token\':token,\'Content-Type\':\'application/json\'},...(data?{body:JSON.stringify(data)}:{})});const j=await r.json();if(!r.ok||j.status===\'error\'||j.error)throw Error(j.message||j.error||r.status);return j}\nfunction minutes(v){if(v==null)return \'—\';const n=Math.max(0,Math.round(Number(v)));return `${Math.floor(n/60)}h ${n%60}m`}\nasync function command(data){try{await api(\'/control\',data);note(\'Command sent. Check the live printer state for confirmation.\')}catch(e){note(e.message)}}\n\nconst namedColors=[[\'Black\',\'#212721\'],[\'White\',\'#ffffff\'],[\'Gray\',\'#808080\'],[\'Light gray\',\'#c0c0c0\'],[\'Dark gray\',\'#404040\'],[\'Red\',\'#f40031\'],[\'Orange\',\'#ff8000\'],[\'Yellow\',\'#ffff00\'],[\'Green\',\'#3db24e\'],[\'Dark green\',\'#006633\'],[\'Blue\',\'#0066ff\'],[\'Navy\',\'#001f60\'],[\'Cyan\',\'#00bcd4\'],[\'Purple\',\'#8000c0\'],[\'Pink\',\'#ff80b0\'],[\'Magenta\',\'#ff00ff\'],[\'Brown\',\'#804020\'],[\'Beige\',\'#d8be98\']];\nfunction colorName(hex){if(!/^#[0-9a-f]{6}$/i.test(hex))return \'Unknown\';const rgb=[1,3,5].map(i=>parseInt(hex.slice(i,i+2),16));let best=\'\',distance=Infinity;for(const [name,color] of namedColors){const d=[1,3,5].reduce((sum,i,n)=>sum+(rgb[n]-parseInt(color.slice(i,i+2),16))**2,0);if(d<distance){distance=d;best=name}}return best}\nlet editingSlot=null;\nfunction openSlotColor(box,index){const slot=(latest.material_boxes||[]).find(b=>b.source===\'ace\'&&Number(b.id)===box)?.slots?.find(s=>Number(s.box_slot)===index);if(!slot?.color_editable||isBusy())return;editingSlot={box_id:box,slot:index,color:slot.color.toLowerCase()};text(\'slotColorTitle\',`ACE ${box+1} · ${String.fromCharCode(65+box)}${index+1} color`);el(\'slotColorPicker\').value=slot.color;el(\'slotColorHex\').value=slot.color;text(\'slotColorName\',colorName(slot.color));text(\'colorEditNote\',\'Material type stays unchanged. Save sends the color to the printer.\');el(\'slotColorDialog\').showModal()}\nel(\'slotColorPicker\').oninput=()=>{el(\'slotColorHex\').value=el(\'slotColorPicker\').value;text(\'slotColorName\',colorName(el(\'slotColorPicker\').value))};\nel(\'slotColorHex\').oninput=()=>{const hex=el(\'slotColorHex\').value;if(/^#[0-9a-f]{6}$/i.test(hex)){el(\'slotColorPicker\').value=hex;text(\'slotColorName\',colorName(hex))}};\nel(\'cancelSlotColor\').onclick=()=>el(\'slotColorDialog\').close();\nel(\'saveSlotColor\').onclick=async()=>{const hex=el(\'slotColorHex\').value;if(!/^#[0-9a-f]{6}$/i.test(hex)){text(\'colorEditNote\',\'Enter an RGB hex color such as #FF8000.\');return}el(\'saveSlotColor\').disabled=true;try{const result=await api(\'/slot_color\',{box_id:editingSlot.box_id,slot:editingSlot.slot,color:hex});note(result.message);el(\'slotColorDialog\').close();await poll()}catch(e){text(\'colorEditNote\',e.message)}finally{el(\'saveSlotColor\').disabled=false}};\nconst aceViews=new Map();\nfunction initBoxes(){\n const parent=el(\'boxes\');\n for(let id=0;id<2;id++){\n  const section=document.createElement(\'section\');section.className=\'ace waiting\';section.dataset.ace=id;\n  const head=document.createElement(\'div\');head.className=\'ace-heading\';const title=document.createElement(\'h3\');title.textContent=`ACE ${id+1}`;const meta=document.createElement(\'span\');meta.textContent=\'No live report\';head.append(title,meta);\n  const trays=document.createElement(\'div\');trays.className=\'trays\';const slots=[];\n  for(let index=0;index<4;index++){const tray=document.createElement(\'div\');tray.className=\'tray\';tray.dataset.slot=`${id}-${index}`;\n   const label=document.createElement(\'div\');label.className=\'tray-label\';label.textContent=`${String.fromCharCode(65+id)}${index+1}`;\n   const swatch=document.createElement(\'span\');swatch.className=\'swatch\';const material=document.createElement(\'div\');material.className=\'tray-material\';material.textContent=\'Unspecified\';const feed=document.createElement(\'div\');feed.className=\'tray-feed\';feed.textContent=\'—\';const colorName=document.createElement(\'div\');colorName.className=\'tray-color-name\';const colorHex=document.createElement(\'div\');colorHex.className=\'tray-color-hex\';const origin=document.createElement(\'div\');origin.className=\'tray-origin\';const edit=document.createElement(\'button\');edit.textContent=\'Edit color\';edit.disabled=true;edit.onclick=()=>openSlotColor(id,index);tray.append(label,swatch,colorName,colorHex,material,feed,origin,edit);trays.append(tray);slots.push({tray,swatch,material,feed,colorName,colorHex,origin,edit});}\n  const actions=document.createElement(\'div\');actions.className=\'ace-actions\';const on=document.createElement(\'button\'),off=document.createElement(\'button\'),dry=document.createElement(\'span\');on.textContent=\'Dry · 45°C / 4h\';off.textContent=\'Stop drying\';dry.textContent=\'—\';on.onclick=()=>{if(confirm(`Start drying ACE ${id+1} at 45°C for 4 hours?`))command({action:\'drying\',box_id:id,on:true,target_temp:45,minutes:240})};off.onclick=()=>command({action:\'drying\',box_id:id,on:false});actions.append(on,off,dry);section.append(head,trays,actions);parent.append(section);aceViews.set(id,{section,meta,slots,on,off,dry});\n }\n}\nfunction setText(node,value){const next=String(value);if(node.textContent!==next)node.textContent=next}\nfunction renderBoxes(boxes){\n const map=new Map(boxes.filter(b=>b.source===\'ace\').map(b=>[Number(b.id),b]));\n for(const [id,v] of aceViews){const b=map.get(id);v.section.classList.toggle(\'waiting\',!b);setText(v.meta,b?`${b.temp}°C · Connected`:\'Not connected\');v.on.disabled=v.off.disabled=!b;\n  setText(v.dry,b?(b.drying?.active?`Drying · ${minutes(b.drying.remain_time)} left`:\'Drying off\'):\'—\');\n  for(let index=0;index<4;index++){const s=b?.slots?.find(s=>Number(s.box_slot)===index),t=v.slots[index];const material=s?.type&&s.type!==\'?\'?s.type:\'Unspecified\';setText(t.material,material);t.material.title=material;t.swatch.style.backgroundColor=s?.color||\'transparent\';t.tray.classList.toggle(\'fed\',!!s?.loaded);const hex=s?.color||\'\';setText(t.colorName,hex?colorName(hex):\'No color\');setText(t.colorHex,hex.toUpperCase());t.swatch.title=hex?`${colorName(hex)} · ${hex.toUpperCase()}`:\'No color\';setText(t.origin,s?.autodetected?\'Autodetected\':s?.edit_status===1?\'Manual\':s?.edit_status===2?\'Empty\':\'Unknown assignment\');t.edit.disabled=!latest.connected||isBusy()||!s?.color_editable;t.edit.title=s?.autodetected?\'Autodetected filament is protected\':isBusy()?\'Edit when the printer is idle\':\'Edit manually assigned color\';setText(t.feed,!b?\'No report\':s?.loaded?\'Fed to toolhead\':s?.available?\'Present · not fed\':\'Not detected\');}\n }\n}\n\nconst busyStates=[\'print\',\'running\',\'printing\',\'paused\',\'pausing\',\'busy\',\'heating\',\'auto_leveling\',\'preheating\',\'preparing\'];\nfunction isBusy(){return busyStates.includes(String(latest.state||\'\').toLowerCase())}\nlet lastJob=null;\nfunction keepJob(previous,report,now=Date.now()){\n const state=String(report.state||\'\').toLowerCase(),active=busyStates.includes(state),done=[\'finish\',\'finished\',\'complete\',\'completed\',\'done\'].includes(state),ended=done||[\'stopped\',\'stop\',\'stoped\',\'canceled\',\'cancelled\',\'failed\',\'fail\',\'abnormal\'].includes(state);\n const filename=report.job_name&&report.job_name!==\'Ready\'?report.job_name:null,id=report.max_taskid==null?null:String(report.max_taskid);\n const changed=active&&previous&&((id&&previous.id&&id!==previous.id)||(filename&&previous.filename&&filename!==previous.filename)||previous.ended);\n if(!active&&!ended)return previous;\n const job=changed||!previous?{progress:0,remain:null,elapsed:null,layer:null,layers:null,finish:null,id:null,filename:null}:Object.assign({},previous);\n if(id)job.id=id;if(filename)job.filename=filename;job.ended=ended;job.state=state;\n const number=v=>v!==null&&v!==undefined&&v!==\'\'&&Number.isFinite(Number(v))?Number(v):null;\n const progress=number(report.progress),elapsed=number(report.print_time),layer=number(report.curr_layer),layers=number(report.total_layers),remaining=number(report.remain_time);\n if(progress!==null&&progress>=0&&progress<=100)job.progress=Math.max(job.progress,progress);\n if(elapsed!==null&&elapsed>=0)job.elapsed=Math.max(job.elapsed||0,elapsed);\n if(layer!==null&&layer>=0)job.layer=Math.max(job.layer||0,layer);\n if(layers!==null&&layers>0)job.layers=layers;\n if(remaining!==null&&remaining>0){\n  const timestamp=number(report.max_remaining_report_time);\n  if(timestamp!==null||job.remain!==remaining||job.finish===null)job.finish=(timestamp!==null?timestamp*1000:now)+remaining*60000;\n  job.remain=remaining;\n }\n if(done){job.progress=100;job.remain=0;job.finish=null}\n return job;\n}\nfunction finishLabel(job,now=new Date()){\n if(!job)return \'—\';if(job.state===\'paused\'||job.state===\'pausing\')return \'Paused\';if(job.ended)return job.progress===100?\'Completed\':\'Print ended\';\n if(job.finish===null)return \'Calculating…\';\n const finish=new Date(job.finish),tomorrow=new Date(now);tomorrow.setDate(tomorrow.getDate()+1);\n const day=finish.toDateString()===now.toDateString()?\'Today\':finish.toDateString()===tomorrow.toDateString()?\'Tomorrow\':finish.toLocaleDateString(undefined,{weekday:\'short\',month:\'short\',day:\'numeric\'});\n return `${day}, ${finish.toLocaleTimeString(undefined,{hour:\'numeric\',minute:\'2-digit\'})}`;\n}\nasync function poll(){if(polling)return;polling=true;try{\n latest=await api(\'/status\');const connected=!!latest.connected,busy=isBusy(),state=String(latest.state||\'unknown\').toLowerCase();\n text(\'connection\',connected?\'Connected\':\'Disconnected\');el(\'connection\').className=\'badge \'+(connected?\'ok\':\'\');text(\'ip\',latest.ip||\'192.168.0.37\');text(\'firmware\',latest.firmware||\'—\');\n if(document.activeElement!==el(\'source\'))el(\'source\').value=latest.material_source||\'external\';el(\'source\').disabled=busy;\n text(\'nozzle\',connected?`${Math.round(latest.nozzle_temp)}°C`:\'—\');text(\'nozzleTarget\',connected?`Target ${latest.target_nozzle_temp}°C`:\'Target —\');text(\'bed\',connected?`${Math.round(latest.bed_temp)}°C`:\'—\');text(\'bedTarget\',connected?`Target ${latest.target_bed_temp}°C`:\'Target —\');text(\'fanLive\',connected?`${latest.fan||0}%`:\'—\');\n lastJob=keepJob(lastJob,latest);const retained=!!lastJob&&(!connected||!busy)&&!lastJob.ended;\n text(\'finish\',`Estimated finish: ${finishLabel(lastJob)}${retained?\' · last report\':\'\'}`);text(\'eta\',lastJob?minutes(lastJob.remain):\'—\');text(\'elapsed\',lastJob?minutes(lastJob.elapsed):\'—\');text(\'state\',!connected?\'Offline · last progress retained\':retained?\'Waiting for job report\':({free:\'Idle\',busy:\'Preparing\',auto_leveling:\'Leveling\'}[state]||state.charAt(0).toUpperCase()+state.slice(1)));\n const job=lastJob?.filename||(busy?\'Preparing print…\':\'No active print\');text(\'filename\',job);el(\'filename\').title=job;text(\'layers\',lastJob?`Layer ${lastJob.layer??\'—\'} / ${lastJob.layers??\'—\'}`:\'Layer — / —\');el(\'progress\').value=lastJob?.progress||0;text(\'percent\',`${lastJob?.progress||0}%`);\n const alert=el(\'printerAlert\'),err=latest.last_error;alert.classList.toggle(\'error\',!!err);setText(alert,err?`Printer error ${latest.last_error_code||\'\'}: ${err}`:connected?\'Live printer status. Commands are confirmed by subsequent printer reports.\':\'Waiting for a live printer report.\');\n const count=(latest.material_boxes||[]).filter(b=>b.source===\'ace\').length;text(\'sourceNote\',latest.material_source===\'ace\'?\'Confirm the selected slot mapping and physical feed path before starting a print.\':count?\'External spool + connected ACE units may be rejected by this firmware. Use a supported feed configuration.\':\'External spool selected. Filament must follow the printer’s intended feed path.\');\n renderBoxes(latest.material_boxes||[]);\n const modes={1:\'Silent\',2:\'Standard\',3:\'Sport\'};text(\'speedLive\',connected?(modes[latest.max_speed_mode]||\'Waiting for printer report\'):\'Offline\');\n document.querySelectorAll(\'[data-speed]\').forEach(b=>{b.disabled=!connected||!busy;b.classList.toggle(\'selected\',connected&&Number(b.dataset.speed)===latest.max_speed_mode)});\n const light=connected?latest.max_camera_light:null;text(\'lightLive\',light===1?\'On\':light===0?\'Off\':\'State unknown\');el(\'lightOn\').classList.toggle(\'selected\',light===1);el(\'lightOff\').classList.toggle(\'selected\',light===0);el(\'lightOn\').disabled=el(\'lightOff\').disabled=!connected;el(\'openCamera\').disabled=!connected||!!cameraPlayer;\n document.querySelector(\'[data-action="pause"]\').disabled=!connected||!busy||state===\'paused\';document.querySelector(\'[data-action="resume"]\').disabled=!connected||state!==\'paused\';document.querySelector(\'[data-action="stop"]\').disabled=!connected||!busy;\n document.querySelectorAll(\'#files [data-print]\').forEach(b=>b.disabled=!connected||busy||latest.material_source!==\'external\');\n }catch(e){text(\'connection\',\'Disconnected\');note(e.message)}finally{polling=false}}\nlet cameraPlayer=null,cameraSession=null,cameraOpening=false,cameraWanted=false,cameraRetries=0,cameraRetryTimer=null,cameraLastTime=0,cameraLastAdvance=Date.now();\nfunction applyCameraHeight(value){const height=Math.max(220,Math.min(900,Number(value)||420));el(\'cameraScreen\').style.height=`${height}px`;el(\'cameraHeight\').value=height;text(\'cameraHeightValue\',`${height} px`);try{localStorage.setItem(\'kobra-max-camera-height\',height)}catch{}}\ntry{const height=localStorage.getItem(\'kobra-max-camera-height\');if(height)applyCameraHeight(height)}catch{}\nel(\'cameraHeight\').oninput=()=>applyCameraHeight(el(\'cameraHeight\').value);\nif(window.ResizeObserver)new ResizeObserver(entries=>{const height=Math.round(entries[0].contentRect.height);el(\'cameraHeight\').value=height;text(\'cameraHeightValue\',`${height} px`)}).observe(el(\'cameraScreen\'));\nfunction cameraFailure(message){\n const retry=cameraWanted&&cameraRetries<5;closeCamera(message,true);\n if(retry){cameraRetries++;const delay=Math.min(15000,2000*cameraRetries);text(\'cameraStatus\',`Reconnecting ${cameraRetries}/5…`);cameraRetryTimer=setTimeout(()=>{if(cameraWanted)openCamera()},delay)}\n else{cameraWanted=false;text(\'cameraStatus\',\'Camera unavailable\');note(message+\' Use Open camera to retry.\')}\n}\nclass OrcaCameraLoader {\n constructor(){this.type=\'orca-native-bridge\';this.status=0;this.needStashBuffer=false;this.cancelled=false;this.offset=0;this.session=null;this.timer=null}\n isWorking(){return this.status===1||this.status===2}\n open(){this.status=1;this.cancelled=false;this.pump()}\n async pump(){try{\n  if(!this.session){const started=await api(\'/camera_start\',{});this.session=started.session;if(this.cancelled){await api(\'/camera_close\',{session:this.session});return}cameraSession=this.session}\n  const data=await api(\'/camera_read\',{session:this.session});if(this.cancelled)return;\n  if(data.error)throw Error(data.error);\n  if(data.chunk){const bytes=Uint8Array.from(atob(data.chunk),c=>c.charCodeAt(0));this.status=2;const start=this.offset;this.offset+=bytes.byteLength;this.onDataArrival?.(bytes.buffer,start,this.offset)}\n  if(data.done)throw Error(\'Camera stream ended. Open the camera to reconnect.\');\n  this.timer=setTimeout(()=>this.pump(),data.chunk?0:30);\n }catch(e){if(!this.cancelled){this.status=3;this.onError?.(\'Exception\',{code:-1,msg:e.message})}}}\n abort(){this.cancelled=true;clearTimeout(this.timer);this.status=0;if(this.session){api(\'/camera_close\',{session:this.session}).catch(()=>{});if(cameraSession===this.session)cameraSession=null;this.session=null}}\n destroy(){this.abort();this.onDataArrival=this.onError=this.onComplete=null}\n}\nfunction closeCamera(message=\'Viewer closed\',recovering=false){\n clearTimeout(cameraRetryTimer);if(!recovering)cameraWanted=false;\n const player=cameraPlayer;cameraPlayer=null;if(player){try{player.pause();player.unload();player.detachMediaElement();player.destroy()}catch{}}\n if(cameraSession){api(\'/camera_close\',{session:cameraSession}).catch(()=>{});cameraSession=null}\n text(\'cameraStatus\',message);text(\'cameraHint\',message===\'Viewer closed\'?\'Open camera to view the printer’s live feed.\':message);el(\'cameraHint\').hidden=false;el(\'openCamera\').disabled=!latest.connected;el(\'closeCamera\').disabled=true;\n}\nasync function openCamera(){\n if(cameraPlayer||cameraOpening)return;cameraOpening=true;cameraLastTime=0;cameraLastAdvance=Date.now();el(\'openCamera\').disabled=true;\n try{\n  if(!window.flvjs?.isSupported())throw Error(\'Video playback is unavailable in this Orca webview.\');\n  text(\'cameraStatus\',\'Connecting…\');text(\'cameraHint\',\'Connecting to printer camera…\');\n  const player=flvjs.createPlayer({type:\'flv\',isLive:true,hasAudio:false,url:\'http://orca-camera.local/stream\'}, {customLoader:OrcaCameraLoader,enableWorker:false,enableStashBuffer:false,stashInitialSize:64,lazyLoad:false,autoCleanupSourceBuffer:true,autoCleanupMaxBackwardDuration:15,autoCleanupMinBackwardDuration:5});\n  cameraPlayer=player;player.on(flvjs.Events.ERROR,(_type,_detail,info)=>{if(cameraPlayer===player)cameraFailure(info?.msg||\'Camera playback failed.\')});\n  player.attachMediaElement(el(\'cameraVideo\'));player.load();el(\'closeCamera\').disabled=false;\n  const playing=player.play();if(playing?.catch)playing.catch(()=>{text(\'cameraStatus\',\'Press play on video\');text(\'cameraHint\',\'Press play on the video controls.\')});\n }catch(e){cameraFailure(e.message)}finally{cameraOpening=false}\n}\nel(\'openCamera\').onclick=()=>{cameraWanted=true;cameraRetries=0;clearTimeout(cameraRetryTimer);openCamera()};\nel(\'cameraVideo\').onplaying=()=>{text(\'cameraStatus\',\'Live\');el(\'cameraHint\').hidden=true};\nel(\'cameraVideo\').onwaiting=()=>{if(cameraPlayer)text(\'cameraStatus\',\'Buffering…\')};\nel(\'closeCamera\').onclick=()=>closeCamera();\nwindow.addEventListener(\'pagehide\',()=>closeCamera());\nsetInterval(()=>{\n if(!cameraPlayer||document.hidden)return;\n const video=el(\'cameraVideo\'),now=Date.now();\n if(video.currentTime>cameraLastTime+.05){cameraLastTime=video.currentTime;cameraLastAdvance=now}\n if(!video.paused&&video.buffered.length){const edge=video.buffered.end(video.buffered.length-1);if(edge-video.currentTime>3){video.currentTime=Math.max(video.buffered.start(video.buffered.length-1),edge-.7);cameraLastAdvance=now}}\n if((!video.paused||video.readyState<2)&&now-cameraLastAdvance>12000)cameraFailure(\'No camera frames received for 12 seconds.\');\n},2000);\ndocument.querySelectorAll(\'[data-speed]\').forEach(b=>b.onclick=()=>command({action:\'speed\',mode:Number(b.dataset.speed)}));\nel(\'lightOn\').onclick=()=>command({action:\'light\',status:1});el(\'lightOff\').onclick=()=>command({action:\'light\',status:0});\nel(\'source\').onchange=async()=>{try{await api(\'/material_source\',{source:el(\'source\').value});note(\'Filament source changed. Review this before every print.\')}catch(e){note(e.message)}await poll()};\ndocument.querySelectorAll(\'[data-action]\').forEach(b=>b.onclick=()=>{if(b.dataset.action!==\'stop\'||confirm(\'Cancel the current print?\'))command({action:b.dataset.action})});\nfor(const [button,input,heater,max] of [[\'applyNozzle\',\'setNozzle\',\'nozzle\',300],[\'applyBed\',\'setBed\',\'bed\',90]])el(button).onclick=()=>{const n=Number(el(input).value);if(Number.isFinite(n)&&n>=0&&n<=max)command({action:\'temp\',heater,value:n});else note(\'Enter a temperature within the shown limits.\')};\nel(\'applyFan\').onclick=()=>{const n=Number(el(\'setFan\').value);if(n>=0&&n<=100)command({action:\'fan\',value:n})};\nel(\'upload\').onclick=async()=>{const file=el(\'uploadFile\').files[0];if(!file||!(/\\.gcode(\\.3mf)?$/i.test(file.name))){note(\'Choose an exported .gcode or .gcode.3mf file.\');return}if(file.size>150*1024*1024){note(\'This preview accepts files up to 150 MB.\');return}el(\'upload\').disabled=true;note(\'Uploading…\');try{const content=await new Promise((resolve,reject)=>{const r=new FileReader();r.onload=()=>resolve(String(r.result).split(\',\')[1]);r.onerror=reject;r.readAsDataURL(file)});const j=await api(\'/upload_print_file\',{filename:file.name,content_base64:content,start:false});note(`Uploaded ${j.filename}. No print was started.`);await files()}catch(e){note(e.message)}finally{el(\'upload\').disabled=false}};\nasync function files(path=\'/\'){try{const j=await api(\'/files\',{op:\'list\',storage:el(\'storage\').value,path});const p=el(\'files\');const previousScroll=p.scrollTop;p.replaceChildren();if(path!==\'/\'){const back=document.createElement(\'button\');back.textContent=\'← Root\';back.onclick=()=>files(\'/\');p.append(back)}for(const f of j.files||[]){const row=document.createElement(\'div\');row.className=\'file\';const name=document.createElement(\'span\');name.textContent=f.name;row.append(name);const b=document.createElement(\'button\');if(f.is_dir){b.textContent=\'Open\';b.onclick=()=>files(path.replace(/\\/$/,\'\')+\'/\'+f.name)}else{b.textContent=\'Print with external spool\';b.dataset.print=\'true\';b.disabled=!latest.connected||isBusy()||latest.material_source!==\'external\';b.onclick=async()=>{if(!confirm(`Start ${f.name} using the external spool? Confirm the file is sliced for this printer and the bed/feed path are ready.`))return;try{await api(\'/files\',{op:\'print\',storage:j.storage,path:j.path,filename:f.name,filesize:f.size,use_ams:false,task_settings:{auto_leveling:true}});note(\'Print-start command sent. Watch for the live state change.\')}catch(e){note(e.message)}}}row.append(b);p.append(row)}if(!(j.files||[]).length)p.textContent=\'No files reported.\'}catch(e){note(e.message)}}\ndocument.querySelectorAll(\'[data-page]\').forEach(b=>b.onclick=()=>{document.querySelectorAll(\'.page\').forEach(p=>p.hidden=p.id!==b.dataset.page);document.querySelectorAll(\'[data-page]\').forEach(n=>n.classList.toggle(\'active\',n===b))});try{const theme=localStorage.getItem(\'kobra-max-theme\');if([\'light\',\'dark\',\'system\'].includes(theme)){el(\'theme\').value=theme;el(\'max-app\').dataset.theme=theme}}catch{}el(\'theme\').onchange=()=>{el(\'max-app\').dataset.theme=el(\'theme\').value;try{localStorage.setItem(\'kobra-max-theme\',el(\'theme\').value)}catch{}};initBoxes();el(\'refreshFiles\').onclick=()=>files();el(\'storage\').onchange=()=>files();poll();setInterval(poll,2500);\n</script></body></html>'
_max_original_normalize_slot = _normalize_slot
def _normalize_slot(slot, *args, **kwargs):
    result = _max_original_normalize_slot(slot, *args, **kwargs)
    edit = slot.get('edit_status')
    result['edit_status'] = edit
    result['autodetected'] = edit == 0
    result['color_editable'] = edit == 1
    return result
DEFAULT_CONFIG['nozzle_diameter'] = '0.4'

_original_push_status = build_push_status
def build_push_status(t, ip):
    result = _original_push_status(t, ip)
    agent = _ACTIVE_AGENT[0]
    diameter = str((getattr(agent, '_cfg_cache', None) or DEFAULT_CONFIG).get('nozzle_diameter', '0.4'))
    if diameter not in ('0.2', '0.25', '0.3', '0.4', '0.5', '0.6', '0.8', '1.0'):
        diameter = '0.4'
    result['print']['nozzle_diameter'] = diameter
    return result

# Keep external feed independent of ACE telemetry. Connecting ACE does not switch feed source.
_original_send = AnycubicClient.send
def _max_send(self, ns, ttype, action, data=None):
    if ttype == "print" and action == "start":
        data = dict(data or {})
        settings = dict(data.get("ams_settings") or {})
        if MATERIAL_SOURCE[0] == "external":
            settings.update(use_ams=False, ams_box_mapping=[])
        elif not settings.get("use_ams") or not settings.get("ams_box_mapping"):
            raise PrinterError("ACE mode requires an explicit filament mapping before printing")
        data["ams_settings"] = settings
    return _original_send(self, ns, ttype, action, data)
AnycubicClient.send = _max_send

def _max_permissions():
    if not IN_ORCA:
        return
    req = getattr(orca, "request_permissions", None)
    if callable(req):
        kw = dict(threading=True, network=["http://192.168.0.37", "http://127.0.0.1"])
        try:
            req(**kw)
        except TypeError:
            kw["network_http"] = kw.pop("network")
            req(**kw)

def _max_page_html(self, http_mode=False):
    return MAX_DASHBOARD_HTML.replace('__TOKEN__', self.token)
WorkbenchServer.page_html = _max_page_html

_original_handle = WorkbenchServer.handle
def _max_handle(self, method, path, data):
    if path == '/slot_color':
        if method != 'POST':
            return 405, {'status':'error','message':'Use Save to send a color change'}
        c = self._client()
        if c is None or not c.link_up:
            return 409, {'status':'error','message':'Printer disconnected'}
        snap = c.state.snapshot()
        if job_state(snap).lower() not in ('free','idle','finish','finished','complete','completed','done','stopped','stoped','canceled','cancelled'):
            return 409, {'status':'error','message':'Change ACE assignments when the printer is idle'}
        box, index, color = data.get('box_id'), data.get('slot'), data.get('color')
        if type(box) is not int or box not in (0,1) or type(index) is not int or index not in range(4) or not isinstance(color,str) or not re.fullmatch(r'#[0-9a-fA-F]{6}',color):
            return 400, {'status':'error','message':'Choose a valid ACE slot and RGB color'}
        slot = next((s for b in snap.get('material_boxes',[]) if b.get('source') == 'ace' and b.get('id') == box for s in b.get('slots',[]) if s.get('box_slot') == index), None)
        if not slot or slot.get('edit_status') != 1:
            return 409, {'status':'error','message':'Only manually assigned slots can be edited; RFID, empty and unknown slots are protected'}
        material = slot.get('type')
        if not material or material == '?':
            return 409, {'status':'error','message':'Assign the filament material at the printer first'}
        rgb = hex_to_rgb(color)
        c.send('web','multiColorBox','setInfo',{'multi_color_box':[{'id':box,'slots':[{'index':index,'type':material,'color':rgb,'color_group':[rgb+[255]]}]}]})
        c.send('slicer','multiColorBox','getInfo')
        return 200, {'status':'ok','message':'Color sent; waiting for the printer to report the new color'}
    if path in ('/camera_start', '/camera_read', '/camera_close'):
        if method != 'POST':
            return 405, {'status':'error', 'message':'Use POST for camera requests'}
        return max_camera_api(self, path, data)
    if path == '/control' and data.get('action') in ('speed', 'light'):
        value = data.get('mode') if data['action'] == 'speed' else data.get('status')
        allowed = (1, 2, 3) if data['action'] == 'speed' else (0, 1)
        if type(value) is not int or value not in allowed:
            return 400, {'status':'error', 'message':'Invalid speed mode or light state'}
    if path == '/material_source' and method == 'POST':
        source = data.get('source')
        if source not in ('external', 'ace'):
            return 400, {'status':'error', 'message':'Choose external or ace'}
        c = self._client()
        if c and job_state(c.state.snapshot()).lower() in ('printing','paused','busy','heating','auto_leveling'):
            return 409, {'status':'error', 'message':'Change source only while idle'}
        MATERIAL_SOURCE[0] = source
        return 200, {'status':'ok', 'source':source}
    if path == '/status' and method == 'GET':
        snap = self.status()
        snap['material_source'] = MATERIAL_SOURCE[0]
        return 200, snap
    # These upstream features target other models and are not validated on the Max.
    if path in ('/run_gcode','/setup','/sync_to_printer','/slicer','/recent_messages'):
        return 400, {'status':'error', 'message':'Unavailable in the Max preview'}
    if path == '/control' and data.get('action') not in ('pause','resume','stop','temp','fan','speed','light','drying','clear_alert'):
        return 400, {'status':'error', 'message':'Control not validated for this preview'}
    if path == '/control' and data.get('action') == 'drying':
        c = self._client()
        if c is None:
            return 409, {'status':'error','message':'Printer disconnected'}
        box = int(data.get('box_id', -1))
        if box not in (0, 1):
            return 400, {'status':'error','message':'Invalid ACE box'}
        c.set_drying(box, bool(data.get('on')), max(35,min(65,int(data.get('target_temp',45)))), max(30,min(1440,int(data.get('minutes',240)))))
        return 200, {'status':'ok','message':'Command sent; waiting for live telemetry'}
    if path == '/files' and data.get('op','list') not in ('list','details','print'):
        return 400, {'status':'error', 'message':'File operation unavailable in this preview'}
    if path == '/upload_print_file':
        data = dict(data)
        data['start'] = False  # Dashboard upload is always upload-only.
    return _original_handle(self, method, path, data)
WorkbenchServer.handle = _max_handle

def _max_launch_setup(self):
    return {'status':'error','message':'No profile or system installation is required'}
WorkbenchServer.launch_setup = _max_launch_setup

def _max_setup_status(self):
    return {'status':'ok','supported':False,'components':[], 'message':'Keep your existing Max profile. No system installer is included.'}
WorkbenchServer.setup_status = _max_setup_status

# In Orca, use the embedded page's message bridge, not a localhost iframe/server.
# The standalone HTTP server remains available for protocol/UI smoke testing only.
if IN_ORCA:
    def workbench_server():
        with _WORKBENCH_LOCK:
            if _WORKBENCH[0] is None:
                _WORKBENCH[0] = WorkbenchServer(None)
            return _WORKBENCH[0]

def _max_connect_panel():
    server = workbench_server()
    server.select_from_preset('192.168.0.37', 'Kobra 3 Max')
    return server

if IN_ORCA and getattr(orca, 'pages', None):
    class KobraMaxPage(orca.pages.PagesPluginCapabilityBase):
        def get_name(self):
            return 'Kobra Max'
        def get_ui(self):
            return MAX_DASHBOARD_HTML
        def on_message(self, data):
            if not isinstance(data, dict) or data.get('type') != 'max_api':
                return
            request_id = data.get('id')
            try:
                server = _max_connect_panel()
            except Exception as exc:
                self.post_message({'type':'max_api_result','id':request_id,'code':500,'data':{'status':'error','message':str(exc)}})
                return
            def worker():
                try:
                    code, result = server.handle(str(data.get('method','GET')), str(data.get('path','/status')), data.get('data') or {})
                except Exception as exc:
                    code, result = 500, {'status':'error','message':str(exc)}
                self.post_message({'type':'max_api_result','id':request_id,'code':code,'data':result})
            if _spawn(worker, 'kobra-max-page-request') is None:
                self.post_message({'type':'max_api_result','id':request_id,'code':500,'data':{'status':'error','message':'Orca denied the background worker permission'}})

@orca.plugin
class KobraMaxPlugin(orca.base):
    def register_capabilities(self):
        _max_permissions()
        orca.register_capability(AnycubicKobraAgent)
        if getattr(orca, 'pages', None):
            orca.register_capability(KobraMaxPage)
        workbench_server()
