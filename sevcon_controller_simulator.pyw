#!/usr/bin/env python3
"""CANable SLCAN "PCAN-View-like" Tkinter monitor

- Connects to a CANable running SLCAN firmware on macOS via /dev/cu.usbmodem*
- Live receive view (aggregated by ID): count, last time, period, DLC, data, flags
- Optional raw log view
- Send single frames (standard/extended, RTR optional)
- Add cyclic TX messages with interval (ms), start/stop, enable/disable
- Click a row in the RX table to populate the TX fields

Requirements:
  python3 -m pip install python-can pyserial

Notes:
- Uses python-can "slcan" backend and talks directly to the serial port.
- Typical CANable SLCAN serial speed is 115200. (Firmware-dependent; adjust if needed.)
"""

import tkinter as tk
from tkinter import ttk, messagebox
import threading
import queue
import time
import glob
import re
import json
from pathlib import Path

try:
    from serial.tools import list_ports
except ImportError:
    list_ports = None
from dataclasses import dataclass, field

try:
    import can
except ImportError:
    can = None


def now_s() -> float:
    return time.time()


def bytes_to_hex(data: bytes) -> str:
    return " ".join(f"{b:02X}" for b in data)


def parse_hex_bytes(s: str) -> bytes:
    """Accepts: "DE AD BE EF" or "DEADBEEF" or "DE-AD-BE-EF""" 
    s = s.strip()
    if not s:
        return b""
    s = s.replace("-", " ").replace(",", " ")
    parts = s.split()
    if len(parts) == 1 and re.fullmatch(r"[0-9a-fA-F]+", parts[0]) and len(parts[0]) % 2 == 0:
        raw = parts[0]
        return bytes(int(raw[i:i+2], 16) for i in range(0, len(raw), 2))
    out = []
    for p in parts:
        if not re.fullmatch(r"[0-9a-fA-F]{1,2}", p):
            raise ValueError(f"Bad byte: '{p}'")
        out.append(int(p, 16))
    return bytes(out)


def parse_id(s: str) -> int:
    s = s.strip().lower()
    if s.startswith("0x"):
        s = s[2:]
    if not s:
        raise ValueError("ID is empty")
    if not re.fullmatch(r"[0-9a-f]+", s):
        raise ValueError("ID must be hex (e.g. 123 or 0x123 or 1ABCDE)")
    return int(s, 16)


def is_valid_std_id(arbid: int) -> bool:
    return 0 <= arbid <= 0x7FF


def is_valid_ext_id(arbid: int) -> bool:
    return 0 <= arbid <= 0x1FFFFFFF


@dataclass
class RxEntry:
    arbitration_id: int
    is_extended_id: bool
    is_remote_frame: bool
    is_error_frame: bool
    dlc: int
    data_hex: str
    count: int = 0
    last_ts: float = 0.0
    prev_ts: float = 0.0
    period_ms: float = 0.0


@dataclass
class CyclicTxItem:
    enabled: bool
    name: str
    arbitration_id: int
    is_extended_id: bool
    is_remote_frame: bool
    dlc: int
    data: bytes
    interval_ms: int
    next_due: float = field(default_factory=now_s)
    tx_count: int = 0
    last_tx_ts: float = 0.0



# ---------------------- CANopen / Sevcon simulator helpers ----------------------

def _parse_od_int(value, node_id: int = 1, default: int = 0) -> int:
    if value is None:
        return default
    if isinstance(value, int):
        return value
    text = str(value).strip()
    if not text or text.lower() == "no":
        return default
    text = text.replace("$NODEID", str(node_id)).replace("$NodeID", str(node_id))
    try:
        if "+" in text:
            return sum(_parse_od_int(part.strip(), node_id, 0) for part in text.split("+"))
        if re.fullmatch(r"[0-9A-Fa-f]+[hH]", text):
            return int(text[:-1], 16)
        return int(text, 0)
    except Exception:
        try:
            return int(text, 16)
        except Exception:
            return default


def _dtype_bytes(dtype: str) -> int:
    d = (dtype or "").lower().replace(" ", "")
    if "8" in d: return 1
    if "16" in d: return 2
    if "24" in d: return 3
    if "32" in d: return 4
    if "64" in d: return 8
    return 4


def _dtype_signed(dtype: str) -> bool:
    return (dtype or "").lower().startswith("integer")


def _pack_le(value: int, size: int, signed: bool = False) -> bytes:
    mask = (1 << (size * 8)) - 1
    value = int(value) & mask
    return value.to_bytes(size, "little", signed=False)


def _unpack_le(data: bytes, signed: bool = False) -> int:
    return int.from_bytes(bytes(data), "little", signed=signed)


@dataclass
class PdoMapEntry:
    index: int
    sub: int
    bits: int
    name: str
    dtype: str

    @property
    def size(self) -> int:
        return max(1, self.bits // 8)


@dataclass
class TpdoDef:
    number: int
    cob_id: int
    interval_ms: int
    enabled: bool
    mappings: list[PdoMapEntry]
    next_due: float = field(default_factory=now_s)
    tx_count: int = 0


class SevconSimulator:
    def __init__(self, app):
        self.app = app
        self.node_id = 1
        self.force_enable_tpdos = True
        # When enabled, transmit like a standard CANopen controller TPDO producer:
        # TPDO1=0x180+node, TPDO2=0x280+node, TPDO3=0x380+node, TPDO4=0x480+node.
        # The Sevcon OD supplied has TPDO COB-IDs in the 0x200/0x300/0x400 range,
        # which look like RPDO IDs to many CANopen tools. This option keeps the
        # TPDO mapping payloads from 0x1A00..0x1A03 but forces the transmit IDs.
        self.standard_tpdo_cobids = True
        # Bench-test option: keep TPDOs transmitting even if another app sends
        # an NMT Pre-Operational/Stop command. Many PC tools do this before SDO
        # access, which otherwise makes TPDOs appear to start and then stop.
        self.tpdo_in_all_nmt_states = True
        self.od = {}
        self.values: dict[tuple[int, int], int] = {}
        self.meta: dict[tuple[int, int], dict] = {}
        self.tpdos: list[TpdoDef] = []
        self.enabled = False
        self.nmt_state = 0x7F  # pre-operational
        self.heartbeat_ms = 500
        self.next_heartbeat = now_s()
        self.lock = threading.Lock()

    def load_od(self, path: str):
        raw = json.loads(Path(path).read_text(encoding="utf-8"))
        with self.lock:
            self.od = raw
            self.values.clear()
            self.meta.clear()
            for idx_s, obj in raw.items():
                try:
                    idx = int(idx_s, 16)
                except Exception:
                    continue
                for sub_s, subobj in (obj.get("subs") or {}).items():
                    try:
                        sub = int(sub_s, 16)
                    except Exception:
                        continue
                    dtype = subobj.get("data_type") or "Unsigned32"
                    val = _parse_od_int(subobj.get("default_value"), self.node_id, 0)
                    self.values[(idx, sub)] = val
                    self.meta[(idx, sub)] = subobj
            self.heartbeat_ms = max(50, _parse_od_int(self._get_default("0x1017", "0x00"), self.node_id, 500))
            self._build_tpdos_locked()

    def _get_default(self, idx_s, sub_s):
        return (((self.od.get(idx_s) or {}).get("subs") or {}).get(sub_s) or {}).get("default_value")

    def _build_tpdos_locked(self):
        self.tpdos.clear()
        for n in range(8):
            comm_idx = 0x1800 + n
            map_idx = 0x1A00 + n
            comm = self.od.get(f"0x{comm_idx:04X}") or self.od.get(f"0x{comm_idx:04x}")
            mp = self.od.get(f"0x{map_idx:04X}") or self.od.get(f"0x{map_idx:04x}")
            if not comm or not mp:
                continue
            cob_raw = self.values.get((comm_idx, 1), 0x180 + self.node_id + n * 0x100)
            enabled = (cob_raw & 0x80000000) == 0 or self.force_enable_tpdos

            if self.standard_tpdo_cobids:
                # Standard CANopen TPDO COB-IDs only define TPDO1..TPDO4.
                # Use the Sevcon mapping objects for the payload, but put the
                # frames on the expected TPDO addresses.
                if n >= 4:
                    continue
                cob_id = 0x180 + self.node_id + (n * 0x100)
            else:
                # Use the exact COB-ID from the object dictionary.
                cob_id = cob_raw & 0x1FFFFFFF
            event_ms = self.values.get((comm_idx, 5), 0) or 100
            count = min(8, self.values.get((map_idx, 0), 0))
            mappings = []
            for sidx in range(1, count + 1):
                val = self.values.get((map_idx, sidx), 0)
                obj_index = (val >> 16) & 0xFFFF
                obj_sub = (val >> 8) & 0xFF
                bits = val & 0xFF
                if bits <= 0:
                    continue
                meta = self.meta.get((obj_index, obj_sub), {})
                name = meta.get("name") or f"0x{obj_index:04X}:{obj_sub:02X}"
                dtype = meta.get("data_type") or ("Integer" + str(bits) if bits in (8,16,32) else "Unsigned32")
                mappings.append(PdoMapEntry(obj_index, obj_sub, bits, name, dtype))
            if mappings:
                self.tpdos.append(TpdoDef(n + 1, cob_id, int(event_ms), enabled, mappings))

    def set_value(self, index: int, sub: int, value: int):
        with self.lock:
            self.values[(index, sub)] = int(value)

    def get_value(self, index: int, sub: int) -> int:
        with self.lock:
            return int(self.values.get((index, sub), 0))

    def handle_message(self, msg):
        """Handle messages addressed to the simulated controller.

        SDO server responses are intentionally allowed any time the simulator
        has an object dictionary loaded. A real CANopen node can answer SDOs in
        pre-operational, and this also makes bench testing easier if the user
        forgets to press Start Simulator. Heartbeat/TPDO generation still uses
        self.enabled.
        """
        arbid = int(msg.arbitration_id)
        data = bytes(getattr(msg, "data", b"") or b"")

        # Ignore extended CAN IDs for CANopen SDO/NMT handling.
        if bool(getattr(msg, "is_extended_id", False)):
            return

        # NMT command: COB-ID 0, data[0]=command, data[1]=node or 0 all
        if arbid == 0 and len(data) >= 2 and data[1] in (0, self.node_id):
            cmd = data[0]
            if cmd == 0x01: self.nmt_state = 0x05
            elif cmd == 0x02: self.nmt_state = 0x04
            elif cmd == 0x80: self.nmt_state = 0x7F
            elif cmd in (0x81, 0x82): self.nmt_state = 0x7F
            self.app._raw_append(f"SIM NMT RX cmd=0x{cmd:02X} node={data[1]} state=0x{self.nmt_state:02X} TPDOs_continue={self.tpdo_in_all_nmt_states}")
            return

        # SDO client -> server. Default CANopen is 0x600 + node ID.
        # Also honor 0x1200:01 if the OD has a numeric COB-ID configured.
        sdo_rx_ids = {0x600 + self.node_id}
        try:
            od_sdo_rx = int(self.values.get((0x1200, 0x01), 0)) & 0x7FF
            if od_sdo_rx:
                sdo_rx_ids.add(od_sdo_rx)
        except Exception:
            pass

        if arbid in sdo_rx_ids and len(data) >= 4:
            self.app._raw_append(f"SIM SDO RX {arbid:03X} [{len(data)}] {bytes_to_hex(data)}")
            self._handle_sdo(data.ljust(8, b"\x00")[:8])
            return

    def tick(self):
        if not self.enabled or self.app.bus is None:
            return
        t = now_s()
        if t >= self.next_heartbeat:
            self._send(0x700 + self.node_id, bytes([self.nmt_state]))
            self.next_heartbeat = t + self.heartbeat_ms / 1000.0
        # A real CANopen node normally transmits PDOs only while Operational
        # (0x05). For this simulator, default to continuing TPDO traffic in any
        # NMT state so an external test app cannot accidentally stop the TPDOs by
        # sending NMT Pre-Operational/Stop during SDO probing.
        if self.nmt_state != 0x05 and not self.tpdo_in_all_nmt_states:
            return
        with self.lock:
            tpdos = list(self.tpdos)
        for tpdo in tpdos:
            if not tpdo.enabled or t < tpdo.next_due:
                continue
            payload = bytearray()
            with self.lock:
                for m in tpdo.mappings:
                    value = self.values.get((m.index, m.sub), 0)
                    payload.extend(_pack_le(value, m.size, _dtype_signed(m.dtype)))
            payload = bytes(payload[:8]).ljust(8, b"\x00")
            self._send(tpdo.cob_id, payload)
            tpdo.tx_count += 1
            tpdo.next_due = t + max(10, tpdo.interval_ms) / 1000.0

    def _send(self, arbid: int, data: bytes):
        try:
            self.app.bus.send(can.Message(arbitration_id=arbid, is_extended_id=(arbid > 0x7FF), data=data, dlc=len(data)))
            self.app._raw_append(f"SIM TX {arbid:03X} [{len(data)}] {bytes_to_hex(data)}")
        except Exception as e:
            self.app._raw_append(f"SIM TX ERROR: {e}")

    def _sdo_tx_cobid(self) -> int:
        """Return SDO server->client COB-ID. Default is 0x580 + node ID."""
        try:
            cob = int(self.values.get((0x1200, 0x02), 0)) & 0x7FF
            if cob:
                return cob
        except Exception:
            pass
        return 0x580 + self.node_id

    def _handle_sdo(self, data: bytes):
        cs = data[0]
        idx = data[1] | (data[2] << 8)
        sub = data[3]
        meta = self.meta.get((idx, sub), {})
        dtype = meta.get("data_type") or "Unsigned32"
        size = min(4, _dtype_bytes(dtype))
        if cs == 0x40:  # expedited upload request
            value = self.get_value(idx, sub)
            n_unused = 4 - size
            resp_cs = 0x43 | (n_unused << 2)  # expedited, size indicated
            payload = bytes([resp_cs, data[1], data[2], sub]) + _pack_le(value, size, _dtype_signed(dtype)).ljust(4, b"\x00")
            self._send(self._sdo_tx_cobid(), payload)
        elif cs in (0x2F, 0x2B, 0x27, 0x23):  # expedited download 1/2/3/4 bytes
            size_map = {0x2F: 1, 0x2B: 2, 0x27: 3, 0x23: 4}
            wr_size = size_map.get(cs, 4)
            value = _unpack_le(data[4:4+wr_size], _dtype_signed(dtype))
            self.set_value(idx, sub, value)
            self._send(self._sdo_tx_cobid(), bytes([0x60, data[1], data[2], sub, 0, 0, 0, 0]))
        else:
            # abort: command specifier not valid/unsupported
            self._send(self._sdo_tx_cobid(), bytes([0x80, data[1], data[2], sub, 0x00, 0x00, 0x04, 0x05]))


class CanMonitorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("CANable Monitor (SLCAN) - Tkinter")
        self.geometry("1180x720")

        if can is None:
            messagebox.showerror(
                "Missing dependency",
                "python-can is not installed.\n\nRun:\n  python3 -m pip install python-can pyserial",
            )
            self.destroy()
            return

        # CAN state
        self.bus = None
        self.reader_thread = None
        self.reader_stop = threading.Event()
        self.rx_queue: "queue.Queue[can.Message]" = queue.Queue(maxsize=5000)

        # RX cache (aggregated)
        self.rx_entries = {}  # key: (is_ext, arbid) -> RxEntry

        # Cyclic TX
        self.cyclic_items: list[CyclicTxItem] = []
        self.last_profile_path: Path | None = None
        self.cyclic_running = False
        self.cyclic_lock = threading.Lock()

        # Sevcon / CANopen controller simulator
        self.sim = SevconSimulator(self)
        self.sim_window = None
        self.sim_status_var = tk.StringVar(value="Simulator: OFF")

        # UI vars
        self.port_var = tk.StringVar(value=self._auto_pick_port() or "")
        self.bitrate_var = tk.StringVar(value="500000")
        self.serial_baud_var = tk.StringVar(value="115200")
        self.connected_var = tk.StringVar(value="DISCONNECTED")
        self.cyclic_status_var = tk.StringVar(value="Cyclic: STOPPED")

        self.filter_id_var = tk.StringVar(value="")
        self.pause_var = tk.BooleanVar(value=False)
        self.rawlog_var = tk.BooleanVar(value=False)
        self.max_raw_lines = 2000

        # TX vars
        self.tx_id_var = tk.StringVar(value="123")
        self.tx_ext_var = tk.BooleanVar(value=False)
        self.tx_rtr_var = tk.BooleanVar(value=False)
        self.tx_data_var = tk.StringVar(value="DE AD BE EF")
        self.tx_dlc_var = tk.StringVar(value="8")

        self._build_ui()

        self.after(100, self._drain_rx_queue)
        self._last_rx_ui_refresh = 0.0
        self._rx_iid_map = {}  # key_tag -> tree iid
        self.after(20, self._cyclic_tick)

        self.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------------------- UI ----------------------

    def _build_ui(self):
        top = ttk.Frame(self)
        top.pack(side=tk.TOP, fill=tk.X, padx=10, pady=8)

        conn = ttk.LabelFrame(top, text="Connection")
        conn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))

        ttk.Label(conn, text="Port:").grid(row=0, column=0, sticky="w", padx=6, pady=4)
        self.port_combo = ttk.Combobox(conn, textvariable=self.port_var, width=34, values=self._list_ports())
        self.port_combo.grid(row=0, column=1, sticky="w", padx=6, pady=4)
        ttk.Button(conn, text="Rescan", command=self._rescan_ports).grid(row=0, column=2, padx=6, pady=4)

        ttk.Label(conn, text="CAN bitrate:").grid(row=1, column=0, sticky="w", padx=6, pady=4)
        bitrate_combo = ttk.Combobox(
            conn,
            textvariable=self.bitrate_var,
            width=14,
            values=["10000", "20000", "50000", "83000", "100000", "125000", "250000", "500000", "800000", "1000000"],
        )
        bitrate_combo.grid(row=1, column=1, sticky="w", padx=6, pady=4)

        ttk.Label(conn, text="SLCAN serial baud:").grid(row=1, column=2, sticky="e", padx=6, pady=4)
        baud_combo = ttk.Combobox(conn, textvariable=self.serial_baud_var, width=10, values=["115200", "230400", "460800", "921600"])
        baud_combo.grid(row=1, column=3, sticky="w", padx=6, pady=4)

        self.connect_btn = ttk.Button(conn, text="Connect", command=self.on_connect)
        self.connect_btn.grid(row=0, column=3, padx=6, pady=4, sticky="e")
        self.disconnect_btn = ttk.Button(conn, text="Disconnect", command=self.on_disconnect, state=tk.DISABLED)
        self.disconnect_btn.grid(row=0, column=4, padx=6, pady=4)

        ttk.Label(conn, text="Status:").grid(row=2, column=0, sticky="w", padx=6, pady=4)
        ttk.Label(conn, textvariable=self.connected_var).grid(row=2, column=1, sticky="w", padx=6, pady=4)

        conn.grid_columnconfigure(1, weight=1)

        controls = ttk.LabelFrame(top, text="View Controls")
        controls.pack(side=tk.LEFT, fill=tk.X)

        ttk.Label(controls, text="Filter ID (hex, optional):").grid(row=0, column=0, padx=6, pady=4, sticky="w")
        ttk.Entry(controls, textvariable=self.filter_id_var, width=18).grid(row=0, column=1, padx=6, pady=4, sticky="w")
        ttk.Checkbutton(controls, text="Pause RX", variable=self.pause_var).grid(row=0, column=2, padx=6, pady=4)
        ttk.Checkbutton(controls, text="Raw log", variable=self.rawlog_var, command=self._toggle_rawlog).grid(row=0, column=3, padx=6, pady=4)
        ttk.Button(controls, text="Clear RX", command=self._clear_rx).grid(row=0, column=4, padx=6, pady=4)
        ttk.Button(controls, text="Sevcon Simulator", command=self._open_simulator_window).grid(row=1, column=0, columnspan=2, padx=6, pady=4, sticky="w")
        ttk.Label(controls, textvariable=self.sim_status_var).grid(row=1, column=2, columnspan=3, padx=6, pady=4, sticky="w")

        mid = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        mid.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        rx_frame = ttk.LabelFrame(mid, text="Receive (aggregated by ID) — click a row to load TX fields")
        mid.add(rx_frame, weight=3)

        cols = ("id", "ext", "rtr", "err", "dlc", "data", "count", "last_ms", "period_ms")
        self.rx_tree = ttk.Treeview(rx_frame, columns=cols, show="headings", height=18)
        headings = {
            "id": "ID",
            "ext": "EXT",
            "rtr": "RTR",
            "err": "ERR",
            "dlc": "DLC",
            "data": "DATA",
            "count": "COUNT",
            "last_ms": "LAST (ms ago)",
            "period_ms": "PERIOD (ms)",
        }
        widths = {"id": 90, "ext": 45, "rtr": 45, "err": 45, "dlc": 45, "data": 330, "count": 70, "last_ms": 100, "period_ms": 110}
        for c in cols:
            self.rx_tree.heading(c, text=headings[c])
            self.rx_tree.column(c, width=widths[c], anchor="w")
        self.rx_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(6, 0), pady=6)

        rx_scroll = ttk.Scrollbar(rx_frame, orient=tk.VERTICAL, command=self.rx_tree.yview)
        rx_scroll.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 6), pady=6)
        self.rx_tree.configure(yscrollcommand=rx_scroll.set)
        self.rx_tree.bind("<<TreeviewSelect>>", self._on_rx_select)

        right = ttk.PanedWindow(mid, orient=tk.VERTICAL)
        mid.add(right, weight=2)

        tx_frame = ttk.LabelFrame(right, text="Transmit (single-shot)")
        right.add(tx_frame, weight=1)

        ttk.Label(tx_frame, text="ID (hex):").grid(row=0, column=0, padx=6, pady=4, sticky="w")
        ttk.Entry(tx_frame, textvariable=self.tx_id_var, width=14).grid(row=0, column=1, padx=6, pady=4, sticky="w")
        ttk.Checkbutton(tx_frame, text="Extended (29-bit)", variable=self.tx_ext_var).grid(row=0, column=2, padx=6, pady=4, sticky="w")
        ttk.Checkbutton(tx_frame, text="RTR", variable=self.tx_rtr_var, command=self._on_rtr_toggle).grid(row=0, column=3, padx=6, pady=4, sticky="w")

        ttk.Label(tx_frame, text="DLC:").grid(row=1, column=0, padx=6, pady=4, sticky="w")
        ttk.Entry(tx_frame, textvariable=self.tx_dlc_var, width=6).grid(row=1, column=1, padx=6, pady=4, sticky="w")

        ttk.Label(tx_frame, text="Data (hex bytes):").grid(row=1, column=2, padx=6, pady=4, sticky="e")
        self.tx_data_entry = ttk.Entry(tx_frame, textvariable=self.tx_data_var, width=36)
        self.tx_data_entry.grid(row=1, column=3, padx=6, pady=4, sticky="w")

        ttk.Button(tx_frame, text="Send Now", command=self.on_send_once).grid(row=2, column=3, padx=6, pady=6, sticky="e")

        tx_frame.grid_columnconfigure(3, weight=1)

        cyc_frame = ttk.LabelFrame(right, text="Cyclic Transmit")
        right.add(cyc_frame, weight=2)

        # Use pack-based layout so the list expands cleanly to the right with no dead space.
        cyc_list_frame = ttk.Frame(cyc_frame)
        cyc_list_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=6, pady=6)

        cyc_cols = ("en", "name", "id", "ext", "rtr", "dlc", "data", "interval", "tx")
        self.cyc_tree = ttk.Treeview(cyc_list_frame, columns=cyc_cols, show="headings", height=8)
        cyc_heads = {"en": "EN", "name": "NAME", "id": "ID", "ext": "EXT", "rtr": "RTR", "dlc": "DLC", "data": "DATA", "interval": "INT(ms)", "tx": "TX#"}
        cyc_w = {"en": 40, "name": 140, "id": 90, "ext": 45, "rtr": 45, "dlc": 45, "data": 260, "interval": 90, "tx": 70}
        for c in cyc_cols:
            self.cyc_tree.heading(c, text=cyc_heads[c])
            self.cyc_tree.column(c, width=cyc_w[c], anchor="w")

        self.cyc_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        cyc_scroll = ttk.Scrollbar(cyc_list_frame, orient=tk.VERTICAL, command=self.cyc_tree.yview)
        cyc_scroll.pack(side=tk.LEFT, fill=tk.Y)
        self.cyc_tree.configure(yscrollcommand=cyc_scroll.set)

        # Button row
        cyc_btns = ttk.Frame(cyc_frame)
        cyc_btns.pack(side=tk.TOP, fill=tk.X, padx=6, pady=(0, 6))

        # Two-row button layout
        cyc_btns_row1 = ttk.Frame(cyc_btns)
        cyc_btns_row1.pack(side=tk.TOP, fill=tk.X)
        cyc_btns_row2 = ttk.Frame(cyc_btns)
        cyc_btns_row2.pack(side=tk.TOP, fill=tk.X, pady=(6, 0))

        ttk.Button(cyc_btns_row1, text="Add from TX fields", command=self._add_cyclic_from_tx).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(cyc_btns_row1, text="Load to TX", command=self._load_cyclic_to_tx).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(cyc_btns_row1, text="Update from TX", command=self._update_selected_cyclic_from_tx).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(cyc_btns_row1, text="Toggle Enable", command=self._toggle_cyclic_enable).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(cyc_btns_row1, text="Remove", command=self._remove_cyclic).pack(side=tk.LEFT, padx=(0, 12))

        ttk.Button(cyc_btns_row2, text="Save List…", command=self._save_cyclic_profile).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(cyc_btns_row2, text="Load List…", command=self._load_cyclic_profile).pack(side=tk.LEFT, padx=(0, 12))

        self.cyc_stop_btn = ttk.Button(cyc_btns_row2, text="Stop Cyclic", command=self._stop_cyclic, state=tk.DISABLED)
        self.cyc_stop_btn.pack(side=tk.RIGHT)
        self.cyc_start_btn = ttk.Button(cyc_btns_row2, text="Start Cyclic", command=self._start_cyclic)
        self.cyc_start_btn.pack(side=tk.RIGHT, padx=(0, 6))

        ttk.Label(cyc_frame, text="Tip: edit interval by removing + re-adding (simple implementation)." ).pack(side=tk.TOP, anchor="w", padx=6, pady=(0, 2))
        ttk.Label(cyc_frame, textvariable=self.cyclic_status_var).pack(side=tk.TOP, anchor="w", padx=6, pady=(0, 6))

        raw_frame = ttk.LabelFrame(right, text="Raw Log (latest messages)")
        right.add(raw_frame, weight=1)

        self.raw_text = tk.Text(raw_frame, height=10, wrap="none", state="disabled")
        self.raw_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(6, 0), pady=6)
        raw_scroll = ttk.Scrollbar(raw_frame, orient=tk.VERTICAL, command=self.raw_text.yview)
        raw_scroll.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 6), pady=6)
        self.raw_text.configure(yscrollcommand=raw_scroll.set)

        self._toggle_rawlog()

    # ---------------------- Port discovery ----------------------

    def _list_ports(self):
        """Return serial port display names for Windows/macOS/Linux.

        The combo box shows friendly labels like:
            COM5 - USB Serial Device
        but the connect code converts that back to just COM5.
        """
        self._port_label_to_device = {}

        ports = []
        if list_ports is not None:
            for p in list_ports.comports():
                desc = p.description or "Serial Device"
                label = f"{p.device} - {desc}"
                ports.append(label)
                self._port_label_to_device[label] = p.device

        # Fallback for older Mac/Linux setups where pyserial does not report the port.
        if not ports:
            devices = sorted(
                glob.glob("/dev/cu.usbmodem*")
                + glob.glob("/dev/cu.usbserial*")
                + glob.glob("/dev/tty.usbmodem*")
                + glob.glob("/dev/tty.usbserial*")
            )
            for d in devices:
                ports.append(d)
                self._port_label_to_device[d] = d

        return sorted(ports)

    def _get_selected_port_device(self):
        selected = self.port_var.get().strip()
        return getattr(self, "_port_label_to_device", {}).get(selected, selected)

    def _auto_pick_port(self):
        ports = self._list_ports()
        for p in ports:
            low = p.lower()
            if "usbmodem" in low or "canable" in low or "slcan" in low:
                return p
        return ports[0] if ports else None

    def _rescan_ports(self):
        ports = self._list_ports()
        self.port_combo["values"] = ports
        if ports and self.port_var.get() not in ports:
            self.port_var.set(self._auto_pick_port() or ports[0])

    # ---------------------- Connection ----------------------

    def on_connect(self):
        if self.bus is not None:
            return
        port_label = self.port_var.get().strip()
        port = self._get_selected_port_device()
        if not port_label:
            messagebox.showerror("Connect", "Select a serial port (for example COM5 on Windows or /dev/cu.usbmodem... on macOS).")
            return

        # Do connect in a worker thread so the GUI never freezes
        self.connect_btn.configure(state=tk.DISABLED)
        self.connected_var.set("CONNECTING...")

        def _worker():
            try:
                bitrate = int(self.bitrate_var.get())
                serial_baud = int(self.serial_baud_var.get())

                kwargs = dict(bustype="slcan", channel=port, bitrate=bitrate)
                try:
                    bus = can.interface.Bus(**kwargs, ttyBaudrate=serial_baud)
                except TypeError:
                    bus = can.interface.Bus(**kwargs, baudrate=serial_baud)

                def _on_ok():
                    self.bus = bus
                    self.connected_var.set(f"CONNECTED: {port} @ {bitrate} bps (serial {serial_baud})")
                    self.disconnect_btn.configure(state=tk.NORMAL)

                    self.reader_stop.clear()
                    self.reader_thread = threading.Thread(target=self._reader_loop, daemon=True)
                    self.reader_thread.start()

                self.after(0, _on_ok)

            except Exception as e:
                def _on_err():
                    self.bus = None
                    self.connected_var.set("DISCONNECTED")
                    self.connect_btn.configure(state=tk.NORMAL)
                    self.disconnect_btn.configure(state=tk.DISABLED)
                    messagebox.showerror("Connect failed", f"Could not open CAN bus.{e}")
                self.after(0, _on_err)

        threading.Thread(target=_worker, daemon=True).start()

    def on_disconnect(self):
        self._stop_cyclic()
        self.reader_stop.set()
        try:
            if self.bus is not None:
                try:
                    self.bus.shutdown()
                except Exception:
                    pass
        finally:
            self.bus = None
        self.connected_var.set("DISCONNECTED")
        self.connect_btn.configure(state=tk.NORMAL)
        self.disconnect_btn.configure(state=tk.DISABLED)

    def _reader_loop(self):
        while not self.reader_stop.is_set():
            bus = self.bus
            if bus is None:
                break
            try:
                msg = bus.recv(timeout=0.1)
                if msg is None:
                    continue
                try:
                    self.rx_queue.put_nowait(msg)
                except queue.Full:
                    pass
            except Exception:
                self.after(0, self.on_disconnect)
                break

    # ---------------------- RX processing ----------------------

    def _clear_rx(self):
        self.rx_entries.clear()
        for item in self.rx_tree.get_children():
            self.rx_tree.delete(item)
        self._raw_clear()

    def _toggle_rawlog(self):
        enabled = self.rawlog_var.get()
        state = "normal" if enabled else "disabled"
        self.raw_text.configure(state=state)
        if not enabled:
            self._raw_clear()

    def _raw_clear(self):
        self.raw_text.configure(state="normal")
        self.raw_text.delete("1.0", "end")
        self.raw_text.configure(state="disabled")

    def _raw_append(self, line: str):
        if not self.rawlog_var.get():
            return
        self.raw_text.configure(state="normal")
        self.raw_text.insert("end", line + "\n")
        lines = int(self.raw_text.index("end-1c").split(".")[0])
        if lines > self.max_raw_lines:
            self.raw_text.delete("1.0", f"{lines - self.max_raw_lines}.0")
        self.raw_text.see("end")
        self.raw_text.configure(state="disabled")

    def _drain_rx_queue(self):
        # Pull messages from the worker thread queue and update our aggregated cache.
        try:
            if not self.pause_var.get():
                f = self.filter_id_var.get().strip()
                filt_id = None
                if f:
                    try:
                        filt_id = parse_id(f)
                    except ValueError:
                        filt_id = None

                # Batch process to keep UI responsive
                processed = 0
                while processed < 200:
                    msg = self.rx_queue.get_nowait()
                    processed += 1
                    if filt_id is not None and msg.arbitration_id != filt_id:
                        continue

                    key = (bool(getattr(msg, "is_extended_id", False)), int(msg.arbitration_id))
                    ts = getattr(msg, "timestamp", now_s())
                    data = bytes(getattr(msg, "data", b"") or b"")
                    dlc = int(getattr(msg, "dlc", len(data)))
                    is_rtr = bool(getattr(msg, "is_remote_frame", False))
                    is_err = bool(getattr(msg, "is_error_frame", False))

                    entry = self.rx_entries.get(key)
                    if entry is None:
                        entry = RxEntry(
                            arbitration_id=msg.arbitration_id,
                            is_extended_id=bool(getattr(msg, "is_extended_id", False)),
                            is_remote_frame=is_rtr,
                            is_error_frame=is_err,
                            dlc=dlc,
                            data_hex=bytes_to_hex(data),
                            count=0,
                            last_ts=ts,
                            prev_ts=0.0,
                            period_ms=0.0,
                        )
                        self.rx_entries[key] = entry

                    entry.count += 1
                    entry.is_remote_frame = is_rtr
                    entry.is_error_frame = is_err
                    entry.dlc = dlc
                    entry.data_hex = bytes_to_hex(data) if not is_rtr else ""
                    entry.prev_ts = entry.last_ts
                    entry.last_ts = ts
                    if entry.prev_ts > 0:
                        entry.period_ms = (entry.last_ts - entry.prev_ts) * 1000.0

                    # Let the simulator respond to NMT/SDO requests from your Electron app.
                    try:
                        self.sim.handle_message(msg)
                    except Exception as _sim_e:
                        self._raw_append(f"SIM RX ERROR: {_sim_e}")

                    if self.rawlog_var.get():
                        arbid_str = f"{msg.arbitration_id:08X}" if entry.is_extended_id else f"{msg.arbitration_id:03X}"
                        flags = ("X" if entry.is_extended_id else "S") + ("R" if is_rtr else "-") + ("E" if is_err else "-")
                        self._raw_append(f"{arbid_str} [{dlc}] {bytes_to_hex(data)}  {flags}")

        except queue.Empty:
            pass

        # Throttle expensive UI updates
        t = now_s()
        if (t - self._last_rx_ui_refresh) >= 0.2:
            self._refresh_rx_tree_incremental()
            self._last_rx_ui_refresh = t

        self.after(50, self._drain_rx_queue)

    def _refresh_rx_tree_incremental(self):
        """Incrementally update the RX Treeview.

        The original implementation rebuilt the entire Treeview every 50 ms,
        which can freeze Tkinter on busy buses. This version updates/creates
        rows in-place and only sorts by recency.
        """
        t = now_s()

        # Determine current ordering by last timestamp
        items = sorted(self.rx_entries.values(), key=lambda e: e.last_ts, reverse=True)

        seen_tags = set()
        for e in items:
            arbid_str = f"{e.arbitration_id:08X}" if e.is_extended_id else f"{e.arbitration_id:03X}"
            last_ms = (t - e.last_ts) * 1000.0 if e.last_ts else 0.0
            key_tag = f"{int(e.is_extended_id)}:{e.arbitration_id}"
            seen_tags.add(key_tag)

            values = (
                arbid_str,
                "Y" if e.is_extended_id else "N",
                "Y" if e.is_remote_frame else "N",
                "Y" if e.is_error_frame else "N",
                str(e.dlc),
                e.data_hex,
                str(e.count),
                f"{last_ms:0.1f}",
                f"{e.period_ms:0.1f}" if e.period_ms else "",
            )

            iid = self._rx_iid_map.get(key_tag)
            if iid is None or not self.rx_tree.exists(iid):
                iid = self.rx_tree.insert("", "end", values=values, tags=(key_tag,))
                self._rx_iid_map[key_tag] = iid
            else:
                self.rx_tree.item(iid, values=values)

        # Remove rows that no longer exist (cleared / filtered)
        for key_tag, iid in list(self._rx_iid_map.items()):
            if key_tag not in seen_tags:
                try:
                    if self.rx_tree.exists(iid):
                        self.rx_tree.delete(iid)
                except Exception:
                    pass
                self._rx_iid_map.pop(key_tag, None)

        # Keep newest near top (cheap move)
        for idx, e in enumerate(items[:200]):  # don’t reorder thousands of rows
            key_tag = f"{int(e.is_extended_id)}:{e.arbitration_id}"
            iid = self._rx_iid_map.get(key_tag)
            if iid is not None and self.rx_tree.exists(iid):
                self.rx_tree.move(iid, "", idx)

    def _on_rx_select(self, _evt):
        sel = self.rx_tree.selection()
        if not sel:
            return
        vals = self.rx_tree.item(sel[0], "values")
        if not vals:
            return
        arbid_str, ext, rtr, _err, dlc, data, *_ = vals
        self.tx_id_var.set(arbid_str)
        self.tx_ext_var.set(ext == "Y")
        self.tx_rtr_var.set(rtr == "Y")
        self.tx_dlc_var.set(str(dlc))
        self.tx_data_var.set(data)
        self._on_rtr_toggle()

    # ---------------------- TX single-shot ----------------------

    def _on_rtr_toggle(self):
        if self.tx_rtr_var.get():
            self.tx_data_entry.configure(state="disabled")
        else:
            self.tx_data_entry.configure(state="normal")

    def on_send_once(self):
        if self.bus is None:
            messagebox.showerror("Send", "Not connected.")
            return

        try:
            arbid = parse_id(self.tx_id_var.get())
            is_ext = bool(self.tx_ext_var.get())
            is_rtr = bool(self.tx_rtr_var.get())
            dlc = int(self.tx_dlc_var.get())
            if dlc < 0 or dlc > 8:
                raise ValueError("DLC must be 0..8")
            if is_ext:
                if not is_valid_ext_id(arbid):
                    raise ValueError("Extended ID must be 0..1FFFFFFF")
            else:
                if not is_valid_std_id(arbid):
                    raise ValueError("Standard ID must be 0..7FF")

            data = b""
            if not is_rtr:
                data = parse_hex_bytes(self.tx_data_var.get())
                if len(data) > 8:
                    raise ValueError("Data max 8 bytes")
                if dlc < len(data):
                    data = data[:dlc]
                elif dlc > len(data):
                    data = data + bytes([0x00] * (dlc - len(data)))

            msg = can.Message(
                arbitration_id=arbid,
                is_extended_id=is_ext,
                is_remote_frame=is_rtr,
                data=(b"" if is_rtr else data),
                dlc=dlc,
            )
            self.bus.send(msg)

        except Exception as e:
            messagebox.showerror("Send failed", str(e))

    # ---------------------- Cyclic TX ----------------------

    def _load_cyclic_to_tx(self):
        """Load the selected cyclic entry into the TX (single-shot) fields for easy editing."""
        sel = self.cyc_tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        with self.cyclic_lock:
            if not (0 <= idx < len(self.cyclic_items)):
                return
            it = self.cyclic_items[idx]

        arbid_str = f"{it.arbitration_id:08X}" if it.is_extended_id else f"{it.arbitration_id:03X}"
        self.tx_id_var.set(arbid_str)
        self.tx_ext_var.set(it.is_extended_id)
        self.tx_rtr_var.set(it.is_remote_frame)
        self.tx_dlc_var.set(str(it.dlc))
        self.tx_data_var.set(bytes_to_hex(it.data) if not it.is_remote_frame else "")
        self._on_rtr_toggle()

    def _update_selected_cyclic_from_tx(self):
        """Update the selected cyclic entry using the current TX (single-shot) fields."""
        sel = self.cyc_tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        try:
            arbid = parse_id(self.tx_id_var.get())
            is_ext = bool(self.tx_ext_var.get())
            is_rtr = bool(self.tx_rtr_var.get())
            dlc = int(self.tx_dlc_var.get())
            if dlc < 0 or dlc > 8:
                raise ValueError("DLC must be 0..8")
            if is_ext:
                if not is_valid_ext_id(arbid):
                    raise ValueError("Extended ID must be 0..1FFFFFFF")
            else:
                if not is_valid_std_id(arbid):
                    raise ValueError("Standard ID must be 0..7FF")

            data = b""
            if not is_rtr:
                data = parse_hex_bytes(self.tx_data_var.get())
                if len(data) > 8:
                    raise ValueError("Data max 8 bytes")
                if dlc < len(data):
                    data = data[:dlc]
                elif dlc > len(data):
                    data = data + bytes([0x00] * (dlc - len(data)))

            with self.cyclic_lock:
                if not (0 <= idx < len(self.cyclic_items)):
                    return
                it = self.cyclic_items[idx]
                # keep existing name/interval/enabled, update frame contents
                it.arbitration_id = arbid
                it.is_extended_id = is_ext
                it.is_remote_frame = is_rtr
                it.dlc = dlc
                it.data = data

            self._refresh_cyclic_tree()

        except Exception as e:
            messagebox.showerror("Update cyclic failed", str(e))

    def _add_cyclic_from_tx(self):
        if self.bus is None:
            messagebox.showerror("Cyclic TX", "Connect first.")
            return

        dlg = CyclicAddDialog(self)
        self.wait_window(dlg)
        if not dlg.ok:
            return

        try:
            arbid = parse_id(self.tx_id_var.get())
            is_ext = bool(self.tx_ext_var.get())
            is_rtr = bool(self.tx_rtr_var.get())
            dlc = int(self.tx_dlc_var.get())
            if dlc < 0 or dlc > 8:
                raise ValueError("DLC must be 0..8")

            data = b""
            if not is_rtr:
                data = parse_hex_bytes(self.tx_data_var.get())
                if len(data) > 8:
                    raise ValueError("Data max 8 bytes")
                if dlc < len(data):
                    data = data[:dlc]
                elif dlc > len(data):
                    data = data + bytes([0x00] * (dlc - len(data)))

            item = CyclicTxItem(
                enabled=True,
                name=dlg.name.get().strip() or "TX",
                arbitration_id=arbid,
                is_extended_id=is_ext,
                is_remote_frame=is_rtr,
                dlc=dlc,
                data=data,
                interval_ms=int(dlg.interval_ms.get()),
            )
            if item.interval_ms < 1:
                raise ValueError("Interval must be >= 1 ms")

            with self.cyclic_lock:
                self.cyclic_items.append(item)

            self._refresh_cyclic_tree()

        except Exception as e:
            messagebox.showerror("Add cyclic failed", str(e))

    def _refresh_cyclic_tree(self):
        for item in self.cyc_tree.get_children():
            self.cyc_tree.delete(item)

        with self.cyclic_lock:
            for idx, it in enumerate(self.cyclic_items):
                arbid_str = f"{it.arbitration_id:08X}" if it.is_extended_id else f"{it.arbitration_id:03X}"
                self.cyc_tree.insert(
                    "",
                    "end",
                    iid=str(idx),
                    values=(
                        "Y" if it.enabled else "N",
                        it.name,
                        arbid_str,
                        "Y" if it.is_extended_id else "N",
                        "Y" if it.is_remote_frame else "N",
                        str(it.dlc),
                        bytes_to_hex(it.data) if not it.is_remote_frame else "",
                        str(it.interval_ms),
                        str(it.tx_count),
                    ),
                )

    def _toggle_cyclic_enable(self):
        sel = self.cyc_tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        with self.cyclic_lock:
            if 0 <= idx < len(self.cyclic_items):
                self.cyclic_items[idx].enabled = not self.cyclic_items[idx].enabled
        self._refresh_cyclic_tree()

    def _remove_cyclic(self):
        sel = self.cyc_tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        with self.cyclic_lock:
            if 0 <= idx < len(self.cyclic_items):
                self.cyclic_items.pop(idx)
        self._refresh_cyclic_tree()

    def _start_cyclic(self):
        if self.bus is None:
            messagebox.showerror("Cyclic TX", "Not connected.")
            return
        # Reset schedules so everything starts immediately and predictably
        t = now_s()
        with self.cyclic_lock:
            for it in self.cyclic_items:
                it.next_due = t
        self.cyclic_running = True
        self.cyclic_status_var.set("Cyclic: RUNNING")
        self.cyc_start_btn.configure(state=tk.DISABLED)
        self.cyc_stop_btn.configure(state=tk.NORMAL)

    def _stop_cyclic(self):
        self.cyclic_running = False
        self.cyclic_status_var.set("Cyclic: STOPPED")
        self.cyc_start_btn.configure(state=tk.NORMAL)
        self.cyc_stop_btn.configure(state=tk.DISABLED)

    def _cyclic_tick(self):
        try:
            self.sim.tick()
        except Exception as _sim_e:
            self._raw_append(f"SIM TICK ERROR: {_sim_e}")

        if self.cyclic_running and self.bus is not None:
            t = now_s()
            send_list = []
            with self.cyclic_lock:
                for it in self.cyclic_items:
                    if not it.enabled:
                        continue
                    if t >= it.next_due:
                        send_list.append(it)
                        it.next_due = t + (it.interval_ms / 1000.0)

            for it in send_list:
                try:
                    msg = can.Message(
                        arbitration_id=it.arbitration_id,
                        is_extended_id=it.is_extended_id,
                        is_remote_frame=it.is_remote_frame,
                        data=(b"" if it.is_remote_frame else it.data),
                        dlc=it.dlc,
                    )
                    self.bus.send(msg)

                    # Counters
                    it.tx_count += 1
                    it.last_tx_ts = now_s()

                    # Log TX so you can verify something is actually being sent.
                    arbid_str = f"{it.arbitration_id:08X}" if it.is_extended_id else f"{it.arbitration_id:03X}"
                    self._raw_append(f"TX {arbid_str} [{it.dlc}] {bytes_to_hex(it.data) if not it.is_remote_frame else ''}")

                except Exception as e:
                    # Stop cyclic and surface the error (don’t fail silently)
                    self.cyclic_status_var.set(f"Cyclic: ERROR - {e}")
                    self._stop_cyclic()
                    self.after(0, lambda: messagebox.showerror("Cyclic TX send failed", str(e)))
                    break

        self.after(10, self._cyclic_tick)

    # ---------------------- Sevcon simulator UI ----------------------

    def _open_simulator_window(self):
        if self.sim_window is not None and self.sim_window.winfo_exists():
            self.sim_window.lift()
            return
        self.sim_window = SevconSimWindow(self, self.sim)

    # ---------------------- Close ----------------------

    def on_close(self):
        try:
            self.on_disconnect()
        except Exception:
            pass
        self.destroy()


# ---------------------- Save/Load cyclic list ----------------------

    def _default_profiles_dir(self) -> Path:
        d = Path.home() / "Documents" / "CANable" / "profiles"
        d.mkdir(parents=True, exist_ok=True)
        return d

    def _cyclic_to_dict(self, it: CyclicTxItem) -> dict:
        return {
            "enabled": bool(it.enabled),
            "name": it.name,
            "arbitration_id": int(it.arbitration_id),
            "is_extended_id": bool(it.is_extended_id),
            "is_remote_frame": bool(it.is_remote_frame),
            "dlc": int(it.dlc),
            "data_hex": (it.data.hex().upper() if (not it.is_remote_frame) else ""),
            "interval_ms": int(it.interval_ms),
        }

    def _dict_to_cyclic(self, d: dict) -> CyclicTxItem:
        data = bytes.fromhex(d.get("data_hex", "") or "")
        it = CyclicTxItem(
            enabled=bool(d.get("enabled", True)),
            name=str(d.get("name", "TX")),
            arbitration_id=int(d.get("arbitration_id", 0)),
            is_extended_id=bool(d.get("is_extended_id", False)),
            is_remote_frame=bool(d.get("is_remote_frame", False)),
            dlc=int(d.get("dlc", len(data))),
            data=data,
            interval_ms=int(d.get("interval_ms", 100)),
        )
        it.next_due = now_s()
        return it

    def _save_cyclic_profile(self):
        try:
            from tkinter import filedialog
        except Exception as e:
            messagebox.showerror("Save", f"filedialog not available: {e}")
            return

        initialdir = str(self._default_profiles_dir())
        initialfile = "cyclic_list.json"
        path = filedialog.asksaveasfilename(
            title="Save cyclic list",
            initialdir=initialdir,
            initialfile=initialfile,
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*")],
        )
        if not path:
            return

        with self.cyclic_lock:
            payload = {
                "schema": "canable_cyclic_profile_v1",
                "saved_at": time.strftime("%Y-%m-%d %H:%M:%S"),
                "items": [self._cyclic_to_dict(it) for it in self.cyclic_items],
            }

        try:
            Path(path).write_text(json.dumps(payload, indent=2), encoding="utf-8")
            self.last_profile_path = Path(path)
            self.cyclic_status_var.set(f"Cyclic: saved to {self.last_profile_path.name}")
        except Exception as e:
            messagebox.showerror("Save failed", str(e))

    def _load_cyclic_profile(self):
        try:
            from tkinter import filedialog
        except Exception as e:
            messagebox.showerror("Load", f"filedialog not available: {e}")
            return

        initialdir = str(self._default_profiles_dir())
        path = filedialog.askopenfilename(
            title="Load cyclic list",
            initialdir=initialdir,
            filetypes=[("JSON files", "*.json"), ("All files", "*")],
        )
        if not path:
            return

        try:
            raw = Path(path).read_text(encoding="utf-8")
            payload = json.loads(raw)
            if payload.get("schema") != "canable_cyclic_profile_v1":
                # still try best-effort if it looks like an older/simple format
                pass
            items = payload.get("items", []) if isinstance(payload, dict) else []
            new_list = [self._dict_to_cyclic(d) for d in items if isinstance(d, dict)]
        except Exception as e:
            messagebox.showerror("Load failed", str(e))
            return

        with self.cyclic_lock:
            self.cyclic_items = new_list

        self._refresh_cyclic_tree()
        self.last_profile_path = Path(path)
        self.cyclic_status_var.set(f"Cyclic: loaded {len(new_list)} item(s) from {self.last_profile_path.name}")



class SevconSimWindow(tk.Toplevel):
    def __init__(self, master: CanMonitorApp, sim: SevconSimulator):
        super().__init__(master)
        self.title("Sevcon Gen4 Controller Simulator")
        self.geometry("980x680")
        self.master_app = master
        self.sim = sim
        self.slider_vars: dict[tuple[int, int], tk.IntVar] = {}

        self.node_var = tk.StringVar(value=str(sim.node_id))
        self.od_path_var = tk.StringVar(value=str(Path(__file__).with_name("sevcon_gen4_object_dictionary_v2.json")))
        self.force_enable_var = tk.BooleanVar(value=True)
        self.standard_tpdo_var = tk.BooleanVar(value=True)
        self.nmt_var = tk.StringVar(value="Operational")

        top = ttk.LabelFrame(self, text="Simulator Setup")
        top.pack(side=tk.TOP, fill=tk.X, padx=10, pady=8)

        ttk.Label(top, text="Node ID:").grid(row=0, column=0, padx=6, pady=4, sticky="w")
        ttk.Entry(top, textvariable=self.node_var, width=8).grid(row=0, column=1, padx=6, pady=4, sticky="w")
        ttk.Label(top, text="Object dictionary:").grid(row=0, column=2, padx=6, pady=4, sticky="e")
        ttk.Entry(top, textvariable=self.od_path_var, width=70).grid(row=0, column=3, padx=6, pady=4, sticky="we")
        ttk.Button(top, text="Browse…", command=self._browse_od).grid(row=0, column=4, padx=6, pady=4)

        ttk.Checkbutton(top, text="Force-enable TPDOs", variable=self.force_enable_var).grid(row=1, column=0, columnspan=2, padx=6, pady=4, sticky="w")
        ttk.Checkbutton(top, text="Use standard TPDO IDs", variable=self.standard_tpdo_var).grid(row=2, column=0, columnspan=2, padx=6, pady=4, sticky="w")
        ttk.Label(top, text="NMT state:").grid(row=1, column=2, padx=6, pady=4, sticky="e")
        ttk.Combobox(top, textvariable=self.nmt_var, values=["Operational", "Pre-operational", "Stopped"], width=18, state="readonly").grid(row=1, column=3, padx=6, pady=4, sticky="w")
        ttk.Button(top, text="Load OD", command=self._load_od).grid(row=1, column=4, padx=6, pady=4)
        ttk.Button(top, text="Start Simulator", command=self._start).grid(row=2, column=3, padx=6, pady=4, sticky="e")
        ttk.Button(top, text="Stop", command=self._stop).grid(row=2, column=4, padx=6, pady=4)
        top.grid_columnconfigure(3, weight=1)

        nb = ttk.Notebook(self)
        nb.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        self.sliders_frame = ttk.Frame(nb)
        self.tpdo_frame = ttk.Frame(nb)
        self.sdo_frame = ttk.Frame(nb)
        nb.add(self.sliders_frame, text="TPDO Sliders")
        nb.add(self.tpdo_frame, text="TPDO Map")
        nb.add(self.sdo_frame, text="SDO / Object Values")

        self._build_sliders_empty()
        self._build_tpdo_table()
        self._build_sdo_tab()
        self.after(500, self._refresh_periodic)

    def _browse_od(self):
        from tkinter import filedialog
        path = filedialog.askopenfilename(title="Select Sevcon object dictionary JSON", filetypes=[("JSON", "*.json"), ("All files", "*")])
        if path:
            self.od_path_var.set(path)

    def _load_od(self):
        try:
            self.sim.node_id = int(self.node_var.get(), 0)
            if not (1 <= self.sim.node_id <= 127):
                raise ValueError("Node ID must be 1..127")
            self.sim.force_enable_tpdos = bool(self.force_enable_var.get())
            self.sim.standard_tpdo_cobids = bool(self.standard_tpdo_var.get())
            self.sim.load_od(self.od_path_var.get())
            self._apply_nmt_from_ui()
            self._rebuild_sliders()
            self._refresh_tpdo_table()
            self.master_app.sim_status_var.set(f"Simulator: OD loaded, node {self.sim.node_id}")
        except Exception as e:
            messagebox.showerror("Load OD failed", str(e))

    def _apply_nmt_from_ui(self):
        text = self.nmt_var.get()
        self.sim.nmt_state = 0x05 if text == "Operational" else (0x04 if text == "Stopped" else 0x7F)

    def _start(self):
        if self.master_app.bus is None:
            messagebox.showerror("Simulator", "Connect to the CAN adapter first.")
            return
        if not self.sim.od:
            self._load_od()
        self._apply_nmt_from_ui()
        self.sim.enabled = True
        self.sim.next_heartbeat = now_s()
        for tpdo in self.sim.tpdos:
            tpdo.next_due = now_s()
        self.master_app.sim_status_var.set(f"Simulator: ON, node {self.sim.node_id}")

    def _stop(self):
        self.sim.enabled = False
        self.master_app.sim_status_var.set("Simulator: OFF")

    def _build_sliders_empty(self):
        ttk.Label(self.sliders_frame, text="Load the object dictionary to create sliders from the active TPDO mapping.").pack(anchor="w", padx=10, pady=10)

    def _rebuild_sliders(self):
        for child in self.sliders_frame.winfo_children():
            child.destroy()
        self.slider_vars.clear()
        canvas = tk.Canvas(self.sliders_frame)
        scroll = ttk.Scrollbar(self.sliders_frame, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)

        seen = set()
        row = 0
        for tpdo in self.sim.tpdos:
            ttk.Label(inner, text=f"TPDO{tpdo.number}  COB-ID 0x{tpdo.cob_id:X}  every {tpdo.interval_ms} ms", font=("TkDefaultFont", 10, "bold")).grid(row=row, column=0, columnspan=5, sticky="w", padx=8, pady=(10, 3))
            row += 1
            for m in tpdo.mappings:
                key = (m.index, m.sub)
                if key in seen:
                    continue
                seen.add(key)
                meta = self.sim.meta.get(key, {})
                lo = _parse_od_int(meta.get("low_limit"), self.sim.node_id, 0)
                hi = _parse_od_int(meta.get("high_limit"), self.sim.node_id, 0)
                if hi <= lo or hi > 1000000:
                    # Friendly default ranges for unknown/scary raw limits.
                    if _dtype_signed(m.dtype):
                        lo, hi = -10000, 10000
                    else:
                        lo, hi = 0, 10000
                val = max(lo, min(hi, self.sim.get_value(m.index, m.sub)))
                var = tk.IntVar(value=val)
                self.slider_vars[key] = var
                label = f"0x{m.index:04X}:{m.sub:02X}  {m.name}"
                ttk.Label(inner, text=label, width=42).grid(row=row, column=0, sticky="w", padx=8, pady=3)
                scale = ttk.Scale(inner, from_=lo, to=hi, orient=tk.HORIZONTAL, length=330, variable=var, command=lambda _v, k=key, vv=var: self._slider_changed(k, vv))
                scale.grid(row=row, column=1, sticky="we", padx=8, pady=3)
                ent = ttk.Entry(inner, width=12, textvariable=var)
                ent.grid(row=row, column=2, sticky="w", padx=4, pady=3)
                ent.bind("<Return>", lambda _e, k=key, vv=var: self._slider_changed(k, vv))
                units = meta.get("units") or "raw"
                ttk.Label(inner, text=units, width=8).grid(row=row, column=3, sticky="w", padx=4, pady=3)
                row += 1
        inner.grid_columnconfigure(1, weight=1)

    def _slider_changed(self, key, var):
        try:
            self.sim.set_value(key[0], key[1], int(float(var.get())))
        except Exception:
            pass

    def _build_tpdo_table(self):
        cols = ("tpdo", "cob", "enabled", "interval", "mapped")
        self.tpdo_tree = ttk.Treeview(self.tpdo_frame, columns=cols, show="headings")
        for c, w in zip(cols, (70, 90, 80, 90, 650)):
            self.tpdo_tree.heading(c, text=c.upper())
            self.tpdo_tree.column(c, width=w, anchor="w")
        self.tpdo_tree.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)

    def _refresh_tpdo_table(self):
        for item in self.tpdo_tree.get_children():
            self.tpdo_tree.delete(item)
        for tpdo in self.sim.tpdos:
            mapped = "; ".join(f"0x{m.index:04X}:{m.sub:02X} {m.name} ({m.bits}b)" for m in tpdo.mappings)
            self.tpdo_tree.insert("", "end", values=(f"TPDO{tpdo.number}", f"0x{tpdo.cob_id:X}", "Y" if tpdo.enabled else "N", tpdo.interval_ms, mapped))

    def _build_sdo_tab(self):
        top = ttk.Frame(self.sdo_frame)
        top.pack(side=tk.TOP, fill=tk.X, padx=8, pady=8)
        self.sdo_index_var = tk.StringVar(value="0x6041")
        self.sdo_sub_var = tk.StringVar(value="0x00")
        self.sdo_val_var = tk.StringVar(value="0")
        ttk.Label(top, text="Index:").pack(side=tk.LEFT)
        ttk.Entry(top, textvariable=self.sdo_index_var, width=10).pack(side=tk.LEFT, padx=4)
        ttk.Label(top, text="Sub:").pack(side=tk.LEFT)
        ttk.Entry(top, textvariable=self.sdo_sub_var, width=6).pack(side=tk.LEFT, padx=4)
        ttk.Label(top, text="Value:").pack(side=tk.LEFT)
        ttk.Entry(top, textvariable=self.sdo_val_var, width=14).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="Read Local", command=self._sdo_read_local).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="Write Local", command=self._sdo_write_local).pack(side=tk.LEFT, padx=4)

        cols = ("idx", "sub", "name", "type", "access", "value")
        self.sdo_tree = ttk.Treeview(self.sdo_frame, columns=cols, show="headings")
        for c, w in zip(cols, (80, 50, 360, 110, 70, 120)):
            self.sdo_tree.heading(c, text=c.upper())
            self.sdo_tree.column(c, width=w, anchor="w")
        self.sdo_tree.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))
        self.sdo_tree.bind("<<TreeviewSelect>>", self._on_sdo_select)

    def _sdo_read_local(self):
        try:
            idx = int(self.sdo_index_var.get(), 0)
            sub = int(self.sdo_sub_var.get(), 0)
            self.sdo_val_var.set(str(self.sim.get_value(idx, sub)))
        except Exception as e:
            messagebox.showerror("Read local", str(e))

    def _sdo_write_local(self):
        try:
            idx = int(self.sdo_index_var.get(), 0)
            sub = int(self.sdo_sub_var.get(), 0)
            val = int(self.sdo_val_var.get(), 0)
            self.sim.set_value(idx, sub, val)
            key = (idx, sub)
            if key in self.slider_vars:
                self.slider_vars[key].set(val)
            self._refresh_sdo_values()
        except Exception as e:
            messagebox.showerror("Write local", str(e))

    def _on_sdo_select(self, _evt):
        sel = self.sdo_tree.selection()
        if not sel:
            return
        vals = self.sdo_tree.item(sel[0], "values")
        if vals:
            self.sdo_index_var.set(vals[0])
            self.sdo_sub_var.set(vals[1])
            self.sdo_val_var.set(vals[5])

    def _refresh_sdo_values(self):
        for item in self.sdo_tree.get_children():
            self.sdo_tree.delete(item)
        # Show TPDO mapped objects first, then common CANopen objects.
        keys = []
        for tpdo in self.sim.tpdos:
            for m in tpdo.mappings:
                if (m.index, m.sub) not in keys:
                    keys.append((m.index, m.sub))
        for key in [(0x1000,0), (0x1001,0), (0x1017,0), (0x1018,1), (0x1018,2), (0x1018,3), (0x1018,4)]:
            if key not in keys:
                keys.append(key)
        for idx, sub in keys:
            meta = self.sim.meta.get((idx, sub), {})
            self.sdo_tree.insert("", "end", values=(f"0x{idx:04X}", f"0x{sub:02X}", meta.get("name", ""), meta.get("data_type", ""), meta.get("access", ""), self.sim.get_value(idx, sub)))

    def _refresh_periodic(self):
        if self.winfo_exists():
            self._refresh_sdo_values()
            self._refresh_tpdo_table()
            self.after(1000, self._refresh_periodic)


class CyclicAddDialog(tk.Toplevel):
    def __init__(self, master: tk.Tk):
        super().__init__(master)
        self.title("Add Cyclic TX")
        self.resizable(False, False)
        self.ok = False

        self.interval_ms = tk.StringVar(value="100")
        self.name = tk.StringVar(value="TX")

        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=12, pady=10)

        ttk.Label(frm, text="Name:").grid(row=0, column=0, sticky="w", padx=6, pady=6)
        ttk.Entry(frm, textvariable=self.name, width=24).grid(row=0, column=1, sticky="w", padx=6, pady=6)

        ttk.Label(frm, text="Interval (ms):").grid(row=1, column=0, sticky="w", padx=6, pady=6)
        ttk.Entry(frm, textvariable=self.interval_ms, width=10).grid(row=1, column=1, sticky="w", padx=6, pady=6)

        btns = ttk.Frame(frm)
        btns.grid(row=2, column=0, columnspan=2, sticky="e", pady=(8, 0))

        ttk.Button(btns, text="Cancel", command=self._cancel).pack(side=tk.RIGHT, padx=6)
        ttk.Button(btns, text="Add", command=self._add).pack(side=tk.RIGHT, padx=6)

        self.bind("<Return>", lambda _e: self._add())
        self.bind("<Escape>", lambda _e: self._cancel())

        self.grab_set()
        self.transient(master)
        self.wait_visibility()
        self.focus_set()

    def _add(self):
        try:
            v = int(self.interval_ms.get())
            if v < 1:
                raise ValueError
        except Exception:
            messagebox.showerror("Invalid interval", "Interval must be an integer >= 1 ms.")
            return
        self.ok = True
        self.destroy()

    def _cancel(self):
        self.ok = False
        self.destroy()


if __name__ == "__main__":
    app = CanMonitorApp()
    app.mainloop()
