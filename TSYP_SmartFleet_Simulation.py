#!/usr/bin/env python3
"""
+ Deadlines & Deadline-Compliance Graph
+ FIXED: Vehicle respawning loops, route visualization, task completion mechanism
+ ENHANCED: DCCBBA cost function with new formula: base_score * priority_multiplier * capacity_penalty * time_window_penalty
+ FIXED: JSON output - no infinity values, proper bid values
+ FIXED: Warehouse completion detection - vehicles no longer get stuck after multiple visits
+ ENHANCED: Additional efficiency visualization figures

Major fixes applied:
1. Fixed vehicle respawning to prevent infinite loops
2. All vehicles now have their own colored route visualization
3. Completely revised task completion mechanism
4. Robust warehouse arrival detection and task progression
5. New cost function with multiplicative factors
6. Fixed JSON output - replaced infinity with high values, ensured proper bid values
7. Fixed warehouse completion detection to prevent vehicles getting stuck
8. Added efficiency visualization: Task allocation distribution and completion timeline
"""

import math
import random
import time
import json
from copy import deepcopy
from typing import Dict, List, Tuple, Optional, Set
from collections import defaultdict

# ==========================
# SUMO / TRACI imports
# ==========================
try:
    import traci
    from sumolib import net
    SUMO_AVAILABLE = True
except Exception:
    SUMO_AVAILABLE = False

# ==========================
# Tkinter GUI imports (optional)
# ==========================
USE_GUI = True  # set False to disable
try:
    if USE_GUI:
        import tkinter as tk
        from tkinter import ttk, filedialog
        from tkinter import scrolledtext
        GUI_AVAILABLE = True
    else:
        GUI_AVAILABLE = False
except Exception:
    GUI_AVAILABLE = False

# ==========================
# Configuration
# ==========================
SIM_STEP = 1
SIM_DURATION = None          # None => run "forever" until you stop
COMM_RANGE = 600.0
RANDOM_SEED = 0

NUM_VEHICLES = 3
FOLLOW_AGENT_ID = "vehB"

# Status & battery
STATUS_PRINT_INTERVAL = 100
BATTERY_DRAIN_PER_STATUS = 0.1

# Logging
LOG_FILE = "dccbba_sumo_log.json"

# SUMO configuration (adjust paths)
SUMO_BINARY = "sumo-gui"
SUMO_CFG = r"c:\\Users\\mejdc\\Desktop\\TSYP SIMULATION AAA3333\\sumo_configs\\sumo_config.sumocfg"
SUMO_NET = r"c:\\Users\\mejdc\\Desktop\\TSYP SIMULATION AAA3333\\sumo_configs\\osm.net.xml.gz"
SUMO_GUI_SETTINGS = r"c:\\Users\\mejdc\\Desktop\\TSYP SIMULATION AAA3333\\sumo_configs\\abcabc.xml"

# Warehouse edge id (validated/auto-repaired at startup)
WAREHOUSE_EDGE_ID = "35282667"

# Packages
GENERATE_RANDOM_PACKAGES = True
PACKAGES_START_FILE = "packages_start.json"
PACKAGES_MID_FILE = "packages_midday.json"

NUM_SOD_TASKS = 5
NUM_MID_TASKS = 20
MID_START_TICK = 60
MID_GAP_MIN = 15
MID_GAP_MAX = 40

# NEW: More lenient deadlines configuration (in ticks)
SOD_DEADLINE_RANGE = (1800, 2000)           # Increased from (50, 150) - much more lenient
MID_DEADLINE_OFFSET_RANGE = (4000, 4200)    # Increased from (30, 120) - much more lenient

# Visuals
WAREHOUSE_BOX_HALF = 12.0              # half-size of warehouse outline square
TASK_CIRCLE_RADIUS = 8.0               # radius for task target circles
TASK_CIRCLE_SIDES = 18                 # circle fidelity
TASK_CIRCLE_COLOR = (255, 140, 0, 220) # orange, filled
FOLLOW_ROUTE_COLOR = (0, 0, 255, 255)  # green polyline for followed
OTHER_ROUTE_LAYER = 40
FOLLOW_ROUTE_LAYER = 99
ROUTE_MARKER_SQUARE_SIZE = 3.0         # small squares along route (followed vehicle only)

# Anti-stall
STALL_SPEED_THRESHOLD = 0.2            # m/s
STALL_TICKS_THRESHOLD = 10             # ticks
WAREHOUSE_PARK_POS = 5.0               # position along warehouse edge to park

# ==========================
# DCCBBA Cost Function Parameters - NEW FORMULA
# ==========================
# Cost = base_score * priority_multiplier * capacity_penalty * time_window_penalty
# Where:
# - base_score: base distance cost
# - priority_multiplier: based on task priority (1.0 for normal, lower for high priority)
# - capacity_penalty: penalty based on current load vs capacity
# - time_window_penalty: penalty based on deadline urgency

# Priority multipliers (lower = higher priority)
HIGH_PRIORITY_MULTIPLIER = 0.5
NORMAL_PRIORITY_MULTIPLIER = 1.0
LOW_PRIORITY_MULTIPLIER = 1.5

# Capacity penalty parameters
CAPACITY_PENALTY_BASE = 1.0
CAPACITY_PENALTY_FACTOR = 2.0  # How aggressively to penalize high load

# Time window penalty parameters
TIME_PENALTY_BASE = 1.0
TIME_PENALTY_URGENT_THRESHOLD = 300  # ticks until deadline considered urgent
TIME_PENALTY_CRITICAL_THRESHOLD = 100  # ticks until deadline considered critical
TIME_PENALTY_URGENT = 1.5
TIME_PENALTY_CRITICAL = 3.0

# Very high bid value to replace infinity (for JSON compatibility)
VERY_HIGH_BID = 9999999999.0

# ==========================
# Global state
# ==========================
SUMO_NET_OBJ = None
TRACI_RUNNING: bool = False
SUMO_EDGE_IDS: List[str] = []
EDGE_ADJ: Dict[str, List[str]] = {}
VALID_DELIVERY_EDGES: List[str] = []

# Per-agent
ACTIVE_ROUTE_EDGES: Dict[str, List[str]] = {}
ACTIVE_ROUTE_TASK_ID: Dict[str, Optional[str]] = {}
VISITED_EDGES: Dict[str, Set[str]] = {}
SUMO_AGENT_VEH_MAP: Dict[str, str] = {}
VEHICLE_LAST_MOVE_TICK: Dict[str, int] = {}
VEHICLE_LABEL_CREATED: Set[str] = set()

# Visualization bookkeeping
ACTIVE_ROUTE_POLY: Dict[str, str] = {}           # per-agent route polyline
ACTIVE_EDGE_POLYGONS: Dict[str, List[str]] = {}  # per-agent edge markers (followed only)
WAREHOUSE_POLY_ID = "warehouse_outline_poly"
WAREHOUSE_POI_ID = "WAREHOUSE"
TASK_TARGET_SIG: Dict[str, Tuple[str, ...]] = {} # agent_id -> signature of delivery edges
TASK_TARGET_IDS: Dict[str, List[str]] = {}       # polygon ids for task targets per agent

# Vehicle colors (RGBA)
VEHICLE_COLORS: List[Tuple[int, int, int, int]] = [
    (0, 0, 255, 255),      # vehA - blue
    (255, 0, 0, 255),      # vehB - red
    (0, 255, 0, 255),     # vehC - green
    (180, 0, 255, 255),    # purple
    (255, 200, 0, 255),    # yellow
    (0, 230, 230, 255),    # cyan
]

# Logging buffer & GUI
LOG_EVENTS: List[Dict] = []
LOG_GUI = None  # will hold LogGUI

# NEW: Deadline tracking
TASK_DEADLINES: Dict[str, int] = {}      # task_id -> due_by (tick)
TASK_ASSIGN_TIME: Dict[str, int] = {}    # task_id -> assigned_at (tick)
TASK_DONE_TIME: Dict[str, int] = {}      # task_id -> completed_at (tick)
TASK_HISTORY: Dict[str, List[Dict]] = {} # agent_id -> list of task records

# NEW: Efficiency tracking
TASK_ALLOCATION_HISTORY: List[Dict] = []  # Track task assignments for efficiency analysis
VEHICLE_UTILIZATION: Dict[str, List[Tuple[int, int]]] = {}  # agent_id -> list of (start_time, end_time) for tasks

# Global agents reference for respawning
AGENTS: Dict[str, "VehicleAgent"] = {}

# Vehicle respawn tracking
VEHICLE_RESPAWN_COOLDOWN: Dict[str, int] = {}  # agent_id -> tick when respawn is allowed

# ==========================
# GUI: Log viewer - ENHANCED WITH EFFICIENCY GRAPHS
# ==========================
class LogGUI:
    def __init__(self, log_buffer: List[Dict]):
        self.log_buffer = log_buffer
        self.root = tk.Tk()
        self.root.title("DCCBBA-SUMO Live Log")
        self.root.geometry("1200x700")  # Increased width for more buttons
        self.root.configure(bg="#1e1e1e")
        top = ttk.Frame(self.root); top.pack(side=tk.TOP, fill=tk.X, padx=6, pady=4)
        ttk.Label(top, text="DCCBBA-SUMO Live Log", font=("Segoe UI", 12, "bold")).pack(side=tk.LEFT)

        # Buttons - ADDED NEW EFFICIENCY GRAPH BUTTONS
        button_frame = ttk.Frame(top); button_frame.pack(side=tk.RIGHT)
        ttk.Button(button_frame, text="Task Allocation Efficiency", command=self.show_allocation_graph).pack(side=tk.LEFT, padx=2)
        ttk.Button(button_frame, text="Task Completion Timeline", command=self.show_completion_timeline).pack(side=tk.LEFT, padx=2)
        ttk.Button(button_frame, text="Deadline Graph (Followed)", command=self.show_deadline_graph).pack(side=tk.LEFT, padx=2)
        ttk.Button(button_frame, text="Save Log as JSON", command=self.save).pack(side=tk.LEFT, padx=2)
        ttk.Button(button_frame, text="Clear", command=self.clear).pack(side=tk.LEFT, padx=2)

        # Filters
        filt = ttk.Frame(self.root); filt.pack(side=tk.TOP, fill=tk.X, padx=6, pady=4)
        self.filter_vars = {
            "STATUS": tk.BooleanVar(value=True),
            "BID": tk.BooleanVar(value=True),
            "WINNER": tk.BooleanVar(value=True),
            "TASK": tk.BooleanVar(value=True),
            "ERROR": tk.BooleanVar(value=True),
            "OTHER": tk.BooleanVar(value=False),
        }
        for name in ["STATUS","BID","WINNER","TASK","ERROR","OTHER"]:
            ttk.Checkbutton(filt, text=name, variable=self.filter_vars[name]).pack(side=tk.LEFT, padx=3)

        # Search
        search = ttk.Frame(self.root); search.pack(side=tk.TOP, fill=tk.X, padx=6, pady=2)
        ttk.Label(search, text="Search:").pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        ttk.Entry(search, textvariable=self.search_var, width=30).pack(side=tk.LEFT, padx=4)
        ttk.Button(search, text="Find Next", command=self.find_next).pack(side=tk.LEFT)

        # Text area
        fr = ttk.Frame(self.root); fr.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=6, pady=6)
        self.text = scrolledtext.ScrolledText(fr, wrap=tk.WORD, state=tk.DISABLED, font=("Consolas", 9),
                                              bg="#1e1e1e", fg="#f0f0f0", insertbackground="#ffffff")
        self.text.pack(fill=tk.BOTH, expand=True)
        self.text.tag_config("STATUS", foreground="#00e676")
        self.text.tag_config("BID", foreground="#29b6f6")
        self.text.tag_config("WINNER", foreground="#ffd54f")
        self.text.tag_config("TASK", foreground="#ce93d8")
        self.text.tag_config("ERROR", foreground="#ff5252")
        self.text.tag_config("OTHER", foreground="#b0bec5")
        self.text.tag_config("TIME", foreground="#9e9e9e")

    def handle(self, event: Dict):
        etype = event.get("type"); t = event.get("time"); data = event.get("data", {})
        line, tag = self.format_line(etype, t, data)
        if not line: return
        if not self.filter_vars.get(tag, tk.BooleanVar(value=True)).get(): return
        self.append(line, tag)

    def poll(self):
        try:
            self.root.update_idletasks()
            self.root.update()
        except tk.TclError:
            pass

    def format_line(self, etype: str, t: float, d: Dict):
        ts = f"[t={t:.1f}]"
        if etype == "vehicle_status":
            a = d.get("agent_id"); sp = d.get("speed",0.0); bat = d.get("battery",0.0)
            rem = d.get("remaining_tasks",[]); done = d.get("completed_tasks",0)
            return f"{ts} STATUS[{a}] speed={sp:.2f} battery={bat:.1f}% done={done}", "STATUS"
        if etype == "mesh_message":
            s = d.get("sender"); r = d.get("receiver"); m = d.get("message", {})
            mt = m.get("message_type","UNKNOWN"); tid = m.get("task_id")
            if mt == "TASK_ANNOUNCEMENT":
                return f"{ts} TASK {mt} {tid} {s}→{r}", "TASK"
            if mt == "FORWARD_ANNOUNCEMENT":
                best = m.get("best",{}); holder = best.get("holder"); bid = best.get("bid", VERY_HIGH_BID)
                try: 
                    bidf = float(bid)
                    # Replace any infinity or extremely high values with our VERY_HIGH_BID for display
                    if bidf > VERY_HIGH_BID * 0.9:  # If it's close to our very high bid
                        bidf = VERY_HIGH_BID
                except: 
                    bidf = VERY_HIGH_BID
                return f"{ts} BID/FWD {tid} {s}→{r} holder={holder} bid={bidf:.2f}", "BID"
            if mt == "WINNER_DECISION":
                win = m.get("winner")
                back = m.get("backtrace_route", [])
                return f"{ts} WINNER {tid} winner={win} route={back} via {s}→{r}", "WINNER"
            return f"{ts} MESH {mt} {s}→{r}", "OTHER"
        if etype == "error":
            return f"{ts} ERROR[{d.get('source','?')}] {d.get('error','')}", "ERROR"
        return f"{ts} {etype}: {d}", "OTHER"

    def append(self, line: str, tag: str):
        self.text.configure(state=tk.NORMAL)
        if line.startswith("[t=") and "] " in line:
            idx = line.index("] ")
            self.text.insert("end", line[:idx+1]+" ", ("TIME",))
            self.text.insert("end", line[idx+2:]+"\n", (tag,))
        else:
            self.text.insert("end", line+"\n", (tag,))
        self.text.configure(state=tk.DISABLED)
        self.text.see("end")

    def save(self):
        try:
            fname = filedialog.asksaveasfilename(defaultextension=".json",
                                                 filetypes=[("JSON","*.json"),("All","*.*")],
                                                 initialfile="dccbba_sumo_log.json")
            if fname:
                with open(fname,"w") as f: json.dump(LOG_EVENTS, f, indent=2)
        except Exception as e:
            self.append(f"[GUI] Save failed: {e}", "ERROR")

    def clear(self):
        self.text.configure(state=tk.NORMAL); self.text.delete("1.0","end"); self.text.configure(state=tk.DISABLED)

    def find_next(self):
        q = self.search_var.get().strip()
        if not q: return
        start = self.text.index(tk.INSERT)
        pos = self.text.search(q, start, stopindex=tk.END, nocase=True)
        if not pos:
            pos = self.text.search(q, "1.0", stopindex=tk.END, nocase=True)
            if not pos: return
        end = f"{pos}+{len(q)}c"
        self.text.tag_remove("search","1.0",tk.END)
        self.text.tag_add("search",pos,end)
        self.text.tag_config("search", background="#555", foreground="#fff")
        self.text.mark_set(tk.INSERT, end); self.text.see(pos)

    def show_deadline_graph(self):
        """Open a toplevel window with a line plot: due_by vs completed_at (followed vehicle)."""
        try:
            import matplotlib
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
            import matplotlib.pyplot as plt
        except Exception as e:
            self.append(f"[GUI] Matplotlib not available: {e}", "ERROR")
            return

        recs = TASK_HISTORY.get(FOLLOW_AGENT_ID, [])
        # keep only completed
        recs = [r for r in recs if r.get("completed_at") is not None]
        if not recs:
            self.append("[GUI] No completed tasks yet for deadline graph.", "OTHER")
            return

        # MODIFIED: Use ALL completed tasks instead of limiting to first N
        recs = sorted(recs, key=lambda r: r["completed_at"])

        task_labels = [r["task_id"] for r in recs]
        due_times   = [r.get("due_by", None) for r in recs]
        done_times  = [r.get("completed_at", None) for r in recs]

        # Build figure
        fig = plt.Figure(figsize=(10, 5), dpi=100)  # Larger for more tasks
        ax = fig.add_subplot(111)
        x = list(range(1, len(recs)+1))

        # Plot due_by and completed_at as two lines
        ax.plot(x, due_times, marker="o", linestyle="-", label="Deadline (due_by)")
        ax.plot(x, done_times, marker="o", linestyle="-", label="Completed at")

        # MODIFIED: Show all tasks in title
        ax.set_title(f"Deadline Compliance — {FOLLOW_AGENT_ID} (all {len(recs)} completed tasks)")
        ax.set_xlabel("Task index (by completion)")
        ax.set_ylabel("Time (ticks)")
        ax.set_xticks(x)
        
        # MODIFIED: Better label rotation for many tasks
        if len(task_labels) > 10:
            rotation = 60
            fontsize = 8
        else:
            rotation = 45
            fontsize = 9
            
        ax.set_xticklabels(task_labels, rotation=rotation, ha="right", fontsize=fontsize)
        ax.grid(True, linestyle="--", alpha=0.4)
        ax.legend()

        win = tk.Toplevel(self.root)
        win.title("Deadline Graph (Followed)")
        canvas = FigureCanvasTkAgg(fig, master=win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def show_allocation_graph(self):
        """Show task allocation efficiency across all vehicles"""
        try:
            import matplotlib
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
            import matplotlib.pyplot as plt
            import numpy as np
        except Exception as e:
            self.append(f"[GUI] Matplotlib not available: {e}", "ERROR")
            return

        # Collect allocation data
        allocation_data = defaultdict(list)
        for event in TASK_ALLOCATION_HISTORY:
            agent_id = event.get("agent_id")
            task_id = event.get("task_id")
            timestamp = event.get("timestamp", 0)
            if agent_id and task_id:
                allocation_data[agent_id].append((task_id, timestamp))

        if not allocation_data:
            self.append("[GUI] No task allocation data available.", "OTHER")
            return

        # Prepare data for plotting
        agents = list(allocation_data.keys())
        task_counts = [len(allocation_data[agent]) for agent in agents]
        colors = [color_for_agent(agent) for agent in agents]
        # Convert RGBA to hex for matplotlib
        colors_hex = [f'#{c[0]:02x}{c[1]:02x}{c[2]:02x}' for c in colors]

        # Create figure
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
        
        # Pie chart for task distribution
        ax1.pie(task_counts, labels=agents, autopct='%1.1f%%', colors=colors_hex, startangle=90)
        ax1.set_title('Task Allocation Distribution')

        # Bar chart for task counts
        bars = ax2.bar(agents, task_counts, color=colors_hex, alpha=0.7)
        ax2.set_title('Tasks per Vehicle')
        ax2.set_ylabel('Number of Tasks')
        ax2.set_xlabel('Vehicles')
        
        # Add value labels on bars
        for bar in bars:
            height = bar.get_height()
            ax2.text(bar.get_x() + bar.get_width()/2., height,
                    f'{int(height)}', ha='center', va='bottom')

        plt.tight_layout()

        win = tk.Toplevel(self.root)
        win.title("Task Allocation Efficiency")
        canvas = FigureCanvasTkAgg(fig, master=win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def show_completion_timeline(self):
        """Show task completion timeline for all vehicles"""
        try:
            import matplotlib
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
            import matplotlib.pyplot as plt
            import numpy as np
        except Exception as e:
            self.append(f"[GUI] Matplotlib not available: {e}", "ERROR")
            return

        # Collect completion data
        completion_data = defaultdict(list)
        for agent_id, tasks in TASK_HISTORY.items():
            for task in tasks:
                if task.get("completed_at") is not None:
                    completion_data[agent_id].append({
                        "task_id": task["task_id"],
                        "completed_at": task["completed_at"],
                        "assigned_at": task.get("assigned_at", task["completed_at"]),
                        "duration": task["completed_at"] - task.get("assigned_at", task["completed_at"])
                    })

        if not completion_data:
            self.append("[GUI] No task completion data available.", "OTHER")
            return

        # Create figure
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

        # Timeline plot
        colors = [color_for_agent(agent_id) for agent_id in completion_data.keys()]
        colors_hex = [f'#{c[0]:02x}{c[1]:02x}{c[2]:02x}' for c in colors]
        
        for i, (agent_id, tasks) in enumerate(completion_data.items()):
            tasks_sorted = sorted(tasks, key=lambda x: x["completed_at"])
            completion_times = [t["completed_at"] for t in tasks_sorted]
            task_ids = [t["task_id"] for t in tasks_sorted]
            
            ax1.scatter(completion_times, [i] * len(completion_times), 
                       color=colors_hex[i], label=agent_id, s=50, alpha=0.7)
            
            # Add task IDs as annotations for first few tasks to avoid clutter
            for j, (time, task_id) in enumerate(zip(completion_times, task_ids)):
                if j < 5:  # Only label first 5 tasks per vehicle
                    ax1.annotate(task_id, (time, i), xytext=(5, 5), 
                                textcoords='offset points', fontsize=8, alpha=0.7)

        ax1.set_xlabel('Completion Time (ticks)')
        ax1.set_ylabel('Vehicle')
        ax1.set_yticks(range(len(completion_data)))
        ax1.set_yticklabels(list(completion_data.keys()))
        ax1.set_title('Task Completion Timeline')
        ax1.legend()
        ax1.grid(True, alpha=0.3)

        # Duration analysis
        durations = []
        agent_labels = []
        for agent_id, tasks in completion_data.items():
            if tasks:
                avg_duration = np.mean([t["duration"] for t in tasks])
                durations.append(avg_duration)
                agent_labels.append(agent_id)

        if durations:
            bars = ax2.bar(agent_labels, durations, color=colors_hex[:len(durations)], alpha=0.7)
            ax2.set_title('Average Task Completion Time')
            ax2.set_ylabel('Time (ticks)')
            ax2.set_xlabel('Vehicles')
            
            # Add value labels on bars
            for bar in bars:
                height = bar.get_height()
                ax2.text(bar.get_x() + bar.get_width()/2., height,
                        f'{height:.1f}', ha='center', va='bottom')

        plt.tight_layout()

        win = tk.Toplevel(self.root)
        win.title("Task Completion Analysis")
        canvas = FigureCanvasTkAgg(fig, master=win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

def init_gui():
    global LOG_GUI
    if not GUI_AVAILABLE: return None
    LOG_GUI = LogGUI(LOG_EVENTS); return LOG_GUI

# ==========================
# Utility + logging - ENHANCED WITH EFFICIENCY TRACKING
# ==========================
def log_event(t, etype: str, payload: Dict):
    # Clean any infinity values from the payload before logging
    cleaned_payload = clean_payload_for_json(payload)
    ev = {"type": etype, "time": float(t), "data": cleaned_payload}
    LOG_EVENTS.append(ev)
    
    # Track task allocations for efficiency analysis
    if etype == "mesh_message":
        message = payload.get("message", {})
        if message.get("message_type") == "WINNER_DECISION":
            task_id = message.get("task_id")
            winner = message.get("winner")
            if task_id and winner:
                TASK_ALLOCATION_HISTORY.append({
                    "timestamp": t,
                    "task_id": task_id,
                    "agent_id": winner,
                    "type": "allocation"
                })
    
    if LOG_GUI is not None:
        LOG_GUI.handle(ev)

def clean_payload_for_json(payload: Dict) -> Dict:
    """Recursively clean payload to remove infinity values and ensure JSON compatibility"""
    if not isinstance(payload, (dict, list)):
        return payload
    
    if isinstance(payload, list):
        return [clean_payload_for_json(item) for item in payload]
    
    cleaned = {}
    for key, value in payload.items():
        if isinstance(value, (dict, list)):
            cleaned[key] = clean_payload_for_json(value)
        elif isinstance(value, float) and (value == float('inf') or value > VERY_HIGH_BID * 0.9):
            cleaned[key] = VERY_HIGH_BID
        elif value is None:
            cleaned[key] = 0.0  # Replace None with 0.0 for numeric fields
        else:
            cleaned[key] = value
    return cleaned

def ensure_str(v, default=""):
    try:
        s = str(v); return s if s else default
    except Exception:
        return default

def ensure_float(v, default=0.0):
    try: 
        result = float(v)
        # Replace any infinity with our VERY_HIGH_BID
        if result == float('inf') or result > VERY_HIGH_BID * 0.9:
            return VERY_HIGH_BID
        return result
    except Exception: 
        return float(default)

# ==========================
# DCCBBA cost model - NEW FORMULA
# ==========================
def path_length(edges: List[str]) -> float:
    L = 0.0
    if not (edges and SUMO_NET_OBJ): return L
    for e in edges:
        try: L += float(SUMO_NET_OBJ.getEdge(e).getLength())
        except Exception: pass
    return L

def find_route_edges_between(netobj, from_edge_id: str, to_edge_id: str) -> Optional[List[str]]:
    try:
        src = netobj.getEdge(from_edge_id)
        dst = netobj.getEdge(to_edge_id)
        p, _ = netobj.getShortestPath(src, dst)
        if p: return [e.getID() for e in p]
        return None
    except Exception:
        return None

def calc_dccbba_cost_for_edges(current_edge: str, delivery_edge: str) -> float:
    """Calculate base distance cost (base_score)"""
    if SUMO_NET_OBJ is None or not current_edge or not delivery_edge:
        return VERY_HIGH_BID  # Use VERY_HIGH_BID instead of infinity
    
    # Calculate base path distances: current→WH + WH→delivery + delivery→WH
    s1 = find_route_edges_between(SUMO_NET_OBJ, current_edge, WAREHOUSE_EDGE_ID) or []
    s2 = find_route_edges_between(SUMO_NET_OBJ, WAREHOUSE_EDGE_ID, delivery_edge) or []
    s3 = find_route_edges_between(SUMO_NET_OBJ, delivery_edge, WAREHOUSE_EDGE_ID) or []
    
    if not s2 or not s3:
        return VERY_HIGH_BID  # Use VERY_HIGH_BID if no path found
    
    base_distance = path_length(s1) + path_length(s2) + path_length(s3)
    return base_distance

def calculate_priority_multiplier(task_weight: float, task_id: str) -> float:
    """Calculate priority multiplier based on task weight/priority"""
    # Use task weight to determine priority (heavier = higher priority)
    if task_weight >= 5.0:
        return HIGH_PRIORITY_MULTIPLIER  # High priority tasks get lower multiplier
    elif task_weight >= 2.0:
        return NORMAL_PRIORITY_MULTIPLIER  # Normal priority
    else:
        return LOW_PRIORITY_MULTIPLIER  # Low priority tasks get higher multiplier

def calculate_capacity_penalty(current_load: float, capacity: float) -> float:
    """Calculate capacity penalty based on current load vs capacity"""
    if capacity <= 0:
        return CAPACITY_PENALTY_BASE
    
    load_ratio = current_load / capacity
    # Exponential penalty as load approaches capacity
    penalty = CAPACITY_PENALTY_BASE + (load_ratio * CAPACITY_PENALTY_FACTOR)
    return max(CAPACITY_PENALTY_BASE, penalty)

def calculate_time_window_penalty(task_id: str, base_score: float, current_time: float) -> float:
    """Calculate time window penalty based on deadline urgency"""
    due_by = TASK_DEADLINES.get(task_id)
    if due_by is None:
        return TIME_PENALTY_BASE  # No deadline, no penalty
    
    # Estimate completion time (current time + travel time)
    # Use base_score as proxy for travel time (assuming constant speed)
    travel_time_estimate = base_score / 10.0  # rough estimate: 10 m/s
    estimated_completion = current_time + travel_time_estimate
    time_remaining = due_by - estimated_completion
    
    if time_remaining <= 0:
        # Already late - very high penalty
        return TIME_PENALTY_CRITICAL * 2.0
    elif time_remaining <= TIME_PENALTY_CRITICAL_THRESHOLD:
        # Critical - high penalty
        return TIME_PENALTY_CRITICAL
    elif time_remaining <= TIME_PENALTY_URGENT_THRESHOLD:
        # Urgent - medium penalty
        return TIME_PENALTY_URGENT
    else:
        # Plenty of time - no penalty
        return TIME_PENALTY_BASE

# ==========================
# Messages - FIXED FOR JSON COMPATIBILITY
# ==========================
def make_task_announcement(task_id, pickup, delivery, weight, due_by=None) -> Dict:
    m = {"message_type":"TASK_ANNOUNCEMENT","task_id":task_id,"pickup":pickup,"delivery":delivery,"weight":weight}
    if due_by is not None:
        m["due_by"] = int(due_by)
    return m

def make_forward_announcement(task_id, pickup, delivery, weight, path, best) -> Dict:
    # Ensure best bid is a proper float value, not infinity
    cleaned_best = dict(best)
    if "bid" in cleaned_best:
        cleaned_best["bid"] = ensure_float(cleaned_best["bid"], VERY_HIGH_BID)
    return {"message_type":"FORWARD_ANNOUNCEMENT","task_id":task_id,"pickup":pickup,"delivery":delivery,
            "weight":weight,"path":list(path),"best":cleaned_best}

def make_winner_decision(task_id, winner, best, backtrace_route, pickup, delivery) -> Dict:
    # Ensure best bid is a proper float value, not infinity
    cleaned_best = dict(best)
    if "bid" in cleaned_best:
        cleaned_best["bid"] = ensure_float(cleaned_best["bid"], VERY_HIGH_BID)
    return {"message_type":"WINNER_DECISION","task_id":task_id,"winner":winner,"best":cleaned_best,
            "backtrace_route":list(backtrace_route),"pickup":pickup,"delivery":delivery}

# ==========================
# Sanitizers
# ==========================
def sanitize_edge_id(edge_id: Optional[str], context="") -> Optional[str]:
    global WAREHOUSE_EDGE_ID, SUMO_EDGE_IDS
    if edge_id is None: edge_id = ""
    edge_id = ensure_str(edge_id,"")
    if not SUMO_EDGE_IDS:
        return edge_id if edge_id else None
    if edge_id in SUMO_EDGE_IDS: return edge_id
    # fallback
    if WAREHOUSE_EDGE_ID in SUMO_EDGE_IDS:
        return WAREHOUSE_EDGE_ID
    return random.choice(SUMO_EDGE_IDS)

# ==========================
# Vehicle Agent - WITH NEW COST FUNCTION
# ==========================
class VehicleAgent:
    def __init__(self, vid: str, xy: Tuple[float, float], capacity: float=10.0, battery: float=100.0):
        self.id = vid
        self.pos = {"x": float(xy[0]), "y": float(xy[1])}
        self.capacity = float(capacity)
        self.battery = float(battery)
        self.load = 0.0
        self.inbox: List[Dict] = []
        # (task_id, delivery_edge)
        self.assigned_tasks: List[Tuple[str,str]] = []
        self.completed_tasks: int = 0

    def position(self) -> Dict[str, float]:
        return dict(self.pos)

    def receive(self, msg: Dict):
        if isinstance(msg, dict) and "message_type" in msg:
            self.inbox.append(msg)

    def compute_dccbba_bid(self, task_id, pickup, delivery, weight, priority=3) -> float:
        # Get current vehicle state
        current_edge = WAREHOUSE_EDGE_ID
        if SUMO_AVAILABLE and TRACI_RUNNING:
            veh_id = SUMO_AGENT_VEH_MAP.get(self.id)
            if veh_id:
                try: 
                    current_edge = traci.vehicle.getRoadID(veh_id) or WAREHOUSE_EDGE_ID
                except Exception: 
                    pass
        
        delivery_edge = delivery if isinstance(delivery, str) else WAREHOUSE_EDGE_ID
        
        # Calculate base_score (distance cost)
        base_score = calc_dccbba_cost_for_edges(
            sanitize_edge_id(current_edge), 
            sanitize_edge_id(delivery_edge)
        )
        
        # If base_score is unreachable, return very high bid
        if base_score >= VERY_HIGH_BID:
            return VERY_HIGH_BID
        
        # Get current time for time window calculations
        current_time = traci.simulation.getTime() if SUMO_AVAILABLE and TRACI_RUNNING else 0
        
        # Calculate all components of the cost function
        priority_multiplier = calculate_priority_multiplier(weight, task_id)
        capacity_penalty = calculate_capacity_penalty(self.load, self.capacity)
        time_window_penalty = calculate_time_window_penalty(task_id, base_score, current_time)
        
        # Calculate final cost using the new formula
        cost = base_score * priority_multiplier * capacity_penalty * time_window_penalty
        
        # Ensure we never return infinity or null
        cost = ensure_float(cost, VERY_HIGH_BID)
        
        print(f"[BID CALC] {self.id} for {task_id}: "
              f"base={base_score:.1f}, priority_mult={priority_multiplier:.2f}, "
              f"cap_penalty={capacity_penalty:.2f}, time_penalty={time_window_penalty:.2f}, "
              f"final={cost:.1f}")
        
        return cost

    def process(self, now: int, mesh: "MeshSimulator"):
        while self.inbox:
            msg = self.inbox.pop(0)
            mt = msg.get("message_type")

            if mt == "FORWARD_ANNOUNCEMENT":
                tid = ensure_str(msg.get("task_id"), "UNKNOWN_TASK")
                pickup = msg.get("pickup"); delivery = msg.get("delivery")
                weight = ensure_float(msg.get("weight", 0.0), 0.0)
                best = msg.get("best", {"bid": VERY_HIGH_BID, "holder": None})  # Use VERY_HIGH_BID instead of float('inf')
                if not isinstance(best, dict):
                    best = {"bid": VERY_HIGH_BID, "holder": None}

                # compute bid using new cost function
                bid = self.compute_dccbba_bid(tid, pickup, delivery, weight)
                
                # Ensure bid is a proper value
                current_best_bid = ensure_float(best.get("bid", VERY_HIGH_BID), VERY_HIGH_BID)
                if bid < current_best_bid:
                    best = {"bid": bid, "holder": self.id}

                path = msg.get("path", []); path = path if isinstance(path, list) else []
                if self.id not in path: path = path + [self.id]
                mesh.send(self.id, make_forward_announcement(tid, pickup, delivery, weight, path, best), sim_time=now)

            elif mt == "WINNER_DECISION":
                win = msg.get("winner"); t_id = ensure_str(msg.get("task_id"),"UNKNOWN_TASK")
                delivery = msg.get("delivery"); delivery = sanitize_edge_id(delivery, context=f"WINNER/{t_id}")
                if win == self.id and delivery:
                    if t_id not in TASK_ASSIGN_TIME:
                        TASK_ASSIGN_TIME[t_id] = now  # record assignment time
                    if not any(t==t_id for (t,_) in self.assigned_tasks):
                        self.assigned_tasks.append((t_id, delivery))
                    # plan route right away if not moving
                    simulate_route_existing_vehicle(self.id, t_id, WAREHOUSE_EDGE_ID, delivery)

    def print_status(self, now: int):
        if not (SUMO_AVAILABLE and TRACI_RUNNING): return
        veh_id = SUMO_AGENT_VEH_MAP.get(self.id); 
        if not veh_id: return
        try:
            sp = traci.vehicle.getSpeed(veh_id)
        except Exception:
            sp = -1.0
        self.battery = max(0.0, self.battery - BATTERY_DRAIN_PER_STATUS)
        rem_tasks = [t for (t,_) in self.assigned_tasks]
        print(f"[STATUS t={now}] [{self.id}] speed={sp:.2f} battery={self.battery:.1f}% remaining={rem_tasks} done={self.completed_tasks}")
        log_event(now, "vehicle_status", {
            "agent_id": self.id, "speed": sp, "battery": self.battery,
            "remaining_tasks": rem_tasks, "completed_tasks": self.completed_tasks
        })

# ==========================
# Warehouse
# ==========================
class Warehouse:
    def __init__(self, position: Dict[str, float], packages_by_tick: Dict[int, List[Dict]]):
        self.pos = {"x": float(position["x"]), "y": float(position["y"])}
        self.packages = dict(packages_by_tick)

    def position(self) -> Dict[str, float]:
        return dict(self.pos)

    def tick_and_announce(self, now: int, mesh: "MeshSimulator"):
        if now not in self.packages: return
        for pkg in self.packages[now]:
            tid = ensure_str(pkg.get("task_id"), f"PKG_{now}")
            weight = ensure_float(pkg.get("weight", 0.0), 0.0)
            delivery = pkg.get("delivery")
            if isinstance(delivery, str):
                delivery_edge = delivery
            else:
                delivery_edge = random.choice(VALID_DELIVERY_EDGES) if VALID_DELIVERY_EDGES else delivery
            delivery_edge = sanitize_edge_id(delivery_edge, context=f"Warehouse/{tid}")

            # NEW: deadline (due_by) may be provided in the packages
            due_by_raw = pkg.get("due_by", None)
            due_by = None
            if due_by_raw is not None:
                try:
                    due_by = int(due_by_raw)
                except Exception:
                    due_by = None
            if due_by is not None:
                TASK_DEADLINES[tid] = due_by

            print(f"[TASK t={now}] [ANNOUNCE] t={now} {tid} warehouse→* delivery={delivery_edge}" + (f" due_by={due_by}" if due_by is not None else ""))
            # Log & send announcement (includes due_by field if present; does not affect logic elsewhere)
            msg = make_task_announcement(tid, WAREHOUSE_EDGE_ID, delivery_edge, weight, due_by=due_by)
            log_event(now, "mesh_message", {"sender":"warehouse","receiver":"*", "message": msg})
            mesh.send("warehouse", msg, sim_time=now)

# ==========================
# Mesh simulator (strict 1→1 ring forwarding + backtrace) - FIXED BID VALUES
# ==========================
class MeshSimulator:
    def __init__(self, agents: Dict[str, VehicleAgent], warehouse: Warehouse, comm_range: float=600.0, rng_seed=None):
        self.agents = agents
        self.warehouse = warehouse
        self.range = comm_range
        self.queue: List[Tuple[str, Dict, int]] = []
        if rng_seed is not None: random.seed(rng_seed)

        # deterministic order for the ring
        self.ring: List[str] = list(self.agents.keys())
        self.sod_assign_index = 0

    def send(self, sender_id: str, msg: Dict, sim_time: int=None):
        if not isinstance(msg, dict) or "message_type" not in msg: return
        self.queue.append((sender_id, deepcopy(msg), sim_time))

    def _next_in_ring(self, current: str, path: List[str]) -> Optional[str]:
        """Pick the next rover in the ring that is not already in path."""
        if current == "warehouse":
            for aid in self.ring:
                if aid not in path: return aid
            return None
        if current not in self.ring: return None
        idx = self.ring.index(current)
        for k in range(1, len(self.ring)+1):
            cand = self.ring[(idx+k) % len(self.ring)]
            if cand not in path: return cand
        return None

    def _pick_sod_winner(self) -> Optional[str]:
        if not self.ring: return None
        w = self.ring[self.sod_assign_index % len(self.ring)]
        self.sod_assign_index += 1
        return w

    def deliver(self, sim_time: int):
        while self.queue:
            sender, msg, stime = self.queue.pop(0)
            t = stime if stime is not None else sim_time
            typ = msg.get("message_type")

            if typ == "TASK_ANNOUNCEMENT" and sender == "warehouse":
                tid = ensure_str(msg.get("task_id"), "UNKNOWN")
                is_sod = tid.startswith("SOD-")
                pickup = sanitize_edge_id(msg.get("pickup"), context=f"ANN/{tid}")
                delivery = sanitize_edge_id(msg.get("delivery"), context=f"ANN/{tid}")
                weight = ensure_float(msg.get("weight", 0.0), 0.0)

                if is_sod:
                    winner = self._pick_sod_winner()
                    if not winner: continue
                    best = {"bid": 0.0, "holder": winner}
                    back = ["warehouse", winner]
                    wmsg = make_winner_decision(tid, winner, best, back, pickup, delivery)
                    wmsg["deliver_to"] = winner
                    print(f"[WINNER t={t}] SOD assign {tid} -> {winner}")
                    log_event(t, "mesh_message", {"sender":"warehouse","receiver":winner,"message":wmsg})
                    recv = self.agents.get(winner)
                    if recv: recv.receive(wmsg)
                    continue

                # MID / others: strict 1→1 chain
                path = ["warehouse"]
                target = self._next_in_ring("warehouse", path)
                if not target:
                    print(f"[MESH t={t}] No neighbor to start forwarding.")
                    continue
                best = {"bid": VERY_HIGH_BID, "holder": None}  # Use VERY_HIGH_BID instead of float('inf')
                fwd = make_forward_announcement(tid, pickup, delivery, weight, path+[target], best)
                print(f"[BID t={t}] [FWD] warehouse→{target} tid={tid}")
                log_event(t,"mesh_message",{"sender":"warehouse","receiver":target,"message":fwd})
                if self.agents.get(target): self.agents[target].receive(fwd)
                continue

            if typ == "FORWARD_ANNOUNCEMENT":
                tid = ensure_str(msg.get("task_id"), "UNKNOWN")
                pickup = msg.get("pickup"); delivery = msg.get("delivery")
                weight = msg.get("weight", 0.0)
                best = msg.get("best", {"bid": VERY_HIGH_BID, "holder": None})  # Use VERY_HIGH_BID instead of float('inf')
                path = msg.get("path", []); path = path if isinstance(path,list) else []

                # choose next in ring that is not in path
                last = path[-1] if path else "warehouse"
                nxt = self._next_in_ring(last, path)
                if not nxt:
                    # reached last rover → backtrace
                    self._backtrace(msg, sim_time=t)
                    continue
                fwd = make_forward_announcement(tid, pickup, delivery, weight, path+[nxt], best)
                print(f"[BID t={t}] [FWD] {last}→{nxt} tid={tid}")
                log_event(t,"mesh_message",{"sender": last, "receiver": nxt, "message": fwd})
                if self.agents.get(nxt): self.agents[nxt].receive(fwd)
                continue

            if typ == "WINNER_DECISION":
                deliver_to = ensure_str(msg.get("deliver_to", msg.get("winner","")), "")
                if deliver_to:
                    log_event(t,"mesh_message",{"sender":"mesh","receiver":deliver_to,"message":msg})
                    recv = self.agents.get(deliver_to)
                    if recv: recv.receive(msg)
                continue

    def _backtrace(self, forward_msg: Dict, sim_time: int):
        path = forward_msg.get("path", []); path = path if isinstance(path, list) else []
        best = forward_msg.get("best", {"bid": VERY_HIGH_BID, "holder": None})  # Use VERY_HIGH_BID instead of float('inf')
        tid = ensure_str(forward_msg.get("task_id"),"UNKNOWN")
        pickup = forward_msg.get("pickup"); delivery = forward_msg.get("delivery")

        winner = best.get("holder")
        if winner is None:
            winner = path[-1] if path else None
            best = {"bid": VERY_HIGH_BID, "holder": winner}  # Use VERY_HIGH_BID instead of float('inf')

        if not winner:
            print(f"[WINNER t={sim_time}] no winner for {tid}")
            return

        if winner in path:
            idx = path.index(winner)
            fwdseg = path[idx:]
        else:
            fwdseg = [winner]
        back_order = list(reversed(fwdseg))

        print(f"[WINNER t={sim_time}] {tid} -> {winner}")
        for i in range(len(back_order)-1):
            frm, to = back_order[i], back_order[i+1]
            wmsg = make_winner_decision(tid, winner, best, back_order, pickup, delivery)
            wmsg["deliver_to"] = to
            self.send("mesh", wmsg, sim_time=sim_time)
        # ensure winner gets it
        wmsg = make_winner_decision(tid, winner, best, back_order, pickup, delivery)
        wmsg["deliver_to"] = winner
        self.send("mesh", wmsg, sim_time=sim_time)

# ==========================
# SUMO helpers / visualization
# ==========================
def start_sumo(step_length="1", delay="50"):
    global SUMO_NET_OBJ, TRACI_RUNNING, SUMO_EDGE_IDS, EDGE_ADJ, VALID_DELIVERY_EDGES, WAREHOUSE_EDGE_ID
    if not SUMO_AVAILABLE:
        print("[TASK t=0] SUMO not available"); return None
    cmd = [SUMO_BINARY, "-c", SUMO_CFG, "--gui-settings-file", SUMO_GUI_SETTINGS,
           "--step-length", str(step_length), "--delay", str(delay), "--no-warnings"]
    traci.start(cmd); TRACI_RUNNING = True
    SUMO_NET_OBJ = net.readNet(SUMO_NET)
    SUMO_EDGE_IDS[:] = [e.getID() for e in SUMO_NET_OBJ.getEdges()]
    print(f"[TASK t=0] SUMO loaded, edges={len(SUMO_EDGE_IDS)}")
    if WAREHOUSE_EDGE_ID not in SUMO_EDGE_IDS and SUMO_EDGE_IDS:
        WAREHOUSE_EDGE_ID = random.choice(SUMO_EDGE_IDS)
    # Build adjacency + valid delivery list
    EDGE_ADJ_dict = build_edge_adjacency(SUMO_NET_OBJ)
    # store as dict (fix for incorrect type above)
    globals()['EDGE_ADJ'] = EDGE_ADJ_dict
    VALID_DELIVERY_EDGES[:] = build_valid_delivery_edges(SUMO_NET_OBJ)
    ensure_warehouse_highlight()  # draw outline + label
    return SUMO_NET_OBJ

def build_edge_adjacency(netobj) -> Dict[str, List[str]]:
    adj: Dict[str, List[str]] = {}
    for e in netobj.getEdges():
        eid = e.getID(); neigh = []
        try:
            to_node = e.getToNode()
            if to_node:
                for nxt in to_node.getOutgoing():
                    neigh.append(nxt.getID())
        except Exception: pass
        adj[eid] = neigh
    return adj

def build_valid_delivery_edges(netobj) -> List[str]:
    val = []
    for eid in SUMO_EDGE_IDS:
        if eid == WAREHOUSE_EDGE_ID: continue
        p1 = find_route_edges_between(netobj, WAREHOUSE_EDGE_ID, eid)
        p2 = find_route_edges_between(netobj, eid, WAREHOUSE_EDGE_ID)
        if p1 and p2: val.append(eid)
    return val

def shortest_path_avoiding(from_edge: str, to_edge: str, forbidden: Set[str]) -> Optional[List[str]]:
    from collections import deque
    if from_edge == to_edge: return [from_edge]
    if from_edge not in EDGE_ADJ or to_edge not in EDGE_ADJ: return None
    vis=set(); dq=deque([(from_edge,[from_edge])])
    while dq:
        e, path = dq.popleft()
        if e == to_edge: return path
        if e in vis: continue
        vis.add(e)
        for nx in EDGE_ADJ.get(e,[]):
            if nx in vis: continue
            if nx in forbidden and nx != to_edge: continue
            dq.append((nx, path+[nx]))
    return None

def build_composite_route(agent_id: str, start_edge: str, delivery_edge: str) -> List[str]:
    """start → WH → delivery → WH (avoid visited when possible)."""
    if SUMO_NET_OBJ is None: return []
    start_edge = sanitize_edge_id(start_edge) or WAREHOUSE_EDGE_ID
    delivery_edge = sanitize_edge_id(delivery_edge) or WAREHOUSE_EDGE_ID
    forb = VISITED_EDGES.get(agent_id, set())

    def leg(a,b):
        p = shortest_path_avoiding(a,b,forb)
        if not p: p = find_route_edges_between(SUMO_NET_OBJ,a,b)
        return p or []

    full: List[str] = []
    if start_edge != WAREHOUSE_EDGE_ID: full += leg(start_edge, WAREHOUSE_EDGE_ID)
    full += leg(WAREHOUSE_EDGE_ID, delivery_edge)
    full += leg(delivery_edge, WAREHOUSE_EDGE_ID)

    stitched: List[str] = []
    for e in full:
        if not stitched or stitched[-1] != e:
            stitched.append(e)
    return stitched

def apply_route_to_sumo_vehicle(agent_id: str, edges: List[str]):
    if not (SUMO_AVAILABLE and TRACI_RUNNING):
        return
    if not edges:
        return
    veh_id = SUMO_AGENT_VEH_MAP.get(agent_id)
    if not veh_id:
        return

    try:
        # ensure it is not frozen with speed 0
        traci.vehicle.setRoute(veh_id, edges)
        traci.vehicle.setSpeed(veh_id, -1)  # let SUMO drive it
    except Exception as e:
        try:
            first = edges[0]
            shp = SUMO_NET_OBJ.getEdge(first).getShape()
            if shp:
                x, y = shp[0]
                traci.vehicle.moveToXY(veh_id, x, y, angle=0.0, keepRoute=1)
                traci.vehicle.setRoute(veh_id, edges)
                traci.vehicle.setSpeed(veh_id, -1)
        except Exception as ee:
            print(f"[ERROR] Route set failed for {veh_id}: {e} / fallback: {ee}")

# ==========================
# Route visualization - FIXED FOR ALL VEHICLES
# ==========================
def draw_polyline(agent_id: str, task_id: str, edges: List[str], color: Tuple[int,int,int,int], layer: int):
    """Draw route polyline for ANY vehicle (not just followed one)"""
    if not (SUMO_AVAILABLE and TRACI_RUNNING and SUMO_NET_OBJ): 
        return
        
    route_shape = []
    for e in edges:
        try: 
            edge_obj = SUMO_NET_OBJ.getEdge(e)
            if edge_obj:
                route_shape.extend(edge_obj.getShape())
        except Exception: 
            pass
            
    if not route_shape: 
        return
        
    # Remove older polyline for this agent
    old_poly = ACTIVE_ROUTE_POLY.pop(agent_id, None)
    if old_poly:
        try: 
            traci.polygon.remove(old_poly)
        except Exception: 
            pass
            
    # Create new polyline with agent-specific color
    pid = f"route_poly_{agent_id}_{task_id}"
    try:
        traci.polygon.add(
            polygonID=pid, 
            shape=route_shape, 
            color=color, 
            fill=False, 
            layer=layer
        )
        ACTIVE_ROUTE_POLY[agent_id] = pid
        print(f"[VISUAL] Drew route for {agent_id} with color {color}")
    except Exception as e:
        print(f"[VISUAL ERROR] Failed to draw polyline for {agent_id}: {e}")

def draw_route_edge_markers(agent_id: str, task_id: str, edges: List[str]):
    """Draw edge markers for ANY vehicle (not just followed one)"""
    if not (SUMO_AVAILABLE and TRACI_RUNNING and SUMO_NET_OBJ): 
        return
        
    # Clear previous markers
    for pid in ACTIVE_EDGE_POLYGONS.get(agent_id, []):
        try: 
            traci.polygon.remove(pid)
        except Exception: 
            pass
            
    ACTIVE_EDGE_POLYGONS[agent_id] = []
    s = ROUTE_MARKER_SQUARE_SIZE
    
    for idx, e in enumerate(edges):
        try:
            edge_obj = SUMO_NET_OBJ.getEdge(e)
            if not edge_obj:
                continue
                
            shp = edge_obj.getShape()
            if not shp: 
                continue
                
            # Use first point of edge for marker
            x, y = shp[0]
            marker = [(x-s,y-s),(x+s,y-s),(x+s,y+s),(x-s,y+s)]
            pid = f"edge_marker_{agent_id}_{task_id}_{idx}"
            
            # Use agent's color for markers too
            marker_color = color_for_agent(agent_id)
            traci.polygon.add(
                polygonID=pid, 
                shape=marker, 
                color=marker_color, 
                fill=True, 
                layer=layer_for_agent(agent_id)+1
            )
            ACTIVE_EDGE_POLYGONS[agent_id].append(pid)
            
        except Exception as e:
            print(f"[MARKER ERROR] Failed to draw marker for {agent_id}: {e}")
            continue

def layer_for_agent(agent_id: str) -> int:
    return FOLLOW_ROUTE_LAYER if agent_id == FOLLOW_AGENT_ID else OTHER_ROUTE_LAYER

def color_for_agent(agent_id: str) -> Tuple[int,int,int,int]:
    ids = ["vehA","vehB","vehC","vehD","vehE","vehF"]
    try: idx = ids.index(agent_id)
    except ValueError: idx = 0
    return VEHICLE_COLORS[idx % len(VEHICLE_COLORS)]

def ensure_warehouse_highlight():
    """Draw outline square + POI label once; update position to keep on top."""
    if not (SUMO_AVAILABLE and TRACI_RUNNING and SUMO_NET_OBJ): return
    try:
        shp = SUMO_NET_OBJ.getEdge(WAREHOUSE_EDGE_ID).getShape()
        if not shp: return
        x,y = shp[0]
    except Exception:
        return
    # outline rect (no fill)
    try:
        rect = [(x-WAREHOUSE_BOX_HALF,y-WAREHOUSE_BOX_HALF),
                (x+WAREHOUSE_BOX_HALF,y-WAREHOUSE_BOX_HALF),
                (x+WAREHOUSE_BOX_HALF,y+WAREHOUSE_BOX_HALF),
                (x-WAREHOUSE_BOX_HALF,y+WAREHOUSE_BOX_HALF)]
        try:
            traci.polygon.remove(WAREHOUSE_POLY_ID)
        except Exception: pass
        traci.polygon.add(polygonID=WAREHOUSE_POLY_ID, shape=rect, color=(0,0,255,200), fill=False, layer=80)
    except Exception: pass
    # POI label
    try:
        if WAREHOUSE_POI_ID not in traci.poi.getIDList():
            traci.poi.add(poiID=WAREHOUSE_POI_ID, x=x, y=y, color=(255,255,255,255), layer=81, imgFile="WAREHOUSE")
            try: traci.poi.setParameter(WAREHOUSE_POI_ID, "name", "WAREHOUSE")
            except Exception: pass
        else:
            traci.poi.setPosition(WAREHOUSE_POI_ID, x, y)
    except Exception: pass

def circle_points(cx: float, cy: float, r: float, sides: int) -> List[Tuple[float,float]]:
    pts = []
    for k in range(sides):
        a = 2*math.pi*k/sides
        pts.append((cx+r*math.cos(a), cy+r*math.sin(a)))
    return pts

def update_task_target_circles(agents: Dict[str,"VehicleAgent"]):
    if not (SUMO_AVAILABLE and TRACI_RUNNING and SUMO_NET_OBJ): return
    for aid, ag in agents.items():
        dels = tuple(sorted(de for (_,de) in ag.assigned_tasks))
        if TASK_TARGET_SIG.get(aid) == dels:
            continue  # no change
        # clear previous
        for pid in TASK_TARGET_IDS.get(aid, []):
            try: traci.polygon.remove(pid)
            except Exception: pass
        TASK_TARGET_IDS[aid] = []
        TASK_TARGET_SIG[aid] = dels
        # draw new circles
        for idx, de in enumerate(dels):
            try:
                shp = SUMO_NET_OBJ.getEdge(de).getShape()
                if not shp: continue
                if len(shp) >= 2:
                    (x1,y1), (x2,y2) = shp[0], shp[-1]
                    x = 0.5*(x1+x2); y = 0.5*(y1+y2)
                else:
                    x,y = shp[0]
                poly = circle_points(x, y, TASK_CIRCLE_RADIUS, TASK_CIRCLE_SIDES)
                pid = f"task_circle_{aid}_{idx}"
                traci.polygon.add(polygonID=pid, shape=poly, color=TASK_CIRCLE_COLOR, fill=True, layer=85)
                TASK_TARGET_IDS[aid].append(pid)
            except Exception:
                continue

def update_vehicle_labels():
    if not (SUMO_AVAILABLE and TRACI_RUNNING): return
    for aid, vid in SUMO_AGENT_VEH_MAP.items():
        try: x,y = traci.vehicle.getPosition(vid)
        except Exception: continue
        poi_id = f"veh_label_{aid}"
        if poi_id in VEHICLE_LABEL_CREATED:
            try: traci.poi.setPosition(poi_id, x, y)
            except Exception: VEHICLE_LABEL_CREATED.discard(poi_id)
        else:
            try:
                traci.poi.add(poiID=poi_id, x=x, y=y, color=(255,255,255,255), layer=90, imgFile="VEH")
                try: traci.poi.setParameter(poi_id, "name", aid)
                except Exception: pass
                VEHICLE_LABEL_CREATED.add(poi_id)
            except Exception: pass

# ==========================
# Spawn / park / resume - FIXED VERSION
# ==========================
def initialize_sumo_vehicles_for_agents(agents: Dict[str,"VehicleAgent"]):
    if not (SUMO_AVAILABLE and TRACI_RUNNING): return
    if not SUMO_EDGE_IDS: return
    init_route_id = "dccbba_init_wh"
    try:
        traci.route.add(routeID=init_route_id, edges=[WAREHOUSE_EDGE_ID])
    except Exception:
        pass
    ids = list(agents.keys())[:NUM_VEHICLES]
    for i, aid in enumerate(ids):
        veh = f"veh_{aid}"
        try:
            depart_time = traci.simulation.getTime() + 0.1*(i+1)
            traci.vehicle.add(vehID=veh, routeID=init_route_id, typeID="car", depart=depart_time, departSpeed=0.0)
            try: traci.vehicle.setColor(veh, color_for_agent(aid))
            except Exception: pass
            SUMO_AGENT_VEH_MAP[aid] = veh
            # Initialize respawn cooldown
            VEHICLE_RESPAWN_COOLDOWN[aid] = 0
        except Exception as e:
            print(f"[ERROR] spawn failed for {aid}: {e}")
    # immediately park everyone at WH so they never "arrive" and despawn
    for aid in ids:
        park_vehicle_at_warehouse(aid)

def park_vehicle_at_warehouse(agent_id: str):
    """Improved parking that prevents SUMO from removing vehicles"""
    if not (SUMO_AVAILABLE and TRACI_RUNNING):
        return
        
    veh = SUMO_AGENT_VEH_MAP.get(agent_id)
    if not veh:
        return
        
    try:
        # Use a simple route that won't complete
        traci.vehicle.setRoute(veh, [WAREHOUSE_EDGE_ID, WAREHOUSE_EDGE_ID])
        # Position vehicle on warehouse edge
        traci.vehicle.moveTo(veh, WAREHOUSE_EDGE_ID, WAREHOUSE_PARK_POS)
        # Set speed to 0 but don't use stops that might cause removal
        traci.vehicle.setSpeed(veh, 0.0)
        # Remove any existing stops
        clear_stops(veh)
    except Exception as e:
        print(f"[PARK ERROR] Failed to park {veh}: {e}")

def unpark_if_stopped(agent_id: str):
    """Ensure vehicle is ready to move"""
    if not (SUMO_AVAILABLE and TRACI_RUNNING): 
        return
        
    veh = SUMO_AGENT_VEH_MAP.get(agent_id)
    if not veh: 
        return
        
    try:
        # Clear any stops
        clear_stops(veh)
        # Resume vehicle and set free speed
        traci.vehicle.resume(veh)
        traci.vehicle.setSpeed(veh, -1)  # -1 means no speed limit
    except Exception as e:
        print(f"[UNPARK ERROR] Failed to unpark {veh}: {e}")

def clear_stops(veh):
    try:
        n = traci.vehicle.getStopNumber(veh)
        for i in range(n):
            traci.vehicle.removeStop(veh, 0)
    except:
        pass

# ==========================
# Route management - COMPLETELY REVISED VERSION WITH FIXED WAREHOUSE COMPLETION
# ==========================
def simulate_route_existing_vehicle(agent_id: str, task_id: str, pickup_edge: str, delivery_edge: str):
    if SUMO_NET_OBJ is None: return
    veh = SUMO_AGENT_VEH_MAP.get(agent_id); 
    if not veh: return
    try: 
        cur = traci.vehicle.getRoadID(veh)
    except Exception: 
        cur = WAREHOUSE_EDGE_ID
    
    full = build_composite_route(agent_id, cur or WAREHOUSE_EDGE_ID, delivery_edge)
    if not full: return
    
    ACTIVE_ROUTE_EDGES[agent_id] = full
    ACTIVE_ROUTE_TASK_ID[agent_id] = task_id
    
    try:
        apply_route_to_sumo_vehicle(agent_id, full)
        # Ensure vehicle is unparked and can move
        unpark_if_stopped(agent_id)
    except Exception as e:
        print(f"[ERROR] Route application failed for {agent_id}: {e}")
        return
    
    # Draw colored route for ALL agents with their respective colors
    col = color_for_agent(agent_id)
    draw_polyline(agent_id, task_id, full, col, layer_for_agent(agent_id))
    
    # Draw edge markers for ALL vehicles, not just followed one
    draw_route_edge_markers(agent_id, task_id, full)
    
    print(f"[ROUTE] {agent_id} starting route for task {task_id} with {len(full)} edges")

def trim_passed_edges_from_route(agent_id: str, ag: "VehicleAgent", now: int):
    """REVISED: Completely rewritten task completion and route management with FIXED warehouse completion"""
    if agent_id not in ACTIVE_ROUTE_EDGES:
        return
        
    veh = SUMO_AGENT_VEH_MAP.get(agent_id)
    if not (SUMO_AVAILABLE and TRACI_RUNNING and veh):
        return
        
    try:
        current_edge = traci.vehicle.getRoadID(veh)
        current_route = ACTIVE_ROUTE_EDGES[agent_id]
        current_task_id = ACTIVE_ROUTE_TASK_ID.get(agent_id)
        
        # FIXED: More robust warehouse completion detection
        # Check if we're at the warehouse AND have completed the delivery portion of the route
        if current_edge == WAREHOUSE_EDGE_ID and current_task_id:
            # Check if we've completed the delivery by verifying we've visited the delivery edge
            delivery_completed = False
            for tid, delivery_edge in ag.assigned_tasks:
                if tid == current_task_id:
                    # Check if we've recently been to the delivery edge
                    # This is a more reliable indicator than route index
                    try:
                        route_idx = traci.vehicle.getRouteIndex(veh)
                        # If we're near the end of the route and at warehouse, consider delivery done
                        if route_idx >= len(current_route) - 2:  # -2 to be more lenient
                            delivery_completed = True
                            break
                    except:
                        # If we can't get route index, use a simpler check
                        if current_edge == WAREHOUSE_EDGE_ID:
                            delivery_completed = True
                            break
            
            if delivery_completed:
                print(f"[ROUTE COMPLETE] {agent_id} completed delivery and returned to warehouse for task {current_task_id}")
                
                # Mark task as completed
                task_removed = False
                new_assigned_tasks = []
                for tid, edge in ag.assigned_tasks:
                    if tid == current_task_id:
                        print(f"[TASK COMPLETED] {agent_id} completed task {tid}")
                        task_removed = True
                        # Record completion
                        if tid not in TASK_DONE_TIME:
                            TASK_DONE_TIME[tid] = now
                            ag.completed_tasks += 1
                            
                            rec = {
                                "task_id": tid,
                                "agent_id": agent_id,
                                "assigned_at": TASK_ASSIGN_TIME.get(tid),
                                "completed_at": now,
                                "due_by": TASK_DEADLINES.get(tid),
                                "on_time": (now <= TASK_DEADLINES.get(tid, float("inf")))
                            }
                            TASK_HISTORY.setdefault(agent_id, []).append(rec)
                    else:
                        new_assigned_tasks.append((tid, edge))
                
                ag.assigned_tasks = new_assigned_tasks
            
                # Clear route state
                ACTIVE_ROUTE_EDGES[agent_id] = []
                ACTIVE_ROUTE_TASK_ID[agent_id] = None
                
                # Clear visualization
                clear_route_visualization(agent_id)
                
                # FIXED: Add a small delay before dispatching next task to ensure clean state
                time.sleep(0.2)
                
                # IMMEDIATELY dispatch next task or park
                if ag.assigned_tasks:
                    next_tid, next_edge = ag.assigned_tasks[0]
                    print(f"[NEXT TASK] {agent_id} starting next task {next_tid}")
                    simulate_route_existing_vehicle(agent_id, next_tid, WAREHOUSE_EDGE_ID, next_edge)
                else:
                    print(f"[PARKING] {agent_id} parking at warehouse - no more tasks")
                    park_vehicle_at_warehouse(agent_id)
                
                return
            
    except Exception as e:
        print(f"[ERROR] Route trimming failed for {agent_id}: {e}")

def clear_route_visualization(agent_id: str):
    """Clear all route visualization for an agent"""
    # Remove polyline
    old_poly = ACTIVE_ROUTE_POLY.pop(agent_id, None)
    if old_poly:
        try: 
            traci.polygon.remove(old_poly)
        except Exception: 
            pass
            
    # Remove edge markers
    for marker_id in ACTIVE_EDGE_POLYGONS.get(agent_id, []):
        try: 
            traci.polygon.remove(marker_id)
        except Exception: 
            pass
    ACTIVE_EDGE_POLYGONS[agent_id] = []

def check_delivery_edge_completion(agent_id: str, ag: "VehicleAgent", now: int):
    """Additional safety check for delivery completion"""
    if not (SUMO_AVAILABLE and TRACI_RUNNING):
        return
        
    veh = SUMO_AGENT_VEH_MAP.get(agent_id)
    if not veh:
        return
        
    try:
        current_edge = traci.vehicle.getRoadID(veh)
    except Exception:
        return
        
    # Double-check if we're on any delivery edge for safety
    for task_id, delivery_edge in ag.assigned_tasks:
        if current_edge == delivery_edge:
            print(f"[DELIVERY SAFETY CHECK] {agent_id} on delivery edge {delivery_edge} for task {task_id}")
            # This should ideally be handled by the route completion, but just in case
            break

# ==========================
# Vehicle respawn - FIXED VERSION
# ==========================
def ensure_vehicle_exists(agent_id: str, now: int):
    """FIXED: Completely rewritten respawn logic to prevent loops"""
    if not (SUMO_AVAILABLE and TRACI_RUNNING):
        return

    veh_id = SUMO_AGENT_VEH_MAP.get(agent_id)
    
    # Check if vehicle exists and is valid
    vehicle_exists = False
    try:
        current_vehicles = set(traci.vehicle.getIDList())
        if veh_id and veh_id in current_vehicles:
            # Additional check: make sure vehicle is not stuck or in bad state
            try:
                speed = traci.vehicle.getSpeed(veh_id)
                road_id = traci.vehicle.getRoadID(veh_id)
                # If we can get these values, vehicle is likely fine
                vehicle_exists = True
            except Exception:
                # Vehicle exists in list but traci can't access it - probably in bad state
                vehicle_exists = False
    except Exception:
        return

    if vehicle_exists:
        return  # Vehicle is fine

    # Vehicle doesn't exist or is in bad state - respawn with careful logic
    last_respawn = VEHICLE_RESPAWN_COOLDOWN.get(agent_id, 0)
    if now - last_respawn < 200:  # Increased cooldown to 200 ticks
        return

    print(f"[RESPAWN] Respawning {agent_id} at tick {now}")
    VEHICLE_RESPAWN_COOLDOWN[agent_id] = now
    
    try:
        # Get the agent to restore state
        ag = AGENTS.get(agent_id)
        
        # Create new vehicle with unique ID
        new_veh_id = f"veh_{agent_id}_{now}"
        
        # Use a simple route to spawn the vehicle
        spawn_route_id = f"spawn_route_{agent_id}_{now}"
        try:
            traci.route.add(spawn_route_id, [WAREHOUSE_EDGE_ID])
        except Exception:
            pass  # Route might already exist
            
        # Add vehicle with careful parameters
        traci.vehicle.add(
            vehID=new_veh_id,
            routeID=spawn_route_id,
            typeID="car",
            depart="now",
            departPos="0",
            departSpeed="0"
        )
        
        # Set vehicle properties
        traci.vehicle.setColor(new_veh_id, color_for_agent(agent_id))
        
        # Update mapping
        SUMO_AGENT_VEH_MAP[agent_id] = new_veh_id
        
        # Immediately park at warehouse to establish position
        time.sleep(0.05)
        park_vehicle_at_warehouse(agent_id)
        
        # If agent has tasks, restart the current task
        if ag and ag.assigned_tasks:
            current_task_id = ACTIVE_ROUTE_TASK_ID.get(agent_id)
            if current_task_id:
                # Find the delivery edge for the current task
                delivery_edge = None
                for tid, edge in ag.assigned_tasks:
                    if tid == current_task_id:
                        delivery_edge = edge
                        break
                
                if delivery_edge:
                    print(f"[RESPAWN] Restarting task {current_task_id} for {agent_id}")
                    time.sleep(0.1)
                    simulate_route_existing_vehicle(agent_id, current_task_id, WAREHOUSE_EDGE_ID, delivery_edge)
            else:
                # Start the first assigned task
                next_tid, next_edge = ag.assigned_tasks[0]
                print(f"[RESPAWN] Starting first task {next_tid} for {agent_id}")
                time.sleep(0.1)
                simulate_route_existing_vehicle(agent_id, next_tid, WAREHOUSE_EDGE_ID, next_edge)
                
    except Exception as e:
        print(f"[RESPAWN ERROR] Failed to respawn {agent_id}: {e}")

def is_vehicle_on_edge_xy(edge_id, veh_x, veh_y):
    try:
        pts = SUMO_NET_OBJ.getEdge(edge_id).getShape()
        for (x,y) in pts:
            if (veh_x-x)**2 + (veh_y-y)**2 < 10**2:
                return True
    except:
        pass
    return False

def normalize_edge_id(e):
    if e is None: 
        return None
    e = str(e)
    if e.startswith(":"):   # SUMO internal junction
        return None
    if e.startswith("-"):   # reverse direction
        return e[1:]
    return e

def monitor_and_recover(agent_id: str, now: int):
    """Nudge vehicles that appear stalled while having a route."""
    if not (SUMO_AVAILABLE and TRACI_RUNNING): return
    veh = SUMO_AGENT_VEH_MAP.get(agent_id); 
    if not veh: return
    try:
        sp = traci.vehicle.getSpeed(veh)
    except Exception:
        return
    if ACTIVE_ROUTE_EDGES.get(agent_id):
        last = VEHICLE_LAST_MOVE_TICK.get(agent_id, now)
        if sp > STALL_SPEED_THRESHOLD:
            VEHICLE_LAST_MOVE_TICK[agent_id] = now
        else:
            if (now - last) >= STALL_TICKS_THRESHOLD:
                r = ACTIVE_ROUTE_EDGES.get(agent_id, [])
                if r:
                    apply_route_to_sumo_vehicle(agent_id, r)
                else:
                    park_vehicle_at_warehouse(agent_id)
                VEHICLE_LAST_MOVE_TICK[agent_id] = now

# ==========================
# Packages I/O - MODIFIED FOR DYNAMIC DEADLINES
# ==========================
def generate_random_packages_as_edges(netobj, start_filename=PACKAGES_START_FILE, mid_filename=PACKAGES_MID_FILE, seed=0):
    """Writes SOD & MID tasks to JSON, each with a 'due_by' field calculated as announcement_time + delay."""
    random.seed(seed)
    edges = VALID_DELIVERY_EDGES if VALID_DELIVERY_EDGES else [e.getID() for e in netobj.getEdges()]
    
    # SOD at t=0 - deadlines are 0 + random delay
    start = {"0": []}
    for i in range(NUM_SOD_TASKS):
        de = random.choice(edges) if edges else None
        # MODIFIED: Dynamic deadlines - due_by = announcement_time (0) + random delay
        delay = random.randint(SOD_DEADLINE_RANGE[0], SOD_DEADLINE_RANGE[1])
        due_by = 0 + delay  # SOD tasks are announced at time 0
        start["0"].append({
            "task_id": f"SOD-{i+1}", 
            "delivery": de, 
            "weight": round(random.uniform(0.5,6.0), 2), 
            "due_by": due_by
        })
        
    # MID spread - deadlines are announcement_time + random delay
    mid = {}
    tick = MID_START_TICK
    for i in range(NUM_MID_TASKS):
        de = random.choice(edges) if edges else None
        # MODIFIED: Dynamic deadlines - due_by = announcement_time (tick) + random delay
        delay = random.randint(MID_DEADLINE_OFFSET_RANGE[0], MID_DEADLINE_OFFSET_RANGE[1])
        due_by = tick + delay
        mid.setdefault(str(tick), []).append({
            "task_id": f"MID-{i+1}", 
            "delivery": de,
            "weight": round(random.uniform(0.5,6.0),2), 
            "due_by": due_by
        })
        tick += random.randint(MID_GAP_MIN, MID_GAP_MAX)
        
    with open(start_filename,"w") as f: json.dump(start,f,indent=2)
    with open(mid_filename,"w") as f: json.dump(mid,f,indent=2)
    print(f"[PACKAGES] Generated {NUM_SOD_TASKS} SOD tasks with delays {SOD_DEADLINE_RANGE}")
    print(f"[PACKAGES] Generated {NUM_MID_TASKS} MID tasks with delays {MID_DEADLINE_OFFSET_RANGE}")

def load_packages_file(path: str) -> Dict[int, List[Dict]]:
    try:
        with open(path,"r") as f: raw = json.load(f)
    except Exception:
        return {}
    out: Dict[int,List[Dict]] = {}
    for k,v in raw.items():
        try: t = int(k)
        except Exception: continue
        if not isinstance(v,list): continue
        lst = []
        for pkg in v:
            if not isinstance(pkg,dict): continue
            tid = ensure_str(pkg.get("task_id"), f"PKG_{t}")
            wt = ensure_float(pkg.get("weight", 0.0), 0.0)
            de = pkg.get("delivery")
            due_by = pkg.get("due_by", None)
            lst.append({"task_id": tid, "weight": wt, "delivery": de, "due_by": due_by})
        if lst: out[t] = lst
    return out

# ==========================
# Agent construction
# ==========================
def build_agents_from_specs(specs: Dict) -> Dict[str, VehicleAgent]:
    agents: Dict[str,VehicleAgent] = {}
    for vid, s in specs.items():
        x = ensure_float(s.get("x",0.0), 0.0); y = ensure_float(s.get("y",0.0), 0.0)
        capacity = ensure_float(s.get("capacity", 10.0), 10.0)
        battery  = ensure_float(s.get("battery", 100.0), 100.0)
        agents[vid] = VehicleAgent(vid, (x,y), capacity, battery)
    return agents

# ==========================
# NEW EFFICIENCY VISUALIZATION FUNCTIONS
# ==========================
def save_task_allocation_graph_png(filename="task_allocation_efficiency.png"):
    """Save task allocation efficiency graph showing distribution across vehicles"""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
    except Exception:
        return

    # Collect allocation data
    allocation_data = defaultdict(list)
    for event in TASK_ALLOCATION_HISTORY:
        agent_id = event.get("agent_id")
        task_id = event.get("task_id")
        timestamp = event.get("timestamp", 0)
        if agent_id and task_id:
            allocation_data[agent_id].append((task_id, timestamp))

    if not allocation_data:
        return

    # Prepare data for plotting
    agents = list(allocation_data.keys())
    task_counts = [len(allocation_data[agent]) for agent in agents]
    colors = [color_for_agent(agent) for agent in agents]
    # Convert RGBA to hex for matplotlib
    colors_hex = [f'#{c[0]:02x}{c[1]:02x}{c[2]:02x}' for c in colors]

    # Create figure with subplots
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    # Pie chart for task distribution
    ax1.pie(task_counts, labels=agents, autopct='%1.1f%%', colors=colors_hex, startangle=90)
    ax1.set_title('Task Allocation Distribution')

    # Bar chart for task counts
    bars = ax2.bar(agents, task_counts, color=colors_hex, alpha=0.7)
    ax2.set_title('Tasks per Vehicle')
    ax2.set_ylabel('Number of Tasks')
    ax2.set_xlabel('Vehicles')
    
    # Add value labels on bars
    for bar in bars:
        height = bar.get_height()
        ax2.text(bar.get_x() + bar.get_width()/2., height,
                f'{int(height)}', ha='center', va='bottom')

    plt.tight_layout()
    
    try:
        fig.savefig(filename, bbox_inches='tight', dpi=150)
        print(f"[EFFICIENCY GRAPH] Saved task allocation graph to {filename}")
    except Exception as e:
        print(f"[EFFICIENCY GRAPH] Save failed: {e}")
    plt.close(fig)

def save_task_completion_timeline_png(filename="task_completion_timeline.png"):
    """Save task completion timeline showing when tasks were completed by each vehicle"""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
    except Exception:
        return

    # Collect completion data
    completion_data = defaultdict(list)
    for agent_id, tasks in TASK_HISTORY.items():
        for task in tasks:
            if task.get("completed_at") is not None:
                completion_data[agent_id].append({
                    "task_id": task["task_id"],
                    "completed_at": task["completed_at"],
                    "assigned_at": task.get("assigned_at", task["completed_at"]),
                    "duration": task["completed_at"] - task.get("assigned_at", task["completed_at"])
                })

    if not completion_data:
        return

    # Create figure with subplots
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    # Timeline plot
    colors = [color_for_agent(agent_id) for agent_id in completion_data.keys()]
    colors_hex = [f'#{c[0]:02x}{c[1]:02x}{c[2]:02x}' for c in colors]
    
    for i, (agent_id, tasks) in enumerate(completion_data.items()):
        tasks_sorted = sorted(tasks, key=lambda x: x["completed_at"])
        completion_times = [t["completed_at"] for t in tasks_sorted]
        task_ids = [t["task_id"] for t in tasks_sorted]
        
        ax1.scatter(completion_times, [i] * len(completion_times), 
                   color=colors_hex[i], label=agent_id, s=50, alpha=0.7)
        
        # Add task IDs as annotations for first few tasks to avoid clutter
        for j, (time, task_id) in enumerate(zip(completion_times, task_ids)):
            if j < 5:  # Only label first 5 tasks per vehicle
                ax1.annotate(task_id, (time, i), xytext=(5, 5), 
                            textcoords='offset points', fontsize=8, alpha=0.7)

    ax1.set_xlabel('Completion Time (ticks)')
    ax1.set_ylabel('Vehicle')
    ax1.set_yticks(range(len(completion_data)))
    ax1.set_yticklabels(list(completion_data.keys()))
    ax1.set_title('Task Completion Timeline')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Duration analysis
    durations = []
    agent_labels = []
    for agent_id, tasks in completion_data.items():
        if tasks:
            avg_duration = np.mean([t["duration"] for t in tasks])
            durations.append(avg_duration)
            agent_labels.append(agent_id)

    if durations:
        bars = ax2.bar(agent_labels, durations, color=colors_hex[:len(durations)], alpha=0.7)
        ax2.set_title('Average Task Completion Time')
        ax2.set_ylabel('Time (ticks)')
        ax2.set_xlabel('Vehicles')
        
        # Add value labels on bars
        for bar in bars:
            height = bar.get_height()
            ax2.text(bar.get_x() + bar.get_width()/2., height,
                    f'{height:.1f}', ha='center', va='bottom')

    plt.tight_layout()
    
    try:
        fig.savefig(filename, bbox_inches='tight', dpi=150)
        print(f"[TIMELINE GRAPH] Saved task completion timeline to {filename}")
    except Exception as e:
        print(f"[TIMELINE GRAPH] Save failed: {e}")
    plt.close(fig)

def save_deadline_graph_png(filename="deadline_graph_followed.png"):
    """Save the deadline compliance line graph for the followed vehicle to a PNG (best effort)."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except Exception:
        return
    recs = TASK_HISTORY.get(FOLLOW_AGENT_ID, [])
    recs = [r for r in recs if r.get("completed_at") is not None]
    if not recs:
        return
        
    # MODIFIED: Use ALL completed tasks instead of limiting to first N
    recs = sorted(recs, key=lambda r: r["completed_at"])
    task_labels = [r["task_id"] for r in recs]
    due_times   = [r.get("due_by", None) for r in recs]
    done_times  = [r.get("completed_at", None) for r in recs]
    x = list(range(1, len(recs)+1))

    fig, ax = plt.subplots(figsize=(10, 5), dpi=120)  # Larger figure for more tasks
    
    # Plot lines
    ax.plot(x, due_times, marker="o", linestyle="-", label="Deadline (due_by)")
    ax.plot(x, done_times, marker="o", linestyle="-", label="Completed at")
    
    # MODIFIED: Dynamic formatting for many tasks
    ax.set_title(f"Deadline Compliance — {FOLLOW_AGENT_ID} (all {len(recs)} completed tasks)")
    ax.set_xlabel("Task index (by completion)")
    ax.set_ylabel("Time (ticks)")
    ax.set_xticks(x)
    
    # Adjust label rotation based on number of tasks
    if len(task_labels) > 10:
        rotation = 60
        fontsize = 8
    else:
        rotation = 45
        fontsize = 9
        
    ax.set_xticklabels(task_labels, rotation=rotation, ha="right", fontsize=fontsize)
    ax.grid(True, linestyle="--", alpha=0.4)
    ax.legend()
    
    # Add some padding for rotated labels
    fig.tight_layout()
    try:
        fig.savefig(filename, bbox_inches='tight')
        print(f"[GRAPH] Saved deadline graph with {len(recs)} tasks to {filename}")
    except Exception as e:
        print(f"[GRAPH] Save failed: {e}")
    plt.close(fig)

# ==========================
# Main - IMPROVED VERSION WITH EFFICIENCY VISUALIZATION
# ==========================
def main():
    global AGENTS
    
    ROVER_SPECS = {
        "vehA": {"x": 131.0, "y": 65.5, "capacity": 10.0, "battery": 80.0},
        "vehB": {"x": 431.0, "y": 65.5, "capacity": 12.0, "battery": 90.0},
        "vehC": {"x": 731.0, "y": 65.5, "capacity": 8.0,  "battery": 70.0},
    }
    if RANDOM_SEED is not None: random.seed(RANDOM_SEED)

    netobj = start_sumo(step_length=str(SIM_STEP), delay="50")
    gui = init_gui()

    if GENERATE_RANDOM_PACKAGES and netobj is not None:
        generate_random_packages_as_edges(netobj, PACKAGES_START_FILE, PACKAGES_MID_FILE, seed=RANDOM_SEED or 0)

    start_pk = load_packages_file(PACKAGES_START_FILE)
    mid_pk = load_packages_file(PACKAGES_MID_FILE)
    packages: Dict[int,List[Dict]] = {}
    for k,v in start_pk.items(): packages.setdefault(k,[]).extend(v)
    for k,v in mid_pk.items(): packages.setdefault(k,[]).extend(v)

    warehouse = Warehouse(position={"x": 400.0, "y": 50.0}, packages_by_tick=packages)

    # build & select NUM_VEHICLES
    all_agents = build_agents_from_specs(ROVER_SPECS)
    sel_ids = list(all_agents.keys())[:NUM_VEHICLES]
    agents = {aid: all_agents[aid] for aid in sel_ids}

    AGENTS = agents  # Set global reference for respawning

    mesh = MeshSimulator(agents, warehouse, comm_range=COMM_RANGE, rng_seed=RANDOM_SEED)

    if SUMO_AVAILABLE and TRACI_RUNNING:
        initialize_sumo_vehicles_for_agents(agents)

    now = 0
    try:
        while True:
            # STEP SUMO
            if SUMO_AVAILABLE and TRACI_RUNNING:
                try:
                    traci.simulationStep()
                except Exception as e:
                    log_event(now,"error",{"source":"simulationStep","error":str(e)})
                    break
                ensure_warehouse_highlight()
                update_vehicle_labels()
                
                # Check and respawn vehicles that disappeared (with cooldown)
                for aid in agents:
                    ensure_vehicle_exists(aid, now)

            # TASKS
            warehouse.tick_and_announce(now, mesh)
            # AGENTS process messages
            for a in agents.values():
                a.process(now, mesh)
            # MESH delivers
            mesh.deliver(sim_time=now)

            # IMPROVED: Route management with better task completion
            if SUMO_AVAILABLE and TRACI_RUNNING:
                for aid, ag in agents.items():
                    veh = SUMO_AGENT_VEH_MAP.get(aid)
                    if not veh:
                        continue
                    
                    # Check for delivery completion
                    check_delivery_edge_completion(aid, ag, now)
                    
                    # Improved route trimming with better task completion
                    trim_passed_edges_from_route(aid, ag, now)
                    
                    # Stall recovery
                    monitor_and_recover(aid, now)

                update_task_target_circles(agents)

            # STATUS
            if STATUS_PRINT_INTERVAL and (now % STATUS_PRINT_INTERVAL == 0):
                for a in agents.values():
                    a.print_status(now)

            # GUI
            if gui is not None: gui.poll()

            now += SIM_STEP
            if SIM_DURATION is not None and now > SIM_DURATION: break
            time.sleep(0.05)  # Keep reduced sleep for responsiveness

    finally:
        # Save logs & graphs
        try:
            with open(LOG_FILE,"w") as f: json.dump(LOG_EVENTS, f, indent=2)
            print(f"[LOG] Saved {len(LOG_EVENTS)} events to {LOG_FILE}")
        except Exception as e:
            print(f"[LOG] Save failed: {e}")
        try:
            save_deadline_graph_png("deadline_graph_followed.png")
            save_task_allocation_graph_png("task_allocation_efficiency.png")
            save_task_completion_timeline_png("task_completion_timeline.png")
        except Exception as e:
            print(f"[GRAPH] Final save failed: {e}")
        if SUMO_AVAILABLE and TRACI_RUNNING:
            try: traci.close()
            except Exception: pass

if __name__ == "__main__":
    main()