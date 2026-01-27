#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Input : pivot CSV created by the previous script
        rows = benchmark (grid(a)×(b)), cols = methods (4), each cell is:
            time：1.000
            results：12
        or timeout/error like:
            time：timeout
            results：-

Output: a single plot (4 lines = 4 methods)
        x-axis = b (because a is fixed in the input)
        y-axis = time (seconds)
        rule: if results == '-' then time is treated as 1800s (timeout cap)

ex: python mkgraph.py --input summary.csv --output runtime.png

"""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path
from typing import Dict, Tuple, Optional, List

import matplotlib.pyplot as plt


RE_GRID = re.compile(r"^grid(\d+)×(\d+)$")


def parse_cell(cell: str) -> Tuple[Optional[str], Optional[str]]:
    """
    Returns (time_str, results_str)
      time_str examples: "1.000", "timeout", "error", None
      results_str examples: "12", "-", None
    """
    if cell is None:
        return None, None
    s = str(cell).strip()
    if not s:
        return None, None

    # CSV cell contains newline between the two lines
    # time：xxx
    # results：yyy
    time_str = None
    results_str = None
    for line in s.splitlines():
        line = line.strip()
        if line.startswith("time："):
            time_str = line.split("time：", 1)[1].strip()
        elif line.startswith("results："):
            results_str = line.split("results：", 1)[1].strip()
    return time_str, results_str


def parse_benchmark(label: str) -> Optional[Tuple[int, int]]:
    m = RE_GRID.match(label.strip())
    if not m:
        return None
    return int(m.group(1)), int(m.group(2))


def to_time_seconds(time_str: Optional[str], results_str: Optional[str]) -> Optional[float]:
    """
    User rule:
      - if results == '-' => 1800s
      - else use time_str as seconds (float)
    """
    if results_str == "-":
        return 1800.0
    if time_str is None:
        return None
    if time_str.lower() in ("timeout", "error"):
        # even if results wasn't '-', treat as capped
        return 1800.0
    try:
        return float(time_str)
    except ValueError:
        return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True, help="Pivot CSV (from previous script).")
    ap.add_argument("--output", type=Path, default=None, help="Output image path (e.g., plot.png). If omitted, show window.")
    ap.add_argument("--title", type=str, default=None, help="Optional plot title.")
    ap.add_argument("--ymax", type=float, default=1900.0, help="Y-axis max (default 1900 to include 1800 cap).")
    args = ap.parse_args()

    # Read CSV
    with args.input.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        if not reader.fieldnames or "benchmark" not in reader.fieldnames:
            raise ValueError("CSV must have a 'benchmark' column.")
        methods = [c for c in reader.fieldnames if c != "benchmark"]

        rows = list(reader)

    # Collect points: method -> list of (b, time_sec)
    method_points: Dict[str, List[Tuple[int, float]]] = {m: [] for m in methods}

    # Determine a (fixed) from the first parseable benchmark
    a_fixed: Optional[int] = None

    for r in rows:
        bench = r.get("benchmark", "").strip()
        parsed = parse_benchmark(bench)
        if not parsed:
            continue
        a, b = parsed
        if a_fixed is None:
            a_fixed = a
        # If multiple a values exist, keep only the first a (as requested "a is fixed")
        if a_fixed is not None and a != a_fixed:
            continue

        for m in methods:
            time_str, results_str = parse_cell(r.get(m, ""))
            tsec = to_time_seconds(time_str, results_str)
            if tsec is None:
                continue
            method_points[m].append((b, tsec))

    if a_fixed is None:
        raise ValueError("No benchmarks like 'grid(a)×(b)' were found in the CSV.")

    # Sort by b for each method, and build unified x ticks from benchmarks present
    all_bs = sorted({b for pts in method_points.values() for (b, _) in pts})
    if not all_bs:
        raise ValueError("No data points found after parsing.")

    # Plot
    plt.figure()
    for m in methods:
        pts = sorted(method_points[m], key=lambda x: x[0])
        if not pts:
            continue
        xs = [b for b, _ in pts]
        ys = [t for _, t in pts]
        # Let matplotlib auto-assign colors; add markers for readability
        plt.plot(xs, ys, marker="o", label=m)

    plt.ylabel("time (s)")
    plt.xticks(all_bs)
    plt.ylim(0, args.ymax)
    plt.grid(True, linestyle="--", linewidth=0.5)
    if args.title:
        plt.title(args.title)
    else:
        plt.title(f"runtime(grid{a_fixed})")
    plt.legend()

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        plt.tight_layout()
        plt.savefig(args.output, dpi=200)
    else:
        plt.tight_layout()
        plt.show()


if __name__ == "__main__":
    main()
