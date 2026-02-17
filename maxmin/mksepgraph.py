#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import argparse
import csv
import re
import math
from pathlib import Path
from typing import Dict, Tuple, Optional, List

import matplotlib.pyplot as plt

# 日本語フォント設定
plt.rcParams['font.sans-serif'] = ['Hiragino Sans', 'Yu Gothic', 'Meirio', 'Takao', 'IPAexGothic', 'IPAPGothic']
plt.rcParams['axes.unicode_minus'] = False


RE_GRID = re.compile(r"^grid(\d+)×(\d+)$")


# ---------- parsing ----------

def parse_cell(cell: str) -> Tuple[Optional[str], Optional[str]]:
    if cell is None:
        return None, None
    s = str(cell).strip()
    if not s:
        return None, None

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


def to_time_seconds(time_str: Optional[str], results_str: Optional[str]) -> float:
    t = (time_str or "").strip().lower()
    r = (results_str or "").strip()

    if r in {"-", "－", "–", "—"}:
        return math.nan
    if not t or "timeout" in t or "error" in t:
        return math.nan

    try:
        return float(t)
    except ValueError:
        return math.nan


# ---------- plotting ----------

def plot_methods(
    method_points: Dict[str, List[Tuple[int, float]]],
    methods: List[str],
    default_ymax: float,
    output_path: Path,
    auto_ymax: bool,
) -> None:
    plt.figure()

    # marker rule
    def marker_for(m: str) -> str:
        return "s" if "trans" in m.lower() else "o"
    
    # label rule
    def label_for(m: str) -> str:
        result = m
        # mds, mis プレフィックスを削除
        result = result.replace("mds-", "").replace("mis-", "").replace("MDS-", "").replace("MIS-", "")
        # basicとtransを日本語に置換
        if "trans" in result.lower():
            result = result.replace("trans", "提案").replace("Trans", "提案").replace("TRANS", "提案")
        if "basic" in result.lower():
            result = result.replace("basic", "既存").replace("Basic", "既存").replace("BASIC", "既存")
        return result
    
    # ----- x-axis auto (timeout(NaN) だけの b は除外) -----
    bs_set = set()
    for m in methods:
        for b, y in method_points[m]:
            if not math.isnan(y) and math.isfinite(y):
                bs_set.add(b)

    bs = sorted(bs_set)
    if not bs:
        return
    xmin, xmax = min(bs), max(bs)

    # ----- y-axis -----
    if auto_ymax:
        finite_vals = [
            y
            for m in methods
            for _, y in method_points[m]
            if not math.isnan(y) and math.isfinite(y)
        ]
        ymax = max(finite_vals) * 1.05 if finite_vals else 1.0
    else:
        ymax = default_ymax

    for m in methods:
        pts = sorted(method_points[m], key=lambda x: x[0])
        xs = [b for b, _ in pts]
        ys = [t for _, t in pts]
        plt.plot(xs, ys, marker=marker_for(m), label=label_for(m))

    plt.xlabel("Grid Size (n)", fontsize=24)
    plt.ylabel("Time (seconds)", fontsize=24)
    plt.xlim(xmin - 0.5, xmax + 0.5)
    plt.xticks(bs, fontsize=15)
    plt.ylim(0, ymax)
    plt.yticks(fontsize=18)
    plt.grid(True, linestyle="--", linewidth=0.5)
    plt.legend(fontsize=20)
    plt.tight_layout()
    plt.savefig(output_path, dpi=200)
    plt.close()


# ---------- main ----------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("out/runtime.png"))
    args = ap.parse_args()

    with args.input.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        methods = [c for c in reader.fieldnames if c != "benchmark"]
        rows = list(reader)

    method_points: Dict[str, List[Tuple[int, float]]] = {m: [] for m in methods}
    a_fixed: Optional[int] = None

    for r in rows:
        parsed = parse_benchmark(r.get("benchmark", ""))
        if not parsed:
            continue
        a, b = parsed
        if a_fixed is None:
            a_fixed = a
        if a != a_fixed:
            continue

        for m in methods:
            time_str, results_str = parse_cell(r.get(m, ""))
            tsec = to_time_seconds(time_str, results_str)
            method_points[m].append((b, tsec))

    # global ymax (MIS 用)
    finite_vals = [
        y
        for pts in method_points.values()
        for _, y in pts
        if not math.isnan(y) and math.isfinite(y)
    ]
    global_ymax = max(finite_vals) * 1.05 if finite_vals else 1.0

    mds_methods = [m for m in methods if "mds" in m.lower()]
    mis_methods = [m for m in methods if "mis" in m.lower()]

    out_dir = args.output.parent
    out_dir.mkdir(parents=True, exist_ok=True)

    if mds_methods:
        plot_methods(
            method_points,
            mds_methods,
            global_ymax,
            out_dir / "runtime_mds.png",
            auto_ymax=True,
        )

    if mis_methods:
        plot_methods(
            method_points,
            mis_methods,
            global_ymax,
            out_dir / "runtime_mis.png",
            auto_ymax=True,
        )


if __name__ == "__main__":
    main()
