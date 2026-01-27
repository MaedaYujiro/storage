#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
log -> pivot CSV (rows=benchmarks, cols=methods)

Cell format (multiple lines):
  time：1.000
  results：12
  cnf_vars_before：20
  cnf_clauses_before：31
  cnf_vars_after：20
  cnf_clauses_after：51
  solver_calls：1

Rules:
- trans:
  - "CSP: X variables, Y clauses" -> before
  - "CNF: X variables, Y clauses" -> after
  - "CaDiCal solver invocations: N" -> solver_calls
- basic (or others):
  - "CNF: X variables, Y clauses" -> before (after stays '-')
  - "Solver invocations: N" -> solver_calls

Timeout/error:
- timeout -> all '-' (time=timeout, results='-')
"""

from __future__ import annotations

import argparse
import csv
import re
import shlex
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Optional, Set, Tuple, Iterable


# -----------------------------
# Patterns
# -----------------------------

RE_FOUND = re.compile(r"^\s*Found\s+(\d+)\s+solutions?\s*:", re.MULTILINE)
RE_ELAPSED = re.compile(
    r"^\s*Elapsed\s+\(wall clock\)\s+time\s+\(h:mm:ss or m:ss\)\s*:\s*([0-9:.]+)\s*$",
    re.MULTILINE,
)
RE_EXIT_STATUS = re.compile(r"^\s*Exit status\s*:\s*(\d+)\s*$", re.MULTILINE)
RE_CMD_TIMED = re.compile(r'^\s*Command being timed:\s*"(.+)"\s*$', re.MULTILINE)

RE_TIMEOUT_WORD = re.compile(r"\btimeout\b", re.IGNORECASE)

# CNF/CSP
RE_CNF = re.compile(r"^\s*CNF:\s*(\d+)\s*variables,\s*(\d+)\s*clauses\s*$", re.MULTILINE)
RE_CSP = re.compile(r"^\s*CSP:\s*(\d+)\s*variables,\s*(\d+)\s*clauses\s*$", re.MULTILINE)

# Solver invocations (label variations)
RE_SOLVER_CALLS = re.compile(
    r"^\s*(?:CaDiCal\s+)?Solver\s+invocations:\s*(\d+)\s*$"
    r"|^\s*CaDiCal\s+solver\s+invocations:\s*(\d+)\s*$",
    re.MULTILINE,
)

# filename parsing
RE_GRID_IN_NAME = re.compile(r"(grid\d+×\d+)")
RE_METHOD_IN_NAME = re.compile(r"__(.+?)\.log$")


# -----------------------------
# Data
# -----------------------------

@dataclass
class Parsed:
    method: str
    benchmark: str
    exit_code: Optional[int]
    elapsed_sec: Optional[float]
    answers: Optional[int]
    vars_before: Optional[int]
    clauses_before: Optional[int]
    vars_after: Optional[int]
    clauses_after: Optional[int]
    solver_calls: Optional[int]
    is_timeout_word: bool


Cell = Tuple[
    str,                 # "ok" | "timeout" | "error"
    Optional[float],     # seconds
    Optional[int],       # results
    Optional[int], Optional[int],  # before vars/clauses
    Optional[int], Optional[int],  # after vars/clauses
    Optional[int],       # solver calls
]


# -----------------------------
# Helpers
# -----------------------------

def parse_elapsed_to_seconds(s: str) -> float:
    parts = s.strip().split(":")
    if len(parts) == 3:
        h = int(parts[0]); m = int(parts[1]); sec = float(parts[2])
        return h * 3600 + m * 60 + sec
    if len(parts) == 2:
        m = int(parts[0]); sec = float(parts[1])
        return m * 60 + sec
    return float(parts[0])


def normalize_benchmark(raw: str) -> str:
    s = raw.strip()
    s = Path(s).name
    if "." in s:
        s = s.split(".", 1)[0]

    m = re.search(r"grid\s*(\d+)\s*[×xX]\s*(\d+)", s, re.IGNORECASE)
    if m:
        a = int(m.group(1)); b = int(m.group(2))
        return f"grid{a}×{b}"
    return s


def grid_sort_key(label: str) -> Tuple[int, int, str]:
    m = re.match(r"^grid(\d+)×(\d+)$", label)
    if m:
        return (int(m.group(1)), int(m.group(2)), label)
    return (10**9, 10**9, label)


def infer_method_benchmark_from_filename(path: Path) -> tuple[Optional[str], Optional[str]]:
    name = path.name
    if "__" not in name:
        return None, None
    left, right = name.rsplit("__", 1)

    method = right[:-4] if right.endswith(".log") else right
    bench = left
    return (method.strip() or None), (bench.strip() or None)


def infer_method_benchmark_from_command(text: str) -> tuple[Optional[str], Optional[str]]:
    m = RE_CMD_TIMED.search(text)
    if not m:
        return None, None
    cmd_str = m.group(1)
    try:
        argv = shlex.split(cmd_str)
    except ValueError:
        return None, None
    if len(argv) < 2:
        return None, None
    return argv[-2], argv[-1]


def parse_solver_calls(text: str) -> Optional[int]:
    m = RE_SOLVER_CALLS.search(text)
    if not m:
        return None
    # the regex has two alternative capture groups
    g1 = m.group(1)
    g2 = m.group(2)
    val = g1 if g1 is not None else g2
    return int(val) if val is not None else None


def parse_log(path: Path) -> Parsed:
    text = path.read_text(encoding="utf-8", errors="replace")

    method, bench_raw = infer_method_benchmark_from_filename(path)
    if method is None or bench_raw is None:
        m2, b2 = infer_method_benchmark_from_command(text)
        method = method or m2 or "-"
        bench_raw = bench_raw or b2 or "-"

    # Clean up method
    method = method.strip()
    if method.endswith(".log"):
        method = method[:-4]

    benchmark = normalize_benchmark(bench_raw)

    # results
    answers = None
    m_found = RE_FOUND.search(text)
    if m_found:
        answers = int(m_found.group(1))

    # exit code
    exit_code = None
    m_exit = RE_EXIT_STATUS.search(text)
    if m_exit:
        exit_code = int(m_exit.group(1))

    # elapsed seconds
    elapsed_sec = None
    m_elapsed = RE_ELAPSED.search(text)
    if m_elapsed:
        try:
            elapsed_sec = parse_elapsed_to_seconds(m_elapsed.group(1))
        except Exception:
            elapsed_sec = None

    # detect timeout word
    is_timeout_word = RE_TIMEOUT_WORD.search(text) is not None

    # CNF/CSP parse
    vars_before = clauses_before = None
    vars_after = clauses_after = None

    # trans: CSP (before), CNF (after)
    m_csp = RE_CSP.search(text)
    if m_csp:
        vars_before = int(m_csp.group(1))
        clauses_before = int(m_csp.group(2))

    m_cnf = RE_CNF.search(text)
    if m_cnf:
        cnf_vars = int(m_cnf.group(1))
        cnf_clauses = int(m_cnf.group(2))
        if m_csp:
            # trans style: CNF is after
            vars_after = cnf_vars
            clauses_after = cnf_clauses
        else:
            # basic style: CNF is before
            vars_before = cnf_vars
            clauses_before = cnf_clauses

    solver_calls = parse_solver_calls(text)

    return Parsed(
        method=method,
        benchmark=benchmark,
        exit_code=exit_code,
        elapsed_sec=elapsed_sec,
        answers=answers,
        vars_before=vars_before,
        clauses_before=clauses_before,
        vars_after=vars_after,
        clauses_after=clauses_after,
        solver_calls=solver_calls,
        is_timeout_word=is_timeout_word,
    )


def status_of(p: Parsed) -> Cell:
    # timeout judgment:
    # - explicit "timeout" word OR common timeout exit code 124 OR killed (137/143)
    if p.is_timeout_word or p.exit_code == 124 or p.exit_code in (137, 143):
        return ("timeout", None, None, None, None, None, None, None)

    if p.exit_code == 0 and p.elapsed_sec is not None:
        return ("ok", p.elapsed_sec, p.answers,
                p.vars_before, p.clauses_before,
                p.vars_after, p.clauses_after,
                p.solver_calls)

    return ("error", None, None, None, None, None, None, None)


def better_cell(new: Cell, old: Optional[Cell]) -> Cell:
    if old is None:
        return new
    rank = {"ok": 2, "timeout": 1, "error": 0}
    if rank[new[0]] != rank[old[0]]:
        return new if rank[new[0]] > rank[old[0]] else old
    if new[0] == "ok" and old[0] == "ok":
        ns, os = new[1], old[1]
        if os is None:
            return new
        if ns is None:
            return old
        return new if ns < os else old
    return old


def format_cell(cell: Optional[Cell]) -> str:
    if cell is None:
        return ""

    kind, sec, ans, vb, cb, va, ca, sc = cell

    def vi(x: Optional[int]) -> str:
        return "-" if x is None else str(x)

    if kind == "timeout":
        return (
            "time：timeout\n"
            "results：-\n"
            "cnf_vars_before：-\n"
            "cnf_clauses_before：-\n"
            "cnf_vars_after：-\n"
            "cnf_clauses_after：-\n"
            "solver_calls：-"
        )

    if kind == "error":
        return (
            "time：error\n"
            "results：-\n"
            "cnf_vars_before：-\n"
            "cnf_clauses_before：-\n"
            "cnf_vars_after：-\n"
            "cnf_clauses_after：-\n"
            "solver_calls：-"
        )

    # ok
    t = f"{sec:.3f}" if sec is not None else "error"
    r = "-" if ans is None else str(ans)

    return (
        f"time：{t}\n"
        f"results：{r}\n"
        f"cnf_vars_before：{vi(vb)}\n"
        f"cnf_clauses_before：{vi(cb)}\n"
        f"cnf_vars_after：{vi(va)}\n"
        f"cnf_clauses_after：{vi(ca)}\n"
        f"solver_calls：{vi(sc)}"
    )


def iter_log_paths(input_dir: Optional[Path], list_file: Optional[Path]) -> Iterable[Path]:
    if input_dir is not None:
        yield from sorted(input_dir.rglob("*.log"))
    if list_file is not None:
        for line in list_file.read_text(encoding="utf-8", errors="replace").splitlines():
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            yield Path(s)


# -----------------------------
# Main
# -----------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input-dir", type=Path, default=None, help="Directory containing log files (searched recursively).")
    ap.add_argument("--list", type=Path, default=None, help="Text file with log paths (one per line).")
    ap.add_argument("--output", type=Path, required=True, help="Output CSV path.")
    ap.add_argument("--methods-order", type=str, default=None,
                    help="Comma-separated method order (optional). Example: mis-basic,mis-trans")
    args = ap.parse_args()

    if args.input_dir is None and args.list is None:
        ap.error("Specify either --input-dir or --list")

    table: Dict[str, Dict[str, Cell]] = {}
    methods_set: Set[str] = set()
    benches_set: Set[str] = set()

    for p in iter_log_paths(args.input_dir, args.list):
        parsed = parse_log(p)
        cell = status_of(parsed)

        b = parsed.benchmark
        m = parsed.method

        benches_set.add(b)
        methods_set.add(m)

        table.setdefault(b, {})
        table[b][m] = better_cell(cell, table[b].get(m))

    # methods order
    if args.methods_order:
        order = [s.strip() for s in args.methods_order.split(",") if s.strip()]
        methods = [m for m in order if m in methods_set] + sorted([m for m in methods_set if m not in set(order)])
    else:
        methods = sorted(methods_set)

    benches = sorted(benches_set, key=grid_sort_key)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["benchmark"] + methods)
        for b in benches:
            row = [b]
            for m in methods:
                row.append(format_cell(table.get(b, {}).get(m)))
            w.writerow(row)


if __name__ == "__main__":
    main()
