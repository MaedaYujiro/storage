#!/usr/bin/env python3
import sys
import os
from typing import List, Tuple

def generate_grid_edges(rows: int, cols: int) -> Tuple[int, List[Tuple[int, int]]]:
    if rows <= 0 or cols <= 0:
        raise ValueError("rows と cols は正の整数である必要があります。")

    n_vertices = rows * cols
    edges: List[Tuple[int, int]] = []

    for r in range(rows):
        for c in range(cols):
            v = r * cols + c + 1
            if c + 1 < cols:
                edges.append((v, v + 1))
            if r + 1 < rows:
                edges.append((v, v + cols))

    return n_vertices, edges

def parse_args() -> Tuple[int, int, str]:
    # 使い方:
    #   grid2col.py <rows> <cols> [--outdir DIR]  または  -o DIR
    args = sys.argv[1:]
    if len(args) < 2:
        raise ValueError("Usage: grid2col.py <rows> <cols> [--outdir DIR|-o DIR]")

    rows = int(args[0])
    cols = int(args[1])

    outdir = "."  # デフォルトはカレントディレクトリ
    i = 2
    while i < len(args):
        if args[i] in ("--outdir", "-o"):
            if i + 1 >= len(args):
                raise ValueError("--outdir/-o の後にディレクトリを指定してください。")
            outdir = args[i + 1]
            i += 2
        else:
            raise ValueError(f"不明な引数: {args[i]}")
    return rows, cols, outdir

def main() -> int:
    try:
        rows, cols, outdir = parse_args()
        n_vertices, edges = generate_grid_edges(rows, cols)
    except Exception as e:
        print(str(e), file=sys.stderr)
        return 2

    # 出力先ディレクトリ作成（無ければ作る）
    os.makedirs(outdir, exist_ok=True)

    filename = f"grid{rows}×{cols}.col"
    outpath = os.path.join(outdir, filename)

    try:
        with open(outpath, "w", encoding="utf-8") as f:
            f.write(f"c Grid graph {rows}x{cols}\n")
            f.write(f"p edge {n_vertices} {len(edges)}\n")
            for u, v in edges:
                f.write(f"e {u} {v}\n")
    except OSError as e:
        print(f"ファイル書き込みに失敗しました: {e}", file=sys.stderr)
        return 1

    print(outpath)  # 生成したファイルのパス
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
