#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
import argparse
from pathlib import Path
import matplotlib.pyplot as plt
import numpy as np

# 日本語フォント設定
plt.rcParams['font.sans-serif'] = ['Hiragino Sans', 'Yu Gothic', 'Meirio', 'Takao', 'IPAexGothic', 'IPAPGothic']
plt.rcParams['axes.unicode_minus'] = False

# --- patterns ---
MODEL_FOUND_RE = re.compile(r"\bModel\s+found\b", re.IGNORECASE)
UNSAT_RE = re.compile(r"\bUNSAT\b", re.IGNORECASE)
TIME_PATTERN = re.compile(r"\bElapsed\s*:\s*([0-9]+(?:\.[0-9]+)?)\s*s\b", re.IGNORECASE)


def extract_time_seconds(line: str):
    """行から時間を抽出"""
    m = TIME_PATTERN.search(line)
    if m:
        return float(m.group(1))
    return None


def parse_basic_log(log_path: Path):
    """
    basic: UNSATでモデルが1つ発見とカウント
    各モデル発見について、直前のModel foundの合計 + UNSAT時間を計算
    """
    total_times = []
    current_accumulated_time = 0.0
    
    with log_path.open("r", errors="ignore") as f:
        for line in f:
            t = extract_time_seconds(line)
            if t is None:
                continue
            
            if MODEL_FOUND_RE.search(line):
                # Model foundの時間を累積
                current_accumulated_time += t
            elif UNSAT_RE.search(line):
                # UNSAT時間を加えて1つのモデルの計算時間とする
                current_accumulated_time += t
                total_times.append(current_accumulated_time)
                current_accumulated_time = 0.0  # 次のモデルのためにリセット
    
    return total_times


def parse_trans_log(log_path: Path):
    """
    trans: Model foundでモデルが1つ発見とカウント
    各Model foundの時間を記録
    """
    times = []
    
    with log_path.open("r", errors="ignore") as f:
        for line in f:
            t = extract_time_seconds(line)
            if t is None:
                continue
            
            if MODEL_FOUND_RE.search(line):
                times.append(t)
    
    return times


def plot_times_graph(basic_log: Path, trans_log: Path, output_path: Path):
    """
    全てのモデルについて計算時間をプロット
    """
    # データ解析
    basic_times = parse_basic_log(basic_log)
    trans_times = parse_trans_log(trans_log)
    
    fig, ax = plt.subplots(figsize=(12, 6))
    
    # --- Basic: 合計時間 ---
    if basic_times:
        x_basic = list(range(1, len(basic_times) + 1))
        ax.plot(x_basic, basic_times, 
                color='blue', linewidth=1,
                label='既存手法', alpha=0.7)
    
    # --- Trans: Model found時間 ---
    if trans_times:
        x_trans = list(range(1, len(trans_times) + 1))
        ax.plot(x_trans, trans_times, 
                color='red', linewidth=1,
                label='提案手法', alpha=0.7)
    
    # x軸の設定（モデル数が多い場合に合わせて調整）
    max_models = max(
        len(basic_times) if basic_times else 0,
        len(trans_times) if trans_times else 0
    )
    
    if max_models > 0:
        ax.set_xlim(0, max_models + 1)
    
    ax.set_xlabel('発見した極小モデル数', fontsize=24)
    ax.set_ylabel('CPU時間 (秒)', fontsize=24)
    
    # 軸の目盛り数字のサイズを大きくする
    ax.tick_params(axis='both', which='major', labelsize=18)
    ax.tick_params(axis='both', which='minor', labelsize=16)
    
    # 対数スケール
    ax.set_yscale('log')
    
    ax.legend(prop={'size': 21})
    ax.grid(True, linestyle='--', alpha=0.6, which='both')
    
    plt.tight_layout()
    plt.savefig(output_path, dpi=200)
    plt.close()
    
    print(f"グラフを保存しました: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description='basicとtransのログファイルから全モデルの計算時間をプロット'
    )
    parser.add_argument('--basic', type=Path, required=True, help='basicのログファイル')
    parser.add_argument('--trans', type=Path, required=True, help='transのログファイル')
    parser.add_argument('--output', type=Path, default=Path('out/model_times.png'), 
                        help='出力画像ファイル')
    
    args = parser.parse_args()
    
    # 出力ディレクトリを作成
    args.output.parent.mkdir(parents=True, exist_ok=True)
    
    # グラフ作成
    plot_times_graph(args.basic, args.trans, args.output)


if __name__ == '__main__':
    main()
