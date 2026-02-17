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


def parse_basic_log(log_path: Path, max_models: int = 20):
    """
    basic: UNSATでモデルが1つ発見とカウント
    各モデル発見までのModel foundの個別時間を記録
    最後のmax_models個を返す
    """
    model_count = 0
    current_model_times = []  # 現在のモデル発見までのModel found時間リスト
    all_models_data = []  # [(model_num, [times]), ...]
    
    with log_path.open("r", errors="ignore") as f:
        for line in f:
            t = extract_time_seconds(line)
            if t is None:
                continue
            
            if MODEL_FOUND_RE.search(line):
                # Model foundの時間を記録
                current_model_times.append(t)
            elif UNSAT_RE.search(line):
                # UNSATでモデル数をカウント
                model_count += 1
                # このモデルのModel found時間とUNSAT時間を保存
                all_models_data.append((model_count, current_model_times[:], t))
                current_model_times = []  # リセット
    
    # 真ん中のmax_models個を取得し、番号を1から振り直す
    total = len(all_models_data)
    if total > max_models:
        start = (total - max_models) // 2
        middle_models = all_models_data[start:start + max_models]
    else:
        middle_models = all_models_data
    return [(i + 1, times, unsat_time) for i, (_, times, unsat_time) in enumerate(middle_models)]


def parse_trans_log(log_path: Path, max_models: int = 20):
    """
    trans: Model foundでモデルが1つ発見とカウント
    各Model foundの個別時間を記録
    """
    model_count = 0
    all_times = []  # (model_count, time)
    
    with log_path.open("r", errors="ignore") as f:
        for line in f:
            t = extract_time_seconds(line)
            if t is None:
                continue
            
            if MODEL_FOUND_RE.search(line):
                model_count += 1
                all_times.append((model_count, t))  # 個別の時間
    
    # 真ん中のmax_models個を取得し、番号を1から振り直す
    total = len(all_times)
    if total > max_models:
        start = (total - max_models) // 2
        middle_times = all_times[start:start + max_models]
    else:
        middle_times = all_times
    return [(i + 1, t) for i, (_, t) in enumerate(middle_times)]


def plot_combined_graph(basic_log: Path, trans_log: Path, output_path: Path, max_models: int = 20):
    """
    basicは各Model foundごとに棒グラフ、transはカクタスプロットで描画
    """
    # データ解析
    basic_data = parse_basic_log(basic_log, max_models)
    trans_times = parse_trans_log(trans_log, max_models)
    
    fig, ax = plt.subplots(figsize=(12, 6))
    
    # --- Basic: Model foundごとの棒グラフ ---
    if basic_data:
        bar_width = 0.8 / max([len(times) for _, times, _ in basic_data] + [1])  # 各モデルのModel found数に応じた幅
        
        colors = plt.cm.Blues(np.linspace(0.4, 0.8, 20))  # Model found用の青グラデーション
        
        for model_num, model_found_times, unsat_time in basic_data:
            x_base = model_num - 1  # 0-indexed
            
            # 各Model foundの棒を横に並べる
            for i, mf_time in enumerate(model_found_times):
                x_pos = x_base + (i - len(model_found_times)/2) * bar_width * 0.8
                ax.bar(x_pos, mf_time, bar_width * 0.7, 
                       color='lightblue', edgecolor='black', linewidth=0.5,
                       label='既存手法 (Model found)' if model_num == 1 and i == 0 else '')
            
            # UNSATの棒（最後に配置）
            x_pos = x_base + (len(model_found_times)/2) * bar_width * 0.8
            ax.bar(x_pos, unsat_time, bar_width * 0.7,
                   color='darkblue', edgecolor='black', linewidth=0.5,
                   label='既存手法 (UNSAT)' if model_num == 1 else '')
        
        # --- Basic: 合計時間のプロット ---
        # 各モデルについて、Model found時間の合計 + UNSAT時間を計算
        basic_total_times = [sum(times) + unsat_time for _, times, unsat_time in basic_data]
        basic_model_indices = [m[0] - 1 for m in basic_data]  # 0-indexed
        
        ax.plot(basic_model_indices, basic_total_times, 
                marker='o', color='green', linewidth=2, markersize=6,
                label='既存手法 (合計時間)', zorder=11)
    
    # --- Trans: カクタスプロット ---
    if trans_times:
        models_trans = [m - 1 for m, _ in trans_times]  # 0-indexed
        times_trans = [t for _, t in trans_times]
        
        # カクタスプロット
        ax.plot(models_trans, times_trans, 
                marker='s', color='red', linewidth=2, markersize=6,
                label='提案手法 (合計時間)', zorder=10)
    
    # x軸の設定
    max_models_actual = max(
        len(basic_data) if basic_data else 0,
        len(trans_times) if trans_times else 0
    )
    ax.set_xlim(-0.5, max_models_actual - 0.5)
    ax.set_xticks(range(max_models_actual))
    ax.set_xticklabels(range(1, max_models_actual + 1))
    
    ax.set_xlabel('発見した極小モデル数', fontsize=24)
    ax.set_ylabel('CPU時間 (秒)', fontsize=24)
    
    # 軸の目盛り数字のサイズを大きくする
    ax.tick_params(axis='both', which='major', labelsize=20)
    ax.tick_params(axis='both', which='minor', labelsize=20)
    
    # 対数スケール
    ax.set_yscale('log')
    
    # 凡例（重複を削除）
    handles, labels = ax.get_legend_handles_labels()
    by_label = dict(zip(labels, handles))
    ax.legend(by_label.values(), by_label.keys(), 
              prop={'size': 20}, 
              loc='upper center', 
              bbox_to_anchor=(0.5, -0.20),
              ncol=2)
    
    ax.grid(True, linestyle='--', alpha=0.6, axis='y')
    
    plt.tight_layout()
    plt.savefig(output_path, dpi=200)
    plt.close()
    
    print(f"グラフを保存しました: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description='basicとtransのログファイルからモデル発見数と実行時間のグラフを作成'
    )
    parser.add_argument('--basic', type=Path, required=True, help='basicのログファイル')
    parser.add_argument('--trans', type=Path, required=True, help='transのログファイル')
    parser.add_argument('--output', type=Path, default=Path('out/model_discovery.png'), 
                        help='出力画像ファイル')
    parser.add_argument('--max-models', type=int, default=20, 
                        help='横軸の最大モデル数（デフォルト: 20）')
    
    args = parser.parse_args()
    
    # 出力ディレクトリを作成
    args.output.parent.mkdir(parents=True, exist_ok=True)
    
    # グラフ作成
    plot_combined_graph(args.basic, args.trans, args.output, args.max_models)


if __name__ == '__main__':
    main()
