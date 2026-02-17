# maxmin

極小支配集合 (Minimal Dominating Set) と極大独立集合 (Maximal Independent Set) を列挙するツール。

## インストール

### Docker を使用する場合

```bash
docker build -t maxmin .
```

### ローカルビルド

Rust 1.83 以上が必要です。

```bash
cargo build --release
```

ビルド後、バイナリは `target/release/maxmin` に生成されます。

## 使い方

```
maxmin <solver> <filename>
```

### ソルバーオプション

| オプション | 説明 |
|------------|------|
| `mds-basic` | 極小支配集合を列挙（基本アルゴリズム） |
| `mds-trans` | 極小支配集合を列挙（trans encoding） |
| `mis-basic` | 極大独立集合を列挙（基本アルゴリズム） |
| `mis-trans` | 極大独立集合を列挙（trans encoding） |

### 入力形式

DIMACS グラフ形式（`.col` ファイル）:

```
c コメント行
p edge <頂点数> <辺数>
e <頂点1> <頂点2>
...
```

頂点番号は 1 から始まります。

## 実行例

### ローカル実行

```bash
# 極小支配集合の列挙
./target/release/maxmin mds-basic examples/path4.col

# 極大独立集合の列挙
./target/release/maxmin mis-basic examples/cycle5.col
```

### Docker 実行

```bash
# 基本的な実行
docker run -v $(pwd)/examples:/data maxmin maxmin mds-basic /data/path4.col

# runsolver でタイムアウト付き実行
docker run -v $(pwd)/examples:/data maxmin -W 300 -C 300 maxmin mds-trans /data/petersen.col
```

runsolver オプション:
- `-W <秒>`: 実時間タイムアウト
- `-C <秒>`: CPU 時間タイムアウト

## 出力形式

```
Graph: <頂点数> vertices, <辺数> edges
Enumerating <問題タイプ>...

Found <解の数> solutions:
  1: [<頂点リスト>]
  2: [<頂点リスト>]
  ...
```

列挙完了時には `Found` で始まる行が出力されます。

## サンプルグラフ

`examples/` ディレクトリに以下のサンプルグラフが含まれています:

| ファイル | 説明 | 頂点数 | 辺数 |
|----------|------|--------|------|
| `path4.col` | パスグラフ (0-1-2-3) | 4 | 3 |
| `cycle5.col` | サイクルグラフ (5頂点) | 5 | 5 |
| `petersen.col` | ピーターセングラフ | 10 | 15 |

## ライセンス

MIT License
