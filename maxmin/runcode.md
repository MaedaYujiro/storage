# 実験の手引き

実験の際に使用するコードや覚えておいた方が良いコードのまとめ

## 基本コード

### runallの実行

```bash
./ runall.pl (benchmarkのcsv) -d (結果を格納するディレクトリ) > (logファイル)
ex) ./runall.pl csv/BENCH.csv -d result > result/run.log
```

さらに先頭に'nohup'をつけると，ターミナルを閉じても動き続け，最後に'&'をつけると他の実行もできる.

### プロセスのkill

```bash
ps aux | grep runall
```
↑ runallが終わっていない時runallのプロセスの番号が表示されます．

```bash
kill -9 <runallのプロセスの番号>
```
↑ runallのプロセスを殺します．

```bash
ps aux | grep cfb
```
↑ runallの中で使用しているコマンドのプロセスの番号がわかります．同様にkill -9 <番号>でプロセスを殺すことができます．

### BENCH.csvの作成

```bash
for f in *;do
echo "${f}\tbenchmark/${f}"
done > ../csv/BENCH.csv
```
このコマンドは、「今いるディレクトリ直下の全ファイル/フォルダ名」を1個ずつ取り出して、
1列目：その名前（$f）
2列目：benchmark/ を前につけたもの（benchmark/$f）
を タブ区切りで1行にして並べ、最後にそれらをまとめて ../csv/BENCH.csv に上書き保存します.

