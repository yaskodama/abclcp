# AIPL は二層である

AIPL には実装が三つある（OCaml 版＝正、Py-I、JS-I）。
長く「三実装は同期している」と言ってきたが、それは**正しいプログラムの出力について**の話で、
**言語の機能そのものは揃っていない**。実測して分かったことを、ここに明示しておく。

## 核（core）---- 三実装すべてが持つ

論文（`docs/aipl_paper5_ja.tex`）が述べている仕様がこれである。

- アクターとメッセージ（`send` / `now` / `future`+`await`）、オブジェクト内部の逐次性
- `reply` と、戻り値型の推論（メソッドごとの $\rho$）
- 効果 `!{ai, net, io, mut, time, mem, fs, log}` の 8 種と `now`/`await` による伝播
- 期限 `timeout n else e`、および `else` を書かない形の `result<τ>`
- 返信先の一級性 `replyto` / `answer` / 引数型 `reply`（線形）
- 資源の順序 `acquire` / `release` と、取得の入れ子から読み取る全体順序
- 義務レベル `@n`（推論あり）とノード境界のレベル
- セッション型 `protocol_define` / `protocol_start` / `protocol_end`（同期の呼び先は展開）
- メッシュ配備 `source_of` / `node_allow` / `deploy`

検証: `sh tools/run_all_impls.sh`（出力一致）と `sh tools/run_reject_tests.sh`（拒否表）。

## 拡張（extension）---- Py-I のみ

Py-I は 15,101 行、OCaml 版は 8,023 行。差の多くはここにある。

| 機能 | 書き方の例 |
|---|---|
| 記録型・行多相 | `{ x = 1, y = 2 }` |
| 精緻化型 | `Rat where r > 0 and r < 1` |
| CSP チャネル | `channel` |
| 所有・use-after-move | `owned` / `move` / `pub` |
| タプル | `tuple` |
| パターン照合 | `match` |
| Saga | `saga { step ... compensate ... }` |
| 構造化並行 | `scope { future ... }` |
| `sender` を値として使う | `pwaiter = sender;` |
| Py-I 専用の組込み | `println` / `error` / `pool_create` / `crdt_*` / `plumtree_*` など |

**核では書けないもの**（実測で確かめた）:

- 返信先をフィールドに保持する（`var w = 0;` は int なので `w = replyto` が型不一致）。
  引数として渡すことはできる。
- `self` / `sender` を値として使う（送信の宛先としてしか書けない）。
- 他のアクターのフィールドへ代入する（`w.x1 = ...`）。

## 分類のしかた

```sh
sh tools/classify_corpus.sh          # 核 / 拡張 / 意図的な不正例 / 要修正 を数える
```

判定は機械的である ---- OCaml が通れば核、OCaml は落ちるが Py-I が通れば拡張、
どちらも落ちれば要修正。`docs/samples/reject/` と `docs/samples/reply_inference/`
は落ちるのが正しいので、はじめから別に数える。

## 書くときの指針

- **新しいサンプルは核で書く。** 三実装で出力を突き合わせられるからである。
- 拡張の機能が要るときは、そのファイルが拡張であることを冒頭のコメントに書く。
- 論文に載せるサンプルは核に限る（`docs/samples/paper/`）。

## いまの分類（2026-08-23 実測）

`docs/corpus_layers.tsv` が明細（`sh tools/classify_corpus.sh` で作り直せる）。

| 区分 | 本数 | 意味 |
|---|---|---|
| **核** | 150 | OCaml 版（正）が通す。三実装で突き合わせられる |
| **拡張** | 336 | OCaml は落ちるが Py-I は通す |
| 意図的な不正例 | 47 | `docs/samples/reject` と `docs/samples/reply_inference` |
| **要修正** | 47 | どちらも落ちる |

`*/removed/` 配下は数えない ---- **言語から外した機能**を使うサンプルで、
動かないのが正しいからである（`become`、クラス単位の `priority(...)`）。

### ここまでで要修正を 182 -> 47 に減らした

効いたのは、サンプルの書き換えよりも**処理系の欠陥を直したこと**だった。

| 直したもの | 効果 |
|---|---|
| Py-I: 署名の省略可能引数（`[, end:int]`・入れ子・先頭）を読めていなかった | 48本の第一エラーが消えた |
| Py-I: 精緻化型 `int where P` が基底型 `int` と両立しないと判定していた | 17本 |
| Py-I: 署名パーサが `record{a:int, b:int}` の中のカンマで引数を切っていた | record 系 6本 |
| Py-I: `++`（文字列連結）が `any` に落ちていた | 検出漏れの解消 |
| OCaml: 別クラスの同名フィールドが多重定義になっていた | 119本が該当 |

サンプル側の書き換えは、期限の追加（86本・1939箇所）、
旧 ABCLc 方言の現行構文への移行、`record`/`tuple` の型注釈の記法統一である。

**罠**: 期限を機械的に足す道具は、最初は文字列リテラルの中の
`now a.m(...)` という「文字列」に反応した。589本を全数検査して、
文字列の中に `timeout N else` が紛れ込んだ箇所が 0 件であることを確かめている。

### 残る 47 本

大きな塊はもう無い（どれも 2〜4 本）。所在は
`src/python-aipl/samples` 14・`abclc` 8・`aios/abclcp/abclc` 8 と、
`aice-*-evolution` / `nextgen` / `experiments/2026-05-*` の研究記録である。
