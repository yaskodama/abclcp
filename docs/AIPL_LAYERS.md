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

`docs/corpus_layers.tsv` が明細。586 本を機械的に分けた結果:

| 区分 | 本数 | 意味 |
|---|---|---|
| **核** | 148 | OCaml 版（正）が通す。三実装で突き合わせられる |
| **拡張** | 209 | OCaml は落ちるが Py-I は通す。上表の機能を使っている |
| 意図的な不正例 | 47 | `docs/samples/reject` と `docs/samples/reply_inference` |
| **要修正** | 182 | どちらも落ちる。実験の残骸を含む |

「要修正」の多くは `aice-*-evolution` / `nextgen` / `experiments/2026-05-*` 配下の
研究記録で、当時の Py-I の機能に対して書かれ、その後の処理系の変化で通らなくなったものである。
まず直すべきは `src/python-aipl/samples`（27 本）と `abclc`（21 本）。
