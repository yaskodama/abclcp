# 次のセッションへの引き継ぎ（AIPL）

最終更新: 2026-08-24

## 30秒で状況を掴む

AIPL には実装が三つあり、**言語は二層**である。

| | 場所 | 動かし方 |
|---|---|---|
| OCaml 版（正） | `~/aios/abclcp` (branch `make-src-base`) | `cd src && make thread_repl` → `./src/abclrepl_thread -q -f run.repl` |
| Py-I | `~/test-bed/aios-claude/src/python-aipl` (branch `add-index-html-aice-portal`) | `python3 aipl_main.py x.aipl` |
| JS-I | `~/projects/drone-hil/abcl` (branch `feat/hybrid-zrp-routing`) | `node ~/aios/abclcp/tools/js_check.mjs x.aipl <JSIパス>` |

**まず `docs/AIPL_LAYERS.md` を読む。** 核（三実装すべて）と拡張（Py-I のみ）の定義、
分類の仕方、これまでに直した処理系の欠陥が全部そこにある。

状況確認は三つ。**何か触ったら必ず流す。**

```sh
sh tools/run_all_impls.sh      # 通るプログラムの出力が3実装で一致するか
sh tools/run_reject_tests.sh   # 弾かれるべき31本が止まるか（3実装の表）
sh tools/classify_corpus.sh    # 核 / 拡張 / 意図的な不正例 / 要修正 を数える
cd coq && make && make check   # 形式化。40個すべて公理なしのはず
```

## いまの数字（2026-08-24）

| | |
|---|---|
| コーパス | 核 161 / 拡張 333 / 意図的な不正例 61 / **要修正 25** |
| paper サンプル | 20本中18本が3実装で出力一致 |
| 弾かれるべきテスト | 31本 × 3実装 = 93枠のうち食い違い10枠（OCaml版は31本すべて期待どおり） |
| 形式化 | `make check` が 40 個すべて `Closed under the global context` |

## ★ この作業でいちばん効いたこと

要修正は 182 → 25 に減った。効いたのは**サンプルの書き換えではなく、
処理系の欠陥を直したこと**だった。

| 直した欠陥 | 効果 |
|---|---|
| Py-I: 署名の省略可能引数 `[, end:int]`・入れ子・先頭を読めていなかった | 48本 |
| Py-I: 精緻化型 `int where P` が基底型 `int` と両立しないと判定 | 17本 |
| Py-I: 署名パーサが `record{a:int, b:int}` の中のカンマで引数を切る | 6本 |
| Py-I: 既定値を落とすつもりで `k >= 0` を `k >` に切る | 5本 |
| Py-I: `++`（文字列連結）が `any` に落ちる | 検出漏れ |
| OCaml: 別クラスの同名フィールドが多重定義になる | 119本が該当 |

**教訓**: サンプルが大量に落ちているときは、まずサンプルを疑うのではなく
**検査器を疑う**。同じ第一エラーが何十本も並んでいたら、まず間違いなく検査器側である。

## ★ 私がやらかしたこと（同じ轍を踏まないために）

1. **`git add -A` を使ってはならない。**
   `ocaml-app/abclcp-project` で先生の未コミット 132ファイル・64万行を
   自分のコミットに巻き込み、push までした。force push で巻き戻した
   （退避ブランチ `backup/before-force-160dd7e` が手元にある。不要なら消す）。
   **触ったファイルだけを名指しで `git add` する。**

2. **一括置換のあとは必ず全数検査する。**
   - 期限を足す道具が、文字列リテラルの中の `now a.m(...)` という「文字列」に反応した
   - record の型注釈の一括置換が、値の側の `{inner: {...}}` まで書き換えた
   - 「メソッドをフィールドの後ろへ移す」変換が、複数行にわたる
     `var x = f(\n ..., \n ...);` をフィールドと誤認し、method 行を途中に差し込んだ
     （`aios_user_three_role_ai.aipl`。コミットまでしてしまい、あとで復旧）

   道具は `tools/add_deadlines.py` に、文字列とコメントを伏せてから走査し
   閉じ括弧は対応を数える形で残してある。**変換のあとは括弧の対応と
   両処理系の判定を必ず確かめる。**

3. **自分の記憶より実物を見る。** このセッションで二度、
   「まだ入っていない」と思った機能が既に入っていた（効果の機械検証、
   `AIPLSoundness2.v` の中身）。着手前に必ずファイルを開く。

## 触ってはいけないもの

- `abclc/aios_user_three_role_ai.aipl` に**期限を足さない**。
  論文 第5版 §11.3 が「モデルを待つ四箇所すべてに期限が無い」ことを
  実測の証拠として引いている。ファイル先頭に `@keep as-is` と書いてある。
- `docs/samples/paper/` と `docs/samples/guide/` は論文の引用元。
  出力を変えるときは論文も直す。

## 「弾かれるのが正しい」プログラムの印

```
// @expect reject: <なぜ落ちるのが正しいか>
```

`tools/classify_corpus.sh` がこれを読んで「意図的な不正例」に数える。
併せて**印が正直かどうか**も見る（両方の処理系が通してしまうなら警告）。
`Typecheck*.aipl` と `Effects.aipl` は `_test_typeck.py` が
「N件の問題が出ること」を検証している実演用サンプルなので、**直すとテストが落ちる**。

## 残っている作業

1. **要修正 25 本**。塊はもう無い。内訳は
   `new X` の引数個数 3 / `reply` しない・複数回 5 / チャネルの引数型 2 /
   `!` の parse 2 / LevelZ の `if`・`while` が先頭 2 / `LPAR` at col 30 2 / 個別 9。
   多くは `aice-*-evolution` / `nextgen` / `experiments/2026-05-*` の研究記録。
2. **弾かれるべきテストの実装差 10枠**。JS-I にメソッド存在／引数個数／引数型／
   戻り値型／アクター型／`result` 型の検査が無い。Py-I は r14 と r8。
3. **AICE ポータル配下のダッシュボード**。`pyi`(:8899) と `phil5`(:8901) は
   正典の Py-I を向くようにした。`web`(:8765) と `node`(:8091) は未確認。
4. **次の形式化**。期限は `AIPLSoundnessMax.v` で入った。
   残るのは `result<τ>` / 返信先の線形性 / 資源の順序 / セッション型。
   返信先の線形性が入りやすい（`replyto`/`answer` を構文に足して線形に追う）。
5. **論文への反映**。`AIPLSoundnessMax.v`（期限の形式化、40定理）と
   `docs/aipl_soundness4_ja.tex`（25p）が入ったので、第5版 §10.4 の
   「機械検証まで届いたのは効果とデッドロック自由の二つ」は更新が要る。

## 掃除（次回いらなければ止める）

- `localhost:3000` の aipl-web、`mongo7` コンテナ、colima が**稼働したまま**
  （`kill $(lsof -ti tcp:3000 -sTCP:LISTEN)` / `docker stop mongo7` / `colima stop`）
- ローカル Mongo に検証用アカウント `aipl-verify-local@example.invalid` を作った
- `ocaml-app/abclcp-project` に先生の未コミット 61 ファイルがある（**触らないこと**）

## 公開物

| | |
|---|---|
| 論文 第5版（43p） | https://kodamay.org/reports/2026-08-23_aipl_paper5.pdf |
| 第4版（38p）・第3版（32p）・第2版・第1版 | 同じ `reports/` 配下。一覧は `aice-aipl.html` |
| 本番サイト | https://airilab.app （2026-08-23 に v10 を出した） |
| 再生成 | `~/kodamay_org_site/kodamay.org/tools/gen_aice_page.py` → lftp で s296.xrea.com |

`heroku login` は**このセッション経由では動かない**（TTY が無く `setRawMode` で落ちる）。
`osascript` で Terminal.app を開いてもらい、そこで実行する。
