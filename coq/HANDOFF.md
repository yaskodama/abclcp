# AIPL 形式化 — セッション再開用ドキュメント

最終更新: 2026-08-24（AIPL⁻max = 健全性・安全性が成り立つ最大の断片まで完了）

## 30 秒で状況を把握する

```bash
export PATH="$HOME/.opam/5.1.1/bin:$PATH"
cd ~/aios/abclcp/coq
make check          # 40 個の定理がすべて Closed under the global context
```

これが全部通れば、前回の到達点がそのまま再現できている。

## ファイル

| ファイル | 行数 | 状態 | 内容 |
|---|---|---|---|
| `AIPLSoundness.v` | 1121 | 通る | AIPL⁻ の型健全性・型安全性（第1版） |
| `AIPLSoundness2.v` | 1524 | 通る | AIPL⁻² = 義務レベル＋効果。**デッドロック自由**まで（第3版） |
| `AIPLSoundness2Example.v` | 140 | 通る | 上の仮定が空虚でないことの確認 |
| `AIPLSoundnessMax.v` | 1510 | 通る | **AIPL⁻max**。健全性・安全性が成り立つ最大の断片（第4版） |
| `AIPLSoundnessMaxExample.v` | 214 | 通る | 委譲を使う例題＋**デッドロックする型付き構成**の反例 |
| `AIPLDining.v` | 566 | 通る | 哲学者の食事問題のデッドロック自由 |
| `ABCMEmbedding.v` | 343 | 通る | ABCM ⊂ AIPL⁻ の埋め込み |
| `ABCMEmbedding_simulation_WIP.v` | 176 | **通らない** | 構成レベルのシミュレーション（未完） |
| `ABCM.v` | — | 通る | `~/seminar/abcm-soundness/ABCM.v` への**シンボリックリンク**。原本は一つ |
| `AbclSoundness.v` | 192 | 通る | 旧・社内レポートの形式化（閉じた式のみ。参考） |
| `Makefile` | — | — | `make` / `make check` / `make clean` |

`ABCMEmbedding_simulation_WIP.v` は `Makefile` の `all` から**意図的に外してある**。

## 検証環境

- Coq / Rocq Prover **9.1.0**（`~/.opam/5.1.1/bin` にある。PATH を通すこと）
- LaTeX は **LuaLaTeX**（`ltjsarticle` + `luatexja` + `mathpartir`）

## 証明済みの定理

### AIPL⁻ の型健全性（`AIPLSoundness.v`）

| 定理 | 内容 |
|---|---|
| `no_method_not_understood` | 飛ぶメッセージは宛先実在・メソッド存在・引数型一致、かつ future の型が返り値型と一致 |
| `preservation` | 3 つの構成遷移すべてで `conf_ok` が保たれる |
| `progress` | 終状態 / 一歩進む / **全タスクが未解決 future を await（デッドロック）** の**三択** |
| `type_safety` | 到達可能な構成は stuck でない |
| `state_type_invariant` | どの時点でも各 actor の状態は宣言型を持つ |
| `future_type_invariant` | 解決済み future の値は宣言された返り値型を持つ |
| `async_deadlock_free` | **await を含まないプログラムは blocked にならない**（一般定理） |

### 哲学者の食事問題（`AIPLDining.v`）

| 定理 | 内容 |
|---|---|
| `dining_no_deadlock` | 初期構成から到達できるどの構成も blocked でない（プログラムそのものについて） |
| `no_dead_state` | 優先度規律のもとで、どの `wf` 状態からも遷移できる（プロトコルについて） |
| `ordering_is_necessary_and_sufficient` | 順序規律は十分であり、かつ**捨てられない**（素朴な割り当ての詰まり状態 `deadS` を構成） |

### ABCM ⊂ AIPL⁻ の埋め込み（`ABCMEmbedding.v`）

| 定理 | 内容 |
|---|---|
| `tr_ht` | **ABCM で型が付く式は、翻訳すると AIPL⁻ で型が付く** |
| `e_bodies_ok` | ABCM のプログラムが型検査を通っていれば、翻訳したものも通っている |
| `tr_step` | ABCM の局所簡約は AIPL⁻ の **1 歩**に写る |
| `tr_estep` | ABCM のメッセージ送出は AIPL⁻ の **2 歩**に写る |
| `tr_afree` | 翻訳結果は `await` を含まない |
| `abcm_translation_safe` | 翻訳した ABCM プログラムは型安全でデッドロックしない（AIPL⁻ 側の定理を適用して得ている） |
| `abcm_translation_never_stuck` | 同上、stuck しない形 |

`tr_afree` が構造的に説明していること: **ABCM の進行定理が二択で AIPL⁻ が三択なのは、
ABCM が AIPL⁻ の「await を含まない断片」にちょうど収まっているから**である。

### AIPL⁻² のデッドロック自由と効果（`AIPLSoundness2.v`, 第3版）

義務レベル（`future` の型に「埋める側のレベル」を持たせ、待ちは必ず上へ）と
実行時不変条件 `prod_ok`（未解決 future には必ず埋める者がいる）で、
**`await` を取り除かないまま** `deadlock_free` / `progress_total` を証明してある。
効果も同じ型に載せ、**送信は引き継がず待ちが引き継ぐ**規則で `effect_soundness` まで。

⚠ **事故の記録**: このファイルは一度 `596471e` で効果なし版へ巻き戻されていた
（`AIPLSoundness2Example.v` / `AIPLDining.v` / `Makefile` は効果あり版を前提にしていたため
`make` が落ちる）。復旧は `git show 'e877755:coq/AIPLSoundness2.v' > coq/AIPLSoundness2.v`。
**効果あり版の原本コミットは `e877755`。**

### AIPL⁻max の型健全性・型安全性（`AIPLSoundnessMax.v`, 第4版）

問い: *デッドロック自由を諦めるなら、健全性・安全性を保ったまま言語はどこまで広げられるか。*

第3版から**外した**もの: 義務レベル（`await` の側条件）、`prod_ok`、効果。
**加えた**もの: 文字列と `++`、対、`result<τ>`、期限つきの待ち2種
（`timeout n else d` と `timeout n`）、**一級の返答先 `reply<τ>`**（`replyto` / `answer`）。

型判断は `ht ot ft C R G e T` = `Ω;Φ;c;ρ;Γ ⊢ e:τ`。
**レベル L を外して、返り値型 ρ を入れた**のが一行の要約
（`ρ` = 実行中メソッドの返り値型 = `replyto` の型 = そのタスクの future の型）。

| 定理 | 内容 |
|---|---|
| `no_method_not_understood` | 飛ぶメッセージは宛先実在・メソッド存在・引数型一致 |
| `preservation` / `preservation_star` | 保存 |
| `progress` | 終状態 ∨ 一歩進める ∨ 全タスクが待ち（**三択**） |
| `type_safety` | 到達可能な構成は `stuck` にならない |
| `state_type_invariant` / `future_type_invariant` | 状態と future の型が保たれる（**委譲しても**） |
| `timeout_always_progresses` / `timeout_never_awaits` | 期限つきの待ちは必ず一歩進める |
| `max_admits_deadlock` / `max_is_not_deadlock_free` | **型が付いたままデッドロックする構成が実在** |
| `dl_not_stuck` | それでも `stuck` ではない（壊れてはいない） |

**設計上いちばん効いている一点**: `replyto` を**値にしない**こと。
値にすると `value_ht_indep`（値の型付けは文脈に依らない）が壊れ、代入補題と保存定理まで倒れる。
`replyto` は自分のところで `ρ_k`（型は `Φ` 由来）へ簡約され、運べるのはその `ρ_k` だけ。
これにより「**誰が答えても future に入る値の型は同じ**」が成り立つ。

これ以上広げると壊れるもの（第4版 PDF §16 に破れ方つきで列挙）:
動的な宛先の `remote`、`any`、計算されたメソッド名、範囲検査のない添字、
注釈のない `reply`、そして `replyto` を値にすること。

## 設計上の要点（忘れやすいもの）

1. **AIPL⁻ は AIPL から機能を削っただけでなく、一箇所だけ言語を変更している。**
   メソッドに返り値型を宣言させ、**`reply(v)` をメソッド本体の値とした**。
   現行実装ではここが型で結ばれておらず `now` / `future` が `any` に落ちる。
   **この一点を直さない限り型安全性は成立しない。** これが実装への一番の指摘。

2. **進行定理は二択でなく三択。** `await` がある以上デッドロックは型だけでは
   排除できない。第三の枝が「未解決 future の await」に限定されていること自体が主張。

3. **store typing が要らない理由。** actor の状態の型は `stype(class_of o)` で決まるので、
   別の store typing を持たなくてよい。伸びるのは `hot` と `hft` だけで、
   その単調性（`ht_mono`）で足りる。

4. **`bodies_ok` は `ot0` 相対。** メソッド本体が `EORef` でオブジェクトを名前で
   参照できるようにするため。`conf_ok` に `ext ot0 (hot H)` が入っている。

5. **`ABCM.v` はシンボリックリンク。** 原本は `~/seminar/abcm-soundness/ABCM.v`。
   こちらを編集すると向こうも変わる。

## いま止まっている一点（次回の最初の仕事）

`ABCMEmbedding_simulation_WIP.v` の `simulation` 定理。骨格は全部書けていて、
四つの場合（CLocal / CSend / CDeliver / CDone）はすべて埋まっている。
残っているのは Coq の技術的な障害が**一つだけ**:

> 証明中の bare な `subst` が、`represents` の第一成分 `hot H = Om0` を使って
> **`Om0` を消してしまう**。すると目標が `hot H = hot H` になって `assumption` が外れ、
> `rewrite Hhot` も使えなくなる。逆に `rewrite <- Hhot in otab_fin` で回避しようとすると
> 「`tr_estep` depends on the variable `Om0` which is not declared」という
> セクション変数の依存エラーになる。

直し方は三つあり、**(b) が一番楽**と見ている:

- (a) bare な `subst` をやめ、必要な等式だけ手で潰す
- **(b) `represents` の第一成分を等式ではなく `ext Om0 (hot H) /\ ext (hot H) Om0` にする。
  等式でなくなるので `subst` の対象にならない**
- (c) `Section` を閉じてから（`Om0` が全称量化された後で）`simulation` を証明する

これが通れば A1（ABCM ⊂ AIPL⁻）は完成。

## その先のロードマップ

前回議論した優先順位。

| 群 | 項目 | 規模 | 備考 |
|---|---|---|---|
| **A** | A1 完成（上記） | 小 | **次回すぐ** |
| A | A2 actor の逐次性（一度に一メッセージ） | 中 | ABCM/ABCL の本来の意味論に忠実になる。`get`/`set` の相互排除が言える |
| A | A3 哲学者の第1層と第2層の精密化 | 中〜大 | フォークの状態を保持者つきに変える必要がある |
| A | A4 局所簡約の決定性・菱形性 | 小〜中 | |
| **B** | **B1 優先度つきセッション型 →「型が付けばデッドロック自由」** | 中〜大 | **本命。新規性のある結果**。素材（`no_dead_state`, `prio_ordered`, 必要性の反例）は揃っている |
| B | B2 `now` 型送信を一級の構文に | 中 | B1 とセットで意味を持つ |
| B | B3 公平性のもとでの生存性（飢餓しない） | 大 | 共帰納が要る |
| B | B4 メッセージ順序（FIFO）保証 | 中 | |
| **C** | C1 型検査器の Coq からの抽出 | 中 | 実装に直接効く |
| C | C2 多相と Algorithm W（HM 側と接続） | 大 | HM 側も principal types が未完 |
| C | C3 `any` / 動的境界を gradual typing + blame 定理で | 大 | |
| C | C4 `become` / C5 `select` | 研究 | |
| **D** | D1 状態の述語不変条件（例: `0 ≤ len ≤ 20`） | 小 | **費用対効果が最良**。`heap_ok` の枠がそのまま使える |
| **E** | 有界バッファ / トークンリング / ロボットアームの検証 | 中 | ポータルのダッシュボードに実在する題材 |

## レポート（PDF）

| レポート | tex | PDF | 頁 |
|---|---|---|---|
| ML (Hindley–Milner) | `~/hm_prover/hm_safety_report_ja.tex` | 同 `.pdf` | 14（英語版 9） |
| ABCM | `~/seminar/abcm-soundness/abcm_soundness_ja.tex` | 同 `.pdf` | 15 |
| AIPL（第1版） | `~/aios/abclcp/docs/aipl_soundness_ja.tex` | 同 `.pdf` | 28 |
| AIPL（第3版・デッドロック自由） | `~/aios/abclcp/docs/aipl_soundness3_ja.tex` | 同 `.pdf` | 11 |
| **AIPL（第4版・AIPL⁻max）** | `~/aios/abclcp/docs/aipl_soundness4_ja.tex` | 同 `.pdf` | 25 |

第3版・第4版は **kodamay.org/aice-aipl.html** に公開済み
（`reports/2026-08-23_aipl_soundness3.pdf` / `reports/2026-08-24_aipl_soundness4.pdf`)。

ビルド: `lualatex -interaction=nonstopmode <file>.tex` を **3 回**（相互参照のため）。

**A1 が完成したら AIPL レポートに埋め込み定理の節を足すこと。** いまの
`aipl_soundness_ja.tex` には入っていない。

## 論文の表紙ページ（ローカル）

三レポートへのポインタを貼ったページを作ってある。

```
~/Dropbox/アプリ/site44/kodama-lab.site44.com/aice/papers/index.html
```

- PDF は `papers/pdf/` に**コピー**してある（相対リンク）。
  **レポートを更新したら再コピーが必要。**
- ポータル本体 `aice/index.html` のナビと Dashboards 直前に「論文」へのリンクを追加済み。
- ポータルは全リンクが `127.0.0.1` / `localhost` を指す**ローカル専用**サイト。

## 関連する場所

| 何 | どこ |
|---|---|
| AIPL 処理系（OCaml） | `~/aios/abclcp/src`（parser / infer / eval_thread） |
| 先行レポート | `~/aios/abclcp/docs/ABCLCP_TYPE_SOUNDNESS_REPORT.md`（2026-05-04） |
| ABCM の Coq とレポート | `~/seminar/abcm-soundness`（GitHub: `yaskodama/abcm-soundness`、非公開） |
| ABCM 解説 Web ページ | `~/seminar/abcm-soundness/web/abcm.html` |
| HM の Coq とレポート | `~/hm_prover`（branch `coq-soundness-safety`） |
| AICE/AIPL ポータル | `~/Dropbox/アプリ/site44/kodama-lab.site44.com/aice/` |

## リポジトリの構成（2026-07-28 に整理した）

**`~/aios/abclcp` は二つの GitHub リポジトリに分かれている。** ディレクトリ単位の
公開設定ができないため、公開してよいものと論文ドラフトを分離した。

| リポジトリ | 公開設定 | 中身 | ローカル |
|---|---|---|---|
| `yaskodama/abclcp` | **PUBLIC** | `coq/`, `docs/`, `src/`（処理系）| `~/aios/abclcp`（branch `make-src-base`）|
| `yaskodama/abclcp-papers` | **PRIVATE** | 論文ドラフト 7 本 + `RETURN_PROMPT.md` | `~/aios/abclcp/paper`（**入れ子の別リポジトリ**）|
| `yaskodama/abcm-soundness` | **PRIVATE** | ABCM の Coq とレポート | `~/seminar/abcm-soundness` |
| `yaskodama/hm_prover` | PUBLIC | HM の Coq とレポート | `~/hm_prover`（branch `coq-soundness-safety`）|

**注意点**

- `~/aios/abclcp/paper/` は**入れ子の git リポジトリ**である。親の `abclcp` は
  `.gitignore` の `/paper/` で完全に無視している。paper/ で作業したら
  そちらで別途コミットすること。
- `coq/ABCM.v` は非公開リポジトリの原本へのシンボリックリンクなので
  **公開側では追跡していない**（`.gitignore`）。用意の仕方は `coq/README.md`。
- 公開側の全ファイルはコミット済み。作業ツリーはクリーン。

## 未解決の宿題（判断待ち）

`paper/aios.{tex,pdf,dvi,aux,log}` が**古いコミットで公開リポジトリの履歴に
残っている**。前々回のセッションで `abclcp` に入っていたもので、2026-07-28 に
追跡からは外した（今後の HEAD には出ない）が、**履歴からは消えていない**。

消すなら `git filter-repo` 等で履歴を書き換えて force push が要る。他の履歴も
書き換わり、既に clone された分は回収できない。**未実施。判断待ち。**

なお `aios.log` は検査済みで、資格情報のパターンに引っかかったのは LaTeX 内部の
`token=\toks29` だけだった。
