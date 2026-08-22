# 次のセッションへの引き継ぎ（AIPL 3実装）

最終更新: 2026-08-22

## 30秒で状況を掴む

AIPL には実装が3つある。**OCaml 版が正**。

| | 場所 | 動かし方 |
|---|---|---|
| OCaml 版（正） | `~/aios/abclcp` (branch `make-src-base`) | `cd src && make thread_repl` → `./src/abclrepl_thread -q -f run.repl` |
| Py-I | `~/test-bed/aios-claude/src/python-aipl` (branch `add-index-html-aice-portal`) | `python3 aipl_main.py x.aipl` |
| JS-I | `~/projects/drone-hil/abcl` (branch `feat/hybrid-zrp-routing`) | ブラウザ実装。CLI は `node ~/aios/abclcp/tools/js_run.mjs x.aipl <JSIパス>` |

**3実装は同期済み**。ガイドのサンプル g1..g9 が全て動き、出力も一致する。
全リポジトリ commit 済み・push 済み（2026-08-01 時点）。

まず状況確認はこれ一発:

```sh
sh ~/aios/abclcp/tools/run_all_impls.sh
```

3実装で同じサンプルを流し、出力を並べて「一致 / ★差あり」を出す。
**何か触ったら必ずこれを流す。** 過去に2回、これで退行に気づいた。

## 2026-08 に入れたもの（3実装すべてに展開済み）

論文 `docs/aipl_paper3_ja.tex`（第3版・30頁）が現在の仕様の説明そのもの。
公開先は https://kodamay.org/reports/2026-08-22_aipl_paper3.pdf （要 Basic 認証）。

| 機能 | 書き方 | 効くもの |
|---|---|---|
| 失敗を型に出す | `timeout n`（else 無し）→ `result<τ>`、`is_ok`/`value` | 期限切れの握り潰し |
| 順序つき効果 | `acquire(r)` / `release(r)` | 取り忘れ・返し忘れ |
| 一級の返信先 | 引数型 `reply`、`answer(r,v)`、`replyto` | 返信の線形性（owed, spent） |
| メッシュ配備 | `source_of` / `node_allow` / `deploy` | ノード境界での効果検査 |
| 義務レベル | `@n` 注釈＋不動点推論、`node_level` | 循環待ち（経路1） |
| `select` の規律 | 期限の義務づけ＋送り手の存在検査 | 待ちっぱなし（経路3） |
| セッション型 | `protocol_define`/`protocol_start`/`protocol_end` | やり取りの**順序**違反（アクターをまたいでも追う） |
| 資源への全体順序 | 取得の入れ子から推論（`resource_order("a -> b")` で明示も可） | 逆順の取得 |

`become` は外した（`docs/samples/removed/` に旧テストと理由）。

**セッション型は新しい宣言を作っていない。** 実行時に既にあった（Coq 検証済みの）
プロトコル宣言を、型検査の側が読むようにしただけ。誤検出を二度直している ----
(a) セッションがアクターをまたぐ例（→ 手順が全部その並びに現れる時だけ「やり残し」を
誤りとする。`AIOS_STRICT_PROTOCOL=1` で警告に）、(b) 手順が `"main_thread.run"` なのに
プログラムは `"main"` へ送る綴り違い（→ **手順に含まれない宛先への送信は見ない**）。

**アクターをまたぐセッションは「振る舞い展開」で解いた。** 多者間セッション型も
委譲も要らなかった。`now`/`aios_now` は呼び先が呼び出し側の続きより先に走り切るので、
**呼び先の送信列をその場に差し込む**。非同期(`send`/`future`)は差し込まず、
呼び先が手順を含むなら「静的に並べられない」と印を付けて実行時に任せる。
名前は解決表でたどる — `aios_register_service("main","main_thread")`、
`var x = new C()`、引数の型注釈 `method run(f: Fetch, ...)`。
**プログラムは一行も変えていない。**

罠: **フィールドに持ったアクターは役になれない**。実行時は `c#f` と持ち主で
修飾した名前で呼ぶが、静的な側はクラスの実体を一つに決められない。
サンプルは引数で渡す形にすること。

**資源への全体順序も新しい注釈を作っていない。** 「r を持ったまま s を取った」
という入れ子が、そのまま r < s の辺である。全体から集めて閉路を見る。
閉路の各辺に「どこで生まれたか」を持たせてあるので、
**逆順に取っている二か所がそのままエラーに出る**。
閉路が無ければ位相の高さがそのまま順序（`AIOS_SHOW_LEVELS=1` で見える）。
リテラルでない名前の acquire は追えないので、宣言順序は**実行時にも効かせている**
（`AIOS_STRICT_RESOURCE=1` で追えなかった場所を知らせる）。

## 残っている課題

1. **非同期の呼び先をまたぐセッション**。展開は同期の呼び先しか差し込めない。
   `send`/`future` の先で手順が進む場合は実行時任せ。多者間セッション型＋委譲
   （線形な `session<S>` を引数で引き回す）なら追えるが、プログラムの書き換えが要る。
2. **資源がアクターの実体であるときの順序**。順序は資源の「名前」についてのもの。
   哲学者のように `lo`/`hi` が同じクラスの別インスタンスだと、
   義務レベルが `Class#method` を鍵にしているので区別できない（`types.ml:180`）。
   精緻化型か、フィールドによる順序宣言 `resource_order_by("Fork","id")` が要る。
   なお「名前が動的な acquire」は582本を測って**一件も無かった**（穴は空）。
3. **メソッド内の失敗の伝わり方が3実装で違う**。宣言順序違反を実行時に捕まえたとき、
   呼び出し側の `now ... timeout ... else` が返すものが
   OCaml=停止 / Py-I=`None` / JS-I=`else` の値、と割れる。
   `result<τ>` に載せる道と揃える必要がある。
4. **JS-I はトップレベル文をクラスより前に書けない**（`resource_order` や
   `protocol_define` を先頭に置くと Parse error）。OCaml 版は書ける。
   サンプルは s18/s19 とも宣言をクラスの後ろに置いて回避している。
5. **弾かれるべきテストの実装差**: 31本×3実装＝93枠のうち **10枠**が食い違う
   （OCaml 版は 29本すべて期待どおり）。JS-I にメソッド存在／引数個数／引数型／
   戻り値型／アクター型／`result` 型の検査が無い。Py-I は r14（future でないものへの
   `await`）と r8（1文字クラス名）。`sh tools/run_reject_tests.sh` で表が出る。
6. **機械検証の範囲**。`AIPLSoundness.v`（1121行・公理なし）が押さえているのは
   **効果と期限を落とした AIPL⁻**。効果つきは証明されていない。論文の §4 に明記した。

## 用意してある道具（`~/aios/abclcp/tools/`）

| ファイル | 用途 |
|---|---|
| `run_all_impls.sh` | 3実装でサンプルを流して出力を突き合わせる |
| `js_run.mjs` | JS-I をヘッドレスで実行（ブラウザ実装なので足場が要る） |
| `js_parse.mjs` | JS-I でパースだけ試す |
| `plus_to_concat.py` | `+` → `++` を構文木で判定して移行する（後述） |
| `tc_main.ml` | 型検査だけ走らせるドライバの素 |
| `run_reject_tests.sh` | 「弾かれるべき29本」を3実装に流して表にする |
| `js_check.mjs` | JS-I の型検査だけ走らせる |

型検査ドライバのビルド:

```sh
cd /tmp && ocamlfind ocamlc -package unix -thread -linkpkg -g -w -a \
  -I ~/aios/abclcp/src -o tc \
  ~/aios/abclcp/src/location.cmo ~/aios/abclcp/src/types.cmo ~/aios/abclcp/src/ast.cmo \
  ~/aios/abclcp/src/typing_env.cmo ~/aios/abclcp/src/infer.cmo ~/aios/abclcp/src/typecheck.cmo \
  ~/aios/abclcp/src/parser.cmo ~/aios/abclcp/src/lexer.cmo ~/aios/abclcp/tools/tc_main.ml
```

## 言語の現状（3実装で揃っているもの）

- 拡張子は **`.aipl`**（`.abcl` は全廃。4リポジトリ 478 本を改名済み）
- `++` が文字列連結。**`+` は数値専用**
- 優先順位は 等値 < 比較 < `++` < 加減 < 乗除 < 単項マイナス。**すべて左結合**（等値も含む）
- `true` / `false` リテラル
- 戻り値型注釈 `method m(x) : T`（Py-I は `-> T` も受ける）
- 効果注釈 `method m(x) : T !{log, mut}`
- 引数の型注釈 `method m(x: D)`
- 期限つきの待ち `now t.m(a) timeout 100 else 0` / `await f timeout 100 else 0`
- 型検査: reply 線形性・戻り値型の義務・期限警告（**3実装で件数まで一致**）
- アクターをメッセージの引数として渡せる（`g9_actor_arg.aipl`）

### 環境変数（OCaml 版）

| 変数 | 効果 |
|---|---|
| `AIOS_STRICT_DEADLINE=1` | 期限なしの now/await をエラーに（既定は警告）。型健全性の定理が成立する範囲に留まるスイッチ |
| `AIOS_LAX_OVERLOAD=1` | 曖昧なオーバーロードを従来動作に戻す |
| `AIOS_LAX_EXPOSE=1` | 公開アクターの注釈漏れを警告に落とす |
| `AIOS_TYPE_TRACE=1` | reply ごとに `[rtype]` を出す（差分テスト用） |
| `AIOS_QUIET=1` | 情報メッセージを抑止 |
| `AIOS_MODEL_PROVIDER` | `ai_call` のモデル事業者（既定 gemini） |

Py-I も `AIOS_STRICT_DEADLINE=1` を見る。

## 残っている課題

優先度順。どれも着手可能な状態。

1. **メソッド内の `return` が JS-I に無い**（Py-I は受ける）。
   `~/projects/drone-hil/bench/*.aipl` 3本がこれで止まっている
   （`method get_meals(unused) { return meals; }`）。
   引数型注釈を入れて失敗位置は 37→74 行に進んだが、次がこれ。
2. **`typeof` の書式が揃っていない**。
   OCaml `actor(D) { ping : () -> unit }` / Py-I `actor(D, methods=[ping])` /
   **JS-I には存在しない**（`Unknown function: typeof`）。
   このため g9 から `typeof` を外した経緯がある。
3. **アクター型が区別されない**（OCaml）。`unify` が `TActor` 同士を無条件に
   成功させるので `actor[A]` と `actor[B]` が単一化できてしまう。
   型健全性レポート第2版で「モデルが実装より厳しい」と書いた箇所。
4. **効果伝播の穴**（OCaml）。`now` を `future` + `await` に分けると
   効果検査を逃れる。再現サンプルは `docs/samples/soundness2_effect_gap.aipl`。
   修正方針は `TFuture of ty` → `TFuture of ty * eff` にして `Await` が
   効果を加えること。`now_edges` と不動点は不要になる。**未着手**。
5. **型注釈付き変数宣言 `var x : T = e` が未実装**（仕様案にはある）。
6. **出力のフラッシュ揺らぎ**（OCaml REPL）。スクリプト終了時に最後の1行を
   取りこぼすことがある。実装差ではないので比較時は複数回流して判断する。

## 触るときの注意（過去に踏んだ罠）

- **`git checkout -- src/` は禁物**。生成物（`lexer.ml` / `parser.ml`）と
  バイナリが追跡されているので、実装ごと消える。一度やって全部やり直した。
- **`params` を使う文法規則は2つある**（`method_decl` と `select_case`）。
  片方だけ直して g4 を deadlock に戻した。JS-I の `grammar.jison` も同様。
- **`+` → `++` の移行を正規表現でやってはいけない**。`+` は `++` より強く
  結合するので `"a" + b + c` の1つだけ替えると意味が変わる。
  `tools/plus_to_concat.py` が構文木で連鎖を判定する。
  **ただし構文木は文字列リテラルの中を見ない** ---- 実行時コンパイル用の
  ソースを文字列で持つファイル（Dynamic.aipl 等）は別途処理が要る。
- **検査の指摘は件数でなく実物を開く**。reply 検査で 62 件出たが 59 件が
  誤検出だった（Py-I のメソッドは `return` でも返せる、`function` は対象外）。
- **警告が出力経路に載っているか確かめる**。Py-I の `check()` が issues しか
  返しておらず、足した警告が `--type-check` にも現れなかった。
- **`_test_channels.py`（Py-I）は元から不安定**。producer と drain の競合で
  6回中3回程度落ちる。退行の指標にしないこと。
- Py-I のテスト基準値は **15通過 / 5失敗**（`_test_aiactor`,
  `_test_multiprovider`, `_test_signatures`, `_test_sitegen`, `_test_typeck`
  は元から失敗）。

## 文書

`~/aios/abclcp/docs/` にある。すべて kodamay.org に掲載済み。

| PDF | 内容 |
|---|---|
| `aipl_three_impl_parity_ja.pdf` (11p) | **今回の作業記録**。6つの不具合と見つけ方 |
| `aipl_guide_ja.pdf` (26p) | ユーザーズガイド。サンプル8本を全文つきで解説 |
| `aipl_soundness2_ja.pdf` (13p) | 型健全性・型安全性の第2版。期限で進行定理が二択に |
| `aipl_soundness_ja.pdf` (28p) | 同 第1版 |
| `aipl_reply_inference_ja.pdf` (36p) | reply からの戻り値型推論 |
| `aipl_abcl1_features_ja.pdf` (29p) | where / express mode / 理想仕様 |
| `aipl_kobayashi_synthesis_ja.pdf` (16p) | 小林研究の取り込み検討 |

## kodamay.org（別リポジトリ）

`~/kodamay_org_site/kodamay.org`（branch `main`）。**54本掲載**。

- 一覧の生成: `python3 tools/gen_aice_page.py`（エントリはこのスクリプトに書く）
- **アップロードは未実施**。`sh tools/upload_aice_aipl.sh` をユーザーが実行する
  （XREA のパスワード入力が要るので、こちらからは実行できない）。
  未送信の差分: ガイド26p版への差し替え、自作10本、今回の11pレポート
- `.gitignore` が**ホワイトリスト方式**。新しいファイルは `git add -f` が要る

### 判断待ちの2件

- **柴山悦哉「An ABCL Kernel Language and Its Semantics」の原論文スキャンと
  日本語訳**（`~/projects/semantics/20260603_001.pdf`, `ABCL_意味論.pdf`）。
  第三者の著作物なので未掲載。許諾状況が確認できれば掲載できる
- **マニュアル類**（xinu-pi5 / rpi4 / rpi3 の ja/en）。
  「レポート・論文」ではないので保留中

## リポジトリの状態（2026-08-01 時点）

| リポジトリ | ブランチ | 状態 |
|---|---|---|
| `aios/abclcp` | `make-src-base` | commit・push 済み |
| `test-bed/aios-claude` | `add-index-html-aice-portal` | commit・push 済み |
| `projects/drone-hil` | `feat/hybrid-zrp-routing` | commit・push 済み |
| `aipl_line_simulator` | `main` | commit・push 済み |
| `kodamay_org_site/kodamay.org` | `main` | commit・push 済み（サーバー反映は未） |

`abclcp` に未追跡の `.aux` / `.log` / `.out` / `.toc` が 32 個あるが、
LaTeX の中間生成物なのでコミットしない。
