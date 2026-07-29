# reply からのメソッド戻り値型推論 — サンプル

`docs/aipl_reply_inference_ja.tex` (PDF: `docs/aipl_reply_inference_ja.pdf`) の
付録 A で参照しているサンプル一式。

## ビルドと実行

REPL は SDL に依存するので、型検査だけを走らせる最小ドライバ `tc_main.ml` を使う。

```sh
cd src && make thread_repl && cd ..

ocamlfind ocamlc -package unix -thread -linkpkg -w -a -I src -o tc \
  src/location.cmo src/types.cmo src/ast.cmo src/typing_env.cmo \
  src/infer.cmo src/typecheck.cmo src/parser.cmo src/lexer.cmo \
  docs/samples/reply_inference/tc_main.ml

for f in docs/samples/reply_inference/s*.abcl; do ./tc "$f"; done
```

`AIOS_STRICT_OVERLOAD=1` を付けると、曖昧なオーバーロードが警告ではなく
型エラーになる。

## 各サンプルの意図

| ファイル | 何を見るか | 期待される結果 |
|---|---|---|
| `s1_ok.abcl` | reply から戻り値型が推論されること。reply の無いメソッドが unit へ defaulting されること | OK。`twice:(int)->int`, `greet:(string)->string`, `log:('a)->unit` |
| `s2_missing_reply.abcl` | reply を書き忘れたメソッドの結果を now で使う | 型エラー `(unit, int)`。パッチ前は `(any, int)` で原因が読めなかった |
| `s3_conflict.abcl` | 分岐ごとに異なる型を reply する | 型エラー `reply type mismatch`。**パッチ前は素通りしていた** |
| `s4_chain.abcl` | ρ がアクター境界を越えて伝播すること | OK。`Store#get->int` → `Front#fetch->string` |
| `s5_overload_ambiguity.abcl` | `a + b` に principal type が無いこと | OK ＋ ambiguous 警告（`float`/`int`）。strict なら型エラー |
| `s6_usable_result.abcl` | now の結果を算術に使う | OK。**パッチ前は `no overload of + matches (any, int)` で落ちていた** |
| `s7_annotation_ok.abcl` | 戻り値型注釈 `method m(x) : T`。期待型が overload 解決へ流れること | OK。`add : (int * int) -> int`。**s5 の曖昧性が注釈だけで解消する** |
| `s8_annotation_conflict.abcl` | 宣言型と食い違う reply | 型エラー `declared to reply with int, but replies with string here` |
| `s9_missing_path.abcl` | 全パス被覆検査 | 型エラー `some execution path does not reply`。**注釈が無ければ書けない検査** |
| `s10_expose_unannotated.abcl` | リモート境界での注釈必須 | `web_expose` した Adder は型エラー、`web_listen` だけで届く Logger は警告 |
| `s11_service.abcl` | **追加機能を一通り使う統合サンプル** | OK。`serve -> unit`（case の reply は place へ帰属）、注釈の無い `twice -> int` |
| `s12_service_exposed.abcl` | s11 を外部公開した版 | 型エラー。ローカルなら推論で済む `twice` が公開すると宣言必須になる |
| `s13_runtime_mismatch.abcl` | **型検査器と評価器の食い違い**（修正済の回帰テスト） | 型検査 `T#f -> int`、実行 `3`。修正前は `3.` |
| `s14_select_pattern.abcl` | select パターンをメソッド署名に照合 | 型エラー `case m binds 1 variable(s) but method m takes 2` |
| `s15_double_reply.abcl` | reply の線形性（高々一度） | 型エラー `may reply more than once on some path` |
| `s16_concat.abcl` | 文字列連結 `++` と数値 `+` の分離 | OK。`label/both/plain -> string`, `sum -> int` |

## 実際に処理系で走らせる

型検査だけでなく実行する場合は、REPL コマンドのファイルを作って `-f` に渡す。

```sh
cat > run.repl <<'EOF'
load docs/samples/reply_inference/s11_service.abcl
compile
EOF
./src/abclrepl_thread -q -f run.repl < /dev/null
```

`-f` に `.abcl` を直接渡すと REPL コマンドとして 1 行ずつ解釈されるので、
クラス定義は読まれない（`Actor stock not found` になる）。`load` + `compile` が正しい。

## 戻り値型注釈の構文

```
method m(x) : int { reply(x * 2); }
```

書ける型は `int` / `float` / `string` / `bool` / `unit` / `any`、
および大文字始まりのクラス名（actor 型）。注釈は省略可能で、
省略した場合は従来どおり `reply` から推論する。

注釈があると次の3つが変わる。

1. `reply` はすべて宣言型に照合される（衝突時の blame が正しい位置に出る）
2. `unit` 以外を宣言したメソッドは**全実行パスで reply する**ことを検査される
3. 宣言型が**期待型として式の推論へ流れる**（双方向型付け）。
   これにより `reply(a + b)` のように引数だけでは principal type が
   決まらない式も一意に解決する

## リモート境界では注釈が必須

境界を開くのは `web_listen` である。gateway の `POST /api/send` は
`to=<アクター名>` で**任意のアクター**に到達するので、`web_expose` は
公開エンドポイントに別名を付けるだけで到達可能性を絞っていない。
そこで2段階で報告する。

| | 判定 |
|---|---|
| `web_expose` で名指しされたアクターのメソッド（`init` を除く） | **型エラー**（`AIOS_LAX_EXPOSE=1` で警告） |
| `web_listen` があるとき、それ以外のアクター | 警告 |

リモート送信 `now remote(host, actor).m()` の相手は別ノードにあり、
本体がこのプログラムに無いので検査できない。

## select の case 本体の reply は「別のメッセージ」に返る

`eval_thread` は case 実行の前に `set_current_msg_id` を選択された
メッセージの id に差し替える。したがって

```
method main() : unit {
  select { case add(a, b) -> { reply(a + b); } ... }
}
```

の `reply` は `main` ではなく **`add` への返信**である。型検査器も
case 本体では `reply` を `add` の ρ に束縛する。`timeout` 本体は
囲むメソッドの msg_id のまま走るので、そちらは囲むメソッドに属する。


## 型と実行値の差分テスト

型検査が付けた戻り値型と、実行時に実際に reply された値の型を突き合わせる。

```sh
python3 scripts/type_runtime_diff.py abclc/*.abcl docs/samples/reply_inference/s*.abcl
```

処理系側は `AIOS_TYPE_TRACE=1` のとき reply のたびに
`[rtype] Class#method = tag` を出す。ハーネスはこれと型検査結果を照合する。

- 型変数のまま（`'a`）や `any` は「型システムが何も約束していない」ので判定しない
- 実行中に一度も reply されなかったメソッドは観測なしで skip
- わざと食い違う負例には `// TYPE_RUNTIME_DIFF: expect-mismatch` と書いておくと
  既知として数え、終了コードを 1 にしない

この仕組みで、整数演算が `VFloat` を返していた preservation の破れが見つかった。


## 文字列連結は `++`（`+` は数値専用）

かつて `+` は数値2種と文字列連結2種の計4候補を持ち、両辺が未束縛の `a + b` では
4つとも一致してしまっていた。しかも候補列が登録順の逆だったため
`('a * string) -> string` が必ず先頭に来て、引数まで string に焼き付いていた。

```
"n=" ++ 42   ->  "n=42"       1 ++ 2  ->  "12"
"a"  ++ "b"  ->  "ab"         1 +  2  ->  3
"a"  +  "b"  ->  no overload of + matches (string, string)
```

- `++ : forall a b. (a * b) -> string`（候補1つ。両辺を文字列化して連結）
- `+` は数値専用。結合は `++` のほうが弱いので `"x=" ++ a + b` は `"x=" ++ (a + b)`

既存コードは型検査器のエラー位置に従って機械的に移行した（38ファイル / 255箇所）。
`Binop` の位置は演算子トークンそのものを指すので、`no overload of + matches` が
出た (line, col) の1文字を `++` にして再検査、を繰り返せばよい。

**注意2点**: 列は**バイトオフセット**なので日本語を含む行では文字インデックスと
ずれる（置換はバイト列で行う）。また、この方法は**文字列連結以外の理由で失敗している
`+` も書き換えてしまう** — `s2_missing_reply.abcl` の `print(x + 1)` は
`x` が `unit` だから失敗する意図的な負例なので、手で戻した。

string 由来の曖昧性は消えたが、`int`/`float` の曖昧性は残る。
完全に消すには `+` と `+.` のように数値側も分ける必要がある。
