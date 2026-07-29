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
| `s5_overload_ambiguity.abcl` | `a + b` に principal type が無いこと | OK ＋ ambiguous 警告。strict なら型エラー |
| `s6_usable_result.abcl` | now の結果を算術に使う | OK。**パッチ前は `no overload of + matches (any, int)` で落ちていた** |
| `s7_annotation_ok.abcl` | 戻り値型注釈 `method m(x) : T`。期待型が overload 解決へ流れること | OK。`add : (int * int) -> int`。**s5 の曖昧性が注釈だけで解消する** |
| `s8_annotation_conflict.abcl` | 宣言型と食い違う reply | 型エラー `declared to reply with int, but replies with string here` |
| `s9_missing_path.abcl` | 全パス被覆検査 | 型エラー `some execution path does not reply`。**注釈が無ければ書けない検査** |

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
