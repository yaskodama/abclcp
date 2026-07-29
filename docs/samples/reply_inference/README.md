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
