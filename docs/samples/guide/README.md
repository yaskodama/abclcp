# 言語ガイドのサンプル

`docs/aipl_guide_ja.tex`（PDF: `docs/aipl_guide_ja.pdf`）第III部で解説している
チュートリアル用サンプル。**すべて型検査を通り、実行結果も PDF 掲載のとおり**。

| ファイル | 扱う内容 |
|---|---|
| `g1_hello.aipl` | クラス・フィールド・`init`・`send`・文字列連結 `++` |
| `g2_now_future.aipl` | `now` / `future` / `await`、戻り値型注釈と推論 |
| `g3_actors.aipl` | 複数アクター、アクターを跨いだ `now`、全パス被覆検査 |
| `g4_select.aipl` | `select` / `case` / `timeout`、case の `reply` の帰属 |
| `g5_web.aipl` | `web_listen` / `web_expose` と注釈の必須化 |

負例（通らないことを確認するもの）は `../reply_inference/` にある。

## 型検査

```sh
cd src && make thread_repl && cd ..
ocamlfind ocamlc -package unix -thread -linkpkg -w -a -I src -o tc \
  src/location.cmo src/types.cmo src/ast.cmo src/typing_env.cmo \
  src/infer.cmo src/typecheck.cmo src/parser.cmo src/lexer.cmo \
  docs/samples/reply_inference/tc_main.ml

for f in docs/samples/guide/g*.aipl; do ./tc "$f"; done
```

## 実行

```sh
cat > run.repl <<'EOF'
load docs/samples/guide/g2_now_future.aipl
compile
EOF
./src/abclrepl_thread -q -f run.repl < /dev/null
```

`g5_web.aipl` は `web_listen(8080)` で待ち受けに入るので、別の端末から:

```sh
curl -s -X POST http://localhost:8080/api/x/echo -d 'method=say&args=hi'
```

## 期待される出力

```
g1_hello        hello, AIPL / tick 1 / tick 2
g2_now_future   twice = 43 / awaited = 20 / v=7
g3_actors       ok, left=7 / sold out
g4_select       direct:1 / waiting / timed out
```

`g4` の出力順は、`now w.job(1)` が通常のメソッド dispatch で先に処理され、
`serve` の `select` が動いたときには mailbox に `job` が残っていないことを示す。
**`select` で待つメッセージ名は直接呼ばせない設計にするのが安全。**
