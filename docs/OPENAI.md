# OpenAI Model Service

作成日: 2026-05-02

ABCL/c+ AIOS から OpenAI API を呼び出す最小経路。

## Key Handling

API key はソースや `.aipl` サンプルに保存しない。
実行時に環境変数 `OPENAI_API_KEY` から読む。

```sh
export OPENAI_API_KEY='...'
```

任意でモデルを変更できる。

```sh
export OPENAI_MODEL='gpt-4.1'
```

## Primitive

```abcl
openai_generate(prompt)  // string
```

`openai_generate` は `AIOS.Model.OpenAI` capability に属する。

## Sample

```sh
cd src
opam exec -- make
printf 'load ../abclc/openai_single_ai.aipl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

## Implementation

`src/eval_thread.ml` の primitive から `scripts/openai_generate.py` を呼び出す。
helper script は OpenAI Responses API の `POST /v1/responses` endpoint を使う。

Authentication は公式APIの Bearer token 形式に従う。

```text
Authorization: Bearer $OPENAI_API_KEY
```
