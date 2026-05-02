# Gemini Model Service

作成日: 2026-05-02

ABCL/c+ AIOS から Gemini API を呼び出す最小経路。

## Key Handling

API key はソースや `.abcl` サンプルに保存しない。
実行時に環境変数 `GEMINI_API_KEY` から読む。

```sh
export GEMINI_API_KEY='...'
```

任意でモデルを変更できる。

```sh
export GEMINI_MODEL='gemini-2.5-flash'
```

## Primitive

```abcl
gemini_generate(prompt)  // string
```

`gemini_generate` は `AIOS.Model.Gemini` capability に属する。

## Sample

```sh
cd src
opam exec -- make
printf 'load ../abclc/gemini_single_ai.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

AIOS agent sample:

```sh
printf 'load ../abclc/aios_gemini_agent.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

このサンプルは `memory`、`model`、`agent` の3サービスを登録し、
`agent` が `aios_future("model", "generate", prompt)` で Gemini に依頼する。

Multi-AI sample:

```sh
printf 'load ../abclc/aios_multi_gemini.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

このサンプルは `planner`、`solver`、`reviewer`、`coordinator` を別々の
AIOS サービスとして登録する。`coordinator` が `aios_future` と `await` で
3つの Gemini AI サービスを協調させる。

Free tier quota が厳しい場合は、1回の Gemini 呼び出しで複数AIの役割を
シミュレートするサンプルを使う。

```sh
printf 'load ../abclc/aios_multi_gemini_onecall.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

429 が短期レート制限の場合、helper は `RetryInfo` に従って短く再試行する。
再試行回数は `GEMINI_RETRIES` で変更できる。

```sh
export GEMINI_RETRIES=3
```

## Implementation

`src/eval_thread.ml` の primitive から `scripts/gemini_generate.py` を呼び出す。
helper script は Google Gemini REST API の `generateContent` endpoint を使う。
