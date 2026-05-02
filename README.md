# ABCL/c+ AI-OS Workspace

This repository is the working baseline for growing ABCL/c+ into an actor-first
AI-OS implementation.

## Current Baseline

- Core language/runtime: `src/`
- Actor runtime: `src/eval_thread.ml`
- REPL entry point: `src/repl_thread.ml`
- Parser/lexer sources: `src/parser.mly`, `src/lexer.mll`
- Checked-in generated parser/lexer baseline: `src/parser.ml`, `src/lexer.ml`
- Existing samples: `abclc/*.abcl`
- AI-OS design notes: `docs/AIOS_LANGUAGE_DESIGN.md`
- AIOS kernel notes: `docs/AIOS_KERNEL.md`

The current top-level build is:

```sh
dune build
```

## Implementation Direction

ABCL/c+ should treat every OS-level unit as an actor:

- kernel service
- UI component
- web endpoint
- device adapter
- model adapter
- memory service
- tool adapter
- autonomous agent

The existing `class` / `new` / `send` model is the right foundation. The first
implementation goal is not a new syntax layer, but a small, stable AI-OS kernel
around the current actor runtime.

## Near-Term Work

1. Keep current ABCL/c+ samples building and loading.
2. Document the current language surface before changing syntax.
3. Split primitives into explicit capabilities.
4. Normalize actor registry, mailbox, event log, and web gateway APIs.
5. Add AI services as actors first, not as special syntax.
6. Add typed synchronous and future sends only after method return types are
   represented in the AST and type checker.

## AIOS Kernel Smoke Test

```sh
cd src
opam exec -- make
printf 'load ../abclc/aios_kernel.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Service registry smoke test:

```sh
printf 'load ../abclc/aios_services.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Standard services smoke test:

```sh
printf 'load ../abclc/aios_standard_services.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Agent loop smoke test:

```sh
printf 'load ../abclc/aios_agent.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Kernel memory smoke test:

```sh
printf 'load ../abclc/aios_memory_store.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Task manager smoke test:

```sh
printf 'load ../abclc/aios_task_manager.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Quiet REPL smoke test:

```sh
printf 'load ../abclc/aios_quiet_demo.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
```

Gemini single-AI smoke test:

```sh
export GEMINI_API_KEY='...'
printf 'load ../abclc/gemini_single_ai.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Gemini AIOS agent smoke test:

```sh
export GEMINI_API_KEY='...'
printf 'load ../abclc/aios_gemini_agent.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Model router smoke test:

```sh
export GEMINI_API_KEY='...'
printf 'load ../abclc/aios_model_router.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Offline workflow smoke test:

```sh
printf 'load ../abclc/aios_workflow_mock.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
```

Gemini workflow smoke test:

```sh
export GEMINI_API_KEY='...'
printf 'load ../abclc/aios_workflow_gemini.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
```

Multi-Gemini AIOS smoke test:

```sh
export GEMINI_API_KEY='...'
printf 'load ../abclc/aios_multi_gemini.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

Quota-saving one-call multi-agent smoke test:

```sh
export GEMINI_API_KEY='...'
printf 'load ../abclc/aios_multi_gemini_onecall.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

OpenAI single-AI smoke test:

```sh
export OPENAI_API_KEY='...'
printf 'load ../abclc/openai_single_ai.abcl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

## Compatibility Policy

Existing samples under `abclc/` are the compatibility baseline. AI-OS features
should be added in small steps without breaking current `class`, `method`,
`var`, `new`, `send`, `send!`, `become`, `select`, and `remote` behavior.
