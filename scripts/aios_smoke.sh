#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
SRC="$ROOT/src"

run_sample() {
  sample="$1"
  expect="$2"
  label="$3"
  tmp="${TMPDIR:-/tmp}/aios-smoke-$$.out"

  printf '[aios-smoke] %s\n' "$label"
  (
    cd "$SRC"
    printf 'load ../abclc/%s\ncompile\nquit\n' "$sample" |
      SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
  ) >"$tmp" 2>&1

  if grep -F "$expect" "$tmp" >/dev/null; then
    rm -f "$tmp"
    printf '[aios-smoke] ok: %s\n' "$label"
  else
    printf '[aios-smoke] failed: %s\n' "$label"
    printf '[aios-smoke] expected: %s\n' "$expect"
    cat "$tmp"
    rm -f "$tmp"
    exit 1
  fi
}

cd "$SRC"
opam exec -- make

run_sample "now_future.aipl" "future result = 30." "now/future message send"
run_sample "aios_kernel.aipl" "ABCL/c+ AIOS kernel" "kernel introspection"
run_sample "aios_services.aipl" "memory get = 42" "service registry"
run_sample "aios_memory_store.aipl" "memory has answer = true" "kernel memory"
run_sample "aios_task_manager.aipl" "status=done" "task manager"
run_sample "aios_workflow_mock.aipl" "workflow.done:task-1" "offline mock workflow"

printf '[aios-smoke] all passed\n'
