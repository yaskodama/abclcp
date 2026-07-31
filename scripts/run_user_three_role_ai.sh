#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
SRC="$ROOT/src"

: "${ABCL_AI_PROVIDER:=mock}"
export ABCL_AI_PROVIDER

cd "$SRC"
opam exec -- make

printf 'load ../abclc/aios_user_three_role_ai.aipl\ncompile\nquit\n' |
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
