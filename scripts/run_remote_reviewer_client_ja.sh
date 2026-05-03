#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
SRC="$ROOT/src"

: "${REMOTE_REVIEWER_HOSTPORT:=127.0.0.1:18080}"
export REMOTE_REVIEWER_HOSTPORT

cd "$SRC"
opam exec -- make

printf 'load ../abclc/aios_remote_reviewer_solve_ja.abcl\ncompile\nquit\n' |
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
