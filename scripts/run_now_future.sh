#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
SRC="$ROOT/src"

cd "$SRC"
opam exec -- make

printf 'load ../abclc/now_future.abcl\ncompile\nquit\n' |
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
