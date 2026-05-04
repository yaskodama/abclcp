#!/bin/sh
set -eu

cd "$(dirname "$0")/../src"
opam exec -- make

printf 'load ../abclc/session_protocol_solve.abcl\ncompile\nquit\n' |
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
