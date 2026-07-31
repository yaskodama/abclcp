#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
SRC="$ROOT/src"
PORT="${REMOTE_REVIEWER_PORT:-18080}"
LOG="${TMPDIR:-/tmp}/remote-reviewer-$$.log"

cleanup() {
  if [ "${SERVER_PID:-}" ]; then
    kill "$SERVER_PID" >/dev/null 2>&1 || true
    wait "$SERVER_PID" >/dev/null 2>&1 || true
  fi
  rm -f "$LOG"
}
trap cleanup EXIT INT TERM

REMOTE_REVIEWER_PORT="$PORT" python3 "$ROOT/scripts/remote_reviewer_server.py" >"$LOG" 2>&1 &
SERVER_PID=$!

i=0
while [ "$i" -lt 20 ]; do
  if grep -F "remote reviewer listening" "$LOG" >/dev/null 2>&1; then
    break
  fi
  i=$((i + 1))
  sleep 0.1
done

cd "$SRC"
opam exec -- make
printf 'load ../abclc/aios_remote_reviewer_solve.aipl\ncompile\nquit\n' |
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread -q
