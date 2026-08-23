#!/bin/sh
# ガイドのサンプルを3実装で流して出力を並べる。
#   使い方: sh tools/run_all_impls.sh [サンプル名...]
# 引数を省くと g1..g9 を全部流す。
set -u
ABCLCP="$HOME/aios/abclcp"
PYI="$HOME/test-bed/aios-claude/src/python-aipl"
JSI="$HOME/projects/drone-hil/abcl"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

SAMPLES="${*:-g1_hello g2_now_future g3_actors g4_select g6_effects g7_deadline g8_bool_equality g9_actor_arg g10_shared_field_names}"
printf '%-22s %-26s %-26s %s\n' サンプル OCaml Py-I JS-I
for g in $SAMPLES; do
  F="$ABCLCP/docs/samples/guide/$g.aipl"
  [ -f "$F" ] || { printf '%-22s (見つからない)\n' "$g"; continue; }

  printf 'load %s\ncompile\n' "$F" > "$TMP/r.repl"
  O=$(cd "$ABCLCP" && timeout 30 ./src/abclrepl_thread -q -f "$TMP/r.repl" </dev/null 2>&1 \
      | grep -vE '^\[|^Compiler|^ABCL/c\+>|^$' | head -3 | tr '\n' '/' | tr -d ' ')
  P=$(cd "$PYI" && timeout 30 python3 aipl_main.py "$F" 2>&1 \
      | grep -vE '^\[|^$' | head -3 | tr '\n' '/' | tr -d ' ')
  J=$(timeout 40 node "$ABCLCP/tools/js_run.mjs" "$F" "$JSI" 2>&1 | tail -1 \
      | tr '/' '\n' | grep -vE '^\s*\[' | head -3 | tr '\n' '/' | tr -d ' ')

  if [ "$O" = "$P" ] && [ "$P" = "$J" ]; then M="一致"; else M="★差あり"; fi
  printf '%-22s %-26s %-26s %-26s %s\n' "$g" "${O%/}" "${P%/}" "${J%/}" "$M"
done
