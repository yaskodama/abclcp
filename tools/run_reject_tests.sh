#!/bin/sh
# 「弾かれるべきプログラム」が3実装それぞれで弾かれるかを見る。
#   使い方: sh tools/run_reject_tests.sh
#
# run_all_impls.sh が「通るプログラムの出力が一致するか」を見るのに対し、
# こちらは「通ってはいけないプログラムが止まるか」を見る。
# 型検査の退行と、実装間の検査の食い違いは、こちらでしか出ない。
set -u
ABCLCP="$HOME/aios/abclcp"
DIR="$ABCLCP/docs/samples/reject"
PYI="$HOME/test-bed/aios-claude/src/python-aipl"
JSI="$HOME/projects/drone-hil/abcl"
TC="$ABCLCP/tools/tc"

if [ ! -x "$TC" ] || [ "$ABCLCP/src/infer.cmo" -nt "$TC" ]; then
  ocamlfind ocamlc -package unix -thread -linkpkg -g -w -a -I "$ABCLCP/src" -o "$TC" \
    "$ABCLCP/src/location.cmo" "$ABCLCP/src/types.cmo" "$ABCLCP/src/ast.cmo" \
    "$ABCLCP/src/typing_env.cmo" "$ABCLCP/src/infer.cmo" "$ABCLCP/src/typecheck.cmo" \
    "$ABCLCP/src/parser.cmo" "$ABCLCP/src/lexer.cmo" "$ABCLCP/tools/tc_main.ml" \
    >/dev/null 2>&1 || echo "（tc のビルドに失敗。src を make してから再実行）" >&2
fi

# 期待: reject / warn（期限は既定で警告）
expect_of() { case "$1" in r3_*) echo warn ;; *) echo reject ;; esac; }

mark() { [ "$1" = "$2" ] && echo "○" || echo "×"; }

printf '%-24s %-6s %-8s %-8s %-8s\n' テスト 期待 OCaml Py-I JS-I
ng=0
for f in "$DIR"/r*.aipl; do
  b=$(basename "$f" .aipl); exp=$(expect_of "$b")

  o=$(timeout 30 "$TC" "$f" 2>&1)
  if   printf '%s' "$o" | grep -q '^TYPE_ERROR'; then O=reject
  elif printf '%s' "$o" | grep -q '^\[warn\]';   then O=warn
  else O=pass; fi

  p=$(cd "$PYI" && timeout 40 python3 aipl_main.py --type-check "$f" 2>&1)
  n=$(printf '%s' "$p" | sed -n 's/^\[type\] \([0-9]*\) issue(s).*/\1/p' | head -1)
  if [ "${n:-0}" -ge 1 ] 2>/dev/null; then
    if printf '%s' "$p" | grep -q '期限が無い'; then P=warn; else P=reject; fi
  else P=pass; fi

  j=$(timeout 40 node "$ABCLCP/tools/js_check.mjs" "$f" "$JSI" 2>&1)
  if printf '%s' "$j" | grep -q '0 issue(s)'; then J=pass
  elif printf '%s' "$j" | grep -q '期限が無い'; then J=warn
  else J=reject; fi

  printf '%-24s %-6s %-8s %-8s %-8s\n' "$b" "$exp" \
    "$(mark "$O" "$exp")$O" "$(mark "$P" "$exp")$P" "$(mark "$J" "$exp")$J"
  for v in "$O" "$P" "$J"; do [ "$v" = "$exp" ] || ng=$((ng+1)); done
done
echo
echo "期待と違う枠 $ng 件（3実装 × テスト数のうち）"
