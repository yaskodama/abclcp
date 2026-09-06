#!/usr/bin/env bash
# board_matrix.sh — 正典 AIPL が三台の実機とホスト VM で同じように動くかを測る。
#
#   ./tools/board_matrix.sh [pi3|pi4|pi5|mac|all]
#
# docs/samples/probe/*.aipl（正典の型検査を通したもの）を各板に投げ、
# 出力を expect/ の期待値と突き合わせる。板ごとに投げ方が違うので、
# そこだけを関数に閉じ込めてある。
#
# ★ 版の確認を必ず先に行う。焼いても電源を入れ直すまで板は前のカーネルで
#   応答するので、「HTTP が返る」ことは反映の証拠にならない。
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"
PROBE="$HERE/docs/samples/probe"
EXPECT="$HERE/docs/samples/probe/expect"
AVM="${AVM_DIR:-$HOME/projects/aice-avm}"

PI3=192.168.3.50:8080
PI4=192.168.3.100
PI5=192.168.3.101

norm() { tr -s ' \n' ' ' | sed 's/^ //; s/ $//'; }

run_pi5() { curl -s -m 60 --data-binary @"$1" "http://$PI5/cc" | sed 's/=> 0$//' | norm; }
run_pi4() { curl -s -m 60 --data-binary @"$1" "http://$PI4/cc?resident=1" \
            | sed 's/=> 0$//; s/\[resident:.*//' | norm; }
run_pi3() {
  # Pi 3 は Mac 側で .avm に直してから投げ、出力は /api/console で読む。
  # 連投すると HTTP が詰まるので必ず間を置く。
  "$AVM/_build/default/compile_avm.exe" "$1" /tmp/_bm.avm >/dev/null 2>&1 || { echo "COMPILE-NG"; return; }
  curl -s -m 15 "http://$PI3/api/console?clear=1" >/dev/null 2>&1
  sleep 8
  "$AVM/_build/default/send.exe" "$PI3" /tmp/_bm.avm --noask >/dev/null 2>&1
  sleep 14
  curl -s -m 20 "http://$PI3/api/console" 2>/dev/null | python3 -c "
import sys,json
try:
  d=json.load(sys.stdin)
  print(' '.join(l.split(': ',1)[-1] for l in d['lines']))
except Exception: print('NG')" | norm
}
run_mac() {
  "$AVM/_build/default/compile_avm.exe" "$1" /tmp/_bm.avm >/dev/null 2>&1 || { echo "COMPILE-NG"; return; }
  local port=8123 log=/tmp/_bm.log
  pkill -f "server.exe $port" 2>/dev/null; sleep 1; rm -f $log
  ("$AVM/_build/default/server.exe" $port --no-open >$log 2>&1 &)
  sleep 3
  "$AVM/_build/default/send.exe" "127.0.0.1:$port" /tmp/_bm.avm --noask >/dev/null 2>&1
  sleep 6
  grep '\[vm\]' $log | sed 's/^\[vm\] a[0-9]*: //' | norm
  pkill -f "server.exe $port" 2>/dev/null
}

# 版を読む。★ 一発で取れなくても諦めない ―― 直前の実行で板が忙しいと
# 取りこぼし、版が空のまま「通過」を報告してしまう（実際にそうなった）。
# 版が分からないまま合否だけ出すのは、この道具の趣旨に反する。
version_of() {
  local url=""
  case "$1" in
    pi3) url="http://$PI3/version" ;;
    pi4) url="http://$PI4/version" ;;
    pi5) url="http://$PI5/version" ;;
    mac) echo "host VM"; return ;;
  esac
  local i v
  for i in 1 2 3 4 5; do
    v="$(curl -s -m 10 "$url" 2>/dev/null | head -1)"
    case "$v" in build*) echo "$v"; return ;; esac
    sleep 3
  done
  echo "版を読めません（/version が無い世代か、板が忙しい）"
}

check_board() {
  local b="$1" pass=0 fail=0
  echo "=== $b  （$(version_of "$b")） ==="
  for f in "$PROBE"/p*.aipl; do
    local n; n="$(basename "$f" .aipl)"
    local exp="$EXPECT/$n.txt"
    [ -f "$exp" ] || { printf "  %-12s (期待値なし) %s\n" "$n" "$(run_$b "$f")"; continue; }
    local got; got="$(run_$b "$f")"
    local want; want="$(cat "$exp" | norm)"
    if [ "$got" = "$want" ]; then printf "  %-12s ok\n" "$n"; pass=$((pass+1))
    else printf "  %-12s NG\n    期待 %s\n    実際 %s\n" "$n" "$want" "$got"; fail=$((fail+1)); fi
  done
  echo "  -> $pass 通過 / $fail 不一致"
  echo
}

case "${1:-all}" in
  all) for b in mac pi5 pi4 pi3; do check_board $b; done ;;
  *)   check_board "$1" ;;
esac
