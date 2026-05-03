#!/bin/sh
set -eu

: "${REMOTE_REVIEWER_HOSTPORT:=127.0.0.1:18080}"

printf '箱が3つあります\n---ANSWER---\n12個です\n' |
  python3 "$(dirname "$0")/remote_review_call.py" "$REMOTE_REVIEWER_HOSTPORT" --ja
