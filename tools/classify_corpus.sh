#!/bin/sh
# .aipl を「核 / 拡張 / 要修正」に分類する。
#
#   sh tools/classify_corpus.sh [根ディレクトリ...]
#
# AIPL は二層である。
#   核   ---- OCaml 版（正）・Py-I・JS-I の三つすべてが実装する。論文の仕様。
#   拡張 ---- Py-I のみ。記録型・チャネル・所有・精緻化型・saga など。
# 分類は「どの処理系が受け付けるか」で機械的に決める。
#
#   OCaml が通る                     -> 核
#   OCaml は落ちるが Py-I が通る     -> 拡張
#   どちらも落ちる                   -> 要修正
#
# 「弾かれるのが正しい」プログラムは、要修正と区別する必要がある。
# 印は先頭付近のコメント一行で書く:
#
#     // @expect reject: <理由>
#
# docs/samples/reject と docs/samples/reply_inference は
# ディレクトリごと同じ扱いにする（歴史的にそこへ集めてあるため）。
set -u
ABCLCP="$HOME/aios/abclcp"
PYI="$HOME/test-bed/aios-claude/src/python-aipl"
TC="$ABCLCP/tools/tc"
ROOTS="${*:-$HOME/aios/abclcp $HOME/test-bed/aios-claude $HOME/projects/drone-hil}"

[ -x "$TC" ] || { echo "tools/tc が無い。src を make してから再実行" >&2; exit 1; }

core=0; ext=0; broken=0; intentional=0; liar=0
: > /tmp/aipl_classify.tsv
for f in $(find $ROOTS -name '*.aipl' 2>/dev/null | grep -v '/removed/' | sort); do
  case "$f" in
    */samples/reject/*|*/samples/reply_inference/*) l=意図的; intentional=$((intentional+1));;
    *)
      if head -15 "$f" | grep -q '@expect reject'; then
        # 印が正直かどうかも見る。どちらの処理系も通してしまうなら、
        # 「弾かれるのが正しい」という主張が嘘になっている。
        if ! timeout 25 "$TC" "$f" 2>&1 | grep -qE '^(TYPE_ERROR|PARSE_ERROR)' \
           && ! (cd "$PYI" && timeout 45 python3 aipl_main.py --type-check "$f" 2>&1 \
                 | grep -qE '^\[parse error\]|^\[type\] [1-9]'); then
          echo "[warn] @expect reject と書いてあるが、両方の処理系が通す: $f" >&2
          liar=$((liar+1))
        fi
        l=意図的; intentional=$((intentional+1))
        printf '%s\t%s\n' "$l" "$f" >> /tmp/aipl_classify.tsv
        continue
      fi
      if timeout 25 "$TC" "$f" 2>&1 | grep -qE '^(TYPE_ERROR|PARSE_ERROR)'; then
        if (cd "$PYI" && timeout 45 python3 aipl_main.py --type-check "$f" 2>&1 \
             | grep -qE '^\[parse error\]|^\[type\] [1-9]'); then
          l=要修正; broken=$((broken+1))
        else
          l=拡張; ext=$((ext+1))
        fi
      else
        l=核; core=$((core+1))
      fi;;
  esac
  printf '%s\t%s\n' "$l" "$f" >> /tmp/aipl_classify.tsv
done
printf '核 %s / 拡張 %s / 意図的な不正例 %s / 要修正 %s\n' "$core" "$ext" "$intentional" "$broken"
[ "$liar" -gt 0 ] && printf '★ 印が嘘になっているもの: %s 本（上の [warn] を見よ）\n' "$liar"
echo '（明細は /tmp/aipl_classify.tsv）'
