"""`+` の連鎖のうち文字列が絡むものを `++` に移行する。

正規表現では危険：`"a" + b + c` の `+` を1つだけ替えると
`"a" ++ (b + c)` となり（`+` の方が強く結合する）意味が変わる。
連鎖ごと替える必要があるので構文木で判定する。
"""
import sys, os, io
sys.path.insert(0, os.path.expanduser("~/test-bed/aios-claude/src/python-aipl"))
from lark import Lark, Tree, Token
import aipl_parser as AP

GRAMMAR = AP._GRAMMAR if hasattr(AP, "_GRAMMAR") else open(
    os.path.expanduser("~/test-bed/aios-claude/src/python-aipl/grammar.lark"),
    encoding="utf-8").read()
P = Lark(GRAMMAR, parser="lalr", propagate_positions=True)

def is_stringy(node):
    """この部分木の“根”が文字列を生むか。"""
    if isinstance(node, Token):
        return node.type == "STRING"
    if isinstance(node, Tree):
        if node.data in ("string_lit",):
            return True
        # 文字列が絡む + 連鎖もまた文字列
        if node.data == "add_expr":
            return chain_is_stringy(node)
        if node.data == "concat_expr":
            return True
    return False

def chain_is_stringy(node):
    return any(is_stringy(c) for c in node.children
               if not (isinstance(c, Tree) and c.data == "add_op"))

def collect(tree, out):
    if not isinstance(tree, Tree):
        return
    if tree.data == "add_expr" and chain_is_stringy(tree):
        for c in tree.children:
            if isinstance(c, Tree) and c.data == "add_op":
                for t in c.children:
                    if isinstance(t, Token) and t.value == "+":
                        out.append((t.line, t.column, t.start_pos))
    for c in tree.children:
        collect(c, out)

def analyse(path):
    src = open(path, encoding="utf-8").read()
    try:
        tree = P.parse(src)
    except Exception as e:
        return None, str(e).split("\n")[0][:70]
    hits = []
    collect(tree, hits)
    return sorted(set(hits)), None

if __name__ == "__main__":
    files = sys.argv[1:]
    tot_f = tot_h = 0; errs = 0
    for f in files:
        hits, err = analyse(f)
        if err is not None:
            errs += 1; continue
        if hits:
            tot_f += 1; tot_h += len(hits)
    print(f"  対象 {len(files)} 本 / 書き換え対象 {tot_f} 本 / `+` の箇所 {tot_h} 個 / パース不能 {errs} 本")

def apply(path):
    hits, err = analyse(path)
    if err is not None or not hits:
        return 0
    src = open(path, encoding="utf-8").read()
    # 末尾から置換する（"+" 1文字 -> "++" 2文字 で以降の位置がずれるため）
    for _line, _col, pos in sorted(hits, key=lambda h: -h[2]):
        assert src[pos] == "+", (path, pos, src[pos-5:pos+5])
        src = src[:pos] + "++" + src[pos+1:]
    open(path, "w", encoding="utf-8").write(src)
    return len(hits)
