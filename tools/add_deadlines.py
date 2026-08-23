# -*- coding: utf-8 -*-
"""期限の無い now / await に `timeout <ms> else <既定値>` を足す。

現行の AIPL は待ちに期限を要求する。

罠が二つある。どちらも実際に踏んだ。

  1. 文字列リテラルとコメントの中の `now a.m(...)` に反応してはならない。
     `print("typeof(now AI.ask(\\"x\\"))")` の中身は「文字列」であって式ではない。
     位置を保ったまま伏せた版を作ってから走査する。
  2. 閉じ括弧は対応を数えて見つける。文字列の中の括弧を数えると
     print(...) の閉じ括弧まで飛んでしまう。

else の既定値は、呼び先メソッドの戻り値注釈（無ければ reply の中身）から決める。

  使い方: python3 tools/add_deadlines.py file.aipl ...
"""
import io, re, sys

MS = 5000


def mask(ln: str) -> str:
    """文字列とコメントを `_` で伏せた版。位置は保つ。"""
    out = []
    i, n, instr = 0, len(ln), False
    while i < n:
        c = ln[i]
        if instr:
            if c == '\\' and i + 1 < n:
                out.append('_'); out.append('_'); i += 2; continue
            if c == '"':
                instr = False; out.append('"'); i += 1; continue
            out.append('_'); i += 1; continue
        if c == '"':
            instr = True; out.append('"'); i += 1; continue
        if c == '/' and i + 1 < n and ln[i + 1] == '/':
            out.append('_' * (n - i)); break
        out.append(c); i += 1
    return ''.join(out)


def close_paren(ln: str, i: int) -> int:
    """ln[i] が '(' のとき、対応する ')' の位置。文字列の中の括弧は数えない。"""
    m = mask(ln)
    d = 0
    while i < len(ln):
        if m[i] == '(':
            d += 1
        elif m[i] == ')':
            d -= 1
            if d == 0:
                return i
        i += 1
    return -1


def defaults(src: str) -> dict:
    """メソッド名 -> else の既定値。戻り値注釈が無ければ reply の中身から推す。"""
    d = {}
    for m in re.finditer(r'method\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*(?::\s*([A-Za-z_]\w*))?', src):
        if m.group(3):
            d[m.group(1)] = {'string': '""', 'int': '0', 'float': '0.0',
                             'bool': 'false', 'unit': '0'}.get(m.group(3), '0')
    for m in re.finditer(r'method\s+([A-Za-z_]\w*)\s*\([^)]*\)\s*(?:!\{[^}]*\})?\s*\{', src):
        name = m.group(1)
        if name in d:
            continue
        i, depth = m.end(), 1
        while i < len(src) and depth:
            if src[i] == '{': depth += 1
            elif src[i] == '}': depth -= 1
            i += 1
        r = re.search(r'reply\s*\(\s*(.)', src[m.end():i])
        if r:
            d[name] = '""' if r.group(1) == '"' else '0'
    return d


def add(src: str) -> tuple:
    dv = defaults(src)
    out, n_ins = [], 0
    for ln in src.split('\n'):
        changed = True
        while changed:
            changed = False
            m = mask(ln)
            for mo in re.finditer(r'\bnow\b\s+[A-Za-z_]\w*\.([A-Za-z_]\w*)\s*\(', m):
                op = m.index('(', mo.end() - 1)
                cp = close_paren(ln, op)
                if cp < 0:
                    continue
                if re.match(r'\s*timeout\b', ln[cp + 1:cp + 20]):
                    continue
                d = dv.get(mo.group(1), '0')
                ln = ln[:cp + 1] + (' timeout %d else %s' % (MS, d)) + ln[cp + 1:]
                n_ins += 1; changed = True; break
        m = mask(ln)
        mo = re.search(r'\bawait\b\s*\(', m)
        if mo and 'timeout' not in m:
            op = m.index('(', mo.end() - 1)
            cp = close_paren(ln, op)
            if cp > 0:
                ln = ln[:cp + 1] + (' timeout %d else 0' % MS) + ln[cp + 1:]
                n_ins += 1
        else:
            mo = re.search(r'\bawait\b\s+([A-Za-z_]\w*)\s*;', m)
            if mo and 'timeout' not in m:
                ln = ln[:mo.end(1)] + (' timeout %d else 0' % MS) + ln[mo.end(1):]
                n_ins += 1
        out.append(ln)
    return '\n'.join(out), n_ins


if __name__ == '__main__':
    total = 0
    for f in sys.argv[1:]:
        s = io.open(f, encoding='utf-8').read()
        t, n = add(s)
        if n:
            io.open(f, 'w', encoding='utf-8').write(t)
            total += n
    print('期限を足した箇所:', total)
