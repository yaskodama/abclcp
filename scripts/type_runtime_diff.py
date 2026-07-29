#!/usr/bin/env python3
"""型検査が付けた戻り値型と、実行時に実際に reply された値の型を突き合わせる。

型検査器が e : int と言っているのに実行時に float が返る、といった
preservation の破れを機械的に見つけるためのハーネス。
実際にこの手のずれが 1 件見つかっている（整数演算が VFloat を返していた）。

使い方（リポジトリのルートから）:

    python3 scripts/type_runtime_diff.py abclc/*.abcl
    python3 scripts/type_runtime_diff.py --verbose docs/samples/reply_inference/s11_service.abcl

仕組み:
  1. 型検査ドライバ tc を走らせ、Class#method -> 型 の表を得る
  2. AIOS_TYPE_TRACE=1 で処理系を走らせ、reply のたびに出る
     [rtype] Class#method = tag を集める
  3. 突き合わせる

判定できないものは失敗にしない。型変数のまま（'a）や any は
「型システムが何も約束していない」ので SKIP、実行中に一度も
reply されなかったメソッドは観測なしで SKIP。

わざと食い違う例（principal type が無いことを示すサンプルなど）には
ソース中に次の行を書いておくと、既知として数え、終了コードを 1 にしない。

    // TYPE_RUNTIME_DIFF: expect-mismatch
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TC_SRC = os.path.join(ROOT, "docs", "samples", "reply_inference", "tc_main.ml")
REPL = os.path.join(ROOT, "src", "abclrepl_thread")

# 静的な型 -> 実行時に許される値タグ
GROUND = {
    "int": {"int"},
    "float": {"float"},
    "string": {"string"},
    "bool": {"bool"},
    "unit": {"unit"},
}

EXPECT_MARK = "TYPE_RUNTIME_DIFF: expect-mismatch"

RET_RE = re.compile(r"^\s+(\S+)#(\S+) -> (.+?)\s*$")
RTYPE_RE = re.compile(r"^\[rtype\]\s+(\S+)#(\S+) = (\S+)\s*$")


def expects_mismatch(abcl):
    """わざと食い違うことを宣言しているサンプルか。"""
    try:
        with open(abcl, encoding="utf-8", errors="replace") as f:
            return EXPECT_MARK in f.read()
    except OSError:
        return False


def build_tc(tc_path):
    """型検査ドライバが無ければ作る。"""
    if os.path.exists(tc_path):
        return True
    src = os.path.join(ROOT, "src")
    cmos = [
        "location.cmo", "types.cmo", "ast.cmo", "typing_env.cmo",
        "infer.cmo", "typecheck.cmo", "parser.cmo", "lexer.cmo",
    ]
    missing = [c for c in cmos if not os.path.exists(os.path.join(src, c))]
    if missing:
        sys.stderr.write(
            "先に `cd src && make thread_repl` を実行してください（%s が無い）\n"
            % ", ".join(missing))
        return False
    cmd = ["ocamlfind", "ocamlc", "-package", "unix", "-thread", "-linkpkg",
           "-w", "-a", "-I", src, "-o", tc_path]
    cmd += [os.path.join(src, c) for c in cmos]
    cmd += [TC_SRC]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write("tc のビルドに失敗しました:\n" + r.stderr + "\n")
        return False
    return True


def static_types(tc_path, abcl, timeout):
    """tc を走らせて {(cls, meth): 型文字列} を返す。型エラーなら None。"""
    try:
        r = subprocess.run([tc_path, abcl], capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    out = r.stdout
    if "[Type error]" in out or "[Parse error]" in out:
        return None
    types, inside = {}, False
    for line in out.splitlines():
        if line.startswith("[method return types"):
            inside = True
            continue
        if inside:
            if line.startswith("["):
                break
            m = RET_RE.match(line)
            if m:
                types[(m.group(1), m.group(2))] = m.group(3)
    return types


def runtime_types(abcl, timeout):
    """処理系を走らせて {(cls, meth): {観測されたタグ}} を返す。"""
    with tempfile.NamedTemporaryFile("w", suffix=".repl", delete=False) as f:
        f.write("load %s\ncompile\n" % abcl)
        repl_script = f.name
    env = dict(os.environ, AIOS_TYPE_TRACE="1", AIOS_QUIET="1")
    try:
        r = subprocess.run([REPL, "-q", "-f", repl_script],
                           capture_output=True, text=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, env=env)
        out = r.stdout
    except subprocess.TimeoutExpired as e:
        # 待ち受けや無限ループでも、そこまでの出力は使う
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
    finally:
        os.unlink(repl_script)
    observed = {}
    for line in out.splitlines():
        m = RTYPE_RE.match(line)
        if m:
            observed.setdefault((m.group(1), m.group(2)), set()).add(m.group(3))
    return observed


def compatible(static, tag):
    """静的な型 static と実行時タグ tag が両立するか。
    None を返したら「判定しない」。"""
    s = static.strip()
    if s == "any" or s.startswith("'"):
        return None                       # 型システムが約束していない
    if s in GROUND:
        return tag in GROUND[s]
    if s.endswith("[]"):
        return tag == "array"
    if s.startswith("future "):
        return tag == "future"
    if s.startswith("actor("):
        return tag == "actor"
    return None                           # 未知の形は判定しない


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--tc", default=os.path.join(ROOT, "tc"))
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args()

    if not build_tc(args.tc):
        return 2
    if not os.path.exists(REPL):
        sys.stderr.write("%s がありません。`cd src && make thread_repl`\n" % REPL)
        return 2

    n_files = n_checked = n_pairs = n_skip_static = 0
    mismatches = []
    expected = []
    unmet_expectations = []

    for abcl in args.files:
        n_files += 1
        st = static_types(args.tc, abcl, args.timeout)
        if st is None:
            if args.verbose:
                print("SKIP (型検査を通らない) %s" % abcl)
            continue
        rt = runtime_types(abcl, args.timeout)
        if not rt:
            if args.verbose:
                print("SKIP (reply が観測されない) %s" % abcl)
            continue
        n_checked += 1
        want_mismatch = expects_mismatch(abcl)
        found_here = 0
        for key, tags in sorted(rt.items()):
            static = st.get(key)
            if static is None:
                continue
            for tag in sorted(tags):
                ok = compatible(static, tag)
                if ok is None:
                    n_skip_static += 1
                    continue
                n_pairs += 1
                if not ok:
                    found_here += 1
                    (expected if want_mismatch else mismatches).append(
                        (abcl, key, static, tag))
                elif args.verbose:
                    print("  ok   %s#%s : %s == %s"
                          % (key[0], key[1], static, tag))
        if want_mismatch and found_here == 0:
            unmet_expectations.append(abcl)

    print("-" * 68)
    print("対象 %d 本 / 突き合わせできた %d 本 / 照合したペア %d 件 "
          "(型変数・any のため判定せず %d 件)"
          % (n_files, n_checked, n_pairs, n_skip_static))
    def show(items):
        for abcl, (cls, meth), static, tag in items:
            print("  %s: %s#%s は型検査では %s だが、実行時は %s を reply した"
                  % (os.path.relpath(abcl, ROOT), cls, meth, static, tag))

    if expected:
        print("\n既知の食い違い %d 件（expect-mismatch 宣言あり）:" % len(expected))
        show(expected)
    if unmet_expectations:
        print("\nexpect-mismatch と書いてあるのに食い違わなかった %d 本:"
              % len(unmet_expectations))
        for abcl in unmet_expectations:
            print("  %s" % os.path.relpath(abcl, ROOT))
        return 1
    if mismatches:
        print("\n食い違い %d 件:" % len(mismatches))
        show(mismatches)
        return 1
    print("想定外の食い違いなし")
    return 0


if __name__ == "__main__":
    sys.exit(main())
