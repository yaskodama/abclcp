# -*- coding: utf-8 -*-
"""paper4 から検証済みの内容を取り出し、第5版として組み直す。
第5版は「経緯」を持たない ---- 現在の仕様と、二つの源流の機能の採否だけを書く。"""
import io, re, sys

SRC = '/Users/kodamay/aios/abclcp/docs/aipl_paper4_ja.tex'
DST = '/Users/kodamay/aios/abclcp/docs/aipl_paper5_ja.tex'
s = io.open(SRC, encoding='utf-8').read()

# ---- 見出しで切り出す ------------------------------------------------
heads = [(m.start(), m.group(1), m.group(2))
         for m in re.finditer(r'\\(section|subsection)\{(.*?)\}\n', s)]
chunks = {}
for i, (pos, lvl, title) in enumerate(heads):
    end = heads[i+1][0] if i+1 < len(heads) else len(s)
    body = s[pos:end]
    # 見出し行を落として本文だけ返す
    chunks[title] = body.split('\n', 1)[1]

def C(title, sub=None):
    """本文を取り出す。sub は (旧, 新) の並び。"""
    if title not in chunks:
        sys.exit('見つからない見出し: ' + title)
    t = chunks[title]
    for a, b in (sub or []):
        if a not in t:
            sys.exit('置換できない: %r in %r' % (a[:50], title))
        t = t.replace(a, b)
    return t.rstrip() + '\n\n'

# 参照の付け替え（章立てが変わったため）
REF = [
  (r'\S\ref{sec:abcl-take}', r'\S\ref{sec:abcl}'),
  (r'\S\ref{sec:abcl-drop}', r'\S\ref{sec:abcl}'),
  (r'\S\ref{sec:koba-take}', r'\S\ref{sec:koba}'),
  (r'\S\ref{sec:koba-drop}', r'\S\ref{sec:koba}'),
  (r'\S\ref{sec:new}',       r'\S\ref{sec:spec}'),
  (r'\S\ref{sec:bg}',        r'\S\ref{sec:intro}'),
]
def R(t):
    for a, b in REF:
        t = t.replace(a, b)
    return t

# 前文（プリアンブル）は paper4 から流用し、表題だけ差し替える
pre = s[:s.index('\\title{')]
pre = pre.replace("""% 型付き AI エージェント言語
% AIPL: Actor based Intelligence Parallel Language — 設計から実現 —（第4版）
%   lualatex -interaction=nonstopmode aipl_paper4_ja.tex   （3回）""",
"""% 型付き AI エージェント言語
% AIPL: Actor based Intelligence Parallel Language — 設計から実現 —（第5版）
%   lualatex -interaction=nonstopmode aipl_paper5_ja.tex   （3回）""")
# become はもう言語に無いので、色づけの語彙からも外す
pre = pre.replace("morekeywords={class,method,var,new,now,future,await,reply,send,become,",
                  "morekeywords={class,method,var,new,now,future,await,reply,send,")

out = [pre]

# =====================================================================
# 表紙とアブストラクト
# =====================================================================
out.append(r"""\title{\bfseries 型付き AI エージェント言語\\[1.5mm]
       \bfseries AIPL: Actor based Intelligence Parallel Language\\[2mm]
       \large --- 設計から実現 ---\\[1mm]
       \normalsize 第 5 版：現在の仕様と、二つの源流からの採否}
\author{児玉靖司\\\small 法政大学経営学部\\\small \texttt{yass@hosei.ac.jp}}
\date{2026 年 8 月 23 日（第 5 版）}

\begin{document}
\maketitle

\begin{abstract}
AI エージェントは、外部のモデルを呼び、他のエージェントを待ち、道具を掴んで放す ---
つまり\textbf{並行で、副作用を持ち、いつ返るか分からない}プログラムである。
にもかかわらず、いま広く使われている書き方には型が無い。
何を待っているのか、何を汚すのか、返らなかったらどうなるのかが、
プログラムの表面に現れない。

本稿は、この隙間を埋めるために作った言語 AIPL（Actor based Intelligence
Parallel Language、処理系名 ABCLc+）の\textbf{現在の仕様}と、
その設計判断をまとめる。
AIPL はアクターを単位とする\textbf{型付き並行言語}であり、
一つのエージェントは一つのアクター、役割どうしのやり取りはメッセージ送信である。

設計は二つの源流から出発している。
\textbf{ABCL/1}（Yonezawa, Briot, Shibayama, OOPSLA 1986）と、
\textbf{小林直樹}らの並行計算のための型システムの系譜である。
本稿は、両者の機構をひとつずつ挙げ、
\textbf{採ったか落としたか・その理由・メリット・デメリット}を、
すべて動く最小プログラムとともに示す。
ABCL/1 からは三種のメッセージ送信・オブジェクト内部の逐次性・\texttt{reply} による返信・
返信先の一級性を採り、\textit{express mode} による割り込みと
\texttt{script} の \texttt{where} ガードを落とした。
小林の系譜からは資源使用解析（効果）・線形型・デッドロック自由な型システム・
サイズ型（粗い代用として期限）を採り、
交差型による高階モデル検査・多相メソッド・完全な所有権型を落とした。

結果として、現在の型システムが押さえるものは七つである。
\textbf{(1)} \textbf{効果} --- \texttt{ai net io mut time mem fs log} の 8 種を
本体から集め、\texttt{now}/\texttt{await} で呼び先から伝播させる。
モデルを呼ぶメソッドは \texttt{ai} を隠せない。
\textbf{(2)} \textbf{期限} --- 待ちには \texttt{timeout} を要求する。
\textbf{(3)} \textbf{失敗の型} --- \texttt{else} を書かない待ちは
\texttt{result}$\langle\tau\rangle$ を返し、確かめずには使えない。
\textbf{(4)} \textbf{返信先の一級性} --- 線形型で「ちょうど一度」を保ったまま委譲できる。
\textbf{(5)} \textbf{資源の順序} --- \texttt{acquire}/\texttt{release} の対に加え、
取得の入れ子から\textbf{全体順序}を読み取り、逆順の取得を止める。
\textbf{(6)} \textbf{義務レベル} --- 待ちの循環を止める。注釈でも書けるし、書かなければ推論される。
\textbf{(7)} \textbf{セッション型} --- 役割どうしのやり取りの順序を静的に照合する。
同期の呼び先は\textbf{展開}するので、セッションがアクターをまたいでも追える。
併せて\textbf{メッシュ配備}を持ち、アクターのソースを他ノードへ送って
相手先で構文解析・型検査してから実体化する。効果注釈がコードと一緒に運ばれる。

\textbf{デッドロック}については、AIPL で待ちが返らなくなる経路が\textbf{四つ}あり、
一つのものとして扱うと答えを誤ることを示す ---
循環待ち、返信されない待ち、\texttt{select} が来ないメッセージを待つ場合、
そして資源を逆順に取る場合である。
四つとも型で押さえた結果、\textbf{待ちの宛先がクラスとして分かるか、
宛先ノードのレベルが宣言されている範囲では、デッドロック自由が型で保証される}。
成立の条件と、依然として残る範囲を明記する。

三役（立案・求解・査読）の AI エージェントを題材に、
型が何を止めるかを実測で示す --- 期限を外すと警告が出て後続の型が合わなくなり、
\texttt{ai} 効果を隠すと弾かれ、役割の順序を入れ替えるとセッション型が弾き、
失敗を確かめずに次へ渡すと型が合わない。
最新仕様の代表的なサンプル 20 本を、コード・出力・メリット・デメリットとともに解説し、
そのうち 18 本が\textbf{三つの独立な処理系で出力一致}することを確認した。
弾かれるべきプログラムは 31 本ある。
\end{abstract}

\tableofcontents
\newpage

% =====================================================================
\section{はじめに}
\label{sec:intro}

""")
def SUB(title, src=None, sub=None, label=None):
    """\subsection を、paper4 の本文を流用して書き出す。"""
    out.append('\\subsection{%s}\n' % title)
    if label: out.append('\\label{%s}\n' % label)
    out.append(R(C(src if src else title, sub)))

def SEC(title, label=None):
    out.append('%% %s\n\\section{%s}\n' % ('='*69, title))
    if label: out.append('\\label{%s}\n' % label)
    out.append('\n')

def TXT(t):
    out.append(t.rstrip() + '\n\n')

SUB('AI エージェントには型が無い')
SUB('二つの世界を混ぜない')

TXT(r"""\subsection{二つの源流}

言語を一から作ってはいない。二つの先行研究から出発している。

\paragraph{ABCL/1（1986）。}
Yonezawa, Briot, Shibayama によるアクター指向の並行オブジェクト言語である。
中核は\textbf{三種のメッセージ送信}（past / now / future）で、
これはそのまま「待たない／待つ／後で受け取る」という区別に対応する。
オブジェクトは一度に一つのメッセージしか処理せず、
\textit{express mode} という割り込み経路と、
\texttt{script} の \texttt{where} ガードによる受理条件を持つ。
ただし\textbf{動的型}であり、型システムを持たない。

\paragraph{小林らの型システム（1997---）。}
ABCL/1 が持たなかった基礎づけを与える系譜である。
$\pi$ 計算に対する線形型、資源使用解析、デッドロック自由な型システム、
サイズ型・精製型、交差型による高階モデル検査などが含まれる。
「通信路をちょうど一度使う」「資源を取ったら放す」「待ちに順序を課す」
といった性質を、実行前に型で言うための道具立てである。

\paragraph{本稿の立場。}
AIPL は、\textbf{ABCL/1 の書き味に小林の型システムを載せる}試みである。
ただし両者をそのまま合わせたのではない。
実際に処理系を三つ書き、582 本のプログラムを通しながら、
機構ごとに採否を決めてきた。
本稿はその\textbf{結果}を、機構ごとの理由・メリット・デメリットとして述べる。

\subsection{本稿の構成}

\S\ref{sec:spec} に AIPL の現在の姿を一望できる形で置く。
\S\ref{sec:abcl} が ABCL/1 の機能の採否、
\S\ref{sec:koba} が小林らの型システムの機能の採否、
\S\ref{sec:orig} がどちらの源流にも無い三つの機構である。
\S\ref{sec:table} に採否の対応表を置く。
\S\ref{sec:dl} がデッドロックの四つの経路とそれぞれの道具、
\S\ref{sec:agent} が\textbf{型付き AI エージェント}を題材にした実測、
\S\ref{sec:samples} が代表的なサンプル 20 本、
\S\ref{sec:impl} が三つの処理系と検証、
\S\ref{sec:discuss} が考察である。

本稿のプログラムはすべて実際に処理系へ通した。
出力は貼り付けたものではなく、実行して得たものである。
""")

# =====================================================================
SEC('AIPL の現在の姿', 'sec:spec')
TXT(r"""採否の議論に入る前に、いまの言語を一望しておく。
以下はすべて現在の仕様であり、実装も三つある（\S\ref{sec:impl}）。

\subsection{アクターとメッセージ}

プログラムは\textbf{クラス}と\textbf{トップレベルの文}からなる。
クラスの実体が\textbf{アクター}で、状態（フィールド）とメソッドを持つ。
アクターは一度に一つのメッセージしか処理しない ---
だから状態を触るのに排他制御を書かない。

送信は三種ある。

\begin{center}
\begin{tabular}{lll}
\toprule
書き方 & 意味 & 返り値 \\
\midrule
\texttt{send a.m(x);} & 送って待たない & 無し \\
\texttt{now a.m(x) timeout $n$ else $e$} & 返信まで待つ & $\tau$ \\
\texttt{now a.m(x) timeout $n$} & 同上（\texttt{else} 無し） & \texttt{result}$\langle\tau\rangle$ \\
\texttt{future a.m(x)} $\to$ \texttt{await $f$} & 後で受け取る & \texttt{future}$\langle\tau\rangle$ \\
\bottomrule
\end{tabular}
\end{center}

返信は \texttt{reply(e)} で行い、\textbf{高々一度}である。
返信先そのものを値として取り出すこともできる（\texttt{replyto}）。

\subsection{型・効果・期限}

型は Hindley--Milner 流に推論する。
メソッドの戻り値型は、書かなければ \texttt{reply} から推論される
（内部的にはメソッドごとに戻り値型変数 $\rho$ を置く）。
書けば、その型が正となり、全経路での \texttt{reply} が課される。

判断は三つ組である。

\[
\Gamma \vdash e : \tau \,!\, \varepsilon
\]

$\varepsilon$ が\textbf{効果}で、次の 8 種からなる。

\begin{center}
\begin{tabular}{ll}
\toprule
効果 & 意味 \\
\midrule
\texttt{ai} & 機外のモデルを呼ぶ \\
\texttt{net} & ネットワークに触る \\
\texttt{io} & 装置に出力する \\
\texttt{mut} & 自分の状態を変える \\
\texttt{time} & 時間を消費する（\texttt{wait}） \\
\texttt{mem} & 永続記憶に触る \\
\texttt{fs} & ファイルに触る \\
\texttt{log} & 記録を残す（\texttt{print}） \\
\bottomrule
\end{tabular}
\end{center}

効果は本体から集められ、\texttt{now} / \texttt{await} で\textbf{呼び先から伝播する}。
注釈 \texttt{!\{...\}} を書けば、本体の効果がそこに収まることが検査される。
書かなければ推論に任せる（gradual）。

待ちには\textbf{期限}を課す。
\texttt{timeout $n$ else $e$} は $n$ ミリ秒待って諦め $e$ を返す。
\texttt{else} を書かなければ \texttt{result}$\langle\tau\rangle$ が返り、
\texttt{is\_ok} / \texttt{value} で確かめないと使えない。

\subsection{七つの規律}

型と効果と期限のうえに、次の七つが載っている。

\begin{center}
\small
\begin{tabular}{p{0.20\textwidth}p{0.34\textwidth}p{0.36\textwidth}}
\toprule
機構 & 書き方 & 止めるもの \\
\midrule
効果 & \texttt{!\{ai, net\}} & 実時間側が機外のモデルを待つこと \\
期限 & \texttt{timeout $n$ else $e$} & 返らない待ち \\
失敗の型 & \texttt{timeout $n$}（\texttt{else} 無し） & 期限切れの値を正常値として流すこと \\
返信先の一級性 & \texttt{replyto} / \texttt{answer} / 引数型 \texttt{reply} & 返信の取りこぼしと二重返信 \\
資源の順序 & \texttt{acquire} / \texttt{release}、\texttt{resource\_order} & 放し忘れ・二重取得・逆順の取得 \\
義務レベル & \texttt{@$n$}（書かなければ推論） & 待ちの循環 \\
セッション型 & \texttt{protocol\_define} / \texttt{\_start} / \texttt{\_end} & やり取りの順序違反 \\
\bottomrule
\end{tabular}
\end{center}

加えて\textbf{メッシュ配備}がある ---
アクターのソースを他ノードへ送り、相手先で構文解析・型検査してから実体化する。
効果注釈がコードと一緒に運ばれ、受け入れ側の方針と照合される。

\subsection{逃げ道}

既定はすべて厳しい側に倒してある。
緩める向きの環境変数を用意しているが、既定で使うことは想定していない。

\begin{term}
AIOS_LAX_WAIT=1        ... 循環待ちを警告に降格
AIOS_LAX_ACTOR=1       ... アクター型を区別しない
AIOS_LAX_ASSIGN=1      ... 未宣言の名前への代入を許す
AIOS_STRICT_DEADLINE=1 ... 期限のない待ちをエラーに昇格
AIOS_STRICT_PROTOCOL=1 ... 追えないセッションのやり残しを警告
AIOS_STRICT_RESOURCE=1 ... 名前がリテラルでない acquire の場所を知らせる
AIOS_SHOW_LEVELS=1     ... 推論した義務レベルと資源の全体順序を見せる
\end{term}
""")

# =====================================================================
SEC('ABCL/1 の機能と、その採否', 'sec:abcl')
TXT(r"""ABCL/1 が持っていた機構をひとつずつ挙げ、
AIPL がそれを採ったか落としたかを、理由・メリット・デメリットとともに述べる。""")

TXT(r"""\subsection{三種のメッセージ送信 ---【採る】}""")
SUB('三種のメッセージ送信', sub=[('\\subsection', '\\subsection')]) if False else None
out.append(R(C('三種のメッセージ送信')))
TXT(r"""\paragraph{採った理由。}
「待たない／待つ／後で受け取る」は、並行プログラムを書くうえで
\textbf{どうしても要る区別}である。
そしてこの三つは型のうえでも別物になる ---
\texttt{send} は値を返さず、\texttt{now} は $\tau$ を返し、
\texttt{future} は \texttt{future}$\langle\tau\rangle$ を返す。
言語が最初から区別しているので、型が後付けにならない。

\textbf{メリット}：待つか待たないかがコードの見た目に出る。
効果の伝播も、待つ送信（\texttt{now}/\texttt{await}）だけを辿ればよい。
\textbf{デメリット}：三つ書き分ける負担がある。
特に \texttt{future} は \texttt{await} と対で書く必要があり、
書き忘れると「送ったが受け取らない」ことになる。""")

TXT(r"""\subsection{オブジェクト内部の逐次性 ---【採る】}""")
out.append(R(C('オブジェクト内部の逐次性')))
TXT(r"""\paragraph{採った理由。}
排他制御を書かずに済むことと、健全性の証明の土台になることの二つである。
\texttt{mut} という効果が意味を持つのも、この前提のうえである ---
「自分の状態を変える」が競合を意味しないのは、一度に一つしか処理しないからである。

\textbf{メリット}：ロックを書かない。データ競合が原理的に起きない。
\textbf{デメリット}：一つのアクターが重い処理をすると、その間そのアクターは止まる。
自分自身への \texttt{now} は原理的に返らない（\S\ref{sec:deadlock}）。""")

TXT(r"""\subsection{\texttt{reply} による返信 ---【採る】}""")
out.append(R(C('返信という考え方')))
TXT(r"""\paragraph{採った理由。}
源流の考え方であり、型付けの問題も解けたからである。
「メソッドの戻り値型」を \texttt{reply} から推論するために、
メソッドごとに戻り値型変数 $\rho$ を置く。
$\rho$ を\textbf{型スキームに含めない}のが要点で、
含めると \texttt{reply} の型と結べなくなる（\S\ref{sec:koba} の多相メソッドの項）。

\textbf{メリット}：戻り値型の注釈が要らない。書けば強い規律になる。
\textbf{デメリット}：単相に限られる。同じメソッドを違う型で使い回せない。""")

TXT(r"""\subsection{返信先の一級性 ---【採る】}
\label{sec:reply1st}

ABCL/1 では \emph{now} 型送信で暗黙に作られる返信先が値であり、他へ渡せる。
つまり「A が受けた依頼に B が代わりに答える」委譲が書ける。
""")
out.append(R(C('返信先を一級の値にする --- 線形型',
   sub=[("""\\S\\ref{sec:abcl-drop} で述べたとおり、ABCL/1 から落とした三つのうち
\\textbf{唯一「型の問題」であった}のが返信先の一級性である。
落とした理由は「ちょうど一度だけ返信する」を構文の走査では守れないことであった。
線形型で取り戻した。""",
        """素朴に値にすると「ちょうど一度だけ返信する」が保てない ---
本体に現れる \\texttt{reply} を構文で数える方式は、
返信先を渡せるようにした途端に無力になる。
\\textbf{線形型}がその答えであった（\\S\\ref{sec:koba}）。""")])))

TXT(r"""\paragraph{採った理由。}
委譲は実際に要る ---- 窓口役が受けて、専門役が直接答える形は、
エージェントでもサービスでも普通に現れる。
そして「ちょうど一度」は線形型で守れる。
落とすべき理由が型の側に無くなった。

\textbf{メリット}：委譲が書けて、なお返信の取りこぼしと二重返信が型で止まる。
\textbf{デメリット}：線形性の検査はメソッド内で閉じている。
返信先を配列に入れて回すような書き方は追えない。

\paragraph{副産物 --- \texttt{self} と \texttt{sender} は値ではない。}
返信先は一級だが、\texttt{self} と \texttt{sender} は
\textbf{送信の宛先としてしか書けない}。

\begin{term}
send self.h(1);          -> OK
send e.take(self, x);    -> PARSE_ERROR
\end{term}

そのため、二者が互いに \texttt{now} で待ち合う循環を、
現在の構文では素直に組み立てられない。
デッドロック自由性はこれとは別に型で保証しているが（\S\ref{sec:dl}）、
\textbf{構文の側でも待ち合いが作りにくい}。
""")

TXT(r"""\subsection{\textit{express mode} による割り込み ---【落とす】}""")
out.append(R(C('express mode による割り込み')))
TXT(r"""\textbf{メリット（落としたことの）}：逐次性が保たれ、健全性の証明が単純なままである。
\texttt{mut} が競合を意味しないという前提も崩れない。
\textbf{デメリット}：緊急停止のような「今すぐ割り込む」記述ができない。
\texttt{select} と期限で近いことは書けるが、
処理中のメッセージを中断することはできない。
""")

TXT(r"""\subsection{\texttt{script} の \texttt{where} ガード ---【落とす】}""")
out.append(R(C('\\texttt{script} の \\texttt{where} ガード')))
TXT(r"""\textbf{メリット（落としたことの）}：進行定理の枝が増えない。
ガードの純粋性という新しい要求も生じない。
受理条件が本体の \texttt{if} として見えるので、読むときに一箇所で済む。
\textbf{デメリット}：「受理しない」が書けない。
在庫が戻るまで待たせたい場合、その待ちはプログラマが書くことになる。
""")

TXT(r"""\subsection{ABCL/1 からの採否 ---- まとめ}

\begin{center}
\small
\begin{tabular}{p{0.22\textwidth}p{0.08\textwidth}p{0.30\textwidth}p{0.30\textwidth}}
\toprule
機構 & 採否 & 主な理由 & 代価 \\
\midrule
三種の送信 & 採る & 設計上必要な区別で、型でも別物 & 書き分けの負担 \\
内部の逐次性 & 採る & 排他制御が要らず、証明の土台になる & 一つのアクターは詰まりうる \\
\texttt{reply} & 採る & $\rho$ で型付けできた & 単相のみ \\
返信先の一級性 & 採る & 委譲が要り、線形型で守れる & 検査はメソッド内で閉じる \\
\addlinespace
\textit{express mode} & 落とす & 逐次性が破れ、証明を書き直す必要 & 割り込みが書けない \\
\texttt{where} ガード & 落とす & 進行定理に枝が増え、純粋性が要る & 「受理しない」が書けない \\
\bottomrule
\end{tabular}
\end{center}
""")

# =====================================================================
SEC('小林らの型システムの機能と、その採否', 'sec:koba')
TXT(r"""小林直樹らの並行計算のための型システムの系譜から、
AIPL が何を採り何を落としたかを、同じ形で述べる。""")

TXT(r"""\subsection{資源使用解析（効果）---【採る】}
\label{sec:eff}
""")
out.append(R(C('効果 --- 資源使用解析の素朴版')))
TXT(r"""\paragraph{採った理由。}
実時間側とエージェント側を分ける\textbf{唯一の手段}だからである。
「このメソッドは機外のモデルを呼ぶ」を型に出さない限り、
実時間で動くアクターが知らずにモデルを待つのを止められない。
本格的な資源使用解析（使用の\textbf{順序}まで追う）ではなく、
\textbf{集合}という素朴な形にしたのは、推論が軽く説明しやすいためである。

\textbf{メリット}：注釈が要らない（推論に任せられる）。
\texttt{now}/\texttt{await} で伝播するので、一段隔てて呼んでも隠せない。
メッシュ配備では、そのまま\textbf{ノード境界の入国審査}になる（\S\ref{sec:mesh}）。
\textbf{デメリット}：集合なので\textbf{順序を表せない}。
「取ったら放す」が言えないので、次項を別に足すことになった。
""")

TXT(r"""\subsection{効果に順序を入れる ---【採る（拡張して）】}""")
out.append(R(C('効果に順序を入れる --- \\texttt{acquire} / \\texttt{release}',
  sub=[("""第 2 版で述べたとおり、効果は\\textbf{順序を持たない集合}であり、""",
        """効果は\\textbf{順序を持たない集合}であり、""")])))
TXT(r"""\paragraph{採った理由。}
効果を集合にした代価をここで払っている。
資源使用解析のいちばん素朴な形 --- 取得と解放の対 --- だけを、
本体の構文を追って検査する。

\textbf{メリット}：デバイスを掴んだまま抜ける経路が静的に消える。
OS を書く目的に直結する。
\textbf{デメリット}：メソッド内で閉じた検査であり、
メソッドをまたぐ受け渡しは見ない。
資源の名前は文字列リテラルに限る。
なお、対の検査だけでは\textbf{逆順の取得}を止められない ---
そのために全体順序を別に入れた（\S\ref{sec:resorder}）。
""")

TXT(r"""\subsection{サイズ型・精製型 ---【粗い代用として採る】}
\label{sec:deadline}
""")
out.append(R(C('期限 --- サイズ型の粗い代用')))
TXT(r"""\paragraph{この形で採った理由。}
「この待ちは有限時間で終わる」を型で言うには、
本来サイズ型や精製型で上界を表す必要がある。
AIPL はそれを\textbf{実行時に打ち切る}ことで代用している ---
上界を証明する代わりに、上界を課す。
機外のモデルを呼ぶ以上、待ち時間の上界を静的に知ることは原理的にできない、
という事情もある。

\textbf{メリット}：書ける。証明が要らない。
そして\textbf{失敗が必ず有限時間で起きる}。
\textbf{デメリット}：\textbf{保証ではない}。
「詰まらない」のではなく「詰まっても諦める」である。
またミリ秒という単位は実時間側には粗すぎる。
""")

TXT(r"""\subsection{失敗を型に出す ---【サイズ型の代用の穴を塞ぐ】}""")
out.append(R(C('失敗を型で表す --- \\texttt{result}$\\langle\\tau\\rangle$',
  sub=[("""第 2 版の考察で、現状の最も弱い箇所として
「期限切れの \\texttt{else} の値が正常値と同じ型である」ことを挙げた。
$-1$ が返ることと、正しく計算できたことを型が区別しない。""",
        """期限で代用すると、新しい穴が開く ---
\\textbf{期限切れの \\texttt{else} の値が正常値と同じ型}になってしまう。
$-1$ が返ることと、正しく計算できたことを型が区別しない。""")])))
TXT(r"""\paragraph{採った理由。}
精製型を入れずに「この値は本当に計算されたのか」を問えるようにする、
いちばん軽い形だからである。

\textbf{メリット}：時間切れの値が正常値のふりをして下流へ流れることが型で止まる。
AI エージェントでは、これがよく効く（\S\ref{sec:agent}）。
\textbf{デメリット}：\texttt{is\_ok} / \texttt{value} を書く手間が増える。
\texttt{else} を書けば従来どおりなので、規律は\textbf{書き手が選ぶ}ことになる。
""")

TXT(r"""\subsection{線形型 ---【採る】}""")
out.append(R(C('線形性の考え方 --- \\texttt{reply} は高々一度',
  sub=[("""ただし実現は\\textbf{構文の走査}であって型ではない。
そのため \\S\\ref{sec:abcl-drop} で述べたとおり、返信先を値にした瞬間に無力になる。""",
        """この二つの実現は\\textbf{構文の走査}である。
返信先を値として渡せるようにした途端、これは無力になる ---
渡された先で何回返されるかは走査では分からない。
そこで返信先そのものには\\textbf{線形型}を与えている
（\\S\\ref{sec:reply1st}）---
\\texttt{reply}$\\langle\\rho\\rangle$ を「ちょうど一度使う」義務として扱い、
使ったか（\\texttt{spent}）と負っているか（\\texttt{owed}）の対で追う。""")])))
TXT(r"""\paragraph{採った理由。}
「ちょうど一度」は返信の要であり、
これが無ければ返信先を一級の値にできない。
逆に言えば、線形型を入れたからこそ ABCL/1 の委譲を取り戻せた。

\textbf{メリット}：委譲が書けて、なお取りこぼしと二重返信が止まる。
\textbf{デメリット}：全面的な線形型ではない。
線形に扱うのは\textbf{返信先だけ}で、通信路一般や資源には及んでいない
（資源の側は \S\ref{sec:resorder} の順序で別に押さえている）。
""")

TXT(r"""\subsection{デッドロック自由な型システム ---【採る】}""")
TXT(r"""通信の依存関係に順序（\textbf{義務レベル}）を入れて循環待ちを型で排除する手法は、
AIPL の課題にそのまま噛み合う。

\paragraph{採った理由。}
期限による代用では\textbf{保証にならない}からである。
「詰まっても諦める」と「詰まらない」は別のことで、
実時間 OS を書く目的には後者が要る。

採るにあたって二つ工夫した。
第一に、レベルは\textbf{書かなくてよい} --- 待ちの辺を見て押し上げる不動点で推論する。
明示注釈は固定点として扱い、動かせなければそこが矛盾である。
第二に、デッドロックを\textbf{一つのものとして扱わなかった}。
調べると経路が四つあり、要る道具が違った（\S\ref{sec:dl}）。

\textbf{メリット}：注釈なしで循環待ちが止まる。
推論したレベルはそのまま\textbf{反例の証人}になる（\texttt{AIOS\_SHOW\_LEVELS=1}）。
ノード境界にも同じ形で課せる（\S\ref{sec:nodelevel}）。
\textbf{デメリット}：宛先がクラスとして分かる範囲でしか効かない。
動的な宛先は見えない。
また粒度が \texttt{Class\#method} なので、
\textbf{同じクラスの別インスタンス}を区別できない。
""")

TXT(r"""\subsection{交差型による高階モデル検査 ---【落とす】}""")
out.append(R(C('交差型による高階モデル検査')))
TXT(r"""\textbf{メリット（落としたことの）}：型検査が決定可能なままである。
エラーが AIPL の言葉（アクター名・メソッド名・行）で出る。
\textbf{デメリット}：借りられたはずの検証力を捨てている。
""")

TXT(r"""\subsection{多相メソッド ---【落とす】}""")
out.append(R(C('多相メソッド')))

TXT(r"""\subsection{完全な所有権の型システム ---【落とす】}""")
out.append(R(C('完全な所有権の型システム')))
TXT(r"""\textbf{メリット（落としたことの）}：借用の注釈を書かずに済む。
\textbf{デメリット}：資源の別名管理が要る場面 ---
たとえば\textbf{資源がアクターの実体}である場合 --- には届かない
（\S\ref{sec:discuss}）。
""")

TXT(r"""\subsection{小林の系譜からの採否 ---- まとめ}

\begin{center}
\small
\begin{tabular}{p{0.22\textwidth}p{0.10\textwidth}p{0.28\textwidth}p{0.30\textwidth}}
\toprule
機構 & 採否 & 主な理由 & 代価 \\
\midrule
資源使用解析（効果） & 採る & 実時間側とエージェント側を分ける唯一の手段 & 集合なので順序を表せない \\
効果の順序 & 採る & 集合にした代価を払う & メソッド内で閉じる \\
サイズ型・精製型 & 代用 & 上界を証明する代わりに課す & 保証ではない \\
線形型 & 採る & 「ちょうど一度」は返信の要 & 返信先だけに限る \\
デッドロック自由な型 & 採る & 代用では保証にならない & 宛先が静的に分かる範囲 \\
\addlinespace
交差型モデル検査 & 落とす & 推論が決定不能。反例が言語の言葉で出ない & 検証力を捨てている \\
多相メソッド & 落とす & $\rho$ をスキームに含めると \texttt{reply} と結べない & 汎用アクターが書けない \\
完全な所有権型 & 落とす & 別名の無さはアクターの性質から既に成立 & 実体ごとの管理に届かない \\
\bottomrule
\end{tabular}
\end{center}
""")

# =====================================================================
SEC('どちらの源流にも無いもの', 'sec:orig')
TXT(r"""三つある。いずれも AIPL の目的 --- 分散 AI エージェントと実時間 OS ---
から要請されたものである。""")

TXT(r"""\subsection{セッション型 ---【採る】}""")
out.append(R(C('やり取りの順序 --- セッション型',
  sub=[("""\\paragraph{誤検出を二度直した。}
最初の実装は 563 本のうち\\textbf{7 本}を落とした。
どれもセッションがアクターをまたぐ例で、
手順の続きは受け手のアクターの中で進んでいた。
そこで、手順が全部この並びに現れる場合だけ「やり残し」を誤りとし、
そうでなければ既定では黙ることにした
（\\texttt{AIOS\\_STRICT\\_PROTOCOL=1} で警告）。

それでも 1 本残った。
手順が \\texttt{"main\\_thread.run"} なのにプログラムは \\texttt{"main"} へ送る、
という\\textbf{綴りの違い}で順序検査が反応していた。
手順に含まれない宛先への送信は、このセッションとは無関係なので見ない。

\\paragraph{結果。}
563 本で新たに落ちるのは\\textbf{1 本だけ}である ---
\\texttt{session\\_protocol\\_violation.aipl}。
名前のとおり、意図的な違反の例題であった。
\\textbf{実行して初めて分かっていたものが、型検査で出るようになった}。

\\begin{finding}
この節の作業は、新しい理論を持ち込む話ではなかった。
\\textbf{実行時にできていたことを、静的にもできるようにした}だけである。
そして二度の誤検出は、どちらも
「静的に見えるものと、実行時に起きることの差」から出た ---
セッションはアクターをまたぐし、宛先の名前は宣言と食い違いうる。
\\S\\ref{sec:select3} の所見と同じ形である ---
\\textbf{言語が世界の全部を見ているわけではない}。
\\end{finding}""",
        """\\paragraph{採った理由。}
「開いてから読み、最後に閉じる」という約束は、
期限でも送り手の存在でも表せない。
そして AIPL には\\textbf{実行時の}セッションプロトコルが既にあった ---
新しい宣言を作る必要が無かった。

\\textbf{メリット}：手順の取り違えが実行前に出る。
実行時の検査と\\textbf{同じ宣言}を使うので、二重に書く必要が無い。
\\textbf{デメリット}：手順は\\textbf{名前}で役を指すので、
名前が静的に解決できる範囲でしか効かない（次項）。""")])))

TXT(r"""\subsubsection*{アクターをまたぐセッション --- 振る舞い展開}""")
out.append(R(C('アクターをまたぐセッション --- 振る舞い展開',
  sub=[("""上の「アクターをまたぐから静的には追えない」は、逃げであった。
数え直すと、セッションを使う 13 本のうち\\textbf{6 本}がまたいでいる ---
つまり\\textbf{半分近くを検査していない}ことになる。
そして 6 本を並べてみると、全部\\textbf{同じ形}をしていた。""",
        """実際のプログラムでは、手順は一つの並びに収まらない。
セッションを使う 13 本のうち\\textbf{6 本}がアクターをまたいでいた。
そして 6 本とも、全部\\textbf{同じ形}をしていた。""")])))

TXT(r"""\subsection{資源への全体順序 ---【採る】}""")
out.append(R(C('資源の取得順序 --- 資源への全体順序')))

TXT(r"""\subsection{メッシュ配備 ---【採る】}
\label{sec:mesh}
""")
out.append(R(C('メッシュ配備 --- ソースを送り、相手先で JIT する')))
TXT(r"""\paragraph{採った理由。}
複数の Xinu ノードでの実行に要るからである。
そして\textbf{効果注釈がそのまま入国審査になる} ---
実時間ノードに \texttt{ai} や \texttt{net} を持つコードは配れない。
言語の側に既にあるものが、そのまま分散の規律になった。

\textbf{メリット}：配るものがソースなので、受け入れ側が\textbf{自分の方針で}検査できる。
効果とレベルがコードと一緒に運ばれる。
\textbf{デメリット}：受け入れ側に処理系が要る。
また輸送は現状ひとつのプロセス内で模しており、実機のノード間転送はこれからである。
""")

# =====================================================================
SEC('採否の対応表', 'sec:table')
TXT(r"""\begin{center}
\small
\begin{longtable}{p{0.20\textwidth}p{0.07\textwidth}p{0.30\textwidth}p{0.33\textwidth}}
\toprule
機構 & 採否 & 理由 & AIPL での姿 \\
\midrule
\endhead
\multicolumn{4}{l}{\textbf{ABCL/1 から}}\\
\midrule
三種の送信 & 採る & 「待たない／待つ／後で」は設計上必要な区別 &
  \texttt{send} / \texttt{now} / \texttt{future}+\texttt{await} \\
内部の逐次性 & 採る & 排他制御を書かずに済む。証明の土台 & 一度に一つ処理 \\
\texttt{reply} による返信 & 採る & 源流の考え方。型付けは $\rho$ で解決 &
  \texttt{reply(e)}、戻り値型は推論または注釈 \\
返信先の一級性 & 採る & 委譲は要る。線形型で「ちょうど一度」を守れる &
  \texttt{replyto} / \texttt{answer} / 引数型 \texttt{reply} \\
\addlinespace
\textit{express mode} & 落とす & 逐次性が破れ、証明を全面的に書き直す必要 &
  無し。\texttt{select}＋期限で近いことのみ \\
\texttt{where} ガード & 落とす & 進行定理に枝が増え、ガードの純粋性が要る &
  \texttt{select} は名前と引数のみ。本体で分岐 \\
\midrule
\multicolumn{4}{l}{\textbf{小林らの型システムから}}\\
\midrule
資源使用解析 & 採る & 実時間側とエージェント側を分ける唯一の手段 &
  8 種の効果集合 \\
効果の順序 & 採る & 集合では「取ったら放す」を表せない &
  \texttt{acquire} / \texttt{release} の対＋全体順序 \\
サイズ型・精製型 & 代用 & 上界を証明する代わりに実行時に打ち切る &
  \texttt{timeout $n$ else $e$}、\texttt{result}$\langle\tau\rangle$ \\
線形型 & 採る & 「ちょうど一度」は返信の要 &
  返信先の線形性検査（\texttt{owed}, \texttt{spent}） \\
デッドロック自由な型 & 採る & 期限による代用は保証にならない &
  義務レベル \texttt{@$n$}（推論。ノード境界にも課す） \\
\addlinespace
交差型モデル検査 & 落とす & 推論が決定不能。反例が言語の言葉で出ない & 無し \\
多相メソッド & 落とす & $\rho$ をスキームに含めると \texttt{reply} と結べない & 単相のみ \\
完全な所有権型 & 落とす & 別名の無さは既に成立 & 無し \\
\midrule
\multicolumn{4}{l}{\textbf{どちらの源流にも無いもの}}\\
\midrule
セッション型 & 採る & 順序の約束は期限でも存在検査でも表せない &
  \texttt{protocol\_define} / \texttt{\_start} / \texttt{\_end}（静的にも読む） \\
資源への全体順序 & 採る & 対の検査では逆順の取得を止められない &
  取得の入れ子から辺を集めて閉路を見る \\
メッシュ配備 & 採る & 複数 Xinu ノードでの実行に要る。
  効果注釈が入国審査になる &
  \texttt{source\_of} / \texttt{node\_allow} / \texttt{deploy} \\
\bottomrule
\end{longtable}
\end{center}

\begin{finding}
表を通して見ると、採否の分かれ目は一つに見える ---
\textbf{反例が AIPL の言葉で出るか}である。
交差型モデル検査を落としたのは検証力が足りないからではなく、
反例が高階再帰スキームの言葉で返るからであった。
逆にデッドロック自由な型を採れたのは、
推論したレベルがそのまま\textbf{「どのメソッドが何を待って詰まるか」}
という形の証人になったからである。
型システムの価値は、通す力ではなく\textbf{落とし方}にある。
\end{finding}
""")

# =====================================================================
SEC('デッドロック --- 四つの経路と、それぞれの道具', 'sec:dl')
TXT(r"""エージェントが止まる、というのはひとつの現象に見える。
実際には、\textbf{ひとつのものとして扱うと答えを誤る}。
待ちが返らなくなる形は四つあり、要る道具が違う。""")

TXT(r"""\subsection{循環待ちの静的検査}
\label{sec:deadlock}
""")
out.append(R(C('循環待ちの静的検査',
  sub=[("""四つの機構を入れる過程で、副産物が一つ出た。
効果の伝播に使っている辺（待つ側 $\\to$ 待たれる側）が、""",
        """まず、いちばん安く手に入るものから見る。
効果の伝播に使っている辺（待つ側 $\\to$ 待たれる側）が、""")])))

TXT(r"""\subsection{四つの経路}
\label{sec:dl3}
""")
out.append(R(C('四つの経路',
  sub=[("""「型でデッドロック自由を保証できるか」を調べる過程で数えたところ、
AIPL で待ちが返らなくなる経路は\\textbf{四つ}あった。
最初に見えたのは三つで、四つ目 --- 資源の取得順序 --- は
\\S\\ref{sec:res} の対の検査を入れたあとに残っていることが分かった。""",
        """AIPL で待ちが返らなくなる経路は\\textbf{四つ}ある。
うち三つは待ちの形をしているが、四つ目はしていない。""")])))

TXT(r"""\subsection{四つとも型で押さえる}
""")
out.append(R(C('四つとも型で押さえる')))
TXT(r"""\subsection{「保証できる」と言うための条件}
""")
out.append(R(C('「保証できる」と言うための条件',
  sub=[("""二つを入れた現在でも、\\textbf{全言語について}デッドロック自由が言えるわけではない。
条件を明記しておく。""",
        """それでも、\\textbf{全言語について}デッドロック自由が言えるわけではない。
条件を明記しておく。""")])))

TXT(r"""\subsection{経路 3 --- \texttt{select} の待ち}
\label{sec:select3}
""")
out.append(R(C('経路 3 --- \\texttt{select} の待ち')))

TXT(r"""\subsection{ノードをまたぐ待ち}
\label{sec:nodelevel}
""")
out.append(R(C('ノードをまたぐ待ち')))

# =====================================================================
SEC('型付き AI エージェントを書く', 'sec:agent')
TXT(r"""ここまでの機構は、それぞれ別の動機から入れたものである。
本節では、それらを\textbf{一つのプログラムの上で}働かせてみる ---
立案・求解・査読の三役からなる、ごく普通の AI エージェントである。""")
SUB('三役のパイプライン')
SUB('何が止まるか --- 四つとも壊してみた')
SUB('実物の corpus はどうだったか')
SUB('見えないところ')

# =====================================================================
SEC('代表的なサンプルプログラム', 'sec:samples')
TXT(r"""最新仕様の代表として 20 本を挙げる。
出力はすべて実行して得たものであり、
うち 18 本は\textbf{三つの処理系すべてで一致する}ことを確認している（\S\ref{sec:impl}）。
残る 2 本（\texttt{s11}・\texttt{s16}）は出力にノード名を含むため自動比較から外し、
内容を目視で照合した。
各サンプルに\textbf{示すもの・メリット・デメリット}を付す。""")

SAMPLES = [
 's01 --- アクターの基本', 's02 --- 三種の送信', 's03 --- \\texttt{reply} の規律',
 's04 --- 効果', 's05 --- 期限', 's06 --- 実時間側の防壁', 's07 --- \\texttt{select}',
 's08 --- 状態機械（\\texttt{become} を使わずに書く）', 's09 --- アクターを引数に渡す',
 's10 --- 三段のパイプライン', 's11 --- メッシュへの配備', 's12 --- 失敗を型で表す',
 's13 --- 資源の取得と解放', 's14 --- 返信先の委譲', 's15 --- 義務レベル',
 's16 --- ノードをまたぐ義務レベル', 's17 --- \\texttt{select} の規律',
 's18 --- セッション型', 's19 --- 資源への全体順序', 's20 --- アクターをまたぐセッション',
]
for t in SAMPLES:
    title = t
    subs = None
    if t.startswith('s08'):
        title = 's08 --- 状態機械'
        subs = [("""\\textbf{示すもの}：\\S\\ref{sec:become} で \\texttt{become} を外したあとの書き方。""",
                 """\\textbf{示すもの}：振る舞いの差し替えを、状態フィールドと分岐で書く。""")]
    out.append('\\subsection{%s}\n' % title)
    out.append(R(C(t, subs)))

SUB('20 本を通して見えること')

# =====================================================================
SEC('三つの処理系と、揃っていることの確かめ方', 'sec:impl')
TXT(r"""AIPL には実装が三つある --- 正となる OCaml 版（手書き 8,023 行）、
Python の CLI 実装（15,101 行）、ブラウザで動く JavaScript 実装（6,331 行）である。
三つ作る理由は二つある。
JS 版はブラウザで動くので処理系を配らずに試してもらえること、
そして\textbf{三つ揃えること自体が仕様の検査になる}ことである。

確かめ方は二本立てである。
\texttt{run\_all\_impls.sh} が\textbf{通るプログラムの出力が一致するか}を見て、
\texttt{run\_reject\_tests.sh} が\textbf{通ってはいけないプログラムが止まるか}を見る。
後者は\textbf{31 本}の「弾かれるべきプログラム」からなる。
前者だけでは足りない ---
検査が丸ごと抜け落ちていても、正しいプログラムの出力は一致するからである。

\subsection{現在の状態}

サンプル 20 本のうち\textbf{18 本が三実装で出力一致}する
（\texttt{s11} と \texttt{s16} は出力にノード名 \texttt{rt0/servo1} を含み、
比較スクリプトが区切りに使う \texttt{/} で割れてしまうため自動比較から外した。
内容は目視で一致を確認している）。
ガイドの 8 本も一致する。
弾かれるべき 31 本については、93 枠のうち\textbf{10 枠}が期待と食い違い、
その内訳は JS 版 7・Py 版 3 である
（\textbf{OCaml 版は 31 本すべてで期待どおりに振る舞う}）。
残りはいずれも「OCaml 版にはあるが他の実装に無い検査」であり、
言語仕様の穴ではなく追随の遅れである。

\subsection{仕様を変えるときの手順}

機構を一つ足すとき、次の順で進めている。

\begin{enumerate}
\item 最小の再現プログラムを書き、\textbf{実際の処理系に通す}。
\item 582 本の \texttt{.aipl} 全体に対する影響を測る ---
      \textbf{採用の前に}、何本が新たに落ちるかを数える。
\item その例を「弾かれるべきプログラム」として恒久的に登録する。
\item 三実装すべてに移植し、出力一致と拒否表を取り直す。
\end{enumerate}

第 2 段が要点である。
たとえば資源への全体順序は 582 本で新たに落ちるものが 0 本、
アクターをまたぐセッションの検査は旧版の型検査器と一件ずつ突き合わせて
判定の変わったファイルが 0 本であった。
\textbf{「厳しくしたが既存を壊していない」を数で言えるようにしておく}。

\begin{finding}
「三実装が揃っている」という主張は、
\textbf{正しいプログラムの出力について}しか成り立っていなかった。
「弾かれるべきプログラム」の側を作って初めて、
実装間の食い違いが見えるようになった ---
最初に表を取ったとき、11 枠が食い違っていた。
検査は、通す側からは見えない。
\end{finding}

\subsection{機械検証との距離}

正直に書いておくべきことがある。
機械検証（Coq/Rocq、\texttt{AIPLSoundness.v}、1121 行、\texttt{Print Assumptions} が公理なし）が
済んでいるのは、\textbf{効果も期限も持たない中核} $\mathrm{AIPL}^{-}$ である ---
保存定理・進行定理・型安全性・\texttt{method not understood} の不在・
非同期送信のデッドロック自由性が示されている。
効果と期限を加えた $\mathrm{AIPL}^{-2}$ 以降は紙の上の証明であり、
本稿の七つの規律は機械検証されていない。
\textbf{実装と機械検証の距離は、縮まるどころか広がっている}。

これは望ましくないが、避けがたくもある。
機構を足すたびに形式化を追いかけると、
「実装が何をしているか」を確かめる速度が落ちる。
現状は、\textbf{機械検証の代わりに「弾かれるべきプログラム」31 本}が
実装の規律を押さえている。
これは証明ではないが、\textbf{三つの実装すべてに同じ問いを投げられる}という利点がある ---
証明は一つのモデルについてしか言えない。
""")

# =====================================================================
SEC('考察', 'sec:discuss')

TXT(r"""\subsection{採否の判断は一貫していたか}

表（\S\ref{sec:table}）を通して見ると、判断の軸は三つに整理できる。

\paragraph{軸 1 --- 反例が AIPL の言葉で出るか。}
交差型による高階モデル検査を落としたのは、検証力が足りないからではない。
反例が高階再帰スキームの言葉で返り、
「どのアクターがどのメッセージで詰まるか」にならないからである。
逆に義務レベルを採れたのは、推論したレベルがそのまま
「\texttt{Ctl2\#go (@7)} が \texttt{@1} を待っている」という形の証人になったからである。

\paragraph{軸 2 --- 証明の構造を壊さないか。}
\textit{express mode} と \texttt{where} ガードは、
どちらも\textbf{進行定理に枝を増やす}という一点で落としている。
逐次性が破れれば \texttt{mut} の意味が変わり、
ガードが増えれば「受理できるメッセージが無い」構成を扱う必要が出る。
機能の魅力ではなく、土台への影響で決めている。

\paragraph{軸 3 --- 実際に書かれているか。}
判断を数で決めた場面がいくつかある ---
「名前が動的な \texttt{acquire}」を課題から外したのは、
582 本を測って\textbf{一件も無かった}からである。
逆にアクターをまたぐセッションを追いかけたのは、
セッションを使う 13 本のうち\textbf{6 本}がまたいでいたからである。
\textbf{仕様の穴は、大きさではなく踏まれ方で優先順位が決まる}。

\subsection{型・効果・期限という三点セットの評価}

三つの仕組みの効き方には差がある。

\textbf{型}は最もよく効いている。
\texttt{reply} の規律とアクター型の区別は、書き間違いの多くをその場で止める。
代価は判定の保守性で、正しいのに拒否される場合がある。

\textbf{効果}は、効くときは非常に効くが\textbf{注釈依存}である。
書かなければ推論されるだけで、誤りは通る。
これは「効果を書かないと損をする」仕組みが無いためで、
たとえば公開するアクターには注釈を義務づけるといった運用が要る。
一方、メッシュ配備では \texttt{node\_allow} が\textbf{注釈を要求する側}に回るので、
国境をまたぐコードについては強制が効く。

\textbf{期限}は最も安上がりに強い性質を与える。
構文を一つ足すだけで進行定理の枝が消える。
ただしこれは失敗を消すのではなく\textbf{失敗の形を変える}だけである。
\texttt{result}$\langle\tau\rangle$ を入れて「変わった形の失敗」を型に出せるようにしたが、
\texttt{else} を書けば従来どおりなので、規律は書き手が選ぶことになる。

\subsection{足した機構に共通していたこと}

七つの規律のうち、後から足した四つ ---
義務レベル・\texttt{select} の規律・セッション型・資源への全体順序 ---
には、共通する性質があった。
\textbf{どれも新しい注釈を作っていない}。

\begin{itemize}
\item 義務レベルは、\textbf{待ちの辺}を読んだ（効果の伝播に使う辺がそのまま使えた）。
\item セッション型は、\textbf{実行時に既にあった宣言}を読んだ。
\item 資源への全体順序は、\textbf{取得の入れ子}を読んだ
      （$r$ を持ったまま $s$ を取ったなら $r < s$）。
\item \texttt{select} の規律は、\textbf{他の場所にある送信}を読んだ。
\end{itemize}

必要な情報は、たいていプログラムの中に既に書かれている。
型システムの仕事は、書かせることより\textbf{読み取ること}であった。

\begin{finding}
「アクターをまたぐから静的には追えない」という判断も、
実は\textbf{型の限界ではなく検査の範囲の狭さ}だった。
必要だったのは多者間セッション型でも委譲でもなく、
同期の呼び先の送信列を差し込むことと、名前の解決表である。
プログラムは一行も変えていない。

そして限界は、予想していたところ（またぐこと）ではなく\textbf{名前}に現れた ---
実行時はフィールドのアクターを持ち主で修飾した名前（\texttt{c\#f}）で呼ぶが、
静的な側はクラスの実体を一つに決められない。
\end{finding}

\subsection{「正」の実装という考え方の限界}

OCaml 版を「正」と決めているが、これは\textbf{どちらが正しいかを決める手続き}ではない。
三実装を突き合わせて食い違いが出たとき、
OCaml 版が正しいとは限らない ---
実際、突き合わせで見つかった実装のバグのうち、
半分以上が\textbf{正であるはずの OCaml 版}のものであった。
「正」は\textbf{仕様の置き場所}であって、正しさの根拠ではない。

根拠になるのは、\textbf{同じ問いを三つに投げられること}である。
機械検証は一つのモデルについてしか言えないが、
「弾かれるべきプログラム」は三つ全部に投げられる。

\subsection{残っている課題}

\begin{enumerate}
\item \textbf{非同期の呼び先をまたぐセッション}。
      \S\ref{sec:crosssession} の展開は同期の呼び先しか差し込めない。
      \texttt{send} / \texttt{future} の先で手順が進む場合は、
      順序が決まらないので実行時に任せている。
      多者間セッション型と委譲（線形な \texttt{session}$\langle S\rangle$ を
      引数で引き回す）に進めば追えるが、プログラムの書き換えが要る。
\item \textbf{フィールドに持ったアクターは役になれない}。
      実行時は持ち主で修飾した名前で呼ぶが、
      静的な側はクラスの実体を一つに決められない。
      手順が名前で役を指す設計そのものに由来する。
\item \textbf{資源がアクターの実体であるときの順序}。
      \S\ref{sec:resorder} の順序は\textbf{資源の名前}についてのものである。
      食事する哲学者のように資源が\textbf{同じクラスの別インスタンス}
      （\texttt{lo} / \texttt{hi}）である場合、
      義務レベルの粒度が \texttt{Class\#method} なので区別できない。
      実体ごとの順序には精緻化型 $\{i:\mathtt{int} \mid i < j\}$ か、
      フィールドによる順序宣言が要る。
\item \textbf{モデルの出力の形は型の外にある}。
      「査読役は OK か NG を返す」はプロンプトにしか書かれていない。
      効果と期限が押さえるのは\textbf{呼び出しの外側}である。
\item \textbf{モデルの mock が三実装で違う}。
      そのためモデルを呼ぶプログラムは型検査でしか突き合わせられない。
\item \textbf{メソッド内で起きた失敗の伝わり方}。
      呼び出し側の \texttt{now ... timeout ... else} が何を返すかが
      三実装で違う。\texttt{result}$\langle\tau\rangle$ に載せる道と揃える必要がある。
\item \textbf{$\mathrm{AIPL}^{-2}$ 以降の機械検証}。
      効果つき判断、期限、\texttt{future}$\langle\tau\,!\,\varepsilon\rangle$、
      そして七つの規律。
\item \textbf{実機のメッシュへの接続}。
      配備の輸送は現状ひとつのプロセス内で模している。
      Xinu ノード間の実際の転送に差し替える。
\end{enumerate}
""")

# =====================================================================
SEC('おわりに')
TXT(r"""本稿は AIPL の現在の仕様と、二つの源流からの採否をまとめた。

ABCL/1 からは\textbf{三種の送信・内部の逐次性・\texttt{reply}・返信先の一級性}を採り、
\textit{express mode} と \texttt{where} ガードを落とした。
落とした二つは、どちらも\textbf{進行定理に枝を増やす}という一点で共通している。

小林らの型システムからは\textbf{資源使用解析（効果）・効果の順序・線形型・
デッドロック自由な型}を採り、サイズ型は\textbf{期限という粗い代用}に置き換えた。
交差型モデル検査・多相メソッド・完全な所有権型は落とした。
落とした三つは、\textbf{反例が言語の言葉で出ない}か、
\textbf{$\rho$ による \texttt{reply} の推論と両立しない}か、
\textbf{アクターの性質から既に成立している}かのいずれかである。

どちらの源流にも無いものとして、\textbf{セッション型・資源への全体順序・
メッシュ配備}を足した。

結果として、\textbf{待ちの宛先がクラスとして分かるか、
宛先ノードのレベルが宣言されている範囲では、デッドロック自由が型で保証される}。
その外側では、期限が失敗を有限時間に変換する。

\paragraph{分かったこと。}
AI エージェントを型で書くために、\textbf{新しい理論は要らなかった}。
1986 年の ABCL/1 と、1997 年以降の小林らの型システムと、
セッション型という三十年ぶんの蓄積が、そのまま当たる問題であった。
足りていなかったのは理論ではなく、
それらを\textbf{一つの言語に同時に載せること}である。

そして載せる作業を通して見えたのは、
\textbf{必要な情報はたいていプログラムの中に既に書かれている}ということであった ---
待ちの辺、取得の入れ子、実行時の宣言、他の場所にある送信。
後から足した規律は、どれも新しい注釈を作らずに済んだ。

\paragraph{仕様は、書くだけでは検査されない。}
走らせて、複数の実装で走らせて、そして\textbf{実際に使われているかを数えて}、
初めて検査される。

\subsection*{再現方法}

\begin{term}
# 本稿の20本を流す
cd ~/aios/abclcp
for f in docs/samples/paper/s*.aipl; do
  printf 'load %s\ncompile\n' "$PWD/$f" > /tmp/s.repl
  ./src/abclrepl_thread -q -f /tmp/s.repl
done

# 通るプログラムの出力一致 / 弾かれるべき31本の拒否（三実装）
sh tools/run_all_impls.sh
sh tools/run_reject_tests.sh
\end{term}
""")

# ---- 参考文献はそのまま流用 -----------------------------------------
bib = s[s.index('\\begin{thebibliography}'):]
out.append('% ' + '='*69 + '\n')
out.append(bib)

io.open(DST, 'w', encoding='utf-8').write(''.join(out))
print('書き出した:', DST)
