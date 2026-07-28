# ABCL/c+ (AIPL) 型システムと健全性証明レポート

作成日: 2026-05-04  
対象リポジトリ: `https://github.com/yaskodama/abclcp.git`  
対象ブランチ: `make-src-base`  
参照コミット: `fa93ee0 Save current version`

## 概要

本レポートは、`yaskodama/abclcp` の現在実装に基づき、ABCL/c+、別名 AIPL 的に拡張されつつある actor-first 言語の型システムを整理し、その健全性を Coq で検証可能なコア体系として定式化する。実装全体は OCaml による parser、型推論、actor runtime、future/await、AIOS primitive、session protocol runtime から構成される。本レポートでは、実装と乖離しない範囲で、現在の型検査器が実際に保証している性質と、設計文書が意図している将来の型安全性を分けて記述する。

結論を先に述べると、現在の ABCL/c+ 型システムは Hindley-Milner 風の型変数、型スキーム、単一化、primitive overload、actor method signature の事前登録を備えている。一方で、`now` / `future` の戻り値型、`sender`、remote actor、`unsafe send`、session protocol はまだ完全な静的型としては閉じていない。したがって、現在の安全性定理は「静的に検査されるローカル actor send と式評価は well-typed に保たれる」「session protocol は runtime の線形オートマトンとして順序違反を mailbox 投入前に拒否する」という二層構造で述べるのが正確である。

Coq 形式化は [coq/AbclSoundness.v](/Users/kodamay/aios/abclcp/coq/AbclSoundness.v) に追加した。`opam` で導入した The Rocq Prover / Coq compatibility binary 9.1.0 により、`opam exec -- coqc coq/AbclSoundness.v` で機械検査済みである。ファイルは標準ライブラリのみを用いる小さな self-contained な証明として記述している。

## 1. 実装概観

リポジトリの主要構成は以下である。

- `src/ast.ml`: 抽象構文木。式、文、class、method、send target、select case を定義する。
- `src/parser.mly` / `src/lexer.mll`: ABCL/c+ 構文。
- `src/types.ml`: 型、型スキーム、単一化、型変数、class method registry。
- `src/typing_env.ml`: primitive と overload を含む型環境。
- `src/infer.ml`: 型推論・型検査本体。
- `src/eval_thread.ml`: actor runtime、mailbox、future、reply、session protocol runtime。
- `abclc/*.abcl`: サンプルプログラム。
- `docs/AIOS_LANGUAGE_DESIGN.md`: AIOS 言語としての設計方針。

現在の README は、ABCL/c+ を actor-first AI-OS 実装へ成長させる作業 baseline として位置づけている。特に `class` / `new` / `send` モデルを基礎に、kernel service、UI component、web endpoint、model adapter、memory service、tool adapter、agent を actor として統一する方針が示されている。

## 2. 言語コア

現在の AST 上の式は以下の形を持つ。

```text
e ::= n
    | f
    | "s"
    | x
    | e1 op e2
    | f(e1, ..., en)
    | new C(e1, ..., en)
    | [e1, ..., en]
    | now target.m(e1, ..., en)
    | future target.m(e1, ..., en)
    | await e
```

文は以下の形を持つ。

```text
s ::= x = e
    | var x = e
    | f(e1, ..., en)
    | send target.m(e1, ..., en)
    | send! target.m(e1, ..., en)
    | become C(e1, ..., en)
    | if e s1 else s2
    | while e do s
    | { s1 ... sn }
    | select { case m(xs) -> { s } ... timeout n -> { s } }
```

`target` はローカル actor 名または `remote("host:port", "actor")` である。`self` と `sender` は特別な target として parser で扱われる。

class は actor behavior 定義である。

```abcl
class Counter {
  var count = 0;

  method inc() {
    count = count + 1;
    reply(count);
  }
}

var c = new Counter();
send c.inc();
```

## 3. 型

`src/types.ml` の型定義に基づく現在の型集合は以下である。

```text
τ ::= α
    | int
    | float
    | string
    | bool
    | unit
    | any
    | τ[]
    | future τ
    | (τ1 * ... * τn) -> τ
    | actor(C){ m1 : τ1; ...; mn : τn }
    | { l1 : τ1; ...; ln : τn }
```

型変数 `α` は `TVar` として表現され、mutable link により union-find 的に代表型へ束縛される。`repr` は代表元をたどり、経路圧縮を行う。`unify` は型同士を単一化し、関数型の arity、一致しない基底型、occurs check failure を型エラーにする。

`any` は dynamic boundary のための型である。現在は `sender`、`now` の戻り値、`future` の戻り値、remote actor 境界などで使われている。`any` は便利だが、健全性定理では「静的に内容を保証しない境界」として切り分ける必要がある。

## 4. 型スキームと多相性

型スキームは以下の形である。

```text
σ ::= forall α1 ... αn. τ
```

実装では `Forall of int list * ty` で表現される。`generalize` は環境に自由でない型変数を量化し、`instantiate` は量化変数を fresh な型変数へ置き換える。

型環境は名前から型スキームのリストへの写像である。

```text
Γ : name -> scheme list
```

リストになっている理由は primitive overload を扱うためである。例えば `+` は `int * int -> int`、`float * float -> float`、`string * α -> string`、`α * string -> string` を持つ。`pick_overload` は引数型と単一化できる候補を探し、戻り値型を返す。

## 5. Actor 型

actor 型は class 名と method signature の表を持つ。

```text
actor(C) { m1 : τ1; ...; mn : τn }
```

実装では `TActor of string * (string * ty) list` である。ただし、現在の型検査では actor 値そのものに保持された method list だけでなく、global な `class_method_schemes` registry も使われる。`preinfer_all_classes` が program 全体の class を先に走査し、各 method を関数型スキームとして登録する。

現在の method 型は、引数に fresh 型変数を割り当て、戻り値を `unit` とする。

```text
method m(x1, ..., xn) : (α1 * ... * αn) -> unit
```

これは実装上の制約である。runtime では method が `reply(v)` により future を resolve できるため、実行上は値を返すように見える。しかし AST には method return annotation がなく、型検査器は reply の値と method 戻り値を結びつけていない。そのため `now` と `future` の戻り値は現状 `any` / `future any` で近似される。

## 6. 主要な型規則

以下では実装を反映した規則を記す。

### 6.1 変数

```text
x : σ ∈ Γ
instantiate(σ) = τ
----------------
Γ ⊢ x : τ
```

本番の型検査では未束縛変数はエラーである。ただし class method registry を作る preinfer phase では、未束縛変数に fresh 型変数を与えて先に進む。

### 6.2 算術・比較・primitive call

```text
Γ ⊢ e1 : τ1 ... Γ ⊢ en : τn
pick_overload(f, τ1 ... τn) = τ
--------------------------------
Γ ⊢ f(e1, ..., en) : τ
```

演算子も primitive 関数として overload 解決される。文字列連結については `+` の片側が `string` であれば戻り値を `string` とする特別処理がある。

### 6.3 配列

```text
Γ ⊢ e1 : τ
Γ ⊢ ei : τ  for all i
-------------------------
Γ ⊢ [e1, ..., en] : τ[]
```

空配列は現在 `unit[]` として扱われる。

### 6.4 `new`

```text
C.init : (τ1 * ... * τn) -> unit
Γ ⊢ ei : τi
--------------------------------
Γ ⊢ new C(e1, ..., en) : actor(C)
```

`init` が存在しない場合、現在の実装は constructor 引数の検査を省略する。存在する場合は arity と引数型を単一化する。

### 6.5 `send`

ローカル actor への通常 send は次の条件を検査する。

```text
Γ ⊢ target : actor(C)
C.m : (τ1 * ... * τn) -> τr
Γ ⊢ ei : τi
--------------------------------
Γ ⊢ send target.m(e1, ..., en) ok
```

現在の実装では method return は使われず、send 文は `unit` 的な effect とみなされる。検査されるのは target が actor であること、method が存在すること、arity と引数型が合うことである。

`sender` は `any` であるため、`send sender.m(...)` は引数式だけを型推論し、method 存在は静的に検査しない。remote target も dynamic boundary であり、引数式だけを検査する。

### 6.6 `send!`

`send!` は unsafe send である。

```text
Γ ⊢ e1 : τ1 ... Γ ⊢ en : τn
--------------------------------
Γ ⊢ send! target.m(e1, ..., en) ok
```

送信先 actor 型と method 存在は検査しない。これは明示的な escape hatch であり、静的健全性の対象外に置くのが正しい。

### 6.7 `now`

設計上の規則は次である。

```text
Γ ⊢ target : actor(C)
C.m : (τ1 * ... * τn) -> τr
Γ ⊢ ei : τi
--------------------------------
Γ ⊢ now target.m(e1, ..., en) : τr
```

ただし現在の実装では method 戻り値型が AST にないため、`now` は `future` send を生成して即 `await` し、型は `any` になる。

```text
Γ ⊢ now target.m(args) : any
```

これは実装の現在地として明記すべきである。将来、method signature に return type を導入すれば、設計上の規則に移行できる。

### 6.8 `future` と `await`

設計上の規則は次である。

```text
Γ ⊢ target : actor(C)
C.m : (τ1 * ... * τn) -> τr
Γ ⊢ ei : τi
--------------------------------
Γ ⊢ future target.m(e1, ..., en) : future τr

Γ ⊢ e : future τ
----------------
Γ ⊢ await e : τ
```

現在の実装では local target の method 存在と引数型を検査したうえで、戻り値は `future any` とする。

```text
Γ ⊢ future target.m(args) : future any
Γ ⊢ await e : any      if Γ ⊢ e : future any
```

remote future は runtime では未実装で、future を rejected にする。

### 6.9 `become`

```text
C.init : (τ1 * ... * τn) -> unit
Γ ⊢ ei : τi
--------------------------------
Γ ⊢ become C(e1, ..., en) ok
```

現在は切り替え後 protocol compatibility、pending mailbox の message 型との整合性は検査していない。これは actor calculus としては重要な未解決点である。

### 6.10 `select`

```text
Γ, x1:α1, ..., xn:αn ⊢ body ok
--------------------------------
Γ ⊢ case m(x1, ..., xn) -> body ok
```

各 case の束縛変数は fresh 型変数として body 内に導入される。現在は `select` case の method 名と actor の受信 protocol は静的に対応づけられていない。

## 7. セッション型・プロトコル

現在の実装にある「セッション型」は、厳密には静的型ではなく runtime session protocol checker である。`src/eval_thread.ml` では、protocol を actor.method の線形列として定義する。

```text
P ::= a1.m1 -> a2.m2 -> ... -> an.mn
```

サンプル:

```abcl
protocol_define("SolveProtocol",
  "planner.plan -> solver.solve -> reviewer.review");
var sid = protocol_start("SolveProtocol");

var plan = now planner.plan("3 boxes with 4 apples");
var answer_future = future solver.solve(plan);
var answer = await answer_future;
var verdict = now reviewer.review(answer);
protocol_end(sid);
```

runtime は session state として以下を持つ。

```text
sid
protocol definition
position pos
closed flag
```

send の直前に `protocol_check_send` が呼ばれる。現在位置 `pos` の expected step が送信先 actor と method に一致すれば `pos` を 1 進める。一致しなければ例外を投げ、message は mailbox に入らない。

この設計で保証できる性質は以下である。

1. 順序保存: session に属する checked send は protocol 定義の順にしか進まない。
2. 線形消費: 1 回の checked send は protocol position をちょうど 1 進める。
3. 完了後拒否: 全 step 消費後の追加 send は拒否される。
4. 不完全終了拒否: 未消費 step がある状態で `protocol_end` すると失敗する。
5. mailbox 汚染防止: 違反 message は actor の mailbox に入る前に拒否される。

ただし、これは「session 型」としての完全な静的保証ではない。現状では protocol string の構文、actor 名、method 名、send 式との対応は runtime で検査される。将来の静的 session type にするなら、protocol を AST と型環境へ昇格し、send rule に session environment を導入する必要がある。

静的 session type として書くなら、型判断は次の形になる。

```text
Γ ; Δ ⊢ send a.m(args) ▷ Δ'
```

ここで `Δ` は session environment であり、現在 session が期待する next action を保持する。

```text
Δ(sid) = a.m ; P
Γ ⊢ args : params(a.m)
--------------------------------
Γ ; Δ ⊢ send a.m(args) ▷ Δ[sid := P]
```

この形にすれば、「型が通った program は session violation を起こさない」という静的 theorem を述べられる。

## 8. 健全性定理

現在実装をそのまま全て証明対象にすると、remote boundary、`any`、primitive side effect、thread scheduler、mutex、condition variable、external AI call まで含む必要があり、論文の最初の形式化としては大きすぎる。そこで本レポートでは、実装から安全性の核を抽出して二つの theorem を述べる。

### 8.1 式コアの型健全性

対象:

- `nat`
- `string`
- `unit`
- `future τ`
- `+`
- `future value`
- `await`

定理:

```text
Preservation:
  もし Γ ⊢ e : τ かつ e -> e' なら Γ ⊢ e' : τ。

Progress:
  もし ∅ ⊢ e : τ なら、e は値であるか、ある e' が存在して e -> e'。
```

Coq ファイルでは、変数と substitution を省いた closed expression calculus として定式化した。ABCL/c+ 実装の健全性へ拡張する場合は、環境、actor store、mailbox、future table、primitive store を operational semantics に追加する。

### 8.2 セッション protocol checker の健全性

対象:

- protocol は label の list。
- label は actor 名と method 名。
- session position は natural number。
- `send_ok p pos l pos'` は `p[pos] = l` かつ `pos' = pos + 1` のときだけ成り立つ。

定理:

```text
send_ok_unique:
  同じ protocol、position、label に対する次 position は一意。

send_ok_advances_one:
  checked send は position をちょうど 1 進める。

complete_rejects_next:
  pos = length p なら追加 send は存在しない。

wrong_label_rejected:
  現在位置の expected label と異なる label は受理されない。

send_ok_within_protocol:
  accepted send は protocol 範囲内でのみ発生する。
```

これらは `src/eval_thread.ml` の `protocol_check_send` が実装している runtime 検査の数学的核に対応する。

## 9. Coq 形式化

追加した [coq/AbclSoundness.v](/Users/kodamay/aios/abclcp/coq/AbclSoundness.v) は以下を含む。

- `ty`: `TNat`, `TString`, `TUnit`, `TAny`, `TFuture`
- `expr`: `ENat`, `EString`, `EUnit`, `EAdd`, `EFutureValue`, `EAwait`
- `value`
- `has_type`
- `step`
- `preservation`
- `progress`
- session `label`
- `send_ok`
- session protocol の各 theorem

この形式化は現在の実装の「小さな信頼核」であり、論文中では mechanized appendix として扱うのが適切である。完全実装の証明へ進む場合の拡張順序は次である。

1. 変数、環境、代入、substitution lemma を追加する。
2. 関数型と primitive overload の soundness を追加する。
3. actor store と method table を追加する。
4. mailbox と send の small-step semantics を追加する。
5. future table と reply の対応を追加する。
6. session environment を静的型判断へ移す。
7. `any` と remote boundary を gradual typing または dynamic contract として定式化する。

## 10. 現在実装が保証すること

現在の型検査器が強く保証するのは以下である。

- `int`, `float`, `string`, `bool`, `unit`, array, future, actor の基本的な型整合性。
- primitive call の arity と overload 一致。
- arithmetic/comparison の引数型整合性。
- local actor への `send` / `now` / `future` で、target が actor であり、method が存在し、引数個数と引数型が合うこと。
- `await` の対象が `future τ` であること。
- `if` / `while` の条件が `bool` であること。
- `become` の `init` 引数が合うこと。

逆に、現在の型だけでは保証しないものは以下である。

- `reply` の値型と `now` / `future` の戻り値型の一致。
- remote actor の method 存在。
- `sender` の actor 型。
- `send!` の target/method 整合性。
- `select` pattern と actor mailbox protocol の静的整合性。
- `become` 前後の protocol compatibility。
- session protocol の静的遵守。
- deadlock freedom。

これらは欠陥というより、現在の実装が「実用的な actor runtime + 漸進的な型システム」の段階にあることを意味する。論文ではこの境界を明確に書くべきである。

## 11. 論文としての主張

ABCL/c+ の型システムは、actor を第一級単位とする AIOS 言語に必要な三つの安全性を段階的に提供する。

第一に、通常の式と primitive 呼び出しに対して、Hindley-Milner 風の型推論と overload 解決により、基礎的な型不一致を実行前に除去する。

第二に、actor method registry により、ローカル actor message の shape、すなわち method 名、arity、payload 型を静的に検査する。これにより、actor 間通信を単なる文字列 dispatch ではなく、型つき message passing として扱える。

第三に、session protocol runtime により、複数 actor にまたがる message 列の順序を線形に検査する。現在は runtime 検査であるが、Coq で示した線形 automaton の性質により、違反 message は protocol state を進めず、mailbox 投入前に拒否される。

この三層は、AIOS における「型つき actor orchestration」の土台になる。

## 12. 今後の静的セッション型

現在の runtime protocol を静的 session type へ発展させるには、protocol string を parser 上の構文へ移す必要がある。

例:

```abcl
protocol SolveProtocol {
  planner.plan(string) -> string;
  solver.solve(string) -> string;
  reviewer.review(string) -> string;
}
```

このとき型環境には以下を入れる。

```text
Π(SolveProtocol) =
  planner.plan : string -> string ;
  solver.solve : string -> string ;
  reviewer.review : string -> string ;
  end
```

send mode ごとの型規則は次のようになる。

```text
Γ ; Δ(s) = a.m : τ1 * ... * τn -> τr ; P
Γ ⊢ ei : τi
------------------------------------------------
Γ ; Δ ⊢ now a.m(e1, ..., en) : τr ; Δ[s := P]

Γ ; Δ(s) = a.m : τ1 * ... * τn -> τr ; P
Γ ⊢ ei : τi
------------------------------------------------
Γ ; Δ ⊢ future a.m(e1, ..., en) : future τr ; Δ[s := P]

Γ ; Δ(s) = a.m : τ1 * ... * τn -> unit ; P
Γ ⊢ ei : τi
------------------------------------------------
Γ ; Δ ⊢ send a.m(e1, ..., en) ok ; Δ[s := P]
```

この設計なら、次の強い theorem を目標にできる。

```text
Session Preservation:
  well-typed send は session environment を protocol tail へ進める。

Session Progress:
  active session が次 action を持つなら、program はその action を実行するか、
  その action を待つ状態にある。

Protocol Fidelity:
  well-typed closed program の runtime trace は declared protocol の prefix である。
```

特に Protocol Fidelity は AI agent workflow の信頼性に直結する。planner、solver、reviewer、model adapter、memory service の呼び出し順序を型で保証できるためである。

## 13. 制限

本レポートの Coq 証明は、実装全体の full abstraction ではない。証明対象は小さなコア体系であり、OCaml runtime の thread scheduling、mutex、condition variable、network、SDL、AI provider call は含めていない。

また、現在の実装には `any` があるため、完全な「well-typed programs cannot go wrong」はそのままでは主張できない。正確な主張は次である。

```text
well-typed programs do not get stuck inside the statically typed fragment;
dynamic boundaries may fail, but failures are explicit at the boundary.
```

`send!`、remote actor、`sender:any`、`now:any` は、この dynamic boundary に分類される。

## 14. 結論

ABCL/c+ の現在の型システムは、AIOS actor 言語として十分に意味のある基盤を持っている。基底型、多相 primitive、array、future、actor method registry、local send 検査により、message passing の多くを静的に検査できる。runtime session protocol はまだ静的型ではないが、線形 protocol checker として設計されており、Coq で示したような単純な automaton 不変条件に支えられている。

次の研究・実装上の中心課題は、method return type を AST と型検査器に導入し、`reply`、`now`、`future` を同じ戻り値型で結ぶことである。その後、protocol string を型レベルの session environment へ昇格すれば、ABCL/c+ は「actor の局所的型安全性」と「workflow の大域的順序安全性」を同じ型システムで扱える AIOS 言語になる。
