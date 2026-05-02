# ABCL/c+- as a Typed AIOS Language

作成日: 2026-05-02

この文書は、ABCL/c+- を AIOS の中核言語として育てるための設計方針をまとめる。現時点では実装を大きく変えず、`make-src-base` の `src/Makefile` でビルドできる系を基準に、段階的に「型つき AIOS」へ移行する。

## 1. Vision

ABCL/c+- は、actor を第一級の実行単位とする型つき AIOS 記述言語である。

AIOS 上の以下のものをすべて actor として扱う。

- OS service
- UI component
- device interface
- web endpoint
- background task
- AI agent
- memory service
- model/tool adapter

actor 同士は message で接続し、message の形を型で検査する。状態は actor 内に閉じ、外部から直接変更しない。

## 2. Design Principles

### Actor First

AIOS の実行単位は actor とする。

`class` は actor の behavior 定義であり、`new` は actor instance の生成である。

### Message Typed

actor 間通信は `send target.method(args)` を基本にする。送信先 actor が持つ method と引数型を、可能な限り静的に検査する。

### State Isolated

actor のフィールドは actor 内部状態である。外部 actor は message を通してのみ操作する。

### Capability Explicit

外部資源へのアクセスは capability として明示する。

例:

- Time
- Console
- UI/SDL
- Web
- Network
- File
- Model
- Memory
- Tool

### Small Core, Rich Runtime

言語コアは小さく保つ。AIOS 固有機能は primitive と actor library として増やす。

### Dynamic Boundary

remote actor、AI model、JSON、外部 tool のように完全静的化が難しい領域は dynamic boundary として扱う。ただし boundary は型や capability で明示する。

## 3. Current Core

現在の実装で確認できる中核構文は以下である。

```abcl
class Counter {
  var count = 0.;

  method inc() {
    count = count + 1.;
    print(count);
  }
}

var c = new Counter();
send c.inc();
```

主な構成:

- `class`
- `method`
- `var`
- `new`
- `send`
- `send!`
- `become`
- `select`
- `remote`
- primitive call

この構文を大きく壊さず、型と runtime の意味を整理して AIOS 化する。

## 4. Execution Model

### Actor

actor は以下を持つ。

- actor name
- class/behavior name
- mailbox
- local environment
- method table
- current sender
- lifecycle state

最小 lifecycle:

- `created`
- `initializing`
- `running`
- `suspended`
- `stopped`

### Message

message は以下の構造を持つ。

```text
from actor
to actor
method name
arguments
optional message id
optional session id
```

現在の `Eval_thread.mmessage` を基礎に、AIOS 用の message metadata を追加していく。

### Scheduler

当面は現在の thread + mailbox 実装を使う。将来は scheduler を抽象化する。

候補:

- thread per actor
- cooperative scheduler
- event loop
- distributed actor scheduler

最初は互換性重視で thread per actor を維持する。

## 5. Type System

### Base Types

最小型:

```text
int
float
string
bool
unit
any
```

複合型:

```text
t[]
(t1 * t2 * ... * tn) -> r
actor(C)
record
```

### Actor Type

actor 型は method signature を含む。

```text
actor(Counter) {
  inc : () -> unit;
  dec : (float) -> unit;
}
```

現在の `TActor of string * (string * ty) list` を基礎にする。

### Method Type

method は原則として `params -> unit` とする。

`reply` を使う request/reply 型は次段階で導入する。

将来案:

```text
ask : (string) -> reply string
```

ただし最初は `reply` は effectful primitive として扱う。

### `self`

`self` は現在の class の actor 型を持つ。

```text
self : actor(CurrentClass)
```

### `sender`

初期実装では `sender : any` とする。

次段階で reply channel 型または sender actor 型へ拡張する。

候補:

```text
sender : actor(?)
sender : reply_to(t)
```

### `send`

ローカル actor への `send` は以下を検査する。

1. target が actor 型である。
2. method が存在する。
3. 引数個数が一致する。
4. 引数型が一致する。

remote actor への `send` は当面 dynamic boundary とする。

通常の `send` は fire-and-forget の非同期 message とする。

```text
send target.method(args) : unit
```

つまり、message を mailbox に投入できれば呼び出し側は継続する。method の計算結果は直接返さない。結果が必要な場合は `reply`、または後述の `future` 型を使う。

### `now` Send

`now` は同期的な即時 message send とする。

目的:

- actor を通常の関数呼び出しに近い形で使う。
- actor 内部 service を型つきで直接問い合わせる。
- AIOS kernel 内の短い問い合わせを明示的に同期実行する。

構文案:

```abcl
var y = now calc.add(1., 2.);
```

型規則:

```text
target : actor(C)
C.add : (float * float) -> float
--------------------------------
now target.add(1., 2.) : float
```

`now` は method の戻り値型を持つ。したがって、AIOS 言語として method signature に戻り値型を導入する必要がある。

初期互換方針:

- 既存 method は戻り値なし、つまり `unit` とみなす。
- `now` で戻り値なし method を呼ぶ場合、型は `unit`。
- actor の mailbox を経由せずに直接実行するか、mailbox に優先投入して完了を待つかは runtime policy とする。

安全性の注意:

- `now` は deadlock を起こし得る。
- actor A が actor B に `now` し、B が A に `now` すると停止する可能性がある。
- そのため、`now` は kernel service や pure/read-only service に限定する capability policy を検討する。

設計上は、`now` は「同期境界」を明示する型つき send である。

実装メモ:

- 2026-05-02 時点で、最小実装として `now target.method(args)` は利用可能。
- 現在は method 戻り値型が AST に無いため、型検査上の戻り値は `any` として扱う。
- runtime では `future` message を作成して即 `await` する。
- 呼び出し先 method は `reply(value)` で結果を返す。

### `future` Send

`future` は結果を後で受け取る非同期 message send とする。

目的:

- AI model call や network call のような遅い処理を非同期に扱う。
- fire-and-forget ではなく、結果型を保持したまま処理を継続する。
- 複数 actor への問い合わせを並列化する。

構文案:

```abcl
var f = future calc.add(1., 2.);
var x = await f;
```

型規則:

```text
target : actor(C)
C.add : (float * float) -> float
--------------------------------
future target.add(1., 2.) : future float

f : future float
----------------
await f : float
```

future 型:

```text
future t
```

future の状態:

- `pending`
- `resolved(value)`
- `rejected(error)`
- `cancelled`

最小 primitive 案:

```text
await     : future t -> t
poll      : future t -> option t
cancel    : future t -> unit
is_done   : future t -> bool
```

初期実装では `await` のみでもよい。

`future` は現在の `reply` / `msg_id` / session log の仕組みと相性がよい。runtime では message id と future object を対応づけ、reply が来たら future を resolve する。

実装メモ:

- 2026-05-02 時点で、最小実装として `future target.method(args)` と `await f` は利用可能。
- 型は `future any` として扱う。
- `reply(value)` が対応する future を resolve する。
- remote future send はまだ未実装で、ローカル actor を対象にする。

### Send Modes

message send は3種類に整理する。

```text
send   target.method(args) : unit
now    target.method(args) : result_type
future target.method(args) : future result_type
```

意味:

- `send`: 非同期、結果を待たない。
- `now`: 同期、結果を待つ。
- `future`: 非同期、結果 handle を返す。

型システム上は、method signature が戻り値型を持つ必要がある。

```text
method add(float, float) : float
method inc() : unit
```

既存構文との互換性のため、戻り値注釈がない method は `unit` とする。

### `send!`

`send!` は unsafe/dynamic send として扱う。

型検査は引数式の well-typedness までに留め、送信先 method の存在は検査しない。

### `become`

`become C(args)` は actor の behavior を `C` に切り替える。

型規則:

1. `C` が存在する。
2. `C.init` がある場合、引数型と個数を検査する。
3. 切り替え後の method table は `C` のものになる。

未解決課題:

- 現在 actor が公開していた protocol と切り替え後 protocol の互換性。
- pending messages に対する型安全性。

最初は runtime behavior として維持し、protocol compatibility は後で扱う。

### `select`

`select` は mailbox から pattern に合う message を受ける構文と位置づける。

型規則:

- case pattern の変数は case body 内で fresh 型変数として束縛する。
- timeout body は通常 statement として検査する。

将来は actor の受信 protocol と対応させる。

## 6. Capability Model

現在の primitive を capability 別に分類する。

### Core

- arithmetic operators
- comparison operators
- `typeof`
- array primitives

### Console

- `print`
- `reply`

### Time

- `wait`

### Actor

- `spawn`
- `send`
- `become`
- `select`

### UI

- `sdl_init`
- `sdl_clear`
- `sdl_line`
- `sdl_erase_line`
- `sdl_present`

### Web

- `web_listen`
- `web_expose`

### AI

今後追加する。

候補:

- `model_call`
- `embed`
- `tool_call`
- `memory_get`
- `memory_put`
- `observe`
- `plan`
- `act`

最初は primitive として追加せず、AI service actor として表現する方針を優先する。

例:

```abcl
class Assistant {
  method ask(prompt) {
    send model.generate(prompt);
  }
}
```

## 7. AIOS Runtime

`eval_thread.ml` の actor runtime を AIOS kernel の原型とみなす。

AIOS kernel が持つべき機能:

- actor registry
- class registry
- mailbox management
- scheduler
- primitive capability registry
- log/event stream
- session management
- web gateway
- remote actor gateway

現在の実装との対応:

- `actor_table` -> actor registry
- `class_env` -> class registry
- `add_prim` -> capability registry
- actor logs / web logs -> event stream
- `web_gateway.ml` -> HTTP/WebSocket gateway

## 8. Remote and Distributed AIOS

`remote(host, actor)` は分散 actor への入口である。

初期方針:

- remote send は静的 method 検査を行わない。
- 引数式だけ型検査する。
- runtime で配送失敗を扱う。

次段階:

```abcl
interface Calculator {
  method add(a: float, b: float);
}

var calc = remote Calculator("localhost:8080", "calc");
send calc.add(1., 2.);
```

interface 導入までは dynamic boundary とする。

## 9. AI Agent Model

AI agent も actor として扱う。

agent 専用構文は急いで導入しない。

まずは通常の `class` で表現する。

```abcl
class Agent {
  var state = "idle";

  method observe(input) {
    print("observed: " + input);
  }

  method act(task) {
    send model.run(task);
  }
}
```

将来、必要が明確になったら syntax sugar として `agent` を検討する。

```abcl
agent Assistant {
  capability Model;
  memory Session;

  method ask(prompt: string) {
    ...
  }
}
```

## 10. Compatibility Policy

既存サンプルを壊さない。

現在の回帰基準:

- `abclc/*.abcl` が全件 `load + compile` できる。
- SDL サンプルは headless 環境では以下を付けて検証する。

```sh
SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software
```

`commands.bat` の古い REPL 構文は、将来修正対象とする。

現在:

```text
send c1.inc
```

期待:

```text
send c1.inc()
```

## 11. Implementation Roadmap

### Phase 0: Baseline

- branch: `make-src-base`
- commit base: `d69378a`
- build: `cd src && opam exec -- make`
- sample check: `abclc/*.abcl`

### Phase 1: Specification Stabilization

- current syntax を文書化する。
- current type rules を文書化する。
- primitive catalog を作る。
- regression scripts を整備する。

### Phase 2: Type System Cleanup

- `sender` の扱いを明示する。
- `send` / `send!` の差を仕様化する。
- `now` / `future` send の型規則を仕様化する。
- method の戻り値型を導入し、既存 method は `unit` とみなす。
- `become` の型規則を固定する。
- `select` の型規則を固定する。
- error message に location を安定して出す。

### Phase 3: Capability Registry

- primitive を capability ごとに登録する。
- 型環境と runtime primitive 登録を対応させる。
- capability 一覧を REPL で表示できるようにする。

### Phase 4: AIOS Kernel API

- actor lifecycle を導入する。
- actor registry API を整理する。
- logs/events を統一する。
- web gateway を AIOS service として整理する。

### Phase 5: AI Services

- model actor
- memory actor
- tool actor
- planner actor
- observer/action loop

これらを primitive ではなく actor service として実装する。

## 12. Immediate Decisions

当面の決定事項:

1. `class` を actor behavior 定義とみなす。
2. `new` は actor instance 作成とみなす。
3. `send` は typed async message send とする。
4. `now` は typed sync message send とする。
5. `future` は typed async request message send とし、`future t` を返す。
6. `send!` は unsafe dynamic send とする。
7. `become` は behavior transition とする。
8. `remote` は dynamic boundary とする。
9. AI agent 専用構文はまだ追加しない。
10. capability は primitive の分類から始める。
11. 既存 `abclc/*.abcl` を互換性テストにする。

## 13. Open Questions

- method に戻り値型を持たせるか、actor message は常に `unit` とするか。
- `reply` をどう型づけるか。
- `future` と既存 `reply` / `msg_id` を同一機構に統合するか。
- `now` を mailbox 経由にするか、直接 method call にするか。
- `now` の deadlock を型または capability policy で制限するか。
- `sender` を actor 型にするか reply channel 型にするか。
- `become` 後の protocol compatibility を検査するか。
- remote actor の interface 宣言をいつ導入するか。
- effect system を導入するか、capability registry に留めるか。
- AI model call を primitive にするか、actor service にするか。

## 14. Next Work Items

1. `docs/ABCLCP_CURRENT_SPEC.md` を作り、現行構文と型規則を実装ベースで記述する。
2. `scripts/test_abclc_samples.sh` を作り、`abclc/*.abcl` の回帰テストを自動化する。
3. `commands.bat` の古い REPL send 構文を修正する。
4. primitive catalog を `docs/CAPABILITIES.md` として整理する。
5. method 戻り値型、`now`、`future`、`await` の最小構文案を決める。
6. `sender`, `remote`, `become`, `select` の型規則を小さく改善する。
