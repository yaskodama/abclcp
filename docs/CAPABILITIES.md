# ABCL/c+ AI-OS Capabilities

作成日: 2026-05-02

ABCL/c+ の AI-OS 化では、外部効果を primitive 名だけで扱わず、capability として分類する。
現在の実装では runtime primitive に capability メタデータを付け、ABCL/c+ プログラムから
一覧を問い合わせられる。

## Runtime Introspection

```abcl
print(capabilities());
print(capability_prims("Actor"));
```

追加された primitive:

- `capabilities() : string[]`
- `capability_prims(capability: string) : string[]`

`capability_prims` は、指定 capability に属する primitive を
`name : signature -- description` の文字列配列として返す。

## Current Capability Groups

- `Actor`
- `Actor.Introspection`
- `AIOS.Event`
- `AIOS.Model`
- `AIOS.Kernel`
- `AIOS.Memory`
- `AIOS.Task`
- `AIOS.Model.Gemini`
- `AIOS.Model.OpenAI`
- `AIOS.Remote`
- `AIOS.Service`
- `Console`
- `Core.Array`
- `Core.Introspection`
- `Core.Math`
- `Time`
- `UI.SDL`
- `Web`

## Policy

AI-OS 固有機能は、まず primitive capability または actor service として追加する。
新しい構文は、既存の actor runtime と型検査で表現できないことが明確になってから導入する。

## AIOS.Kernel

```abcl
print(aios_kernel());
print(aios_actors());
print(aios_actor_info("echo"));
print(aios_actor_methods("echo"));
print(aios_mailbox_len("echo"));
```

`AIOS.Kernel` は actor registry と mailbox を観測するための最小 kernel capability である。

## AIOS.Service

```abcl
aios_register_service("memory", "memory");
print(aios_services());
print(aios_service_actor("memory"));
print(aios_service_info("memory"));
print(aios_now("memory", "get", "topic"));
```

`AIOS.Service` は名前付きAIOS serviceをactorに対応づけ、service名からrequest/replyを行う capability である。

## AIOS.Event

```abcl
aios_emit("agent.observe input");
print(aios_event_count());
print(aios_events());
print(aios_events_since(0));
```

`AIOS.Event` はkernel event streamに観測可能なイベントを記録する capability である。

## AIOS.Memory

```abcl
aios_memory_put("problem", "3 boxes with 4 apples");
print(aios_memory_get("problem"));
print(aios_memory_has("problem"));
print(aios_memory_keys());
```

`AIOS.Memory` は kernel 内の文字列 key/value store である。actor service から使うことで、
AIOS agent の問題、回答、会話履歴、成果物IDなどを共有できる。

## AIOS.Task

```abcl
var tid = aios_task_create("solve apple problem");
aios_task_set(tid, "status", "done");
print(aios_task_get(tid, "status"));
print(aios_task_info(tid));
print(aios_tasks());
```

`AIOS.Task` は作業単位を task id で管理する capability である。agent が問題、
計画、回答、レビュー、状態を同じ task に集約できる。

## AIOS.Model.Gemini

## AIOS.Model

```abcl
var answer = model_generate("gemini", "Solve: 3 boxes with 4 apples each");
var answer2 = model_generate("openai", "Solve: 3 boxes with 4 apples each");
var answer3 = model_generate("mock", "Solve: 3 boxes with 4 apples each");
```

`AIOS.Model` は provider 名で model backend を切り替える capability である。
`"gemini"` / `"google"` は Gemini、`"openai"` / `"chatgpt"` は OpenAI を使う。
`"mock"` / `"test"` / `"offline"` は外部APIを呼ばない deterministic mock を使う。
provider に `"default"` または空文字列を渡した場合は `AIOS_MODEL_PROVIDER` を読み、
未設定なら Gemini を使う。

## AIOS.Model.Gemini

```abcl
var answer = gemini_generate("Solve: 3 boxes with 4 apples each");
```

`AIOS.Model.Gemini` は `GEMINI_API_KEY` 環境変数を使って Gemini API にpromptを送る capability である。

## AIOS.Model.OpenAI

```abcl
var answer = openai_generate("Solve: 3 boxes with 4 apples each");
```

`AIOS.Model.OpenAI` は `OPENAI_API_KEY` 環境変数を使って OpenAI Responses API にpromptを送る capability である。

## AIOS.Remote

```abcl
var host = remote_reviewer_host();
var review = remote_review(host, problem, answer);
var review_ja = remote_review_ja(host, problem, answer);
```

`AIOS.Remote` は別プロセスや別マシンで動くAIOS補助サービスを呼び出すための capability である。
現在は reviewer 用のHTTP同期呼び出しを提供する。
`remote_reviewer_host()` は `REMOTE_REVIEWER_HOSTPORT` を読み、未設定なら `127.0.0.1:18080` を返す。
