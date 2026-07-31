# ABCL/c+ AIOS Kernel

作成日: 2026-05-02

この段階の AIOS kernel は、既存の actor runtime を中核にした最小 kernel surface である。
ABCL/c+ プログラムから capability、actor registry、mailbox、request/reply を観測できる。

## Kernel Primitives

```abcl
aios_kernel()              // string
aios_actors()              // string[]
aios_actor_info(name)      // string
aios_actor_methods(name)   // string[]
aios_mailbox_len(name)     // int
```

これらは `AIOS.Kernel` capability に属する。

## Service Registry

AIOS service は、名前付き actor として kernel に登録する。

```abcl
aios_register_service("memory", "memory_actor");
print(aios_services());
print(aios_service_actor("memory"));
print(aios_service_info("memory"));
```

Service registry primitive:

```abcl
aios_register_service(service, actor)  // unit
aios_services()                        // string[]
aios_service_actor(service)            // string
aios_service_info(service)             // string
aios_now(service, method, ...args)      // any
aios_future(service, method, ...args)   // future any
```

これらは `AIOS.Service` capability に属する。

Service request example:

```abcl
var value = aios_now("memory", "get", "topic");

var f = aios_future("model", "generate", "hello");
var text = await f;
```

## Event Stream

Kernel event stream は、agent や service の観測ログを保持する。

```abcl
aios_emit("agent.observe build");
print(aios_events());
print(aios_events_since(0));
print(aios_event_count());
```

Event primitive:

```abcl
aios_emit(event)          // int
aios_events()             // string[]
aios_events_since(after)  // string[]
aios_event_count()        // int
```

これらは `AIOS.Event` capability に属する。

## Agent Loop

現段階では agent も通常の actor service として表現する。

```abcl
class AgentService {
  method handle(input) {
    aios_emit("agent.observe " + input);
    var plan_future = aios_future("model", "generate", input);
    var plan = await plan_future;
    aios_emit("agent.plan " + plan);
    var result = aios_now("tool", "run", "echo", plan);
    reply(result);
  }
}
```

## Request/Reply

`now` と `future` は、actor method が `reply(value)` を呼ぶことで値を返す。

```abcl
var answer = now service.ping("ready");

var f = future service.ping("later");
var value = await f;
```

現在の制限:

- method 戻り値型はまだ構文に無いため、`now` は `any`、`future` は `future any` として扱う。
- remote actor に対する `future` は未実装。
- `reply(value)` を呼ばない method を `now` / `await` すると待ち続ける。

## Smoke Test

```sh
cd src
opam exec -- make
printf 'load ../abclc/aios_kernel.aipl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

期待される出力には以下が含まれる。

```text
ABCL/c+ AIOS kernel actors=1 capabilities=11
actor echo class=EchoService mailbox=0 methods=[ping]
kernel now = echo: ready
kernel future = echo: future-ready
```

Service registry smoke test:

```sh
printf 'load ../abclc/aios_services.aipl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

期待される出力には以下が含まれる。

```text
[memory]
service memory actor=memory actor memory class=MemoryService mailbox=0 methods=[get, put]
memory put = ok
memory get = 42.
```

Standard services smoke test:

```sh
printf 'load ../abclc/aios_standard_services.aipl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

期待される出力には以下が含まれる。

```text
[memory, model, tool]
memory.put = ok
memory.get = AIOS
model.generate = model: hello
tool.run = tool echo: done
```

Agent smoke test:

```sh
printf 'load ../abclc/aios_agent.aipl\ncompile\nquit\n' | \
  SDL_VIDEODRIVER=dummy SDL_RENDER_DRIVER=software opam exec -- ./abclrepl_thread
```

期待される出力には以下が含まれる。

```text
agent output = tool echo -> plan: build
[agent.observe build, agent.plan plan: build, agent.act tool echo -> plan: build]
```
