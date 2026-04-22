export class Runtime {
  constructor(printer = console.log) {
    this.print = printer;
    this.classes = new Map();
    this.actors = new Map();
    this.nextId = 1;
    this.replies = [];
  }

  reset() {
    this.classes.clear();
    this.actors.clear();
    this.nextId = 1;
    this.replies = [];
  }

  registerClass(cls) {
    this.classes.set(cls.name, cls);
  }

  createActor(name, className) {
    const cls = this.classes.get(className);
    if (!cls) throw new Error("Class not found: " + className);

    const actor = {
      name,
      className,
      methods: new Map(cls.methods.map(m => [m.name, m])),
      mailbox: []
    };

    this.actors.set(name, actor);
    this.print(`[actor created] ${name} : ${className}`);

    if (actor.methods.has("init")) {
      this.invoke(actor, "init", []);
    }

    return actor;
  }

  hasSelectableMethod(actor, methodName) {
    for (const method of actor.methods.values()) {
      if (!method.body || !method.body.statements) continue;

      for (const st of method.body.statements) {
        if (st.type === "Select") {
          for (const c of st.cases) {
            if (c.method === methodName) return true;
          }
        }
      }
    }
    return false;
  }

  knowsMessage(actor, methodName) {
    return actor.methods.has(methodName) || this.hasSelectableMethod(actor, methodName);
  }

  send(actorName, methodName, args, unsafe = false) {
    const actor = this.actors.get(actorName);
    if (!actor) throw new Error("actor not found: " + actorName);

    if (!unsafe && !this.knowsMessage(actor, methodName)) {
      throw new Error(`unknown method: ${actor.className}.${methodName}`);
    }      

    actor.mailbox.push({ methodName, args, unsafe });
    this.print(`[send] ${actorName}.${methodName}(${args.join(", ")})`);
    this.processMailbox(actor);
  }

  processMailbox(actor) {
    while (actor.mailbox.length > 0) {
      const msg = actor.mailbox.shift();
      this.invoke(actor, msg.methodName, msg.args, msg.unsafe);
    }
  }

  invoke(actor, methodName, args, unsafe = false) {
    const method = actor.methods.get(methodName);
    if (!method) {
      if (unsafe) {
        this.print(`[unsafe-send ignored] ${actor.className}.${methodName}`);
        return null;
      }
      throw new Error(`unknown method at runtime: ${actor.className}.${methodName}`);
    }

    const env = { __currentActor: actor.name };
    method.params.forEach((p, i) => {
      env[p] = args[i];
    });

    let last = null;
    for (const st of method.body.statements) {
      last = this.evalStmt(st, env);
    }
    return last;
  }

  evalStmt(stmt, env) {
    switch (stmt.type) {
      case "Print": {
        const v = this.evalExpr(stmt.expr, env);
        this.print(v);
        return v;
      }

      case "Reply": {
        const v = this.evalExpr(stmt.expr, env);
        this.replies.push(v);
        this.print(`[REPLY] value=${v}`);
        return v;
      }

      case "VarDecl": {
        // ★ ここが重要
        // var calc = new Calc();
        // のときは、変数名 calc を actor 名として使う
        if (stmt.expr.type === "NewExpr") {
          const actorName = stmt.name;
          const className = stmt.expr.className;
          this.createActor(actorName, className);
          env[stmt.name] = actorName;
          return actorName;
        }

        const v = this.evalExpr(stmt.expr, env);
        env[stmt.name] = v;
        return v;
      }

      case "Send": {
        const actorName = this.evalTarget(stmt.target, env);
        const args = stmt.args.map(a => this.evalExpr(a, env));
        this.send(actorName, stmt.method, args, stmt.unsafe);
        return null;
      }

      case "Select": {
        return this.evalSelect(stmt, env);
      }
	
      default:
        throw new Error("Unsupported statement: " + stmt.type);
    }
  }

  evalTarget(target, env) {
    // target は今は IDENT 文字列想定
    if (typeof target === "string") {
      if (target in env) return env[target];
      if (this.actors.has(target)) return target;
      return target;
    }
    throw new Error("Unsupported send target: " + JSON.stringify(target));
  }

  evalSelect(stmt, env) {
    // 現段階では env.__currentActor が必要
    const actorName = env.__currentActor;
    if (!actorName) {
      throw new Error("select used outside actor method");
    }

    const actor = this.actors.get(actorName);
    if (!actor) {
      throw new Error("current actor not found: " + actorName);
    }

    // mailbox から最初に一致する message を探す
    let matchedIndex = -1;
    let matchedCase = null;
    let matchedMsg = null;

    for (let i = 0; i < actor.mailbox.length; i++) {
      const msg = actor.mailbox[i];
      for (const c of stmt.cases) {
        if (msg.methodName === c.method) {
          matchedIndex = i;
          matchedCase = c;
          matchedMsg = msg;
          break;
        }
      }
      if (matchedCase) break;
    }

       if (matchedCase) {
      actor.mailbox.splice(matchedIndex, 1);

      const localEnv = { ...env };
      matchedCase.params.forEach((p, i) => {
        localEnv[p] = matchedMsg.args[i];
      });

      let last = null;
      for (const st of matchedCase.body.statements) {
        last = this.evalStmt(st, localEnv);
      }
      return last;
    }

    // timeout があればそれを実行
    if (stmt.timeoutBody) {
      this.print(`[timeout] ${stmt.timeoutMs}ms`);
      let last = null;
      for (const st of stmt.timeoutBody.statements) {
        last = this.evalStmt(st, env);
      }
      return last;
    }

    return null;
  }

  evalExpr(expr, env) {
    switch (expr.type) {
      case "IntLit":
        return expr.value;

      case "StringLit":
        return expr.value;

      case "Var":
        if (expr.name in env) return env[expr.name];
        if (this.actors.has(expr.name)) return expr.name;
        throw new Error("Unknown var: " + expr.name);

      case "Binop": {
        const l = this.evalExpr(expr.left, env);
        const r = this.evalExpr(expr.right, env);
        if (expr.op === "+") return l + r;
        throw new Error("Unsupported op: " + expr.op);
      }

      case "NewExpr": {
        // 単独評価時は自動名を使う
        const name = expr.className.toLowerCase() + this.nextId++;
        this.createActor(name, expr.className);
        return name;
      }

      default:
        throw new Error("Unsupported expr: " + expr.type);
    }
  }
}
