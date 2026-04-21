import { Runtime } from "./runtime.js";

export class Interpreter {
  constructor(printer) {
    this.runtime = new Runtime(printer);
  }

  runProgram(ast) {
    this.runtime.reset();
    for (const cls of ast.classes) {
      this.runtime.registerClass(cls);
    }
    for (const st of ast.statements) {
      this.runtime.evalStmt(st, {});
    }
  }
}
