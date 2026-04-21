import * as AST from "../ast.js";
import { Interpreter } from "../interpreter.js";

window.addEventListener("DOMContentLoaded", () => {
  const parser = window.parser;

  document.body.innerHTML = `
    <div id="bar" style="padding:10px;background:#222;border-bottom:1px solid #333;">
      <button id="btnRunSample">run sample</button>
      <button id="btnParseOnly">parse only</button>
      <button id="btnClear">clear</button>
    </div>

    <div id="consoleOut"
         style="height:calc(100vh - 320px);
                overflow:auto;
                padding:12px;
                white-space:pre-wrap;
                background:#000;
                color:#0f0;
                font-family:monospace;"></div>

    <div id="inputRow"
         style="display:flex;
                gap:8px;
                align-items:center;
                padding:10px;
                background:#181818;
                border-top:1px solid #333;">
      <span style="color:#0f0;font-family:monospace;font-weight:bold;">ABCL/c+&gt;</span>
      <input id="cmd" type="text" placeholder="single command (optional)"
             style="flex:1;padding:8px;background:#222;color:#fff;border:1px solid #555;font-family:monospace;">
      <button id="runCmdBtn"
              style="padding:8px 12px;background:#333;color:#fff;border:1px solid #666;cursor:pointer;">Run Cmd</button>
    </div>

    <textarea id="src"
              style="width:100%;
                     height:180px;
                     background:#111;
                     color:#fff;
                     font-family:monospace;
                     padding:8px;
                     box-sizing:border-box;">class Calc {
  method init() {
    print("Calc initialized");
  }

  method add(a,b) {
    print("add received");
    reply(a + b);
  }
}

var calc = new Calc();
send calc.add(3,4);
    </textarea>
  `;

  const consoleOut = document.getElementById("consoleOut");
  const src = document.getElementById("src");
  const cmdInput = document.getElementById("cmd");
  const runCmdBtn = document.getElementById("runCmdBtn");

  let history = [];
  let historyIndex = -1;

  function appendConsole(line) {
    if (line === undefined || line === null) return;
    const s = String(line);
    consoleOut.textContent += s;
    if (!s.endsWith("\n")) consoleOut.textContent += "\n";
    consoleOut.scrollTop = consoleOut.scrollHeight;
  }

  function clearConsole() {
    consoleOut.textContent = "";
  }

  function closeConsoleWindow() {
    const ok = window.confirm("Close this console?");
    if (!ok) return;
    appendConsole("Bye!");
    setTimeout(() => window.close(), 200);
  }

  if (!parser) {
    appendConsole("[ERROR] window.parser is not available.");
    appendConsole("Check that browser_console.html loads /src/parser/parser.js first.");
    return;
  }

  // Jison parser に AST 関数群を渡す
  parser.yy = AST;

  const interpreter = new Interpreter(appendConsole);

  function runSource(code) {
    appendConsole(">>> run");
    try {
      const ast = parser.parse(code);
      appendConsole("[parse ok]");
      interpreter.runProgram(ast);
    } catch (e) {
      appendConsole("[ERROR] " + e);
    }
  }

  function parseOnly(code) {
    appendConsole(">>> parse");
    try {
      const ast = parser.parse(code);
      appendConsole("[parse ok]");
      appendConsole(JSON.stringify(ast, null, 2));
    } catch (e) {
      appendConsole("[ERROR] " + e);
    }
  }

  function runSingleCommand(cmd) {
    const trimmed = cmd.trim();
    if (!trimmed) return;

    if (trimmed === "exit" || trimmed === "quit") {
      closeConsoleWindow();
      return;
    }

    if (trimmed === "help") {
      appendConsole("Available commands:");
      appendConsole("  help");
      appendConsole("  exit");
      appendConsole("  parse      (use the parse only button)");
      appendConsole("  run        (use the run sample button)");
      appendConsole("");
      appendConsole("You can also type a single ABCL/c+ command such as:");
      appendConsole('  var calc = new Calc();');
      appendConsole('  send calc.add(3,4);');
      return;
    }

    appendConsole("ABCL/c+> " + trimmed);

    try {
      // 単一コマンドだけを stmts として parse させるために、
      // 空プログラム末尾に付ける最小ラップ
      const wrapped = trimmed.endsWith(";") ? trimmed : trimmed + ";";
      const ast = parser.parse(wrapped);
      appendConsole("[parse ok]");
      interpreter.runProgram(ast);
    } catch (e) {
      appendConsole("[ERROR] " + e);
    }
  }

  document.getElementById("btnRunSample").addEventListener("click", () => {
    clearConsole();
    runSource(src.value);
  });

  document.getElementById("btnParseOnly").addEventListener("click", () => {
    clearConsole();
    parseOnly(src.value);
  });

  document.getElementById("btnClear").addEventListener("click", () => {
    clearConsole();
    cmdInput.focus();
  });

  runCmdBtn.addEventListener("click", () => {
    const cmd = cmdInput.value.trim();
    if (!cmd) return;

    history.push(cmd);
    historyIndex = history.length;

    runSingleCommand(cmd);
    cmdInput.value = "";
    cmdInput.focus();
  });

  cmdInput.addEventListener("keydown", (ev) => {
    if (ev.key === "Enter") {
      runCmdBtn.click();
      return;
    }

    if (ev.ctrlKey && (ev.key === "d" || ev.key === "D")) {
      ev.preventDefault();
      closeConsoleWindow();
      return;
    }

    if (ev.key === "ArrowUp") {
      if (history.length === 0) return;
      historyIndex = Math.max(0, historyIndex - 1);
      cmdInput.value = history[historyIndex] || "";
      ev.preventDefault();
      return;
    }

    if (ev.key === "ArrowDown") {
      if (history.length === 0) return;
      historyIndex = Math.min(history.length, historyIndex + 1);
      cmdInput.value = history[historyIndex] || "";
      if (historyIndex === history.length) cmdInput.value = "";
      ev.preventDefault();
    }
  });

  appendConsole("ABCL/c+ Browser Console");
  appendConsole("Jison-based parser + JavaScript runtime");
  appendConsole("Buttons:");
  appendConsole("  run sample  : parse + run textarea");
  appendConsole("  parse only  : show AST");
  appendConsole("  clear       : clear console");
  appendConsole("");
  appendConsole("Try:");
  appendConsole("  1) Press 'run sample'");
  appendConsole("  2) Or type: help");
  appendConsole("");

  cmdInput.focus();
});
