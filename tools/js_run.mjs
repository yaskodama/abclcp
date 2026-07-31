import { readFileSync } from 'fs';
import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const JS = process.argv[3];
const AST = await import(JS + '/ast.js');
const p = require(JS + '/parser/parser.js');
const parser = p.parser || p;
parser.yy = AST;
const { Interpreter } = await import(JS + '/interpreter.js');
const out = [];
const interp = new Interpreter(s => out.push(String(s)));
try {
  const ast = parser.parse(readFileSync(process.argv[2], 'utf8'));
  interp.runProgram(ast);
} catch (e) { out.push('[err] ' + String(e.message).split('\n')[0].slice(0,110)); }
setTimeout(() => { console.log(out.slice(0,40).join(' / ')); process.exit(0); }, 1200);
