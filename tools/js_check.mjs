// JS-I の型検査だけを走らせる。
//   node tools/js_check.mjs <file.aipl> <JS-I のパス>
import { readFileSync } from 'fs';
import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const JS = process.argv[3];
const AST = await import(JS + '/ast.js');
const p = require(JS + '/parser/parser.js');
const parser = p.parser || p;
parser.yy = AST;
const tc = await import(JS + '/typecheck.js');
let issues = [];
try {
  const ast = parser.parse(readFileSync(process.argv[2], 'utf8'));
  if (tc.checkReplyAndDeadlines) {
    const r = tc.checkReplyAndDeadlines(ast, {}) || [];
    issues = issues.concat(r.map(x => typeof x === 'string' ? x : (x.message || JSON.stringify(x))));
  }
  if (tc.checkResourceUse) {
    issues = issues.concat(tc.checkResourceUse(ast) || []);
  }
  if (tc.checkWaitCycle) {
    issues = issues.concat(tc.checkWaitCycle(ast) || []);
  }
  if (tc.checkBadDeadlines) {
    issues = issues.concat(tc.checkBadDeadlines(ast) || []);
  }
  if (tc.checkUndeclaredAssign) {
    issues = issues.concat(tc.checkUndeclaredAssign(ast) || []);
  }
  if (tc.checkEffectDeclarations) {
    issues = issues.concat(tc.checkEffectDeclarations(ast) || []);
  }
  if (tc.runTypeCheck) {
    try { tc.runTypeCheck(ast); }
    catch (e) { issues.push('TYPE_ERROR: ' + String(e.message).split('\n')[0]); }
  }
} catch (e) {
  issues.push('PARSE_ERROR: ' + String(e.message).split('\n')[0].slice(0, 90));
}
console.log(issues.length ? issues.length + ' issue(s)\n  ' + issues.slice(0,4).join('\n  ') : '0 issue(s)');
process.exit(0);
