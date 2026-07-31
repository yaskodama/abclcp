import { readFileSync } from 'fs';
import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const JS = process.argv[3];
const AST = await import(JS + '/ast.js');
const p = require(JS + '/parser/parser.js');
const parser = p.parser || p;
parser.yy = AST;
try { const ast = parser.parse(readFileSync(process.argv[2],'utf8')); console.log('PARSE OK'); }
catch (e) { console.log('[err] ' + String(e.message).split('\n')[0].slice(0,120)); }
