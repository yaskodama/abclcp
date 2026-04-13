type token =
  | ID of (
# 13 "parser.mly"
        string
# 6 "parser.ml"
)
  | FLOATLIT of (
# 14 "parser.mly"
        float
# 11 "parser.ml"
)
  | INTLIT of (
# 15 "parser.mly"
        int
# 16 "parser.ml"
)
  | STRINGLIT of (
# 16 "parser.mly"
        string
# 21 "parser.ml"
)
  | METHOD
  | FLOAT
  | CALL
  | SEND
  | UNSAFESEND
  | IF
  | THEN
  | ELSE
  | WHILE
  | DO
  | ASSIGN
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | SEMICOLON
  | COMMA
  | GE
  | LE
  | GT
  | LT
  | SELF
  | SENDER
  | CLASS
  | SELECT
  | CASE
  | TIMEOUT
  | ARROW
  | EOF
  | NEW
  | VAR
  | EQ
  | DOT
  | BECOME

open Parsing
let _ = parse_error;;
# 2 "parser.mly"
open Ast
open Location
let mk_expr (d : Ast.expr_desc) : Ast.expr = { loc  = Location.dummy; desc  = d }
let mk_stmt (d : Ast.stmt_desc) : Ast.stmt = { sloc = Location.dummy; sdesc = d }
exception Syntax_error of Location.t * string
let loc_of_rhs i =
  let p = Parsing.rhs_start_pos i in
  { line = p.Lexing.pos_lnum; col  = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 }
let mk_expr1 i d : Ast.expr = { loc = loc_of_rhs i; desc = d }
let mk_stmt1 i d : Ast.stmt = { sloc = loc_of_rhs i; sdesc = d }
# 75 "parser.ml"
let yytransl_const = [|
  261 (* METHOD *);
  262 (* FLOAT *);
  263 (* CALL *);
  264 (* SEND *);
  265 (* UNSAFESEND *);
  266 (* IF *);
  267 (* THEN *);
  268 (* ELSE *);
  269 (* WHILE *);
  270 (* DO *);
  271 (* ASSIGN *);
  272 (* PLUS *);
  273 (* MINUS *);
  274 (* TIMES *);
  275 (* DIV *);
  276 (* LPAREN *);
  277 (* RPAREN *);
  278 (* LBRACE *);
  279 (* RBRACE *);
  280 (* SEMICOLON *);
  281 (* COMMA *);
  282 (* GE *);
  283 (* LE *);
  284 (* GT *);
  285 (* LT *);
  286 (* SELF *);
  287 (* SENDER *);
  288 (* CLASS *);
  289 (* SELECT *);
  290 (* CASE *);
  291 (* TIMEOUT *);
  292 (* ARROW *);
    0 (* EOF *);
  293 (* NEW *);
  294 (* VAR *);
  295 (* EQ *);
  296 (* DOT *);
  297 (* BECOME *);
    0|]

let yytransl_block = [|
  257 (* ID *);
  258 (* FLOATLIT *);
  259 (* INTLIT *);
  260 (* STRINGLIT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\004\000\004\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\006\000\
\006\000\009\000\009\000\007\000\007\000\010\000\011\000\011\000\
\011\000\012\000\012\000\014\000\014\000\013\000\013\000\013\000\
\013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
\013\000\013\000\013\000\013\000\013\000\013\000\015\000\015\000\
\015\000\015\000\017\000\018\000\019\000\019\000\020\000\020\000\
\016\000\016\000\008\000\008\000\021\000\021\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\005\000\009\000\008\000\008\000\005\000\001\000\
\002\000\005\000\005\000\001\000\002\000\008\000\000\000\001\000\
\003\000\001\000\002\000\002\000\000\000\004\000\006\000\005\000\
\008\000\008\000\008\000\008\000\005\000\007\000\004\000\003\000\
\005\000\009\000\005\000\006\000\005\000\005\000\002\000\000\000\
\002\000\000\000\006\000\004\000\001\000\000\000\001\000\003\000\
\006\000\000\000\000\000\001\000\003\000\005\000\001\000\001\000\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\004\000\
\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\078\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\
\000\000\001\000\000\000\006\000\000\000\063\000\065\000\064\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\077\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\015\000\000\000\
\000\000\000\000\000\000\000\000\000\000\010\000\017\000\021\000\
\000\000\011\000\072\000\000\000\000\000\000\000\000\000\000\000\
\000\000\009\000\000\000\071\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\013\000\014\000\000\000\000\000\018\000\
\019\000\000\000\025\000\000\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\048\000\000\000\000\000\022\000\
\027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\028\000\040\000\000\000\000\000\000\000\030\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\039\000\000\000\000\000\000\000\047\000\000\000\000\000\000\000\
\000\000\043\000\032\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\046\000\000\000\041\000\045\000\
\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\044\000\000\000\000\000\000\000\000\000\
\038\000\055\000\000\000\000\000\000\000\000\000\000\000\035\000\
\033\000\034\000\036\000\052\000\000\000\000\000\000\000\000\000\
\056\000\051\000\057\000\042\000"

let yydgoto = "\002\000\
\009\000\010\000\011\000\027\000\028\000\053\000\054\000\029\000\
\055\000\056\000\096\000\120\000\121\000\132\000\149\000\164\000\
\165\000\179\000\203\000\204\000\000\000"

let yysindex = "\005\000\
\003\255\000\000\014\000\032\255\059\255\074\255\076\255\081\255\
\000\000\080\000\070\255\000\000\129\255\047\255\069\255\091\255\
\100\255\000\000\082\255\000\000\097\255\000\000\000\000\000\000\
\129\255\117\255\099\255\253\255\104\255\127\255\145\255\002\255\
\133\255\000\000\129\255\175\255\128\255\129\255\129\255\129\255\
\129\255\129\255\129\255\129\255\129\255\129\255\123\255\130\255\
\131\255\157\255\163\255\164\255\162\255\152\255\043\255\162\255\
\167\255\189\255\156\255\000\000\129\255\253\255\031\000\031\000\
\183\255\183\255\253\255\253\255\253\255\253\255\000\000\129\255\
\129\255\166\255\180\255\199\255\200\255\000\000\000\000\000\000\
\204\255\000\000\000\000\205\255\207\255\216\255\224\255\129\255\
\129\255\000\000\129\255\000\000\214\255\215\255\006\000\219\255\
\203\255\217\255\012\000\000\000\000\000\224\255\220\255\000\000\
\000\000\008\000\000\000\088\255\000\000\044\255\017\000\024\255\
\033\000\015\000\129\255\088\255\020\000\035\000\046\000\030\000\
\088\255\129\255\129\255\034\000\036\000\039\000\042\000\045\000\
\129\255\171\255\088\255\052\000\000\000\066\000\067\000\000\000\
\000\000\231\255\065\000\026\255\055\000\087\000\088\000\089\000\
\235\255\088\255\000\000\000\000\027\255\141\255\030\255\000\000\
\068\000\069\000\070\000\074\000\075\000\076\000\077\000\088\255\
\000\000\097\000\096\000\078\000\000\000\099\000\249\255\079\000\
\081\000\000\000\000\000\082\000\129\255\129\255\129\255\129\255\
\092\000\085\000\071\000\072\000\000\000\090\000\000\000\000\000\
\091\000\000\000\093\000\095\000\098\000\100\000\088\255\108\000\
\101\000\102\000\129\255\000\000\094\000\103\000\104\000\105\000\
\000\000\000\000\109\000\086\000\088\255\088\255\110\000\000\000\
\000\000\000\000\000\000\000\000\111\000\112\000\113\000\114\000\
\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\113\001\000\000\116\000\000\000\000\000\000\000\
\000\000\000\000\117\001\000\000\155\255\000\000\000\000\000\000\
\000\000\000\000\118\000\049\255\000\000\000\000\000\000\000\000\
\000\000\000\000\116\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\115\000\117\000\
\000\000\000\000\000\000\000\000\116\000\086\255\047\000\053\000\
\138\255\027\000\079\255\098\255\041\000\059\000\000\000\116\000\
\116\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\120\000\000\000\
\000\000\000\000\116\000\000\000\000\000\000\000\121\000\000\000\
\000\000\000\000\000\000\000\000\000\000\120\000\000\000\000\000\
\000\000\011\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\122\000\000\000\000\000\000\000\000\000\
\123\000\000\000\116\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\122\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\124\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\116\000\116\000\116\000\116\000\
\035\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\127\000\
\000\000\000\000\116\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\128\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\011\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\250\255\000\000\000\000\233\255\067\001\016\000\221\255\
\000\000\000\000\023\001\136\255\149\255\251\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 405
let yytable = "\059\000\
\137\000\036\000\003\000\004\000\020\000\001\000\050\000\051\000\
\131\000\058\000\005\000\006\000\034\000\012\000\062\000\063\000\
\064\000\065\000\066\000\067\000\068\000\069\000\070\000\131\000\
\125\000\084\000\021\000\022\000\023\000\024\000\021\000\022\000\
\023\000\024\000\007\000\037\000\085\000\086\000\161\000\052\000\
\008\000\037\000\037\000\037\000\037\000\025\000\154\000\037\000\
\051\000\025\000\168\000\013\000\177\000\126\000\127\000\099\000\
\037\000\037\000\122\000\014\000\162\000\163\000\026\000\123\000\
\097\000\098\000\026\000\037\000\077\000\007\000\004\000\080\000\
\037\000\007\000\015\000\037\000\016\000\005\000\006\000\018\000\
\052\000\017\000\004\000\201\000\214\000\215\000\030\000\139\000\
\110\000\005\000\006\000\130\000\073\000\019\000\111\000\112\000\
\113\000\114\000\138\000\073\000\115\000\007\000\073\000\073\000\
\155\000\145\000\008\000\008\000\031\000\116\000\008\000\074\000\
\032\000\007\000\033\000\169\000\035\000\037\000\074\000\008\000\
\117\000\074\000\074\000\038\000\047\000\118\000\167\000\048\000\
\119\000\021\000\022\000\023\000\024\000\021\000\022\000\023\000\
\024\000\187\000\188\000\189\000\190\000\021\000\022\000\023\000\
\024\000\049\000\071\000\061\000\025\000\072\000\073\000\069\000\
\025\000\069\000\069\000\069\000\069\000\074\000\069\000\207\000\
\025\000\069\000\069\000\075\000\076\000\026\000\050\000\081\000\
\066\000\057\000\066\000\066\000\066\000\066\000\078\000\066\000\
\083\000\166\000\066\000\066\000\066\000\066\000\066\000\066\000\
\146\000\087\000\039\000\040\000\041\000\042\000\039\000\040\000\
\041\000\042\000\088\000\060\000\043\000\044\000\045\000\046\000\
\043\000\044\000\045\000\046\000\039\000\040\000\041\000\042\000\
\043\000\044\000\045\000\046\000\082\000\089\000\043\000\044\000\
\045\000\046\000\039\000\040\000\041\000\042\000\090\000\091\000\
\095\000\092\000\104\000\093\000\043\000\044\000\045\000\046\000\
\039\000\040\000\041\000\042\000\094\000\100\000\101\000\103\000\
\105\000\108\000\043\000\044\000\045\000\046\000\039\000\040\000\
\041\000\042\000\039\000\040\000\041\000\042\000\152\000\160\000\
\043\000\044\000\045\000\046\000\043\000\044\000\045\000\046\000\
\039\000\040\000\041\000\042\000\039\000\040\000\041\000\042\000\
\183\000\124\000\043\000\044\000\045\000\046\000\043\000\044\000\
\045\000\046\000\071\000\071\000\071\000\071\000\102\000\109\000\
\106\000\128\000\129\000\134\000\071\000\071\000\071\000\071\000\
\070\000\133\000\070\000\070\000\070\000\070\000\135\000\070\000\
\041\000\042\000\070\000\070\000\136\000\140\000\075\000\156\000\
\043\000\044\000\045\000\046\000\067\000\075\000\067\000\067\000\
\075\000\075\000\068\000\067\000\068\000\068\000\067\000\067\000\
\076\000\068\000\148\000\141\000\068\000\068\000\142\000\076\000\
\150\000\143\000\076\000\076\000\144\000\153\000\151\000\157\000\
\158\000\159\000\172\000\170\000\171\000\173\000\174\000\175\000\
\176\000\178\000\180\000\182\000\181\000\185\000\184\000\191\000\
\192\000\186\000\193\000\194\000\202\000\195\000\213\000\217\000\
\003\000\197\000\196\000\198\000\004\000\208\000\199\000\016\000\
\200\000\079\000\205\000\206\000\107\000\147\000\209\000\210\000\
\211\000\212\000\216\000\000\000\000\000\000\000\218\000\219\000\
\059\000\220\000\060\000\020\000\023\000\024\000\000\000\000\000\
\029\000\026\000\058\000\054\000\053\000"

let yycheck = "\035\000\
\121\000\025\000\000\001\001\001\011\000\001\000\005\001\006\001\
\116\000\033\000\008\001\009\001\019\000\000\000\038\000\039\000\
\040\000\041\000\042\000\043\000\044\000\045\000\046\000\131\000\
\001\001\061\000\001\001\002\001\003\001\004\001\001\001\002\001\
\003\001\004\001\032\001\001\001\072\000\073\000\146\000\038\001\
\038\001\007\001\008\001\009\001\010\001\020\001\021\001\013\001\
\006\001\020\001\021\001\020\001\160\000\030\001\031\001\091\000\
\022\001\023\001\015\001\001\001\034\001\035\001\037\001\020\001\
\088\000\089\000\037\001\033\001\053\000\021\001\001\001\056\000\
\038\001\025\001\001\001\041\001\001\001\008\001\009\001\000\000\
\038\001\001\001\001\001\191\000\205\000\206\000\040\001\123\000\
\001\001\008\001\009\001\115\000\014\001\024\001\007\001\008\001\
\009\001\010\001\122\000\021\001\013\001\032\001\024\001\025\001\
\140\000\129\000\021\001\038\001\040\001\022\001\025\001\014\001\
\022\001\032\001\015\001\151\000\020\001\001\001\021\001\038\001\
\033\001\024\001\025\001\025\001\021\001\038\001\150\000\001\001\
\041\001\001\001\002\001\003\001\004\001\001\001\002\001\003\001\
\004\001\173\000\174\000\175\000\176\000\001\001\002\001\003\001\
\004\001\001\001\024\001\020\001\020\001\020\001\020\001\014\001\
\020\001\016\001\017\001\018\001\019\001\001\001\021\001\195\000\
\020\001\024\001\025\001\001\001\001\001\037\001\005\001\001\001\
\014\001\037\001\016\001\017\001\018\001\019\001\023\001\021\001\
\021\001\037\001\024\001\025\001\026\001\027\001\028\001\029\001\
\014\001\020\001\016\001\017\001\018\001\019\001\016\001\017\001\
\018\001\019\001\015\001\021\001\026\001\027\001\028\001\029\001\
\026\001\027\001\028\001\029\001\016\001\017\001\018\001\019\001\
\026\001\027\001\028\001\029\001\024\001\015\001\026\001\027\001\
\028\001\029\001\016\001\017\001\018\001\019\001\023\001\020\001\
\001\001\021\001\024\001\021\001\026\001\027\001\028\001\029\001\
\016\001\017\001\018\001\019\001\021\001\024\001\024\001\021\001\
\024\001\022\001\026\001\027\001\028\001\029\001\016\001\017\001\
\018\001\019\001\016\001\017\001\018\001\019\001\024\001\021\001\
\026\001\027\001\028\001\029\001\026\001\027\001\028\001\029\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\001\001\026\001\027\001\028\001\029\001\026\001\027\001\
\028\001\029\001\016\001\017\001\018\001\019\001\025\001\024\001\
\021\001\001\001\020\001\001\001\026\001\027\001\028\001\029\001\
\014\001\022\001\016\001\017\001\018\001\019\001\001\001\021\001\
\018\001\019\001\024\001\025\001\023\001\020\001\014\001\001\001\
\026\001\027\001\028\001\029\001\014\001\021\001\016\001\017\001\
\024\001\025\001\014\001\021\001\016\001\017\001\024\001\025\001\
\014\001\021\001\023\001\040\001\024\001\025\001\040\001\021\001\
\015\001\040\001\024\001\025\001\040\001\021\001\020\001\001\001\
\001\001\001\001\021\001\024\001\024\001\020\001\020\001\020\001\
\020\001\001\001\003\001\001\001\023\001\021\001\024\001\012\001\
\020\001\024\001\036\001\036\001\001\001\020\001\025\001\001\001\
\000\000\021\001\024\001\021\001\000\000\024\001\021\001\005\001\
\021\001\055\000\022\001\022\001\102\000\131\000\024\001\024\001\
\024\001\021\001\021\001\255\255\255\255\255\255\023\001\023\001\
\021\001\024\001\021\001\023\001\021\001\021\001\255\255\255\255\
\023\001\023\001\023\001\021\001\021\001"

let yynames_const = "\
  METHOD\000\
  FLOAT\000\
  CALL\000\
  SEND\000\
  UNSAFESEND\000\
  IF\000\
  THEN\000\
  ELSE\000\
  WHILE\000\
  DO\000\
  ASSIGN\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  LPAREN\000\
  RPAREN\000\
  LBRACE\000\
  RBRACE\000\
  SEMICOLON\000\
  COMMA\000\
  GE\000\
  LE\000\
  GT\000\
  LT\000\
  SELF\000\
  SENDER\000\
  CLASS\000\
  SELECT\000\
  CASE\000\
  TIMEOUT\000\
  ARROW\000\
  EOF\000\
  NEW\000\
  VAR\000\
  EQ\000\
  DOT\000\
  BECOME\000\
  "

let yynames_block = "\
  ID\000\
  FLOATLIT\000\
  INTLIT\000\
  STRINGLIT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decls) in
    Obj.repr(
# 33 "parser.mly"
              ( _1 )
# 410 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 34 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 416 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 37 "parser.mly"
         ( [_1] )
# 423 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 38 "parser.mly"
                   ( [_1] )
# 430 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 39 "parser.mly"
                         ( _1 :: _3 )
# 438 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 40 "parser.mly"
               ( _1 :: _2 )
# 446 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 43 "parser.mly"
                             ( [_1] )
# 453 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 44 "parser.mly"
                               ( _1 @ [_3] )
# 461 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 47 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 470 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 48 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 478 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 49 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 486 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 50 "parser.mly"
                                                        ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 495 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 51 "parser.mly"
                                                              ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 504 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 52 "parser.mly"
                                                              ( Global (mk_stmt1 1 (UnsafeSend (_2, _4, _6))) )
# 513 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 53 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 521 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 56 "parser.mly"
          ( [_1] )
# 528 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 57 "parser.mly"
                 ( _1 :: _2 )
# 536 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 60 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 544 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 552 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 64 "parser.mly"
                ( [_1] )
# 559 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 65 "parser.mly"
                        ( _1 :: _2 )
# 567 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 68 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = mk_stmt1 2 (Seq _7) } )
# 577 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
       ( [] )
# 583 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 73 "parser.mly"
       ( [_1] )
# 590 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 74 "parser.mly"
                        ( _1::_3 )
# 598 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 77 "parser.mly"
         ( [_1] )
# 605 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 78 "parser.mly"
               ( _1 :: _2 )
# 613 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 81 "parser.mly"
                   ( _1::_2 )
# 621 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "parser.mly"
                   ( [] )
# 627 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 635 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 86 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 643 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 87 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 650 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 88 "parser.mly"
                                                  ( mk_stmt1 4 (Send("self", _4, _6)) )
# 658 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 89 "parser.mly"
                                                    ( mk_stmt1 4 (Send ("sender", _4, _6)) )
# 666 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 90 "parser.mly"
                                                ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 675 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 91 "parser.mly"
                                                      ( mk_stmt1 2 (UnsafeSend (_2, _4, _6)) )
# 684 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 92 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 692 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 93 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 701 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 94 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 709 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 95 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 716 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 724 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 97 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 733 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 98 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 741 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 99 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 749 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 100 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 756 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'select_cases) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'select_timeout_opt) in
    Obj.repr(
# 101 "parser.mly"
                                                         ( mk_stmt1 3 (Select(_3, _4)) )
# 764 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 104 "parser.mly"
                             ( _1 @ [_2] )
# 772 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 105 "parser.mly"
                             ( [] )
# 778 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 108 "parser.mly"
                             ( _1 @ [_2] )
# 786 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 109 "parser.mly"
                             ( [] )
# 792 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'select_pat) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 113 "parser.mly"
    ( { pat = _2; body = mk_stmt1 5 (Seq(_5)) } )
# 800 "parser.ml"
               : 'select_case))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opt_id_list) in
    Obj.repr(
# 117 "parser.mly"
    ( { meth = _1; vars = _3 } )
# 808 "parser.ml"
               : 'select_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 120 "parser.mly"
            ( _1 )
# 815 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 121 "parser.mly"
                ( [] )
# 821 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 124 "parser.mly"
                         ( [_1] )
# 828 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 125 "parser.mly"
                      ( _1 @ [_3] )
# 836 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 129 "parser.mly"
      ( (Some _2, Some (mk_stmt1 5 (Seq _5))) )
# 844 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 131 "parser.mly"
      ( (None, None) )
# 850 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 134 "parser.mly"
                 ( [] )
# 856 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 135 "parser.mly"
                 ( _1 )
# 863 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 138 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 871 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 139 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 880 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 142 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 887 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 143 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 894 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 144 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 901 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 145 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 908 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 146 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 916 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 147 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 924 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 148 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 932 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 149 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 940 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 150 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 948 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 151 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 956 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 152 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 964 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 153 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 972 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 154 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 980 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 155 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 988 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 156 "parser.mly"
                       ( _2 )
# 995 "parser.ml"
               : 'expr))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.program)
