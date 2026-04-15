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
  | REMOTE
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
# 76 "parser.ml"
let yytransl_const = [|
  261 (* METHOD *);
  262 (* FLOAT *);
  263 (* CALL *);
  264 (* SEND *);
  265 (* UNSAFESEND *);
  266 (* REMOTE *);
  267 (* IF *);
  268 (* THEN *);
  269 (* ELSE *);
  270 (* WHILE *);
  271 (* DO *);
  272 (* ASSIGN *);
  273 (* PLUS *);
  274 (* MINUS *);
  275 (* TIMES *);
  276 (* DIV *);
  277 (* LPAREN *);
  278 (* RPAREN *);
  279 (* LBRACE *);
  280 (* RBRACE *);
  281 (* SEMICOLON *);
  282 (* COMMA *);
  283 (* GE *);
  284 (* LE *);
  285 (* GT *);
  286 (* LT *);
  287 (* SELF *);
  288 (* SENDER *);
  289 (* CLASS *);
  290 (* SELECT *);
  291 (* CASE *);
  292 (* TIMEOUT *);
  293 (* ARROW *);
    0 (* EOF *);
  294 (* NEW *);
  295 (* VAR *);
  296 (* EQ *);
  297 (* DOT *);
  298 (* BECOME *);
    0|]

let yytransl_block = [|
  257 (* ID *);
  258 (* FLOATLIT *);
  259 (* INTLIT *);
  260 (* STRINGLIT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\005\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\007\000\
\007\000\010\000\010\000\008\000\008\000\011\000\012\000\012\000\
\012\000\002\000\002\000\013\000\013\000\015\000\015\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\016\000\016\000\016\000\016\000\018\000\019\000\020\000\020\000\
\021\000\021\000\017\000\017\000\009\000\009\000\022\000\022\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\005\000\009\000\008\000\008\000\005\000\001\000\
\002\000\005\000\005\000\001\000\002\000\008\000\000\000\001\000\
\003\000\001\000\006\000\001\000\002\000\002\000\000\000\004\000\
\006\000\005\000\008\000\008\000\008\000\008\000\005\000\007\000\
\004\000\003\000\005\000\009\000\005\000\006\000\005\000\005\000\
\002\000\000\000\002\000\000\000\006\000\004\000\001\000\000\000\
\001\000\003\000\006\000\000\000\000\000\001\000\003\000\005\000\
\001\000\001\000\001\000\001\000\003\000\003\000\003\000\003\000\
\005\000\004\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\080\000\000\000\000\000\002\000\000\000\026\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\006\000\000\000\065\000\
\067\000\066\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\005\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\079\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\015\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\010\000\017\000\021\000\000\000\011\000\074\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
\000\000\073\000\027\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\013\000\014\000\000\000\000\000\018\000\019\000\
\000\000\025\000\000\000\012\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\050\000\000\000\000\000\022\000\029\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\030\000\042\000\000\000\000\000\000\000\032\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\041\000\
\000\000\000\000\000\000\049\000\000\000\000\000\000\000\000\000\
\045\000\034\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\048\000\000\000\043\000\047\000\000\000\
\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\046\000\000\000\000\000\000\000\000\000\040\000\
\057\000\000\000\000\000\000\000\000\000\000\000\035\000\036\000\
\037\000\038\000\054\000\000\000\000\000\000\000\000\000\058\000\
\053\000\059\000\044\000"

let yydgoto = "\002\000\
\009\000\016\000\010\000\011\000\029\000\030\000\057\000\058\000\
\031\000\059\000\060\000\103\000\127\000\128\000\139\000\156\000\
\171\000\172\000\186\000\210\000\211\000\000\000"

let yysindex = "\024\000\
\005\255\000\000\049\000\040\255\096\255\096\255\063\255\090\255\
\000\000\093\000\027\255\000\000\081\255\000\000\073\255\057\255\
\058\255\102\255\088\255\000\000\062\255\000\000\109\255\000\000\
\000\000\000\000\081\255\112\255\106\255\001\000\126\255\163\255\
\149\255\168\255\003\255\120\255\000\000\081\255\178\255\160\255\
\081\255\081\255\081\255\081\255\081\255\081\255\081\255\081\255\
\081\255\154\255\156\255\169\255\197\255\198\255\226\255\227\255\
\224\255\208\255\006\255\224\255\229\255\192\255\219\255\000\000\
\081\255\001\000\047\000\047\000\186\255\186\255\001\000\001\000\
\001\000\001\000\000\000\239\255\081\255\081\255\221\255\228\255\
\007\000\222\255\000\000\000\000\000\000\248\255\000\000\000\000\
\014\000\016\000\017\000\018\000\036\000\081\255\081\255\000\000\
\081\255\000\000\000\000\022\000\027\000\028\000\019\000\206\255\
\220\255\033\000\000\000\000\000\036\000\041\000\000\000\000\000\
\034\000\000\000\066\255\000\000\035\255\069\000\080\255\096\255\
\050\000\081\255\066\255\056\000\071\000\072\000\058\000\066\255\
\081\255\081\255\062\000\045\000\046\000\051\000\052\000\081\255\
\174\255\066\255\060\000\000\000\074\000\070\000\000\000\000\000\
\234\255\073\000\125\255\095\000\096\000\097\000\098\000\238\255\
\066\255\000\000\000\000\043\255\136\255\132\255\000\000\075\000\
\076\000\080\000\082\000\083\000\084\000\085\000\066\255\000\000\
\106\000\091\000\086\000\000\000\107\000\253\255\087\000\089\000\
\000\000\000\000\088\000\081\255\081\255\081\255\081\255\101\000\
\094\000\079\000\081\000\000\000\099\000\000\000\000\000\092\000\
\000\000\100\000\102\000\103\000\104\000\066\255\108\000\105\000\
\109\000\081\255\000\000\110\000\111\000\112\000\113\000\000\000\
\000\000\117\000\114\000\066\255\066\255\119\000\000\000\000\000\
\000\000\000\000\000\000\118\000\120\000\121\000\122\000\000\000\
\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\121\001\000\000\124\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\123\001\000\000\158\255\000\000\
\000\000\000\000\000\000\000\000\126\000\007\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\124\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\125\000\127\000\000\000\000\000\000\000\000\000\
\124\000\050\255\134\255\063\000\031\000\043\000\028\255\092\255\
\140\255\146\255\000\000\000\000\124\000\124\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\128\000\000\000\000\000\000\000\
\124\000\000\000\000\000\000\000\000\000\130\000\000\000\000\000\
\000\000\000\000\000\000\000\000\128\000\000\000\000\000\000\000\
\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\129\000\000\000\000\000\000\000\000\000\131\000\
\000\000\124\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\129\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\132\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\124\000\124\000\124\000\124\000\023\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\135\000\000\000\
\000\000\124\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\136\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\015\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\252\255\037\000\000\000\000\000\230\255\068\001\203\255\
\218\255\000\000\000\000\020\001\131\255\144\255\249\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 414
let yytable = "\063\000\
\039\000\017\000\144\000\082\000\003\000\004\000\085\000\054\000\
\055\000\062\000\138\000\055\000\005\000\006\000\066\000\067\000\
\068\000\069\000\070\000\071\000\072\000\073\000\074\000\039\000\
\001\000\138\000\089\000\004\000\007\000\039\000\039\000\039\000\
\007\000\039\000\005\000\006\000\039\000\007\000\091\000\092\000\
\168\000\056\000\075\000\008\000\056\000\039\000\039\000\022\000\
\012\000\075\000\129\000\021\000\075\000\075\000\184\000\130\000\
\039\000\037\000\106\000\007\000\013\000\039\000\004\000\018\000\
\039\000\008\000\117\000\104\000\105\000\005\000\006\000\008\000\
\118\000\119\000\120\000\008\000\121\000\169\000\170\000\122\000\
\014\000\023\000\024\000\025\000\026\000\208\000\221\000\222\000\
\123\000\015\000\019\000\146\000\020\000\032\000\007\000\137\000\
\014\000\033\000\034\000\124\000\008\000\027\000\145\000\036\000\
\125\000\015\000\076\000\126\000\162\000\152\000\132\000\133\000\
\040\000\076\000\134\000\135\000\076\000\076\000\028\000\176\000\
\023\000\024\000\025\000\026\000\035\000\023\000\024\000\025\000\
\026\000\038\000\174\000\041\000\023\000\024\000\025\000\026\000\
\023\000\024\000\025\000\026\000\027\000\194\000\195\000\196\000\
\197\000\027\000\161\000\050\000\069\000\052\000\069\000\069\000\
\027\000\175\000\077\000\069\000\027\000\061\000\069\000\069\000\
\078\000\077\000\028\000\214\000\077\000\077\000\051\000\078\000\
\053\000\028\000\078\000\078\000\068\000\173\000\068\000\068\000\
\068\000\068\000\075\000\068\000\065\000\076\000\068\000\068\000\
\068\000\068\000\068\000\068\000\153\000\077\000\042\000\043\000\
\044\000\045\000\042\000\043\000\044\000\045\000\079\000\064\000\
\046\000\047\000\048\000\049\000\046\000\047\000\048\000\049\000\
\042\000\043\000\044\000\045\000\046\000\047\000\048\000\049\000\
\087\000\078\000\046\000\047\000\048\000\049\000\042\000\043\000\
\044\000\045\000\080\000\081\000\054\000\086\000\111\000\083\000\
\046\000\047\000\048\000\049\000\042\000\043\000\044\000\045\000\
\088\000\093\000\090\000\094\000\112\000\096\000\046\000\047\000\
\048\000\049\000\042\000\043\000\044\000\045\000\042\000\043\000\
\044\000\045\000\159\000\167\000\046\000\047\000\048\000\049\000\
\046\000\047\000\048\000\049\000\097\000\042\000\043\000\044\000\
\045\000\042\000\043\000\044\000\045\000\190\000\095\000\046\000\
\047\000\048\000\049\000\046\000\047\000\048\000\049\000\073\000\
\073\000\073\000\073\000\098\000\102\000\099\000\100\000\101\000\
\110\000\073\000\073\000\073\000\073\000\071\000\107\000\071\000\
\071\000\071\000\071\000\108\000\071\000\109\000\113\000\071\000\
\071\000\072\000\116\000\072\000\072\000\072\000\072\000\115\000\
\072\000\044\000\045\000\072\000\072\000\131\000\136\000\141\000\
\142\000\046\000\047\000\048\000\049\000\070\000\140\000\070\000\
\070\000\143\000\147\000\155\000\070\000\148\000\149\000\070\000\
\070\000\157\000\158\000\150\000\151\000\187\000\160\000\163\000\
\164\000\165\000\166\000\177\000\178\000\179\000\180\000\181\000\
\182\000\183\000\185\000\189\000\209\000\188\000\192\000\191\000\
\193\000\198\000\199\000\200\000\203\000\201\000\224\000\202\000\
\003\000\204\000\004\000\205\000\206\000\207\000\084\000\212\000\
\114\000\016\000\154\000\213\000\000\000\000\000\215\000\216\000\
\217\000\218\000\219\000\220\000\223\000\000\000\000\000\225\000\
\226\000\061\000\227\000\062\000\000\000\023\000\020\000\024\000\
\031\000\000\000\028\000\060\000\056\000\055\000"

let yycheck = "\038\000\
\027\000\006\000\128\000\057\000\000\001\001\001\060\000\005\001\
\006\001\036\000\123\000\006\001\008\001\009\001\041\000\042\000\
\043\000\044\000\045\000\046\000\047\000\048\000\049\000\001\001\
\001\000\138\000\065\000\001\001\022\001\007\001\008\001\009\001\
\026\001\011\001\008\001\009\001\014\001\033\001\077\000\078\000\
\153\000\039\001\015\001\039\001\039\001\023\001\024\001\011\000\
\000\000\022\001\016\001\025\001\025\001\026\001\167\000\021\001\
\034\001\021\000\097\000\033\001\021\001\039\001\001\001\001\001\
\042\001\039\001\001\001\094\000\095\000\008\001\009\001\022\001\
\007\001\008\001\009\001\026\001\011\001\035\001\036\001\014\001\
\001\001\001\001\002\001\003\001\004\001\198\000\212\000\213\000\
\023\001\010\001\001\001\130\000\000\000\021\001\033\001\122\000\
\001\001\041\001\041\001\034\001\039\001\021\001\129\000\016\001\
\039\001\010\001\015\001\042\001\147\000\136\000\031\001\032\001\
\001\001\022\001\119\000\120\000\025\001\026\001\038\001\158\000\
\001\001\002\001\003\001\004\001\023\001\001\001\002\001\003\001\
\004\001\021\001\157\000\026\001\001\001\002\001\003\001\004\001\
\001\001\002\001\003\001\004\001\021\001\180\000\181\000\182\000\
\183\000\021\001\022\001\022\001\015\001\001\001\017\001\018\001\
\021\001\022\001\015\001\022\001\021\001\038\001\025\001\026\001\
\015\001\022\001\038\001\202\000\025\001\026\001\004\001\022\001\
\001\001\038\001\025\001\026\001\015\001\038\001\017\001\018\001\
\019\001\020\001\025\001\022\001\021\001\026\001\025\001\026\001\
\027\001\028\001\029\001\030\001\015\001\021\001\017\001\018\001\
\019\001\020\001\017\001\018\001\019\001\020\001\001\001\022\001\
\027\001\028\001\029\001\030\001\027\001\028\001\029\001\030\001\
\017\001\018\001\019\001\020\001\027\001\028\001\029\001\030\001\
\025\001\021\001\027\001\028\001\029\001\030\001\017\001\018\001\
\019\001\020\001\001\001\001\001\005\001\001\001\025\001\024\001\
\027\001\028\001\029\001\030\001\017\001\018\001\019\001\020\001\
\022\001\021\001\004\001\016\001\025\001\024\001\027\001\028\001\
\029\001\030\001\017\001\018\001\019\001\020\001\017\001\018\001\
\019\001\020\001\025\001\022\001\027\001\028\001\029\001\030\001\
\027\001\028\001\029\001\030\001\021\001\017\001\018\001\019\001\
\020\001\017\001\018\001\019\001\020\001\025\001\016\001\027\001\
\028\001\029\001\030\001\027\001\028\001\029\001\030\001\017\001\
\018\001\019\001\020\001\022\001\001\001\022\001\022\001\022\001\
\022\001\027\001\028\001\029\001\030\001\015\001\025\001\017\001\
\018\001\019\001\020\001\025\001\022\001\026\001\022\001\025\001\
\026\001\015\001\025\001\017\001\018\001\019\001\020\001\023\001\
\022\001\019\001\020\001\025\001\026\001\001\001\021\001\001\001\
\001\001\027\001\028\001\029\001\030\001\015\001\023\001\017\001\
\018\001\024\001\021\001\024\001\022\001\041\001\041\001\025\001\
\026\001\016\001\021\001\041\001\041\001\003\001\022\001\001\001\
\001\001\001\001\001\001\025\001\025\001\022\001\021\001\021\001\
\021\001\021\001\001\001\001\001\001\001\024\001\022\001\025\001\
\025\001\013\001\021\001\037\001\025\001\037\001\001\001\021\001\
\000\000\022\001\000\000\022\001\022\001\022\001\059\000\023\001\
\109\000\005\001\138\000\023\001\255\255\255\255\025\001\025\001\
\025\001\025\001\022\001\026\001\022\001\255\255\255\255\024\001\
\024\001\022\001\025\001\022\001\255\255\022\001\024\001\022\001\
\024\001\255\255\024\001\024\001\022\001\022\001"

let yynames_const = "\
  METHOD\000\
  FLOAT\000\
  CALL\000\
  SEND\000\
  UNSAFESEND\000\
  REMOTE\000\
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
# 418 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 34 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 424 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 37 "parser.mly"
         ( [_1] )
# 431 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 38 "parser.mly"
                   ( [_1] )
# 438 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 39 "parser.mly"
                         ( _1 :: _3 )
# 446 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 40 "parser.mly"
               ( _1 :: _2 )
# 454 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 43 "parser.mly"
                             ( [_1] )
# 461 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 44 "parser.mly"
                               ( _1 @ [_3] )
# 469 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 47 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 478 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 48 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 486 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 49 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 494 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 51 "parser.mly"
    ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 503 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 52 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 512 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 53 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (UnsafeSend (_2, _4, _6))) )
# 521 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 54 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 529 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 57 "parser.mly"
          ( [_1] )
# 536 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 58 "parser.mly"
                 ( _1 :: _2 )
# 544 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 61 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 552 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 560 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 65 "parser.mly"
                ( [_1] )
# 567 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 66 "parser.mly"
                        ( _1 :: _2 )
# 575 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 70 "parser.mly"
    ( { mname = _2; params = _4; body = mk_stmt1 2 (Seq _7) } )
# 584 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 73 "parser.mly"
       ( [] )
# 590 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 74 "parser.mly"
       ( [_1] )
# 597 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 75 "parser.mly"
                        ( _1::_3 )
# 605 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 78 "parser.mly"
                                                      ( LocalTarget _1 )
# 612 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 79 "parser.mly"
                                                      ( RemoteTarget (_3, _5) )
# 620 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 82 "parser.mly"
         ( [_1] )
# 627 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 83 "parser.mly"
               ( _1 :: _2 )
# 635 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 86 "parser.mly"
                   ( _1::_2 )
# 643 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 87 "parser.mly"
                   ( [] )
# 649 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 90 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 657 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 91 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 665 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 92 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 672 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 93 "parser.mly"
                                                  ( mk_stmt1 4 (Send(LocalTarget "self", _4, _6)) )
# 680 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 94 "parser.mly"
                                                    ( mk_stmt1 4 (Send (LocalTarget "sender", _4, _6)) )
# 688 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 95 "parser.mly"
                                                         ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 697 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 96 "parser.mly"
                                                               ( mk_stmt1 2 (UnsafeSend (_2, _4, _6)) )
# 706 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 97 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 714 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 98 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 723 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 99 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 731 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 100 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 738 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 101 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 746 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 102 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 755 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 103 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 763 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 104 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 771 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 105 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 778 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'select_cases) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'select_timeout_opt) in
    Obj.repr(
# 106 "parser.mly"
                                                         ( mk_stmt1 3 (Select(_3, _4)) )
# 786 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 109 "parser.mly"
                             ( _1 @ [_2] )
# 794 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 110 "parser.mly"
                             ( [] )
# 800 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 113 "parser.mly"
                             ( _1 @ [_2] )
# 808 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 114 "parser.mly"
                             ( [] )
# 814 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'select_pat) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 118 "parser.mly"
    ( { pat = _2; body = mk_stmt1 5 (Seq(_5)) } )
# 822 "parser.ml"
               : 'select_case))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opt_id_list) in
    Obj.repr(
# 122 "parser.mly"
    ( { meth = _1; vars = _3 } )
# 830 "parser.ml"
               : 'select_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 125 "parser.mly"
            ( _1 )
# 837 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 126 "parser.mly"
                ( [] )
# 843 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 129 "parser.mly"
                         ( [_1] )
# 850 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 130 "parser.mly"
                      ( _1 @ [_3] )
# 858 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 134 "parser.mly"
      ( (Some _2, Some (mk_stmt1 5 (Seq _5))) )
# 866 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 136 "parser.mly"
      ( (None, None) )
# 872 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 139 "parser.mly"
                 ( [] )
# 878 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 140 "parser.mly"
                 ( _1 )
# 885 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 143 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 893 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 144 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 902 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 147 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 909 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 148 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 916 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 149 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 923 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 150 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 930 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 151 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 938 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 152 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 946 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 153 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 954 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 154 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 962 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 155 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 970 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 156 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 978 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 157 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 986 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 158 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 994 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 159 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 1002 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 160 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 1010 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 161 "parser.mly"
                       ( _2 )
# 1017 "parser.ml"
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
