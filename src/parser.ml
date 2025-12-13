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
  | OBJECT
  | METHOD
  | FLOAT
  | CALL
  | SEND
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
  | SELF
  | SENDER
  | CLASS
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
# 69 "parser.ml"
let yytransl_const = [|
  261 (* OBJECT *);
  262 (* METHOD *);
  263 (* FLOAT *);
  264 (* CALL *);
  265 (* SEND *);
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
  284 (* SELF *);
  285 (* SENDER *);
  286 (* CLASS *);
    0 (* EOF *);
  287 (* NEW *);
  288 (* VAR *);
  289 (* EQ *);
  290 (* DOT *);
  291 (* BECOME *);
    0|]

let yytransl_block = [|
  257 (* ID *);
  258 (* FLOATLIT *);
  259 (* INTLIT *);
  260 (* STRINGLIT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\004\000\004\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\006\000\006\000\010\000\010\000\007\000\
\007\000\011\000\012\000\012\000\012\000\013\000\013\000\015\000\
\015\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\009\000\009\000\008\000\008\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\006\000\005\000\003\000\007\000\006\000\005\000\
\009\000\008\000\005\000\001\000\002\000\005\000\005\000\001\000\
\002\000\008\000\000\000\001\000\003\000\001\000\002\000\002\000\
\000\000\004\000\006\000\005\000\008\000\008\000\008\000\006\000\
\004\000\005\000\003\000\005\000\009\000\005\000\006\000\005\000\
\000\000\001\000\003\000\005\000\001\000\001\000\001\000\001\000\
\003\000\003\000\003\000\003\000\005\000\004\000\003\000\003\000\
\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\066\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\
\000\000\000\000\001\000\000\000\006\000\000\000\000\000\013\000\
\000\000\053\000\055\000\054\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\065\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\019\000\000\000\000\000\000\000\
\000\000\012\000\021\000\025\000\000\000\000\000\010\000\000\000\
\016\000\000\000\000\000\015\000\062\000\000\000\000\000\000\000\
\000\000\011\000\000\000\009\000\000\000\000\000\014\000\061\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\022\000\023\000\018\000\000\000\052\000\029\000\000\000\
\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\026\000\031\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\032\000\043\000\000\000\000\000\
\034\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\041\000\000\000\000\000\000\000\000\000\046\000\042\000\
\036\000\000\000\000\000\000\000\000\000\000\000\000\000\044\000\
\048\000\000\000\035\000\000\000\000\000\000\000\040\000\000\000\
\047\000\000\000\000\000\000\000\000\000\039\000\037\000\038\000\
\000\000\045\000"

let yydgoto = "\002\000\
\009\000\010\000\011\000\031\000\032\000\055\000\056\000\065\000\
\033\000\057\000\058\000\106\000\131\000\132\000\143\000"

let yysindex = "\009\000\
\036\255\000\000\005\000\050\255\062\255\068\255\076\255\081\255\
\000\000\056\000\043\255\000\000\118\255\093\255\066\255\071\255\
\067\255\085\255\000\000\049\255\000\000\090\255\093\255\000\000\
\095\255\000\000\000\000\000\000\093\255\121\255\098\255\045\000\
\105\255\007\255\126\255\007\255\115\255\000\000\135\255\131\255\
\093\255\246\254\119\255\093\255\093\255\093\255\093\255\093\255\
\093\255\093\255\123\255\148\255\160\255\161\255\144\255\141\255\
\251\254\144\255\151\255\144\255\164\255\189\255\162\255\185\255\
\172\255\178\255\186\255\000\000\093\255\045\000\080\255\080\255\
\016\255\016\255\045\000\045\000\000\000\188\255\200\255\202\255\
\187\255\000\000\000\000\000\000\093\255\199\255\000\000\203\255\
\000\000\093\255\201\255\000\000\000\000\207\255\228\255\093\255\
\093\255\000\000\209\255\000\000\093\255\253\255\000\000\000\000\
\212\255\211\255\001\000\013\000\214\255\219\255\135\255\228\255\
\221\255\000\000\000\000\000\000\220\255\000\000\000\000\025\255\
\000\000\044\255\244\255\246\255\002\255\093\255\093\255\025\255\
\251\255\252\255\239\255\025\255\093\255\093\255\006\000\236\255\
\232\255\248\255\008\000\166\255\241\255\025\255\015\000\039\000\
\038\000\000\000\000\000\017\000\048\000\093\255\083\255\069\000\
\072\000\073\000\025\255\025\255\000\000\000\000\128\255\089\255\
\000\000\053\000\029\000\054\000\058\000\060\000\061\000\062\000\
\071\000\000\000\083\000\033\000\064\000\065\000\000\000\000\000\
\000\000\066\000\093\255\093\255\093\255\025\255\067\000\000\000\
\000\000\068\000\000\000\070\000\074\000\075\000\000\000\093\255\
\000\000\076\000\077\000\078\000\082\000\000\000\000\000\000\000\
\080\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\085\001\000\000\000\000\084\000\000\000\000\000\
\000\000\000\000\000\000\089\001\000\000\000\000\084\000\000\000\
\149\255\000\000\000\000\000\000\000\000\000\000\086\000\028\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\084\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\087\000\088\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\084\000\055\255\210\255\225\255\
\180\255\195\255\130\255\240\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\084\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\089\000\000\000\
\000\000\000\000\000\000\000\000\084\000\090\000\000\000\000\000\
\091\000\000\000\000\000\000\000\000\000\000\000\000\000\089\000\
\000\000\000\000\000\000\000\000\049\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\092\000\
\000\000\000\000\000\000\093\000\000\000\084\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\092\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\084\000\084\000\084\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\084\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\049\000\000\000"

let yygindex = "\000\000\
\000\000\063\000\000\000\000\000\231\255\004\000\085\000\239\000\
\233\255\000\000\000\000\241\000\222\000\129\255\213\000"

let yytablesize = 372
let yytable = "\040\000\
\142\000\053\000\137\000\042\000\012\000\045\000\046\000\047\000\
\048\000\001\000\068\000\063\000\052\000\053\000\142\000\049\000\
\050\000\067\000\070\000\071\000\072\000\073\000\074\000\075\000\
\076\000\122\000\054\000\169\000\170\000\138\000\139\000\123\000\
\124\000\125\000\126\000\003\000\004\000\127\000\054\000\060\000\
\005\000\049\000\050\000\004\000\006\000\094\000\128\000\005\000\
\007\000\004\000\013\000\006\000\007\000\005\000\191\000\019\000\
\129\000\006\000\133\000\130\000\083\000\099\000\015\000\134\000\
\102\000\007\000\020\000\008\000\016\000\014\000\107\000\108\000\
\007\000\021\000\008\000\008\000\017\000\110\000\007\000\008\000\
\008\000\018\000\038\000\025\000\026\000\027\000\028\000\034\000\
\036\000\025\000\026\000\027\000\028\000\025\000\026\000\027\000\
\028\000\047\000\048\000\037\000\140\000\141\000\029\000\164\000\
\035\000\049\000\050\000\148\000\029\000\173\000\149\000\039\000\
\029\000\030\000\041\000\025\000\026\000\027\000\028\000\030\000\
\061\000\043\000\044\000\030\000\163\000\051\000\059\000\165\000\
\025\000\026\000\027\000\028\000\022\000\172\000\029\000\064\000\
\174\000\023\000\069\000\081\000\063\000\024\000\084\000\063\000\
\086\000\062\000\077\000\029\000\078\000\052\000\063\000\066\000\
\063\000\063\000\063\000\188\000\189\000\190\000\171\000\056\000\
\079\000\080\000\056\000\082\000\056\000\056\000\056\000\056\000\
\197\000\056\000\085\000\056\000\056\000\056\000\056\000\056\000\
\155\000\045\000\046\000\047\000\048\000\045\000\046\000\047\000\
\048\000\089\000\087\000\049\000\050\000\088\000\059\000\049\000\
\050\000\059\000\091\000\059\000\059\000\059\000\059\000\090\000\
\059\000\092\000\059\000\059\000\059\000\060\000\093\000\095\000\
\060\000\098\000\060\000\060\000\060\000\060\000\096\000\060\000\
\097\000\060\000\060\000\060\000\057\000\100\000\101\000\057\000\
\103\000\057\000\057\000\104\000\105\000\109\000\057\000\113\000\
\057\000\057\000\057\000\058\000\112\000\116\000\058\000\117\000\
\058\000\058\000\120\000\121\000\135\000\058\000\136\000\058\000\
\058\000\058\000\064\000\144\000\145\000\064\000\156\000\151\000\
\045\000\046\000\047\000\048\000\064\000\146\000\064\000\064\000\
\064\000\152\000\049\000\050\000\045\000\046\000\047\000\048\000\
\045\000\046\000\047\000\048\000\150\000\111\000\049\000\050\000\
\114\000\153\000\049\000\050\000\045\000\046\000\047\000\048\000\
\045\000\046\000\047\000\048\000\115\000\158\000\049\000\050\000\
\161\000\154\000\049\000\050\000\045\000\046\000\047\000\048\000\
\045\000\046\000\047\000\048\000\176\000\159\000\049\000\050\000\
\184\000\160\000\049\000\050\000\045\000\046\000\047\000\048\000\
\061\000\061\000\061\000\061\000\162\000\166\000\049\000\050\000\
\167\000\168\000\061\000\061\000\175\000\177\000\178\000\179\000\
\180\000\181\000\182\000\183\000\003\000\186\000\192\000\185\000\
\004\000\187\000\194\000\193\000\020\000\118\000\195\000\196\000\
\119\000\147\000\157\000\198\000\199\000\200\000\201\000\202\000\
\049\000\000\000\050\000\000\000\000\000\027\000\024\000\028\000\
\051\000\000\000\033\000\030\000"

let yycheck = "\023\000\
\128\000\007\001\001\001\029\000\000\000\016\001\017\001\018\001\
\019\001\001\000\021\001\037\000\006\001\007\001\142\000\026\001\
\027\001\041\000\044\000\045\000\046\000\047\000\048\000\049\000\
\050\000\001\001\032\001\155\000\156\000\028\001\029\001\007\001\
\008\001\009\001\010\001\000\001\001\001\013\001\032\001\036\000\
\005\001\026\001\027\001\001\001\009\001\069\000\022\001\005\001\
\021\001\001\001\001\001\009\001\025\001\005\001\182\000\000\000\
\032\001\009\001\015\001\035\001\057\000\085\000\001\001\020\001\
\090\000\030\001\024\001\032\001\001\001\020\001\096\000\097\000\
\030\001\011\000\032\001\021\001\001\001\101\000\030\001\025\001\
\032\001\001\001\020\000\001\001\002\001\003\001\004\001\022\001\
\022\001\001\001\002\001\003\001\004\001\001\001\002\001\003\001\
\004\001\018\001\019\001\015\001\126\000\127\000\020\001\021\001\
\034\001\026\001\027\001\133\000\020\001\021\001\134\000\022\001\
\020\001\031\001\020\001\001\001\002\001\003\001\004\001\031\001\
\036\000\001\001\025\001\031\001\150\000\021\001\001\001\151\000\
\001\001\002\001\003\001\004\001\015\001\159\000\020\001\001\001\
\160\000\020\001\020\001\055\000\011\001\024\001\058\000\014\001\
\060\000\031\001\024\001\020\001\001\001\006\001\021\001\021\001\
\023\001\024\001\025\001\179\000\180\000\181\000\031\001\011\001\
\001\001\001\001\014\001\023\001\016\001\017\001\018\001\019\001\
\192\000\021\001\020\001\023\001\024\001\025\001\026\001\027\001\
\011\001\016\001\017\001\018\001\019\001\016\001\017\001\018\001\
\019\001\024\001\023\001\026\001\027\001\001\001\011\001\026\001\
\027\001\014\001\023\001\016\001\017\001\018\001\019\001\015\001\
\021\001\024\001\023\001\024\001\025\001\011\001\021\001\020\001\
\014\001\023\001\016\001\017\001\018\001\019\001\015\001\021\001\
\015\001\023\001\024\001\025\001\011\001\023\001\020\001\014\001\
\024\001\016\001\017\001\021\001\001\001\021\001\021\001\021\001\
\023\001\024\001\025\001\011\001\025\001\024\001\014\001\021\001\
\016\001\017\001\022\001\024\001\001\001\021\001\001\001\023\001\
\024\001\025\001\011\001\001\001\001\001\014\001\014\001\020\001\
\016\001\017\001\018\001\019\001\021\001\023\001\023\001\024\001\
\025\001\034\001\026\001\027\001\016\001\017\001\018\001\019\001\
\016\001\017\001\018\001\019\001\015\001\025\001\026\001\027\001\
\024\001\034\001\026\001\027\001\016\001\017\001\018\001\019\001\
\016\001\017\001\018\001\019\001\024\001\023\001\026\001\027\001\
\024\001\034\001\026\001\027\001\016\001\017\001\018\001\019\001\
\016\001\017\001\018\001\019\001\024\001\015\001\026\001\027\001\
\024\001\020\001\026\001\027\001\016\001\017\001\018\001\019\001\
\016\001\017\001\018\001\019\001\021\001\001\001\026\001\027\001\
\001\001\001\001\026\001\027\001\024\001\024\001\021\001\020\001\
\020\001\020\001\012\001\001\001\000\000\021\001\020\001\024\001\
\000\000\024\001\021\001\024\001\006\001\111\000\021\001\021\001\
\112\000\132\000\142\000\024\001\024\001\024\001\021\001\024\001\
\021\001\255\255\021\001\255\255\255\255\021\001\023\001\021\001\
\023\001\255\255\023\001\023\001"

let yynames_const = "\
  OBJECT\000\
  METHOD\000\
  FLOAT\000\
  CALL\000\
  SEND\000\
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
  SELF\000\
  SENDER\000\
  CLASS\000\
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
# 32 "parser.mly"
              ( _1 )
# 374 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 33 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 380 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 36 "parser.mly"
         ( [_1] )
# 387 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 37 "parser.mly"
                   ( [_1] )
# 394 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 38 "parser.mly"
                         ( _1 :: _3 )
# 402 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 39 "parser.mly"
               ( _1 :: _2 )
# 410 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                             ( [_1] )
# 417 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 43 "parser.mly"
                               ( _1 @ [_3] )
# 425 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 46 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 434 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 47 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 442 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 48 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 451 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 49 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 459 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 50 "parser.mly"
                                           ( Instantiate (_1, _2) )
# 467 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'inits) in
    Obj.repr(
# 51 "parser.mly"
                                                 ( InstantiateInit (_1, _2, _5) )
# 476 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 52 "parser.mly"
                                                 ( InstantiateArgs (_1, _2, _4) )
# 485 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 53 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 493 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 54 "parser.mly"
                                                        ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 502 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 55 "parser.mly"
                                                        ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 511 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 56 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 519 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 59 "parser.mly"
          ( [_1] )
# 526 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 60 "parser.mly"
                 ( _1 :: _2 )
# 534 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 542 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 550 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 67 "parser.mly"
                ( [_1] )
# 557 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 68 "parser.mly"
                        ( _1 :: _2 )
# 565 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 71 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = mk_stmt1 2 (Seq _7) } )
# 575 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
         ( [] )
# 581 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 76 "parser.mly"
       ( [_1] )
# 588 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 77 "parser.mly"
                        ( _1::_3 )
# 596 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 80 "parser.mly"
         ( [_1] )
# 603 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 81 "parser.mly"
               ( _1 :: _2 )
# 611 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 84 "parser.mly"
                   ( _1::_2 )
# 619 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 85 "parser.mly"
                   ( [] )
# 625 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 88 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 633 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 89 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 641 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 90 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 648 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 91 "parser.mly"
                                                  ( mk_stmt1 4 (Send("self", _4, _6)) )
# 656 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 92 "parser.mly"
                                                    ( mk_stmt1 4 (Send ("sender", _4, _6)) )
# 664 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 93 "parser.mly"
                                                ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 673 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 94 "parser.mly"
                                ( mk_stmt1 2 (If(_2, _4, _6)) )
# 682 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 95 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 690 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                                   ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 698 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 97 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 705 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 713 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 99 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 722 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 100 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 730 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 101 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 738 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 102 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 745 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 105 "parser.mly"
                 ( [] )
# 751 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 106 "parser.mly"
                 ( _1 )
# 758 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 766 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 110 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 775 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 113 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 782 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 114 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 789 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 115 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 796 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 116 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 803 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 117 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 811 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 819 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 119 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 827 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 120 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 835 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 121 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 843 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 122 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 851 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 123 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 859 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 124 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 867 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 125 "parser.mly"
                       ( _2 )
# 874 "parser.ml"
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
