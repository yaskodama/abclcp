type token =
  | ID of (
# 6 "parser.mly"
        string
# 6 "parser.ml"
)
  | FLOATLIT of (
# 7 "parser.mly"
        float
# 11 "parser.ml"
)
  | INTLIT of (
# 8 "parser.mly"
        int
# 16 "parser.ml"
)
  | STRINGLIT of (
# 9 "parser.mly"
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

open Parsing
let _ = parse_error;;
# 2 "parser.mly"
open Ast
let mk_expr d : Ast.expr = { loc = Location.dummy; desc = d }
# 60 "parser.ml"
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
    0|]

let yytransl_block = [|
  257 (* ID *);
  258 (* FLOATLIT *);
  259 (* INTLIT *);
  260 (* STRINGLIT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\004\000\004\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\006\000\006\000\010\000\010\000\007\000\007\000\
\011\000\012\000\012\000\012\000\013\000\013\000\015\000\015\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\009\000\009\000\008\000\
\008\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\001\000\002\000\003\000\002\000\001\000\003\000\006\000\
\005\000\006\000\005\000\003\000\007\000\006\000\005\000\009\000\
\008\000\005\000\001\000\002\000\005\000\005\000\001\000\002\000\
\008\000\000\000\001\000\003\000\001\000\002\000\002\000\000\000\
\004\000\006\000\005\000\008\000\008\000\008\000\006\000\004\000\
\005\000\003\000\005\000\009\000\005\000\000\000\001\000\003\000\
\005\000\001\000\001\000\001\000\001\000\003\000\003\000\003\000\
\003\000\005\000\004\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\063\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\000\000\005\000\000\000\000\000\012\000\000\000\050\000\
\052\000\051\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\004\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\062\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\018\000\000\000\000\000\000\000\000\000\011\000\
\020\000\024\000\000\000\000\000\009\000\000\000\015\000\000\000\
\000\000\014\000\059\000\000\000\000\000\000\000\000\000\010\000\
\000\000\008\000\000\000\000\000\013\000\058\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\021\000\
\022\000\017\000\000\000\049\000\028\000\000\000\016\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\025\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\031\000\042\000\000\000\033\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\040\000\000\000\000\000\045\000\
\041\000\035\000\000\000\000\000\000\000\000\000\000\000\000\000\
\043\000\034\000\000\000\000\000\000\000\039\000\000\000\000\000\
\000\000\000\000\000\000\038\000\036\000\037\000\000\000\044\000"

let yydgoto = "\002\000\
\008\000\009\000\010\000\029\000\030\000\053\000\054\000\063\000\
\031\000\055\000\056\000\104\000\128\000\129\000\140\000"

let yysindex = "\044\000\
\001\255\000\000\012\255\052\255\053\255\059\255\062\255\000\000\
\051\000\043\255\076\255\054\255\048\255\056\255\075\255\089\255\
\000\000\001\255\000\000\084\255\054\255\000\000\092\255\000\000\
\000\000\000\000\054\255\112\255\090\255\037\000\093\255\009\255\
\116\255\009\255\085\255\000\000\118\255\097\255\054\255\229\255\
\100\255\054\255\054\255\054\255\054\255\054\255\054\255\054\255\
\101\255\120\255\123\255\126\255\124\255\106\255\254\254\124\255\
\119\255\124\255\114\255\144\255\241\255\132\255\125\255\122\255\
\129\255\000\000\054\255\037\000\050\255\050\255\057\255\057\255\
\037\000\037\000\000\000\139\255\143\255\145\255\149\255\000\000\
\000\000\000\000\054\255\151\255\000\000\141\255\000\000\054\255\
\155\255\000\000\000\000\146\255\179\255\054\255\054\255\000\000\
\161\255\000\000\054\255\245\255\000\000\000\000\162\255\168\255\
\001\000\005\000\170\255\174\255\118\255\179\255\175\255\000\000\
\000\000\000\000\176\255\000\000\000\000\027\255\000\000\088\255\
\200\255\201\255\010\255\054\255\054\255\027\255\203\255\186\255\
\027\255\054\255\054\255\195\255\192\255\181\255\183\255\189\255\
\138\255\225\255\027\255\202\255\216\255\000\000\000\000\017\000\
\211\255\054\255\078\255\232\255\234\255\239\255\027\255\027\255\
\000\000\000\000\091\255\000\000\242\255\021\000\002\000\228\255\
\249\255\010\000\022\000\034\000\000\000\252\255\033\000\000\000\
\000\000\000\000\038\000\054\255\054\255\054\255\027\255\041\000\
\000\000\000\000\048\000\050\000\052\000\000\000\054\255\046\000\
\053\000\054\000\058\000\000\000\000\000\000\000\056\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\254\000\000\000\060\000\000\000\000\000\000\000\000\000\
\000\000\058\001\000\000\000\000\060\000\000\000\117\255\000\000\
\000\000\000\000\000\000\000\000\061\000\238\254\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\060\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\066\000\062\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\060\000\022\255\182\255\197\255\152\255\167\255\
\205\255\213\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\060\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\063\000\000\000\000\000\000\000\
\000\000\000\000\060\000\064\000\000\000\000\000\065\000\000\000\
\000\000\000\000\000\000\000\000\000\000\063\000\000\000\000\000\
\000\000\000\000\049\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\067\000\000\000\000\000\
\068\000\000\000\060\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\067\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\060\000\060\000\060\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\060\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\049\000\000\000"

let yygindex = "\000\000\
\000\000\255\255\000\000\000\000\233\255\230\255\008\000\221\000\
\235\255\000\000\000\000\229\000\215\000\131\255\206\000"

let yytablesize = 347
let yytable = "\038\000\
\139\000\003\000\006\000\040\000\051\000\004\000\006\000\058\000\
\019\000\005\000\134\000\061\000\011\000\139\000\050\000\051\000\
\036\000\065\000\068\000\069\000\070\000\071\000\072\000\073\000\
\074\000\164\000\165\000\120\000\081\000\052\000\006\000\012\000\
\007\000\121\000\122\000\123\000\124\000\135\000\136\000\125\000\
\052\000\059\000\007\000\003\000\001\000\092\000\007\000\004\000\
\126\000\182\000\017\000\005\000\013\000\014\000\023\000\024\000\
\025\000\026\000\127\000\015\000\079\000\097\000\016\000\082\000\
\100\000\084\000\018\000\045\000\046\000\032\000\105\000\106\000\
\006\000\027\000\007\000\047\000\048\000\108\000\023\000\024\000\
\025\000\026\000\047\000\048\000\028\000\023\000\024\000\025\000\
\026\000\033\000\020\000\023\000\024\000\025\000\026\000\021\000\
\034\000\027\000\159\000\022\000\137\000\138\000\130\000\035\000\
\027\000\037\000\144\000\131\000\028\000\145\000\027\000\039\000\
\041\000\049\000\042\000\060\000\057\000\064\000\062\000\067\000\
\076\000\166\000\158\000\077\000\075\000\160\000\078\000\053\000\
\080\000\050\000\053\000\167\000\053\000\053\000\053\000\053\000\
\085\000\053\000\083\000\053\000\053\000\053\000\053\000\053\000\
\086\000\090\000\088\000\089\000\151\000\091\000\179\000\180\000\
\181\000\043\000\044\000\045\000\046\000\094\000\093\000\095\000\
\099\000\187\000\056\000\047\000\048\000\056\000\102\000\056\000\
\056\000\056\000\056\000\096\000\056\000\098\000\056\000\056\000\
\056\000\057\000\101\000\103\000\057\000\107\000\057\000\057\000\
\057\000\057\000\110\000\057\000\111\000\057\000\057\000\057\000\
\054\000\114\000\115\000\054\000\118\000\054\000\054\000\119\000\
\132\000\133\000\054\000\141\000\054\000\054\000\054\000\055\000\
\142\000\146\000\055\000\147\000\055\000\055\000\148\000\060\000\
\149\000\055\000\060\000\055\000\055\000\055\000\150\000\061\000\
\154\000\060\000\061\000\060\000\060\000\060\000\155\000\157\000\
\161\000\061\000\162\000\061\000\061\000\061\000\152\000\163\000\
\043\000\044\000\045\000\046\000\043\000\044\000\045\000\046\000\
\171\000\066\000\047\000\048\000\176\000\002\000\047\000\048\000\
\043\000\044\000\045\000\046\000\043\000\044\000\045\000\046\000\
\087\000\168\000\047\000\048\000\172\000\109\000\047\000\048\000\
\043\000\044\000\045\000\046\000\043\000\044\000\045\000\046\000\
\112\000\170\000\047\000\048\000\113\000\173\000\047\000\048\000\
\043\000\044\000\045\000\046\000\043\000\044\000\045\000\046\000\
\156\000\174\000\047\000\048\000\169\000\175\000\047\000\048\000\
\043\000\044\000\045\000\046\000\043\000\044\000\045\000\046\000\
\177\000\003\000\047\000\048\000\183\000\178\000\047\000\048\000\
\058\000\058\000\058\000\058\000\184\000\188\000\185\000\019\000\
\186\000\116\000\058\000\058\000\189\000\190\000\191\000\192\000\
\046\000\047\000\117\000\026\000\023\000\027\000\048\000\143\000\
\153\000\032\000\029\000"

let yycheck = "\021\000\
\126\000\001\001\021\001\027\000\007\001\005\001\025\001\034\000\
\010\000\009\001\001\001\035\000\001\001\139\000\006\001\007\001\
\018\000\039\000\042\000\043\000\044\000\045\000\046\000\047\000\
\048\000\151\000\152\000\001\001\055\000\032\001\030\001\020\001\
\032\001\007\001\008\001\009\001\010\001\028\001\029\001\013\001\
\032\001\034\000\021\001\001\001\001\000\067\000\025\001\005\001\
\022\001\175\000\000\000\009\001\001\001\001\001\001\001\002\001\
\003\001\004\001\032\001\001\001\053\000\083\000\001\001\056\000\
\088\000\058\000\024\001\018\001\019\001\022\001\094\000\095\000\
\030\001\020\001\032\001\026\001\027\001\099\000\001\001\002\001\
\003\001\004\001\026\001\027\001\031\001\001\001\002\001\003\001\
\004\001\034\001\015\001\001\001\002\001\003\001\004\001\020\001\
\022\001\020\001\021\001\024\001\124\000\125\000\015\001\015\001\
\020\001\022\001\130\000\020\001\031\001\131\000\020\001\020\001\
\001\001\021\001\025\001\031\001\001\001\021\001\001\001\020\001\
\001\001\031\001\146\000\001\001\024\001\147\000\001\001\011\001\
\023\001\006\001\014\001\155\000\016\001\017\001\018\001\019\001\
\023\001\021\001\020\001\023\001\024\001\025\001\026\001\027\001\
\001\001\024\001\015\001\023\001\011\001\021\001\172\000\173\000\
\174\000\016\001\017\001\018\001\019\001\015\001\020\001\015\001\
\020\001\183\000\011\001\026\001\027\001\014\001\021\001\016\001\
\017\001\018\001\019\001\023\001\021\001\023\001\023\001\024\001\
\025\001\011\001\024\001\001\001\014\001\021\001\016\001\017\001\
\018\001\019\001\025\001\021\001\021\001\023\001\024\001\025\001\
\011\001\024\001\021\001\014\001\022\001\016\001\017\001\024\001\
\001\001\001\001\021\001\001\001\023\001\024\001\025\001\011\001\
\023\001\015\001\014\001\020\001\016\001\017\001\034\001\011\001\
\034\001\021\001\014\001\023\001\024\001\025\001\034\001\011\001\
\023\001\021\001\014\001\023\001\024\001\025\001\015\001\021\001\
\001\001\021\001\001\001\023\001\024\001\025\001\014\001\001\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\021\001\021\001\026\001\027\001\001\001\000\000\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\024\001\026\001\027\001\020\001\025\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\024\001\026\001\027\001\024\001\020\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\020\001\026\001\027\001\024\001\012\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\000\000\026\001\027\001\020\001\024\001\026\001\027\001\
\016\001\017\001\018\001\019\001\021\001\024\001\021\001\006\001\
\021\001\109\000\026\001\027\001\024\001\024\001\021\001\024\001\
\021\001\021\001\110\000\021\001\023\001\021\001\023\001\129\000\
\139\000\023\001\023\001"

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
# 25 "parser.mly"
              ( _1 )
# 349 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 28 "parser.mly"
         ( [_1] )
# 356 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 29 "parser.mly"
                   ( [_1] )
# 363 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 30 "parser.mly"
                         ( _1 :: _3 )
# 371 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 31 "parser.mly"
               ( _1 :: _2 )
# 379 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 34 "parser.mly"
                             ( [_1] )
# 386 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 35 "parser.mly"
                               ( _1 @ [_3] )
# 394 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 38 "parser.mly"
                                          ( Class { cname = _2; fields = _4; methods = _5 } )
# 403 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 39 "parser.mly"
                                          ( Class { cname = _2; fields = []; methods = _4 } )
# 411 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 40 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 420 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 41 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 428 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 42 "parser.mly"
                                           ( Instantiate (_1, _2) )
# 436 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'inits) in
    Obj.repr(
# 43 "parser.mly"
                                                 ( InstantiateInit (_1, _2, _5) )
# 445 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 44 "parser.mly"
                                                 ( InstantiateArgs (_1, _2, _4) )
# 454 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 45 "parser.mly"
                                 ( Global (VarDecl (_2, _4)) )
# 462 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 46 "parser.mly"
                                                        ( Global (VarDecl (_2, mk_expr(New (_5, _7)))) )
# 471 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 47 "parser.mly"
                                                     ( Global (Send (_2, _4, _6)) )
# 480 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 48 "parser.mly"
                                    ( Global (CallStmt (_1, _3)) )
# 488 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 51 "parser.mly"
          ( [_1] )
# 495 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 52 "parser.mly"
                 ( _1 :: _2 )
# 503 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 55 "parser.mly"
                                   ( VarDecl (_2, _4) )
# 511 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 56 "parser.mly"
                                 ( VarDecl (_2, _4) )
# 519 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 59 "parser.mly"
                ( [_1] )
# 526 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 60 "parser.mly"
                        ( _1 :: _2 )
# 534 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 63 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = Seq _7 } )
# 544 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 67 "parser.mly"
         ( [] )
# 550 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 68 "parser.mly"
       ( [_1] )
# 557 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 69 "parser.mly"
                        ( _1::_3 )
# 565 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 72 "parser.mly"
         ( [_1] )
# 572 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 73 "parser.mly"
               ( _1 :: _2 )
# 580 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 76 "parser.mly"
                   ( _1::_2 )
# 588 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "parser.mly"
                   ( [] )
# 594 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 80 "parser.mly"
                             ( Assign (_1, _3) )
# 602 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 81 "parser.mly"
                                         ( CallStmt (_2, _4) )
# 610 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 82 "parser.mly"
                                    ( CallStmt (_2, []) )
# 617 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 83 "parser.mly"
                                                  ( Send ("self", _4, _6) )
# 625 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 84 "parser.mly"
                                                    ( Send ("sender", _4, _6) )
# 633 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 85 "parser.mly"
                                                ( Send (_2, _4, _6) )
# 642 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 86 "parser.mly"
                                ( If (_2, _4, _6) )
# 651 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 87 "parser.mly"
                       ( While (_2, _4) )
# 659 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 88 "parser.mly"
                                   ( VarDecl (_2, _4) )
# 667 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 89 "parser.mly"
                            ( Seq _2 )
# 674 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 90 "parser.mly"
                                 ( VarDecl (_2, _4) )
# 682 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 91 "parser.mly"
                                                      ( VarDecl(_2, mk_expr(New(_5,_7))) )
# 691 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 92 "parser.mly"
                                    ( CallStmt (_1, _3) )
# 699 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 95 "parser.mly"
                 ( [] )
# 705 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 96 "parser.mly"
                 ( _1 )
# 712 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                   ( [VarDecl(_1, _3)] )
# 720 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 100 "parser.mly"
                               ( VarDecl(_1, _3) :: _5 )
# 729 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 103 "parser.mly"
             ( mk_expr(Float _1) )
# 736 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 104 "parser.mly"
              ( mk_expr(String _1) )
# 743 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 105 "parser.mly"
           ( mk_expr(Int _1) )
# 750 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 106 "parser.mly"
       ( mk_expr(Var _1) )
# 757 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                   ( mk_expr(Binop ("+", _1, _3)) )
# 765 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                    ( mk_expr(Binop ("-", _1, _3)) )
# 773 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                    ( mk_expr(Binop ("*", _1, _3)) )
# 781 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                  ( mk_expr(Binop ("/", _1, _3)) )
# 789 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 111 "parser.mly"
                              ( mk_expr(New (_2, _4)) )
# 797 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 112 "parser.mly"
                          ( mk_expr(Call (_1, _3)) )
# 805 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 113 "parser.mly"
                 ( mk_expr(Binop (">=", _1, _3)) )
# 813 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 114 "parser.mly"
                 ( mk_expr(Binop ("<=", _1, _3)) )
# 821 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                       ( _2 )
# 828 "parser.ml"
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
