type token =
  | ID of (
# 5 "parser.mly"
        string
# 6 "parser.ml"
)
  | FLOATLIT of (
# 6 "parser.mly"
        float
# 11 "parser.ml"
)
  | INTLIT of (
# 7 "parser.mly"
        int
# 16 "parser.ml"
)
  | STRINGLIT of (
# 8 "parser.mly"
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
# 59 "parser.ml"
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
\006\000\006\000\010\000\010\000\007\000\007\000\011\000\012\000\
\012\000\012\000\013\000\013\000\015\000\015\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\014\000\014\000\009\000\009\000\008\000\008\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\001\000\002\000\003\000\002\000\001\000\003\000\006\000\
\005\000\006\000\005\000\003\000\007\000\006\000\009\000\008\000\
\001\000\002\000\005\000\005\000\001\000\002\000\008\000\000\000\
\001\000\003\000\001\000\002\000\002\000\000\000\004\000\006\000\
\005\000\008\000\008\000\008\000\006\000\004\000\005\000\003\000\
\005\000\009\000\000\000\001\000\003\000\005\000\001\000\001\000\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\004\000\
\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\060\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\
\000\000\005\000\000\000\000\000\012\000\000\000\000\000\000\000\
\000\000\004\000\000\000\000\000\047\000\049\000\048\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\011\000\018\000\022\000\000\000\000\000\009\000\000\000\000\000\
\000\000\000\000\059\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\014\000\000\000\000\000\000\000\010\000\
\000\000\008\000\000\000\000\000\013\000\056\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\
\000\000\019\000\020\000\016\000\000\000\046\000\026\000\000\000\
\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\023\000\028\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\029\000\040\000\000\000\031\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\000\000\000\000\000\039\000\033\000\
\000\000\000\000\000\000\000\000\000\000\000\000\041\000\032\000\
\000\000\000\000\000\000\037\000\000\000\000\000\000\000\000\000\
\000\000\036\000\034\000\035\000\000\000\042\000"

let yydgoto = "\002\000\
\008\000\009\000\010\000\034\000\035\000\040\000\041\000\049\000\
\036\000\042\000\043\000\097\000\122\000\123\000\133\000"

let yysindex = "\005\000\
\042\255\000\000\020\255\043\255\044\255\059\255\061\255\000\000\
\087\000\018\255\046\255\071\255\060\255\076\255\084\255\000\000\
\042\255\000\000\078\255\051\255\000\000\252\254\101\255\252\254\
\072\255\000\000\103\255\085\255\000\000\000\000\000\000\051\255\
\106\255\086\255\003\000\089\255\116\255\120\255\125\255\127\255\
\108\255\033\255\127\255\132\255\127\255\134\255\147\255\149\255\
\139\255\051\255\211\255\150\255\051\255\051\255\051\255\051\255\
\051\255\051\255\051\255\145\255\152\255\162\255\164\255\161\255\
\000\000\000\000\000\000\051\255\167\255\000\000\165\255\051\255\
\163\255\170\255\000\000\051\255\003\000\065\255\065\255\041\255\
\041\255\003\000\003\000\000\000\191\255\051\255\051\255\000\000\
\173\255\000\000\051\255\124\255\000\000\000\000\178\255\175\255\
\181\255\223\255\227\255\183\255\184\255\103\255\000\000\191\255\
\192\255\000\000\000\000\000\000\189\255\000\000\000\000\007\255\
\000\000\200\255\216\255\221\255\009\255\051\255\051\255\007\255\
\230\255\212\255\007\255\051\255\237\255\228\255\202\255\234\255\
\246\255\128\255\207\255\007\255\241\255\012\000\000\000\000\000\
\239\255\051\255\055\255\027\000\034\000\035\000\007\255\007\255\
\000\000\000\000\077\255\000\000\243\255\013\000\017\000\019\000\
\020\000\023\000\032\000\000\000\044\000\255\255\000\000\000\000\
\022\000\051\255\051\255\051\255\007\255\028\000\000\000\000\000\
\026\000\029\000\030\000\000\000\051\255\025\000\031\000\033\000\
\037\000\000\000\000\000\000\000\036\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\052\001\000\000\000\000\000\000\000\000\000\000\000\000\
\053\001\000\000\000\000\038\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\111\255\000\000\000\000\000\000\000\000\
\000\000\040\000\242\254\000\000\000\000\000\000\000\000\000\000\
\000\000\048\000\039\000\000\000\000\000\000\000\000\000\000\000\
\000\000\038\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\000\052\255\172\255\187\255\142\255\
\157\255\095\255\195\255\000\000\042\000\000\000\000\000\000\000\
\000\000\000\000\038\000\041\000\000\000\000\000\000\000\046\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\042\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\043\000\
\000\000\000\000\047\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\043\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\038\000\038\000\038\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\038\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\015\000\000\000"

let yygindex = "\000\000\
\000\000\251\255\000\000\000\000\233\255\236\255\045\000\210\000\
\206\255\000\000\000\000\217\000\201\000\137\255\193\000"

let yytablesize = 326
let yytable = "\074\000\
\132\000\037\000\038\000\045\000\018\000\001\000\006\000\114\000\
\051\000\127\000\006\000\026\000\132\000\115\000\116\000\117\000\
\118\000\089\000\003\000\119\000\011\000\066\000\004\000\155\000\
\156\000\095\000\005\000\039\000\120\000\077\000\078\000\079\000\
\080\000\081\000\082\000\083\000\128\000\129\000\121\000\038\000\
\101\000\017\000\003\000\012\000\013\000\172\000\004\000\006\000\
\092\000\007\000\005\000\028\000\029\000\030\000\031\000\028\000\
\029\000\030\000\031\000\014\000\019\000\015\000\098\000\099\000\
\039\000\020\000\058\000\059\000\046\000\021\000\032\000\006\000\
\007\000\007\000\032\000\150\000\007\000\028\000\029\000\030\000\
\031\000\033\000\056\000\057\000\064\000\033\000\016\000\067\000\
\151\000\069\000\058\000\059\000\022\000\023\000\130\000\131\000\
\032\000\024\000\025\000\027\000\137\000\044\000\047\000\048\000\
\050\000\057\000\052\000\157\000\057\000\060\000\053\000\169\000\
\170\000\171\000\149\000\057\000\061\000\057\000\057\000\057\000\
\062\000\050\000\177\000\158\000\050\000\063\000\050\000\050\000\
\050\000\050\000\065\000\050\000\037\000\050\000\050\000\050\000\
\050\000\050\000\143\000\054\000\055\000\056\000\057\000\054\000\
\055\000\056\000\057\000\071\000\102\000\058\000\059\000\068\000\
\053\000\058\000\059\000\053\000\070\000\053\000\053\000\053\000\
\053\000\073\000\053\000\072\000\053\000\053\000\053\000\054\000\
\084\000\076\000\054\000\085\000\054\000\054\000\054\000\054\000\
\086\000\054\000\087\000\054\000\054\000\054\000\051\000\088\000\
\091\000\051\000\093\000\051\000\051\000\090\000\094\000\096\000\
\051\000\100\000\051\000\051\000\051\000\052\000\103\000\104\000\
\052\000\105\000\052\000\052\000\109\000\058\000\108\000\052\000\
\058\000\052\000\052\000\052\000\113\000\112\000\124\000\058\000\
\125\000\058\000\058\000\058\000\144\000\126\000\054\000\055\000\
\056\000\057\000\054\000\055\000\056\000\057\000\134\000\075\000\
\058\000\059\000\135\000\140\000\058\000\059\000\054\000\055\000\
\056\000\057\000\054\000\055\000\056\000\057\000\106\000\139\000\
\058\000\059\000\107\000\138\000\058\000\059\000\054\000\055\000\
\056\000\057\000\054\000\055\000\056\000\057\000\148\000\146\000\
\058\000\059\000\159\000\141\000\058\000\059\000\054\000\055\000\
\056\000\057\000\054\000\055\000\056\000\057\000\167\000\142\000\
\058\000\059\000\147\000\152\000\058\000\059\000\055\000\055\000\
\055\000\055\000\153\000\154\000\160\000\161\000\162\000\163\000\
\055\000\055\000\164\000\165\000\166\000\168\000\174\000\173\000\
\178\000\175\000\176\000\002\000\003\000\017\000\179\000\110\000\
\180\000\181\000\043\000\182\000\044\000\021\000\024\000\045\000\
\111\000\030\000\025\000\136\000\145\000\027\000"

let yycheck = "\050\000\
\120\000\006\001\007\001\024\000\010\000\001\000\021\001\001\001\
\032\000\001\001\025\001\017\000\132\000\007\001\008\001\009\001\
\010\001\068\000\001\001\013\001\001\001\042\000\005\001\143\000\
\144\000\076\000\009\001\032\001\022\001\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\028\001\029\001\032\001\007\001\
\091\000\024\001\001\001\001\001\001\001\165\000\005\001\030\001\
\072\000\032\001\009\001\001\001\002\001\003\001\004\001\001\001\
\002\001\003\001\004\001\001\001\015\001\001\001\086\000\087\000\
\032\001\020\001\026\001\027\001\024\000\024\001\020\001\030\001\
\021\001\032\001\020\001\021\001\025\001\001\001\002\001\003\001\
\004\001\031\001\018\001\019\001\040\000\031\001\000\000\043\000\
\139\000\045\000\026\001\027\001\022\001\034\001\118\000\119\000\
\020\001\022\001\015\001\022\001\124\000\001\001\031\001\001\001\
\020\001\011\001\001\001\031\001\014\001\021\001\025\001\162\000\
\163\000\164\000\138\000\021\001\001\001\023\001\024\001\025\001\
\001\001\011\001\173\000\147\000\014\001\001\001\016\001\017\001\
\018\001\019\001\023\001\021\001\006\001\023\001\024\001\025\001\
\026\001\027\001\011\001\016\001\017\001\018\001\019\001\016\001\
\017\001\018\001\019\001\001\001\025\001\026\001\027\001\020\001\
\011\001\026\001\027\001\014\001\023\001\016\001\017\001\018\001\
\019\001\023\001\021\001\015\001\023\001\024\001\025\001\011\001\
\024\001\020\001\014\001\020\001\016\001\017\001\018\001\019\001\
\015\001\021\001\015\001\023\001\024\001\025\001\011\001\023\001\
\020\001\014\001\024\001\016\001\017\001\023\001\021\001\001\001\
\021\001\021\001\023\001\024\001\025\001\011\001\021\001\025\001\
\014\001\021\001\016\001\017\001\021\001\011\001\024\001\021\001\
\014\001\023\001\024\001\025\001\024\001\022\001\015\001\021\001\
\001\001\023\001\024\001\025\001\014\001\001\001\016\001\017\001\
\018\001\019\001\016\001\017\001\018\001\019\001\001\001\021\001\
\026\001\027\001\023\001\034\001\026\001\027\001\016\001\017\001\
\018\001\019\001\016\001\017\001\018\001\019\001\024\001\020\001\
\026\001\027\001\024\001\015\001\026\001\027\001\016\001\017\001\
\018\001\019\001\016\001\017\001\018\001\019\001\024\001\023\001\
\026\001\027\001\024\001\034\001\026\001\027\001\016\001\017\001\
\018\001\019\001\016\001\017\001\018\001\019\001\024\001\034\001\
\026\001\027\001\015\001\001\001\026\001\027\001\016\001\017\001\
\018\001\019\001\001\001\001\001\024\001\021\001\020\001\020\001\
\026\001\027\001\020\001\012\001\001\001\024\001\021\001\020\001\
\024\001\021\001\021\001\000\000\000\000\006\001\024\001\102\000\
\024\001\021\001\021\001\024\001\021\001\023\001\021\001\023\001\
\104\000\023\001\021\001\123\000\132\000\023\001"

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
# 24 "parser.mly"
              ( _1 )
# 339 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 27 "parser.mly"
         ( [_1] )
# 346 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 28 "parser.mly"
                   ( [_1] )
# 353 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 29 "parser.mly"
                         ( _1 :: _3 )
# 361 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 30 "parser.mly"
               ( _1 :: _2 )
# 369 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 33 "parser.mly"
                             ( [_1] )
# 376 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 34 "parser.mly"
                             ( _1 @ [_3] )
# 384 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 37 "parser.mly"
                                          ( Class { cname = _2; fields = _4; methods = _5 } )
# 393 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 38 "parser.mly"
                                          ( Class { cname = _2; fields = []; methods = _4 } )
# 401 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 39 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 410 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 40 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 418 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 41 "parser.mly"
                                           ( Instantiate (_1, _2) )
# 426 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'inits) in
    Obj.repr(
# 42 "parser.mly"
                                                 ( InstantiateInit (_1, _2, _5) )
# 435 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 43 "parser.mly"
                                                 ( InstantiateArgs (_1, _2, _4) )
# 444 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 44 "parser.mly"
                                                        ( Global (VarDecl (_2, New (_5, _7))) )
# 453 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 45 "parser.mly"
                                                     ( Global (Send (_2, _4, _6)) )
# 462 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 48 "parser.mly"
          ( [_1] )
# 469 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 49 "parser.mly"
                 ( _1 :: _2 )
# 477 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 52 "parser.mly"
                                   ( VarDecl (_2, _4) )
# 485 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 53 "parser.mly"
                                 ( VarDecl (_2, _4) )
# 493 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 56 "parser.mly"
                ( [_1] )
# 500 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 57 "parser.mly"
                        ( _1 :: _2 )
# 508 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 60 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = Seq _7 } )
# 518 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
         ( [] )
# 524 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 65 "parser.mly"
       ( [_1] )
# 531 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 66 "parser.mly"
                        ( _1::_3 )
# 539 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 69 "parser.mly"
         ( [_1] )
# 546 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 70 "parser.mly"
               ( _1 :: _2 )
# 554 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 73 "parser.mly"
                   ( _1::_2 )
# 562 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "parser.mly"
                   ( [] )
# 568 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 77 "parser.mly"
                             ( Assign (_1, _3) )
# 576 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 78 "parser.mly"
                                         ( CallStmt (_2, _4) )
# 584 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 79 "parser.mly"
                                    ( CallStmt (_2, []) )
# 591 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 80 "parser.mly"
                                                  ( Send ("self", _4, _6) )
# 599 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 81 "parser.mly"
                                                    ( Send ("sender", _4, _6) )
# 607 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 82 "parser.mly"
                                                ( Send (_2, _4, _6) )
# 616 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 83 "parser.mly"
                                ( If (_2, _4, _6) )
# 625 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 84 "parser.mly"
                       ( While (_2, _4) )
# 633 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
                                   ( VarDecl (_2, _4) )
# 641 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 86 "parser.mly"
                            ( Seq _2 )
# 648 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 87 "parser.mly"
                                 ( VarDecl (_2, _4) )
# 656 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 88 "parser.mly"
                                                      ( VarDecl(_2, New(_5,_7)) )
# 665 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 91 "parser.mly"
                 ( [] )
# 671 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 92 "parser.mly"
                 ( _1 )
# 678 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
                   ( [VarDecl(_1, _3)] )
# 686 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 96 "parser.mly"
                               ( VarDecl(_1, _3) :: _5 )
# 695 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 99 "parser.mly"
             ( Float _1 )
# 702 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 100 "parser.mly"
              ( String _1 )
# 709 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 101 "parser.mly"
           ( Int _1 )
# 716 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 102 "parser.mly"
       ( Var _1 )
# 723 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 103 "parser.mly"
                   ( Binop ("+", _1, _3) )
# 731 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                    ( Binop ("-", _1, _3) )
# 739 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 105 "parser.mly"
                    ( Binop ("*", _1, _3) )
# 747 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                  ( Binop ("/", _1, _3) )
# 755 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 107 "parser.mly"
                              ( New (_2, _4) )
# 763 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 108 "parser.mly"
                          ( Call (_1, _3) )
# 771 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                 ( Binop (">=", _1, _3) )
# 779 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                 ( Binop ("<=", _1, _3) )
# 787 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 111 "parser.mly"
                       ( _2 )
# 794 "parser.ml"
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
