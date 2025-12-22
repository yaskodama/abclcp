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
# 70 "parser.ml"
let yytransl_const = [|
  261 (* METHOD *);
  262 (* FLOAT *);
  263 (* CALL *);
  264 (* SEND *);
  265 (* IF *);
  266 (* THEN *);
  267 (* ELSE *);
  268 (* WHILE *);
  269 (* DO *);
  270 (* ASSIGN *);
  271 (* PLUS *);
  272 (* MINUS *);
  273 (* TIMES *);
  274 (* DIV *);
  275 (* LPAREN *);
  276 (* RPAREN *);
  277 (* LBRACE *);
  278 (* RBRACE *);
  279 (* SEMICOLON *);
  280 (* COMMA *);
  281 (* GE *);
  282 (* LE *);
  283 (* GT *);
  284 (* LT *);
  285 (* SELF *);
  286 (* SENDER *);
  287 (* CLASS *);
    0 (* EOF *);
  288 (* NEW *);
  289 (* VAR *);
  290 (* EQ *);
  291 (* DOT *);
  292 (* BECOME *);
    0|]

let yytransl_block = [|
  257 (* ID *);
  258 (* FLOATLIT *);
  259 (* INTLIT *);
  260 (* STRINGLIT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\004\000\004\000\
\003\000\003\000\003\000\003\000\003\000\003\000\006\000\006\000\
\009\000\009\000\007\000\007\000\010\000\011\000\011\000\011\000\
\012\000\012\000\014\000\014\000\013\000\013\000\013\000\013\000\
\013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
\013\000\013\000\013\000\008\000\008\000\015\000\015\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\005\000\009\000\008\000\005\000\001\000\002\000\
\005\000\005\000\001\000\002\000\008\000\000\000\001\000\003\000\
\001\000\002\000\002\000\000\000\004\000\006\000\005\000\008\000\
\008\000\008\000\005\000\007\000\004\000\003\000\005\000\009\000\
\005\000\006\000\005\000\000\000\001\000\003\000\005\000\001\000\
\001\000\001\000\001\000\003\000\003\000\003\000\003\000\005\000\
\004\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\063\000\
\000\000\000\000\002\000\000\000\000\000\000\000\000\000\001\000\
\000\000\006\000\000\000\048\000\050\000\049\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\062\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\014\000\000\000\000\000\000\000\000\000\000\000\
\010\000\016\000\020\000\000\000\011\000\057\000\000\000\000\000\
\000\000\000\000\000\000\009\000\000\000\056\000\000\000\000\000\
\000\000\000\000\000\000\000\000\013\000\000\000\000\000\017\000\
\018\000\000\000\024\000\000\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\021\000\026\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\027\000\038\000\000\000\
\000\000\029\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\037\000\000\000\000\000\000\000\000\000\041\000\031\000\
\000\000\000\000\000\000\000\000\000\000\000\000\039\000\043\000\
\000\000\030\000\000\000\000\000\000\000\000\000\000\000\042\000\
\000\000\000\000\000\000\036\000\000\000\034\000\032\000\033\000\
\000\000\040\000"

let yydgoto = "\002\000\
\008\000\009\000\010\000\025\000\026\000\049\000\050\000\027\000\
\051\000\052\000\089\000\110\000\111\000\121\000\000\000"

let yysindex = "\004\000\
\032\255\000\000\006\000\241\254\011\255\025\255\026\255\000\000\
\038\000\056\255\000\000\106\255\019\255\061\255\072\255\000\000\
\059\255\000\000\069\255\000\000\000\000\000\000\106\255\094\255\
\078\255\229\255\107\255\125\255\002\255\117\255\000\000\106\255\
\151\255\109\255\106\255\106\255\106\255\106\255\106\255\106\255\
\106\255\106\255\106\255\111\255\118\255\138\255\140\255\145\255\
\180\255\148\255\251\254\180\255\183\255\165\255\166\255\000\000\
\106\255\229\255\086\255\086\255\131\255\131\255\229\255\229\255\
\229\255\229\255\000\000\106\255\168\255\175\255\184\255\177\255\
\000\000\000\000\000\000\181\255\000\000\000\000\192\255\194\255\
\200\255\106\255\106\255\000\000\106\255\000\000\190\255\191\255\
\197\255\179\255\193\255\242\255\000\000\200\255\182\255\000\000\
\000\000\226\255\000\000\038\255\000\000\037\255\007\000\012\255\
\244\255\106\255\038\255\008\000\009\000\245\255\038\255\106\255\
\106\255\254\255\246\255\250\255\014\000\106\255\147\255\038\255\
\002\000\046\000\043\000\000\000\000\000\207\255\032\000\074\255\
\062\000\065\000\066\000\211\255\038\255\000\000\000\000\129\255\
\097\255\000\000\255\255\045\000\049\000\051\000\052\000\053\000\
\038\255\000\000\072\000\225\255\054\000\055\000\000\000\000\000\
\056\000\106\255\106\255\106\255\063\000\057\000\000\000\000\000\
\058\000\000\000\060\000\064\000\067\000\038\255\106\255\000\000\
\059\000\068\000\069\000\000\000\070\000\000\000\000\000\000\000\
\071\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\078\001\000\000\107\255\000\000\000\000\000\000\000\000\
\083\001\000\000\127\255\000\000\000\000\000\000\000\000\000\000\
\073\000\028\255\000\000\000\000\000\000\000\000\000\000\107\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\080\000\074\000\000\000\000\000\000\000\000\000\
\107\255\048\255\021\000\027\000\003\000\015\000\060\255\033\000\
\035\000\041\000\000\000\107\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\075\000\000\000\000\000\000\000\107\255\000\000\000\000\077\000\
\000\000\000\000\000\000\000\000\000\000\075\000\000\000\000\000\
\000\000\243\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\076\000\000\000\000\000\000\000\078\000\000\000\
\107\255\000\000\000\000\000\000\000\000\000\000\000\000\076\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\107\255\107\255\107\255\022\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\107\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\243\255\000\000"

let yygindex = "\000\000\
\000\000\249\255\000\000\000\000\235\255\035\001\017\000\224\255\
\000\000\000\000\250\000\234\000\160\255\235\000\000\000"

let yytablesize = 356
let yytable = "\055\000\
\047\000\033\000\018\000\012\000\001\000\011\000\046\000\047\000\
\054\000\031\000\120\000\013\000\115\000\058\000\059\000\060\000\
\061\000\062\000\063\000\064\000\065\000\066\000\035\000\120\000\
\079\000\014\000\015\000\048\000\035\000\035\000\035\000\003\000\
\004\000\035\000\048\000\080\000\146\000\016\000\102\000\005\000\
\116\000\117\000\035\000\035\000\103\000\104\000\105\000\007\000\
\157\000\106\000\112\000\007\000\092\000\028\000\035\000\113\000\
\004\000\035\000\107\000\004\000\090\000\091\000\006\000\005\000\
\007\000\072\000\005\000\008\000\075\000\172\000\108\000\008\000\
\058\000\109\000\019\000\020\000\021\000\022\000\017\000\058\000\
\127\000\029\000\058\000\058\000\119\000\030\000\006\000\032\000\
\007\000\006\000\126\000\007\000\023\000\140\000\034\000\141\000\
\132\000\019\000\020\000\021\000\022\000\035\000\038\000\039\000\
\150\000\024\000\019\000\020\000\021\000\022\000\040\000\041\000\
\042\000\043\000\148\000\023\000\149\000\019\000\020\000\021\000\
\022\000\163\000\164\000\165\000\023\000\045\000\044\000\057\000\
\024\000\019\000\020\000\021\000\022\000\067\000\173\000\023\000\
\068\000\024\000\069\000\051\000\070\000\051\000\051\000\051\000\
\051\000\071\000\051\000\023\000\053\000\051\000\051\000\051\000\
\051\000\051\000\051\000\040\000\041\000\042\000\043\000\133\000\
\147\000\036\000\037\000\038\000\039\000\036\000\037\000\038\000\
\039\000\073\000\056\000\040\000\041\000\042\000\043\000\040\000\
\041\000\042\000\043\000\036\000\037\000\038\000\039\000\076\000\
\046\000\078\000\081\000\077\000\082\000\040\000\041\000\042\000\
\043\000\036\000\037\000\038\000\039\000\083\000\084\000\085\000\
\088\000\096\000\100\000\040\000\041\000\042\000\043\000\036\000\
\037\000\038\000\039\000\086\000\093\000\087\000\094\000\097\000\
\095\000\040\000\041\000\042\000\043\000\036\000\037\000\038\000\
\039\000\036\000\037\000\038\000\039\000\138\000\145\000\040\000\
\041\000\042\000\043\000\040\000\041\000\042\000\043\000\036\000\
\037\000\038\000\039\000\036\000\037\000\038\000\039\000\159\000\
\101\000\040\000\041\000\042\000\043\000\040\000\041\000\042\000\
\043\000\056\000\056\000\056\000\056\000\098\000\118\000\114\000\
\122\000\123\000\124\000\056\000\056\000\056\000\056\000\054\000\
\128\000\054\000\054\000\054\000\054\000\151\000\054\000\135\000\
\129\000\054\000\054\000\055\000\130\000\055\000\055\000\055\000\
\055\000\052\000\055\000\052\000\052\000\055\000\055\000\053\000\
\052\000\053\000\053\000\052\000\052\000\059\000\053\000\060\000\
\131\000\053\000\053\000\139\000\059\000\061\000\060\000\059\000\
\059\000\060\000\060\000\136\000\061\000\137\000\142\000\061\000\
\061\000\143\000\144\000\152\000\153\000\154\000\155\000\156\000\
\158\000\166\000\161\000\167\000\160\000\003\000\162\000\169\000\
\168\000\174\000\004\000\170\000\015\000\074\000\171\000\099\000\
\125\000\177\000\175\000\176\000\045\000\178\000\022\000\019\000\
\023\000\028\000\134\000\025\000"

let yycheck = "\032\000\
\006\001\023\000\010\000\019\001\001\000\000\000\005\001\006\001\
\030\000\017\000\107\000\001\001\001\001\035\000\036\000\037\000\
\038\000\039\000\040\000\041\000\042\000\043\000\001\001\120\000\
\057\000\001\001\001\001\033\001\007\001\008\001\009\001\000\001\
\001\001\012\001\033\001\068\000\133\000\000\000\001\001\008\001\
\029\001\030\001\021\001\022\001\007\001\008\001\009\001\020\001\
\145\000\012\001\014\001\024\001\085\000\035\001\033\001\019\001\
\001\001\036\001\021\001\001\001\082\000\083\000\031\001\008\001\
\033\001\049\000\008\001\020\001\052\000\166\000\033\001\024\001\
\013\001\036\001\001\001\002\001\003\001\004\001\023\001\020\001\
\113\000\021\001\023\001\024\001\106\000\014\001\031\001\019\001\
\033\001\031\001\112\000\033\001\019\001\020\001\001\001\128\000\
\118\000\001\001\002\001\003\001\004\001\024\001\017\001\018\001\
\137\000\032\001\001\001\002\001\003\001\004\001\025\001\026\001\
\027\001\028\001\136\000\019\001\020\001\001\001\002\001\003\001\
\004\001\154\000\155\000\156\000\019\001\001\001\020\001\019\001\
\032\001\001\001\002\001\003\001\004\001\023\001\167\000\019\001\
\019\001\032\001\001\001\013\001\001\001\015\001\016\001\017\001\
\018\001\001\001\020\001\019\001\032\001\023\001\024\001\025\001\
\026\001\027\001\028\001\025\001\026\001\027\001\028\001\013\001\
\032\001\015\001\016\001\017\001\018\001\015\001\016\001\017\001\
\018\001\022\001\020\001\025\001\026\001\027\001\028\001\025\001\
\026\001\027\001\028\001\015\001\016\001\017\001\018\001\001\001\
\005\001\020\001\019\001\023\001\014\001\025\001\026\001\027\001\
\028\001\015\001\016\001\017\001\018\001\014\001\022\001\019\001\
\001\001\023\001\021\001\025\001\026\001\027\001\028\001\015\001\
\016\001\017\001\018\001\020\001\023\001\020\001\024\001\023\001\
\020\001\025\001\026\001\027\001\028\001\015\001\016\001\017\001\
\018\001\015\001\016\001\017\001\018\001\023\001\020\001\025\001\
\026\001\027\001\028\001\025\001\026\001\027\001\028\001\015\001\
\016\001\017\001\018\001\015\001\016\001\017\001\018\001\023\001\
\023\001\025\001\026\001\027\001\028\001\025\001\026\001\027\001\
\028\001\015\001\016\001\017\001\018\001\020\001\019\001\001\001\
\001\001\001\001\022\001\025\001\026\001\027\001\028\001\013\001\
\019\001\015\001\016\001\017\001\018\001\023\001\020\001\022\001\
\035\001\023\001\024\001\013\001\035\001\015\001\016\001\017\001\
\018\001\013\001\020\001\015\001\016\001\023\001\024\001\013\001\
\020\001\015\001\016\001\023\001\024\001\013\001\020\001\013\001\
\035\001\023\001\024\001\020\001\020\001\013\001\020\001\023\001\
\024\001\023\001\024\001\014\001\020\001\019\001\001\001\023\001\
\024\001\001\001\001\001\023\001\020\001\019\001\019\001\019\001\
\001\001\011\001\020\001\019\001\023\001\000\000\023\001\020\001\
\023\001\023\001\000\000\020\001\005\001\051\000\020\001\094\000\
\111\000\020\001\023\001\023\001\020\001\023\001\020\001\022\001\
\020\001\022\001\120\000\022\001"

let yynames_const = "\
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
  GT\000\
  LT\000\
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
# 362 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 33 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 368 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 36 "parser.mly"
         ( [_1] )
# 375 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 37 "parser.mly"
                   ( [_1] )
# 382 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 38 "parser.mly"
                         ( _1 :: _3 )
# 390 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 39 "parser.mly"
               ( _1 :: _2 )
# 398 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                             ( [_1] )
# 405 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 43 "parser.mly"
                               ( _1 @ [_3] )
# 413 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 46 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 422 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 47 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 430 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 48 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 438 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 49 "parser.mly"
                                                        ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 447 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 50 "parser.mly"
                                                        ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 456 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 51 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 464 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 54 "parser.mly"
          ( [_1] )
# 471 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 55 "parser.mly"
                 ( _1 :: _2 )
# 479 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 58 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 487 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 59 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 495 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 62 "parser.mly"
                ( [_1] )
# 502 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 63 "parser.mly"
                        ( _1 :: _2 )
# 510 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 66 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = mk_stmt1 2 (Seq _7) } )
# 520 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
       ( [] )
# 526 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 71 "parser.mly"
       ( [_1] )
# 533 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 72 "parser.mly"
                        ( _1::_3 )
# 541 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 75 "parser.mly"
         ( [_1] )
# 548 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 76 "parser.mly"
               ( _1 :: _2 )
# 556 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 79 "parser.mly"
                   ( _1::_2 )
# 564 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "parser.mly"
                   ( [] )
# 570 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 578 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 84 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 586 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 85 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 593 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 86 "parser.mly"
                                                  ( mk_stmt1 4 (Send("self", _4, _6)) )
# 601 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 87 "parser.mly"
                                                    ( mk_stmt1 4 (Send ("sender", _4, _6)) )
# 609 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 88 "parser.mly"
                                                ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 618 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 89 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 626 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 90 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 635 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 91 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 643 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 92 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 650 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 658 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 94 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 667 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 95 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 675 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 96 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 683 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 97 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 690 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 100 "parser.mly"
                 ( [] )
# 696 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 101 "parser.mly"
                 ( _1 )
# 703 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 711 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 105 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 720 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 108 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 727 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 109 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 734 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 110 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 741 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 111 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 748 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 112 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 756 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 113 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 764 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 114 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 772 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 780 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 116 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 788 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 117 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 796 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 804 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 119 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 812 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 120 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 820 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 121 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 828 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 122 "parser.mly"
                       ( _2 )
# 835 "parser.ml"
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
