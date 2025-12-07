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
# 68 "parser.ml"
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
\001\000\001\000\002\000\002\000\002\000\002\000\004\000\004\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\006\000\006\000\010\000\010\000\007\000\
\007\000\011\000\012\000\012\000\012\000\013\000\013\000\015\000\
\015\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\009\000\009\000\
\008\000\008\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\006\000\005\000\003\000\007\000\006\000\005\000\
\009\000\008\000\005\000\001\000\002\000\005\000\005\000\001\000\
\002\000\008\000\000\000\001\000\003\000\001\000\002\000\002\000\
\000\000\004\000\006\000\005\000\008\000\008\000\008\000\006\000\
\004\000\005\000\003\000\005\000\009\000\005\000\000\000\001\000\
\003\000\005\000\001\000\001\000\001\000\001\000\003\000\003\000\
\003\000\003\000\005\000\004\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\064\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\
\000\000\000\000\001\000\000\000\006\000\000\000\000\000\013\000\
\000\000\051\000\053\000\052\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\005\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\063\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\019\000\000\000\000\000\000\000\
\000\000\012\000\021\000\025\000\000\000\000\000\010\000\000\000\
\016\000\000\000\000\000\015\000\060\000\000\000\000\000\000\000\
\000\000\011\000\000\000\009\000\000\000\000\000\014\000\059\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\022\000\023\000\018\000\000\000\050\000\029\000\000\000\
\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\026\000\
\031\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\032\000\043\000\000\000\034\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\041\000\000\000\
\000\000\046\000\042\000\036\000\000\000\000\000\000\000\000\000\
\000\000\000\000\044\000\035\000\000\000\000\000\000\000\040\000\
\000\000\000\000\000\000\000\000\000\000\039\000\037\000\038\000\
\000\000\045\000"

let yydgoto = "\002\000\
\009\000\010\000\011\000\031\000\032\000\055\000\056\000\065\000\
\033\000\057\000\058\000\106\000\130\000\131\000\142\000"

let yysindex = "\028\000\
\002\255\000\000\055\000\008\255\057\255\059\255\062\255\067\255\
\000\000\069\000\043\255\000\000\091\255\083\255\055\255\049\255\
\066\255\090\255\000\000\044\255\000\000\071\255\083\255\000\000\
\092\255\000\000\000\000\000\000\083\255\115\255\095\255\037\000\
\096\255\255\254\124\255\255\254\088\255\000\000\126\255\097\255\
\083\255\229\255\119\255\083\255\083\255\083\255\083\255\083\255\
\083\255\083\255\113\255\144\255\145\255\146\255\142\255\127\255\
\001\255\142\255\139\255\142\255\135\255\159\255\241\255\157\255\
\151\255\137\255\158\255\000\000\083\255\037\000\103\255\103\255\
\246\254\246\254\037\000\037\000\000\000\147\255\165\255\172\255\
\166\255\000\000\000\000\000\000\083\255\171\255\000\000\162\255\
\000\000\083\255\173\255\000\000\000\000\174\255\199\255\083\255\
\083\255\000\000\180\255\000\000\083\255\245\255\000\000\000\000\
\177\255\183\255\001\000\005\000\185\255\189\255\126\255\199\255\
\190\255\000\000\000\000\000\000\191\255\000\000\000\000\029\255\
\000\000\251\254\216\255\222\255\012\255\083\255\083\255\029\255\
\224\255\208\255\029\255\083\255\083\255\217\255\215\255\206\255\
\219\255\220\255\138\255\225\255\029\255\210\255\234\255\000\000\
\000\000\017\000\248\255\083\255\078\255\009\000\025\000\029\000\
\029\255\029\255\000\000\000\000\093\255\000\000\018\000\021\000\
\022\000\040\000\038\000\042\000\050\000\057\000\000\000\070\000\
\033\000\000\000\000\000\000\000\048\000\083\255\083\255\083\255\
\029\255\053\000\000\000\000\000\056\000\058\000\059\000\000\000\
\083\255\054\000\060\000\061\000\062\000\000\000\000\000\000\000\
\063\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\074\001\000\000\000\000\065\000\000\000\000\000\
\000\000\000\000\000\000\081\001\000\000\000\000\065\000\000\000\
\117\255\000\000\000\000\000\000\000\000\000\000\067\000\045\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\065\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\076\000\066\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\065\000\079\255\182\255\197\255\
\152\255\167\255\205\255\213\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\065\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\071\000\000\000\
\000\000\000\000\000\000\000\000\065\000\068\000\000\000\000\000\
\072\000\000\000\000\000\000\000\000\000\000\000\000\000\071\000\
\000\000\000\000\000\000\000\000\049\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\073\000\
\000\000\000\000\074\000\000\000\065\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\073\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\065\000\065\000\065\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\065\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\049\000\000\000"

let yygindex = "\000\000\
\000\000\036\000\000\000\000\000\231\255\007\000\255\255\235\000\
\233\255\000\000\000\000\238\000\220\000\129\255\213\000"

let yytablesize = 354
let yytable = "\040\000\
\141\000\003\000\004\000\042\000\052\000\053\000\005\000\053\000\
\013\000\132\000\006\000\063\000\136\000\141\000\133\000\049\000\
\050\000\067\000\070\000\071\000\072\000\073\000\074\000\075\000\
\076\000\166\000\167\000\014\000\001\000\122\000\054\000\007\000\
\054\000\008\000\061\000\123\000\124\000\125\000\126\000\137\000\
\138\000\127\000\060\000\004\000\004\000\094\000\021\000\005\000\
\005\000\184\000\128\000\006\000\006\000\081\000\012\000\038\000\
\084\000\015\000\086\000\016\000\129\000\099\000\017\000\083\000\
\102\000\007\000\020\000\018\000\019\000\007\000\107\000\108\000\
\007\000\007\000\008\000\008\000\034\000\110\000\025\000\026\000\
\027\000\028\000\035\000\025\000\026\000\027\000\028\000\036\000\
\025\000\026\000\027\000\028\000\039\000\025\000\026\000\027\000\
\028\000\029\000\161\000\008\000\139\000\140\000\029\000\008\000\
\037\000\022\000\146\000\029\000\030\000\147\000\023\000\041\000\
\029\000\030\000\024\000\043\000\051\000\066\000\062\000\044\000\
\047\000\048\000\160\000\168\000\059\000\162\000\064\000\054\000\
\049\000\050\000\054\000\169\000\054\000\054\000\054\000\054\000\
\077\000\054\000\069\000\054\000\054\000\054\000\054\000\054\000\
\078\000\079\000\080\000\052\000\153\000\082\000\181\000\182\000\
\183\000\045\000\046\000\047\000\048\000\087\000\085\000\088\000\
\092\000\189\000\057\000\049\000\050\000\057\000\095\000\057\000\
\057\000\057\000\057\000\090\000\057\000\091\000\057\000\057\000\
\057\000\058\000\093\000\096\000\058\000\101\000\058\000\058\000\
\058\000\058\000\097\000\058\000\098\000\058\000\058\000\058\000\
\055\000\100\000\104\000\055\000\103\000\055\000\055\000\105\000\
\109\000\112\000\055\000\113\000\055\000\055\000\055\000\056\000\
\116\000\117\000\056\000\120\000\056\000\056\000\121\000\061\000\
\134\000\056\000\061\000\056\000\056\000\056\000\135\000\062\000\
\143\000\061\000\062\000\061\000\061\000\061\000\144\000\148\000\
\156\000\062\000\149\000\062\000\062\000\062\000\154\000\150\000\
\045\000\046\000\047\000\048\000\045\000\046\000\047\000\048\000\
\157\000\068\000\049\000\050\000\151\000\152\000\049\000\050\000\
\045\000\046\000\047\000\048\000\045\000\046\000\047\000\048\000\
\089\000\163\000\049\000\050\000\159\000\111\000\049\000\050\000\
\045\000\046\000\047\000\048\000\045\000\046\000\047\000\048\000\
\114\000\164\000\049\000\050\000\115\000\165\000\049\000\050\000\
\045\000\046\000\047\000\048\000\045\000\046\000\047\000\048\000\
\158\000\170\000\049\000\050\000\171\000\172\000\049\000\050\000\
\045\000\046\000\047\000\048\000\045\000\046\000\047\000\048\000\
\179\000\174\000\049\000\050\000\173\000\175\000\049\000\050\000\
\059\000\059\000\059\000\059\000\177\000\176\000\178\000\180\000\
\185\000\003\000\059\000\059\000\186\000\190\000\187\000\188\000\
\004\000\020\000\193\000\191\000\192\000\047\000\194\000\048\000\
\024\000\118\000\049\000\027\000\028\000\119\000\145\000\033\000\
\030\000\155\000"

let yycheck = "\023\000\
\128\000\000\001\001\001\029\000\006\001\007\001\005\001\007\001\
\001\001\015\001\009\001\037\000\001\001\141\000\020\001\026\001\
\027\001\041\000\044\000\045\000\046\000\047\000\048\000\049\000\
\050\000\153\000\154\000\020\001\001\000\001\001\032\001\030\001\
\032\001\032\001\036\000\007\001\008\001\009\001\010\001\028\001\
\029\001\013\001\036\000\001\001\001\001\069\000\011\000\005\001\
\005\001\177\000\022\001\009\001\009\001\055\000\000\000\020\000\
\058\000\001\001\060\000\001\001\032\001\085\000\001\001\057\000\
\090\000\021\001\024\001\001\001\000\000\025\001\096\000\097\000\
\030\001\030\001\032\001\032\001\022\001\101\000\001\001\002\001\
\003\001\004\001\034\001\001\001\002\001\003\001\004\001\022\001\
\001\001\002\001\003\001\004\001\022\001\001\001\002\001\003\001\
\004\001\020\001\021\001\021\001\126\000\127\000\020\001\025\001\
\015\001\015\001\132\000\020\001\031\001\133\000\020\001\020\001\
\020\001\031\001\024\001\001\001\021\001\021\001\031\001\025\001\
\018\001\019\001\148\000\031\001\001\001\149\000\001\001\011\001\
\026\001\027\001\014\001\157\000\016\001\017\001\018\001\019\001\
\024\001\021\001\020\001\023\001\024\001\025\001\026\001\027\001\
\001\001\001\001\001\001\006\001\011\001\023\001\174\000\175\000\
\176\000\016\001\017\001\018\001\019\001\023\001\020\001\001\001\
\024\001\185\000\011\001\026\001\027\001\014\001\020\001\016\001\
\017\001\018\001\019\001\015\001\021\001\023\001\023\001\024\001\
\025\001\011\001\021\001\015\001\014\001\020\001\016\001\017\001\
\018\001\019\001\015\001\021\001\023\001\023\001\024\001\025\001\
\011\001\023\001\021\001\014\001\024\001\016\001\017\001\001\001\
\021\001\025\001\021\001\021\001\023\001\024\001\025\001\011\001\
\024\001\021\001\014\001\022\001\016\001\017\001\024\001\011\001\
\001\001\021\001\014\001\023\001\024\001\025\001\001\001\011\001\
\001\001\021\001\014\001\023\001\024\001\025\001\023\001\015\001\
\023\001\021\001\020\001\023\001\024\001\025\001\014\001\034\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\015\001\021\001\026\001\027\001\034\001\034\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\001\001\026\001\027\001\021\001\025\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\001\001\026\001\027\001\024\001\001\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\024\001\026\001\027\001\024\001\024\001\026\001\027\001\
\016\001\017\001\018\001\019\001\016\001\017\001\018\001\019\001\
\024\001\020\001\026\001\027\001\021\001\020\001\026\001\027\001\
\016\001\017\001\018\001\019\001\012\001\020\001\001\001\024\001\
\020\001\000\000\026\001\027\001\021\001\024\001\021\001\021\001\
\000\000\006\001\021\001\024\001\024\001\021\001\024\001\021\001\
\023\001\111\000\023\001\021\001\021\001\112\000\131\000\023\001\
\023\001\141\000"

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
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 48 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 439 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 49 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 447 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 50 "parser.mly"
                                           ( Instantiate (_1, _2) )
# 455 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'inits) in
    Obj.repr(
# 51 "parser.mly"
                                                 ( InstantiateInit (_1, _2, _5) )
# 464 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 52 "parser.mly"
                                                 ( InstantiateArgs (_1, _2, _4) )
# 473 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 53 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 481 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 54 "parser.mly"
                                                        ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 490 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 55 "parser.mly"
                                                        ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 499 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 56 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 507 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 59 "parser.mly"
          ( [_1] )
# 514 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 60 "parser.mly"
                 ( _1 :: _2 )
# 522 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 530 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 538 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 67 "parser.mly"
                ( [_1] )
# 545 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 68 "parser.mly"
                        ( _1 :: _2 )
# 553 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 71 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = mk_stmt1 2 (Seq _7) } )
# 563 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "parser.mly"
         ( [] )
# 569 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 76 "parser.mly"
       ( [_1] )
# 576 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 77 "parser.mly"
                        ( _1::_3 )
# 584 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 80 "parser.mly"
         ( [_1] )
# 591 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 81 "parser.mly"
               ( _1 :: _2 )
# 599 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 84 "parser.mly"
                   ( _1::_2 )
# 607 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 85 "parser.mly"
                   ( [] )
# 613 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 88 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 621 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 89 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 629 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 90 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 636 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 91 "parser.mly"
                                                  ( mk_stmt1 4 (Send("self", _4, _6)) )
# 644 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 92 "parser.mly"
                                                    ( mk_stmt1 4 (Send ("sender", _4, _6)) )
# 652 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 93 "parser.mly"
                                                ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 661 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 94 "parser.mly"
                                ( mk_stmt1 2 (If(_2, _4, _6)) )
# 670 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 95 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 678 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
                                   ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 686 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 97 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 693 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 701 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 99 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 710 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 100 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 718 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 103 "parser.mly"
                 ( [] )
# 724 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 104 "parser.mly"
                 ( _1 )
# 731 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 739 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 108 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 748 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 111 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 755 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 112 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 762 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 113 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 769 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 114 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 776 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 784 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 116 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 792 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 117 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 800 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 808 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 119 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 816 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 120 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 824 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 121 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 832 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 122 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 840 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 123 "parser.mly"
                       ( _2 )
# 847 "parser.ml"
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
