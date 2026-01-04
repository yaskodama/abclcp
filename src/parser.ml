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
# 74 "parser.ml"
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
  288 (* SELECT *);
  289 (* CASE *);
  290 (* TIMEOUT *);
  291 (* ARROW *);
    0 (* EOF *);
  292 (* NEW *);
  293 (* VAR *);
  294 (* EQ *);
  295 (* DOT *);
  296 (* BECOME *);
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
\013\000\013\000\013\000\013\000\015\000\015\000\015\000\015\000\
\017\000\018\000\019\000\019\000\020\000\020\000\016\000\016\000\
\008\000\008\000\021\000\021\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\005\000\009\000\008\000\005\000\001\000\002\000\
\005\000\005\000\001\000\002\000\008\000\000\000\001\000\003\000\
\001\000\002\000\002\000\000\000\004\000\006\000\005\000\008\000\
\008\000\008\000\005\000\007\000\004\000\003\000\005\000\009\000\
\005\000\006\000\005\000\005\000\002\000\000\000\002\000\000\000\
\006\000\004\000\001\000\000\000\001\000\003\000\006\000\000\000\
\000\000\001\000\003\000\005\000\001\000\001\000\001\000\001\000\
\003\000\003\000\003\000\003\000\005\000\004\000\003\000\003\000\
\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\076\000\
\000\000\000\000\002\000\000\000\000\000\000\000\000\000\001\000\
\000\000\006\000\000\000\061\000\063\000\062\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\075\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\014\000\000\000\000\000\000\000\000\000\000\000\
\010\000\016\000\020\000\000\000\011\000\070\000\000\000\000\000\
\000\000\000\000\000\000\009\000\000\000\069\000\000\000\000\000\
\000\000\000\000\000\000\000\000\013\000\000\000\000\000\017\000\
\018\000\000\000\024\000\000\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\046\000\000\000\000\000\021\000\026\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\027\000\
\038\000\000\000\000\000\000\000\029\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\037\000\000\000\000\000\000\000\
\045\000\000\000\000\000\000\000\000\000\041\000\031\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\044\000\
\000\000\039\000\043\000\000\000\030\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\042\000\000\000\000\000\
\000\000\036\000\053\000\000\000\000\000\000\000\000\000\000\000\
\034\000\032\000\033\000\050\000\000\000\000\000\000\000\000\000\
\054\000\049\000\055\000\040\000"

let yydgoto = "\002\000\
\008\000\009\000\010\000\025\000\026\000\049\000\050\000\027\000\
\051\000\052\000\089\000\111\000\112\000\122\000\138\000\152\000\
\153\000\166\000\188\000\189\000\000\000"

let yysindex = "\005\000\
\031\255\000\000\030\000\021\255\043\255\044\255\048\255\000\000\
\051\000\069\255\000\000\121\255\013\255\046\255\055\255\000\000\
\056\255\000\000\059\255\000\000\000\000\000\000\121\255\073\255\
\051\255\243\255\063\255\085\255\005\255\131\255\000\000\121\255\
\173\255\070\255\121\255\121\255\121\255\121\255\121\255\121\255\
\121\255\121\255\121\255\065\255\071\255\093\255\094\255\098\255\
\097\255\081\255\006\255\097\255\104\255\179\255\087\255\000\000\
\121\255\243\255\033\000\033\000\088\255\088\255\243\255\243\255\
\243\255\243\255\000\000\121\255\107\255\124\255\125\255\119\255\
\000\000\000\000\000\000\123\255\000\000\000\000\132\255\134\255\
\150\255\121\255\121\255\000\000\121\255\000\000\120\255\140\255\
\153\255\193\255\207\255\161\255\000\000\150\255\157\255\000\000\
\000\000\169\255\000\000\064\255\000\000\027\255\202\255\025\255\
\194\255\121\255\064\255\191\255\213\255\214\255\195\255\064\255\
\121\255\121\255\208\255\187\255\189\255\190\255\121\255\143\255\
\064\255\209\255\000\000\249\255\002\000\000\000\000\000\221\255\
\003\000\108\255\019\000\021\000\023\000\225\255\064\255\000\000\
\000\000\227\254\144\255\117\255\000\000\008\000\013\000\018\000\
\006\000\020\000\024\000\064\255\000\000\047\000\052\000\032\000\
\000\000\056\000\239\255\054\000\060\000\000\000\000\000\059\000\
\121\255\121\255\121\255\077\000\070\000\057\000\058\000\000\000\
\071\000\000\000\000\000\068\000\000\000\074\000\075\000\076\000\
\064\255\096\000\078\000\079\000\121\255\000\000\080\000\081\000\
\082\000\000\000\000\000\086\000\083\000\064\255\064\255\088\000\
\000\000\000\000\000\000\000\000\097\000\087\000\089\000\090\000\
\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\101\001\000\000\092\000\000\000\000\000\000\000\000\000\
\102\001\000\000\159\255\000\000\000\000\000\000\000\000\000\000\
\094\000\239\254\000\000\000\000\000\000\000\000\000\000\092\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\105\000\093\000\000\000\000\000\000\000\000\000\
\092\000\004\255\049\000\055\000\017\000\029\000\142\255\043\000\
\061\000\063\000\000\000\092\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\098\000\000\000\000\000\000\000\092\000\000\000\000\000\099\000\
\000\000\000\000\000\000\000\000\000\000\098\000\000\000\000\000\
\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\095\000\000\000\000\000\000\000\000\000\100\000\
\000\000\092\000\000\000\000\000\000\000\000\000\000\000\000\000\
\095\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\101\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\092\000\092\000\092\000\026\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\104\000\000\000\000\000\092\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\106\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\001\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\012\000\000\000\000\000\234\255\065\001\007\000\224\255\
\000\000\000\000\026\001\146\255\158\255\000\001\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 382
let yytable = "\055\000\
\033\000\127\000\007\000\150\000\151\000\001\000\007\000\054\000\
\121\000\046\000\047\000\047\000\058\000\059\000\060\000\061\000\
\062\000\063\000\064\000\065\000\066\000\018\000\121\000\008\000\
\079\000\116\000\035\000\008\000\031\000\011\000\003\000\004\000\
\035\000\035\000\035\000\080\000\149\000\035\000\005\000\012\000\
\113\000\048\000\048\000\013\000\014\000\114\000\035\000\035\000\
\015\000\164\000\016\000\028\000\092\000\117\000\118\000\072\000\
\004\000\035\000\075\000\090\000\091\000\006\000\035\000\005\000\
\102\000\035\000\029\000\007\000\030\000\004\000\103\000\104\000\
\105\000\034\000\035\000\106\000\005\000\032\000\186\000\198\000\
\199\000\129\000\044\000\120\000\107\000\045\000\006\000\067\000\
\057\000\068\000\128\000\017\000\007\000\069\000\070\000\108\000\
\134\000\144\000\071\000\006\000\109\000\046\000\073\000\110\000\
\076\000\007\000\078\000\157\000\019\000\020\000\021\000\022\000\
\040\000\041\000\042\000\043\000\155\000\019\000\020\000\021\000\
\022\000\019\000\020\000\021\000\022\000\081\000\023\000\143\000\
\174\000\175\000\176\000\019\000\020\000\021\000\022\000\023\000\
\156\000\082\000\083\000\023\000\084\000\085\000\093\000\024\000\
\019\000\020\000\021\000\022\000\192\000\023\000\088\000\086\000\
\024\000\087\000\071\000\135\000\024\000\036\000\037\000\038\000\
\039\000\071\000\023\000\094\000\071\000\071\000\053\000\040\000\
\041\000\042\000\043\000\064\000\095\000\064\000\064\000\064\000\
\064\000\100\000\064\000\154\000\098\000\064\000\064\000\064\000\
\064\000\064\000\064\000\036\000\037\000\038\000\039\000\101\000\
\056\000\036\000\037\000\038\000\039\000\040\000\041\000\042\000\
\043\000\077\000\115\000\040\000\041\000\042\000\043\000\036\000\
\037\000\038\000\039\000\123\000\119\000\124\000\125\000\096\000\
\126\000\040\000\041\000\042\000\043\000\036\000\037\000\038\000\
\039\000\131\000\130\000\132\000\133\000\097\000\137\000\040\000\
\041\000\042\000\043\000\036\000\037\000\038\000\039\000\036\000\
\037\000\038\000\039\000\141\000\148\000\040\000\041\000\042\000\
\043\000\040\000\041\000\042\000\043\000\036\000\037\000\038\000\
\039\000\036\000\037\000\038\000\039\000\170\000\139\000\040\000\
\041\000\042\000\043\000\040\000\041\000\042\000\043\000\069\000\
\069\000\069\000\069\000\145\000\140\000\146\000\142\000\147\000\
\161\000\069\000\069\000\069\000\069\000\067\000\158\000\067\000\
\067\000\067\000\067\000\159\000\067\000\160\000\162\000\067\000\
\067\000\068\000\163\000\068\000\068\000\068\000\068\000\165\000\
\068\000\038\000\039\000\068\000\068\000\168\000\167\000\072\000\
\169\000\040\000\041\000\042\000\043\000\065\000\072\000\065\000\
\065\000\072\000\072\000\066\000\065\000\066\000\066\000\065\000\
\065\000\073\000\066\000\074\000\171\000\066\000\066\000\172\000\
\073\000\173\000\074\000\073\000\073\000\074\000\074\000\177\000\
\178\000\181\000\182\000\179\000\180\000\183\000\184\000\185\000\
\187\000\201\000\190\000\191\000\003\000\004\000\193\000\194\000\
\195\000\196\000\197\000\200\000\202\000\015\000\203\000\057\000\
\204\000\058\000\019\000\074\000\028\000\022\000\023\000\099\000\
\136\000\025\000\056\000\052\000\000\000\051\000"

let yycheck = "\032\000\
\023\000\112\000\020\001\033\001\034\001\001\000\024\001\030\000\
\107\000\005\001\006\001\006\001\035\000\036\000\037\000\038\000\
\039\000\040\000\041\000\042\000\043\000\010\000\121\000\020\001\
\057\000\001\001\001\001\024\001\017\000\000\000\000\001\001\001\
\007\001\008\001\009\001\068\000\135\000\012\001\008\001\019\001\
\014\001\037\001\037\001\001\001\001\001\019\001\021\001\022\001\
\001\001\148\000\000\000\039\001\085\000\029\001\030\001\049\000\
\001\001\032\001\052\000\082\000\083\000\031\001\037\001\008\001\
\001\001\040\001\021\001\037\001\014\001\001\001\007\001\008\001\
\009\001\001\001\024\001\012\001\008\001\019\001\177\000\190\000\
\191\000\114\000\020\001\106\000\021\001\001\001\031\001\023\001\
\019\001\019\001\113\000\023\001\037\001\001\001\001\001\032\001\
\119\000\130\000\001\001\031\001\037\001\005\001\022\001\040\001\
\001\001\037\001\020\001\140\000\001\001\002\001\003\001\004\001\
\025\001\026\001\027\001\028\001\139\000\001\001\002\001\003\001\
\004\001\001\001\002\001\003\001\004\001\019\001\019\001\020\001\
\161\000\162\000\163\000\001\001\002\001\003\001\004\001\019\001\
\020\001\014\001\014\001\019\001\022\001\019\001\023\001\036\001\
\001\001\002\001\003\001\004\001\181\000\019\001\001\001\020\001\
\036\001\020\001\013\001\013\001\036\001\015\001\016\001\017\001\
\018\001\020\001\019\001\024\001\023\001\024\001\036\001\025\001\
\026\001\027\001\028\001\013\001\020\001\015\001\016\001\017\001\
\018\001\021\001\020\001\036\001\020\001\023\001\024\001\025\001\
\026\001\027\001\028\001\015\001\016\001\017\001\018\001\023\001\
\020\001\015\001\016\001\017\001\018\001\025\001\026\001\027\001\
\028\001\023\001\001\001\025\001\026\001\027\001\028\001\015\001\
\016\001\017\001\018\001\021\001\019\001\001\001\001\001\023\001\
\022\001\025\001\026\001\027\001\028\001\015\001\016\001\017\001\
\018\001\039\001\019\001\039\001\039\001\023\001\022\001\025\001\
\026\001\027\001\028\001\015\001\016\001\017\001\018\001\015\001\
\016\001\017\001\018\001\023\001\020\001\025\001\026\001\027\001\
\028\001\025\001\026\001\027\001\028\001\015\001\016\001\017\001\
\018\001\015\001\016\001\017\001\018\001\023\001\014\001\025\001\
\026\001\027\001\028\001\025\001\026\001\027\001\028\001\015\001\
\016\001\017\001\018\001\001\001\019\001\001\001\020\001\001\001\
\019\001\025\001\026\001\027\001\028\001\013\001\023\001\015\001\
\016\001\017\001\018\001\023\001\020\001\020\001\019\001\023\001\
\024\001\013\001\019\001\015\001\016\001\017\001\018\001\001\001\
\020\001\017\001\018\001\023\001\024\001\022\001\003\001\013\001\
\001\001\025\001\026\001\027\001\028\001\013\001\020\001\015\001\
\016\001\023\001\024\001\013\001\020\001\015\001\016\001\023\001\
\024\001\013\001\020\001\013\001\023\001\023\001\024\001\020\001\
\020\001\023\001\020\001\023\001\024\001\023\001\024\001\011\001\
\019\001\019\001\023\001\035\001\035\001\020\001\020\001\020\001\
\001\001\001\001\021\001\021\001\000\000\000\000\023\001\023\001\
\023\001\020\001\024\001\020\001\022\001\005\001\022\001\020\001\
\023\001\020\001\022\001\051\000\022\001\020\001\020\001\094\000\
\121\000\022\001\022\001\020\001\255\255\020\001"

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
# 395 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 34 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 401 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 37 "parser.mly"
         ( [_1] )
# 408 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 38 "parser.mly"
                   ( [_1] )
# 415 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 39 "parser.mly"
                         ( _1 :: _3 )
# 423 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 40 "parser.mly"
               ( _1 :: _2 )
# 431 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 43 "parser.mly"
                             ( [_1] )
# 438 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 44 "parser.mly"
                               ( _1 @ [_3] )
# 446 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 47 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 455 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 48 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 463 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 49 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 471 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 50 "parser.mly"
                                                        ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 480 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 51 "parser.mly"
                                                        ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 489 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 52 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 497 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 55 "parser.mly"
          ( [_1] )
# 504 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 56 "parser.mly"
                 ( _1 :: _2 )
# 512 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 59 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 520 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 60 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 528 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 63 "parser.mly"
                ( [_1] )
# 535 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 64 "parser.mly"
                        ( _1 :: _2 )
# 543 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 67 "parser.mly"
                                                           (
    { mname = _2; params = _4; body = mk_stmt1 2 (Seq _7) } )
# 553 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "parser.mly"
       ( [] )
# 559 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 72 "parser.mly"
       ( [_1] )
# 566 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 73 "parser.mly"
                        ( _1::_3 )
# 574 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 76 "parser.mly"
         ( [_1] )
# 581 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 77 "parser.mly"
               ( _1 :: _2 )
# 589 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 80 "parser.mly"
                   ( _1::_2 )
# 597 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "parser.mly"
                   ( [] )
# 603 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 611 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 85 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 619 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 86 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 626 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 87 "parser.mly"
                                                  ( mk_stmt1 4 (Send("self", _4, _6)) )
# 634 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 88 "parser.mly"
                                                    ( mk_stmt1 4 (Send ("sender", _4, _6)) )
# 642 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 89 "parser.mly"
                                                ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 651 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 90 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 659 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 91 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 668 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 92 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 676 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 93 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 683 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 94 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 691 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 95 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 700 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 96 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 708 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 97 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 716 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 98 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 723 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'select_cases) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'select_timeout_opt) in
    Obj.repr(
# 99 "parser.mly"
                                                         ( mk_stmt1 3 (Select(_3, _4)) )
# 731 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 102 "parser.mly"
                             ( _1 @ [_2] )
# 739 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 103 "parser.mly"
                             ( [] )
# 745 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 106 "parser.mly"
                             ( _1 @ [_2] )
# 753 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 107 "parser.mly"
                             ( [] )
# 759 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'select_pat) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 111 "parser.mly"
    ( { pat = _2; body = mk_stmt1 5 (Seq(_5)) } )
# 767 "parser.ml"
               : 'select_case))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opt_id_list) in
    Obj.repr(
# 115 "parser.mly"
    ( { meth = _1; vars = _3 } )
# 775 "parser.ml"
               : 'select_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 118 "parser.mly"
            ( _1 )
# 782 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 119 "parser.mly"
                ( [] )
# 788 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 122 "parser.mly"
                         ( [_1] )
# 795 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 123 "parser.mly"
                      ( _1 @ [_3] )
# 803 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 127 "parser.mly"
      ( (Some _2, Some (mk_stmt1 5 (Seq _5))) )
# 811 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 129 "parser.mly"
      ( (None, None) )
# 817 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 132 "parser.mly"
                 ( [] )
# 823 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 133 "parser.mly"
                 ( _1 )
# 830 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 136 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 838 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 137 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 847 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 140 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 854 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 141 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 861 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 142 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 868 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 143 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 875 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 144 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 883 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 145 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 891 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 146 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 899 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 147 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 907 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 148 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 915 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 149 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 923 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 150 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 931 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 151 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 939 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 152 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 947 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 153 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 955 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 154 "parser.mly"
                       ( _2 )
# 962 "parser.ml"
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
