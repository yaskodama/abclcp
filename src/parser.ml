type token =
  | ID of (
# 31 "parser.mly"
        string
# 6 "parser.ml"
)
  | FLOATLIT of (
# 32 "parser.mly"
        float
# 11 "parser.ml"
)
  | INTLIT of (
# 33 "parser.mly"
        int
# 16 "parser.ml"
)
  | STRINGLIT of (
# 34 "parser.mly"
        string
# 21 "parser.ml"
)
  | METHOD
  | FLOAT
  | CALL
  | SEND
  | UNSAFESEND
  | REMOTE
  | NOW
  | FUTURE
  | AWAIT
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
  | COLON
  | PLUSPLUS
  | BANG

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

(* 戻り値型注釈で書ける型名。
   基底型のほかに、大文字始まりの名前は actor 型として受ける。 *)
let ty_of_name (loc : Location.t) (s : string) : Types.ty =
  match s with
  | "int"    -> Types.TInt
  | "float"  -> Types.TFloat
  | "string" -> Types.TString
  | "bool"   -> Types.TBool
  | "unit"   -> Types.TUnit
  | "any"    -> Types.TAny
  | _ ->
      if String.length s > 0 && s.[0] >= 'A' && s.[0] <= 'Z' then
        Types.TActor (s, [])
      else
        raise (Syntax_error (loc,
          "unknown type name in return annotation: " ^ s
          ^ " (expected int/float/string/bool/unit/any or a class name)"))
# 100 "parser.ml"
let yytransl_const = [|
  261 (* METHOD *);
  262 (* FLOAT *);
  263 (* CALL *);
  264 (* SEND *);
  265 (* UNSAFESEND *);
  266 (* REMOTE *);
  267 (* NOW *);
  268 (* FUTURE *);
  269 (* AWAIT *);
  270 (* IF *);
  271 (* THEN *);
  272 (* ELSE *);
  273 (* WHILE *);
  274 (* DO *);
  275 (* ASSIGN *);
  276 (* PLUS *);
  277 (* MINUS *);
  278 (* TIMES *);
  279 (* DIV *);
  280 (* LPAREN *);
  281 (* RPAREN *);
  282 (* LBRACE *);
  283 (* RBRACE *);
  284 (* SEMICOLON *);
  285 (* COMMA *);
  286 (* GE *);
  287 (* LE *);
  288 (* GT *);
  289 (* LT *);
  290 (* SELF *);
  291 (* SENDER *);
  292 (* CLASS *);
  293 (* SELECT *);
  294 (* CASE *);
  295 (* TIMEOUT *);
  296 (* ARROW *);
    0 (* EOF *);
  297 (* NEW *);
  298 (* VAR *);
  299 (* EQ *);
  300 (* DOT *);
  301 (* BECOME *);
  302 (* COLON *);
  303 (* PLUSPLUS *);
  304 (* BANG *);
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
\007\000\010\000\010\000\008\000\008\000\011\000\013\000\013\000\
\014\000\014\000\014\000\016\000\016\000\012\000\012\000\012\000\
\002\000\002\000\015\000\015\000\019\000\019\000\018\000\018\000\
\018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
\018\000\018\000\018\000\018\000\018\000\018\000\018\000\020\000\
\020\000\020\000\020\000\022\000\023\000\024\000\024\000\017\000\
\017\000\021\000\021\000\009\000\009\000\025\000\025\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\005\000\009\000\008\000\008\000\005\000\001\000\
\002\000\005\000\005\000\001\000\002\000\010\000\000\000\002\000\
\000\000\003\000\004\000\001\000\001\000\000\000\001\000\003\000\
\001\000\006\000\001\000\002\000\002\000\000\000\004\000\006\000\
\005\000\008\000\008\000\008\000\008\000\005\000\007\000\004\000\
\003\000\005\000\009\000\005\000\006\000\005\000\005\000\002\000\
\000\000\002\000\000\000\006\000\004\000\001\000\000\000\001\000\
\003\000\006\000\000\000\000\000\001\000\003\000\005\000\001\000\
\001\000\001\000\001\000\003\000\003\000\003\000\003\000\003\000\
\005\000\007\000\011\000\007\000\002\000\006\000\004\000\003\000\
\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\093\000\000\000\000\000\002\000\000\000\033\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\006\000\000\000\072\000\
\074\000\073\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\092\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\015\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\010\000\017\000\021\000\
\000\000\011\000\087\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\009\000\000\000\000\000\
\000\000\000\000\081\000\034\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\013\000\014\000\
\000\000\000\000\018\000\019\000\000\000\000\000\084\000\032\000\
\000\000\000\000\012\000\000\000\029\000\028\000\024\000\000\000\
\000\000\000\000\000\000\000\000\000\000\064\000\026\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\027\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\057\000\000\000\000\000\022\000\036\000\065\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\037\000\049\000\000\000\000\000\000\000\039\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\048\000\
\000\000\000\000\000\000\056\000\000\000\000\000\000\000\000\000\
\052\000\041\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\055\000\000\000\050\000\054\000\000\000\
\040\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\053\000\000\000\000\000\000\000\000\000\047\000\
\000\000\000\000\000\000\000\000\000\000\042\000\043\000\044\000\
\045\000\061\000\000\000\000\000\000\000\060\000\066\000\051\000"

let yydgoto = "\002\000\
\009\000\016\000\010\000\011\000\032\000\033\000\064\000\065\000\
\034\000\066\000\067\000\120\000\138\000\145\000\163\000\143\000\
\152\000\164\000\178\000\196\000\211\000\212\000\226\000\250\000\
\000\000"

let yysindex = "\016\000\
\004\255\000\000\035\000\055\255\052\255\052\255\059\255\073\255\
\000\000\089\000\060\255\000\000\183\255\000\000\084\255\053\255\
\067\255\072\255\098\255\000\000\074\255\000\000\096\255\000\000\
\000\000\000\000\052\255\052\255\183\255\183\255\124\255\090\255\
\192\000\101\255\123\255\130\255\131\255\001\255\187\255\000\000\
\183\255\089\255\094\255\060\000\080\000\115\255\183\255\183\255\
\183\255\183\255\183\255\183\255\183\255\183\255\183\255\183\255\
\113\255\114\255\120\255\121\255\141\255\159\255\160\255\157\255\
\139\255\002\255\157\255\166\255\098\000\143\255\169\255\170\255\
\171\255\000\000\183\255\192\000\248\255\248\255\118\255\118\255\
\192\000\192\000\192\000\192\000\102\000\000\000\168\255\183\255\
\183\255\149\255\156\255\164\255\151\255\000\000\000\000\000\000\
\173\255\000\000\000\000\182\255\184\255\176\255\185\255\190\255\
\192\255\193\255\220\255\183\255\183\255\000\000\183\255\183\255\
\183\255\183\255\000\000\000\000\195\255\198\255\202\255\210\255\
\116\000\134\000\225\255\227\255\235\255\192\000\000\000\000\000\
\220\255\181\255\000\000\000\000\212\255\214\255\000\000\000\000\
\036\255\234\255\000\000\030\000\000\000\000\000\000\000\247\255\
\012\000\246\255\009\255\092\255\183\255\000\000\000\000\076\255\
\054\255\039\000\031\255\052\255\017\000\183\255\092\255\024\000\
\051\000\056\000\033\000\092\255\192\000\000\000\061\000\183\255\
\183\255\045\000\020\000\028\000\032\000\042\000\183\255\254\255\
\092\255\047\000\000\000\065\000\063\000\000\000\000\000\000\000\
\152\000\069\000\111\255\087\000\094\000\095\000\097\000\170\000\
\092\255\000\000\000\000\046\255\201\255\152\255\000\000\076\000\
\078\000\083\000\085\000\090\000\091\000\092\000\092\255\000\000\
\139\000\114\000\115\000\000\000\140\000\188\000\122\000\118\000\
\000\000\000\000\123\000\183\255\183\255\183\255\183\255\136\000\
\129\000\119\000\120\000\000\000\137\000\000\000\000\000\130\000\
\000\000\143\000\144\000\145\000\146\000\092\255\175\000\151\000\
\153\000\183\255\000\000\150\000\158\000\159\000\160\000\000\000\
\165\000\164\000\092\255\092\255\171\000\000\000\000\000\000\000\
\000\000\000\000\177\000\178\000\169\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\198\001\000\000\181\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\207\001\000\000\216\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\201\000\
\245\254\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\181\000\000\000\000\000\027\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\223\000\202\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\181\000\025\255\038\000\050\000\014\000\026\000\
\191\255\209\000\226\000\231\000\204\255\000\000\000\000\181\000\
\181\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\211\000\000\000\000\000\000\000\181\000\181\000\
\181\000\000\000\000\000\000\000\000\000\000\000\220\000\000\000\
\000\000\000\000\000\000\000\000\000\000\243\000\000\000\000\000\
\211\000\246\254\000\000\000\000\210\000\236\255\000\000\000\000\
\000\000\221\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\219\000\000\000\
\000\000\000\000\000\000\225\000\248\000\000\000\000\000\000\000\
\181\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\219\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\235\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\181\000\181\000\181\000\181\000\050\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\228\000\000\000\
\000\000\181\000\000\000\000\000\000\000\000\000\000\000\000\000\
\233\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\210\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\003\000\018\000\000\000\000\000\228\255\184\001\040\000\
\215\255\000\000\000\000\134\001\000\000\000\000\095\255\000\000\
\025\001\112\255\090\001\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yytablesize = 543
let yytable = "\070\000\
\044\000\045\000\183\000\003\000\004\000\061\000\062\000\062\000\
\017\000\150\000\069\000\005\000\006\000\007\000\177\000\023\000\
\001\000\007\000\076\000\077\000\078\000\079\000\080\000\081\000\
\082\000\083\000\084\000\085\000\022\000\042\000\043\000\014\000\
\177\000\103\000\012\000\151\000\141\000\023\000\040\000\007\000\
\015\000\142\000\063\000\063\000\085\000\008\000\105\000\106\000\
\208\000\008\000\046\000\085\000\014\000\008\000\085\000\085\000\
\046\000\046\000\046\000\018\000\004\000\015\000\224\000\046\000\
\171\000\172\000\046\000\005\000\006\000\123\000\124\000\125\000\
\168\000\019\000\004\000\046\000\046\000\169\000\013\000\121\000\
\122\000\005\000\006\000\209\000\210\000\126\000\046\000\021\000\
\020\000\003\001\004\001\046\000\153\000\248\000\046\000\007\000\
\036\000\038\000\154\000\155\000\156\000\008\000\166\000\093\000\
\167\000\157\000\096\000\035\000\158\000\007\000\037\000\023\000\
\024\000\025\000\026\000\008\000\039\000\159\000\047\000\041\000\
\165\000\027\000\028\000\029\000\046\000\057\000\058\000\186\000\
\160\000\176\000\059\000\060\000\071\000\161\000\030\000\201\000\
\162\000\072\000\075\000\185\000\086\000\090\000\087\000\088\000\
\089\000\202\000\192\000\052\000\053\000\054\000\055\000\031\000\
\023\000\024\000\025\000\026\000\216\000\173\000\174\000\091\000\
\092\000\061\000\027\000\028\000\029\000\094\000\097\000\099\000\
\214\000\100\000\101\000\104\000\107\000\102\000\108\000\030\000\
\215\000\110\000\234\000\235\000\236\000\237\000\109\000\023\000\
\024\000\025\000\026\000\023\000\024\000\025\000\026\000\114\000\
\031\000\027\000\028\000\029\000\111\000\027\000\028\000\029\000\
\253\000\023\000\024\000\025\000\026\000\112\000\030\000\113\000\
\088\000\115\000\030\000\027\000\028\000\029\000\116\000\088\000\
\117\000\118\000\088\000\088\000\119\000\076\000\127\000\031\000\
\030\000\128\000\137\000\068\000\076\000\088\000\129\000\076\000\
\076\000\075\000\130\000\075\000\075\000\075\000\075\000\139\000\
\075\000\213\000\076\000\075\000\075\000\075\000\075\000\075\000\
\075\000\133\000\076\000\134\000\140\000\082\000\075\000\082\000\
\082\000\082\000\082\000\135\000\082\000\149\000\075\000\082\000\
\082\000\082\000\082\000\082\000\082\000\050\000\051\000\193\000\
\147\000\048\000\049\000\050\000\051\000\052\000\053\000\054\000\
\055\000\144\000\082\000\052\000\053\000\054\000\055\000\079\000\
\146\000\079\000\079\000\079\000\079\000\148\000\079\000\170\000\
\175\000\079\000\079\000\080\000\056\000\080\000\080\000\080\000\
\080\000\179\000\080\000\180\000\079\000\080\000\080\000\077\000\
\181\000\077\000\077\000\182\000\079\000\184\000\077\000\188\000\
\080\000\077\000\077\000\078\000\187\000\078\000\078\000\189\000\
\080\000\195\000\078\000\190\000\077\000\078\000\078\000\048\000\
\049\000\050\000\051\000\197\000\077\000\191\000\198\000\203\000\
\078\000\052\000\053\000\054\000\055\000\200\000\204\000\205\000\
\078\000\206\000\073\000\048\000\049\000\050\000\051\000\217\000\
\074\000\218\000\056\000\219\000\220\000\052\000\053\000\054\000\
\055\000\221\000\222\000\223\000\227\000\048\000\049\000\050\000\
\051\000\048\000\049\000\050\000\051\000\098\000\056\000\052\000\
\053\000\054\000\055\000\052\000\053\000\054\000\055\000\048\000\
\049\000\050\000\051\000\225\000\229\000\228\000\232\000\131\000\
\056\000\052\000\053\000\054\000\055\000\231\000\233\000\238\000\
\239\000\048\000\049\000\050\000\051\000\243\000\240\000\241\000\
\242\000\132\000\056\000\052\000\053\000\054\000\055\000\244\000\
\245\000\246\000\247\000\048\000\049\000\050\000\051\000\150\000\
\251\000\254\000\252\000\199\000\056\000\052\000\053\000\054\000\
\055\000\255\000\000\001\001\001\002\001\048\000\049\000\050\000\
\051\000\167\000\207\000\005\001\008\001\003\000\056\000\052\000\
\053\000\054\000\055\000\006\001\007\001\068\000\004\000\048\000\
\049\000\050\000\051\000\048\000\049\000\050\000\051\000\230\000\
\056\000\052\000\053\000\054\000\055\000\052\000\053\000\054\000\
\055\000\069\000\089\000\016\000\020\000\081\000\081\000\081\000\
\081\000\089\000\056\000\030\000\089\000\089\000\056\000\081\000\
\081\000\081\000\081\000\090\000\031\000\038\000\025\000\089\000\
\091\000\095\000\090\000\035\000\063\000\090\000\090\000\091\000\
\081\000\062\000\091\000\091\000\086\000\067\000\136\000\249\000\
\090\000\083\000\194\000\086\000\000\000\091\000\086\000\086\000\
\083\000\000\000\000\000\083\000\083\000\000\000\000\000\000\000\
\000\000\086\000\000\000\000\000\000\000\000\000\083\000"

let yycheck = "\041\000\
\029\000\030\000\164\000\000\001\001\001\005\001\006\001\006\001\
\006\000\001\001\039\000\008\001\009\001\025\001\159\000\026\001\
\001\000\029\001\047\000\048\000\049\000\050\000\051\000\052\000\
\053\000\054\000\055\000\056\000\011\000\027\000\028\000\001\001\
\177\000\075\000\000\000\027\001\001\001\048\001\021\000\036\001\
\010\001\006\001\042\001\042\001\018\001\042\001\088\000\089\000\
\193\000\025\001\001\001\025\001\001\001\029\001\028\001\029\001\
\007\001\008\001\009\001\001\001\001\001\010\001\207\000\014\001\
\034\001\035\001\017\001\008\001\009\001\111\000\112\000\113\000\
\019\001\001\001\001\001\026\001\027\001\024\001\024\001\108\000\
\109\000\008\001\009\001\038\001\039\001\114\000\037\001\028\001\
\000\000\251\000\252\000\042\001\001\001\238\000\045\001\036\001\
\044\001\026\001\007\001\008\001\009\001\042\001\027\001\064\000\
\029\001\014\001\067\000\024\001\017\001\036\001\044\001\001\001\
\002\001\003\001\004\001\042\001\019\001\026\001\029\001\024\001\
\149\000\011\001\012\001\013\001\001\001\025\001\004\001\169\000\
\037\001\158\000\001\001\001\001\044\001\042\001\024\001\025\001\
\045\001\044\001\024\001\168\000\028\001\001\001\029\001\024\001\
\024\001\187\000\175\000\030\001\031\001\032\001\033\001\041\001\
\001\001\002\001\003\001\004\001\198\000\155\000\156\000\001\001\
\001\001\005\001\011\001\012\001\013\001\027\001\001\001\025\001\
\197\000\001\001\001\001\004\001\024\001\003\001\019\001\024\001\
\025\001\027\001\220\000\221\000\222\000\223\000\019\001\001\001\
\002\001\003\001\004\001\001\001\002\001\003\001\004\001\016\001\
\041\001\011\001\012\001\013\001\024\001\011\001\012\001\013\001\
\242\000\001\001\002\001\003\001\004\001\024\001\024\001\024\001\
\018\001\025\001\024\001\011\001\012\001\013\001\025\001\025\001\
\025\001\025\001\028\001\029\001\001\001\018\001\028\001\041\001\
\024\001\028\001\046\001\041\001\025\001\039\001\029\001\028\001\
\029\001\018\001\025\001\020\001\021\001\022\001\023\001\028\001\
\025\001\041\001\039\001\028\001\029\001\030\001\031\001\032\001\
\033\001\025\001\047\001\025\001\039\001\018\001\039\001\020\001\
\021\001\022\001\023\001\025\001\025\001\016\001\047\001\028\001\
\029\001\030\001\031\001\032\001\033\001\022\001\023\001\018\001\
\026\001\020\001\021\001\022\001\023\001\030\001\031\001\032\001\
\033\001\048\001\047\001\030\001\031\001\032\001\033\001\018\001\
\003\001\020\001\021\001\022\001\023\001\026\001\025\001\001\001\
\024\001\028\001\029\001\018\001\047\001\020\001\021\001\022\001\
\023\001\026\001\025\001\001\001\039\001\028\001\029\001\018\001\
\001\001\020\001\021\001\027\001\047\001\001\001\025\001\044\001\
\039\001\028\001\029\001\018\001\024\001\020\001\021\001\044\001\
\047\001\027\001\025\001\044\001\039\001\028\001\029\001\020\001\
\021\001\022\001\023\001\019\001\047\001\044\001\024\001\001\001\
\039\001\030\001\031\001\032\001\033\001\025\001\001\001\001\001\
\047\001\001\001\039\001\020\001\021\001\022\001\023\001\028\001\
\025\001\028\001\047\001\025\001\024\001\030\001\031\001\032\001\
\033\001\024\001\024\001\024\001\003\001\020\001\021\001\022\001\
\023\001\020\001\021\001\022\001\023\001\028\001\047\001\030\001\
\031\001\032\001\033\001\030\001\031\001\032\001\033\001\020\001\
\021\001\022\001\023\001\001\001\001\001\027\001\025\001\028\001\
\047\001\030\001\031\001\032\001\033\001\028\001\028\001\016\001\
\024\001\020\001\021\001\022\001\023\001\028\001\040\001\040\001\
\024\001\028\001\047\001\030\001\031\001\032\001\033\001\025\001\
\025\001\025\001\025\001\020\001\021\001\022\001\023\001\001\001\
\026\001\028\001\026\001\028\001\047\001\030\001\031\001\032\001\
\033\001\028\001\028\001\028\001\025\001\020\001\021\001\022\001\
\023\001\029\001\025\001\025\001\028\001\000\000\047\001\030\001\
\031\001\032\001\033\001\027\001\027\001\025\001\000\000\020\001\
\021\001\022\001\023\001\020\001\021\001\022\001\023\001\028\001\
\047\001\030\001\031\001\032\001\033\001\030\001\031\001\032\001\
\033\001\025\001\018\001\005\001\027\001\020\001\021\001\022\001\
\023\001\025\001\047\001\025\001\028\001\029\001\047\001\030\001\
\031\001\032\001\033\001\018\001\025\001\027\001\026\001\039\001\
\018\001\066\000\025\001\027\001\025\001\028\001\029\001\025\001\
\047\001\025\001\028\001\029\001\018\001\027\001\129\000\239\000\
\039\001\018\001\177\000\025\001\255\255\039\001\028\001\029\001\
\025\001\255\255\255\255\028\001\029\001\255\255\255\255\255\255\
\255\255\039\001\255\255\255\255\255\255\255\255\039\001"

let yynames_const = "\
  METHOD\000\
  FLOAT\000\
  CALL\000\
  SEND\000\
  UNSAFESEND\000\
  REMOTE\000\
  NOW\000\
  FUTURE\000\
  AWAIT\000\
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
  COLON\000\
  PLUSPLUS\000\
  BANG\000\
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
# 55 "parser.mly"
              ( _1 )
# 504 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 510 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 59 "parser.mly"
         ( [_1] )
# 517 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 60 "parser.mly"
                   ( [_1] )
# 524 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 61 "parser.mly"
                         ( _1 :: _3 )
# 532 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 62 "parser.mly"
               ( _1 :: _2 )
# 540 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 65 "parser.mly"
                             ( [_1] )
# 547 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 66 "parser.mly"
                               ( _1 @ [_3] )
# 555 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 69 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 564 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 70 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 572 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 580 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 73 "parser.mly"
    ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 589 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 74 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 598 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 75 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (UnsafeSend (_2, _4, _6))) )
# 607 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 76 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 615 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 79 "parser.mly"
          ( [_1] )
# 622 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 80 "parser.mly"
                 ( _1 :: _2 )
# 630 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 638 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 84 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 646 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 87 "parser.mly"
                ( [_1] )
# 653 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 88 "parser.mly"
                        ( _1 :: _2 )
# 661 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'param_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : 'opt_ret) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'opt_eff) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 92 "parser.mly"
    ( { mname = _2; params = _4; ret = _6; eff = _7;
        body = mk_stmt1 2 (Seq _9) } )
# 673 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 96 "parser.mly"
                    ( None )
# 679 "parser.ml"
               : 'opt_ret))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ret_ann) in
    Obj.repr(
# 97 "parser.mly"
                    ( Some _2 )
# 686 "parser.ml"
               : 'opt_ret))
; (fun __caml_parser_env ->
    Obj.repr(
# 101 "parser.mly"
                                 ( None )
# 692 "parser.ml"
               : 'opt_eff))
; (fun __caml_parser_env ->
    Obj.repr(
# 102 "parser.mly"
                                 ( Some [] )
# 698 "parser.ml"
               : 'opt_eff))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'id_list) in
    Obj.repr(
# 103 "parser.mly"
                                 ( Some _3 )
# 705 "parser.ml"
               : 'opt_eff))
; (fun __caml_parser_env ->
    Obj.repr(
# 106 "parser.mly"
          ( Types.TFloat )
# 711 "parser.ml"
               : 'ret_ann))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 107 "parser.mly"
          ( ty_of_name (loc_of_rhs 1) _1 )
# 718 "parser.ml"
               : 'ret_ann))
; (fun __caml_parser_env ->
    Obj.repr(
# 110 "parser.mly"
       ( [] )
# 724 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 111 "parser.mly"
       ( [_1] )
# 731 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 112 "parser.mly"
                        ( _1::_3 )
# 739 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 115 "parser.mly"
                                                      ( LocalTarget _1 )
# 746 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 116 "parser.mly"
                                                      ( RemoteTarget (_3, _5) )
# 754 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 119 "parser.mly"
         ( [_1] )
# 761 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 120 "parser.mly"
               ( _1 :: _2 )
# 769 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 123 "parser.mly"
                   ( _1::_2 )
# 777 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 124 "parser.mly"
                   ( [] )
# 783 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 127 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 791 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 128 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 799 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 129 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 806 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 130 "parser.mly"
                                                  ( mk_stmt1 4 (Send(LocalTarget "self", _4, _6)) )
# 814 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 131 "parser.mly"
                                                    ( mk_stmt1 4 (Send (LocalTarget "sender", _4, _6)) )
# 822 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 132 "parser.mly"
                                                         ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 831 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 133 "parser.mly"
                                                               ( mk_stmt1 2 (UnsafeSend (_2, _4, _6)) )
# 840 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 134 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 848 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 135 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 857 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 136 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 865 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 137 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 872 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 138 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 880 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 139 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 889 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 140 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 897 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 141 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 905 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 142 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 912 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'select_cases) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'select_timeout_opt) in
    Obj.repr(
# 143 "parser.mly"
                                                         ( mk_stmt1 3 (Select(_3, _4)) )
# 920 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 146 "parser.mly"
                             ( _1 @ [_2] )
# 928 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 147 "parser.mly"
                             ( [] )
# 934 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 150 "parser.mly"
                             ( _1 @ [_2] )
# 942 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 151 "parser.mly"
                             ( [] )
# 948 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'select_pat) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 155 "parser.mly"
    ( { pat = _2; body = mk_stmt1 5 (Seq(_5)) } )
# 956 "parser.ml"
               : 'select_case))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opt_id_list) in
    Obj.repr(
# 159 "parser.mly"
    ( { meth = _1; vars = _3 } )
# 964 "parser.ml"
               : 'select_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 162 "parser.mly"
            ( _1 )
# 971 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 163 "parser.mly"
                ( [] )
# 977 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 166 "parser.mly"
                         ( [_1] )
# 984 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 167 "parser.mly"
                      ( _1 @ [_3] )
# 992 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 171 "parser.mly"
      ( (Some _2, Some (mk_stmt1 5 (Seq _5))) )
# 1000 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 173 "parser.mly"
      ( (None, None) )
# 1006 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 176 "parser.mly"
                 ( [] )
# 1012 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 177 "parser.mly"
                 ( _1 )
# 1019 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 180 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 1027 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 181 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 1036 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 184 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 1043 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 185 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 1050 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 186 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 1057 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 187 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 1064 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 188 "parser.mly"
                       ( mk_expr1 2 (Binop ("++", _1, _3)) )
# 1072 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 189 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 1080 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 190 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 1088 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 191 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 1096 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 192 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 1104 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 193 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 1112 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 195 "parser.mly"
      ( mk_expr1 1 (NowSend (_2, _4, _6, None)) )
# 1121 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 9 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 5 : 'args) in
    let _9 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _11 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 197 "parser.mly"
      ( mk_expr1 1 (NowSend (_2, _4, _6, Some (_9, _11))) )
# 1132 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 198 "parser.mly"
                                                 ( mk_expr1 1 (FutureSend (_2, _4, _6)) )
# 1141 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 199 "parser.mly"
               ( mk_expr1 1 (Await (_2, None)) )
# 1148 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 200 "parser.mly"
                                        ( mk_expr1 1 (Await (_2, Some (_4, _6))) )
# 1157 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 201 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 1165 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 202 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 1173 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 203 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 1181 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 204 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 1189 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 205 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 1197 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 206 "parser.mly"
                       ( _2 )
# 1204 "parser.ml"
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
