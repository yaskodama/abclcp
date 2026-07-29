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
# 98 "parser.ml"
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
\007\000\010\000\010\000\008\000\008\000\011\000\011\000\014\000\
\014\000\012\000\012\000\012\000\002\000\002\000\013\000\013\000\
\016\000\016\000\015\000\015\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\017\000\017\000\017\000\017\000\019\000\
\020\000\021\000\021\000\022\000\022\000\018\000\018\000\009\000\
\009\000\023\000\023\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\006\000\006\000\006\000\006\000\006\000\000\000"

let yylen = "\002\000\
\002\000\002\000\001\000\002\000\003\000\002\000\001\000\003\000\
\006\000\005\000\005\000\009\000\008\000\008\000\005\000\001\000\
\002\000\005\000\005\000\001\000\002\000\008\000\010\000\001\000\
\001\000\000\000\001\000\003\000\001\000\006\000\001\000\002\000\
\002\000\000\000\004\000\006\000\005\000\008\000\008\000\008\000\
\008\000\005\000\007\000\004\000\003\000\005\000\009\000\005\000\
\006\000\005\000\005\000\002\000\000\000\002\000\000\000\006\000\
\004\000\001\000\000\000\001\000\003\000\006\000\000\000\000\000\
\001\000\003\000\005\000\001\000\001\000\001\000\001\000\003\000\
\003\000\003\000\003\000\005\000\007\000\007\000\002\000\004\000\
\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\086\000\000\000\000\000\002\000\000\000\029\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\006\000\000\000\068\000\
\070\000\069\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\085\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\015\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\010\000\017\000\021\000\000\000\011\000\080\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\009\000\000\000\000\000\000\000\076\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\013\000\014\000\000\000\000\000\018\000\019\000\000\000\077\000\
\078\000\028\000\000\000\000\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\025\000\024\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\
\000\000\000\000\022\000\032\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\033\000\045\000\
\000\000\000\000\000\000\000\000\035\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\044\000\000\000\000\000\
\000\000\052\000\000\000\000\000\000\000\000\000\023\000\048\000\
\037\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\051\000\000\000\046\000\050\000\000\000\036\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\049\000\000\000\000\000\000\000\000\000\043\000\060\000\
\000\000\000\000\000\000\000\000\000\000\038\000\039\000\040\000\
\041\000\057\000\000\000\000\000\000\000\000\000\061\000\056\000\
\062\000\047\000"

let yydgoto = "\002\000\
\009\000\016\000\010\000\011\000\032\000\033\000\063\000\064\000\
\034\000\065\000\066\000\115\000\144\000\148\000\145\000\159\000\
\177\000\193\000\194\000\209\000\233\000\234\000\000\000"

let yysindex = "\009\000\
\072\255\000\000\018\000\005\255\004\255\004\255\034\255\051\255\
\000\000\071\000\082\255\000\000\176\255\000\000\030\255\038\255\
\040\255\062\255\070\255\000\000\093\255\000\000\069\255\000\000\
\000\000\000\000\004\255\004\255\176\255\176\255\102\255\076\255\
\189\255\087\255\103\255\118\255\121\255\001\255\190\255\000\000\
\176\255\081\255\086\255\189\255\236\255\112\255\176\255\176\255\
\176\255\176\255\176\255\176\255\176\255\176\255\176\255\098\255\
\108\255\120\255\127\255\144\255\151\255\152\255\154\255\133\255\
\253\254\154\255\160\255\250\255\141\255\166\255\167\255\000\000\
\176\255\189\255\193\255\193\255\142\255\142\255\189\255\189\255\
\189\255\189\255\000\000\172\255\176\255\176\255\157\255\163\255\
\164\255\158\255\000\000\000\000\000\000\175\255\000\000\000\000\
\180\255\184\255\165\255\188\255\202\255\203\255\229\255\176\255\
\176\255\000\000\176\255\176\255\176\255\000\000\000\000\201\255\
\204\255\211\255\208\255\008\000\022\000\217\255\218\255\226\255\
\000\000\000\000\229\255\246\254\000\000\000\000\246\255\000\000\
\000\000\000\000\078\255\011\255\000\000\050\255\019\000\003\255\
\004\255\251\255\176\255\078\255\234\255\020\000\031\000\252\255\
\078\255\000\000\000\000\007\000\176\255\176\255\010\000\247\255\
\249\255\002\000\004\000\176\255\232\255\078\255\024\000\000\000\
\028\000\025\000\000\000\000\000\078\255\036\000\068\000\130\255\
\082\000\097\000\099\000\100\000\040\000\078\255\000\000\000\000\
\024\255\194\255\145\255\078\000\000\000\108\000\110\000\103\000\
\101\000\115\000\118\000\119\000\078\255\000\000\143\000\142\000\
\120\000\000\000\145\000\054\000\121\000\123\000\000\000\000\000\
\000\000\122\000\176\255\176\255\176\255\176\255\135\000\128\000\
\113\000\114\000\000\000\131\000\000\000\000\000\129\000\000\000\
\133\000\134\000\136\000\137\000\078\255\155\000\138\000\139\000\
\176\255\000\000\132\000\140\000\141\000\144\000\000\000\000\000\
\146\000\147\000\078\255\078\255\148\000\000\000\000\000\000\000\
\000\000\000\000\162\000\150\000\151\000\152\000\000\000\000\000\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\166\001\000\000\149\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\167\001\000\000\216\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\154\000\
\026\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\149\000\000\000\000\000\028\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\165\000\156\000\000\000\000\000\000\000\000\000\000\000\000\000\
\149\000\036\255\092\000\098\000\074\000\086\000\088\255\104\000\
\106\000\112\000\000\000\000\000\149\000\149\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\157\000\000\000\
\000\000\000\000\149\000\149\000\149\000\000\000\000\000\000\000\
\000\000\159\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\157\000\000\000\000\000\000\000\058\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\158\000\000\000\000\000\000\000\000\000\
\160\000\000\000\000\000\000\000\000\000\149\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\158\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\161\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\149\000\149\000\149\000\149\000\033\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\164\000\000\000\000\000\
\149\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\166\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\058\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\003\000\037\000\000\000\000\000\228\255\110\001\034\000\
\215\255\000\000\000\000\058\001\119\255\000\000\131\255\028\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 447
let yytable = "\069\000\
\044\000\045\000\061\000\014\000\014\000\060\000\061\000\164\000\
\017\000\001\000\068\000\146\000\015\000\015\000\158\000\131\000\
\147\000\012\000\074\000\075\000\076\000\077\000\078\000\079\000\
\080\000\081\000\082\000\180\000\013\000\042\000\043\000\099\000\
\158\000\042\000\018\000\132\000\152\000\153\000\062\000\042\000\
\042\000\042\000\062\000\101\000\102\000\079\000\042\000\022\000\
\190\000\042\000\007\000\019\000\079\000\035\000\007\000\079\000\
\079\000\040\000\042\000\042\000\008\000\191\000\192\000\207\000\
\008\000\118\000\119\000\120\000\149\000\042\000\020\000\003\000\
\004\000\150\000\042\000\116\000\117\000\042\000\134\000\005\000\
\006\000\036\000\004\000\037\000\135\000\136\000\137\000\038\000\
\039\000\005\000\006\000\138\000\041\000\004\000\139\000\231\000\
\090\000\244\000\245\000\093\000\005\000\006\000\046\000\140\000\
\047\000\081\000\057\000\007\000\167\000\021\000\157\000\056\000\
\081\000\008\000\141\000\081\000\081\000\007\000\058\000\142\000\
\166\000\059\000\143\000\008\000\070\000\083\000\184\000\173\000\
\007\000\071\000\023\000\024\000\025\000\026\000\008\000\073\000\
\084\000\198\000\154\000\155\000\027\000\028\000\029\000\085\000\
\087\000\023\000\024\000\025\000\026\000\196\000\086\000\088\000\
\089\000\030\000\183\000\027\000\028\000\029\000\060\000\091\000\
\094\000\217\000\218\000\219\000\220\000\096\000\097\000\098\000\
\030\000\197\000\031\000\052\000\053\000\054\000\055\000\100\000\
\023\000\024\000\025\000\026\000\103\000\104\000\105\000\237\000\
\106\000\031\000\027\000\028\000\029\000\110\000\023\000\024\000\
\025\000\026\000\023\000\024\000\025\000\026\000\107\000\030\000\
\027\000\028\000\029\000\108\000\027\000\028\000\029\000\109\000\
\048\000\049\000\050\000\051\000\111\000\030\000\050\000\051\000\
\031\000\030\000\052\000\053\000\054\000\055\000\052\000\053\000\
\054\000\055\000\112\000\113\000\121\000\114\000\067\000\122\000\
\124\000\071\000\195\000\071\000\071\000\071\000\071\000\123\000\
\071\000\127\000\128\000\071\000\071\000\071\000\071\000\071\000\
\071\000\174\000\129\000\048\000\049\000\050\000\051\000\048\000\
\049\000\050\000\051\000\160\000\072\000\052\000\053\000\054\000\
\055\000\052\000\053\000\054\000\055\000\048\000\049\000\050\000\
\051\000\133\000\156\000\151\000\161\000\095\000\163\000\052\000\
\053\000\054\000\055\000\048\000\049\000\050\000\051\000\162\000\
\165\000\168\000\169\000\125\000\170\000\052\000\053\000\054\000\
\055\000\048\000\049\000\050\000\051\000\171\000\178\000\172\000\
\179\000\126\000\176\000\052\000\053\000\054\000\055\000\048\000\
\049\000\050\000\051\000\048\000\049\000\050\000\051\000\181\000\
\189\000\052\000\053\000\054\000\055\000\052\000\053\000\054\000\
\055\000\048\000\049\000\050\000\051\000\076\000\076\000\076\000\
\076\000\213\000\185\000\052\000\053\000\054\000\055\000\076\000\
\076\000\076\000\076\000\074\000\182\000\074\000\074\000\074\000\
\074\000\186\000\074\000\187\000\188\000\074\000\074\000\075\000\
\199\000\075\000\075\000\075\000\075\000\072\000\075\000\072\000\
\072\000\075\000\075\000\073\000\072\000\073\000\073\000\072\000\
\072\000\082\000\073\000\083\000\203\000\073\000\073\000\202\000\
\082\000\084\000\083\000\082\000\082\000\083\000\083\000\200\000\
\084\000\201\000\204\000\084\000\084\000\205\000\206\000\208\000\
\210\000\212\000\211\000\215\000\214\000\216\000\221\000\222\000\
\223\000\224\000\225\000\232\000\226\000\227\000\228\000\238\000\
\229\000\230\000\247\000\235\000\236\000\003\000\004\000\239\000\
\240\000\016\000\242\000\241\000\246\000\064\000\092\000\243\000\
\248\000\249\000\065\000\250\000\130\000\026\000\020\000\027\000\
\034\000\175\000\031\000\063\000\059\000\000\000\058\000"

let yycheck = "\041\000\
\029\000\030\000\006\001\001\001\001\001\005\001\006\001\145\000\
\006\000\001\000\039\000\001\001\010\001\010\001\140\000\026\001\
\006\001\000\000\047\000\048\000\049\000\050\000\051\000\052\000\
\053\000\054\000\055\000\165\000\024\001\027\000\028\000\073\000\
\158\000\001\001\001\001\046\001\034\001\035\001\042\001\007\001\
\008\001\009\001\042\001\085\000\086\000\018\001\014\001\011\000\
\174\000\017\001\025\001\001\001\025\001\024\001\029\001\028\001\
\029\001\021\000\026\001\027\001\025\001\038\001\039\001\189\000\
\029\001\107\000\108\000\109\000\019\001\037\001\000\000\000\001\
\001\001\024\001\042\001\104\000\105\000\045\001\001\001\008\001\
\009\001\044\001\001\001\044\001\007\001\008\001\009\001\026\001\
\019\001\008\001\009\001\014\001\024\001\001\001\017\001\221\000\
\063\000\235\000\236\000\066\000\008\001\009\001\001\001\026\001\
\029\001\018\001\004\001\036\001\150\000\028\001\139\000\025\001\
\025\001\042\001\037\001\028\001\029\001\036\001\001\001\042\001\
\149\000\001\001\045\001\042\001\044\001\028\001\168\000\156\000\
\036\001\044\001\001\001\002\001\003\001\004\001\042\001\024\001\
\029\001\179\000\136\000\137\000\011\001\012\001\013\001\024\001\
\001\001\001\001\002\001\003\001\004\001\178\000\024\001\001\001\
\001\001\024\001\025\001\011\001\012\001\013\001\005\001\027\001\
\001\001\203\000\204\000\205\000\206\000\025\001\001\001\001\001\
\024\001\025\001\041\001\030\001\031\001\032\001\033\001\004\001\
\001\001\002\001\003\001\004\001\024\001\019\001\019\001\225\000\
\027\001\041\001\011\001\012\001\013\001\025\001\001\001\002\001\
\003\001\004\001\001\001\002\001\003\001\004\001\024\001\024\001\
\011\001\012\001\013\001\024\001\011\001\012\001\013\001\024\001\
\020\001\021\001\022\001\023\001\025\001\024\001\022\001\023\001\
\041\001\024\001\030\001\031\001\032\001\033\001\030\001\031\001\
\032\001\033\001\025\001\025\001\028\001\001\001\041\001\028\001\
\025\001\018\001\041\001\020\001\021\001\022\001\023\001\029\001\
\025\001\025\001\025\001\028\001\029\001\030\001\031\001\032\001\
\033\001\018\001\025\001\020\001\021\001\022\001\023\001\020\001\
\021\001\022\001\023\001\026\001\025\001\030\001\031\001\032\001\
\033\001\030\001\031\001\032\001\033\001\020\001\021\001\022\001\
\023\001\028\001\024\001\001\001\001\001\028\001\027\001\030\001\
\031\001\032\001\033\001\020\001\021\001\022\001\023\001\001\001\
\026\001\024\001\044\001\028\001\044\001\030\001\031\001\032\001\
\033\001\020\001\021\001\022\001\023\001\044\001\019\001\044\001\
\024\001\028\001\027\001\030\001\031\001\032\001\033\001\020\001\
\021\001\022\001\023\001\020\001\021\001\022\001\023\001\028\001\
\025\001\030\001\031\001\032\001\033\001\030\001\031\001\032\001\
\033\001\020\001\021\001\022\001\023\001\020\001\021\001\022\001\
\023\001\028\001\001\001\030\001\031\001\032\001\033\001\030\001\
\031\001\032\001\033\001\018\001\025\001\020\001\021\001\022\001\
\023\001\001\001\025\001\001\001\001\001\028\001\029\001\018\001\
\027\001\020\001\021\001\022\001\023\001\018\001\025\001\020\001\
\021\001\028\001\029\001\018\001\025\001\020\001\021\001\028\001\
\029\001\018\001\025\001\018\001\024\001\028\001\029\001\025\001\
\025\001\018\001\025\001\028\001\029\001\028\001\029\001\028\001\
\025\001\028\001\024\001\028\001\029\001\024\001\024\001\001\001\
\003\001\001\001\027\001\025\001\028\001\028\001\016\001\024\001\
\040\001\040\001\024\001\001\001\028\001\025\001\025\001\028\001\
\025\001\025\001\001\001\026\001\026\001\000\000\000\000\028\001\
\028\001\005\001\025\001\028\001\025\001\025\001\065\000\029\001\
\027\001\027\001\025\001\028\001\123\000\025\001\027\001\025\001\
\027\001\158\000\027\001\027\001\025\001\255\255\025\001"

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
# 52 "parser.mly"
              ( _1 )
# 467 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 53 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 473 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 56 "parser.mly"
         ( [_1] )
# 480 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 57 "parser.mly"
                   ( [_1] )
# 487 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 58 "parser.mly"
                         ( _1 :: _3 )
# 495 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 59 "parser.mly"
               ( _1 :: _2 )
# 503 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 62 "parser.mly"
                             ( [_1] )
# 510 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 63 "parser.mly"
                               ( _1 @ [_3] )
# 518 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 66 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 527 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 67 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 535 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 68 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 543 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 70 "parser.mly"
    ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 552 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 71 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 561 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 72 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (UnsafeSend (_2, _4, _6))) )
# 570 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 73 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 578 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 76 "parser.mly"
          ( [_1] )
# 585 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 77 "parser.mly"
                 ( _1 :: _2 )
# 593 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 80 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 601 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 81 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 609 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 84 "parser.mly"
                ( [_1] )
# 616 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 85 "parser.mly"
                        ( _1 :: _2 )
# 624 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 89 "parser.mly"
    ( { mname = _2; params = _4; ret = None; body = mk_stmt1 2 (Seq _7) } )
# 633 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'ret_ann) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 91 "parser.mly"
    ( { mname = _2; params = _4; ret = Some _7; body = mk_stmt1 2 (Seq _9) } )
# 643 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 94 "parser.mly"
          ( Types.TFloat )
# 649 "parser.ml"
               : 'ret_ann))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 95 "parser.mly"
          ( ty_of_name (loc_of_rhs 1) _1 )
# 656 "parser.ml"
               : 'ret_ann))
; (fun __caml_parser_env ->
    Obj.repr(
# 98 "parser.mly"
       ( [] )
# 662 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 99 "parser.mly"
       ( [_1] )
# 669 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 100 "parser.mly"
                        ( _1::_3 )
# 677 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 103 "parser.mly"
                                                      ( LocalTarget _1 )
# 684 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 104 "parser.mly"
                                                      ( RemoteTarget (_3, _5) )
# 692 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 107 "parser.mly"
         ( [_1] )
# 699 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 108 "parser.mly"
               ( _1 :: _2 )
# 707 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 111 "parser.mly"
                   ( _1::_2 )
# 715 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 112 "parser.mly"
                   ( [] )
# 721 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 729 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 116 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 737 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 117 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 744 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 118 "parser.mly"
                                                  ( mk_stmt1 4 (Send(LocalTarget "self", _4, _6)) )
# 752 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 119 "parser.mly"
                                                    ( mk_stmt1 4 (Send (LocalTarget "sender", _4, _6)) )
# 760 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 120 "parser.mly"
                                                         ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 769 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 121 "parser.mly"
                                                               ( mk_stmt1 2 (UnsafeSend (_2, _4, _6)) )
# 778 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 122 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 786 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 123 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 795 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 124 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 803 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 125 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 810 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 126 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 818 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 127 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 827 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 128 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 835 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 129 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 843 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 130 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 850 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'select_cases) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'select_timeout_opt) in
    Obj.repr(
# 131 "parser.mly"
                                                         ( mk_stmt1 3 (Select(_3, _4)) )
# 858 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 134 "parser.mly"
                             ( _1 @ [_2] )
# 866 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 135 "parser.mly"
                             ( [] )
# 872 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 138 "parser.mly"
                             ( _1 @ [_2] )
# 880 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 139 "parser.mly"
                             ( [] )
# 886 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'select_pat) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 143 "parser.mly"
    ( { pat = _2; body = mk_stmt1 5 (Seq(_5)) } )
# 894 "parser.ml"
               : 'select_case))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opt_id_list) in
    Obj.repr(
# 147 "parser.mly"
    ( { meth = _1; vars = _3 } )
# 902 "parser.ml"
               : 'select_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 150 "parser.mly"
            ( _1 )
# 909 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 151 "parser.mly"
                ( [] )
# 915 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 154 "parser.mly"
                         ( [_1] )
# 922 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 155 "parser.mly"
                      ( _1 @ [_3] )
# 930 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 159 "parser.mly"
      ( (Some _2, Some (mk_stmt1 5 (Seq _5))) )
# 938 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 161 "parser.mly"
      ( (None, None) )
# 944 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 164 "parser.mly"
                 ( [] )
# 950 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 165 "parser.mly"
                 ( _1 )
# 957 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 168 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 965 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 169 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 974 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 172 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 981 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 173 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 988 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 174 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 995 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 175 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 1002 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 176 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 1010 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 177 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 1018 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 178 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 1026 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 179 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 1034 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 180 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 1042 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 181 "parser.mly"
                                              ( mk_expr1 1 (NowSend (_2, _4, _6)) )
# 1051 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 182 "parser.mly"
                                                 ( mk_expr1 1 (FutureSend (_2, _4, _6)) )
# 1060 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 183 "parser.mly"
               ( mk_expr1 1 (Await _2) )
# 1067 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 184 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 1075 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 185 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 1083 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 186 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 1091 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 187 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 1099 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 188 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 1107 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 189 "parser.mly"
                       ( _2 )
# 1114 "parser.ml"
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
