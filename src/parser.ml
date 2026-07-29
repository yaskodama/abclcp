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
# 99 "parser.ml"
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
\006\000\006\000\006\000\006\000\006\000\006\000\000\000"

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
\003\000\003\000\003\000\003\000\005\000\007\000\007\000\002\000\
\004\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\087\000\000\000\000\000\002\000\000\000\029\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\006\000\000\000\068\000\
\070\000\069\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\086\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\015\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\010\000\017\000\021\000\000\000\
\011\000\081\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\009\000\000\000\000\000\000\000\077\000\
\030\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\013\000\014\000\000\000\000\000\018\000\019\000\
\000\000\078\000\079\000\028\000\000\000\000\000\012\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\025\000\024\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\053\000\000\000\000\000\022\000\032\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\033\000\045\000\000\000\000\000\000\000\000\000\035\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\044\000\
\000\000\000\000\000\000\052\000\000\000\000\000\000\000\000\000\
\023\000\048\000\037\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\051\000\000\000\046\000\050\000\
\000\000\036\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\049\000\000\000\000\000\000\000\000\000\
\043\000\060\000\000\000\000\000\000\000\000\000\000\000\038\000\
\039\000\040\000\041\000\057\000\000\000\000\000\000\000\000\000\
\061\000\056\000\062\000\047\000"

let yydgoto = "\002\000\
\009\000\016\000\010\000\011\000\032\000\033\000\064\000\065\000\
\034\000\066\000\067\000\117\000\146\000\150\000\147\000\161\000\
\179\000\195\000\196\000\211\000\235\000\236\000\000\000"

let yysindex = "\006\000\
\073\255\000\000\014\000\013\255\028\255\028\255\038\255\044\255\
\000\000\063\000\047\255\000\000\178\255\000\000\036\255\040\255\
\054\255\062\255\082\255\000\000\085\255\000\000\080\255\000\000\
\000\000\000\000\028\255\028\255\178\255\178\255\104\255\077\255\
\150\000\083\255\106\255\111\255\115\255\254\254\192\255\000\000\
\178\255\075\255\076\255\150\000\038\000\098\255\178\255\178\255\
\178\255\178\255\178\255\178\255\178\255\178\255\178\255\178\255\
\100\255\097\255\107\255\108\255\136\255\137\255\138\255\141\255\
\120\255\255\254\141\255\152\255\056\000\129\255\154\255\160\255\
\000\000\178\255\150\000\078\000\078\000\144\255\144\255\150\000\
\150\000\150\000\150\000\060\000\000\000\158\255\178\255\178\255\
\139\255\149\255\150\255\143\255\000\000\000\000\000\000\159\255\
\000\000\000\000\161\255\163\255\153\255\167\255\176\255\181\255\
\183\255\178\255\178\255\000\000\178\255\178\255\178\255\000\000\
\000\000\182\255\184\255\185\255\188\255\074\000\092\000\190\255\
\198\255\200\255\000\000\000\000\183\255\245\254\000\000\000\000\
\189\255\000\000\000\000\000\000\050\255\065\255\000\000\066\255\
\229\255\090\255\028\255\208\255\178\255\050\255\216\255\243\255\
\244\255\225\255\050\255\000\000\000\000\234\255\178\255\178\255\
\231\255\217\255\219\255\220\255\227\255\178\255\236\255\050\255\
\235\255\000\000\001\000\254\255\000\000\000\000\050\255\110\000\
\005\000\132\255\022\000\030\000\031\000\033\000\128\000\050\255\
\000\000\000\000\015\255\196\255\147\255\012\000\000\000\007\000\
\016\000\017\000\023\000\026\000\027\000\040\000\050\255\000\000\
\051\000\059\000\039\000\000\000\053\000\146\000\037\000\047\000\
\000\000\000\000\000\000\045\000\178\255\178\255\178\255\178\255\
\058\000\075\000\076\000\077\000\000\000\094\000\000\000\000\000\
\070\000\000\000\101\000\102\000\103\000\104\000\050\255\118\000\
\108\000\109\000\178\255\000\000\116\000\119\000\126\000\134\000\
\000\000\000\000\111\000\117\000\050\255\050\255\112\000\000\000\
\000\000\000\000\000\000\000\000\162\000\137\000\138\000\156\000\
\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\186\001\000\000\169\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\187\001\000\000\218\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\178\000\
\237\254\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\169\000\000\000\000\000\089\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\199\000\179\000\000\000\000\000\000\000\000\000\000\000\
\000\000\169\000\244\254\008\000\020\000\206\255\252\255\193\255\
\127\000\167\000\184\000\028\000\000\000\000\000\169\000\169\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\180\000\000\000\000\000\000\000\169\000\169\000\169\000\000\000\
\000\000\000\000\000\000\182\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\180\000\000\000\000\000\000\000\
\168\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\181\000\000\000\000\000\
\000\000\000\000\183\000\000\000\000\000\000\000\000\000\169\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\181\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\187\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\169\000\169\000\169\000\169\000\
\035\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\186\000\
\000\000\000\000\169\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\191\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\168\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\003\000\253\255\000\000\000\000\228\255\151\001\032\000\
\215\255\000\000\000\000\093\001\121\255\000\000\130\255\059\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 475
let yytable = "\070\000\
\044\000\045\000\061\000\062\000\062\000\007\000\001\000\022\000\
\017\000\007\000\069\000\166\000\008\000\012\000\133\000\160\000\
\008\000\040\000\075\000\076\000\077\000\078\000\079\000\080\000\
\081\000\082\000\083\000\084\000\014\000\042\000\043\000\182\000\
\101\000\160\000\134\000\042\000\013\000\015\000\018\000\063\000\
\063\000\042\000\042\000\042\000\019\000\103\000\104\000\004\000\
\042\000\192\000\136\000\042\000\193\000\194\000\005\000\006\000\
\137\000\138\000\139\000\035\000\042\000\042\000\020\000\140\000\
\209\000\148\000\141\000\120\000\121\000\122\000\149\000\042\000\
\003\000\004\000\021\000\142\000\042\000\118\000\119\000\042\000\
\005\000\006\000\007\000\036\000\151\000\004\000\143\000\038\000\
\008\000\152\000\014\000\144\000\005\000\006\000\145\000\092\000\
\233\000\037\000\095\000\015\000\039\000\246\000\247\000\041\000\
\046\000\047\000\080\000\057\000\007\000\058\000\169\000\059\000\
\159\000\080\000\008\000\060\000\080\000\080\000\071\000\072\000\
\007\000\074\000\168\000\154\000\155\000\086\000\008\000\085\000\
\186\000\175\000\087\000\088\000\023\000\024\000\025\000\026\000\
\089\000\090\000\091\000\200\000\156\000\157\000\027\000\028\000\
\029\000\061\000\093\000\023\000\024\000\025\000\026\000\198\000\
\096\000\098\000\099\000\030\000\185\000\027\000\028\000\029\000\
\100\000\102\000\105\000\219\000\220\000\221\000\222\000\106\000\
\107\000\108\000\030\000\199\000\031\000\052\000\053\000\054\000\
\055\000\112\000\023\000\024\000\025\000\026\000\109\000\116\000\
\110\000\239\000\111\000\031\000\027\000\028\000\029\000\113\000\
\023\000\024\000\025\000\026\000\023\000\024\000\025\000\026\000\
\114\000\030\000\027\000\028\000\029\000\115\000\027\000\028\000\
\029\000\123\000\082\000\124\000\126\000\125\000\129\000\030\000\
\135\000\082\000\031\000\030\000\082\000\082\000\130\000\075\000\
\131\000\075\000\075\000\075\000\075\000\153\000\075\000\158\000\
\068\000\075\000\075\000\071\000\197\000\071\000\071\000\071\000\
\071\000\162\000\071\000\163\000\164\000\071\000\071\000\071\000\
\071\000\071\000\071\000\165\000\075\000\176\000\170\000\048\000\
\049\000\050\000\051\000\167\000\171\000\178\000\172\000\173\000\
\071\000\052\000\053\000\054\000\055\000\076\000\174\000\076\000\
\076\000\076\000\076\000\180\000\076\000\181\000\187\000\076\000\
\076\000\073\000\056\000\073\000\073\000\184\000\188\000\189\000\
\073\000\190\000\202\000\073\000\073\000\074\000\201\000\074\000\
\074\000\204\000\076\000\203\000\074\000\072\000\205\000\074\000\
\074\000\206\000\207\000\210\000\072\000\214\000\073\000\072\000\
\072\000\048\000\049\000\050\000\051\000\212\000\073\000\208\000\
\216\000\213\000\074\000\052\000\053\000\054\000\055\000\217\000\
\218\000\223\000\072\000\048\000\049\000\050\000\051\000\048\000\
\049\000\050\000\051\000\097\000\056\000\052\000\053\000\054\000\
\055\000\052\000\053\000\054\000\055\000\048\000\049\000\050\000\
\051\000\228\000\224\000\050\000\051\000\127\000\056\000\052\000\
\053\000\054\000\055\000\052\000\053\000\054\000\055\000\048\000\
\049\000\050\000\051\000\225\000\226\000\227\000\234\000\128\000\
\056\000\052\000\053\000\054\000\055\000\229\000\230\000\231\000\
\232\000\048\000\049\000\050\000\051\000\237\000\238\000\244\000\
\248\000\183\000\056\000\052\000\053\000\054\000\055\000\240\000\
\083\000\245\000\241\000\048\000\049\000\050\000\051\000\083\000\
\191\000\242\000\083\000\083\000\056\000\052\000\053\000\054\000\
\055\000\243\000\249\000\250\000\251\000\048\000\049\000\050\000\
\051\000\048\000\049\000\050\000\051\000\215\000\056\000\052\000\
\053\000\054\000\055\000\052\000\053\000\054\000\055\000\252\000\
\084\000\003\000\004\000\077\000\077\000\077\000\077\000\084\000\
\056\000\064\000\084\000\084\000\056\000\077\000\077\000\077\000\
\077\000\085\000\065\000\016\000\026\000\020\000\027\000\034\000\
\085\000\031\000\059\000\085\000\085\000\063\000\077\000\058\000\
\094\000\132\000\177\000"

let yycheck = "\041\000\
\029\000\030\000\005\001\006\001\006\001\025\001\001\000\011\000\
\006\000\029\001\039\000\147\000\025\001\000\000\026\001\142\000\
\029\001\021\000\047\000\048\000\049\000\050\000\051\000\052\000\
\053\000\054\000\055\000\056\000\001\001\027\000\028\000\167\000\
\074\000\160\000\046\001\001\001\024\001\010\001\001\001\042\001\
\042\001\007\001\008\001\009\001\001\001\087\000\088\000\001\001\
\014\001\176\000\001\001\017\001\038\001\039\001\008\001\009\001\
\007\001\008\001\009\001\024\001\026\001\027\001\000\000\014\001\
\191\000\001\001\017\001\109\000\110\000\111\000\006\001\037\001\
\000\001\001\001\028\001\026\001\042\001\106\000\107\000\045\001\
\008\001\009\001\036\001\044\001\019\001\001\001\037\001\026\001\
\042\001\024\001\001\001\042\001\008\001\009\001\045\001\064\000\
\223\000\044\001\067\000\010\001\019\001\237\000\238\000\024\001\
\001\001\029\001\018\001\025\001\036\001\004\001\152\000\001\001\
\141\000\025\001\042\001\001\001\028\001\029\001\044\001\044\001\
\036\001\024\001\151\000\034\001\035\001\029\001\042\001\028\001\
\170\000\158\000\024\001\024\001\001\001\002\001\003\001\004\001\
\001\001\001\001\001\001\181\000\138\000\139\000\011\001\012\001\
\013\001\005\001\027\001\001\001\002\001\003\001\004\001\180\000\
\001\001\025\001\001\001\024\001\025\001\011\001\012\001\013\001\
\001\001\004\001\024\001\205\000\206\000\207\000\208\000\019\001\
\019\001\027\001\024\001\025\001\041\001\030\001\031\001\032\001\
\033\001\025\001\001\001\002\001\003\001\004\001\024\001\001\001\
\024\001\227\000\024\001\041\001\011\001\012\001\013\001\025\001\
\001\001\002\001\003\001\004\001\001\001\002\001\003\001\004\001\
\025\001\024\001\011\001\012\001\013\001\025\001\011\001\012\001\
\013\001\028\001\018\001\028\001\025\001\029\001\025\001\024\001\
\028\001\025\001\041\001\024\001\028\001\029\001\025\001\018\001\
\025\001\020\001\021\001\022\001\023\001\001\001\025\001\024\001\
\041\001\028\001\029\001\018\001\041\001\020\001\021\001\022\001\
\023\001\026\001\025\001\001\001\001\001\028\001\029\001\030\001\
\031\001\032\001\033\001\027\001\047\001\018\001\024\001\020\001\
\021\001\022\001\023\001\026\001\044\001\027\001\044\001\044\001\
\047\001\030\001\031\001\032\001\033\001\018\001\044\001\020\001\
\021\001\022\001\023\001\019\001\025\001\024\001\001\001\028\001\
\029\001\018\001\047\001\020\001\021\001\025\001\001\001\001\001\
\025\001\001\001\028\001\028\001\029\001\018\001\027\001\020\001\
\021\001\025\001\047\001\028\001\025\001\018\001\024\001\028\001\
\029\001\024\001\024\001\001\001\025\001\001\001\047\001\028\001\
\029\001\020\001\021\001\022\001\023\001\003\001\025\001\024\001\
\028\001\027\001\047\001\030\001\031\001\032\001\033\001\025\001\
\028\001\016\001\047\001\020\001\021\001\022\001\023\001\020\001\
\021\001\022\001\023\001\028\001\047\001\030\001\031\001\032\001\
\033\001\030\001\031\001\032\001\033\001\020\001\021\001\022\001\
\023\001\028\001\024\001\022\001\023\001\028\001\047\001\030\001\
\031\001\032\001\033\001\030\001\031\001\032\001\033\001\020\001\
\021\001\022\001\023\001\040\001\040\001\024\001\001\001\028\001\
\047\001\030\001\031\001\032\001\033\001\025\001\025\001\025\001\
\025\001\020\001\021\001\022\001\023\001\026\001\026\001\025\001\
\025\001\028\001\047\001\030\001\031\001\032\001\033\001\028\001\
\018\001\029\001\028\001\020\001\021\001\022\001\023\001\025\001\
\025\001\028\001\028\001\029\001\047\001\030\001\031\001\032\001\
\033\001\028\001\001\001\027\001\027\001\020\001\021\001\022\001\
\023\001\020\001\021\001\022\001\023\001\028\001\047\001\030\001\
\031\001\032\001\033\001\030\001\031\001\032\001\033\001\028\001\
\018\001\000\000\000\000\020\001\021\001\022\001\023\001\025\001\
\047\001\025\001\028\001\029\001\047\001\030\001\031\001\032\001\
\033\001\018\001\025\001\005\001\025\001\027\001\025\001\027\001\
\025\001\027\001\025\001\028\001\029\001\027\001\047\001\025\001\
\066\000\125\000\160\000"

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
# 54 "parser.mly"
              ( _1 )
# 478 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
              ( raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) )
# 484 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decl) in
    Obj.repr(
# 58 "parser.mly"
         ( [_1] )
# 491 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    Obj.repr(
# 59 "parser.mly"
                   ( [_1] )
# 498 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'decl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 60 "parser.mly"
                         ( _1 :: _3 )
# 506 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'decls) in
    Obj.repr(
# 61 "parser.mly"
               ( _1 :: _2 )
# 514 "parser.ml"
               : 'decls))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 64 "parser.mly"
                             ( [_1] )
# 521 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 65 "parser.mly"
                               ( _1 @ [_3] )
# 529 "parser.ml"
               : 'arg_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'fields) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 68 "parser.mly"
                                           ( Class { cname = _2; fields = _4; methods = _5 } )
# 538 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'methods) in
    Obj.repr(
# 69 "parser.mly"
                                           ( Class { cname = _2; fields = []; methods = _4 } )
# 546 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                                           ( Global (mk_stmt1 2 (VarDecl (_2, _4))) )
# 554 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 72 "parser.mly"
    ( Global (mk_stmt1 2 (VarDecl (_2, mk_expr1 4 (New (_5, _7))))) )
# 563 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 73 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (Send (_2, _4, _6))) )
# 572 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 74 "parser.mly"
                                                                       ( Global (mk_stmt1 1 (UnsafeSend (_2, _4, _6))) )
# 581 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 75 "parser.mly"
                                           ( Global (mk_stmt1 1 (CallStmt (_1, _3))) )
# 589 "parser.ml"
               : 'decl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'field) in
    Obj.repr(
# 78 "parser.mly"
          ( [_1] )
# 596 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'field) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'fields) in
    Obj.repr(
# 79 "parser.mly"
                 ( _1 :: _2 )
# 604 "parser.ml"
               : 'fields))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 82 "parser.mly"
                                   ( mk_stmt1 2  (VarDecl (_2, _4)) )
# 612 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 83 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl (_2, _4)) )
# 620 "parser.ml"
               : 'field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'method_decl) in
    Obj.repr(
# 86 "parser.mly"
                ( [_1] )
# 627 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'method_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'methods) in
    Obj.repr(
# 87 "parser.mly"
                        ( _1 :: _2 )
# 635 "parser.ml"
               : 'methods))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 91 "parser.mly"
    ( { mname = _2; params = _4; ret = None; body = mk_stmt1 2 (Seq _7) } )
# 644 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'param_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'ret_ann) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 93 "parser.mly"
    ( { mname = _2; params = _4; ret = Some _7; body = mk_stmt1 2 (Seq _9) } )
# 654 "parser.ml"
               : 'method_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 96 "parser.mly"
          ( Types.TFloat )
# 660 "parser.ml"
               : 'ret_ann))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 97 "parser.mly"
          ( ty_of_name (loc_of_rhs 1) _1 )
# 667 "parser.ml"
               : 'ret_ann))
; (fun __caml_parser_env ->
    Obj.repr(
# 100 "parser.mly"
       ( [] )
# 673 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 101 "parser.mly"
       ( [_1] )
# 680 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 102 "parser.mly"
                        ( _1::_3 )
# 688 "parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 105 "parser.mly"
                                                      ( LocalTarget _1 )
# 695 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 106 "parser.mly"
                                                      ( RemoteTarget (_3, _5) )
# 703 "parser.ml"
               : Ast.send_target))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 109 "parser.mly"
         ( [_1] )
# 710 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmts) in
    Obj.repr(
# 110 "parser.mly"
               ( _1 :: _2 )
# 718 "parser.ml"
               : 'stmts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 113 "parser.mly"
                   ( _1::_2 )
# 726 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 114 "parser.mly"
                   ( [] )
# 732 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 117 "parser.mly"
                             ( mk_stmt1 1 (Assign (_1, _3)) )
# 740 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 118 "parser.mly"
                                         ( mk_stmt1 2 (CallStmt (_2, _4)) )
# 748 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 119 "parser.mly"
                                    ( mk_stmt1 2 (CallStmt (_2, [])) )
# 755 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 120 "parser.mly"
                                                  ( mk_stmt1 4 (Send(LocalTarget "self", _4, _6)) )
# 763 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 121 "parser.mly"
                                                    ( mk_stmt1 4 (Send (LocalTarget "sender", _4, _6)) )
# 771 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 122 "parser.mly"
                                                         ( mk_stmt1 2 (Send (_2, _4, _6)) )
# 780 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 123 "parser.mly"
                                                               ( mk_stmt1 2 (UnsafeSend (_2, _4, _6)) )
# 789 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 124 "parser.mly"
                               ( mk_stmt1 2 (If(_3, _5, mk_stmt1 5 (Seq([])))) )
# 797 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 125 "parser.mly"
                                         ( mk_stmt1 3 (If(_3, _5, _7)) )
# 806 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 126 "parser.mly"
                       ( mk_stmt1 2 (While (_2, _4)) )
# 814 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 127 "parser.mly"
                            ( mk_stmt1 2 (Seq _2) )
# 821 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 128 "parser.mly"
                                 ( mk_stmt1 2 (VarDecl(_2, _4)) )
# 829 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 129 "parser.mly"
                                                      ( mk_stmt1 2 (VarDecl(_2, mk_expr1 4 (New(_5,_7)))) )
# 838 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 130 "parser.mly"
                                    ( mk_stmt1 1 (CallStmt (_1, _3)) )
# 846 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    Obj.repr(
# 131 "parser.mly"
                                           ( mk_stmt1 2 (Become (_2, _4)) )
# 854 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 132 "parser.mly"
                                      ( mk_stmt1 2 (Become (_2, [])) )
# 861 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'select_cases) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'select_timeout_opt) in
    Obj.repr(
# 133 "parser.mly"
                                                         ( mk_stmt1 3 (Select(_3, _4)) )
# 869 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 136 "parser.mly"
                             ( _1 @ [_2] )
# 877 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 137 "parser.mly"
                             ( [] )
# 883 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'select_cases) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'select_case) in
    Obj.repr(
# 140 "parser.mly"
                             ( _1 @ [_2] )
# 891 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    Obj.repr(
# 141 "parser.mly"
                             ( [] )
# 897 "parser.ml"
               : 'select_cases))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'select_pat) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 145 "parser.mly"
    ( { pat = _2; body = mk_stmt1 5 (Seq(_5)) } )
# 905 "parser.ml"
               : 'select_case))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'opt_id_list) in
    Obj.repr(
# 149 "parser.mly"
    ( { meth = _1; vars = _3 } )
# 913 "parser.ml"
               : 'select_pat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'id_list) in
    Obj.repr(
# 152 "parser.mly"
            ( _1 )
# 920 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    Obj.repr(
# 153 "parser.mly"
                ( [] )
# 926 "parser.ml"
               : 'opt_id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 156 "parser.mly"
                         ( [_1] )
# 933 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'id_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 157 "parser.mly"
                      ( _1 @ [_3] )
# 941 "parser.ml"
               : 'id_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'stmts) in
    Obj.repr(
# 161 "parser.mly"
      ( (Some _2, Some (mk_stmt1 5 (Seq _5))) )
# 949 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 163 "parser.mly"
      ( (None, None) )
# 955 "parser.ml"
               : 'select_timeout_opt))
; (fun __caml_parser_env ->
    Obj.repr(
# 166 "parser.mly"
                 ( [] )
# 961 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg_list) in
    Obj.repr(
# 167 "parser.mly"
                 ( _1 )
# 968 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 170 "parser.mly"
                   ( [(mk_stmt1 1 (VarDecl(_1, _3)))] )
# 976 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'inits) in
    Obj.repr(
# 171 "parser.mly"
                               ( (mk_stmt1 1 (VarDecl(_1, _3))) :: _5 )
# 985 "parser.ml"
               : 'inits))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 174 "parser.mly"
             ( mk_expr1 1 (Float _1) )
# 992 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 175 "parser.mly"
              ( mk_expr1 1 (String _1) )
# 999 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 176 "parser.mly"
           ( mk_expr1 1 (Int _1) )
# 1006 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 177 "parser.mly"
       ( mk_expr1 1 (Var _1) )
# 1013 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 178 "parser.mly"
                       ( mk_expr1 2 (Binop ("++", _1, _3)) )
# 1021 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 179 "parser.mly"
                   ( mk_expr1 2 (Binop ("+", _1, _3)) )
# 1029 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 180 "parser.mly"
                    ( mk_expr1 2 (Binop ("-", _1, _3)) )
# 1037 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 181 "parser.mly"
                    ( mk_expr1 2 (Binop ("*", _1, _3)) )
# 1045 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 182 "parser.mly"
                  ( mk_expr1 2 (Binop ("/", _1, _3)) )
# 1053 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 183 "parser.mly"
                              ( mk_expr1 1 (New (_2, _4)) )
# 1061 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 184 "parser.mly"
                                              ( mk_expr1 1 (NowSend (_2, _4, _6)) )
# 1070 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : Ast.send_target) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 185 "parser.mly"
                                                 ( mk_expr1 1 (FutureSend (_2, _4, _6)) )
# 1079 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 186 "parser.mly"
               ( mk_expr1 1 (Await _2) )
# 1086 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'args) in
    Obj.repr(
# 187 "parser.mly"
                          ( mk_expr1 1 (Call (_1, _3)) )
# 1094 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 188 "parser.mly"
                 ( mk_expr1 2 (Binop (">=", _1, _3)) )
# 1102 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 189 "parser.mly"
                 ( mk_expr1 2 (Binop ("<=", _1, _3)) )
# 1110 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 190 "parser.mly"
                 ( mk_expr1 2 (Binop (">", _1, _3)) )
# 1118 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 191 "parser.mly"
                 ( mk_expr1 2 (Binop ("<", _1, _3)) )
# 1126 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 192 "parser.mly"
                       ( _2 )
# 1133 "parser.ml"
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
