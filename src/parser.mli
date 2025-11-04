type token =
  | ID of (
# 5 "parser.mly"
        string
# 6 "parser.mli"
)
  | FLOATLIT of (
# 6 "parser.mly"
        float
# 11 "parser.mli"
)
  | INTLIT of (
# 7 "parser.mly"
        int
# 16 "parser.mli"
)
  | STRINGLIT of (
# 8 "parser.mly"
        string
# 21 "parser.mli"
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

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.program
