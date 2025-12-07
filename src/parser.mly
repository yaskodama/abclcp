%{
open Ast
open Location
let mk_expr (d : Ast.expr_desc) : Ast.expr = { loc  = Location.dummy; desc  = d }
let mk_stmt (d : Ast.stmt_desc) : Ast.stmt = { sloc = Location.dummy; sdesc = d }
exception Syntax_error of Location.t * string
let loc_of_rhs i =
  let p = Parsing.rhs_start_pos i in
  { line = p.Lexing.pos_lnum; col  = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 }
%}
%token <string> ID
%token <float> FLOATLIT
%token <int> INTLIT
%token <string> STRINGLIT
%token OBJECT METHOD FLOAT CALL SEND
%token IF THEN ELSE WHILE DO
%token ASSIGN PLUS MINUS TIMES DIV LPAREN RPAREN LBRACE RBRACE SEMICOLON COMMA
%token GE LE SELF SENDER CLASS
%token EOF NEW
%token VAR EQ DOT

%left PLUS MINUS
%left TIMES DIV
%start program
%type <Ast.program> program

%%

program:
  | decls EOF { $1 }
  | error EOF { raise (Syntax_error (loc_of_rhs 1, "syntax error in program")) }
  
decls:
  | decl { [$1] }
  | decl SEMICOLON { [$1] }
  | decl SEMICOLON decls { $1 :: $3 }
  | decl decls { $1 :: $2 }

arg_list:
  expr                       { [$1] }
  | arg_list COMMA expr        { $1 @ [$3] }

decl:
  | CLASS ID LBRACE fields methods RBRACE { Class { cname = $2; fields = $4; methods = $5 } }
  | CLASS ID LBRACE methods RBRACE        { Class { cname = $2; fields = []; methods = $4 } }
  | OBJECT ID LBRACE fields methods RBRACE { Class { cname = $2; fields = $4; methods = $5 } }
  | OBJECT ID LBRACE methods RBRACE        { Class { cname = $2; fields = []; methods = $4 } }
  | ID ID SEMICOLON                        { Instantiate ($1, $2) }
  | ID ID ASSIGN LBRACE inits RBRACE SEMICOLON   { InstantiateInit ($1, $2, $5) }
  | ID ID LPAREN args RPAREN SEMICOLON           { InstantiateArgs ($1, $2, $4) }
  | VAR ID ASSIGN expr SEMICOLON { Global (mk_stmt(VarDecl ($2, $4))) }
  | VAR ID ASSIGN NEW ID LPAREN args RPAREN SEMICOLON   { Global (mk_stmt(VarDecl ($2, mk_expr(New ($5, $7))))) }
  | SEND ID DOT ID LPAREN args RPAREN SEMICOLON      { Global (mk_stmt(Send ($2, $4, $6))) }
  | ID LPAREN args RPAREN SEMICOLON { Global (mk_stmt(CallStmt ($1, $3))) }

fields:
  | field { [$1] }
  | field fields { $1 :: $2 }

field:
  | FLOAT ID ASSIGN expr SEMICOLON { mk_stmt(VarDecl ($2, $4)) }
  | VAR ID ASSIGN expr SEMICOLON { mk_stmt(VarDecl ($2, $4)) }
  
methods:
  | method_decl { [$1] }
  | method_decl methods { $1 :: $2 }

method_decl:
  | METHOD ID LPAREN param_list RPAREN LBRACE stmts RBRACE {
    { mname = $2; params = $4; body = mk_stmt(Seq $7) } }

param_list:
  |      { [] }
  | ID { [$1] }
  | ID COMMA param_list { $1::$3 }

stmts:
  | stmt { [$1] }
  | stmt stmts { $1 :: $2 }

stmt_list:
  | stmt stmt_list { $1::$2 }
  |                { [] }
  
stmt:
  | ID ASSIGN expr SEMICOLON { mk_stmt(Assign ($1, $3)) }
  | CALL ID LPAREN args RPAREN SEMICOLON { mk_stmt(CallStmt ($2, $4)) }
  | CALL ID LPAREN RPAREN SEMICOLON { mk_stmt(CallStmt ($2, [])) }
  | SEND SELF DOT ID LPAREN args RPAREN SEMICOLON { mk_stmt(Send("self", $4, $6)) }
  | SEND SENDER DOT ID LPAREN args RPAREN SEMICOLON { mk_stmt(Send ("sender", $4, $6)) }
  | SEND ID DOT ID LPAREN args RPAREN SEMICOLON { mk_stmt(Send ($2, $4, $6)) }
  | IF expr THEN stmt ELSE stmt { mk_stmt(If($2, $4, $6)) }
  | WHILE expr DO stmt { mk_stmt(While ($2, $4)) }
  | FLOAT ID ASSIGN expr SEMICOLON { mk_stmt(VarDecl($2, $4)) }
  | LBRACE stmt_list RBRACE { mk_stmt(Seq $2) }
  | VAR ID ASSIGN expr SEMICOLON { mk_stmt(VarDecl($2, $4)) }
  | VAR ID ASSIGN NEW ID LPAREN args RPAREN SEMICOLON { mk_stmt(VarDecl($2, mk_expr(New($5,$7)))) }
  | ID LPAREN args RPAREN SEMICOLON { mk_stmt(CallStmt ($1, $3)) }
  
args:
  /* empty */    { [] }
  | arg_list     { $1 }

inits:
  | ID ASSIGN expr { [(mk_stmt(VarDecl($1, $3)))] }
  | ID ASSIGN expr COMMA inits { (mk_stmt(VarDecl($1, $3))) :: $5 }

expr:
  | FLOATLIT { mk_expr(Float $1) }
  | STRINGLIT { mk_expr(String $1) }
  | INTLIT { mk_expr(Int $1) }
  | ID { mk_expr(Var $1) }
  | expr PLUS expr { mk_expr(Binop ("+", $1, $3)) }
  | expr MINUS expr { mk_expr(Binop ("-", $1, $3)) }
  | expr TIMES expr { mk_expr(Binop ("*", $1, $3)) }
  | expr DIV expr { mk_expr(Binop ("/", $1, $3)) }
  | NEW ID LPAREN args RPAREN { mk_expr(New ($2, $4)) }
  | ID LPAREN args RPAREN { mk_expr(Call ($1, $3)) }
  | expr GE expr { mk_expr(Binop (">=", $1, $3)) }
  | expr LE expr { mk_expr(Binop ("<=", $1, $3)) }
  | LPAREN expr RPAREN { $2 }
