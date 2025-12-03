OCAMLC=ocamlfind ocamlc
LEX=ocamllex
YACC=ocamlyacc

THREAD_FLAGS=-thread
PKGS=-package tsdl

all: thread_repl

parser.ml parser.mli: parser.mly
	$(YACC) parser.mly

lexer.ml: lexer.mll
	$(LEX) lexer.mll

thread_repl: parser.ml parser.mli lexer.ml ast.ml eval_thread.ml sdl_helper.ml compiler.ml repl_thread.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c types.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c ast.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c typing_env.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c typing_env.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c infer.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c typecheck.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c sdl_helper.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c eval_thread.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c parser.mli
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c parser.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c lexer.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c compiler.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -c repl_thread.ml
	$(OCAMLC) $(PKGS) $(THREAD_FLAGS) -linkpkg -g -o abclrepl_thread sdl_helper.cmo ast.cmo types.cmo typing_env.cmo infer.cmo typecheck.cmo eval_thread.cmo parser.cmo lexer.cmo compiler.cmo repl_thread.cmo

clean:
	rm -f *.cmo *.cmi *.cma *.cmx *.o *.out parser.ml parser.mli lexer.ml abclrepl_thread
