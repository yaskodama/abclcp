(* tc_main.ml — AIPL/ABCL の型検査だけを走らせる小さなドライバ *)

let parse_file (fname : string) : Ast.program =
  let ic = open_in fname in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  let lb = Lexing.from_string s in
  lb.Lexing.lex_curr_p <- { lb.Lexing.lex_curr_p with Lexing.pos_fname = fname };
  Parser.program Lexer.token lb

let () =
  let fname = Sys.argv.(1) in
  Printf.printf "=== %s ===\n%!" (Filename.basename fname);
  match (try Ok (parse_file fname) with e -> Error (Printexc.to_string e)) with
  | Error m -> Printf.printf "[Parse error] %s\n%!" m; exit 2
  | Ok prog ->
      (* クラスメソッドのスキーム表は出さず、戻り値型の表だけ見たいので
         Infer.verbose は false にして、自前で表示する *)
      Infer.verbose := false;
      (match Infer.check_program prog with
       | Ok _ ->
           print_endline "[OK] type check passed";
           Types.debug_print_method_rets ();
           print_endline "[class_method_schemes]";
           Hashtbl.iter
             (fun cls sigs ->
                Printf.printf "class %s\n" cls;
                List.iter
                  (fun (m, sch) ->
                     Printf.printf "  %s : %s\n" m
                       (Types.string_of_ty_pretty (Types.repr (Types.instantiate sch))))
                  sigs)
             Types.class_method_schemes
       | Error msg ->
           Printf.printf "[Type error] %s\n" msg;
           Types.debug_print_method_rets ());
      print_newline ()
