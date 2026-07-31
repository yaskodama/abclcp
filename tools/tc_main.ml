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
  match (try Ok (parse_file fname) with e -> Error (Printexc.to_string e)) with
  | Error _ -> print_endline "PARSE_ERROR"
  | Ok prog ->
      Infer.verbose := false;
      (match Infer.check_program prog with
       | Ok _ -> print_endline "OK"
       | Error msg -> print_endline ("TYPE_ERROR: " ^ msg))
