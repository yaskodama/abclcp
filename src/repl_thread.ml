open Ast
open Eval_thread
open Lexer
open Parser
open Thread

exception Quit

let parse_program_safe (src : string) : (Ast.program, string) result =
  let lb = Lexing.from_string src in
  try
    lb.Lexing.lex_curr_pos <- 0;
    Ok (Parser.program Lexer.token lb)
  with
  | Parser.Syntax_error (loc, msg) ->
      (* parser.mly から投げた Syntax_error を位置付きで表示 *)
      Printf.printf "[Parse error] %s: %s\n%!"
        (Location.to_string loc) msg;
      raise (Failure "parse error")
  | Parsing.Parse_error ->
      let pos  = Lexing.lexeme_start_p lb in
      let line = pos.Lexing.pos_lnum in
      let col  = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
      Printf.printf "[Parse error] line %d, col %d\n%!" line col;
      raise (Failure "parse error")
  | exn -> Error (Printexc.to_string exn)

let pp_token = function
  | CLASS     -> "CLASS"
  | METHOD    -> "METHOD"
  | FLOAT     -> "FLOAT"
  | VAR       -> "VAR"
  | CALL      -> "CALL"
  | SEND      -> "SEND"
  | SELF      -> "SELF"
  | SENDER    -> "SENDER"
  | IF        -> "IF"
  | THEN      -> "THEN"
  | ELSE      -> "ELSE"
  | WHILE     -> "WHILE"
  | DO        -> "DO"
  | ASSIGN    -> "ASSIGN"
  | PLUS      -> "PLUS"
  | MINUS     -> "MINUS"
  | TIMES     -> "TIMES"
  | DIV       -> "DIV"
  | GE        -> "GE"
  | LE        -> "LE"
  | LPAREN    -> "LPAREN"
  | RPAREN    -> "RPAREN"
  | LBRACE    -> "LBRACE"
  | RBRACE    -> "RBRACE"
  | COMMA     -> "COMMA"
  | SEMICOLON -> "SEMICOLON"
  | NEW       -> "NEW"
  | ID s      -> Printf.sprintf "ID(%s)" s
  | STRINGLIT s -> Printf.sprintf "STRING(%s)" s
  | FLOATLIT f  -> Printf.sprintf "FLOAT(%g)" f
  | INTLIT n   -> Printf.sprintf "INT(%d)" n
  | EQ         -> "EQ"
  | DOT        -> "DOT"
  | EOF       -> "EOF"

let dump_tokens_of_string (src:string) =
  let lb = Lexing.from_string src in
  print_endline "[Token stream]";
  let rec loop () =
    match Lexer.token lb with
    | EOF -> print_endline "EOF"
    | t   -> Printf.printf "Token: %s\n%!" (pp_token t); loop ()
  in
  loop ()

let exit_banner = "Bye!"

let starts_with s pref =
  let ls = String.length s and lp = String.length pref in
  ls >= lp && String.sub s 0 lp = pref

let is_command_line (s:string) =
  let s = String.trim s in
  s = "" ||
  List.exists (fun p -> starts_with s p)
    ["help"; "exit"; "quit"; "load "; "compile"; "list"; "vlist"; "actors";
     "send "; "ssend "; "ast "; "pprint "; "pprint "; "clear"; "reset"; "script "]

let delta_brace (line : string) : int =
  let d     = ref 0 in
  let in_str = ref false in
  let esc    = ref false in
  for i = 0 to String.length line - 1 do
    let c = line.[i] in
    if !in_str then (
      (* 文字列リテラル中 *)
      if !esc then esc := false
      else if c = '\\' then esc := true
      else if c = '"'  then in_str := false
      else ()
    ) else (
      (* 文字列リテラル外 *)
      if c = '"' then in_str := true
      else if c = '{' then incr d
      else if c = '}' then decr d
      else ()
    )
  done;
  !d

let trim s =
  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false in
  let len = String.length s in
  let i = ref 0 and j = ref (len - 1) in
  while !i < len && is_space s.[!i] do incr i done;
  while !j >= !i && is_space s.[!j] do decr j done;
  if !j < !i then "" else String.sub s !i (!j - !i + 1)

let parse_arg_token (t : string) : Ast.expr =
  let t = trim t in
  let n = String.length t in
  if n >= 2 && t.[0] = '"' && t.[n-1] = '"' then
    Ast.mk_expr(Ast.String (String.sub t 1 (n - 2)))
  else
    (* 数値 or 識別子 *)
    (try Ast.mk_expr(Ast.Float (float_of_string t)) with _ -> Ast.mk_expr(Ast.Var t))

let split_args (s : string) : string list =
  (* カンマ区切り（クォート内のカンマは今回非対応：必要なら強化） *)
  let rec loop i start acc =
    if i >= String.length s then
      let last = String.sub s start (i - start) in
      List.rev (last :: acc)
    else
      match s.[i] with
      | ',' ->
          let part = String.sub s start (i - start) in
          loop (i+1) (i+1) (part :: acc)
      | _ -> loop (i+1) start acc
  in
  let s = trim s in
  if s = "" then [] else List.map trim (loop 0 0 [])

let parse_args_list (inside_paren : string) : Ast.expr list =
  split_args inside_paren |> List.map parse_arg_token

let script_file = ref None

let speclist = [
  ("-f", Arg.String (fun s -> script_file := Some s), "Script file to execute at startup");
]

let parse_input (s : string) : Ast.program =
  let lb = Lexing.from_string s in
  (* 表示用に入力名を入れておく（任意） *)
  lb.Lexing.lex_curr_p <- { lb.Lexing.lex_curr_p with Lexing.pos_fname = "<repl>" };
  Parser.program token lb

let parse_input_safe (s : string) : (Ast.program, string) result =
  try Ok (parse_input s) with
  | Failure msg -> Error (Printf.sprintf "Failure: %s" msg)
  | Parsing.Parse_error -> Error "Parse error"
  | exn -> Error (Printexc.to_string exn)

let parse_file_safe (filename : string) : (Ast.program, string) result =
  try
    let ic = open_in filename in
    let len = in_channel_length ic in
    let s = really_input_string ic len in
    close_in ic;
    parse_input_safe s
  with
  | Sys_error e -> Error (Printf.sprintf "Sys_error: %s" e)

type session = {
  mutable ast      : Ast.program option;  (* 直近にロード/パース成功した AST *)
  mutable filename : string option;       (* 直近に成功したファイル名 *)
}

let sess = { ast = None; filename = None }

let load_decls ?filename (decls : Ast.program) =
  if not (Typecheck.run decls) then
    Printf.printf "[Abort] Type error%s\n%!"
      (match filename with None -> "" | Some f -> " while loading "^f)
  else begin
    (* ここで必要なら eval/登録など *)
    (* program_buffer := !program_buffer @ decls; 等 *)
    Printf.printf "[Loaded]%s%s\n%!"
      (match filename with None -> "" | Some _ -> " ")
      (match filename with None -> "" | Some f -> f)
  end

let load_file (fname : string) : Ast.program option =
  try
    let ic = open_in fname in
    let len = in_channel_length ic in
    let src = really_input_string ic len in
    close_in ic;

    (* === 追加: トークン列を表示 === *)
    Printf.printf "[Token stream]\n%!";
    let lexbuf = Lexing.from_string src in
    let rec show_tokens () =
      match token lexbuf with
      | EOF ->
          Printf.printf "EOF\n%!"
      | t ->
          (match t with
           | CLASS -> print_endline "Token: CLASS"
           | METHOD -> print_endline "Token: METHOD"
           | FLOAT -> print_endline "Token: FLOAT"
           | VAR -> print_endline "Token: VAR"
           | CALL -> print_endline "Token: CALL"
           | SEND -> print_endline "Token: SEND"
           | ID s -> Printf.printf "Token: ID(%s)\n" s
           | STRINGLIT s -> Printf.printf "Token: STRING(%s)\n" s
           | FLOATLIT f -> Printf.printf "Token: FLOAT(%g)\n" f
	   | INTLIT i -> Printf.printf "Token: INT(%d)\n" i
           | ASSIGN -> print_endline "Token: ASSIGN"
           | PLUS -> print_endline "Token: PLUS"
           | MINUS -> print_endline "Token: MINUS"
           | TIMES -> print_endline "Token: TIMES"
           | DIV -> print_endline "Token: DIV"
           | LPAREN -> print_endline "Token: LPAREN"
           | RPAREN -> print_endline "Token: RPAREN"
           | LBRACE -> print_endline "Token: LBRACE"
           | RBRACE -> print_endline "Token: RBRACE"
           | SEMICOLON -> print_endline "Token: SEMICOLON"
           | COMMA -> print_endline "Token: COMMA"
           | NEW -> print_endline "Token: NEW"
           | SELF -> print_endline "Token: SELF"
           | SENDER -> print_endline "Token: SENDER"
           | IF -> print_endline "Token: IF"
           | THEN -> print_endline "Token: THEN"
           | ELSE -> print_endline "Token: ELSE"
           | WHILE -> print_endline "Token: WHILE"
           | DO -> print_endline "Token: DO"
           | _ -> print_endline "Token: (other)"
          );
          show_tokens ()
    in
(*    show_tokens (); *)
    let decls =
      let lb = Lexing.from_string src in
      Parser.program Lexer.token lb
    in
    print_endline "[AST]";
    Ast.dump_program decls;

    if Typecheck.run decls then begin
      Printf.printf "[Loaded] %s\n%!" fname;
      Some decls
    end else begin
      Printf.printf "[Abort] Type error while loading %s\n%!" fname;
      None
    end
  with Sys_error msg ->
    Printf.printf "[Error] could not load %s\n%s\n%!" fname msg;
    None

let usage_msg = "Usage: abclrepl_thread [-f script_file]"

let rec string_of_expr (e : Ast.expr) =
  match e.desc with
  | Float f -> string_of_float f
  | String s -> s
  | Var v -> v
  | Binop (op, e1, e2) -> "(" ^ string_of_expr e1 ^ " " ^ op ^ " " ^ string_of_expr e2 ^ ")"
  | Call (fname, args) -> fname ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | Expr e -> (string_of_expr e)
  | Int i -> string_of_int i
  | New (cls, args) -> cls ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | Array (_,_) -> "array"
  
  let rec string_of_stmt (st: Ast.stmt) =
  match st.sdesc with
  | Assign (v, e) -> v ^ " = " ^ string_of_expr e
  | CallStmt (fname, args) -> "call " ^ fname ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | Send (tgt, msg, args) -> "send " ^ tgt ^ " " ^ msg ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | Seq stmts -> String.concat "; " (List.map string_of_stmt stmts)
  | If (cond, t, f) -> "if " ^ string_of_expr cond ^ " then (" ^ string_of_stmt t ^ ") else (" ^ string_of_stmt f ^ ")"
  | While (cond, body) -> "while " ^ string_of_expr cond ^ " do (" ^ string_of_stmt body ^ ")"
  | VarDecl (vname, e) -> vname ^ " = " ^ string_of_expr e

let string_of_decl = function
  | Class obj ->
    let fields = obj.fields
    |> List.filter_map (fun (st: Ast.stmt) ->
       match st.sdesc with
       | VarDecl(n,e) -> Some (" float " ^ n ^ " = " ^ string_of_expr e)
       | _ -> None) in
    let methods = List.map (fun m -> "  method " ^ m.mname ^ "() { " ^ string_of_stmt m.body ^ " }") obj.methods in
    "object " ^ obj.cname ^ " {\n" ^ String.concat "\n" (fields @ methods) ^ "\n}"

let pending_global_sends : (unit -> unit) list ref = ref []

let program_buffer = ref []
let compiled = ref false

let rec process_command line =
  if line = "exit" || line = "quit" then (
    (try Sdl_helper.sdl_quit () with _ -> ());
    raise Quit
  )
  else if String.trim line = "" then ()
  else if String.length line >= 4 && String.sub line 0 4 = "help" then begin
    print_endline "Commands:";
    print_endline "  load <file.abcl>      - load a source file (shows tokens & AST; typechecks)";
    print_endline "  compile               - build/spawn from the loaded program";
    print_endline "  list                  - list active objects";
    print_endline "  send obj.method(args) - send async message";
    print_endline "  ast <name>            - show AST of a class or instance's class";
    print_endline "  pprint <name>         - pretty-print the class source";
    print_endline "  script <file>         - run REPL commands from file";
    print_endline "  exit / quit           - exit REPL";
  end
  else if line = "compile" then (
    compiled := true;
    List.iter (function
    | Class obj ->
      Printf.printf "[Defined class %s]\n%!" obj.cname;
      Eval_thread.register_class obj;
      let ms_arity : (string * int) list =
        obj.methods |> List.map (fun (md:Ast.method_decl) -> (md.mname, List.length md.params))
      in
        Types.register_class_auto obj.cname ms_arity;
        Printf.printf "[Registered types for class %s: %s]\n%!" obj.cname
        (String.concat ", " (List.map (fun (m,a)-> Printf.sprintf "%s/%d" m a) ms_arity));
    | _ -> ()
    ) !program_buffer;
    List.iter (function
    | Global s -> (
      match s.sdesc with
      | VarDecl (name, rhs) -> (
        match rhs.desc with
        | New (cls, args) -> (
          let cobj = Eval_thread.find_class_exn cls in
            Eval_thread.register_instance_source name cobj;
            let obj  = { cobj with cname = cls } in
            let actor_inst = Eval_thread.create_actor name cls in
            List.iter (fun (st:Ast.stmt) ->
              match st.sdesc with
              | VarDecl (k, init) ->
                let v = Eval_thread.eval_expr actor_inst init in
                Hashtbl.replace actor_inst.env k v
              | _ -> ()
            ) obj.fields;
            List.iter (fun (m:method_decl) -> Hashtbl.replace actor_inst.methods m.mname m
            ) obj.methods;
            Hashtbl.add Eval_thread.actor_table name actor_inst;
            ignore (Thread.create (fun () -> Eval_thread.actor_loop actor_inst) ());
            let init_opt = List.find_opt (fun (m:Ast.method_decl) -> m.mname = "init") obj.methods in
            (match init_opt with
            | None ->
              Printf.printf "[Actor] %s: no init; skipped\n%!" name; ()
            | Some m ->
              let need = List.length m.params and got  = List.length args in
                if need <> got then
                  Printf.printf "[Actor] %s.init arity mismatch: expected %d but %d given — skipped\n%!"
                    name need got
                else
                  Eval_thread.send_message ~from:"<new>" name (CallStmt ("init", args))
		  ));
        | _ -> ())
      | Send (tgt, mname, args) -> (
        pending_global_sends := (fun () -> Eval_thread.send_message ~from:"<top>" tgt (CallStmt (mname, args))
          ) :: !pending_global_sends)
      | _ -> ())
    | Class _ -> ()
    | _ -> ()
    ) !program_buffer;
    List.iter (fun thunk -> thunk ()) (List.rev !pending_global_sends);
    pending_global_sends := [];
    print_endline "[Compiled]"
  )
  else if String.length line > 6 && String.sub line 0 6 = "ssend " then (
            let parts = String.split_on_char '.' (String.sub line 6 (String.length line - 6)) in
              match parts with
              | [obj; meth] -> send_message ~from:"main" obj (CallStmt (meth, []))
              | _ -> print_endline "[Error] Invalid ssend syntax"
          )
          else if String.length line > 5 && String.sub line 0 5 = "send " then (
            let payload = String.sub line 5 (String.length line - 5) |> trim in
            let lparen =
              try String.index payload '(' with Not_found ->
                print_endline "[Error] Invalid send syntax: missing '('"; -1
            in
              if lparen >= 0 then (
                let rparen =
                  try String.rindex payload ')' with Not_found ->
                    print_endline "[Error] Invalid send syntax: missing ')'"; -1
                in
                  if rparen > lparen then (
                    let head = String.sub payload 0 lparen |> trim in
                    let args_inside = String.sub payload (lparen+1) (rparen - lparen - 1) in
                      (* head = obj.method を分解 *)
                      let parts = String.split_on_char '.' head in
                        match parts with
                        | [obj; meth] ->
                          let args = parse_args_list args_inside in
                          send_message ~from:"main" obj (CallStmt (meth, args))
                        | _ ->
                        print_endline "[Error] Invalid send target (use obj.method(...))"
                  ) else
                    ()
              ) else
                ()
          )
  else if String.length line > 5 && String.sub line 0 5 = "load " then (
    let filename = String.trim (String.sub line 5 (String.length line - 5)) in
      match load_file filename with
      | Some decls -> program_buffer := !program_buffer @ decls
      | None -> ()
    )
  else if String.length line > 7 && String.sub line 0 7 = "script " then (
    let filename = String.trim (String.sub line 7 (String.length line - 7)) in
      try
        let ic = open_in filename in
          try
            while true do
              let cmd = input_line ic in
                print_endline ("[script] " ^ cmd);
                try process_command cmd with
                | Quit -> close_in_noerr ic; raise Quit
                | Parser.Syntax_error (loc, msg) ->
                  Printf.printf "[Error in script line] %s: %s\n%!" (Location.to_string loc) msg
                | Types.Type_error (loc, msg) ->
                  Printf.printf "[Type error] %s: %s\n%!" (Location.to_string loc) msg
                | exn -> Printf.printf "[Error in script line] %s\n%!" (Printexc.to_string exn)
            done
          with End_of_file ->
            close_in ic;
            print_endline "[Script execution completed]"
      with Sys_error msg ->
        Printf.printf "[Error] Could not open script file: %s\n" msg
  )
  else if String.length line > 4 && String.sub line 0 4 = "ast " then (
    let name = String.trim (String.sub line 4 (String.length line - 4)) in
      (* 1) まずインスタンス名として検索 *)
      match Eval_thread.get_instance_source name with
      | Some cdecl ->
        (* 既存の AST ダンパを使って見やすく出す *)
        Ast.dump_decl ~prefix:"" ~is_last:true (Class cdecl)
      | None ->
        (* 2) クラス名として検索（class_env） *)
        (match Eval_thread.find_class_exn name with
          | cdecl ->
            Ast.dump_decl ~prefix:"" ~is_last:true (Class cdecl)
          | exception _ ->
            Printf.printf "[Error] no AST found for '%s' (not an instance nor a class)\n%!" name)
        )
  else if line = "list" then (
  print_endline "[Registered actors and types]";
    (* すでに生きているアクタ（actor_table）から “変数名” と “クラス名” を確実に取得 *)
    Eval_thread.iter_actor_table (fun aname a ->
      let cls_name = Eval_thread.actor_class_name aname a in
      let methods  =
        match Types.lookup_class_methods_inst cls_name with  (* or lookup_class_methods_inst *)
        | ms -> ms                                               (* if your function name differs, adjust *)
        (* if your lookup raises Not_found, wrap it: *)
        (* | exception Not_found -> [] *)
      in
      let ty   = Types.TActor (cls_name, methods) in
      let show = Types.string_of_ty_pretty ty in
      Printf.printf "- %s : %s\n%!" aname show
    );
    flush stdout;
  )
  else if line = "actors" then (
    print_endline "[actor_table]";
    Eval_thread.iter_actor_table (fun aname a ->
      let cls_name = Eval_thread.actor_class_name aname a in
      let ty_str =
        let ms = Types.lookup_class_methods_inst cls_name in
        if ms = [] then
          "actor(" ^ cls_name ^ ")"
        else
          Types.string_of_ty_pretty (Types.TActor (cls_name, ms))
      in
      let mbox_n = Eval_thread.mailbox_len a in
      let mnames =
        match Eval_thread.method_names a with
        | [] -> "(no methods)"
        | xs -> String.concat ", " xs
      in
      Printf.printf "- %s : %s\n    mbox: %d\n    methods: %s\n%!"
        aname ty_str mbox_n mnames
    );
    flush stdout;
  )
  else if line = "vlist" then (
    print_endline "Active objects:";
    Hashtbl.iter (fun name (actor:Eval_thread.actor) ->
    (* 見出し：オブジェクト名のみ *)
    Printf.printf "- %s\n" name;
    (* 変数（状態） *)
    if Hashtbl.length actor.env = 0 then
      Printf.printf "    (no vars)\n"
    else
      Hashtbl.iter (fun key v ->
      Printf.printf "    var %s = %s\n" key (string_of_value v)
      ) actor.env;
      (* メソッド一覧：methods のキーを列挙 *)
      let method_names =
        Hashtbl.fold (fun mname _ acc -> mname :: acc) actor.methods []
        |> List.sort String.compare
      in
        Printf.printf "    methods: %s\n" (String.concat ", " method_names);
    ) Eval_thread.actor_table
  )    
  else if String.length line > 7 && String.sub line 0 7 = "pprint " then (
    let name = String.trim (String.sub line 7 (String.length line - 7)) in
      match Eval_thread.get_instance_source name with
      | Some cdecl ->
        print_endline (Ast.pprint_class cdecl)
      | None ->
        (match Hashtbl.find_opt Eval_thread.class_env name with
        | Some cdecl ->
          print_endline (Ast.pprint_class cdecl)
        | None ->
          Printf.printf "[Error] cannot find source for '%s'\n%!" name)
  )

let start_repl () =
  let building = ref false in
  let buf = Buffer.create 4096 in
  let depth = ref 0 in
  let prompt () =
    if !building then print_string "... "
    else print_string "ABCL/c+> ";
    flush stdout
  in
  let rec loop () =
    prompt ();
    let line =
      try read_line () with End_of_file -> (print_endline ""; raise Thread.Exit)
    in
      let s = String.trim line in
      if (not !building) && is_command_line s then (
          (try
            process_command line
          with
          | Quit -> raise Quit
          | Failure msg -> Printf.printf "[Error] %s\n%!" msg
          | exn -> Printf.printf "[Error] %s\n%!" (Printexc.to_string exn));
          loop ()
      ) else begin
        Buffer.add_string buf line; Buffer.add_char buf '\n';
        depth := !depth + (delta_brace line);
        let last_nonspace_is_term =
        let i = ref (String.length line - 1) in
        let rec back k =
          if k < 0 then false
          else match line.[k] with
             | ' ' | '\t' | '\r' -> back (k-1)
             | ';' | '}' -> true
             | _ -> false
        in
          back !i
        in
          if (!depth > 0) || (not last_nonspace_is_term) then (
          building := true;
          loop ()
          ) else begin
            (* ここで一塊のソースが完成。パースしてみる。*)
            let src = Buffer.contents buf in
              Buffer.clear buf; depth := 0; building := false;
            (* オプション：トークン列を表示 *)
(*              (try dump_tokens_of_string src with _ -> ());  *)
              match parse_program_safe src with
              | Error msg ->
                Printf.printf "[Parse error] %s\n%!" msg;
                loop ()
              | Ok decls ->
            (* AST表示（既存のダンプ関数を使う） *)
                print_endline "[AST]";
                Ast.dump_program decls;
                (* 型検査＆登録 *)
                if Typecheck.run decls then begin
                  program_buffer := !program_buffer @ decls;
                  (* 必要ならクラスの register など、既存の load/compile と同じ処理をここで呼ぶ *)
                  Printf.printf "[Loaded] <repl>\n%!"
                end else
                  Printf.printf "[Abort] Type error while parsing input\n%!";
                (* 次のプロンプトへ *)
                loop ()
        end
        end
        in
        (* Ctrl-C で REPL を落とさず戻す *)
          (try Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> ())) with _ -> ());
          (try Sys.set_signal Sys.sigint  (Sys.Signal_handle (fun _ -> print_endline ""; ())) with _ -> ());
          loop ()

let run_repl () =
  (match !script_file with
   | Some f ->
       Printf.printf "[script] %s\n%!" f;
       process_command ("script " ^ f);
       script_file := None
   | None -> ());
  start_repl ()  (* 既存の対話ループ *)

let repl_thread_fun () =
  try
    run_repl ()
  with
  | Quit ->
      print_endline exit_banner;
      (try Sdl_helper.sdl_quit () with _ -> ());
      ()
  | exn ->
      Printf.printf "[REPL thread error] %s\n%!" (Printexc.to_string exn)

let () =
  Arg.parse speclist (fun _ -> ()) "Usage: abclrepl_thread [-f script_file]";

  (match !script_file with
   | Some f -> Printf.printf "[info] -f: %s\n%!" f
   | None   -> Printf.printf "[info] -f: (none)\n%!");

  add_prim "array_empty" (function
    | [] -> make_array [||]
    | _  -> failwith "array_empty(): arity 0 expected");

  (* --- Web gateway (demo) ---
     web_listen(port)
     web_expose("/calc", "calc")
     Then open: http://localhost:port/ and send messages from your browser.
  *)
  add_prim "web_listen" (function
    | [VInt p] -> Web_gateway.start ~port:p; VUnit
    | [VFloat f] -> Web_gateway.start ~port:(int_of_float f); VUnit
    | _ -> failwith "web_listen(port): arity 1 expected (int/float)");

  add_prim "web_expose" (function
    | [VString path; VString actor_name] ->
        let key =
          let p = String.trim path in
          if p <> "" && p.[0] = '/' then String.sub p 1 (String.length p - 1) else p
        in
        if key = "" then failwith "web_expose: empty path";
        Web_gateway.expose ~key ~actor_name;
        VUnit
    | _ -> failwith "web_expose(path, actor): arity 2 expected (string,string)");

  let repl_thr = Thread.create (fun () -> repl_thread_fun ()) () in

  Sdl_helper.main_loop ();
  (try Thread.join repl_thr with _ -> ());
  Stdlib.exit 0
