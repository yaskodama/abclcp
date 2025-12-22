(* web_gateway.ml
   Minimal HTTP gateway embedded in the ABCL/c+ runtime.

   - No external OCaml web libraries.
   - Runs as a background thread.
   - Lets a web browser send messages to actors.

   Endpoints:
     GET  /              -> simple HTML UI
     POST /api/send      -> send to actor by name
         form fields: to=<actorName>&method=<m>&args=<a,b,c>&from=<who>
     POST /api/x/<key>   -> send to exposed endpoint
         form fields: method=<m>&args=<a,b,c>&from=<who>

   Notes:
     - This is a demo-quality server. For production, use a real HTTP stack.
     - We support both form-encoded and JSON payloads (a tiny JSON parser is included).
*)

open Unix

(* We only need Eval_thread.send_message and Ast constructors. *)
open Ast
open Types

(* ---------- Public API ---------- *)

(* Exposed endpoints: "key" -> actor_name *)
let exposed : (string, string) Hashtbl.t = Hashtbl.create 32

let expose ~(key:string) ~(actor_name:string) : unit =
  Hashtbl.replace exposed key actor_name

let list_exposed () : (string * string) list =
  Hashtbl.to_seq exposed |> List.of_seq

(* A single running server per process (good enough for now). *)
let server_thread : Thread.t option ref = ref None

(* ---------- Tiny helpers ---------- *)

let is_space = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let trim (s:string) : string =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && is_space s.[!i] do incr i done;
  let j = ref (n - 1) in
  while !j >= !i && is_space s.[!j] do decr j done;
  if !j < !i then "" else String.sub s !i (!j - !i + 1)

let url_decode (s:string) : string =
  let buf = Buffer.create (String.length s) in
  let hex_val c =
    match c with
    | '0'..'9' -> Char.code c - Char.code '0'
    | 'a'..'f' -> 10 + Char.code c - Char.code 'a'
    | 'A'..'F' -> 10 + Char.code c - Char.code 'A'
    | _ -> 0
  in
  let i = ref 0 in
  while !i < String.length s do
    match s.[!i] with
    | '+' -> Buffer.add_char buf ' '; incr i
    | '%' when !i + 2 < String.length s ->
        let a = hex_val s.[!i+1] in
        let b = hex_val s.[!i+2] in
        Buffer.add_char buf (Char.chr (a * 16 + b));
        i := !i + 3
    | c -> Buffer.add_char buf c; incr i
  done;
  Buffer.contents buf

let split_on (ch:char) (s:string) : string list =
  let rec loop acc i j =
    if j = String.length s then
      List.rev ((String.sub s i (j-i)) :: acc)
    else if s.[j] = ch then
      loop ((String.sub s i (j-i)) :: acc) (j+1) (j+1)
    else
      loop acc i (j+1)
  in
  if s = "" then [] else loop [] 0 0

let parse_form_urlencoded (body:string) : (string, string) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  let pairs = split_on '&' body in
  List.iter
    (fun p ->
      match split_on '=' p with
      | [k; v] -> Hashtbl.replace tbl (url_decode k) (url_decode v)
      | [k] -> Hashtbl.replace tbl (url_decode k) ""
      | _ -> ())
    pairs;
  tbl

let read_line_opt (ic:in_channel) : string option =
  try Some (input_line ic) with End_of_file -> None

let read_headers (ic:in_channel) : (string, string) Hashtbl.t =
  let h = Hashtbl.create 16 in
  let rec loop () =
    match read_line_opt ic with
    | None -> h
    | Some line ->
        let line = trim line in
        if line = "" then h
        else begin
          match split_on ':' line with
          | key :: rest ->
              let v = String.concat ":" rest |> trim in
              Hashtbl.replace h (String.lowercase_ascii (trim key)) v;
              loop ()
          | _ -> loop ()
        end
  in
  loop ()

let read_exactly (ic:in_channel) (n:int) : string =
  really_input_string ic n

let http_response ?(code=200) ?(content_type="text/plain; charset=utf-8") (body:string) : string =
  let reason = match code with
    | 200 -> "OK"
    | 400 -> "Bad Request"
    | 404 -> "Not Found"
    | 500 -> "Internal Server Error"
    | _ -> "OK"
  in
  Printf.sprintf
    "HTTP/1.1 %d %s\r\nContent-Type: %s\r\nContent-Length: %d\r\nConnection: close\r\n\r\n%s"
    code reason content_type (String.length body) body

let html_index () : string =
  (* A tiny UI that posts JSON data to /api/json/send. *)
  "<!doctype html>\n" ^
  "<html><head><meta charset='utf-8'><title>ABCL/c+ Web Gateway</title></head>\n" ^
  "<body style='font-family: sans-serif'>\n" ^
  "<h2>ABCL/c+ Web Gateway</h2>\n" ^
  "<p>Send a message to an actor in the running ABCL/c+ process.</p>\n" ^
  "<div style='display:flex; gap:24px; align-items:flex-start'>\n" ^
  "<div>\n" ^
  "<h3>Direct send (JSON)</h3>\n" ^
  "<label>to (actor name): <input id='to' value='calc'></label><br>\n" ^
  "<label>method: <input id='method' value='add'></label><br>\n" ^
  "<label>args (comma sep): <input id='args' value='1,2'></label><br>\n" ^
  "<button onclick='send()'>Send</button>\n" ^
  "<pre id='out' style='background:#f4f4f4; padding:8px; min-height:4em'></pre>\n" ^
  "</div>\n" ^
  "</div>\n" ^
  "<script>\n" ^
  "async function send(){\n" ^
  "  const payload = {\n" ^
  "    to: document.getElementById('to').value,\n" ^
  "    method: document.getElementById('method').value,\n" ^
  "    args: document.getElementById('args').value.split(',').map(s=>s.trim()).filter(s=>s.length>0),\n" ^
  "    from: 'browser'\n" ^
  "  };\n" ^
  "  const r = await fetch('/api/json/send',{method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(payload)});\n" ^
  "  const t = await r.text();\n" ^
  "  document.getElementById('out').textContent = t;\n" ^
  "}\n" ^
  "</script>\n" ^
  "</body></html>\n"

(* ---------- Minimal JSON (only what we need) ---------- *)

type jv =
  | JObject of (string * jv) list
  | JArray of jv list
  | JString of string
  | JNumber of float
  | JBool of bool
  | JNull

exception Json_error of string

let json_error msg = raise (Json_error msg)

let parse_json (s:string) : jv =
  let n = String.length s in
  let i = ref 0 in
  let peek () = if !i < n then Some s.[!i] else None in
  let next () = let c = peek () in (match c with Some _ -> incr i | None -> ()); c in
  let rec skip_ws () =
    while !i < n && is_space s.[!i] do incr i done
  in
  let expect ch =
    skip_ws (); match next () with
    | Some c when c = ch -> ()
    | Some c -> json_error (Printf.sprintf "expected '%c' but got '%c'" ch c)
    | None -> json_error (Printf.sprintf "expected '%c' but got EOF" ch)
  in
  let rec parse_string () : string =
    expect '"';
    let buf = Buffer.create 32 in
    let rec loop () =
      match next () with
      | None -> json_error "unterminated string"
      | Some '"' -> Buffer.contents buf
      | Some '\\' ->
          (match next () with
           | Some '"' -> Buffer.add_char buf '"'
           | Some '\\' -> Buffer.add_char buf '\\'
           | Some 'n' -> Buffer.add_char buf '\n'
           | Some 'r' -> Buffer.add_char buf '\r'
           | Some 't' -> Buffer.add_char buf '\t'
           | Some c -> Buffer.add_char buf c
           | None -> json_error "bad escape") ;
          loop ()
      | Some c -> Buffer.add_char buf c; loop ()
    in
    loop ()
  in
  let rec parse_number () : float =
    skip_ws ();
    let start = !i in
    let is_num_char = function
      | '0'..'9' | '-' | '+' | '.' | 'e' | 'E' -> true
      | _ -> false
    in
    while !i < n && is_num_char s.[!i] do incr i done;
    if !i = start then json_error "expected number";
    let sub = String.sub s start (!i - start) in
    match float_of_string_opt sub with
    | Some f -> f
    | None -> json_error ("bad number: " ^ sub)
  in
  let rec parse_value () : jv =
    skip_ws ();
    match peek () with
    | None -> json_error "unexpected EOF"
    | Some '"' -> JString (parse_string ())
    | Some '{' -> parse_object ()
    | Some '[' -> parse_array ()
    | Some 't' ->
        if !i + 3 < n && String.sub s !i 4 = "true" then (i := !i + 4; JBool true)
        else json_error "bad token"
    | Some 'f' ->
        if !i + 4 < n && String.sub s !i 5 = "false" then (i := !i + 5; JBool false)
        else json_error "bad token"
    | Some 'n' ->
        if !i + 3 < n && String.sub s !i 4 = "null" then (i := !i + 4; JNull)
        else json_error "bad token"
    | Some ('0'..'9' | '-') -> JNumber (parse_number ())
    | Some c -> json_error (Printf.sprintf "unexpected char: %c" c)
  and parse_array () : jv =
    expect '[';
    skip_ws ();
    let rec loop acc =
      skip_ws ();
      match peek () with
      | Some ']' -> ignore (next ()); JArray (List.rev acc)
      | _ ->
          let v = parse_value () in
          skip_ws ();
          (match peek () with
           | Some ',' -> ignore (next ()); loop (v :: acc)
           | Some ']' -> ignore (next ()); JArray (List.rev (v :: acc))
           | _ -> json_error "expected , or ]")
    in
    loop []
  and parse_object () : jv =
    expect '{';
    skip_ws ();
    let rec loop acc =
      skip_ws ();
      match peek () with
      | Some '}' -> ignore (next ()); JObject (List.rev acc)
      | Some '"' ->
          let k = parse_string () in
          skip_ws (); expect ':';
          let v = parse_value () in
          skip_ws ();
          (match peek () with
           | Some ',' -> ignore (next ()); loop ((k, v) :: acc)
           | Some '}' -> ignore (next ()); JObject (List.rev ((k, v) :: acc))
           | _ -> json_error "expected , or }")
      | _ -> json_error "expected object key"
    in
    loop []
  in
  let v = parse_value () in
  skip_ws (); if !i <> n then json_error "trailing characters";
  v

let json_get (k:string) (o:(string * jv) list) : jv option =
  List.assoc_opt k o

let json_get_string (k:string) (o:(string * jv) list) : string option =
  match json_get k o with Some (JString s) -> Some s | _ -> None

let json_get_array (k:string) (o:(string * jv) list) : jv list option =
  match json_get k o with Some (JArray xs) -> Some xs | _ -> None

let ast_of_json_value (v:jv) : Ast.expr =
  match v with
  | JString s -> Ast.mk_expr (Ast.String s)
  | JBool b -> Ast.mk_expr (Ast.String (if b then "true" else "false"))
  | JNumber f ->
      (* If it's integral, prefer Int. *)
      if Float.is_finite f && abs_float (f -. Float.floor f) < 1e-9
      then Ast.mk_int (int_of_float (Float.round f))
      else Ast.mk_float f
  | JNull -> Ast.mk_expr (Ast.String "")
  | JObject _ | JArray _ -> Ast.mk_expr (Ast.String "")

(* ---------- Type checking for web calls (best-effort) ---------- *)

let type_matches (param:Types.ty) (arg:Ast.expr) : bool * Ast.expr =
  (* return (ok, maybe-coerced-arg) *)
  let param = Types.repr param in
  match param, arg.desc with
  | TInt, Int _ -> (true, arg)
  | TFloat, Float _ -> (true, arg)
  | TFloat, Int i -> (true, Ast.mk_float (float_of_int i)) (* allow int->float *)
  | TString, String _ -> (true, arg)
(*  | TBool, Bool _ -> (true, arg)   *)
  | TBool, String "true"  -> (true, arg)
  | TBool, String "false" -> (true, arg)
(* もし 0/1 も許したければ *)
  | TBool, Int 0 -> (true, arg)
  | TBool, Int 1 -> (true, arg)
  | TVar _, _ -> (true, arg) (* polymorphic: accept *)
  | _, _ -> (false, arg)

let check_web_call ~(actor_name:string) ~(method_name:string) (args:Ast.expr list)
  : (bool * string * Ast.expr list) =
  match Eval_thread.lookup_actor_class actor_name with
  | None -> (false, "unknown actor: " ^ actor_name, args)
  | Some cls ->
      (match Types.lookup_class_method_scheme cls method_name with
       | None -> (false, Printf.sprintf "unknown method: %s.%s" cls method_name, args)
       | Some (Forall (_, ty)) ->
           (match Types.repr ty with
            | TFun (params, _ret) ->
                if List.length params <> List.length args then
                  (false, Printf.sprintf "arity mismatch: expected %d args" (List.length params), args)
                else
                  let ok = ref true in
                  let coerced =
                    List.map2
                      (fun p a ->
                        let (b, a2) = type_matches p a in
                        if not b then ok := false;
                        a2)
                      params args
                  in
                  if !ok then (true, "", coerced)
                  else (false, "type mismatch", args)
            | _ -> (true, "", args)))

let parse_args_to_exprs (args_s:string) : Ast.expr list =
  let items =
    args_s
    |> split_on ','
    |> List.map trim
    |> List.filter (fun s -> s <> "")
  in
  let parse_one (s:string) : Ast.expr =
    (* try int, then float, else string *)
    let s0 = trim s in
    let unquoted =
      let n = String.length s0 in
      if n >= 2 && ((s0.[0] = '"' && s0.[n-1] = '"') || (s0.[0] = '\'' && s0.[n-1] = '\''))
      then String.sub s0 1 (n-2)
      else s0
    in
    match int_of_string_opt unquoted with
    | Some i -> Ast.mk_int i
    | None ->
        (match float_of_string_opt unquoted with
         | Some f -> Ast.mk_float f
         | None -> Ast.mk_expr (Ast.String unquoted))
  in
  List.map parse_one items

let handle_send_direct (params:(string, string) Hashtbl.t) : (int * string * string) =
  let get k = match Hashtbl.find_opt params k with Some v -> v | None -> "" in
  let to_ = get "to" in
  let meth = get "method" in
  let args = get "args" in
  let from_ = let f = get "from" in if f = "" then "<web>" else f in
  if to_ = "" || meth = "" then
    (400, "text/plain; charset=utf-8", "missing to/method")
  else
    let exprs = parse_args_to_exprs args in
    (try
       Eval_thread.send_message ~from:from_ to_ (CallStmt (meth, exprs));
       (200, "text/plain; charset=utf-8", "OK")
     with exn ->
       (500, "text/plain; charset=utf-8", "error: " ^ Printexc.to_string exn))

let handle_send_exposed ~(key:string) (params:(string, string) Hashtbl.t) : (int * string * string) =
  match Hashtbl.find_opt exposed key with
  | None -> (404, "text/plain; charset=utf-8", "unknown endpoint: " ^ key)
  | Some actor_name ->
      let get k = match Hashtbl.find_opt params k with Some v -> v | None -> "" in
      let meth = get "method" in
      let args = get "args" in
      let from_ = let f = get "from" in if f = "" then "<web>" else f in
      if meth = "" then
        (400, "text/plain; charset=utf-8", "missing method")
      else
        let exprs = parse_args_to_exprs args in
        (try
           Eval_thread.send_message ~from:from_ actor_name (CallStmt (meth, exprs));
           (200, "text/plain; charset=utf-8", "OK")
         with exn ->
           (500, "text/plain; charset=utf-8", "error: " ^ Printexc.to_string exn))

let handle_send_direct_json (body:string) : (int * string * string) =
  try
    match parse_json body with
    | JObject o ->
        let to_ = match json_get_string "to" o with Some s -> s | None -> "" in
        let meth = match json_get_string "method" o with Some s -> s | None -> "" in
        let from_ = match json_get_string "from" o with Some s -> s | None -> "<web>" in
        let args_json = match json_get_array "args" o with Some xs -> xs | None -> [] in
        if to_ = "" || meth = "" then
          (400, "text/plain; charset=utf-8", "missing to/method")
        else
          let exprs = List.map ast_of_json_value args_json in
          let (ok, msg, exprs2) = check_web_call ~actor_name:to_ ~method_name:meth exprs in
          if not ok then
            (400, "text/plain; charset=utf-8", "typecheck failed: " ^ msg)
          else
            (try
               Eval_thread.send_message ~from:from_ to_ (CallStmt (meth, exprs2));
               (200, "text/plain; charset=utf-8", "OK")
             with exn ->
               (500, "text/plain; charset=utf-8", "error: " ^ Printexc.to_string exn))
    | _ -> (400, "text/plain; charset=utf-8", "JSON must be an object")
  with
  | Json_error m -> (400, "text/plain; charset=utf-8", "bad JSON: " ^ m)

let handle_send_exposed_json ~(key:string) (body:string) : (int * string * string) =
  match Hashtbl.find_opt exposed key with
  | None -> (404, "text/plain; charset=utf-8", "unknown endpoint: " ^ key)
  | Some actor_name ->
      try
        match parse_json body with
        | JObject o ->
            let meth = match json_get_string "method" o with Some s -> s | None -> "" in
            let from_ = match json_get_string "from" o with Some s -> s | None -> "<web>" in
            let args_json = match json_get_array "args" o with Some xs -> xs | None -> [] in
            if meth = "" then
              (400, "text/plain; charset=utf-8", "missing method")
            else
              let exprs = List.map ast_of_json_value args_json in
              let (ok, msg, exprs2) = check_web_call ~actor_name ~method_name:meth exprs in
              if not ok then
                (400, "text/plain; charset=utf-8", "typecheck failed: " ^ msg)
              else
                (try
                   Eval_thread.send_message ~from:from_ actor_name (CallStmt (meth, exprs2));
                   (200, "text/plain; charset=utf-8", "OK")
                 with exn ->
                   (500, "text/plain; charset=utf-8", "error: " ^ Printexc.to_string exn))
        | _ -> (400, "text/plain; charset=utf-8", "JSON must be an object")
      with
      | Json_error m -> (400, "text/plain; charset=utf-8", "bad JSON: " ^ m)

let handle_client (client: file_descr) : unit =
  let ic = in_channel_of_descr client in
  let oc = out_channel_of_descr client in
  let safe_write s =
    output_string oc s;
    flush oc
  in
  (try
     match read_line_opt ic with
     | None -> ()
     | Some req_line ->
         let parts = split_on ' ' (trim req_line) in
         let meth, path =
           match parts with
           | m :: p :: _ -> (String.uppercase_ascii m, p)
           | _ -> ("", "/")
         in
         let headers = read_headers ic in
         let content_len =
           match Hashtbl.find_opt headers "content-length" with
           | None -> 0
           | Some v -> (try int_of_string (trim v) with _ -> 0)
         in
         let body = if content_len > 0 then read_exactly ic content_len else "" in
         let code, ctype, resp_body =
           match meth, path with
           | "GET", "/" -> (200, "text/html; charset=utf-8", html_index ())
           | "POST", "/api/send" ->
               let params = parse_form_urlencoded body in
               handle_send_direct params
           | "POST", "/api/json/send" ->
               handle_send_direct_json body
           | "POST", _ when String.length path >= String.length "/api/x/" &&
                            String.sub path 0 (String.length "/api/x/") = "/api/x/" ->
               let key = String.sub path (String.length "/api/x/") (String.length path - String.length "/api/x/") in
               let params = parse_form_urlencoded body in
               handle_send_exposed ~key params
           | "POST", _ when String.length path >= String.length "/api/json/x/" &&
                            String.sub path 0 (String.length "/api/json/x/") = "/api/json/x/" ->
               let key = String.sub path (String.length "/api/json/x/") (String.length path - String.length "/api/json/x/") in
               handle_send_exposed_json ~key body
           | _ -> (404, "text/plain; charset=utf-8", "not found")
         in
         safe_write (http_response ~code ~content_type:ctype resp_body)
   with _ -> ());
  (try close_in ic with _ -> ());
  (try close_out oc with _ -> ());
  (try Unix.close client with _ -> ())

let start ~(port:int) : unit =
  match !server_thread with
  | Some _ -> ()
  | None ->
      let thr =
        Thread.create
          (fun () ->
             let sock = Unix.socket PF_INET SOCK_STREAM 0 in
             Unix.setsockopt sock SO_REUSEADDR true;
             Unix.bind sock (ADDR_INET (Unix.inet_addr_any, port));
             Unix.listen sock 50;
             Printf.printf "[web] listening on http://localhost:%d/\n%!" port;
             while true do
               let (client, _) = Unix.accept sock in
               ignore (Thread.create handle_client client)
             done)
          ()
      in
      server_thread := Some thr
