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
     - We intentionally keep the payload form-encoded to avoid JSON libs.
*)

open Unix

(* We only need Eval_thread.send_message and Ast constructors. *)
open Ast

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
  (* A tiny UI that posts form-encoded data to /api/send. *)
  "<!doctype html>\n" ^
  "<html><head><meta charset='utf-8'><title>ABCL/c+ Web Gateway</title></head>\n" ^
  "<body style='font-family: sans-serif'>\n" ^
  "<h2>ABCL/c+ Web Gateway</h2>\n" ^
  "<p>Send a message to an actor in the running ABCL/c+ process.</p>\n" ^
  "<div style='display:flex; gap:24px; align-items:flex-start'>\n" ^
  "<div>\n" ^
  "<h3>Direct send</h3>\n" ^
  "<label>to (actor name): <input id='to' value='calc'></label><br>\n" ^
  "<label>method: <input id='method' value='add'></label><br>\n" ^
  "<label>args (comma sep): <input id='args' value='1,2'></label><br>\n" ^
  "<button onclick='send()'>Send</button>\n" ^
  "<pre id='out' style='background:#f4f4f4; padding:8px; min-height:4em'></pre>\n" ^
  "</div>\n" ^
  "</div>\n" ^
  "<script>\n" ^
  "async function send(){\n" ^
  "  const p = new URLSearchParams();\n" ^
  "  p.set('to', document.getElementById('to').value);\n" ^
  "  p.set('method', document.getElementById('method').value);\n" ^
  "  p.set('args', document.getElementById('args').value);\n" ^
  "  p.set('from', 'browser');\n" ^
  "  const r = await fetch('/api/send',{method:'POST', headers:{'Content-Type':'application/x-www-form-urlencoded'}, body:p.toString()});\n" ^
  "  const t = await r.text();\n" ^
  "  document.getElementById('out').textContent = t;\n" ^
  "}\n" ^
  "</script>\n" ^
  "</body></html>\n"

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
           | "POST", _ when String.length path >= String.length "/api/x/" &&
                            String.sub path 0 (String.length "/api/x/") = "/api/x/" ->
               let key = String.sub path (String.length "/api/x/") (String.length path - String.length "/api/x/") in
               let params = parse_form_urlencoded body in
               handle_send_exposed ~key params
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
