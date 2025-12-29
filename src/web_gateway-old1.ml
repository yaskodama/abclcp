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

(* msg_id -> sid *)
let msgid_to_sid : (string, string) Hashtbl.t = Hashtbl.create 2048
let msgid_mu = Mutex.create ()

let bind_msgid_sid (msg_id:string) (sid:string) =
  Mutex.lock msgid_mu;
  Hashtbl.replace msgid_to_sid msg_id sid;
  Mutex.unlock msgid_mu

let lookup_sid (msg_id:string) : string option =
  Mutex.lock msgid_mu;
  let r = Hashtbl.find_opt msgid_to_sid msg_id in
  Mutex.unlock msgid_mu;
  r

(* ---- websocket clients per sid ---- *)
let ws_clients : (string, out_channel list ref) Hashtbl.t = Hashtbl.create 64
let ws_clients_mu = Mutex.create ()

let ws_add (sid:string) (oc:out_channel) : unit =
  Mutex.lock ws_clients_mu;
  let r =
    match Hashtbl.find_opt ws_clients sid with
    | Some r -> r
    | None -> let r = ref [] in Hashtbl.add ws_clients sid r; r
  in
  r := oc :: !r;
  Mutex.unlock ws_clients_mu

let ws_remove (sid:string) (oc:out_channel) : unit =
  Mutex.lock ws_clients_mu;
  (match Hashtbl.find_opt ws_clients sid with
   | Some r -> r := List.filter (fun x -> x != oc) !r
   | None -> ());
  Mutex.unlock ws_clients_mu

let ws_send_to_sid (sid:string) (f:out_channel -> unit) : unit =
  Mutex.lock ws_clients_mu;
  let targets =
    match Hashtbl.find_opt ws_clients sid with
    | Some r -> !r
    | None -> []
  in
  Mutex.unlock ws_clients_mu;
  List.iter (fun oc -> try f oc with _ -> ()) targets

(* ---------- WebSocket helpers (RFC6455) ---------- *)

let ws_guid = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

(* Minimal SHA1 implementation (pure OCaml) *)
let sha1 (s:string) : bytes =
  let open Int32 in
  let ( ++ ) = add in
  let ( ** ) = logxor in
  let ( &&& ) = logand in
  let ( ||| ) = logor in

  let rol x n = (shift_left x n) ||| (shift_right_logical x (32 - n)) in

  let ml = String.length s in
  let bit_len = Int64.mul (Int64.of_int ml) 8L in


  (* padding *)
  let pad_len =
    let r = (ml + 1) mod 64 in
    if r <= 56 then (56 - r) else (56 + (64 - r))
  in
  let total = ml + 1 + pad_len + 8 in
  let msg = Bytes.make total '\000' in
  Bytes.blit_string s 0 msg 0 ml;
  Bytes.set msg ml (Char.chr 0x80);
  (* write 64-bit length big-endian *)
  for i = 0 to 7 do
    let shift = 8 * (7 - i) in
    let b =
      Int64.(to_int (logand (shift_right bit_len shift) 0xFFL))
    in
    Bytes.set msg (total - 8 + i) (Char.chr b)
  done;

  let h0 = ref 0x67452301l
  and h1 = ref 0xEFCDAB89l
  and h2 = ref 0x98BADCFEl
  and h3 = ref 0x10325476l
  and h4 = ref 0xC3D2E1F0l in


  let w = Array.make 80 0l in

  let read_u32_be b off =
    let c i = Int32.of_int (Char.code (Bytes.get b (off+i))) in
    (shift_left (c 0) 24) |||
    (shift_left (c 1) 16) |||
    (shift_left (c 2) 8)  |||
    (c 3)
  in

  let blocks = total / 64 in
  for bi = 0 to blocks - 1 do
    let base = bi * 64 in
    for i = 0 to 15 do
      w.(i) <- read_u32_be msg (base + (i*4))
    done;
    for i = 16 to 79 do
      w.(i) <- rol (w.(i-3) ** w.(i-8) ** w.(i-14) ** w.(i-16)) 1
    done;

    let a = ref !h0
    and b = ref !h1
    and c = ref !h2
    and d = ref !h3
    and e = ref !h4 in


    for i = 0 to 79 do
      let f,k =
        if i <= 19 then (((!b &&& !c) ||| ((lognot !b) &&& !d)), 0x5A827999l)
        else if i <= 39 then ((!b ** !c ** !d), 0x6ED9EBA1l)
        else if i <= 59 then (((!b &&& !c) ||| (!b &&& !d) ||| (!c &&& !d)), 0x8F1BBCDCl)
        else ((!b ** !c ** !d), 0xCA62C1D6l)
      in
      let temp = (rol !a 5) ++ f ++ !e ++ k ++ w.(i) in
      e := !d;
      d := !c;
      c := rol !b 30;
      b := !a;
      a := temp;
    done;

    h0 := !h0 ++ !a;
    h1 := !h1 ++ !b;
    h2 := !h2 ++ !c;
    h3 := !h3 ++ !d;
    h4 := !h4 ++ !e;
  done;

let out = Bytes.create 20 in
  let write_u32_be v off =
    let byte i = Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical v (8*(3-i))) 0xFFl)) in
    Bytes.set out (off+0) (byte 0);
    Bytes.set out (off+1) (byte 1);
    Bytes.set out (off+2) (byte 2);
    Bytes.set out (off+3) (byte 3)
  in
  write_u32_be !h0 0;
  write_u32_be !h1 4;
  write_u32_be !h2 8;
  write_u32_be !h3 12;
  write_u32_be !h4 16;
  out

let base64_encode_bytes (b:bytes) : string =
  let tbl = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" in
  let n = Bytes.length b in
  let out = Buffer.create ((n+2)/3*4) in
  let get i = Char.code (Bytes.get b i) in
  let rec loop i =
    if i >= n then ()
    else
      let b0 = get i in
      let b1 = if i+1 < n then get (i+1) else 0 in
      let b2 = if i+2 < n then get (i+2) else 0 in
      let triple = (b0 lsl 16) lor (b1 lsl 8) lor b2 in
      let c0 = (triple lsr 18) land 0x3F
      and c1 = (triple lsr 12) land 0x3F
      and c2 = (triple lsr 6)  land 0x3F
      and c3 = triple land 0x3F in
      Buffer.add_char out tbl.[c0];
      Buffer.add_char out tbl.[c1];
      if i+1 < n then Buffer.add_char out tbl.[c2] else Buffer.add_char out '=';
      if i+2 < n then Buffer.add_char out tbl.[c3] else Buffer.add_char out '=';
      loop (i+3)
  in
  loop 0;
  Buffer.contents out

let ws_accept (sec_key:string) : string =
  sec_key ^ ws_guid |> sha1 |> base64_encode_bytes

(* Write a server->client TEXT frame. *)
let ws_send_text (oc:out_channel) (payload:string) : unit =
  let len = String.length payload in
  let b0 = 0x81 (* FIN=1, opcode=TEXT *) in
  output_char oc (Char.chr b0);
  if len < 126 then begin
    output_char oc (Char.chr len)
  end else if len < 65536 then begin
    output_char oc (Char.chr 126);
    output_char oc (Char.chr ((len lsr 8) land 0xFF));
    output_char oc (Char.chr (len land 0xFF));
  end else begin
    (* very large not needed for demo; send as 64-bit length *)
    output_char oc (Char.chr 127);
    for i = 7 downto 0 do
      output_char oc (Char.chr ((len lsr (8*i)) land 0xFF))
    done
  end;
  output_string oc payload;
  flush oc

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

let json_escape (s:string) : string =
  let b = Buffer.create (String.length s + 16) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | _ -> Buffer.add_char b c)
    s;
  Buffer.contents b

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
  "<pre id='out' style='background:#f4f4f4; padding:8px; min-height:2em'></pre>\n" ^
  "<h4>Actor log (latest prints)</h4>\n" ^
  "<pre id='log' style='background:#111; color:#0f0; padding:8px; min-height:8em; max-height:20em; overflow:auto'></pre>\n" ^
  "<h4>Events</h4>\n" ^
  "<div id='events' style='background:#222; padding:8px; min-height:6em; max-height:14em; overflow:auto; font-family: monospace'></div>\n" ^
  "<h4>Message Tree (by msg_id)</h4>\n" ^
  "<div id='tree' style='background:#111; color:#ddd; padding:8px; min-height:8em; max-height:24em; overflow:auto; font-family: monospace'></div>\n" ^
  "<pre id='replies'></pre>\n" ^
  "</div>\n" ^
  "</div>\n" ^
  "<script>\n" ^
  "function parseAtom(s){\n" ^
  "  s = (s ?? '').trim();\n" ^
  "  if(s.length===0) return null;\n" ^
  "  if(s==='true') return true;\n" ^
  "  if(s==='false') return false;\n" ^
  "  if(s==='null') return null;\n" ^
  "  // quoted string\n" ^
  "  if((s.startsWith('\\\"') && s.endsWith('\\\"')) || (s.startsWith('\'') && s.endsWith('\''))){\n" ^
  "    return s.slice(1, -1);\n" ^
  "  }\n" ^
  "  // number (int/float/scientific)\n" ^
  "  const num = Number(s);\n" ^
  "  if(Number.isFinite(num) && /^[-+]?((\\d+(\\.\\d*)?)|(\\.\\d+))([eE][-+]?\\d+)?$/.test(s)) return num;\n" ^
  "  return s;\n" ^
  "}\n" ^
  "async function send(){\n" ^
  "  const payload = {\n" ^
  "    to: document.getElementById('to').value,\n" ^
  "    method: document.getElementById('method').value,\n" ^
  "    args: document.getElementById('args').value.split(',').map(s=>s.trim()).filter(s=>s.length>0).map(parseAtom),\n" ^
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
       Eval_thread.send_message ~from:from_ to_ (mk_stmt (CallStmt (meth, exprs)));
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
           Eval_thread.send_message ~from:from_ actor_name (mk_stmt (CallStmt (meth, exprs)));
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
        let sid = match json_get_string "sid" o with Some s -> s | None -> "" in
        let args_json = match json_get_array "args" o with Some xs -> xs | None -> [] in
        if to_ = "" || meth = "" then
          (400, "text/plain; charset=utf-8", "missing to/method")
        else
          let exprs = List.map ast_of_json_value args_json in
          let (ok, msg, exprs2) = check_web_call ~actor_name:to_ ~method_name:meth exprs in
          if not ok then (
            Eval_thread.push_web_evt
              (Printf.sprintf "[FAILED] to=%s.%s reason=typecheck:%s" to_ meth msg);
            (400, "text/plain; charset=utf-8", "typecheck failed: " ^ msg)
          ) else (
           let msg_id =
               Printf.sprintf "m-%d" (int_of_float (Unix.time () *. 1000.0))
            in
            if sid <> "" then bind_msgid_sid msg_id sid;               
            Eval_thread.push_web_evt
              (Printf.sprintf "[ACCEPTED] id=%s to=%s.%s" msg_id to_ meth);
            try
              Eval_thread.send_message ~msg_id ~from:from_ to_ (mk_stmt (CallStmt (meth, exprs2)));
              (200, "text/plain; charset=utf-8", "OK")
            with exn ->
              Eval_thread.push_web_evt
                (Printf.sprintf "[FAILED] id=%s to=%s.%s reason=%s"
                   msg_id to_ meth (Printexc.to_string exn));
              (500, "text/plain; charset=utf-8", "error: " ^ Printexc.to_string exn)
          )
    | _ ->
        (400, "text/plain; charset=utf-8", "JSON must be an object")
  with
  | Json_error m ->
      (400, "text/plain; charset=utf-8", "bad JSON: " ^ m)

let handle_send_exposed_json ~(key:string) (body:string) : (int * string * string) =
  match Hashtbl.find_opt exposed key with
  | None ->
      (404, "text/plain; charset=utf-8", "unknown endpoint: " ^ key)
  | Some actor_name ->
      try
        match parse_json body with
        | JObject o ->
            let meth = match json_get_string "method" o with Some s -> s | None -> "" in
            let from_ = match json_get_string "from" o with Some s -> s | None -> "<web>" in
            let args_json = match json_get_array "args" o with Some xs -> xs | None -> [] in
            let sid = match json_get_string "sid" o with Some s -> s | None -> "" in
            if meth = "" then
              (400, "text/plain; charset=utf-8", "missing method")
            else
             let exprs = List.map ast_of_json_value args_json in
              let (ok, msg, exprs2) = check_web_call ~actor_name ~method_name:meth exprs in
              if not ok then (
                Eval_thread.push_web_evt
                  (Printf.sprintf "[FAILED] to=%s.%s reason=typecheck:%s" actor_name meth msg);
                (400, "text/plain; charset=utf-8", "typecheck failed: " ^ msg)
              ) else (
                let msg_id =
                  Printf.sprintf "m-%d" (int_of_float (Unix.time () *. 1000.0))
                in
                if sid <> "" then bind_msgid_sid msg_id sid;
                Eval_thread.push_web_evt
                  (Printf.sprintf "[ACCEPTED] id=%s to=%s.%s" msg_id actor_name meth);
                try
		  Eval_thread.send_message ~msg_id ~from:from_ actor_name (mk_stmt (CallStmt (meth, exprs2)));
                  (200, "text/plain; charset=utf-8", "OK")
                with exn ->
                 Eval_thread.push_web_evt
                    (Printf.sprintf "[FAILED] id=%s to=%s.%s reason=%s"
                       msg_id actor_name meth (Printexc.to_string exn));
                  (500, "text/plain; charset=utf-8", "error: " ^ Printexc.to_string exn)
              )
        | _ ->
            (400, "text/plain; charset=utf-8", "JSON must be an object")
      with
      | Json_error m ->
          (400, "text/plain; charset=utf-8", "bad JSON: " ^ m)

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
