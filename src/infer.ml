(* infer.ml *)
open Types

let verbose =
  match Sys.getenv_opt "AIOS_QUIET" with
  | Some "1" | Some "true" | Some "yes" -> ref false
  | _ -> ref true
open Typing_env
open Ast

let in_preinfer = ref false

let unify_at (loc:Location.t) (t1:ty) (t2:ty): bool =
  try
    Types.unify ~loc t1 t2; true
  with
  | Types.Type_error (_, msg) -> Types.type_error ~loc msg

let set_var_scheme (env : (string, scheme list) Hashtbl.t) (x:string) (sch:scheme) : unit =
  Hashtbl.replace env x [sch]

let find_all (env : (string, scheme list) Hashtbl.t) (name : string) : scheme list =
  match Hashtbl.find_opt env name with
  | Some schemes -> schemes
  | None -> []

let ty_of_binop_as_function (op:string) : ty option =
  (* Binop は「関数」のオーバーロードとして env にも入れているので、ここでは補助的に *)
  match op with
  | _ -> None

(* env : Typing_env.env = (string, Types.scheme list) Hashtbl.t *)
let ftv_env (env : Typing_env.env) : Types.ISet.t =
  Hashtbl.fold
    (fun _name (schemes : Types.scheme list) acc ->
       List.fold_left
         (fun acc sch -> Types.ISet.union acc (Types.ftv_scheme sch))
         acc schemes)
    env Types.ISet.empty

let generalize_env (env : Typing_env.env) (t : Types.ty) : Types.scheme =
  Types.generalize (ftv_env env) t

(* ---- shallow clone for env (string -> scheme list) ---- *)
let clone (e : (string, scheme list) Hashtbl.t) : (string, scheme list) Hashtbl.t =
  let e' = Hashtbl.create (Hashtbl.length e) in
  Hashtbl.iter (fun k v -> Hashtbl.replace e' k v) e;
  e'

(* ---------------------------------------------------------------- *)
(*  reply の構文スキャン                                              *)
(* ---------------------------------------------------------------- *)
(* 本体に reply(...) が1つでも現れるか。
   現れないメソッドは戻り値 ρ を即座に unit へ落とす（Pony の
   「戻り値型を省略した関数は None を返す」と同じ defaulting）。
   これをやらないと reply を書き忘れたメソッドの ρ が未束縛のまま残り、
   呼び出し側の now が「どんな型にも化ける値」を受け取ってしまう。
   実行時にはその now は永久に返らないので、型が嘘をつくことになる。 *)
let rec expr_has_reply (e : Ast.expr) : bool =
  match e.desc with
  | Ast.Call ("reply", _) -> true
  | Ast.Call (_, args)
  | Ast.New (_, args)
  | Ast.Array (args, _)
  | Ast.FutureSend (_, _, args) -> List.exists expr_has_reply args
  | Ast.NowSend (_, _, args, d) ->
      List.exists expr_has_reply args || alt_has_reply d
  | Ast.Binop (_, a, b) -> expr_has_reply a || expr_has_reply b
  | Ast.Expr e1 -> expr_has_reply e1
  | Ast.Await (e1, d) -> expr_has_reply e1 || alt_has_reply d
  | Ast.Int _ | Ast.Float _ | Ast.String _ | Ast.Bool _ | Ast.Var _ | Ast.ActorRef _ | Ast.ReplyRef _ -> false
and alt_has_reply = function
  | None -> false
  | Some (_, None) -> false
  | Some (_, Some a) -> expr_has_reply a

let rec stmt_has_reply (s : Ast.stmt) : bool =
  match s.sdesc with
  | Ast.CallStmt ("reply", _) -> true
  | Ast.CallStmt (_, args)
  | Ast.Send (_, _, args)
  | Ast.UnsafeSend (_, _, args)
  | Ast.Become (_, args) -> List.exists expr_has_reply args
  | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> expr_has_reply e
  | Ast.Seq ss -> List.exists stmt_has_reply ss
  | Ast.If (c, a, b) ->
      expr_has_reply c || stmt_has_reply a || stmt_has_reply b
  | Ast.While (c, b) -> expr_has_reply c || stmt_has_reply b
  (* ★ select の case 本体にある reply は、囲むメソッドではなく
     「選択されたメッセージ」に返る。eval_thread が case 実行の前に
     set_current_msg_id を差し替えるためである。よってここでは数えない。
     timeout 本体は囲むメソッドの msg_id のまま走るので数える。 *)
  | Ast.Select (_cases, (_, to_body)) ->
      (match to_body with Some b -> stmt_has_reply b | None -> false)

(* 「すべての実行パスで必ず reply する」か。
   戻り値型を宣言したメソッドにだけ課す検査で、推論側には書けない。
   宣言型という照合先があって初めて「reply し損ねている」と言えるためである。
   while の本体は0回実行されうるので false（保守的）。 *)
let rec replies_on_all_paths (s : Ast.stmt) : bool =
  match s.sdesc with
  | Ast.CallStmt ("reply", _) -> true
  | Ast.Seq ss -> List.exists replies_on_all_paths ss
  | Ast.If (_, a, b) -> replies_on_all_paths a && replies_on_all_paths b
  (* case 本体の reply は別メッセージ宛なので、囲むメソッドの被覆にはならない。
     case が選ばれた実行では囲むメソッドは reply しないまま終わる。 *)
  | Ast.Select (_, _) -> false
  (* 式は無条件に評価されるので、式中の reply も「必ず起きる」とみなせる *)
  | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> expr_has_reply e
  | Ast.CallStmt (_, args)
  | Ast.Send (_, _, args)
  | Ast.UnsafeSend (_, _, args)
  | Ast.Become (_, args) -> List.exists expr_has_reply args
  | Ast.While (_, _) -> false

(* reply の回数の構文的な上界。2 は「2 回以上ありうる」を表す（それ以上は数えない）。
   ちょうど一度 reply することを検査するために使う。二重 reply は
   resolve_future が 2 度呼ばれることになり、後から来た値は
   すでに待ち手が受け取ったあとなので黙って捨てられる。 *)
let cap2 n = if n > 2 then 2 else n

(* select の case が待っているメッセージ（クラス名, メソッド名, 位置）。
   プログラムを全部見終わってから「誰かが送っているか」を照合する。
   先に照合すると、あとで現れる送信を見落とす。 *)
let selected_msgs : (string * string * Location.t) list ref = ref []

(* 本体が replyto を使っているか。
   使っていれば「返信の義務」は線形性の検査（check_reply_linearity）が担うので、
   reply の回数・被覆の構文検査は適用しない。 *)
let rec expr_uses_replyto (e : Ast.expr) : bool =
  match e.desc with
  | Ast.Var "replyto" -> true
  | Ast.Call (_, args) | Ast.New (_, args) | Ast.FutureSend (_, _, args) ->
      List.exists expr_uses_replyto args
  | Ast.NowSend (_, _, args, d) ->
      List.exists expr_uses_replyto args
      || (match d with Some (_, Some a) -> expr_uses_replyto a | _ -> false)
  | Ast.Await (e1, d) ->
      expr_uses_replyto e1
      || (match d with Some (_, Some a) -> expr_uses_replyto a | _ -> false)
  | Ast.Binop (_, a, b) -> expr_uses_replyto a || expr_uses_replyto b
  | Ast.Expr e1 -> expr_uses_replyto e1
  | _ -> false

let rec stmt_uses_replyto (s : Ast.stmt) : bool =
  match s.sdesc with
  | Ast.Seq ss -> List.exists stmt_uses_replyto ss
  | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> expr_uses_replyto e
  | Ast.CallStmt (_, args) | Ast.Send (_, _, args) | Ast.UnsafeSend (_, _, args)
  | Ast.Become (_, args) -> List.exists expr_uses_replyto args
  | Ast.If (c, a, b) ->
      expr_uses_replyto c || stmt_uses_replyto a || stmt_uses_replyto b
  | Ast.While (c, b) -> expr_uses_replyto c || stmt_uses_replyto b
  | Ast.Select (cases, (_, to_body)) ->
      List.exists (fun (c : Ast.select_case) -> stmt_uses_replyto c.Ast.body) cases
      || (match to_body with Some b -> stmt_uses_replyto b | None -> false)


let rec max_replies_expr (e : Ast.expr) : int =
  match e.desc with
  | Ast.Call ("reply", args) ->
      cap2 (1 + List.fold_left (fun n a -> n + max_replies_expr a) 0 args)
  | Ast.Call (_, args)
  | Ast.New (_, args)
  | Ast.Array (args, _)
  | Ast.FutureSend (_, _, args) ->
      cap2 (List.fold_left (fun n a -> n + max_replies_expr a) 0 args)
  (* 期限切れの else 節は「本体と else のどちらか一方」なので max を取る *)
  | Ast.NowSend (_, _, args, d) ->
      cap2 (List.fold_left (fun n a -> n + max_replies_expr a) 0 args
            + max_alt d)
  | Ast.Binop (_, a, b) -> cap2 (max_replies_expr a + max_replies_expr b)
  | Ast.Expr e1 -> max_replies_expr e1
  | Ast.Await (e1, d) -> cap2 (max_replies_expr e1 + max_alt d)
  | Ast.Int _ | Ast.Float _ | Ast.String _ | Ast.Bool _ | Ast.Var _ | Ast.ActorRef _ | Ast.ReplyRef _ -> 0
and max_alt = function None -> 0 | Some (_, None) -> 0 | Some (_, Some a) -> max_replies_expr a

(* 囲むメソッドから見た reply 回数の上界。
   select の case 本体は別メッセージ宛なので数えない（timeout 本体だけ数える）。 *)
let rec max_replies (s : Ast.stmt) : int =
  match s.sdesc with
  | Ast.CallStmt ("reply", args) ->
      cap2 (1 + List.fold_left (fun n a -> n + max_replies_expr a) 0 args)
  | Ast.CallStmt (_, args)
  | Ast.Send (_, _, args)
  | Ast.UnsafeSend (_, _, args)
  | Ast.Become (_, args) ->
      cap2 (List.fold_left (fun n a -> n + max_replies_expr a) 0 args)
  | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> max_replies_expr e
  | Ast.Seq ss -> cap2 (List.fold_left (fun n st -> n + max_replies st) 0 ss)
  | Ast.If (c, a, b) ->
      cap2 (max_replies_expr c + max (max_replies a) (max_replies b))
  (* 本体が 1 回でも reply するなら、ループなので 2 回以上ありうる *)
  | Ast.While (c, b) ->
      cap2 (max_replies_expr c + (if max_replies b > 0 then 2 else 0))
  | Ast.Select (_, (_, to_body)) ->
      (match to_body with Some b -> max_replies b | None -> 0)

(* ---------------------------------------------------------------- *)
(*  効果の収集                                                       *)
(* ---------------------------------------------------------------- *)
(* いま検査しているメソッドの効果を溜める先。check_decl が
   メソッドごとに Types.eff_cell で確保したセルを指す。 *)
let current_eff : Types.SSet.t ref ref = ref (ref Types.SSet.empty)
let current_key : string ref = ref ""

(* current_key は "クラス名#メソッド名"。いま検査しているクラス名を返す。 *)
let current_class_name () : string =
  match String.index_opt !current_key '#' with
  | Some i -> String.sub !current_key 0 i
  | None -> ""
(* いま検査しているクラスのフィールド名。代入が mut かどうかの判定に使う。
   ローカル変数への代入は mut ではない。 *)
let current_fields : (string, unit) Hashtbl.t = Hashtbl.create 16

let add_eff (l : string list) : unit =
  let c = !current_eff in
  c := List.fold_left (fun acc e -> Types.SSet.add e acc) !c l

let add_eff_set (e : Types.SSet.t) : unit =
  let c = !current_eff in c := Types.SSet.union !c e

(* 検査中のメソッドが戻り値型を宣言しているか（エラー文言の出し分け用） *)
let current_ret_declared = ref false

(* now で待つ辺を記録する。future / send は待たないので辺を張らない。
   FutureSend の型付けは now からも使われるので、now かどうかは
   呼び出し側で判定して here を呼ぶ。 *)
module SSet = Types.SSet

(* 未宣言の名前への代入を暗黙の宣言として受ける、従来の挙動へ戻す逃げ道。 *)
(* send も呼ばれる側の効果を引き継ぐか。既定は off（OCaml 版の従来動作）。 *)
let send_effects () : bool =
  match Sys.getenv_opt "AIOS_SEND_EFFECTS" with
  | Some ("1" | "true" | "yes") -> true
  | _ -> false

(* become の置換先が元のインタフェースを満たすかの検査を外す逃げ道。 *)
(* 循環待ちの検査。既定はエラー。
   手元の .aipl 543 本すべてで閉路が 0 件だったので、既定を厳しくしても
   既存のコードは落ちない。AIOS_LAX_WAIT=1 で警告に落とせる。 *)
let strict_wait () : bool =
  match Sys.getenv_opt "AIOS_LAX_WAIT" with
  | Some ("1" | "true" | "yes") -> false
  | _ -> true

let lax_become () : bool =
  match Sys.getenv_opt "AIOS_LAX_BECOME" with
  | Some ("1" | "true" | "yes") -> true
  | _ -> false

let lax_assign () : bool =
  match Sys.getenv_opt "AIOS_LAX_ASSIGN" with
  | Some ("1" | "true" | "yes") -> true
  | _ -> false

let in_now_send = ref false

(* 直前に型付けした FutureSend の呼び先（効果キー）。
   FutureSend の本体は入れ子の match の中で決まるので、
   結果を組み立てる場所まで値を運ぶための一時置き場。 *)
let pending_future_callee : Types.SSet.t ref = ref Types.SSet.empty

let record_now_edge (cls : string) (mname : string) : unit =
  (* future / now のどちらでも呼び先を記録する。
     now はここで即座に辺を張り、future は型に載せて await まで持ち越す。 *)
  pending_future_callee := Types.SSet.singleton (Types.eff_key cls mname);
  if !in_now_send && !current_key <> "" then
    Types.add_now_edge !current_key (Types.eff_key cls mname)

(* 送信先メソッドの戻り値型 ρ を引く。
   リモート先など静的に本体が見えないメソッドは any のまま（従来どおり）。 *)
let method_ret_ty (cls : string) (mname : string) : ty =
  match Types.lookup_method_ret cls mname with
  | Some t -> t
  | None   -> TAny

(* loc 付きで unify を試して、成功なら true、失敗なら false を返すヘルパ *)
let unify_try (loc : Location.t) (t1 : ty) (t2 : ty) : bool =
  try
    Types.unify ~loc t1 t2; true
  with
  | Types.Type_error _ -> false

(* ---------------------------------------------------------------- *)
(*  オーバーロード解決                                                *)
(* ---------------------------------------------------------------- *)

(* AIOS_STRICT_DEADLINE=1 で、期限なしの now / await をエラーにする。
   既定は警告（既存コードに now が 57 箇所・await が 30 箇所あるため）。 *)
let strict_deadline =
  match Sys.getenv_opt "AIOS_STRICT_DEADLINE" with
  | Some "1" | Some "true" | Some "yes" -> ref true
  | _ -> ref false

(* 曖昧な overload は既定でエラーにする。
   principal type が無い箇所は注釈で決める、という規律にするため。
   コーパス 49 本で実測して 1 本も落ちなかったので既定 ON にできた。
   AIOS_LAX_OVERLOAD=1 で従来の「警告して既定候補を選ぶ」動作に戻せる。 *)
let strict_overload =
  match Sys.getenv_opt "AIOS_LAX_OVERLOAD" with
  | Some "1" | Some "true" | Some "yes" -> ref false
  | _ -> ref true

(* 型に現れる型変数セルを、link 鎖もたどって集める。
   トライアルで焼き付いた束縛を巻き戻すための対象リストになる。 *)
let collect_tvar_cells (ts : ty list) : tvar ref list =
  let seen : (int, unit) Hashtbl.t = Hashtbl.create 16 in
  let acc = ref [] in
  let rec go t =
    match t with
    | TVar cell ->
        let id = (!cell).id in
        if not (Hashtbl.mem seen id) then begin
          Hashtbl.replace seen id ();
          acc := cell :: !acc;
          match (!cell).link with Some t' -> go t' | None -> ()
        end
    | TArray t1 -> go t1
    | TFuture (t1, _) -> go t1
    | TRecord fs      -> List.iter (fun (_, t1) -> go t1) fs
    | TActor (_, ms)  -> List.iter (fun (_, t1) -> go t1) ms
    | TFun (ps, r)    -> List.iter go ps; go r
    | _ -> ()
  in
  List.iter go ts;
  !acc

(* link を「値として」保存/復元する。
   repr は `cell := {!cell with link}`、prune は `(!cell).link <- ...` と
   2通りの書き換えをするので、レコードを共有したまま持つと復元にならない。
   新しいレコードを作り直して差し替える。 *)
let snapshot_links (cells : tvar ref list) : (tvar ref * ty option) list =
  List.map (fun c -> (c, (!c).link)) cells

let restore_links (snap : (tvar ref * ty option) list) : unit =
  List.iter (fun (c, l) -> c := { !c with link = l }) snap

(* 引数型が型変数を含まない（＝候補が「具体的」）か *)
let is_ground (t : ty) : bool = ISet.is_empty (ftv_ty t)

(* loc 付きオーバーロード解決

   従来の実装には2つの欠陥があった。

   (1) 失敗した候補の単一化が巻き戻らない。
       List.for_all2 は途中で false になると打ち切るので、それまでに
       結んだ束縛（例: 第1引数 := string）が残ったまま次の候補へ進む。
       候補を1つ試すたびに引数の型が汚染されていく。

   (2) 候補の優先順位が「登録順の逆」。
       typing_env は overload を `sch :: prev` で積むので、リストの先頭は
       最後に登録されたものになる。`+` なら ('a * string) -> string が先頭で、
       引数が両方とも未束縛の型変数のときはこれが必ず最初に一致してしまう。
       a + b が問答無用で string に潰れていたのはこれが理由。

   ここでは
     - 各トライアルの前後で link をスナップショット/復元し、副作用を出さない
     - 候補を「具体的な引数型を持つもの優先 → 引数側の型変数を束縛しない
       もの優先 → 登録順」で順位付けする
     - 最上位が複数あって戻り値型が割れる場合は、真に曖昧なので報告する
   の3点を行う。

   さらに、呼び出し元から期待型 [expected] が与えられていれば
   「戻り値がそれと合う候補」を最優先する。これが戻り値型注釈の効きどころで、
   a + b のように引数だけからは principal type が決まらない式でも、
   囲む reply の宣言型が分かっていれば一意に解決できる。 *)
let pick_overload ?expected (loc:Location.t) (name:string) (env:tenv) (arg_tys:ty list) : ty =
  (* ★ プリミティブの効果を、いま検査中のメソッドへ足す *)
  add_eff_set (Typing_env.prim_eff name);
  let schemes =
    match Hashtbl.find_opt env name with
    | Some ss -> List.rev ss     (* ★ 登録順に戻す *)
    | None    -> []
  in
  let arg_cells = collect_tvar_cells arg_tys in
  let base = snapshot_links arg_cells in
  let exp_tys = match expected with Some t -> [t] | None -> [] in

  (* 候補を1つ試す。副作用は必ず巻き戻す。 *)
  let trial (idx : int) (sch : scheme) =
    let inst = repr (instantiate sch) in
    let snap = snapshot_links (collect_tvar_cells (inst :: arg_tys @ exp_tys)) in
    let res =
      match inst with
      | TFun (ps, ret) when List.length ps = List.length arg_tys ->
          let ground = List.for_all is_ground ps in
          if List.for_all2 (unify_try loc) ps arg_tys then begin
            (* このトライアルで新たに束縛された引数側変数の個数。
               少ないほど「引数の型を決め打ちしていない」＝素直な一致。 *)
            let binds =
              List.fold_left
                (fun n (c, l0) ->
                   if l0 = None && (!c).link <> None then n + 1 else n)
                0 base
            in
            (* 期待型との照合。ここでの単一化も選択のためだけで、巻き戻される。 *)
            let exp_ok =
              match expected with
              | None    -> true
              | Some te -> unify_try loc ret te
            in
            Some (exp_ok, ground, binds, idx, sch,
                  Types.string_of_ty_pretty (prune ret))
          end else None
      | _ -> None
    in
    restore_links snap;
    res
  in

  let cands =
    schemes
    |> List.mapi (fun i sch -> (i, sch))
    |> List.filter_map (fun (i, sch) -> trial i sch)
  in
  restore_links base;   (* 念のため、全トライアル分をもう一度戻す *)

  let rank (exp_ok, ground, binds, idx, _, _) =
    ((if exp_ok then 0 else 1), (if ground then 0 else 1), binds, idx) in
  let sorted = List.sort (fun a b -> compare (rank a) (rank b)) cands in

  match sorted with
  | (e0, g0, b0, _, winner, _) :: _ ->
      (* 同順位に戻り値型の異なる候補が残っていれば、この呼び出しは真に曖昧。
         principal type が無いので、本来は型注釈で決めるしかない。 *)
      let top =
        List.filter (fun (e, g, b, _, _, _) -> e = e0 && g = g0 && b = b0) sorted in
      let rets = List.sort_uniq compare (List.map (fun (_,_,_,_,_,r) -> r) top) in
      if List.length rets > 1 then begin
        let msg =
          Printf.sprintf
            "ambiguous overload of %s for (%s): candidate return types are %s"
            name
            (String.concat ", " (List.map Types.string_of_ty_pretty arg_tys))
            (String.concat " / " rets)
        in
        if !strict_overload then Types.type_error ~loc msg
        else
          Printf.eprintf "[warn] %s: %s (picked %s)\n%!"
            (Location.to_string loc) msg (List.hd rets)
      end;
      (* 勝った候補だけを、今度は本番として単一化する *)
      (match repr (instantiate winner) with
       | TFun (ps, ret) ->
           List.iter2 (Types.unify ~loc) ps arg_tys;
           repr ret
       | t -> t)
  | [] ->
      let sigstr =
        "(" ^ String.concat ", " (List.map Types.string_of_ty_pretty arg_tys) ^ ")"
      in
      Types.type_error ~loc ("no overload of " ^ name ^ " matches " ^ sigstr)

let lookup_method_type (tobj : ty) (mname : string) : ty option =
  match repr tobj with
  | TActor (cls, ms) -> begin
      match List.assoc_opt mname (ms : (string * ty) list) with
      | Some t -> Some t
      | None ->
          (* fallback: 事前登録済みのスキーマを具体化して返す *)
          (match Types.lookup_class_method_scheme cls mname with
           | Some sc -> Some (Types.instantiate sc)
           | None    -> None)
    end
  | _ -> None

(* 期待型として下へ流してよいのは、それ自身に未確定の型変数を含まない型だけ。
   未束縛の ρ をそのまま流すと、overload 候補との照合で ρ 自身が
   最初の候補の戻り値型に焼き付いてしまう。 *)
let expected_of (t : ty) : ty option =
  let t' = repr t in
  if is_ground t' then Some t' else None

(* reply(v) の型付け。
   検査中のメソッドの戻り値型 ρ は、env の "reply" に (ρ -> unit) として
   単相で束縛されている（check_decl / preinfer が入れる）。
   グローバルの reply : forall a. a -> unit はそれに隠される。

   ここを pick_overload 任せにせず専用に書いているのは、失敗時のメッセージの
   ためである。overload 解決に流すと「no overload of reply matches (string)」
   という、どの reply と衝突したのか分からない文言になる。 *)
let rec check_reply (env:env) (loc:Location.t) (args : Ast.expr list) : ty =
  match Hashtbl.find_opt env "reply" with
  | Some (Forall ([], TFun ([rho], _)) :: _) ->
      (match args with
       | [a] ->
           let before = Types.string_of_ty_pretty (repr rho) in
           (* ★ 宣言済みの ρ を期待型として引数の推論へ流す（双方向型付け）。
              これがあると reply(a + b) の overload が一意に決まる。 *)
           let t = infer_expr ?expected:(expected_of rho) env a in
           (try Types.unify ~loc rho t
            with Types.Type_error (_, _) ->
              let here = Types.string_of_ty_pretty (repr t) in
              let msg =
                if !current_ret_declared then
                  Printf.sprintf
                    "reply type mismatch: this method is declared to reply with %s, but replies with %s here"
                    before here
                else
                  Printf.sprintf
                    "reply type mismatch: this method replies with %s elsewhere, but with %s here"
                    before here
              in
              Types.type_error ~loc msg);
           TUnit
       | _ ->
           Types.type_error ~loc
             (Printf.sprintf "reply takes exactly 1 argument, got %d"
                (List.length args)))
  | _ ->
      (* メソッド本体の外側にある reply（グローバル文など）は従来どおり *)
      pick_overload loc "reply" env (List.map (infer_expr env) args)

and infer_expr ?expected (env:env) (e:expr) : ty =
  match e.desc with
  | Int _ -> TInt
  | Float _ -> TFloat
  | Bool _ -> TBool
  (* 実行時に値から作られる式。クラスは実行時にしか分からないので
     未知のアクター型にしておく（unify は TActor 同士を同一視する） *)
  | ReplyRef _ -> Types.TReply (Types.TVar (Types.fresh_tvar ()))
  | ActorRef _ -> TActor ("?", [])
  | String _ -> TString
  | Binop (op, e1, e2) ->
    let t1 = infer_expr env e1 in
    let t2 = infer_expr env e2 in
    (* かつてここに "+" の片側が string なら string、という特例があった。
       文字列連結を ++ に分けたので不要になり、+ は純粋に数値演算になった。 *)
    pick_overload ?expected e.loc op env [t1; t2]
  | Call ("reply", args) ->
      check_reply env e.loc args
  | Call (fname, arg1) ->
      let t_args = List.map (infer_expr env) arg1 in
      pick_overload ?expected e.loc fname env t_args
  | Expr e -> infer_expr env e
  | Var x when x = "sender" -> TAny
  (* ★ replyto ---- いま処理しているメッセージの返信先を値として取り出す。
     ABCL/1 の reply destination の一級性を、線形に扱うことで取り戻したもの。
     型は reply<ρ>（ρ はこのメソッドの戻り値型）。
     使ったら、ちょうど一度 answer するか、他へ渡して義務を移さなければならない。 *)
  | Var "replyto" when !current_key <> "" ->
      let cls = current_class_name () in
      let mname =
        (match String.index_opt !current_key '#' with
         | Some i -> String.sub !current_key (i + 1) (String.length !current_key - i - 1)
         | None -> "") in
      Types.TReply (method_ret_ty cls mname)
  | Var x ->
     (* preinfer（1パス目）のときは、未束縛変数は「新しい型変数」として許す *)
      (match Hashtbl.find_opt env x with
       | Some [sch] ->
           instantiate sch
       | Some (sch :: _) ->
           instantiate sch
       | Some [] ->
           (* 空リストになっていることは通常ないはずだが、念のため *)
           TVar(Types.fresh_tvar ())
       | None ->
           if !in_preinfer then
             (* ★ preinfer 中：グローバル actor など、まだ env に無い変数があっても
                とりあえず fresh な型変数を割り当てて先に進む *)
             TVar(Types.fresh_tvar ())
           else
             (* ★ 2パス目（本番）：ここで初めて「未束縛変数はエラー」とする *)
             raise (Type_error (e.loc, ("unbound variable: " ^ x))))
  | New (cls, args) ->
    add_eff ["mem"];                     (* ★ 動的割り付け *)
    let targs = List.map (infer_expr env) args in
    (match Types.lookup_class_method_scheme cls "init" with
     | Some sch ->
         (match Types.instantiate sch with
          | Types.TFun (params, _ret) ->
              let unify_many ps qs =
                try List.iter2 (Types.unify ~loc:e.loc) ps qs with Invalid_argument _ ->
                    Types.type_error ~loc:e.loc (Printf.sprintf "constructor %s: arity mismatch (expected %d, got %d)"
                         cls (List.length ps) (List.length qs))
              in
                unify_many params targs
          | ty ->
              raise (Type_error (e.loc,
                (Printf.sprintf "constructor %s: init is not a function: %s"
                   cls (Types.string_of_ty_pretty ty))))
          )
     | None -> ());
    let ms = Types.lookup_class_methods_inst cls in TActor (cls, ms)
  | FutureSend (target, mname, args) ->
      let arg_tys = List.map (infer_expr env) args in
      (* 引数の中に別の future があると呼び先が残っているので、必ず消してから入る。
         呼び先が静的に分からない枝（remote / sender）では空のままになる。 *)
      pending_future_callee := Types.SSet.empty;
      let ret =
        begin match target with
        (* リモート宛先は本体が別ノードにあり推論できない。
           ここは宣言（インタフェース）でしか埋まらない場所なので any のまま。
           ただし★ノード外へ出る通信なので net 効果は確定する。 *)
        | RemoteTarget (hostport, _actor_name) ->
            add_eff ["net"];
            (* ★ 遠隔への待ち。宛先の実体は見えないので、ノード単位で記録する。 *)
            if !current_key <> "" then Types.add_remote_wait !current_key hostport;
            TAny
        | LocalTarget vname when vname = "sender" -> TAny
        | LocalTarget vname ->
            let t_actor = infer_expr env (mk_var vname) in
            (match repr t_actor with
             | TActor (cls, _) ->
                 (match Types.lookup_class_method_scheme cls mname with
                  | None ->
                      Types.type_error ~loc:e.loc
                        ("no method " ^ mname ^ " in actor(" ^ cls ^ ")")
                  | Some sc ->
                      (match repr (Types.instantiate sc) with
                       | TFun (param_tys, _ret_ty) ->
                           if List.length param_tys <> List.length arg_tys then
                             Types.type_error ~loc:e.loc "arity mismatch in future send";
                           List.iter2 (Types.unify ~loc:e.loc) param_tys arg_tys;
                           (* ★ 戻り値はスキーム側（量化で切れている）ではなく
                              ρ 表から取る。これが reply 地点と繋がっている唯一の経路。 *)
                           record_now_edge cls mname;
                           Types.add_sent cls mname;
                           method_ret_ty cls mname
                       | ty ->
                           Types.type_error ~loc:e.loc
                             ("method " ^ mname ^ " is not a function: "
                              ^ string_of_ty ty)))
             | t_non_actor ->
                 Types.type_error ~loc:e.loc
                   ("future target is not actor: " ^ string_of_ty t_non_actor))
        end
      in
      (* ★ 呼ばれる側の効果キーを future の型に載せる。
         await の地点で、now と同じ辺を張るために使う。 *)
      TFuture (ret, ref !pending_future_callee)
  | NowSend (target, mname, args, dl) ->
      (* now は future の即時 await。戻り値型も同じ ρ になる。
         ★ 待つので、呼ばれる側の効果を引き継ぐ辺を張る。 *)
      let saved = !in_now_send in
      in_now_send := true;
      let r =
        (match repr (infer_expr env { e with desc = FutureSend (target, mname, args) }) with
         | TFuture (t, _) -> t
         | _              -> TAny)
      in
      in_now_send := saved;
      check_deadline env e.loc "now" r dl;
      (* else を書かなければ result<τ>。成功したかどうかを型で持つ。 *)
      (match dl with Some (_, None) -> Types.TResult r | _ -> r)
  | Await (e1, dl) ->
      let r =
        (match repr (infer_expr env e1) with
         | TFuture (t, ks) ->
             (* ★ 待つ側は、呼ばれる側の効果を負う。now と同じ規律。
                これを書くまで、now を future+await に分けると効果検査を逃れていた。 *)
             if !current_key <> "" then
               SSet.iter (fun k -> Types.add_now_edge !current_key k) !ks;
             t
         | TAny -> TAny
         | t -> Types.type_error ~loc:e.loc
                  ("await expected future, got " ^ string_of_ty_pretty t))
      in
      check_deadline env e.loc "await" r dl;
      (match dl with Some (_, None) -> Types.TResult r | _ -> r)

  | Array (elems, _) ->
    begin match elems with
    | [] -> TArray TUnit
    | e1 :: rest ->
        let t1 = infer_expr env e1 in
        List.iter (fun e -> unify ~loc:e.loc (infer_expr env e) t1) rest;
        TArray t1
    end
    
(* 期限節の検査。
   else 節は本体と同じ型でなければならない ---- 期限切れでも
   式全体の型は変わらないため。
   期限が無い場合は、無期限に待つのでデッドロックの余地が残る。
   AIOS_STRICT_DEADLINE=1 でエラー、既定は警告。 *)
and check_deadline (env:env) (loc:Location.t) (kind:string)
                   (rty:ty) (dl:(int * Ast.expr option) option) : unit =
  match dl with
  (* else を書かない形。式全体の型は result<τ> になるので、
     ここで照合する相手が無い。期限が正であることだけ見る。 *)
  | Some (ms, None) ->
      if ms <= 0 then
        Types.type_error ~loc (kind ^ ": timeout must be positive")
  | Some (ms, Some alt) ->
      if ms <= 0 then
        Types.type_error ~loc (kind ^ ": timeout must be positive");
      let ta = infer_expr ?expected:(expected_of rty) env alt in
      (try Types.unify ~loc rty ta
       with Types.Type_error (_, _) ->
         Types.type_error ~loc
           (Printf.sprintf
              "%s: the else branch has type %s but the call returns %s"
              kind (Types.string_of_ty_pretty (repr ta))
              (Types.string_of_ty_pretty (repr rty))))
  | None ->
      let msg =
        Printf.sprintf
          "%s without a deadline waits forever; write `%s ... timeout <ms> else <expr>`"
          kind kind
      in
      if !strict_deadline then Types.type_error ~loc msg
      else Printf.eprintf "[warn] %s: %s\n%!" (Location.to_string loc) msg

let set (e:env) (name:string) (sch:scheme) =
  Hashtbl.replace e name [sch]

let rec check_stmt (env:env) (s:stmt) : unit =
  match s.sdesc with
  | Assign (x, e) ->
    (* ★ フィールドへの代入だけが mut。ローカル変数は効果ではない *)
    if Hashtbl.mem current_fields x then add_eff ["mut"];
    let t_rhs = infer_expr env e in
    (match Hashtbl.find_opt env x with
     | None ->
         (* ★ 未宣言の名前への代入。読み出しは unbound variable で弾いているのに、
            代入だけ黙って新しい変数を作っていた。
            フィールド名を打ち間違えると、フィールドは更新されないまま
            別の変数ができて、何のエラーも出ない。
            AIOS_LAX_ASSIGN=1 で従来の暗黙宣言に戻せる。 *)
         if not (lax_assign ()) then
           raise (Type_error (s.sloc,
             "assignment to undeclared name: " ^ x
             ^ " (write `var " ^ x ^ " = ...` to declare it)"));
         let sch = Types.generalize (ftv_env env) t_rhs in
         set_var_scheme env x sch
     | Some [sch] ->
         let t_old = instantiate sch in
         ignore(unify_at s.sloc t_old t_rhs);
         let sch' = Types.generalize (ftv_env env) t_rhs in
	 				(* 代入後の型を更新（単相にしたいなら Forall([], t_rhs)）*)
         set_var_scheme env x sch'
     | Some _ ->
         raise (Type_error (s.sloc,("cannot assign to overloaded name: " ^ x))));
    ()
  | VarDecl (name, rhs) ->
      let t   = infer_expr env rhs in
      let sch = Types.generalize (ftv_env env) t in
      (* 単一束縛として“置き換え” *)
        set_var_scheme env name sch;
        ()
  | If (cond, tbr, fbr) ->
      let tc = infer_expr env cond in
      ignore(unify_at s.sloc tc TBool);
      check_stmt env tbr; check_stmt env fbr
  | While (cond, body) ->
      let tc = infer_expr env cond in ignore(unify_at s.sloc tc TBool);
      check_stmt env body
  | Seq ss -> List.iter (check_stmt env) ss
  | CallStmt ("reply", args) ->
      ignore (check_reply env s.sloc args);
      ()
  | CallStmt (fname, args) ->
      let arg_tys = List.map (infer_expr env) args in
      ignore (pick_overload s.sloc fname env arg_tys);
      ()
  | Become (cls, args) ->
      add_eff ["mut"];                   (* ★ 振る舞いの置換は状態変更 *)
      (* ★ 置換後のクラスは、置換前が受け取れたメッセージをすべて受け取れなければ
         ならない。そうでないと、外から見た型 actor(C) が嘘になる ----
         型検査は通るのに、become のあとで「そのメソッドは無い」が起きる。
         Akka Typed が Behavior[T] の T を固定しているのと同じ制限で、
         これを入れて初めて no_method_not_understood が become を含む
         プログラムでも成り立つ。AIOS_LAX_BECOME=1 で従来どおりにできる。 *)
      let old_cls = current_class_name () in
      if old_cls <> "" && old_cls <> cls && not (lax_become ()) then begin
        let names t = List.map fst t in
        let before = names (Types.lookup_class_methods_inst old_cls) in
        let after  = names (Types.lookup_class_methods_inst cls) in
        let missing = List.filter (fun m -> not (List.mem m after)) before in
        let missing = List.filter (fun m -> m <> "init") missing in
        if missing <> [] then
          raise (Type_error (s.sloc,
            Printf.sprintf
              "become %s: %s does not accept %s, which %s accepts"
              cls cls (String.concat ", " missing) old_cls))
      end;
      let _ = Types.lookup_class_methods_inst cls in
      let targs = List.map (infer_expr env) args in
      (match Types.lookup_class_method_scheme cls "init" with
       | Some sch ->
           (match Types.instantiate sch with
            | Types.TFun (params, _ret) ->
                (try List.iter2 (Types.unify ~loc:s.sloc) params targs
                 with Invalid_argument _ ->
                   raise (Type_error (s.sloc,
                     Printf.sprintf "become %s: arity mismatch" cls)))
            | ty ->
                raise (Type_error (s.sloc,
                  Printf.sprintf "become %s: init is not a function: %s"
                    cls (Types.string_of_ty_pretty ty))))
       | None -> ());
      ()
  | Send (target, mname, args) ->
    if !in_preinfer then begin
      (* ★ 1パス目（preinfer） *)
      begin match target with
      | LocalTarget vname ->
          (* ローカル actor だけ従来どおり軽く見る *)
          ignore (infer_expr env (mk_var vname))
      | RemoteTarget (_hostport, _actor_name) ->
          (* リモート宛先は actor 型を静的に見ない *)
          ()
      end;
      List.iter (fun e -> ignore (infer_expr env e)) args;
    end else begin
      (* ★ 2パス目（本番の型チェック） *)
      match target with
      | RemoteTarget (_hostport, _actor_name) ->
          (* リモート送信は送り先の actor 型・メソッド存在を静的にチェックしない *)
          List.iter (fun e -> ignore (infer_expr env e)) args
      | LocalTarget vname ->
          if vname = "sender" then begin
            (* sender は動的なので、引数だけ型推論 *)
            List.iter (fun e -> ignore (infer_expr env e)) args
          end else if vname = "self" then begin
            (* self もローカル actor として扱う。
               既存実装で self を infer_expr env (mk_var "self") できるならそのままでよい *)
            let t_actor = infer_expr env (mk_var vname) in
            match repr t_actor with
            | TActor (cls, _) ->
                (match Types.lookup_class_method_scheme cls mname with
                 | None ->
                     raise (Type_error (s.sloc,
                       ("no method " ^ mname ^ " in actor(" ^ cls ^ ")")))
                 | Some sc ->
                     let tf = repr (Types.instantiate sc) in
                     match tf with
                     | TFun (param_tys, _ret_ty) ->
                         let actuals =
                           List.map (fun e -> repr (infer_expr env e)) args in
                         if List.length param_tys <> List.length actuals then
                           raise (Type_error (s.sloc, "arity mismatch in send"));
                         List.iter2 (Types.unify ~loc:s.sloc) param_tys actuals;
                         Types.add_sent cls mname;
                         (* AIOS_SEND_EFFECTS=1 のとき、send も呼ばれる側の効果を負う。
                            既定は off（送るだけで待たないので負わない）。
                            Py-I / JS-I は既定で負う側なので、ここは仕様の判断待ち。 *)
                         if send_effects () && !current_key <> "" then
                           Types.add_now_edge !current_key (Types.eff_key cls mname)
                     | _ ->
                         raise (Type_error (s.sloc,
                           ("method " ^ mname ^ " is not a function: "
                            ^ string_of_ty tf))))
            | t_non_actor ->
                raise (Type_error (s.sloc,
                  ("send target is not actor: " ^ string_of_ty t_non_actor)))
          end else begin
            (* 通常のローカル send *)
            let t_actor = infer_expr env (mk_var vname) in
            match repr t_actor with
            | TActor (cls, _) ->
                (match Types.lookup_class_method_scheme cls mname with
                 | None ->
                     raise (Type_error (s.sloc,
                       ("no method " ^ mname ^ " in actor(" ^ cls ^ ")")))
                 | Some sc ->
                     let tf = repr (Types.instantiate sc) in
                     match tf with
                     | TFun (param_tys, _ret_ty) ->
                         let actuals =
                           List.map (fun e -> repr (infer_expr env e)) args in
                         if List.length param_tys <> List.length actuals then
                           raise (Type_error (s.sloc, "arity mismatch in send"));
                         List.iter2 (Types.unify ~loc:s.sloc) param_tys actuals;
                         Types.add_sent cls mname;
                         (* AIOS_SEND_EFFECTS=1 のとき、send も呼ばれる側の効果を負う。
                            既定は off（送るだけで待たないので負わない）。
                            Py-I / JS-I は既定で負う側なので、ここは仕様の判断待ち。 *)
                         if send_effects () && !current_key <> "" then
                           Types.add_now_edge !current_key (Types.eff_key cls mname)
                     | _ ->
                         raise (Type_error (s.sloc,
                           ("method " ^ mname ^ " is not a function: "
                            ^ string_of_ty tf))))
            | t_non_actor ->
                raise (Type_error (s.sloc,
                  ("send target is not actor: " ^ string_of_ty t_non_actor)))
          end
    end
  | UnsafeSend (_target, _mname, args) -> List.iter (fun e -> ignore (infer_expr env e)) args
  | Select (cases, (to_ms_opt, to_body_opt)) ->
    (* timeout body *)
    (match (to_ms_opt, to_body_opt) with
     | (Some _, Some to_stmt) ->
         check_stmt env to_stmt
     | (None, None) ->
         (* ★ 期限の無い select は、来ないメッセージを永久に待ちうる。
            now / await と同じ扱いにする ---- 既定は警告、
            AIOS_STRICT_DEADLINE=1 でエラーに昇格。 *)
         let msg =
           "select without a timeout waits forever; write `timeout <ms> -> { ... }`" in
         if !strict_deadline then Types.type_error ~loc:s.sloc msg
         else Printf.eprintf "[warn] %s: %s\n%!" (Location.to_string s.sloc) msg
     | _ ->
         Types.type_error ~loc:s.sloc
           "select: timeout requires both milliseconds and a body");
    (* 検査中のクラス（self の型）。case の reply の帰属先を決めるのに使う *)
    let self_cls =
      match Hashtbl.find_opt env "self" with
      | Some (sch :: _) ->
          (match repr (Types.instantiate sch) with
           | TActor (cls, _) -> Some cls
           | _ -> None)
      | _ -> None
    in
    List.iter
      (fun (c:Ast.select_case) ->
        (* 誰かがこのメッセージを送っているかは、全部見終わってから照合する *)
        (match self_cls with
         | Some cls -> selected_msgs := (cls, c.Ast.pat.Ast.meth, s.sloc) :: !selected_msgs
         | None -> ());
        let env' : Typing_env.env = Hashtbl.copy env in
        (* ★ case パターンを、受け取るメッセージ（= 同じクラスのメソッド）の
           シグネチャに照合する。arity と引数型をここで検査しないと、
           case m(x) が method m(a,b) を受けても素通りしてしまう。 *)
        let param_tys =
          match self_cls with
          | None -> None
          | Some cls ->
              (match Types.lookup_class_method_scheme cls c.pat.meth with
               | None ->
                   Types.type_error ~loc:c.body.Ast.sloc
                     ("select: no method " ^ c.pat.meth ^ " in actor(" ^ cls ^ ")")
               | Some sc ->
                   (match repr (Types.instantiate sc) with
                    | TFun (ps, _) ->
                        if List.length ps <> List.length c.pat.vars then
                          Types.type_error ~loc:c.body.Ast.sloc
                            (Printf.sprintf
                               "select: case %s binds %d variable(s) but method %s takes %d"
                               c.pat.meth (List.length c.pat.vars)
                               c.pat.meth (List.length ps));
                        Some ps
                    | _ -> None))
        in
        (match param_tys with
         | Some ps ->
             (* パターン変数はメッセージの引数そのものなので、署名の型を持つ *)
             List.iter2
               (fun x t -> set_var_scheme env' x (Forall ([], t)))
               c.pat.vars ps
         | None ->
             List.iter
               (fun x ->
                 let tv = Types.fresh_tvar () in
                 Typing_env.add_mono env' x (TVar tv))
               c.pat.vars);
        (* ★ case 本体の reply は「選択されたメッセージ」に返る。
           eval_thread が case 実行の前に set_current_msg_id を差し替えるので、
           reply の型は囲むメソッドではなく c.pat.meth の rho に属する。 *)
        (match self_cls with
         | Some cls ->
             (match Types.lookup_method_ret cls c.pat.meth with
              | Some rho ->
                  set_var_scheme env' "reply" (Forall ([], TFun ([rho], TUnit)))
              | None -> ())
         | None -> ());
        (* case 本体も「ちょうど一度 reply」の対象。二重 reply は
           後から来た値が捨てられるだけなので静かに壊れる。 *)
        if max_replies c.body > 1 then
          Types.type_error ~loc:c.body.Ast.sloc
            (Printf.sprintf
               "select: case %s may reply more than once on some path"
               c.pat.meth);
        check_stmt env' c.body
      )
      cases
      
let check_decl (env:env) = function
  | Class c ->
    List.iter
      (fun (st:Ast.stmt) ->
	match st.sdesc with
        | VarDecl (name, init) ->
            let t   = infer_expr env init in
            let sch = Types.generalize (ftv_env env) t in
            (* ★ フィールドは「重ねる」のではなく「置き換える」。
               add だと別のクラスが同じ名前のフィールドを持ったときに
               多重定義になり、そのフィールドへの代入が
               「cannot assign to overloaded name」で弾かれていた。
               クラス本体はそのクラスのフィールドの下で検査するので、
               置き換えが正しい。実測: コーパス 652 本のうち
               119 本が同名フィールドを持つ 2 クラスを含んでいた。 *)
            set_var_scheme env name sch
        | _ -> ()
      ) c.fields;

      (* 2) メソッド名を「float^n -> unit」として env に先に登録 *)
      List.iter (fun m ->
        let param_count =
          try List.length (Obj.magic m.params : string list) with _ -> 0
        in
        let ft = TFun (List.init param_count (fun _ -> TFloat), TUnit) in
        add env m.mname (Forall ([], ft))
      ) c.methods;

      (* ★ このクラスのフィールド名を集める。代入が mut かどうかの判定に使う *)
      Hashtbl.reset current_fields;
      List.iter
        (fun (st:Ast.stmt) ->
          match st.sdesc with
          | VarDecl (name, _) -> Hashtbl.replace current_fields name ()
          | _ -> ())
        c.fields;

      (* 3) 本文は“ローカル環境”で検査：ローカル変数が外へ漏れない *)
      List.iter (fun m ->
        let env_m = clone env in
        (* ★ self をこのクラスのアクターとしてローカル環境に追加 *)
        set env_m "self" (Forall ([], TActor (c.Ast.cname, [])));

        (* ★ 本体の仮引数を、preinfer が作ったスキームの引数型に結線する。
           以前はここで fresh な型変数を振っていたため、本体が要求する型と
           呼び出し側が渡す型が別世界になっていた。実質「引数の型検査を
           していない」状態で、
             method m(a) : int { reply(a + 1); }   に   now c.m("hello")
           が素通りしていた。

           スキームの引数型変数は generalize されていない（preinfer で
           env_m に置かれているため ftv_env に入る）ので、instantiate しても
           そのまま残り、すべての送信地点と共有される。したがってここで
           束縛すれば、本体・呼び出し側の双方から同じ変数へ制約が集まる。 *)
        let fresh_params () =
          List.iter (fun p ->
            set env_m p (Forall ([], TVar (Types.fresh_tvar ())))
          ) m.params
        in
        (match Types.lookup_class_method_scheme c.Ast.cname m.mname with
         | Some sc ->
             (match repr (Types.instantiate sc) with
              | TFun (ps, _) when List.length ps = List.length m.params ->
                  List.iter2 (fun p t -> set env_m p (Forall ([], t))) m.params ps
              | _ -> fresh_params ())
         | None -> fresh_params ());

        (* 引数の型注釈 `method m(x: T)` を反映する。
           注釈が無い引数はこれまでどおり推論に任せる。
           注釈と推論が食い違えば、ここで単一化が失敗して型エラーになる。 *)
        (if List.length m.Ast.param_tys = List.length m.params then
           List.iter2 (fun p ty_opt ->
             match ty_opt with
             | None -> ()
             | Some declared ->
                 (match find_all env_m p with
                  | sch :: _ ->
                      let actual = Types.instantiate sch in
                      (try unify actual declared
                       with _ ->
                         failwith
                           (Printf.sprintf
                              "parameter %s of %s.%s is declared %s but used as %s"
                              p c.Ast.cname m.mname
                              (Types.string_of_ty declared)
                              (Types.string_of_ty (repr actual))))
                  | [] -> set env_m p (Forall ([], declared)))
           ) m.params m.Ast.param_tys);

        (* ★ reply をこのメソッド専用に単相で束縛し、
           グローバルの reply : forall a. a -> unit を隠す。
           これで body 中の reply(v) が ρ を単一化するようになる。 *)
        let rho =
          match Types.lookup_method_ret c.Ast.cname m.mname with
          | Some t -> t
          | None   -> TVar (Types.fresh_tvar ())   (* preinfer 未通過は従来どおり *)
        in
        set env_m "reply" (Forall ([], TFun ([rho], TUnit)));

        current_ret_declared := (m.ret <> None);
        (* ★ 効果はこのメソッド専用のセルに溜める *)
        current_key := Types.eff_key c.Ast.cname m.mname;
        current_eff := Types.eff_cell c.Ast.cname m.mname;
        check_stmt env_m m.body;
        current_key := "";
        current_eff := ref Types.SSet.empty;
        current_ret_declared := false;

        (* ★ reply の線形性（上界）。注釈の有無によらず、二重 reply は常に誤り。
           2 度目の resolve_future は、待ち手がすでに 1 度目の値を受け取った
           あとに来るので黙って捨てられる。型は付くが動かない典型。 *)
        if (not (stmt_uses_replyto m.body)) && max_replies m.body > 1 then
          Types.type_error ~loc:m.body.Ast.sloc
            (Printf.sprintf
               "method %s may reply more than once on some path; a method must reply at most once"
               m.mname);

        (* ★ 注釈があるメソッドにだけ課せる検査（下界）：
           unit 以外を宣言したなら、全実行パスで reply しなければならない。
           推論だけではこれを述べられない（照合先が無いため）。
           上の上界と合わせて「ちょうど一度」になる。 *)
        (match m.ret with
         | Some t ->
             (match repr t with
              | TUnit -> ()
              | _ ->
                  if (not (stmt_uses_replyto m.body))
                     && not (replies_on_all_paths m.body) then
                    Types.type_error ~loc:m.body.Ast.sloc
                      (Printf.sprintf
                         "method %s is declared to reply with %s, but some execution path does not reply"
                         m.mname (Types.string_of_ty_pretty t)))
         | None -> ())
	) c.methods
  | Global s ->                         
      check_stmt env s

let build_proto (m : Ast.method_decl) : string * Types.ty =
  let tvs = List.init (List.length m.Ast.params) (fun _ -> Types.fresh_tvar ()) in
  let ps  = List.map (fun a -> Types.TVar a) tvs in
  (* いまは戻り値を unit としておく。必要なら推論後に具体化する *)
  (m.Ast.mname, Types.TFun (ps, Types.TUnit))
  (* ↑ ↑ ↑ フィールド名は実際のレコード定義に合わせてください。
     これまでのコードでは m.Ast.mname / m.Ast.params でした。 *)

(* 例: クラス1つ分のメソッドを先に推論して (method_name * scheme) のリストにする *)
let infer_class_methods
    (gamma0 : Typing_env.env)          (* ここは (string, Types.scheme) Hashtbl.t のはず *)
    (cls_name : string)
    (methods : (string * expr) list    (* あるいはあなたの ast の method レコード型 *))
  : (string * Types.scheme) list =
  (* 1) このクラス専用の “項の型環境” を用意 *)
  let env_cls : Typing_env.env = Hashtbl.copy gamma0 in

  (* 2) 各メソッドを型推論し、関数型 t を得たら env から自由変数を集めて generalize *)
  let infer_one (mname, body_expr) =
    let t = infer_expr env_cls body_expr in   (* ←あなたの expr 用型付け関数名に合わせて *)
    let sc = Types.generalize (Types.ftv_env env_cls) t in
    (mname, sc)
  in
  List.map infer_one methods

(* グローバルの VarDecl から、New クラス名を拾って
   その変数を env に TActor(cls, []) として登録しておく *)
let prebind_global_actors (p : Ast.program) (env : env) : unit =
  let rec new_class_of_expr (e : expr) : string option =
    match e.desc with
    | New (cls, _args) -> Some cls
    | _ -> None
  in
  List.iter
    (function
      | Ast.Global s -> begin
        match s.Ast.sdesc with
        | Ast.VarDecl (name, rhs) ->
          (match new_class_of_expr rhs with
           | Some cls ->
               let t   = Types.TActor (cls, []) in
               let sch = Types.Forall ([], t) in
               set_var_scheme env name sch
           | None -> ())
        | _ -> ()
        end
      | _ -> ())
    p

let preinfer_all_classes (p : Ast.program) (g0 : Types.tenv) : unit =
  let infer_one_class (c : Ast.class_decl) : (string * Types.scheme) list =
    let env_cls = clone g0 in
      List.iter
        (fun (st:Ast.stmt) ->
          match st.Ast.sdesc with
          | Ast.VarDecl (name, rhs) ->
            let t = infer_expr env_cls rhs in
            let sch = generalize (ftv_env env_cls) t in
            set_var_scheme env_cls name sch
          | _ -> ()
        ) c.Ast.fields;
    let infer_method (m : Ast.method_decl) =
    let env_m = clone env_cls in
      set_var_scheme env_m "self"
      (Types.Forall ([], Types.TActor (c.Ast.cname, [])));
      (* 仮引数ごとに新しい型変数を割り当てて ps に入れる *)
    let ps =
      List.map
        (fun p ->
           let a  = Types.fresh_tvar () in
           let ty = Types.TVar a in
           set_var_scheme env_m p (Types.Forall ([], ty));
           ty)
        m.Ast.params
    in
      (* ★ 1パス目ではメソッド本体は見ない設計なので、check_stmt は呼ばない ★ *)
      (* check_stmt env_m m.Ast.body; *)

      (* ★ 戻り値型 ρ を1つ確保して表に登録する。
         2パス目で本体の reply がこの ρ を単一化し、
         送信地点は method_ret_ty 経由で同じ ρ を読む。 *)
      let rho = Types.TVar (Types.fresh_tvar ()) in
      Types.register_method_ret c.Ast.cname m.Ast.mname rho;

      (* ★ 注釈があればそれが正。以後 reply も送信地点もこの型に照合される。
         注釈が無い場合のみ推論に任せ、本体に reply が無ければ
         即 unit へ defaulting する（Pony 方式）。
         未束縛のまま残すと ∀ρ.ρ 相当になり、返らない now が型検査を通る。 *)
      (match m.Ast.ret with
       | Some t -> Types.unify ~loc:Location.dummy rho t
       | None ->
           if not (stmt_has_reply m.Ast.body) then
             Types.unify ~loc:Location.dummy rho Types.TUnit);

      (* ρ を env に置いて generalize から守る。
         ρ が量化されると instantiate が呼び出しごとに別変数へ差し替えてしまい、
         reply 側の制約が呼び出し側に届かなくなる。 *)
      set_var_scheme env_m "reply"
        (Types.Forall ([], Types.TFun ([rho], Types.TUnit)));

      (* ps の repr だけを見て関数型を作る *)
      let ps' = List.map Types.repr ps in
      let tfun = Types.TFun (ps', rho) in
      let sch  = generalize (ftv_env env_m) tfun in
        (m.Ast.mname, sch)
(*
let infer_method (m : Ast.method_decl) =
      let env_m = clone env_cls in
      set_var_scheme env_m "self" (Types.Forall ([], Types.TActor(c.Ast.cname,[])));
      let ps =
        List.map (fun p -> let a = Types.fresh_tvar () in
                           set_var_scheme env_m p (Types.Forall ([], Types.TVar a));
                           Types.TVar a) m.Ast.params
      in
      let ps' = List.map (fun p -> Types.repr (Types.instantiate (get_var_scheme_exn env_m p))) m.Ast.params in
      let tfun = Types.TFun (ps', Types.TUnit) in
      let sch  = generalize (ftv_env env_m) tfun in
      (m.Ast.mname, sch) *)
    in
    List.map infer_method c.Ast.methods
  in
    List.iter (function
    | Ast.Class c ->
        let sigs = infer_one_class c in
        Types.register_class_method_schemes c.Ast.cname sigs
    | _ -> ()
  ) p

(* ================================================================= *)
(*  リモート境界での戻り値型注釈の必須化                              *)
(* ================================================================= *)
(* AIOS_LAX_EXPOSE=1 で、公開アクターの注釈漏れをエラーではなく警告にする *)
let lax_expose =
  match Sys.getenv_opt "AIOS_LAX_EXPOSE" with
  | Some "1" | Some "true" | Some "yes" -> ref true
  | _ -> ref false

(* プログラム中のプリミティブ呼び出しを (名前, 引数, 位置) で全部拾う。
   web_listen / web_expose はメソッド本体の中から呼ばれることもあるので、
   グローバル文だけでなくクラス本体も走査する。 *)
let collect_prim_calls (p : Ast.program) : (string * Ast.expr list * Location.t) list =
  let acc = ref [] in
  let rec ex (e : Ast.expr) =
    match e.desc with
    | Ast.Call (f, args) ->
        acc := (f, args, e.loc) :: !acc; List.iter ex args
    | Ast.Binop (_, a, b) -> ex a; ex b
    | Ast.Expr e1 -> ex e1
    | Ast.Await (e1, d) -> ex e1; (match d with Some (_, Some a) -> ex a | _ -> ())
    | Ast.New (_, args) | Ast.Array (args, _)
    | Ast.FutureSend (_, _, args) -> List.iter ex args
    | Ast.NowSend (_, _, args, d) ->
        List.iter ex args; (match d with Some (_, Some a) -> ex a | _ -> ())
    | Ast.Int _ | Ast.Float _ | Ast.String _ | Ast.Bool _ | Ast.Var _ | Ast.ActorRef _ | Ast.ReplyRef _ -> ()
  and st (s : Ast.stmt) =
    match s.sdesc with
    | Ast.CallStmt (f, args) ->
        acc := (f, args, s.sloc) :: !acc; List.iter ex args
    | Ast.Send (_, _, args) | Ast.UnsafeSend (_, _, args)
    | Ast.Become (_, args) -> List.iter ex args
    | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> ex e
    | Ast.Seq ss -> List.iter st ss
    | Ast.If (c, a, b) -> ex c; st a; st b
    | Ast.While (c, b) -> ex c; st b
    | Ast.Select (cases, (_, to_body)) ->
        List.iter (fun (c : Ast.select_case) -> st c.body) cases;
        (match to_body with Some b -> st b | None -> ())
  in
  List.iter
    (function
      | Ast.Class c ->
          List.iter st c.Ast.fields;
          List.iter (fun (m : Ast.method_decl) -> st m.Ast.body) c.Ast.methods
      | Ast.Global s -> st s)
    p;
  List.rev !acc

(* 外から呼ばれうるアクターのメソッドには戻り値型注釈を要求する。

   境界を開くのは web_listen である。web_gateway の POST /api/send は
   to=<アクター名> で「任意のアクター」に到達するので、web_expose は
   公開エンドポイントの別名を付けるだけで、到達可能性を絞ってはいない。
   そこで 2 段階で報告する。

   - web_expose で名指しされたアクター
       プログラムが自ら「これが公開インタフェースだ」と宣言している。
       注釈漏れはエラー（AIOS_LAX_EXPOSE=1 で警告）。
   - web_listen があるとき、それ以外のアクター
       /api/send 経由で到達可能ではあるが、公開の意図があるとは限らない。
       警告にとどめる。

   リモート送信（RemoteTarget）の相手は別ノードにあり、本体がこの
   プログラムに無いので、ここでは検査できない。 *)
let check_boundary_annotations (p : Ast.program) (env : env) : unit =
  let calls = collect_prim_calls p in
  let has_listen = List.exists (fun (f, _, _) -> f = "web_listen") calls in
  let exposed_calls = List.filter (fun (f, _, _) -> f = "web_expose") calls in
  if has_listen || exposed_calls <> [] then begin
    (* クラス名 -> class_decl *)
    let classes : (string, Ast.class_decl) Hashtbl.t = Hashtbl.create 16 in
    List.iter
      (function Ast.Class c -> Hashtbl.replace classes c.Ast.cname c | _ -> ())
      p;
    let class_of_var (v : string) : string option =
      match Hashtbl.find_opt env v with
      | Some (sch :: _) ->
          (match repr (Types.instantiate sch) with
           | TActor (cls, _) -> Some cls
           | _ -> None)
      | _ -> None
    in
    (* init は生成時にしか呼ばれないので対象外 *)
    let unannotated (c : Ast.class_decl) : string list =
      c.Ast.methods
      |> List.filter (fun (m : Ast.method_decl) ->
             m.Ast.mname <> "init"
             && (match m.Ast.ret with None -> true | Some _ -> false))
      |> List.map (fun (m : Ast.method_decl) -> m.Ast.mname)
    in
    let describe cls ms =
      Printf.sprintf
        "actor %s is reachable from outside this program, but %s %s no return type annotation; \
         a remote caller cannot see the body, so the reply type has to be declared \
         (method %s(...) : T)"
        cls
        (String.concat ", " ms)
        (if List.length ms = 1 then "has" else "have")
        (List.hd ms)
    in
    (* --- web_expose で名指しされたアクター --- *)
    let exposed_classes = ref [] in
    List.iter
      (fun (_, args, loc) ->
        match args with
        | [_; { desc = Ast.String vname; _ }] ->
            (match class_of_var vname with
             | None ->
                 Printf.eprintf
                   "[warn] %s: web_expose(..., %S): %s is not a known actor variable, \
                    so its return annotations cannot be checked\n%!"
                   (Location.to_string loc) vname vname
             | Some cls ->
                 exposed_classes := cls :: !exposed_classes;
                 (match Hashtbl.find_opt classes cls with
                  | None -> ()
                  | Some c ->
                      (match unannotated c with
                       | [] -> ()
                       | ms ->
                           let msg = describe cls ms in
                           if !lax_expose then
                             Printf.eprintf "[warn] %s: %s\n%!"
                               (Location.to_string loc) msg
                           else Types.type_error ~loc msg)))
        | _ ->
            Printf.eprintf
              "[warn] %s: web_expose with non-literal arguments: \
               return annotations cannot be checked statically\n%!"
              (Location.to_string loc))
      exposed_calls;
    (* --- web_listen があるとき、名指しされていないアクター --- *)
    if has_listen then
      Hashtbl.iter
        (fun cls (c : Ast.class_decl) ->
          if not (List.mem cls !exposed_classes) then
            match unannotated c with
            | [] -> ()
            | ms ->
                Printf.eprintf
                  "[warn] web_listen is called, so POST /api/send can reach any actor by name: %s\n%!"
                  (describe cls ms))
        classes
  end

(* 宣言された効果と、本体から集めた（そして now で伝播した）効果を照合する。
   注釈が無いメソッドは推論に任せる ---- 戻り値型と同じ gradual な扱い。 *)

(* ============================================================ *)
(*  資源の使用順序の検査（小林の資源使用解析のいちばん素朴な形）  *)
(* ============================================================ *)
(* 効果は集合なので「取得したら解放する」という順序を表せない。
   そこで acquire("r") / release("r") の対を、メソッド本体の中で
   構文的に追う。規律は三つ:
     1. メソッドを抜けるとき、持っている資源が残っていてはならない
     2. 持っていない資源を release してはならない
     3. 二重に acquire してはならない
   if の二つの枝は、抜けたときに同じ集合を持っていなければならない。
   while の本体は、入る前と出た後で持ち物が変わってはならない
   （0回でも n 回でも同じにするため）。
   これはメソッド内で閉じた検査で、メソッドをまたぐ受け渡しは見ない。 *)

exception Res_error of Location.t * string

(* ---- 資源への全体順序 --------------------------------------
   対の検査は「取ったら返す」までしか見ない。
   二つのアクターが同じ二つの資源を逆の順序で取ると、
   どちらも対は正しいのに、実行するとお互いを待つ。
   そこで、取得の入れ子から辺を集める ----
   r を持っているあいだに s を取ったなら r < s。
   集めた辺に閉路があれば、逆順に取る場所が二つ以上あるということである。
   閉路が無ければ、それは全体順序を作れるということ ----
   位相順序がそのまま「レベル」の証人になる（§義務レベルと同じ形）。 *)

(* (下位, 上位) -> (どこで入れ子になったか) *)
let res_edges : (string * string, string * Location.t) Hashtbl.t = Hashtbl.create 16
(* いま歩いている場所の名前（エラーに出す） *)
let res_site : string ref = ref "top level"
(* 追えない acquire（引数が文字列リテラルでない）を見つけた場所 *)
let res_opaque : (Location.t * string) list ref = ref []

let rec res_of_expr (e : Ast.expr) (held : SSet.t) : SSet.t =
  match e.desc with
  | Ast.Call ("acquire", [{ Ast.desc = Ast.String r; _ }]) ->
      if SSet.mem r held then
        raise (Res_error (e.loc, Printf.sprintf "resource %s is acquired twice" r));
      (* すでに持っているものは、これより先に取られた＝下位である *)
      SSet.iter (fun h ->
        if h <> r && not (Hashtbl.mem res_edges (h, r)) then
          Hashtbl.replace res_edges (h, r) (!res_site, e.loc)) held;
      SSet.add r held
  | Ast.Call ("acquire", [arg]) ->
      (* 資源の名前が実行時に決まる形は追えない。黙って通すが、覚えておく。 *)
      res_opaque := (e.loc, !res_site) :: !res_opaque;
      res_of_expr arg held
  | Ast.Call ("release", [{ Ast.desc = Ast.String r; _ }]) ->
      if not (SSet.mem r held) then
        raise (Res_error (e.loc,
          Printf.sprintf "resource %s is released without being acquired" r));
      SSet.remove r held
  | Ast.Call (_, args) | Ast.New (_, args) | Ast.FutureSend (_, _, args) ->
      List.fold_left (fun h a -> res_of_expr a h) held args
  | Ast.NowSend (_, _, args, d) ->
      let h = List.fold_left (fun h a -> res_of_expr a h) held args in
      (match d with Some (_, Some alt) -> res_of_expr alt h | _ -> h)
  | Ast.Await (e1, d) ->
      let h = res_of_expr e1 held in
      (match d with Some (_, Some alt) -> res_of_expr alt h | _ -> h)
  | Ast.Binop (_, a, b) -> res_of_expr b (res_of_expr a held)
  | Ast.Expr e1 -> res_of_expr e1 held
  | _ -> held

let rec res_of_stmt (s : Ast.stmt) (held : SSet.t) : SSet.t =
  match s.sdesc with
  | Ast.Seq ss -> List.fold_left (fun h st -> res_of_stmt st h) held ss
  | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> res_of_expr e held
  | Ast.CallStmt (f, args) ->
      res_of_expr { Ast.desc = Ast.Call (f, args); loc = s.sloc } held
  | Ast.Send (_, _, args) | Ast.UnsafeSend (_, _, args) | Ast.Become (_, args) ->
      List.fold_left (fun h a -> res_of_expr a h) held args
  | Ast.If (c, a, b) ->
      let h = res_of_expr c held in
      let ha = res_of_stmt a h and hb = res_of_stmt b h in
      if not (SSet.equal ha hb) then begin
        let d = SSet.union (SSet.diff ha hb) (SSet.diff hb ha) in
        raise (Res_error (s.sloc,
          Printf.sprintf
            "the two branches disagree on which resources are held (%s)"
            (String.concat ", " (SSet.elements d))))
      end;
      ha
  | Ast.While (c, b) ->
      let h = res_of_expr c held in
      let hb = res_of_stmt b h in
      if not (SSet.equal h hb) then
        raise (Res_error (s.sloc,
          "the loop body must leave the same resources held as it found"));
      h
  | Ast.Select (cases, (_, to_body)) ->
      List.iter (fun (c : Ast.select_case) ->
        let hb = res_of_stmt c.Ast.body held in
        if not (SSet.equal hb held) then
          raise (Res_error (s.sloc,
            "a select case must leave the same resources held as it found"))) cases;
      (match to_body with
       | Some b ->
           let hb = res_of_stmt b held in
           if not (SSet.equal hb held) then
             raise (Res_error (s.sloc,
               "the timeout body must leave the same resources held as it found"));
           held
       | None -> held)

let check_resource_use (cls : string) (m : Ast.method_decl) : unit =
  res_site := cls ^ "." ^ m.Ast.mname;
  let left = res_of_stmt m.Ast.body SSet.empty in
  if not (SSet.is_empty left) then
    raise (Res_error (m.Ast.body.Ast.sloc,
      Printf.sprintf "method %s.%s returns while still holding %s"
        cls m.Ast.mname (String.concat ", " (SSet.elements left))))

(* "a -> b -> c" を [("a","b"); ("b","c")] にする *)
let parse_res_order (spec : string) : (string * string) list =
  let parts =
    let n = String.length spec in
    let rec go i start acc =
      if i + 1 < n && spec.[i] = '-' && spec.[i+1] = '>' then
        go (i+2) (i+2) (String.sub spec start (i-start) :: acc)
      else if i >= n then List.rev (String.sub spec start (n-start) :: acc)
      else go (i+1) start acc
    in go 0 0 []
  in
  let names = List.filter (fun x -> x <> "") (List.map String.trim parts) in
  let rec pairs = function
    | a :: (b :: _ as rest) -> (a, b) :: pairs rest
    | _ -> [] in
  pairs names

(* 閉路を一つ返す。[a; b; c] なら a -> b -> c -> a *)
let res_cycle () : string list option =
  let succ : (string, string list) Hashtbl.t = Hashtbl.create 16 in
  Hashtbl.iter (fun (a, b) _ ->
    Hashtbl.replace succ a (b :: (try Hashtbl.find succ a with Not_found -> [])))
    res_edges;
  let color : (string, int) Hashtbl.t = Hashtbl.create 16 in
  let found = ref None in
  let rec go n path =
    if !found <> None then () else
    match Hashtbl.find_opt color n with
    | Some 2 -> ()
    | Some _ ->
        (* n はいま辿っている道の上にある = 閉路 *)
        let rec take acc = function
          | [] -> List.rev acc
          | x :: rest -> if x = n then n :: acc else take (x :: acc) rest in
        found := Some (take [] path)
    | None ->
        Hashtbl.replace color n 1;
        List.iter (fun m -> go m (n :: path))
          (try Hashtbl.find succ n with Not_found -> []);
        Hashtbl.replace color n 2
  in
  Hashtbl.iter (fun (a, _) _ -> go a []) res_edges;
  !found

(* 閉路が無いなら、位相の高さがそのまま全体順序になる（証人） *)
let res_levels () : (string * int) list =
  let succ : (string, string list) Hashtbl.t = Hashtbl.create 16 in
  let nodes = Hashtbl.create 16 in
  Hashtbl.iter (fun (a, b) _ ->
    Hashtbl.replace nodes a (); Hashtbl.replace nodes b ();
    Hashtbl.replace succ a (b :: (try Hashtbl.find succ a with Not_found -> [])))
    res_edges;
  let lv = Hashtbl.create 16 in
  let rec depth n =
    match Hashtbl.find_opt lv n with
    | Some d -> d
    | None ->
        Hashtbl.replace lv n 0;                     (* 閉路よけの仮置き *)
        let d =
          List.fold_left (fun acc m -> max acc (1 + depth m)) 0
            (try Hashtbl.find succ n with Not_found -> []) in
        Hashtbl.replace lv n d; d
  in
  Hashtbl.iter (fun n () -> ignore (depth n)) nodes;
  (* 高さが大きいほど「先に取る」= 下位。見やすいように逆にして 0 から振る *)
  let mx = Hashtbl.fold (fun _ d a -> max a d) lv 0 in
  let items = Hashtbl.fold (fun n d acc -> (n, mx - d) :: acc) lv [] in
  List.sort (fun (na, a) (nb, b) ->
    if a <> b then compare a b else compare na nb) items

(* 宣言 resource_order("a -> b -> c") を辺として取り込み、
   集めた辺と合わせて閉路が無いことを見る。 *)
let check_resource_order (p : Ast.program) : unit =
  (* 1) 宣言された順序 *)
  List.iter (function
    | Ast.Global ({ Ast.sdesc =
          Ast.CallStmt ("resource_order", [ { Ast.desc = Ast.String spec; _ } ]); _ } as st)
    | Ast.Global ({ Ast.sdesc =
          Ast.VarDecl (_, { Ast.desc =
            Ast.Call ("resource_order", [ { Ast.desc = Ast.String spec; _ } ]); _ }); _ } as st) ->
        List.iter (fun (a, b) ->
          if not (Hashtbl.mem res_edges (a, b)) then
            Hashtbl.replace res_edges (a, b) ("resource_order", st.Ast.sloc))
          (parse_res_order spec)
    | _ -> ()) p;
  (* 2) 閉路 = 逆順に取る場所がある *)
  (match res_cycle () with
   | Some (n :: _ as cyc) ->
       let rec edges = function
         | a :: (b :: _ as rest) -> (a, b) :: edges rest
         | [last] -> [(last, n)]
         | [] -> [] in
       let es = edges cyc in
       let where =
         String.concat "; "
           (List.map (fun (a, b) ->
              match Hashtbl.find_opt res_edges (a, b) with
              | Some (site, _) -> Printf.sprintf "%s before %s (in %s)" a b site
              | None -> Printf.sprintf "%s before %s" a b) es) in
       let loc =
         match Hashtbl.find_opt res_edges (List.hd es) with
         | Some (_, l) -> l | None -> Location.dummy in
       Types.type_error ~loc
         (Printf.sprintf
            "resource order: %s -> %s is circular; %s. Acquiring in opposite orders deadlocks"
            (String.concat " -> " cyc) n where)
   | _ -> ());
  (* 3) 追えなかった acquire を知らせる（既定では黙る） *)
  if Sys.getenv_opt "AIOS_STRICT_RESOURCE" = Some "1" then
    List.iter (fun (loc, site) ->
      Printf.eprintf
        "[warn] %s: acquire with a name that is not a literal, in %s; its order is not checked\n%!"
        (Location.to_string loc) site) (List.rev !res_opaque);
  (* 4) 推論した全体順序を見せる *)
  if Sys.getenv_opt "AIOS_SHOW_LEVELS" = Some "1" then
    List.iter (fun (n, d) -> Printf.eprintf "[resource] %-20s @%d\n%!" n d)
      (res_levels ())


(* ============================================================ *)
(*  返信先の線形性（reply<τ> をちょうど一度だけ使う）            *)
(* ============================================================ *)
(* replyto で取り出した返信先は義務である。
   ちょうど一度 answer するか、他のアクターへ渡して義務を移さなければならない。
   ABCL/1 は返信先を一級の値にしたが、回数を守る手立てが無かった。
   ここでは線形に扱うことで、委譲を許しながら「ちょうど一度」を保つ。

   規律（メソッド内で閉じた検査）:
     1. `var r = replyto;` で義務が生まれる
     2. `answer(r, v)` か、送信の引数に r を渡すと義務が消える
     3. 同じ r を二度使ってはならない
     4. メソッドを抜けるとき義務が残っていてはならない
     5. if の二つの枝は同じ状態で合流する
   `send b.m(replyto)` のように、その場で作ってその場で渡す形は差引ゼロ。 *)

(* 状態は (owed, spent)。owed はまだ答えていない返信先、
   spent は既に使った返信先。spent をもう一度使ったらエラーにする
   （消すだけだと、二度渡しがただの変数参照に見えて素通りする）。 *)
let rec rep_of_expr (e : Ast.expr) ((owed, spent) : SSet.t * SSet.t) : SSet.t * SSet.t =
  match e.desc with
  (* answer(r, v)：r が変数なら義務を消す *)
  | Ast.Call ("answer", ({ Ast.desc = Ast.Var r; _ } :: rest)) when r <> "replyto" ->
      if SSet.mem r spent then
        raise (Res_error (e.loc,
          Printf.sprintf "reply destination %s is used twice" r));
      if not (SSet.mem r owed) then
        raise (Res_error (e.loc,
          Printf.sprintf "reply destination %s was never taken from replyto" r));
      List.fold_left (fun h a -> rep_of_expr a h)
        (SSet.remove r owed, SSet.add r spent) rest
  | Ast.Call (_, args) | Ast.New (_, args) ->
      List.fold_left (fun h a -> rep_of_expr a h) (owed, spent) args
  (* 送信の引数に返信先の変数を渡すと、義務は相手へ移る *)
  | Ast.FutureSend (_, _, args) | Ast.NowSend (_, _, args, _) ->
      List.fold_left (fun h a -> consume_arg e.loc a h) (owed, spent) args
  | Ast.Await (e1, _) -> rep_of_expr e1 (owed, spent)
  | Ast.Binop (_, a, b) -> rep_of_expr b (rep_of_expr a (owed, spent))
  | Ast.Expr e1 -> rep_of_expr e1 (owed, spent)
  | _ -> (owed, spent)

and consume_arg (loc : Location.t) (a : Ast.expr)
                ((owed, spent) : SSet.t * SSet.t) : SSet.t * SSet.t =
  match a.desc with
  | Ast.Var r when SSet.mem r spent ->
      raise (Res_error (loc,
        Printf.sprintf "reply destination %s is used twice" r))
  | Ast.Var r when SSet.mem r owed -> (SSet.remove r owed, SSet.add r spent)
  | _ -> rep_of_expr a (owed, spent)

let rec rep_of_stmt (s : Ast.stmt) ((owed, spent) : SSet.t * SSet.t) : SSet.t * SSet.t =
  match s.sdesc with
  | Ast.Seq ss -> List.fold_left (fun h st -> rep_of_stmt st h) (owed, spent) ss
  (* var r = replyto;  ---- 義務が生まれる *)
  | Ast.VarDecl (x, { Ast.desc = Ast.Var "replyto"; _ }) -> (SSet.add x owed, spent)
  | Ast.Assign (_, e) | Ast.VarDecl (_, e) -> rep_of_expr e (owed, spent)
  | Ast.CallStmt (f, args) ->
      rep_of_expr { Ast.desc = Ast.Call (f, args); loc = s.sloc } (owed, spent)
  | Ast.Send (_, _, args) | Ast.UnsafeSend (_, _, args) ->
      List.fold_left (fun h a -> consume_arg s.sloc a h) (owed, spent) args
  | Ast.Become (_, args) ->
      List.fold_left (fun h a -> rep_of_expr a h) (owed, spent) args
  | Ast.If (c, a, b) ->
      let h = rep_of_expr c (owed, spent) in
      let ha = rep_of_stmt a h and hb = rep_of_stmt b h in
      if not (SSet.equal (fst ha) (fst hb)) then
        raise (Res_error (s.sloc,
          "the two branches disagree on which reply destinations are still owed"));
      ha
  | Ast.While (c, b) ->
      let h = rep_of_expr c (owed, spent) in
      let hb = rep_of_stmt b h in
      if not (SSet.equal (fst h) (fst hb)) then
        raise (Res_error (s.sloc,
          "the loop body must leave the same reply destinations owed as it found"));
      h
  | Ast.Select (cases, (_, to_body)) ->
      List.iter (fun (c : Ast.select_case) ->
        if not (SSet.equal (fst (rep_of_stmt c.Ast.body (owed, spent))) owed) then
          raise (Res_error (s.sloc,
            "a select case must leave the same reply destinations owed"))) cases;
      (match to_body with
       | Some b ->
           if not (SSet.equal (fst (rep_of_stmt b (owed, spent))) owed) then
             raise (Res_error (s.sloc,
               "the timeout body must leave the same reply destinations owed"));
           (owed, spent)
       | None -> (owed, spent))

let check_reply_linearity (cls : string) (m : Ast.method_decl) : unit =
  (* 引数で受け取った返信先も義務である（reply 注釈の付いた引数） *)
  let start =
    List.fold_left2
      (fun acc p t ->
        match t with Some (Types.TReply _) -> SSet.add p acc | _ -> acc)
      SSet.empty m.Ast.params
      (if List.length m.Ast.param_tys = List.length m.Ast.params
       then m.Ast.param_tys
       else List.map (fun _ -> None) m.Ast.params)
  in
  let (left, _) = rep_of_stmt m.Ast.body (start, SSet.empty) in
  if not (SSet.is_empty left) then
    raise (Res_error (m.Ast.body.Ast.sloc,
      Printf.sprintf "method %s.%s returns without answering %s"
        cls m.Ast.mname (String.concat ", " (SSet.elements left))))


(* ============================================================ *)
(*  セッション型 ---- プロトコルを静的に検査する                *)
(* ============================================================ *)
(* AIPL には既に実行時のセッションプロトコルがある
   （protocol_define / protocol_start / protocol_end、Coq で検証済み）。
   ここではそれを型検査の側へ持ち上げる ----
   同じ宣言を読み、送信の順序が約束どおりかを走らせる前に見る。

   対象は「protocol_start と protocol_end が同じ文の並びにある」場合に限る。
   セッションがアクターをまたぐ場合は実行時の検査に任せる。
   ここで見るのは「書き間違い」---- 順序を取り違えた、一段飛ばした、
   終える前に抜けた、という形である。 *)

(* "a.m -> b.n -> c.p" を [("a","m"); ("b","n"); ("c","p")] にする *)
let parse_protocol_spec (spec : string) : (string * string) list =
  let parts =
    let n = String.length spec in
    let rec go i start acc =
      if i + 1 < n && spec.[i] = '-' && spec.[i+1] = '>' then
        go (i+2) (i+2) (String.sub spec start (i-start) :: acc)
      else if i >= n then List.rev (String.sub spec start (n-start) :: acc)
      else go (i+1) start acc
    in go 0 0 []
  in
  List.filter_map (fun p ->
    let p = String.trim p in
    match String.index_opt p '.' with
    | Some i ->
        Some (String.sub p 0 i,
              String.sub p (i+1) (String.length p - i - 1))
    | None -> None) parts

(* ---- 宛先の解決表 --------------------------------------------
   手順は "main_thread.run" のようにアクターの変数名で書かれるが、
   送信は aios_now("main", "run", ...) のようにサービス名で書かれる。
   両者は aios_register_service("main", "main_thread") で結ばれている。
   同じことをクラスの解決にも行う ---- var planner = new PlannerActor(); *)
let proto_svc_actor : (string, string) Hashtbl.t = Hashtbl.create 16
let proto_var_class : (string, string) Hashtbl.t = Hashtbl.create 16
let proto_field_class : (string * string, string) Hashtbl.t = Hashtbl.create 32
let proto_methods : (string * string, Ast.method_decl) Hashtbl.t = Hashtbl.create 32
(* 全プロトコルの手順の和集合。非同期の呼び先が手順を含むかの判定に使う *)
let proto_steps : (string * string) list ref = ref []
(* 非同期の呼び先が手順を含んでいた = 静的に順序を決められない *)
let proto_unsequenced = ref false

let resolve_actor (a : string) : string =
  match Hashtbl.find_opt proto_svc_actor a with Some x -> x | None -> a

(* いま歩いているメソッドが引数で受け取ったアクター（名前 -> クラス）。
   method run(f: Fetch, ...) の f は、呼び出し側の実体を指す。 *)
let proto_params : (string, string) Hashtbl.t = Hashtbl.create 8

let class_of_actor (cls : string option) (a : string) : string option =
  match Hashtbl.find_opt proto_params a with
  | Some c -> Some c
  | None ->
      (match cls with
       | Some c when Hashtbl.mem proto_field_class (c, a) ->
           Hashtbl.find_opt proto_field_class (c, a)
       | _ -> Hashtbl.find_opt proto_var_class a)

(* 文の並びから、送信を (宛先アクター, メソッド) の順に取り出す。

   ここが「振る舞い展開」である。
   同期の送信（now / aios_now）は、呼び先の本体が呼び出し側の続きより
   先に走り切るので、その送信列を\textbf{その場に差し込む}ことができる。
   これでセッションがアクターをまたいでも、送信の順序が一本に並ぶ。

   非同期（send / future）は差し込まない ---- いつ走るか決まらないからである。
   呼び先が手順を含んでいた場合は、その並びは静的に追えないと印を付け、
   完了検査を実行時に任せる。 *)
let rec sends_of_stmt (vis : (string * string) list) (cls : string option)
                      (st : Ast.stmt) : (string * string) list =
  let go = sends_of_stmt vis cls and goe = sends_of_expr vis cls in
  match st.Ast.sdesc with
  | Ast.Seq ss -> List.concat_map go ss
  | Ast.Send (Ast.LocalTarget t, m, args) | Ast.UnsafeSend (Ast.LocalTarget t, m, args) ->
      List.concat_map goe args @ expand vis cls t m false
  | Ast.VarDecl (_, e) | Ast.Assign (_, e) -> goe e
  | Ast.CallStmt (f, args) ->
      goe { Ast.desc = Ast.Call (f, args); loc = st.Ast.sloc }
  | Ast.If (c, a, b) -> goe c @ go a @ go b
  | Ast.While (c, b) -> goe c @ go b
  | _ -> []

and sends_of_expr (vis : (string * string) list) (cls : string option)
                  (e : Ast.expr) : (string * string) list =
  let goe = sends_of_expr vis cls in
  match e.Ast.desc with
  | Ast.NowSend (Ast.LocalTarget t, m, args, _) ->
      List.concat_map goe args @ expand vis cls t m true
  | Ast.FutureSend (Ast.LocalTarget t, m, args) ->
      List.concat_map goe args @ expand vis cls t m false
  (* aios_now("actor", "method", ...) ---- 文字列で宛先を指す形 *)
  | Ast.Call (("aios_now" | "remote_now") as f,
              ({ Ast.desc = Ast.String t; _ } :: { Ast.desc = Ast.String m; _ } :: rest)) ->
      ignore f;
      List.concat_map goe rest @ expand vis cls t m true
  | Ast.Call (("aios_send" | "aios_future"),
              ({ Ast.desc = Ast.String t; _ } :: { Ast.desc = Ast.String m; _ } :: rest)) ->
      List.concat_map goe rest @ expand vis cls t m false
  | Ast.Call (_, args) | Ast.New (_, args) -> List.concat_map goe args
  | Ast.Binop (_, a, b) -> goe a @ goe b
  | Ast.Await (e1, _) -> goe e1
  | Ast.Expr e1 -> goe e1
  | _ -> []

(* 送信ひとつを、それ自身と（同期なら）呼び先の送信列に展開する *)
and expand (vis : (string * string) list) (cls : string option)
           (target : string) (m : string) (sync : bool) : (string * string) list =
  let a = resolve_actor target in
  let self = [(a, m)] in
  (* 手順の宛先なのに本体が見えないなら、続きがそこで進んでいるかもしれない。
     見えないものは「静的に並べられない」と印を付け、完了検査を実行時に任せる。 *)
  let opaque () = if List.mem (a, m) !proto_steps then proto_unsequenced := true in
  match class_of_actor cls a with
  | None -> opaque (); self
  | Some c ->
      if List.mem (c, m) vis then self          (* 再帰は一度で止める *)
      else
        (match Hashtbl.find_opt proto_methods (c, m) with
         | None -> opaque (); self
         | Some md ->
             (* 呼び先が引数でアクターを受け取るなら、その名前を解決できる *)
             let saved = Hashtbl.copy proto_params in
             List.iter2 (fun nm ty ->
               match ty with
               | Some (Types.TActor (cn, _)) when cn <> "?" ->
                   Hashtbl.replace proto_params nm cn
               | _ -> Hashtbl.remove proto_params nm)
               md.Ast.params md.Ast.param_tys;
             let inner = sends_of_stmt ((c, m) :: vis) (Some c) md.Ast.body in
             Hashtbl.reset proto_params;
             Hashtbl.iter (fun k v -> Hashtbl.replace proto_params k v) saved;
             if sync then self @ inner
             else begin
               (* 非同期。呼び先が手順を含むなら、順序は静的に決められない *)
               if List.exists (fun x -> List.mem x !proto_steps) inner then
                 proto_unsequenced := true;
               self
             end)

(* 解決表を作る。トップレベルの var と register_service、
   各クラスのフィールドとメソッドを拾う。 *)
let build_proto_tables (p : Ast.program) : unit =
  Hashtbl.reset proto_svc_actor; Hashtbl.reset proto_var_class;
  Hashtbl.reset proto_field_class; Hashtbl.reset proto_methods;
  proto_unsequenced := false;
  List.iter (function
    | Ast.Class c ->
        List.iter (fun (st : Ast.stmt) ->
          match st.Ast.sdesc with
          | Ast.VarDecl (x, { Ast.desc = Ast.New (cn, _); _ })
          | Ast.Assign (x, { Ast.desc = Ast.New (cn, _); _ }) ->
              Hashtbl.replace proto_field_class (c.Ast.cname, x) cn
          | _ -> ()) c.Ast.fields;
        List.iter (fun (m : Ast.method_decl) ->
          Hashtbl.replace proto_methods (c.Ast.cname, m.Ast.mname) m) c.Ast.methods
    | Ast.Global st ->
        (match st.Ast.sdesc with
         | Ast.VarDecl (x, { Ast.desc = Ast.New (cn, _); _ }) ->
             Hashtbl.replace proto_var_class x cn
         | Ast.CallStmt ("aios_register_service",
             [ { Ast.desc = Ast.String svc; _ }; { Ast.desc = Ast.String actor; _ } ]) ->
             Hashtbl.replace proto_svc_actor svc actor
         | _ -> ())) p

(* トップレベルの文の並びを、宣言・開始・送信・終了の順に見る *)
let check_protocols (p : Ast.program) : unit =
  let defs : (string, (string * string) list) Hashtbl.t = Hashtbl.create 8 in
  (* 1) 宣言を集める *)
  List.iter (function
    | Ast.Global { Ast.sdesc =
          Ast.CallStmt ("protocol_define",
            [ { Ast.desc = Ast.String name; _ }; { Ast.desc = Ast.String spec; _ } ]); _ } ->
        Hashtbl.replace defs name (parse_protocol_spec spec)
    | _ -> ()) p;
  if Hashtbl.length defs = 0 then () else begin
    (* 宛先の解決表と、全手順の和集合を用意する（振る舞い展開で使う） *)
    build_proto_tables p;
    proto_steps := Hashtbl.fold (fun _ v acc -> v @ acc) defs [];
    (* 送信列を一度全部展開して、静的に並べきれたかを見る。
       並べきれた（proto_unsequenced が立たなかった）なら、
       セッションがアクターをまたいでいても「やり残し」を誤りと言ってよい。
       並べきれなければ、続きが見えないところで進んでいるかもしれないので、
       完了の判定は実行時に任せる。 *)
    List.iter (function
      | Ast.Global st -> ignore (sends_of_stmt [] None st)
      | _ -> ()) p;
    let sequenced = not !proto_unsequenced in
    (* 2) start から end までの間の送信を順に照合する *)
    let cur : (string * string) list ref = ref [] in   (* 残りの手順 *)
    let active = ref None in
    (* 送信列を静的に並べきれたか。並べきれなければ、
       順序の違反は依然として誤りだが、
       「まだやっていない」は誤りだと言い切れない。 *)
    let full = ref false in
    let loc = ref Location.dummy in
    List.iter (function
      | Ast.Global st ->
          (match st.Ast.sdesc with
           | Ast.VarDecl (_, { Ast.desc =
                 Ast.Call ("protocol_start", [ { Ast.desc = Ast.String n; _ } ]); _ })
           | Ast.CallStmt ("protocol_start", [ { Ast.desc = Ast.String n; _ } ]) ->
               (match Hashtbl.find_opt defs n with
                | Some steps ->
                    active := Some n; cur := steps; loc := st.Ast.sloc;
                    full := sequenced
                | None ->
                    Types.type_error ~loc:st.Ast.sloc
                      ("protocol_start: unknown protocol " ^ n))
           | Ast.CallStmt ("protocol_end", _) ->
               (match !active with
                | Some n when !cur <> [] ->
                    let (a, m) = List.hd !cur in
                    let msg =
                      Printf.sprintf
                        "protocol %s is incomplete at protocol_end; next expected %s.%s"
                        n a m in
                    (* 手順が全部この並びに現れているなら、やり残しは誤りである。
                       そうでなければ、続きが受け手の中で進んでいるかもしれない ----
                       言い切れないので、既定では黙る。 *)
                    if !full then Types.type_error ~loc:st.Ast.sloc msg
                    else if Sys.getenv_opt "AIOS_STRICT_PROTOCOL" = Some "1" then
                      Printf.eprintf "[warn] %s: %s (the rest may run inside another actor)\n%!"
                        (Location.to_string st.Ast.sloc) msg;
                    active := None; cur := []
                | _ -> active := None; cur := [])
           | _ ->
               (match !active with
                | None -> ()
                | Some n ->
                    let all_steps =
                      match Hashtbl.find_opt defs n with Some x -> x | None -> [] in
                    List.iter (fun (t, m) ->
                      (* 手順に無い宛先への送信は、このセッションとは無関係。
                         宛先の綴りが手順と違うだけで誤検出していた
                         （手順が "main_thread.run" でプログラムは "main" へ送る等）。 *)
                      if List.mem (t, m) all_steps then begin
                        match !cur with
                        | [] -> ()   (* 手順は終わっている。余分は実行時に任せる *)
                        | (ea, em) :: rest ->
                            if ea = t && em = m then cur := rest
                            else
                              Types.type_error ~loc:st.Ast.sloc
                                (Printf.sprintf
                                   "protocol %s: expected %s.%s but the program sends %s.%s here"
                                   n ea em t m)
                      end)
                      (sends_of_stmt [] None st)))
      | _ -> ()) p;
    (* 3) end を書かずに終わった場合 *)
    (match !active with
     | Some n when !cur <> [] ->
         let (a, m) = List.hd !cur in
         let msg =
           Printf.sprintf "protocol %s is never completed; next expected %s.%s" n a m in
         if !full then Types.type_error ~loc:!loc msg
         else if Sys.getenv_opt "AIOS_STRICT_PROTOCOL" = Some "1" then
           Printf.eprintf "[warn] %s: %s\n%!" (Location.to_string !loc) msg
     | _ -> ())
  end

let check_effect_annotations (p : Ast.program) : unit =
  List.iter
    (function
      | Ast.Class c ->
          List.iter
            (fun (m : Ast.method_decl) ->
              match m.Ast.eff with
              | None -> ()                (* 無注釈は推論に任せる *)
              | Some declared ->
                  let d = Types.eff_of_list declared in
                  let actual = Types.lookup_method_eff c.Ast.cname m.Ast.mname in
                  (* 未知の効果名は誤記の可能性が高いので弾く *)
                  let unknown =
                    List.filter (fun e -> not (List.mem e Types.all_effects)) declared in
                  if unknown <> [] then
                    Types.type_error ~loc:m.Ast.body.Ast.sloc
                      (Printf.sprintf "unknown effect(s) %s in %s.%s; known effects are %s"
                         (String.concat ", " unknown) c.Ast.cname m.Ast.mname
                         (String.concat ", " Types.all_effects));
                  let missing = Types.SSet.diff actual d in
                  if not (Types.SSet.is_empty missing) then
                    Types.type_error ~loc:m.Ast.body.Ast.sloc
                      (Printf.sprintf
                         "method %s.%s declares %s but its body has %s (missing %s)"
                         c.Ast.cname m.Ast.mname
                         (Types.string_of_eff d) (Types.string_of_eff actual)
                         (Types.string_of_eff missing)))
            c.Ast.methods
      | _ -> ())
    p

(* デバッグ表示。推論された効果を一覧する（移行の手がかり） *)
let debug_print_effects () : unit =
  print_endline "[method effects (inferred / declared)]";
  Hashtbl.fold (fun k r acc -> (k, !r) :: acc) Types.method_effs []
  |> List.sort (fun (a,_) (b,_) -> compare a b)
  |> List.iter (fun (k, e) ->
       Printf.printf "  %s !%s\n" k (Types.string_of_eff e))

let check_program (p: Ast.program) : (Types.tenv, string) result =
  let env0 = Typing_env.prelude () in
  try
    Types.reset_method_rets ();             (* ★ 前回検査の ρ を持ち越さない *)
    Types.reset_effects ();                 (* ★ 効果も持ち越さない *)
    prebind_global_actors p env0;
    in_preinfer := true;
    preinfer_all_classes p env0;           (* ★ 先に全クラスのメソッド型を登録 *)
    in_preinfer := false;
    if !verbose then Types.debug_print_class_method_schemes ();
    List.iter (check_decl env0) p;          (* それから通常どおりトップレベルを検査 *)
    Types.propagate_effects ();             (* ★ now の連鎖に沿って効果を伝播 *)
    check_effect_annotations p;             (* ★ 宣言と本体の効果を照合 *)
    check_protocols p;                      (* ★ セッションの手順を静的に照合 *)
    (* ★ 循環待ちの検査。now / await の辺に閉路があれば、
       期限が無ければ確実に詰まる。既定は警告、
       AIOS_STRICT_WAIT=1 でエラーに昇格する（期限の扱いと同じ形）。 *)
    (* ★ 待たれるメソッドは必ず返す（reply の全域性）。
       デッドロックは循環待ちだけではない ---- 閉路が無くても、
       呼ばれる側が reply しなければ待ちは返らない。
       戻り値型を宣言したメソッドには既に被覆を課しているが、
       unit を返すメソッドが抜け穴になっていた。
       now/await で待たれるメソッドに限って、戻り値型に関わらず課す。
       AIOS_LAX_REPLY_TOTAL=1 で従来どおりにできる。 *)
    (if Sys.getenv_opt "AIOS_LAX_REPLY_TOTAL" <> Some "1" then begin
       let waited = List.map snd !Types.now_edges in
       List.iter (function
         | Ast.Class c ->
             List.iter (fun (m : Ast.method_decl) ->
               let key = Types.eff_key c.Ast.cname m.Ast.mname in
               if List.mem key waited
                  && not (stmt_uses_replyto m.Ast.body)
                  && not (replies_on_all_paths m.Ast.body) then
                 Types.type_error ~loc:m.Ast.body.Ast.sloc
                   (Printf.sprintf
                      "method %s.%s is waited on by now/await but does not reply on every path"
                      c.Ast.cname m.Ast.mname)) c.Ast.methods
         | _ -> ()) p
     end);
    (* ★ select が待っているメッセージを、誰かが送っているか。
       送る側がどこにも無ければ、その case は永久に発火しない。
       閉路でも返信漏れでもない三つ目の詰まり方。
       送信が動的（sender 経由・遠隔）だと見えないので、既定は警告。
       AIOS_STRICT_SELECT=1 でエラーに昇格。 *)
    (* 外から送られてくる場合は見えない。web_expose / web_listen があれば
       そのプログラムは外部の送り手を持つので、この検査は当てにならない。
       遠隔（remote / deploy）も同様。実測でも、警告が出た 2 本は
       どちらも web_expose で外へ公開している例題であった。 *)
    let has_external_sender =
      List.exists (function
        | Ast.Global { Ast.sdesc = Ast.CallStmt (f, _); _ } ->
            f = "web_expose" || f = "web_listen" || f = "deploy"
        | _ -> false) p
      || !Types.remote_waits <> [] in
    List.iter (fun (cls, m, loc) ->
      if (not has_external_sender) && not (Types.was_sent cls m) then begin
        let msg =
          Printf.sprintf
            "select waits for %s.%s but nothing in this program sends it" cls m in
        if Sys.getenv_opt "AIOS_STRICT_SELECT" = Some "1" then
          Types.type_error ~loc msg
        else Printf.eprintf "[warn] %s: %s\n%!" (Location.to_string loc) msg
      end) !selected_msgs;
    selected_msgs := [];
    (match Types.wait_cycle () with
     | Some cyc ->
         let msg =
           Printf.sprintf
             "circular wait: %s; a now/await cycle deadlocks unless a deadline breaks it"
             (String.concat " -> " cyc) in
         if strict_wait () then Types.type_error ~loc:Location.dummy msg
         else Printf.eprintf "[warn] %s\n%!" msg
     | None -> ());
    (* ★ 義務レベル。now/await は厳密に大きいレベルにしか向かえない。
       注釈が無いメソッドには\textbf{レベルを推論する} ----
       待ちの辺 (a, b) を見て level(b) <= level(a) なら b を押し上げる、を
       不動点まで繰り返す。明示注釈は固定点で、押し上げが要るのに動かせなければ
       そこが矛盾である。閉路があれば収束しないが、閉路は別に弾いている。
       これで、片方にしか注釈が無い辺も検査できる
       （注釈だけの段階では、付け忘れた組が素通りしていた）。 *)
    (let lv = Hashtbl.create 32 in
     let fixed = Hashtbl.create 32 in
     List.iter (function
       | Ast.Class c ->
           List.iter (fun (m : Ast.method_decl) ->
             let k = Types.eff_key c.Ast.cname m.Ast.mname in
             Hashtbl.replace lv k (match m.Ast.level with Some n -> n | None -> 0);
             (match m.Ast.level with
              | Some _ -> Hashtbl.replace fixed k ()
              | None -> ())) c.Ast.methods
       | _ -> ()) p;
     let get k = match Hashtbl.find_opt lv k with Some n -> n | None -> 0 in
     let changed = ref true and guard = ref 0 in
     while !changed && !guard < 1000 do
       changed := false; incr guard;
       List.iter (fun (caller, callee) ->
         let a = get caller and b = get callee in
         if b <= a then begin
           if Hashtbl.mem fixed callee then
             Types.type_error ~loc:Location.dummy
               (Printf.sprintf
                  "obligation level: %s (@%d) waits on %s (@%d); a wait must go to a strictly higher level"
                  caller a callee b)
           else begin Hashtbl.replace lv callee (a + 1); changed := true end
         end) !Types.now_edges
     done;
     if !guard >= 1000 then
       Types.type_error ~loc:Location.dummy
         "obligation levels do not converge; the wait graph has a cycle";
     (* ★ ノード間のレベル。プログラム中の node_level("n", k) を読み、
        そのノードへの待ちが上へ向かうことを要求する。
        宛先の実体は別ノードにあり見えないので、ノード単位の階層で近似する。 *)
     (let floors = Hashtbl.create 8 in
      List.iter (function
        | Ast.Global { Ast.sdesc =
              Ast.CallStmt ("node_level",
                [ { Ast.desc = Ast.String n; _ }; { Ast.desc = Ast.Int k; _ } ]); _ } ->
            Hashtbl.replace floors n k
        | _ -> ()) p;
      List.iter (fun (caller, node) ->
        match Hashtbl.find_opt floors node with
        | Some f ->
            let a = get caller in
            if f <= a then
              Types.type_error ~loc:Location.dummy
                (Printf.sprintf
                   "obligation level: %s (@%d) waits on node %s (floor @%d); a wait across nodes must go up"
                   caller a node f)
        | None -> ()) !Types.remote_waits);
     (* 推論したレベルを見せる（AIOS_SHOW_LEVELS=1） *)
     if Sys.getenv_opt "AIOS_SHOW_LEVELS" = Some "1" then begin
       let items = Hashtbl.fold (fun k v acc -> (k, v) :: acc) lv [] in
       let items = List.sort (fun (_, a) (_, b) -> compare a b) items in
       List.iter (fun (k, v) ->
         Printf.eprintf "[level] %-28s @%d%s\n%!" k v
           (if Hashtbl.mem fixed k then " (declared)" else "")) items
     end);

    (* ★ 資源の使用順序（acquire / release の対）。効果集合では表せない性質。 *)
    Hashtbl.reset res_edges; res_opaque := []; res_site := "top level";
    List.iter (function
      | Ast.Class c ->
          List.iter (fun (m : Ast.method_decl) ->
            (try check_resource_use c.Ast.cname m
             with Res_error (loc, msg) -> Types.type_error ~loc msg);
            (* ★ 返信先の線形性 *)
            (try check_reply_linearity c.Ast.cname m
             with Res_error (loc, msg) -> Types.type_error ~loc msg)) c.Ast.methods
      | _ -> ()) p;
    (* トップレベルの並びも同じ規律で見る（ここも acquire できる） *)
    res_site := "top level";
    (try
       let left =
         List.fold_left (fun h -> function
           | Ast.Global st -> res_of_stmt st h
           | _ -> h) SSet.empty p in
       if not (SSet.is_empty left) then
         raise (Res_error (Location.dummy,
           Printf.sprintf "the program ends while still holding %s"
             (String.concat ", " (SSet.elements left))))
     with Res_error (loc, msg) -> Types.type_error ~loc msg);
    (* ★ 資源への全体順序。対だけでは逆順の取得を止められない。 *)
    check_resource_order p;
    check_boundary_annotations p env0;      (* ★ リモート境界の注釈必須検査 *)
    if !verbose then Types.debug_print_method_rets ();
    if !verbose then debug_print_effects ();
    Ok env0
  with
  | Types.Type_error (loc, msg) ->
      let loc_s = Location.to_string loc in
      Error (Printf.sprintf "%s: %s" loc_s msg)
