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
  | Ast.Int _ | Ast.Float _ | Ast.String _ | Ast.Bool _ | Ast.Var _ -> false
and alt_has_reply = function
  | None -> false
  | Some (_, a) -> expr_has_reply a

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
  | Ast.Int _ | Ast.Float _ | Ast.String _ | Ast.Bool _ | Ast.Var _ -> 0
and max_alt = function None -> 0 | Some (_, a) -> max_replies_expr a

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
let in_now_send = ref false
let record_now_edge (cls : string) (mname : string) : unit =
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
    | TArray t1 | TFuture t1 -> go t1
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
      let ret =
        begin match target with
        (* リモート宛先は本体が別ノードにあり推論できない。
           ここは宣言（インタフェース）でしか埋まらない場所なので any のまま。
           ただし★ノード外へ出る通信なので net 効果は確定する。 *)
        | RemoteTarget (_hostport, _actor_name) -> add_eff ["net"]; TAny
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
      TFuture ret
  | NowSend (target, mname, args, dl) ->
      (* now は future の即時 await。戻り値型も同じ ρ になる。
         ★ 待つので、呼ばれる側の効果を引き継ぐ辺を張る。 *)
      let saved = !in_now_send in
      in_now_send := true;
      let r =
        (match repr (infer_expr env { e with desc = FutureSend (target, mname, args) }) with
         | TFuture t -> t
         | _         -> TAny)
      in
      in_now_send := saved;
      check_deadline env e.loc "now" r dl;
      r
  | Await (e1, dl) ->
      let r =
        (match repr (infer_expr env e1) with
         | TFuture t -> t
         | TAny -> TAny
         | t -> Types.type_error ~loc:e.loc
                  ("await expected future, got " ^ string_of_ty_pretty t))
      in
      check_deadline env e.loc "await" r dl;
      r

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
                   (rty:ty) (dl:(int * Ast.expr) option) : unit =
  match dl with
  | Some (ms, alt) ->
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
                         List.iter2 (Types.unify ~loc:s.sloc) param_tys actuals
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
                         List.iter2 (Types.unify ~loc:s.sloc) param_tys actuals
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
         ()
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
            add env name sch
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
        if max_replies m.body > 1 then
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
                  if not (replies_on_all_paths m.body) then
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
    | Ast.Await (e1, d) -> ex e1; (match d with Some (_,a) -> ex a | None -> ())
    | Ast.New (_, args) | Ast.Array (args, _)
    | Ast.FutureSend (_, _, args) -> List.iter ex args
    | Ast.NowSend (_, _, args, d) ->
        List.iter ex args; (match d with Some (_,a) -> ex a | None -> ())
    | Ast.Int _ | Ast.Float _ | Ast.String _ | Ast.Bool _ | Ast.Var _ -> ()
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
    check_boundary_annotations p env0;      (* ★ リモート境界の注釈必須検査 *)
    if !verbose then Types.debug_print_method_rets ();
    if !verbose then debug_print_effects ();
    Ok env0
  with
  | Types.Type_error (loc, msg) ->
      let loc_s = Location.to_string loc in
      Error (Printf.sprintf "%s: %s" loc_s msg)
