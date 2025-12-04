(* infer.ml *)
open Types
open Typing_env
open Ast

(* preinfer（1パス目）中かどうかのフラグ *)
let in_preinfer = ref false

let set_var_scheme (env : (string, scheme list) Hashtbl.t) (x:string) (sch:scheme) : unit =
  Hashtbl.replace env x [sch]

let get_var_scheme_exn (env : (string, scheme list) Hashtbl.t) (x:string) : scheme =
  match Hashtbl.find_opt env x with
  | Some [sch] -> sch
  | Some _     -> raise (Type_error (Location.dummy,("cannot assign to overloaded name: " ^ x)))
  | None       -> raise (Type_error (Location.dummy,("unbound variable: " ^ x)))

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

let pick_overload (name:string) (env:tenv) (arg_tys:ty list) : ty =
  let schemes =
    match Hashtbl.find_opt env name with Some ss -> ss | None -> []
  in
  let ok =
    List.filter_map (fun sch ->
      match repr (instantiate sch) with
      | TFun (ps, ret) when List.length ps = List.length arg_tys ->
          (try List.iter2 unify ps arg_tys; Some (repr ret)
           with _ -> None)
      | _ -> None
    ) schemes
  in
  match ok with
  | [r] -> r
  | r::_ -> r     (* 単一に絞れない場合の方針は実装に合わせて *)
  | [] ->
      let sigstr =
        "(" ^ String.concat ", " (List.map Types.string_of_ty_pretty arg_tys) ^ ")"
      in
      raise (Type_error (Location.dummy,("no overload of "^name^" matches "^sigstr)))

let unify_many (ps : Types.ty list) (as_ : Types.ty list) =
  try List.iter2 Types.unify ps as_
  with Invalid_argument _ ->
    raise (Type_error (Location.dummy,(Printf.sprintf
		       "arity mismatch: expected %d args, got %d" (List.length ps) (List.length as_))))

(* 受け手の型からメソッド mname のモノタイプを取り出す。
   TActor の第2引数 ms に暫定/確定メソッド表があればそれを優先、
   無ければクラス名 cls で事前登録テーブルから sc を引いて instantiate します. *)
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

let rec infer_expr (env:env) (e:expr) : ty =
  match e.desc with
  | Int _ -> TInt
  | Float _ -> TFloat
  | String _ -> TString
  | Binop (op, e1, e2) ->
    let t1 = infer_expr env e1 in
    let t2 = infer_expr env e2 in
    (* 特例: 片側が string の + は文字列連結として扱う *)
    (match op, repr t1, repr t2 with
     | "+", TString, _ -> TString
     | "+", _, TString -> TString
     | _ ->
         (* 従来のオーバーロード解決 *)
         pick_overload op env [t1; t2])
  | Call (fname, arg1) ->
      let t_args = List.map (infer_expr env) arg1 in
      pick_overload fname env t_args
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
    let targs = List.map (infer_expr env) args in
    (match Types.lookup_class_method_scheme cls "init" with
     | Some sch ->
         (match Types.instantiate sch with
          | Types.TFun (params, _ret) ->
              let unify_many ps qs =
                try List.iter2 Types.unify ps qs with Invalid_argument _ ->
                    raise (Type_error (e.loc,
                      (Printf.sprintf "constructor %s: arity mismatch (expected %d, got %d)"
                         cls (List.length ps) (List.length qs))))
              in
                unify_many params targs
          | ty ->
              raise (Type_error (e.loc,
                (Printf.sprintf "constructor %s: init is not a function: %s"
                   cls (Types.string_of_ty_pretty ty))))
          )
     | None -> ());
    let ms = Types.lookup_class_methods_inst cls in TActor (cls, ms)
  | Array (elems, _) ->
    begin match elems with
    | [] -> TArray TUnit   (* 空配列は unit[] として扱う *)
    | e1 :: rest ->
        let t1 = infer_expr env e1 in
        List.iter (fun e -> unify (infer_expr env e) t1) rest;
        TArray t1
    end
    
let set (e:env) (name:string) (sch:scheme) =
  Hashtbl.replace e name [sch]

let class_name_of_var (env : Types.tenv) (vname : string) : string =
  let t = repr (Types.instantiate (get_var_scheme_exn env vname)) in
  match t with
  | TActor (cls, _) -> cls
  | other -> raise (Type_error (Location.dummy,("send target is not an actor: " ^ string_of_ty(other))))

let rec check_stmt (env:env) (s:stmt) : unit =
  match s with
  | Assign (x, e) ->
    let t_rhs = infer_expr env e in
    (match Hashtbl.find_opt env x with
     | None ->
         let sch = Types.generalize (ftv_env env) t_rhs in
         set_var_scheme env x sch
     | Some [sch] ->
         (* 既存の型に RHS を合わせる：必要なら instantiate → unify *)
         let t_old = instantiate sch in
         unify t_old t_rhs;
         let sch' = Types.generalize (ftv_env env) t_rhs in   (* 代入後の型を更新（単相にしたいなら Forall([], t_rhs)）*)
         set_var_scheme env x sch'
     | Some _ ->
         raise (Type_error (Location.dummy,("cannot assign to overloaded name: " ^ x))));
    ()
  | VarDecl (name, rhs) ->
      let t   = infer_expr env rhs in
      let sch = Types.generalize (ftv_env env) t in
      (* 単一束縛として“置き換え” *)
        set_var_scheme env name sch;
        ()
  | If (cond, tbr, fbr) ->
      let tc = infer_expr env cond in
      unify tc TFloat;
      check_stmt env tbr; check_stmt env fbr
  | While (cond, body) ->
      let tc = infer_expr env cond in unify tc TFloat;
      check_stmt env body
  | Seq ss -> List.iter (check_stmt env) ss
  | CallStmt (fname, args) ->
      let arg_tys = List.map (infer_expr env) args in
      ignore (pick_overload fname env arg_tys);
      ()
  | Send (vname, mname, args) ->
      if !in_preinfer then begin
        (* ★ 1パス目（preinfer）：
           - 変数や引数の型だけざっくり推論しておく
           - actor かどうか / メソッドが存在するかはチェックしない *)
        ignore (infer_expr env (mk_var(vname)));
        List.iter (fun e -> ignore (infer_expr env e)) args;
      end else begin
        (* ★ 2パス目（本番の型チェック） *)
        if vname = "sender" then begin
          (* 特別扱い：sender は動的な送り主アクターなので、
             - actor かどうか
             - メソッド ping/pong が存在するか
             は静的にはチェックしない。
             引数の型だけ推論しておく。 *)
          List.iter (fun e -> ignore (infer_expr env e)) args;
        end else begin
          (* 通常の send: vname の型を actor(C) として取り出し、
             preinfer で登録したクラスメソッド表から mname の型を調べる *)
          let t_actor = infer_expr env (mk_var(vname)) in
          match repr t_actor with
          | TActor (cls, _) ->
              (match Types.lookup_class_method_scheme cls mname with
               | None ->
                   raise (Type_error (Location.dummy,
                     ("no method " ^ mname ^ " in actor(" ^ cls ^ ")")))
               | Some sc ->
                   let tf = repr (Types.instantiate sc) in
                   match tf with
                   | TFun (param_tys, ret_ty) ->
                       let actuals =
                         List.map (fun e -> repr (infer_expr env e)) args in
                       if List.length param_tys <> List.length actuals then
                         raise (Type_error (Location.dummy,"arity mismatch in send"));
                       List.iter2 Types.unify param_tys actuals;
                       ()
                   | _ ->
                       raise (Type_error (Location.dummy,
                         ("method " ^ mname ^ " is not a function: "
                          ^ string_of_ty tf))))
          | t_non_actor ->
              raise (Type_error (Location.dummy,
                ("send target is not actor: " ^ string_of_ty t_non_actor)))
        end
    end

let check_decl (env:env) = function
  | Class c ->
      List.iter (function
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

      (* 3) 本文は“ローカル環境”で検査：ローカル変数が外へ漏れない *)
      List.iter (fun m ->
        let env_m = clone env in
        (* ★ self をこのクラスのアクターとしてローカル環境に追加 *)
        set env_m "self" (Forall ([], TActor (c.Ast.cname, [])));

        (* ★ メソッド仮引数をローカル環境に束縛（今は float 想定） *)
        List.iter (fun p ->
          set env_m p (Forall ([], TFloat))
        ) m.params;

        check_stmt env_m m.body
	) c.methods
  | Instantiate (_obj, _class) -> ()
  | InstantiateInit (_obj, _class, inits) ->
    List.iter (fun st ->
      match st with
      | VarDecl (_f, e) -> ignore (infer_expr env e)
      | _ -> ()
    ) inits
  | InstantiateArgs (_cls, _var, args) ->  
      List.iter (fun a -> unify (infer_expr env a) TFloat) args
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

let infer_class_method_schemes (g0 : env) (c : Ast.class_decl) : (string * Types.scheme) list =
  (* 0) クラス用の「項レベル環境」(string -> Types.scheme) を用意 *)
  let env_cls : env = clone g0 in

  (* 1) フィールドの単相バインドを env_cls に入れる *)
  List.iter
    (function
      | Ast.VarDecl (name, rhs) ->
          let t   = infer_expr env_cls rhs in
          let sc  = Types.generalize (Types.ftv_env env_cls) t in
          set_var_scheme env_cls name sc
      | _ -> ()
    )
    c.Ast.fields;

  (* 2) メソッドの暫定型 (相互再帰のため) を name -> TFun([α…] -> unit) で作る *)
  let proto_tys : (string * Types.ty) list = List.map build_proto c.Ast.methods
  in
  (* 3) 各メソッドを、self を TActor(cname, proto_tys) にして型付け *)
  let infer_one (m : Ast.method_decl) : (string * Types.scheme) =
    let env_m = clone env_cls in
    (* self はこのクラス名＋暫定メソッド群 *)
    set_var_scheme env_m "self" (Forall ([], Types.TActor (c.Ast.cname, proto_tys)));

    (* このメソッド m のパラメータ名群と、proto が持つ m の仮引数型（= TVar の列）を対応づけて単相バインド *)
    let ps0 =
      match List.assoc m.Ast.mname proto_tys with
      | Types.TFun (ps, _) -> ps
      | _ -> failwith "internal: expected TFun in proto"
    in
    List.iter2
      (fun (pname : string) (pt : Types.ty) ->
         set_var_scheme (env_m) pname (Forall ([], pt)))
      m.Ast.params
      ps0;
   (* 本体を型検査。ここで param/“self.メソッド”を通じて TVar が具体化される *)
    let () = check_stmt env_m m.Ast.body in

    (* パラメータの最終的な型を取り出す（monotypeをreprしてやる） *)
    let inst_param_tys : Types.ty list =
      List.map
        (fun pname ->
           let sc = get_var_scheme_exn env_m pname in
           Types.repr (Types.instantiate sc))
        m.Ast.params
    in
    let tfun = Types.TFun (inst_param_tys, Types.TUnit) in

    (* env_cls の自由変数を引いた上で generalize *)
    let sc = Types.generalize (Types.ftv_env env_cls) tfun in
    (m.Ast.mname, sc)
  in
  List.map infer_one c.Ast.methods

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
      | Ast.Global (Ast.VarDecl (name, rhs)) ->
          (match new_class_of_expr rhs with
           | Some cls ->
               let t   = Types.TActor (cls, []) in
               let sch = Types.Forall ([], t) in
               (* 既存の set_var_scheme を使って環境に登録 *)
               set_var_scheme env name sch
           | None -> ())
      | _ -> ())
    p

let preinfer_all_classes (p : Ast.program) (g0 : Types.tenv) : unit =
  let infer_one_class (c : Ast.class_decl) : (string * Types.scheme) list =
    let env_cls = clone g0 in
    List.iter (function
      | Ast.VarDecl (name, rhs) ->
          let t = infer_expr env_cls rhs in
          let sch = generalize (ftv_env env_cls) t in
          set_var_scheme env_cls name sch
      | _ -> ()
    ) c.Ast.fields;
    let infer_method (m : Ast.method_decl) =
      let env_m = clone env_cls in
      set_var_scheme env_m "self" (Types.Forall ([], Types.TActor(c.Ast.cname,[])));
      let ps =
        List.map (fun p -> let a = Types.fresh_tvar () in
                           set_var_scheme env_m p (Types.Forall ([], Types.TVar a));
                           Types.TVar a) m.Ast.params
      in
(*       check_stmt env_m m.Ast.body;     *)
      let ps' = List.map (fun p -> Types.repr (Types.instantiate (get_var_scheme_exn env_m p))) m.Ast.params in
      let tfun = Types.TFun (ps', Types.TUnit) in
      let sch  = generalize (ftv_env env_m) tfun in
      (m.Ast.mname, sch)
    in
    List.map infer_method c.Ast.methods
  in
    List.iter (function
    | Ast.Class c ->
        let sigs = infer_one_class c in
        Types.register_class_method_schemes c.Ast.cname sigs
    | _ -> ()
  ) p

let check_program (p: Ast.program) : (Types.tenv, string) result =
  let env0 = Typing_env.prelude () in
  try
    prebind_global_actors p env0;
    in_preinfer := true;
    preinfer_all_classes p env0;           (* ★ 先に全クラスのメソッド型を登録 *)
    in_preinfer := false;
    Types.debug_print_class_method_schemes ();
    List.iter (check_decl env0) p;          (* それから通常どおりトップレベルを検査 *)
    Ok env0
  with
  | Types.Type_error (loc, msg) ->
      let loc_s = Location.to_string loc in
      Error (Printf.sprintf "%s: %s" loc_s msg)
