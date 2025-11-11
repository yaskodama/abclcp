(** infer.ml *)
open Types
open Typing_env
open Ast

(* ========================================= *)
(* 名前に対応する全スキームを取得する関数   *)
(* ========================================= *)
let set_var_scheme (env : (string, scheme list) Hashtbl.t) (x:string) (sch:scheme) : unit =
  Hashtbl.replace env x [sch]

let get_var_scheme_exn (env : (string, scheme list) Hashtbl.t) (x:string) : scheme =
  match Hashtbl.find_opt env x with
  | Some [sch] -> sch
  | Some _     -> raise (Type_error ("cannot assign to overloaded name: " ^ x))
  | None       -> raise (Type_error ("unbound variable: " ^ x))

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
      raise (Type_error ("no overload of "^name^" matches "^sigstr))

let unify_many (ps : Types.ty list) (as_ : Types.ty list) =
  try List.iter2 Types.unify ps as_
  with Invalid_argument _ ->
    raise (Type_error (Printf.sprintf
		       "arity mismatch: expected %d args, got %d" (List.length ps) (List.length as_)))

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

(* let lookup_method_type (tobj : Types.ty) (mname : string) : Types.ty option =
  match Types.repr tobj with
  | Types.TActor (cls, ms) ->
      (* 1st: 既に self に埋めてある暫定/最終のメソッド表を優先 *)
      (match List.assoc_opt mname ms with
       | Some t -> Some t
       | None ->
           (* 2nd: 事前登録されたスキーマから引いて具体化 *)
           (match Types.lookup_class_method_scheme cls with
            | Some sc -> Some (Types.instantiate sc)
            | None    -> None))
  | _ -> None   *)

(* 補助: 受信オブジェクトの型からメソッドの “具体 ty” を引く（instantiate 済） *)
(* let lookup_method_type (tobj : Types.ty) (mname : string) : Types.ty option =
  match tobj with
  | Types.TActor (nm, _) ->
     Option.map Types.instantiate (Types.lookup_class_method_scheme nm mname)
  | Types.TRecord ms ->
      List.assoc_opt mname ms
      | _ -> None   *)

let rec infer_expr (env:env) (e:expr) : ty =
  match e with
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
  | Var x ->
      let sch = get_var_scheme_exn env x in
        instantiate sch
  | New (cls, args) ->
    let targs = List.map (infer_expr env) args in
    (match Types.lookup_class_method_scheme cls "init" with
     | Some sch ->
         (match Types.instantiate sch with
          | Types.TFun (params, _ret) ->
              let unify_many ps qs =
                try List.iter2 Types.unify ps qs with Invalid_argument _ ->
                    raise (Type_error
                      (Printf.sprintf "constructor %s: arity mismatch (expected %d, got %d)"
                         cls (List.length ps) (List.length qs)))
              in
                unify_many params targs
          | ty ->
              raise (Type_error
                (Printf.sprintf "constructor %s: init is not a function: %s"
                   cls (Types.string_of_ty_pretty ty)))
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

(*
let class_name_of_target (env: Types.tenv) (e: Ast.expr) : string =
  match repr (infer_expr env e) with
  | TActor (cname, _) -> cname
  | other -> raise (Type_error ("send target is not an object/actor, got " ^ Types.string_of_ty other))
*)

(* Send の型付け: Send of string (* var名 *) * expr list という定義を想定 *)
(* let class_name_of_var (env : Types.t_env) (vname : string) : string =
  let t = Types.repr (Types.instantiate (get_var_scheme_exn env vname)) in
  match t with
  | Types.TActor (cls, _) -> cls
  | _ -> raise (Types.Error ("send target is not an actor: " ^ Types.string_of_ty t))    *)

let class_name_of_var (env : Types.tenv) (vname : string) : string =
  let t = repr (Types.instantiate (get_var_scheme_exn env vname)) in
  match t with
  | TActor (cls, _) -> cls
  | other -> raise (Type_error ("send target is not an actor: " ^ string_of_ty(other)))

(* 変数名から、その静的型（TObject/TActor）に埋まっている“クラス名”を取り出す *)
let class_name_of_var (env : Types.tenv) (vname : string) : string =
  let t = repr (instantiate (get_var_scheme_exn env vname)) in
  match t with
(*  | TObject cname -> cname    *)
  | TActor (cname, _) -> cname              (* 名義つき Actor 型にも対応 *)
  | other -> raise (Type_error ("send target is not an object/actor, got "^string_of_ty other))

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
         raise (Type_error ("cannot assign to overloaded name: " ^ x)));
    ()
  | VarDecl (name, rhs) ->
      let t   = infer_expr env rhs in
      let sch = Types.generalize (ftv_env env) t in
      (* 単一束縛として“置き換え” *)
        set_var_scheme env name sch;
        ()
  | If (cond, tbr, fbr) ->
      (* 現実装互換: 条件は float（0/非0）扱い。将来 Bool にするならここを TBool へ。 *)
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
    let cls = class_name_of_var env vname in
    (* 事前に登録したメソッドのスキーマを取り出す（二引数で呼ぶ！） *)
    (match Types.lookup_class_method_scheme cls mname with
     | None ->
         raise (Type_error ("no method " ^ mname ^ " in actor(" ^ cls ^ ")"))
     | Some sc ->
         let tf = repr (Types.instantiate sc) in
         let (ps, r) =
           match tf with
           | TFun (ps, r) -> (ps, r)
           | _ -> raise (Type_error ("method "^mname^" is not a function: " ^ string_of_ty tf))
         in
         let actuals = List.map (fun e -> repr (infer_expr env e)) args in
         if List.length ps <> List.length actuals then
           raise (Type_error "arity mismatch in send");
         List.iter2 (fun p a -> Types.unify p a) ps actuals;
(*         TActor (cls, [])  *)(* ← send の式自体は unit にしたいなら `TUnit` を返す *)
         ()
      )
(*  | Send (vname, mname, args) ->
    let cls = class_name_of_var env vname in
    (* 受け手の型は TActor (cls, …) だとわかっているので、先に受け手の self メソッド表を作る必要はなし *)
    (match Typing_env.lookup_class_method_scheme cls mname with
     | None ->
         raise (Types.Error ("no method "^mname^" in actor("^cls^")"))
     | Some sc ->
        let Types.TFun (ps, r) = Types.repr (Types.instantiate sc) in
         let arg_tys = List.map (fun e -> Types.repr (infer_expr env e)) args in
         if List.length ps <> List.length arg_tys then
           raise (Types.Error "arity mismatch in send");
         List.iter2 (fun p a -> Types.unify p a) ps arg_tys;
         (* send 弾性: 自身の型は unit *)
         Types.TUnit
    )    *)
(*  | Send (tgt_exp, mname, args) ->
    let cls = class_name_of_var env mname in
    (match Types.lookup_class_method_scheme cls mname with
     | None ->
         raise (Type_error ("no method " ^ mname ^ " in class " ^ cls))
     | Some sch ->
        let tfun = repr (instantiate sch) in
         let (param_tys, ret_ty) =
           match tfun with
           | TFun (ps, r) -> (ps, r)
           | other -> raise (Type_error ("method "^mname^" is not a function type: " ^ string_of_ty other))
         in
         let arg_tys = List.map (fun e -> repr (infer_expr env e)) args in
         if List.length arg_tys <> List.length param_tys then
           raise (Type_error "arity mismatch in send");
         List.iter2 (fun p a -> unify p a) param_tys arg_tys;
         ()
    )
*)
(*    let cls = class_name_of_target env tgt_exp in
    begin match Typing_Env.lookup_method_scheme cls mname with
    | None -> raise (Type_error ("no method "^mname^" in class "^cls))
    | Some sch ->
        let TFun (ps, _ret) = repr (instantiate sch) in
        let arg_tys = List.map (fun a -> repr (infer_expr env a)) args in
        if List.length ps <> List.length arg_tys then
          raise (Type_error "arity mismatch in send");
        List.iter2 (fun p a -> unify p a) ps arg_tys;
        ()
    end  *)
(*   | Send (recv_name, mname, args) ->
    let t_tgt = repr (instantiate (get_var_scheme_exn env tgt)) in
    let cls =
      match t_tgt with
      | TObject cname -> cname
      | TActor        -> (* もし TActor を使っている場合、静的にはクラス名が無いのでエラーにするか、
                            別途 env に “var -> class_name” の表を持って取り出してください。 *)
                         raise (Type_error "send target has type 'actor' without class; bind as TObject \"C\"")
      | _             -> raise (Type_error "send target is not an object/actor")
    in
    (match Typing_env.lookup_method_scheme cls mname with
     | None ->
         raise (Type_error ("no method " ^ mname ^ " in class " ^ cls))
     | Some sch ->
         let TFun (ps, _ret) = repr (instantiate sch) in
         let arg_tys = List.map (infer_expr env) args in
         if List.length ps <> List.length arg_tys
           then raise (Type_error "arity mismatch in send");
         List.iter2 (fun pty aty -> unify pty aty) ps arg_tys;
         (* send は戻り値を使わないので、ret は unit かどうかは厳密には問わない。
            厳密化したいなら: unify _ret TUnit; *)
         ()
      )
*)
(*    let trecv = infer_expr env (Ast.Var recv_name) in
    let lookup_method_type (tobj:Types.ty) (m:string) : Types.ty option =
      match tobj with
      | Types.TActor (nm, _) ->
        Option.map Types.instantiate (Types.lookup_class_method_scheme nm m)
      | Types.TRecord ms -> List.assoc_opt m ms
      | _ -> None
    in
    (match lookup_method_type trecv mname with
     | Some (Types.TFun (ps, _)) ->
       let tas = List.map (infer_expr env) args in
       (try List.iter2 Types.unify ps tas with Invalid_argument _ ->
          raise (Type_error (Printf.sprintf
            "send %s: arity mismatch (expected %d, got %d)"
            mname (List.length ps) (List.length tas))));
       ()
     | Some t ->
       raise (Type_error (Printf.sprintf
         "send %s: method is not a function: %s" mname (Types.string_of_ty_pretty t)))
     | None ->
       let hint =
         match trecv with
         | Types.TActor (nm, _) ->
             let ms = Types.lookup_class_methods_inst nm in
             if ms = [] then Printf.sprintf "registered: <none for %s>" nm
             else Printf.sprintf "registered: %s"
                    (Types.string_of_ty_pretty (Types.TActor (nm, ms)))
         | _ -> "registered: <not an actor/object>"
       in
         raise (Type_error (Printf.sprintf "send %s: no such method for receiver type %s; %s"
         mname (Types.string_of_ty_pretty trecv) hint)))
*)


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
        (* ★ 追加：メソッド仮引数をローカル環境に束縛（型は float 想定） *)
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

(* clone は既存のものを使います *)
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

(* ===== 1st pass: クラスごとのメソッド型を HM で推論し、Typing_env に登録 ===== *)
(* let ms : (string * Types.scheme) list = infer_class_methods gamma cls_name methods in
  Types.register_class_methods cls_name ms *)

let infer_class_method_schemes (g0 : env) (c : Ast.class_decl)
  : (string * Types.scheme) list =
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

(*
let infer_class_method_schemes (g0 : env) (c : Ast.class_decl)
  : (string * Types.scheme) list =
  (* クラス用の環境を作成：Prelude + フィールド型 *)
  let env_cls = clone g0 in
  (* 1) フィールド: var f = e; の型を推論し、単相で env_cls へ入れる *)
  List.iter (function
    | Ast.VarDecl (name, rhs) ->
        let t = infer_expr env_cls rhs in
        let sch = generalize (Types.ftv_env env_cls) t in
        set_var_scheme env_cls name sch
    | _ -> ()
  ) c.Ast.fields;
  (* 2) 各メソッドの仮引数に新しい型変数を割り当てて body をチェック *)
  let infer_one (m : Ast.method_decl) : (string * Types.scheme) =
    (* ローカル環境: クラスのフィールド・プリミティブを含み、self も束縛 *)
    let env_m = clone env_cls in
    set_var_scheme env_m "self" (Forall ([], TActor(c.Ast.cname,env_m)));
    (* 仮引数を新しい型変数で束縛（モノモルフィックに） *)
    let param_tys =
      List.map
        (fun p ->
           let a = fresh_tvar () in
           set_var_scheme env_m p (Forall ([ (* no generics at binding *) ], TVar a));
           TVar a)
        m.Ast.params
    in
   (* 本体を型検査：パラメタの TVar が使用により具体化される *)
    let () = check_stmt env_m m.Ast.body in
    let inst_param_tys =
      List.map
        (fun p ->
           let sch = get_var_scheme_exn env_m p in
           repr (instantiate sch)
        ) m.Ast.params
    in
    let tfun = TFun (inst_param_tys, TUnit) in
    let sch  = generalize env_cls tfun in
    (m.Ast.mname, sch)
  in
  List.map infer_one c.Ast.methods
*)
(* すべてのクラスについてメソッド型（スキーム）を事前に推論して登録する *)
let preinfer_all_classes (p : Ast.program) (g0 : Types.tenv) : unit =
  let infer_one_class (c : Ast.class_decl) : (string * Types.scheme) list =
    let env_cls = clone g0 in
    (* フィールドを先に単相で env_cls へ *)
    List.iter (function
      | Ast.VarDecl (name, rhs) ->
          let t = infer_expr env_cls rhs in
          let sch = generalize (ftv_env env_cls) t in
          set_var_scheme env_cls name sch
      | _ -> ()
    ) c.Ast.fields;
    let infer_method (m : Ast.method_decl) =
      let env_m = clone env_cls in
      (* self : TObject cls *)
(*      set_var_scheme env_m "self" (Types.Forall ([], Types.TActor(c.Ast.cname,[])));   by kodama *)
      (* 仮引数を新しい型変数で束縛 *)
      let ps =
        List.map (fun p -> let a = Types.fresh_tvar () in
                           set_var_scheme env_m p (Types.Forall ([], Types.TVar a));
                           Types.TVar a) m.Ast.params
      in
      (* 本文を型チェックして各 TVar を具体化させる *)
      check_stmt env_m m.Ast.body;
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

(* プログラム全体のクラス定義を走査し、メソッド型スキームを Typing_env へ登録 *)
(* let preinfer_all_classes (p : Ast.program) (g0 : env) : unit =
  List.iter (function
    | Ast.Class c ->
        let sigs = infer_class_method_sounds g0 c in
        Typing_env.register_class_method_schemes c.Ast.cname sigs
    | _ -> ()
  ) p
*)

let check_program (p: Ast.program) : (Types.tenv, string) result =
  let env0 = Typing_env.prelude () in
  try
    preinfer_all_classes p env0;           (* ★ 先に全クラスのメソッド型を登録 *)
    List.iter (check_decl env0) p;          (* それから通常どおりトップレベルを検査 *)
    Ok env0
  with
  | Types.Type_error msg -> Error msg

(* let check_program (p:program) : (Typing_env.env, string) result =
  let env = Typing_env.prelude () in
  try
    (* ★ まずクラス宣言を走査してメソッド型を前計算し、Typing_env に登録 *)
    List.iter (function
      | Class c ->
          let sigs = infer_class_method_schemes env c in
          Typing_env.register_class_method_schemes c.cname sigs
      | _ -> ()
    ) p;
    (* その後、通常どおり宣言や本文を型検査（send などもメソッド型を使ってチェック可能） *)
    List.iter (check_decl env) p;
    Ok env
  with
  | Type_error msg -> Error msg
*)
(* let check_program (p:program) : (Typing_env.env, string) result =
  let env = Typing_env.prelude () in
  try
    List.iter (check_decl env) p;
    Ok env
  with
  | Type_error msg -> Error msg
*)
