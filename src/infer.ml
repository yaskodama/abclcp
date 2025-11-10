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
        "(" ^ String.concat ", " (List.map string_of_ty arg_tys) ^ ")"
      in
      raise (Type_error ("no overload of "^name^" matches "^sigstr))

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
    let _ = List.map (infer_expr env) args in
    let ms = Types.lookup_class_methods cls in
      TActor (cls, ms)
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

let rec check_stmt (env:env) (s:stmt) : unit =
  match s with
  | Assign (x, e) ->
    let t_rhs = infer_expr env e in
    (match Hashtbl.find_opt env x with
     | None ->
         let sch = generalize env t_rhs in
         set_var_scheme env x sch
     | Some [sch] ->
         (* 既存の型に RHS を合わせる：必要なら instantiate → unify *)
         let t_old = instantiate sch in
         unify t_old t_rhs;
         let sch' = generalize env t_rhs in   (* 代入後の型を更新（単相にしたいなら Forall([], t_rhs)）*)
         set_var_scheme env x sch'
     | Some _ ->
         raise (Type_error ("cannot assign to overloaded name: " ^ x)));
    ()
  | VarDecl (name, rhs) ->
      let t   = infer_expr env rhs in
      let sch = generalize env t in
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
  | Send (_tgt, _meth, args) ->
      (* まずは送信引数は float と仮定。将来、クラスのメソッド表を env に載せて精密化 *)
      List.iter (fun a -> unify (infer_expr env a) TFloat) args
  | _ -> ()                            (* フォールバックで静かにする *)

(* ---- shallow clone for env (string -> scheme list) ---- *)
let clone (e : (string, scheme list) Hashtbl.t) : (string, scheme list) Hashtbl.t =
  let e' = Hashtbl.create (Hashtbl.length e) in
  Hashtbl.iter (fun k v -> Hashtbl.replace e' k v) e;
  e'

let check_decl (env:env) = function
  | Class c ->
      (* 1) フィールドを env に載せる（既存でOK） *)
      List.iter (function
        | VarDecl (name, init) ->
            let t   = infer_expr env init in
            let sch = generalize env t in
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

let check_program (p:program) : (Typing_env.env, string) result =
  let env = Typing_env.prelude () in
  try
    List.iter (check_decl env) p;
    Ok env
  with
  | Type_error msg -> Error msg
