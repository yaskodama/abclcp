(* types.ml *)
type tvar = { id: int; mutable link : ty option }
and ty =
  | TVar of tvar ref
  | TInt
  | TFloat
  | TString
  | TBool
  | TUnit
  | TFun of ty list * ty
  | TActor of string * (string * ty) list
  | TArray of ty
  | TAny
  | TRecord of (string * ty) list

type scheme = Forall of int list * ty

exception Type_error of string

let counter = ref 0

let fresh_id =
  let r = ref 0 in
  fun () -> incr r; !r

let fresh_tvar () : tvar ref = ref { id = fresh_id (); link = None }


let class_methods : (string, (string * ty) list) Hashtbl.t = Hashtbl.create 17

let register_class (name : string) (methods : (string * ty) list) =
  Hashtbl.replace class_methods name methods

let lookup_class_methods name =
  match Hashtbl.find_opt class_methods name with
  | Some ms -> ms
  | None -> []

(* ========================================= *)
(* 代表元をたどって正規化する関数          *)
(* ========================================= *)

let rec repr (t : ty) : ty =
  match t with
  | TVar vref ->
      (* vref : tvar ref = ref { id; link } *)
      (match !vref with
       | { link = Some t' } ->
           (* リンク先を再帰的にたどり、最終的な代表へ *)
           let t'' = repr t' in
           (* 経路圧縮：この変数を直接代表へリンクさせる *)
           vref := { !vref with link = Some t'' };
           t''
       | _ ->
           (* 未束縛の型変数はそのまま返す *)
           t)
  | _ ->
      (* 型変数以外（int, float, arrayなど）はそのまま *)
      t

(* 代表元をたどって圧縮 *)
(* let rec repr (t : ty) : ty =
  match t with
  | TVar vref ->
      (match !vref with
       | { link = Some t' } ->
           let t'' = repr t' in
           vref := { !vref with link = Some t'' };   (* 経路圧縮 *)
           t''
       | _ -> t)
  | _ -> t   *)

(* ========================================= *)
(* 型 ty を文字列に変換する関数             *)
(* ========================================= *)

let rec string_of_ty (t : ty) : string =
  match repr t with
  | TInt      -> "int"
  | TFloat    -> "float"
  | TBool     -> "bool"
  | TString   -> "string"
  | TUnit     -> "unit"
  | TActor (name, methods) ->
      let ms =
        methods
        |> List.map (fun (m, t) -> m ^ " : " ^ string_of_ty t)
        |> String.concat "; "
      in
      "actor(" ^ name ^ ") {" ^ ms ^ "}"
  | TRecord fields ->
      let fs =
        fields
        |> List.map (fun (l,t) -> l ^ " : " ^ string_of_ty t)
        |> String.concat "; "
      in
      "{" ^ fs ^ "}"
  | TArray t1 -> Printf.sprintf "%s array" (string_of_ty t1)
  | TFun (ps, r) ->
    let ps_s =
      match ps with
      | [] -> "()"  (* ← 空引数は () *)
      | _  -> "(" ^ String.concat " * " (List.map string_of_ty ps) ^ ")"
    in
      ps_s ^ " -> " ^ string_of_ty r
  | TVar vref ->
      (match !vref.link with
       | Some t' -> string_of_ty t'          (* すでに束縛済みなら中身を展開 *)
       | None ->
           (* 未束縛の型変数は 'a1, 'a2 ... のように表示 *)
           Printf.sprintf "'a%d" (!vref).id)
  | TAny      -> "any"                   

(* occurs check: v が t 中に出現するか？ *)
let rec occurs (v : tvar ref) (t : ty) : bool =
  match repr t with
  | TVar v'      -> v == v'
  | TArray t1    -> occurs v t1
  | TFun(ps,r)   -> List.exists (occurs v) ps || occurs v r
  | _            -> false

let rec unify (t1 : ty) (t2 : ty) : unit =
  match repr t1, repr t2 with
  | t1, t2 when t1 == t2 -> ()
  | TVar v, t | t, TVar v ->
      if occurs v t then raise (Type_error "occurs check failed")
      else v := { !v with link = Some t }
  | TInt,   TInt
  | TFloat, TFloat
  | TBool,  TBool
  | TString,TString
  | TUnit,  TUnit
  | TActor(_,_), TActor (_,_) -> ()
  | TArray a, TArray b -> unify a b
  | TFun(ps1, r1), TFun(ps2, r2) ->
      if List.length ps1 <> List.length ps2 then raise (Type_error "arity mismatch");
      List.iter2 unify ps1 ps2; unify r1 r2
  | _ -> raise (Type_error "type mismatch")

(* 既存の unify を前提にしています。名前が違う場合は合わせてください *)
let unify_many (ps : ty list) (as_ : ty list) =
  try
    List.iter2 unify ps as_
  with Invalid_argument _ ->
    raise (Type_error (Printf.sprintf
      "arity mismatch: expected %d args, got %d"
      (List.length ps) (List.length as_)))

(* 受信側の型からメソッド型を見つける *)
let rec lookup_method_type (tobj : ty) (mname : string) : ty option =
  match tobj with
  | TActor (_nm, ms) ->
      List.assoc_opt mname ms
  | TRecord ms ->
      List.assoc_opt mname ms
  | _ ->
      None

(* 自由型変数集合（ID の集合） *)
module ISet = Set.Make(Int)

let union_list f xs =
  List.fold_left (fun acc x -> ISet.union acc (f x)) ISet.empty xs

(* ty の自由型変数集合 *)
let rec ftv_ty (t : ty) : ISet.t =
  match repr t with
  | TVar vref          -> ISet.singleton (!vref).id
  | TArray t1          -> ftv_ty t1
  | TFun (ps, r)       -> ISet.union (union_list ftv_ty ps) (ftv_ty r)
  | TAny               -> ISet.empty
  | (TInt | TFloat | TBool | TString | TUnit | TActor(_,_)) -> ISet.empty

(* scheme の自由型変数集合 = ty の自由変数から量化されたIDを除いたもの *)
let ftv_scheme (Forall (qs, t)) : ISet.t =
  let qs_set = List.fold_left (fun s q -> ISet.add q s) ISet.empty qs in
  ISet.diff (ftv_ty t) qs_set

(* 環境の自由型変数集合（env は名前→スキーマの “複数候補” を持つ想定） *)
type tenv = (string, scheme list) Hashtbl.t

let ftv_env (env : tenv) : ISet.t =
  Hashtbl.fold
    (fun _ schemes acc ->
       List.fold_left
         (fun acc sch -> ISet.union acc (ftv_scheme sch))
         acc schemes)
    env ISet.empty

(* 一般化: env に自由でない型変数を ∀ で量化する *)
let generalize (env : tenv) (t : ty) : scheme =
  let env_fv = ftv_env env in
  let t_fv   = ftv_ty t in
  let qs     = ISet.elements (ISet.diff t_fv env_fv) in
  Forall (qs, t)

(* インスタンス化: 量化されたIDを fresh TVar に差し替える *)
let instantiate (Forall (qs, t) : scheme) : ty =
  (* 量化ID -> 新規 ty の写像 *)
  let subst : (int, ty) Hashtbl.t = Hashtbl.create 8 in
  let qset =
    List.fold_left (fun s q -> ISet.add q s) ISet.empty qs
  in
  let rec inst (ty : ty) : ty =
    match repr ty with
    | TVar vref ->
        let id = (!vref).id in
        if ISet.mem id qset then
          (* 量化IDは fresh に置換（同じIDは同じ fresh を再利用） *)
          match Hashtbl.find_opt subst id with
          | Some u -> u
          | None ->
              let u = TVar (fresh_tvar ()) in
              Hashtbl.add subst id u;
              u
        else
          TVar vref
    | TArray t1      -> TArray (inst t1)
    | TFun (ps, ret) -> TFun (List.map inst ps, inst ret)
    | TAny               -> TAny
    | (TInt | TFloat | TBool | TString | TUnit | TActor(_,_)) as c -> c
  in
  inst t
