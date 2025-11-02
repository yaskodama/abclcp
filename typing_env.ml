(* typing_env.ml *)
(* ==== 前提: Types を開く ==== *)
open Types  (* ty, scheme(=Forall), TVar, fresh_tvar, など *)

(* 環境の型：名前 -> スキーム(オーバーロード)のリスト *)
type env = (string, scheme list) Hashtbl.t

let add (e:env) (name:string) (sch:scheme) : unit =
  let prev = match Hashtbl.find_opt e name with Some xs -> xs | None -> [] in
  Hashtbl.replace e name (sch :: prev)

let empty_env () : env = Hashtbl.create 97

let add_mono (e:env) (name:string) (t:ty) : unit =
  let prev = match Hashtbl.find_opt e name with Some xs -> xs | None -> [] in
  Hashtbl.replace e name (Forall ([], t) :: prev)

let add_poly (e:env) (name:string) (sch:scheme) : unit =
  let prev = match Hashtbl.find_opt e name with Some xs -> xs | None -> [] in
  Hashtbl.replace e name (sch :: prev)

let find_all (e:env) (name:string) : scheme list =
  match Hashtbl.find_opt e name with Some xs -> xs | None -> []

(* 初期ビルトイン環境 *)
let prelude () : env =
  let e = empty_env () in

  (* 1) 単項 math: float -> float *)
  let add_f1 f = add_mono e f (TFun ([TFloat], TFloat)) in
  List.iter add_f1
    [ "sin"; "cos"; "tan"; "asin"; "acos"; "atan";
      "sqrt"; "exp"; "log10"; "abs"; "floor"; "ceil"; "round" ];

  (* 2) print : ∀a. a -> unit （任意型を表示できる版） *)
  let a1 = fresh_tvar () in
  add_poly e "print" (Forall ([(!a1).id], TFun ([TVar a1], TUnit)));

  (* 2.5) 二項算術: float × float -> float *)
  let add_f2 f = add_mono e f (TFun ([TFloat; TFloat], TFloat)) in
  List.iter add_f2 [ "+"; "-"; "*"; "/" ];

  (* 2.6) 文字列連結: 片側が string なら string *)
  let a = fresh_tvar () in
  add_poly e "+" (Forall ([(!a).id], TFun ([TString; TVar a], TString)));
  let a = fresh_tvar () in
  add_poly e "+" (Forall ([(!a).id], TFun ([TVar a; TString], TString)));

  (* 3) typeof : 各型 or 多相。ここでは各型を列挙 *)
  add_mono e "typeof" (TFun ([TInt],    TString));
  add_mono e "typeof" (TFun ([TFloat],  TString));
  add_mono e "typeof" (TFun ([TBool],   TString));
  add_mono e "typeof" (TFun ([TString], TString));
  add_mono e "typeof" (TFun ([TUnit],   TString));
  add_mono e "typeof" (TFun ([TActor],  TString));
  (* 要素型つき配列にも対応（多相にしたいなら下の多相版を使う） *)
  let a_to = fresh_tvar () in
  add_poly e "typeof" (Forall ([(!a_to).id], TFun ([TArray (TVar a_to)], TString)));

  (* 4) 配列 API（要素型付き・多相） *)
  let a = fresh_tvar () in
  add_poly e "array_empty" (Forall ([(!a).id], TFun ([], TArray (TVar a))));
  let a = fresh_tvar () in
  add_poly e "array_len"   (Forall ([(!a).id], TFun ([TArray (TVar a)], TInt)));
  let a = fresh_tvar () in
  add_poly e "array_get"   (Forall ([(!a).id], TFun ([TArray (TVar a); TInt],   TVar a)));
  (* 添字が float で来るケースも許すならこちらも登録 *)
  let a = fresh_tvar () in
  add_poly e "array_get"   (Forall ([(!a).id], TFun ([TArray (TVar a); TFloat], TVar a)));
  let a = fresh_tvar () in
  add_poly e "array_set"   (Forall ([(!a).id], TFun ([TArray (TVar a); TInt;   TVar a], TArray (TVar a))));
  let a = fresh_tvar () in
  add_poly e "array_set"   (Forall ([(!a).id], TFun ([TArray (TVar a); TFloat; TVar a], TArray (TVar a))));
  let a = fresh_tvar () in
  add_poly e "array_push"  (Forall ([(!a).id], TFun ([TArray (TVar a); TVar a], TArray (TVar a))));

  e
