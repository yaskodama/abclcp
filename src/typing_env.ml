(* typing_env.ml *)
(* ==== 前提: Types を開く ==== *)
open Types  (* ty, scheme(=Forall), TVar, fresh_tvar, など *)

(* 環境の型：名前 -> スキーム(オーバーロード)のリスト *)
type env = (string, scheme list) Hashtbl.t

let add (e:env) (name:string) (sch:scheme) : unit =
  let prev = match Hashtbl.find_opt e name with Some xs -> xs | None -> [] in
  Hashtbl.replace e name (sch :: prev)

(* actor_table を表示するためのフック。
   デフォルトは no-op。Eval_thread 側で実体をセットする。 *)
let actor_table_printer : (unit -> unit) ref = ref (fun () -> ())

let set_actor_table_printer (f : unit -> unit) : unit =
  actor_table_printer := f

let debug_print_actor_table () : unit =
  (!actor_table_printer) ()

let empty_env () : env = Hashtbl.create 97

let add_mono (e:env) (name:string) (t:ty) : unit =
  let prev = match Hashtbl.find_opt e name with Some xs -> xs | None -> [] in
  Hashtbl.replace e name (Forall ([], t) :: prev)

let add_poly (e:env) (name:string) (sch:scheme) : unit =
  let prev = match Hashtbl.find_opt e name with Some xs -> xs | None -> [] in
  Hashtbl.replace e name (sch :: prev)

let find_all (e:env) (name:string) : scheme list =
  match Hashtbl.find_opt e name with Some xs -> xs | None -> []

let prelude () : env =
  let e = empty_env () in

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

(*  Types.register_class "H" [
    ("greet", Types.TFun ([], Types.TUnit));
  ]; *)

(* クラス Hello の例：init(n:float) : unit / greet() : unit *)
(*  Types.register_class "Hello" [
    ("init",  Types.TFun ([Types.TFloat], Types.TUnit));
    ("greet", Types.TFun ([],             Types.TUnit));
  ]; *)

  (* ---- wait: sleep milliseconds ---- *)
  add_mono e "wait" (TFun ([TInt],   TUnit));
  add_mono e "wait" (TFun ([TFloat], TUnit));

  (* sdl_init : (float,float) -> unit  と (int,int) -> unit *)
  add_mono e "sdl_init" (TFun ([TFloat; TFloat], TUnit));
  add_mono e "sdl_init" (TFun ([TInt;   TInt  ], TUnit));

  (* sdl_clear : unit -> unit *)
  add_mono e "sdl_clear" (TFun ([], TUnit));

  (* sdl_present : unit -> unit *)
  add_mono e "sdl_present" (TFun ([], TUnit));

  (* sdl_line : (float,float,float,float) -> unit  と int 版 *)
  add_mono e "sdl_line" (TFun ([TFloat; TFloat; TFloat; TFloat], TUnit));
  add_mono e "sdl_line" (TFun ([TInt;   TInt;   TInt;   TInt  ], TUnit));

  (* sdl_erase_line : (float,float,float,float) -> unit  と int 版 *)
  add_mono e "sdl_erase_line" (TFun ([TFloat; TFloat; TFloat; TFloat], TUnit));
  add_mono e "sdl_erase_line" (TFun ([TInt;   TInt;   TInt;   TInt  ], TUnit));

  (* 3) typeof : 各型 or 多相。ここでは各型を列挙 *)
  add_mono e "typeof" (TFun ([TInt],    TString));
  add_mono e "typeof" (TFun ([TFloat],  TString));
  add_mono e "typeof" (TFun ([TBool],   TString));
  add_mono e "typeof" (TFun ([TString], TString));
  add_mono e "typeof" (TFun ([TUnit],   TString));
  add_mono e "typeof" (TFun ([TActor("Hello",[])],  TString));

  (* 要素型つき配列にも対応（多相にしたいなら下の多相版を使う） *)
  let a_to = fresh_tvar () in
  add_poly e "typeof" (Forall ([(!a_to).id], TFun ([TArray (TVar a_to)], TString)));
  let a_to = fresh_tvar () in
    add_poly e "typeof" (Forall ([(!a_to).id], TFun ([TVar a_to], TString)));
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
