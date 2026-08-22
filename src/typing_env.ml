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

(* ================================================================= *)
(*  プリミティブ -> 効果                                              *)
(* ================================================================= *)
(* 既存の capability 分類（eval_thread の prim_specs に 17 種ある）を
   静的な効果へ写した表。分類を新たに設計するのではなく、
   すでにある分類を静的にしただけである。

   要点は ai と net を分けること。機外へ出るモデル呼び出しは両方を持つが、
   オンデバイス推論を足すときは {ai} だけを与えればよく、
   「AI を使うが機外へは出ない」がシグネチャに現れる。 *)
let prim_effs : (string, SSet.t) Hashtbl.t = Hashtbl.create 128

let set_eff (names : string list) (effs : string list) : unit =
  let e = eff_of_list effs in
  List.iter (fun n -> Hashtbl.replace prim_effs n e) names

let () =
  (* Core.Math / Core.Introspection / reply : 効果なし *)
  set_eff [ "sin";"cos";"tan";"asin";"acos";"atan";"sqrt";"exp";"log10";
            "abs";"floor";"ceil";"round";"typeof";"reply";"neg" ] [];
  (* Core.Array : 読みは効果なし、割り付けは mem *)
  set_eff [ "array_get"; "array_len" ] [];
  set_eff [ "array_empty"; "array_push"; "array_set" ] ["mem"];
  (* 配備はノード外へ出て、相手に割り付けさせる *)
  set_eff [ "deploy" ] ["net"; "mem"];
  set_eff [ "source_of" ] [];
  set_eff [ "node_allow" ] [];
  (* 資源の取得と解放は状態を変える *)
  set_eff [ "acquire"; "release" ] ["mut"];
  (* Console / AIOS.Kernel / AIOS.Event / Protocol.Session / Actor.Introspection *)
  set_eff [ "print" ] ["log"];
  set_eff [ "capabilities"; "capability_prims"; "aios_kernel"; "aios_actors";
            "aios_actor_info"; "aios_actor_methods"; "aios_mailbox_len";
            "actor_dump" ] ["log"];
  set_eff [ "aios_emit"; "aios_events"; "aios_events_since";
            "aios_event_count" ] ["log"];
  set_eff [ "protocol_define"; "protocol_start"; "protocol_use";
            "protocol_current"; "protocol_state"; "protocol_end";
            "protocol_events" ] ["log"];
  (* Time *)
  set_eff [ "wait" ] ["time"];
  (* UI.SDL : 装置への出力 *)
  set_eff [ "sdl_init"; "sdl_clear"; "sdl_line"; "sdl_erase_line";
            "sdl_present"; "sdl_line_c" ] ["io"];
  (* AIOS.Memory / AIOS.Task : 永続化 *)
  set_eff [ "aios_memory_put"; "aios_memory_get"; "aios_memory_has";
            "aios_memory_keys"; "aios_task_create"; "aios_task_set";
            "aios_task_get"; "aios_task_info"; "aios_tasks" ] ["fs"];
  (* AIOS.Model : モデル推論。機外へ出るので net も持つ *)
  set_eff [ "ai_call"; "ai_call_with_system"; "model_generate";
            "gemini_generate"; "openai_generate" ] ["ai"; "net"];
  (* AIOS.Remote / Web / AIOS.Service : ノード外への通信 *)
  set_eff [ "remote_review"; "remote_review_ja"; "remote_reviewer_host";
            "web_listen"; "web_expose";
            "aios_now"; "aios_future" ] ["net"];
  set_eff [ "aios_register_service"; "aios_services"; "aios_service_actor";
            "aios_service_info" ] ["log"];
  (* Actor : 動的生成 *)
  set_eff [ "spawn" ] ["mem"]

let prim_eff (name : string) : SSet.t =
  match Hashtbl.find_opt prim_effs name with
  | Some e -> e
  | None   -> SSet.empty      (* 未登録のプリミティブは効果なしと見なす *)

let prelude () : env =
  let e = empty_env () in

  let add_f1 f = add_mono e f (TFun ([TFloat], TFloat)) in
  List.iter add_f1
    [ "sin"; "cos"; "tan"; "asin"; "acos"; "atan";
      "sqrt"; "exp"; "log10"; "abs"; "floor"; "ceil"; "round" ];

  (* 2) print : ∀a. a -> unit （任意型を表示できる版） *)
  let a1 = fresh_tvar () in
  add_poly e "print" (Forall ([(!a1).id], TFun ([TVar a1], TUnit)));

  (* 3) result<τ> を扱う組込み。
     期限つきの待ちで else を書かないと result<τ> が返る。
     is_ok で成否を見て、value で中身を取り出す（既定値つき）。
     これが無いと「期限切れの値」と「正常な値」が区別できない。 *)
  let r1 = fresh_tvar () in
  add_poly e "is_ok" (Forall ([(!r1).id], TFun ([TResult (TVar r1)], TBool)));
  let r2 = fresh_tvar () in
  add_poly e "value"
    (Forall ([(!r2).id], TFun ([TResult (TVar r2); TVar r2], TVar r2)));
  let r3 = fresh_tvar () in
  add_poly e "timed_out" (Forall ([(!r3).id], TFun ([TResult (TVar r3)], TBool)));

  (* 返信先を値として扱う ---- answer(r, v) で返信する。
     r は reply<a>、v は a。線形性は別に検査する。 *)
  let q1 = fresh_tvar () in
  add_poly e "answer"
    (Forall ([(!q1).id], TFun ([TReply (TVar q1); TVar q1], TUnit)));

  (* メッシュ配備。ソースを送り、相手先で JIT して動かす。
     deploy は外へ出て相手に割り付けさせるので net と mem を持つ。 *)
  add_mono e "source_of" (TFun ([TString], TString));
  add_mono e "node_allow" (TFun ([TString; TString], TUnit));
  add_mono e "deploy" (TFun ([TString; TString; TString], TString));

  (* 資源の取得と解放。型は string -> unit だが、
     本体の中で対になっているかを別に検査する（順序つきの効果）。 *)
  add_mono e "acquire" (TFun ([TString], TUnit));
  add_mono e "release" (TFun ([TString], TUnit));

  (* AI-OS capability introspection *)
  add_mono e "capabilities" (TFun ([], TArray TString));
  add_mono e "capability_prims" (TFun ([TString], TArray TString));
  add_mono e "aios_kernel" (TFun ([], TString));
  add_mono e "aios_actors" (TFun ([], TArray TString));
  add_mono e "aios_actor_info" (TFun ([TString], TString));
  add_mono e "aios_actor_methods" (TFun ([TString], TArray TString));
  add_mono e "aios_mailbox_len" (TFun ([TString], TInt));
  add_mono e "aios_register_service" (TFun ([TString; TString], TUnit));
  add_mono e "aios_services" (TFun ([], TArray TString));
  add_mono e "aios_service_actor" (TFun ([TString], TString));
  add_mono e "aios_service_info" (TFun ([TString], TString));
  add_mono e "aios_now" (TFun ([TString; TString], TAny));
  add_mono e "aios_now" (TFun ([TString; TString; TString], TAny));
  add_mono e "aios_now" (TFun ([TString; TString; TFloat], TAny));
  add_mono e "aios_now" (TFun ([TString; TString; TFloat; TFloat], TAny));
  add_mono e "aios_now" (TFun ([TString; TString; TString; TString], TAny));
  let a = fresh_tvar () in
  add_poly e "aios_now" (Forall ([(!a).id], TFun ([TString; TString; TVar a], TAny)));
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  add_poly e "aios_now" (Forall ([(!a).id; (!b).id], TFun ([TString; TString; TVar a; TVar b], TAny)));
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  let c = fresh_tvar () in
  add_poly e "aios_now" (Forall ([(!a).id; (!b).id; (!c).id], TFun ([TString; TString; TVar a; TVar b; TVar c], TAny)));
  add_mono e "aios_future" (TFun ([TString; TString], TFuture (TAny, ref Types.SSet.empty)));
  add_mono e "aios_future" (TFun ([TString; TString; TString], TFuture (TAny, ref Types.SSet.empty)));
  add_mono e "aios_future" (TFun ([TString; TString; TFloat], TFuture (TAny, ref Types.SSet.empty)));
  add_mono e "aios_future" (TFun ([TString; TString; TFloat; TFloat], TFuture (TAny, ref Types.SSet.empty)));
  add_mono e "aios_future" (TFun ([TString; TString; TString; TString], TFuture (TAny, ref Types.SSet.empty)));
  let a = fresh_tvar () in
  add_poly e "aios_future" (Forall ([(!a).id], TFun ([TString; TString; TVar a], TFuture (TAny, ref Types.SSet.empty))));
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  add_poly e "aios_future" (Forall ([(!a).id; (!b).id], TFun ([TString; TString; TVar a; TVar b], TFuture (TAny, ref Types.SSet.empty))));
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  let c = fresh_tvar () in
  add_poly e "aios_future" (Forall ([(!a).id; (!b).id; (!c).id], TFun ([TString; TString; TVar a; TVar b; TVar c], TFuture (TAny, ref Types.SSet.empty))));
  add_mono e "aios_emit" (TFun ([TString], TInt));
  add_mono e "aios_events" (TFun ([], TArray TString));
  add_mono e "aios_events_since" (TFun ([TInt], TArray TString));
  add_mono e "aios_events_since" (TFun ([TFloat], TArray TString));
  add_mono e "aios_event_count" (TFun ([], TInt));
  add_mono e "aios_memory_put" (TFun ([TString; TString], TUnit));
  add_mono e "aios_memory_get" (TFun ([TString], TString));
  add_mono e "aios_memory_has" (TFun ([TString], TBool));
  add_mono e "aios_memory_keys" (TFun ([], TArray TString));
  add_mono e "aios_task_create" (TFun ([TString], TString));
  add_mono e "aios_task_set" (TFun ([TString; TString; TString], TUnit));
  add_mono e "aios_task_get" (TFun ([TString; TString], TString));
  add_mono e "aios_task_info" (TFun ([TString], TString));
  add_mono e "aios_tasks" (TFun ([], TArray TString));
  add_mono e "protocol_define" (TFun ([TString; TString], TUnit));
  add_mono e "protocol_start" (TFun ([TString], TString));
  add_mono e "protocol_use" (TFun ([TString], TUnit));
  add_mono e "protocol_current" (TFun ([], TString));
  add_mono e "protocol_state" (TFun ([TString], TString));
  add_mono e "protocol_end" (TFun ([TString], TUnit));
  add_mono e "protocol_events" (TFun ([], TArray TString));
  add_mono e "model_generate" (TFun ([TString; TString], TString));
  add_mono e "ai_call" (TFun ([TString], TString));
  add_mono e "ai_call_with_system" (TFun ([TString; TString], TString));
  add_mono e "gemini_generate" (TFun ([TString], TString));
  add_mono e "openai_generate" (TFun ([TString], TString));
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  add_poly e "remote_review" (Forall ([(!a).id; (!b).id], TFun ([TString; TVar a; TVar b], TString)));
  add_mono e "remote_reviewer_host" (TFun ([], TString));
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  add_poly e "remote_review_ja" (Forall ([(!a).id; (!b).id], TFun ([TString; TVar a; TVar b], TString)));

  (* 2.5.1) 二項算術 *)
  let add_f2 f = add_mono e f (TFun ([TFloat; TFloat], TFloat)) in
  List.iter add_f2 [ "+"; "-"; "*"; "/" ];
  let add_f3 f = add_mono e f (TFun ([TInt; TInt], TInt)) in
  List.iter add_f3 [ "+"; "-"; "*" ];
  (* 整数除算は行わない。int / int も float を返す（評価器の apply_binop に合わせる）。
     ここを (int * int) -> int にすると 7 / 2 の型が int、値が 3.5 になって食い違う。 *)
  add_mono e "/" (TFun ([TInt; TInt], TFloat));

  (* 2.5.2) 二項関係 *)
  let add_f4 f = add_mono e f (TFun ([TFloat; TFloat], TBool)) in
  List.iter add_f4 [ ">"; "<"; "<="; ">=" ];
  let add_f5 f = add_mono e f (TFun ([TInt; TInt], TBool)) in
  List.iter add_f5 [ ">"; "<"; "<="; ">=" ];

  (* 2.5.3) 等値。数値・文字列・真偽値のそれぞれで比較できる。
     候補は4つあるが戻り値はすべて bool なので、両辺が未束縛でも
     曖昧にはならない（pick_overload は戻り値型が割れたときだけ曖昧と言う）。 *)
  let add_eq f =
    add_mono e f (TFun ([TInt;    TInt],    TBool));
    add_mono e f (TFun ([TFloat;  TFloat],  TBool));
    add_mono e f (TFun ([TString; TString], TBool));
    add_mono e f (TFun ([TBool;   TBool],   TBool))
  in
  List.iter add_eq [ "=="; "!=" ];

  (* 2.5.4) 単項マイナス。文法は - e を neg(e) へ落とす *)
  add_mono e "neg" (TFun ([TInt],   TInt));
  add_mono e "neg" (TFun ([TFloat], TFloat));

  (* 2.6) 文字列連結は ++ （+ からは外した）。
     + に string の overload を混ぜていたせいで、両辺が未束縛の a + b に
     principal type が無くなり、('a * string) -> string が既定で選ばれていた。
     ++ は両辺を文字列化するので候補は1つだけ、曖昧さは生じない。 *)
  let a = fresh_tvar () in
  let b = fresh_tvar () in
  add_poly e "++"
    (Forall ([(!a).id; (!b).id], TFun ([TVar a; TVar b], TString)));

  (* reply : 'a -> unit  （まずは多相でもOK。型が厳しいなら int/float/string の overload に） *)
  let a = fresh_tvar () in
    add_poly e "reply" (Forall ([(!a).id], TFun([TVar a], TUnit)));
(*  add_mono e "reply" (TFun ([TInt], TUnit));
  add_mono e "reply" (TFun ([TFloat], TUnit));
  add_mono e "reply" (TFun ([TString], TUnit));  *)

  (* ---- web gateway ---- *)
  add_mono e "web_listen" (TFun ([TInt],   TUnit));
  add_mono e "web_listen" (TFun ([TFloat], TUnit));   (* float も許すなら *)
  add_mono e "web_expose" (TFun ([TString; TString], TUnit));

  (* ---- wait: sleep milliseconds ---- *)
  add_mono e "wait" (TFun ([TInt],   TUnit));
  add_mono e "wait" (TFun ([TFloat], TUnit));

  (* sdl_init : (float,float) -> unit  と (int,int) -> unit *)
  add_mono e "sdl_init" (TFun ([TFloat; TFloat], TUnit));
  add_mono e "sdl_init" (TFun ([TInt;   TInt  ], TUnit));

  add_mono e "spawn" (TFun ([TString; TString], TUnit));

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
(*  let a_to = fresh_tvar () in
    add_poly e "typeof" (Forall ([(!a_to).id], TFun ([TArray (TVar a_to)], TString))); *)
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
