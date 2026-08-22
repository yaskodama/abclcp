(* types.ml *)
open Location

(* 効果の名前と、メソッドの効果キー（"クラス名#メソッド名"）を入れる集合。
   ty が TFuture で参照するので、型定義より前に置く。 *)
module SSet = Set.Make(String)

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
  (* future<τ ! ε>。ε は「この future を await した側が負う効果」で、
     呼ばれる側のメソッド（"クラス名#メソッド名"）の集合として持つ。
     実効果は method_effs 側で本体検査中に育つので、ここでは名前で参照し、
     await の地点で now と同じ辺を張る。集合にしてあるのは、
     別々の呼び出し由来の future が単一化されうるため。 *)
  | TFuture of ty * SSet.t ref
  (* result<τ>。期限つきの待ちで else を書かなかったときの型。
     成功した値か、期限切れかを区別する。組込みの is_ok / value で取り出す。 *)
  | TResult of ty
  (* reply<τ>。返信先を値として持つ型（ABCL/1 の reply destination）。
     線形に扱う ---- ちょうど一度 answer するか、他へ渡して義務を移す。 *)
  | TReply of ty
  | TAny
  | TRecord of (string * ty) list
and scheme = Forall of int list * ty

exception Type_error of Location.t * string
let type_error ?(loc=Location.dummy) msg = raise (Type_error (loc, msg))

let counter = ref 0
let next_scheme_var = ref 0

let fresh_id =
  let r = ref 0 in
  fun () -> incr r; !r

let next_tvar = ref 0
let fresh_tvar () =
  let id = !next_tvar in
  incr next_tvar;
  ref { id; link = None }

(* スキーム用の新しい型変数ID（int）を発行するカウンタ *)
let fresh_scheme_var () =
  let v = !next_scheme_var in
  incr next_scheme_var;
  v

(* n 個の新しい int 型変数IDを作る：Forall([id0; id1; ...], ty) 用 *)
let freshes (n : int) : int list =
  let rec go k acc =
    if k = n then List.rev acc
    else go (k + 1) (fresh_scheme_var () :: acc)
  in
  go 0 []

(* ======================================== *)
(*  クラス -> (メソッド名 × 型スキーム) 表 *)
(* ======================================== *)

(* ====== クラスのメソッド型レジストリ ===== *)

(* クラス名 → (メソッド名 × 型スキーム) のリスト *)
let class_method_schemes : (string, (string * scheme) list) Hashtbl.t = Hashtbl.create 97

(* preinfer_all_classes から呼ぶ登録関数 *)
let register_class_method_schemes (cls : string) (sigs : (string * scheme) list) : unit =
  Hashtbl.replace class_method_schemes cls sigs

let lookup_method_scheme (cls : string) (mname : string) : scheme option =
  match Hashtbl.find_opt class_method_schemes cls with
  | None -> None
  | Some lst ->
      (try Some (List.assoc mname lst) with Not_found -> None)

let register_class (name : string) (methods : (string * scheme) list) : unit =
  Hashtbl.replace class_method_schemes name methods


(* 1つのメソッドだけ取り出す（send や New の init で使用） *)
let lookup_class_method_scheme (cls : string) (mname : string) : scheme option =
  match Hashtbl.find_opt class_method_schemes cls with
  | None -> None
  | Some lst -> List.assoc_opt mname lst

(* ★ ここがポイント：引数個数 arity から、tvar ref と その id を同時に作る *)
let register_class_auto (name : string) (methods_arity : (string * int) list) : unit =
  let ms =
    methods_arity
    |> List.map (fun (m, arity) ->
         (* arity 個の tvar ref を作る *)
         let tvars : tvar ref list =
           let rec go k acc =
             if k = arity then List.rev acc
             else go (k+1) (fresh_tvar () :: acc)
           in
           go 0 []
         in
         let qs : int list    = List.map (fun tv -> (!tv).id) tvars in
         let params : ty list = List.map (fun tv -> TVar tv) tvars in
         let ty : ty          = TFun (params, TUnit) in
         (m, Forall (qs, ty))
       )
  in
    register_class name ms

(* ================================================================= *)
(*  メソッド戻り値型テーブル：reply から推論される ρ の置き場所        *)
(* ================================================================= *)
(* "クラス名#メソッド名" -> ρ。
   ρ は単相の型変数で、そのメソッドの
     - すべての reply(v) 地点
     - すべての now / future 送信地点
   がこの同じ ρ を共有する。union-find の link 経由で伝播するので、
   どちらが先に検査されても制約は届く。

   ρ をメソッドの型スキームに埋めずに別表で持つのは generalize 対策である。
   Forall に ρ が量化されてしまうと instantiate が呼び出しごとに ρ を
   別の変数へ差し替えるため、reply 側で付いた制約が呼び出し側へ伝わらない。 *)
let method_ret_tys : (string, ty) Hashtbl.t = Hashtbl.create 97

let method_ret_key (cls : string) (m : string) : string = cls ^ "#" ^ m

let register_method_ret (cls : string) (m : string) (t : ty) : unit =
  Hashtbl.replace method_ret_tys (method_ret_key cls m) t

let lookup_method_ret (cls : string) (m : string) : ty option =
  Hashtbl.find_opt method_ret_tys (method_ret_key cls m)

(* REPL は同じプログラムを何度も型検査するので、
   前回の実行で確定済みの ρ を持ち越さないよう毎回クリアする *)
let reset_method_rets () : unit = Hashtbl.reset method_ret_tys

(* ================================================================= *)
(*  効果（effect）                                                    *)
(* ================================================================= *)
(* 既存の capability 分類（実行時メタデータとして 17 種あった）を
   静的に扱うための効果集合。プロファイル分離、境界の方向の規律、
   外部流出の保証がすべてこの上に乗る。

     mut   自分の状態（フィールド）を書き換える
     time  時刻の取得・待機
     io    装置への入出力
     mem   動的割り付け（new、配列の伸長、アクター生成）
     net   ノード外への通信
     ai    モデル推論（機外へ出るものは net も併記する）
     fs    永続化
     log   観測のみの出力

   ai と net を分けるのが要点。オンデバイス推論は {ai} だけを持ち
   net を持たないので、「AI を使うが機外へは出ない」がシグネチャに現れる。 *)
(* SSet は ty の定義より前に置いてある（future が効果キー集合を持つため） *)

let all_effects = ["mut"; "time"; "io"; "mem"; "net"; "ai"; "fs"; "log"]

let eff_of_list (l : string list) : SSet.t =
  List.fold_left (fun s e -> SSet.add e s) SSet.empty l

let string_of_eff (e : SSet.t) : string =
  if SSet.is_empty e then "{}"
  else "{" ^ String.concat ", " (SSet.elements e) ^ "}"

(* "クラス名#メソッド名" -> そのメソッドが持つ効果。
   ρ と同じく可変で、本体検査中に育ち、そのあと now の連鎖に沿って
   不動点まで伝播させる。 *)
let method_effs : (string, SSet.t ref) Hashtbl.t = Hashtbl.create 97

(* now で待つ辺 (呼び出す側, 呼ばれる側)。効果の伝播に使う。
   send / future は待たないので辺を張らない。 *)
let now_edges : (string * string) list ref = ref []

let eff_key (cls : string) (m : string) : string = cls ^ "#" ^ m

let eff_cell (cls : string) (m : string) : SSet.t ref =
  let k = eff_key cls m in
  match Hashtbl.find_opt method_effs k with
  | Some r -> r
  | None -> let r = ref SSet.empty in Hashtbl.replace method_effs k r; r

let lookup_method_eff (cls : string) (m : string) : SSet.t =
  match Hashtbl.find_opt method_effs (eff_key cls m) with
  | Some r -> !r
  | None -> SSet.empty

let add_now_edge (caller : string) (callee : string) : unit =
  if not (List.mem (caller, callee) !now_edges) then
    now_edges := (caller, callee) :: !now_edges

(* now で待つ側は、待っている間の性質に責任を持つので
   呼ばれる側の効果を引き継ぐ。効果は増えるだけなので不動点で止まる。 *)
let propagate_effects () : unit =
  let changed = ref true in
  let guard = ref 0 in
  while !changed && !guard < 1000 do
    changed := false; incr guard;
    List.iter
      (fun (caller, callee) ->
        match Hashtbl.find_opt method_effs caller,
              Hashtbl.find_opt method_effs callee with
        | Some cr, Some ce ->
            let merged = SSet.union !cr !ce in
            if not (SSet.equal merged !cr) then (cr := merged; changed := true)
        | _ -> ())
      !now_edges
  done

(* now / await の辺（待つ側 -> 待たれる側）に閉路があれば、
   循環待ち＝デッドロックの可能性がある。
   この辺集合は効果の伝播のために既に作ってあるので、閉路検査はほぼ只である。
   保守的な検査であることに注意 ---- メソッド単位で見るので、
   別々の実体どうしなら実際には循環しない場合も拾う。
   遠隔配備先（deploy / remote）は見えないので、そこは守れない。 *)
let wait_cycle () : string list option =
  let succ = Hashtbl.create 32 in
  List.iter (fun (a, b) ->
    let cur = try Hashtbl.find succ a with Not_found -> [] in
    Hashtbl.replace succ a (b :: cur)) !now_edges;
  let state = Hashtbl.create 32 in     (* 0 未訪問 / 1 探索中 / 2 済み *)
  let found = ref None in
  let rec dfs path n =
    if !found <> None then () else
    match Hashtbl.find_opt state n with
    | Some 1 ->
        (* n から始まる閉路。path は逆順に積んである *)
        let rec take acc = function
          | [] -> acc
          | x :: _ when x = n -> n :: acc
          | x :: r -> take (x :: acc) r in
        found := Some (take [] path)
    | Some 2 -> ()
    | _ ->
        Hashtbl.replace state n 1;
        List.iter (dfs (n :: path))
          (try Hashtbl.find succ n with Not_found -> []);
        Hashtbl.replace state n 2
  in
  Hashtbl.iter (fun k _ -> if !found = None then dfs [] k) succ;
  !found

let reset_effects () : unit =
  Hashtbl.reset method_effs; now_edges := []

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
  | TResult t1 -> Printf.sprintf "result %s" (string_of_ty t1)
  | TReply t1 -> Printf.sprintf "reply %s" (string_of_ty t1)
  | TFuture (t1, ks) ->
      if SSet.is_empty !ks then Printf.sprintf "future %s" (string_of_ty t1)
      else Printf.sprintf "future %s ! {%s}" (string_of_ty t1)
             (String.concat ", " (SSet.elements !ks))
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
  | TFuture (t1, _) -> occurs v t1
  | TResult t1 -> occurs v t1
  | TReply t1 -> occurs v t1
  | TFun(ps,r)   -> List.exists (occurs v) ps || occurs v r
  | _            -> false

(* 異なるクラスのアクター型を単一化してしまう従来の挙動へ戻す逃げ道。
   既存コードが落ちたときの一時退避用で、既定は off。 *)
let lax_actor () : bool =
  match Sys.getenv_opt "AIOS_LAX_ACTOR" with
  | Some ("1" | "true" | "yes") -> true
  | _ -> false

let rec unify ?(loc = Location.dummy) (t1 : ty) (t2 : ty) : unit =
  match repr t1, repr t2 with
  | t1, t2 when t1 == t2 -> ()
  | TVar v, t
  | t, TVar v ->
      if occurs v t then
        raise (Type_error (loc, "occurs check failed"))
      else
        v := { !v with link = Some t }
  | TInt,    TInt
  | TFloat,  TFloat
  | TBool,   TBool
  | TString, TString
  | TUnit,   TUnit -> ()
  (* アクター型は名前で区別する。
     "?" は実行時の値から作られた未知のクラスなので、どちらとも合わせる
     （ActorRef から作られる TActor ("?", [])）。
     AIOS_LAX_ACTOR=1 で従来どおり無条件に成功させる。 *)
  | TActor (a, _), TActor (b, _) ->
      if lax_actor () || a = b || a = "?" || b = "?" then ()
      else
        raise (Type_error (loc,
          Printf.sprintf "actor type mismatch: actor(%s) vs actor(%s)" a b))
  | TArray a, TArray b ->
      unify ~loc a b  (* ★ loc を引き継ぐ *)
  | TResult a, TResult b -> unify ~loc a b
  | TReply a, TReply b -> unify ~loc a b
  | TFuture (a, ka), TFuture (b, kb) ->
      unify ~loc a b;
      (* 効果キーは和にして両方へ書き戻す。どちらの ref も他所から
         参照されうるので、片方だけ更新すると await 地点で取りこぼす。 *)
      let u = SSet.union !ka !kb in
      ka := u; kb := u
  | TFun (ps1, r1), TFun (ps2, r2) ->
      if List.length ps1 <> List.length ps2 then
        raise (Type_error (loc, "arity mismatch"));
      List.iter2 (unify ~loc) ps1 ps2;  (* ★ ここも loc 付き *)
      unify ~loc r1 r2                  (* ★ ここも loc 付き *)
  | _ ->
    if loc == Location.dummy then
      Printf.eprintf "DEBUG: type mismatch raised with Location.dummy\n%!";
    raise (Type_error (loc, "type mismatch"))

(* 受信側の型からメソッド型を見つける *)
let rec lookup_method_type (tobj : ty) (mname : string) : ty option =
  match tobj with
  | TActor (_nm, ms) ->
      List.assoc_opt mname ms
  | TRecord ms ->
      List.assoc_opt mname ms
  | _ ->
      None
(* --- 自由型変数集合 --- *)
module ISet = Set.Make(Int)

(* --- 再帰的置換ユーティリティ --- *)
let rec prune t =
  match t with
  | TVar tv ->
      (match (!tv).link with
       | None -> t
       | Some t' ->
           let t'' = prune t' in
           (!tv).link <- Some t'';
           t'')
  | TArray t1 -> TArray (prune t1)
  | TFuture (t1, ks) -> TFuture (prune t1, ks)
  | TResult t1 -> TResult (prune t1)
  | TReply t1 -> TReply (prune t1)
  | TRecord fs -> TRecord (List.map (fun (l,t1) -> (l, prune t1)) fs)
  | TActor (n,ms) -> TActor (n, List.map (fun (m,t1)->(m,prune t1)) ms)
  | TFun (ps,r) -> TFun (List.map prune ps, prune r)
  | _ -> t

let string_of_ty_pretty (t : ty) : string =
  (* TVar の id を 'a, 'b, … に割り当てて見やすくする *)
  let names : (int, string) Hashtbl.t = Hashtbl.create 16 in
  let next = ref 0 in
  let name_of id =
    match Hashtbl.find_opt names id with
    | Some n -> n
    | None ->
        let base = Char.code 'a' + (!next mod 26) in
        let suffix = !next / 26 in
        incr next;
        if suffix = 0 then Printf.sprintf "'%c" (Char.chr base)
        else Printf.sprintf "'%c%d" (Char.chr base) suffix
  in
  let rec go ty =
    match prune ty with
    | TVar v      -> name_of (!v).id
    | TArray t1   -> go t1 ^ "[]"
    | TFuture (t1, _) -> "future " ^ go t1
    | TResult t1 -> "result " ^ go t1
    | TReply t1 -> "reply " ^ go t1
    | TRecord fs  ->
        "{" ^ (fs |> List.map (fun (l,t)-> l ^ " : " ^ go t) |> String.concat "; ") ^ "}"
    | TActor(n,ms) ->
        "actor(" ^ n ^ ") { "
        ^ (ms |> List.map (fun (m,t)-> m ^ " : " ^ go t) |> String.concat "; ")
        ^ " }"
    | TFun(ps,r)  ->
        let ps_s =
          match ps with
          | [] -> "()"
          | _  -> "(" ^ (ps |> List.map go |> String.concat " * ") ^ ")"
        in
        ps_s ^ " -> " ^ go r
    | TInt        -> "int"
    | TFloat      -> "float"
    | TBool       -> "bool"
    | TString     -> "string"
    | TUnit       -> "unit"
    | TAny 	  -> "any"
in
  go t

let rec ftv_ty t =
  match prune t with
  | TVar tv ->
      (match (!tv).link with
       | None -> ISet.singleton (!tv).id
       | Some t' -> ftv_ty t')
  | TArray t1 -> ftv_ty t1
  | TFuture (t1, _) -> ftv_ty t1
  | TResult t1 -> ftv_ty t1
  | TReply t1 -> ftv_ty t1
  | TRecord fs ->
      List.fold_left (fun acc (_,t1)->ISet.union acc (ftv_ty t1)) ISet.empty fs
  | TActor (_n,ms) ->
      List.fold_left (fun acc (_,t1)->ISet.union acc (ftv_ty t1)) ISet.empty ms
  | TFun (ps,r) ->
      List.fold_left (fun acc ti->ISet.union acc (ftv_ty ti)) (ftv_ty r) ps
  | _ -> ISet.empty

let generalize (env_ftv : ISet.t) (t : ty) : scheme =
  let fv_t = ftv_ty t in
  let qs = ISet.elements (ISet.diff fv_t env_ftv) in
  Forall (qs, t)

let instantiate (Forall (qs, t)) : ty =
  let tbl : (int, tvar ref) Hashtbl.t = Hashtbl.create (List.length qs) in
  List.iter (fun q -> Hashtbl.replace tbl q (fresh_tvar ())) qs;
  let rec inst ty =
    match ty with
    | TInt | TFloat | TBool | TString | TAny | TUnit -> ty
    | TArray t1 -> TArray (inst t1)
    | TFuture (t1, ks) -> TFuture (inst t1, ks)
    | TResult t1 -> TResult (inst t1)
    | TReply t1 -> TReply (inst t1)
    | TRecord fs -> TRecord (List.map (fun (l,t1)->(l,inst t1)) fs)
    | TActor (n,ms) -> TActor (n, List.map (fun (m,t1)->(m,inst t1)) ms)
    | TFun (ps,r) -> TFun (List.map inst ps, inst r)
    | TVar tv ->
        let id = (!tv).id in
        match Hashtbl.find_opt tbl id with
        | Some tv' -> TVar tv'
        | None -> TVar tv
  in
  inst t

(* 表示用：具体化済みメソッド型リストを取り出す *)
let lookup_class_methods_inst (cls : string) : (string * ty) list =
  match Hashtbl.find_opt class_method_schemes cls with
  | None -> []
  | Some lst ->
      List.map
        (fun (m, sch) ->
           let ty = repr (instantiate sch) in
           (m, ty))
        lst

(* デバッグ：クラスごとのメソッドスキーム表を表示 *)
let debug_print_class_method_schemes () : unit =
  print_endline "[class_method_schemes]";
  Hashtbl.iter
    (fun cls sigs ->
       Printf.printf "class %s\n" cls;
       List.iter
         (fun (m, sch) ->
            let ty = repr (instantiate sch) in
            Printf.printf "  %s : %s\n" m (string_of_ty_pretty ty))
         sigs;)
(*       print_newline ()) *)
   class_method_schemes

(* デバッグ：reply から推論した戻り値型を表示する。
   'a のように未束縛のまま残っているものは
   「reply はあるが、その値の型がどこからも決まっていない」メソッドで、
   注釈を書くべき第一候補である。 *)
let debug_print_method_rets () : unit =
  print_endline "[method return types (inferred from reply)]";
  let items =
    Hashtbl.fold (fun k t acc -> (k, t) :: acc) method_ret_tys []
    |> List.sort (fun (a,_) (b,_) -> compare a b)
  in
  List.iter
    (fun (k, t) -> Printf.printf "  %s -> %s\n" k (string_of_ty_pretty (repr t)))
    items

(* 自由型変数: 量化された変数ID(qs)を t の自由変数集合から取り除く *)
let ftv_scheme (Forall (qs, t) : scheme) : ISet.t =
  let fv = ftv_ty t in
  List.fold_left (fun acc q -> ISet.remove q acc) fv qs

let union_list f xs =
  List.fold_left (fun acc x -> ISet.union acc (f x)) ISet.empty xs

(* 環境の自由型変数集合（env は名前→スキーマの “複数候補” を持つ想定） *)
type tenv = (string, scheme list) Hashtbl.t

let ftv_env (env : tenv) : ISet.t =
  Hashtbl.fold
    (fun _ schemes acc ->
       List.fold_left
         (fun acc sch -> ISet.union acc (ftv_scheme sch))
         acc schemes)
    env ISet.empty
