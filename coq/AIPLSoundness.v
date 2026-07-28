(*
  AIPL^- : AIPL (ABCL/c+) のうち、型健全性と型安全性が証明できる範囲

  実装 (src/ast.ml, src/types.ml, src/infer.ml, src/eval_thread.ml) の
  actor コアを取り出し、証明が通る形に一箇所だけ言語を変更したものである。

  変更点（これが AIPL^- を「マイナーバージョン」たらしめる点）:

    メソッドに返り値型を宣言させ、reply(v) を「メソッド本体の値」とした。
    現行実装では method の返り値型が AST に無く、reply と now/future の
    戻り値が型で結ばれていないため now : any, future : future any になっている。
    この一点を直すと、future/await を含めた完全な型健全性が証明できる。

  形式化した範囲:
    - 変数、局所変数束縛 (var x = e)、代入補題
    - オブジェクト store（フィールド状態）とその型不変条件
    - クラス表・メソッド表（引数型と返り値型）
    - メールボックスと非同期 send の small-step 意味論
    - future 表、future send、await、reply（= 本体の値）
    - 動的な actor 生成 (new C)

  形式化から外した範囲:
    any, send!, remote actor, sender, become, select, 配列, レコード,
    overload, 多相（型スキーム）, timeout, protocol/session

  主定理:
    no_method_not_understood  型の付いた構成を飛ぶメッセージは、宛先が実在し、
                              そのクラスがそのメソッドを持ち、引数と future の
                              型も合っている
    preservation              構成が一歩進んでも conf_ok が保たれる
    progress                  型の付いた構成は、終状態か、一歩進めるか、
                              全タスクが await で待っている（デッドロック）か
    type_safety               型の付いた構成から到達できる構成は stuck でない
    state_type_invariant      どの時点でも各 actor の状態は宣言型を持つ
    future_type_invariant     解決済み future の値は宣言された返り値型を持つ
                              （= reply と now/future の戻り値型の一致）
*)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

(* ================================================================= *)
(* 1. 型と式                                                         *)
(* ================================================================= *)

Inductive ty : Type :=
| TInt   : ty
| TBool  : ty
| TUnit  : ty
| TActor : nat -> ty        (* actor[c] : クラス c の actor *)
| TFut   : ty -> ty.        (* future t *)

Inductive tm : Type :=
| ENum   : nat -> tm
| EBool  : bool -> tm
| EUnit  : tm
| EVar   : nat -> tm
| ESelf  : tm
| EORef  : nat -> tm                  (* 実行時のみ: actor 参照 *)
| EFRef  : nat -> tm                  (* 実行時のみ: future 参照 *)
| EAdd   : tm -> tm -> tm
| ELt    : tm -> tm -> tm
| EIf    : tm -> tm -> tm -> tm
| ELet   : nat -> tm -> tm -> tm      (* var x = e1; e2 *)
| EGet   : tm                         (* 自分の状態を読む *)
| ESet   : tm -> tm                   (* 自分の状態を書く *)
| ENew   : nat -> tm                  (* new C *)
| EFSend : tm -> nat -> tm -> tm      (* future t.m(e) *)
| EAwait : tm -> tm.

(* 糖衣:
     e1 ; e2            = ELet fresh e1 e2      (fresh は e2 に現れない)
     send t.m(e)        = ELet fresh (EFSend t m e) EUnit
     now t.m(e)         = EAwait (EFSend t m e)
   いずれも AIPL^- の式で書けるので、規則を増やす必要はない。 *)

Inductive value : tm -> Prop :=
| VNum  : forall n, value (ENum n)
| VBool : forall b, value (EBool b)
| VUnit : value EUnit
| VORef : forall o, value (EORef o)
| VFRef : forall k, value (EFRef k).

Fixpoint subst (x : nat) (v : tm) (t : tm) : tm :=
  match t with
  | EVar y        => if Nat.eqb y x then v else EVar y
  | ELet y e1 e2  => ELet y (subst x v e1)
                       (if Nat.eqb y x then e2 else subst x v e2)
  | EAdd a b      => EAdd (subst x v a) (subst x v b)
  | ELt  a b      => ELt  (subst x v a) (subst x v b)
  | EIf a b c     => EIf (subst x v a) (subst x v b) (subst x v c)
  | ESet a        => ESet (subst x v a)
  | EFSend a m b  => EFSend (subst x v a) m (subst x v b)
  | EAwait a      => EAwait (subst x v a)
  | _             => t
  end.

(* ================================================================= *)
(* 2. 実行時の構造                                                   *)
(* ================================================================= *)

Record heap := Heap {
  hot : list nat;            (* actor 番号 -> クラス番号 *)
  hst : list tm;             (* actor 番号 -> 現在の状態値 *)
  hft : list ty;             (* future 番号 -> その型 *)
  hfv : list (option tm)     (* future 番号 -> 解決済みの値 *)
}.

Definition msg  := (nat * nat * tm * nat)%type.   (* 宛先, メソッド, 引数, future *)
Definition task := (nat * nat * tm)%type.         (* self, 返す future, 式 *)
Definition conf := (heap * list msg * list task)%type.

(* リストの一点更新 *)
Fixpoint upd {A : Type} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _        => []
  | _ :: tl, 0   => x :: tl
  | h :: tl, S k => h :: upd tl k x
  end.

Lemma upd_length : forall A (l : list A) n x, length (upd l n x) = length l.
Proof. induction l; intros [|n] x; simpl; auto. Qed.

Lemma nth_upd_eq : forall A (l : list A) n x y,
  nth_error l n = Some y -> nth_error (upd l n x) n = Some x.
Proof.
  induction l; intros [|n] x y H; simpl in *; try discriminate; auto.
  eapply IHl; eauto.
Qed.

Lemma nth_upd_neq : forall A (l : list A) n m x,
  n <> m -> nth_error (upd l n x) m = nth_error l m.
Proof.
  induction l; intros [|n] [|m] x Hne; simpl; try reflexivity; try congruence.
  apply IHl. lia.
Qed.

(* 表の拡張 *)
Definition ext {A : Type} (l l' : list A) : Prop :=
  forall n x, nth_error l n = Some x -> nth_error l' n = Some x.

Lemma ext_refl : forall A (l : list A), ext l l.
Proof. unfold ext; auto. Qed.

Lemma ext_app : forall A (l l' : list A), ext l (l ++ l').
Proof.
  unfold ext. intros A l l' n x H.
  rewrite nth_error_app1; auto.
  apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma ext_trans : forall A (l1 l2 l3 : list A), ext l1 l2 -> ext l2 l3 -> ext l1 l3.
Proof. unfold ext; auto. Qed.

Lemma nth_app_last : forall A (l : list A) x,
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  intros. rewrite nth_error_app2 by lia.
  replace (length l - length l) with 0 by lia. reflexivity.
Qed.

(* 型環境 *)
Definition env := nat -> option ty.
Definition empty : env := fun _ => None.
Definition extend (G : env) (x : nat) (T : ty) : env :=
  fun y => if Nat.eqb y x then Some T else G y.

(* ================================================================= *)
(* 3. プログラム（クラス表）                                         *)
(* ================================================================= *)

Section AIPL.

Variable stype : nat -> ty.                       (* クラス c の状態の型 *)
Variable sinit : nat -> tm.                       (* クラス c の状態の初期値 *)
Variable mtab  : nat -> nat -> option (ty * ty).  (* c.m : 引数型 * 返り値型 *)
Variable mbody : nat -> nat -> tm.                (* c.m の本体。引数は EVar 0 *)
(* 起動時のオブジェクト表。メソッド本体はここに載っている actor を
   直接参照してよい（例: 哲学者がフォークを名前で知っている）。 *)
Variable ot0  : list nat.

(* ================================================================= *)
(* 4. 型付け                                                         *)
(* ================================================================= *)

(* ht ot ft C G e T :
     オブジェクト表 ot、future 表 ft のもとで、クラス C の本体の中で、
     型環境 G において式 e が型 T を持つ。 *)

Inductive ht (ot : list nat) (ft : list ty) (C : nat)
  : env -> tm -> ty -> Prop :=
| HNum  : forall G n, ht ot ft C G (ENum n) TInt
| HBool : forall G b, ht ot ft C G (EBool b) TBool
| HUnit : forall G,   ht ot ft C G EUnit TUnit
| HVar  : forall G x T, G x = Some T -> ht ot ft C G (EVar x) T
| HSelf : forall G, ht ot ft C G ESelf (TActor C)
| HORef : forall G o c, nth_error ot o = Some c -> ht ot ft C G (EORef o) (TActor c)
| HFRef : forall G k T, nth_error ft k = Some T -> ht ot ft C G (EFRef k) (TFut T)
| HAdd  : forall G a b, ht ot ft C G a TInt -> ht ot ft C G b TInt ->
                        ht ot ft C G (EAdd a b) TInt
| HLt   : forall G a b, ht ot ft C G a TInt -> ht ot ft C G b TInt ->
                        ht ot ft C G (ELt a b) TBool
| HIf   : forall G a b c T, ht ot ft C G a TBool ->
                            ht ot ft C G b T -> ht ot ft C G c T ->
                            ht ot ft C G (EIf a b c) T
| HLet  : forall G x e1 e2 T1 T2,
            ht ot ft C G e1 T1 ->
            ht ot ft C (extend G x T1) e2 T2 ->
            ht ot ft C G (ELet x e1 e2) T2
| HGet  : forall G, ht ot ft C G EGet (stype C)
| HSet  : forall G e, ht ot ft C G e (stype C) -> ht ot ft C G (ESet e) TUnit
| HNew  : forall G c, ht ot ft C G (ENew c) (TActor c)
| HSend : forall G e0 m e1 c ta tr,
            ht ot ft C G e0 (TActor c) ->
            mtab c m = Some (ta, tr) ->
            ht ot ft C G e1 ta ->
            ht ot ft C G (EFSend e0 m e1) (TFut tr)
| HAwait : forall G e T, ht ot ft C G e (TFut T) -> ht ot ft C G (EAwait e) T.

(* プログラム全体が型検査を通っていること。
   Section の Hypothesis なので、End で各定理の前提に変わる。公理ではない。 *)

Hypothesis sinit_value : forall c, value (sinit c).

Hypothesis sinit_ok : forall c ot ft C G, ht ot ft C G (sinit c) (stype c).

Hypothesis bodies_ok :
  forall c m ta tr, mtab c m = Some (ta, tr) ->
    forall ot ft, ext ot0 ot -> ht ot ft c (extend empty 0 ta) (mbody c m) tr.

(* ================================================================= *)
(* 5. 型付けの基本補題                                               *)
(* ================================================================= *)

(* 型環境の外延性 *)
Lemma ht_env_ext : forall ot ft C G1 G2 e T,
  (forall z, G1 z = G2 z) -> ht ot ft C G1 e T -> ht ot ft C G2 e T.
Proof.
  intros ot ft C G1 G2 e T Heq H. generalize dependent G2.
  induction H; intros G2 Heq; try (econstructor; eauto; fail).
  - constructor. rewrite <- Heq. assumption.
  - econstructor; [ eauto | ].
    apply IHht2. intros z. unfold extend. destruct (Nat.eqb z x); auto.
Qed.

(* オブジェクト表・future 表の拡張に対する単調性 *)
Lemma ht_mono : forall ot ft C G e T ot' ft',
  ht ot ft C G e T -> ext ot ot' -> ext ft ft' -> ht ot' ft' C G e T.
Proof.
  intros ot ft C G e T ot' ft' H. generalize dependent ft'. generalize dependent ot'.
  induction H; intros ot' ft' Ho Hf; try (econstructor; eauto; fail).
Qed.

(* 値の型付けはクラス文脈にも型環境にも依存しない *)
Lemma value_ht_indep : forall ot ft C G v T,
  value v -> ht ot ft C G v T -> forall C' G', ht ot ft C' G' v T.
Proof.
  intros ot ft C G v T Hv Ht. inversion Hv; subst; inversion Ht; subst;
    intros; econstructor; eauto.
Qed.

(* 代入補題 *)
Lemma substitution : forall ot ft C e T G x T1 v,
  ht ot ft C (extend G x T1) e T ->
  value v ->
  (forall C' G', ht ot ft C' G' v T1) ->
  ht ot ft C G (subst x v e) T.
Proof.
  intros ot ft C e. induction e; intros T G x T1 v Ht Hv Hvt;
    inversion Ht; subst; simpl; try (econstructor; eauto; fail).
  - (* EVar *)
    unfold extend in H1. destruct (Nat.eqb n x) eqn:E.
    + inversion H1; subst. apply Hvt.
    + constructor. assumption.
  - (* ELet *)
    destruct (Nat.eqb n x) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      econstructor; [ eapply IHe1; eauto | ].
      eapply ht_env_ext; [ | eassumption ].
      intros z. unfold extend. destruct (Nat.eqb z x); reflexivity.
    + econstructor; [ eapply IHe1; eauto | ].
      apply IHe2 with (T1 := T1); auto.
      eapply ht_env_ext; [ | eassumption ].
      intros z. unfold extend.
      destruct (Nat.eqb z n) eqn:E1; destruct (Nat.eqb z x) eqn:E2; try reflexivity.
      apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. subst.
      rewrite Nat.eqb_refl in E. discriminate.
Qed.

(* 標準形 *)
Lemma canon_int : forall ot ft C G v,
  value v -> ht ot ft C G v TInt -> exists n, v = ENum n.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_bool : forall ot ft C G v,
  value v -> ht ot ft C G v TBool -> exists b, v = EBool b.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_actor : forall ot ft C G v c,
  value v -> ht ot ft C G v (TActor c) ->
  exists o, v = EORef o /\ nth_error ot o = Some c.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_fut : forall ot ft C G v T,
  value v -> ht ot ft C G v (TFut T) ->
  exists k, v = EFRef k /\ nth_error ft k = Some T.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

(* ================================================================= *)
(* 6. 操作的意味論                                                   *)
(* ================================================================= *)

(* タスク一つの一歩。self は o。out は新たに送出されるメッセージ。 *)
Inductive tstep : heap -> nat -> tm -> heap -> list msg -> tm -> Prop :=
(* --- 基底規則 --- *)
| STAdd : forall H o n k,
    tstep H o (EAdd (ENum n) (ENum k)) H [] (ENum (n + k))
| STLt : forall H o n k,
    tstep H o (ELt (ENum n) (ENum k)) H [] (EBool (Nat.ltb n k))
| STIfT : forall H o e1 e2,
    tstep H o (EIf (EBool true) e1 e2) H [] e1
| STIfF : forall H o e1 e2,
    tstep H o (EIf (EBool false) e1 e2) H [] e2
| STLet : forall H o x v e,
    value v -> tstep H o (ELet x v e) H [] (subst x v e)
| STSelf : forall H o,
    tstep H o ESelf H [] (EORef o)
| STGet : forall H o v,
    nth_error (hst H) o = Some v -> tstep H o EGet H [] v
| STSet : forall H o v,
    value v ->
    tstep H o (ESet v) (Heap (hot H) (upd (hst H) o v) (hft H) (hfv H)) [] EUnit
| STNew : forall H o cn,
    tstep H o (ENew cn)
      (Heap (hot H ++ [cn]) (hst H ++ [sinit cn]) (hft H) (hfv H))
      [] (EORef (length (hot H)))
| STSend : forall H o o' m v cc ta tr,
    value v ->
    nth_error (hot H) o' = Some cc ->
    mtab cc m = Some (ta, tr) ->
    tstep H o (EFSend (EORef o') m v)
      (Heap (hot H) (hst H) (hft H ++ [tr]) (hfv H ++ [None]))
      [(o', m, v, length (hft H))]
      (EFRef (length (hft H)))
| STAwait : forall H o k v,
    nth_error (hfv H) k = Some (Some v) ->
    tstep H o (EAwait (EFRef k)) H [] v
(* --- 合同規則 --- *)
| STAdd1 : forall H o a b H' out a',
    tstep H o a H' out a' -> tstep H o (EAdd a b) H' out (EAdd a' b)
| STAdd2 : forall H o v b H' out b',
    value v -> tstep H o b H' out b' -> tstep H o (EAdd v b) H' out (EAdd v b')
| STLt1 : forall H o a b H' out a',
    tstep H o a H' out a' -> tstep H o (ELt a b) H' out (ELt a' b)
| STLt2 : forall H o v b H' out b',
    value v -> tstep H o b H' out b' -> tstep H o (ELt v b) H' out (ELt v b')
| STIf1 : forall H o a b c H' out a',
    tstep H o a H' out a' -> tstep H o (EIf a b c) H' out (EIf a' b c)
| STLet1 : forall H o x a b H' out a',
    tstep H o a H' out a' -> tstep H o (ELet x a b) H' out (ELet x a' b)
| STSet1 : forall H o a H' out a',
    tstep H o a H' out a' -> tstep H o (ESet a) H' out (ESet a')
| STSend1 : forall H o a m b H' out a',
    tstep H o a H' out a' -> tstep H o (EFSend a m b) H' out (EFSend a' m b)
| STSend2 : forall H o v m b H' out b',
    value v -> tstep H o b H' out b' -> tstep H o (EFSend v m b) H' out (EFSend v m b')
| STAwait1 : forall H o a H' out a',
    tstep H o a H' out a' -> tstep H o (EAwait a) H' out (EAwait a').

(* 未解決の future を待って止まっている状態 *)
Inductive awaiting (H : heap) : tm -> Prop :=
| AwHere : forall k, nth_error (hfv H) k = Some None -> awaiting H (EAwait (EFRef k))
| AwAdd1 : forall a b, awaiting H a -> awaiting H (EAdd a b)
| AwAdd2 : forall v b, value v -> awaiting H b -> awaiting H (EAdd v b)
| AwLt1  : forall a b, awaiting H a -> awaiting H (ELt a b)
| AwLt2  : forall v b, value v -> awaiting H b -> awaiting H (ELt v b)
| AwIf   : forall a b c, awaiting H a -> awaiting H (EIf a b c)
| AwLet  : forall x a b, awaiting H a -> awaiting H (ELet x a b)
| AwSet  : forall a, awaiting H a -> awaiting H (ESet a)
| AwSend1 : forall a m b, awaiting H a -> awaiting H (EFSend a m b)
| AwSend2 : forall v m b, value v -> awaiting H b -> awaiting H (EFSend v m b)
| AwAwait : forall a, awaiting H a -> awaiting H (EAwait a).

(* 構成の一歩 *)
Inductive cstep : conf -> conf -> Prop :=
(* タスクが一歩進む。送出されたメッセージはメールボックスに入る *)
| CTask : forall H ms ts1 o k e ts2 H' out e',
    tstep H o e H' out e' ->
    cstep (H, ms, ts1 ++ (o, k, e) :: ts2)
          (H', ms ++ out, ts1 ++ (o, k, e') :: ts2)
(* タスクが値になった。それが reply の値であり、future を解決する *)
| CFinish : forall H ms ts1 o k v ts2,
    value v ->
    cstep (H, ms, ts1 ++ (o, k, v) :: ts2)
          (Heap (hot H) (hst H) (hft H) (upd (hfv H) k (Some v)), ms, ts1 ++ ts2)
(* メッセージを配送し、メソッド本体を新しいタスクとして起こす *)
| CDeliver : forall H ms1 o m v k ms2 ts c ta tr,
    nth_error (hot H) o = Some c ->
    mtab c m = Some (ta, tr) ->
    cstep (H, ms1 ++ (o, m, v, k) :: ms2, ts)
          (H, ms1 ++ ms2, ts ++ [(o, k, subst 0 v (mbody c m))]).

Inductive csteps : conf -> conf -> Prop :=
| CSRefl : forall C, csteps C C
| CSStep : forall C1 C2 C3, cstep C1 C2 -> csteps C2 C3 -> csteps C1 C3.

(* ================================================================= *)
(* 7. 不変条件                                                       *)
(* ================================================================= *)

Definition heap_ok (H : heap) : Prop :=
  length (hst H) = length (hot H) /\
  length (hfv H) = length (hft H) /\
  (forall o c v, nth_error (hot H) o = Some c -> nth_error (hst H) o = Some v ->
     value v /\ forall C G, ht (hot H) (hft H) C G v (stype c)) /\
  (forall k T v, nth_error (hft H) k = Some T -> nth_error (hfv H) k = Some (Some v) ->
     value v /\ forall C G, ht (hot H) (hft H) C G v T).

Definition msg_ok (H : heap) (M : msg) : Prop :=
  let '(o, m, v, k) := M in
  exists c ta tr,
       nth_error (hot H) o = Some c
    /\ mtab c m = Some (ta, tr)
    /\ value v
    /\ (forall C G, ht (hot H) (hft H) C G v ta)
    /\ nth_error (hft H) k = Some tr.

Definition task_ok (H : heap) (t : task) : Prop :=
  let '(o, k, e) := t in
  exists c T,
       nth_error (hot H) o = Some c
    /\ nth_error (hft H) k = Some T
    /\ ht (hot H) (hft H) c empty e T.

Definition conf_ok (C : conf) : Prop :=
  let '(H, ms, ts) := C in
  heap_ok H /\
  ext ot0 (hot H) /\
  (forall M, In M ms -> msg_ok H M) /\
  (forall t, In t ts -> task_ok H t).

Definition terminal (C : conf) : Prop :=
  let '(_, ms, ts) := C in ms = [] /\ ts = [].

Definition blocked (C : conf) : Prop :=
  let '(H, ms, ts) := C in
  ms = [] /\ ts <> [] /\ forall o k e, In (o, k, e) ts -> awaiting H e.

Definition stuck (C : conf) : Prop :=
  ~ terminal C /\ ~ blocked C /\ ~ (exists C', cstep C C').

(* ================================================================= *)
(* 8. 局所進行性                                                     *)
(* ================================================================= *)

Lemma nth_error_ex : forall A (l : list A) n,
  n < length l -> exists x, nth_error l n = Some x.
Proof.
  intros A l n Hlt. destruct (nth_error l n) eqn:E; eauto.
  apply nth_error_None in E. lia.
Qed.

Lemma nth_error_lt : forall A (l : list A) n (x : A),
  nth_error l n = Some x -> n < length l.
Proof. intros. apply nth_error_Some. rewrite H. discriminate. Qed.

Lemma local_progress : forall H o c G e T,
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  ht (hot H) (hft H) c G e T ->
  (forall x, G x = None) ->
  value e \/ (exists H' out e', tstep H o e H' out e') \/ awaiting H e.
Proof.
  intros H o c G e T Hh Ho Ht.
  destruct Hh as [Hl1 [Hl2 [Hstok Hfvok]]].
  induction Ht; intros Hcl; try (left; constructor; fail).
  - (* HVar *) rewrite Hcl in H0. discriminate.
  - (* HSelf *) right. left. eauto using tstep.
  - (* HAdd *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_int _ _ _ _ _ Hv1 Ht1) as [n ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_int _ _ _ _ _ Hv2 Ht2) as [k ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STAdd2; [ constructor | eassumption ].
    + right. apply AwAdd2; [ constructor | assumption ].
  - (* HLt *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_int _ _ _ _ _ Hv1 Ht1) as [n ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_int _ _ _ _ _ Hv2 Ht2) as [k ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STLt2; [ constructor | eassumption ].
    + right. apply AwLt2; [ constructor | assumption ].
  - (* HIf *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + destruct (canon_bool _ _ _ _ _ Hv1 Ht1) as [[|] ->].
      * left. eauto using tstep.
      * left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HLet *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HGet *)
    right. left.
    assert (Hlt : o < length (hst H)).
    { rewrite Hl1. eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hlt) as [v Hv].
    exists H, (@nil msg), v. constructor. assumption.
  - (* HSet *)
    right.
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HNew *) right. left. eauto using tstep.
  - (* HSend *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_actor _ _ _ _ _ _ Hv1 Ht1) as [o' [-> Hoc]].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + left. eexists; eexists; eexists. eapply STSend; eassumption.
    + left. eexists; eexists; eexists. apply STSend2; [ constructor | eassumption ].
    + right. apply AwSend2; [ constructor | assumption ].
  - (* HAwait *)
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    2:{ right. left. eauto using tstep. }
    2:{ right. right. constructor. assumption. }
    destruct (canon_fut _ _ _ _ _ _ Hv Ht) as [k [-> Hk]].
    assert (Hlt : k < length (hfv H)).
    { rewrite Hl2. eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hlt) as [ov Hov].
    destruct ov as [v |].
    + right. left. exists H, (@nil msg), v. constructor. assumption.
    + right. right. constructor. assumption.
Qed.

(* ================================================================= *)
(* 9. 局所保存                                                       *)
(* ================================================================= *)

Lemma nth_app1_inv : forall A (l : list A) x n y,
  nth_error (l ++ [x]) n = Some y ->
  (n < length l /\ nth_error l n = Some y) \/ (n = length l /\ y = x).
Proof.
  intros A l x n y Hn.
  destruct (Nat.lt_ge_cases n (length l)) as [Hlt | Hge].
  - left. split; [ assumption | ]. rewrite <- Hn. symmetry.
    apply nth_error_app1. assumption.
  - right. rewrite nth_error_app2 in Hn by assumption.
    destruct (n - length l) as [| d] eqn:Ed; simpl in Hn.
    + inversion Hn. split; [ lia | reflexivity ].
    + destruct d; simpl in Hn; discriminate.
Qed.

(* heap_ok の射影 *)
Lemma heap_len_st : forall H, heap_ok H -> length (hst H) = length (hot H).
Proof. intros H [A _]; exact A. Qed.
Lemma heap_len_fv : forall H, heap_ok H -> length (hfv H) = length (hft H).
Proof. intros H [_ [A _]]; exact A. Qed.
Lemma heap_st_ok : forall H o c v, heap_ok H ->
  nth_error (hot H) o = Some c -> nth_error (hst H) o = Some v ->
  value v /\ forall C G, ht (hot H) (hft H) C G v (stype c).
Proof. intros H o c v [_ [_ [A _]]]; apply A. Qed.
Lemma heap_fv_ok : forall H k T v, heap_ok H ->
  nth_error (hft H) k = Some T -> nth_error (hfv H) k = Some (Some v) ->
  value v /\ forall C G, ht (hot H) (hft H) C G v T.
Proof. intros H k T v [_ [_ [_ A]]]; apply A. Qed.

(* 型付けの反転補題。証明を仮説名に依存させないため *)
Lemma ht_oref_inv : forall ot ft C G o T,
  ht ot ft C G (EORef o) T -> exists c, T = TActor c /\ nth_error ot o = Some c.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma ht_fref_inv : forall ot ft C G k T,
  ht ot ft C G (EFRef k) T -> exists T0, T = TFut T0 /\ nth_error ft k = Some T0.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma ht_add_inv : forall ot ft C G a b T,
  ht ot ft C G (EAdd a b) T ->
  T = TInt /\ ht ot ft C G a TInt /\ ht ot ft C G b TInt.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_lt_inv : forall ot ft C G a b T,
  ht ot ft C G (ELt a b) T ->
  T = TBool /\ ht ot ft C G a TInt /\ ht ot ft C G b TInt.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_if_inv : forall ot ft C G a b d T,
  ht ot ft C G (EIf a b d) T ->
  ht ot ft C G a TBool /\ ht ot ft C G b T /\ ht ot ft C G d T.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_let_inv : forall ot ft C G x e1 e2 T,
  ht ot ft C G (ELet x e1 e2) T ->
  exists T1, ht ot ft C G e1 T1 /\ ht ot ft C (extend G x T1) e2 T.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma ht_self_inv : forall ot ft C G T, ht ot ft C G ESelf T -> T = TActor C.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_get_inv : forall ot ft C G T, ht ot ft C G EGet T -> T = stype C.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_set_inv : forall ot ft C G e T,
  ht ot ft C G (ESet e) T -> T = TUnit /\ ht ot ft C G e (stype C).
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_new_inv : forall ot ft C G cn T, ht ot ft C G (ENew cn) T -> T = TActor cn.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_send_inv : forall ot ft C G e0 m e1 T,
  ht ot ft C G (EFSend e0 m e1) T ->
  exists c1 ta1 tr1, ht ot ft C G e0 (TActor c1)
                  /\ mtab c1 m = Some (ta1, tr1)
                  /\ ht ot ft C G e1 ta1
                  /\ T = TFut tr1.
Proof. intros. inversion H; subst. exists c, ta, tr. auto. Qed.
Lemma ht_await_inv : forall ot ft C G e T,
  ht ot ft C G (EAwait e) T -> ht ot ft C G e (TFut T).
Proof. intros. inversion H; subst; auto. Qed.

Ltac split5 := split; [ | split; [ | split; [ | split ] ] ].
Ltac split4 := split; [ | split; [ | split ] ].
Ltac lift := eapply ht_mono; [ eassumption | try assumption; apply ext_refl
                             | try assumption; apply ext_refl ].
Ltac nomsg := intros ? [].

Lemma local_preservation : forall H o c e T H' out e',
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  ht (hot H) (hft H) c empty e T ->
  tstep H o e H' out e' ->
  heap_ok H'
  /\ ext (hot H) (hot H')
  /\ ext (hft H) (hft H')
  /\ ht (hot H') (hft H') c empty e' T
  /\ (forall M, In M out -> msg_ok H' M).
Proof.
  intros H o c e T H' out e' Hh Ho Ht Hs.
  generalize dependent T. revert Ho. revert Hh.
  induction Hs; intros Hh Ho T Ht.
  - (* STAdd *)
    apply ht_add_inv in Ht as [-> _].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STLt *)
    apply ht_lt_inv in Ht as [-> _].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STIfT *)
    apply ht_if_inv in Ht as [_ [Hb _]].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STIfF *)
    apply ht_if_inv in Ht as [_ [_ Hd]].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STLet *)
    apply ht_let_inv in Ht as [T1 [Hv1 Hb]].
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    eapply substitution; [ eassumption | assumption | ].
    intros C' G'. eapply value_ht_indep; eassumption.
  - (* STSelf *)
    apply ht_self_inv in Ht as ->.
    split5; [ assumption | apply ext_refl | apply ext_refl
            | constructor; assumption | nomsg ].
  - (* STGet *)
    apply ht_get_inv in Ht as ->.
    destruct (heap_st_ok _ _ _ _ Hh Ho H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl | apply Hvt | nomsg ].
  - (* STSet *)
    apply ht_set_inv in Ht as [-> Hv0].
    assert (Hvt : forall C' G', ht (hot H) (hft H) C' G' v (stype c)).
    { intros C' G'. eapply value_ht_indep; eassumption. }
    assert (Hex : exists w, nth_error (hst H) o = Some w).
    { apply nth_error_ex. rewrite (heap_len_st _ Hh). eapply nth_error_lt; eauto. }
    destruct Hex as [w Hw].
    split5.
    + unfold heap_ok; simpl; split4.
      * rewrite upd_length. apply (heap_len_st _ Hh).
      * apply (heap_len_fv _ Hh).
      * intros o2 c2 v2 Hoc Hsv.
        destruct (Nat.eq_dec o2 o) as [-> | Hne].
        -- rewrite Ho in Hoc. inversion Hoc; subst.
           rewrite (nth_upd_eq _ _ _ _ _ Hw) in Hsv. inversion Hsv; subst.
           split; [ assumption | apply Hvt ].
        -- rewrite nth_upd_neq in Hsv by auto.
           apply (heap_st_ok _ _ _ _ Hh Hoc Hsv).
      * intros k2 T2 w2 Hk Hw2. apply (heap_fv_ok _ _ _ _ Hh Hk Hw2).
    + apply ext_refl.
    + apply ext_refl.
    + constructor.
    + nomsg.
  - (* STNew *)
    apply ht_new_inv in Ht as ->.
    assert (Hext : ext (hot H) (hot H ++ [cn])) by apply ext_app.
    split5.
    + unfold heap_ok; simpl; split4.
      * repeat rewrite length_app. rewrite (heap_len_st _ Hh). reflexivity.
      * apply (heap_len_fv _ Hh).
      * intros o2 c2 v2 Hoc Hsv.
        destruct (nth_app1_inv _ _ _ _ _ Hoc) as [[Hlt Hoc0] | [Heq Hc0]].
        -- rewrite nth_error_app1 in Hsv by (rewrite (heap_len_st _ Hh); lia).
           destruct (heap_st_ok _ _ _ _ Hh Hoc0 Hsv) as [Hvv Hvt].
           split; [ assumption | ].
           intros C' G'. eapply ht_mono; [ apply Hvt | assumption | apply ext_refl ].
        -- subst o2 c2. rewrite <- (heap_len_st _ Hh) in Hsv.
           rewrite nth_app_last in Hsv. inversion Hsv; subst.
           split; [ apply sinit_value | intros C' G'; apply sinit_ok ].
      * intros k2 T2 w2 Hk Hw2.
        destruct (heap_fv_ok _ _ _ _ Hh Hk Hw2) as [Hvv Hvt].
        split; [ assumption | ].
        intros C' G'. eapply ht_mono; [ apply Hvt | assumption | apply ext_refl ].
    + assumption.
    + apply ext_refl.
    + simpl. constructor. rewrite nth_app_last. reflexivity.
    + nomsg.
  - (* STSend *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Hto [Hmt [Htv ->]]]]]].
    apply ht_oref_inv in Hto as [c2 [Heq Hoc2]]. inversion Heq; subst c2.
    assert (Hcc : c1 = cc) by congruence. subst c1.
    assert (Hpair : (ta1, tr1) = (ta, tr)) by congruence.
    inversion Hpair; subst ta1 tr1.
    assert (Hextf : ext (hft H) (hft H ++ [tr])) by apply ext_app.
    assert (Hvt : forall C' G', ht (hot H) (hft H ++ [tr]) C' G' v ta).
    { intros C' G'. eapply ht_mono;
        [ eapply value_ht_indep; eassumption | apply ext_refl | assumption ]. }
    split5.
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * repeat rewrite length_app. rewrite (heap_len_fv _ Hh). reflexivity.
      * intros o2 c2 v2 Hoc Hsv.
        destruct (heap_st_ok _ _ _ _ Hh Hoc Hsv) as [Hvv Hv2].
        split; [ assumption | ].
        intros C' G'. eapply ht_mono; [ apply Hv2 | apply ext_refl | assumption ].
      * intros k2 T2 w2 Hk Hw2.
        destruct (nth_app1_inv _ _ _ _ _ Hw2) as [[Hlt Hw0] | [Heq2 Hbad]];
          [ | discriminate ].
        rewrite nth_error_app1 in Hk by (rewrite <- (heap_len_fv _ Hh); lia).
        destruct (heap_fv_ok _ _ _ _ Hh Hk Hw0) as [Hvv Hv2].
        split; [ assumption | ].
        intros C' G'. eapply ht_mono; [ apply Hv2 | apply ext_refl | assumption ].
    + apply ext_refl.
    + assumption.
    + simpl. constructor. rewrite nth_app_last. reflexivity.
    + intros M HM. simpl in HM. destruct HM as [<- | []].
      exists cc, ta, tr. simpl.
      split; [ assumption | ]. split; [ assumption | ]. split; [ assumption | ].
      split; [ apply Hvt | ]. rewrite nth_app_last. reflexivity.
  - (* STAwait *)
    apply ht_await_inv in Ht.
    apply ht_fref_inv in Ht as [T0 [Heq Hk]]. inversion Heq; subst T0.
    destruct (heap_fv_ok _ _ _ _ Hh Hk H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl | apply Hvt | nomsg ].
  - (* STAdd1 *)
    apply ht_add_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho TInt Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor; [ assumption | lift ].
  - (* STAdd2 *)
    apply ht_add_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho TInt Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. constructor; [ lift | assumption ].
  - (* STLt1 *)
    apply ht_lt_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho TInt Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor; [ assumption | lift ].
  - (* STLt2 *)
    apply ht_lt_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho TInt Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. constructor; [ lift | assumption ].
  - (* STIf1 *)
    apply ht_if_inv in Ht as [Ha [Hb Hd]].
    destruct (IHHs Hh Ho TBool Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor; [ assumption | lift | lift ].
  - (* STLet1 *)
    apply ht_let_inv in Ht as [T1 [Ha Hb]].
    destruct (IHHs Hh Ho T1 Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STSet1 *)
    apply ht_set_inv in Ht as [-> Ha].
    destruct (IHHs Hh Ho (stype c) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor. assumption.
  - (* STSend1 *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Hto [Hmt [Htv ->]]]]]].
    destruct (IHHs Hh Ho (TActor c1) Hto) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | eassumption | lift ].
  - (* STSend2 *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Hto [Hmt [Htv ->]]]]]].
    destruct (IHHs Hh Ho ta1 Htv) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. econstructor; [ lift | eassumption | eassumption ].
  - (* STAwait1 *)
    apply ht_await_inv in Ht.
    destruct (IHHs Hh Ho (TFut T) Ht) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor. assumption.
Qed.

(* ================================================================= *)
(* 10. 構成レベルの定理                                              *)
(* ================================================================= *)

Lemma msg_ok_mono : forall H H' M,
  msg_ok H M -> ext (hot H) (hot H') -> ext (hft H) (hft H') -> msg_ok H' M.
Proof.
  intros H H' [[[o m] v] k] Hm Ho Hf. simpl in *.
  destruct Hm as [c [ta [tr [A [B [Cv [D E]]]]]]].
  exists c, ta, tr.
  split; [ auto | ]. split; [ auto | ]. split; [ auto | ].
  split; [ | auto ].
  intros C' G'. eapply ht_mono; [ apply D | auto | auto ].
Qed.

Lemma task_ok_mono : forall H H' t,
  task_ok H t -> ext (hot H) (hot H') -> ext (hft H) (hft H') -> task_ok H' t.
Proof.
  intros H H' [[o k] e] Ht Ho Hf. simpl in *.
  destruct Ht as [c [T [A [B Cc]]]].
  exists c, T. split; [ auto | ]. split; [ auto | ].
  eapply ht_mono; [ apply Cc | auto | auto ].
Qed.

(* --- 定理 1: 理解できないメッセージは飛ばない --- *)
Theorem no_method_not_understood : forall H ms ts o m v k,
  conf_ok (H, ms, ts) ->
  In (o, m, v, k) ms ->
  exists c ta tr,
       nth_error (hot H) o = Some c
    /\ mtab c m = Some (ta, tr)
    /\ (forall C G, ht (hot H) (hft H) C G v ta)
    /\ nth_error (hft H) k = Some tr.
Proof.
  intros H ms ts o m v k [_ [_ [Hms _]]] Hin.
  destruct (Hms _ Hin) as [c [ta [tr [A [B [Cv [D E]]]]]]].
  exists c, ta, tr. auto.
Qed.

Lemma in_app_middle : forall A (x : A) l1 l2, In x (l1 ++ x :: l2).
Proof. intros. apply in_or_app. right. left. reflexivity. Qed.

(* --- 定理 2: 保存 --- *)
Theorem preservation : forall C C', conf_ok C -> cstep C C' -> conf_ok C'.
Proof.
  intros C C' Hok Hs. inversion Hs; subst; simpl in *;
    destruct Hok as [Hh [Hb [Hms Hts]]].
  - (* CTask *)
    assert (Hte : task_ok H (o, k, e)) by (apply Hts; apply in_app_middle).
    simpl in Hte. destruct Hte as [cc [T [Hoc [Hk Hte]]]].
    destruct (local_preservation _ _ _ _ _ _ _ _ Hh Hoc Hte H0)
      as [Hh' [Hxo [Hxf [Hte' Hout]]]].
    split; [ assumption | ]. split; [ eapply ext_trans; eassumption | ]. split.
    + intros M HM. apply in_app_or in HM. destruct HM as [HM | HM].
      * eapply msg_ok_mono; [ apply Hms; assumption | assumption | assumption ].
      * apply Hout. assumption.
    + intros t HT. apply in_app_or in HT. destruct HT as [HT | [Heq | HT]].
      * eapply task_ok_mono; [ apply Hts; apply in_or_app; left; eassumption
                            | assumption | assumption ].
      * subst t. simpl. exists cc, T. auto.
      * eapply task_ok_mono; [ apply Hts; apply in_or_app; right; right; eassumption
                            | assumption | assumption ].
  - (* CFinish *)
    assert (Hte : task_ok H (o, k, v)) by (apply Hts; apply in_app_middle).
    simpl in Hte. destruct Hte as [cc [T [Hoc [Hk Hte]]]].
    assert (Hvt : forall C' G', ht (hot H) (hft H) C' G' v T).
    { intros C' G'. eapply value_ht_indep; eassumption. }
    assert (Hkl : k < length (hfv H)).
    { rewrite (heap_len_fv _ Hh). eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hkl) as [ov Hov].
    split; [ | split; [ simpl; assumption | split ] ].
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * rewrite upd_length. apply (heap_len_fv _ Hh).
      * intros o2 c2 v2 A B. apply (heap_st_ok _ _ _ _ Hh A B).
      * intros k2 T2 w2 A B.
        destruct (Nat.eq_dec k2 k) as [-> | Hne].
        -- rewrite (nth_upd_eq _ _ _ _ _ Hov) in B. inversion B; subst.
           rewrite Hk in A. inversion A; subst.
           split; [ assumption | apply Hvt ].
        -- rewrite nth_upd_neq in B by auto.
           apply (heap_fv_ok _ _ _ _ Hh A B).
    + intros M HM. simpl. apply Hms. assumption.
    + intros t HT. simpl. apply Hts. apply in_app_or in HT.
      apply in_or_app. destruct HT as [HT | HT]; [ left; auto | right; right; auto ].
  - (* CDeliver *)
    assert (Hme : msg_ok H (o, m, v, k)) by (apply Hms; apply in_app_middle).
    simpl in Hme. destruct Hme as [c0 [ta0 [tr0 [A [B [Cv [D E]]]]]]].
    assert (Hc : c0 = c) by congruence. subst c0.
    assert (Hp : (ta0, tr0) = (ta, tr)) by congruence.
    inversion Hp; subst ta0 tr0.
    split; [ assumption | ]. split; [ assumption | ]. split.
    + intros M HM. apply Hms. apply in_app_or in HM.
      apply in_or_app. destruct HM as [HM | HM]; [ left; auto | right; right; auto ].
    + intros t HT. apply in_app_or in HT. destruct HT as [HT | [Heq | []]].
      * apply Hts. assumption.
      * subst t. simpl. exists c, tr.
        split; [ assumption | ]. split; [ assumption | ].
        eapply substitution;
          [ eapply bodies_ok; eassumption | assumption | ].
        intros C' G'. apply D.
Qed.

Theorem preservation_star : forall C C', conf_ok C -> csteps C C' -> conf_ok C'.
Proof.
  intros C C' Hok Hs. induction Hs; [ assumption | ].
  apply IHHs. eapply preservation; eassumption.
Qed.

(* --- 定理 3: 進行 --- *)
Lemma tasks_progress : forall H ts,
  heap_ok H ->
  (forall t, In t ts -> task_ok H t) ->
  (exists ts1 o k e ts2, ts = ts1 ++ (o, k, e) :: ts2 /\
      (value e \/ exists H' out e', tstep H o e H' out e'))
  \/ (forall o k e, In (o, k, e) ts -> awaiting H e).
Proof.
  intros H ts Hh. induction ts as [| t ts IH]; intros Hts.
  - right. intros o k e [].
  - destruct t as [[o k] e].
    assert (Hte : task_ok H (o, k, e)) by (apply Hts; left; reflexivity).
    simpl in Hte. destruct Hte as [c [T [Hoc [Hk Hte]]]].
    destruct (local_progress _ _ _ _ _ _ Hh Hoc Hte (fun _ => eq_refl))
      as [Hv | [Hst | Haw]].
    + left. exists (@nil task), o, k, e, ts. split; [ reflexivity | left; assumption ].
    + left. exists (@nil task), o, k, e, ts. split; [ reflexivity | right; assumption ].
    + destruct (IH (fun t Hin => Hts t (or_intror Hin))) as [Hl | Hr].
      * destruct Hl as [ts1 [o1 [k1 [e1 [ts2 [-> Hp]]]]]].
        left. exists ((o,k,e) :: ts1), o1, k1, e1, ts2.
        split; [ reflexivity | assumption ].
      * right. intros o1 k1 e1 [Heq | Hin].
        -- inversion Heq; subst. assumption.
        -- apply (Hr o1 k1 e1 Hin).
Qed.

Theorem progress : forall C,
  conf_ok C -> terminal C \/ (exists C', cstep C C') \/ blocked C.
Proof.
  intros [[H ms] ts] [Hh [Hb [Hms Hts]]].
  destruct ms as [| M ms'].
  - (* メッセージが無い *)
    destruct (tasks_progress H ts Hh Hts) as [Hact | Hall].
    + right. left.
      destruct Hact as [ts1 [o [k [e [ts2 [-> [Hv | [H' [out [e' Hst]]]]]]]]]].
      * eexists. apply CFinish. assumption.
      * eexists. eapply CTask. eassumption.
    + destruct ts as [| t ts'].
      * left. simpl. split; reflexivity.
      * right. right. simpl. split; [ reflexivity | ].
        split; [ discriminate | assumption ].
  - (* メッセージがある。理解されないことは起こらないので必ず配送できる *)
    right. left. destruct M as [[[o m] v] k].
    assert (Hme : msg_ok H (o, m, v, k)) by (apply Hms; left; reflexivity).
    simpl in Hme. destruct Hme as [c [ta [tr [A [B _]]]]].
    exists (H, [] ++ ms', ts ++ [(o, k, subst 0 v (mbody c m))]).
    apply (CDeliver H [] o m v k ms' ts c ta tr); assumption.
Qed.

(* --- 定理 4: 型安全性 --- *)
Theorem type_safety : forall C C', conf_ok C -> csteps C C' -> ~ stuck C'.
Proof.
  intros C C' Hok Hs [Hnt [Hnb Hns]].
  assert (Hok' : conf_ok C') by (eapply preservation_star; eassumption).
  destruct (progress _ Hok') as [Ht | [Hst | Hb]]; contradiction.
Qed.

(* --- 定理 5: actor の状態は常に宣言型を持つ --- *)
Theorem state_type_invariant : forall C H' ms' ts',
  conf_ok C -> csteps C (H', ms', ts') ->
  forall o c v, nth_error (hot H') o = Some c -> nth_error (hst H') o = Some v ->
    value v /\ forall C0 G, ht (hot H') (hft H') C0 G v (stype c).
Proof.
  intros C H' ms' ts' Hok Hs o c v Hoc Hsv.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [Hh _]. apply (heap_st_ok _ _ _ _ Hh Hoc Hsv).
Qed.

(* --- 定理 6: 解決済み future の値は宣言された返り値型を持つ ---
   これが reply と now/future の戻り値型の一致である。 *)
Theorem future_type_invariant : forall C H' ms' ts',
  conf_ok C -> csteps C (H', ms', ts') ->
  forall k T v, nth_error (hft H') k = Some T ->
                nth_error (hfv H') k = Some (Some v) ->
    value v /\ forall C0 G, ht (hot H') (hft H') C0 G v T.
Proof.
  intros C H' ms' ts' Hok Hs k T v Hk Hv.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [Hh _]. apply (heap_fv_ok _ _ _ _ Hh Hk Hv).
Qed.

(* ================================================================= *)
(* 11. await を含まない断片 ---- 機械的デッドロック自由              *)
(* ================================================================= *)

(* 式が await を含まないこと *)
Inductive afree : tm -> Prop :=
| AFNum  : forall n, afree (ENum n)
| AFBool : forall b, afree (EBool b)
| AFUnit : afree EUnit
| AFVar  : forall x, afree (EVar x)
| AFSelf : afree ESelf
| AFORef : forall o, afree (EORef o)
| AFFRef : forall k, afree (EFRef k)
| AFAdd  : forall a b, afree a -> afree b -> afree (EAdd a b)
| AFLt   : forall a b, afree a -> afree b -> afree (ELt a b)
| AFIf   : forall a b d, afree a -> afree b -> afree d -> afree (EIf a b d)
| AFLet  : forall x a b, afree a -> afree b -> afree (ELet x a b)
| AFGet  : afree EGet
| AFSet  : forall a, afree a -> afree (ESet a)
| AFNew  : forall c, afree (ENew c)
| AFSend : forall a m b, afree a -> afree b -> afree (EFSend a m b).

Lemma value_afree : forall v, value v -> afree v.
Proof. intros v Hv; inversion Hv; constructor. Qed.

Lemma afree_subst : forall e x v, afree v -> afree e -> afree (subst x v e).
Proof.
  induction e; intros x v Hv He; simpl; inversion He; subst.
  - constructor.
  - constructor.
  - constructor.
  - destruct (Nat.eqb n x); [ assumption | constructor ].
  - constructor.
  - constructor.
  - constructor.
  - constructor; [ apply IHe1 | apply IHe2 ]; assumption.
  - constructor; [ apply IHe1 | apply IHe2 ]; assumption.
  - constructor; [ apply IHe1 | apply IHe2 | apply IHe3 ]; assumption.
  - constructor;
      [ apply IHe1; assumption
      | destruct (Nat.eqb n x); [ assumption | apply IHe2; assumption ] ].
  - constructor.
  - constructor; apply IHe; assumption.
  - constructor.
  - constructor; [ apply IHe1 | apply IHe2 ]; assumption.
Qed.

Lemma afree_not_awaiting : forall H e, awaiting H e -> ~ afree e.
Proof.
  intros H e Haw. induction Haw; intros Ha; inversion Ha; subst; auto.
Qed.

Lemma heap_st_value : forall H o v,
  heap_ok H -> nth_error (hst H) o = Some v -> value v.
Proof.
  intros H o v Hh Hsv.
  assert (Hlt : o < length (hot H)).
  { rewrite <- (heap_len_st _ Hh). eapply nth_error_lt; eauto. }
  destruct (nth_error_ex _ _ _ Hlt) as [c Hc].
  apply (heap_st_ok _ _ _ _ Hh Hc Hsv).
Qed.

Lemma afree_tstep : forall H o e H' out e',
  heap_ok H -> afree e -> tstep H o e H' out e' -> afree e'.
Proof.
  intros H o e H' out e' Hh Ha Hs. revert Ha.
  induction Hs; intros Ha; inversion Ha; subst;
    try (constructor; auto; fail);
    try assumption;
    try (apply afree_subst; assumption);
    try (apply value_afree; eapply heap_st_value; eassumption).
Qed.

Definition conf_afree (C : conf) : Prop :=
  let '(_, _, ts) := C in forall o k e, In (o, k, e) ts -> afree e.

Lemma conf_afree_pres : forall C C',
  (forall c m, afree (mbody c m)) ->
  conf_ok C -> conf_afree C -> cstep C C' -> conf_afree C'.
Proof.
  intros C C' Hbody Hok Haf Hs.
  inversion Hs; subst; simpl in *; destruct Hok as [Hh [Hb [Hms Hts]]].
  - (* CTask *)
    intros o2 k2 e2 HT. apply in_app_or in HT. destruct HT as [HT | [Heq | HT]].
    + apply (Haf o2 k2 e2). apply in_or_app. left. assumption.
    + inversion Heq; subst. eapply afree_tstep;
        [ eassumption | eapply Haf; apply in_app_middle | eassumption ].
    + apply (Haf o2 k2 e2). apply in_or_app. right. right. assumption.
  - (* CFinish *)
    intros o2 k2 e2 HT. apply in_app_or in HT.
    apply (Haf o2 k2 e2). apply in_or_app.
    destruct HT as [HT | HT]; [ left; auto | right; right; auto ].
  - (* CDeliver *)
    intros o2 k2 e2 HT. apply in_app_or in HT. destruct HT as [HT | [Heq | []]].
    + apply (Haf o2 k2 e2). assumption.
    + assert (Hme := Hms _ (in_app_middle _ _ _ _)).
      simpl in Hme. destruct Hme as [c0 [ta0 [tr0 [A [B [Cv [D E]]]]]]].
      inversion Heq; subst.
      apply afree_subst; [ apply value_afree; exact Cv | apply Hbody ].
Qed.

(* await を含まない構成はブロックしない *)
Theorem no_await_no_deadlock : forall C, conf_afree C -> ~ blocked C.
Proof.
  intros [[H ms] ts] Haf [Hms [Hne Hall]].
  destruct ts as [| [[o k] e] ts']; [ apply Hne; reflexivity | ].
  eapply afree_not_awaiting;
    [ apply (Hall o k e); left; reflexivity
    | apply (Haf o k e); left; reflexivity ].
Qed.

(* 主結果: await を含まないプログラムは、型が付いていれば
   どこまで実行してもデッドロックせず、終状態でなければ必ず一歩進める *)
Theorem async_deadlock_free : forall C C',
  (forall c m, afree (mbody c m)) ->
  conf_ok C -> conf_afree C -> csteps C C' ->
  conf_ok C' /\ conf_afree C' /\ ~ blocked C'
  /\ (terminal C' \/ exists C'', cstep C' C'').
Proof.
  intros C C' Hbody Hok Haf Hs.
  assert (Hboth : conf_ok C' /\ conf_afree C').
  { induction Hs; [ split; assumption | ].
    apply IHHs.
    - eapply preservation; eassumption.
    - eapply conf_afree_pres; eassumption. }
  destruct Hboth as [Hok' Haf'].
  split; [ assumption | ]. split; [ assumption | ].
  split; [ apply no_await_no_deadlock; assumption | ].
  destruct (progress _ Hok') as [Ht | [Hst | Hbl]].
  - left. assumption.
  - right. assumption.
  - exfalso. eapply no_await_no_deadlock; eassumption.
Qed.

End AIPL.
