(*
  AIPLSoundnessMax.v
  ------------------------------------------------------------------
  AIPL^-max : 型健全性・型安全性が成り立つ「最大の」AIPL 断片
  ------------------------------------------------------------------

  AIPLSoundness2.v は、義務レベルを課すことでデッドロック自由まで
  証明した。その代償として言語を狭めている ---
    ・await は必ず「自分より上のレベル」へ向かねばならない
    ・未解決の future には必ず埋める者がいなければならない（prod_ok）
    ・したがって、待ちの環・返答の委譲・自分自身への now は書けない

  本ファイルは逆を行く。デッドロック自由を要求から外し、
  型健全性（preservation + progress）と型安全性だけを目標に据えて、
  それが成り立つ範囲で言語を最大まで広げる。

  AIPLSoundness2 から取り除いたもの:
    ・future の義務レベル（await の向きの制約）      -> 任意の await を許す
    ・prod_ok（未解決 future には埋める者がいる）     -> 孤児 future を許す
    ・効果（AIPLSoundness2 の直交する層。あちらで証明済み）

  AIPLSoundness2 に加えたもの（いずれも実装 AIPL にある機構）:
    ・文字列と ++（+ とは別の演算。型で分ける）
    ・対（多引数メソッド・複数フィールドの状態の代用）
    ・result<t> ---- ok / err / is_ok / value(既定値つき)
    ・期限つきの待ち  now e timeout n else ed   （型 t）
    ・期限つきの待ち  now e timeout n           （型 result<t>）
    ・一級の返答先 reply<t> ---- replyto / answer による委譲
    ・自分自身への送信・待ち、待ちの環（型では禁じない）

  結果:
    ・preservation / progress / type_safety は成り立つ（定理 2,3,4）
    ・deadlock_free は成り立たない。しかもそれは証明の不足ではなく、
      この断片には実際にデッドロックする型の付いた構成が存在する
      （AIPLSoundnessMaxExample.v の max_admits_deadlock）。
    ・つまりここが「型健全性・型安全性だけを求めるときの上限」である。

  Rocq 9.1.0 で検査。Print Assumptions は Closed under the global context。
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
| TStr   : ty
| TActor : nat -> ty              (* actor[c] *)
| TPair  : ty -> ty -> ty         (* (t1, t2) *)
| TFut   : ty -> ty               (* future<t> *)
| TReply : ty -> ty               (* reply<t>  一級の返答先 *)
| TRes   : ty -> ty.              (* result<t> *)

Inductive tm : Type :=
| ENum    : nat -> tm
| EBool   : bool -> tm
| EUnit   : tm
| EStr    : list nat -> tm             (* 文字列。文字は番号で表す *)
| EVar    : nat -> tm
| ESelf   : tm
| EORef   : nat -> tm                  (* 実行時のみ: actor 参照 *)
| EFRef   : nat -> tm                  (* 実行時のみ: future 参照 *)
| ERRef   : nat -> tm                  (* 実行時のみ: 返答先 *)
| EAdd    : tm -> tm -> tm             (* 数の + *)
| ECat    : tm -> tm -> tm             (* 文字列の ++ *)
| ELt     : tm -> tm -> tm
| EIf     : tm -> tm -> tm -> tm
| ELet    : nat -> tm -> tm -> tm      (* var x = e1; e2 *)
| ESeq    : tm -> tm -> tm
| EWhile  : tm -> tm -> tm
| EGet    : tm                         (* 自分の状態を読む *)
| ESet    : tm -> tm                   (* 自分の状態を書く *)
| ENew    : nat -> tm
| EPair   : tm -> tm -> tm
| EFst    : tm -> tm
| ESnd    : tm -> tm
| EOk     : tm -> tm                   (* ok(e) : result<t> *)
| EErr    : ty -> tm                   (* err   : result<t>（型注釈つき） *)
| EIsOk   : tm -> tm
| EGetOr  : tm -> tm -> tm             (* e.value(既定値 d) *)
| EFSend  : tm -> nat -> tm -> tm      (* future t.m(e) *)
| EAwait  : tm -> tm                   (* now ...（期限なし） *)
| EAwaitD : tm -> nat -> tm -> tm      (* now ... timeout n else ed *)
| EAwaitR : tm -> nat -> tm            (* now ... timeout n : result<t> *)
| EReplyTo : tm                        (* 自分の返答先 *)
| EAnswer : tm -> tm -> tm.            (* answer r e *)

(* 糖衣:
     e1 ; e2         = ESeq
     send t.m(e)     = ELet fresh (EFSend t m e) EUnit
     now t.m(e)      = EAwait (EFSend t m e)
     now t.m(e) timeout n else d = EAwaitD (EFSend t m e) n d
     reply e         = EAnswer EReplyTo e   （返り値をそのまま返す場合は本体の値）
     m(a, b)         = 対を一つ渡す                                            *)

Inductive value : tm -> Prop :=
| VNum  : forall n, value (ENum n)
| VBool : forall b, value (EBool b)
| VUnit : value EUnit
| VStr  : forall s, value (EStr s)
| VORef : forall o, value (EORef o)
| VFRef : forall k, value (EFRef k)
| VRRef : forall k, value (ERRef k)
| VPair : forall a b, value a -> value b -> value (EPair a b)
| VOk   : forall v, value v -> value (EOk v)
| VErr  : forall T, value (EErr T).

Fixpoint subst (x : nat) (v : tm) (t : tm) : tm :=
  match t with
  | EVar y         => if Nat.eqb y x then v else EVar y
  | ELet y e1 e2   => ELet y (subst x v e1)
                        (if Nat.eqb y x then e2 else subst x v e2)
  | EAdd a b       => EAdd (subst x v a) (subst x v b)
  | ECat a b       => ECat (subst x v a) (subst x v b)
  | ELt  a b       => ELt  (subst x v a) (subst x v b)
  | EIf a b c      => EIf (subst x v a) (subst x v b) (subst x v c)
  | ESeq a b       => ESeq (subst x v a) (subst x v b)
  | EWhile a b     => EWhile (subst x v a) (subst x v b)
  | ESet a         => ESet (subst x v a)
  | EPair a b      => EPair (subst x v a) (subst x v b)
  | EFst a         => EFst (subst x v a)
  | ESnd a         => ESnd (subst x v a)
  | EOk a          => EOk (subst x v a)
  | EIsOk a        => EIsOk (subst x v a)
  | EGetOr a b     => EGetOr (subst x v a) (subst x v b)
  | EFSend a m b   => EFSend (subst x v a) m (subst x v b)
  | EAwait a       => EAwait (subst x v a)
  | EAwaitD a n b  => EAwaitD (subst x v a) n (subst x v b)
  | EAwaitR a n    => EAwaitR (subst x v a) n
  | EAnswer a b    => EAnswer (subst x v a) (subst x v b)
  | _              => t
  end.

(* ================================================================= *)
(* 2. 実行時の構造                                                   *)
(* ================================================================= *)

Record heap := Heap {
  hot : list nat;             (* actor 番号 -> クラス番号 *)
  hst : list tm;              (* actor 番号 -> 現在の状態値 *)
  hft : list ty;              (* future 番号 -> 型 *)
  hfv : list (option tm)      (* future 番号 -> 解決済みの値 *)
}.

Definition msg  := (nat * nat * tm * nat)%type.   (* 宛先, メソッド, 引数, future *)
Definition task := (nat * nat * tm)%type.         (* self, 自分が埋める future, 式 *)
Definition conf := (heap * list msg * list task)%type.

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
  eapply IHl; eassumption.
Qed.

Lemma nth_upd_neq : forall A (l : list A) n m x,
  n <> m -> nth_error (upd l n x) m = nth_error l m.
Proof.
  induction l as [|a l IH]; intros [|n] [|m] x Hne; simpl; try reflexivity.
  - contradiction Hne. reflexivity.
  - apply IH. lia.
Qed.

(* 表は伸びるだけ *)
Definition ext {A : Type} (l l' : list A) : Prop :=
  exists l'', l' = l ++ l''.

Lemma ext_refl : forall A (l : list A), ext l l.
Proof. intros. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma ext_app : forall A (l l' : list A), ext l (l ++ l').
Proof. intros. exists l'. reflexivity. Qed.

Lemma ext_trans : forall A (l1 l2 l3 : list A), ext l1 l2 -> ext l2 l3 -> ext l1 l3.
Proof.
  intros A l1 l2 l3 [a ->] [b ->]. exists (a ++ b). rewrite app_assoc. reflexivity.
Qed.

Lemma nth_app_last : forall A (l : list A) x,
  nth_error (l ++ [x]) (length l) = Some x.
Proof.
  induction l; intros x; simpl; [ reflexivity | apply IHl ].
Qed.

Lemma nth_app1_inv : forall A (l : list A) x n y,
  nth_error (l ++ [x]) n = Some y ->
  (n < length l /\ nth_error l n = Some y) \/ (n = length l /\ y = x).
Proof.
  induction l; intros x [|n] y H; simpl in *.
  - right. split; [ reflexivity | congruence ].
  - destruct n; simpl in H; discriminate.
  - left. split; [ lia | assumption ].
  - destruct (IHl x n y H) as [[Hl Hn] | [-> ->]].
    + left. split; [ lia | assumption ].
    + right. split; reflexivity.
Qed.

Lemma nth_error_lt : forall A (l : list A) n (x : A),
  nth_error l n = Some x -> n < length l.
Proof.
  intros A l. induction l; intros [|n] x H; simpl in *; try discriminate.
  - lia.
  - apply IHl in H. lia.
Qed.

Lemma nth_error_ex : forall A (l : list A) n,
  n < length l -> exists x, nth_error l n = Some x.
Proof.
  intros A l. induction l; intros [|n] H; simpl in *; try lia.
  - exists a. reflexivity.
  - apply IHl. lia.
Qed.

Lemma nth_ext_some : forall A (l l' : list A) n x,
  ext l l' -> nth_error l n = Some x -> nth_error l' n = Some x.
Proof.
  intros A l l' n x [d ->] H. rewrite nth_error_app1;
    [ assumption | eapply nth_error_lt; eassumption ].
Qed.

(* 型環境 *)
Definition env := nat -> option ty.
Definition empty : env := fun _ => None.
Definition extend (G : env) (x : nat) (T : ty) : env :=
  fun y => if Nat.eqb y x then Some T else G y.

(* ================================================================= *)
(* 3. プログラム                                                     *)
(* ================================================================= *)

Section AIPL.

Variable stype : nat -> ty.                       (* クラス c の状態の型 *)
Variable sinit : nat -> tm.                       (* クラス c の状態の初期値 *)
Variable mtab  : nat -> nat -> option (ty * ty).  (* c.m : 引数型 * 返り値型 *)
Variable mbody : nat -> nat -> tm.                (* c.m の本体。引数は EVar 0 *)
Variable ot0   : list nat.                        (* 最初から居る actor の表 *)

(* ================================================================= *)
(* 4. 型付け                                                         *)
(* ================================================================= *)

(* ht ot ft C R G e T :
     ot  : actor 表（番号 -> クラス）
     ft  : future 表（番号 -> 型）
     C   : いま自分がいるクラス（self の型）
     R   : いま実行中のメソッドの返り値型（replyto の型）
     G   : 型環境
   AIPLSoundness2 との差:
     ・future の型にレベルも効果も載せない
     ・したがって await に側条件がない（どこへ待ってもよい）        *)

Inductive ht (ot : list nat) (ft : list ty) (C : nat) (R : ty)
  : env -> tm -> ty -> Prop :=
| HNum   : forall G n, ht ot ft C R G (ENum n) TInt
| HBool  : forall G b, ht ot ft C R G (EBool b) TBool
| HUnit  : forall G,   ht ot ft C R G EUnit TUnit
| HStr   : forall G s, ht ot ft C R G (EStr s) TStr
| HVar   : forall G x T, G x = Some T -> ht ot ft C R G (EVar x) T
| HSelf  : forall G, ht ot ft C R G ESelf (TActor C)
| HORef  : forall G o c, nth_error ot o = Some c -> ht ot ft C R G (EORef o) (TActor c)
| HFRef  : forall G k T, nth_error ft k = Some T -> ht ot ft C R G (EFRef k) (TFut T)
| HRRef  : forall G k T, nth_error ft k = Some T -> ht ot ft C R G (ERRef k) (TReply T)
(* 数の + と文字列の ++ は別の演算である。型がそれを分ける。 *)
| HAdd   : forall G a b, ht ot ft C R G a TInt -> ht ot ft C R G b TInt ->
             ht ot ft C R G (EAdd a b) TInt
| HCat   : forall G a b, ht ot ft C R G a TStr -> ht ot ft C R G b TStr ->
             ht ot ft C R G (ECat a b) TStr
| HLt    : forall G a b, ht ot ft C R G a TInt -> ht ot ft C R G b TInt ->
             ht ot ft C R G (ELt a b) TBool
| HIf    : forall G a b c T, ht ot ft C R G a TBool ->
             ht ot ft C R G b T -> ht ot ft C R G c T -> ht ot ft C R G (EIf a b c) T
| HLet   : forall G x e1 e2 T1 T2, ht ot ft C R G e1 T1 ->
             ht ot ft C R (extend G x T1) e2 T2 -> ht ot ft C R G (ELet x e1 e2) T2
| HSeq   : forall G a b T1 T2, ht ot ft C R G a T1 -> ht ot ft C R G b T2 ->
             ht ot ft C R G (ESeq a b) T2
| HWhile : forall G a b T1, ht ot ft C R G a TBool -> ht ot ft C R G b T1 ->
             ht ot ft C R G (EWhile a b) TUnit
| HGet   : forall G, ht ot ft C R G EGet (stype C)
| HSet   : forall G e, ht ot ft C R G e (stype C) -> ht ot ft C R G (ESet e) TUnit
| HNew   : forall G c, ht ot ft C R G (ENew c) (TActor c)
| HPair  : forall G a b Ta Tb, ht ot ft C R G a Ta -> ht ot ft C R G b Tb ->
             ht ot ft C R G (EPair a b) (TPair Ta Tb)
| HFst   : forall G a Ta Tb, ht ot ft C R G a (TPair Ta Tb) -> ht ot ft C R G (EFst a) Ta
| HSnd   : forall G a Ta Tb, ht ot ft C R G a (TPair Ta Tb) -> ht ot ft C R G (ESnd a) Tb
| HOk    : forall G a T, ht ot ft C R G a T -> ht ot ft C R G (EOk a) (TRes T)
| HErr   : forall G T, ht ot ft C R G (EErr T) (TRes T)
| HIsOk  : forall G a T, ht ot ft C R G a (TRes T) -> ht ot ft C R G (EIsOk a) TBool
| HGetOr : forall G a b T, ht ot ft C R G a (TRes T) -> ht ot ft C R G b T ->
             ht ot ft C R G (EGetOr a b) T
| HSend  : forall G ea m e1 c ta tr,
             ht ot ft C R G ea (TActor c) -> mtab c m = Some (ta, tr) ->
             ht ot ft C R G e1 ta -> ht ot ft C R G (EFSend ea m e1) (TFut tr)
(* ★ 待ちに側条件はない。自分自身を待ってもよいし、環を作ってもよい。 *)
| HAwait : forall G e T, ht ot ft C R G e (TFut T) -> ht ot ft C R G (EAwait e) T
| HAwaitD : forall G e n ed T, ht ot ft C R G e (TFut T) -> ht ot ft C R G ed T ->
             ht ot ft C R G (EAwaitD e n ed) T
| HAwaitR : forall G e n T, ht ot ft C R G e (TFut T) ->
             ht ot ft C R G (EAwaitR e n) (TRes T)
(* ★ 一級の返答先。いま実行中のメソッドの返り値型が replyto の型である。 *)
| HReplyTo : forall G, ht ot ft C R G EReplyTo (TReply R)
| HAnswer  : forall G r e T, ht ot ft C R G r (TReply T) -> ht ot ft C R G e T ->
             ht ot ft C R G (EAnswer r e) TUnit.

(* プログラム全体が型検査を通っていること。
   Section の Hypothesis なので、End で各定理の前提に変わる。公理ではない。 *)

Hypothesis sinit_value : forall c, value (sinit c).

Hypothesis sinit_ok : forall c ot ft C R G, ht ot ft C R G (sinit c) (stype c).

(* メソッド本体は、そのメソッドの返り値型を R として型が付く。
   R が replyto の型になるので、委譲しても型は合う。 *)
Hypothesis bodies_ok :
  forall c m ta tr, mtab c m = Some (ta, tr) ->
    forall ot ft, ext ot0 ot ->
      ht ot ft c tr (extend empty 0 ta) (mbody c m) tr.

(* ================================================================= *)
(* 5. 型付けの基本補題                                               *)
(* ================================================================= *)

Lemma ht_env_ext : forall ot ft C R G1 G2 e T,
  (forall z, G1 z = G2 z) -> ht ot ft C R G1 e T -> ht ot ft C R G2 e T.
Proof.
  intros ot ft C R G1 G2 e T Heq H. generalize dependent G2.
  induction H; intros G2 Heq; try (econstructor; eauto; fail).
  - constructor. rewrite <- Heq. assumption.
  - econstructor; [ eauto | ].
    apply IHht2. intros z. unfold extend. destruct (Nat.eqb z x); auto.
Qed.

(* 表の拡張に対する単調性 *)
Lemma ht_mono : forall ot ft C R G e T ot' ft',
  ht ot ft C R G e T -> ext ot ot' -> ext ft ft' -> ht ot' ft' C R G e T.
Proof.
  intros ot ft C R G e T ot' ft' H. generalize dependent ft'. generalize dependent ot'.
  induction H; intros ot' ft' Ho Hf; try (econstructor; eauto; fail).
  - constructor. eapply nth_ext_some; eassumption.
  - constructor. eapply nth_ext_some; eassumption.
  - constructor. eapply nth_ext_some; eassumption.
Qed.

(* 値の型付けは、クラス文脈にも返り値型にも型環境にも依存しない *)
Lemma value_ht_indep : forall ot ft C R G v T,
  value v -> ht ot ft C R G v T -> forall C' R' G', ht ot ft C' R' G' v T.
Proof.
  intros ot ft C R G v T Hv. generalize dependent T.
  induction Hv; intros T0 Ht C' R' G'; inversion Ht; subst;
    try (econstructor; eauto; fail).
Qed.

(* 代入補題 *)
Lemma substitution : forall ot ft C R e T G x T1 v,
  ht ot ft C R (extend G x T1) e T ->
  value v ->
  (forall C' R' G', ht ot ft C' R' G' v T1) ->
  ht ot ft C R G (subst x v e) T.
Proof.
  intros ot ft C R e. induction e; intros T G x T1 v Ht Hv Hvt;
    inversion Ht; subst; simpl; try (econstructor; eauto; fail).
  - (* EVar *)
    unfold extend in H1. destruct (Nat.eqb n x) eqn:Q.
    + inversion H1; subst. apply Hvt.
    + constructor. assumption.
  - (* ELet *)
    destruct (Nat.eqb n x) eqn:Q.
    + apply Nat.eqb_eq in Q. subst n.
      econstructor; [ eapply IHe1; eauto | ].
      eapply ht_env_ext; [ | eassumption ].
      intros z. unfold extend. destruct (Nat.eqb z x); reflexivity.
    + econstructor; [ eapply IHe1; eauto | ].
      apply IHe2 with (T1 := T1); auto.
      eapply ht_env_ext; [ | eassumption ].
      intros z. unfold extend.
      destruct (Nat.eqb z n) eqn:Q1; destruct (Nat.eqb z x) eqn:Q2; try reflexivity.
      apply Nat.eqb_eq in Q1. apply Nat.eqb_eq in Q2. subst.
      rewrite Nat.eqb_refl in Q. discriminate.
Qed.

(* ----- 標準形 ----- *)
Lemma canon_int : forall ot ft C R G v,
  value v -> ht ot ft C R G v TInt -> exists n, v = ENum n.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_bool : forall ot ft C R G v,
  value v -> ht ot ft C R G v TBool -> exists b, v = EBool b.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_str : forall ot ft C R G v,
  value v -> ht ot ft C R G v TStr -> exists s, v = EStr s.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_actor : forall ot ft C R G v c,
  value v -> ht ot ft C R G v (TActor c) ->
  exists o, v = EORef o /\ nth_error ot o = Some c.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_pair : forall ot ft C R G v Ta Tb,
  value v -> ht ot ft C R G v (TPair Ta Tb) ->
  exists a b, v = EPair a b /\ value a /\ value b.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_fut : forall ot ft C R G v T,
  value v -> ht ot ft C R G v (TFut T) ->
  exists k, v = EFRef k /\ nth_error ft k = Some T.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_reply : forall ot ft C R G v T,
  value v -> ht ot ft C R G v (TReply T) ->
  exists k, v = ERRef k /\ nth_error ft k = Some T.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_res : forall ot ft C R G v T,
  value v -> ht ot ft C R G v (TRes T) ->
  (exists w, v = EOk w /\ value w) \/ v = EErr T.
Proof.
  intros. inversion H; subst; inversion H0; subst;
    [ left; eauto | right; reflexivity ].
Qed.

(* ================================================================= *)
(* 6. 操作的意味論                                                   *)
(* ================================================================= *)

(* tstep H o k e H' out e'
     o : 実行中のタスクの self、k : そのタスクが埋める future。
     k が要るのは replyto を評価するためである。 *)
Inductive tstep : heap -> nat -> nat -> tm -> heap -> list msg -> tm -> Prop :=
(* --- 基底規則 --- *)
| STAdd : forall H o k n1 n2,
    tstep H o k (EAdd (ENum n1) (ENum n2)) H [] (ENum (n1 + n2))
| STCat : forall H o k s1 s2,
    tstep H o k (ECat (EStr s1) (EStr s2)) H [] (EStr (s1 ++ s2))
| STLt : forall H o k n1 n2,
    tstep H o k (ELt (ENum n1) (ENum n2)) H [] (EBool (Nat.ltb n1 n2))
| STIfT : forall H o k e1 e2,
    tstep H o k (EIf (EBool true) e1 e2) H [] e1
| STIfF : forall H o k e1 e2,
    tstep H o k (EIf (EBool false) e1 e2) H [] e2
| STLet : forall H o k x v e,
    value v -> tstep H o k (ELet x v e) H [] (subst x v e)
| STSeq : forall H o k v b,
    value v -> tstep H o k (ESeq v b) H [] b
| STWhile : forall H o k a b,
    tstep H o k (EWhile a b) H [] (EIf a (ESeq b (EWhile a b)) EUnit)
| STSelf : forall H o k,
    tstep H o k ESelf H [] (EORef o)
| STReplyTo : forall H o k,
    tstep H o k EReplyTo H [] (ERRef k)
| STGet : forall H o k v,
    nth_error (hst H) o = Some v -> tstep H o k EGet H [] v
| STSet : forall H o k v,
    value v ->
    tstep H o k (ESet v) (Heap (hot H) (upd (hst H) o v) (hft H) (hfv H)) [] EUnit
| STNew : forall H o k cn,
    tstep H o k (ENew cn)
      (Heap (hot H ++ [cn]) (hst H ++ [sinit cn]) (hft H) (hfv H))
      [] (EORef (length (hot H)))
| STFst : forall H o k v1 v2,
    value v1 -> value v2 -> tstep H o k (EFst (EPair v1 v2)) H [] v1
| STSnd : forall H o k v1 v2,
    value v1 -> value v2 -> tstep H o k (ESnd (EPair v1 v2)) H [] v2
| STIsOkT : forall H o k v,
    value v -> tstep H o k (EIsOk (EOk v)) H [] (EBool true)
| STIsOkF : forall H o k T,
    tstep H o k (EIsOk (EErr T)) H [] (EBool false)
| STGetOrOk : forall H o k v d,
    value v -> tstep H o k (EGetOr (EOk v) d) H [] v
| STGetOrErr : forall H o k T d,
    tstep H o k (EGetOr (EErr T) d) H [] d
| STSend : forall H o k o' m v cc ta tr,
    value v ->
    nth_error (hot H) o' = Some cc ->
    mtab cc m = Some (ta, tr) ->
    tstep H o k (EFSend (EORef o') m v)
      (Heap (hot H) (hst H) (hft H ++ [tr]) (hfv H ++ [None]))
      [(o', m, v, length (hft H))]
      (EFRef (length (hft H)))
| STAwait : forall H o k k' v,
    nth_error (hfv H) k' = Some (Some v) ->
    tstep H o k (EAwait (EFRef k')) H [] v
(* 期限つきの待ち。解決していれば値を返し、そうでなくても（あっても）
   期限切れは起こりうる。期限は「いつでも起こりうる分岐」として表す。 *)
| STAwaitDVal : forall H o k k' n d v,
    nth_error (hfv H) k' = Some (Some v) ->
    tstep H o k (EAwaitD (EFRef k') n d) H [] v
| STAwaitDTo : forall H o k k' n d T,
    nth_error (hft H) k' = Some T ->
    tstep H o k (EAwaitD (EFRef k') n d) H [] d
| STAwaitRVal : forall H o k k' n v,
    nth_error (hfv H) k' = Some (Some v) ->
    tstep H o k (EAwaitR (EFRef k') n) H [] (EOk v)
| STAwaitRTo : forall H o k k' n T,
    nth_error (hft H) k' = Some T ->
    tstep H o k (EAwaitR (EFRef k') n) H [] (EErr T)
(* ★ 返答先へ答える。自分の future でなくてもよい（委譲）。
   既に解決していれば上書きする（実装は二度目を実行時に拒む）。 *)
| STAnswer : forall H o k k' v,
    value v ->
    tstep H o k (EAnswer (ERRef k') v)
      (Heap (hot H) (hst H) (hft H) (upd (hfv H) k' (Some v))) [] EUnit
(* --- 合同規則（評価は左から右） --- *)
| STAdd1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (EAdd a b) H' out (EAdd a' b)
| STAdd2 : forall H o k v b H' out b',
    value v -> tstep H o k b H' out b' -> tstep H o k (EAdd v b) H' out (EAdd v b')
| STCat1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (ECat a b) H' out (ECat a' b)
| STCat2 : forall H o k v b H' out b',
    value v -> tstep H o k b H' out b' -> tstep H o k (ECat v b) H' out (ECat v b')
| STLt1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (ELt a b) H' out (ELt a' b)
| STLt2 : forall H o k v b H' out b',
    value v -> tstep H o k b H' out b' -> tstep H o k (ELt v b) H' out (ELt v b')
| STIf1 : forall H o k a b c H' out a',
    tstep H o k a H' out a' -> tstep H o k (EIf a b c) H' out (EIf a' b c)
| STLet1 : forall H o k x a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (ELet x a b) H' out (ELet x a' b)
| STSeq1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (ESeq a b) H' out (ESeq a' b)
| STSet1 : forall H o k a H' out a',
    tstep H o k a H' out a' -> tstep H o k (ESet a) H' out (ESet a')
| STPair1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (EPair a b) H' out (EPair a' b)
| STPair2 : forall H o k v b H' out b',
    value v -> tstep H o k b H' out b' -> tstep H o k (EPair v b) H' out (EPair v b')
| STFst1 : forall H o k a H' out a',
    tstep H o k a H' out a' -> tstep H o k (EFst a) H' out (EFst a')
| STSnd1 : forall H o k a H' out a',
    tstep H o k a H' out a' -> tstep H o k (ESnd a) H' out (ESnd a')
| STOk1 : forall H o k a H' out a',
    tstep H o k a H' out a' -> tstep H o k (EOk a) H' out (EOk a')
| STIsOk1 : forall H o k a H' out a',
    tstep H o k a H' out a' -> tstep H o k (EIsOk a) H' out (EIsOk a')
| STGetOr1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (EGetOr a b) H' out (EGetOr a' b)
| STSend1 : forall H o k a m b H' out a',
    tstep H o k a H' out a' -> tstep H o k (EFSend a m b) H' out (EFSend a' m b)
| STSend2 : forall H o k v m b H' out b',
    value v -> tstep H o k b H' out b' ->
    tstep H o k (EFSend v m b) H' out (EFSend v m b')
| STAwait1 : forall H o k a H' out a',
    tstep H o k a H' out a' -> tstep H o k (EAwait a) H' out (EAwait a')
| STAwaitD1 : forall H o k a n d H' out a',
    tstep H o k a H' out a' -> tstep H o k (EAwaitD a n d) H' out (EAwaitD a' n d)
| STAwaitR1 : forall H o k a n H' out a',
    tstep H o k a H' out a' -> tstep H o k (EAwaitR a n) H' out (EAwaitR a' n)
| STAnswer1 : forall H o k a b H' out a',
    tstep H o k a H' out a' -> tstep H o k (EAnswer a b) H' out (EAnswer a' b)
| STAnswer2 : forall H o k v b H' out b',
    value v -> tstep H o k b H' out b' ->
    tstep H o k (EAnswer v b) H' out (EAnswer v b').

(* 未解決の future を「期限なしで」待って止まっている状態。
   期限つきの待ちは、いつでも期限切れに進めるので、ここには入らない。 *)
Inductive awaiting (H : heap) : tm -> Prop :=
| AwHere  : forall k, nth_error (hfv H) k = Some None -> awaiting H (EAwait (EFRef k))
| AwAdd1  : forall a b, awaiting H a -> awaiting H (EAdd a b)
| AwAdd2  : forall v b, value v -> awaiting H b -> awaiting H (EAdd v b)
| AwCat1  : forall a b, awaiting H a -> awaiting H (ECat a b)
| AwCat2  : forall v b, value v -> awaiting H b -> awaiting H (ECat v b)
| AwLt1   : forall a b, awaiting H a -> awaiting H (ELt a b)
| AwLt2   : forall v b, value v -> awaiting H b -> awaiting H (ELt v b)
| AwIf    : forall a b c, awaiting H a -> awaiting H (EIf a b c)
| AwLet   : forall x a b, awaiting H a -> awaiting H (ELet x a b)
| AwSeq   : forall a b, awaiting H a -> awaiting H (ESeq a b)
| AwSet   : forall a, awaiting H a -> awaiting H (ESet a)
| AwPair1 : forall a b, awaiting H a -> awaiting H (EPair a b)
| AwPair2 : forall v b, value v -> awaiting H b -> awaiting H (EPair v b)
| AwFst   : forall a, awaiting H a -> awaiting H (EFst a)
| AwSnd   : forall a, awaiting H a -> awaiting H (ESnd a)
| AwOk    : forall a, awaiting H a -> awaiting H (EOk a)
| AwIsOk  : forall a, awaiting H a -> awaiting H (EIsOk a)
| AwGetOr : forall a b, awaiting H a -> awaiting H (EGetOr a b)
| AwSend1 : forall a m b, awaiting H a -> awaiting H (EFSend a m b)
| AwSend2 : forall v m b, value v -> awaiting H b -> awaiting H (EFSend v m b)
| AwAwait : forall a, awaiting H a -> awaiting H (EAwait a)
| AwAwaitD : forall a n d, awaiting H a -> awaiting H (EAwaitD a n d)
| AwAwaitR : forall a n, awaiting H a -> awaiting H (EAwaitR a n)
| AwAnswer1 : forall a b, awaiting H a -> awaiting H (EAnswer a b)
| AwAnswer2 : forall v b, value v -> awaiting H b -> awaiting H (EAnswer v b).

(* 構成の一歩 *)
Inductive cstep : conf -> conf -> Prop :=
| CTask : forall H ms ts1 o k e ts2 H' out e',
    tstep H o k e H' out e' ->
    cstep (H, ms, ts1 ++ (o, k, e) :: ts2)
          (H', ms ++ out, ts1 ++ (o, k, e') :: ts2)
| CFinish : forall H ms ts1 o k v ts2,
    value v ->
    cstep (H, ms, ts1 ++ (o, k, v) :: ts2)
          (Heap (hot H) (hst H) (hft H) (upd (hfv H) k (Some v)), ms, ts1 ++ ts2)
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
     value v /\ forall C R G, ht (hot H) (hft H) C R G v (stype c)) /\
  (forall k T v, nth_error (hft H) k = Some T ->
     nth_error (hfv H) k = Some (Some v) ->
     value v /\ forall C R G, ht (hot H) (hft H) C R G v T).

Definition msg_ok (H : heap) (M : msg) : Prop :=
  let '(o, m, v, k) := M in
  exists c ta tr,
       nth_error (hot H) o = Some c
    /\ mtab c m = Some (ta, tr)
    /\ value v
    /\ (forall C R G, ht (hot H) (hft H) C R G v ta)
    /\ nth_error (hft H) k = Some tr.

(* タスクは、自分が埋める future の型を返り値型として型が付く。
   その型が replyto の型でもある。 *)
Definition task_ok (H : heap) (t : task) : Prop :=
  let '(o, k, e) := t in
  exists c T,
       nth_error (hot H) o = Some c
    /\ nth_error (hft H) k = Some T
    /\ ht (hot H) (hft H) c T empty e T.

(* AIPLSoundness2 の prod_ok（未解決 future には埋める者がいる）は無い。
   孤児 future を許すことが、この断片が「最大」である理由の一つである。 *)
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

Lemma local_progress : forall H o c k R G e T,
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  ht (hot H) (hft H) c R G e T ->
  (forall x, G x = None) ->
  value e \/ (exists H' out e', tstep H o k e H' out e') \/ awaiting H e.
Proof.
  intros H o c k R G e T Hh Ho Ht.
  destruct Hh as [Hl1 [Hl2 [Hstok Hfvok]]].
  induction Ht; intros Hcl; try (left; constructor; fail).
  - (* HVar *) rewrite Hcl in H0. discriminate.
  - (* HSelf *) right. left. eauto using tstep.
  - (* HAdd *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_int _ _ _ _ _ _ Hv1 Ht1) as [n ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_int _ _ _ _ _ _ Hv2 Ht2) as [n2 ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STAdd2; [ constructor | eassumption ].
    + right. apply AwAdd2; [ constructor | assumption ].
  - (* HCat *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_str _ _ _ _ _ _ Hv1 Ht1) as [s1 ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_str _ _ _ _ _ _ Hv2 Ht2) as [s2 ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STCat2; [ constructor | eassumption ].
    + right. apply AwCat2; [ constructor | assumption ].
  - (* HLt *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_int _ _ _ _ _ _ Hv1 Ht1) as [n ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_int _ _ _ _ _ _ Hv2 Ht2) as [n2 ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STLt2; [ constructor | eassumption ].
    + right. apply AwLt2; [ constructor | assumption ].
  - (* HIf *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + destruct (canon_bool _ _ _ _ _ _ Hv1 Ht1) as [[|] ->].
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
  - (* HSeq *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HWhile *) right. left. eauto using tstep.
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
  - (* HPair *)
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ right. left. eauto using tstep. }
    2:{ right. right. constructor. assumption. }
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + left. constructor; assumption.
    + right. left. eexists; eexists; eexists. apply STPair2; eassumption.
    + right. right. apply AwPair2; assumption.
  - (* HFst *)
    right.
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + destruct (canon_pair _ _ _ _ _ _ _ _ Hv Ht) as [x [y [-> [Hx Hy]]]].
      left. eexists; eexists; eexists. apply STFst; assumption.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HSnd *)
    right.
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + destruct (canon_pair _ _ _ _ _ _ _ _ Hv Ht) as [x [y [-> [Hx Hy]]]].
      left. eexists; eexists; eexists. apply STSnd; assumption.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HOk *)
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + left. constructor. assumption.
    + right. left. eauto using tstep.
    + right. right. constructor. assumption.
  - (* HIsOk *)
    right.
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + destruct (canon_res _ _ _ _ _ _ _ Hv Ht) as [[w [-> Hw]] | ->].
      * left. eexists; eexists; eexists. apply STIsOkT. assumption.
      * left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HGetOr *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + destruct (canon_res _ _ _ _ _ _ _ Hv1 Ht1) as [[w [-> Hw]] | ->].
      * left. eexists; eexists; eexists. apply STGetOrOk. assumption.
      * left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HSend *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_actor _ _ _ _ _ _ _ Hv1 Ht1) as [o' [-> Hoc]].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + left. eexists; eexists; eexists. eapply STSend; eassumption.
    + left. eexists; eexists; eexists. apply STSend2; [ constructor | eassumption ].
    + right. apply AwSend2; [ constructor | assumption ].
  - (* HAwait *)
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    2:{ right. left. eauto using tstep. }
    2:{ right. right. constructor. assumption. }
    destruct (canon_fut _ _ _ _ _ _ _ Hv Ht) as [k' [-> Hk]].
    assert (Hlt : k' < length (hfv H)).
    { rewrite Hl2. eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hlt) as [ov Hov].
    destruct ov as [v |].
    + right. left. exists H, (@nil msg), v. constructor. assumption.
    + right. right. constructor. assumption.
  - (* HAwaitD : 待つ相手が future 参照になっていれば、期限切れへ一歩進める *)
    destruct (IHHt1 Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + destruct (canon_fut _ _ _ _ _ _ _ Hv Ht1) as [k' [-> Hk]].
      right. left. exists H, (@nil msg), ed. eapply STAwaitDTo. eassumption.
    + right. left. eauto using tstep.
    + right. right. apply AwAwaitD. assumption.
  - (* HAwaitR *)
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    + destruct (canon_fut _ _ _ _ _ _ _ Hv Ht) as [k' [-> Hk]].
      right. left. exists H, (@nil msg), (EErr T). eapply STAwaitRTo. eassumption.
    + right. left. eauto using tstep.
    + right. right. apply AwAwaitR. assumption.
  - (* HReplyTo *) right. left. eauto using tstep.
  - (* HAnswer *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_reply _ _ _ _ _ _ _ Hv1 Ht1) as [k' [-> Hk]].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + left. eexists; eexists; eexists. apply STAnswer. assumption.
    + left. eexists; eexists; eexists. apply STAnswer2; [ constructor | eassumption ].
    + right. apply AwAnswer2; [ constructor | assumption ].
Qed.

(* ================================================================= *)
(* 9. 逆転補題とヒープの補題                                         *)
(* ================================================================= *)

Lemma heap_len_st : forall H, heap_ok H -> length (hst H) = length (hot H).
Proof. intros H [A _]. exact A. Qed.

Lemma heap_len_fv : forall H, heap_ok H -> length (hfv H) = length (hft H).
Proof. intros H [_ [A _]]. exact A. Qed.

Lemma heap_st_ok : forall H o c v, heap_ok H ->
  nth_error (hot H) o = Some c -> nth_error (hst H) o = Some v ->
  value v /\ forall C R G, ht (hot H) (hft H) C R G v (stype c).
Proof. intros H o c v [_ [_ [A _]]]. apply A. Qed.

Lemma heap_fv_ok : forall H k T v, heap_ok H ->
  nth_error (hft H) k = Some T -> nth_error (hfv H) k = Some (Some v) ->
  value v /\ forall C R G, ht (hot H) (hft H) C R G v T.
Proof. intros H k T v [_ [_ [_ A]]]. apply A. Qed.

Lemma ht_oref_inv : forall ot ft C R G o T,
  ht ot ft C R G (EORef o) T -> exists c, T = TActor c /\ nth_error ot o = Some c.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_fref_inv : forall ot ft C R G k T,
  ht ot ft C R G (EFRef k) T -> exists T0, T = TFut T0 /\ nth_error ft k = Some T0.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_rref_inv : forall ot ft C R G k T,
  ht ot ft C R G (ERRef k) T -> exists T0, T = TReply T0 /\ nth_error ft k = Some T0.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_add_inv : forall ot ft C R G a b T,
  ht ot ft C R G (EAdd a b) T ->
  T = TInt /\ ht ot ft C R G a TInt /\ ht ot ft C R G b TInt.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_cat_inv : forall ot ft C R G a b T,
  ht ot ft C R G (ECat a b) T ->
  T = TStr /\ ht ot ft C R G a TStr /\ ht ot ft C R G b TStr.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_lt_inv : forall ot ft C R G a b T,
  ht ot ft C R G (ELt a b) T ->
  T = TBool /\ ht ot ft C R G a TInt /\ ht ot ft C R G b TInt.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_if_inv : forall ot ft C R G a b c T,
  ht ot ft C R G (EIf a b c) T ->
  ht ot ft C R G a TBool /\ ht ot ft C R G b T /\ ht ot ft C R G c T.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_let_inv : forall ot ft C R G x e1 e2 T,
  ht ot ft C R G (ELet x e1 e2) T ->
  exists T1, ht ot ft C R G e1 T1 /\ ht ot ft C R (extend G x T1) e2 T.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_seq_inv : forall ot ft C R G a b T,
  ht ot ft C R G (ESeq a b) T ->
  exists T1, ht ot ft C R G a T1 /\ ht ot ft C R G b T.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_while_inv : forall ot ft C R G a b T,
  ht ot ft C R G (EWhile a b) T ->
  T = TUnit /\ ht ot ft C R G a TBool /\ exists T1, ht ot ft C R G b T1.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_self_inv : forall ot ft C R G T,
  ht ot ft C R G ESelf T -> T = TActor C.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_get_inv : forall ot ft C R G T,
  ht ot ft C R G EGet T -> T = stype C.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_set_inv : forall ot ft C R G e T,
  ht ot ft C R G (ESet e) T -> T = TUnit /\ ht ot ft C R G e (stype C).
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_new_inv : forall ot ft C R G cn T,
  ht ot ft C R G (ENew cn) T -> T = TActor cn.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_pair_inv : forall ot ft C R G a b T,
  ht ot ft C R G (EPair a b) T ->
  exists Ta Tb, T = TPair Ta Tb /\ ht ot ft C R G a Ta /\ ht ot ft C R G b Tb.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_fst_inv : forall ot ft C R G a T,
  ht ot ft C R G (EFst a) T -> exists Tb, ht ot ft C R G a (TPair T Tb).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_snd_inv : forall ot ft C R G a T,
  ht ot ft C R G (ESnd a) T -> exists Ta, ht ot ft C R G a (TPair Ta T).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_ok_inv : forall ot ft C R G a T,
  ht ot ft C R G (EOk a) T -> exists T0, T = TRes T0 /\ ht ot ft C R G a T0.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_err_inv : forall ot ft C R G T0 T,
  ht ot ft C R G (EErr T0) T -> T = TRes T0.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_isok_inv : forall ot ft C R G a T,
  ht ot ft C R G (EIsOk a) T ->
  T = TBool /\ exists T0, ht ot ft C R G a (TRes T0).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_getor_inv : forall ot ft C R G a b T,
  ht ot ft C R G (EGetOr a b) T ->
  ht ot ft C R G a (TRes T) /\ ht ot ft C R G b T.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_send_inv : forall ot ft C R G ea m e1 T,
  ht ot ft C R G (EFSend ea m e1) T ->
  exists c ta tr, ht ot ft C R G ea (TActor c) /\ mtab c m = Some (ta, tr)
               /\ ht ot ft C R G e1 ta /\ T = TFut tr.
Proof. intros. inversion H; subst; eauto 10. Qed.

Lemma ht_await_inv : forall ot ft C R G e T,
  ht ot ft C R G (EAwait e) T -> ht ot ft C R G e (TFut T).
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_awaitd_inv : forall ot ft C R G e n d T,
  ht ot ft C R G (EAwaitD e n d) T ->
  ht ot ft C R G e (TFut T) /\ ht ot ft C R G d T.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_awaitr_inv : forall ot ft C R G e n T,
  ht ot ft C R G (EAwaitR e n) T ->
  exists T0, T = TRes T0 /\ ht ot ft C R G e (TFut T0).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ht_replyto_inv : forall ot ft C R G T,
  ht ot ft C R G EReplyTo T -> T = TReply R.
Proof. intros. inversion H; subst; auto. Qed.

Lemma ht_answer_inv : forall ot ft C R G r e T,
  ht ot ft C R G (EAnswer r e) T ->
  T = TUnit /\ exists T0, ht ot ft C R G r (TReply T0) /\ ht ot ft C R G e T0.
Proof. intros. inversion H; subst; eauto. Qed.

Ltac split5 := split; [ | split; [ | split; [ | split ] ] ].
Ltac split4 := split; [ | split; [ | split ] ].
Ltac lift := eapply ht_mono; [ eassumption | try assumption; apply ext_refl
                             | try assumption; apply ext_refl ].
Ltac nomsg := intros ? [].

(* ================================================================= *)
(* 10. 局所保存                                                      *)
(* ================================================================= *)

Lemma local_preservation : forall H o c k R e T H' out e',
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  nth_error (hft H) k = Some R ->
  ht (hot H) (hft H) c R empty e T ->
  tstep H o k e H' out e' ->
  heap_ok H'
  /\ ext (hot H) (hot H')
  /\ ext (hft H) (hft H')
  /\ ht (hot H') (hft H') c R empty e' T
  /\ (forall M, In M out -> msg_ok H' M).
Proof.
  intros H o c k R e T H' out e' Hh Ho Hk Ht Hs.
  generalize dependent T. revert Hk. revert Ho. revert Hh.
  induction Hs; intros Hh Ho Hk T0 Ht.
  - (* STAdd *)
    apply ht_add_inv in Ht as [-> [Ha Hb]].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STCat *)
    apply ht_cat_inv in Ht as [-> [Ha Hb]].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STLt *)
    apply ht_lt_inv in Ht as [-> [Ha Hb]].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STIfT *)
    apply ht_if_inv in Ht as [Ha [Hb Hc]].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STIfF *)
    apply ht_if_inv in Ht as [Ha [Hb Hc]].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STLet *)
    apply ht_let_inv in Ht as [T1 [Hv1 He2]].
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    eapply substitution; [ eassumption | assumption | ].
    intros C' R' G'. eapply value_ht_indep; eassumption.
  - (* STSeq *)
    apply ht_seq_inv in Ht as [T1 [Ha Hb]].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STWhile *)
    apply ht_while_inv in Ht as [-> [Ha [T1 Hb]]].
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    apply HIf; [ assumption | | constructor ].
    eapply HSeq; [ eassumption | eapply HWhile; eassumption ].
  - (* STSelf *)
    apply ht_self_inv in Ht as ->.
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    constructor. assumption.
  - (* STReplyTo *)
    apply ht_replyto_inv in Ht as ->.
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    constructor. assumption.
  - (* STGet *)
    apply ht_get_inv in Ht as ->.
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    destruct (heap_st_ok H o c v Hh Ho H0) as [_ Hvt]. apply Hvt.
  - (* STSet *)
    apply ht_set_inv in Ht as [-> Hv].
    assert (Hvt : forall C' R' G', ht (hot H) (hft H) C' R' G' v (stype c)).
    { intros C' R' G'. eapply value_ht_indep; eassumption. }
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
      * intros k2 T2 w2 Hk2 Hw2. apply (heap_fv_ok _ _ _ _ Hh Hk2 Hw2).
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
           intros C' R' G'. eapply ht_mono; [ apply Hvt | assumption | apply ext_refl ].
        -- subst o2 c2. rewrite <- (heap_len_st _ Hh) in Hsv.
           rewrite nth_app_last in Hsv. inversion Hsv; subst.
           split; [ apply sinit_value | intros C' R' G'; apply sinit_ok ].
      * intros k2 T2 w2 Hk2 Hw2.
        destruct (heap_fv_ok _ _ _ _ Hh Hk2 Hw2) as [Hvv Hvt].
        split; [ assumption | ].
        intros C' R' G'. eapply ht_mono; [ apply Hvt | assumption | apply ext_refl ].
    + assumption.
    + apply ext_refl.
    + simpl. constructor. rewrite nth_app_last. reflexivity.
    + nomsg.
  - (* STFst *)
    apply ht_fst_inv in Ht as [Tb Hp].
    apply ht_pair_inv in Hp as [Ta' [Tb' [Heq [Ha Hb]]]].
    inversion Heq; subst Ta' Tb'.
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STSnd *)
    apply ht_snd_inv in Ht as [Ta Hp].
    apply ht_pair_inv in Hp as [Ta' [Tb' [Heq [Ha Hb]]]].
    inversion Heq; subst Ta' Tb'.
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STIsOkT *)
    apply ht_isok_inv in Ht as [-> [T1 Hr]].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STIsOkF *)
    apply ht_isok_inv in Ht as [-> [T1 Hr]].
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STGetOrOk *)
    apply ht_getor_inv in Ht as [Hr Hd].
    apply ht_ok_inv in Hr as [T1 [Heq Hvv]]. inversion Heq; subst T1.
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STGetOrErr *)
    apply ht_getor_inv in Ht as [Hr Hd].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STSend *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Hto [Hmt [Htv ->]]]]]].
    apply ht_oref_inv in Hto as [c2 [Heq Hoc2]]. inversion Heq; subst c2.
    assert (Hcc : c1 = cc) by congruence. subst c1.
    assert (Hpair : (ta1, tr1) = (ta, tr)) by congruence.
    inversion Hpair; subst ta1 tr1.
    assert (Hextf : ext (hft H) (hft H ++ [tr])) by apply ext_app.
    assert (Hvt : forall C' R' G', ht (hot H) (hft H ++ [tr]) C' R' G' v ta).
    { intros C' R' G'. eapply ht_mono;
        [ eapply value_ht_indep; eassumption | apply ext_refl | assumption ]. }
    split5.
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * repeat rewrite length_app. rewrite (heap_len_fv _ Hh). reflexivity.
      * intros o2 c2 v2 Hoc Hsv.
        destruct (heap_st_ok _ _ _ _ Hh Hoc Hsv) as [Hvv Hv2].
        split; [ assumption | ].
        intros C' R' G'. eapply ht_mono; [ apply Hv2 | apply ext_refl | assumption ].
      * intros k2 T2 w2 Hk2 Hw2.
        destruct (nth_app1_inv _ _ _ _ _ Hw2) as [[Hlt Hw0] | [Heq2 Hbad]];
          [ | discriminate ].
        rewrite nth_error_app1 in Hk2 by (rewrite <- (heap_len_fv _ Hh); lia).
        destruct (heap_fv_ok _ _ _ _ Hh Hk2 Hw0) as [Hvv Hv2].
        split; [ assumption | ].
        intros C' R' G'. eapply ht_mono; [ apply Hv2 | apply ext_refl | assumption ].
    + apply ext_refl.
    + assumption.
    + simpl. constructor. rewrite nth_app_last. reflexivity.
    + intros M HM. simpl in HM. destruct HM as [<- | []].
      exists cc, ta, tr. simpl.
      split; [ assumption | ]. split; [ assumption | ]. split; [ assumption | ].
      split; [ apply Hvt | ]. rewrite nth_app_last. reflexivity.
  - (* STAwait *)
    apply ht_await_inv in Ht.
    apply ht_fref_inv in Ht as [T1 [Heq Hk1]]. inversion Heq; subst T1.
    destruct (heap_fv_ok _ _ _ _ Hh Hk1 H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl | apply Hvt | nomsg ].
  - (* STAwaitDVal *)
    apply ht_awaitd_inv in Ht as [He Hd].
    apply ht_fref_inv in He as [T1 [Heq Hk1]]. inversion Heq; subst T1.
    destruct (heap_fv_ok _ _ _ _ Hh Hk1 H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl | apply Hvt | nomsg ].
  - (* STAwaitDTo : 期限切れ。既定の式へ移る *)
    apply ht_awaitd_inv in Ht as [He Hd].
    split5; [ assumption | apply ext_refl | apply ext_refl | assumption | nomsg ].
  - (* STAwaitRVal *)
    apply ht_awaitr_inv in Ht as [T1 [-> He]].
    apply ht_fref_inv in He as [T2 [Heq Hk1]]. inversion Heq; subst T2.
    destruct (heap_fv_ok _ _ _ _ Hh Hk1 H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    constructor. apply Hvt.
  - (* STAwaitRTo : 期限切れ。err になる *)
    apply ht_awaitr_inv in Ht as [T1 [-> He]].
    apply ht_fref_inv in He as [T2 [Heq Hk1]]. inversion Heq; subst T2.
    assert (T = T1) by congruence. subst T.
    split5; [ assumption | apply ext_refl | apply ext_refl | constructor | nomsg ].
  - (* STAnswer : 一級の返答先へ答える（委譲でもよい） *)
    apply ht_answer_inv in Ht as [-> [T1 [Hr Hv]]].
    apply ht_rref_inv in Hr as [T2 [Heq Hk1]]. inversion Heq; subst T2.
    assert (Hex : exists w, nth_error (hfv H) k' = Some w).
    { apply nth_error_ex. rewrite (heap_len_fv _ Hh). eapply nth_error_lt; eauto. }
    destruct Hex as [w Hw].
    split5.
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * rewrite upd_length. apply (heap_len_fv _ Hh).
      * intros o2 c2 v2 Hoc Hsv. apply (heap_st_ok _ _ _ _ Hh Hoc Hsv).
      * intros k2 T2 w2 Hk2 Hw2.
        destruct (Nat.eq_dec k2 k') as [-> | Hne].
        -- rewrite Hk1 in Hk2. inversion Hk2; subst T2.
           rewrite (nth_upd_eq _ _ _ _ _ Hw) in Hw2. inversion Hw2; subst w2.
           split; [ assumption | ].
           intros C' R' G'. eapply value_ht_indep; eassumption.
        -- rewrite nth_upd_neq in Hw2 by auto.
           apply (heap_fv_ok _ _ _ _ Hh Hk2 Hw2).
    + apply ext_refl.
    + apply ext_refl.
    + constructor.
    + nomsg.
  (* --- 合同規則 --- *)
  - (* STAdd1 *)
    apply ht_add_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho Hk TInt Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STAdd2 *)
    apply ht_add_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho Hk TInt Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. econstructor; [ lift | eassumption ].
  - (* STCat1 *)
    apply ht_cat_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho Hk TStr Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STCat2 *)
    apply ht_cat_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho Hk TStr Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. econstructor; [ lift | eassumption ].
  - (* STLt1 *)
    apply ht_lt_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho Hk TInt Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STLt2 *)
    apply ht_lt_inv in Ht as [-> [Ha Hb]].
    destruct (IHHs Hh Ho Hk TInt Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. econstructor; [ lift | eassumption ].
  - (* STIf1 *)
    apply ht_if_inv in Ht as [Ha [Hb Hc]].
    destruct (IHHs Hh Ho Hk TBool Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift | lift ].
  - (* STLet1 *)
    apply ht_let_inv in Ht as [T1 [Ha Hb]].
    destruct (IHHs Hh Ho Hk T1 Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STSeq1 *)
    apply ht_seq_inv in Ht as [T1 [Ha Hb]].
    destruct (IHHs Hh Ho Hk T1 Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STSet1 *)
    apply ht_set_inv in Ht as [-> Ha].
    destruct (IHHs Hh Ho Hk (stype c) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor. assumption.
  - (* STPair1 *)
    apply ht_pair_inv in Ht as [Ta [Tb [-> [Ha Hb]]]].
    destruct (IHHs Hh Ho Hk Ta Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STPair2 *)
    apply ht_pair_inv in Ht as [Ta [Tb [-> [Ha Hb]]]].
    destruct (IHHs Hh Ho Hk Tb Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. econstructor; [ lift | eassumption ].
  - (* STFst1 *)
    apply ht_fst_inv in Ht as [Tb Ha].
    destruct (IHHs Hh Ho Hk (TPair T0 Tb) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. eapply HFst; eassumption.
  - (* STSnd1 *)
    apply ht_snd_inv in Ht as [Ta Ha].
    destruct (IHHs Hh Ho Hk (TPair Ta T0) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. eapply HSnd; eassumption.
  - (* STOk1 *)
    apply ht_ok_inv in Ht as [T1 [-> Ha]].
    destruct (IHHs Hh Ho Hk T1 Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor. assumption.
  - (* STIsOk1 *)
    apply ht_isok_inv in Ht as [-> [T1 Ha]].
    destruct (IHHs Hh Ho Hk (TRes T1) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. eapply HIsOk; eassumption.
  - (* STGetOr1 *)
    apply ht_getor_inv in Ht as [Ha Hb].
    destruct (IHHs Hh Ho Hk (TRes T0) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STSend1 *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ha [Hmt [Hb ->]]]]]].
    destruct (IHHs Hh Ho Hk (TActor c1) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. eapply HSend; [ eassumption | eassumption | lift ].
  - (* STSend2 *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ha [Hmt [Hb ->]]]]]].
    destruct (IHHs Hh Ho Hk ta1 Hb) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. eapply HSend; [ lift | eassumption | eassumption ].
  - (* STAwait1 *)
    apply ht_await_inv in Ht.
    destruct (IHHs Hh Ho Hk (TFut T0) Ht) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. constructor. assumption.
  - (* STAwaitD1 *)
    apply ht_awaitd_inv in Ht as [Ha Hd].
    destruct (IHHs Hh Ho Hk (TFut T0) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. econstructor; [ eassumption | lift ].
  - (* STAwaitR1 *)
    apply ht_awaitr_inv in Ht as [T1 [-> Ha]].
    destruct (IHHs Hh Ho Hk (TFut T1) Ha) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. eapply HAwaitR; eassumption.
  - (* STAnswer1 *)
    apply ht_answer_inv in Ht as [-> [T1 [Hr He]]].
    destruct (IHHs Hh Ho Hk (TReply T1) Hr) as [Hh' [Ho1 [Hf1 [Ha1 Hm1]]]].
    split5; try assumption. eapply HAnswer; [ eassumption | lift ].
  - (* STAnswer2 *)
    apply ht_answer_inv in Ht as [-> [T1 [Hr He]]].
    destruct (IHHs Hh Ho Hk T1 He) as [Hh' [Ho1 [Hf1 [Hb1 Hm1]]]].
    split5; try assumption. eapply HAnswer; [ lift | eassumption ].
Qed.

(* ================================================================= *)
(* 11. 表が伸びても不変条件は保たれる                                *)
(* ================================================================= *)

Lemma msg_ok_mono : forall H H' M,
  msg_ok H M -> ext (hot H) (hot H') -> ext (hft H) (hft H') -> msg_ok H' M.
Proof.
  intros H H' [[[o m] v] k] [c [ta [tr [A [B [Cv [D E]]]]]]] Hxo Hxf.
  exists c, ta, tr.
  split; [ eapply nth_ext_some; eassumption | ].
  split; [ assumption | ]. split; [ assumption | ].
  split; [ intros C' R' G'; eapply ht_mono; [ apply D | assumption | assumption ] | ].
  eapply nth_ext_some; eassumption.
Qed.

Lemma task_ok_mono : forall H H' t,
  task_ok H t -> ext (hot H) (hot H') -> ext (hft H) (hft H') -> task_ok H' t.
Proof.
  intros H H' [[o k] e] [c [T [A [B D]]]] Hxo Hxf.
  exists c, T.
  split; [ eapply nth_ext_some; eassumption | ].
  split; [ eapply nth_ext_some; eassumption | ].
  eapply ht_mono; eassumption.
Qed.

Lemma in_app_middle : forall A (x : A) l1 l2, In x (l1 ++ x :: l2).
Proof. intros. apply in_or_app. right. left. reflexivity. Qed.

(* ================================================================= *)
(* 12. 定理                                                          *)
(* ================================================================= *)

(* --- 定理 1: 理解できないメッセージは飛ばない --------------------- *)
Theorem no_method_not_understood : forall H ms ts o m v k,
  conf_ok (H, ms, ts) ->
  In (o, m, v, k) ms ->
  exists c ta tr,
       nth_error (hot H) o = Some c
    /\ mtab c m = Some (ta, tr)
    /\ (forall C R G, ht (hot H) (hft H) C R G v ta)
    /\ nth_error (hft H) k = Some tr.
Proof.
  intros H ms ts o m v k [_ [_ [Hms _]]] Hin.
  destruct (Hms _ Hin) as [c [ta [tr [A [B [Cv [D E]]]]]]].
  exists c, ta, tr. auto.
Qed.

(* --- 定理 2: 保存 ------------------------------------------------- *)
Theorem preservation : forall C C', conf_ok C -> cstep C C' -> conf_ok C'.
Proof.
  intros C C' Hok Hs. inversion Hs; subst; simpl in *;
    destruct Hok as [Hh [Hb [Hms Hts]]].
  - (* CTask *)
    assert (Hte : task_ok H (o, k, e)) by (apply Hts; apply in_app_middle).
    simpl in Hte. destruct Hte as [cc [T [Hoc [Hk Hte]]]].
    destruct (local_preservation _ _ _ _ _ _ _ _ _ _ Hh Hoc Hk Hte H0)
      as [Hh' [Hxo [Hxf [Hte' Hout]]]].
    split; [ assumption | ]. split; [ eapply ext_trans; eassumption | ].
    split.
    + intros M HM. apply in_app_or in HM. destruct HM as [HM | HM].
      * eapply msg_ok_mono; [ apply Hms; assumption | assumption | assumption ].
      * apply Hout. assumption.
    + intros t HT. apply in_app_or in HT. destruct HT as [HT | [Heq | HT]].
      * eapply task_ok_mono; [ apply Hts; apply in_or_app; left; eassumption
                            | assumption | assumption ].
      * subst t. simpl. exists cc, T.
        split; [ eapply nth_ext_some; eassumption | ].
        split; [ eapply nth_ext_some; eassumption | assumption ].
      * eapply task_ok_mono; [ apply Hts; apply in_or_app; right; right; eassumption
                            | assumption | assumption ].
  - (* CFinish *)
    assert (Hte : task_ok H (o, k, v)) by (apply Hts; apply in_app_middle).
    simpl in Hte. destruct Hte as [cc [T [Hoc [Hk Hte]]]].
    assert (Hvt : forall C' R' G', ht (hot H) (hft H) C' R' G' v T).
    { intros C' R' G'. eapply value_ht_indep; eassumption. }
    assert (Hkl : k < length (hfv H)).
    { rewrite (heap_len_fv _ Hh). eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hkl) as [ov Hov].
    split; [ | split; [ simpl; assumption | split ] ].
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * rewrite upd_length. apply (heap_len_fv _ Hh).
      * intros o2 c2 v2 A B. apply (heap_st_ok _ _ _ _ Hh A B).
      * intros k2 T2 w2 A B.
        destruct (Nat.eq_dec k2 k) as [Heqk | Hne].
        -- subst k2. rewrite (nth_upd_eq _ _ _ _ _ Hov) in B. inversion B; subst.
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
          [ apply (bodies_ok _ _ _ _ B (hot H) (hft H) Hb) | assumption | ].
        intros C' R' G'. apply D.
Qed.

Theorem preservation_star : forall C C', conf_ok C -> csteps C C' -> conf_ok C'.
Proof.
  intros C C' Hok Hs. induction Hs; [ assumption | ].
  apply IHHs. eapply preservation; eassumption.
Qed.

(* --- 定理 3: 進行 ------------------------------------------------- *)
Lemma tasks_progress : forall H ts,
  heap_ok H ->
  (forall t, In t ts -> task_ok H t) ->
  (exists ts1 o k e ts2, ts = ts1 ++ (o, k, e) :: ts2 /\
      (value e \/ exists H' out e', tstep H o k e H' out e'))
  \/ (forall o k e, In (o, k, e) ts -> awaiting H e).
Proof.
  intros H ts Hh. induction ts as [| t ts IH]; intros Hts.
  - right. intros o k e [].
  - destruct t as [[o k] e].
    assert (Hte : task_ok H (o, k, e)) by (apply Hts; left; reflexivity).
    simpl in Hte. destruct Hte as [c [T [Hoc [Hk Hte]]]].
    destruct (local_progress _ _ _ k _ _ _ _ Hh Hoc Hte (fun _ => eq_refl))
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
  - destruct (tasks_progress H ts Hh Hts) as [Hact | Hall].
    + right. left.
      destruct Hact as [ts1 [o [k [e [ts2 [-> [Hv | [H' [out [e' Hst]]]]]]]]]].
      * eexists. apply CFinish. assumption.
      * eexists. eapply CTask. eassumption.
    + destruct ts as [| t ts'].
      * left. simpl. split; reflexivity.
      * right. right. simpl. split; [ reflexivity | ].
        split; [ discriminate | assumption ].
  - right. left. destruct M as [[[o m] v] k].
    assert (Hme : msg_ok H (o, m, v, k)) by (apply Hms; left; reflexivity).
    simpl in Hme. destruct Hme as [c [ta [tr [A [B _]]]]].
    exists (H, [] ++ ms', ts ++ [(o, k, subst 0 v (mbody c m))]).
    apply (CDeliver H [] o m v k ms' ts c ta tr); assumption.
Qed.

(* --- 定理 4: 型安全性 --------------------------------------------- *)
(* 型の付いた構成から到達できる構成は、決して行き詰まらない。
   「行き詰まる」とは、終状態でも、待ち状態でもなく、しかも一歩も
   進めないことをいう。メソッド不理解・型の食い違い・存在しない
   actor/future への操作は、すべてここに落ちる。 *)
Theorem type_safety : forall C C', conf_ok C -> csteps C C' -> ~ stuck C'.
Proof.
  intros C C' Hok Hs [Hnt [Hnb Hns]].
  assert (Hok' : conf_ok C') by (eapply preservation_star; eassumption).
  destruct (progress _ Hok') as [Ht | [Hst | Hbl]]; auto.
Qed.

(* --- 定理 5: 状態の型は保たれる ----------------------------------- *)
Theorem state_type_invariant : forall C H' ms' ts',
  conf_ok C -> csteps C (H', ms', ts') ->
  forall o c v, nth_error (hot H') o = Some c -> nth_error (hst H') o = Some v ->
    value v /\ forall C0 R0 G0, ht (hot H') (hft H') C0 R0 G0 v (stype c).
Proof.
  intros C H' ms' ts' Hok Hs o c v Hoc Hsv.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [Hh _]. apply (heap_st_ok _ _ _ _ Hh Hoc Hsv).
Qed.

(* --- 定理 6: future に入る値の型は保たれる ------------------------
   委譲（answer による他人の future への書き込み）があっても、
   future に入るのは宣言した型の値だけである。 *)
Theorem future_type_invariant : forall C H' ms' ts',
  conf_ok C -> csteps C (H', ms', ts') ->
  forall k T v, nth_error (hft H') k = Some T ->
                nth_error (hfv H') k = Some (Some v) ->
    value v /\ forall C0 R0 G0, ht (hot H') (hft H') C0 R0 G0 v T.
Proof.
  intros C H' ms' ts' Hok Hs k T v Hk Hv.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [Hh _]. apply (heap_fv_ok _ _ _ _ Hh Hk Hv).
Qed.

(* --- 定理 7: 期限つきの待ちは必ず一歩進める -----------------------
   デッドロック自由は成り立たないが、期限をつけた待ちに限れば
   「待ったまま止まる」ことはない。第 2 版の主張の、意味論版である。 *)
Theorem timeout_always_progresses : forall H o k k' n d T,
  nth_error (hft H) k' = Some T ->
  exists H' out e', tstep H o k (EAwaitD (EFRef k') n d) H' out e'.
Proof. intros. exists H, (@nil msg), d. eapply STAwaitDTo. eassumption. Qed.

Lemma timeout_never_awaits : forall H k' n d,
  ~ awaiting H (EAwaitD (EFRef k') n d).
Proof. intros H k' n d Haw. inversion Haw; subst. inversion H1. Qed.

End AIPL.
