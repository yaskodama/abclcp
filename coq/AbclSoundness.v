From Stdlib Require Import List String Arith Lia.
Import ListNotations.
Open Scope string_scope.

(*
  A small mechanized core for the ABCL/c+ report.

  The implementation in src/ is an actor language with Hindley-Milner style
  inference, actor method tables, future/await, and a runtime linear session
  checker.  This Coq file intentionally formalizes only the stable core needed
  for a type-soundness argument:

  - first-order values and expressions,
  - future/await as a typed result handle,
  - standard progress and preservation,
  - the runtime session checker as a linear protocol automaton.
*)

Inductive ty : Type :=
| TNat
| TString
| TUnit
| TAny
| TFuture (t : ty).

Inductive expr : Type :=
| ENat (n : nat)
| EString (s : string)
| EUnit
| EAdd (e1 e2 : expr)
| EFutureValue (v : expr)
| EAwait (e : expr).

Inductive value : expr -> Prop :=
| VNat : forall n, value (ENat n)
| VString : forall s, value (EString s)
| VUnit : value EUnit
| VFutureValue : forall v, value v -> value (EFutureValue v).

Inductive has_type : expr -> ty -> Prop :=
| T_Nat : forall n,
    has_type (ENat n) TNat
| T_String : forall s,
    has_type (EString s) TString
| T_Unit :
    has_type EUnit TUnit
| T_Add : forall e1 e2,
    has_type e1 TNat ->
    has_type e2 TNat ->
    has_type (EAdd e1 e2) TNat
| T_Future : forall v t,
    value v ->
    has_type v t ->
    has_type (EFutureValue v) (TFuture t)
| T_Await : forall e t,
    has_type e (TFuture t) ->
    has_type (EAwait e) t.

Inductive step : expr -> expr -> Prop :=
| ST_AddNat : forall n1 n2,
    step (EAdd (ENat n1) (ENat n2)) (ENat (n1 + n2))
| ST_Add1 : forall e1 e1' e2,
    step e1 e1' ->
    step (EAdd e1 e2) (EAdd e1' e2)
| ST_Add2 : forall n1 e2 e2',
    step e2 e2' ->
    step (EAdd (ENat n1) e2) (EAdd (ENat n1) e2')
| ST_Await1 : forall e e',
    step e e' ->
    step (EAwait e) (EAwait e')
| ST_AwaitFuture : forall v,
    value v ->
    step (EAwait (EFutureValue v)) v.

Lemma canonical_nat : forall e,
  value e -> has_type e TNat -> exists n, e = ENat n.
Proof.
  intros e Hv Ht. inversion Hv; subst; inversion Ht; subst; eauto.
Qed.

Lemma canonical_future : forall e t,
  value e -> has_type e (TFuture t) ->
  exists v, e = EFutureValue v /\ value v /\ has_type v t.
Proof.
  intros e t Hv Ht. inversion Hv; subst; inversion Ht; subst; eauto.
Qed.

Theorem preservation : forall e e' t,
  has_type e t -> step e e' -> has_type e' t.
Proof.
  intros e e' t Hty Hstep.
  generalize dependent t.
  induction Hstep; intros t Hty; inversion Hty; subst.
  - constructor.
  - constructor; [apply IHHstep; assumption | assumption].
  - constructor; [assumption | apply IHHstep; assumption].
  - constructor. apply IHHstep. assumption.
  - match goal with
    | H : has_type (EFutureValue _) (TFuture _) |- _ =>
        inversion H; subst; assumption
    end.
Qed.

Theorem progress : forall e t,
  has_type e t -> value e \/ exists e', step e e'.
Proof.
  intros e t Hty.
  induction Hty; eauto using value.
  - destruct IHHty1 as [Hv1 | [e1' Hs1]].
    + destruct (canonical_nat _ Hv1 Hty1) as [n1 ->].
      destruct IHHty2 as [Hv2 | [e2' Hs2]].
      * destruct (canonical_nat _ Hv2 Hty2) as [n2 ->].
        right. exists (ENat (n1 + n2)). constructor.
      * right. exists (EAdd (ENat n1) e2'). constructor. exact Hs2.
    + right. exists (EAdd e1' e2). constructor. exact Hs1.
  - destruct IHHty as [Hv | [e' Hs]].
    + destruct (canonical_future _ _ Hv Hty) as [v [-> [Hvv Hvt]]].
      right. exists v. constructor. exact Hvv.
    + right. exists (EAwait e'). constructor. exact Hs.
Qed.

Record label : Type := {
  actor_name : string;
  method_name : string
}.

Definition protocol := list label.

Inductive send_ok : protocol -> nat -> label -> nat -> Prop :=
| SendOk : forall p pos l,
    nth_error p pos = Some l ->
    send_ok p pos l (S pos).

Definition complete (p : protocol) (pos : nat) : Prop :=
  pos = List.length p.

Theorem send_ok_unique : forall p pos l pos1 pos2,
  send_ok p pos l pos1 ->
  send_ok p pos l pos2 ->
  pos1 = pos2.
Proof.
  intros p pos l pos1 pos2 H1 H2.
  inversion H1; subst. inversion H2; subst. reflexivity.
Qed.

Theorem send_ok_advances_one : forall p pos l pos',
  send_ok p pos l pos' ->
  pos' = S pos.
Proof.
  intros p pos l pos' H. inversion H; reflexivity.
Qed.

Theorem complete_rejects_next : forall p l,
  ~ exists pos', send_ok p (List.length p) l pos'.
Proof.
  intros p l [pos' H].
  inversion H; subst.
  assert (Hnone : nth_error p (List.length p) = None).
  { apply nth_error_None. lia. }
  match goal with
  | Hnth : nth_error p (List.length p) = Some _ |- _ =>
      rewrite Hnone in Hnth; discriminate
  end.
Qed.

Theorem wrong_label_rejected : forall p pos expected got pos',
  nth_error p pos = Some expected ->
  expected <> got ->
  ~ send_ok p pos got pos'.
Proof.
  intros p pos expected got pos' Hnth Hneq Hok.
  inversion Hok; subst.
  match goal with
  | Hgot : nth_error p pos = Some got |- _ =>
      rewrite Hnth in Hgot; inversion Hgot; subst; contradiction
  end.
Qed.

Theorem send_ok_within_protocol : forall p pos l pos',
  send_ok p pos l pos' ->
  pos < List.length p /\ pos' <= List.length p.
Proof.
  intros p pos l pos' H.
  inversion H; subst.
  assert (Hlt : pos < List.length p).
  { apply nth_error_Some.
    match goal with
    | Hnth : nth_error p pos = Some _ |- _ =>
        rewrite Hnth; discriminate
    end. }
  split; lia.
Qed.
