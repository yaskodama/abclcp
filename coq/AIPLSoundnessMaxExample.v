(*
  AIPLSoundnessMax.v の定理が空虚でないことの確認と、
  「ここが上限である」ことの確認。

  (A) 仮定（sinit_value / sinit_ok / bodies_ok）を満たす具体的なプログラムを
      一つ与える。そのプログラムは、AIPLSoundness2 では書けない機構
      ---- 一級の返答先による委譲 ---- を使う。

        class Worker {                              // クラス 0
          method add(x : int) : int  { var y = state + x; state = y; y }
          method serve(r : reply<int>) : unit { answer r 7 }   // 他人の返答先に答える
        }
        class Front {                               // クラス 1
          method ask(x : int) : int { var f = future w.serve(replyto); 0 }
        }

      Front.ask は自分の返答先 replyto を Worker へ渡す。
      AIPLSoundness2 の義務レベルでは、この委譲は書けない
      （返答の義務が、レベルの高い側から低い側へ移ってしまう）。

  (B) 型の付いた構成でありながら、全タスクが待ち合ったまま止まる構成を
      一つ与える。したがってこの断片では deadlock_free は成り立たない。
      それでも type_safety は成り立つ ---- 行き詰まり（stuck）ではない。
*)
From Stdlib Require Import List Arith.
Import ListNotations.
Require Import AIPLSoundnessMax.

Definition ex_stype (c : nat) : ty := TInt.
Definition ex_sinit (c : nat) : tm := ENum 0.

Definition ex_mtab (c m : nat) : option (ty * ty) :=
  match c, m with
  | 0, 0 => Some (TInt, TInt)                (* Worker.add   *)
  | 0, 1 => Some (TReply TInt, TUnit)        (* Worker.serve *)
  | 1, 0 => Some (TInt, TInt)                (* Front.ask    *)
  | _, _ => None
  end.

Definition ex_ot0 : list nat := [0; 1].      (* 0 番に Worker、1 番に Front *)

Definition ex_mbody (c m : nat) : tm :=
  match c, m with
  (* var y = state + x; state = y; y *)
  | 0, 0 => ELet 1 (EAdd EGet (EVar 0)) (ESeq (ESet (EVar 1)) (EVar 1))
  (* answer r 7 : 渡された返答先へ、自分から答える *)
  | 0, 1 => EAnswer (EVar 0) (ENum 7)
  (* var f = future worker.serve(replyto); 0 *)
  | 1, 0 => ELet 1 (EFSend (EORef 0) 1 EReplyTo) (ENum 0)
  | _, _ => EUnit
  end.

Lemma ex_sinit_value : forall c, value (ex_sinit c).
Proof. intros. constructor. Qed.

Lemma ex_sinit_ok : forall c ot ft C R G,
  ht ex_stype ex_mtab ot ft C R G (ex_sinit c) (ex_stype c).
Proof. intros. constructor. Qed.

Lemma ex_bodies_ok : forall c m ta tr, ex_mtab c m = Some (ta, tr) ->
  forall ot ft, ext ex_ot0 ot ->
    ht ex_stype ex_mtab ot ft c tr (extend empty 0 ta) (ex_mbody c m) tr.
Proof.
  intros c m ta tr Hm ot ft Hext.
  destruct c as [| [| c']]; destruct m as [| [| m']]; simpl in Hm;
    try discriminate; inversion Hm; subst; simpl.
  - (* Worker.add *)
    eapply HLet.
    + eapply HAdd; [ apply HGet | constructor; unfold extend; simpl; reflexivity ].
    + eapply HSeq.
      * apply HSet. constructor. unfold extend. simpl. reflexivity.
      * constructor. unfold extend. simpl. reflexivity.
  - (* Worker.serve: 引数の返答先へ answer *)
    eapply HAnswer.
    + constructor. unfold extend. simpl. reflexivity.
    + constructor.
  - (* Front.ask: replyto を渡して送る *)
    eapply HLet.
    + eapply HSend with (c := 0) (ta := TReply TInt) (tr := TUnit).
      * constructor. destruct Hext as [d ->]. simpl. reflexivity.
      * simpl. reflexivity.
      * (* ★ replyto : reply<int>。Front.ask の返り値型が int だから通る *)
        apply HReplyTo.
    + constructor.
Qed.

(* ================================================================= *)
(* (A) 動いている構成                                                *)
(* ================================================================= *)

(* Front.ask の本体が走っているところ。future 0 は Front.ask の返答先 *)
Definition ex_heap : heap :=
  Heap [0; 1] [ENum 0; ENum 0] [TInt] [None].
Definition ex_conf : conf :=
  (ex_heap, @nil msg, [(1, 0, ex_mbody 1 0)]).

Lemma ex_conf_ok : conf_ok ex_stype ex_mtab ex_ot0 ex_conf.
Proof.
  unfold ex_conf, ex_heap, conf_ok. simpl.
  split; [ | split; [ | split ] ].
  - unfold heap_ok; simpl.
    split; [ reflexivity | ]. split; [ reflexivity | ]. split.
    + intros o c v Hoc Hsv.
      destruct o as [| [| o']]; simpl in *;
        [ | | destruct o'; simpl in Hoc; discriminate ];
        inversion Hoc; inversion Hsv; subst;
        (split; [ apply VNum | intros; unfold ex_stype; apply HNum ]).
    + intros k T v Hk Hv.
      destruct k as [| k']; simpl in Hv; [ discriminate | ].
      destruct k'; simpl in Hv; discriminate.
  - apply ext_refl.
  - intros M [].
  - intros t [<- | []]. simpl. exists 1, TInt.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    simpl. eapply HLet.
    + eapply HSend with (c := 0) (ta := TReply TInt) (tr := TUnit).
      * constructor. simpl. reflexivity.
      * simpl. reflexivity.
      * apply HReplyTo.
    + constructor.
Qed.

(* 一歩進める（終状態でも待ち状態でもない） *)
Corollary ex_can_step :
  exists C', cstep ex_sinit ex_mtab ex_mbody ex_conf C'.
Proof.
  destruct (progress ex_stype ex_sinit ex_mtab ex_mbody ex_ot0 ex_conf ex_conf_ok)
    as [[_ Hnil] | [Hst | [_ [_ Hall]]]].
  - discriminate.
  - assumption.
  - exfalso.
    assert (Haw : awaiting ex_heap (ex_mbody 1 0))
      by (apply (Hall 1 0); left; reflexivity).
    simpl in Haw.
    repeat match goal with
    | Hx : awaiting _ _ |- _ => inversion Hx; subst; clear Hx
    end.
Qed.

(* 型安全性は、この構成から到達できるどの構成についても言える *)
Corollary ex_never_stuck : forall C',
  csteps ex_sinit ex_mtab ex_mbody ex_conf C' ->
  ~ stuck ex_sinit ex_mtab ex_mbody C'.
Proof.
  intros C' Hs.
  eapply type_safety;
    [ apply ex_sinit_value | apply ex_sinit_ok | apply ex_bodies_ok
    | apply ex_conf_ok | eassumption ].
Qed.

(* ================================================================= *)
(* (B) 上限であることの確認: 型は付くが、デッドロックする            *)
(* ================================================================= *)

(* future 0 は actor 0 のタスクが埋める。future 1 は actor 1 のタスクが埋める。
   ところが actor 0 は future 1 を待ち、actor 1 は future 0 を待っている。
   どちらの待ちにも期限が無い。義務レベルが無いので、これに型が付いてしまう。 *)
Definition dl_heap : heap :=
  Heap [0; 1] [ENum 0; ENum 0] [TInt; TInt] [None; None].
Definition dl_conf : conf :=
  (dl_heap, @nil msg, [(0, 0, EAwait (EFRef 1)); (1, 1, EAwait (EFRef 0))]).

Lemma dl_conf_ok : conf_ok ex_stype ex_mtab ex_ot0 dl_conf.
Proof.
  unfold dl_conf, dl_heap, conf_ok. simpl.
  split; [ | split; [ | split ] ].
  - unfold heap_ok; simpl.
    split; [ reflexivity | ]. split; [ reflexivity | ]. split.
    + intros o c v Hoc Hsv.
      destruct o as [| [| o']]; simpl in *;
        [ | | destruct o'; simpl in Hoc; discriminate ];
        inversion Hoc; inversion Hsv; subst;
        (split; [ apply VNum | intros; unfold ex_stype; apply HNum ]).
    + intros k T v Hk Hv.
      destruct k as [| [| k']]; simpl in Hv; try discriminate.
      destruct k'; simpl in Hv; discriminate.
  - apply ext_refl.
  - intros M [].
  - intros t [<- | [<- | []]]; simpl.
    + exists 0, TInt. split; [ reflexivity | ]. split; [ reflexivity | ].
      apply HAwait. constructor. simpl. reflexivity.
    + exists 1, TInt. split; [ reflexivity | ]. split; [ reflexivity | ].
      apply HAwait. constructor. simpl. reflexivity.
Qed.

Lemma dl_blocked : blocked dl_conf.
Proof.
  unfold dl_conf, blocked. simpl.
  split; [ reflexivity | ]. split; [ discriminate | ].
  intros o k e [Heq | [Heq | []]]; inversion Heq; subst;
    apply AwHere; simpl; reflexivity.
Qed.

(* ★ この断片では、デッドロック自由は成り立たない。
   AIPLSoundness2 の deadlock_free は、義務レベルと prod_ok を捨てた
   とたんに失われる。これが「型健全性・型安全性だけを求めるときの上限」
   の意味である。 *)
Theorem max_admits_deadlock :
  conf_ok ex_stype ex_mtab ex_ot0 dl_conf /\ blocked dl_conf.
Proof. split; [ apply dl_conf_ok | apply dl_blocked ]. Qed.

Corollary max_is_not_deadlock_free :
  ~ (forall C, conf_ok ex_stype ex_mtab ex_ot0 C -> ~ blocked C).
Proof.
  intros Hall. apply (Hall dl_conf dl_conf_ok). apply dl_blocked.
Qed.

(* それでも型安全性は失われない。待っているのであって、壊れてはいない。 *)
Corollary dl_not_stuck : ~ stuck ex_sinit ex_mtab ex_mbody dl_conf.
Proof.
  eapply type_safety;
    [ apply ex_sinit_value | apply ex_sinit_ok | apply ex_bodies_ok
    | apply dl_conf_ok | apply CSRefl ].
Qed.
