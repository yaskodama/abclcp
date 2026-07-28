(*
  哲学者の食事問題 (dining philosophers) を AIPL^- で書き、
  デッドロックを起こさないことを証明する。

  二つの層に分けて述べる。

  第 1 層  機械的デッドロック自由 (dining_no_deadlock)
      AIPL^- のプログラムそのものについての定理。初期構成から到達できる
      どの構成も blocked でなく、終状態でなければ必ず一歩進める。
      プログラムが await を一切使わない（完全非同期）ことによる。

  第 2 層  資源デッドロック自由 (no_dead_state)
      フォーク割り当てプロトコルについての定理。番号順取得
      (lo i < hi i) のもとで、どの到達可能状態にも必ず動ける哲学者がいる。
      「全員が 1 本ずつ持って永久に止まる」という古典的なデッドロックが
      起きないことを言う。

  第 1 層と第 2 層の対応（プログラムの状態が抽象状態に写ること）は
  本ファイルでは機械検証していない。この点は正直に述べる。
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import AIPLSoundness.

(* ================================================================= *)
(* 第 I 部  AIPL^- のプログラム                                      *)
(* ================================================================= *)

(*
  オブジェクト   0,1,2 = フォーク    3,4,5 = 哲学者
  クラス         0,1,2 = Fork0..2    3,4,5 = Phil0..2
  哲学者 i が使うフォークは lo i と hi i で、番号の小さい方から取る。

     哲学者 0 : フォーク 0, 1      lo=0, hi=1
     哲学者 1 : フォーク 1, 2      lo=1, hi=2
     哲学者 2 : フォーク 0, 2      lo=0, hi=2     <- ここが非対称。輪を切る

  メソッド番号
     0 req(int)   : unit   フォーク: 要求
     1 rel(unit)  : unit   フォーク: 返却
     2 go(unit)   : unit   哲学者: 思考をやめて lo を要求
     3 granted    : unit   哲学者: 要求が通った
     4 denied     : unit   哲学者: 要求が断られた（再要求）
     5 eat(unit)  : unit   哲学者: 食べて両方返す

  哲学者の状態 (int)  0=思考中  1=lo 要求中  2=lo 保持・hi 要求中  3=食事中
  フォークの状態(bool) true=空き  false=使用中
*)

Definition philObj (i : nat) : nat := 3 + i.
Definition forkObj (j : nat) : nat := j.

Definition dlo (i : nat) : nat := match i with 0 => 0 | 1 => 1 | _ => 0 end.
Definition dhi (i : nat) : nat := match i with 0 => 1 | 1 => 2 | _ => 2 end.

(* フォーク j を使う 2 人の哲学者（番号の小さい順） *)
Definition cliA (j : nat) : nat := match j with 0 => 0 | 1 => 0 | _ => 1 end.
Definition cliB (j : nat) : nat := match j with 0 => 2 | 1 => 1 | _ => 2 end.

Definition dp_stype (c : nat) : ty :=
  if c <? 3 then TBool else if c <? 6 then TInt else TUnit.

Definition dp_sinit (c : nat) : tm :=
  if c <? 3 then EBool true else if c <? 6 then ENum 0 else EUnit.

Definition dp_mtab (c m : nat) : option (ty * ty) :=
  if c <? 3 then
    match m with
    | 0 => Some (TInt, TUnit)
    | 1 => Some (TUnit, TUnit)
    | _ => None
    end
  else if c <? 6 then
    match m with
    | 2 | 3 | 4 | 5 => Some (TUnit, TUnit)
    | _ => None
    end
  else None.

(* send o.m(arg) の糖衣。future を作って捨てる *)
Definition sendTo (o m : nat) (arg : tm) : tm :=
  ELet 1 (EFSend (EORef o) m arg) EUnit.

(* --- フォークのメソッド本体 --- *)
Definition forkReq (j : nat) : tm :=
  EIf EGet
      (ELet 1 (ESet (EBool false))
         (EIf (ELt (EVar 0) (ENum (cliB j)))
              (sendTo (philObj (cliA j)) 3 EUnit)
              (sendTo (philObj (cliB j)) 3 EUnit)))
      (EIf (ELt (EVar 0) (ENum (cliB j)))
           (sendTo (philObj (cliA j)) 4 EUnit)
           (sendTo (philObj (cliB j)) 4 EUnit)).

Definition forkRel : tm := ESet (EBool true).

(* --- 哲学者のメソッド本体 --- *)
Definition philGo (i : nat) : tm :=
  ELet 1 (ESet (ENum 1)) (sendTo (forkObj (dlo i)) 0 (ENum i)).

Definition philGranted (i : nat) : tm :=
  EIf (ELt EGet (ENum 2))
      (ELet 1 (ESet (ENum 2)) (sendTo (forkObj (dhi i)) 0 (ENum i)))
      (ELet 1 (ESet (ENum 3)) (sendTo (philObj i) 5 EUnit)).

Definition philDenied (i : nat) : tm :=
  EIf (ELt EGet (ENum 2))
      (sendTo (forkObj (dlo i)) 0 (ENum i))
      (sendTo (forkObj (dhi i)) 0 (ENum i)).

Definition philEat (i : nat) : tm :=
  ELet 1 (ESet (ENum 0))
    (ELet 1 (EFSend (EORef (forkObj (dlo i))) 1 EUnit)
      (ELet 1 (EFSend (EORef (forkObj (dhi i))) 1 EUnit)
        (sendTo (philObj i) 2 EUnit))).

Definition dp_mbody (c m : nat) : tm :=
  match c, m with
  | 0, 0 => forkReq 0 | 1, 0 => forkReq 1 | 2, 0 => forkReq 2
  | 0, 1 => forkRel   | 1, 1 => forkRel   | 2, 1 => forkRel
  | 3, 2 => philGo 0  | 4, 2 => philGo 1  | 5, 2 => philGo 2
  | 3, 3 => philGranted 0 | 4, 3 => philGranted 1 | 5, 3 => philGranted 2
  | 3, 4 => philDenied 0  | 4, 4 => philDenied 1  | 5, 4 => philDenied 2
  | 3, 5 => philEat 0     | 4, 5 => philEat 1     | 5, 5 => philEat 2
  | _, _ => EUnit
  end.

(* 起動時のオブジェクト表。オブジェクト i のクラスは i *)
Definition dp_ot0 : list nat := [0; 1; 2; 3; 4; 5].

(* ================================================================= *)
(* プログラムが型検査を通ること                                      *)
(* ================================================================= *)

Lemma dp_sinit_value : forall c, value (dp_sinit c).
Proof.
  intros c. unfold dp_sinit.
  destruct (c <? 3); [ constructor | ].
  destruct (c <? 6); constructor.
Qed.

Lemma dp_sinit_ok : forall c ot ft C G,
  ht dp_stype dp_mtab ot ft C G (dp_sinit c) (dp_stype c).
Proof.
  intros c ot ft C G. unfold dp_sinit, dp_stype.
  destruct (c <? 3); [ constructor | ].
  destruct (c <? 6); constructor.
Qed.

Ltac dpty Hext :=
  repeat first
    [ reflexivity
    | (apply Hext; reflexivity)
    | econstructor ].

Lemma dp_bodies_ok : forall c m ta tr, dp_mtab c m = Some (ta, tr) ->
  forall ot ft, ext dp_ot0 ot ->
    ht dp_stype dp_mtab ot ft c (extend empty 0 ta) (dp_mbody c m) tr.
Proof.
  intros c m ta tr Hm ot ft Hext.
  destruct c as [|[|[|[|[|[|c]]]]]];
    destruct m as [|[|[|[|[|[|m]]]]]];
    simpl in Hm; try discriminate; inversion Hm; subst; clear Hm;
    simpl; unfold forkReq, forkRel, philGo, philGranted, philDenied, philEat,
                  sendTo, philObj, forkObj, cliA, cliB, dlo, dhi;
    dpty Hext.
Qed.

Lemma dp_mbody_afree : forall c m, afree (dp_mbody c m).
Proof.
  intros c m.
  destruct c as [|[|[|[|[|[|c]]]]]];
    destruct m as [|[|[|[|[|[|m]]]]]];
    simpl; unfold forkReq, forkRel, philGo, philGranted, philDenied, philEat,
                  sendTo;
    repeat constructor.
Qed.

(* ================================================================= *)
(* 初期構成                                                          *)
(* ================================================================= *)

Definition dp_H0 : heap :=
  Heap dp_ot0
       [EBool true; EBool true; EBool true; ENum 0; ENum 0; ENum 0]
       [TUnit; TUnit; TUnit]
       [None; None; None].

(* 3 人の哲学者に go を送った状態から始める *)
Definition dp_C0 : conf :=
  (dp_H0,
   [(philObj 0, 2, EUnit, 0); (philObj 1, 2, EUnit, 1); (philObj 2, 2, EUnit, 2)],
   []).

Lemma dp_heap_ok : heap_ok dp_stype dp_mtab dp_H0.
Proof.
  unfold heap_ok, dp_H0, dp_ot0; simpl.
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split.
  { intros o c v Ho Hv.
    destruct o as [|[|[|[|[|[|o]]]]]]; simpl in Ho, Hv;
      try discriminate; try (destruct o; discriminate);
      inversion Ho; inversion Hv; subst; unfold dp_stype; simpl;
      split; try (apply VBool); try (apply VNum);
      intros; try (apply HBool); try (apply HNum). }
  { intros k T v Hk Hv.
    destruct k as [|[|[|k]]]; simpl in Hk, Hv;
      try discriminate; destruct k; discriminate. }
Qed.

Lemma dp_conf_ok : conf_ok dp_stype dp_mtab dp_ot0 dp_C0.
Proof.
  unfold conf_ok, dp_C0. split; [ apply dp_heap_ok | ].
  split; [ simpl; apply ext_refl | ]. split.
  - intros M HM. simpl in HM.
    destruct HM as [<- | [<- | [<- | []]]];
      simpl; unfold philObj; simpl;
      [ exists 3, TUnit, TUnit | exists 4, TUnit, TUnit | exists 5, TUnit, TUnit ];
      repeat split; try reflexivity; try constructor; intros; constructor.
  - intros t [].
Qed.

Lemma dp_conf_afree : conf_afree dp_C0.
Proof. intros o k e []. Qed.

(* ================================================================= *)
(* 第 1 層の定理: 機械的デッドロック自由                             *)
(* ================================================================= *)

Theorem dining_no_deadlock : forall C',
  csteps dp_sinit dp_mtab dp_mbody dp_C0 C' ->
     conf_ok dp_stype dp_mtab dp_ot0 C'
  /\ conf_afree C'
  /\ ~ blocked C'
  /\ (terminal C' \/ exists C'', cstep dp_sinit dp_mtab dp_mbody C' C'').
Proof.
  intros C' Hs.
  eapply async_deadlock_free with (C := dp_C0).
  - apply dp_sinit_value.
  - apply dp_sinit_ok.
  - apply dp_bodies_ok.
  - apply dp_mbody_afree.
  - apply dp_conf_ok.
  - apply dp_conf_afree.
  - exact Hs.
Qed.

(* ================================================================= *)
(* 第 II 部  フォーク割り当てプロトコル                              *)
(* ================================================================= *)

Inductive pstate : Type := Think | Hold | Eat.

Lemma pstate_eq_dec : forall a b : pstate, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition upn {A : Type} (f : nat -> A) (x : nat) (v : A) : nat -> A :=
  fun y => if Nat.eqb y x then v else f y.

Lemma upn_eq : forall A (f : nat -> A) x v, upn f x v x = v.
Proof. intros. unfold upn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upn_neq : forall A (f : nat -> A) x v y, y <> x -> upn f x v y = f y.
Proof.
  intros. unfold upn. destruct (Nat.eqb y x) eqn:E; [ | reflexivity ].
  apply Nat.eqb_eq in E. contradiction.
Qed.

Section Protocol.

Variable n : nat.                 (* 哲学者の数 = フォークの数 *)
Variable lo hi : nat -> nat.      (* 哲学者 i が使う 2 本。番号順に取る *)

Hypothesis lo_lt_hi : forall i, i < n -> lo i < hi i.

Record pst : Type := St {
  phase : nat -> pstate;          (* 哲学者 -> 状態 *)
  own   : nat -> option nat       (* フォーク -> 保持者 *)
}.

(* 状態の健全性 *)
Definition wf (s : pst) : Prop :=
  (forall f i, own s f = Some i -> i < n) /\
  (forall i, i < n -> phase s i = Think -> forall f, own s f <> Some i) /\
  (forall i, i < n -> phase s i = Hold ->
       own s (lo i) = Some i /\ (forall f, own s f = Some i -> f = lo i)) /\
  (forall i, i < n -> phase s i = Eat ->
       own s (lo i) = Some i /\ own s (hi i) = Some i).

Inductive pstep : pst -> pst -> Prop :=
(* 思考中の哲学者が、空いている lo を取る *)
| TakeLo : forall s i, i < n -> phase s i = Think -> own s (lo i) = None ->
    pstep s (St (upn (phase s) i Hold) (upn (own s) (lo i) (Some i)))
(* lo を持つ哲学者が、空いている hi を取って食べ始める *)
| TakeHi : forall s i, i < n -> phase s i = Hold -> own s (hi i) = None ->
    pstep s (St (upn (phase s) i Eat) (upn (own s) (hi i) (Some i)))
(* 食べ終わって両方返す *)
| Release : forall s i, i < n -> phase s i = Eat ->
    pstep s (St (upn (phase s) i Think)
                (upn (upn (own s) (lo i) None) (hi i) None)).

(* --- 補助: 有界な述語についての最大元。決定可能性から直接構成する --- *)
Lemma max_over : forall (P : nat -> bool) (f : nat -> nat) (N : nat),
  (exists i, i < N /\ P i = true) ->
  exists p, p < N /\ P p = true /\ (forall q, q < N -> P q = true -> f q <= f p).
Proof.
  intros P f N. induction N as [| N IH]; intros [i [Hi HP]]; [ lia | ].
  destruct (P N) eqn:EN.
  - (* 上端 N が P を満たす *)
    destruct (le_gt_dec N i) as [Hle | Hgt].
    + (* i = N しかありえない。N のみが候補になるかもしれないので分岐 *)
      destruct (Nat.eq_dec i N) as [-> | Hne]; [ | lia ].
      (* N より下に P があるかどうか *)
      destruct (Nat.eq_dec N 0) as [-> | Hn0].
      * exists 0. split; [ lia | ]. split; [ assumption | ].
        intros q Hq _. assert (q = 0) by lia. subst. lia.
      * assert (Hcase : (exists j, j < N /\ P j = true) \/
                        (forall j, j < N -> P j = false)).
        { clear. induction N as [| N IHN].
          - right. intros j Hj. lia.
          - destruct IHN as [[j [Hj Hpj]] | Hall].
            + left. exists j. split; [ lia | assumption ].
            + destruct (P N) eqn:E.
              * left. exists N. split; [ lia | assumption ].
              * right. intros j Hj.
                destruct (Nat.eq_dec j N) as [-> | Hne2]; [ assumption | ].
                apply Hall. lia. }
        destruct Hcase as [Hex | Hall].
        -- destruct (IH Hex) as [p [Hp [Hpp Hmax]]].
           destruct (le_gt_dec (f N) (f p)) as [Hle2 | Hgt2].
           ++ exists p. split; [ lia | ]. split; [ assumption | ].
              intros q Hq Hpq.
              destruct (Nat.eq_dec q N) as [-> | Hne2]; [ assumption | ].
              apply Hmax; [ lia | assumption ].
           ++ exists N. split; [ lia | ]. split; [ assumption | ].
              intros q Hq Hpq.
              destruct (Nat.eq_dec q N) as [-> | Hne2]; [ lia | ].
              assert (f q <= f p) by (apply Hmax; [ lia | assumption ]). lia.
        -- exists N. split; [ lia | ]. split; [ assumption | ].
           intros q Hq Hpq.
           destruct (Nat.eq_dec q N) as [-> | Hne2]; [ lia | ].
           rewrite Hall in Hpq; [ discriminate | lia ].
    + (* i < N なので下側にも候補がある *)
      destruct (IH (ex_intro _ i (conj Hgt HP))) as [p [Hp [Hpp Hmax]]].
      destruct (le_gt_dec (f N) (f p)) as [Hle2 | Hgt2].
      * exists p. split; [ lia | ]. split; [ assumption | ].
        intros q Hq Hpq.
        destruct (Nat.eq_dec q N) as [-> | Hne2]; [ assumption | ].
        apply Hmax; [ lia | assumption ].
      * exists N. split; [ lia | ]. split; [ assumption | ].
        intros q Hq Hpq.
        destruct (Nat.eq_dec q N) as [-> | Hne2]; [ lia | ].
        assert (f q <= f p) by (apply Hmax; [ lia | assumption ]). lia.
  - (* 上端 N は P を満たさない。よって i < N *)
    assert (Hi' : i < N).
    { destruct (Nat.eq_dec i N) as [-> | Hne]; [ congruence | lia ]. }
    destruct (IH (ex_intro _ i (conj Hi' HP))) as [p [Hp [Hpp Hmax]]].
    exists p. split; [ lia | ]. split; [ assumption | ].
    intros q Hq Hpq.
    destruct (Nat.eq_dec q N) as [-> | Hne2]; [ congruence | ].
    apply Hmax; [ lia | assumption ].
Qed.

(* 状態の判定を bool に落とす *)
Definition isHold (s : pst) (i : nat) : bool :=
  match phase s i with Hold => true | _ => false end.

(* 有界な場合分け: 動ける哲学者がいるか、全員詰まっているか *)
Lemma classify : forall (s : pst) (N : nat),
  (exists i, i < N /\ phase s i = Eat) \/
  (exists i, i < N /\ phase s i = Hold /\ own s (hi i) = None) \/
  (exists i, i < N /\ phase s i = Think /\ own s (lo i) = None) \/
  ((forall i, i < N -> phase s i <> Eat) /\
   (forall i, i < N -> phase s i = Hold -> own s (hi i) <> None) /\
   (forall i, i < N -> phase s i = Think -> own s (lo i) <> None)).
Proof.
  intros s N. induction N as [| N IH].
  - right; right; right. repeat split; intros i Hi; lia.
  - destruct IH as [[i [Hi HE]] | [[i [Hi [HH HF]]] | [[i [Hi [HT HF]]] | [A [B C]]]]].
    + left. exists i. split; [ lia | assumption ].
    + right; left. exists i. split; [ lia | split; assumption ].
    + right; right; left. exists i. split; [ lia | split; assumption ].
    + destruct (phase s N) eqn:EN.
      * (* Think *)
        destruct (own s (lo N)) eqn:EL.
        -- right; right; right. repeat split.
           ++ intros i Hi. destruct (Nat.eq_dec i N) as [-> | Hne];
                [ rewrite EN; discriminate | apply A; lia ].
           ++ intros i Hi HH. destruct (Nat.eq_dec i N) as [-> | Hne];
                [ rewrite EN in HH; discriminate | apply B; [ lia | assumption ] ].
           ++ intros i Hi HT. destruct (Nat.eq_dec i N) as [-> | Hne];
                [ rewrite EL; discriminate | apply C; [ lia | assumption ] ].
        -- right; right; left. exists N. split; [ lia | split; assumption ].
      * (* Hold *)
        destruct (own s (hi N)) eqn:EL.
        -- right; right; right. repeat split.
           ++ intros i Hi. destruct (Nat.eq_dec i N) as [-> | Hne];
                [ rewrite EN; discriminate | apply A; lia ].
           ++ intros i Hi HH. destruct (Nat.eq_dec i N) as [-> | Hne];
                [ rewrite EL; discriminate | apply B; [ lia | assumption ] ].
           ++ intros i Hi HT. destruct (Nat.eq_dec i N) as [-> | Hne];
                [ rewrite EN in HT; discriminate | apply C; [ lia | assumption ] ].
        -- right; left. exists N. split; [ lia | split; assumption ].
      * (* Eat *) left. exists N. split; [ lia | assumption ].
Qed.

Lemma hold_dec : forall (s : pst) (N : nat),
  (exists i, i < N /\ isHold s i = true) \/ (forall i, i < N -> isHold s i = false).
Proof.
  intros s N. induction N as [| N IH].
  - right. intros i Hi. lia.
  - destruct IH as [[i [Hi Hh]] | Hall].
    + left. exists i. split; [ lia | assumption ].
    + destruct (isHold s N) eqn:E.
      * left. exists N. split; [ lia | assumption ].
      * right. intros i Hi. destruct (Nat.eq_dec i N) as [-> | Hne];
          [ assumption | apply Hall; lia ].
Qed.

(* --- 第 2 層の定理: 動けない状態は存在しない --- *)
Theorem no_dead_state : forall s,
  0 < n -> wf s -> exists s', pstep s s'.
Proof.
  intros s Hn [Wn [Wt [Wh We]]].
  destruct (classify s n)
    as [[i [Hi HE]] | [[i [Hi [HH HF]]] | [[i [Hi [HT HF]]] | [A [B C]]]]].
  - eexists. apply (Release s i Hi HE).
  - eexists. apply (TakeHi s i Hi HH HF).
  - eexists. apply (TakeLo s i Hi HT HF).
  - (* 全員詰まっているとして矛盾を導く *)
    exfalso.
    destruct (hold_dec s n) as [Hex | Hnone].
    + (* hi が最大の Hold 哲学者を取る *)
      destruct (max_over (isHold s) hi n Hex) as [p [Hp [Hph Hmax]]].
      assert (Hpp : phase s p = Hold).
      { unfold isHold in Hph. destruct (phase s p); congruence. }
      destruct (own s (hi p)) as [q |] eqn:Eq;
        [ | apply (B p Hp Hpp); assumption ].
      assert (Hq : q < n) by (eapply Wn; eauto).
      assert (Hqp : phase s q = Hold).
      { destruct (phase s q) eqn:EQ.
        - exfalso. apply (Wt q Hq EQ (hi p)). assumption.
        - reflexivity.
        - exfalso. apply (A q Hq). assumption. }
      destruct (Wh q Hq Hqp) as [_ Honly].
      assert (Hloq : hi p = lo q) by (apply Honly; assumption).
      assert (Hlt : lo q < hi q) by (apply lo_lt_hi; assumption).
      assert (Hmaxq : hi q <= hi p).
      { apply Hmax; [ assumption | unfold isHold; rewrite Hqp; reflexivity ]. }
      lia.
    + (* Hold が一人もいない。すると誰もフォークを持っていない *)
      assert (Hfree : forall f i, own s f <> Some i).
      { intros f i Hcon.
        assert (Hi : i < n) by (eapply Wn; eauto).
        destruct (phase s i) eqn:EI.
        - apply (Wt i Hi EI f). assumption.
        - specialize (Hnone i Hi). unfold isHold in Hnone.
          rewrite EI in Hnone. discriminate.
        - apply (A i Hi). assumption. }
      destruct (phase s 0) eqn:E0.
      * apply (C 0 Hn E0). destruct (own s (lo 0)) eqn:EL;
          [ exfalso; eapply Hfree; eassumption | reflexivity ].
      * specialize (Hnone 0 Hn). unfold isHold in Hnone.
        rewrite E0 in Hnone. discriminate.
      * apply (A 0 Hn). assumption.
Qed.

End Protocol.

(* ================================================================= *)
(* プログラムの lo/hi が番号順であること                             *)
(* ================================================================= *)

Lemma dp_ordered : forall i, i < 3 -> dlo i < dhi i.
Proof.
  intros i Hi. destruct i as [|[|[|i]]]; simpl; lia.
Qed.

(* 第 2 層の定理を、このプログラムのフォーク割り当てに適用したもの *)
Corollary dining_no_resource_deadlock : forall s,
  wf 3 dlo dhi s -> exists s', pstep 3 dlo dhi s s'.
Proof.
  intros s Hwf. eapply no_dead_state; [ apply dp_ordered | lia | exact Hwf ].
Qed.

(* ================================================================= *)
(* 第 III 部  優先度規律 ---- セッション型から見た定式化              *)
(* ================================================================= *)

(*
  二者間セッション型は「哲学者とフォークの間のやりとりの順序」を保証するが、
  複数セッションにまたがるデッドロックは排除できない。哲学者の食事問題は
  まさにその標準的な反例である。デッドロックまで型で排除するには、
  資源に優先度（レベル）を与え、優先度の昇順にしか獲得できないことを
  型規律にする（Kobayashi の usage 型、Dardha--Gay の priority-based
  session types などがこの系統）。

  ここでは、その優先度規律を prio_ordered として書き、
    「優先度規律を満たす -> 資源デッドロックしない」          (十分性)
    「優先度規律を落とすと実際に詰まる状態がある」            (必要性)
  の両方を証明する。前者の証明 (no_dead_state) が、この型規律の
  健全性証明そのものである。
*)

Definition prio_ordered (n : nat) (lo hi : nat -> nat) : Prop :=
  forall i, i < n -> lo i < hi i.

(* 十分性 *)
Theorem priority_implies_deadlock_free : forall n lo hi s,
  prio_ordered n lo hi -> 0 < n -> wf n lo hi s -> exists s', pstep n lo hi s s'.
Proof. intros n lo hi s Hp Hn Hw. eapply no_dead_state; eauto. Qed.

(* 必要性: 素朴な「左を取って右を取る」割り当ては優先度規律を満たさず、
   実際に一歩も動けない状態を持つ *)
Definition nlo (i : nat) : nat := i.
Definition nhi (i : nat) : nat := match i with 0 => 1 | 1 => 2 | _ => 0 end.

Lemma naive_not_ordered : ~ prio_ordered 3 nlo nhi.
Proof.
  intros H. assert (H2 : 2 < 3) by lia.
  specialize (H 2 H2). unfold nlo, nhi in H. simpl in H. lia.
Qed.

(* 全員が自分の左のフォークを持ったまま止まっている状態 *)
Definition deadS : pst :=
  St (fun _ => Hold) (fun f => if f <? 3 then Some f else None).

Lemma deadS_own : forall f i, own deadS f = Some i -> f = i /\ i < 3.
Proof.
  intros f i H. simpl in H. destruct (f <? 3) eqn:E; [ | discriminate ].
  inversion H; subst. apply Nat.ltb_lt in E. split; [ reflexivity | assumption ].
Qed.

Lemma deadS_wf : wf 3 nlo nhi deadS.
Proof.
  unfold wf. split; [ | split; [ | split ] ].
  - intros f i H. apply (deadS_own f i H).
  - intros i Hi HT. simpl in HT. discriminate.
  - intros i Hi HH. split.
    + unfold nlo. simpl. apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
    + intros f Hf. destruct (deadS_own f i Hf) as [-> _]. reflexivity.
  - intros i Hi HE. simpl in HE. discriminate.
Qed.

Lemma deadS_stuck : ~ exists s', pstep 3 nlo nhi deadS s'.
Proof.
  intros [s' Hst]. inversion Hst; subst; simpl in *; try discriminate.
  (* TakeHi: nhi i は 0,1,2 のいずれかで、すべて誰かが持っている *)
  destruct i as [|[|[|i]]]; unfold nhi in *; simpl in *;
    try discriminate; lia.
Qed.

(* まとめ: 優先度規律は十分であり、かつ捨てられない *)
Theorem ordering_is_necessary_and_sufficient :
  (prio_ordered 3 dlo dhi /\ forall s, wf 3 dlo dhi s -> exists s', pstep 3 dlo dhi s s')
  /\ (~ prio_ordered 3 nlo nhi /\ wf 3 nlo nhi deadS
      /\ ~ exists s', pstep 3 nlo nhi deadS s').
Proof.
  split.
  - split; [ exact dp_ordered | ].
    intros s Hw. eapply no_dead_state; [ exact dp_ordered | lia | exact Hw ].
  - split; [ exact naive_not_ordered | ].
    split; [ exact deadS_wf | exact deadS_stuck ].
Qed.
