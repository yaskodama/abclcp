(*
  【未完成 / WIP】ABCM -> AIPL^- 構成レベルのシミュレーション

  ★ このファイルはコンパイルを通りません。Makefile からも外してあります。
     ABCMEmbedding.v（通る）の続きとして、次回に仕上げる分です。

  現状
  ----
  静的な埋め込み（tr_ht, e_bodies_ok）と、局所簡約・送出の対応
  （tr_step は 1 歩、tr_estep は 2 歩）は ABCMEmbedding.v で証明済み。
  残っているのは、それらを構成（メッセージ列 × タスク列）のレベルへ
  持ち上げる simulation 定理だけである。

  残っている障害（一点だけ）
  --------------------------
  証明の途中で使う `inversion HT2 ...; subst` の bare な subst が、
  represents の第一成分 `hot H = Om0` を使って **Om0 を消してしまう**。
  すると
    - 目標が `hot H = hot H` になって `assumption` が外れる
    - `rewrite Hhot` が使えなくなる
  という副作用が出る。
  一方これを避けようと `rewrite <- Hhot in otab_fin` で otab_fin を
  hot H 側に寄せると、今度は
    「tr_estep depends on the variable Om0 which is not declared」
  というセクション変数の依存エラーになる。

  次回の直し方（どれか一つでよい）
  --------------------------------
  (a) bare な `subst` をやめ、`inversion HT2 as [...]` のあと
      必要な等式だけ手で潰す（Om0 に触らせない）。
  (b) represents の第一成分を等式 `hot H = Om0` ではなく
      `ext Om0 (hot H) /\ ext (hot H) Om0` にする。等式でなくなるので
      subst の対象にならない。--- おそらくこれが一番楽。
  (c) Section を閉じてから（Om0 が全称量化された後で）simulation を
      証明する。セクション変数の依存問題が消える。

  証明の骨格自体は下に書いてあるとおりで、四つの場合はすべて埋まっている。
    CLocal   : tr_step で 1 歩          (CTask)
    CSend    : tr_estep で 2 歩         (CTask; CTask)
    CDeliver : tr_subst で本体の代入を合わせて 1 歩 (CDeliver)
    CDone    : tr EU = EUnit なので 1 歩 (CFinish)
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import AIPLSoundness.
Require Import ABCMEmbedding.
Require ABCM.

Section SimulationWIP.
Variable otab : nat -> option nat.
Variable itab : nat -> nat -> option ABCM.ty.
Variable body : nat -> nat -> ABCM.tm.
Variable Om0 : list nat.
Hypothesis otab_fin : forall o, otab o = nth_error Om0 o.

(* ================================================================= *)
(* 7. 構成レベルのシミュレーション                                   *)
(* ================================================================= *)

(*
  ABCM の構成と AIPL^- の構成の対応。AIPL^- 側はメッセージが future 番号を、
  タスクが所有 actor と future 番号を余分に持つので、それらを無視した
  対応関係になる。
*)

Definition rel_msg (M : ABCM.msg) (N : msg) : Prop :=
  let '(o, m, v) := M in
  let '(o', m', v', k) := N in
  o = o' /\ m = m' /\ v' = tr v.

Definition rel_task (a : ABCM.tm) (t : task) : Prop :=
  let '(o, k, e) := t in e = tr a.

Definition represents (AC : ABCM.conf) (C : conf) : Prop :=
  let '(ams, ats) := AC in
  let '(H, ms, ts) := C in
  hot H = Om0 /\ Forall2 rel_msg ams ms /\ Forall2 rel_task ats ts.

Lemma csteps_one : forall C C',
  cstep e_sinit e_mtab e_mbody C C' -> csteps e_sinit e_mtab e_mbody C C'.
Proof. intros. econstructor; [ eassumption | constructor ]. Qed.

Lemma csteps_two : forall C C' C'',
  cstep e_sinit e_mtab e_mbody C C' ->
  cstep e_sinit e_mtab e_mbody C' C'' ->
  csteps e_sinit e_mtab e_mbody C C''.
Proof. intros. econstructor; [ eassumption | apply csteps_one; assumption ]. Qed.

(*
  シミュレーション定理。ABCM が一歩進むとき、それに対応する AIPL^- の
  構成は 1 歩または 2 歩進んで、再び対応がつく。
*)
Theorem simulation : forall AC AC',
  ABCM.conf_ok otab itab AC ->
  ABCM.cstep otab body AC AC' ->
  forall C, represents AC C ->
  exists C', csteps e_sinit e_mtab e_mbody C C' /\ represents AC' C'.
Proof.
  intros AC AC' Hok Hs [[H ms] ts] Hrep.
  inversion Hs; subst; simpl in *; destruct Hrep as [Hhot [Hm Ht]];
    rewrite <- Hhot in otab_fin.
  - (* CLocal : 局所簡約。1 歩 *)
    apply Forall2_app_inv_l in Ht.
    destruct Ht as [U1 [U2' [HT1 [HT2 ->]]]].
    inversion HT2 as [| a0 t0 l0 l0' Hrt HT2' Heq1 Heq2]; subst.
    destruct t0 as [[oo kk] ee]. simpl in Hrt. subst ee.
    exists (H, ms ++ [], U1 ++ (oo, kk, tr e') :: l0').
    split.
    + apply csteps_one. apply CTask. apply tr_step. assumption.
    + simpl. split; [ congruence | ].
      rewrite app_nil_r. split; [ assumption | ].
      apply Forall2_app; [ assumption | ].
      apply Forall2_cons; [ reflexivity | assumption ].
  - (* CSend : 送出。2 歩 *)
    apply Forall2_app_inv_l in Ht.
    destruct Ht as [U1 [U2' [HT1 [HT2 ->]]]].
    inversion HT2 as [| a0 t0 l0 l0' Hrt HT2' Heq1 Heq2]; subst.
    destruct t0 as [[oo kk] ee]. simpl in Hrt. subst ee.
    (* タスクの型付けを ABCM 側の conf_ok から取る *)
    assert (Hte : ABCM.ht otab itab None e ABCM.TUnit).
    { destruct Hok as [_ Hts]. apply Hts. apply in_or_app. right. left. reflexivity. }
    destruct (tr_estep _ _ _ H0 _ Hte H oo)
      as [E [S1 S2]]; [ unfold ext; intros; congruence | ].
    exists (addfut H TUnit,
            (ms ++ [tr_msg M (length (hft H))]) ++ [],
            U1 ++ (oo, kk, tr e') :: l0').
    split.
    + eapply csteps_two.
      * apply CTask. exact S1.
      * apply CTask. exact S2.
    + simpl. split; [ congruence | ].
      rewrite app_nil_r. split.
      * apply Forall2_app; [ assumption | ].
        apply Forall2_cons; [ | constructor ].
        destruct M as [[oM mM] vM]. simpl. repeat split.
      * apply Forall2_app; [ assumption | ].
        apply Forall2_cons; [ reflexivity | assumption ].
  - (* CDeliver : 配送。1 歩 *)
    apply Forall2_app_inv_l in Hm.
    destruct Hm as [N1 [N2' [HM1 [HM2 ->]]]].
    inversion HM2 as [| a0 n0 l0 l0' Hrm HM2' Heq1 Heq2]; subst.
    destruct n0 as [[[o2 m2] v2] k2]. simpl in Hrm.
    destruct Hrm as [-> [-> ->]].
    (* ABCM 側の msg_ok から itab を引く *)
    assert (Hmo : ABCM.msg_ok otab itab (o2, m2, v)).
    { destruct Hok as [Hms _]. apply Hms. apply in_or_app. right. left. reflexivity. }
    simpl in Hmo. destruct Hmo as [i2 [ta2 [Ho2 [Hi2 _]]]].
    assert (i2 = i) by congruence. subst i2.
    exists (H, N1 ++ l0',
            ts ++ [(o2, k2, subst 0 (tr v) (e_mbody i m2))]).
    split.
    + apply csteps_one.
      eapply CDeliver.
      * rewrite <- otab_fin. assumption.
      * unfold e_mtab. rewrite Hi2. reflexivity.
    + simpl. split; [ congruence | ]. split.
      * apply Forall2_app; assumption.
      * apply Forall2_app; [ assumption | ].
        apply Forall2_cons; [ | constructor ].
        simpl. unfold e_mbody. apply tr_subst.
  - (* CDone : 値になったタスクを片付ける。1 歩 *)
    apply Forall2_app_inv_l in Ht.
    destruct Ht as [U1 [U2' [HT1 [HT2 ->]]]].
    inversion HT2 as [| a0 t0 l0 l0' Hrt HT2' Heq1 Heq2]; subst.
    destruct t0 as [[oo kk] ee]. simpl in Hrt. subst ee.
    exists (Heap (hot H) (hst H) (hft H) (upd (hfv H) kk (Some EUnit)),
            ms, U1 ++ l0').
    split.
    + apply csteps_one. apply CFinish. constructor.
    + simpl. split; [ congruence | ]. split; [ assumption | ].
      apply Forall2_app; assumption.
Qed.


End SimulationWIP.
