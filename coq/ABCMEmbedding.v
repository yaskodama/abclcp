(*
  ABCM ⊂ AIPL^-  ---- 埋め込み定理

  米澤・Briot・柴山の並行オブジェクト計算モデル ABCM（past 型送信の核）が、
  AIPL^- の部分体系であることを示す。すなわち翻訳 [[ · ]] を与えて

    静的  ABCM で型が付く式は、翻訳すると AIPL^- で型が付く
          （型検査を通った ABCM プログラムは、型検査を通る AIPL^- プログラム）

    動的  ABCM の局所簡約は AIPL^- の 1 歩に、
          ABCM のメッセージ送出は AIPL^- の 2 歩に、忠実に写る

  を証明する。これにより三つのレポート
    (1) ML (Hindley--Milner) の型健全性
    (2) ABCM の型健全性
    (3) AIPL^- の型健全性・型安全性
  のうち (2) と (3) が定理で接続される。

  翻訳の要点
  ----------
    ABCM の型      int, unit, obj[i]        -> int, unit, actor[i]
                   （インタフェース番号 = クラス番号）

    ABCM の式      n, (), o, x              -> n, (), o, x0
                   a + b                    -> a + b
                   a ; b                    -> let x1 = a in b
                   a <= m(b)                -> let x1 = (a <= m(b)) in ()
                   （past 送信は「future を作って捨てる」糖衣）

    ABCM のオブジェクトは状態を持たないので stype c = unit, sinit c = ()。
    ABCM のメソッドは返り値を持たないので mtab c m = (引数型, unit)。

  制限
  ----
    ABCM のオブジェクト表 otab は関数だが AIPL^- のそれはリストなので、
    otab が有限（あるリスト Om0 の nth_error）であることを仮定する。
    ABCM にはオブジェクトの動的生成が無いので、これは制限にならない。
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import AIPLSoundness.
Require ABCM.

(* ================================================================= *)
(* 1. 翻訳                                                           *)
(* ================================================================= *)

Definition tr_ty (t : ABCM.ty) : ty :=
  match t with
  | ABCM.TInt   => TInt
  | ABCM.TUnit  => TUnit
  | ABCM.TObj i => TActor i
  end.

(* 捨て変数。ABCM の式は変数を一つ（x0 に写る）しか持たないので、
   x1 は翻訳結果のどこにも自由に現れない。 *)
Definition xd : nat := 1.

Fixpoint tr (e : ABCM.tm) : tm :=
  match e with
  | ABCM.ENum n     => ENum n
  | ABCM.EU         => EUnit
  | ABCM.ERef o     => EORef o
  | ABCM.EVar       => EVar 0
  | ABCM.EAdd a b   => EAdd (tr a) (tr b)
  | ABCM.ESeq a b   => ELet xd (tr a) (tr b)
  | ABCM.ESend a m b => ELet xd (EFSend (tr a) m (tr b)) EUnit
  end.

(* メッセージの翻訳。AIPL^- のメッセージは future 番号を運ぶ *)
Definition tr_msg (M : ABCM.msg) (k : nat) : msg :=
  let '(o, m, v) := M in (o, m, tr v, k).

Lemma tr_value : forall v, ABCM.value v -> value (tr v).
Proof. intros v Hv; inversion Hv; simpl; constructor. Qed.

(* 翻訳結果は捨て変数 x1 を自由に含まない *)
Lemma subst_xd_tr : forall e v, subst xd v (tr e) = tr e.
Proof.
  induction e; intros v; simpl; try reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

(* ABCM の代入は翻訳と可換 *)
Lemma tr_subst : forall e w, subst 0 (tr w) (tr e) = tr (ABCM.subst w e).
Proof.
  induction e; intros w; simpl; try reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
Qed.

(* ================================================================= *)
(* 2. プログラム（表）の翻訳                                         *)
(* ================================================================= *)

Section Embedding.

Variable otab : nat -> option nat.
Variable itab : nat -> nat -> option ABCM.ty.
Variable body : nat -> nat -> ABCM.tm.

(* ABCM のオブジェクト表が有限であること *)
Variable Om0 : list nat.
Hypothesis otab_fin : forall o, otab o = nth_error Om0 o.

Definition e_stype (c : nat) : ty := TUnit.
Definition e_sinit (c : nat) : tm := EUnit.

Definition e_mtab (c m : nat) : option (ty * ty) :=
  match itab c m with
  | Some ta => Some (tr_ty ta, TUnit)
  | None    => None
  end.

Definition e_mbody (c m : nat) : tm := tr (body c m).

Definition tr_env (G : option ABCM.ty) : env :=
  match G with
  | None   => empty
  | Some t => extend empty 0 (tr_ty t)
  end.

(* ================================================================= *)
(* 3. 静的な埋め込み ---- 型付けの保存                               *)
(* ================================================================= *)

(*
  翻訳結果は変数 0 しか読まないので、型環境は 0 の像さえ合っていればよい。
  この形にしておくと ESeq / ESend が導入する x1 の束縛を弱化補題なしで扱える。
*)
Theorem tr_ht : forall e G T,
  ABCM.ht otab itab G e T ->
  forall ot ft C (Gam : env),
    ext Om0 ot ->
    Gam 0 = tr_env G 0 ->
    ht e_stype e_mtab ot ft C Gam (tr e) (tr_ty T).
Proof.
  intros e G T H.
  induction H; intros ot ft C Gam Hext HG0; simpl.
  - (* HNum *) constructor.
  - (* HU *) constructor.
  - (* HRef *) constructor. apply Hext. rewrite <- otab_fin. assumption.
  - (* HVar *) constructor. rewrite HG0. simpl. unfold extend. reflexivity.
  - (* HAdd *) constructor; [ apply IHht1 | apply IHht2 ]; assumption.
  - (* HSeq : a ; b  ->  let x1 = a in b *)
    econstructor.
    + apply IHht1; assumption.
    + apply IHht2; [ assumption | ].
      unfold extend. simpl. assumption.
  - (* HSend : a <= m(b)  ->  let x1 = (a <= m(b)) in () *)
    econstructor.
    + econstructor.
      * apply IHht1; assumption.
      * unfold e_mtab. rewrite H0. reflexivity.
      * apply IHht2; assumption.
    + constructor.
Qed.

Lemma e_sinit_value : forall c, value (e_sinit c).
Proof. intros. constructor. Qed.

Lemma e_sinit_ok : forall c ot ft C G,
  ht e_stype e_mtab ot ft C G (e_sinit c) (e_stype c).
Proof. intros. constructor. Qed.

(* ABCM のプログラムが型検査を通っているなら、翻訳したものも通っている *)
Theorem e_bodies_ok :
  (forall i m targ, itab i m = Some targ ->
     ABCM.ht otab itab (Some targ) (body i m) ABCM.TUnit) ->
  forall c m ta tr', e_mtab c m = Some (ta, tr') ->
    forall ot ft, ext Om0 ot ->
      ht e_stype e_mtab ot ft c (extend empty 0 ta) (e_mbody c m) tr'.
Proof.
  intros Hb c m ta tr' Hm ot ft Hext.
  unfold e_mtab in Hm. destruct (itab c m) as [ta0 |] eqn:Eit; [ | discriminate ].
  inversion Hm; subst ta tr'. clear Hm.
  unfold e_mbody.
  change TUnit with (tr_ty ABCM.TUnit).
  eapply tr_ht; [ apply Hb; exact Eit | assumption | ].
  simpl. unfold extend. reflexivity.
Qed.

(* ================================================================= *)
(* 4. 動的な埋め込み ---- 局所簡約は 1 歩に写る                      *)
(* ================================================================= *)

Theorem tr_step : forall e e', ABCM.step e e' ->
  forall H o, tstep e_sinit e_mtab H o (tr e) H [] (tr e').
Proof.
  intros e e' Hs. induction Hs; intros Hp slf; simpl.
  - (* SAdd *) constructor.
  - (* SAdd1 *) constructor. apply IHHs.
  - (* SAdd2 *) constructor; [ apply tr_value; assumption | apply IHHs ].
  - (* SSeq : ();e -> e *)
    rewrite <- (subst_xd_tr e EUnit) at 2.
    apply STLet. constructor.
  - (* SSeq1 *) constructor. apply IHHs.
  - (* SSend1 *) constructor. constructor. apply IHHs.
  - (* SSend2 *)
    constructor. constructor; [ apply tr_value; assumption | apply IHHs ].
Qed.

(* ================================================================= *)
(* 5. 動的な埋め込み ---- 送出は 2 歩に写る                          *)
(* ================================================================= *)

(* future を一つ足したヒープ *)
Definition addfut (H : heap) (T : ty) : heap :=
  Heap (hot H) (hst H) (hft H ++ [T]) (hfv H ++ [None]).

(*
  ABCM の送出 e --M--> e' は、AIPL^- では
      [[e]] --(M に future 番号を付けたもの)--> E --()--> [[e']]
  という 2 歩になる。1 歩目が future を確保してメッセージを出し、
  2 歩目が捨て変数の let を潰す。
*)
Theorem tr_estep : forall e M e', ABCM.estep e M e' ->
  forall T, ABCM.ht otab itab None e T ->
  forall Hp slf, ext Om0 (hot Hp) ->
  exists E,
       tstep e_sinit e_mtab Hp slf (tr e)
             (addfut Hp TUnit) [tr_msg M (length (hft Hp))] E
    /\ tstep e_sinit e_mtab (addfut Hp TUnit) slf E (addfut Hp TUnit) [] (tr e').
Proof.
  intros e M e' Hes. induction Hes; intros T Ht Hp slf Hext.
  - (* EFire :  o' <= m(v)  で v が値 *)
    inversion Ht; subst.
    match goal with
    | Hr : ABCM.ht _ _ _ (ABCM.ERef o) _ |- _ => inversion Hr; subst
    end.
    exists (ELet xd (EFRef (length (hft Hp))) EUnit).
    split.
    + simpl. constructor.
      eapply STSend.
      * apply tr_value; assumption.
      * apply Hext. rewrite <- otab_fin. eassumption.
      * unfold e_mtab. match goal with
        | Hi : itab _ m = Some _ |- _ => rewrite Hi
        end. reflexivity.
    + simpl. rewrite <- (subst_xd_tr ABCM.EU (EFRef (length (hft Hp)))) at 2.
      apply STLet. constructor.
  - (* EAddL *)
    inversion Ht; subst.
    destruct (IHHes _ ltac:(eassumption) Hp slf Hext) as [E [S1 S2]].
    exists (EAdd E (tr b)). split.
    + simpl. constructor. assumption.
    + constructor. assumption.
  - (* EAddR *)
    inversion Ht; subst.
    destruct (IHHes _ ltac:(eassumption) Hp slf Hext) as [E [S1 S2]].
    exists (EAdd (tr v) E). split.
    + simpl. constructor; [ apply tr_value; assumption | assumption ].
    + constructor; [ apply tr_value; assumption | assumption ].
  - (* ESeqL *)
    inversion Ht; subst.
    destruct (IHHes _ ltac:(eassumption) Hp slf Hext) as [E [S1 S2]].
    exists (ELet xd E (tr b)). split.
    + simpl. constructor. assumption.
    + constructor. assumption.
  - (* ESendL *)
    inversion Ht; subst.
    destruct (IHHes _ ltac:(eassumption) Hp slf Hext) as [E [S1 S2]].
    exists (ELet xd (EFSend E m (tr b)) EUnit). split.
    + simpl. constructor. constructor. assumption.
    + constructor. constructor. assumption.
  - (* ESendR *)
    inversion Ht; subst.
    destruct (IHHes _ ltac:(eassumption) Hp slf Hext) as [E [S1 S2]].
    exists (ELet xd (EFSend (tr v) m E) EUnit). split.
    + simpl. constructor. constructor;
        [ apply tr_value; assumption | assumption ].
    + constructor. constructor;
        [ apply tr_value; assumption | assumption ].
Qed.

(* ================================================================= *)
(* 6. 系 ---- 翻訳した ABCM プログラムは await を含まない            *)
(* ================================================================= *)

(*
  ABCM には await が無いので、翻訳結果も await を含まない。
  これが「ABCM の進行定理は二択なのに AIPL^- の進行定理は三択である」
  ことの構造的な理由である ---- ABCM は AIPL^- の await を含まない断片に
  ちょうど収まっており、第三の枝（await 待ち）が到達不能になる。
*)

Lemma tr_afree : forall e, afree (tr e).
Proof.
  induction e; simpl; try (constructor; fail);
    repeat (constructor; try assumption).
Qed.

Lemma e_mbody_afree : forall c m, afree (e_mbody c m).
Proof. intros c m. unfold e_mbody. apply tr_afree. Qed.

(*
  ABCM のプログラムを翻訳して AIPL^- の意味論で走らせると、
  型安全であり、かつデッドロックしない。
  ABCM 側で証明し直したのではなく、AIPL^- の定理を適用して得ている。
*)
Theorem abcm_translation_safe :
  (forall i m targ, itab i m = Some targ ->
     ABCM.ht otab itab (Some targ) (body i m) ABCM.TUnit) ->
  forall C C',
    conf_ok e_stype e_mtab Om0 C ->
    conf_afree C ->
    csteps e_sinit e_mtab e_mbody C C' ->
       conf_ok e_stype e_mtab Om0 C'
    /\ conf_afree C'
    /\ ~ blocked C'
    /\ (terminal C' \/ exists C'', cstep e_sinit e_mtab e_mbody C' C'').
Proof.
  intros Hb C C' Hok Haf Hs.
  eapply async_deadlock_free with (C := C).
  - apply e_sinit_value.
  - apply e_sinit_ok.
  - apply e_bodies_ok. exact Hb.
  - apply e_mbody_afree.
  - exact Hok.
  - exact Haf.
  - exact Hs.
Qed.

Corollary abcm_translation_never_stuck :
  (forall i m targ, itab i m = Some targ ->
     ABCM.ht otab itab (Some targ) (body i m) ABCM.TUnit) ->
  forall C C',
    conf_ok e_stype e_mtab Om0 C ->
    conf_afree C ->
    csteps e_sinit e_mtab e_mbody C C' ->
    ~ stuck e_sinit e_mtab e_mbody C'.
Proof.
  intros Hb C C' Hok Haf Hs [Hnt [Hnb Hns]].
  destruct (abcm_translation_safe Hb C C' Hok Haf Hs) as [_ [_ [Hb2 [Ht | Hst]]]].
  - contradiction.
  - contradiction.
Qed.

End Embedding.
