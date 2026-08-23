(*
  AIPL^-2 が空虚でないことの確認。

  定理はすべて「プログラムが型検査を通っている」という仮定のもとにある。
  義務レベルの条件（待ちは必ず上へ）が満たせないなら、定理は空虚である。
  そこで、await を実際に使うプログラムを一つ作り、仮定をすべて満たすこと、
  そして初期構成が conf_ok であることを示す。

    class Svc    { method get(x) : int  { reply(x); } }        // レベル 1
    class Caller { method run(x) : int  { reply(now svc.get(x)); } }  // レベル 0

  Caller.run は await を含む。0 < 1 なのでレベル条件を満たす。
*)
From Stdlib Require Import List Arith.
Import ListNotations.
Require Import AIPLSoundness2.

(* クラス 0 = Svc, クラス 1 = Caller。どちらも状態は int *)
Definition ex_stype (c : nat) : ty := TInt.
Definition ex_sinit (c : nat) : tm := ENum 0.

(* メソッドはどちらも 0 番。引数も返り値も int *)
Definition ex_mtab (c m : nat) : option (ty * ty) :=
  match c, m with
  | 0, 0 => Some (TInt, TInt)     (* Svc.get *)
  | 1, 0 => Some (TInt, TInt)     (* Caller.run *)
  | _, _ => None
  end.

(* 義務レベル: Svc.get は 1、Caller.run は 0。待ちは 0 -> 1 で上へ向かう *)
Definition ex_mlvl (c m : nat) : nat :=
  match c, m with
  | 0, 0 => 1
  | _, _ => 0
  end.

(* 宣言する効果。Svc.get は何もしない。
   Caller.run は Svc.get を await するので、その効果を引き継ぐ ---- が、
   引き継ぐ先が空なので、こちらも空でよい。 *)
Definition ex_meff (c m : nat) : eff := e0.

(* 起動時のオブジェクト表: 0 番に Svc が一つ居る *)
Definition ex_ot0 : list nat := [0].

Definition ex_mbody (c m : nat) : tm :=
  match c, m with
  | 0, 0 => EVar 0                                    (* reply(x) *)
  (* while で数えながら、途中で now svc.get(x) を待つ。
     第 2 版で広げた構文（逐次実行・繰り返し）と await が同居している *)
  | 1, 0 => ESeq (EWhile (ELt (EVar 0) (ENum 0)) EUnit)
                 (EAwait (EFSend (EORef 0) 0 (EVar 0)))
  | _, _ => EUnit
  end.

Lemma ex_sinit_value : forall c, value (ex_sinit c).
Proof. intros. constructor. Qed.

Lemma ex_sinit_ok : forall c ot ft C L G,
  ht ex_stype ex_mtab ex_mlvl ex_meff ot ft C L G (ex_sinit c) (ex_stype c) e0.
Proof. intros. constructor. Qed.

(* ★ 本体が、そのメソッドの義務レベルのもとで型検査を通る。
   Caller.run の await が 0 < 1 で通るのが要点である。 *)
Lemma ex_bodies_ok : forall c m ta tr, ex_mtab c m = Some (ta, tr) ->
  forall ot ft, ext ex_ot0 ot ->
    exists E, ht ex_stype ex_mtab ex_mlvl ex_meff ot ft c (ex_mlvl c m)
                 (extend empty 0 ta) (ex_mbody c m) tr E
           /\ incl E (ex_meff c m).
Proof.
  intros c m ta tr Hm ot ft Hext.
  destruct c as [| [| c']]; destruct m as [| m']; simpl in Hm;
    try discriminate; inversion Hm; subst; simpl.
  - (* Svc.get: 引数をそのまま返す *)
    exists e0. split; [ | apply incl_refl ].
    constructor. unfold extend. simpl. reflexivity.
  - (* Caller.run: while ... ; now svc.get(x) *)
    eexists. split.
    + eapply HSeq.
      * eapply HWhile with (T1 := TUnit).
        -- econstructor; [ constructor; unfold extend; simpl; reflexivity
                         | constructor ].
        -- constructor.
      * eapply HAwait with (n := 1).
        -- eapply HSend with (c := 0) (ta := TInt) (tr := TInt).
           ++ constructor. apply Hext. simpl. reflexivity.
           ++ simpl. reflexivity.
           ++ constructor. unfold extend. simpl. reflexivity.
        -- auto.
    + simpl. apply incl_refl.
Qed.

(* 初期構成: Caller.run へのメッセージが一通、飛んでいる途中 *)
Definition ex_heap : heap :=
  Heap [0; 1] [ENum 0; ENum 0] [(TInt, 0, e0)] [None].
Definition ex_conf : conf :=
  (ex_heap, [(1, 0, ENum 5, 0)], @nil task).

Lemma ex_conf_ok :
  conf_ok ex_stype ex_mtab ex_mlvl ex_meff ex_ot0 ex_conf.
Proof.
  unfold ex_conf, ex_heap, conf_ok. simpl.
  split; [ | split; [ | split; [ | split ] ] ].
  - (* heap_ok *)
    unfold heap_ok; simpl.
    split; [ reflexivity | ]. split; [ reflexivity | ]. split.
    + intros o c v Hoc Hsv.
      destruct o as [| [| o']]; simpl in *;
        [ | | destruct o'; simpl in Hoc; discriminate ];
        inversion Hoc; inversion Hsv; subst;
        (split; [ apply VNum | intros; unfold ex_stype; apply HNum ]).
    + intros k T n v Hk Hv.
      destruct k as [| k']; simpl in Hv; [ discriminate | ].
      destruct k'; simpl in Hv; discriminate.
  - (* ext ot0 (hot H): [0] は [0;1] の先頭 *)
    intros n x Hn. destruct n as [| [| n']]; simpl in *; auto; discriminate.
  - (* msg_ok: 宛先 1 は Caller、メソッド 0 は run、future 0 のレベルは 0 *)
    intros M [<- | []]. simpl.
    exists 1, TInt, TInt.
    split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ constructor | ].
    split; [ intros; constructor | reflexivity ].
  - (* task_ok: タスクは無い *)
    intros t [].
  - (* prod_ok: 未解決の future 0 には、飛んでいるメッセージが対応する *)
    intros k T n Hk Hu.
    destruct k as [| k']; simpl in Hu; [ | destruct k'; simpl in Hu; discriminate ].
    left. exists 1, 0, (ENum 5). left. reflexivity.
Qed.

(* この構成はデッドロックしていない。await を含む言語のままで言えている。 *)
Corollary ex_not_blocked : ~ blocked ex_conf.
Proof. eapply deadlock_free with (stype := ex_stype). apply ex_conf_ok. Qed.

(* 一歩進める（終状態ではない） *)
Corollary ex_can_step :
  terminal ex_conf \/ exists C', cstep ex_sinit ex_mtab ex_mbody ex_mlvl ex_meff ex_conf C'.
Proof.
  apply progress_total with (stype := ex_stype) (ot0 := ex_ot0).
  apply ex_conf_ok.
Qed.
