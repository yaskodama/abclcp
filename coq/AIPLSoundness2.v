(*
  AIPL^-2 : 型健全性・型安全性・デッドロック自由の三つが
            同時に証明できる、最大の構文

  第 1 版（AIPLSoundness.v）に対する違いは一点に尽きる。

    第 1 版は、デッドロック自由を await を言語から取り除いた断片
    （conf_afree）についてしか言えなかった。待てる構文を捨てて
    「待ちが返らない」を消していたのだから、当然である。

    第 2 版は await を含んだまま言う。道具は義務レベルである。

  ---- 何を足したか ------------------------------------------------

  1. future の型に、それを埋める側のレベルと効果を持たせた。

       TFut : ty -> nat -> eff -> ty     future t @ n ! E

  2. 型判断に「いま検査しているメソッドの義務レベル」を足した。

       ht ot ft C L G e T

  3. 待ちは必ず上へ向かうことを型で要求した。これが要である。

       HAwait : ht ... C L G e (TFut T n) -> L < n ->
                ht ... C L G (EAwait e) T

  4. 実行時の不変条件を一つ足した（prod_ok）。

       未解決の future には、必ずそれを埋める者がいる。
       メールボックスの中のメッセージか、走っているタスクである。

  5. 構文を広げた。逐次実行 (ESeq) と繰り返し (EWhile) を入れた。
     while は if へ展開する形にしたので、束縛を作らない
     （変数捕獲の心配が無い）。

  6. 効果を判断に足した。

       ht ot ft C L G e T E

     規則の要は二つである。
       ・send は呼び先の効果を引き継がない（待たないので）
       ・await は引き継ぐ（Ee ++ Ec）
     これは実装の挙動と同じである。bodies_ok には
     「本体の効果は宣言した効果に収まる」を課す。

  ---- 証明の骨 ----------------------------------------------------

  デッドロック自由は「レベルが最大のタスクを取る」ことで示す。
  全タスクが待ちだと仮定する。レベル最大のタスクも待っている。
  待っている先の future はそれより真に上のレベルである（規則 HAwait）。
  その future には埋める者がいる（prod_ok）。メールボックスは空だから
  埋める者はタスクであり、そのタスクのレベルは上である。
  レベル最大に反する。

  ---- 主定理 ------------------------------------------------------

    no_method_not_understood  型の付いた構成を飛ぶメッセージは、
                              宛先が実在し、そのクラスがそのメソッドを持ち、
                              引数と future の型もレベルも合っている
    preservation              一歩進んでも conf_ok が保たれる（★健全性）
    preservation_star         何歩進んでも保たれる
    type_safety               到達できる構成は stuck でない（★安全性）
    deadlock_free             型の付いた構成は blocked にならない（★デッドロック自由）
    progress_total            終状態か、一歩進めるか、の二択
                              （第 1 版の「全部待ち」の枝が消えた）
    deadlock_free_star        到達できる構成すべてについて同じことを言う
    state_type_invariant      どの時点でも各 actor の状態は宣言型を持つ
    future_type_invariant     解決済み future の値は宣言された返り値型を持つ
    effect_no_increase        一歩進んでも効果は増えない（★効果の健全性）
    effect_soundness          走っているタスクの効果は、担当する future に
                              記録された効果に収まり続ける
    await_charges_callee      待つと呼び先の効果を必ず引き継ぐ
                              （＝一段隔てても隠せない）
    send_does_not_charge      送るだけでは引き継がない（待たないので）

  いずれも Print Assumptions が Closed under the global context である。

  ---- なぜこれが「最大」か ----------------------------------------

  次のものを入れると、三つのうちどれかが成り立たなくなる。
  外した理由を書いておく。

    select        受け取るメッセージが来ない場合に止まる。
                  レベルは「待ちの相手」を型から特定できるときにしか
                  効かないが、select の相手は誰が送るか型に現れない。
                  進行の枝が一つ増え、デッドロック自由が壊れる。
                  （実装では期限の義務づけと送り手の存在検査で補っている）

    timeout       時間を意味論に入れる必要がある。進行は保てるが、
                  「詰まらない」ではなく「詰まっても諦める」になり、
                  デッドロック自由の主張が別物になる。

    any / 多重定義 / 多相
                  標準形補題が壊れる。値の形が型から決まらなくなるので、
                  進行の証明が通らない。

    become        受け手のクラスが実行時に変わると、
                  メッセージの型が配送時に合っている保証が崩れる
                  （no_method_not_understood が壊れる）。
                  なお実装では become 自体を言語から外した。

    他アクターの状態への直接代入
                  heap_ok の「各 actor の状態は宣言型を持つ」が
                  自分のメソッド内でしか保てなくなる。

  逆に、次のものは入れても三つとも保たれる（実際に入れてある）。

    while / 逐次実行      進行は保たれる。止まらない繰り返しは
                          「デッドロック」ではなく「停止しない」であって、
                          進行定理は一歩進めることしか言っていない。
    動的な actor 生成     new C は heap を伸ばすだけである。
    future の入れ子       await の中に await があってもよい。
                          レベルは式の位置ではなくメソッドに付くので、
                          入れ子でも同じ条件で足りる。

  ---- 空虚でないこと ----------------------------------------------

  定理はすべて「プログラムが型検査を通っている」という仮定のもとにある。
  AIPLSoundness2Example.v に、await を実際に使うプログラムを一つ置き、
  仮定をすべて満たすこと、初期構成が conf_ok であること、
  したがって deadlock_free が適用できることを示した。
  レベルを同じにすると本体の型検査が通らないことも確かめてある
  （条件が効いていることの対照）。

  ---- 形式化から外した範囲 ----------------------------------------
    any, send!, remote actor, sender, become, select, 配列, レコード,
    overload, 多相（型スキーム）, timeout, protocol/session
*)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

(* ================================================================= *)
(* 0. 効果                                                           *)
(* ================================================================= *)

(* 効果名の集合。実装の ai / net / io / mut / time / mem / fs / log に
   対応するが、形式化では名前を自然数で表すだけでよい。
   包含は incl（標準ライブラリ）、合併は ++ である。 *)
Definition eff := list nat.
Definition e0 : eff := [].
Definition emut : nat := 0.        (* 自分の状態を書く *)

(* ================================================================= *)
(* 1. 型と式                                                         *)
(* ================================================================= *)

Inductive ty : Type :=
| TInt   : ty
| TBool  : ty
| TUnit  : ty
| TActor : nat -> ty        (* actor[c] : クラス c の actor *)
| TFut   : ty -> nat -> eff -> ty.
  (* future t @ n ! E : レベル n のメソッドが埋め、その本体の効果は E に収まる *)

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
| EAwait : tm -> tm
| ESeq   : tm -> tm -> tm             (* e1 ; e2 *)
| EWhile : tm -> tm -> tm.            (* while c do b *)

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
  | ESeq a b      => ESeq (subst x v a) (subst x v b)
  | EWhile a b    => EWhile (subst x v a) (subst x v b)
  | _             => t
  end.

(* ================================================================= *)
(* 2. 実行時の構造                                                   *)
(* ================================================================= *)

Record heap := Heap {
  hot : list nat;            (* actor 番号 -> クラス番号 *)
  hst : list tm;             (* actor 番号 -> 現在の状態値 *)
  hft : list (ty * nat * eff);  (* future 番号 -> (型, レベル, 効果) *)
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
Variable mlvl  : nat -> nat -> nat.               (* c.m の義務レベル *)
Variable meff  : nat -> nat -> eff.               (* c.m が宣言する効果 *)
(* 起動時のオブジェクト表。メソッド本体はここに載っている actor を
   直接参照してよい（例: 哲学者がフォークを名前で知っている）。 *)
Variable ot0  : list nat.

(* ================================================================= *)
(* 4. 型付け                                                         *)
(* ================================================================= *)

(* ht ot ft C L G e T :
     オブジェクト表 ot、future 表 ft のもとで、クラス C の本体の中で、
     型環境 G において式 e が型 T を持つ。 *)

Inductive ht (ot : list nat) (ft : list (ty * nat * eff)) (C : nat) (L : nat)
  : env -> tm -> ty -> eff -> Prop :=
| HNum  : forall G n, ht ot ft C L G (ENum n) TInt e0
| HBool : forall G b, ht ot ft C L G (EBool b) TBool e0
| HUnit : forall G,   ht ot ft C L G EUnit TUnit e0
| HVar  : forall G x T, G x = Some T -> ht ot ft C L G (EVar x) T e0
| HSelf : forall G, ht ot ft C L G ESelf (TActor C) e0
| HORef : forall G o c, nth_error ot o = Some c -> ht ot ft C L G (EORef o) (TActor c) e0
| HFRef : forall G k T n E, nth_error ft k = Some (T, n, E) ->
            ht ot ft C L G (EFRef k) (TFut T n E) e0
| HAdd  : forall G a b Ea Eb, ht ot ft C L G a TInt Ea -> ht ot ft C L G b TInt Eb ->
                        ht ot ft C L G (EAdd a b) TInt (Ea ++ Eb)
| HLt   : forall G a b Ea Eb, ht ot ft C L G a TInt Ea -> ht ot ft C L G b TInt Eb ->
                        ht ot ft C L G (ELt a b) TBool (Ea ++ Eb)
| HIf   : forall G a b c T Ea Eb Ec, ht ot ft C L G a TBool Ea ->
                            ht ot ft C L G b T Eb -> ht ot ft C L G c T Ec ->
                            ht ot ft C L G (EIf a b c) T (Ea ++ Eb ++ Ec)
| HLet  : forall G x e1 e2 T1 T2 E1 E2,
            ht ot ft C L G e1 T1 E1 ->
            ht ot ft C L (extend G x T1) e2 T2 E2 ->
            ht ot ft C L G (ELet x e1 e2) T2 (E1 ++ E2)
| HGet  : forall G, ht ot ft C L G EGet (stype C) e0
(* 自分の状態を書くのは mut *)
| HSet  : forall G e E, ht ot ft C L G e (stype C) E ->
            ht ot ft C L G (ESet e) TUnit (emut :: E)
| HNew  : forall G c, ht ot ft C L G (ENew c) (TActor c) e0
(* 送るだけでは呼び先の効果を引き継がない（待たないので）。
   引き継ぐのは await の側である。実装もこの区別をしている。 *)
| HSend : forall G ea m e1 c ta tr Ea E1,
            ht ot ft C L G ea (TActor c) Ea ->
            mtab c m = Some (ta, tr) ->
            ht ot ft C L G e1 ta E1 ->
            ht ot ft C L G (EFSend ea m e1) (TFut tr (mlvl c m) (meff c m)) (Ea ++ E1)
(* ★ 待ちは必ず「上」へ向かう。これがデッドロックフリーの要である。 *)
(* ★ 待つと、呼び先の効果を引き継ぐ *)
| HAwait : forall G e T n Ee Ec,
             ht ot ft C L G e (TFut T n Ec) Ee -> L < n ->
             ht ot ft C L G (EAwait e) T (Ee ++ Ec)
| HSeq  : forall G a b T1 T2 Ea Eb,
            ht ot ft C L G a T1 Ea -> ht ot ft C L G b T2 Eb ->
            ht ot ft C L G (ESeq a b) T2 (Ea ++ Eb)
| HWhile : forall G a b T1 Ea Eb,
            ht ot ft C L G a TBool Ea -> ht ot ft C L G b T1 Eb ->
            ht ot ft C L G (EWhile a b) TUnit (Ea ++ Eb).

(* プログラム全体が型検査を通っていること。
   Section の Hypothesis なので、End で各定理の前提に変わる。公理ではない。 *)

Hypothesis sinit_value : forall c, value (sinit c).

Hypothesis sinit_ok : forall c ot ft C L G, ht ot ft C L G (sinit c) (stype c) e0.

(* 本体はそのメソッドの義務レベルのもとで型が付き、
   その効果は宣言した効果に収まる。
   実装は推論した効果を注釈と照合する。ここも同じ形である。 *)
Hypothesis bodies_ok :
  forall c m ta tr, mtab c m = Some (ta, tr) ->
    forall ot ft, ext ot0 ot ->
      exists E, ht ot ft c (mlvl c m) (extend empty 0 ta) (mbody c m) tr E
             /\ incl E (meff c m).

(* ================================================================= *)
(* 5. 型付けの基本補題                                               *)
(* ================================================================= *)

(* 型環境の外延性 *)
Lemma ht_env_ext : forall ot ft C L G1 G2 e T E,
  (forall z, G1 z = G2 z) -> ht ot ft C L G1 e T E -> ht ot ft C L G2 e T E.
Proof.
  intros ot ft C L G1 G2 e T E Heq H. generalize dependent G2.
  induction H; intros G2 Heq; try (econstructor; eauto; fail).
  - constructor. rewrite <- Heq. assumption.
  - econstructor; [ eauto | ].
    apply IHht2. intros z. unfold extend. destruct (Nat.eqb z x); auto.
Qed.

(* オブジェクト表・future 表の拡張に対する単調性 *)
Lemma ht_mono : forall ot ft C L G e T E ot' ft',
  ht ot ft C L G e T E -> ext ot ot' -> ext ft ft' -> ht ot' ft' C L G e T E.
Proof.
  intros ot ft C L G e T E ot' ft' H. generalize dependent ft'. generalize dependent ot'.
  induction H; intros ot' ft' Ho Hf; try (econstructor; eauto; fail).
Qed.

(* 値の効果は空である。値は何もしない。 *)
Lemma value_eff : forall ot ft C L G v T E,
  value v -> ht ot ft C L G v T E -> E = e0.
Proof.
  intros ot ft C L G v T E Hv Ht.
  inversion Hv; subst; inversion Ht; subst; reflexivity.
Qed.

(* 値の型付けはクラス文脈にも型環境にも依存しない *)
Lemma value_ht_indep : forall ot ft C L G v T E,
  value v -> ht ot ft C L G v T E -> forall C' L' G', ht ot ft C' L' G' v T e0.
Proof.
  intros ot ft C L G v T E Hv Ht. inversion Hv; subst; inversion Ht; subst;
    intros; econstructor; eauto.
Qed.

(* 代入補題。値の効果は空なので、代入しても効果は増えない。 *)
Lemma substitution : forall ot ft C L e T E G x T1 v,
  ht ot ft C L (extend G x T1) e T E ->
  value v ->
  (forall C' L' G', ht ot ft C' L' G' v T1 e0) ->
  ht ot ft C L G (subst x v e) T E.
Proof.
  intros ot ft C L e. induction e; intros T E G x T1 v Ht Hv Hvt;
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

(* 標準形 *)
Lemma canon_int : forall ot ft C L G v E,
  value v -> ht ot ft C L G v TInt E -> exists n, v = ENum n.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_bool : forall ot ft C L G v E,
  value v -> ht ot ft C L G v TBool E -> exists b, v = EBool b.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_actor : forall ot ft C L G v c E,
  value v -> ht ot ft C L G v (TActor c) E ->
  exists o, v = EORef o /\ nth_error ot o = Some c.
Proof. intros. inversion H; subst; inversion H0; subst; eauto. Qed.

Lemma canon_fut : forall ot ft C L G v T n Ec E,
  value v -> ht ot ft C L G v (TFut T n Ec) E ->
  exists k, v = EFRef k /\ nth_error ft k = Some (T, n, Ec).
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
      (Heap (hot H) (hst H) (hft H ++ [(tr, mlvl cc m, meff cc m)]) (hfv H ++ [None]))
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
    tstep H o a H' out a' -> tstep H o (EAwait a) H' out (EAwait a')
| STSeq : forall H o v b,
    value v -> tstep H o (ESeq v b) H [] b
| STSeq1 : forall H o a b H' out a',
    tstep H o a H' out a' -> tstep H o (ESeq a b) H' out (ESeq a' b)
(* while は if へ展開する。束縛を作らないので変数捕獲の心配が無い *)
| STWhile : forall H o a b,
    tstep H o (EWhile a b) H [] (EIf a (ESeq b (EWhile a b)) EUnit).

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
| AwAwait : forall a, awaiting H a -> awaiting H (EAwait a)
| AwSeq1  : forall a b, awaiting H a -> awaiting H (ESeq a b).

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
     value v /\ forall C L G, ht (hot H) (hft H) C L G v (stype c) e0) /\
  (forall k T n E v, nth_error (hft H) k = Some (T, n, E) ->
     nth_error (hfv H) k = Some (Some v) ->
     value v /\ forall C L G, ht (hot H) (hft H) C L G v T e0).

(* メッセージが持つ future の型・レベル・効果は、宛先メソッドのものと一致する。
   「その future を埋めるのは c.m であり、その効果は meff c m に収まる」
   という約束がここに入る。 *)
Definition msg_ok (H : heap) (M : msg) : Prop :=
  let '(o, m, v, k) := M in
  exists c ta tr,
       nth_error (hot H) o = Some c
    /\ mtab c m = Some (ta, tr)
    /\ value v
    /\ (forall C L G, ht (hot H) (hft H) C L G v ta e0)
    /\ nth_error (hft H) k = Some (tr, mlvl c m, meff c m).

(* タスクは、自分が埋める future のレベルのもとで型が付き、
   その効果は、その future に記録された効果に収まる。
   ★ これが効果の健全性の担い手である。 *)
Definition task_ok (H : heap) (t : task) : Prop :=
  let '(o, k, e) := t in
  exists c T L EF E,
       nth_error (hot H) o = Some c
    /\ nth_error (hft H) k = Some (T, L, EF)
    /\ ht (hot H) (hft H) c L empty e T E
    /\ incl E EF.

(* ★ 未解決の future には必ず「埋める者」がいる。
   メールボックスの中のメッセージか、走っているタスクのどちらかである。
   これがデッドロックフリーの証明の骨である。 *)
Definition prod_ok (H : heap) (ms : list msg) (ts : list task) : Prop :=
  forall k T n E,
    nth_error (hft H) k = Some (T, n, E) ->
    nth_error (hfv H) k = Some None ->
    (exists o m v, In (o, m, v, k) ms) \/ (exists o e, In (o, k, e) ts).

Definition conf_ok (C : conf) : Prop :=
  let '(H, ms, ts) := C in
  heap_ok H /\
  ext ot0 (hot H) /\
  (forall M, In M ms -> msg_ok H M) /\
  (forall t, In t ts -> task_ok H t) /\
  prod_ok H ms ts.

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

Lemma local_progress : forall H o c L G e T E,
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  ht (hot H) (hft H) c L G e T E ->
  (forall x, G x = None) ->
  value e \/ (exists H' out e', tstep H o e H' out e') \/ awaiting H e.
Proof.
  intros H o c L G e T E Hh Ho Ht.
  destruct Hh as [Hl1 [Hl2 [Hstok Hfvok]]].
  induction Ht; intros Hcl; try (left; constructor; fail).
  - (* HVar *) rewrite Hcl in H0. discriminate.
  - (* HSelf *) right. left. eauto using tstep.
  - (* HAdd *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_int _ _ _ _ _ _ _ Hv1 Ht1) as [n ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_int _ _ _ _ _ _ _ Hv2 Ht2) as [k ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STAdd2; [ constructor | eassumption ].
    + right. apply AwAdd2; [ constructor | assumption ].
  - (* HLt *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    2:{ left. eauto using tstep. }
    2:{ right. constructor. assumption. }
    destruct (canon_int _ _ _ _ _ _ _ Hv1 Ht1) as [n ->].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + destruct (canon_int _ _ _ _ _ _ _ Hv2 Ht2) as [k ->].
      left. eauto using tstep.
    + left. eexists; eexists; eexists. apply STLt2; [ constructor | eassumption ].
    + right. apply AwLt2; [ constructor | assumption ].
  - (* HIf *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + destruct (canon_bool _ _ _ _ _ _ _ Hv1 Ht1) as [[|] ->].
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
    destruct (canon_actor _ _ _ _ _ _ _ _ Hv1 Ht1) as [o' [-> Hoc]].
    destruct (IHHt2 Hcl) as [Hv2 | [[H2 [o2 [b2 Hs2]]] | Ha2]].
    + left. eexists; eexists; eexists. eapply STSend; eassumption.
    + left. eexists; eexists; eexists. apply STSend2; [ constructor | eassumption ].
    + right. apply AwSend2; [ constructor | assumption ].
  - (* HAwait *)
    destruct (IHHt Hcl) as [Hv | [[H1 [o1 [a1 Hs1]]] | Ha]].
    2:{ right. left. eauto using tstep. }
    2:{ right. right. constructor. assumption. }
    destruct (canon_fut _ _ _ _ _ _ _ _ _ _ Hv Ht) as [k [-> Hk]].
    assert (Hlt : k < length (hfv H)).
    { rewrite Hl2. eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hlt) as [ov Hov].
    destruct ov as [v |].
    + right. left. exists H, (@nil msg), v. constructor. assumption.
    + right. right. constructor. assumption.
  - (* HSeq *)
    right.
    destruct (IHHt1 Hcl) as [Hv1 | [[H1 [o1 [a1 Hs1]]] | Ha1]].
    + left. eauto using tstep.
    + left. eauto using tstep.
    + right. constructor. assumption.
  - (* HWhile *)
    right. left. eauto using tstep.
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
  value v /\ forall C L G, ht (hot H) (hft H) C L G v (stype c) e0.
Proof. intros H o c v [_ [_ [A _]]]; apply A. Qed.
Lemma heap_fv_ok : forall H k T n E v, heap_ok H ->
  nth_error (hft H) k = Some (T, n, E) -> nth_error (hfv H) k = Some (Some v) ->
  value v /\ forall C L G, ht (hot H) (hft H) C L G v T e0.
Proof. intros H k T n E v [_ [_ [_ A]]]; apply A. Qed.

(* 型付けの反転補題。証明を仮説名に依存させないため *)
Lemma ht_oref_inv : forall ot ft C L G o T E,
  ht ot ft C L G (EORef o) T E ->
  exists c, T = TActor c /\ E = e0 /\ nth_error ot o = Some c.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma ht_fref_inv : forall ot ft C L G k T E,
  ht ot ft C L G (EFRef k) T E ->
  exists T0 n0 E0, T = TFut T0 n0 E0 /\ E = e0
                /\ nth_error ft k = Some (T0, n0, E0).
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_add_inv : forall ot ft C L G a b T E,
  ht ot ft C L G (EAdd a b) T E ->
  exists Ea Eb, T = TInt /\ E = Ea ++ Eb
             /\ ht ot ft C L G a TInt Ea /\ ht ot ft C L G b TInt Eb.
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_lt_inv : forall ot ft C L G a b T E,
  ht ot ft C L G (ELt a b) T E ->
  exists Ea Eb, T = TBool /\ E = Ea ++ Eb
             /\ ht ot ft C L G a TInt Ea /\ ht ot ft C L G b TInt Eb.
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_if_inv : forall ot ft C L G a b d T E,
  ht ot ft C L G (EIf a b d) T E ->
  exists Ea Eb Ed, E = Ea ++ Eb ++ Ed
                /\ ht ot ft C L G a TBool Ea
                /\ ht ot ft C L G b T Eb /\ ht ot ft C L G d T Ed.
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_let_inv : forall ot ft C L G x e1 e2 T E,
  ht ot ft C L G (ELet x e1 e2) T E ->
  exists T1 E1 E2, E = E1 ++ E2 /\ ht ot ft C L G e1 T1 E1
                /\ ht ot ft C L (extend G x T1) e2 T E2.
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_self_inv : forall ot ft C L G T E,
  ht ot ft C L G ESelf T E -> T = TActor C /\ E = e0.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_get_inv : forall ot ft C L G T E,
  ht ot ft C L G EGet T E -> T = stype C /\ E = e0.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_set_inv : forall ot ft C L G e T E,
  ht ot ft C L G (ESet e) T E ->
  exists E1, T = TUnit /\ E = emut :: E1 /\ ht ot ft C L G e (stype C) E1.
Proof. intros. inversion H; subst; eauto. Qed.
Lemma ht_new_inv : forall ot ft C L G cn T E,
  ht ot ft C L G (ENew cn) T E -> T = TActor cn /\ E = e0.
Proof. intros. inversion H; subst; auto. Qed.
Lemma ht_send_inv : forall ot ft C L G e0' m e1 T E,
  ht ot ft C L G (EFSend e0' m e1) T E ->
  exists c1 ta1 tr1 Ea E1,
       ht ot ft C L G e0' (TActor c1) Ea
    /\ mtab c1 m = Some (ta1, tr1)
    /\ ht ot ft C L G e1 ta1 E1
    /\ T = TFut tr1 (mlvl c1 m) (meff c1 m)
    /\ E = Ea ++ E1.
Proof. intros. inversion H; subst. exists c, ta, tr, Ea, E1. auto. Qed.
Lemma ht_await_inv : forall ot ft C L G e T E,
  ht ot ft C L G (EAwait e) T E ->
  exists n Ee Ec, ht ot ft C L G e (TFut T n Ec) Ee /\ L < n /\ E = Ee ++ Ec.
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_seq_inv : forall ot ft C L G a b T E,
  ht ot ft C L G (ESeq a b) T E ->
  exists T1 Ea Eb, E = Ea ++ Eb
                /\ ht ot ft C L G a T1 Ea /\ ht ot ft C L G b T Eb.
Proof. intros. inversion H; subst; eauto 10. Qed.
Lemma ht_while_inv : forall ot ft C L G a b T E,
  ht ot ft C L G (EWhile a b) T E ->
  exists T1 Ea Eb, T = TUnit /\ E = Ea ++ Eb
                /\ ht ot ft C L G a TBool Ea /\ ht ot ft C L G b T1 Eb.
Proof. intros. inversion H; subst; eauto 10. Qed.

Ltac split5 := split; [ | split; [ | split; [ | split ] ] ].
Ltac split4 := split; [ | split; [ | split ] ].
Ltac lift := eapply ht_mono; [ eassumption | try assumption; apply ext_refl
                             | try assumption; apply ext_refl ].
Ltac nomsg := intros ? [].

(* 効果の合併に対する単調性 *)
Lemma incl_app2 : forall (a a' b b' : eff),
  incl a a' -> incl b b' -> incl (a ++ b) (a' ++ b').
Proof.
  intros a a' b b' Ha Hb. apply incl_app;
    [ apply incl_appl | apply incl_appr ]; assumption.
Qed.

Lemma incl_e0 : forall (l : eff), incl e0 l.
Proof. intros l x []. Qed.

(* 一歩進んでも、型は変わらず、効果は増えない。
   「増えない」が効果の健全性の中身である。 *)
Lemma local_preservation : forall H o c L e T E H' out e',
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  ht (hot H) (hft H) c L empty e T E ->
  tstep H o e H' out e' ->
  heap_ok H'
  /\ ext (hot H) (hot H')
  /\ ext (hft H) (hft H')
  /\ (exists E', ht (hot H') (hft H') c L empty e' T E' /\ incl E' E)
  /\ (forall M, In M out -> msg_ok H' M).
Proof.
  intros H o c L e T E H' out e' Hh Ho Ht Hs.
  generalize dependent T. generalize dependent E. revert Ho. revert Hh.
  induction Hs; intros Hh Ho E T Ht.
  - (* STAdd *)
    apply ht_add_inv in Ht as [Ea [Eb [-> [-> _]]]].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists e0; split; [ constructor | apply incl_e0 ] | nomsg ].
  - (* STLt *)
    apply ht_lt_inv in Ht as [Ea [Eb [-> [-> _]]]].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists e0; split; [ constructor | apply incl_e0 ] | nomsg ].
  - (* STIfT *)
    apply ht_if_inv in Ht as [Ea [Eb [Ed [-> [_ [Hb _]]]]]].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists Eb; split; [ assumption | ] | nomsg ].
    apply incl_appr. apply incl_appl. apply incl_refl.
  - (* STIfF *)
    apply ht_if_inv in Ht as [Ea [Eb [Ed [-> [_ [_ Hd]]]]]].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists Ed; split; [ assumption | ] | nomsg ].
    apply incl_appr. apply incl_appr. apply incl_refl.
  - (* STLet *)
    apply ht_let_inv in Ht as [T1 [E1 [E2 [-> [Hv1 Hb]]]]].
    assert (E1 = e0) by (eapply value_eff; eassumption). subst E1.
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists E2; split; [ | simpl; apply incl_refl ] | nomsg ].
    eapply substitution; [ eassumption | assumption | ].
    intros C' L' G'. eapply value_ht_indep; eassumption.
  - (* STSelf *)
    apply ht_self_inv in Ht as [-> ->].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists e0; split; [ constructor; assumption | apply incl_refl ]
            | nomsg ].
  - (* STGet *)
    apply ht_get_inv in Ht as [-> ->].
    destruct (heap_st_ok _ _ _ _ Hh Ho H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists e0; split; [ apply Hvt | apply incl_refl ] | nomsg ].
  - (* STSet *)
    apply ht_set_inv in Ht as [E1 [-> [-> Hv0]]].
    assert (Hvt : forall C' L' G', ht (hot H) (hft H) C' L' G' v (stype c) e0).
    { intros C' L' G'. eapply value_ht_indep; eassumption. }
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
      * intros k2 T2 n2 E2 w2 Hk Hw2. apply (heap_fv_ok _ _ _ _ _ _ Hh Hk Hw2).
    + apply ext_refl.
    + apply ext_refl.
    + exists e0. split; [ constructor | apply incl_e0 ].
    + nomsg.
  - (* STNew *)
    apply ht_new_inv in Ht as [-> ->].
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
           intros C' L' G'. eapply ht_mono; [ apply Hvt | assumption | apply ext_refl ].
        -- subst o2 c2. rewrite <- (heap_len_st _ Hh) in Hsv.
           rewrite nth_app_last in Hsv. inversion Hsv; subst.
           split; [ apply sinit_value | intros C' L' G'; apply sinit_ok ].
      * intros k2 T2 n2 E2 w2 Hk Hw2.
        destruct (heap_fv_ok _ _ _ _ _ _ Hh Hk Hw2) as [Hvv Hvt].
        split; [ assumption | ].
        intros C' L' G'. eapply ht_mono; [ apply Hvt | assumption | apply ext_refl ].
    + assumption.
    + apply ext_refl.
    + exists e0. split; [ | apply incl_refl ].
      simpl. constructor. rewrite nth_app_last. reflexivity.
    + nomsg.
  - (* STSend *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ea [E1 [Hto [Hmt [Htv [-> ->]]]]]]]]].
    apply ht_oref_inv in Hto as [c2 [Heq [_ Hoc2]]]. inversion Heq; subst c2.
    assert (Hcc : c1 = cc) by congruence. subst c1.
    assert (Hpair : (ta1, tr1) = (ta, tr)) by congruence.
    inversion Hpair; subst ta1 tr1.
    assert (Hextf : ext (hft H) (hft H ++ [(tr, mlvl cc m, meff cc m)]))
      by apply ext_app.
    assert (Hvt : forall C' L' G',
              ht (hot H) (hft H ++ [(tr, mlvl cc m, meff cc m)]) C' L' G' v ta e0).
    { intros C' L' G'. eapply ht_mono;
        [ eapply value_ht_indep; eassumption | apply ext_refl | assumption ]. }
    split5.
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * repeat rewrite length_app. rewrite (heap_len_fv _ Hh). reflexivity.
      * intros o2 c2 v2 Hoc Hsv.
        destruct (heap_st_ok _ _ _ _ Hh Hoc Hsv) as [Hvv Hv2].
        split; [ assumption | ].
        intros C' L' G'. eapply ht_mono; [ apply Hv2 | apply ext_refl | assumption ].
      * intros k2 T2 n2 E2 w2 Hk Hw2.
        destruct (nth_app1_inv _ _ _ _ _ Hw2) as [[Hlt Hw0] | [Heq2 Hbad]];
          [ | discriminate ].
        rewrite nth_error_app1 in Hk by (rewrite <- (heap_len_fv _ Hh); lia).
        destruct (heap_fv_ok _ _ _ _ _ _ Hh Hk Hw0) as [Hvv Hv2].
        split; [ assumption | ].
        intros C' L' G'. eapply ht_mono; [ apply Hv2 | apply ext_refl | assumption ].
    + apply ext_refl.
    + assumption.
    + exists e0. split; [ | apply incl_e0 ].
      simpl. constructor. rewrite nth_app_last. reflexivity.
    + intros M HM. simpl in HM. destruct HM as [<- | []].
      exists cc, ta, tr. simpl.
      split; [ assumption | ]. split; [ assumption | ]. split; [ assumption | ].
      split; [ apply Hvt | ]. rewrite nth_app_last. reflexivity.
  - (* STAwait *)
    apply ht_await_inv in Ht as [nn [Ee [Ec [Ht [_ ->]]]]].
    apply ht_fref_inv in Ht as [T0 [n0 [E0 [Heq [-> Hk]]]]].
    inversion Heq; subst T0 n0 E0.
    destruct (heap_fv_ok _ _ _ _ _ _ Hh Hk H0) as [Hvv Hvt].
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists e0; split; [ apply Hvt | apply incl_e0 ] | nomsg ].
  (* --- 合同規則 --- *)
  - (* STAdd1 *)
    apply ht_add_inv in Ht as [Ea [Eb [-> [-> [Ha Hb]]]]].
    destruct (IHHs Hh Ho Ea TInt Ha) as [Hh' [Ho1 [Hf1 [[Ea' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea' ++ Eb). split; [ econstructor; [ eassumption | lift ] | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STAdd2 *)
    apply ht_add_inv in Ht as [Ea [Eb [-> [-> [Ha Hb]]]]].
    destruct (IHHs Hh Ho Eb TInt Hb) as [Hh' [Ho1 [Hf1 [[Eb' [Hb1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea ++ Eb'). split; [ econstructor; [ lift | eassumption ] | ].
    apply incl_app2; [ apply incl_refl | assumption ].
  - (* STLt1 *)
    apply ht_lt_inv in Ht as [Ea [Eb [-> [-> [Ha Hb]]]]].
    destruct (IHHs Hh Ho Ea TInt Ha) as [Hh' [Ho1 [Hf1 [[Ea' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea' ++ Eb). split; [ econstructor; [ eassumption | lift ] | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STLt2 *)
    apply ht_lt_inv in Ht as [Ea [Eb [-> [-> [Ha Hb]]]]].
    destruct (IHHs Hh Ho Eb TInt Hb) as [Hh' [Ho1 [Hf1 [[Eb' [Hb1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea ++ Eb'). split; [ econstructor; [ lift | eassumption ] | ].
    apply incl_app2; [ apply incl_refl | assumption ].
  - (* STIf1 *)
    apply ht_if_inv in Ht as [Ea [Eb [Ed [-> [Ha [Hb Hd]]]]]].
    destruct (IHHs Hh Ho Ea TBool Ha) as [Hh' [Ho1 [Hf1 [[Ea' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea' ++ Eb ++ Ed).
    split; [ econstructor; [ eassumption | lift | lift ] | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STLet1 *)
    apply ht_let_inv in Ht as [T1 [E1 [E2 [-> [Ha Hb]]]]].
    destruct (IHHs Hh Ho E1 T1 Ha) as [Hh' [Ho1 [Hf1 [[E1' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (E1' ++ E2). split; [ econstructor; [ eassumption | lift ] | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STSet1 *)
    apply ht_set_inv in Ht as [E1 [-> [-> Ha]]].
    destruct (IHHs Hh Ho E1 (stype c) Ha) as [Hh' [Ho1 [Hf1 [[E1' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (emut :: E1'). split; [ constructor; assumption | ].
    intros z Hz. destruct Hz as [<- | Hz]; [ left; reflexivity | right; auto ].
  - (* STSend1 *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ea [E1 [Hto [Hmt [Htv [-> ->]]]]]]]]].
    destruct (IHHs Hh Ho Ea (TActor c1) Hto)
      as [Hh' [Ho1 [Hf1 [[Ea' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea' ++ E1).
    split; [ econstructor; [ eassumption | eassumption | lift ] | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STSend2 *)
    apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ea [E1 [Hto [Hmt [Htv [-> ->]]]]]]]]].
    destruct (IHHs Hh Ho E1 ta1 Htv) as [Hh' [Ho1 [Hf1 [[E1' [Hb1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea ++ E1').
    split; [ econstructor; [ lift | eassumption | eassumption ] | ].
    apply incl_app2; [ apply incl_refl | assumption ].
  - (* STAwait1 *)
    apply ht_await_inv in Ht as [nn [Ee [Ec [Ha [Hlt ->]]]]].
    destruct (IHHs Hh Ho Ee (TFut T nn Ec) Ha)
      as [Hh' [Ho1 [Hf1 [[Ee' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ee' ++ Ec). split; [ econstructor; eassumption | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STSeq *)
    apply ht_seq_inv in Ht as [T1 [Ea [Eb [-> [Ha Hb]]]]].
    assert (Ea = e0) by (eapply value_eff; eassumption). subst Ea.
    split5; [ assumption | apply ext_refl | apply ext_refl
            | exists Eb; split; [ assumption | simpl; apply incl_refl ] | nomsg ].
  - (* STSeq1 *)
    apply ht_seq_inv in Ht as [T1 [Ea [Eb [-> [Ha Hb]]]]].
    destruct (IHHs Hh Ho Ea T1 Ha) as [Hh' [Ho1 [Hf1 [[Ea' [Ha1 Hi]] Hm1]]]].
    split5; try assumption.
    exists (Ea' ++ Eb). split; [ econstructor; [ eassumption | lift ] | ].
    apply incl_app2; [ assumption | apply incl_refl ].
  - (* STWhile *)
    apply ht_while_inv in Ht as [T1 [Ea [Eb [-> [-> [Hc Hb]]]]]].
    split5; [ assumption | apply ext_refl | apply ext_refl | | nomsg ].
    exists (Ea ++ (Eb ++ (Ea ++ Eb)) ++ e0). split.
    + econstructor; [ eassumption | | constructor ].
      econstructor; [ eassumption | ]. econstructor; eassumption.
    + apply incl_app; [ apply incl_appl; apply incl_refl | ].
      apply incl_app; [ | apply incl_e0 ].
      apply incl_app; [ apply incl_appr; apply incl_refl | apply incl_refl ].
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
  intros C' L' G'. eapply ht_mono; [ apply D | auto | auto ].
Qed.

Lemma task_ok_mono : forall H H' t,
  task_ok H t -> ext (hot H) (hot H') -> ext (hft H) (hft H') -> task_ok H' t.
Proof.
  intros H H' [[o k] e] Ht Ho Hf. simpl in *.
  destruct Ht as [c [T [L [EF [E [A [B [Cc Hi]]]]]]]].
  exists c, T, L, EF, E. split; [ auto | ]. split; [ auto | ].
  split; [ | auto ].
  eapply ht_mono; [ apply Cc | auto | auto ].
Qed.

(* 一歩で新しく「未解決」になる future には、その一歩が出したメッセージが
   必ず対応する。STSend だけが future を増やし、そのとき同時に
   メッセージを出すからである。prod_ok の保存はここに帰着する。 *)
Lemma tstep_fut : forall H o e H' out e',
  heap_ok H ->
  tstep H o e H' out e' ->
  forall k T n E,
    nth_error (hft H') k = Some (T, n, E) ->
    nth_error (hfv H') k = Some None ->
    nth_error (hfv H) k = Some None \/ (exists o' m' v', In (o', m', v', k) out).
Proof.
  intros H o e H' out e' Hh Hs.
  induction Hs; intros k0 T0 n0 E0 Hk Hu; simpl in *;
    try (left; exact Hu); try (eapply IHHs; eassumption).
  - (* STSend: future を一つ増やし、同時にメッセージを出す *)
    destruct (nth_app1_inv _ _ _ _ _ Hu) as [[Hlt Hu0] | [Heq Hbad]].
    + left. exact Hu0.
    + right. exists o', m, v. left. subst k0.
      f_equal. f_equal. symmetry. apply (heap_len_fv _ Hh).
Qed.

(* --- 定理 1: 理解できないメッセージは飛ばない --- *)
Theorem no_method_not_understood : forall H ms ts o m v k,
  conf_ok (H, ms, ts) ->
  In (o, m, v, k) ms ->
  exists c ta tr,
       nth_error (hot H) o = Some c
    /\ mtab c m = Some (ta, tr)
    /\ (forall C L G, ht (hot H) (hft H) C L G v ta e0)
    /\ nth_error (hft H) k = Some (tr, mlvl c m, meff c m).
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
    destruct Hok as [Hh [Hb [Hms [Hts Hpr]]]].
  - (* CTask *)
    assert (Hte : task_ok H (o, k, e)) by (apply Hts; apply in_app_middle).
    simpl in Hte.
    destruct Hte as [cc [T [LL [EF [E [Hoc [Hk [Hte Hi]]]]]]]].
    destruct (local_preservation _ _ _ _ _ _ _ _ _ _ Hh Hoc Hte H0)
      as [Hh' [Hxo [Hxf [[E' [Hte' Hi']] Hout]]]].
    split; [ assumption | ]. split; [ eapply ext_trans; eassumption | ].
    split; [ | split ].
    + intros M HM. apply in_app_or in HM. destruct HM as [HM | HM].
      * eapply msg_ok_mono; [ apply Hms; assumption | assumption | assumption ].
      * apply Hout. assumption.
    + intros t HT. apply in_app_or in HT. destruct HT as [HT | [Heq | HT]].
      * eapply task_ok_mono; [ apply Hts; apply in_or_app; left; eassumption
                            | assumption | assumption ].
      * subst t. simpl. exists cc, T, LL, EF, E'.
        split; [ apply Hxo; assumption | ]. split; [ apply Hxf; assumption | ].
        split; [ assumption | ].
        (* ★ 効果は増えない。E' ⊆ E ⊆ EF *)
        eapply incl_tran; eassumption.
      * eapply task_ok_mono; [ apply Hts; apply in_or_app; right; right; eassumption
                            | assumption | assumption ].
    + (* prod_ok *)
      intros k2 T2 n2 E2 Hk2 Hu2.
      destruct (tstep_fut _ _ _ _ _ _ Hh H0 _ _ _ _ Hk2 Hu2) as [Hold | Hnew].
      * assert (Hk2' : exists T3 n3 E3, nth_error (hft H) k2 = Some (T3, n3, E3)).
        { assert (Hlt : k2 < length (hft H)).
          { rewrite <- (heap_len_fv _ Hh). eapply nth_error_lt; eauto. }
          destruct (nth_error_ex _ _ _ Hlt) as [[[T3 n3] E3] Eq]. eauto. }
        destruct Hk2' as [T3 [n3 [E3 E3q]]].
        destruct (Hpr _ _ _ _ E3q Hold) as [[o3 [m3 [v3 Hin]]] | [o3 [e3 Hin]]].
        -- left. exists o3, m3, v3. apply in_or_app. left. assumption.
        -- right. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
           ++ exists o3, e3. apply in_or_app. left. assumption.
           ++ inversion Heq; subst o3 k2 e3. exists o, e'.
              apply in_app_middle.
           ++ exists o3, e3. apply in_or_app. right. right. assumption.
      * destruct Hnew as [o3 [m3 [v3 Hin]]].
        left. exists o3, m3, v3. apply in_or_app. right. assumption.
  - (* CFinish *)
    assert (Hte : task_ok H (o, k, v)) by (apply Hts; apply in_app_middle).
    simpl in Hte.
    destruct Hte as [cc [T [LL [EF [E [Hoc [Hk [Hte Hi]]]]]]]].
    assert (Hvt : forall C' L' G', ht (hot H) (hft H) C' L' G' v T e0).
    { intros C' L' G'. eapply value_ht_indep; eassumption. }
    assert (Hkl : k < length (hfv H)).
    { rewrite (heap_len_fv _ Hh). eapply nth_error_lt; eauto. }
    destruct (nth_error_ex _ _ _ Hkl) as [ov Hov].
    split; [ | split; [ simpl; assumption | split; [ | split ] ] ].
    + unfold heap_ok; simpl; split4.
      * apply (heap_len_st _ Hh).
      * rewrite upd_length. apply (heap_len_fv _ Hh).
      * intros o2 c2 v2 A B. apply (heap_st_ok _ _ _ _ Hh A B).
      * intros k2 T2 n2 E2 w2 A B.
        destruct (Nat.eq_dec k2 k) as [Heqk | Hne].
        -- subst k2. rewrite (nth_upd_eq _ _ _ _ _ Hov) in B. inversion B; subst.
           rewrite Hk in A. inversion A; subst.
           split; [ assumption | apply Hvt ].
        -- rewrite nth_upd_neq in B by auto.
           apply (heap_fv_ok _ _ _ _ _ _ Hh A B).
    + intros M HM. simpl. apply Hms. assumption.
    + intros t HT. simpl. apply Hts. apply in_app_or in HT.
      apply in_or_app. destruct HT as [HT | HT]; [ left; auto | right; right; auto ].
    + simpl. intros k2 T2 n2 E2 Hk2 Hu2. simpl in Hk2, Hu2.
      destruct (Nat.eq_dec k2 k) as [Heqk | Hne].
      * subst k2.
        rewrite (nth_upd_eq _ _ _ _ _ Hov) in Hu2. discriminate.
      * rewrite nth_upd_neq in Hu2 by auto.
        destruct (Hpr _ _ _ _ Hk2 Hu2) as [Hmsg | [o3 [e3 Hin]]].
        -- left. assumption.
        -- right. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
           ++ exists o3, e3. apply in_or_app. left. assumption.
           ++ inversion Heq; subst. contradiction Hne. reflexivity.
           ++ exists o3, e3. apply in_or_app. right. assumption.
  - (* CDeliver *)
    assert (Hme : msg_ok H (o, m, v, k)) by (apply Hms; apply in_app_middle).
    simpl in Hme. destruct Hme as [c0 [ta0 [tr0 [A [B [Cv [D E]]]]]]].
    assert (Hc : c0 = c) by congruence. subst c0.
    assert (Hp : (ta0, tr0) = (ta, tr)) by congruence.
    inversion Hp; subst ta0 tr0.
    split; [ assumption | ]. split; [ assumption | ]. split; [ | split ].
    + intros M HM. apply Hms. apply in_app_or in HM.
      apply in_or_app. destruct HM as [HM | HM]; [ left; auto | right; right; auto ].
    + intros t HT. apply in_app_or in HT. destruct HT as [HT | [Heq | []]].
      * apply Hts. assumption.
      * subst t. simpl.
        destruct (bodies_ok _ _ _ _ B (hot H) (hft H) Hb) as [Ebody [Hbody Hbi]].
        exists c, tr, (mlvl c m), (meff c m), Ebody.
        split; [ assumption | ]. split; [ assumption | ].
        split; [ | assumption ].
        eapply substitution; [ eassumption | assumption | ].
        intros C' L' G'. apply D.
    + (* prod_ok: 配送されたメッセージの役目は、起きたタスクが引き継ぐ *)
      intros k2 T2 n2 E2 Hk2 Hu2.
      destruct (Hpr _ _ _ _ Hk2 Hu2) as [[o3 [m3 [v3 Hin]]] | [o3 [e3 Hin]]].
      * apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
        -- left. exists o3, m3, v3. apply in_or_app. left. assumption.
        -- inversion Heq; subst o3 m3 v3 k2.
           right. exists o, (subst 0 v (mbody c m)).
           apply in_or_app. right. left. reflexivity.
        -- left. exists o3, m3, v3. apply in_or_app. right. assumption.
      * right. exists o3, e3. apply in_or_app. left. assumption.
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
    simpl in Hte. destruct Hte as [c [T [LL [EF [E [Hoc [Hk [Hte Hi]]]]]]]].
    destruct (local_progress _ _ _ _ _ _ _ _ Hh Hoc Hte (fun _ => eq_refl))
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
  intros [[H ms] ts] [Hh [Hb [Hms [Hts Hpr]]]].
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
    value v /\ forall C0 L0 G, ht (hot H') (hft H') C0 L0 G v (stype c) e0.
Proof.
  intros C H' ms' ts' Hok Hs o c v Hoc Hsv.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [Hh _]. apply (heap_st_ok _ _ _ _ Hh Hoc Hsv).
Qed.

(* --- 定理 6: 解決済み future の値は宣言された返り値型を持つ ---
   これが reply と now/future の戻り値型の一致である。 *)
Theorem future_type_invariant : forall C H' ms' ts',
  conf_ok C -> csteps C (H', ms', ts') ->
  forall k T n E v, nth_error (hft H') k = Some (T, n, E) ->
                    nth_error (hfv H') k = Some (Some v) ->
    value v /\ forall C0 L0 G, ht (hot H') (hft H') C0 L0 G v T e0.
Proof.
  intros C H' ms' ts' Hok Hs k T n E v Hk Hv.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [Hh _]. apply (heap_fv_ok _ _ _ _ _ _ Hh Hk Hv).
Qed.

(* ================================================================= *)
(* 11. デッドロック自由 ---- 義務レベルによる                        *)
(* ================================================================= *)

(* 第 1 版は await を言語から取り除いた断片 (afree) についてしか
   デッドロック自由を言えなかった。第 2 版は await を含んだまま言う。

   道具は義務レベルである。
     ・future は「どのレベルのメソッドが埋めるか」を型に持つ (TFut T n)
     ・レベル L のメソッドが待てるのは、レベルが L より真に大きい future だけ
     ・タスクは、自分が埋める future のレベルのもとで型が付く (task_ok)
     ・未解決の future には必ず埋める者がいる (prod_ok)

   この四つから、全タスクが待ち状態になることはない。
   証明の骨は「レベルが最大のタスクを取る」ことである。
   そのタスクも待っているなら、待っている先の future のレベルは
   さらに大きく、その future を埋める者もまたタスクなので、
   レベル最大に反する。 *)

(* タスクのレベル: 自分が埋める future に記録されているもの *)
Definition tlvl (H : heap) (t : task) : nat :=
  let '(_, k, _) := t in
  match nth_error (hft H) k with Some (_, n, _) => n | None => 0 end.

(* 有限のリストにはレベル最大の要素がある *)
Lemma exists_max_task : forall H ts,
  ts <> [] ->
  exists t, In t ts /\ forall t', In t' ts -> tlvl H t' <= tlvl H t.
Proof.
  intros H ts. induction ts as [| a ts IH]; intros Hne; [ contradiction | ].
  destruct ts as [| b ts'].
  - exists a. split; [ left; reflexivity | ].
    intros t' [<- | []]. apply Nat.le_refl.
  - destruct (IH ltac:(discriminate)) as [t [Hin Hmax]].
    destruct (Nat.le_gt_cases (tlvl H a) (tlvl H t)) as [Hle | Hgt].
    + exists t. split; [ right; assumption | ].
      intros t' [<- | Hin']; [ assumption | apply Hmax; assumption ].
    + exists a. split; [ left; reflexivity | ].
      intros t' [<- | Hin']; [ apply Nat.le_refl | ].
      apply Nat.le_trans with (m := tlvl H t);
        [ apply Hmax; assumption | apply Nat.lt_le_incl; assumption ].
Qed.

(* 待っている式は、必ず「未解決の future をひとつ」名指ししている。
   その future のレベルは、いま型が付いているレベルより真に大きい。 *)
Lemma awaiting_fut : forall H c L e T E,
  heap_ok H ->
  ht (hot H) (hft H) c L empty e T E ->
  awaiting H e ->
  exists k Tk nk Ek,
       nth_error (hft H) k = Some (Tk, nk, Ek)
    /\ nth_error (hfv H) k = Some None
    /\ L < nk.
Proof.
  intros H c L e T E Hh Ht Haw. revert T E Ht.
  induction Haw; intros T E Ht.
  - (* AwHere: await (EFRef k) を、まさにここで待っている *)
    apply ht_await_inv in Ht as [n0 [Ee [Ec [Ht0 [Hlt _]]]]].
    apply ht_fref_inv in Ht0 as [T0 [n1 [E1 [Heq [_ Hk]]]]].
    inversion Heq; subst T0 n1 E1.
    exists k, T, n0, Ec.
    split; [ exact Hk | ]. split; [ assumption | exact Hlt ].
  - apply ht_add_inv in Ht as [Ea [Eb [_ [_ [Ha _]]]]]. eapply IHHaw; eassumption.
  - apply ht_add_inv in Ht as [Ea [Eb [_ [_ [_ Hb]]]]]. eapply IHHaw; eassumption.
  - apply ht_lt_inv in Ht as [Ea [Eb [_ [_ [Ha _]]]]]. eapply IHHaw; eassumption.
  - apply ht_lt_inv in Ht as [Ea [Eb [_ [_ [_ Hb]]]]]. eapply IHHaw; eassumption.
  - apply ht_if_inv in Ht as [Ea [Eb [Ed [_ [Ha _]]]]]. eapply IHHaw; eassumption.
  - apply ht_let_inv in Ht as [T1 [E1 [E2 [_ [Ha _]]]]]. eapply IHHaw; eassumption.
  - apply ht_set_inv in Ht as [E1 [_ [_ Ha]]]. eapply IHHaw; eassumption.
  - apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ea [E1 [Ha _]]]]]].
    eapply IHHaw; eassumption.
  - apply ht_send_inv in Ht as [c1 [ta1 [tr1 [Ea [E1 [_ [_ [Hb _]]]]]]]].
    eapply IHHaw; eassumption.
  - apply ht_await_inv in Ht as [n0 [Ee [Ec [Ha _]]]]. eapply IHHaw; eassumption.
  - apply ht_seq_inv in Ht as [T1 [Ea [Eb [_ [Ha _]]]]]. eapply IHHaw; eassumption.
Qed.

(* --- 定理 7: デッドロック自由 ------------------------------------
   型の付いた構成は、全タスクが待ち状態になることがない。
   await を除いた断片ではなく、await を含んだ言語全体について言える。 *)
Theorem deadlock_free : forall C, conf_ok C -> ~ blocked C.
Proof.
  intros [[H ms] ts] [Hh [Hb [Hms [Hts Hpr]]]] [Hnil [Hne Hall]].
  (* レベルが最大のタスクを取る *)
  destruct (exists_max_task H ts Hne) as [[[o k] e] [Hin Hmax]].
  assert (Haw : awaiting H e) by (apply (Hall o k e); assumption).
  assert (Hte : task_ok H (o, k, e)) by (apply Hts; assumption).
  simpl in Hte. destruct Hte as [c [T [L [EF [E [Hoc [Hk [Ht Hi]]]]]]]].
  (* そのタスクが待っている future は、自分より上のレベルである *)
  destruct (awaiting_fut _ _ _ _ _ _ Hh Ht Haw)
    as [k2 [T2 [n2 [E2 [Hk2 [Hu2 Hlt]]]]]].
  (* その future には埋める者がいる *)
  destruct (Hpr _ _ _ _ Hk2 Hu2) as [[o3 [m3 [v3 Hin3]]] | [o3 [e3 Hin3]]].
  - (* メッセージだとすると、メールボックスは空ではない ---- 矛盾 *)
    subst ms. destruct Hin3.
  - (* タスクだとすると、そのレベルは n2。L < n2 なのに最大性から n2 <= L *)
    assert (Hle : tlvl H (o3, k2, e3) <= tlvl H (o, k, e))
      by (apply Hmax; assumption).
    unfold tlvl in Hle. rewrite Hk2 in Hle. rewrite Hk in Hle. lia.
Qed.

(* --- 定理 8: 進行（デッドロックの逃げ道なし） --------------------
   第 1 版の progress は「終状態 / 一歩進める / 全部待ち」の三択だった。
   第 3 の枝が消えるので、二択になる。 *)
Theorem progress_total : forall C,
  conf_ok C -> terminal C \/ (exists C', cstep C C').
Proof.
  intros C Hok. destruct (progress _ Hok) as [Ht | [Hst | Hbl]].
  - left. assumption.
  - right. assumption.
  - exfalso. eapply deadlock_free; eassumption.
Qed.

(* 到達可能な構成すべてについて言い直す *)
Theorem deadlock_free_star : forall C C',
  conf_ok C -> csteps C C' ->
  ~ blocked C' /\ (terminal C' \/ exists C'', cstep C' C'').
Proof.
  intros C C' Hok Hs.
  assert (Hok' : conf_ok C') by (eapply preservation_star; eassumption).
  split; [ eapply deadlock_free; eassumption | apply progress_total; assumption ].
Qed.

(* ================================================================= *)
(* 12. 効果の健全性                                                  *)
(* ================================================================= *)

(* --- 定理 10: 一歩進んでも効果は増えない ------------------------- *)
Theorem effect_no_increase : forall H o c L e T E H' out e',
  heap_ok H ->
  nth_error (hot H) o = Some c ->
  ht (hot H) (hft H) c L empty e T E ->
  tstep H o e H' out e' ->
  exists E', ht (hot H') (hft H') c L empty e' T E' /\ incl E' E.
Proof.
  intros H o c L e T E H' out e' Hh Ho Ht Hs.
  destruct (local_preservation _ _ _ _ _ _ _ _ _ _ Hh Ho Ht Hs)
    as [_ [_ [_ [Hex _]]]]. exact Hex.
Qed.

(* --- 定理 11: 待つと呼び先の効果を必ず引き継ぐ -------------------
   これが「効果は一段隔てても隠せない」の中身である。
   send は待たないので引き継がないが、await は引き継ぐ。 *)
Theorem await_charges_callee : forall ot ft C L G e T E,
  ht ot ft C L G (EAwait e) T E ->
  exists n Ee Ec,
       ht ot ft C L G e (TFut T n Ec) Ee
    /\ L < n
    /\ incl Ec E /\ incl Ee E.
Proof.
  intros ot ft C L G e T E Ht.
  apply ht_await_inv in Ht as [n [Ee [Ec [Ht [Hlt ->]]]]].
  exists n, Ee, Ec.
  split; [ assumption | ]. split; [ assumption | ].
  split; [ apply incl_appr; apply incl_refl
         | apply incl_appl; apply incl_refl ].
Qed.

(* --- 定理 12: 走っているタスクの効果は、担当する future に
       記録された効果に収まり続ける ---------------------------------
   配送のときに bodies_ok（本体の効果は宣言した効果に収まる）が入り、
   以後は effect_no_increase で保たれる。
   したがって「メソッドが宣言した効果は、そのメソッドが実際に行うことを
   ---- now で呼んだ先も含めて ---- 覆っている」。 *)
Theorem effect_soundness : forall C H' ms' ts',
  conf_ok C -> csteps C (H', ms', ts') ->
  forall o k e, In (o, k, e) ts' ->
    exists c T L EF E,
         nth_error (hot H') o = Some c
      /\ nth_error (hft H') k = Some (T, L, EF)
      /\ ht (hot H') (hft H') c L empty e T E
      /\ incl E EF.
Proof.
  intros C H' ms' ts' Hok Hs o k e Hin.
  assert (Hok' : conf_ok (H', ms', ts')) by (eapply preservation_star; eassumption).
  destruct Hok' as [_ [_ [_ [Hts _]]]].
  apply (Hts (o, k, e) Hin).
Qed.

(* 送信は呼び先の効果を引き継がない（待たないので）。
   規則 HSend の結論の効果が Ea ++ E1 であって meff を含まないことが、
   そのまま主張になっている。 *)
Theorem send_does_not_charge : forall ot ft C L G ea m e1 T E,
  ht ot ft C L G (EFSend ea m e1) T E ->
  exists c ta tr Ea E1,
       mtab c m = Some (ta, tr)
    /\ T = TFut tr (mlvl c m) (meff c m)
    /\ E = Ea ++ E1
    /\ ht ot ft C L G ea (TActor c) Ea
    /\ ht ot ft C L G e1 ta E1.
Proof.
  intros. apply ht_send_inv in H
    as [c1 [ta1 [tr1 [Ea [E1 [Hto [Hmt [Htv [-> ->]]]]]]]]].
  exists c1, ta1, tr1, Ea, E1. auto.
Qed.

End AIPL.
