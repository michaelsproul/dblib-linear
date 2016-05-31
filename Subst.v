(*
Require Import DbLib.Environments.
Require Import List.
Require Import Typing.
Require Import Syntax.
Require Import Empty.
Require Import Context.
Require Import Environment.
Require Import DbLib.DeBruijn.
Require Import Arith.
Require Import DbLibExt.
Require Import InsertNone.
Import ListNotations.
*)
Require Export DbLib.DeBruijn.
Require Export LLC.Syntax.
Require Export LLC.Typing.
Require Export Linear.Context.
Require Export Linear.InsertNone.
Require Export Arith.

(* For dependent induction we require "John Major" heterogeneous equality *)
Require Export Coq.Program.Equality.

Lemma unshift_Abs : forall x t e, unshift x (TAbs t e) = TAbs t (unshift (S x) e).
Proof with eauto.
  intros.
  simpl_lower_goal...
Qed.

Lemma unshift_App : forall x e1 e2,
  unshift x (TApp e1 e2) = TApp (unshift x e1) (unshift x e2).
Proof with auto.
  intros.
  simpl_lower_goal...
Qed.

Lemma subst_unshift : forall x e v,
  ~ contains_var x e ->
  subst v x e = unshift x e.
Proof with (eauto using f_equal, not_contains_Abs,
                        not_contains_App1, not_contains_App2 with linear).
  Local Transparent lower.
  intros x e v NotContains.
  generalize dependent x.
  generalize dependent v.
  induction e; try solve [simpl_subst_goal; simpl; auto].
  Case "Var".
    intros.
    simpl_subst_goal. simpl.
    destruct (le_gt_dec x n).
    SCase "x <= n".
      destruct (le_lt_eq_dec x n)...
      SSCase "x < n". subst_idx...
      SSCase "x = n". exfalso. subst...
    SCase "x > n".
      subst_idx...
  Case "Abs".
    intros.
    simpl_subst_goal. rewrite unshift_Abs...
  Case "App".
    intros.
    simpl_subst_goal. rewrite unshift_App.
    rewrite IHe1...
Qed.

Lemma typing_without_var : forall E e x t,
  raw_insert x None E |- e ~: t -> ~ contains_var x e.
Proof with (eauto using raw_insert_eq_insert_1, le_0_n).
  unfold not.
  intros E e x t WT Contains.
  generalize dependent E.
  generalize dependent x.
  generalize dependent t.
  induction e; try solve [intros; solve by inversion].
  Case "Var".
    intros.
    destruct (eq_nat_dec x n).
    SCase "x = n".
      subst x.
      inversion WT; subst.
      assert (Some t = None)...
      solve by inversion.
    SCase "x <> n".
      inversion Contains...
  Case "TAbs".
    intros.
    inversion WT; subst.
    rewrite insert_insert in AbsPre...
    inversion Contains; subst...
  Case "TApp".
    intros.
    inversion Contains;
      subst;
      inversion WT; subst;
      apply insert_none_split_backwards in AppPreSplit;
      decompose record AppPreSplit;
      subst...
Qed.

(* Lang-specific *)
(* Required by the lambda abstraction case in the substitution lemma *)
Lemma typing_insert_none : forall E e t x,
  E |- e ~: t ->
  raw_insert x None E |- shift x e ~: t.
Proof with (eauto using le_0_n, lt_n_Sm_le, insert_none_is_empty, insert_none_split with linear).
  intros E e t x WT.
  generalize dependent x.
  induction WT; intros y; simpl_lift_goal...
  Case "Var".
    destruct (le_lt_dec y x); lift_idx.
    SCase "y <= x".
      rewrite insert_insert...
    SCase "y > x".
      destruct y as [|y']; try solve by inversion...
      rewrite <- insert_insert...
  Case "Abs".
    constructor.
    rewrite insert_insert...
Qed.

(* Lang-specific *)
Lemma typing_insert_none_reverse : forall E e t x,
  raw_insert x None E |- e ~: t ->
  E |- unshift x e ~: t.
Proof with (eauto using insert_none_is_empty_inversion with linear).
  Transparent lower.
  intros E e t x WT.
  generalize dependent x.
  generalize dependent t.
  generalize dependent E.
  induction e; try solve [intros; simpl; inversion WT; subst; eauto using insert_none_is_empty_inversion with linear].
  Case "TVar".
    intros.
    simpl.
    destruct (le_gt_dec x n).
    SCase "x <= n".
      (* FIXME: naming is a pain here *)
      inversion WT; subst.
      rename E0 into E1.
      rename E into E2.
      symmetry in H0.
      apply raw_insert_swap in H0...
      decompose record H0.
      subst...
    SCase "x > n".
      inversion WT; subst.
      apply raw_insert_swap in H0.
      decompose record H0.
      subst...
      omega.
  Case "TAbs".
    intros.
    simpl_lower_goal.
    inversion WT; subst.
    econstructor.
    apply IHe.
    rewrite<- insert_insert...
    omega.
  Case "TApp".
    intros.
    simpl_lower_goal.
    inversion WT; subst.
    apply insert_none_split_backwards in AppPreSplit.
    destruct AppPreSplit as [E1' [E2' [? [? [? [? ?]]]]]].
    subst...
Qed.

Lemma typing_insert_none_subst : forall E e x junk t,
  raw_insert x None E |- e ~: t ->
  E |- subst junk x e ~: t.
Proof.
  intros E e x junk t WT.
  remember WT as H eqn:Junk; clear Junk.
  apply typing_without_var in H.
  apply subst_unshift with (v := junk) in H.
  rewrite H.
  eauto using typing_insert_none_reverse.
Qed.

Lemma length_zero_nil : forall A (l : list A),
  length l = length (@nil A) ->
  l = (@nil A).
Proof.
  intros. destruct l; try solve by inversion; reflexivity.
Qed.

Hint Immediate length_zero_nil : linear.

Lemma substitution: forall E2 e2 t1 t2 x,
  insert x t1 E2 |- e2 ~: t2 ->
  forall E E1 e1, E1 |- e1 ~: t1 ->
  context_split E E1 E2 ->
  E |- (subst e1 x e2) ~: t2.
Proof with (eauto using typing_insert_none, typing_insert_none_subst,
            split_rotate  with linear).
  intros E2 e2 t1 t2 x WT2 E E1 e1 WT1 Split.
  dependent induction WT2; simpl_subst_goal; try solve [exfalso; eauto using empty_insert_contra].
  Case "Var".
    (* XXX: naming of x is weird here *)
    apply empty_insert_injective in x...
    destruct x as [XEq [TEq E2Eq]].
    subst.
    simpl_subst_goal.
    apply split_all_left in Split...
    subst...
  Case "Abs".
    constructor.
    (* XXX: Bug (?) in error reporting - can't specify E0 *)
    eapply IHWT2 with (t3 := t1) (E1 := (None :: E1)).
    SCase "inserts are equal". insert_insert.
    SCase "e1 well-typed under shifting".
      assert (raw_insert 0 None E1 |- shift 0 e1 ~: t1)...
    SCase "context_split is sensible".
      repeat rewrite raw_insert_zero...
  Case "App".
    rename E0 into E2'.
    rename E1 into E1'.
    rename E3 into E0.
    rename E2 into E12.
    (* x is either in E1' or E2' *)
    assert (SplitX := AppPreSplit).
    apply context_split_insert in SplitX.
    destruct SplitX as [XLeft | XRight].
    SCase "x on the left".
      destruct XLeft as [E1 [E2 [? [? [? [? ?]]]]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E2 E1); [eboom | ].
      assert (exists E01, context_split E E2 E01 /\ context_split E01 E0 E1)
        as [E01 [Split201 SplitE01]]...
    SCase "x on the right".
      destruct XRight as [E1 [E2 [? [? [? [? ?]]]]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E1 E2); [eboom | ].
      assert (exists E02, context_split E E1 E02 /\ context_split E02 E0 E2)
        as [E01 [Split201 SplitE01]]...
Qed.
