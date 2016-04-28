(* Lemmas about inserting None into a typing context *)
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
Import ListNotations.

(* Universal *)
Lemma insert_none_def : forall A x (E : env A),
  x >= length E ->
  raw_insert x None E = E ++ repeat (S (x - length E)) None.
Proof with (simpl; eboom).
  intros A x E Len.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    destruct E as [|e E'].
    SCase "E = []".
      rewrite raw_insert_zero...
    SCase "E = e :: E'".
      solve by inversion.
  Case "x = S x'".
    destruct E as [|e E'];
      simpl in *; rewrite raw_insert_successor; rewrite IHx'; simpl; try omega...
    SCase "E = []".
      replace (x' - 0) with x'; try omega...
Qed.

(* Universal *)
Lemma insert_none_is_empty : forall A (E : env A) E' x,
  is_empty E ->
  raw_insert x None E = E' ->
  is_empty E'.
Proof with eboom.
  intros A E E' x EmptyE Ins.
  generalize dependent E.
  generalize dependent E'.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Ins.
    subst...
  Case "x = S x'".
    rewrite raw_insert_successor in Ins.
    assert (lookup 0 E = None) as R; eauto using empty_lookup. rewrite R in Ins.
    subst E'.
    constructor.
    apply IHx' with (E := tl E)...
Qed.

Hint Resolve insert_none_is_empty : l3.

(* Universal *)
Lemma insert_none_is_empty_inversion : forall A (E : env A) x,
  is_empty (raw_insert x None E) -> is_empty E.
Proof with eboom.
  intros A E x Empty.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Empty. inversion Empty...
  Case "x = S x'".
    rewrite raw_insert_successor in Empty.
    inversion Empty; subst.
    destruct E as [|e E']...
Qed.

(* Hint Resolve insert_none_is_empty_inversion : l3. *)

(* Universal *)
Lemma insert_none_split : forall A (E : env A) E1 E2 x,
  context_split E E1 E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2).
Proof with eboom.
  Local Transparent lookup.
  intros A E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero; eboom.
  Case "x = S x'".
    repeat rewrite raw_insert_successor.
    inversion Split as [|E' E1' E2']...
Qed.

(* Universal *)
Lemma split_none_head : forall A (E : env A) E1 E2,
  context_split (None :: E) E1 E2 ->
  exists E1' E2', E1 = None :: E1' /\ E2 = None :: E2'.
Proof with eboom.
  intros A E E1 E2 Split.
  inversion Split; inversion SplitElem; subst...
Qed.

(* Universal *)
Lemma split_insert_none_left_lookup : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  lookup x E1 = None.
Proof with eboom.
  intros A E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [| x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in *.
    inversion Split; inversion SplitElem...
  Case "x = S x'".
    rewrite raw_insert_successor in Split.
    destruct E1 as [|e1 E1']...
    replace (lookup (S x') (e1 :: E1')) with (lookup x' E1')...
    inversion Split; inversion SplitElem; subst...
Qed.

(* Universal *)
Lemma split_insert_none_right_lookup : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  lookup x E2 = None.
Proof.
  eauto using split_insert_none_left_lookup, split_commute.
Qed.

Lemma min_plus_r : forall n m,
  min n (n + m) = n.
Proof.
  intros.
  rewrite <- Plus.plus_0_r with (n := n) at 1.
  rewrite Min.plus_min_distr_l.
  auto.
Qed.

Lemma firstn_all : forall A (E : list A) l,
  l = length E ->
  firstn l E = E.
Proof with (subst; simpl; auto using f_equal).
  intros.
  generalize dependent l.
  induction E; intros...
Qed.

Hint Resolve firstn_all : l3.

(* Universal *)
Lemma split_app_single : forall A (E : env A) E1 E2,
  context_split (E ++ [None]) E1 E2 ->
  exists E1' E2', E1 = E1' ++ [None] /\ E2 = E2' ++ [None] /\ context_split E E1' E2'.
Proof.
  intros A E E1 E2 Split.
  generalize dependent E.
  generalize dependent E2.
  induction E1 as [| e1 E1s]; intros.
  Case "E1 = []".
  inversion Split.
  assert (E = [] /\ [@None A] = []) as [? ?].
    apply app_eq_nil.
    auto.
  solve by inversion.
  Case "E1 = e1 :: E1s".
    destruct E as [|e E'].
    SCase "E = []".
      exists nil. exists nil.
      simpl in *.
      inversion Split; inversion SplitPre; inversion SplitElem; subst; eboom.
    SCase "E = e :: E'".
      destruct E2 as [|e2 E2s]; try solve by inversion.
      (* E2 is now e2 :: E2s *)
      simpl in Split.
      inversion Split; subst.
      apply IHE1s in SplitPre.
      destruct SplitPre as [E1' [E2' [? [? ?]]]].
      exists (e1 :: E1').
      exists (e2 :: E2').
      subst.
      eboom.
Qed. (* NOTE: benefits of split_single demonstrated here *)

(* Universal *)
Lemma split_app : forall A (E : env A) E1 E2 n,
  context_split (E ++ repeat n None) E1 E2 ->
  exists E1' E2',
    E1 = E1' ++ repeat n None /\
    E2 = E2' ++ repeat n None /\
    context_split E E1' E2'.
Proof with eboom.
  intros A E E1 E2 n Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction n as [|n']; intros.
  Case "n = 0".
    simpl in *.
    exists E1, E2.
    repeat rewrite app_nil_r in *...
  Case "n = S n'".
    rewrite repeat_app in Split.
    rewrite app_assoc in Split.
    apply split_app_single in Split.
    destruct Split as [E1' [E2' [? [? SplitInd]]]].
    apply IHn' in SplitInd.
    destruct SplitInd as [E1'' [E2'' [? [? ?]]]].
    subst.
    exists E1''. exists E2''.
    repeat rewrite <- app_assoc.
    repeat rewrite repeat_app.
    eboom.
Qed.

(* Universal *)
Lemma insert_none_split_strip_none : forall A (E : env A) E1 E2 x,
  length E = length E1 ->
  length E = length E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2) ->
  context_split E E1 E2.
Proof with eboom.
  intros A E E1 E2 x Len1 Len2 Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero in *. inversion Split...
  Case "x = S x'".
    repeat rewrite raw_insert_successor in Split.
    inversion Split; subst.
    destruct E as [|e E'];
    destruct E1 as [|e1 E1'];
    destruct E2 as [|e2 E2']; try solve by inversion...
Qed. (* NOTE: more massive benefits of split_single *)

Hint Resolve insert_none_split_strip_none : l3.

(* Universal *)
Lemma insert_none_split_backwards : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  exists E1' E2',
    E1 = raw_insert x None E1' /\
    length E1' = length E /\
    E2 = raw_insert x None E2' /\
    length E2' = length E /\
    context_split E E1' E2'.
Proof with eboom.
  intros A E E1 E2 x Split.
  destruct (Compare_dec.le_gt_dec (length E) x) as [OutOfBounds | InBounds].
  Case "length E <= x".
    rewrite insert_none_def in Split; try omega.
    apply split_app in Split.
    destruct Split as [E1' [E2' [? [? ?]]]].
    exists E1', E2'.
    subst E1 E2.
    assert (length E1' = length E) as Len1...
    assert (length E2' = length E) as Len2...
    repeat rewrite insert_none_def; try omega.
    rewrite Len1; rewrite Len2...
  Case "length E > x".
    generalize dependent E.
    generalize dependent E1.
    generalize dependent E2.
    induction x as [|x']; intros.
    SCase "x = 0".
      repeat rewrite raw_insert_zero in *.
      destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2']; try solve by inversion.
      inversion Split; inversion SplitElem; subst;
        exists E1', E2';
        repeat rewrite raw_insert_zero;
        repeat split...
    SCase "x = S x'".
      destruct E as [|e E']; try solve by inversion.
      destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2']; try solve by inversion.
      rewrite raw_insert_successor in Split.
      simpl in Split.
      inversion Split; subst.
      apply IHx' in SplitPre; simpl in *; try omega.
      destruct SplitPre as [E1'' [E2'' [? [? [? [? ?]]]]]].
      exists (e1 :: E1''), (e2 :: E2'').
      subst; simpl.
      repeat split...
Qed. (* NOTE: more benefits of split_single *)

(* Do we need this any more? *)
(*
Lemma insert_none_split_right : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E2', E2 = raw_insert x None E2' /\ length E2' = length E).
Proof.
  eauto using insert_none_split_left, split_commute.
Qed.
*)

(* Lang-specific *)
Lemma typing_insert_none : forall L E e t x,
  L; E |- e ~: t ->
  L; raw_insert x None E |- shift x e ~: t.
Proof with (eauto using le_0_n, lt_n_Sm_le, insert_none_is_empty, insert_none_split with l3).
  intros L E e t x WT.
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
Lemma typing_insert_none_reverse : forall L E e t x,
  L; raw_insert x None E |- e ~: t ->
  L; E |- unshift x e ~: t.
Proof with (eauto using insert_none_is_empty_inversion with l3).
  Transparent lower.
  intros L E e t x WT.
  generalize dependent x.
  generalize dependent t.
  generalize dependent E.
  induction e; try solve [intros; simpl; inversion WT; subst; eauto using insert_none_is_empty_inversion with l3].
  Case "TVar".
    intros.
    simpl.
    destruct (le_gt_dec x n).
    SCase "x <= n".
      inversion WT; subst.
      rename E0 into E1.
      rename E into E2.
      symmetry in H1.
      apply raw_insert_swap in H1...
      decompose record H1.
      subst...
    SCase "x > n".
      inversion WT; subst.
      apply raw_insert_swap in H1.
      decompose record H1.
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
