(* Lemmas about inserting None into a typing context *)
Require Import DbLib.Environments.
Require Import Environments.
Require Import List.
Require Import Typing.
Require Import Syntax.
Require Import Empty.
Require Import Context.
Require Import Environment.
Import ListNotations.

Transparent lookup.

Check (nil; nil |- TTrue ~: TyBool).

Fixpoint repeat {A} (n : nat) (e : A) : list A :=
  match n with
  | 0 => []
  | S n' => e :: repeat n' e
  end.

Lemma repeat_length : forall A n (e : A),
  length (repeat n e) = n.
Proof with (simpl; auto).
  intros.
  induction n as [|n']...
Qed.

Lemma repeat_none_empty : forall A n,
  is_empty (repeat n None : env A).
Proof with (simpl; boom).
  intros.
  induction n...
Qed.

Lemma repeat_app : forall A n (e : A),
  repeat (S n) e = repeat n e ++ [e].
Proof.
  intros.
  induction n as [|n'].
  Case "n = 0". auto.
  Case "n = S n'".
    replace (repeat (S (S n')) e) with (e :: repeat (S n') e).
    rewrite IHn' at 1.
    auto.
    auto.
Qed.

Lemma is_empty_def : forall A (E : env A),
  is_empty E ->
  E = repeat (length E) None.
Proof with (simpl; boom).
  intros A E Empty.
  induction Empty...
Qed.

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

Lemma insert_none_empty_def : forall A x (E : env A),
  is_empty E ->
  raw_insert x None E = repeat (S (mymax (length E) x)) None.
Proof.
Abort.

Lemma insert_none_is_empty : forall {A} (E : env A) E' x,
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

Lemma insert_none_is_empty_inversion : forall {A} (E : env A) x,
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

Lemma insert_none_split : forall A (E : env A) E1 E2 x,
  context_split E E1 E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2).
Proof with eboom.
  intros A E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero; eboom.
  Case "x = S x'".
    repeat rewrite raw_insert_successor.
    inversion Split as [|E' E1' E2'|E' E1' E2']...
Qed.

Lemma split_none_head : forall A (E : env A) E1 E2,
  context_split (None :: E) E1 E2 ->
  exists E1' E2', E1 = None :: E1' /\ E2 = None :: E2'.
Proof with eboom.
  intros A E E1 E2 Split.
  inversion Split; subst...
Qed.

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
    inversion Split...
  Case "x = S x'".
    rewrite raw_insert_successor in Split.
    destruct E1 as [|e1 E1']...
    replace (lookup (S x') (e1 :: E1')) with (lookup x' E1')...
    inversion Split; subst...
Qed.

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
      inversion Split; [ inversion SplitLeft | inversion SplitRight]; subst; eboom.
    SCase "E = e :: E'".
      destruct E2 as [|e2 E2s]; try solve by inversion.
      (* E2 is now e2 :: E2s *)
      simpl in Split.
      inversion Split; subst.
      (* TODO: Dedup *)
      SSCase "split left".
        apply IHE1s in SplitLeft.
        destruct SplitLeft as [E1' [E2' [? [? ?]]]].
        exists (e1 :: E1').
        exists (None :: E2').
        subst.
        eboom.
      SSCase "split right".
        apply IHE1s in SplitRight.
        destruct SplitRight as [E1' [E2' [? [? ?]]]].
        exists (None :: E1').
        exists (e2 :: E2').
        subst.
        eboom.
Qed.



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

Lemma insert_none_split_backwards : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  exists E1' E2',
    E1 = raw_insert x None E1' /\
    length E1' = length E /\
    E2 = raw_insert x None E2' /\
    length E2' = length E.
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
  (* This hideous junk is required to explicitly use firstn *)
  (*
    (* There are two main lengths involved, one long and one short *)
    set (lengthShort := length E).
    set (lengthLong := lengthShort + S (x - length E)).
    (* We take the first lengthShort elements of E1 as the base for the insert *)
    exists (firstn lengthShort E1).
    (* The length of the first part of the context split is long by definiton *)
    assert (length (E ++ repeat (S (x - length E)) None) = lengthLong) as LengthELong.
      rewrite app_length.
      rewrite repeat_length.
      solve [auto].
    (* We also know that the length of E1 is long, from the context split *)
    assert (length E1 = lengthLong) as LengthE1.
      subst lengthLong.
      rewrite <- LengthELong.
      solve [eboom].
    (* The proof about the length of firstn is easy *)
    assert (length (firstn lengthShort E1) = lengthShort) as LengthChop.
      rewrite firstn_length.
      rewrite LengthE1.
      subst lengthShort lengthLong.
      rewrite min_plus_r; solve [reflexivity].
    split; [ | solve [auto]].
    (* Now, the main proof *)
    rewrite insert_none_def.
    rewrite LengthChop.
    eapply split_app in Split.
    decompose record Split.
    exact H.
    auto. rewrite LengthChop. auto.
  *)
  Case "length E > x".
    generalize dependent E.
    generalize dependent E1.
    generalize dependent E2.
    induction x as [|x']; intros.
    SCase "x = 0".
      repeat rewrite raw_insert_zero in *.
      destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2']; try solve by inversion.
      inversion Split; subst;
        exists E1', E2';
        repeat rewrite raw_insert_zero;
        repeat split...
    SCase "x = S x'".
      destruct E as [|e E']; try solve by inversion.
      destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2']; try solve by inversion.
      rewrite raw_insert_successor in Split.
      simpl in Split.
      inversion Split; subst.
      (* TODO: dedup, should really use split on single elems *)
      SSCase "split left".
        apply IHx' in SplitLeft; simpl in *; try omega.
        destruct SplitLeft as [E1'' [E2'' [? [? [? ?]]]]].
        exists (e1 :: E1''), (None :: E2'').
        subst; simpl.
        repeat split...
      SSCase "split right".
        apply IHx' in SplitRight; simpl in *; try omega.
        destruct SplitRight as [E1'' [E2'' [? [? [? ?]]]]].
        exists (None :: E1''), (e2 :: E2'').
        subst; simpl.
        repeat split...
Qed.

(* Do we need these any more? *)
(*
Lemma insert_none_split_right : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E2', E2 = raw_insert x None E2' /\ length E2' = length E).
Proof.
  eauto using insert_none_split_left, split_commute.
Qed.

Lemma insert_none_split_strip_none : forall E E1 E2 x,
  length E = length E1 ->
  length E = length E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2) ->
  context_split E E1 E2.
Proof with eauto.
  intros E E1 E2 x Len1 Len2 Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero in *. inversion Split...
  Case "x = S x'".
    repeat rewrite raw_insert_successor in Split.
    inversion Split; subst.
    (* TODO: deduplicate this *)
    SCase "split_left".
      destruct E as [|e E'];
      destruct E1 as [|e1 E1'];
      destruct E2 as [|e2 E2']; try solve by inversion...
      (* Now we have only the cons cases *)
      simpl in *.
      replace e2 with (@None ty).
      replace e1 with e...
    SCase "split_right".
      destruct E as [|e E'];
      destruct E1 as [|e1 E1'];
      destruct E2 as [|e2 E2']; try solve by inversion...
      (* Now we have only the cons cases *)
      simpl in *.
      replace e1 with (@None ty).
      replace e2 with e...
Qed.

Lemma insert_none_split_backwards : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E1' E2', E1 = raw_insert x None E1' /\ E2 = raw_insert x None E2' /\ context_split E E1' E2').
Proof.
  intros E E1 E2 x H.
  assert (SplitL := H).
  assert (SplitR := H).
  apply insert_none_split_left in SplitL. destruct SplitL as [F1' [? ?]].
  apply insert_none_split_right in SplitR. destruct SplitR as [F2' [? ?]].
  exists F1'. exists F2'.
  split. eauto.
  split. eauto.
  subst. eauto using insert_none_split_strip_none.
Qed.
*)