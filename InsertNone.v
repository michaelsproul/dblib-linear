(* Lemmas about inserting None into a typing context *)
Require Import DbLib.Environments.
Require Import Environments.
Require Import List.
Require Import Typing.
Require Import Syntax.
Require Import Empty.
Require Import Context.
Import ListNotations.

Transparent lookup.

Check (nil; nil |- TTrue ~: TyBool).

Fixpoint repeat {A} (n : nat) (e : A) : list A :=
  match n with
  | 0 => []
  | S n' => e :: repeat n' e
  end.

Lemma repeat_none_empty : forall A n,
  is_empty (repeat n None : env A).
Proof with (simpl; boom).
  intros.
  induction n...
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

(* The proof of this looks like it would be very involved *)
Lemma insert_none_split_left : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E1', E1 = raw_insert x None E1' /\ length E1' = length E).
Proof.
  admit.
Qed.
(*
  intros E E1 E2 x Split.
  exists (remove' x E1 (length E1 - length E - 1)).
  induction E1 as [|e1 E1'].
  Case "E1 = nil".
    inversion Split. exfalso; eauto using insert_nil.
  Case "E1 = e1 :: E1'".
    destruct x.
*)

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