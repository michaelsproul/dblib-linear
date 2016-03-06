Require Import DbLib.Environments.

Require Import Syntax.
Require Import Util.
Require Import Environment.
Require Import List.
Require Import Empty.

(* Context splitting similar to Liam OConnor's approach *)
Inductive context_split {A} : env A -> env A -> env A -> Prop :=
  | split_nil : context_split nil nil nil
  | split_left E E1 E2 v
      (SplitLeft : context_split E E1 E2) :
      context_split (v :: E) (v :: E1) (None :: E2)
  | split_right E E1 E2 v
      (SplitRight : context_split E E1 E2) :
      context_split (v :: E) (None :: E1) (v :: E2).

Hint Constructors context_split : l3.

(* Basic lemmas about context splitting *)

Lemma split_commute : forall {A} (E : env A) E1 E2,
  context_split E E1 E2 -> context_split E E2 E1.
Proof with boom.
  intros A E E1 E2 Split.
  induction Split...
Qed.

Hint Resolve split_commute : l3.

(* In the proof of the lemma below, the proofs for the left and right cases are almost the same.
   The proofs differ only in the first elements of their new amalgamated contexts (E02).
   The first elements for each of the inversion cases are passed as the arguments v1 and v2. *)
Ltac split_rotate_crush v1 v2 E E0 :=
  inversion Split12 as [| ? E1' E2' | ? E1' E2'];
  subst;
  assert (exists ENew, context_split E E1' ENew /\ context_split ENew E0 E2') as [ENew [EN1 EN2]];
  boom;
  [exists (v1 :: ENew); eboom | exists (v2 :: ENew); eboom ].

(* Draw a tree! *)
Lemma split_rotate : forall {A} (E : env A) E0 E12 E1 E2,
  context_split E E0 E12 ->
  context_split E12 E1 E2 ->
  (exists E02, context_split E E1 E02 /\ context_split E02 E0 E2).
Proof with eboom.
  intros A E E0 E12 E1 E2 SplitE012 Split12.
  generalize dependent E1.
  generalize dependent E2.
  induction SplitE012 as [| E E0 E12 | E E0 E12]; intros.
  Case "empty". inversion Split12; subst...
  Case "left". split_rotate_crush v v E E0.
  Case "right". split_rotate_crush (@None A) v E E0.
Qed.

Lemma context_split_length1 : forall {A} (E : env A) E1 E2,
  context_split E E1 E2 ->
  length E = length E1.
Proof with boom.
  intros A E E1 E2 Split.
  induction Split; simpl...
Qed.

Lemma context_split_length1_x : forall {A} (E : env A) E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E1 = l.
Proof.
  intros.
  subst l.
  symmetry.
  eauto using context_split_length1.
Qed.

Hint Resolve context_split_length1_x.

(* ASIDE: Note how much more verbose the above proof is if it's done by hand. *)
Lemma context_split_length1_x_bad : forall {A} (E : env A) E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E1 = l.
Proof.
  intros A E E1 E2 l Split Len.
  generalize dependent l.
  induction Split;
  [ auto
  | intros;
    simpl in *;
    assert (length E = l - 1); [ omega | assert (length E1 = l - 1); eauto; omega ] ..].
Qed.

Example context_split_length2 : forall {A} (E : env A) E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E2 = l.
Proof. eboom. Qed.

Lemma split_all_left : forall {A} (E : env A) E1 E2,
  is_empty E2 ->
  context_split E E1 E2 ->
  E = E1.
Proof with eboom.
  intros A E E1 E2 Empty Split.
  induction Split; solve [ boom |
    inversion Empty; subst; eboom ].
Qed.

Hint Resolve split_all_left : l3.

Lemma split_all_right : forall {A} (E : env A) E1 E2,
  is_empty E1 ->
  context_split E E1 E2 ->
  E = E2.
Proof. eboom. Qed.

(* Possible idiocy *)
Lemma insert_zero_x : forall A o (E : env A) E1 E2,
  context_split E (raw_insert 0 o E1) E2 ->
  context_split E (o :: E1) E2.
Proof with boom.
  intros A P o E.
  rewrite raw_insert_zero...
Qed.

Hint Immediate insert_zero_x.

(* Examples *)

Example context_split_ex1 : exists E,
  context_split (insert 0 TyBool nil) (insert 0 TyBool nil) E /\
  is_empty E.
Proof with eboom.
  exists (None :: nil)...
  rewrite raw_insert_zero...
Qed.

(* Context splitting and emptyness *)

Lemma split_empty : forall {A} (E : env A) E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E1 /\ is_empty E2.
Proof.
  intros A E E1 E2 Empty Split.
  induction Split; solve [ boom |
    inversion Empty; subst; assert (is_empty E1 /\ is_empty E2) as [EmptyE1 EmptyE2]; eboom].
Qed.

Lemma split_empty_left : forall {A} (E : env A) E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E1.
Proof with eauto.
  intros A E E1 E2 Empty Split.
  apply split_empty in Split; destruct Split...
Qed.

Hint Resolve split_empty_left : l3.