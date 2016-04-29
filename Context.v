Require Import DbLib.Environments.

Require Import Syntax.
Require Import Util.
Require Import Environment.
Require Import List.
Require Import Empty.

(* Context splitting similar to Liam OConnor's approach *)
Inductive split_single {A} : option A -> option A -> option A -> Prop :=
  | split_none : split_single None None None
  | split_left (v : A) : split_single (Some v) (Some v) None
  | split_right (v : A) : split_single (Some v) None (Some v).

Hint Constructors split_single : l3.

Inductive context_split {A} : env A -> env A -> env A -> Prop :=
  | split_nil : context_split nil nil nil
  | split_cons E E1 E2 v v1 v2
      (SplitElem : split_single v v1 v2)
      (SplitPre : context_split E E1 E2) :
      context_split (v :: E) (v1 :: E1) (v2 :: E2).

Hint Constructors context_split : l3.

(* Basic lemmas about context splitting *)

Lemma split_single_commute : forall A (v : option A) v1 v2,
  split_single v v1 v2 -> split_single v v2 v1.
Proof with boom.
  intros A v v1 v2 Split.
  induction Split...
Qed.

Hint Immediate split_single_commute : l3.

Lemma split_commute : forall A (E : env A) E1 E2,
  context_split E E1 E2 -> context_split E E2 E1.
Proof with boom.
  intros A E E1 E2 Split.
  induction Split...
Qed.

(* NB: split_commute can create loops, so we only apply it at most once using auto *)
Hint Immediate split_commute : l3.

Lemma split_single_assoc : forall A (v v0 v1 v2 v12 : option A),
  split_single v v0 v12 ->
  split_single v12 v1 v2 ->
  (exists v01, split_single v v01 v2 /\ split_single v01 v0 v1).
Proof.
  intros A v v0 v1 v2 v12 Split Split12.
  destruct v; destruct v0; destruct v1; destruct v2; destruct v12;
  inversion Split12; inversion Split; eboom.
Qed.

Hint Resolve split_single_assoc : l3.

Lemma split_assoc : forall A (E E0 E1 E2 E12 : env A),
  context_split E E0 E12 ->
  context_split E12 E1 E2 ->
  (exists E01, context_split E E01 E2 /\ context_split E01 E0 E1).
Proof with eboom.
  intros A E E0 E1 E2 E12 SplitE Split12.
  generalize dependent E1.
  generalize dependent E2.
  induction SplitE as [|E' E0' E12' v v0 v12]; intros.
  Case "empty". inversion Split12; subst...
  Case "cons".
    inversion Split12 as [|? E1' E2' ? v1 v2 SplitSingle12 Split12'].
    subst.
    apply IHSplitE in Split12'.
    destruct Split12' as [E01' [? ?]].
    assert (exists v01, split_single v v01 v2 /\ split_single v01 v0 v1) as [v01 [? ?]]...
Qed.

Hint Resolve split_assoc : l3.

Lemma split_assoc_rev : forall A (E E0 E1 E2 E01 : env A),
  context_split E E01 E2 ->
  context_split E01 E0 E1 ->
  (exists E12, context_split E E0 E12 /\ context_split E12 E1 E2).
Proof with eboom.
  intros A E E0 E1 E2 E01 SplitE Split01.
  assert (exists E21, context_split E E21 E0 /\ context_split E21 E2 E1) as [E21 [? ?]]...
Qed.

Hint Resolve split_assoc_rev : l3.

(* Draw a tree! *)
Lemma split_rotate : forall A (E : env A) E0 E12 E1 E2,
  context_split E E0 E12 ->
  context_split E12 E1 E2 ->
  (exists E02, context_split E E1 E02 /\ context_split E02 E0 E2).
Proof with eboom.
  intros A E E0 E12 E1 E2 SplitE Split12.
  assert (exists E02, context_split E E02 E1 /\ context_split E02 E0 E2) as [? [? ?]]...
Qed.

Lemma split_swap : forall A (E E1 E2 E1a E1b E2a E2b : env A),
  context_split E E1 E2 ->
  context_split E1 E1a E1b ->
  context_split E2 E2a E2b ->
  (exists Ea Eb,
    context_split E Ea Eb /\
    context_split Ea E1a E2a /\
    context_split Eb E1b E2b).
Proof with eboom.
  intros A E E1 E2 E1a E1b E2a E2b SplitE Split1 Split2.
  assert (exists E12a, context_split E E12a E2b /\ context_split E12a E1 E2a) as [E12a [? ?]]...
  assert (exists Ea, context_split E12a E1b Ea /\ context_split Ea E1a E2a) as [Ea [? ?]]...
  assert (exists Eb, context_split E Ea Eb /\ context_split Eb E1b E2b) as [Eb [? ?]]...
Qed.

Lemma split_single_rotate : forall A (v : option A) v0 v12 v1 v2,
  split_single v v0 v12 ->
  split_single v12 v1 v2 ->
  (exists v02, split_single v v1 v02 /\ split_single v02 v0 v2).
Proof with eboom.
  intros A v v0 v12 v1 v2 Split012 Split12.
  destruct v; destruct v0; destruct v1; destruct v2; destruct v12;
  inversion Split012; inversion Split12; eboom.
Qed.

Hint Resolve split_single_rotate : l3.

Lemma context_split_length1 : forall A (E : env A) E1 E2,
  context_split E E1 E2 ->
  length E = length E1.
Proof with boom.
  intros A E E1 E2 Split.
  induction Split; simpl...
Qed.

Hint Resolve context_split_length1 : l3.

Lemma context_split_length1_x : forall A (E : env A) E1 E2 l,
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
Lemma context_split_length1_x_bad : forall A (E : env A) E1 E2 l,
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

Example context_split_length2 : forall A (E : env A) E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E2 = l.
Proof. eboom. Qed.

Lemma split_single_left : forall A (v : option A) v1,
  split_single v v1 None ->
  v = v1.
Proof with reflexivity.
  intros A v v1 Split.
  inversion Split; subst...
Qed.

Lemma split_single_right : forall A (v : option A) v1,
  split_single v None v1 ->
  v = v1.
Proof. eauto using split_single_commute, split_single_left. Qed.

Lemma split_all_left : forall A (E : env A) E1 E2,
  is_empty E2 ->
  context_split E E1 E2 ->
  E = E1.
Proof with (eauto using split_single_left, f_equal).
  intros A E E1 E2 Empty Split.
  induction Split...
  inversion Empty; subst.
  replace v1 with v...
Qed.

Hint Resolve split_all_left : l3.

Lemma split_all_right : forall A (E : env A) E1 E2,
  is_empty E1 ->
  context_split E E1 E2 ->
  E = E2.
Proof. eboom. Qed.

(* XXX: This lemma is possibly useless, it's just faking a rewrite *)
Lemma insert_zero_x : forall A o (E : env A) E1 E2,
  context_split E (raw_insert 0 o E1) E2 ->
  context_split E (o :: E1) E2.
Proof with boom.
  intros A P o E.
  rewrite raw_insert_zero...
Qed.

(* Context splitting and emptyness *)

Lemma split_empty : forall A (E : env A) E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E1 /\ is_empty E2.
Proof with eboom.
  intros A E E1 E2 Empty Split.
  induction Split...
  inversion Empty; subst.
  inversion SplitElem; subst.
  assert (is_empty E1 /\ is_empty E2) as [EmptyE1 EmptyE2]...
Qed.

Lemma split_empty_left : forall A (E : env A) E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E1.
Proof with eboom.
  intros A E E1 E2 Empty Split.
  apply split_empty in Split; destruct Split...
Qed.

Hint Immediate split_empty_left : l3.

Lemma split_empty_right : forall A (E : env A) E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E2.
Proof. eauto using split_empty_left, split_commute. Qed.

Hint Immediate split_empty_right : l3.

(* Examples *)
Example context_split_ex1 : exists E,
  context_split (insert 0 TyBool nil) (insert 0 TyBool nil) E /\
  is_empty E.
Proof with eboom.
  exists (None :: nil)...
  rewrite raw_insert_zero...
Qed.
