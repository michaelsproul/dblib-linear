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
Require Import Subst.
Require Import SmallStepSemantics.
Import ListNotations.

Theorem preservation : forall E e e' s s' t,
  is_empty E ->
  E |- e ~: t ->
  step s e s' e' ->
  E |- e' ~: t.
Proof with eboom.
  intros E e e' s s' t EmptyE WT ST.
  generalize dependent E.
  generalize dependent t.
  induction ST.
  Case "Beta reduction".
    intros.
    inversion WT; subst.
    assert (is_empty E1 /\ is_empty E2) as [EmptyE1 EmptyE2]...
    inversion AppPreWT1; subst.
    (* Establish that the contexts are all the same length and apply substitution lemma *)
    set (len := length E).
    assert (length E1 = len)...
    assert (length E2 = len)...
    apply substitution with (E1 := E2) (t1 := t1) (E2 := E1)...
  Case "App1 stepping".
    intros.
    inversion WT; subst.
    assert (is_empty E1 /\ is_empty E2) as [EmptyE1 _]...
  Case "App2 stepping".
    intros.
    inversion WT; subst.
    assert (is_empty E1 /\ is_empty E2) as [_ EmptyE2]...
Qed.
