Require Import Typing.
Require Import Syntax.
Require Import SmallStepSemantics.
Require Import Empty.
Require Export Context.
Require Import Environment.

Lemma step_app1_x : forall e1 e2,
  (exists e', step e1 e') ->
  exists e'', step (TApp e1 e2) e''.
Proof with eboom.
  intros e1 e2 Step1.
  decompose record Step1...
Qed.

Hint Resolve step_app1_x : l3.

Lemma fun_value_is_abs : forall E e t1 t2,
  is_empty E ->
  E |- e ~: TyFun t1 t2 ->
  value e ->
  (exists e', e = TAbs t1 e').
Proof.
  intros E e t1 t2 Empty WT Val.
  destruct e; try (solve by inversion).
  Case "e is a variable, impossible with an empty context".
    inversion WT; subst; exfalso; eauto 2 with l3.
  Case "e is a lambda abstraction, good!".
    inversion WT; subst.
    eauto.
Qed.

Hint Resolve fun_value_is_abs : l3.

Lemma value_app1_x : forall E1 e1 e2 t1 t2,
  is_empty E1 ->
  E1 |- e1 ~: TyFun t1 t2 ->
  value e1 ->
  (exists e2', step e2 e2') \/ value e2 ->
  (exists e'', step (TApp e1 e2) e'').
Proof with eboom.
  intros E1 e1 e2 t1 t2 Empty1 WT1 Val1 [Step2 | Val2].
  Case "e2 steps".
    decompose record Step2...
  Case "e2 is also a value".
    (* Beta reduction *)
    assert (exists e1', e1 = TAbs t1 e1') as [e1']...
    subst e1...
Qed.

Hint Resolve value_app1_x : l3.

(* Proof of progress! *)
Theorem progress : forall E e t,
  is_empty E ->
  E |- e ~: t ->
  (exists e', step e e') \/ value e.
Proof with eboom.
  intros E e t EmptyE WT.
  induction WT...
  Case "Application".
    assert (is_empty E1 /\ is_empty E2) as [? ?]...
    destruct IHWT1...
Qed.
