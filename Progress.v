Require Import Typing.
Require Import Syntax.
Require Import SmallStepSemantics.
Require Import Empty.
Require Export Context.
Require Import Environment.

Lemma step_app1_x : forall s e1 e2,
  (exists s' e', step s e1 s' e') ->
  exists s' e'', step s (TApp e1 e2) s' e''.
Proof with eboom.
  intros s e1 e2 Step1.
  decompose record Step1...
Qed.

Hint Resolve step_app1_x : l3.

Lemma fun_value_is_abs : forall L E e t1 t2,
  is_empty E ->
  L; E |- e ~: TyFun t1 t2 ->
  value e ->
  (exists e', e = TAbs t1 e').
Proof.
  intros L E e t1 t2 Empty WT Val.
  destruct e; try (solve by inversion).
  Case "e is a variable, impossible with an empty context".
    inversion WT; subst; exfalso; eauto 2 with l3.
  Case "e is a lambda abstraction, good!".
    inversion WT; subst.
    eauto.
Qed.

Hint Resolve fun_value_is_abs : l3.

Lemma value_app1_x : forall L E1 s e1 e2 t1 t2,
  is_empty E1 ->
  L; E1 |- e1 ~: TyFun t1 t2 ->
  value e1 ->
  (exists s' e2', step s e2 s' e2') \/ value e2 ->
  (exists s' e'', step s (TApp e1 e2) s' e'').
Proof with eboom.
  intros L E1 s e1 e2 t1 t2 Empty1 WT1 Val1 [Step2 | Val2].
  Case "e2 steps".
    decompose record Step2...
  Case "e2 is also a value".
    (* Beta reduction *)
    assert (exists e1', e1 = TAbs t1 e1') as [e1']...
    subst e1...
Qed.

Hint Resolve value_app1_x : l3.

(* Proof of progress! *)
Theorem progress : forall L E e s t,
  is_empty L ->
  is_empty E ->
  L; E |- e ~: t ->
  (exists s' e', step s e s' e') \/ value e.
Proof with eboom.
  intros L E e s t EmptyL EmptyE WT.
  induction WT...
  Case "Application".
    assert (is_empty E1 /\ is_empty E2) as [? ?]...
    destruct IHWT1...
Qed.