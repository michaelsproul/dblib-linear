Require Import Progress.
Require Import Preservation.

Inductive multi_step : term -> term -> Prop :=
  | multi_step_refl e : multi_step e e
  | multi_step_trans e e' e''
      (SingleStep : step e e')
      (MultiStep : multi_step e' e'') :
      multi_step e e''.

Hint Constructors multi_step : linear.

Corollary soundness : forall E e e' t,
  is_empty E ->
  E |- e ~: t ->
  multi_step e e' ->
  (exists e'', step e' e'') \/ value e'.
Proof with eboom.
  intros E e e' t Empty WT Steps.
  induction Steps.
  Case "zero steps".
    eapply progress...
  Case "one or more steps".
    apply IHSteps.
    eapply preservation...
Qed.
