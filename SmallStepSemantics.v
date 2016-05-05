Require Import Syntax.
Require Import DbLib.DeBruijn.

(* e ==> e' *)
Inductive step : term -> term -> Prop :=
  | StepAppAbs e e' v t
      (BetaPreVal : value v)
      (BetaPreSubst : subst v 0 e = e') :
      step (TApp (TAbs t e) v) e'
  | StepApp1 e1 e1' e2
      (App1Step : step e1 e1') :
      step (TApp e1 e2) (TApp e1' e2)
  | StepApp2 v1 e2 e2'
      (App2Val : value v1)
      (App2Step : step e2 e2') :
      step (TApp v1 e2) (TApp v1 e2').

Hint Constructors step : l3.
