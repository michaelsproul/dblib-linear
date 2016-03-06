Require Import Syntax.
Require Import DbLib.DeBruijn.

(* (sigma, e) -> (sigma', e') *)
Inductive step : store -> term -> store -> term -> Prop :=
  | StepAppAbs s e e' v t
      (BetaPreVal : value v)
      (BetaPreSubst : subst v 0 e = e') :
      step s (TApp (TAbs t e) v) s e'
  | StepApp1 s s' e1 e1' e2
      (App1Step : step s e1 s' e1') :
      step s (TApp e1 e2) s' (TApp e1' e2)
  | StepApp2 s s' v1 e2 e2'
      (App2Val : value v1)
      (App2Step : step s e2 s' e2') :
      step s (TApp v1 e2) s' (TApp v1 e2')
.

Hint Constructors step.