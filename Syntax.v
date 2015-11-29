Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import DbLib.DblibTactics.

Module Syntax.

(* We use natural numbers as De Bruijn indices to denote term and location variables. *)
Inductive name := Name : nat -> name.
(* No distinction between location variables and constants. *)
Inductive loc := Loc : nat -> loc.

(* Terms, or 'expressions' in L3 parlance. *)
Inductive term : Type :=
  (* () *)
  | TUnit
  (* let () = e1 in e2 *)
  (*
  | TLetUnit : term -> term -> term
  (* (x, y) *)
  | TPair : term -> term -> term
  (* let (x1, x2) = e1 in e2 *)
  | TLetPair : name -> name -> term -> term
  *)
  | TVar : name -> term
  | TAbs : term -> term
  | TApp : term -> term -> term
  (*
  (* FIXME: Need a value bound here? *)
  | TBang : term -> term
  (* let !x = e1 in e2 *)
  | TLetBang : name -> term -> term -> term
  | TDupl : term -> term
  | TDrop : term -> term
  | TPtr : loc -> term
  | TCap
  | TNew : term -> term
  | TFree : term -> term
  | TSwap : term -> term -> term -> term
  | TLocAbs : term -> term 
  | TLocApp : term -> loc -> term
  (* let |p, x| = e1 in e2 *)
  | TLetEx : loc -> name -> term -> term -> term
  *)
  | TTrue
  | TFalse
.

Inductive value : term -> Type :=
  | VUnit : value TUnit
  | VAbs : forall e, value (TAbs e)
  | VTrue : value TTrue
  | VFalse : value TFalse
.

Inductive ty : Type :=
  | TyUnit
  (*
  | TyProduct : ty -> ty -> ty
  *)
  | TyFunc : ty -> ty -> ty
  (*
  | TyBang : ty -> ty
  | TyPtr : loc -> ty
  | TyCap : loc -> ty -> ty
  | TyForAll : ty -> ty
  | TyEx : ty -> ty
  *)
  | TyBool
.

(* Substitution via DbLib *)
Instance Var_term : Var term := {
  var := fun i => TVar (Name i)
}.

(* Note: All terms stored in contexts are closed. *)
Definition store : Type :=
  loc -> option term.

(* Evaluation contexts *)
(* Options:
     + Write out lifting rules in the small step semantics.
     + Use a function ala Iron Lambda.
     + Use an inductive proposition `eval_ctxt term term`.
     + Normalise to let bindings (more reading required).
*)
(* eval_ctxt : term -> term *)
Inductive eval_ctxt : term -> term -> Prop :=
  | EId : forall e, eval_ctxt e e
  (*
  | ELetUnit : forall E e1 e2,
      eval_ctxt E e1 ->
      eval_ctxt (TLetUnit E e2) (TLetUnit e1 e2)
  | EPair : forall E e1 e2,
      eval_ctxt E e1 ->
      eval_ctxt (TPair E e2) (TPair e1 e2)
  *)
.

(* (sigma, e) -> (sigma', e') *)
Inductive step : store -> term -> store -> term -> Prop :=
  | StepAppAbs :
      value v ->
      
      step s () s' e'
.









End Syntax.