Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import DbLib.DblibTactics.
Require Import PartialMap.

Module Syntax.

(* We use natural numbers as De Bruijn indices to denote term and location variables. *)
Inductive name := Name : nat -> name.
(* No distinction between location variables and constants. *)
Inductive loc := Loc : nat -> loc.

(* Terms, or 'expressions' in L3 parlance. *)
Inductive term : Type :=
  (* () *)
  | TUnit
  | TTrue
  | TFalse
  (* let () = e1 in e2 *)
  (*
  | TLetUnit : term -> term -> term
  (* (x, y) *)
  | TPair : term -> term -> term
  (* let (x1, x2) = e1 in e2 *)
  | TLetPair : name -> name -> term -> term
  *)
  (* FIXME: Would be nice to use name type, but prove_*_traverse tactics choke. *)
  | TVar : nat -> term
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

(* ---------------------- *)
(* Substitution via DbLib *)
(* ~~~~~~~~~~~~~~~~~~~~~~ *)

Instance Var_term : Var term := {
  var := TVar
}.

(* Traverse the variable/value structure of a term.
   We also need a similar function for location traversal and substituion. *)
Fixpoint traverse_term (f : nat -> nat -> term) l t :=
  match t with
  | TUnit => TUnit
  | TTrue => TTrue
  | TFalse => TFalse
  | TVar x =>
      f l x
  | TAbs e =>
      TAbs (traverse_term f (1 + l) e)
  | TApp e1 e2 =>
      TApp (traverse_term f l e1) (traverse_term f l e2)
  end.

Instance Traverse_term : Traverse term term := {
  traverse := traverse_term
}.

Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_term : @TraverseRelative term term _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* END DbLib definitions *)

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
  | StepAppAbs : forall s e e' v,
      value v ->
      subst v 0 e = e' ->
      step s (TApp (TAbs e) v) s e'
  | StepApp1 : forall s s' e1 e1' e2,
      step s e1 s' e1' ->
      step s (TApp e1 e2) s' (TApp e1' e2)
  | StepApp2 : forall s s' v1 e2 e2',
      value v1 ->
      step s e2 s' e2' ->
      step s (TApp v1 e2) s' (TApp v1 e2')
.









End Syntax.
