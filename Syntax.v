Require Import DbLib.DeBruijn.
Require Import DbLib.DblibTactics.
Require Export Linear.Basics.

Inductive ty : Set :=
  | TyUnit
  | TyPrim : String.string -> ty
  | TyFun : ty -> ty -> ty
.

Hint Constructors ty : linear.

(* Terms, or 'expressions' *)
Inductive term : Set :=
  | TUnit
  | TPrim : String.string -> term
  | TVar : nat -> term
  | TAbs : ty -> term -> term
  | TApp : term -> term -> term
.

Hint Constructors term : linear.

Inductive value : term -> Prop :=
  | VUnit : value TUnit
  | VPrim : forall s, value (TPrim s)
  | VVar : forall x, value (TVar x)
  | VAbs : forall t e, value (TAbs t e)
.

Hint Constructors value : linear.


(* Substitution via DbLib *)

Instance Var_term : Var term := {
  var := TVar
}.

(* Traverse the variable/value structure of a term.
   We also need a similar function for location traversal and substituion. *)
Fixpoint traverse_term (f : nat -> nat -> term) l t :=
  match t with
  | TVar x =>
      f l x
  | TAbs t e =>
      TAbs t (traverse_term f (1 + l) e)
  | TApp e1 e2 =>
      TApp (traverse_term f l e1) (traverse_term f l e2)
  | _ => t
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
