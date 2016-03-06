Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import List.
Require Import Syntax.
Require Import Environment.
Require Import Context.
Require Import Empty.

Reserved Notation "L ';' E '|-' t '~:' T" (at level 40).

Inductive has_type : loc_ctxt -> ty_ctxt -> term -> ty -> Prop :=
  | HasTyUnit L E
      (UnitEmpty : is_empty E) :
      L; E |- TUnit ~: TyUnit
  | HasTyTrue L E
      (TrueEmpty : is_empty E) :
      L; E |- TTrue ~: TyBool
  | HasTyFalse L E
      (FalseEmpty : is_empty E) :
      L; E |- TFalse ~: TyBool
  | HasTyVar L E x t
      (VarPre : is_empty E) :
      L; insert x t E |- TVar x ~: t
  | HasTyAbs L E e t1 t2
      (AbsPre : L; (insert 0 t1 E) |- e ~: t2) :
      L; E |- TAbs t1 e ~: (TyFun t1 t2)
  | HasTyApp L E E1 E2 e1 e2 t1 t2
      (AppPreSplit : context_split E E1 E2)
      (AppPreWT1 : L; E1 |- e1 ~: TyFun t1 t2)
      (AppPreWT2 : L; E2 |- e2 ~: t1) :
      L; E  |- TApp e1 e2 ~: t2

where "L ';' E '|-' t '~:' T" := (has_type L E t T).

Hint Constructors has_type : l3.

(* Predicate for describing whether a variable is contained in a term. *)
Inductive contains_var : nat -> term -> Prop :=
  | ContainsVar n : contains_var n (TVar n)
  | ContainsAbs n e t (CVAbsPre : contains_var (S n) e)
      : contains_var n (TAbs t e)
  | ContainsApp1 n e1 e2 (CVApp1Pre : contains_var n e1)
      : contains_var n (TApp e1 e2)
  | ContainsApp2 n e1 e2 (CVApp2Pre : contains_var n e2)
      : contains_var n (TApp e1 e2).

Hint Constructors contains_var : l3.

Example contains_var_ex1 : contains_var 0 (TAbs TyBool (TVar 1)).
Proof. boom. Qed.

Lemma not_contains_Abs : forall x t e,
  ~ contains_var x (TAbs t e) ->
  ~ contains_var (S x) e.
Proof. boom. Qed.

Lemma not_contains_App1 : forall x e1 e2,
  ~ contains_var x (TApp e1 e2) ->
  ~ contains_var x e1.
Proof. boom. Qed.

Lemma not_contains_App2 : forall x e1 e2,
  ~ contains_var x (TApp e1 e2) ->
  ~ contains_var x e2.
Proof. boom. Qed.

Hint Resolve not_contains_Abs : l3.
Hint Resolve not_contains_App1 : l3.
Hint Resolve not_contains_App2 : l3.