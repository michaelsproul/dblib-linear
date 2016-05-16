Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import List.
Require Import Syntax.
Require Import Environment.
Require Import Context.
Require Import Empty.

Reserved Notation "E '|-' e '~:' t" (at level 40).

Inductive has_type : (env ty) -> term -> ty -> Prop :=
  | HasTyUnit E
      (UnitEmpty : is_empty E) :
      E |- TUnit ~: TyUnit
  | HasTyTrue E
      (TrueEmpty : is_empty E) :
      E |- TTrue ~: TyBool
  | HasTyFalse E
      (FalseEmpty : is_empty E) :
      E |- TFalse ~: TyBool
  | HasTyVar E x t
      (VarPre : is_empty E) :
      insert x t E |- TVar x ~: t
  | HasTyAbs E e t1 t2
      (AbsPre : (insert 0 t1 E) |- e ~: t2) :
      E |- TAbs t1 e ~: (TyFun t1 t2)
  | HasTyApp E E1 E2 e1 e2 t1 t2
      (AppPreSplit : context_split E E1 E2)
      (AppPreWT1 : E1 |- e1 ~: TyFun t1 t2)
      (AppPreWT2 : E2 |- e2 ~: t1) :
      E  |- TApp e1 e2 ~: t2
  | HasTyPair E E1 E2 e1 e2 t1 t2
      (PairPreSplit : context_split E E1 E2)
      (PairPreWT1 : E1 |- e1 ~: t1)
      (PairPreWT2 : E2 |- e2 ~: t2) :
      E |- TPair e1 e2 ~: (TyProduct t1 t2)

where "E '|-' e '~:' t" := (has_type E e t).

Hint Constructors has_type : l3.

(* Predicate for describing whether a variable is contained in a term. *)
Inductive contains_var : nat -> term -> Prop :=
  | ContainsVar n : contains_var n (TVar n)
  | ContainsAbs n e t (CVAbsPre : contains_var (S n) e)
      : contains_var n (TAbs t e)
  | ContainsApp1 n e1 e2 (CVApp1Pre : contains_var n e1)
      : contains_var n (TApp e1 e2)
  | ContainsApp2 n e1 e2 (CVApp2Pre : contains_var n e2)
      : contains_var n (TApp e1 e2)
  | ContainsPair1 n e1 e2 (CVPair1Pre : contains_var n e1)
      : contains_var n (TPair e1 e2)
  | ContainsPair2 n e1 e2 (CVPair2Pre : contains_var n e2)
      : contains_var n (TPair e1 e2)
.

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
