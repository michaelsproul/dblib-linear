Require Import LLC.Syntax.
Require Import Linear.Context.

Reserved Notation "E '|-' e '~:' t" (at level 40).

Inductive has_type : (env ty) -> term -> ty -> Prop :=
  | HasTyUnit E
      (UnitPre : is_empty E) :
      E |- TUnit ~: TyUnit
  | HasTyPrim E s t
      (PrimPre : is_empty E) :
      E |- TPrim s ~: TyPrim t
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

where "E '|-' e '~:' t" := (has_type E e t).

Hint Constructors has_type : linear.

(* Predicate for describing whether a variable is contained in a term. *)
Inductive contains_var : nat -> term -> Prop :=
  | ContainsVar n : contains_var n (TVar n)
  | ContainsAbs n e t (CVAbsPre : contains_var (S n) e)
      : contains_var n (TAbs t e)
  | ContainsApp1 n e1 e2 (CVApp1Pre : contains_var n e1)
      : contains_var n (TApp e1 e2)
  | ContainsApp2 n e1 e2 (CVApp2Pre : contains_var n e2)
      : contains_var n (TApp e1 e2).

Hint Constructors contains_var : linear.

Example contains_var_ex1 : contains_var 0 (TAbs (TyPrim "bool") (TVar 1)).
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

Hint Resolve not_contains_Abs : linear.
Hint Resolve not_contains_App1 : linear.
Hint Resolve not_contains_App2 : linear.
