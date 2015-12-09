Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import DbLib.DblibTactics.
Require Import Util.

(* We use natural numbers as De Bruijn indices to denote term and location variables. *)
Inductive name := Name : nat -> name.
(* No distinction between location variables and constants. *)
Inductive loc := Loc : nat -> loc.

Inductive ty : Type :=
  | TyUnit
  (*
  | TyProduct : ty -> ty -> ty
  *)
  | TyFun : ty -> ty -> ty
  (*
  | TyBang : ty -> ty
  | TyPtr : loc -> ty
  | TyCap : loc -> ty -> ty
  | TyForAll : ty -> ty
  | TyEx : ty -> ty
  *)
  | TyBool
.

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
  (* (\0: tau. e *)
  | TAbs : ty -> term -> term
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

Hint Constructors term.

Inductive value : term -> Prop :=
  | VUnit : value TUnit
  | VVar : forall x, value (TVar x)
  | VAbs : forall t e, value (TAbs t e)
  | VTrue : value TTrue
  | VFalse : value TFalse
.

Hint Constructors value.


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
  | TAbs t e =>
      TAbs t (traverse_term f (1 + l) e)
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
(* FIXME: Could use another environment here. *)
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
(* ^ NOT USED *)

(* (sigma, e) -> (sigma', e') *)
Inductive step : store -> term -> store -> term -> Prop :=
  | StepAppAbs : forall s e e' v t,
      value v ->
      subst v 0 e = e' ->
      step s (TApp (TAbs t e) v) s e'
  | StepApp1 : forall s s' e1 e1' e2,
      step s e1 s' e1' ->
      step s (TApp e1 e2) s' (TApp e1' e2)
  | StepApp2 : forall s s' v1 e2 e2',
      value v1 ->
      step s e2 s' e2' ->
      step s (TApp v1 e2) s' (TApp v1 e2')
.

Hint Constructors step.

(* Typing judgements *)
Definition loc_ctxt := env unit.
Definition ty_ctxt := env ty.

Reserved Notation "LC ';' VC '|-' t '~:' T" (at level 40).

(* TODO: Work out context splitting. Probably doesn't work well with partial maps... *)

(* Adapted from de Vries *)
Inductive context_split : ty_ctxt -> ty_ctxt -> ty_ctxt -> Prop :=
  | split_empty : context_split empty empty empty
  | split_left : forall E E1 E2 x t,
      lookup x E = None ->
      context_split E E1 E2 ->
      context_split (insert x t E) (insert x t E1) E2
  | split_right : forall E E1 E2 x t,
      lookup x E = None ->
      context_split E E1 E2 ->
      context_split (insert x t E) E1 (insert x t E2)
.

Hint Constructors context_split.

Lemma empty_context : forall E1 E2,
  context_split empty E1 E2 -> E1 = empty /\ E2 = empty.
Proof.
  intros E1 E2 H.
  admit.
  (*
  inversion H.
  (* Split empty *)
  auto.
  (* Split left *)
  unfold not in H0. apply extend_neq_empty in H0. inversion H0.
  admit.
  *)
Qed.

Lemma split_complete : forall E E1 E2 x t,
  context_split E E1 E2 ->
  lookup x E = Some t ->
  (lookup x E1 = Some t) \/ (lookup x E2 = Some t).
Proof.
  (*
  intros.
  induction H.
  (* Case split_empty *)
  inversion H0.
  (* Case split_left *)
  destruct (eq_nat_dec x x0).
    (* Equal *)
    subst x0.
    left.
    rewrite extend_eq in H0.
    inversion H0. subst t0.
    apply extend_eq.
    (* Not equal *)
    rewrite extend_neq in H0.
    rewrite extend_neq; auto. auto.
  (* Case split_right *)
  destruct (eq_nat_dec x x0).
    subst x0.
    right.
    rewrite extend_eq in H0.
    inversion H0. subst t0.
    apply extend_eq.
    (* Not equal *)
    rewrite extend_neq in H0.
    rewrite extend_neq; auto. auto.
  *)
  admit.
Qed.

Inductive has_type : loc_ctxt -> ty_ctxt -> term -> ty -> Prop :=
  | HasTyUnit : forall LC VC,
      LC; VC |- TUnit ~: TyUnit
  | HasTyTrue : forall LC VC,
      LC; VC |- TTrue ~: TyBool
  | HasTyFalse : forall LC VC,
      LC; VC |- TFalse ~: TyBool
  | HasTyVar : forall LC VC x t,
      lookup x VC = Some t ->
      LC; VC |- TVar x ~: t
  | HasTyAbs : forall LC VC e t1 t2,
      LC; (insert 0 t1 VC) |- e ~: t2 ->
      LC; VC |- TAbs t1 e ~: TyFun t1 t2
  | HasTyApp : forall LC E E1 E2 e1 e2 t1 t2,
      context_split E E1 E2 ->
      LC; E1 |- e1 ~: TyFun t1 t2 ->
      LC; E2 |- e2 ~: t1 ->
      LC; E  |- TApp e1 e2 ~: t2

where "LC ';' VC '|-' t '~:' T" := (has_type LC VC t T).

Hint Constructors has_type.



(* Time to prove progress *)
Theorem progress : forall L E e s t,
  (* Hacks to prevent empty from disappearing during induction *)
  L = empty ->
  E = empty ->
  L; E |- e ~: t ->
  (exists s' e', step s e s' e') \/ value e.
Proof with eauto.
  intros L E e s t Ln En H.
  induction H; auto.
  (* Application *)
  (* First, reasoning about the context splitting. We want E1 = E2 = empty. *)
  subst E. apply empty_context in H. destruct H as [E1empty E2empty].
  destruct IHhas_type1...
  (* e1 steps *)
  Case "e1 steps".
    (* Proof by StepApp1 (invert stepping of e1) *)
    inversion H. inversion H2... (* FIXME: tactic here *)
  Case "e1 is a value".
    destruct IHhas_type2 as [IH1 | IH2]...
    SCase "e2 steps".
      inversion IH1... inversion H2... (* Same tactic needed here *)
    SCase "e2 is a value".
      (* Here we use beta reduction, by first showing that e1 must be a lambda expression *)
      left.
      destruct e1; try (solve by inversion).
      (* Var case is impossible *)
      inversion H0; subst.
      apply lookup_empty_Some in H5. solve by inversion.
      (* Beta reduction! *)
      exists s.
      exists (subst e2 0 e1)...
Qed.

Lemma weakening: forall L E e t,
  L; E |- e ~: t ->
  forall x u E', insert x u E = E' ->
  L; E' |- (shift x e) ~: t.
Proof.
  admit.
Qed.

Lemma subst_preserves_typing : forall v x e e' t,
  subst v x e = e' ->
  empty; empty |- e ~: t ->
  empty; empty |- e' ~: t.
Proof.
Abort.

Lemma substitution: forall L E x e1 e2 t1 t2,
  L; (insert x t1 E) |- e2 ~: t2 ->
  L; E |- e1 ~: t1 ->
  L; E |- (subst e1 x e2) ~: t2.
Proof.
  intros L E x e1 e2 t1 t2 WT2 WT1.
  admit.
Qed.

(* Preservation *)
Theorem preservation : forall e e' s s' t,
  empty; empty |- e ~: t ->
  step s e s' e' ->
  empty; empty |- e' ~: t.
Proof with eauto.
  intros e e' s s' t WT ST.
  generalize dependent t.
  induction ST.
  Case "Beta reduction".
    intros.
    inversion WT; subst.
    apply empty_context in H3. destruct H3. subst. (* TACME *)
    inversion H6; subst.
    eauto using substitution.
  Case "App1 stepping".
    intros.
    inversion WT.
    apply empty_context in H1. destruct H1. subst. (* This is a tactic of sorts *)
    eauto.
  Case "App2 stepping".
    intros.
    inversion WT.
    apply empty_context in H2. destruct H2. subst. (* TACME *)
    eauto.
Qed.