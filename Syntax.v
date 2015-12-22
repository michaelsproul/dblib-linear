Require Import Coq.Lists.List.
Require Export Coq.Program.Equality.
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

(* Liam OConnor's approach... seems to require vector environments *)
(*
Inductive split_single : option ty -> option ty -> option ty -> Prop :=
  | split_left : forall v, split_single v v None
  | split_right : forall v, split_single v None v.

Inductive context_split : ty_ctxt -> ty_ctxt -> ty_ctxt -> Prop :=
  | split_empty : context_split empty empty empty
  | split_cons : forall E E1 E2 v v1 v2,
      split_single v v1 v2 ->
      context_split E E1 E2 ->
      context_split (v :: E) (v1 :: E1) (v2 :: E2).
*)

(* Computational definition of context splitting. *)
Inductive selector := Left | Right.
Definition mask := list selector.

Fixpoint do_context_split (E: ty_ctxt) mask : (ty_ctxt * ty_ctxt) :=
  match E with
  | nil => (empty, empty)
  | cons h t => (
    match mask with
    | nil => (empty, empty)
    | cons sel mask' => (
      let (left, right) := do_context_split t mask' in
      match sel with
      | Left => (cons h left, right)
      | Right => (left, cons h right)
      end)
    end)
  end.

Inductive context_split : ty_ctxt -> ty_ctxt -> ty_ctxt -> Prop :=
  | ContextSplit : forall E E1 E2,
    (exists sl, do_context_split E sl = (E1, E2) /\ length sl = length E) ->
    context_split E E1 E2.

Hint Constructors context_split.

Example split_test : context_split (insert 0 TyBool empty) (insert 0 TyBool empty) empty.
Proof.
  constructor.
  exists (cons Left nil).
  auto.
Qed.

Lemma empty_context : forall E1 E2,
  context_split empty E1 E2 -> E1 = empty /\ E2 = empty.
Proof with eauto.
  intros E1 E2 CSplit.
  inversion CSplit; subst.
  destruct H as [sl [Split Len]].
  simpl in Split.
  inversion Split...
Qed.

Lemma zero_length_empty : forall (E : ty_ctxt), length E = 0 -> E = empty.
Proof.
  intros E Len.
  unfold empty.
  destruct E; [auto | solve by inversion].
Qed.

Lemma split_complete_forward : forall E E1 E2 x t,
  context_split E E1 E2 ->
  lookup x E = Some t ->
  (lookup x E1 = Some t) \/ (lookup x E2 = Some t).
Proof.
  intros E E1 E2 x t CSplit Lookup.
  inversion CSplit; subst.
  destruct H as [sl [Split Len]].
  induction sl as [ | s sl'].
  Case "nil - impossible".
    assert (E = empty).
      auto using zero_length_empty.
    subst.
    exfalso; eauto using lookup_empty_Some.
  Case "s :: sl'".
    simpl in Split.
    destruct E as [ | t0 E'].
      solve by inversion.
    simpl in Split.
    destruct s.
    SCase "Left".
      admit.
    SCase "Right".
      admit.
Abort.

Lemma split_complete_E1 : forall E E1 E2 x t,
  context_split E E1 E2 ->
  lookup x E1 = Some t ->
  lookup x E = Some t.
Abort.

(* This is probably true *)
Lemma split_complete_E2 : forall E E1 E2 x t,
  context_split E E1 E2 ->
  lookup x E2 = Some t ->
  lookup x E = Some t.
Abort.

Lemma split_single_left : forall E E1,
  context_split E E1 empty ->
  E = E1.
Abort.

Lemma split_single_right : forall E E2,
  context_split E empty E2 ->
  E = E2.
Abort.

Inductive has_type : loc_ctxt -> ty_ctxt -> term -> ty -> Prop :=
  | HasTyUnit : forall LC VC,
      LC; VC |- TUnit ~: TyUnit
  | HasTyTrue : forall LC VC,
      LC; VC |- TTrue ~: TyBool
  | HasTyFalse : forall LC VC,
      LC; VC |- TFalse ~: TyBool
  | HasTyVar : forall LC x t,
      LC; insert x t empty |- TVar x ~: t
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
      apply insert_nil in H3. solve by inversion.
      (* Beta reduction! *)
      exists s.
      exists (subst e2 0 e1)...
Qed.

Example test:
  empty; insert 0 (TyFun TyUnit TyBool) empty |-
    (subst TUnit 1 (TApp (TVar 0) (TVar 1))) ~: TyBool.
Proof with auto.
  simpl_subst_goal.
  apply HasTyApp with (E1 := (insert 0 (TyFun TyUnit TyBool) empty)) (E2 := empty) (t1 := TyUnit)...
  constructor.
  exists (Left :: nil).
  rewrite raw_insert_zero.
  auto.
Qed.

Lemma insert_empty : forall x1 x2 (t1 : ty) t2 E,
  insert x1 t1 empty = insert x2 t2 E ->
  x1 = x2 /\ t1 = t2 /\ E = empty.
Proof.
  intros.
  assert (lookup x2 (insert x1 t1 empty) = lookup x2 (insert x2 t2 E)).
  auto using f_equal.
  destruct (lt_eq_lt_dec x1 x2). destruct s.
  Case "x1 < x2".
    lookup_insert_all. rewrite lookup_insert_bingo in H0.
    assert False. eauto using lookup_empty_Some. solve by inversion. auto.
  Case "x1 = x2".
    lookup_insert_all. rewrite lookup_insert_bingo in H0.
    inversion H0. split; auto. split; auto.
    (* TODO: Look up some other key *)
    admit. auto.
  Case "x2 < x1".
    lookup_insert_all. rewrite lookup_insert_bingo in H0.
    assert False. eauto using lookup_empty_Some. solve by inversion. auto.
Qed.

(* Works up to here *)

Lemma substitution: forall L E2 e2 t1 t2 x,
  L; insert x t1 E2 |- e2 ~: t2 ->
  forall E E1 e1, L; E1 |- e1 ~: t1 ->
  context_split E E1 E2 ->
  L; E |- (subst e1 x e2) ~: t2.
Proof.
  intros L E2 e2 t1 t2 x WT2 E E1 e1 WT1 Split.
  dependent induction WT2; simpl_subst_goal; eauto.
  Case "Var".
    (* WTF hypothesis naming... *)
    apply insert_empty in x. destruct x as [XEq [TEq E2Eq]].
    subst. simpl_subst_goal.
    apply split_single_left in Split. subst; auto.
  Case "Abs".
    constructor.
    (* XXX: Bug in error reporting - can't specify E0 *)
    eapply IHWT2 with (t3 := t1) (E1 := E1).
    insert_insert.
    admit. (* Require closed terms for substitution? *)
    auto using split_right.
  Case "App".
    admit.
Qed.

Lemma substitution_old: forall L E x (*e1*) e2 t1 t2,
  L; (insert x t1 E) |- e2 ~: t2 ->
  forall e1, L; E |- e1 ~: t1 ->
  L; E |- (subst e1 x e2) ~: t2.
Proof.
  intros L E x e2 t1 t2 WT2.
  (* We seem to require dependent induction here to avoid getting useless contexts *)
  dependent induction WT2; intros e1' WT1; simpl_subst_goal; eauto.
  Case "TVar".
    unfold subst_idx.
    dblib_by_cases; lookup_insert_all; auto.
  Case "TAbs".
    constructor.
    apply IHWT2 with (t3 := t1).
      insert_insert.

      auto.
      apply blah.
  Case "TApp".

(* Alternative induction *)
(* de
  intros L E x e2. (* t1 t2 WT2 e1 WT1. *)
  induction e2; simpl_subst_goal. intros t1 t2 WT1 e1 WT2; inversion WT2; eauto; subst.
  Case "TVar".
    unfold subst_idx.
    dblib_by_cases; lookup_insert_all; auto.
  Case "TAbs".
    constructor.

  simpl_subst_goal.
  inversion WT2. auto.
*)
(*

    intros.
    apply HasTyAbs.
    assert (closed 0 e1) as E1Closed. admit.
    rewrite E1Closed.
    Check lift_subst_2.
    apply weakening.

    unfold closed in H. subst.
    assert (empty; insert 0 t0 empty |- subst (shift 0 e1) (1 + x) (shift 0 e) ~: t2).
    Check closed.
    Check lift_subst_1.

    assert (empty; insert 0 t0 empty |- subst (lift 1 0 e) (1 + x) (lift 1 0 e) ~: t2).
    rewrite <- lift_subst_1.
    apply weakening with (E := empty) (u := t0).
    eauto with insert_insert.
    admit.
    reflexivity.
    SearchPattern (0 <= _).
    auto using le_0_n.
    (* FIXME: This appears to require e to be closed (shift 0 e) = e *)
    admit.
  Case "TApp".
    intros.
    apply HasTyApp with (E1 := E1) (E2 := E2) (t1 := t1).
    admit. admit. admit.
Qed.
*)
Abort.

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
