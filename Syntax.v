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

(* Typing judgements *)
Definition loc_ctxt := env unit.
Definition ty_ctxt := env ty.

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
Definition mask_t := list selector.

(* Apply a mask to create the left split *)
Fixpoint filter_left (E : ty_ctxt) mask : ty_ctxt :=
  match E, mask with
  | e :: E', Left :: mask' => e :: filter_left E' mask'
  | _ :: E', Right :: mask' => None :: filter_left E' mask'
  | _, _ => empty
  end.

Fixpoint filter_right (E : ty_ctxt) mask : ty_ctxt :=
  match E, mask with
  | _ :: E', Left :: mask' => None :: filter_right E' mask'
  | e :: E', Right :: mask' => e :: filter_right E' mask'
  | _, _ => empty
  end.

(*
Fixpoint do_context_split (E: ty_ctxt) mask : (ty_ctxt * ty_ctxt) :=
  match E, mask with
  | e :: E', sel :: mask' => (
    let (left, right) := do_context_split E' mask' in
    match sel with
    | Left => (e :: left, None :: right)
    | Right => (None :: left, e :: right)
    end)
  | _, _ => (empty, empty)
  end.
*)

Inductive context_split : ty_ctxt -> ty_ctxt -> ty_ctxt -> Prop :=
  | ContextSplit E E1 E2
      (ExMask : exists mask,
        filter_left E mask = E1 /\
        filter_right E mask = E2 /\
        length mask = length E) :
    context_split E E1 E2.

Hint Constructors context_split.

(* Predicate for contexts that states their emptyness (DbLib's definition is too limiting) *)
Inductive is_empty {A} : env A -> Prop :=
  | is_empty_nil : is_empty empty
  | is_empty_cons E (EmptyTail : is_empty E) : is_empty (None :: E).

Hint Constructors is_empty.

Example is_empty_test : is_empty (None :: None :: @empty ty).
Proof. auto. Qed.

Example split_test : exists E,
  context_split (insert 0 TyBool empty) (insert 0 TyBool empty) E /\
  is_empty E.
Proof with auto.
  exists (None :: empty).
  split...
  constructor.
  exists (Left :: nil)...
Qed.

(* ----------------------- *)
(* Lemma's about emptyness *)
(* ----------------------- *)

Lemma tail_empty_is_empty : forall {A} (E : env A),
  is_empty E ->
  is_empty (tl E).
Proof.
  intros A E Empty.
  destruct E; auto.
  inversion Empty; subst; auto.
Qed.

Hint Resolve tail_empty_is_empty.

Check lookup_empty_None.
Lemma lookup_empty_None' : forall {A} x (E : env A),
  is_empty E ->
  lookup x E = None.
Proof.
  intros A x E Empty.
  generalize dependent E.
  induction x as [|x'].
  Case "x = 0".
    intros. inversion Empty; auto.
  Case "x = S x'".
    intros.
    rewrite lookup_successor.
    eauto.
Qed.

Lemma lookup_empty_Some' : forall {A} x (E : env A) t,
  is_empty E ->
  lookup x E = Some t ->
  False.
Proof.
  intros A x E t Insert Lookup.
  rewrite lookup_empty_None' in Lookup.
  solve by inversion.
  assumption.
Qed.

Lemma insert_empty_contra : forall x (t : ty) E E',
  E = insert x t E' ->
  is_empty E -> False.
Proof with eauto.
  intros x t E E' Eq Empty.
  generalize dependent x.
  generalize dependent t.
  generalize dependent E'.
  induction E.
  Case "E = []". eauto using insert_nil.
  Case "E = a :: E".
    intros.
    destruct x as [|x'].
    SCase "x = 0".
      erewrite raw_insert_zero in Eq.
      solve by inversion 2.
    SCase "x = S x'".
      rewrite raw_insert_successor in Eq.
      inversion Eq; subst.
      inversion Empty...
Qed.

Lemma insert_empty_inversion : forall x1 x2 (t1 : ty) t2 E1 E2,
  is_empty E1 ->
  insert x1 t1 E1 = insert x2 t2 E2 ->
  x1 = x2 /\ t1 = t2 /\ is_empty E2.
Proof.
  intros x1 x2 t1 t2 E1 E2 Empty Insert.
  generalize dependent x2.
  generalize dependent E1.
  generalize dependent E2.
  induction x1 as [|x1'].
  Case "x1 = 0".
    intros.
    rewrite raw_insert_zero in Insert.
    destruct x2 as [|x2'].
    SCase "x2 = 0".
      rewrite raw_insert_zero in Insert.
      inversion Insert. subst. auto.
    SCase "x2 = S x2'".
      rewrite raw_insert_successor in Insert.
      inversion Insert. exfalso. eauto using insert_empty_contra.
  Case "x1 = S x1'".
    intros.
    rewrite raw_insert_successor in Insert.
    destruct x2 as [|x2'].
    SCase "x2 = 0".
      rewrite raw_insert_zero in Insert.
      inversion Insert. exfalso. eauto using lookup_empty_Some'.
    SCase "x2 = S x2'".
      rewrite raw_insert_successor in Insert.
      assert (x1' = x2' /\ t1 = t2 /\ is_empty (tl E2)) as [XEq [TEq E2Empty]].
        apply IHx1' with (E1 := tl E1). auto.
        inversion Insert; auto.
      inversion Insert as [[Lookup Insert']].
      rewrite lookup_empty_None' in Lookup.
      destruct E2 as [|e2 E2'].
      SSCase "E2 = nil". auto.
      SSCase "E2 = e2 :: E2'".
        split; auto.
        split; auto.
        assert (lookup 0 (e2 :: E2') = e2) as Lookup0. auto.
        rewrite Lookup0 in Lookup.
        simpl in E2Empty.
        subst.
        auto.
        auto.
Qed. (* Automation? *)

Lemma empty_context : forall E E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E1 /\ is_empty E2.
Proof with eauto.
  intros E E1 E2 Empty CSplit.
  generalize dependent E1.
  generalize dependent E2.
  induction E.
  Case "nil".
    intros.
    inversion CSplit. subst.
    destruct ExMask as [mask [SplitL [SplitR Len]]].
    subst...
  Case "a :: E".
    intros.
    inversion Empty. subst.
    inversion CSplit. subst.
    destruct ExMask as [mask [SplitL [SplitR Len]]].
    destruct mask as [| s mask']; try solve by inversion.
    destruct s; simpl in SplitL; simpl in SplitR.
    (* FIXME: Deduplicate this. *)
    SCase "Left".
      destruct E1 as [| x E1']; try solve by inversion.
      destruct E2 as [| y E2']; try solve by inversion.
      inversion SplitL.
      inversion SplitR.
      assert (is_empty E1' /\ is_empty E2') as [EmptyE1 EmptyE2].
      SSCase "Proof of assertion".
        apply IHE.
          auto.
        constructor.
        exists (mask').
        auto.
      subst.
      split; constructor; eauto.
    (* FIXME : copy paste *)
    SCase "Right".
      destruct E1 as [| x E1']; try solve by inversion.
      destruct E2 as [| y E2']; try solve by inversion.
      inversion SplitL.
      inversion SplitR.
      assert (is_empty E1' /\ is_empty E2') as [EmptyE1 EmptyE2].
      SSCase "Proof of assertion".
        apply IHE.
          auto.
        constructor.
        exists (mask').
        auto.
      subst.
      split; constructor; eauto.
Qed.

Lemma zero_length_empty : forall (E : ty_ctxt), length E = 0 -> E = empty.
Proof.
  intros E Len.
  unfold empty.
  destruct E; [auto | solve by inversion].
Qed.

(* ----------------------- *)
(* Lemma's about splitting *)
(* ----------------------- *)

(*
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
*)

Lemma split_complete_E1 : forall E E1 E2 x t,
  context_split E E1 E2 ->
  lookup x E1 = Some t ->
  lookup x E = Some t.
Abort.

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

(* TYPING JUDGEMENT *)
Reserved Notation "L ';' E '|-' t '~:' T" (at level 40).

Inductive has_type : loc_ctxt -> ty_ctxt -> term -> ty -> Prop :=
  | HasTyUnit L E :
      L; E |- TUnit ~: TyUnit
  | HasTyTrue L E :
      L; E |- TTrue ~: TyBool
  | HasTyFalse L E :
      L; E |- TFalse ~: TyBool
  | HasTyVar L E x t
      (VarPre : is_empty E) :
      L; insert x t E |- TVar x ~: t
  | HasTyAbs L E e t1 t2
      (AbsPre : L; (insert 0 t1 E) |- e ~: t2) :
      L; E |- TAbs t1 e ~: TyFun t1 t2
  | HasTyApp L E E1 E2 e1 e2 t1 t2
      (AppPreSplit : context_split E E1 E2)
      (AppPreWT1 : L; E1 |- e1 ~: TyFun t1 t2)
      (AppPreWT2 : L; E2 |- e2 ~: t1) :
      L; E  |- TApp e1 e2 ~: t2

where "L ';' E '|-' t '~:' T" := (has_type L E t T).

Hint Constructors has_type.

(* Time to prove progress *)
Theorem progress : forall L E e s t,
  is_empty L ->
  is_empty E ->
  L; E |- e ~: t ->
  (exists s' e', step s e s' e') \/ value e.
Proof with eauto.
  intros L E e s t EmptyL EmptyE WT.
  induction WT; auto.
  Case "Application".
  (* First, reasoning about the context splitting. We want E1 and E2 empty. *)
  assert (is_empty E1 /\ is_empty E2) as [EmptyE1 EmptyE2].
    eauto using empty_context.
  destruct IHWT1 as [Step_e1 | Value_e1]...
  (* e1 steps *)
  SCase "e1 steps".
    (* Proof by StepApp1 (invert stepping of e1) *)
    inversion Step_e1. inversion H... (* FIXME: naming here *)
  SCase "e1 is a value".
    destruct IHWT2 as [Step_e2 | Value_e2]...
    SSCase "e2 steps".
      inversion Step_e2... inversion H... (* FIXME: same naming fix needed here *)
    SSCase "e2 is a value".
      (* Here we use beta reduction, by first showing that e1 must be a lambda expression *)
      left.
      destruct e1; try (solve by inversion).
      SSSCase "e1 is a TVar".
        (* Var case is impossible *)
        inversion WT1; subst.
        exfalso. eauto using insert_empty_contra.
      (* Beta reduction! *)
      exists s.
      exists (subst e2 0 e1)...
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
    (* FIXME: naming? *)
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
