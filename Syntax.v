Require Import Coq.Lists.List.
Require Export Coq.Program.Equality.
Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import DbLib.DblibTactics.
Require Import Util.

(* TODO: Make list notations play nicely with typing notation *)
(*
Import ListNotations.
Open Scope list_scope.
*)

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

(* Context splitting similar to Liam OConnor's approach *)
Inductive context_split : ty_ctxt -> ty_ctxt -> ty_ctxt -> Prop :=
  | split_empty : context_split empty empty empty
  | split_left E E1 E2 v
      (SplitLeft : context_split E E1 E2) :
      context_split (v :: E) (v :: E1) (None :: E2)
  | split_right E E1 E2 v
      (SplitRight : context_split E E1 E2) :
      context_split (v :: E) (None :: E1) (v :: E2).

Hint Constructors context_split.

(* Predicate for contexts that states their emptyness (DbLib's definition is too limiting) *)
Inductive is_empty {A} : env A -> Prop :=
  | is_empty_nil : is_empty empty
  | is_empty_cons E (EmptyTail : is_empty E) : is_empty (None :: E).

Hint Constructors is_empty.

Example is_empty_ex1 : is_empty (None :: None :: @empty ty).
Proof. auto. Qed.

Example context_split_ex1 : exists E,
  context_split (insert 0 TyBool empty) (insert 0 TyBool empty) E /\
  is_empty E.
Proof with auto.
  exists (None :: empty).
  split...
  rewrite raw_insert_zero...
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
Qed. (* TODO: Automation? *)

Lemma empty_context : forall E E1 E2,
  is_empty E ->
  context_split E E1 E2 ->
  is_empty E1 /\ is_empty E2.
Proof with eauto.
  intros E E1 E2 Empty Split.
  induction Split; solve [ auto |
    inversion Empty; subst; assert (is_empty E1 /\ is_empty E2) as [EmptyE1 EmptyE2]; eauto].
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

Lemma split_commute : forall E E1 E2,
  context_split E E1 E2 -> context_split E E2 E1.
Proof with auto.
  intros E E1 E2 Split.
  induction Split...
Qed.

(* In the proof of the lemma below, the proofs for the left and right cases are almost the same.
   The proofs differ only in the first elements of their new amalgamated contexts (E02).
   The first elements for each of the inversion cases are passed as the arguments v1 and v2. *)
Ltac split_rotate_crush v1 v2 E E0 :=
  inversion Split12 as [| ? E1' E2' | ? E1' E2'];
  subst;
  assert (exists ENew, context_split E E1' ENew /\ context_split ENew E0 E2') as [ENew [EN1 EN2]];
  auto;
  [exists (v1 :: ENew); eauto | exists (v2 :: ENew); eauto ].

(* Draw a tree! *)
Lemma split_rotate : forall E E0 E12 E1 E2,
  context_split E E0 E12 ->
  context_split E12 E1 E2 ->
  (exists E02, context_split E E1 E02 /\ context_split E02 E0 E2).
Proof.
  intros E E0 E12 E1 E2 SplitE012 Split12.
  generalize dependent E1.
  generalize dependent E2.
  induction SplitE012 as [| E E0 E12 | E E0 E12]; intros.
  Case "empty". inversion Split12; subst; eauto.
  Case "left". split_rotate_crush v v E E0.
  Case "right". split_rotate_crush (None : option ty) v E E0.
Qed.

Lemma context_split_length1_imp : forall E E1 E2,
  context_split E E1 E2 ->
  length E = length E1.
Proof.
  intros E E1 E2 Split.
  induction Split; simpl; eauto.
Qed.

Lemma context_split_length1 : forall E E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E1 = l.
Proof.
  intros.
  subst l.
  symmetry.
  eauto using context_split_length1_imp.
Qed.

(* Note how much more verbose the proof is if it's done by hand. *)
Lemma context_split_length1_v : forall E E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E1 = l.
Proof.
  intros E E1 E2 l Split Len.
  generalize dependent l.
  induction Split;
  [ auto
  | intros;
    simpl in *;
    assert (length E = l - 1); [ omega | assert (length E1 = l - 1); eauto; omega ] ..].
Qed.

Lemma context_split_length2 : forall E E1 E2 l,
  context_split E E1 E2 ->
  length E = l ->
  length E2 = l.
Proof.
  eauto using context_split_length1, split_commute.
Qed.

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

Lemma split_single_left : forall E E1 E2,
  is_empty E2 ->
  context_split E E1 E2 ->
  E = E1.
Proof.
  intros E E1 E2 Empty Split.
  induction Split; solve [ auto |
    inversion Empty; subst; eauto using f_equal].
Qed.

Lemma split_single_right : forall E E1 E2,
  is_empty E1 ->
  context_split E E1 E2 ->
  E = E2.
Proof.
  eauto using split_commute, split_single_left.
Qed.

(* TYPING JUDGEMENT *)
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

Hint Constructors has_type.

(* Predicate for describing whether a variable is contained in a term. *)
Inductive contains_var : nat -> term -> Prop :=
  | ContainsVar n : contains_var n (TVar n)
  | ContainsAbs n e t (CVAbsPre : contains_var (S n) e)
      : contains_var n (TAbs t e)
  | ContainsApp1 n e1 e2 (CVApp1Pre : contains_var n e1)
      : contains_var n (TApp e1 e2)
  | ContainsApp2 n e1 e2 (CVApp2Pre : contains_var n e2)
      : contains_var n (TApp e1 e2).

Hint Constructors contains_var.

Example contains_var_ex1 : contains_var 0 (TAbs TyBool (TVar 1)).
Proof. auto. Qed.

Lemma not_contains_Abs : forall x t e,
  ~ contains_var x (TAbs t e) ->
  ~ contains_var (S x) e.
Proof. auto. Qed.

Lemma not_contains_App1 : forall x e1 e2,
  ~ contains_var x (TApp e1 e2) ->
  ~ contains_var x e1.
Proof. auto. Qed.

Lemma not_contains_App2 : forall x e1 e2,
  ~ contains_var x (TApp e1 e2) ->
  ~ contains_var x e2.
Proof. auto. Qed.

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

(* -------------------------- *)
(* Substitution helper lemmas *)
(* -------------------------- *)

Lemma insert_none_is_empty : forall {A} (E : env A) E' x,
  is_empty E ->
  raw_insert x None E = E' ->
  is_empty E'.
Proof with eauto using (lookup_empty_None').
  intros A E E' x EmptyE Ins.
  generalize dependent E.
  generalize dependent E'.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Ins.
    subst...
  Case "x = S x'".
    rewrite raw_insert_successor in Ins.
    assert (lookup 0 E = None) as R... rewrite R in Ins.
    subst E'.
    constructor.
    apply IHx' with (E := tl E)...
Qed.

Lemma lookup_zero : forall {A} e (E : env A),
  lookup 0 (e :: E) = e.
Proof.
  Transparent lookup.
  eauto.
  Opaque lookup.
Qed.

Hint Resolve lookup_zero.

Lemma insert_none_is_empty_inversion : forall {A} (E : env A) x,
  is_empty (raw_insert x None E) -> is_empty E.
Proof with eauto.
  intros A E x Empty.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Empty. inversion Empty...
  Case "x = S x'".
    rewrite raw_insert_successor in Empty.
    inversion Empty; subst.
    destruct E as [|e E']...
    SCase "E = e :: E'".
      replace e with (@None A)...
Qed.

Lemma insert_none_split : forall E E1 E2 x,
  context_split E E1 E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2).
Proof with eauto.
  intros E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero...
  Case "x = S x'".
    repeat rewrite raw_insert_successor.
    inversion Split as [|E' E1' E2'|E' E1' E2']...
Qed.

Lemma split_none_head : forall E E1 E2,
  context_split (None :: E) E1 E2 ->
  exists E1' E2', E1 = None :: E1' /\ E2 = None :: E2'.
Proof.
  intros E E1 E2 Split.
  inversion Split; subst; eauto.
Qed.

Fixpoint remove {A} (x : nat) (E : env A) : env A :=
  match x, E with
  | _, nil => nil
  | 0, h :: t => t
  | (S x'), h :: t => h :: remove x' t
  end.

Fixpoint remove_fancy {A} (x : nat) (E : env A) (chomp_limit : nat) (nones : env A) : env A :=
  match x, E, chomp_limit, nones with
  | _, nil, _, _ => nil
  (* If we've reached our element, and there are no more following it, drop the nones preceding it *)
  | 0, h :: nil, _, nones => nil
  (* Otherwise, if we've reached our element and there are things after it, re-insert the nones *)
  | 0, h :: tail, _, nones => nones ++ tail
  (* If we find an intermediate element, clear the nones list and proceed with the recursion *)
  | (S x'), (Some t) :: tail, _, _ => (Some t) :: remove_fancy x' tail chomp_limit nil
  (* If we find an intermediate element and the chomp_limit is exhausted we have to leave the None in there *)
  | (S x'), None :: tail, 0, nones => None :: remove_fancy x' tail 0 nones
  (* Otherwise if the chomp_limit isn't exhausted we add to the nones list *)
  | (S x'), None :: tail, (S l'), nones => remove_fancy x' tail l' (None :: nones)
  end.

Notation remove' x E l := (remove_fancy x E l nil).

Example remove_single : remove 0 (cons (Some TyBool) nil) = nil.
Proof.
  auto.
Qed.

Example remove_single' : remove' 0 (cons (Some TyBool) nil) 0 = nil.
Proof.
  auto.
Qed.

Example remove_oob : remove 1 (cons (Some TyBool) nil) = cons (Some TyBool) nil.
Proof.
  auto.
Qed.

Example remove_oob' : remove' 1 (cons (Some TyBool) nil) 0 = cons (Some TyBool) nil.
Proof. auto. Qed.

Example remove_last : remove' 1 (None :: Some TyBool :: nil) 1 = nil.
Proof.
  auto.
Qed.

Example remove_limit' : remove' 1 (None :: Some TyBool :: nil) 0 = None :: nil.
Proof.
  auto.
Qed.

Lemma split_insert_none_left_lookup : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  lookup x E1 = None.
Proof with eauto.
  intros E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [| x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in *.
    inversion Split...
  Case "x = S x'".
    rewrite raw_insert_successor in Split.
    destruct E1 as [|e1 E1']...
    replace (lookup (S x') (e1 :: E1')) with (lookup x' E1')...
    inversion Split; subst...
Qed.

Lemma split_insert_none_right_lookup : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  lookup x E2 = None.
Proof.
  eauto using split_insert_none_left_lookup, split_commute.
Qed.

Ltac omega_contra := exfalso; simpl in *; omega.

Lemma lookup_zero' : forall {A} (E : env A) e,
  lookup 0 (e :: E) = e.
Proof. eauto. Qed.

Lemma lookup_successor' : forall {A} (E : env A) e x,
  lookup (S x) (e :: E) = lookup x E.
Proof. eauto. Qed.

Lemma insert_remove : forall {A} (E : env A) x,
  x < length E ->
  raw_insert x (lookup x E) (remove x E) = E.
Proof with (eauto using lt_S_n).
  intros.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero.
    destruct E.
    SCase "E = nil". omega_contra.
    SCase "E = _ :: _". simpl...
  Case "x = S x'".
    destruct E as [|e E'].
    SCase "E = nil". omega_contra.
    SCase "E = e E'".
      simpl in *.
      rewrite lookup_successor'.
      rewrite raw_insert_successor.
      rewrite lookup_zero'.
      simpl.
      assert (x' < length E')...
      f_equal...
Qed.

(* The proof of this looks like it would be very involved *)
Lemma insert_none_split_left : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E1', E1 = raw_insert x None E1' /\ length E1' = length E).
Proof.
  admit.
Qed.
(*
  intros E E1 E2 x Split.
  exists (remove' x E1 (length E1 - length E - 1)).
  induction E1 as [|e1 E1'].
  Case "E1 = nil".
    inversion Split. exfalso; eauto using insert_nil.
  Case "E1 = e1 :: E1'".
    destruct x.
*)

Lemma insert_none_split_right : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E2', E2 = raw_insert x None E2' /\ length E2' = length E).
Proof.
  eauto using insert_none_split_left, split_commute.
Qed.

Lemma insert_none_split_strip_none : forall E E1 E2 x,
  length E = length E1 ->
  length E = length E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2) ->
  context_split E E1 E2.
Proof with eauto.
  intros E E1 E2 x Len1 Len2 Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero in *. inversion Split...
  Case "x = S x'".
    repeat rewrite raw_insert_successor in Split.
    inversion Split; subst.
    (* TODO: deduplicate this *)
    SCase "split_left".
      destruct E as [|e E'];
      destruct E1 as [|e1 E1'];
      destruct E2 as [|e2 E2']; try solve by inversion...
      (* Now we have only the cons cases *)
      simpl in *.
      replace e2 with (@None ty).
      replace e1 with e...
    SCase "split_right".
      destruct E as [|e E'];
      destruct E1 as [|e1 E1'];
      destruct E2 as [|e2 E2']; try solve by inversion...
      (* Now we have only the cons cases *)
      simpl in *.
      replace e1 with (@None ty).
      replace e2 with e...
Qed.

Lemma insert_none_split_backwards : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E1' E2', E1 = raw_insert x None E1' /\ E2 = raw_insert x None E2' /\ context_split E E1' E2').
Proof.
  intros E E1 E2 x H.
  assert (SplitL := H).
  assert (SplitR := H).
  apply insert_none_split_left in SplitL. destruct SplitL as [F1' [? ?]].
  apply insert_none_split_right in SplitR. destruct SplitR as [F2' [? ?]].
  exists F1'. exists F2'.
  split. eauto.
  split. eauto.
  subst. eauto using insert_none_split_strip_none.
Qed.

Lemma typing_insert_None : forall L E e t x,
  L; E |- e ~: t ->
  L; raw_insert x None E |- shift x e ~: t.
Proof with (eauto using le_0_n, lt_n_Sm_le, insert_none_is_empty, insert_none_split).
  intros L E e t x WT.
  generalize dependent x.
  induction WT; intros y; simpl_lift_goal...
  Case "Var".
    destruct (le_lt_dec y x); lift_idx.
    SCase "y <= x".
      rewrite insert_insert...
    SCase "y > x".
      destruct y as [|y']; try solve by inversion...
      rewrite <- insert_insert...
  Case "Abs".
    constructor.
    rewrite insert_insert...
Qed.

(* TODO: Prove the lemmas like this in DbLib (replace their equivalents) *)
Lemma raw_insert_eq_insert_1:
  forall A x a1 a2 (e1 e2 : env A),
  raw_insert x a1 e1 = raw_insert x a2 e2 ->
  a1 = a2.
Proof. admit. Qed.

Lemma raw_insert_eq_insert_3:
  forall A x1 x2 a1 a2 (e1 e2 : env A),
  raw_insert x1 a1 e1 = raw_insert x2 a2 e2 ->
  x1 <> x2 ->
  exists e y1 y2,
  e1 = raw_insert y1 a2 e /\
  e2 = raw_insert y2 a1 e /\
  shift x1 y1 = x2 /\
  y2 = (if le_gt_dec x1 y1 then x1 else x1 - 1).
Proof.
  admit.
Qed.

Lemma raw_insert_swap : forall A (E1 : env A) E2 x1 x2 o1 o2,
  raw_insert x1 o1 E1 = raw_insert x2 o2 E2 ->
  x1 <= x2 ->
  exists E0, E1 = raw_insert (x2 - 1) o2 E0 /\ E2 = raw_insert x1 o1 E0.
Proof.
  admit.
Qed.

Opaque unlift.

Lemma lift_var : forall x t e, shift x (TAbs t e) = TAbs t (shift (S x) (e)).
Proof with eauto.
  intros.
  repeat rewrite expand_lift.
  simpl traverse.
  simpl_lift_goal...
Qed.

Lemma unshift_Abs : forall x t e, unshift x (TAbs t e) = TAbs t (unshift (S x) e).
Proof with eauto.
  intros.
  simpl_unlift_goal...
Qed.

Lemma unshift_App : forall x e1 e2,
  unshift x (TApp e1 e2) = TApp (unshift x e1) (unshift x e2).
Proof with auto.
  intros.
  simpl_unlift_goal...
Qed.

Lemma typing_insert_None_reverse : forall L E e t x,
  L; raw_insert x None E |- e ~: t ->
  L; E |- unshift x e ~: t.
Proof with (eauto using insert_none_is_empty_inversion).
  intros L E e t x WT.
  generalize dependent x.
  generalize dependent t.
  generalize dependent E.
  induction e; try solve [intros; simpl; inversion WT; subst; eauto using insert_none_is_empty_inversion].
  Case "TVar".
    intros.
    Transparent unlift.
    simpl.
    destruct (le_gt_dec x n).
    SCase "x <= n".
      inversion WT; subst.
      rename E0 into E1.
      rename E into E2.
      symmetry in H1.
      apply raw_insert_swap in H1...
      decompose record H1.
      subst...
    SCase "x > n".
      inversion WT; subst.
      apply raw_insert_swap in H1.
      decompose record H1.
      subst...
      omega.
  Case "TAbs".
    intros.
    simpl_unlift_goal.
    inversion WT; subst.
    econstructor.
    apply IHe.
    rewrite<- insert_insert...
    omega.
  Case "TApp".
    intros.
    simpl_unlift_goal.
    inversion WT; subst.
    apply insert_none_split_backwards in AppPreSplit.
    destruct AppPreSplit as [E1' [E2' [E1'Intro [E2'Intro SplitE]]]].
    subst...
Qed.

Lemma subst_unshift : forall x e v,
  ~ contains_var x e ->
  subst v x e = unshift x e.
Proof with (eauto using f_equal, not_contains_Abs,
                        not_contains_App1, not_contains_App2).
  intros x e v NotContains.
  generalize dependent x.
  generalize dependent v.
  induction e; try solve [simpl_subst_goal; simpl; auto].
  Case "Var".
    intros.
    simpl_subst_goal. simpl.
    destruct (le_gt_dec x n).
    SCase "x <= n".
      destruct (le_lt_eq_dec x n)...
      SSCase "x < n". subst_idx...
      SSCase "x = n". exfalso. subst...
    SCase "x > n".
      subst_idx...
  Case "Abs".
    intros.
    simpl_subst_goal. rewrite unshift_Abs...
  Case "App".
    intros.
    simpl_subst_goal. rewrite unshift_App.
    rewrite IHe1...
Qed.

Lemma typing_without_var : forall L E e x t,
  L; raw_insert x None E |- e ~: t -> ~ contains_var x e.
Proof with (eauto using raw_insert_eq_insert_1, le_0_n).
  unfold not.
  intros L E e x t WT Contains.
  generalize dependent E.
  generalize dependent x.
  generalize dependent t.
  induction e; try solve [intros; solve by inversion].
  Case "Var".
    intros.
    destruct (eq_nat_dec x n).
    SCase "x = n".
      subst x.
      inversion WT; subst.
      assert (Some t = None)...
      solve by inversion.
    SCase "x <> n".
      inversion Contains...
  Case "TAbs".
    intros.
    inversion WT; subst.
    rewrite insert_insert in AbsPre...
    inversion Contains; subst...
  Case "TApp".
    intros.
    inversion Contains.
    (* TODO: deduplicate *)
    SCase "e1 contains x".
      subst.
      inversion WT. subst.
      apply insert_none_split_left in AppPreSplit.
      destruct AppPreSplit as [E1' [? ?]].
      subst...
    SCase "e2 contains x".
      subst.
      inversion WT. subst.
      apply insert_none_split_right in AppPreSplit.
      destruct AppPreSplit as [E1' [? ?]].
      subst...
Qed.

Lemma typing_insert_none_subst : forall L E e x junk t,
  L; raw_insert x None E |- e ~: t ->
  L; E |- subst junk x e ~: t.
Proof.
  intros L E e x junk t WT.
  remember WT as H eqn:Junk; clear Junk.
  apply typing_without_var in H.
  apply subst_unshift with (v := junk) in H.
  rewrite H.
  eauto using typing_insert_None_reverse.
Qed.

(* TODO: prove this with added bounds on the length *)
Lemma context_split_insert : forall E E1 E2 x t,
  context_split (insert x t E) E1 E2 ->
  (exists E1' E2',
    E1 = insert x t E1' /\
    E2 = raw_insert x None E2' /\
    length E1' = length E /\
    length E1' = length E
  ) \/
  (exists E1' E2',
    E1 = raw_insert x None E1' /\
    E2 = insert x t E2' /\
    length E1' = length E /\
    length E2' = length E
  ).
Proof with (eauto using raw_insert_zero, context_split_length1, context_split_length2).
  intros E E1 E2 x t Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x'].
  Case "x = 0".
    intros.
    rewrite raw_insert_zero in Split.
    (* FIXME: Bit messy, eauto used to Just Work here *)
    inversion Split; subst; [left | right]; eexists; eexists; repeat rewrite raw_insert_zero; repeat split...
  Case "x = S x'".
    intros.
    rewrite raw_insert_successor in Split.
    inversion Split.
    rename E3 into E1'.
    rename E4 into E2'.
    SCase "split left".
      left.
      apply IHx' in SplitLeft.
      destruct SplitLeft.
      SSCase "left".
        destruct H as [E1'' [E2'' [? [? [? ?]]]]].
        exists (lookup 0 E :: E1'').
        exists (None :: E2'').
        repeat rewrite raw_insert_successor.
        simpl.
        assert (lookup 0 (lookup 0 E :: E1'') = lookup 0 E) as R...
        rewrite R; clear R.
        assert (lookup 0 (None :: E2'') = None) as R...
        rewrite R; clear R.
        subst...
        (* Endless screaming *)
    admit. admit.
Qed.

Lemma split_cons : forall E E1 E2 e e1 e2,
  context_split (e :: E) (e1 :: E1) (e2 :: E2) ->
  context_split E E1 E2.
Proof with eauto.
  intros E E1 E2 e e1 e2 Split.
  destruct e1; inversion Split; subst...
Qed.

Lemma split_tails : forall E E1 E2,
  context_split (lookup 0 E :: tl E) (lookup 0 E1 :: tl E1) (lookup 0 E2 :: tl E2) ->
  context_split E E1 E2.
Proof with eauto.
  intros E E1 E2 Split.
  induction (E1).
  Case "nil".
    simpl in Split.
    rewrite lookup_empty_None in Split.
    inversion Split; subst.
    SCase "split empty".
      inversion SplitLeft.
      assert (E = None :: nil).
        destruct E. simpl in H1.
  Abort.
(*
  induction (lookup 0 E1 :: tl E1) as [|e1 E1'].
  Case "nil".
    solve by inversion.
  Case 
    inversion Split.

  dependent induction Split.
  apply IHSplit.

  induction E as [|e E'].
  Case "E = nil".
    simpl in Split.
    rewrite lookup_empty_None in Split.
    inversion Split; subst. inversion SplitLeft.
*)

Lemma length_insert' : forall {A} (E1 : env A) (E2 : env A) x v1 v2,
  length (raw_insert x v1 E1) = length (raw_insert x v2 E2) ->
  length E1 = length E2.
Proof with eauto.
  intros A E1 E2 x v1 v2 Len.
  rewrite length_insert_general with (k := length E1) in Len...
  rewrite length_insert_general with (k := length E2) in Len...
  simpl in Len.
  unfold mymax in Len.
  destruct (le_gt_dec (S (length E1)) (S x));
  destruct (le_gt_dec (S (length E2)) (S x)).
Abort.

(*
  intros A E1 E2 x v1 v2 Len.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent v1.
  generalize dependent v2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero in Len...
  Case "x = S x'".
    repeat rewrite raw_insert_successor in Len...
    assert (length (tl E1) = length (tl E2))...
    destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2'].
    SCase "nil and nil". auto.
    SCase "nil and cons".
      exfalso. simpl in H. simpl in Len.
        
Abort.
*)

Lemma split_insert_x : forall E E1 E2 x t,
  context_split (insert x t E) (insert x t E1) (raw_insert x None E2) ->
  context_split E E1 E2.
Proof with (eauto using split_cons).
(*
  intros E E1 E2 x t Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent t.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero in Split.
    inversion Split...
  Case "x = S x'".
    repeat rewrite raw_insert_successor in Split.
    destruct (lookup 0 E) as [t' | ] eqn: Lookup0E.
    SCase "E[0] = Some t'".
      inversion Split. subst.
      assert (context_split (tl E) (tl E1) (tl E2))...
      assert (context_split (Some t' :: tl E)
                            (Some t' :: tl E1)
                            (None :: tl E2))...
      Transparent lookup.
      Ltac crush list eq :=
        destruct list as [|e E'];
          [ exfalso; eauto using lookup_empty_Some
          | simpl in eq; subst e; eauto ].
      assert (E = Some t' :: tl E).
        crush E Lookup0E.
      assert (E1 = Some t' :: tl E1).
        crush E1 H.
      (* Eurgh, this is painful *)
      assert (E2 = None :: tl E2).
        assert (length E = length E2).
          rewrite <- Lookup0E in Split.
          repeat rewrite <- raw_insert_successor in Split.
          eauto using context_split_length2, length_insert'.
        destruct E2 as [|e2 E2'].
        SSCase "nil is impossible".
          exfalso. rewrite H2 in H5. solve by inversion.
        simpl in H4. subst e2. auto.
        (* that was the worst... *)
      (* Main lemma *)
      rewrite H2. rewrite H3. rewrite H5. auto.
      (* Split right case, similar *)
      admit.
    SCase "E[0] = None".
      admit.
*)
Abort.

Lemma split_insert_x : forall E E1 E2 x t,
  context_split (insert x t E) (insert x t E1) (raw_insert x None E2) ->
  context_split E E1 E2.
Abort.

Lemma substitution: forall L E2 e2 t1 t2 x,
  L; insert x t1 E2 |- e2 ~: t2 ->
  forall E E1 e1, L; E1 |- e1 ~: t1 ->
  context_split E E1 E2 ->
  L; E |- (subst e1 x e2) ~: t2.
Proof with (eauto using typing_insert_None, typing_insert_none_subst,
                        split_commute, split_rotate).
  intros L E2 e2 t1 t2 x WT2 E E1 e1 WT1 Split.
  dependent induction WT2; simpl_subst_goal; try solve [exfalso; eauto using insert_empty_contra].
  Case "Var".
    (* XXX: naming of x is weird here *)
    apply insert_empty_inversion in x...
    destruct x as [XEq [TEq E2Eq]].
    subst.
    simpl_subst_goal.
    apply split_single_left in Split...
    subst...
  Case "Abs".
    constructor.
    (* XXX: Bug in error reporting - can't specify E0 *)
    eapply IHWT2 with (t3 := t1) (E1 := (None :: E1)).
    SCase "inserts are equal". insert_insert.
    SCase "e1 well-typed under shifting".
      assert (L; raw_insert 0 None E1 |- shift 0 e1 ~: t1)...
    SCase "context_split is sensible".
      rewrite raw_insert_zero; rewrite raw_insert_zero...
  Case "App".
    rename E0 into E2'.
    rename E1 into E1'.
    rename E3 into E0.
    rename E2 into E12.
    (* x is either in E1' or E2' *)
    assert (SplitX := AppPreSplit).
    apply context_split_insert in SplitX.
    destruct SplitX as [XLeft | XRight].
    SCase "x on the left".
      destruct XLeft as [E1 [E2 [? ?]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E1 E2).
      Check length_insert_general.
        admit. (* problematic *)
      assert (context_split E12 E2 E1)...
      assert (exists E01, context_split E E2 E01 /\ context_split E01 E0 E1)
        as [E01 [Split201 SplitE01]]...
    SCase "x on the right".
      destruct XRight as [E1 [E2 [? ?]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E1 E2).
        admit.
      assert (exists E02, context_split E E1 E02 /\ context_split E02 E0 E2)
        as [E01 [Split201 SplitE01]]...
Qed.

(* Preservation *)
Theorem preservation : forall L E e e' s s' t,
  is_empty L ->
  is_empty E ->
  L; E |- e ~: t ->
  step s e s' e' ->
  L; E |- e' ~: t.
Proof with (eauto using empty_context, split_commute,
                        context_split_length1, context_split_length2).
  intros L E e e' s s' t EmptyL EmptyE WT ST.
  generalize dependent L.
  generalize dependent E.
  generalize dependent t.
  induction ST.
  Case "Beta reduction".
    intros.
    inversion WT; subst.
    assert (is_empty E1 /\ is_empty E2) as [EmptyE1 EmptyE2]...
    inversion AppPreWT1; subst.
    (* Establish that the contexts are all the same length and apply substitution lemma *)
    set (len := length E).
    assert (length E1 = len)...
    assert (length E2 = len)...
    apply substitution with (E1 := E2) (t1 := t1) (E2 := E1)...
  Case "App1 stepping".
    intros.
    inversion WT; subst.
    assert (is_empty E1 /\ is_empty E2) as [EmptyE1 _]...
  Case "App2 stepping".
    intros.
    inversion WT; subst.
    assert (is_empty E1 /\ is_empty E2) as [_ EmptyE2]...
Qed.
