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

Lemma context_split_length1 : forall E E1 E2,
  context_split E E1 E2 ->
  length E = length E1.
Proof.
  intros E E1 E2 Split.
  induction Split; simpl; eauto.
Qed.

Lemma context_split_length2 : forall E E1 E2,
  context_split E E1 E2 ->
  length E = length E2.
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
      L; E |- TAbs t1 e ~: TyFun t1 t2
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
Proof. admit. Qed.

Lemma insert_none_is_empty_inversion : forall {A} (E : env A) x,
  is_empty (raw_insert x None E) -> is_empty E.
Proof.
  admit.
Qed.
(*
  intros A E x Empty.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Empty.
    inversion Empty. assumption.
  Case "x = S x'".
    rewrite raw_insert_successor in Empty.
    inversion Empty.
    assert (is_empty (tl E)).
    auto.
    assert (E = lookup 0 E :: tl E).
      admit.
    rewrite H. auto.
    Check (hd E).
    Check lookup_zero.
    auto.
*)

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

(* TODO *)
Lemma insert_none_split_left : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E1', E1 = raw_insert x None E1').
Proof.
  intros E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Split.
    apply split_none_head in Split. destruct Split as [E1' [E2' [Intro1 Intro2]]].
    exists E1'.
    eauto using raw_insert_zero.
  Case "S x'".
    rewrite raw_insert_successor in Split.
    inversion Split; subst.
    SCase "split_left".
      subst.
      admit.
  admit.
Qed.

Lemma insert_none_split_right : forall E E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  (exists E2', E2 = raw_insert x None E2').
Proof.
  eauto using insert_none_split_left, split_commute.
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

(* TODO *)
Lemma typing_insert_None_reverse : forall L E e t x,
  L; raw_insert x None E |- e ~: t ->
  L; E |- unshift x e ~: t.
Proof.
  intros L E e t x WT.
  admit.
Qed.

(* TODO: These two lemmas will be proved with DbLib automation, simpl_unlift_goal. *)
Lemma unshift_Abs : forall x t e,
  unshift x (TAbs t e) = TAbs t (unshift (S x) e).
Proof.
  admit.
Qed.

Lemma unshift_App : forall x e1 e2,
  unshift x (TApp e1 e2) = TApp (unshift x e1) (unshift x e2).
Proof.
  admit.
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
      destruct AppPreSplit as [E1' IntroE1'].
      subst...
    SCase "e2 contains x".
      subst.
      inversion WT. subst.
      apply insert_none_split_right in AppPreSplit.
      destruct AppPreSplit as [E1' IntroE1'].
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

Lemma substitution: forall L E2 e2 t1 t2 x,
  L; insert x t1 E2 |- e2 ~: t2 ->
  forall E E1 e1, L; E1 |- e1 ~: t1 ->
  context_split E E1 E2 ->
  L; E |- (subst e1 x e2) ~: t2.
Proof with (eauto using typing_insert_None).
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
    assert (exists E1, E1' = raw_insert x None E1) as [E1 E1Intro].
      admit.
    assert (exists E2, E2' = insert x t1 E2) as [E2 E2Intro].
      admit.
    assert (exists E02, context_split E02 E0 E2 /\ context_split E E1 E02) as [E02 [SplitE02 SplitE102]].
      admit.
    apply HasTyApp with (E1 := E1) (E2 := E02) (t1 := t0).
      assumption.
    subst E1'; eauto using typing_insert_none_subst.
    apply IHWT2_2 with (E1 := E0) (E2 := E2) (t1 := t1).
      rewrite E2Intro; auto. (* messy *)
      assumption.
      assumption.
Qed.

(* Preservation - TODO *)
Theorem preservation : forall L E e e' s s' t,
  is_empty L ->
  is_empty E ->
  L; E |- e ~: t ->
  step s e s' e' ->
  L; E |- e' ~: t.
Proof with eauto.
  intros L E e e' s s' t EmptyL EmptyE WT ST.
  generalize dependent t.
  induction ST.
  Case "Beta reduction".
    intros.
    inversion WT; subst.
    apply empty_context in AppPreSplit. destruct AppPreSplit. subst.
    inversion AppPreWT1; subst.
    apply substitution with (E1 := E2) (t1 := t1) (E2 := E1).
      assumption.
      assumption.
      admit. (* need a thing about empty context splits *)
      assumption.
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
