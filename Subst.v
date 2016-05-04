Require Import DbLib.Environments.
Require Import List.
Require Import Typing.
Require Import Syntax.
Require Import Empty.
Require Import Context.
Require Import Environment.
Require Import DbLib.DeBruijn.
Require Import Arith.
Require Import DbLibExt.
Require Import InsertNone.
Import ListNotations.

Lemma unshift_Abs : forall x t e, unshift x (TAbs t e) = TAbs t (unshift (S x) e).
Proof with eauto.
  intros.
  simpl_lower_goal...
Qed.

Lemma unshift_App : forall x e1 e2,
  unshift x (TApp e1 e2) = TApp (unshift x e1) (unshift x e2).
Proof with auto.
  intros.
  simpl_lower_goal...
Qed.

Lemma subst_unshift : forall x e v,
  ~ contains_var x e ->
  subst v x e = unshift x e.
Proof with (eauto using f_equal, not_contains_Abs,
                        not_contains_App1, not_contains_App2 with l3).
  Local Transparent lower.
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

Lemma typing_without_var : forall E e x t,
  raw_insert x None E |- e ~: t -> ~ contains_var x e.
Proof with (eauto using raw_insert_eq_insert_1, le_0_n).
  unfold not.
  intros E e x t WT Contains.
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
      apply insert_none_split_backwards in AppPreSplit.
      decompose record AppPreSplit.
      subst...
    SCase "e2 contains x".
      subst.
      inversion WT. subst.
      apply insert_none_split_backwards in AppPreSplit.
      decompose record AppPreSplit.
      subst...
Qed.

Lemma typing_insert_none_subst : forall E e x junk t,
  raw_insert x None E |- e ~: t ->
  E |- subst junk x e ~: t.
Proof.
  intros E e x junk t WT.
  remember WT as H eqn:Junk; clear Junk.
  apply typing_without_var in H.
  apply subst_unshift with (v := junk) in H.
  rewrite H.
  eauto using typing_insert_none_reverse.
Qed.

Lemma length_zero_nil : forall A (l : list A),
  length l = length (@nil A) ->
  l = (@nil A).
Proof.
  intros. destruct l; try solve by inversion; reflexivity.
Qed.

Hint Immediate length_zero_nil : l3.

(* UNIVERSAL *)
(* insert/split *)
Lemma context_split_insert : forall A (E : env A) E1 E2 x t,
  context_split (insert x t E) E1 E2 ->
  (exists E1' E2',
    E1 = insert x t E1' /\
    E2 = raw_insert x None E2' /\
    length E1' = length E /\
    length E2' = length E /\
    context_split E E1' E2'
  ) \/
  (exists E1' E2',
    E1 = raw_insert x None E1' /\
    E2 = insert x t E2' /\
    length E1' = length E /\
    length E2' = length E /\
    context_split E E1' E2'
  ).
Proof with eboom.
  intros A E E1 E2 x t Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x'].
  Case "x = 0".
    intros.
    rewrite raw_insert_zero in Split.
    inversion Split; subst.
    inversion SplitElem; subst; [left | right];
    eexists; eexists; repeat rewrite raw_insert_zero; repeat split...
  Case "x = S x'".
    intros.
    rewrite raw_insert_successor in Split.
    destruct E as [|e E];
    destruct E1 as [|e1 E1'];
    destruct E2 as [|e2 E2']; try solve by inversion.
    SCase "E = nil, E1 = e1 :: E1, E2 = e2 :: E2".
      replace (lookup 0 (@nil (option ty))) with (@None ty) in Split...
      simpl in *.
      inversion Split; subst.
      set (Intro := SplitPre).
      apply IHx' in Intro...
      destruct Intro as [IH | IH];
        [left | right];
        destruct IH as [E1'' [E2'' [? [? [? [? ?]]]]]];
        assert (E1'' = []); eboom;
        assert (E2'' = []); eboom;
        subst;
        exists [], [];
        repeat rewrite raw_insert_successor;
        repeat rewrite lookup_zero_nil in *;
        inversion SplitElem...
  SCase "all cons".
    rewrite lookup_zero_cons in Split.
    simpl in Split.
    inversion Split; subst.
    set (Intro := SplitPre).
    apply IHx' in Intro.
    destruct Intro as [IH | IH];
      [left | right];
      destruct IH as [E1'' [E2'' [? [? [? [? ?]]]]]];
      exists (e1 :: E1''), (e2 :: E2'');
      repeat rewrite raw_insert_successor in *;
      repeat rewrite lookup_zero_cons in *;
      simpl; subst; repeat split...
Qed.

Lemma substitution: forall E2 e2 t1 t2 x,
  insert x t1 E2 |- e2 ~: t2 ->
  forall E E1 e1, E1 |- e1 ~: t1 ->
  context_split E E1 E2 ->
  E |- (subst e1 x e2) ~: t2.
Proof with (eauto using typing_insert_none, typing_insert_none_subst,
            split_rotate  with l3).
  intros E2 e2 t1 t2 x WT2 E E1 e1 WT1 Split.
  dependent induction WT2; simpl_subst_goal; try solve [exfalso; eauto using empty_insert_contra].
  Case "Var".
    (* XXX: naming of x is weird here *)
    apply empty_insert_injective in x...
    destruct x as [XEq [TEq E2Eq]].
    subst.
    simpl_subst_goal.
    apply split_all_left in Split...
    subst...
  Case "Abs".
    constructor.
    (* XXX: Bug (?) in error reporting - can't specify E0 *)
    eapply IHWT2 with (t3 := t1) (E1 := (None :: E1)).
    SCase "inserts are equal". insert_insert.
    SCase "e1 well-typed under shifting".
      assert (raw_insert 0 None E1 |- shift 0 e1 ~: t1)...
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
      destruct XLeft as [E1 [E2 [? [? [? [? ?]]]]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E2 E1); [eboom | ].
      assert (exists E01, context_split E E2 E01 /\ context_split E01 E0 E1)
        as [E01 [Split201 SplitE01]]...
    SCase "x on the right".
      destruct XRight as [E1 [E2 [? [? [? [? ?]]]]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E1 E2); [eboom | ].
      assert (exists E02, context_split E E1 E02 /\ context_split E02 E0 E2)
        as [E01 [Split201 SplitE01]]...
Qed.
