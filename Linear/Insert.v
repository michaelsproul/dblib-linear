(* Lemmas about inserting values into typing contexts and splitting them *)

Require Export Linear.Context.

Lemma insert_none_def : forall A x (E : env A),
  x >= length E ->
  raw_insert x None E = E ++ repeat (S (x - length E)) None.
Proof with (simpl; eboom).
  intros A x E Len.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    destruct E as [|e E'].
    SCase "E = []".
      simpl...
    SCase "E = e :: E'".
      solve by inversion.
  Case "x = S x'".
    destruct E as [|e E'];
      simpl in *; rewrite raw_insert_successor; rewrite IHx'; simpl; try omega...
    SCase "E = []".
      replace (x' - 0) with x'; try omega...
Qed.

Lemma insert_none_is_empty : forall A (E : env A) E' x,
  is_empty E ->
  raw_insert x None E = E' ->
  is_empty E'.
Proof with eboom.
  intros A E E' x EmptyE Ins.
  generalize dependent E.
  generalize dependent E'.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Ins.
    subst...
  Case "x = S x'".
    rewrite raw_insert_successor in Ins.
    assert (lookup 0 E = None) as R; eauto using empty_lookup. rewrite R in Ins.
    subst E'.
    constructor.
    apply IHx' with (E := tl E)...
Qed.

Hint Resolve insert_none_is_empty : linear.

Lemma insert_none_is_empty_inversion : forall A (E : env A) x,
  is_empty (raw_insert x None E) -> is_empty E.
Proof with eboom.
  intros A E x Empty.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in Empty. inversion Empty...
  Case "x = S x'".
    rewrite raw_insert_successor in Empty.
    inversion Empty; subst.
    destruct E as [|e E']...
Qed.

Lemma insert_none_split : forall A (E : env A) E1 E2 x,
  context_split E E1 E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2).
Proof with eboom.
  Local Transparent lookup.
  intros A E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero; eboom.
  Case "x = S x'".
    repeat rewrite raw_insert_successor.
    inversion Split as [|E' E1' E2']...
Qed.

(* Note: this lemma isn't used by PLLC *)
Lemma split_none_head : forall A (E : env A) E1 E2,
  context_split (None :: E) E1 E2 ->
  exists E1' E2', E1 = None :: E1' /\ E2 = None :: E2'.
Proof with eboom.
  intros A E E1 E2 Split.
  inversion Split; inversion SplitElem; subst...
Qed.

(* Not used by PLLC, but nice to have *)
Lemma split_insert_none_left_lookup : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  lookup x E1 = None.
Proof with eboom.
  intros A E E1 E2 x Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [| x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero in *.
    inversion Split; inversion SplitElem...
  Case "x = S x'".
    rewrite raw_insert_successor in Split.
    destruct E1 as [|e1 E1']...
    replace (lookup (S x') (e1 :: E1')) with (lookup x' E1')...
    inversion Split; inversion SplitElem; subst...
Qed.

(* Not used, as above *)
Lemma split_insert_none_right_lookup : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  lookup x E2 = None.
Proof.
  eauto using split_insert_none_left_lookup, split_commute.
Qed.

Lemma split_app_single : forall A (E : env A) E1 E2,
  context_split (E ++ [None]) E1 E2 ->
  exists E1' E2', E1 = E1' ++ [None] /\ E2 = E2' ++ [None] /\ context_split E E1' E2'.
Proof.
  intros A E E1 E2 Split.
  generalize dependent E.
  generalize dependent E2.
  induction E1 as [| e1 E1s]; intros.
  Case "E1 = []".
  inversion Split.
  assert (E = [] /\ [@None A] = []) as [? ?].
    apply app_eq_nil.
    auto.
  solve by inversion.
  Case "E1 = e1 :: E1s".
    destruct E as [|e E'].
    SCase "E = []".
      exists nil. exists nil.
      simpl in *.
      inversion Split; inversion SplitPre; inversion SplitElem; subst; eboom.
    SCase "E = e :: E'".
      destruct E2 as [|e2 E2s]; try solve by inversion.
      (* E2 is now e2 :: E2s *)
      simpl in Split.
      inversion Split; subst.
      apply IHE1s in SplitPre.
      destruct SplitPre as [E1' [E2' [? [? ?]]]].
      exists (e1 :: E1').
      exists (e2 :: E2').
      subst.
      eboom.
Qed. (* NOTE: benefits of split_single demonstrated here *)

Lemma split_app : forall A (E : env A) E1 E2 n,
  context_split (E ++ repeat n None) E1 E2 ->
  exists E1' E2',
    E1 = E1' ++ repeat n None /\
    E2 = E2' ++ repeat n None /\
    context_split E E1' E2'.
Proof with eboom.
  intros A E E1 E2 n Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction n as [|n']; intros.
  Case "n = 0".
    simpl in *.
    exists E1, E2.
    repeat rewrite app_nil_r in *...
  Case "n = S n'".
    rewrite repeat_app in Split.
    rewrite app_assoc in Split.
    apply split_app_single in Split.
    destruct Split as [E1' [E2' [? [? SplitInd]]]].
    apply IHn' in SplitInd.
    destruct SplitInd as [E1'' [E2'' [? [? ?]]]].
    subst.
    exists E1'', E2''.
    repeat rewrite <- app_assoc.
    repeat rewrite repeat_app.
    eboom.
Qed.

Lemma insert_none_split_strip_none : forall A (E : env A) E1 E2 x,
  length E = length E1 ->
  length E = length E2 ->
  context_split (raw_insert x None E) (raw_insert x None E1) (raw_insert x None E2) ->
  context_split E E1 E2.
Proof with eboom.
  intros A E E1 E2 x Len1 Len2 Split.
  generalize dependent E.
  generalize dependent E1.
  generalize dependent E2.
  induction x as [|x']; intros.
  Case "x = 0".
    repeat rewrite raw_insert_zero in *. inversion Split...
  Case "x = S x'".
    repeat rewrite raw_insert_successor in Split.
    inversion Split; subst.
    destruct E as [|e E'];
    destruct E1 as [|e1 E1'];
    destruct E2 as [|e2 E2']; try solve by inversion...
Qed. (* NOTE: more massive benefits of split_single *)

Hint Resolve insert_none_split_strip_none : linear.

(* This was one of the most difficult to prove *)
Lemma insert_none_split_backwards : forall A (E : env A) E1 E2 x,
  context_split (raw_insert x None E) E1 E2 ->
  exists E1' E2',
    E1 = raw_insert x None E1' /\
    length E1' = length E /\
    E2 = raw_insert x None E2' /\
    length E2' = length E /\
    context_split E E1' E2'.
Proof with eboom.
  intros A E E1 E2 x Split.
  destruct (Compare_dec.le_gt_dec (length E) x) as [OutOfBounds | InBounds].
  Case "length E <= x".
    rewrite insert_none_def in Split; try omega.
    apply split_app in Split.
    destruct Split as [E1' [E2' [? [? ?]]]].
    exists E1', E2'.
    subst E1 E2.
    assert (length E1' = length E) as Len1...
    assert (length E2' = length E) as Len2...
    repeat rewrite insert_none_def; try omega.
    rewrite Len1; rewrite Len2...
  Case "length E > x".
    generalize dependent E.
    generalize dependent E1.
    generalize dependent E2.
    induction x as [|x']; intros.
    SCase "x = 0".
      repeat rewrite raw_insert_zero in *.
      destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2']; try solve by inversion.
      inversion Split; inversion SplitElem; subst;
        exists E1', E2';
        repeat rewrite raw_insert_zero;
        repeat split...
    SCase "x = S x'".
      destruct E as [|e E']; try solve by inversion.
      destruct E1 as [|e1 E1']; destruct E2 as [|e2 E2']; try solve by inversion.
      rewrite raw_insert_successor in Split.
      simpl in Split.
      inversion Split; subst.
      apply IHx' in SplitPre; simpl in *; try omega.
      destruct SplitPre as [E1'' [E2'' [? [? [? [? ?]]]]]].
      exists (e1 :: E1''), (e2 :: E2'').
      subst; simpl.
      repeat split...
Qed. (* NOTE: more benefits of split_single *)

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
      replace (lookup 0 [] : option A) with (@None A) in Split...
      simpl in *.
      inversion Split; subst.
      set (Intro := SplitPre).
      apply IHx' in Intro...
      destruct Intro as [IH | IH];
        [left | right];
        destruct IH as [E1'' [E2'' [? [? [? [? ?]]]]]];
        destruct E1'' as [|]; try solve by inversion;
        destruct E2'' as [|]; try solve by inversion;
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
