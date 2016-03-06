

(* Time to prove progress *)

(* -------------------------- *)
(* Substitution helper lemmas *)
(* -------------------------- *)

Lemma insert_none_is_empty : forall {A} (E : env A) E' x,
  is_empty E ->
  raw_insert x None E = E' ->
  is_empty E'.
Proof with eauto using (empty_lookup).
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

Lemma context_split_insert : forall E E1 E2 x t,
  context_split (insert x t E) E1 E2 ->
  (exists E1' E2',
    E1 = insert x t E1' /\
    E2 = raw_insert x None E2' /\
    length E1' = length E /\
    length E2' = length E
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
    destruct E as [|e E];
    destruct E1 as [|e1 E1'];
    destruct E2 as [|e2 E2']; try solve by inversion.
    SCase "E = nil, E1 = e1 :: E1, E2 = e2 :: E2".
      replace (lookup 0 (@nil (option ty))) with (@None ty) in Split...
      simpl in *.
      inversion Split; subst.
      SSCase "left".
        set (T := SplitLeft).
        apply IHx' in T...
        destruct T.
        SSSCase "left".
          left.
          destruct H as [E1'' [E2'' [? [? [? ?]]]]].
          exists nil. exists nil.
          repeat rewrite raw_insert_successor.
          repeat rewrite lookup_zero'.
          assert (E1'' = nil)...
            destruct E1''; try solve by inversion...
          assert (E2'' = nil)...
            destruct E2''; try solve by inversion...
          subst...
        admit. (* Same *)
      SSCase "right".
        admit. (* Same *)
  SCase "all cons".
    rewrite lookup_zero' in Split.
    simpl in Split.
    inversion Split; subst.
    SSCase "left".
      set (T := SplitLeft).
      apply IHx' in T.
      destruct T.
      SSSCase "left".
        destruct H as [E1'' [E2'' [? [? [? ?]]]]].
        left.
        exists (e1 :: E1'').
        exists (None :: E2'').
        repeat rewrite raw_insert_successor in *.
        simpl.
        repeat rewrite lookup_zero'.
        subst.
        repeat split...
     SSSCase "right".
       admit.
   SSCase "right".
     admit.
Qed. (* FIXME: use split_cons to remove duplication *)

Lemma split_cons : forall E E1 E2 e e1 e2,
  context_split (e :: E) (e1 :: E1) (e2 :: E2) ->
  context_split E E1 E2.
Proof with eauto.
  intros E E1 E2 e e1 e2 Split.
  destruct e1; inversion Split; subst...
Qed.

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
  dependent induction WT2; simpl_subst_goal; try solve [exfalso; eauto using empty_insert_contra].
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
      destruct XLeft as [E1 [E2 [? [? [? ?]]]]].
      subst E1'.
      subst E2'.
      assert (context_split E12 E1 E2).
      Check length_insert_general.
        admit. (* problematic *)
      assert (context_split E12 E2 E1)...
      assert (exists E01, context_split E E2 E01 /\ context_split E01 E0 E1)
        as [E01 [Split201 SplitE01]]...
    SCase "x on the right".
      destruct XRight as [E1 [E2 [? [? [? ?]]]]].
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
