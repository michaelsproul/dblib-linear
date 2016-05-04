(* Lemmas that may prove useful at some point... *)

Lemma term_split : forall e,
  {e = TVar 0} + {e <> TVar 0}.
Proof.
  Ltac crush := right; unfold not; intros; solve by inversion.
  destruct e; try solve [crush].
  destruct n as [|n']; try solve [crush].
    left; auto.
Qed.

Lemma split_misc_lemma : forall E E1 E2 v,
  context_split (v :: E) E1 E2 ->
  exists v1 v2 E1' E2', E1 = v1 :: E1' /\ E2 = v2 :: E2' /\ context_split E E1' E2'.
Proof with auto.
  intros E E1 E2 v Split.
  inversion Split as [| ? E1' E2' | ? E1' E2']; subst.
  Case "left".
    exists v, None, E1', E2'...
  Case "right".
    exists None, v, E1', E2'...
Qed.
