(* Proof of progress! *)
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
