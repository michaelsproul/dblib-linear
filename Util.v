Require Import Coq.Lists.List.
Require Export Coq.Program.Equality.

(* Decision procedure for nat equality, and some theorems about it. *)
Theorem eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
Proof.
  decide equality.
Defined.

Theorem eq_id : forall (T: Type) n (p q: T), (if eq_nat_dec n n then p else q) = p.
Proof.
  intros T n p q.
  destruct (eq_nat_dec n n).
    reflexivity.
    assert False as contra; auto. inversion contra.
Qed.

Theorem neq_id : forall (T: Type) n1 n2 (p q: T),
  n1 <> n2 ->
  (if eq_nat_dec n1 n2 then p else q) = q.
Proof.
  intros T n1 n2 p q neq.
  destruct (eq_nat_dec n1 n2).
    assert False as contra; auto. inversion contra.
    reflexivity.
Qed.

(* Solve by inversion tactic nicked from SfLib *)
Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

(* Case markers also nicked from SF *)
Require String.
Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* Hint database for use with auto *)
(* Note, the _x suffix is used for automation-oriented tactics *)
Create HintDb l3.

(* Miscellaneous lemmas for us with auto *)
Lemma list_head_eq : forall {A} (h1 : A) h2 t1 t2,
  h1 :: t1 = h2 :: t2 ->
  h1 = h2.
Proof. congruence. Qed.

Lemma zero_length_nil : forall {A} (l : list A),
  length l = 0 ->
  l = nil.
Proof with auto.
  intros.
  destruct l; try solve by inversion...
Qed.

Hint Resolve zero_length_nil : l3.

(* f_equal is great *)
Hint Resolve f_equal : l3.

(* Specialised versions of auto *)
Ltac boom := auto with l3.
Ltac eboom := eauto with l3.