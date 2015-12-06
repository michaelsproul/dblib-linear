(* PartialMap implementation adapted from Ben Pierce's Software Foundations *)
Module PartialMap.

(* Decision procedure for nat equality and some theorems about it. *)
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

Definition partial_map (A : Type) := nat -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

Definition extend {A:Type} (Gamma : partial_map A) (x : nat) (T : A) :=
  fun x' => if eq_nat_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.