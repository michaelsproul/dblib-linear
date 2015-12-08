(* PartialMap implementation adapted from Ben Pierce's Software Foundations *)
Require Import Util.
Require Import Coq.Logic.FunctionalExtensionality.

Definition partial_map (A : Type) := nat -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

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

Lemma extend_neq_empty : forall A (ctxt : partial_map A) x T,
  extend ctxt x T <> empty.
Proof.
  unfold not.
  intros.
  admit.
Qed.


