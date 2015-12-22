(* Environments that store their length as part of their type *)
Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.VectorDef.

Notation "[]" := (nil _).
Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Definition env (A : Type) (n : nat) : Type :=
  Vector.t (option A) n.

Definition empty A n : env A n :=
  const None n.

(* Environment of length n with x = a. *)
(* FIXME: finite integers? x < n *)
Definition singleton A n x (a : A) : env A n :=
  match x with
  | O => Some a :: []
  |
  end.
