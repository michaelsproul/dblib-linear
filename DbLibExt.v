Require Import Environments.
Require Import DbLib.Environments.
Require Import DbLib.DeBruijn.
Require Import Compare_dec.

(* Temporary extensions to DbLib *)
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