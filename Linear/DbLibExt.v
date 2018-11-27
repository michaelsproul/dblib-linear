Require Import Basics.
Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Export Compare_dec.

(* Temporary extensions to DbLib *)
(* These lemmas are the same as ones upstream except that they use raw_insert rather than insert
 * Therefore it's "relatively safe" to admit them as axioms (I'm almost certain they're true).
*)
Lemma raw_insert_eq_insert_1:
  forall A x a1 a2 (e1 e2 : env A),
  raw_insert x a1 e1 = raw_insert x a2 e2 ->
  a1 = a2.
Proof with eauto.
  induction x.
  Case "x = 0".
    intros a1 a2 e1 e2 RI.
    rewrite raw_insert_zero in RI.
    rewrite raw_insert_zero in RI.
    inversion RI...
  Case "x = Suc _".
    intros a1 a2 e1 e2 RI.
    rewrite raw_insert_successor in RI.
    rewrite raw_insert_successor in RI.
    inversion RI...
Qed.

Lemma raw_insert_swap : forall A (E1 : env A) E2 x1 x2 o1 o2,
  raw_insert x1 o1 E1 = raw_insert x2 o2 E2 ->
  x1 <= x2 ->
  exists E0, E1 = raw_insert (x2 - 1) o2 E0 /\ E2 = raw_insert x1 o1 E0.
Proof.
  admit.
Qed.

(* These are some safe utility lemmas about DbLib *)
Lemma lookup_zero_nil : forall A,
  lookup 0 [] = @None A.
Proof. auto. Qed.

Lemma lookup_zero_cons : forall A (E : env A) e,
  lookup 0 (e :: E) = e.
Proof. eauto. Qed.

Lemma lookup_succ_cons : forall A (E : env A) e x,
  lookup (S x) (e :: E) = lookup x E.
Proof. eauto. Qed.

Global Opaque empty.
