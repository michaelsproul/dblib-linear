Require Import Basics.
Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Export Compare_dec.

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
