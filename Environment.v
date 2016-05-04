Require Import DbLib.Environments.
Require Import List.
Require Export Syntax.

(* DbLib utils *)
Lemma lookup_zero_nil : forall A,
  lookup 0 [] = @None A.
Proof. auto. Qed.

Lemma lookup_zero_cons : forall A (E : env A) e,
  lookup 0 (e :: E) = e.
Proof. eauto. Qed.

Lemma lookup_succ_cons : forall A (E : env A) e x,
  lookup (S x) (e :: E) = lookup x E.
Proof. eauto. Qed.
