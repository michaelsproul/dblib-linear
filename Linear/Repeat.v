Require Import Basics.

(* A [repeat] function on lists, and lemmas about it *)
Fixpoint repeat {A} (n : nat) (e : A) : list A :=
  match n with
  | 0 => []
  | S n' => e :: repeat n' e
  end.

Lemma repeat_length : forall A n (e : A),
  length (repeat n e) = n.
Proof with (simpl; auto).
  intros.
  induction n as [|n']...
Qed.

Lemma repeat_app : forall A n (e : A),
  repeat (S n) e = repeat n e ++ [e].
Proof.
  intros.
  induction n as [|n'].
  Case "n = 0". auto.
  Case "n = S n'".
    replace (repeat (S (S n')) e) with (e :: repeat (S n') e).
    rewrite IHn' at 1.
    auto.
    auto.
Qed.
