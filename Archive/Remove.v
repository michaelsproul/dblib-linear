(* Unused functions relating to the removal of values from environments *)
(* Ultimately, this approach was found to be highly annoying to reason about *)
Require Import DbLib.Environments.
Require Import List.
Require Import Syntax.
Require Import Lt.
Require Import Environment.

Fixpoint remove {A} (x : nat) (E : env A) : env A :=
  match x, E with
  | _, nil => nil
  | 0, h :: t => t
  | (S x'), h :: t => h :: remove x' t
  end.

Fixpoint remove_fancy {A} (x : nat) (E : env A) (chomp_limit : nat) (nones : env A) : env A :=
  match x, E, chomp_limit, nones with
  | _, nil, _, _ => nil
  (* If we've reached our element, and there are no more following it, drop the nones preceding it *)
  | 0, h :: nil, _, nones => nil
  (* Otherwise, if we've reached our element and there are things after it, re-insert the nones *)
  | 0, h :: tail, _, nones => nones ++ tail
  (* If we find an intermediate element, clear the nones list and proceed with the recursion *)
  | (S x'), (Some t) :: tail, _, _ => (Some t) :: remove_fancy x' tail chomp_limit nil
  (* If we find an intermediate element and the chomp_limit is exhausted we have to leave the None in there *)
  | (S x'), None :: tail, 0, nones => None :: remove_fancy x' tail 0 nones
  (* Otherwise if the chomp_limit isn't exhausted we add to the nones list *)
  | (S x'), None :: tail, (S l'), nones => remove_fancy x' tail l' (None :: nones)
  end.

Notation remove' x E l := (remove_fancy x E l nil).

Ltac omega_contra := exfalso; simpl in *; omega.

Check lt_S_n.

Lemma insert_remove : forall A (E : env A) x,
  x < length E ->
  raw_insert x (lookup x E) (remove x E) = E.
Proof with (eauto using lt_S_n with l3).
  intros.
  generalize dependent E.
  induction x as [|x']; intros.
  Case "x = 0".
    rewrite raw_insert_zero.
    destruct E.
    SCase "E = nil". omega_contra.
    SCase "E = _ :: _". simpl...
  Case "x = S x'".
    destruct E as [|e E'].
    SCase "E = nil". omega_contra.
    SCase "E = e E'".
      simpl in *.
      rewrite lookup_succ_cons.
      rewrite raw_insert_successor.
      rewrite lookup_zero_cons.
      simpl.
      assert (x' < length E')...
Qed.

Example remove_single : remove 0 (cons (Some TyBool) nil) = nil.
Proof.
  auto.
Qed.

Example remove_single' : remove' 0 (cons (Some TyBool) nil) 0 = nil.
Proof.
  auto.
Qed.

Example remove_oob : remove 1 (cons (Some TyBool) nil) = cons (Some TyBool) nil.
Proof.
  auto.
Qed.

Example remove_oob' : remove' 1 (cons (Some TyBool) nil) 0 = cons (Some TyBool) nil.
Proof. auto. Qed.

Example remove_last : remove' 1 (None :: Some TyBool :: nil) 1 = nil.
Proof.
  auto.
Qed.

Example remove_limit' : remove' 1 (None :: Some TyBool :: nil) 0 = None :: nil.
Proof.
  auto.
Qed.
