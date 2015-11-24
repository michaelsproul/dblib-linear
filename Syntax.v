Require Import DbLib.DeBruijn.
Require Import DbLib.Environments.
Require Import DbLib.DblibTactics.

Module Syntax.

(* We use natural numbers as De Bruijn indices to denote term and location variables. *)
Definition id := nat.

(* Type for terms, or 'expressions' in L3 parlance. *)
Inductive term : Type :=
  (* () *)
  | TUnit
  (* let () = e1 in e2 *)
  | TLetUnit : term -> term -> term
  (* (x, y) *)
  | TPair : term -> term -> term
  (* let (x1, x2) = e1 in e2 *)
  | TLetPair : id -> id -> term -> term
  | TVar : id -> term
  | TAbs : term -> term
  | TApp : term -> term -> term
  (* FIXME: Need a value bound here? *)
  | TBang : term -> term
  (* let !x = e1 in e2 *)
  | TLetBang : id -> term -> term -> term
  | TDupl : term -> term
  | TDrop : term -> term
  | TPtr : id -> term
  | TCap
  | TNew : term -> term
  | TFree : term -> term
  | TSwap : term -> term -> term -> term
  | TLocAbs : id -> term -> term 
  | TLocApp : term -> id -> term
  (* let |p, x| = e1 in e2 *)
  | TLetEx : id -> id -> term -> term -> term
.

Inductive ty : Type :=
  | TyUnit
  | TyProduct : ty -> ty -> ty
  | TyFunc : ty -> ty -> ty
  | TyBang : ty -> ty
  | TyPtr : id -> ty
  | TyCap : id -> ty -> ty
  | TyForAll : ty -> ty
  | TyEx : ty -> ty
.

Instance Var_term : Var term := {
  var := TVar
}.

End Syntax.