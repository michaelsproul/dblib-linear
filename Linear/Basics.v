(* Export lists and list notation *)
Require Export List.
Export ListNotations.

(* Export strings and SfLib tactics *)
Require Export Linear.SfLib.

(* A hint database for library lemmas, that we also use for language lemmas *)
Create HintDb linear.

Hint Resolve f_equal : linear.

(* Specialised versions of auto *)
Ltac boom := auto with linear.
Ltac eboom := eauto with linear.
