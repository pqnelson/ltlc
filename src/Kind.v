Require Import Expression.
Require Import Util.
(**
Definition. The set [K] of lambda-kinds is defined
inductively as follows:

- [kappa] is in [K]
- If [x] is a variable and [A] is in [E] (i.e.,
  [A] is a lambda-expression) and [B] is in [K],
  then [KLam x:A.B] is in [K].
*)
Inductive kind : Type :=
 | kappa : kind                (* kind constant *)
 | KLam : exp -> kind -> kind. (* lambda kind *)

(**
Theorem. If [k] is a Lambda-Kind, then either
[k = kappa] or [k = KLam t k'] where [t] is some [exp]
and [k'] is another Lambda-Kind.

(As a consequence, it makes sense to talk about the
"length" of a [kind] by counting the number of [KLam]
constants that appear.)
*)
Theorem canonical_form_of_kinds :
 forall k : kind, k = kappa \/ (exists (t : exp) (k' : kind), k = KLam t k').
Proof.
  intuition.
  induction k.
  (* Case: k = kappa *)
  - left. reflexivity.
  (* Case: k = KLam e k *)
  - right. eauto .
Qed.