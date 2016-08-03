Require Export Expression.

(**
Definition. The set [K] of lambda-kinds is defined
inductively as follows:

- [kappa] is in [K]
- If [x] is a variable and [A] is in [E] (i.e.,
  [A] is a lambda-expression) and [B] is in [K],
  then [KLam x:A.B] is in [K].
*)
Inductive kind : Type :=
 | kappa : kind                           (* kind constant *)
 | KLam : Expression.exp -> kind -> kind. (* lambda kind *)


