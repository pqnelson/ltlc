(** * Kinding judgements *)

Require Import Kind.
Require Import Expression.
Require Import Util.
Require Import ExpJudgment.

Reserved Notation "Gamma '|-' T '\ESTI' K" (at level 40).

Inductive has_kind : context -> exp -> kind -> Prop :=
  | K_Const : nil |- tau \ESTI kappa
  | K_Abs :
      forall (Gamma : context) (t T : exp) (K : kind),
      cons t Gamma |- T \ESTI K -> Gamma |- ELam t T \ESTI KLam t K
  | K_App :
      forall (Gamma : context) (t12 t1 T1 : exp) (K : kind),
      Gamma |- t12 \ESTI KLam T1 K ->
      Gamma |- t1 esti T1 -> Gamma |- EApp t12 t1 \ESTI K
  | K_Weak :
      forall (Gamma : context) (T T' : exp) (K K' : kind),
      Gamma |- T \ESTI K ->
      Gamma |- T' \ESTI K' -> cons T' Gamma |- T \ESTI K
 where "Gamma '|-' T '\ESTI' K" := (has_kind Gamma T K).
Hint Constructors has_kind.

(**
Definition. A lambda-expression [X] is "well-typed" according
to the context [Gamma] if either
  - there is some lambda-expression [T] such that [Gamma |- X \esti T], or
  - there is some lambda-kind [K] such that [Gamma |- X \ESTI K].
*)
Definition well_typed (X : exp) (Gamma : context) : Prop :=
  (exists T : exp, Gamma |- X esti T) \/
  (exists K : kind, Gamma |- X \ESTI K).

Definition correct (t : exp) : Prop := well_typed t nil.