Require Export Coq.Lists.List.
Require Export Symbols.
Require Export Util.
Require Export Expression.

(** printing esti #<span style="font-family: monospace;">&#58;</span># *)
(** printing ==> #<span style="font-family: arial;">&rArr;</span># *)
(** printing ==>* #<span style="font-family: arial;">&rArr;*</span># *)
(** printing |- #<span style="font-family: arial;">&#8866;</span># *)
(** printing tau #<span style="font-family: serif; font-size:85%;">&tau;</span># *)
(** printing Gamma #<span style="font-family: serif; font-size:85%;">&Gamma;</span># *)
(** printing Gamma' #<span style="font-family: serif; font-size:85%;">&Gamma;'</span># *)
(** printing Gamma'' #<span style="font-family: serif; font-size:85%;">&Gamma;''</span># *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : exp -> exp -> Prop :=
  | ST_AppAbs :
      forall T t12 v2, wnf v2 -> EApp (ELam T t12) v2 ==> subst 0 v2 t12
  | ST_App1 : forall t1 t1' t2, t1 ==> t1' -> EApp t1 t2 ==> EApp t1' t2
  | ST_App2 : forall t1 t2 t2', t2 ==> t2' -> EApp t1 t2 ==> EApp t1 t2'
 where "t1 '==>' t2" := (step t1 t2).
Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(** ** Typing judgements 

For lambda-typed lambda calculus, the type rules may superficially
resemble other lambda calculi. There are some quirks to observe.
The first is the variable typing rule:

<<
    Gamma |- A : B
  ------------------- (X_Var)
   Gamma, x:A |- x:A
>>

Although [X_Var] is semantically equivalent to the familiar rule,
this version allows us to introduce types (i.e., terms of the form [T:tau]).

*)

Reserved Notation "Gamma '|-' t 'esti' T" (at level 40).

Inductive has_type : context -> exp -> exp -> Prop :=
  | X_Var :
      forall (Gamma : context) (A B : exp),
      Gamma |- A esti B ->
      (cons A Gamma) |- (EVar (length Gamma)) esti (lift (length Gamma) A)
  | X_Abs :
      forall (Gamma : context) t1 t12 T,
      In t1 Gamma ->
      Gamma |- t12 esti T ->
      remove exp_eq_dec t1 Gamma |- ELam t1 t12 esti ELam t1 T
  | X_App :
      forall (Gamma : context) (t1 t12 T1 T12 : exp),
      Gamma |- t12 esti ELam T1 T12 ->
      Gamma |- t1 esti T1 ->
      Gamma |- EApp t12 t1 esti subst (length Gamma) t1 T12
  | X_Weak :
      forall (Gamma : context) (A B C D : exp),
      Gamma |- A esti B ->
      Gamma |- C esti D -> 
      cons C Gamma |- (lift (length Gamma) A) esti (lift (length Gamma) B)
 where "Gamma '|-' t 'esti' T" := (has_type Gamma t T).

Hint Constructors has_type.