Require Export Coq.Arith.EqNat.
Require Export Util.

(** * Lambda-typed lambda calculus.
*)

(**
Definition. The set [E] of lambda-expressions is
defined inductively as follows:

- [tau] is in [E]
- If [x] is a variable, then [x] is in [E]
- If [x] is a variable and [A], [B] is in [E],
  then [ELam (x:A).B] is in [E]
- If [A] and [B] are in [E],
  then [(A B)] is in [E].

We will use de Bruijn indices, so we'll have a number of
lemmas on lifting.
*)

Inductive exp : Type :=
 | tau : exp                 (* type constant *)
 | EVar : nat -> exp         (* de Bruijn index *)
 | ELam : exp -> exp -> exp  (* function abstraction *)
 | EApp : exp -> exp -> exp. (* function application *)
Hint Constructors exp.

(**
Equality between [exp] is decidable and may be used for conditional
statements in Coq.
*)
Definition exp_eq_dec : forall (A B:exp), {A = B} + {A <> B}.
Proof.
  intros.
  decide equality.
  decide equality.
Defined.

(**
Definition. A Context is inductively defined as

- The empty context
- If [Gamma] is a context, [T] a lambda-expression not present in
  [Gamma], and [x] is a free variable not present in [Gamma], then
  [Gamma, x:T] is a context.

We represent a context simply as a list of lambda-expressions,
since we're using de Bruijn indices.
*)

Definition context := list exp.

(**
We would like to check if a given context contains a variable.
Since variables are represented using de Bruijn indices, this amounts
to testing if the [nat] passed in is less than the length of the
context.
*)
Module Context.
Definition contains (c : context) (n : nat) : Prop := not (length c > n).
End Context.

(** ** Weak Normal Forms.

Expressions in weak normal form cannot be reduced further
from call-by-value evaluation.
*)

Inductive wnf : exp -> Prop :=
  | wnf_tau : wnf (tau)
  | wnf_EVar : forall (n:nat), wnf (EVar n)
  | wnf_ELam : forall (t b:exp), wnf (ELam t b).
Hint Constructors wnf.

(** Well formed expressions are closed under the given context *)
Fixpoint well_formed (Gamma:context) (x:exp) : Prop :=
  match x with
  | tau        => True
  | EVar n     => exists t, get n Gamma = Some t
  | ELam t b   => well_formed (t :: Gamma) b
  | EApp t1 t2 => (well_formed Gamma t1) /\ (well_formed Gamma t2)
  end.

(** * De Bruijn Indices

We use de Bruijn indices since, well, that appears to be convention.
The following functions are designed towards that end.
*)

(** The [d]-place shift of a term [t] above the cutoff [c]. *)
Fixpoint shift (d: nat) (* current binding depth *)
               (c: nat) (* cutoff *)
               (x: exp) (* expression containing references to lift *)
               : exp
:= match x with
 | tau        => x
 | EVar k     => if le_gt_dec c k
                 then EVar (k+d)
                 else x
 | ELam t b   => ELam t (shift d (S c) b)
 | EApp t1 t2 => EApp (shift d c t1) (shift d c t2)
end.

Definition lift (d: nat) (x:exp) : exp := shift d 0 x.

(* Unit tests for [lift] *)
Example lift_var_ex1:
  lift 1 (EVar 2) = EVar 3.
Proof.
  intuition.
Qed.

Example lift_lambda_ex1:
  lift 2 (ELam tau (ELam tau (EApp (EVar 1)
                                   (EApp (EVar 0)
                                         (EVar 2)))))
       = (ELam tau (ELam tau (EApp (EVar 1)
                                   (EApp (EVar 0)
                                         (EVar 4))))).
Proof.
  intuition.
Qed.


Example lift_lambda_ex2:
  lift 2 (ELam tau (EApp (EVar 0)
                         (EApp (EVar 1)
                               (ELam tau
                                     (EApp (EVar 0)
                                           (EApp (EVar 1)
                                                 (EVar 2)))))))
       = (ELam tau (EApp (EVar 0)
                         (EApp (EVar 3)
                               (ELam tau
                                     (EApp (EVar 0)
                                           (EApp (EVar 1)
                                                 (EVar 4))))))).
Proof.
  intuition.
Qed.

(**
 Definition. The substitution of a term [s] for a variable [j] in term [x]
 written [subst j s x] is:
 - [subst j s (EVar k) = s] if [j = k]
 - [subst j s (EVar k) = (EVar k)] if [j <> k]
 - [subst j s (ELam t b) = ELam (subst (S j) (lift 1 s) t) (subst (S j) (lift 1 s) b)]
 - [subst j s (EApp t1 t2) = EApp (subst j s t1) (subst j s t2)].

 Remark 1.
 Since we have lambda expressions also type the terms, we need to handle
 the case where the type of the lambda-abstraction parameter is really
 in the [context]. That is, we need to handle situations like
 [ELam (EVar 1) b], where [EVar 1] binds the variable to the first
 expression in the context stack.

 Remark 2.
 We sweep under the rug something "clever".
 Substitution, when applied to beta reduction, evaluates
 [EApp (ELam t b) v] to [lift -1 (subst 0 (lift 1 v) b)]. Since
 the first argument in [lift] must be a [nat], viz. non-negative,
 this naive approach to beta reduction would cause problems. The clever
 approach is to have substitution handle the [lift -1 ...] automatically.
*)
Fixpoint subst (j:nat) (* replace [j] *)
               (s:exp) (* with [s] *)
               (x:exp) (* in [t] *)
               : exp
:= match x with
 | tau        => x
 | EVar n     => match nat_compare n j with
                 | Eq => s
                 | Gt => EVar (n - 1)
                 | Lt => EVar n
                 end
 | ELam t b   => ELam (subst (S j) (lift 1 s) t) (subst (S j) (lift 1 s) b)
 | EApp t1 t2 => EApp (subst j s t1) (subst j s t2)
 end.

Example subst_ex1 :
  let (a, b) := (EVar 2, EVar 3)
  in
    (subst 2 b (EApp a
                     (ELam tau
                           (ELam tau
                                 (shift 2 2 a)))))
    = (EApp b
            (ELam tau
                  (ELam tau
                        (shift 2 2 b)))).
Proof.
  intuition.
Qed.

