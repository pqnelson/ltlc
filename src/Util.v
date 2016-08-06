Require Import String.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Arith.EqNat.

(* Add a single element to the end of the list *)
Fixpoint snoc {A : Type} (x : A) (xx : list A): list A :=
  match xx with
  | nil => x :: nil
  | y :: xs' => y :: snoc x xs'
  end.

(* Get an indexed element from a list, starting from 0.
   This is like the Coq 'nth' function, but returns an option instead
   of a provided default value. Using an option is useful when we simply
   want to determine whether some element is in the list, but don't
   need the actual value *)
Fixpoint get {A : Type} (i : nat) (e : list A) {struct e}: 
option A :=
  match e, i with
  | x :: _, O => Some x
  | _ :: xs, S i' => get i' xs
  | _, _ => None
  end.

(** Remove all instances of a given string [s] from a list of strings [l]. *)
Definition rm (s : string) (l : list string) := remove string_dec s l.

Fixpoint is_in (s : string) (l : list string): bool :=
  match l with
  | nil => false
  | x :: rest => if string_dec s x then true else is_in s rest
  end.

(** Appends [l2] to [l1] removing duplicates from [l2]. *)
Fixpoint append (l1 : list string) (l2 : list string): 
list string :=
  match l2 with
  | nil => l1
  | x :: tl2 => append (if is_in x l1 then l1 else snoc x l1) tl2
  end.

Open Scope string_scope.
Example append_ex1 :
  append (cons "a" (cons "b" nil)) (cons "x" (cons "y" nil)) =
  "a" :: "b" :: "x" :: "y" :: nil.
Proof. reflexivity. Qed.

Example append_ex2 :
  append (cons "a" (cons "b" nil)) (cons "x" (cons "b" nil)) =
  "a" :: "b" :: "x" :: nil.
Proof. reflexivity. Qed.

Example append_ex3 :
  append (cons "a" (cons "b" nil)) (cons "a" (cons "y" nil)) =
  "a" :: "b" :: "y" :: nil.
Proof. reflexivity. Qed.
Close Scope string_scope.



Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H:_ |- _ => try move x after H
  end.

Tactic Notation
  "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity; clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(**
Binary relation utilities, specifically the [multi] closure of a relation.
*)
Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X : Type) (R : relation X) : X -> X -> Prop :=
  | multi_refl : forall x : X, multi X R x x
  | multi_step : forall x y z : X, R x y -> multi X R y z -> multi X R x z.
Implicit Arguments  multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R :
 forall (X : Type) (R : relation X) (x y : X), R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
 forall (X : Type) (R : relation X) (x y z : X),
 multi R x y -> multi R y z -> multi R x z.
Proof.
  intuition.
  induction H.
  - assumption.
  - apply multi_step with y. assumption.
    apply IHmulti. assumption. 
Qed.