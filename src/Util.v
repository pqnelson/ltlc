Require Import String.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Arith.EqNat.

(* Add a single element to the end of the list *)
Fixpoint snoc {A: Type} (x: A) (xx: list A) : list A :=
 match xx with 
 | nil       => x :: nil
 | y :: xs'  => y :: snoc x xs'
 end.

(* Get an indexed element from a list, starting from 0.
   This is like the Coq 'nth' function, but returns an option instead
   of a provided default value. Using an option is useful when we simply
   want to determine whether some element is in the list, but don't
   need the actual value *)
Fixpoint get {A: Type} (i: nat) (e: list A) {struct e}: option A :=
 match e, i with
 | x :: _,  O     => Some x
 | _ :: xs, S i'  => get  i' xs
 | _, _           => None
 end.

(** Remove all instances of a given string [s] from a list of strings [l]. *)
Fixpoint rm (s:string) (l:list string) :=
  match l with
  | nil => nil
  | y::tl => if (string_dec s y) then tl else y::(rm s tl)
  end.

Fixpoint is_in (s:string) (l:list string) : bool :=
  match l with
  | nil => false
  | x::tl => if (string_dec x s) then true else is_in s tl
  end.

Fixpoint append (l1:list string) (l2:list string) : list string :=
  match l2 with
  | nil => l1
  | x::tl => append (if is_in x l1 then l1 else snoc x l1) tl
  end.

Open Scope string_scope.
Example append_ex1 :
  append (cons "a" (cons "b" nil))
         (cons "x" (cons "y" nil))
   = "a" :: "b" :: "x" :: "y" :: nil.
Proof. reflexivity. Qed.
Close Scope string_scope.