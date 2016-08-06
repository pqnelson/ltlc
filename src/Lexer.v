(**
This just transforms "pretty print" notation to internal
de Bruijn indices. It's probably the most involved code
that has the least to do with the actual type theoretic
machinery.
*)
Require Import String.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Arith.EqNat.
Require Export Util.
Require Import Expression.

(** 
For denaming some pretty-printed lambda expression into our
internal representation.
*)
Module PrettyTerm.
Inductive pterm : Type :=
 | tau : pterm
 | Var : string -> pterm
 | Lam : string -> pterm -> pterm -> pterm
 | App : pterm -> pterm -> pterm.

(** The free variables in a given [pterm]. *)
Fixpoint FV (t:pterm): list string :=
  match t with
  | tau => nil
  | Var s => s::nil
  | Lam x t b => rm x (append (FV t) (FV b))
  | App t1 t2 => append (FV t1) (FV t2)
  end.

(** A [context] for pretty print reasons is a list of
declarations, which themselves are ordered pairs of a 
[string] identifier, and its corresponding [pterm] "type".
*)
Definition context := list (string * pterm).
End PrettyTerm.

Notation "` x" := (if string_dec x "tau"
                   then PrettyTerm.tau
                   else PrettyTerm.Var x) (at level 20).
Notation "\ x t ~> M" := (PrettyTerm.Lam x t M) (at level 30).
Infix "$" := PrettyTerm.App (at level 25, left associativity).

(* Unit tests for [FV] *)
Example FV_ex1 :
  PrettyTerm.FV (`"f" $ `"g" $ `"h" $ `"i") =
  "f"%string :: "g"%string :: "h"%string :: "i"%string :: nil.
Proof. reflexivity. Qed.

Example prettier_left_assoc_ex1 :
  `"f" $ `"g" $ `"h" $ `"i" =
  PrettyTerm.App
    (PrettyTerm.App
       (PrettyTerm.App (PrettyTerm.Var "f") (PrettyTerm.Var "g"))
       (PrettyTerm.Var "h")) (PrettyTerm.Var "i").
Proof.
  simpl. reflexivity.
Qed.

Example prettier_ex2 :
  \ "f" `"tau" ~> `"f" $ (\ "x" `"tau" ~> `"x" $ `"y") =
  PrettyTerm.Lam "f" PrettyTerm.tau
    (PrettyTerm.App (PrettyTerm.Var "f")
       (PrettyTerm.Lam "x" PrettyTerm.tau
          (PrettyTerm.App (PrettyTerm.Var "x") (PrettyTerm.Var "y")))).
Proof. simpl. reflexivity. Qed.

Fixpoint lookup (s : string) (ls : list (string * nat)): 
option nat :=
  match ls with
  | nil => None
  | (x, n) :: t => if string_dec x s then Some n else lookup s t
  end.

(** Pushes the depth one layer, introduces a "new" variable [s]. *)
Fixpoint hide (s : string) (ls : list (string * nat)): 
list (string * nat) :=
  match ls with
  | nil => (s, 0) :: nil
  | (x, n) :: t =>
      if string_dec x s then (x, 0) :: hide s t else (x, n + 1) :: hide s t
  end.

Fixpoint dename' (t : PrettyTerm.pterm) (binds : list (string * nat)): exp :=
  match t with
  | PrettyTerm.tau => tau
  | PrettyTerm.Var s =>
      match lookup s binds with
      | Some n => EVar n
      | None => EVar 0
      end
  | PrettyTerm.Lam s t b =>
      ELam (dename' t (hide s binds)) (dename' b (hide s binds))
  | PrettyTerm.App t1 t2 => EApp (dename' t1 binds) (dename' t2 binds)
  end.

(** Given a list [identifiers] of free variables, and a list [binds] of
    binds to de Bruijn indices, update it adding values for the free variables. *)
Fixpoint FV_binds (identifiers : list string) (binds : list (string * nat)):
list (string * nat) :=
  match identifiers with
  | nil => binds
  | x :: tl =>
      match lookup x binds with
      | Some n => FV_binds tl binds
      | None => FV_binds tl (cons (x, length binds) binds)
      end
  end.

Fixpoint context_binds' (Gamma : PrettyTerm.context)
(binds : list (string * nat)): list (string * nat) :=
  match Gamma with
  | nil => binds
  | (x, _) :: tl =>
      match lookup x binds with
      | Some n => context_binds' tl binds
      | None => context_binds' tl (cons (x, length binds) binds)
      end
  end.

(** Given a [context Gamma = (xN,type_N), ..., (x1, type_1)] produce a lookup
    map for the variables and identifiers to convert to de Bruijn indices. *)
Definition context_binds (Gamma : PrettyTerm.context) :
  list (string * nat) := context_binds' (rev Gamma) nil.

(* Unit tests for the [context_binds] *)
Open Scope string_scope.
Example context_binds_ex1 :
  context_binds (cons ("f", PrettyTerm.tau) nil) = ("f", 0) :: nil.
Proof.
  reflexivity.
Qed.

Example context_binds_ex2 :
  context_binds
    (cons ("f", PrettyTerm.tau)
       (cons ("g", PrettyTerm.tau) (cons ("f", PrettyTerm.tau) nil))) =
  ("g", 1) :: ("f", 0) :: nil.
Proof.
  reflexivity.
Qed.

Example fv_binds_context_binds_ex1 :
  FV_binds (PrettyTerm.FV (`"f" $ `"g" $ `"f"))
    (context_binds (cons ("g", PrettyTerm.tau) nil)) =
  ("f", 1) :: ("g", 0) :: nil.
Proof.
  reflexivity.
Qed.
Close Scope string_scope.

(** Given a [PrettyTerm.pterm] without a [context], convert it
    into a [exp] using de Bruijn indices. *)
Definition dename (t : PrettyTerm.pterm) : exp :=
  dename' t (FV_binds (PrettyTerm.FV t) nil).

(** If we have a given [context Gamma], then we want to convert it into
    a [list exp] which binds to de Bruijn indices. *)
Fixpoint deconstruct_context (c : PrettyTerm.context)
(binds : list (string * nat)): list exp :=
  match c with
  | nil => nil
  | (x, t) :: ctxt => cons (dename' t binds) (deconstruct_context ctxt binds)
  end.

(** Claim: Let [c = f : tau, h : \g:tau~>f], then
    [deconstruct_context c (context_binds c) = Elam tau f :: tau].
*)
Example deconstruct_context_ex1 :
  let c :=
    snoc ("f"%string, `"tau") (cons ("h"%string, \ "g" `"tau" ~> `"f") nil) in
  deconstruct_context c (context_binds c) = ELam tau (EVar 1) :: tau :: nil.
Proof. reflexivity. Qed.

(** Claim: Let [c = h : \g:tau~>f, g : tau, f : tau], then
    [deconstruct_context c (context_binds c) = Elam tau f :: tau :: tau].
*)
Example deconstruct_context_ex2 :
  let c :=
    snoc ("f"%string, `"tau")
      (snoc ("g"%string, `"tau") (cons ("h"%string, \ "x" `"g" ~> `"f") nil)) in
  deconstruct_context c (context_binds c) =
  ELam (EVar 2) (EVar 1) :: tau :: tau :: nil.
Proof. reflexivity. Qed.

(** Convert a [PrettyTerm.pterm] in a given [PrettyTerm.context] to
    a pair [context, exp] using de Bruijn indices. Free Variables are
    handled properly.
*)
Definition dename_with_context (c : PrettyTerm.context)
  (t : PrettyTerm.pterm) : context * exp :=
  let binds := FV_binds (PrettyTerm.FV t) (context_binds c) in
  (deconstruct_context c binds, dename' t binds).

(* Unit tests for [dename_with_context] *)
Open Scope string_scope.
Example dename_with_context_ex1 :
  dename_with_context (cons ("g", PrettyTerm.tau) nil) (`"f" $ `"g" $ `"f") =
  (tau :: nil, EApp (EApp (EVar 1) (EVar 0)) (EVar 1)).
Proof.
  reflexivity.
Qed.

Example dename_ex1 :
  dename (`"f" $ `"g" $ `"f") = EApp (EApp (EVar 0) (EVar 1)) (EVar 0).
Proof.
  reflexivity.
Qed.
Close Scope string_scope.