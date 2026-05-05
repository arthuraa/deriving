(** * Shape of (mutually recursive) inductive types

    This file defines the data types that describe the *syntactic shape* of
    one or more mutually recursive inductive types: the kinds of arguments
    a constructor can take, the arity of one constructor, the signature of
    one inductive type, and the joint declaration of a mutual block.  No
    typeclass content appears here — these definitions describe shape only.

    The deriving framework parametrises everything by a number of types
    [n : nat] and a family [T : fin n -> Type] giving the carrier of each.
    A [declaration n] then specifies, for each [i : fin n], the list of
    argument lists of the constructors of the inductive type at index [i].

    See [lift_class.v] for the corresponding class-decorated views and
    [ind.v] for the recursor / destructor primitives that consume a
    declaration. *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Backwards compatibility for hint locality attributes *)
Set Warnings "-unsupported-attributes".

Open Scope deriving_scope.

(** ** Notational shortcuts for indexed type families

    [T -F> S] is a function between two [fin n]-indexed type families,
    pointwise.  [T *F S] is the pointwise product.  Both are used
    pervasively as parameters of the deriving combinators. *)

Notation "T -F> S" :=
  (forall i, T i -> S i)
  (at level 30, only parsing, no associativity)
  : deriving_scope.

Notation "T *F S"  :=
  (fun i => T i * S i)%type
  (at level 20, only parsing, no associativity)
  : deriving_scope.

Set Universe Polymorphism.

Section Shape.

Import PolyType.

Variable n : nat.
Implicit Types (T S : fin n -> Type).

(** ** Constructor arguments

    Every constructor argument is either a non-recursive type or a recursive
    reference to one of the [n] types in the mutual block.  The reason to
    use a tagged sum [arg] rather than spelling out [T_i] directly is that
    the same [arg] is reused with different carrier families: [T] for
    interpreting an argument as a value, and [T *F S] in the body of a
    recursor branch (which receives both the recursive subterm and the
    result of recursion). *)

Variant arg := NonRec of Type | Rec of fin n.

Definition type_of_arg T (A : arg) : Type :=
  match A with
  | NonRec X => X
  | Rec i    => T i
  end.

Definition type_of_arg_map T S (f : T -F> S) A :
  type_of_arg T A -> type_of_arg S A :=
  match A with
  | NonRec X => id
  | Rec i    => f i
  end.

Definition is_rec A := if A is Rec _ then true else false.

(** ** Arities, signatures, declarations

    An [arity] is the list of arguments of one constructor.  A [signature]
    is the list of arities (one per constructor) of one inductive type.  A
    [declaration] gives the signature of each of the [n] types in a mutual
    block. *)

Definition arity        := seq arg.
Definition signature    := seq arity.
Definition declaration  := fin n -> signature.

Identity Coercion seq_of_arity : arity >-> seq.
Identity Coercion seq_of_sig   : signature >-> seq.

(** [empty_decl] is the empty declaration: every type has zero
    constructors.  [add_arity D i As] extends [D] by adding a constructor
    with argument list [As] to type [i]; the other types are unchanged.
    Together they let one build up a declaration constructor by
    constructor. *)

Definition empty_decl : declaration :=
  fun _ => [::].

Definition add_arity (D : declaration) i As : declaration :=
  fun j => if leq_fin i j is inl _ then As :: D i
           else D j.

(** [add_arity_ind] is the matching induction principle for [add_arity]:
    knowing how to construct [P i (As :: D i)] (the freshly-added
    constructor case at index [i]) and [P j (D j)] (any other index, where
    [D] is unchanged), we get [P j (add_arity D i As j)] for any [j].  This
    is the workhorse used by [Ind.add_cons] and other "consing" lemmas. *)

Definition add_arity_ind (P : fin n -> signature -> Type) D i As j :
  P i (As :: D i) -> P j (D j) -> P j (add_arity D i As j) :=
  fun H1 H2 =>
    match leq_fin i j
    as X
    return P j (if X is inl _ then As :: D i else D j) with
    | inl e => cast (fun k => P k (As :: D i)) e H1
    | inr _ => H2
    end.

End Shape.

Unset Universe Polymorphism.

Arguments NonRec        {n} _.
Arguments Rec           {n} _.
Arguments add_arity_ind {n} P D i As j H1 H2.
Arguments empty_decl    {n}.

#[global]
Hint Unfold type_of_arg : deriving.
#[global]
Hint Unfold type_of_arg_map : deriving.
#[global]
Hint Unfold is_rec : deriving.
#[global]
Hint Unfold arity : deriving.
#[global]
Hint Unfold signature : deriving.
#[global]
Hint Unfold declaration : deriving.
#[global]
Hint Unfold empty_decl : deriving.
#[global]
Hint Unfold add_arity : deriving.
#[global]
Hint Unfold add_arity_ind : deriving.
