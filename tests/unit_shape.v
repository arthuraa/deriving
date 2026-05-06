(** Unit tests for [theories/shape.v].

    Each test pins down one piece of [shape.v] reduction behaviour
    against concrete, hand-written inputs, without going through any
    other [deriving] machinery (no [[indDef for ...]], no
    canonical-structure inference).

    Note: declarations have type [PolyType.seq (arity n)], not mathcomp's
    [seq], so list values must be built with [PolyType]'s constructors
    (or its [_ :: _] / [[:: x]] notations bound in [deriving_scope]). *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** ** [type_of_arg]: dispatch on [arg]. *)

Lemma type_of_arg_NonRec (T : fin 2 -> Type) (X : Type) :
  type_of_arg T (NonRec X) = X.
Proof. by []. Qed.

Lemma type_of_arg_Rec (T : fin 2 -> Type) (i : fin 2) :
  type_of_arg T (Rec i) = T i.
Proof. by []. Qed.

(** ** [type_of_arg_map]: identity on a [NonRec] argument; the supplied
    map [f] on a [Rec] argument. *)

Lemma type_of_arg_map_NonRec
  (T S : fin 2 -> Type) (f : T -F> S) (X : Type) (x : X) :
  type_of_arg_map f (A:=NonRec X) x = x.
Proof. by []. Qed.

Lemma type_of_arg_map_Rec
  (T S : fin 2 -> Type) (f : T -F> S) (i : fin 2) (x : T i) :
  type_of_arg_map f (A:=Rec i) x = f i x.
Proof. by []. Qed.

(** ** [is_rec]: trivially true on [Rec], false on [NonRec]. *)

Lemma is_rec_NonRec (X : Type) : @is_rec 2 (NonRec X) = false.
Proof. by []. Qed.

Lemma is_rec_Rec (i : fin 2) : is_rec (Rec i) = true.
Proof. by []. Qed.

(** ** [add_arity] on [empty_decl] places the new arity at the requested
    index and leaves other indices empty. *)

Lemma add_arity_empty_at (As : arity 2) :
  add_arity (@empty_decl 2) None As None =
  PolyType.cons As PolyType.nil.
Proof. by []. Qed.

Lemma add_arity_empty_other (As : arity 2) :
  add_arity (@empty_decl 2) None As (Some None) = PolyType.nil.
Proof. by []. Qed.

(** ** Two [add_arity] consings stack: at the shared index, both arities
    are present (most-recently-added at the head); at a different index
    only the matching one is. *)

Lemma add_arity_stack_head (As Bs : arity 2) :
  add_arity (add_arity (@empty_decl 2) None As) None Bs None =
  PolyType.cons Bs (PolyType.cons As PolyType.nil).
Proof. by []. Qed.

Lemma add_arity_stack_skew (As Bs : arity 2) :
  add_arity (add_arity (@empty_decl 2) None As) (Some None) Bs (Some None) =
  PolyType.cons Bs PolyType.nil.
Proof. by []. Qed.

(** ** [add_arity_ind]: dispatches on whether the matched index [j]
    coincides with the freshly-added index [i].  We pick a [P] that
    extracts the resulting signature's head, so the two branches are
    visibly distinct. *)

Lemma add_arity_ind_match (D : declaration 2) (As : arity 2) :
  add_arity_ind (fun _ _ => arity 2)
                D None As None
                (* head case (i = j) *)  As
                (* skew case (unused) *) PolyType.nil =
  As.
Proof. by []. Qed.

Lemma add_arity_ind_skew (D : declaration 2) (As Bs : arity 2) :
  add_arity_ind (fun _ _ => arity 2)
                D None As (Some None)
                (* head case (unused) *)  PolyType.nil
                (* skew case (returned) *) Bs =
  Bs.
Proof. by []. Qed.
