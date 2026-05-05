(** Unit tests for [theories/shape.v].

    These tests pin down the reduction behaviour of [add_arity]: the
    freshly-added arity lands at the requested index, the other indices
    are unchanged.

    Note: declarations have type [PolyType.seq (arity n)], not mathcomp's
    [seq], so list values must be built with [PolyType]'s constructors
    (or its [_ :: _] / [[:: x]] notations bound in [deriving_scope] —
    but only when [PolyType] is the most recently [Import]ed module
    contributing those names).  We use the qualified [PolyType.cons] /
    [PolyType.nil] forms for clarity. *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

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
    are present (most-recently-added at the head). *)

Lemma add_arity_stack_head (As Bs : arity 2) :
  add_arity (add_arity (@empty_decl 2) None As) None Bs None =
  PolyType.cons Bs (PolyType.cons As PolyType.nil).
Proof. by []. Qed.

Lemma add_arity_stack_skew (As Bs : arity 2) :
  add_arity (add_arity (@empty_decl 2) None As) (Some None) Bs (Some None) =
  PolyType.cons Bs PolyType.nil.
Proof. by []. Qed.
