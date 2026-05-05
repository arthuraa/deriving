(** Unit tests for [theories/lift_class.v].

    [arity_rec]'s reduction behaviour is exercised in practice by every
    deriving recipe in [theories/instances/], so the existing top-level
    tests already cover it.  We only test [fun_split] here, since the
    universe-polymorphic [arity_rec] is awkward to apply at abstract
    type without forcing universe instantiations the elaborator
    rejects. *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape lift_class.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

(** ** L1.  [fsE1] / [fsE2] of [fun_split1] are reflexive: the canonical
    splitter is the trivial one. *)

Lemma fsE1_canonical n R (f : fin n.+1 -> R) :
  fsE1 (fun_split1 f) = erefl.
Proof. by []. Qed.

Lemma fsE2_canonical n R (f : fin n.+1 -> R) i :
  fsE2 (fun_split1 f) i = erefl.
Proof. by []. Qed.

(** ** L2.  [fs_fun (fun_split1 f) = f]: the splitter recovers the
    original function. *)

Lemma fs_fun_canonical n R (f : fin n.+1 -> R) :
  fs_fun (fun_split1 f) = f.
Proof. by []. Qed.
