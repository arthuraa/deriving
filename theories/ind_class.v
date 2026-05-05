(** * Bundled [indType] + MathComp class

    For each MathComp class [C] (currently [Equality], [Choice],
    [Countable]) there is a sister class [IndCType] that bundles an
    [Ind.Def.class_of] (a mutual block of inductive types) with a
    per-index [C] instance.  These are used by the deriving recipes
    (e.g. [DerOrderType] in [theories/instances/order.v]) so that an
    instance derivation can locate the relevant MathComp class for each
    inductive in the block at the same time as the [indDef].

    The [HB.instance] declarations after each [Pack] register the
    per-index class as the canonical structure for [sorts i], so that
    user code can mention [(_ : eqType)] / [(_ : choiceType)] /
    [(_ : countType)] anywhere a sort would appear and have it resolved. *)

From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Set SsrOldRewriteGoalsOrder.

From deriving Require Import base shape ind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Backwards compatibility for hint locality attributes *)
Set Warnings "-unsupported-attributes".

Open Scope deriving_scope.

(** ** [indEqType]: an [indDef] whose every sort has decidable equality *)

Module IndEqType.

Record type := Pack {
  n         : nat;
  sorts     : fin n -> Type;
  decl      : declaration n;
  eq_class  : forall i, Equality (sorts i);
  ind_class : Ind.Def.class_of sorts decl;
}.

Definition indDef T := Ind.Def.Pack (ind_class T).

Module Import Exports.
Notation indEqType := type.
Notation IndEqType := Pack.
Coercion sorts : type >-> Funclass.
Coercion indDef : type >-> Ind.Def.type.
Canonical indDef.
End Exports.

End IndEqType.

Export IndEqType.Exports.

Section IndEqTypeInstances.
Variables (T : indEqType) (i : fin (IndEqType.n T)).
HB.instance Definition indEqType_eqType := IndEqType.eq_class i.
End IndEqTypeInstances.

#[global]
Hint Unfold IndEqType.n : deriving.
#[global]
Hint Unfold IndEqType.sorts : deriving.
#[global]
Hint Unfold IndEqType.decl : deriving.
#[global]
Hint Unfold IndEqType.eq_class : deriving.
#[global]
Hint Unfold IndEqType.ind_class : deriving.
#[global]
Hint Unfold IndEqType.indDef : deriving.

(** ** [indChoiceType]: an [indDef] whose every sort has [Choice] *)

Module IndChoiceType.

Record type := Pack {
  n            : nat;
  sorts        : fin n -> Type;
  decl         : declaration n;
  choice_class : forall i, Choice (sorts i);
  ind_class    : Ind.Def.class_of sorts decl;
}.

Definition indDef T := Ind.Def.Pack (ind_class T).

Module Import Exports.
Notation indChoiceType := type.
Notation IndChoiceType := Pack.
Coercion sorts : type >-> Funclass.
Coercion indDef : type >-> Ind.Def.type.
Canonical indDef.
End Exports.

End IndChoiceType.

Export IndChoiceType.Exports.

#[global]
Hint Unfold IndChoiceType.n : deriving.
#[global]
Hint Unfold IndChoiceType.sorts : deriving.
#[global]
Hint Unfold IndChoiceType.decl : deriving.
#[global]
Hint Unfold IndChoiceType.choice_class : deriving.
#[global]
Hint Unfold IndChoiceType.ind_class : deriving.
#[global]
Hint Unfold IndChoiceType.indDef : deriving.

Section IndChoiceTypeInstances.
Variables (T : indChoiceType) (i : fin (IndChoiceType.n T)).
HB.instance Definition _ := IndChoiceType.choice_class i.
End IndChoiceTypeInstances.

(** ** [indCountType]: an [indDef] whose every sort has [Countable] *)

Module IndCountType.

Record type := Pack {
  n           : nat;
  sorts       : fin n -> Type;
  decl        : declaration n;
  count_class : forall i, Countable (sorts i);
  ind_class   : Ind.Def.class_of sorts decl;
}.

Definition indDef T := Ind.Def.Pack (ind_class T).

Module Import Exports.
Notation indCountType := type.
Notation IndCountType := Pack.
Coercion sorts : type >-> Funclass.
Coercion indDef : type >-> Ind.Def.type.
Canonical indDef.
End Exports.

End IndCountType.

Export IndCountType.Exports.

Section IndCountTypeInstances.
Variables (T : indCountType) (i : fin (IndCountType.n T)).
HB.instance Definition _ := IndCountType.count_class i.
End IndCountTypeInstances.

#[global]
Hint Unfold IndCountType.n : deriving.
#[global]
Hint Unfold IndCountType.sorts : deriving.
#[global]
Hint Unfold IndCountType.decl : deriving.
#[global]
Hint Unfold IndCountType.count_class : deriving.
#[global]
Hint Unfold IndCountType.ind_class : deriving.
#[global]
Hint Unfold IndCountType.indDef : deriving.
