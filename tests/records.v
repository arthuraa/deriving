From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.

Record foo := Foo { foo1 : nat; foo2 : bool }.
Scheme foo_rect := Induction for foo Sort Type.

Definition foo_indDef := [indDef for foo_rect].
Canonical foo_indType := IndType foo foo_indDef.
Definition foo_eqMixin := [derive eqMixin for foo].
HB.instance Definition _ := foo_eqMixin.
Definition foo_choiceMixin := [derive choiceMixin for foo].
HB.instance Definition _ := foo_choiceMixin.
Definition foo_countMixin := [derive countMixin for foo].
HB.instance Definition _ := foo_countMixin.
