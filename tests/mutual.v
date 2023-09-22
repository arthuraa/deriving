From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Elimination Schemes.
Inductive foo :=
| Foo1 of nat
| Foo2 of bool & bar

with bar :=
| Bar1 of foo & foo
| Bar2 of nat & foo

with baz :=
| Baz of foo & baz.
Set Elimination Schemes.

Scheme foo_rect := Induction for foo Sort Type
with   bar_rect := Induction for bar Sort Type
with   baz_rect := Induction for baz Sort Type.

Combined Scheme foo_bar_baz_rect from foo_rect, bar_rect, baz_rect.

Definition foo_bar_baz_indDef := [indDef for foo_bar_baz_rect].
Canonical foo_indType := IndType foo foo_bar_baz_indDef.
Canonical bar_indType := IndType bar foo_bar_baz_indDef.
Canonical baz_indType := IndType baz foo_bar_baz_indDef.

(* FIXME: Why aren't the recursors being simplified away here? *)
Definition foo_hasDecEq := [derive hasDecEq for foo].
HB.instance Definition _ := foo_hasDecEq.
Definition bar_hasDecEq := [derive hasDecEq for bar].
HB.instance Definition _ := bar_hasDecEq.
Definition baz_hasDecEq := [derive hasDecEq for baz].
HB.instance Definition _ := baz_hasDecEq.
Definition foo_hasChoice := [derive hasChoice for foo].
HB.instance Definition _ := foo_hasChoice.
Definition bar_hasChoice := [derive hasChoice for bar].
HB.instance Definition _ := bar_hasChoice.
Definition baz_hasChoice := [derive hasChoice for baz].
HB.instance Definition _ := baz_hasChoice.
Definition foo_isCountable := [derive isCountable for foo].
HB.instance Definition _ := foo_isCountable.
Definition bar_isCountable := [derive isCountable for bar].
HB.instance Definition _ := bar_isCountable.
Definition baz_isCountable := [derive isCountable for baz].
HB.instance Definition _ := baz_isCountable.
(* FIXME: Why aren't the recursors being simplified away here? *)
Definition foo_isOrder := [derive isOrder for foo].
HB.instance Definition _ := foo_isOrder.
Definition bar_isOrder := [derive isOrder for bar].
HB.instance Definition _ := bar_isOrder.
Definition baz_isOrder := [derive isOrder for baz].
HB.instance Definition _ := baz_isOrder.
