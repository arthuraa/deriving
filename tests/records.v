From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From deriving Require Import deriving.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Record foo := Foo { foo1 : nat; foo2 : bool }.
Scheme foo_rect := Induction for foo Sort Type.

Definition foo_indDef := [indDef for foo_rect].
Canonical foo_indType := IndType foo foo_indDef.
Definition foo_hasDecEq := [derive hasDecEq for foo].
HB.instance Definition _ := foo_hasDecEq.
Definition foo_hasChoice := [derive hasChoice for foo].
HB.instance Definition _ := foo_hasChoice.
Definition foo_isCountable := [derive isCountable for foo].
HB.instance Definition _ := foo_isCountable.
Definition foo_isOrder := [derive isOrder for foo].
HB.instance Definition _ := foo_isOrder.
