From HB Require Import structures.
From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

(* Compatibility layer for Order.disp_t introduced in MathComp 2.3            *)
(* TODO: remove when we drop the support for MathComp 2.2                     *)
Module Order.
Import Order.
Definition disp_t : Set.
Proof. exact: disp_t || exact: unit. Defined.
Definition default_display : disp_t.
Proof. exact: tt || exact: Disp tt tt. Defined.
End Order.
