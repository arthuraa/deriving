From HB Require Import structures.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finset order.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Elimination Schemes.
Inductive rose := Rose of seq rose.
Set Elimination Schemes.

Definition rose_rect
  (P1 : rose -> Type)
  (P2 : seq rose -> Type)
  (HR : forall rs, P2 rs -> P1 (Rose rs))
  (HN : P2 [::])
  (HC : forall r, P1 r -> forall rs, P2 rs -> P2 (r :: rs))
  : forall r, P1 r :=
  fix rose_rect r :=
    let fix seq_rose_rect rs : P2 rs :=
        match rs with
        | [::] => HN
        | r :: rs => HC r (rose_rect r) rs (seq_rose_rect rs)
        end in
    match r with Rose rs => HR rs (seq_rose_rect rs) end.

Definition seq_rose_rect
  (P1 : rose -> Type)
  (P2 : seq rose -> Type)
  (HR : forall rs, P2 rs -> P1 (Rose rs))
  (HN : P2 [::])
  (HC : forall r, P1 r -> forall rs, P2 rs -> P2 (r :: rs))
  : forall rs, P2 rs :=
    fix seq_rose_rect rs : P2 rs :=
      match rs with
      | [::] => HN
      | r :: rs => HC r (rose_rect HR HN HC r) rs (seq_rose_rect rs)
      end.

Combined Scheme rose_seq_rose_rect from rose_rect, seq_rose_rect.

Definition rose_seq_rose_indDef := [indDef for rose_seq_rose_rect].
Canonical rose_indType := IndType rose rose_seq_rose_indDef.
Definition rose_eqMixin := [derive eqMixin for rose].
HB.instance Definition _ := rose_eqMixin.
Definition rose_choiceMixin := [derive choiceMixin for rose].
HB.instance Definition _ := rose_choiceMixin.
Definition rose_countMixin := [derive countMixin for rose].
HB.instance Definition _ := rose_countMixin.
Definition rose_orderMixin := [derive orderMixin for rose].
HB.instance Definition _ := rose_orderMixin.
