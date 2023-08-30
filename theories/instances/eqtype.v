From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics infer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Module DerEqType.

Section EqType.

Variable T : indDef.
Notation n := (Ind.Def.n T).
Local Notation arg_class := (@arg_class n _ Equality.sort).
Local Notation arg_inst := (arg_inst n Equality.sort).
Local Notation arity_inst := (arity_inst n Equality.sort).
Local Notation sig_inst := (sig_inst n Equality.sort).
Local Notation decl_inst := (decl_inst n Equality.sort n).
Variable (sT : forall i, sig_class Equality.sort (Ind.Def.decl T i)).

Import IndF.

Definition eq_op_branch As (cAs : hlist' arg_class As) :
  hlist' (type_of_arg (T *F (fun i => T i -> bool))) As ->
  hlist' (type_of_arg T)                             As ->
  bool                                                  ->
  bool :=
  arity_rec _ (fun As => hlist' _ As -> hlist' _ As -> bool -> bool)
    (fun _ _ b => b)
    (fun R As rec x y b => rec x.(tl) y.(tl) (b && (x.(hd) == y.(hd))))
    (fun j As rec x y b => rec x.(tl) y.(tl) (b &&  x.(hd).2 y.(hd)))
    As cAs.

(* FIXME: Do we really need these annotations? *)
Definition eq_op : forall i, T i -> T i -> bool :=
  rec  (fun i args1 =>
  case (fun   args2 =>
     match leq_fin (constr args2) (constr args1) with
      | inl e =>
        eq_op_branch
          (hnth (sT i) (constr args1))
          (args args1)
          (cast (hlist' (type_of_arg T) \o @nth_fin _ _) e (args args2))
          true
      | inr _ => false
      end)).

Lemma eq_opP i : Equality.axiom (@eq_op i).
Proof.
elim/indP: i / => i [xC xargs] y.
rewrite /eq_op recE /= -/eq_op /=.
rewrite -[y]unrollK caseE; move: {y} (unroll y)=> [yC yargs] /=.
case le: (leq_fin yC xC)=> [e|b]; last first.
  constructor=> /Roll_inj /= [] e _.
  by move: le; rewrite e leq_finii.
case: xC / e xargs {le} => /= xargs.
apply/(@iffP (hmap' (type_of_arg_map (fun=> tag)) xargs = yargs)); first last.
- by move=> /Roll_inj /IndF.inj.
- by move=> <-.
apply/(iffP idP)=> [H|<-]; last first.
  elim/arity_ind: {yC} _ / (hnth _ _) xargs {yargs}=> //= [|j] S As cAs.
    move=> /= IH [x xargs]; rewrite /= eqxx; exact: IH.
  move=> [[x xP] xargs] /=; rewrite (introT (xP _)) //; exact: cAs.
suffices [//]: true /\ hmap' (type_of_arg_map (fun=> tag)) xargs = yargs.
elim/arity_ind: {yC} _ / (hnth _ _) xargs yargs true H.
- by move=> [] [].
- move=> S As cAs IH /= [x xargs] [y yargs] /= b /IH.
  by case=> /andP [-> /eqP <-] <-.
- move=> j As cAs /= IH [[x xP] xargs] [y yargs] /= b /IH.
  by case=> /andP [-> /xP <-] <-.
Qed.

End EqType.

Definition pack (T : Type) :=
  [infer indType of T with Equality.sort as sT n sorts D cD in
   cast (fun A => Equality.mixin_of A) (Ind.idxE sT)^-1
    (hasDecEq.Axioms_ _ (@eq_opP sT cD (Ind.idx sT)))].

End DerEqType.

Notation "[ 'derive' 'nored' 'eqMixin' 'for' T ]" :=
  (@DerEqType.pack T _ id _ _ _ _ _ _ id _ id _ id)
  (at level 0) : form_scope.

Ltac derive_eqMixin T :=
  match eval hnf in [derive nored eqMixin for T] with
  | @hasDecEq.Axioms_ _ ?op ?opP =>
    let op := eval unfold DerEqType.eq_op, DerEqType.eq_op_branch in op in
    let op := eval deriving_compute in op in
    exact (@hasDecEq.Axioms_ T op opP)
  end.

Notation "[ 'derive' 'eqMixin' 'for' T ]" :=
  (ltac:(derive_eqMixin T))
  (at level 0) : form_scope.

Ltac derive_lazy_eqMixin T :=
  match eval hnf in [derive nored eqMixin for T] with
  | @hasDecEq.Axioms_ _ ?op ?opP =>
    let op := eval unfold DerEqType.eq_op, DerEqType.eq_op_branch in op in
    let op := eval deriving_lazy in op in
    exact (@hasDecEq.Axioms_ T op opP)
  end.

Notation "[ 'derive' 'lazy' 'eqMixin' 'for' T ]" :=
  (ltac:(derive_lazy_eqMixin T))
  (at level 0) : form_scope.
