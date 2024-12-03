From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics infer compat.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Module DerOrderType.
Section DerOrderType.

Import Order.Total Order.Theory.

Record packedOrderType := Pack {
  disp : Order.disp_t;
  sort : orderType disp;
}.

Section Def.

Variable (T : indChoiceType).
Notation n := (Ind.Def.n T).
Notation D := (Ind.Def.decl T).
Notation arg_class  := (arg_class  sort).
Notation arg_inst   := (arg_inst   n sort).
Notation arity_inst := (arity_inst n sort).
Notation sig_inst   := (sig_inst   n sort).
Notation decl_inst  := (decl_inst  n sort).
Variable (sT : forall i, sig_class sort (D i)).

Import IndF.

Definition le_branch As (cAs : hlist' arg_class As) :
  hlist' (type_of_arg (T *F (fun i => T i -> bool))) As ->
  hlist' (type_of_arg T)                             As ->
  bool :=
  @arity_rec
    _ _ _
   (fun a => hlist' (type_of_arg (T *F (fun i => T i -> bool))) a ->
             hlist' (type_of_arg T) a ->
             bool)
    (fun _ _ => true)
    (fun R As rec x y =>
       if x.(hd) == y.(hd) then rec x.(tl) y.(tl) else (x.(hd) <= y.(hd))%O)
    (fun j As rec x y =>
       if x.(hd).1 == y.(hd) then rec x.(tl) y.(tl) else x.(hd).2 y.(hd)) As cAs.

Definition le : forall i, T i -> T i -> bool :=
  rec  (fun i args1 =>
  case (fun   args2 =>
          match leq_fin (constr args2) (constr args1) with
          | inl e =>
            le_branch
              (hnth (sT i) (constr args1))
              (args args1)
              (cast (hlist' (type_of_arg T) \o @nth_fin _ _) e (args args2))
          | inr b => ~~ b
          end)).

Lemma refl i : reflexive (@le i).
Proof.
elim/indP: i / => i [j args].
rewrite /le recE /= -/le caseE leq_finii /=.
elim/arity_ind: {j} _ / (hnth _ _) args=> [[]|R As cAs IH|j As cAs IH] //=.
  case=> [x args]; rewrite /= eqxx; exact: IH.
by case=> [[x xP] args] /=; rewrite eqxx; exact: IH.
Qed.

Lemma anti i : antisymmetric (@le i).
Proof.
elim/indP: i / => i [xi xargs] y.
rewrite -[y]unrollK; case: {y} (unroll _)=> [yi yargs].
rewrite /le !recE -/le /= !caseE /=.
case ie: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e|b].
  case: xi / e {ie} xargs=> xargs _ /=; rewrite leq_finii /= => h.
  congr (Roll (Cons _))=> /=.
  elim/arity_ind: {yi} (nth_fin yi) / (hnth _ _) xargs yargs h
      => [[] []|R As cAs IH|j As cAs IH] //=.
    case=> [x xargs] [y yargs] /=.
    rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH <-|yx] //.
    by move=> /le_anti e; rewrite e eqxx in yx.
  case=> [[x xP] xargs] [y yargs] /=.
  rewrite eq_sym; case: (altP (_ =P _))=> [-> /IH <-|yx /xP e] //.
  by rewrite e eqxx in yx.
case: (leq_fin xi yi) (leq_nat_of_fin xi yi)=> [e|b'].
  by rewrite e leq_finii in ie.
move=> <- <-.
have ne: nat_of_fin yi != nat_of_fin xi.
  by apply/eqP=> /nat_of_fin_inj e; rewrite e leq_finii in ie.
  by case: ltngtP ne.
Qed.

Lemma trans i : transitive (@le i).
Proof.
move=> y x z; elim/indP: i / x y z => i [xi xargs] y z.
rewrite -[y]unrollK -[z]unrollK.
move: (unroll y) (unroll z)=> {y z} [yi yargs] [zi zargs].
rewrite /le !recE /= -/le !caseE /=.
case: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e _|b] //.
  case: xi / e xargs=> /= xargs.
  case: (leq_fin zi yi) (leq_nat_of_fin zi yi)=> [e _|b] //.
    case: yi / e xargs yargs => xargs yargs /=.
    elim/arity_ind: {zi} _ / (hnth _ _) xargs yargs zargs
                    => [//|R|j] As cAs IH /=.
      case=> [x xargs] [y yargs] [z zargs] /=.
      case: (altP (_ =P _)) => [<-|xy].
        case: ifP=> // /eqP _; exact: IH.
      case: (altP (_ =P _)) => [<-|yz]; first by rewrite (negbTE xy).
      case: (altP (_ =P _)) => [<-|xz]; last exact: le_trans.
      move=> c1 c2; suffices e: x = y by rewrite e eqxx in xy.
      by have /andP/le_anti := conj c1 c2.
    case=> [[x xP] xargs] [y yargs] [z zargs] /=.
    case: (altP (x =P y))=> [<-|xy].
      case: (altP (x =P z))=> [_|//]; exact: IH.
    case: (altP (x =P z))=> [<-|yz].
      rewrite eq_sym (negbTE xy)=> le1 le2.
      suffices e : x = y by rewrite e eqxx in xy.
      by apply: anti; rewrite le1.
    case: (altP (_ =P _))=> [<-|_] //; exact: xP.
move=> <- {b} ei.
case: (leq_fin zi yi) (leq_nat_of_fin zi yi)=> [e _|_ <-].
  case: yi / e yargs ei=> /= yargs.
  by rewrite leq_nat_of_fin; case: (leq_fin zi xi).
case: (leq_fin zi xi) (leq_nat_of_fin zi xi)=> [e|_ <-].
  by case: xi / e ei xargs; rewrite -ltnNge => /ltnW ->.
move: ei; rewrite -!ltnNge; exact: ltn_trans.
Qed.

Lemma total i : total (@le i).
Proof.
elim/indP: i / => i [xi xargs] y.
rewrite -[y]unrollK; case: {y} (unroll _)=> [yi yargs].
rewrite /le !recE /= -/le !caseE /= (leq_fin_swap xi yi).
case: (leq_fin yi xi)=> [e|[] //].
case: xi / e xargs=> /= xargs.
elim/arity_ind: {yi} _ / (hnth _ _) xargs yargs=> [[] []|R|j] //= As cAs IH.
  case=> [x xargs] [y yargs] /=.
  rewrite eq_sym; case: (altP eqP)=> [{y} _|]; first exact: IH.
  by rewrite le_total.
case=> /= [[x xP] xargs] [y yargs] /=.
by rewrite eq_sym; case: (altP eqP)=> ?; [apply: IH|apply: xP].
Qed.

Definition ind_isOrder i :=
  Eval unfold Order.isOrder.phant_Build in
  Order.isOrder.Build Order.default_display (T i)
    (fun _ _ => erefl) (fun _ _ => erefl) (fun _ _ => erefl)
    (@anti i) (@trans i) (@total i).

End Def.

End DerOrderType.

Definition pack (T : Type) :=
  [infer indType of T with sort as sT n Ts' D cD in
   fun (Ts : lift_class Choice.sort n) =>
   fun & phant_id Ts' (untag_sort Ts) =>
   fun T_choice & phant_id (lift_class_proj Choice.class Ts) T_choice =>
   let T_ind_choice := @IndChoiceType _ _ _ T_choice sT in
   fun cD' & phant_id cD cD' =>
   @ind_isOrder T_ind_choice cD' (Ind.idx sT)].

End DerOrderType.

Canonical packOrderType disp (T : orderType disp) :=
  DerOrderType.Pack T.

Notation "[ 'derive' 'nored' 'isOrder' 'for' T ]" :=
  (@DerOrderType.pack T%type _ id _ _ _ _ _ _ id _ id _ id _ id _ id _ id :
    Order.isOrder Order.default_display T%type
  )
  (at level 0) : form_scope.

(* FIXME: Axioms_ is an internal function *)
Ltac derive_isOrder T :=
  let mixin := constr:([derive nored isOrder for T]) in
  let mixin :=
    eval unfold DerOrderType.pack, DerOrderType.ind_isOrder in mixin in
  match mixin with
  | @Order.isOrder.Axioms_ ?d ?T' ?choice_m ?eq_m ?le ?lt ?meet ?join _ _ _
                           ?anti ?trans ?total =>
    let le := eval unfold DerOrderType.le, DerOrderType.le_branch in le in
    let le := eval deriving_compute in le in
    exact (@Order.isOrder.Axioms_ d T choice_m eq_m le _ _ _
                         (fun _ _ => erefl) (fun _ _ => erefl) (fun _ _ => erefl)
                         anti trans total)
  end.

Notation "[ 'derive' 'isOrder' 'for' T ]" :=
  (ltac:(derive_isOrder T))
  (at level 0, format "[ 'derive'  'isOrder'  'for'  T ]") : form_scope.

(* FIXME: Axioms_ is an internal function *)
Ltac derive_lazy_isOrder T :=
  let mixin := constr:([derive nored isOrder for T]) in
  let mixin :=
    eval unfold DerOrderType.pack, DerOrderType.ind_isOrder in mixin in
  match mixin with
  | @Order.isOrder.Axioms_ ?d ?T' ?choice_m ?eq_m ?le ?lt ?meet ?join _ _ _
                           ?anti ?trans ?total =>
    let le := eval unfold DerOrderType.le, DerOrderType.le_branch in le in
    let le := eval deriving_lazy in le in
    exact (@Order.isOrder.Axioms_ d T choice_m eq_m le _ meet join
                         (fun _ _ => erefl) (fun _ _ => erefl) (fun _ _ => erefl)
                         anti trans total)
  end.

Notation "[ 'derive' 'lazy' 'isOrder' 'for' T ]" :=
  (ltac:(derive_lazy_isOrder T)) (at level 0) : form_scope.

#[deprecated(since="deriving 0.2.0",
      note="Use [derive nored isOrder for _] instead")]
Notation "[ 'derive' 'nored' 'orderMixin' 'for' T ]" :=
  ([derive nored isOrder for T])
  (at level 0) : form_scope.
#[deprecated(since="deriving 0.2.0",
      note="Use [derive isOrder for _] instead")]
Notation "[ 'derive' 'orderMixin' 'for' T ]" :=
  ([derive isOrder for T])
  (at level 0) : form_scope.
#[deprecated(since="deriving 0.2.0",
      note="Use [derive lazy isOrder for _] instead")]
Notation "[ 'derive' 'lazy' 'orderMixin' 'for' T ]" :=
  ([derive lazy isOrder for T]) (at level 0) : form_scope.
