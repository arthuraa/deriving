From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics infer.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Module DerFinType.

Import PolyType.

Section FinType.

Fixpoint allP T (P : T -> bool) (xs : seq T) :
  all P xs -> forall i : fin (size xs), P (nth_fin i) :=
  match xs with
  | [::] =>
    fun H i => match i with end
  | x :: xs =>
    match P x as b
    return (P x = b -> b && all P xs ->
            forall i : fin (size (x :: xs)), P (nth_fin i))
    with
    | true => fun e H i => match i with
                           | None => e
                           | Some j => allP H j
                           end
    | false => ltac:(done)
    end erefl
  end.

Fixpoint all_finbP n : forall (f : fin n -> bool),
  all_finb f -> forall i, f i :=
  match n with
  | 0 => fun f _ i => match i with end
  | n.+1 => fun f =>
    match f None as b
    return (f None = b -> b && @all_finb n (f \o Some) ->
            forall i : fin n.+1, f i)
    with
    | true => fun e H i => match i with
                           | None => e
                           | Some j => all_finbP H j
                           end
    | false => ltac:(done)
    end erefl
  end.

(** It is strange to derive a finType instance for a mutually inductive type,
but you never know...*)
Variable (T : indEqType).
Notation n := (Ind.Def.n T).
Notation D := (Ind.Def.decl T).

Hypothesis sT : forall i, sig_class Finite.sort (D i).

Hypothesis not_rec :
  all_finb (fun i => all (all (negb \o @is_rec n)) (D i)).

Import IndF.

Definition enum_branch_aux :=
  arity_rec
    _ (fun As => all (negb \o @is_rec n) As -> seq.seq (hlist' (type_of_arg T) As))
    (fun _ => [:: tt]%SEQ)
    (fun S As rec P => allpairs Cell (Finite.enum S) (rec P))
    (fun i As rec P => ltac:(done)).

Definition enum_branch i (j : Ind.Cidx D i) :=
  enum_branch_aux (hnth (sT i) j)
                  (allP (all_finbP not_rec i) j).

Definition enum_ind i :=
  seq.flatten [seq [seq Roll (Cons args) | args <- enum_branch j]
              | j <- list_of_seq (enum_fin (size (D i)))].

Lemma enum_indP i : Finite.axiom (enum_ind i).
Proof.
move=> /= x; rewrite -(unrollK x); case: {x} (unroll x)=> j xs.
rewrite /enum_ind count_flatten -!map_comp /comp /=.
have <- : seq.sumn [seq j == j' : nat
                   | j' <- list_of_seq (enum_fin (size (D i)))] = 1.
  rewrite /Ind.Cidx in j {xs} *.
  elim: (size (D i)) j => [|m IH] //= [j|] /=.
    by rewrite list_of_seq_map -map_comp /comp /= -(IH j) add0n.
  rewrite list_of_seq_map -map_comp /comp /=; congr addn; apply/eqP/natnseq0P.
  by elim: (enum_fin m)=> {IH} // k ks /= <-.
congr seq.sumn; apply/eq_map=> j' /=; rewrite count_map.
have [<- {j'}|ne] /= := altP (j =P j').
  set P := preim _ _.
  have PP : forall ys, reflect (xs = ys) (P ys).
    move=> ys; rewrite /P /=; apply/(iffP idP); last by move=> ->.
    by move=> /eqP/Roll_inj/IndF.inj ->.
  move: P PP.
  rewrite /enum_branch.
  elim/arity_ind: {j} _ / (hnth _ j) xs (allP _ _)=> //=.
    by move=> [] _ P /(_ tt); case.
  move=> S As cAs IH [x xs] As_not_rec P PP.
  elim: (Finite.enum S) (enumP x)=> //= y ys IHys.
  have [-> {y} [e]|ne] := altP (y =P x).
    rewrite count_cat count_map (IH xs); last first.
      by move=> zs; apply/(iffP (PP (x ::: zs))) => [[<-]|->].
    congr succn.
    elim: ys e {IHys} => //= y ys; case: (altP eqP) => //= ne H /H.
    rewrite count_cat => ->; rewrite addn0.
    elim: (enum_branch_aux _ _)=> //= zs e ->; rewrite addn0.
    apply/eqP; rewrite eqb0; apply/negP=> /PP [] /esym/eqP.
    by rewrite (negbTE ne).
  rewrite count_cat; move=> /IHys ->; rewrite addn1; congr succn.
  elim: (enum_branch_aux _ _) {IHys}=> //= zs e ->; rewrite addn0.
  apply/eqP; rewrite eqb0; apply/negP=> /PP [] /esym/eqP.
  by rewrite (negbTE ne).
set P := preim _ _.
rewrite (@eq_count _ _ pred0) ?count_pred0 //.
move=> ys /=; apply/negbTE; apply: contra ne.
by move=> /eqP/Roll_inj/(congr1 (@constr _ _ _ i)) /= ->.
Qed.

End FinType.

Definition pack (T : Type) :=
  [infer indType of T with Finite.sort as sT n sorts D cD in
   fun (Ts : lift_class Equality.sort n) =>
   fun & phant_id sorts (untag_sort Ts) =>
   fun T_count & phant_id (lift_class_proj Equality.class Ts) T_count =>
   let T_ind_count := @IndEqType _ _ _ T_count sT in
   fun cD' & phant_id cD cD' =>
   fun (not_rec : all_finb (fun i => all (all (negb \o @is_rec n)) (D i))) =>
   isFinite.Build _ (@enum_indP T_ind_count cD' not_rec (Ind.idx sT))].

End DerFinType.

(** By default, the derived enumeration of a finite type is kept unnormalized,
since it is not used much -- indeed, [Finite.enum] is even kept opaque. You can
override this behavior by using the [[derive red finMixin for T]] variant
below. *)

Notation "[ 'derive' 'isFinite' 'for' T ]" :=
  (@DerFinType.pack T _ id _ _ _ _ _ _ id _ id _ id _ id _ id _ id erefl
    : isFinite T%type
  )
  (at level 0) : form_scope.

Ltac derive_red_isFinite T :=
  match eval hnf in [derive isFinite for T] with
  | @isFinite.Axioms_ ?T' ?eqP ?enum ?enumP=>
    let enum := eval unfold DerFinType.enum_ind,
                            DerFinType.enum_branch,
                            DerFinType.enum_branch_aux,
                            DerFinType.allP,
                            DerFinType.all_finbP,
                            flatten, allpairs, foldr, map, cat
    in enum in
    let enum := eval deriving_compute in enum in
    exact (@isFinite.Build T eqP  enum enumP)
  end.

Notation "[ 'derive' 'red' 'isFinite' 'for' T ]" :=
  (ltac:(derive_red_isFinite T))
  (at level 0, format "[ 'derive' 'red' 'isFinite'  'for'  T ]") : form_scope.

#[deprecated(since="deriving 0.2.0",
      note="Use [derive isFinite for _]")]
Notation "[ 'derive' 'finMixin' 'for' T ]" :=
  ([derive isFinite for T])
  (at level 0) : form_scope.

#[deprecated(since="deriving 0.2.0",
      note="Use [derive red isFinite for _] instead")]
Notation "[ 'derive' 'red' 'finMixin' 'for' T ]" :=
  ([derive red isFinite for T])
  (at level 0) : form_scope.
