From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.

From deriving Require Import base ind tactics.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Ltac unwind_recursor rec :=
  try red;
  match goal with
  | |- ?F -> ?G =>
    let X := fresh "X" in
    intros X; unwind_recursor (rec X)
  | |- prod ?T1 ?T2 =>
    let rec1 := eval hnf in rec.1 in
    let rec2 := eval hnf in rec.2 in
    split; [unwind_recursor rec1|unwind_recursor rec2]
  | |- forall x, _ =>
    let rec' := eval hnf in rec in
    intros x; destruct x; apply rec'
  end.

Ltac mut_ind_type rec :=
  let Rec := eval red in rec in
  let H   := constr:((fun n Ts D Cs RecT' Rec' Rec'' =>
                      fun (H : infer_ind _ Rec n Ts D Cs RecT' Rec' Rec'') => H)
                     _ _ _ _ _ _ _ _) in
  match type of H with
  | infer_ind _ _ ?n ?Ts ?D ?Cs ?RecT' ?Rec' ?Rec'' =>
    let case := constr:(ltac:(intros P; deriving_compute; unwind_recursor (Rec' P))
                        : forall P, RecT' P) in
    let case := constr:(fun S : fin n -> Type => case (fun i _ => S i)) in
    let case := constr:(@MutInd.destructor_of_recursor n D Ts case) in
    let case := eval deriving_compute in case in
    refine (@MutIndType n D Ts Cs (fun S => Rec' (fun i _ => S i)) case _ _ rec);
    abstract (deriving_compute; intuition)
  end.

Notation "[ 'mutIndType' 'for' rect ]" :=
  (ltac:(mut_ind_type rect))
  (at level 0) : form_scope.

Module DerEqType.

Section EqType.

Variable (n : nat).
Local Notation arg_class := (@arg_class n _ Equality.sort).
Local Notation arg_inst := (arg_inst n Equality.sort).
Local Notation arity_inst := (arity_inst n Equality.sort).
Local Notation sig_inst := (sig_inst n Equality.sort).
Local Notation decl_inst := (decl_inst n Equality.sort n).
Variable (D : decl_inst).
Let F := MutIndF.functor D.
Variable (T : initAlgType F).

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

Definition eq_op : forall i, T i -> T i -> bool :=
  rec   (fun i args1 =>
  case1 (fun   args2 =>
          match leq_fin (MutIndF.constr args2) (MutIndF.constr args1) with
          | inl e =>
            eq_op_branch
              (hnth (decl_inst_class D i) (MutIndF.constr args1))
              (MutIndF.args args1)
              (cast (hlist' (type_of_arg T) \o @nth_fin _ _) e (MutIndF.args args2))
              true
          | inr _ => false
          end)).

Lemma eq_opP i : Equality.axiom (@eq_op i).
Proof.
elim/indP: i / => i [xC xargs] y.
rewrite /eq_op recE /= -[rec _]/(eq_op) /=.
rewrite -[y]unrollK case1E; move: {y} (unroll y)=> [yC yargs] /=.
case le: (leq_fin yC xC)=> [e|b]; last first.
  constructor=> /(@Roll_inj _ _ _ i) /= [] e _.
  by move: le; rewrite e leq_finii.
case: xC / e xargs {le} => /= xargs.
apply/(@iffP (hmap' (type_of_arg_map (fun=> tag)) xargs = yargs)); first last.
- by move=> /(@Roll_inj _ _ _ i) /MutIndF.inj.
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

End DerEqType.

Ltac derive_eqMixin T :=
  let sT := eval hnf in [the indType _ of T by @Ind.sort _ _] in
  match sT with @Ind.Pack ?n ?D ?sTs ?cT ?pfs =>
  let sTs := eval hnf in sTs in
  match sTs with @MutInd.Pack _ _ ?Ts ?cTs =>
  let Ts   := eval red in Ts in
  let sTs  := constr:(@MutInd.Pack n D Ts cTs) in
  let sTs' := constr:(@MutIndF.initAlgType sTs) in
  let sD   := eval hnf in (@pack_decl_inst n D n _ id) in
  let cD   := eval hnf in (decl_inst_class sD) in
  let cD   := eval deriving_compute in cD in
  let op   := constr:(@DerEqType.eq_op (@DeclInst _ _ _ D cD) sTs') in
  let op   := eval cbv delta [DerEqType.eq_op DerEqType.eq_op_branch] in op in
  let op   := eval deriving_compute in op in
  let op   := eval simpl in op in
  exact (@EqMixin _ op (@DerEqType.eq_opP sD sTs'))
  end
  end.

Notation "[ 'derive' 'eqMixin' 'for' T ]" :=
  (ltac:(derive_eqMixin T))
  (at level 0) : form_scope.

Section TreeOfInd.

Variables (n : nat) (D : declaration n).
Let F := MutIndF.functor D.
Variables (T : initAlgType F).

Import GenTree.
Import PolyType.

Definition ind_arg :=
  hsum (fun i => hsum' (hsum' (type_of_arg (fun=> void))) (D i)).

Definition mk_ind_arg i (j : MutInd.Cidx D i) (k : fin (size (nth_fin j))) :
  type_of_arg (fun=> void) (nth_fin k) -> ind_arg :=
  fun x => hin (hin (hin x)).

Definition proj_ind_arg
  i (j : MutInd.Cidx D i) (k : fin (size (nth_fin j))) (x : ind_arg) :
  option (type_of_arg (fun=> void) (nth_fin k)) :=
  if hproj i x is Some x then
    if hproj j x is Some x then hproj k x
    else None
  else None.

Lemma mk_ind_argK i j k : pcancel (@mk_ind_arg i j k) (@proj_ind_arg i j k).
Proof. by move=> x; rewrite /proj_ind_arg !hinK. Qed.

Let wrap i (j : MutInd.Cidx D i) (k : fin (size (nth_fin j))) :
  type_of_arg (fun=> tree ind_arg) (nth_fin k) -> tree ind_arg :=
  match nth_fin k as A
  return (type_of_arg (fun=> void) A -> ind_arg) ->
         type_of_arg (fun=> tree ind_arg) A -> tree ind_arg
  with
  | NonRec R  => fun c x => Leaf (c x)
  | Rec    i' => fun c x => x
  end (@mk_ind_arg i j k).

Definition tree_of_coq_ind i (x : T i) : tree ind_arg :=
  rec (fun i x =>
         let j := MutIndF.constr x in
         Node (nat_of_fin j)
           (list_of_seq (seq_of_hlist (@wrap i j)
              (hmap' (type_of_arg_map (fun=> snd)) (MutIndF.args x)))))
      x.

Fixpoint coq_ind_of_tree i (x : tree ind_arg) : option (T i) :=
  match x with
  | Leaf _ => None
  | Node c xs =>
    if fin_of_nat (size (D i)) c isn't Some j then None else
    let xs := seq_of_list [seq (t, coq_ind_of_tree^~ t) | t <- xs] in
    if hlist_of_seq (fun k ts =>
                       match nth_fin k as A
                       return (ind_arg -> option (type_of_arg (fun=> void) A)) ->
                               option (type_of_arg T A) with
                       | NonRec R => fun f => if ts.1 is Leaf x then f x else None
                       | Rec i'   => fun _ => ts.2 i'
                       end (@proj_ind_arg i j k)) xs
    is Some args then Some (Roll (MutIndF.Cons args))
    else None
  end.

Lemma tree_of_coq_indK i : pcancel (@tree_of_coq_ind i) (@coq_ind_of_tree i).
Proof.
elim/indP: i / => i [j xs].
rewrite /tree_of_coq_ind recE /= -[rec _]/(tree_of_coq_ind).
rewrite nat_of_finK /hmap' !hmap_comp /=.
set xs' := hlist_of_seq _ _.
suffices -> : xs' = Some (hmap' (type_of_arg_map (fun=> tag)) xs) by [].
rewrite {}/xs' seq_of_list_map list_of_seqK hlist_of_seq_map /= /wrap.
move: (@mk_ind_arg i j) (@proj_ind_arg i j) (@mk_ind_argK i j).
elim: {j} (nth_fin j) xs=> //= - [S|i'] As IH /= xs C p CK.
  by rewrite CK IH //= => j x; rewrite CK.
case: xs=> [[x xP] xs] /=; rewrite xP IH //.
by move=> j ?; rewrite CK.
Qed.

End TreeOfInd.

Definition pack_tree_of_indK :=
  fun (T : Type) =>
  fun n D (sT_ind : @indType n D) & phant_id (Ind.sort sT_ind) T =>
  @tree_of_coq_indK _ D sT_ind (type_idx sT_ind).

Notation "[ 'derive' 'choiceMixin' 'for' T ]" :=
  (PcanChoiceMixin (@pack_tree_of_indK T _ _ id))
  (at level 0, format "[ 'derive'  'choiceMixin'  'for'  T ]") : form_scope.

Notation "[ 'derive' 'countMixin' 'for' T ]" :=
  (PcanCountMixin (@pack_tree_of_indK T _ _ id))
  (at level 0, format "[ 'derive' 'countMixin'  'for'  T ]") : form_scope.

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
Variable (n : nat) (D : decl_inst n Finite.sort n).
Let F := MutIndF.functor D.
Variable (T : initAlgEqType F).

Hypothesis not_rec :
  all_finb (fun i => all (all (negb \o @is_rec n)) (D i)).

Definition enum_branch_aux :=
  arity_rec
    _ (fun As => all (negb \o @is_rec n) As -> seq.seq (hlist' (type_of_arg T) As))
    (fun _ => [:: tt]%SEQ)
    (fun S As rec P => allpairs Cell (Finite.enum S) (rec P))
    (fun i As rec P => ltac:(done)).

Definition enum_branch i (j : MutInd.Cidx D i) :=
  enum_branch_aux (hnth (decl_inst_class D i) j)
                  (allP (all_finbP not_rec i) j).

Definition enum_ind i :=
  seq.flatten [seq [seq Roll (MutIndF.Cons args) | args <- enum_branch j]
              | j <- list_of_seq (enum_fin (size (D i)))].

Lemma enum_indP i : Finite.axiom (enum_ind i).
Proof.
move=> x; rewrite -[x]unrollK; case: {x} (unroll x)=> j xs.
rewrite /enum_ind count_flatten -!map_comp /comp /=.
have <- : seq.sumn [seq j == j' : nat | j' <- list_of_seq (enum_fin (size (D i)))] = 1.
  rewrite /MutInd.Cidx in j {xs} *.
  elim: (size (D i)) j => [|m IH] //= [j|] /=.
    by rewrite list_of_seq_map -map_comp /comp /= -(IH j) add0n.
  rewrite list_of_seq_map -map_comp /comp /=; congr addn; apply/eqP/natnseq0P.
  by elim: (enum_fin m)=> {IH} // k ks /= <-.
congr seq.sumn; apply/eq_map=> j' /=; rewrite count_map.
have [<- {j'}|ne] /= := altP (j =P j').
  set P := preim _ _.
  have PP : forall ys, reflect (xs = ys) (P ys).
    move=> ys; rewrite /P /=; apply/(iffP idP); last by move=> ->.
    by move=> /eqP/(@Roll_inj _ _ _ i)/(@MutIndF.inj n D _ i) ->.
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
by move=> /eqP/(@Roll_inj _ _ _ i)/(congr1 (@MutIndF.constr _ _ _ i)) /= ->.
Qed.

End FinType.

(*
Definition pack :=
  fun (T : Type) =>
  fun (b : Countable.class_of T) bT & phant_id (Countable.class bT) b =>
  fun n D (sT : @indType n D) & phant_id (Ind.sort sT) T =>
  fun (sD : decl_inst n Finite.sort n) & phant_id D (decl_inst_sort sD) =>
  fun (sTs : lift_class n Equality.sort)
      & phant_id (Ind.mutInd sT) (untag_sort sTs) =>
  fun (cTs :
  fun (not_rec : all_finb (fun i => all (all (negb \o @is_rec n)) (sD i))) =>
    ltac:(
      let sT_eq := constr:(@InitAlgEqType (fin n) _ _
      let ax := constr:(@enum_indP n sD
      match type of ax with
      | Finite.axiom ?e =>
        let e' := (eval compute -[Finite.sort Equality.sort allpairs cat map] in e) in
        exact (@FinMixin (Countable.Pack b) e' ax)
      end).

Module Import Exports.
Notation "[ 'derive' 'finMixin' 'for' T ]" :=
  (let m := @pack T _ _ id _ _ id _ id _ id erefl in
   ltac:(
     let x := eval hnf in m in
     exact x))
  (at level 0, format "[ 'derive'  'finMixin'  'for'  T ]") : form_scope.
End Exports.*)

End DerFinType.
(*Export DerFinType.Exports.*)

Module DerOrderType.
Section DerOrderType.

Import Order.Total Order.Theory.

Record packedOrderType := Pack {
  disp : unit;
  sort : orderType disp;
}.

Section Def.

Variable n : nat.
Notation arg_class  := (arg_class  sort).
Notation arg_inst   := (arg_inst   n sort).
Notation arity_inst := (arity_inst n sort).
Notation sig_inst   := (sig_inst   n sort).
Notation decl_inst  := (decl_inst  n sort).
Variable (D : decl_inst n).
Let F := MutIndF.functor D.
Variable (T : initAlgChoiceType F).

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
  rec   (fun i args1 =>
  case1 (fun   args2 =>
           match leq_fin (MutIndF.constr args2) (MutIndF.constr args1) with
           | inl e =>
             le_branch
               (hnth (decl_inst_class D i) (MutIndF.constr args1))
               (MutIndF.args args1)
               (cast (hlist' (type_of_arg T) \o @nth_fin _ _) e (MutIndF.args args2))
           | inr b => ~~ b
           end)).

Lemma refl i : reflexive (@le i).
Proof.
elim/indP: i / => i [j args].
rewrite /le recE /= -[rec _]/(le) case1E leq_finii /=.
elim/arity_ind: {j} _ / (hnth _ _) args=> [[]|R As cAs IH|j As cAs IH] //=.
  case=> [x args]; rewrite /= eqxx; exact: IH.
by case=> [[x xP] args] /=; rewrite eqxx; exact: IH.
Qed.

Lemma anti i : antisymmetric (@le i).
Proof.
elim/indP: i / => i [xi xargs] y.
rewrite -(unrollK y); case: {y} (unroll y)=> [yi yargs].
rewrite /le !recE -[rec _]/(le) /= !case1E /=.
case ie: (leq_fin yi xi) (leq_nat_of_fin yi xi)=> [e|b].
  case: xi / e {ie} xargs=> xargs _ /=; rewrite leq_finii /= => h.
  congr (Roll (MutIndF.Cons _))=> /=.
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
rewrite -(unrollK y) -(unrollK z).
move: (unroll y) (unroll z)=> {y z} [yi yargs] [zi zargs].
rewrite /le !recE /= -[rec _]/(le) !case1E /=.
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
rewrite -(unrollK y); case: {y} (unroll y)=> [yi yargs].
rewrite /le !recE /= -[rec _]/(le) !case1E /= (leq_fin_swap xi yi).
case: (leq_fin yi xi)=> [e|[] //].
case: xi / e xargs=> /= xargs.
elim/arity_ind: {yi} _ / (hnth _ _) xargs yargs=> [[] []|R|j] //= As cAs IH.
  case=> [x xargs] [y yargs] /=.
  rewrite eq_sym; case: (altP eqP)=> [{y} _|]; first exact: IH.
  by rewrite le_total.
case=> /= [[x xP] xargs] [y yargs] /=.
by rewrite eq_sym; case: (altP eqP)=> ?; [apply: IH|apply: xP].
Qed.

Definition ind_porderMixin i :=
  @LeOrderMixin _ (@le i) _ _ _
                (fun _ _ => erefl) (fun _ _ => erefl) (fun _ _ => erefl)
                (@anti i) (@trans i) (@total i).

End Def.

End DerOrderType.
End DerOrderType.

Canonical packOrderType disp (T : orderType disp) :=
  DerOrderType.Pack T.

Ltac derive_orderMixin T :=
  let sT_ind := eval hnf in [the indType _ of T by @Ind.sort _] in
  match sT_ind with @Ind.Pack ?Σ _ ?cT_ind =>
  let cT_ind := eval red in cT_ind in
  let sT_ind := constr:(@Ind.Pack Σ T cT_ind) in
  let sT_ind := constr:(MutIndF.initAlgType sT_ind) in
  let sT_ch  := eval hnf in [choiceType of T] in
  let bT_ch  := constr:(Choice.class sT_ch) in
  let sΣ     := eval hnf in [the sig_inst DerOrderType.sort of Σ
                             by @sig_inst_sort _ _] in
  let cΣ     := eval hnf in (sig_inst_class sΣ) in
  let cΣ     := eval deriving_compute in cΣ in
  let sΣ     := constr:(@SigInst _ DerOrderType.sort Σ cΣ) in
  let sT_ind_ch := constr:(InitAlgChoiceType bT_ch (InitAlg.class sT_ind)) in
  let op     := constr:(@DerOrderType.le sΣ sT_ind_ch) in
  let op     := eval cbv delta [DerOrderType.le DerOrderType.le_branch] in op in
  let op     := eval deriving_compute in op in
  let op     := eval simpl in op in
  exact (@LeOrderMixin _ op _ _ _
                       (fun _ _ => erefl)
                       (fun _ _ => erefl)
                       (fun _ _ => erefl)
                       (@DerOrderType.anti sΣ sT_ind_ch)
                       (@DerOrderType.trans sΣ sT_ind_ch)
                       (@DerOrderType.total sΣ sT_ind_ch))
  end.

Notation "[ 'derive' 'orderMixin' 'for' T ]" :=
  (ltac:(derive_orderMixin T))
  (at level 0) : form_scope.

Section Instances.

Variables (T T1 T2 : Type).

Definition unit_indMixin :=
  Eval simpl in [indMixin for unit_rect].
Canonical unit_indType :=
  Eval hnf in IndType _ unit unit_indMixin.

Definition void_indMixin :=
  Eval simpl in [indMixin for Empty_set_rect].
Canonical void_indType :=
  Eval hnf in IndType _ void void_indMixin.

Definition bool_indMixin :=
  Eval simpl in [indMixin for bool_rect].
Canonical bool_indType :=
  Eval hnf in IndType _ bool bool_indMixin.

Definition nat_indMixin :=
  Eval simpl in [indMixin for nat_rect].
Canonical nat_indType :=
  Eval hnf in IndType _ nat nat_indMixin.

Definition option_indMixin :=
  Eval simpl in [indMixin for @option_rect T].
Canonical option_indType :=
  Eval hnf in IndType _ (option T) option_indMixin.

Definition sum_indMixin :=
  Eval simpl in [indMixin for @sum_rect T1 T2].
Canonical sum_indType :=
  Eval hnf in IndType _ _ sum_indMixin.

Definition prod_indMixin :=
  Eval simpl in [indMixin for @prod_rect T1 T2].
Canonical prod_indType :=
  Eval hnf in IndType _ _ prod_indMixin.

Definition seq_indMixin :=
  Eval simpl in [indMixin for @list_rect T].
Canonical seq_indType :=
  Eval hnf in IndType _ _ seq_indMixin.

Definition comparison_indMixin :=
  [indMixin for comparison_rect].
Canonical comparison_indType :=
  Eval hnf in IndType _ comparison comparison_indMixin.
Definition comparison_eqMixin :=
  [derive eqMixin for comparison].
Canonical comparison_eqType :=
  Eval hnf in EqType comparison comparison_eqMixin.
Definition comparison_choiceMixin :=
  Eval simpl in [derive choiceMixin for comparison].
Canonical comparison_choiceType :=
  Eval hnf in ChoiceType comparison comparison_choiceMixin.
Definition comparison_countMixin :=
  Eval simpl in [derive countMixin for comparison].
Canonical comparison_countType :=
  Eval hnf in CountType comparison comparison_countMixin.
Definition comparison_finMixin :=
  Eval simpl in [derive finMixin for comparison].
Canonical comparison_finType :=
  Eval hnf in FinType comparison comparison_finMixin.

Definition positive_indMixin :=
  Eval simpl in [indMixin for positive_rect].
Canonical positive_indType :=
  Eval hnf in IndType _ positive positive_indMixin.
Definition positive_eqMixin :=
  Eval simpl in [derive eqMixin for positive].
Canonical positive_eqType :=
  Eval hnf in EqType positive positive_eqMixin.
Definition positive_choiceMixin :=
  Eval simpl in [derive choiceMixin for positive].
Canonical positive_choiceType :=
  Eval hnf in ChoiceType positive positive_choiceMixin.
Definition positive_countMixin :=
  Eval simpl in [derive countMixin for positive].
Canonical positive_countType :=
  Eval hnf in CountType positive positive_countMixin.

Definition bin_nat_indMixin :=
  Eval simpl in [indMixin for N_rect].
Canonical bin_nat_indType :=
  Eval hnf in IndType _ N bin_nat_indMixin.
Definition bin_nat_choiceMixin :=
  Eval simpl in [derive choiceMixin for N].
Canonical bin_nat_choiceType :=
  Eval hnf in ChoiceType N bin_nat_choiceMixin.
Definition bin_nat_countMixin :=
  Eval simpl in [derive countMixin for N].
Canonical bin_nat_countType :=
  Eval hnf in CountType N bin_nat_countMixin.

Definition Z_indMixin :=
  Eval simpl in [indMixin for Z_rect].
Canonical Z_indType :=
  Eval hnf in IndType _ Z Z_indMixin.
Definition Z_eqMixin :=
  Eval simpl in [derive eqMixin for Z].
Canonical Z_eqType :=
  Eval hnf in EqType Z Z_eqMixin.
Definition Z_choiceMixin :=
  Eval simpl in [derive choiceMixin for Z].
Canonical Z_choiceType :=
  Eval hnf in ChoiceType Z Z_choiceMixin.
Definition Z_countMixin :=
  Eval simpl in [derive countMixin for Z].
Canonical Z_countType :=
  Eval hnf in CountType Z Z_countMixin.

Definition ascii_indMixin :=
  Eval simpl in [indMixin for ascii_rect].
Canonical ascii_indType :=
  Eval hnf in IndType _ ascii ascii_indMixin.
Definition ascii_eqMixin :=
  Eval simpl in [derive eqMixin for ascii].
Canonical ascii_eqType :=
  Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin :=
  Eval simpl in [derive choiceMixin for ascii].
Canonical ascii_choiceType :=
  Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_countMixin :=
  Eval simpl in [derive countMixin for ascii].
Canonical ascii_countType :=
  Eval hnf in CountType ascii ascii_countMixin.
Definition ascii_finMixin :=
  Eval simpl in [derive finMixin for ascii].
Canonical ascii_finType :=
  Eval hnf in FinType ascii ascii_finMixin.

Definition string_indMixin :=
  Eval simpl in [indMixin for string_rect].
Canonical string_indType :=
  Eval hnf in IndType _ string string_indMixin.
Definition string_eqMixin :=
  Eval simpl in [derive eqMixin for string].
Canonical string_eqType :=
  Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin :=
  Eval simpl in [derive choiceMixin for string].
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_countMixin :=
  Eval simpl in [derive countMixin for string].
Canonical string_countType :=
  Eval hnf in CountType string string_countMixin.

End Instances.
