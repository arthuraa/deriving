From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype order.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

From deriving Require Import base ind tactics infer.

From Coq Require Import ZArith NArith String Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope deriving_scope.

Section OuterHsum.

Fixpoint outer_hsum k : (fin k -> Type) -> Type :=
  match k with
  | 0    => fun _  => void
  | k.+1 => fun T_ => (T_ None + @outer_hsum k (fun i => T_ (Some i)))%type
  end.

Fixpoint outer_hin k : forall (T_ : fin k -> Type) (i : fin k),
  T_ i -> outer_hsum T_ :=
  match k with
  | 0 => fun _ i => match i with end
  | k.+1 => fun T_ i =>
    match i return T_ i -> outer_hsum T_ with
    | None => fun x => inl x
    | Some j => fun x => inr (@outer_hin k (fun i => T_ (Some i)) j x)
    end
  end.

Fixpoint outer_hproj k : forall (T_ : fin k -> Type) (i : fin k),
  outer_hsum T_ -> option (T_ i) :=
  match k with
  | 0 => fun _ i => match i with end
  | k.+1 => fun T_ i =>
    match i return outer_hsum T_ -> option (T_ i) with
    | None => fun x => match x with inl y => Some y | inr _ => None end
    | Some j => fun x => match x with
                         | inl _ => None
                         | inr y => @outer_hproj k (fun i => T_ (Some i)) j y
                         end
    end
  end.

Lemma outer_hinK k (T_ : fin k -> Type) i x :
  outer_hproj i (@outer_hin k T_ i x) = Some x.
Proof.
elim: k T_ i x => [|k IH] T_; first by case.
by case=> [j|] x //=; rewrite IH.
Qed.

End OuterHsum.

Section TreeOfInd.

Variables (T : indDef).
Notation n := (Ind.Def.n T).
Let D := Ind.Def.decl T.

Import GenTree.
Import PolyType.
Import IndF.

Definition ind_arg :=
  outer_hsum (fun i : fin n =>
    hsum (fun a : arity n => hsum (type_of_arg (fun=> void)) a) (D i)).

Definition mk_ind_arg i (j : Ind.Cidx D i) (k : fin (size (nth_fin j))) :
  type_of_arg (fun=> void) (nth_fin k) -> ind_arg :=
  fun x =>
    @outer_hin n (fun i : fin n =>
                    hsum (fun a : arity n => hsum (type_of_arg (fun=> void)) a)
                         (D i)) i
      (@hin _ (fun a => hsum (type_of_arg (fun=> void)) a) (D i) j
        (@hin _ (type_of_arg (fun=> void)) (nth_fin j) k x)).

Definition proj_ind_arg
  i (j : Ind.Cidx D i) (k : fin (size (nth_fin j))) (x : ind_arg) :
  option (type_of_arg (fun=> void) (nth_fin k)) :=
  if outer_hproj i x is Some x then
    if hproj j x is Some x then hproj k x
    else None
  else None.

Lemma mk_ind_argK i j k : pcancel (@mk_ind_arg i j k) (@proj_ind_arg i j k).
Proof. by move=> x; rewrite /proj_ind_arg outer_hinK !hinK. Qed.

Let wrap i (j : Ind.Cidx D i) (k : fin (size (nth_fin j))) :
  type_of_arg (fun=> tree ind_arg) (nth_fin k) -> tree ind_arg :=
  match nth_fin k as A
  return (type_of_arg (fun=> void) A -> ind_arg) ->
         type_of_arg (fun=> tree ind_arg) A -> tree ind_arg
  with
  | NonRec R  => fun c x => Leaf (c x)
  | Rec    i' => fun c x => x
  end (@mk_ind_arg i j k).

Definition tree_of_coq_ind : forall i, T i -> tree ind_arg :=
  rec (fun i x =>
         let j := constr x in
         Node (nat_of_fin j)
           (list_of_seq (seq_of_hlist (@wrap i j)
              (hmap (type_of_arg_map (fun=> snd)) (args x))))).

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
    is Some args then Some (Roll (Cons args))
    else None
  end.

Lemma tree_of_coq_indK i : pcancel (@tree_of_coq_ind i) (@coq_ind_of_tree i).
Proof.
elim/indP: i / => i [j xs].
rewrite /tree_of_coq_ind recE /= -/tree_of_coq_ind.
rewrite nat_of_finK !hmap_comp /=.
set xs' := hlist_of_seq _ _.
suffices -> : xs' = Some (hmap (type_of_arg_map (fun=> tag)) xs) by [].
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
  fun (sT_ind : indType) & phant_id (Ind.sort sT_ind) T =>
  @tree_of_coq_indK sT_ind (Ind.idx sT_ind).

Notation "[ 'derive' 'hasChoice' 'for' T ]" :=
  (Choice.copy T%type (pcan_type (@pack_tree_of_indK T _ id)))
  (at level 0, format "[ 'derive'  'hasChoice'  'for'  T ]") : form_scope.

Notation "[ 'derive' 'isCountable' 'for' T ]" :=
  (Countable.copy T%type (pcan_type (@pack_tree_of_indK T _ id)))
  (at level 0, format "[ 'derive' 'isCountable'  'for'  T ]") : form_scope.

#[deprecated(since="deriving 0.2.0",
      note="Use [derive hasChoice for _] instead")]
Notation "[ 'derive' 'choiceMixin' 'for' T ]" :=
  ([derive hasChoice for T])
  (at level 0) : form_scope.

#[deprecated(since="deriving 0.2.0",
      note="Use [derive isCountable for _] instead")]
Notation "[ 'derive' 'countMixin' 'for' T ]" :=
  ([derive isCountable for T])
  (at level 0) : form_scope.
