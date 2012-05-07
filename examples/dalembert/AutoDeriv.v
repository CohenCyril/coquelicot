Require Import Reals.
Require Import Arithmetique.
Require Import Function1 Function2 Partial_function Partial_function2.

Open Scope R_scope.

(** * Définition d'une expression et de sa dérivée *)

(** Opérations de base *)

Inductive bop :=
  | Eplus
  | Emult.

Inductive uop :=
  | Eopp.

(** Expression *)

Record Cont_F := mkCont_F {fct :> R -> partial_val ; Cf_cond : Pfun_continuity fct}.

Inductive expr :=
  | Var : expr
  | Cst : R -> expr
  | Binary : bop -> expr -> expr -> expr
  | Unary : uop -> expr -> expr
  | Int : Cont_F -> expr -> expr -> expr
  | Fun1 : (R -> partial_val) -> expr -> expr
  | Fun2 : (R -> R -> partial_val) -> expr -> expr -> expr.

(** Derivation *)

Fixpoint D (e : expr) :=
  match e with
    | Var => (Cst 1)
    | Cst _ => (Cst 0)
    | Binary b e1 e2 =>
    match b, e1, e2 with
      | Eplus, Cst _, _ => D e2
      | Eplus, _, Cst _ => D e1
      | Eplus, _, _ => (Binary Eplus (D e1) (D e2))
      | Emult, Cst _, _ => Binary Emult e1 (D e2)
      | Emult, _, Cst _ => Binary Emult (D e1) e2
      | Emult, _, _ => Binary Eplus
            (Binary Emult (D e1) e2)
            (Binary Emult e1 (D e2))
    end
    | Unary u e0 =>
    match u with
      | Eopp => Unary Eopp (D e0)
    end
    | Int f a b => Binary Eplus
      (Binary Emult (D b) (Fun1 f b))
      (Unary Eopp (Binary Emult (D a) (Fun1 f a)))
    | Fun1 f e0 => Binary Emult (D e0) (Fun1 (Pfun_derive f) e0)
    | Fun2 f e1 e2 =>
      let df := Pfun2_differential f in
      Binary Eplus
        (Binary Emult (D e1) (Fun2 (fun x y => fst (df x y)) e1 e2))
        (Binary Emult (D e2) (Fun2 (fun x y => snd (df x y)) e1 e2))
  end.

(** * Passage entre expression et fonction *)

(** expression -> fonction *)

Fixpoint interp (e : expr) (x : R) : partial_val :=
  match e with
    | Var  => Pval_val x
    | Cst a => Pval_val a
    | Binary b e1 e2 =>
    match b with
      | Eplus => Pval_plus (interp e1 x) (interp e2 x)
      | Emult => Pval_mult (interp e1 x) (interp e2 x)
    end
    | Unary u e0 =>
    match u with
      | Eopp => Pval_opp (interp e0 x)
    end
    | Int f a b => Pfun2_app (Pfun2_Rint (fct f)) (interp a x) (interp b x)
    | Fun1 f e0  => Pfun_app f (interp e0 x)
    | Fun2 f e0 e1 => Pfun2_app f (interp e0 x) (interp e1 x)
  end.

(** fonction -> expression **)

Ltac reify_helper a b z d :=
  match a with
    | Cst _ =>
        match b with
          | Cst _ => constr : (Cst d)
          | _ => z
        end
    | _ => z
  end.

Ltac reify fct :=
  match fct with
    | AppVar => constr : Var
    | Rplus ?a ?b =>
        let a' := reify a in
        let b' := reify b in
        reify_helper a' b' (Binary Eplus a' b') fct
    | Ropp ?a =>
        let a' := reify a in
        match a' with
          | Cst _ => constr : (Cst fct)
          | _ => constr : (Unary Eopp a')
        end
    | Rminus ?a ?b =>
        let a' := reify a in
        let b' := reify b in
        reify_helper a' b' (Binary Eplus a' (Unary Eopp b')) fct
    | Rmult ?a ?b =>
        let a' := reify a in
        let b' := reify b in
        reify_helper a' b' (Binary Emult a' b') fct
    | RiemannInt (cont_impl_Rint ?f ?Cf ?a ?b) =>
        let a' := reify a in
        let b' := reify b in
        constr : (Int (mkCont_F (Pfun_fun f)
          (fun x => fst (Pfun_continuity_pt_fun f x) (Cf x))) a' b')
    | Rint ?f (cont_impl_Rint ?f ?Cf) ?a ?b =>
        let a' := reify a in
        let b' := reify b in
        constr : (Int (mkCont_F (Pfun_fun f)
          (fun x => fst (Pfun_continuity_pt_fun f x) (Cf x))) a' b')
    | @RiemannInt ?f ?a ?b (?pr _ _) =>
        match goal with
          | Cf : continuity f |- _ =>
                let a' := reify a in
                let b' := reify b in
                constr : (Int (mkCont_F (Pfun_fun f)
                (fun x => fst (Pfun_continuity_pt_fun f x) (Cf x))) a' b')
          | _ =>
                let a' := reify a in
                let b' := reify b in
                constr : (Fun2 (Pfun2_fun (Rint f pr)) a' b')
        end
    | Rint ?f ?pr ?a ?b =>
        match goal with
          | Cf : continuity f |- _ =>
                let a' := reify a in
                let b' := reify b in
                constr : (Int (mkCont_F (Pfun_fun f)
                (fun x => fst (Pfun_continuity_pt_fun f x) (Cf x))) a' b')
          | _ =>
                let a' := reify a in
                let b' := reify b in
                constr : (Fun2 (Pfun2_fun (Rint f pr)) a' b')
        end
    | ?f ?a ?b =>
        let a' := reify a in
        let b' := reify b in
        match b' with
          | Cst _ =>
              match a' with
                | Cst _ => constr : (Cst fct)
                | _ => constr : (Fun1 (Pfun_fun (fun x => f x b)) a')
              end
          | _ =>
              match a' with
                | Cst _ => constr : (Fun1 (Pfun_fun (f a)) b')
                | _ => constr : (Fun2 (Pfun2_fun f) a' b')
              end
        end
    | ?f ?a =>
        let a' := reify a in
        match a' with
          | Cst _ => constr : (Cst fct)
          | _ => constr : (Fun1 (Pfun_fun f) a')
        end
    | _ =>
        match fct with
          | context [AppVar] =>
              match eval pattern AppVar in fct with
              | ?f _ => constr:(Fun1 (Pfun_fun f) Var)
              end
          | _ => constr : (Cst fct)
        end
  end.

(** * L'opérateur D est correct *)

Lemma D_Cst_aux : forall e,
  sum (forall T (e1 e2 : T), match e with Cst _ => e1 | _ => e2 end = e2) { c | e = Cst c }.
Proof.
intros [| | | | | |] ; try now left.
intros c ; right ; now exists c.
Qed.

Lemma D_correct : forall (e : expr) (x : R),
  let vd := interp (D e) x in
  forall d : pdom vd, Pfun_derivable_pt_lim (interp e) x (pval vd d).
Proof.
intros e x.
induction e.

(* Var *)
simpl ; intros.
apply Pfun_derivable_pt_lim_id.

(* Cst *)
simpl ; intros.
apply Pfun_derivable_pt_lim_const.

(* Binary *)
destruct b.
(* * Eplus *)
simpl in *.
destruct (D_Cst_aux e1) as [H1|(c1,H1)] ; rewrite H1 ; clear H1.
destruct (D_Cst_aux e2) as [H2|(c1,H2)] ; rewrite H2 ; clear H2.
simpl ; intros.
now apply Pfun_derivable_pt_lim_plus.
simpl ; intros.
rewrite <- Rplus_0_r.
apply Pfun_derivable_pt_lim_plus.
apply IHe1.
apply Pfun_derivable_pt_lim_const.
simpl ; intros.
rewrite <- Rplus_0_l.
apply Pfun_derivable_pt_lim_plus.
apply Pfun_derivable_pt_lim_const.
apply IHe2.

(* * Emult *)
simpl in *.
destruct (D_Cst_aux e1) as [H1|(c1,H1)] ; rewrite H1 ; clear H1.
destruct (D_Cst_aux e2) as [H2|(c1,H2)] ; rewrite H2 ; clear H2.
simpl ; intros.
now apply Pfun_derivable_pt_lim_mult.
simpl ; intros d.
apply (Pfun_derivable_pt_lim_extension _ (fun x => Pval_scal c1 (interp e1 x))).
intros x0.
unfold Pval_extension, Pval_mult.
simpl.
intuition.
simpl.
rewrite (pHeq _ a0 b1).
apply Rmult_comm.
rewrite Rmult_comm.
now apply Pfun_derivable_pt_lim_scal.
simpl.
intros d.
now apply Pfun_derivable_pt_lim_scal.

(* Unary *)
destruct u.
(* * Eopp *)
simpl ; intros.
now apply Pfun_derivable_pt_lim_opp.

(* Int *)
destruct c as (f, Cf).
simpl ; intros ((dde2,(de2,dfe2)),(dde1,(de1,dfe1))) ; simpl.
replace (pval _ dde2 * pval _ dfe2 + - (pval _ dde1 * pval _ dfe1)) with
   (fst (- pval _ dfe1, pval _ dfe2) * pval _ dde1 +
    snd (- pval _ dfe1, pval _ dfe2) * pval _ dde2) by (simpl ; ring).
  apply Pfun_derivable_pt_lim_comp2.
  apply IHe1.
  apply IHe2.
intros.
rewrite (pHeq _ d2 de1), (pHeq _ d3 de2).
apply (Pfun2_differentiable_pt_lim_Rint _ _ _ (mkposreal 1 Rlt_0_1)).
  apply Cf.
  apply Cf.
  apply (Pfun_cont_impl_Rint f) ;
  intros ; apply Cf.
  apply Pfun_cont_impl_Rint ;
  intros ; apply Cf.
  apply Pfun_cont_impl_Rint ;
  intros ; apply Cf.

(* Fun1 *)
simpl.
intros.
rewrite Rmult_comm.
apply Pfun_derivable_pt_lim_comp with (projT1 (snd d)).
apply IHe.
eapply Pfun_derivable_derive.
reflexivity.

(* Fun2 *)
simpl ; intros ((dde1,(dx1,(dy1,(l1,d1)))),(dde2,(dx2,(dy2,(l2,d2))))) ; simpl.
assert (pval (interp (D e1) x) dde1 * fst l1 + pval (interp (D e2) x) dde2 * snd l2 =
  fst l1 * pval (interp (D e1) x) dde1 + snd l1 * pval (interp (D e2) x) dde2).
  rewrite (Pfun2_differential_unique p (pval (interp e1 x) dx1) (pval (interp e2 x) dy1) l2 l1).
  ring.
  rewrite (pHeq _ dx1 dx2), (pHeq _ dy1 dy2) ; apply d2.
  apply d1.
  rewrite H ; clear H.
apply Pfun_derivable_pt_lim_comp2.
apply IHe1.
apply IHe2.
intros ; rewrite (pHeq _ d0 dx1), (pHeq _ d3 dy1) ; apply d1.
Qed.

(** * Dérivation automatique *)

Ltac Simpl_dom :=
match goal with
  | _ =>intuition ;
	repeat split ;
	intuition ;
	try apply (Pfun_derivable_pt_fun _ _) (*;
	try apply Pfun2_differentiable_pt_fun ;
        try apply Pfun_Riemann_integrable_fun*)
end.

Ltac Simpl_val :=
  repeat split ;
  simpl ;
  intuition ;
  match goal with |- _ = ?e => unfold e ; clear e | _ => idtac end ;
  unfold Rminus ;
  repeat match goal with
  | |- context[Pval_RiemannInt (Pfun_fun ?f) ?a ?b ?p] =>
    match goal with
    | |- context[@RiemannInt ?f ?a' ?b' ?q] => let z := constr:(refl_equal a : a = a') in
        let z' := constr:(refl_equal b : b = b') in
        rewrite (Pval_RiemannInt_fun f a b q p)
    | |- context[Rint ?f ?q ?a' ?b'] => let z := constr:(refl_equal a : a = a') in
        let z' := constr:(refl_equal b : b = b') in
	unfold Rint ;
        rewrite (Pval_RiemannInt_fun f a b (q a b) p)
(*    | |- _ => let pr := constr:((Pfun_Riemann_integrable_fun f a b) p) in
      rewrite (Pfun_derive_pt_fun f x p pr) *)
    end
  | |- context[Pfun_derive_pt (Pfun_fun (derive ?f ?q1)) ?x ?p] =>
    match goal with
    | |- context[derive2 ?f ?q ?x'] =>
	let z := constr:(refl_equal x : x = x') in
        rewrite (Pfun_derive_pt_fun1 f x q1 p q)
    end
  | |- context[Pfun_derive_pt (Pfun_fun ?f) ?x ?p] =>
    let pr :=
      match goal with
      | |- context[derive_pt f x ?q] => q
      | _ =>
        match p with
        | fst (Pfun_derivable_pt_fun _ _) ?q => q
        | _ => constr:(snd (Pfun_derivable_pt_fun f x) p)
        end
      end in
    rewrite (Pfun_derive_pt_fun f x p pr)
  (*| |- context[Pfun2_differential_pt (Pfun2_fun ?f) ?x ?y ?p] =>
	let pr := constr: (Pfun2_differentiable_pt_fun_1 f x y p) in
	rewrite (Pfun2_differential_pt_fun f x y p pr)*)
  end ; try reflexivity.

Lemma CompressDomain_helper :
  forall D1 D2 (f : D1 -> D2) P,
  { d : D1 | P (f d) } ->
  { d : D2 | P d }.
Proof.
intros D1 D2 f P (d, v).
now exists (f d).
Qed.

Ltac CompressDomain :=
  let rec scan t :=
    match t with
    | prod ?t1 ?t2 =>
      let f1 := scan t1 in
      let f2 := scan t2 in
      match type of f1 with
      | True -> _ =>
        match type of f2 with
        | True -> _ => constr:(fun _ : True => (f1 I, f2 I))
        | _ => constr:(fun d => (f1 I, f2 d))
        end
      | _ =>
        match type of f2 with
        | True -> _ => constr:(fun d => (f1 d, f2 I))
        | _ => constr:(fun d => (f1 (fst d), f2 (snd d)))
        end
      end
    | @sigT ?t1 (fun _ => ?t2) =>
      let f1 := scan t1 in
      let f2 := scan t2 in
      match type of f1 with
      | True -> _ =>
        match type of f2 with
        | True -> _ => constr:(fun _ : True => existT (fun _ => t2) (f1 I) (f2 I))
        | _ => constr:(fun d => existT (fun _ => t2) (f1 I) (f2 d))
        end
      | _ =>
        match type of f2 with
        | True -> _ => constr:(fun d => existT (fun _ => t2) (f1 d) (f2 I))
        | _ => constr:(fun d => existT (fun _ => t2) (f1 (fst d)) (f2 (snd d)))
        end
      end
    | Pfun_derivable_pt (Pfun_fun ?f) ?x =>
      match goal with
      | H : derivable_pt _ _ |- _ => constr:(fun _ : True => fst (Pfun_derivable_pt_fun f x) H : t)
      | H : context[derive_pt _ _ ?pr] |- _ => constr:(fun _ : True => fst (Pfun_derivable_pt_fun f x) pr : t)
      | v := context[derive_pt _ _ ?pr] |- _ => constr:(fun _ : True => fst (Pfun_derivable_pt_fun f x) pr : t)
      end
    | _ => constr:(fun d : t => d)
    end in
  compute [interp D Pval_val Pval_opp Pval_plus Pval_mult Pfun_app Pfun_derive pval pdom] ;
  match goal with
  | |- {d : ?e | _ } =>
    let f := scan e in
    let f := eval cbv beta in f in
    refine (CompressDomain_helper _ _ f _ _) ;
    simpl
  end.

Lemma AutoDerive_helper :
  forall e f x l,
  (forall x, let v := interp e x in forall d : pdom v, pval v d = f x) ->
  (let vd := interp (D e) x in { d : pdom vd | pval vd d = l }) ->
  derivable_pt_lim f x l.
Proof.
intros e f x l Hf Hd.
apply (Pfun_derivable_pt_lim_fun _ _ _).
apply (Pfun_derivable_pt_lim_extension _ (interp e)).
clear x Hd.
repeat split.
simpl.
intros _ d.
now apply sym_eq.
destruct Hd as (d, Hd).
rewrite <- Hd.
apply D_correct.
Qed.

Ltac AutoDerive1 :=
  unfold derivable_pt_abs, derivable10_pt_lim, derivable01_pt_lim ;
  match goal with
  | |-derivable_pt_lim ?f ?v ?l =>
    let l' := fresh "AutoDerive_lim" in
    set (l' := l) ;
    unfold derive10, derive01, derive, derive10_pt, derive01_pt in l' ;
    let fx := eval cbv beta in (f AppVar) in
    let exp := reify fx in
    match exp with
    | context[AppVar] => fail 2 "AutoDerive failure: variable found in unsupported expression"
    | _ => apply (AutoDerive_helper exp f v l')
    end
  end.

Ltac AutoDerive :=
  AutoDerive1 ;
  [ Simpl_val |
    CompressDomain ;
    refine (let d := _ in exist  _ d _) ;
    [ Simpl_dom | Simpl_val ; try ring ; try field ]
  ].
