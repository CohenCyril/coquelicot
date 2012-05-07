Require Import Reals.
Require Import Arithmetique.

Open Local Scope R_scope.

(** * Continuity *)
(** Another definition for continuity *)

Definition continuity_pt_aux (f : R -> R) (x : R) :=
  forall eps : posreal, exists delta : posreal,
    forall y : R, Rabs (y-x) < delta -> Rabs (f y - f x) < eps.

Lemma equiv_cont_pt_0 : forall f x,
  continuity_pt f x -> continuity_pt_aux f x.
Proof.
  intros f x Cf eps.
  elim (Cf eps (cond_pos eps)) ;
  clear Cf ; simpl ; unfold R_dist, D_x, no_cond ;
  intros delta (Hdelta,Cf).
  exists (mkposreal _ Hdelta) ; simpl ; intros.
  destruct (Req_dec x y).
  rewrite H0, (Rminus_diag_eq _ _ (refl_equal _)), Rabs_R0 ; apply eps.
  intuition.
Qed.
Lemma equiv_cont_pt_1 : forall f x,
  continuity_pt_aux f x -> continuity_pt f x.
Proof.
  intros f x Cf eps Heps.
  elim (Cf (mkposreal _ Heps)) ;
  clear Cf ; simpl ; unfold R_dist, D_x, no_cond ;
  intros delta Cf.
  exists delta.
  intuition.
  apply delta.
Qed.
Lemma equiv_cont_pt : forall f x,
  continuity_pt f x <-> continuity_pt_aux f x.
Proof.
  split ; intros Cf.
  apply (equiv_cont_pt_0 _ _ Cf).
  apply (equiv_cont_pt_1 _ _ Cf).
Qed.

(** * Differentiability in R *)
(** Another definition *)

Definition derivable_pt_lim_aux (f : R -> R) (x l : R) :=
  forall eps : posreal, exists delta : posreal, forall y : R,
    Rabs (y-x) < delta -> Rabs (f y - f x - l * (y-x)) <= eps * Rabs (y-x).

Lemma equiv_deriv_pt_lim_0 : forall f x l,
  derivable_pt_lim f x l -> derivable_pt_lim_aux f x l.
Proof.
  intros f x l Df.
  intros eps.
  elim (Df eps (cond_pos eps)) ; clear Df ; intros delta Df.
  exists delta ; intros.
  destruct (Req_dec (y-x) 0).
  rewrite H0.
  rewrite (Rminus_diag_uniq _ _ H0).
  assert ((f x - f x - l * 0) = 0).
    ring.
    rewrite H1 ; clear H1.
  rewrite Rabs_R0 ; apply Req_le.
  ring.

  assert ((f y - f x - l * (y - x)) = ((f (x+(y-x)) - f x)/(y-x) - l) * (y-x)).
    assert (x+(y-x) = y).
      ring.
      rewrite H1 ; clear H1.
    field.
    apply H0.
    rewrite H1 ; clear H1.
  rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply Rlt_le.
  apply (Df (y-x) H0 H).
Qed.
Lemma equiv_deriv_pt_lim_1 : forall f x l,
  derivable_pt_lim_aux f x l -> derivable_pt_lim f x l.
Proof.
  intros f x l Df.
  intros eps Heps.
  assert (He : 0 < eps/2).
    apply Rdiv_lt_0_compat.
    apply Heps.
    apply Rlt_R0_R2.
    set (eps2 := mkposreal _ He).
  elim (Df eps2) ; clear Df ; intros delta Df.
  exists delta ; intros.
  assert (x+h-x = h).
    ring.
  assert (((f (x + h) - f x) / h - l) = (f(x+h) - f x - l * ((x+h)-x))/((x+h)-x)).
    field.
    rewrite H1 ;
    apply H.
    rewrite H2 ; clear H2.
  apply (Rle_lt_trans _ eps2).
  rewrite Rabs_div.
  apply (Rle_div _ _ (Rabs (x + h - x))).
  apply Rabs_pos_lt.
  rewrite H1 ;
    apply H.
  apply (Df (x+h)).
  rewrite H1 ;
    apply H0.
    rewrite H1 ; apply H.
  rewrite (double_var eps).
  rewrite <- (Rplus_0_r eps2).
  unfold eps2 ; simpl.
  apply Rplus_lt_compat_l.
  apply He.
Qed.
Lemma equiv_deriv_pt_lim : forall f x l,
  derivable_pt_lim f x l <-> derivable_pt_lim_aux f x l.
Proof.
  split ; intros.
  apply (equiv_deriv_pt_lim_0 _ _ _ H).
  apply (equiv_deriv_pt_lim_1 _ _ _ H).
Qed.

(** * Change of expression *)

Lemma continuity_pt_expr_loc : forall (f g : R -> R) (x : R) (d : posreal),
  (forall y, Rabs (y-x) < d -> f y = g y) ->
    continuity_pt f x -> continuity_pt g x.
Proof.
  intros f g x d2 Heq Cf.
  apply (equiv_cont_pt f x) in Cf.
  apply (equiv_cont_pt g x).
  intros eps.
  elim (Cf eps) ; clear Cf ; intros d1 Cf.
  assert (Hd : 0 < Rmin d1 d2).
    apply Rmin_pos ; [apply d1 | apply d2].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  rewrite <- (Heq y), <- (Heq x).
  apply (Cf y).
  apply (Rlt_le_trans _ delta) ;
  [apply H |
  unfold delta ; apply Rmin_l].
  rewrite Rminus_eq0, Rabs_R0 ; apply d2.
  apply (Rlt_le_trans _ delta) ;
  [apply H |
  unfold delta ; apply Rmin_r].
Qed.
Lemma continuity_pt_expr : forall (f g : R -> R) (x : R),
  (forall y, f y = g y) ->
    continuity_pt f x -> continuity_pt g x.
Proof.
  intros f g x Heq Cf.
  apply (continuity_pt_expr_loc f g x (mkposreal _ Rlt_0_1)).
  simpl ; intros ; apply Heq.
  apply Cf.
Qed.

Lemma derivable_pt_lim_expr_loc : forall (f g : R -> R) (x l : R) (d : posreal),
  (forall y, Rabs (y-x) < d -> f y = g y)
  -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros f g x l d2 Heq Df.
  intros eps Heps.
  elim (Df eps Heps) ; clear Df ; intros d1 Df.
  assert (Hd : 0 < Rmin d1 d2).
    apply Rmin_pos ;
    [apply d1 |
    apply d2].
    set (delta := mkposreal _ Hd).
  exists delta ; intros h Hh0 Hhd.
  rewrite <- (Heq (x+h)), <- (Heq x).
  apply (Df h Hh0).
  apply (Rlt_le_trans _ delta) ;
  [apply Hhd |
  unfold delta ; apply Rmin_l].
  rewrite (Rminus_eq0), Rabs_R0 ; apply d2.
  assert (x + h - x = h).
    ring.
    rewrite H ; clear H.
  apply (Rlt_le_trans _ delta) ;
  [ apply Hhd |
  unfold delta ; apply Rmin_r].
Qed.
Lemma derivable_pt_lim_expr : forall (f g : R -> R) (x l : R),
  (forall y, f y = g y) -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros f g x l Heq Df.
  apply (derivable_pt_lim_expr_loc f g x l (mkposreal _ Rlt_0_1)).
  intros ; apply Heq.
  apply Df.
Qed.

Lemma derivable_pt_expr : forall (f g : R -> R) (x : R),
  (forall y, f y = g y) -> derivable_pt f x -> derivable_pt g x.
Proof.
  intros f g x Heq (l,Df).
  exists l ; apply (derivable_pt_lim_expr f g x l Heq Df).
Qed.
Lemma derivable_expr : forall (f g : R -> R),
  (forall y, f y = g y) -> derivable f -> derivable g.
Proof.
  intros f g Heq Df x.
  apply (derivable_pt_expr f g x Heq (Df x)).
Qed.

Lemma derive_pt_expr : forall (f g : R -> R) (x : R) pr_f pr_g,
  (forall y, f y = g y) -> derive_pt f x pr_f = derive_pt g x pr_g.
Proof.
  intros f g x (lf,Df) (lg,Dg) Heq ; simpl.
  apply (uniqueness_limite g x).
  apply (derivable_pt_lim_expr f g x lf Heq Df).
  apply Dg.
Qed.
Lemma derive_expr : forall (f g : R -> R) pr_f pr_g,
  (forall y, f y = g y) -> forall x, derive f pr_f x = derive g pr_g x.
Proof.
  intros f g pr_f pr_g Heq x.
  apply (derive_pt_expr f g x (pr_f x) (pr_g x) Heq).
Qed.

(** * Complements for basic functions *)

(** Identity function is continuous *)

Lemma continuity_pt_id : forall x, continuity_pt id x.
Proof.
  intros x.
  apply derivable_continuous_pt.
  apply derivable_pt_id.
Qed.

Lemma continuity_id : continuity id.
Proof.
  intros x.
  apply continuity_pt_id.
Qed.

(** The function Ropp *)

Lemma continuity_pt_Ropp : forall x, continuity_pt Ropp x.
Proof.
  intros ; 
  apply (equiv_cont_pt _ _) ;
  intro.
  exists eps ; intros.
  unfold Rminus ; 
  rewrite <- (Ropp_plus_distr y (-x)), Rabs_Ropp.
  apply H.
Qed.

Lemma derivable_pt_lim_Ropp : forall x, derivable_pt_lim Ropp x (-1).
Proof.
  intros ; 
  apply (equiv_deriv_pt_lim _ _ _) ;
  intro.
  exists eps ; intros.
  assert (- y - - x - -1 * (y - x) = 0).
    ring.
    rewrite H0, Rabs_R0 ; clear H0.
  apply Rmult_le_pos.
  apply Rlt_le, eps.
  apply Rabs_pos.
Qed.

(** * Second derivative *)

Definition derivable2_pt_lim (f : R -> R) (x l : R) :=
  {f' : R -> R | (forall x, derivable_pt_lim f x (f' x)) /\ derivable_pt_lim f' x l}.
Definition derivable2_pt (f : R -> R) (x : R) :=
  {l : R & derivable2_pt_lim f x l}.
Definition derive2_pt (f : R -> R) (x : R) (pr2 : derivable2_pt f x) :=
  projT1 pr2.
Definition derivable2 (f : R -> R) :=
  forall x, derivable2_pt f x.
Definition derive2 (f : R -> R) (pr2 : derivable2 f) :=
  fun x => derive2_pt f x (pr2 x).

Lemma d2_pt_impl_d1_pt : forall (f : R -> R) (x : R),
  derivable2_pt f x -> derivable_pt f x.
Proof.
  intros f x (l1,(f',(d1,d2))).
  exists (f' x).
  apply d1.
Qed.
Lemma d2_impl_d1 : forall (f : R -> R),
  derivable2 f -> derivable f.
Proof.
  intros f d2 x.
  apply d2_pt_impl_d1_pt.
  apply d2.
Qed.

Lemma derivable2_derive2_0 : forall (f : R -> R) (x l : R) (pr2 : derivable2_pt f x),
  derivable2_pt_lim f x l -> derive2_pt f x pr2 = l.
Proof.
  intros f x l (l',(f1',(df1',df2'))) (f1,(df1,df2)) ; simpl.
  apply (uniqueness_limite f1 x).
  apply (derivable_pt_lim_expr f1').
  intros ; apply (uniqueness_limite f y).
  apply df1'.
  apply df1.
  apply df2'.
  apply df2.
Qed.
Lemma derivable2_derive2_1 : forall (f : R -> R) (x l : R) (pr2 : derivable2_pt f x),
  derive2_pt f x pr2 = l -> derivable2_pt_lim f x l.
Proof.
  intros f x l (l',(f',(pr1,pr2))) Heq ; simpl in Heq.
  exists f' ; split.
  apply pr1.
  rewrite <- Heq ; apply pr2.
Qed.
Lemma derivable2_derive2 : forall (f : R -> R) (x l : R) (pr2 : derivable2_pt f x),
  prod (derivable2_pt_lim f x l -> derive2_pt f x pr2 = l)
    (derive2_pt f x pr2 = l -> derivable2_pt_lim f x l).
Proof.
  split.
  apply derivable2_derive2_0.
  apply derivable2_derive2_1.
Qed.

Lemma derivable_pt_lim_derive : forall f x pr1 l,
  derivable2_pt_lim f x l -> derivable_pt_lim (derive f pr1) x l.
Proof.
  intros.
  destruct H as (f',(d1,d2)).
  apply (derivable_pt_lim_expr f').
  intros ; apply sym_equal, derive_pt_eq_0, d1.
  apply d2.
Qed.
Lemma derivable_pt_derive : forall f x pr1,
  derivable2_pt f x -> derivable_pt (derive f pr1) x.
Proof.
  intros.
  destruct H as (l,d2).
  exists l.
  apply derivable_pt_lim_derive.
  apply d2.
Qed.
Lemma derivable_derive : forall f pr1,
  derivable2 f -> derivable (derive f pr1).
Proof.
  intros f pr1 d2 x.
  apply (derivable_pt_derive _ _ pr1).
  apply d2.
Qed.

Lemma derivable2_pt_lim_derive : forall f x pr1 l,
  derivable_pt_lim (derive f pr1) x l -> derivable2_pt_lim f x l.
Proof.
  intros.
  exists (derive f pr1) ; split.
  intros ; apply (derive_pt_eq_1 _ _ _ (pr1 x0)) ; reflexivity.
  apply H.
Qed.
Lemma derivable2_pt_derive : forall f x pr1,
  derivable_pt (derive f pr1) x -> derivable2_pt f x.
Proof.
  intros.
  destruct H as (l,d2).
  exists l.
  apply (derivable2_pt_lim_derive _ _ pr1).
  apply d2.
Qed.
Lemma derivable2_derive : forall f pr1,
  derivable (derive f pr1) -> derivable2 f.
Proof.
  intros f pr1 d2 x.
  apply (derivable2_pt_derive _ _ pr1).
  apply d2.
Qed.
Lemma derive_pt_derive : forall f x pr1 pr2 pr3,
  derive_pt (derive f pr1) x pr2 = derive2_pt f x pr3.
Proof.
  intros.
  destruct pr2 as (l,d2) ;
  destruct pr3 as (l',d3) ;
  simpl.
  apply (uniqueness_limite (derive f pr1) x).
  apply d2.
  apply derivable_pt_lim_derive.
  apply d3.
Qed.

Lemma derivable2_pt_lim_derivable_pt_lim :
  forall f' f x l,
  (forall x, derivable_pt_lim f x (f' x)) ->
  derivable_pt_lim f' x l ->
  derivable2_pt_lim f x l.
Proof.
  intros f' f x l H H'.
  exists f' ; split.
  apply H.
  apply H'.
Qed.

Lemma derivable2_pt_lim_derivable_pt_lim_bis :
  forall f f' x l,
  (forall x, derivable_pt_lim f x (f' x)) ->
  derivable2_pt_lim f x l -> derivable_pt_lim f' x l.
Proof.
  intros f f' x l Df (f1,(D1f,D2f)).
  apply (derivable_pt_lim_expr f1).
  intros ; apply (uniqueness_limite f y).
  apply D1f.
  apply Df.
  apply D2f.
Qed.

(** * Primitive of a continuous function *)

Lemma cont_impl_Rint : forall (f : R -> R),
  continuity f -> (forall (a b : R), Riemann_integrable f a b).
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  apply continuity_implies_RiemannInt.
  apply r.
  intros ; apply H.
  apply RiemannInt_P1.
  apply RiemannInt_P6.
  apply r.
  intros ; apply H.
Qed.

Lemma derivable_pt_lim_prim : forall (f : R -> R) (a x : R) (Cf : continuity f),
  derivable_pt_lim (fun x => RiemannInt (cont_impl_Rint f Cf a x)) x (f x).
Proof.
  intros.
  assert (h : x-1 <= x+1).
    Fourier.fourier.
  assert (C0 : forall x0 : R, x-1 <= x0 <= x+1 -> continuity_pt f x0).
    intros ; apply Cf.
  apply (derivable_pt_lim_expr_loc (fun x0 => RiemannInt (cont_impl_Rint f Cf a (x-1)) +
    primitive h (FTC_P1 h C0) x0) _ _ _ (mkposreal _ Rlt_0_1)).
    simpl ; intros.
    rewrite <- (RiemannInt_P26 (cont_impl_Rint f Cf a (x-1)) (cont_impl_Rint f Cf (x-1) y)).
    apply Rplus_eq_compat_l.
    unfold primitive.
    destruct (Rle_dec (x - 1) y).
    destruct (Rle_dec y (x + 1)).
    apply RiemannInt_P5.
    apply Rabs_lt_encadre_cor in H.
    elim n ; apply Rlt_le ; apply H.
    apply Rabs_lt_encadre_cor in H.
    elim n ; apply Rlt_le ; apply H.
  rewrite <- (Rplus_0_l (f x)).
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply RiemannInt_P28.
  apply (Rabs_le_encadre_cor x x 1).
  rewrite (Rminus_eq0), Rabs_R0 ;
  apply Rle_0_1.
Qed.
Lemma derivable_pt_prim : forall (f : R -> R) (a x : R) (Cf : continuity f),
  derivable_pt (fun x => RiemannInt (cont_impl_Rint f Cf a x)) x.
Proof.
  intros.
  exists (f x).
  apply derivable_pt_lim_prim.
Qed.
Lemma derivable_prim : forall (f : R -> R) (a : R) (Cf : continuity f),
  derivable (fun x => RiemannInt (cont_impl_Rint f Cf a x)).
Proof.
  intros f a Cf x.
  apply derivable_pt_prim.
Qed.
Lemma derive_pt_prim : forall (f : R -> R) (a x : R) (Cf : continuity f) pr,
  derive_pt (fun x => RiemannInt (cont_impl_Rint f Cf a x)) x pr = f x.
Proof.
  intros.
  apply (derive_pt_eq _ _ _ _).
  apply derivable_pt_lim_prim.
Qed.

(** * Operations on the Riemann integral *)

(** Change of expression *)

Lemma Riemann_integrable_expr : forall (f g : R -> R) (a b : R),
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x)
    -> Riemann_integrable f a b -> Riemann_integrable g a b.
Proof.
  intros f g a b Heq pr_f.
  intro eps.
  elim (pr_f eps) ; clear pr_f ; intros phi (psi, pr_f).
  exists phi.
  exists psi.
  split ; intros.
  rewrite <- (Heq t H).
  apply (proj1 pr_f t H).
  apply pr_f.
Qed.
Lemma RiemannInt_expr : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (Heq : forall x, Rmin a b <= x <= Rmax a b -> f x = g x),
    RiemannInt pr_f = RiemannInt pr_g.
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  apply RiemannInt_P18.
  apply r.
  intros.
  apply Heq.
  split.
  rewrite (Rmin_eq_l _ _ r).
  apply Rlt_le ; apply H.
  rewrite (Rmax_eq_l _ _ r).
  apply Rlt_le ; apply H.
  rewrite (RiemannInt_P8 pr_f (RiemannInt_P1 pr_f)).
  rewrite (RiemannInt_P8 pr_g (RiemannInt_P1 pr_g)).
  apply Ropp_eq_compat.
  apply RiemannInt_P18.
  apply Rlt_le ; apply r.
  intros.
  apply Heq.
  split.
  rewrite (Rmin_eq_r _ _ r).
  apply Rlt_le ; apply H.
  rewrite (Rmax_eq_r _ _ r).
  apply Rlt_le ; apply H.
Qed.

(** Constant function *)

Lemma Riemann_integrable_const : forall (c a b : R),
  Riemann_integrable (fun x => c) a b.
Proof.
  intros.
  apply RiemannInt_P14.
Qed.
Lemma RiemannInt_const : forall (c a b : R) (pr : Riemann_integrable (fun x => c) a b),
  RiemannInt pr = c * (b-a).
Proof.
  intros.
  apply RiemannInt_P15.
Qed.

(** Addition *)

Lemma Riemann_integrable_plus : forall (f g : R -> R) (a b : R),
  Riemann_integrable f a b -> Riemann_integrable g a b ->
    Riemann_integrable (fun x => f x + g x) a b.
Proof.
  intros f g a b pr_f pr_g.
  apply (Riemann_integrable_expr (fun x => f x + 1 * g x)).
  intros ; ring.
  apply (RiemannInt_P10 1 pr_f pr_g).
Qed.
Lemma RiemannInt_plus : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (pr : Riemann_integrable (fun x => f x + g x) a b),
  RiemannInt pr = RiemannInt pr_f + RiemannInt pr_g.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_g)).
  rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 1 pr_f pr_g)).
  apply RiemannInt_expr.
  intros ; ring.
Qed.

(** Subtraction *)

Lemma Riemann_integrable_minus : forall (f g : R -> R) (a b : R),
  Riemann_integrable f a b -> Riemann_integrable g a b ->
    Riemann_integrable (fun x => f x - g x) a b.
Proof.
  intros f g a b pr_f pr_g.
  apply (Riemann_integrable_expr (fun x => f x + (-1) * g x)).
  intros ; ring.
  apply (RiemannInt_P10 (-1) pr_f pr_g).
Qed.
Lemma RiemannInt_minus : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (pr : Riemann_integrable (fun x => f x - g x) a b),
  RiemannInt pr = RiemannInt pr_f - RiemannInt pr_g.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_g)).
  unfold Rminus. rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 (-1) pr_f pr_g)).
  apply RiemannInt_expr.
  intros ; ring.
Qed.

(** Opposite *)

Lemma Riemann_integrable_opp : forall (f : R -> R) (a b : R),
  Riemann_integrable f a b ->
    Riemann_integrable (fun x => - f x) a b.
Proof.
  intros f a b pr_f.
  apply (Riemann_integrable_expr (fun x => 0 + (-1) * f x)).
  intros ; ring.
  apply (RiemannInt_P10 (-1) (Riemann_integrable_const _ _ _) pr_f).
Qed.
Lemma RiemannInt_opp : forall (f : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b)
  (pr : Riemann_integrable (fun x => - f x) a b),
  RiemannInt pr = - RiemannInt pr_f.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_f)).
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- (Rplus_0_l (-1 * RiemannInt pr_f)).
  assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
    rewrite RiemannInt_const.
    ring.
    rewrite H ; clear H.
  rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (-1) (Riemann_integrable_const 0 a b) pr_f)).
  apply RiemannInt_expr.
  intros ; ring.
Qed.

(** Multiplication by a scalar *)

Lemma Riemann_integrable_scal : forall (f : R -> R) (a b c : R),
  Riemann_integrable f a b ->
    Riemann_integrable (fun x => c * f x) a b.
Proof.
  intros f a b c pr_f.
  apply (Riemann_integrable_expr (fun x => 0 + c * f x)).
  intros ; ring.
  apply (RiemannInt_P10 (c) (Riemann_integrable_const _ _ _) pr_f).
Qed.
Lemma RiemannInt_scal : forall (f : R -> R) (a b c : R)
  (pr_f : Riemann_integrable f a b)
  (pr : Riemann_integrable (fun x => c * f x) a b),
  RiemannInt pr = c * RiemannInt pr_f.
Proof.
  intros.
  rewrite <- (Rplus_0_l (c * RiemannInt pr_f)).
  assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
    rewrite RiemannInt_const.
    ring.
    rewrite H ; clear H.
  rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (c) (Riemann_integrable_const 0 a b) pr_f)).
  apply RiemannInt_expr.
  intros ; ring.
Qed.

(** Increase by a constant *)

Lemma RiemannInt_Rabs_le_const : forall (f : R -> R) (a b e : R)
  (pr : Riemann_integrable f a b),
  (forall x, Rmin a b <= x <= Rmax a b -> Rabs (f x) <= e) ->
  Rabs (RiemannInt pr) <= e * Rabs (b - a).
Proof.
  intros f a b e pr Hle.
  destruct (Rle_lt_dec a b).
  assert (pr_abs : Riemann_integrable (fun x => Rabs (f x)) a b).
    apply (RiemannInt_P16 pr).
  apply (Rle_trans _ (RiemannInt pr_abs)).
  apply RiemannInt_P17.
  apply r.
  rewrite Rabs_right.
  rewrite <- (RiemannInt_const _ _ _ (Riemann_integrable_const _ _ _)).
  apply RiemannInt_P19.
  apply r.
  intros ; apply Hle.
  split.
  rewrite (Rmin_eq_l _ _ r).
  apply Rlt_le ; apply H.
  rewrite (Rmax_eq_l _ _ r).
  apply Rlt_le ; apply H.
  apply Rge_minus.
  apply Rle_ge, r.

  rewrite (RiemannInt_P8 pr (RiemannInt_P1 pr)) ;
  rewrite Rabs_Ropp.
  assert (Rabs (b-a) = a-b).
  rewrite Rabs_left.
  ring.
  apply Rlt_minus.
  apply r.
  rewrite H ; clear H.
  assert (pr_abs : Riemann_integrable (fun x => Rabs (f x)) b a).
    apply (RiemannInt_P16 (RiemannInt_P1 pr)).
  apply (Rle_trans _ (RiemannInt pr_abs)).
  apply RiemannInt_P17.
  apply Rlt_le, r.
  rewrite <- (RiemannInt_const _ _ _ (Riemann_integrable_const _ _ _)).
  apply RiemannInt_P19.
  apply Rlt_le, r.
  intros ; apply Hle.
  split.
  rewrite (Rmin_eq_r _ _ r).
  apply Rlt_le ; apply H.
  rewrite (Rmax_eq_r _ _ r).
  apply Rlt_le ; apply H.
Qed.

(** * Value theorem *)

Lemma Value_theorem : forall (f : R -> R) (a b : R) (pr : derivable f),
  exists c : R, f b - f a = derive f pr c * (b-a) /\ Rmin a b <= c <= Rmax a b.
Proof.
  intros.
  destruct (Rtotal_order a b).
  cut (exists c : R, f b - f a = derive f pr c * (b - a) /\ a < c < b).
    intros (c,MVT).
    exists c.
    split.
    apply MVT.
    rewrite Rmin_eq_l, Rmax_eq_l ; [| apply Rlt_le ; apply H | apply Rlt_le ; apply H].
    split ; apply Rlt_le ; apply MVT.
    apply MVT_cor1 ; apply H.
  destruct H.
  exists a.
  split.
  rewrite H ; ring.
  rewrite H ; split.
  apply Rmin_l.
  apply RmaxLess1.
  cut (exists c : R, f a - f b = derive f pr c * (a - b) /\ b < c < a).
    intros (c,MVT).
    exists c.
    split.
    rewrite <- (Ropp_minus_distr' (f b)).
    rewrite <- (Ropp_minus_distr' b).
    rewrite Ropp_mult_distr_r_reverse.
    apply Ropp_eq_compat.
    apply MVT.
    rewrite Rmin_eq_r, Rmax_eq_r ; [| apply H | apply H].
    split ; apply Rlt_le ; apply MVT.
    apply MVT_cor1 ; apply H.
Qed.
