Require Import Reals.

Require Import Arithmetique Function1 Function2.
Require Import Probleme.

Open Local Scope R_scope.

(** Dans ce fichier, toutes les preuves ont été faites manuellement *)

(** * Lemmes complémentaires *)

Definition PrimParam (f : R -> R -> R) (a : R)
  (RIf : forall x y, Riemann_integrable (fun x => f x y) a x)
  (x y : R) := RiemannInt (RIf x y).

Lemma continuity2_pt_PrimParam : forall f a RIf x y,
  continuity2 f ->
  continuity2_pt (PrimParam f a RIf) x y.
Proof.
  intros.
  cut (forall eps : posreal, exists delta : posreal, forall x' y',
    Rabs (x'-x) < delta -> Rabs (y'-y) < delta ->
    Rabs (PrimParam f a RIf x' y' - PrimParam f a RIf x y) <= eps).
  intros ; intro.
  assert (0 < eps/2).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rlt_R0_R2].
    set (eps' := mkposreal _ H1).
  elim (H0 eps') ; clear H0 ; intros delta Cf.
  exists delta ; intros.
  apply (Rle_lt_trans _ (eps')).
  apply (Cf _ _ H0 H2).
  rewrite (double_var eps), <- (Rplus_0_r eps').
  apply Rplus_lt_compat_l.
  apply H1.

  intro.
  assert (He1 : 0 < eps / (Rabs (x-a) + 1)).
    apply Rdiv_lt_0_compat ;
    [apply eps | apply Rplus_le_lt_0_compat].
    apply Rabs_pos.
    apply Rlt_0_1.
    set (eps1 := mkposreal _ He1).
  assert (unif_cont2_pave f (Rmin a x -1) (Rmax a x +1) (y-1) (y+1)).
    apply cont2_impl_unif_cont2.
    apply H.
  elim (H0 eps1) ; clear H0 ; intros d1 H0.
  assert (Cf : forall x' y', Rmin a x-1 <= x' <= Rmax a x+1 -> y-1 <= y' <= y+1 ->
    Rabs (x'-x) < d1 -> Rabs (y'-y) < d1 -> Rabs (f x' y') < Rabs (f x y) + eps1).
    intros.
    rewrite <- (Rplus_0_r (Rabs (f x' y'))), <- (Rplus_opp_l (Rabs (f x y))),
      <- Rplus_assoc, Rplus_comm.
      apply Rplus_lt_compat_l.
      apply (Rle_lt_trans _ (Rabs (f x' y' - f x y))).
      apply Rabs_triang_inv.
      apply H0.
      split.
        apply (Rle_trans _ (Rmin a x)).
        apply (Rle_minus2 _ _ _).
        apply Rlt_le, Rlt_plus_1.
        apply Rmin_r.
        apply (Rle_trans _ (Rmax a x)).
        apply RmaxLess2.
        apply Rlt_le, Rlt_plus_1.
      apply H1.
      split ; [apply (Rle_minus2 _ _ _)|] ; apply Rlt_le, Rlt_plus_1.
      apply H2.
      apply H3.
      apply H4.
  assert (Hd2 : 0 < eps1 / (Rabs (f x y) + eps1)).
    apply Rdiv_lt_0_compat ; [apply eps1 | apply Rplus_le_lt_0_compat].
    apply Rabs_pos.
    apply eps1.
    set (d2 := mkposreal _ Hd2).
  assert (Hd : 0 < Rmin 1 (Rmin d1 d2)).
    apply (Rmin_pos _ _ Rlt_0_1) ;
    apply Rmin_pos ; [apply d1 | apply d2].
    set (delta := mkposreal _ Hd).
  exists delta ; intros.
  apply (Rle_trans _ (Rabs (PrimParam f a RIf x' y' - PrimParam f a RIf x y')
    + Rabs (PrimParam f a RIf x y' - PrimParam f a RIf x y))).
    assert ((PrimParam f a RIf x' y' - PrimParam f a RIf x y) =
      (PrimParam f a RIf x' y' - PrimParam f a RIf x y') +
      (PrimParam f a RIf x y' - PrimParam f a RIf x y)).
      ring.
    rewrite H3 ; clear H3 ; apply Rabs_triang.
  apply (Rle_trans _ (d2 * (Rabs (f x y) + eps1) + Rabs (x-a) * eps1)).
  apply Rplus_le_compat.
  apply (Rle_trans _ (Rabs (x'-x) * (Rabs (f x y) + eps1))).
  assert (Riemann_integrable (fun x => f x y') x x').
    apply (@RiemannInt_P24 _ _ a _).
    apply RiemannInt_P1.
    apply (RIf x y').
    apply (RIf x' y').
  assert (PrimParam f a RIf x' y' - PrimParam f a RIf x y' = RiemannInt X).
    unfold Rminus, PrimParam ;
    rewrite Rplus_comm, <- (RiemannInt_P8 (RiemannInt_P1 (RIf x y'))).
    apply RiemannInt_P26.
    rewrite H3 ; clear H3.
    rewrite Rmult_comm ; apply RiemannInt_Rabs_le_const.
    intros ; apply Rlt_le, Cf.
    destruct (Rle_lt_dec x x') ;
    [rewrite (Rmin_eq_l _ _ r), (Rmax_eq_l _ _ r) in H3|
    rewrite (Rmin_eq_r _ _ r), (Rmax_eq_r _ _ r) in H3].
    split ;
    [apply (Rle_trans _ x)|apply (Rle_trans _ x')].
    apply (Rle_trans _ (Rmin a x)).
    apply (Rle_minus2 _ _ _), Rlt_le, Rlt_plus_1.
    apply Rmin_r.
    apply H3.
    apply H3.
    apply (Rle_trans _ (x+1)).
    rewrite Rplus_comm ; apply (Rle_minus2 _ _ _).
    apply (Rle_trans _ (Rabs (x'-x)) _ (Rabs_maj1 _)).
    apply (Rle_trans _ _ _ (Rlt_le _ _ H1)).
    simpl ; apply Rmin_l.
    apply Rplus_le_compat_r, RmaxLess2.
    split ;
    [apply (Rle_trans _ x')|apply (Rle_trans _ x)].
    apply (Rle_trans _ (x-1)).
    unfold Rminus ; apply Rplus_le_compat_r, Rmin_r.
    apply (Rle_minus2 _ _ _) ;
    rewrite Rplus_comm ; apply (Rle_minus2 _ _ _).
    apply (Rle_trans _ (Rabs (x'-x)) _).
    rewrite <- Ropp_minus_distr' ; apply Rabs_maj2.
    apply (Rle_trans _ _ _ (Rlt_le _ _ H1)).
    simpl ; apply Rmin_l.
    apply H3.
    apply H3.
    apply (Rle_trans _ (Rmax a x)).
    apply RmaxLess2.
    apply Rlt_le, Rlt_plus_1.
    apply (Rabs_le_encadre_cor _ _ _).
    apply (Rle_trans _ _ _ (Rlt_le _ _ H2)).
    simpl ; apply Rmin_l.
  apply (Rle_lt_trans _ (Rabs (x'-x))).
  destruct (Rle_lt_dec x x') ;
  [rewrite (Rmin_eq_l _ _ r), (Rmax_eq_l _ _ r) in H3|
  rewrite (Rmin_eq_r _ _ r), (Rmax_eq_r _ _ r) in H3].
  repeat rewrite Rabs_right.
  unfold Rminus ; apply Rplus_le_compat_r ; apply H3.
  apply Rge_minus, Rle_ge, r.
  apply Rge_minus, Rle_ge, H3.
  repeat rewrite Rabs_left1.
  unfold Rminus ; apply Ropp_le_contravar, Rplus_le_compat_r ; apply H3.
  apply Rle_minus, Rlt_le, r.
  apply Rle_minus, H3.
  apply (Rlt_le_trans _ delta _ H1) ; simpl ;
  apply (Rle_trans _ (Rmin d1 d2) _ (Rmin_r _ _) (Rmin_l _ _)).
  apply (Rlt_le_trans _ delta _ H2) ; simpl ;
  apply (Rle_trans _ (Rmin d1 d2) _ (Rmin_r _ _) (Rmin_l _ _)).
  apply Rmult_le_compat_r.
  apply Rplus_le_le_0_compat ; [apply Rabs_pos | apply Rlt_le, eps1].
  apply (Rle_trans _ _ _ (Rlt_le _ _ H1)); simpl ;
  apply (Rle_trans _ (Rmin d1 d2) _ (Rmin_r _ _) (Rmin_r _ _)).

  unfold PrimParam ; rewrite <- (RiemannInt_minus _ _ a x _ _ (
  Riemann_integrable_minus _ _ _ _ (RIf x y') (RIf x y))).
  rewrite Rmult_comm ; apply RiemannInt_Rabs_le_const.
  intros.
  apply Rlt_le, H0.
  split ; [apply (Rle_trans _ (Rmin a x))|apply (Rle_trans _ (Rmax a x))].
  apply (Rle_minus2 _ _ _), Rlt_le, Rlt_plus_1.
  apply H3.
  apply H3.
  apply Rlt_le, Rlt_plus_1.
  split ; [apply (Rle_trans _ (Rmin a x))|apply (Rle_trans _ (Rmax a x))].
  apply (Rle_minus2 _ _ _), Rlt_le, Rlt_plus_1.
  apply H3.
  apply H3.
  apply Rlt_le, Rlt_plus_1.
  split ; [apply (Rle_minus2 _ _ _)|] ; apply Rlt_le, Rlt_plus_1.
  apply (Rabs_le_encadre_cor _ _ _), (Rle_trans _ _ _ (Rlt_le _ _ H2)).
  simpl ; apply Rmin_l.
  rewrite Rminus_eq0, Rabs_R0 ; apply d1.
  apply (Rlt_le_trans _ _ _ H2) ; simpl ;
  apply (Rle_trans _ (Rmin d1 d2) _ (Rmin_r _ _) (Rmin_l _ _)).
  simpl ; apply Req_le ; field.
  split ; apply sym_not_eq, Rlt_not_eq, Rplus_le_lt_0_compat.
  apply Rabs_pos.
  apply Rlt_0_1.
  apply Rmult_le_pos.
  apply Rabs_pos.
  apply Rplus_le_le_0_compat.
  apply Rabs_pos.
  apply Rle_0_1.
  apply eps.
Qed.

Lemma differentiable_pt_lim_PrimParam : forall f a RIf x y
  (D01 : derivable01 f)
  (RIdf : forall x y, Riemann_integrable (fun x => (derive01 f D01) x y) a x),
  continuity2 f -> continuity2 (derive01 f D01) ->
  differentiable_pt_lim (PrimParam f a RIf) x y (f x y , PrimParam _ _ RIdf x y).
Proof.
  intros.
  assert (forall x y, derivable10_pt_lim (PrimParam f a RIf) x y (f x y)).
    intros.
    set (g x0 := f x0 y0).
    assert (g x0 = f x0 y0).
      unfold g ; reflexivity.
      rewrite <- H1 ; clear H1.
    apply (derivable_pt_lim_expr (fun x => RiemannInt
       (cont_impl_Rint g (cont2_impl_cont_0 f H y0) a x))).
       intros ; unfold PrimParam ; apply RiemannInt_expr.
       intros ; reflexivity.
    apply derivable_pt_lim_prim.
  assert (derivable10 (PrimParam f a RIf)).
    intros x0 y0 ; exists (f x0 y0) ; apply H1.
  assert (forall x y, derive10 (PrimParam f a RIf) H2 x y = f x y).
    intros ; apply (derivable10_derive10 _ _ _ _ _) ; apply H1.
  rewrite <- H3.
  assert (forall x y, derivable01_pt_lim (PrimParam f a RIf) x y
    (PrimParam (derive01 f D01) a RIdf x y)).
    intros.
    apply (derivable_pt_lim_expr (Param f a x0 (cont2_impl_Rint01 f H a x0))).
      intros ; unfold Param, PrimParam ; apply RiemannInt_expr.
      intros ; reflexivity.
    assert (forall x0 y0, PrimParam (derive01 f D01) a RIdf x0 y0
      = Param (derive01 f D01) a x0 (cont2_impl_Rint01 (derive01 f D01) H0 a x0) y0).
      intros ; unfold Param, PrimParam ; apply RiemannInt_expr.
      intros ; reflexivity.
    rewrite H4 ; clear H4.
    apply derivable_pt_lim_param.
  assert (derivable01 (PrimParam f a RIf)).
    intros x0 y0 ; exists (PrimParam (derive01 f D01) a RIdf x0 y0) ; apply H4.
  assert (forall x y, derive01 (PrimParam f a RIf) H5 x y = PrimParam (derive01 f D01) a RIdf x y).
    intros ; apply (derivable01_derive01 _ _ _ _ _) ; apply H4.
  rewrite <- H6.
  apply derivable_differentiable_pt_lim.
  apply (continuity2_pt_expr f).
    intros ; apply sym_equal ; apply H3.
    apply H.
  apply (continuity2_pt_expr (PrimParam (derive01 f D01) a RIdf)).
    intros ; apply sym_equal ; apply H6.
  apply continuity2_pt_PrimParam.
  apply H0.
Qed.


(** * Paramètres *)

Hypothesis Cf : continuity2 f.
Hypothesis D10_f : derivable10 f.
Hypothesis C10_f : continuity2 (derive10 f D10_f).
Lemma Cont10_f : forall tau, continuity (fun xi => f xi tau).
Proof.
  intros tau xi.
  apply (cont2_impl_cont_pt _ _ _).
  apply Cf.
Qed.
Lemma RInt1_f : forall a b tau, Riemann_integrable (fun xi => f xi tau) a b.
Proof.
  intros.
  apply cont_impl_Rint.
  apply Cont10_f.
Qed.

(** * Fonctions auxiliaires *)
(** gamma0 *)
Definition gamma0 x t tau := RiemannInt (RInt1_f (x-c*(t-tau)) (x+c*(t-tau)) tau).

Lemma Cont1_gamma0 : forall t, continuity2 (fun tau x => gamma0 x t tau).
Proof.
  intros t tau x ; unfold gamma0.
  apply (continuity2_pt_expr (fun tau x => RiemannInt (RInt1_f 0 (x+c*(t-tau)) tau)
    - RiemannInt (RInt1_f 0 (x-c*(t-tau)) tau))).
    intros ; unfold Rminus.
    rewrite <- (RiemannInt_P8 (RiemannInt_P1 (RInt1_f 0 (y' + - (c * (t + - x'))) x'))).
    rewrite Rplus_comm.
    rewrite (RiemannInt_P26 _ _ (RiemannInt_P24 (RiemannInt_P1 (RInt1_f 0 (y' + - (c * (t + - x'))) x')) (RInt1_f 0 (y' + c * (t + - x')) x'))).
    apply RiemannInt_P5.
  apply continuity2_pt_minus.
  apply (continuity2_pt_comp2 (fun t1 t2 => RiemannInt (RInt1_f 0 t1 t2)) (fun x0 y => y+c*(t-x0)) Fct2_Var1).
  apply continuity2_pt_PrimParam.
  apply Cf.
  apply continuity2_pt_plus.
  apply continuity2_pt_var2.
  apply (continuity2_pt_proj1 (fun tau => c * (t-tau)) _ _).
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  apply continuity_pt_const ; intros _ _ ; reflexivity.
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
  apply (continuity2_pt_comp2 (fun t1 t2 => RiemannInt (RInt1_f 0 t1 t2)) (fun x0 y => y-c*(t-x0)) Fct2_Var1).
  apply continuity2_pt_PrimParam.
  apply Cf.
  apply continuity2_pt_minus.
  apply continuity2_pt_var2.
  apply (continuity2_pt_proj1 (fun tau => c *(t-tau)) _ _).
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  apply continuity_pt_const ; intros _ _ ; reflexivity.
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
Qed.

Lemma Cont2_gamma0 : forall x, continuity2 (fun tau t => gamma0 x t tau).
Proof.
  intros x tau t ; unfold gamma0.
  apply (continuity2_pt_expr (fun tau t => RiemannInt (RInt1_f 0 (x+c*(t-tau)) tau)
    - RiemannInt (RInt1_f 0 (x-c*(t-tau)) tau))).
    intros ; unfold Rminus.
    rewrite <- (RiemannInt_P8 (RiemannInt_P1 (RInt1_f 0 (x + - (c * (y' + - x'))) x'))).
    rewrite Rplus_comm.
    rewrite (RiemannInt_P26 _ _ (RiemannInt_P24 (RiemannInt_P1 (RInt1_f 0 (x + - (c * (y' + - x'))) x')) (RInt1_f 0 (x + c * (y' + - x')) x'))).
    apply RiemannInt_P5.
  apply continuity2_pt_minus.
  apply (continuity2_pt_comp2 (fun t1 t2 => RiemannInt (RInt1_f 0 t1 t2)) (fun x0 t => x+c*(t-x0)) Fct2_Var1).
  apply continuity2_pt_PrimParam.
  apply Cf.
  apply continuity2_pt_plus.
  apply continuity2_pt_const.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
  apply continuity2_pt_var2.
  apply continuity2_pt_var1.
  apply continuity2_pt_var1.
  apply (continuity2_pt_comp2 (fun t1 t2 => RiemannInt (RInt1_f 0 t1 t2)) (fun x0 t => x-c*(t-x0)) Fct2_Var1).
  apply continuity2_pt_PrimParam.
  apply Cf.
  apply continuity2_pt_minus.
  apply continuity2_pt_const.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
  apply continuity2_pt_var2.
  apply continuity2_pt_var1.
  apply continuity2_pt_var1.
Qed.

Lemma RInt_gamma0 : forall x tau t, Riemann_integrable (fun tau => gamma0 x t tau) 0 tau.
Proof.
  intros.
  apply cont_impl_Rint.
  apply (cont2_impl_cont (fun tau t => gamma0 x t tau)).
  apply Cont2_gamma0.
Qed.

(** gamma1 *)

Definition gamma1 x t tau := f (x + c * (t-tau)) tau - f (x-c * (t-tau)) tau.

Lemma gamma0_01_lim : forall x t tau, derivable01_pt_lim (fun tau x => gamma0 x t tau) tau x
  (gamma1 x t tau).
Proof.
  intros.
  unfold gamma0, gamma1.
  set (g xi := f xi tau).
  assert (f (x + c * (t - tau)) tau - f (x - c * (t - tau)) tau =
    fst (- g (x - c * (t - tau)), g (x+c*(t-tau))) * (1-0) +
    snd (- g (x - c * (t - tau)), g (x+c*(t-tau))) * (1+0)).
    unfold g ; simpl ; ring.
  rewrite H ; clear H.
  apply (derivable_pt_lim_expr (fun x => Rint g
    (cont_impl_Rint _ (Cont10_f tau)) (x-c*(t-tau)) (x+c*(t-tau)))).
    intros ; unfold Rint ; apply RiemannInt_expr.
    intros ; reflexivity.
  apply derivable_pt_lim_comp2.
  apply differentiable_pt_lim_Rint.
  apply (cont2_impl_cont _).
  apply Cf.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
Qed.
Lemma gamma0_01_pr : forall t, derivable01 (fun tau x => gamma0 x t tau).
Proof.
  intros t tau x.
  exists (gamma1 x t tau).
  apply gamma0_01_lim.
Qed.
Lemma gamma0_01 : forall x t tau, derive01 (fun tau x => gamma0 x t tau) (gamma0_01_pr t) tau x =
  (gamma1 x t tau).
Proof.
  intros ;
  apply (derivable01_derive01 _ _ _ _ _).
  apply gamma0_01_lim.
Qed.

Lemma Cont_gamma1 : forall t, continuity2 (derive01 (fun tau x => gamma0 x t tau) (gamma0_01_pr t)).
Proof.
  intros t tau x.
  apply (continuity2_pt_expr (fun tau x => gamma1 x t tau)).
    intros ; apply sym_equal, gamma0_01.
  unfold gamma1.
    apply continuity2_pt_minus.
  apply continuity2_pt_comp2.
  apply Cf.
    apply continuity2_pt_plus.
  apply continuity2_pt_var2.
  apply (continuity2_pt_proj1 (fun tau => c*(t-tau)) _ _).
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  apply continuity_pt_const.
    intros a b ; reflexivity.
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
  apply continuity2_pt_comp2.
  apply Cf.
    apply continuity2_pt_minus.
  apply continuity2_pt_var2.
  apply (continuity2_pt_proj1 (fun tau => c*(t-tau)) _ _).
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  apply continuity_pt_const.
    intros a b ; reflexivity.
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
Qed.

Lemma RInt_gamma1 : forall x t, Riemann_integrable (fun tau => gamma1 x t tau) 0 t.
Proof.
  intros.
  unfold gamma1.
  apply cont_impl_Rint.
  intros tau.
  apply (continuity_pt_expr (fun tau => derive01 _ (gamma0_01_pr t) tau x)).
    intros ; rewrite gamma0_01.
    unfold gamma1 ; reflexivity.
  apply (cont2_impl_cont_0 _ (Cont_gamma1 t)).
Qed.

(** gamma1' *)

Definition gamma1' x t tau := f (x + c * (t-tau)) tau + f (x-c * (t-tau)) tau.

Lemma gamma0_01'_lim : forall x t tau, derivable01_pt_lim (fun tau t => gamma0 x t tau) tau t
  (c* gamma1' x t tau).
Proof.
  intros.
  unfold gamma0, gamma1'.
  set (g xi := f xi tau).
  assert (c * (f (x + c * (t - tau)) tau + f (x - c * (t - tau)) tau) =
    fst (- g (x - c * (t - tau)), g (x+c*(t-tau))) * (0-c*(1-0)) +
    snd (- g (x - c * (t - tau)), g (x+c*(t-tau))) * (0+c*(1-0))).
    unfold g ; simpl ; ring.
  rewrite H ; clear H.
  apply (derivable_pt_lim_expr (fun t => Rint g
    (cont_impl_Rint _ (Cont10_f tau)) (x-c*(t-tau)) (x+c*(t-tau)))).
    intros ; unfold Rint ; apply RiemannInt_expr.
    intros ; reflexivity.
  apply derivable_pt_lim_comp2.
  apply differentiable_pt_lim_Rint.
  apply (cont2_impl_cont _ Cf).
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
Qed.
Lemma gamma0_01'_pr : forall x, derivable01 (fun tau t => gamma0 x t tau).
Proof.
  intros x tau t.
  exists (c*gamma1' x t tau).
  apply gamma0_01'_lim.
Qed.
Lemma gamma0_01' : forall x t tau, derive01 (fun tau t => gamma0 x t tau) (gamma0_01'_pr x) tau t =
  (c*gamma1' x t tau).
Proof.
  intros ;
  apply (derivable01_derive01 _ _ _ _ _).
  apply gamma0_01'_lim.
Qed.

Lemma Cont2_gamma1' : forall x, continuity2 (derive01 (fun tau t => gamma0 x t tau) (gamma0_01'_pr x)).
Proof.
  intros x tau t.
  apply (continuity2_pt_expr (fun tau t => c * gamma1' x t tau)).
    intros ; apply sym_equal, gamma0_01'.
  unfold gamma1'.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_plus.
  apply continuity2_pt_comp2.
  apply Cf.
    apply continuity2_pt_plus.
  apply continuity2_pt_const.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
    apply continuity2_pt_var2.
    apply continuity2_pt_var1.
  apply continuity2_pt_var1.
  apply continuity2_pt_comp2.
  apply Cf.
    apply continuity2_pt_minus.
  apply continuity2_pt_const.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
    apply continuity2_pt_var2.
    apply continuity2_pt_var1.
  apply continuity2_pt_var1.
Qed.

Lemma RInt_gamma1' : forall x tau t, Riemann_integrable (fun tau => gamma1' x t tau) 0 tau.
Proof.
  intros.
  unfold gamma1'.
  apply cont_impl_Rint.
  intros tau0.
  apply (continuity_pt_expr (fun tau => 1/c * (derive01 _ (gamma0_01'_pr x) tau t))).
    intros ; rewrite gamma0_01'.
    unfold gamma1' ; field.
    apply Hc.
  apply continuity_pt_scal.
  apply (cont2_impl_cont_0 _ (Cont2_gamma1' x)).
Qed.

Lemma RInt_gamma0_01' : forall x tau t, Riemann_integrable (fun tau => derive01 (fun tau t => gamma0 x t tau) (gamma0_01'_pr x) tau t) 0 tau.
Proof.
  intros.
  apply cont_impl_Rint.
  apply (cont2_impl_cont_0 _ (Cont2_gamma1' x)).
Qed.

(** gamma2 *)

Definition gamma2 x t tau := derive10 f D10_f (x + c*(t-tau)) tau - derive10 f D10_f (x-c*(t-tau)) tau.

Lemma gamma1_01_lim : forall x t tau, derivable01_pt_lim (fun tau x => gamma1 x t tau) tau x
  (gamma2 x t tau).
Proof.
  intros ; unfold gamma1, gamma2.
  assert (derive10 f D10_f (x + c * (t - tau)) tau -
   derive10 f D10_f (x - c * (t - tau)) tau =
   derive10 f D10_f (x + c * (t - tau)) tau * (1+0) -
   derive10 f D10_f (x - c * (t - tau)) tau * (1-0)).
   ring.
   rewrite H ; clear H.
  unfold derivable01_pt_lim ;
  apply derivable_pt_lim_minus.
  apply (derivable_pt_lim_comp (fun x => x + c*(t-tau)) (fun xi => f xi tau)).
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (D10_f (x+c*(t-tau)) tau)).
    apply pr_nu.
  apply (derivable_pt_lim_comp (fun x => x - c*(t-tau)) (fun xi => f xi tau)).
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (D10_f (x-c*(t-tau)) tau)).
    apply pr_nu.
Qed.
Lemma gamma1_01_pr : forall t, derivable01 (fun tau x => gamma1 x t tau).
Proof.
  intros t tau x ; exists (gamma2 x t tau).
  apply gamma1_01_lim.
Qed.
Lemma gamma1_01 : forall x t tau, derive01 (fun tau x => gamma1 x t tau) (gamma1_01_pr t) tau x =
  (gamma2 x t tau).
Proof.
  intros.
  apply (derivable01_derive01 _ _ _ _ _).
  apply gamma1_01_lim.
Qed.

Lemma gamma1'_01_lim : forall x t tau, derivable01_pt_lim (fun tau t => gamma1' x t tau) tau t
  (c * gamma2 x t tau).
Proof.
  intros ; unfold gamma1', gamma2.
  assert (c * (derive10 f D10_f (x + c * (t - tau)) tau -
   derive10 f D10_f (x - c * (t - tau)) tau) =
   derive10 f D10_f (x + c * (t - tau)) tau * (0+c*(1-0)) +
   derive10 f D10_f (x - c * (t - tau)) tau * (0-c*(1-0))).
   ring.
   rewrite H ; clear H.
  unfold derivable01_pt_lim ;
  apply derivable_pt_lim_plus.
  apply (derivable_pt_lim_comp (fun t => x + c*(t-tau)) (fun xi => f xi tau)).
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (D10_f (x+c*(t-tau)) tau)).
    apply pr_nu.
  apply (derivable_pt_lim_comp (fun t => x - c*(t-tau)) (fun xi => f xi tau)).
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (D10_f (x-c*(t-tau)) tau)).
    apply pr_nu.
Qed.
Lemma gamma1'_01_pr : forall x, derivable01 (fun tau t => gamma1' x t tau).
Proof.
  intros x tau t ; exists (c*gamma2 x t tau).
  apply gamma1'_01_lim.
Qed.
Lemma gamma1'_01 : forall x t tau, derive01 (fun tau t => gamma1' x t tau) (gamma1'_01_pr x) tau t =
  (c*gamma2 x t tau).
Proof.
  intros.
  apply (derivable01_derive01 _ _ _ _ _).
  apply gamma1'_01_lim.
Qed.

Lemma Cont2_gamma2 : forall t, continuity2 (derive01 (fun tau x => gamma1 x t tau) (gamma1_01_pr t)).
Proof.
  intros t tau x.
  apply (continuity2_pt_expr (fun tau x => gamma2 x t tau)).
    intros ; apply sym_equal, gamma1_01.
  unfold gamma2.
    apply continuity2_pt_minus.
  apply continuity2_pt_comp2.
  apply C10_f.
    apply continuity2_pt_plus.
  apply continuity2_pt_var2.
  apply (continuity2_pt_proj1 (fun tau => c*(t-tau)) _ _).
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  apply continuity_pt_const.
    intros a b ; reflexivity.
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
  apply continuity2_pt_comp2.
  apply C10_f.
    apply continuity2_pt_minus.
  apply continuity2_pt_var2.
  apply (continuity2_pt_proj1 (fun tau => c*(t-tau)) _ _).
  apply continuity_pt_scal.
  apply continuity_pt_minus.
  apply continuity_pt_const.
    intros a b ; reflexivity.
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
Qed.
Lemma Cont1_gamma2 : forall x, continuity2 (derive01 (fun tau t => gamma1' x t tau) (gamma1'_01_pr x)).
Proof.
  intros x tau t.
  apply (continuity2_pt_expr (fun tau t => c * gamma2 x t tau)).
    intros ; apply sym_equal, gamma1'_01.
  unfold gamma2.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
  apply continuity2_pt_comp2.
  apply C10_f.
    apply continuity2_pt_plus.
  apply continuity2_pt_const.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
  apply (continuity2_pt_proj2 _ _ _).
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
  apply continuity2_pt_var1.
  apply continuity2_pt_comp2.
  apply C10_f.
    apply continuity2_pt_minus.
  apply continuity2_pt_const.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
    apply continuity2_pt_minus.
  apply (continuity2_pt_proj2 _ _ _).
  apply derivable_continuous_pt, derivable_pt_id.
  apply continuity2_pt_var1.
  apply continuity2_pt_var1.
Qed.

Lemma RInt_gamma2 : forall x tau t, Riemann_integrable (fun tau => gamma2 x t tau) 0 tau.
Proof.
  intros.
  apply cont_impl_Rint.
  intros tau0.
  apply (continuity_pt_expr (fun tau : R =>
     derive01 (fun tau x : R => gamma1 x t tau) (gamma1_01_pr t) tau x)).
     intros ; apply gamma1_01.
  apply (cont2_impl_cont_0 _ (Cont2_gamma2 t)).
Qed.

Lemma RInt_gamma1_01' : forall x tau t, Riemann_integrable
  (fun tau => derive01 (fun tau t => gamma1' x t tau) (gamma1'_01_pr x) tau t) 0 tau.
Proof.
  intros.
  apply cont_impl_Rint.
  apply (cont2_impl_cont_0 _ (Cont1_gamma2 x)).
Qed.


(** * Etude de gamma *)
Definition gamma x t := 1/(2*c) * RiemannInt (RInt_gamma0 x t t).

(** * Dérivées par rapport à x *)
(** Dérivées premières *)

Definition gamma10 x t := (1/(2*c) * RiemannInt (RInt_gamma1 x t)).

Lemma gamma10_lim : forall x t, derivable10_pt_lim gamma x t (gamma10 x t).
Proof.
  intros.
  unfold gamma, gamma10.
  apply (derivable_pt_lim_scal (fun x0 : R => RiemannInt (RInt_gamma0 x0 t t)) (1/(2*c))).
  apply (derivable_pt_lim_expr (Param _ 0 t (fun x => RInt_gamma0 x t t))).
    intros ; unfold Param ; apply RiemannInt_expr.
    intros ; reflexivity.
  assert (RiemannInt (RInt_gamma1 x t) =
    Param (derive01 (fun tau x => gamma0 x t tau) (gamma0_01_pr t)) 0 t
    (cont2_impl_Rint01 _ (Cont_gamma1 t) 0 t) x).
    unfold Param ; apply RiemannInt_expr.
    intros ; apply sym_equal, gamma0_01.
  rewrite H ; clear H.
  apply derivable_pt_lim_param.
Qed.

(** Dérivée seconde *)
Definition gamma20 x t := (1/(2*c) * RiemannInt (RInt_gamma2 x t t)).

Lemma gamma20_lim : forall x t, derivable20_pt_lim gamma x t (gamma20 x t).
Proof.
  intros.
  apply derivable20_10_pt_lim with (1 := fun x => gamma10_lim x t).
  unfold gamma10, gamma20.
  apply derivable_pt_lim_scal.
  assert (RiemannInt (RInt_gamma2 x t t) =
    Param (derive01 (fun tau x => gamma1 x t tau) (gamma1_01_pr t)) 0 t
    (cont2_impl_Rint01 _ (Cont2_gamma2 t) 0 t) x).
    unfold Param ; apply RiemannInt_expr.
    intros ; apply sym_equal, gamma1_01.
  rewrite H ; clear H.
  apply derivable_pt_lim_param.
Qed.

(** * Dérivées par rapport à t *)
(** Dérivée première *)

Definition gamma01 x t := (1/2 * RiemannInt (RInt_gamma1' x t t)).

Lemma gamma01_lim : forall x t, derivable01_pt_lim gamma x t (gamma01 x t).
Proof.
  intros ; unfold gamma, gamma01.

  assert (1 / 2 * RiemannInt (RInt_gamma1' x t t)
    = 1/(2*c) * (fst (gamma0 x t t, PrimParam (derive01 _ (gamma0_01'_pr x)) 0 (RInt_gamma0_01' x) t t) * 1 +
      snd (gamma0 x t t, PrimParam (derive01 _ (gamma0_01'_pr x)) 0 (RInt_gamma0_01' x) t t) * 1)).
  assert (c * RiemannInt (RInt_gamma1' x t t) =
    PrimParam (derive01 _ (gamma0_01'_pr x)) 0 (RInt_gamma0_01' x) t t).
    unfold PrimParam.
    rewrite <- (RiemannInt_scal _ _ _ _ _ (Riemann_integrable_scal _ _ _ _ (RInt_gamma1' x t t))).
    apply RiemannInt_expr.
    intros ; apply sym_equal, gamma0_01'.
    rewrite <- H ; clear H.
    unfold gamma0 ; simpl.
    rewrite Rminus_eq0, Rmult_0_r, Rplus_0_r, Rminus_0_r,
    RiemannInt_P9.
    field.
    apply Hc.
  rewrite H ; clear H ; unfold derivable01_pt_lim ;
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_comp2
    (PrimParam (fun tau t => gamma0 x t tau) 0 (RInt_gamma0 x))
    id id ).
  apply (differentiable_pt_lim_PrimParam (fun tau t => gamma0 x t tau)).
  apply Cont2_gamma0.
  apply Cont2_gamma1'.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_id.
Qed.


(** Dérivée seconde *)
Definition gamma02 x t := (f x t + c/2 * RiemannInt (RInt_gamma2 x t t)).

Lemma gamma02_lim : forall x t, derivable02_pt_lim gamma x t (gamma02 x t).
Proof.
  intros.
  apply derivable02_01_pt_lim with (1 := fun t => gamma01_lim x t).
  unfold gamma01.
  assert (gamma02 x t
    = 1/2 * (fst (gamma1' x t t, PrimParam (derive01 _ (gamma1'_01_pr x)) 0 (RInt_gamma1_01' x) t t) * 1 +
      snd (gamma1' x t t, PrimParam (derive01 _ (gamma1'_01_pr x)) 0 (RInt_gamma1_01' x) t t) * 1)).
      unfold gamma02.
  assert (c * RiemannInt (RInt_gamma2 x t t) =
    PrimParam (derive01 _ (gamma1'_01_pr x)) 0 (RInt_gamma1_01' x) t t).
    unfold PrimParam.
    rewrite <- (RiemannInt_scal _ _ _ _ _ (Riemann_integrable_scal _ _ _ _ (RInt_gamma2 x t t))).
    apply RiemannInt_expr.
    intros ; apply sym_equal, gamma1'_01.
    rewrite <- H ; clear H.
    unfold gamma1' ; simpl.
    rewrite Rminus_eq0, Rmult_0_r, Rplus_0_r, Rminus_0_r.
    field.
  rewrite H ; clear H.
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_comp2 (PrimParam (fun tau t : R => gamma1' x t tau) 0 (RInt_gamma1' x)) id id).
  apply (differentiable_pt_lim_PrimParam (fun tau t => gamma1' x t tau) 0 (RInt_gamma1' x) t t 
    (gamma1'_01_pr x) (RInt_gamma1_01' x)).
  intros tau t0.
  apply (continuity2_pt_expr (fun tau t => 1/c * (derive01 (fun tau t : R => gamma0 x t tau) (gamma0_01'_pr x) tau t))).
    intros ; rewrite gamma0_01'.
    field ; apply Hc.
    apply continuity2_pt_mult.
    apply continuity2_pt_const.
  apply Cont2_gamma1'.
  apply Cont1_gamma2.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_id.
Qed.