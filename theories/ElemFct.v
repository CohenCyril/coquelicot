Require Import Reals ssreflect.

Require Import Rbar Rcomplements Continuity Derive Locally.

(** * Identities *)

Lemma continuity_2d_pt_id1 :
  forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

Lemma continuity_2d_pt_id2 :
  forall x y, continuity_2d_pt (fun u v => v) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

(** * Constant functions *)

Lemma continuity_2d_pt_const :
  forall x y c, continuity_2d_pt (fun u v => c) x y.
Proof.
  intros x y c eps; exists eps; rewrite Rminus_eq_0 Rabs_R0.
  intros; apply cond_pos.
Qed.

(** * Absolute value *)

Lemma derivable_pt_lim_Rabs (x : R) :
  x <> 0 -> is_derive Rabs x (sign x).
Proof.
  move => Hx0.
  case: (Rle_lt_dec 0 x) => Hx.
  case: Hx => //= Hx.
  rewrite (proj1 (sign_0_lt x)) => //.
  by apply Rabs_derive_1.
  by apply sym_eq in Hx.
  rewrite (proj1 (sign_lt_0 x)) => //.
  by apply Rabs_derive_2.
Qed.
Lemma continuity_pt_Rabs (x : R) :
  continuity_pt Rabs x.
Proof.
  apply continuity_pt_locally => eps.
  exists eps => y Hy.
  by apply Rle_lt_trans with (1 := Rabs_triang_inv2 _ _).
Qed.

(** * Inverse function *)

Lemma is_lim_Rinv_0 : is_lim (fun x => / Rabs x) 0 p_infty.
Proof.
  move => M.
  have Hd : 0 < / Rmax 1 M.
    apply Rinv_0_lt_compat.
    apply Rlt_le_trans with (2 := Rmax_l _ _).
    by apply Rlt_0_1.
  exists (mkposreal _ Hd) => x /= Hx Hx0.
  apply Rle_lt_trans with (1 := Rmax_r 1 M).
  replace (Rmax 1 M) with (/ / Rmax 1 M)
  by (field ; apply Rgt_not_eq, Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1).
  apply Rinv_lt_contravar.
  apply Rdiv_lt_0_compat.
  by apply Rabs_pos_lt.
  apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
  by rewrite Rminus_0_r in Hx.
Qed.

(** * Square root function *)

Lemma is_lim_sqrt_p : is_lim sqrt p_infty p_infty.
Proof.
  move => M.
  exists ((Rmax 0 M)²) => x Hx.
  apply Rle_lt_trans with (1 := Rmax_r 0 M).
  rewrite -(sqrt_Rsqr (Rmax 0 M)).
  apply sqrt_lt_1_alt.
  split.
  apply Rle_0_sqr.
  by apply Hx.
  apply Rmax_l.
Qed.

(** * Exponential function *)

Lemma Rle_exp (x : R) (n : nat) :
  0 <= x -> sum_f_R0 (fun k => x^k / INR (fact k)) n <= exp x.
Proof.
  move => Hx.
  rewrite /exp /exist_exp.
  case: Alembert_C3 => /= y Hy.
  apply Rnot_lt_le => H.
  apply Rminus_lt_0 in H.
  case: (Hy _ H) => N {Hy} Hy.
  move: (Hy _ (le_plus_r n N)) => {Hy}.
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: N => [ | N IH].
  rewrite plus_0_r.
  apply Req_le.
  elim: (n) => {n H} [ | n /= <-].
  apply Rmult_comm.
  apply f_equal.
  apply Rmult_comm.
  apply Rle_trans with (1 := IH).
  rewrite -plus_n_Sm.
  move: (n + N)%nat => {n H N IH} n.
  rewrite /sum_f_R0 -/sum_f_R0.
  apply Rminus_le_0 ; ring_simplify.
  apply Rmult_le_pos.
  apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
  by apply pow_le.
Qed.

Lemma is_lim_exp_p : is_lim (fun y => exp y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => 1 + y).
  pattern p_infty at 2.
  replace p_infty with (Rbar_plus 1 p_infty) by auto.
  apply is_lim_plus.
  apply is_lim_const.
  apply is_lim_id.
  by [].
  exists 0 => y Hy.
  by apply Rlt_le, exp_ineq1.
Qed.

Lemma is_lim_exp_m : is_lim (fun y => exp y) m_infty 0.
Proof.
  search_lim.
  apply is_lim_ext with (fun y => /(exp (- y))).
  move => y ; rewrite exp_Ropp ; apply Rinv_involutive.
  apply Rgt_not_eq, exp_pos.
  apply is_lim_inv.
  apply is_lim_comp with p_infty.
  apply is_lim_exp_p.
  replace p_infty with (Rbar_opp m_infty) by auto.
  apply is_lim_opp.
  apply is_lim_id.
  by apply Rbar_locally_forall.
  by [].
  by [].
Qed.

Lemma ex_lim_exp (x : Rbar) : ex_lim (fun y => exp y) x.
Proof.
  case: x => [x | | ].
  apply ex_finite_lim_correct, ex_lim_continuity.
  apply derivable_continuous_pt, derivable_pt_exp.
  exists p_infty ; by apply is_lim_exp_p.
  exists 0 ; by apply is_lim_exp_m.
Qed.

Lemma Lim_exp (x : Rbar) : 
  Lim (fun y => exp y) x = 
    match x with
      | Finite x => exp x
      | p_infty => p_infty
      | m_infty => 0
    end.
Proof.
  apply is_lim_unique.
  case: x => [x | | ].
  apply is_lim_continuity.
  apply derivable_continuous_pt, derivable_pt_exp.
  by apply is_lim_exp_p.
  by apply is_lim_exp_m.
Qed.

Lemma is_lim_exp_aux1 : is_lim (fun y => exp y / y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => (1 + y + y^2 / 2)/y).
  evar (l : Rbar).
  pattern p_infty at 2.
  replace p_infty with l.
  apply is_lim_ext_loc with (fun y => /y + 1 + y / 2).
  exists 0 => y Hy.
  field.
  by apply Rgt_not_eq.
  apply is_lim_plus.
  apply is_lim_plus.
  apply is_lim_inv.
  apply is_lim_id.
  by [].
  apply is_lim_const.
  by [].
  apply is_lim_div.
  apply is_lim_id.
  apply is_lim_const.
  apply Rbar_finite_neq, Rgt_not_eq, Rlt_0_2.
  simpl.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  simpl.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  rewrite /l /=.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  exists 0 => y Hy.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rinv_0_lt_compat.
  rewrite /exp.
  rewrite /exist_exp.
  case: Alembert_C3 => /= x Hx.
  rewrite /Pser /infinite_sum in Hx.
  apply Rnot_lt_le => H.
  case: (Hx _ (proj1 (Rminus_lt_0 _ _) H)) => N {Hx} Hx.
  move: (Hx _ (le_plus_r 2 N)) => {Hx}.
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: N => [ | n IH].
  simpl ; apply Req_le ; field.
  apply Rle_trans with (1 := IH).
  rewrite -plus_n_Sm ; move: (2 + n)%nat => {n IH} n.
  rewrite /sum_f_R0 -/sum_f_R0.
  rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_eq_0.
  apply Rmult_le_pos.
  apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
  apply pow_le.
  by apply Rlt_le.
Qed.

Lemma is_lim_exp_aux2 : is_lim (fun y => y * exp y) m_infty 0.
Proof.
  search_lim.
  apply is_lim_ext_loc with (fun y => - / (exp (-y) / (- y))).
  exists 0 => y Hy.
  rewrite exp_Ropp.
  field.
  split.
  apply Rgt_not_eq, exp_pos.
  by apply Rlt_not_eq.
  apply is_lim_opp.
  apply is_lim_inv.
  apply (is_lim_comp (fun y => exp y / y)) with p_infty.
  by apply is_lim_exp_aux1.
  search_lim.
  apply is_lim_opp.
  apply is_lim_id.
  by [].
  by apply Rbar_locally_forall.
  by [].
  simpl ; by rewrite Ropp_0.
Qed.

Lemma is_lim_exp_aux3 : is_lim (fun y => (exp y - 1) / y) 0 1.
Proof.
  move => eps.
  case: (derivable_pt_lim_exp_0 eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite Rplus_0_l exp_0.
Qed.

(** * Natural logarithm *)

Lemma is_lim_ln_p : is_lim (fun y => ln y) p_infty p_infty.
Proof.
  move => M.
  exists (exp M) => x Hx.
  rewrite -(ln_exp M).
  apply ln_increasing.
  apply exp_pos.
  by apply Hx.
Qed.

Lemma is_lim_ln_0 : is_lim (fun y => ln (Rabs y)) 0 m_infty.
Proof.
  move => eps.
  exists (mkposreal (exp eps) (exp_pos _)) => x /= Hx Hx0.
  rewrite -(ln_exp eps).
  apply ln_increasing.
  by apply Rabs_pos_lt.
  rewrite Rminus_0_r in Hx.
  by apply Hx.
Qed.

Lemma is_lim_ln_aux1 : is_lim (fun y => ln y / y) p_infty 0.
Proof.
  have H : forall x, 0 < x -> ln x < x.
    move => x Hx.
    apply Rminus_lt_0.
    apply Rlt_le_trans with (1 := Rlt_0_1).
    have H : forall x, 0 < x -> derivable_pt_lim (fun y => y - ln y) x ((x - 1) / x).
      move => z Hz.
      evar (l : R).
      replace ((z - 1) / z) with l.
      apply derivable_pt_lim_minus.
      apply derivable_pt_lim_id.
      apply derivable_pt_lim_ln.
      by apply Hz.
      rewrite /l ; field.
      by apply Rgt_not_eq.
    case: (MVT_gen (fun y => y - ln y) 1 x).
    move => y Hy ; exists ((y-1)/y) ; apply H.
    apply Rlt_trans with (2 := proj1 Hy).
    apply Rmin_case.
    apply Rlt_0_1.
    by apply Hx.
    move => y Hy.
    apply derivable_continuous_pt.
    exists ((y-1)/y) ; apply H.
    apply Rlt_le_trans with (2 := proj1 Hy).
    apply Rmin_case.
    apply Rlt_0_1.
    by apply Hx.
    move => c [Hc H0].
    replace 1 with (1 - ln 1) by (rewrite ln_1 Rminus_0_r //).
    apply Rminus_le_0.
    rewrite H0.
    rewrite (is_derive_unique _ _ ((c-1)/c)).
    move: Hc ; rewrite /Rmin /Rmax ; case: Rle_dec => H1 Hc.
    apply Rmult_le_pos.
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Hc.
    apply Rlt_le_trans with (1 := Rlt_0_1).
    by apply Hc.
    apply -> Rminus_le_0 ; apply H1.
    apply Rnot_le_lt in H1.
    replace ((c - 1) / c * (x - 1)) with ((1-c) * (1-x) / c).
    apply Rdiv_le_0_compat.
    apply Rmult_le_pos.
    apply -> Rminus_le_0 ; apply Hc.
    apply -> Rminus_le_0 ; apply Rlt_le, H1.
    apply Rlt_le_trans with (1 := Hx).
    by apply Hc.
    field.
    apply Rgt_not_eq.
    apply Rlt_le_trans with (1 := Hx).
    by apply Hc.
    apply H.
    apply Rlt_le_trans with (2 := proj1 Hc).
    apply Rmin_case.
    apply Rlt_0_1.
    apply Hx.
  search_lim.
  apply (is_lim_le_le_loc (fun _ => 0) (fun y => 2/sqrt y)).
  apply is_lim_const.
  search_lim.
  apply is_lim_div.
  apply is_lim_const.
  apply is_lim_sqrt_p.
  by [].
  by [].
  simpl ; by rewrite Rmult_0_r.
  exists 1 => x Hx.
  split.
  apply Rdiv_le_0_compat.
  rewrite -ln_1.
  apply ln_le.
  apply Rlt_0_1.
  by apply Rlt_le.
  by apply Rlt_trans with (1 := Rlt_0_1).
  replace (ln _) with (2 * ln (sqrt x)).
  rewrite /Rdiv Rmult_assoc.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rle_div_l.
  by apply Rlt_trans with (1 := Rlt_0_1).
  rewrite -{3}(sqrt_sqrt x).
  field_simplify ; rewrite ?Rdiv_1.
  apply Rlt_le, H.
  apply sqrt_lt_R0.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply Rgt_not_eq.
  apply sqrt_lt_R0.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply Rlt_le.
  by apply Rlt_trans with (1 := Rlt_0_1).
  replace 2 with (INR 2) by (simpl ; ring).
  rewrite -ln_pow.
  rewrite /= Rmult_1_r.
  rewrite sqrt_sqrt.
  by [].
  apply Rlt_le.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply sqrt_lt_R0.
  by apply Rlt_trans with (1 := Rlt_0_1).
  by [].
Qed.

Lemma is_lim_ln_aux2 : is_lim (fun y => ln (1+y) / y) 0 1.
Proof.
  move => eps.
  case: (derivable_pt_lim_ln 1 (Rlt_0_1) eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite ln_1 Rinv_1 Rminus_0_r.
Qed.

(** * the function sin x / x *)

Lemma is_lim_sin_aux : is_lim (fun x => sin x / x) 0 1.
Proof.
  move => eps.
  case: (derivable_pt_lim_sin_0 eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite Rplus_0_l sin_0 Rminus_0_r.
Qed.
