(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2013 Sylvie Boldo
#<br />#
Copyright (C) 2011-2013 Catherine Lelay
#<br />#
Copyright (C) 2011-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt.

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

Lemma filterlim_abs_0 :
  filterlim Rabs (Rbar_locally' 0) (at_right 0).
Proof.
intros P [eps HP].
exists eps.
intros x Hx Hx'.
apply HP.
simpl.
revert Hx.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
rewrite -?/(Rminus _ _) 2!Rminus_0_r.
now rewrite Rabs_Rabsolu.
now apply Rabs_pos_lt.
Qed.

(** * Inverse function *)

Lemma is_lim_Rinv_0 :
  filterlim Rinv (at_right 0) (Rbar_locally p_infty).
Proof.
  intros P [M HM].
  have Hd : 0 < / Rmax 1 M.
    apply Rinv_0_lt_compat.
    apply Rlt_le_trans with (2 := Rmax_l _ _).
    by apply Rlt_0_1.
  exists (mkposreal _ Hd) => x /= Hx Hx0.
  apply HM.
  apply Rle_lt_trans with (1 := Rmax_r 1 M).
  replace (Rmax 1 M) with (/ / Rmax 1 M)
  by (field ; apply Rgt_not_eq, Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1).
  apply Rinv_lt_contravar.
  apply Rdiv_lt_0_compat with (1 := Hx0).
  apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
  rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
  rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq // in Hx.
  exact: Rlt_le.
Qed.

(** * Square root function *)

Lemma is_lim_sqrt_p : is_lim sqrt p_infty p_infty.
Proof.
  apply is_lim_spec.
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

(** * Power function *)

Lemma is_RInt_pow :
  forall a b n,
  is_RInt (fun x => pow x n) a b (pow b (S n) / INR (S n) - pow a (S n) / INR (S n)).
Proof.
intros a b n.
set f := fun x => pow x (S n) / INR (S n).
fold (f a) (f b).
assert (H: forall x, is_derive f x (pow x n)).
  intros x.
  search_derive.
  apply derivable_pt_lim_scal_r.
  apply derivable_pt_lim_pow.
  rewrite /pred.
  field.
  rewrite S_INR.
  apply Rgt_not_eq, INRp1_pos.
apply is_RInt_ext with (Derive f).
  intros x _.
  now apply is_derive_unique.
apply: is_RInt_Derive => x Hx.
  now eexists.
apply continuity_pt_ext with (fun x => pow x n).
  intros t.
  apply sym_eq.
  now apply is_derive_unique.
apply derivable_continuous_pt.
apply derivable_pt_pow.
Qed.

(** * Exponential function *)

Lemma is_RInt_exp :
  forall a b,
  is_RInt exp a b (exp b - exp a).
Proof.
intros a b.
apply is_RInt_ext with (Derive exp).
  intros x _.
  apply is_derive_unique.
  apply derivable_pt_lim_exp.
apply is_RInt_Derive.
  intros x _.
  exists (exp x).
  apply derivable_pt_lim_exp.
intros x _.
apply continuity_pt_ext with exp.
  intros t.
  apply sym_eq, is_derive_unique, derivable_pt_lim_exp.
apply derivable_continuous_pt.
apply derivable_pt_exp.
Qed.

Lemma exp_ge_taylor (x : R) (n : nat) :
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
  exists 0 => y Hy.
  by apply Rlt_le, exp_ineq1.
  pattern p_infty at 2.
  replace p_infty with (Rbar_plus 1 p_infty) by auto.
  eapply is_lim_plus.
  apply is_lim_const.
  apply is_lim_id.
  by [].
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
  by apply filter_forall.
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

Lemma is_lim_div_exp_p : is_lim (fun y => exp y / y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => (1 + y + y^2 / 2)/y).
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
  apply is_lim_ext_loc with (fun y => /y + 1 + y / 2).
  exists 0 => y Hy.
  field.
  by apply Rgt_not_eq.
  eapply is_lim_plus.
  eapply is_lim_plus.
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
  apply Rgt_not_eq, Rinv_0_lt_compat, Rlt_0_2.
  simpl.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
Qed.

Lemma is_lim_mul_exp_m : is_lim (fun y => y * exp y) m_infty 0.
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
  by apply is_lim_div_exp_p.
  search_lim.
  apply is_lim_opp.
  apply is_lim_id.
  by [].
  by apply filter_forall.
  by [].
  simpl ; by rewrite Ropp_0.
Qed.

Lemma is_lim_div_expm1_0 : is_lim (fun y => (exp y - 1) / y) 0 1.
Proof.
  apply is_lim_spec.
  move => eps.
  case: (derivable_pt_lim_exp_0 eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
  rewrite -/(Rminus _ _) Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite Rplus_0_l exp_0.
Qed.

(** * Natural logarithm *)

Lemma is_lim_ln_p : is_lim (fun y => ln y) p_infty p_infty.
Proof.
  apply is_lim_spec.
  move => M.
  exists (exp M) => x Hx.
  rewrite -(ln_exp M).
  apply ln_increasing.
  apply exp_pos.
  by apply Hx.
Qed.

Lemma is_lim_ln_0 :
  filterlim ln (at_right 0) (Rbar_locally m_infty).
Proof.
intros P [M HM].
exists (mkposreal (exp M) (exp_pos _)) => x /= Hx Hx0.
apply HM.
rewrite <- (ln_exp M).
apply ln_increasing.
exact Hx0.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq in Hx.
exact Hx.
now apply Rlt_le.
Qed.

Lemma is_lim_div_ln_p : is_lim (fun y => ln y / y) p_infty 0.
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
  apply (is_lim_le_le_loc (fun _ => 0) (fun y => 2/sqrt y)).
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
  apply is_lim_const.
  search_lim.
  apply is_lim_div.
  apply is_lim_const.
  apply is_lim_sqrt_p.
  by [].
  by [].
  simpl ; by rewrite Rmult_0_r.
Qed.

Lemma is_lim_div_ln1p_0 : is_lim (fun y => ln (1+y) / y) 0 1.
Proof.
  apply is_lim_spec.
  move => eps.
  case: (derivable_pt_lim_ln 1 (Rlt_0_1) eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
  rewrite /= -/(Rminus _ _) Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite ln_1 Rinv_1 Rminus_0_r.
Qed.

(** * Unnormalized sinc *)

Lemma is_lim_sinc_0 : is_lim (fun x => sin x / x) 0 1.
Proof.
  apply is_lim_spec.
  move => eps.
  case: (derivable_pt_lim_sin_0 eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
  rewrite /= -/(Rminus _ _) Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite Rplus_0_l sin_0 Rminus_0_r.
Qed.
