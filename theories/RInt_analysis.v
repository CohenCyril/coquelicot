(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals.
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Derive_2d Hierarchy Seq_fct RInt PSeries.

(** This file contains results about the integral as a function:
 continuity, differentiability, and composition. Theorems on
 parametric integrals are also provided. *)


(** * Continuity *)

Section Continuity.

Context {V : NormedModule R_AbsRing}.

Lemma continuous_RInt_0 :
  forall (f : R -> V) (a : R) If,
    locally a (fun x => is_RInt f a x (If x))
    -> continuous If a.
Proof.
  move => f a If [d1 /= CIf].
  assert (forall eps : posreal, norm (If a) < eps).
    move => eps.
    generalize (fun Hy => proj1 (filterlim_locally_ball_norm _ _) (CIf a Hy) eps)
      => /= {CIf} CIf.
      assert (Rabs (a + - a) < d1).
        rewrite -/(Rminus _ _) Rminus_eq_0 Rabs_R0.
        by apply d1.
      destruct (CIf H) as [d CIf'].
      assert (exists y : SF_seq,
        seq_step (SF_lx y) < d /\
        pointed_subdiv y /\
        SF_h y = Rmin a a /\ seq.last (SF_h y) (SF_lx y) = Rmax a a).
        apply filter_ex.
        exists d => y Hy Hy'.
        now split.
      case: H0 => {CIf H} ptd [Hstep Hptd].
      specialize (CIf' ptd Hstep Hptd).
      rewrite Rminus_eq_0 sign_0 in CIf'.
      rewrite -norm_opp.
      replace (opp (If a)) with (minus (scal 0 (Riemann_sum f ptd)) (If a)).
      by apply CIf'.
      replace (scal 0 (Riemann_sum f ptd) : V) with (zero : V).
      by rewrite /minus plus_zero_l.
      apply sym_eq ; apply: scal_zero_l.
  apply filterlim_locally_ball_norm.
  cut (forall eps : posreal, locally a (fun x : R => norm (If x) < eps)).
    move => H0 eps.
    specialize (H (pos_div_2 eps)).
    specialize (H0 (pos_div_2 eps)).
    destruct H0 as [d Hd].
    exists d => /= y Hy.
    apply Rle_lt_trans with (norm (If y) + norm (If a))%R.
    rewrite -(norm_opp (If a)).
    apply @norm_triangle.
    rewrite (double_var eps).
    apply Rplus_lt_compat.
    now apply Hd.
    by apply H.
  clear H.
  move => eps.
  destruct (ex_RInt_ub f (a - d1 / 2) (a + d1 / 2)) as [Mf HMf].
    apply ex_RInt_Chasles with a.
    apply ex_RInt_swap ; eexists ; apply CIf.
    rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
    field_simplify (a - d1 / 2 + - a)%R.
    rewrite Rabs_left.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
    apply Ropp_lt_cancel ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
    eexists ; apply CIf.
    rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
    field_simplify (a + d1 / 2 + - a)%R.
    rewrite Rabs_pos_eq.
    apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
    apply Rlt_le ; field_simplify ; rewrite Rdiv_1.
    by apply is_pos_div_2.
  assert ((a - d1 / 2) <= (a + d1 / 2)).
    apply Rminus_le_0.
    replace (a + d1 / 2 - (a - d1 / 2))%R with (d1 : R) by field.
    by apply Rlt_le, d1.
  move: HMf ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ HMf.
  assert (0 <= Mf).
    eapply Rle_trans.
    2: apply (HMf (a - d1 / 2)%R) ; split => // ; by apply Rle_refl.
    by apply norm_ge_0.
  generalize (fun y Hy => proj1 (filterlim_locally_ball_norm _ _) (CIf y Hy) (pos_div_2 eps))
    => /= {CIf} CIf.
  assert (0 < Rmin (d1 / 2) (eps / (2 * (Mf + 1)))).
    apply Rmin_case.
    by apply is_pos_div_2.
    apply Rdiv_lt_0_compat.
    by apply eps.
    apply Rmult_lt_0_compat.
    by apply Rlt_0_2.
    apply Rplus_le_lt_0_compat.
    by [].
    by apply Rlt_0_1.
  set (d2 := mkposreal _ H1).
  exists d2 => x /= Hx.
  specialize (CIf x).
  destruct CIf as [d' CIf].
  apply Rlt_trans with (1 := Hx).
  apply Rle_lt_trans with (1 := Rmin_l _ _).
  apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  assert (exists y0, seq_step (SF_lx y0) < d' /\
      pointed_subdiv y0 /\
      SF_h y0 = Rmin a x /\ seq.last (SF_h y0) (SF_lx y0) = Rmax a x).
    apply filter_ex.
    exists d' => y Hy Hy'.
    now split.
    case: H2 => ptd [Hstep Hptd].
    specialize (CIf ptd Hstep Hptd).
  rewrite -norm_opp.
  replace (opp (If x)) with
    (minus (minus (scal (sign (x - a)) (Riemann_sum f ptd)) (If x)) (scal (sign (x - a)) (Riemann_sum f ptd))).
  2: rewrite /minus plus_comm plus_assoc plus_opp_l.
  2: by apply plus_zero_l.
  apply Rle_lt_trans with (norm (minus (scal (sign (x - a)) (Riemann_sum f ptd)) (If x))
    + norm (opp (scal (sign (x - a)) (Riemann_sum f ptd))))%R.
  rewrite /minus ; by apply @norm_triangle.
  rewrite norm_opp (double_var eps).
  apply Rplus_lt_le_compat.
  by [].
  apply Rle_trans with (norm (Riemann_sum f ptd)).
  rewrite /sign ; case: Rle_dec => H2.
  case: Rle_lt_or_eq_dec => H3.
  rewrite scal_one ; by right.
  rewrite scal_zero_l norm_zero.
  by apply norm_ge_0.
  rewrite scal_opp_l scal_one norm_opp ; by right.
  apply Rle_trans with (Riemann_sum (fun _ => Mf) ptd).
  apply Riemann_sum_norm.
  apply Hptd.
  move => t.
  rewrite (proj2 (proj2 Hptd)) (proj1 (proj2 Hptd)) => Ht.
  apply HMf ; split ; eapply Rle_trans ; try apply Ht.
  apply Rmin_case.
  apply Rlt_le, Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rlt_le, Rabs_lt_between'.
  apply Rlt_le_trans with (1 := Hx).
  by apply Rmin_l.
  apply Rmax_case.
  apply Rlt_le, Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1 ; by apply is_pos_div_2.
  apply Rlt_le, Rabs_lt_between'.
  apply Rlt_le_trans with (1 := Hx).
  by apply Rmin_l.
  rewrite Riemann_sum_const.
  rewrite (proj2 (proj2 Hptd)) (proj1 (proj2 Hptd)) /=.
  apply Rle_trans with (Rabs (x + - a) * Mf)%R.
  apply Rmult_le_compat_r.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec => _.
  apply Rle_abs.
  rewrite -Ropp_minus_distr.
  apply Rabs_maj2.
  apply Rle_trans with (Rabs (x + - a) * (Mf + 1))%R.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply Rminus_le_0 ; ring_simplify ; by apply Rle_0_1.
  apply Rle_div_r.
  apply Rlt_le_trans with (1 := Rlt_0_1).
  apply Rminus_le_0 ; by ring_simplify.
  apply Rlt_le, Rlt_le_trans with (1 := Hx).
  apply Rle_trans with (1 := Rmin_r _ _).
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1).
  apply Rminus_le_0 ; by ring_simplify.
Qed.

Lemma continuous_RInt_1 (f : R -> V) (a b : R) (If : R -> V) :
  locally b (fun z : R => is_RInt f a z (If z))
  -> continuous If b.
Proof.
  intros.
  generalize (locally_singleton _ _ H) => /= Hab.
  apply continuous_ext with (fun z => plus (If b) (minus (If z) (If b))) ; simpl.
  intros x.
  by rewrite plus_comm -plus_assoc plus_opp_l plus_zero_r.
  eapply filterlim_comp_2, filterlim_plus.
  apply filterlim_const.
  apply (continuous_RInt_0 f _ (fun x : R_UniformSpace => minus (If x) (If b))).
  apply: filter_imp H => x Hx.
  rewrite /minus plus_comm.
  eapply is_RInt_Chasles, Hx.
  by apply is_RInt_swap.
Qed.
Lemma continuous_RInt_2 (f : R -> V) (a b : R) (If : R -> V) :
  locally a (fun z : R => is_RInt f z b (If z))
  -> continuous If a.
Proof.
  intros.
  generalize (locally_singleton _ _ H) => /= Hab.
  apply continuous_ext with (fun z => opp (plus (opp (If a)) (minus (If a) (If z)))) ; simpl.
  intros x.
  by rewrite /minus plus_assoc plus_opp_l plus_zero_l opp_opp.
  apply continuous_opp.
  apply continuous_plus.
  apply filterlim_const.
  apply (continuous_RInt_0 f _ (fun x : R_UniformSpace => minus (If a) (If x))).
  apply: filter_imp H => x Hx.
  eapply is_RInt_Chasles.
  by apply Hab.
  by apply is_RInt_swap.
Qed.
Lemma continuous_RInt (f : R -> V) (a b : R) (If : R -> R -> V) :
  locally (a,b) (fun z : R * R => is_RInt f (fst z) (snd z) (If (fst z) (snd z)))
  -> continuous (fun z : R * R => If (fst z) (snd z)) (a,b).
Proof.
  intros HIf.
  move: (locally_singleton _ _ HIf) => /= Hab.
  apply continuous_ext_loc
    with (fun z : R * R => plus (If (fst z) b) (plus (opp (If a b)) (If a (snd z)))) ; simpl.
    assert (Ha : locally (a,b) (fun z : R * R => is_RInt f a (snd z) (If a (snd z)))).
      case: HIf => /= d HIf.
      exists d => y /= Hy.
      apply (HIf (a,(snd y))) ; split => //=.
      by apply ball_center.
      by apply Hy.
    assert (Hb : locally (a,b) (fun z : R * R => is_RInt f (fst z) b (If (fst z) b))).
      case: HIf => /= d HIf.
      exists d => x /= Hx.
      apply (HIf (fst x,b)) ; split => //=.
      by apply Hx.
      by apply ball_center.
    generalize (filter_and _ _ HIf (filter_and _ _ Ha Hb)).
    apply filter_imp => {HIf Ha Hb} /= x [HIf [Ha Hb]].
    apply ball_eq.
    eapply filterlim_locally_close.
    eapply is_RInt_Chasles.
    by apply Hb.
    eapply is_RInt_Chasles.
    by apply is_RInt_swap, Hab.
    by apply Ha.
    by apply HIf.
  eapply filterlim_comp_2, filterlim_plus ; simpl.
  apply (continuous_comp (fun x => fst x) (fun x => If x b)) ; simpl.
  apply continuous_fst.
  eapply (continuous_RInt_2 f _ b).
    case: HIf => /= d HIf.
    exists d => x /= Hx.
    apply (HIf (x,b)).
    split => //=.
    by apply ball_center.
  eapply filterlim_comp_2, filterlim_plus ; simpl.
  apply filterlim_const.
  apply (continuous_comp (fun x => snd x) (fun x => If a x)) ; simpl.
  apply continuous_snd.
  eapply (continuous_RInt_1 f a b).
    case: HIf => /= d HIf.
    exists d => x /= Hx.
    apply (HIf (a,x)).
    split => //=.
    by apply ball_center.
Qed.

End Continuity.

(** * Riemann integral and differentiability *)

Section Derive.

Context {V : NormedModule R_AbsRing}.

Lemma is_derive_RInt_0 (f If : R -> V) (a : R) :
  locally a (fun b => is_RInt f a b (If b))
  -> continuous f a
  -> is_derive If a (f a).
Proof.
  intros HIf Hf.
  split ; simpl.
  apply is_linear_scal_l.
  intros y Hy.
  apply @is_filter_lim_locally_unique in Hy.
  rewrite -Hy {y Hy}.
  intros eps.
  generalize (proj1 (filterlim_locally _ _) Hf) => {Hf} Hf.
  eapply filter_imp.
  simpl ; intros y Hy.
  replace (If a) with (@zero V).
  rewrite @minus_zero_r.
  rewrite Rmult_comm ; eapply norm_RInt_le_const_abs ; last first.
  apply is_RInt_minus.
  instantiate (1 := f).
  eapply (proj1 Hy).
  apply is_RInt_const.
  simpl.
  apply (proj2 Hy).
  apply locally_singleton in HIf.
  set (HIf_0 := is_RInt_point f a).
  apply (filterlim_locally_unique _ _ _ HIf_0 HIf).

  apply filter_and.
  by apply HIf.
  assert (0 < eps / @norm_factor _ V).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply norm_factor_gt_0.
  case: (Hf (mkposreal _ H)) => {Hf} delta Hf.
  exists delta ; intros y Hy z Hz.
  eapply Rle_trans.
  apply Rlt_le, norm_compat2.
  apply Hf.
  apply Rabs_lt_between'.
  move/Rabs_lt_between': Hy => Hy.
  rewrite /Rmin /Rmax in Hz ; destruct (Rle_dec a y) as [Hxy | Hxy].
  split.
  eapply Rlt_le_trans, Hz.
  apply Rminus_lt_0 ; ring_simplify.
  by apply delta.
  eapply Rle_lt_trans, Hy.
  by apply Hz.
  split.
  eapply Rlt_le_trans, Hz.
  by apply Hy.
  eapply Rle_lt_trans.
  apply Hz.
  apply Rminus_lt_0 ; ring_simplify.
  by apply delta.
  simpl ; apply Req_le.
  field.
  apply Rgt_not_eq, norm_factor_gt_0.
Qed.
Lemma is_derive_RInt (f If : R -> V) (a b : R) :
  locally b (fun b => is_RInt f a b (If b))
  -> continuous f b
  -> is_derive If b (f b).
Proof.
  intros HIf Hf.
  apply is_derive_ext with (fun y => (plus (minus (If y) (If b)) (If b))).
  simpl ; intros.
  rewrite /minus -plus_assoc plus_opp_l.
  by apply plus_zero_r.
  evar_last.
  apply is_derive_plus.
  apply is_derive_RInt_0.
  2: apply Hf.
  eapply filter_imp.
  intros y Hy.
  evar_last.
  apply is_RInt_Chasles with a.
  apply is_RInt_swap.
  3: by apply plus_comm.
  by apply locally_singleton in HIf.
  by apply Hy.
  by apply HIf.
  apply is_derive_const.
  by apply plus_zero_r.
Qed.
Lemma is_derive_RInt' (f If : R -> V) (a b : R) :
  locally a (fun a => is_RInt f a b (If a))
  -> continuous f a
  -> is_derive If a (opp (f a)).
Proof.
  intros.
  apply is_derive_ext with (fun x => opp (opp (If x))).
  intros ; by rewrite opp_opp.
  apply is_derive_opp.
  apply is_derive_RInt with b => //.
  move: H ; apply filter_imp.
  intros x Hx.
  by apply is_RInt_swap.
Qed.

Lemma filterdiff_RInt (f : R -> V) (If : R -> R -> V) (a b : R) :
  locally (a,b) (fun u : R * R => is_RInt f (fst u) (snd u) (If (fst u) (snd u)))
  -> continuous f a -> continuous f b
  -> filterdiff (fun u : R * R => If (fst u) (snd u)) (locally (a,b))
                (fun u : R * R => minus (scal (snd u) (f b)) (scal (fst u) (f a))).
Proof.
  intros Hf Cfa Cfb.

  assert (Ha : locally a (fun a : R => is_RInt f a b (If a b))).
    case: Hf => /= e He.
    exists e => x Hx.
    apply (He (x,b)).
    split => //.
    by apply ball_center.
  assert (Hb : locally b (fun b : R => is_RInt f a b (If a b))).
    case: Hf => /= e He.
    exists e => x Hx.
    apply (He (a,x)).
    split => //.
    by apply ball_center.

  eapply filterdiff_ext_lin.

  apply (filterdiff_ext_loc (FF := @filter_filter _ _ (locally_filter _)) (fun u : R * R => plus (If (fst u) b) (minus (If a (snd u)) (If a b)))) ;
  last first.
  apply filterdiff_plus_fct.
  apply (filterdiff_comp' (fun u : R * R => fst u) (fun a : R => If a b)).
  by apply filterdiff_linear, is_linear_fst.
  eapply is_derive_RInt', Cfa.
  by apply Ha.
  apply filterdiff_plus_fct.
  apply (filterdiff_comp' (fun u : R * R => snd u) (fun b : R => If a b)).
  by apply filterdiff_linear, is_linear_snd.
  eapply is_derive_RInt, Cfb.
  by apply Hb.
  apply filterdiff_const.

  move => /= x Hx.
  apply @is_filter_lim_locally_unique in Hx.
  by rewrite -Hx /= minus_eq_zero plus_zero_r.
  simpl.

  have : (locally (a,b) (fun u : R * R => is_RInt f (fst u) b (If (fst u) b))) => [ | {Ha} Ha].
    case: Ha => /= e He.
    exists e => y Hy.
    apply He, Hy.
  have : (locally (a,b) (fun u : R * R => is_RInt f a (snd u) (If a (snd u)))) => [ | {Hb} Hb].
    case: Hb => /= e He.
    exists e => y Hy.
    apply He, Hy.
  move: (locally_singleton _ _ Hf) => /= Hab.
  generalize (filter_and _ _ Hf (filter_and _ _ Ha Hb)).
  apply filter_imp => {Hf Ha Hb} /= u [Hf [Ha Hb]].
  apply sym_eq, (filterlim_locally_unique _ _ _ Hf).
  apply is_RInt_Chasles with b => //.
  rewrite /minus plus_comm.
  apply is_RInt_Chasles with a => //.
  by apply is_RInt_swap.
  simpl => y.
  rewrite scal_opp_r plus_zero_r.
  apply plus_comm.
Qed.

End Derive.

Lemma is_RInt_derive (f df : R -> R) (a b : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> continuous df x) ->
    is_RInt df a b (f b - f a)%R.
Proof.
  intros Hf Hdf.
  wlog: a b Hf Hdf / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite Hab Rminus_eq_0.
    by apply @is_RInt_point.
    evar_last.
    apply is_RInt_swap.
    apply Hw => //.
    by rewrite Rmin_comm Rmax_comm.
    by rewrite Rmin_comm Rmax_comm.
    change opp with Ropp ; simpl ; ring.
  apply filterlim_locally.
  rewrite (proj1 (sign_0_lt _)).
  2: by apply Rminus_lt_0 in Hab.
  intros.
  eapply filter_imp.
  intros x Hx ; rewrite scal_one ; by apply norm_compat1, Hx.
  rewrite /Rmin /Rmax in Hf, Hdf ;
  destruct (Rle_dec a b) as [_ | Hab'].
  2: contradict Hab' ; by apply Rlt_le.

  assert (He : 0 < eps / (b - a)).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply Rminus_lt_0 in Hab.
  set (e := mkposreal _ He).
  destruct (unifcont_normed_1d _ _ _ Hdf e) as [delta Hd] ; clear Hdf.
  exists delta.
  rewrite /Rmin /Rmax ;
  destruct (Rle_dec a b) as [_ | Hab'].
  2: contradict Hab' ; by apply Rlt_le.
  intros y Hstep [Hptd [Ha Hb]].
  replace (pos eps) with (e * (b - a))%R.
  move: e Hd => {eps He} e Hd.
  rewrite -Ha {a Ha} in Hf Hd Hab |- *.
  rewrite -Hb {b Hb} in Hf Hd Hab |- *.
  move: Hab Hstep Hptd Hf Hd.
  apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IHy] /= Hab Hstep Hptd Hf Hd.
  by apply Rlt_irrefl in Hab.
  rewrite Riemann_sum_cons.
  change minus with Rminus ;
  change plus with Rplus ;
  change scal with Rmult.

  assert (Hab_0 : fst x0 <= SF_h y).
    eapply Rle_trans ; apply (Hptd _ (lt_O_Sn _)).
  assert (Hab_1 : SF_h y <= seq.last (SF_h y) (SF_lx y)).
    apply (sorted_last (SF_lx y) O).
    apply ptd_sort.
    by apply ptd_cons with x0.
    by apply lt_O_Sn.
  assert (Hstep_0 : Rabs (SF_h y - fst x0) < delta).
    eapply Rle_lt_trans, Hstep.
    by apply Rmax_l.
  assert (Hstep_1 : seq_step (SF_lx y) < delta).
    eapply Rle_lt_trans, Hstep.
    by apply Rmax_r.
  assert (Hptd_0 : fst x0 <= snd x0 <= SF_h y).
    by apply (Hptd _ (lt_O_Sn _)).
  assert (Hptd_1 : pointed_subdiv y).
    by apply ptd_cons with x0.
  assert (Hf_0 : forall x : R, fst x0 <= x <= (SF_h y) -> is_derive f x (df x)).
    intros ; apply Hf ; split.
    by apply H.
    eapply Rle_trans, Hab_1 ; by apply H.
  assert (Hf_1 : forall x : R,
    SF_h y <= x <= seq.last (SF_h y) (SF_lx y) -> is_derive f x (df x)).
    intros ; apply Hf ; split.
    by eapply Rle_trans, H.
    by apply H.
  assert (Hd_0 : forall x y0 : R,
    fst x0 <= x <= (SF_h y) -> fst x0 <= y0 <= (SF_h y) ->
    ball x delta y0 -> ball_norm (df x) e (df y0)).
    intros ; apply Hd => // ; split.
    by apply H.
    eapply Rle_trans, Hab_1 ; by apply H.
    apply H0.
    eapply Rle_trans, Hab_1 ; by apply H0.
  assert (Hd_1 : forall x y0 : R,
    SF_h y <= x <= seq.last (SF_h y) (SF_lx y) ->
    SF_h y <= y0 <= seq.last (SF_h y) (SF_lx y) ->
    ball x delta y0 -> ball_norm (df x) e (df y0)).
    intros ; apply Hd => // ; split.
    by eapply Rle_trans, H.
    by apply H.
    by eapply Rle_trans, H0.
    by apply H0.
  move: (fun H => IHy H Hstep_1 Hptd_1 Hf_1 Hd_1) => {IHy Hstep Hptd Hf Hd Hstep_1 Hf_1 Hd_1} IHy.
  assert (((SF_h y - fst x0) * df (snd x0) + Riemann_sum df y -
    (f (seq.last (SF_h y) (seq.unzip1 (SF_t y))) - f (fst x0)))%R
    = (((SF_h y - fst x0) * df (snd x0) - (f (SF_h y) - f (fst x0)))
        + (Riemann_sum df y - (f (seq.last (SF_h y) (seq.unzip1 (SF_t y))) - f (SF_h y))))%R)
    by ring.
  rewrite H {H}.
  eapply Rle_lt_trans.
  apply @norm_triangle.
  replace (e * (seq.last (SF_h y) (seq.unzip1 (SF_t y)) - fst x0))%R
    with ((SF_h y - fst x0) * e +
         (e * (seq.last (SF_h y) (seq.unzip1 (SF_t y)) - SF_h y)))%R
    by ring.

  case: Hab_0 => Hab_0 ; last first.
  rewrite Hab_0 !Rminus_eq_0 !Rmult_0_l Rminus_eq_0 norm_zero !Rplus_0_l.
  apply IHy.
  by rewrite -Hab_0.
  destruct (MVT_gen f (fst x0) (SF_h y) df) as [c [Hc Hdf]] => //.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab_0) => // _ _.
  intros c Hc ; apply Hf_0.
  move: Hc ;
  by split ; apply Rlt_le ; apply Hc.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab_0) => // _ _.
  intros c Hc ; apply continuity_pt_filterlim, @ex_derive_continuous.
  by eexists ; apply Hf_0.
  move: Hc ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab_0) => // _ _ Hc.
  rewrite Hdf {Hdf} Rmult_comm -Rmult_minus_distr_r Rmult_comm.
  eapply Rle_lt_trans.
  apply Rplus_le_compat_r.
  apply @norm_scal.
  change abs with Rabs.
  rewrite Rabs_pos_eq.
  2: by apply Rminus_lt_0, Rlt_le in Hab_0.
  apply Rplus_lt_le_compat.
  apply Rmult_lt_compat_l.
  by apply Rminus_lt_0 in Hab_0.
  apply Hd_0 => //.
  eapply Rle_lt_trans, Hstep_0.
  rewrite Rabs_pos_eq.
  2: by apply Rminus_lt_0, Rlt_le in Hab_0.
  apply Rabs_le_between ; split.
  rewrite Ropp_minus_distr.
  apply Rplus_le_compat.
  by apply Hptd_0.
  by apply Ropp_le_contravar, Hc.
  apply Rplus_le_compat.
  by apply Hptd_0.
  by apply Ropp_le_contravar, Hc.

  case: Hab_1 => /= Hab_1 ; last first.
  rewrite -Hab_1 !Rminus_eq_0 Rmult_0_r.
  rewrite Riemann_sum_zero //.
  rewrite Rminus_eq_0 norm_zero.
  by apply Rle_refl.
  by apply ptd_sort.

  by apply Rlt_le, IHy.

  unfold e ; simpl ; field.
  apply Rgt_not_eq.
  by apply Rminus_lt_0 in Hab.
Qed.

Lemma RInt_Derive (f : R -> R) (a b : R):
  (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) ->
  (forall x, Rmin a b <= x <= Rmax a b -> continuous (Derive f) x) ->
  RInt (Derive f) a b = f b - f a.
Proof.
intros Df Cdf.
apply is_RInt_unique, is_RInt_derive => //.
intros ; by apply Derive_correct, Df.
Qed.

(** * Composition *)

Lemma is_RInt_comp (f g dg : R -> R) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> continuous f (g x))
  -> (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x)
  -> is_RInt (fun y => dg y * f (g y)) a b (RInt f (g a) (g b)).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
    move => Hf Hg.
    rewrite RInt_point ; by apply @is_RInt_point.
  wlog: a b Hab /(a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab' Hf Hg.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -RInt_swap.
    apply @is_RInt_swap.
    apply Hw => //.
    by apply sym_not_eq.
    rewrite Rmin_comm Rmax_comm.
    by apply Hf.
    rewrite Rmin_comm Rmax_comm.
    by apply Hg.
  rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab)
    => // _ _.

  wlog: g dg / (forall x : R, is_derive g x (dg x) /\ continuous dg x) => [Hw Hf Hg | Hg Hf _].
    rewrite -?(extension_C1_ext g a b) ; try by [left | right].
    set g0 := extension_C1 g dg a b.
    set dg0 := extension_C0 dg a b.
    apply is_RInt_ext with (fun y : R => dg0 y * f (g0 y)).
    rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
    apply f_equal2.
    apply extension_C0_ext ; by apply Rlt_le, Hx.
    apply f_equal, extension_C1_ext ; by apply Rlt_le, Hx.
    evar_last.
    apply Hw.
    intros x ; split.
    apply extension_C1_is_derive.
    by apply Rlt_le.
    intros ; apply Hg ; by split.
    apply @extension_C0_continuous.
    by apply Rlt_le.
    intros ; apply Hg ; by split.
    intros ; rewrite /g0 extension_C1_ext.
    by apply Hf.
    by apply H.
    by apply H.
    intros ; split.
    apply extension_C1_is_derive.
    by apply Rlt_le.
    intros ; apply Hg ; by split.
    apply @extension_C0_continuous.
    by apply Rlt_le.
    intros ; apply Hg ; by split.
    apply f_equal2.
    apply extension_C1_ext.
    by apply Rle_refl.
    by apply Rlt_le.
    apply extension_C1_ext.
    by apply Rlt_le.
    by apply Rle_refl.
  wlog: f Hf / (forall x, continuous f x) => [Hw | {Hf} Hf].
    case: (continuity_ab_maj g a b (Rlt_le _ _ Hab)) => [ | M HM].
      move => x Hx.
      apply derivable_continuous_pt.
      exists (dg x) ; apply is_derive_Reals, Hg.
    case: (continuity_ab_min g a b (Rlt_le _ _ Hab)) => [ | m Hm].
      move => x Hx.
      apply derivable_continuous_pt.
      exists (dg x) ; apply is_derive_Reals, Hg.
    have H : g m <= g M.
      apply Hm ; intuition.
    case: (C0_extension_le f (g m) (g M)) => [ y Hy | f0 Hf0].
    case: (IVT_gen g m M y).
    move => x ; apply derivable_continuous_pt.
    exists (Derive g x) ; apply is_derive_Reals, Derive_correct.
    by eexists ; apply Hg.
    rewrite /Rmin /Rmax ; case: Rle_dec => //.
    move => x [Hx <-].
    apply Hf ; split.
    apply Rle_trans with (2 := proj1 Hx).
    apply Rmin_case ; intuition.
    apply Rle_trans with (1 := proj2 Hx).
    apply Rmax_case ; intuition.
    replace (RInt f (g a) (g b)) with (RInt f0 (g a) (g b)).
    apply is_RInt_ext with (fun y : R => dg y * f0 (g y)).
    rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hc.
    apply f_equal.
    apply Hf0 ; split.
    by apply Hm ; split ; apply Rlt_le ; apply Hc.
    by apply HM ; split ; apply Rlt_le ; apply Hc.
    apply Hw.
    move => x Hx ; apply Hf0.
    move => x ; apply Hf0.
    apply RInt_ext => x Hx.
    apply Hf0 ; split.
    apply Rle_trans with (2 := proj1 Hx).
    apply Rmin_case ; intuition.
    apply Rle_trans with (1 := proj2 Hx).
    apply Rmax_case ; intuition.
  evar_last.
  apply (is_RInt_derive (fun x => RInt f (g a) (g x))).
  intros x Hx.
  evar_last.
  apply is_derive_comp.
  apply is_derive_RInt with (g a).
  apply filter_forall => y.
  apply RInt_correct, @ex_RInt_continuous.
  intros ; apply Hf.
  by apply Hf.
  apply Hg.
  reflexivity.
  intros x Hx.
  apply @continuous_scal.
  by apply Hg.
  apply continuous_comp.
  apply @ex_derive_continuous.
  eexists ; by apply Hg.
  by apply Hf.
  by rewrite RInt_point Rminus_0_r.
Qed.

Lemma RInt_Chasles_bound_comp_l_loc :
  forall f a b x,
  locally x (fun y => ex_RInt (f y) (a x) b) ->
  (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) ->
  continuity_pt a x ->
  locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) b =
    RInt (f x') (a x') b).
Proof.
intros f a b x Hab (eps,Hae) Ca.
move /continuity_pt_locally: Ca => Ca.
generalize (filter_and _ _ (Ca eps) (filter_and _ _ Hab Hae)).
apply filter_imp => {Ca Hae Hab} y [Hy [Hab Hae]].
apply RInt_Chasles with (2 := Hab).
apply ex_RInt_inside with (1 := Hae).
now apply Rlt_le.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
Qed.

Lemma RInt_Chasles_bound_comp_loc :
  forall f a b x,
  locally x (fun y => ex_RInt (f y) (a x) (b x)) ->
  (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) ->
  (exists eps : posreal, locally x (fun y => ex_RInt (f y) (b x - eps) (b x + eps))) ->
  continuity_pt a x ->
  continuity_pt b x ->
  locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) (b x') =
    RInt (f x') (a x') (b x')).
Proof.
intros f a b x Hab (ea,Hae) (eb,Hbe) Ca Cb.
move /continuity_pt_locally: Ca => Ca.
move /continuity_pt_locally: Cb => Cb.
set (e := mkposreal _ (Rmin_stable_in_posreal ea eb)).
generalize (filter_and _ _ (filter_and _ _ (Ca e) (Cb e))
  (filter_and _ _ Hab (filter_and _ _ Hae Hbe))).
apply filter_imp => {Ca Cb Hab Hae Hbe} y [[Hay Hby] [Hab [Hae Hbe]]].
apply RInt_Chasles.
apply ex_RInt_inside with (1 := Hae).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hay).
exact: Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply ex_RInt_Chasles with (1 := Hab).
apply ex_RInt_inside with (1 := Hbe).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hby).
exact: Rmin_r.
Qed.

Lemma is_derive_RInt_bound_comp :
  forall f a b da db x,
  ex_RInt f (a x) (b x) ->
  (exists eps : posreal, ex_RInt f (a x - eps) (a x + eps)) ->
  (exists eps : posreal, ex_RInt f (b x - eps) (b x + eps)) ->
  continuity_pt f (a x) ->
  continuity_pt f (b x) ->
  is_derive a x da ->
  is_derive b x db ->
  is_derive (fun x => RInt f (a x) (b x)) x (db * f (b x) - da * f (a x)).
Proof.
intros f a b da db x Hi Ia Ib Ca Cb Da Db.
apply is_derive_ext_loc with (fun x0 => plus ((fun y => RInt f y (a x)) (a x0))
  ((fun y => RInt f (a x) y) (b x0))).
(* *)
apply RInt_Chasles_bound_comp_loc.
by apply filter_forall.
destruct Ia as (d1,H1).
exists d1.
by apply filter_forall.
destruct Ib as (d2,H2).
exists d2.
by apply filter_forall.
apply derivable_continuous_pt.
eexists ; apply is_derive_Reals, Da.
apply derivable_continuous_pt.
eexists ; apply is_derive_Reals, Db.
(* *)
eapply filterdiff_ext_lin.
generalize (filterdiff_plus_fct (F := locally x) (fun x0 => (fun y : R => RInt f y (a x)) (a x0))
  (fun x0 => (fun y : R => RInt f (a x) y) (b x0))) => /= H.
apply H ; clear H.
generalize (filterdiff_comp' a (fun y : R => RInt f y (a x)) x) => /= H ;
apply H ; clear H.
exact Da.
apply (is_derive_RInt' f _ _ (a x)) ; trivial.
case: Ia => e He.
exists e => /= y Hy.
apply RInt_correct.
generalize (proj1 (Rabs_lt_between' _ _ _) Hy) => {Hy} Hy.
eapply ex_RInt_Chasles.
eapply ex_RInt_Chasles, He.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_1, He.
split ; apply Rlt_le, Hy.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_2, He.
split ; apply Rminus_le_0 ; ring_simplify ; apply Rlt_le, e.
by apply continuity_pt_filterlim.
generalize (filterdiff_comp' b (RInt f (a x)) x) => /= H ; apply H ; clear H.
exact Db.
apply (is_derive_RInt f _ (a x)).
case: Ib => e He.
exists e => /= y Hy.
apply RInt_correct.
eapply ex_RInt_Chasles.
apply Hi.
generalize (proj1 (Rabs_lt_between' _ _ _) Hy) => {Hy} Hy.
eapply ex_RInt_Chasles.
eapply ex_RInt_Chasles, He.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_1, He.
split ; apply Rminus_le_0 ; ring_simplify ; apply Rlt_le, e.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_2, He.
split ; apply Rlt_le, Hy.
by apply continuity_pt_filterlim.

simpl => y.
rewrite /plus /scal /= /mult /= /opp /=.
ring.
Qed.

(** * Parametric integrals *)

Lemma is_derive_RInt_param_aux : forall f a b x,
  locally x (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally x (fun y => ex_RInt (fun t => f y t) a b) ->
  ex_RInt (fun t => Derive (fun u => f u t) x) a b ->
  is_derive (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x.
wlog: a b / a < b => H.
(* *)
destruct (total_order_T a b) as [[Hab|Hab]|Hab].
now apply H.
intros _ _ _ _.
rewrite Hab.
rewrite RInt_point.
apply is_derive_ext with (fun _ => 0).
simpl => t.
apply sym_eq.
apply RInt_point.
apply: is_derive_const.
simpl => H1 H2 H3 H4.
apply is_derive_ext with (fun u => - RInt (fun t => f u t) b a).
simpl => t.
apply RInt_swap.
eapply filterdiff_ext_lin.
apply @filterdiff_opp_fct ; try by apply locally_filter.
apply H.
exact Hab.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
move: H3 ; apply filter_imp => y H3.
now apply ex_RInt_swap.
now apply ex_RInt_swap.
rewrite -RInt_swap => /= y.
by rewrite -scal_opp_r opp_opp.
(* *)
rewrite Rmin_left. 2: now apply Rlt_le.
rewrite Rmax_right. 2: now apply Rlt_le.
intros Df Cdf If IDf.
split => [ | y Hy].
by apply @is_linear_scal_l.
rewrite -(is_filter_lim_locally_unique _ _ Hy) => {y Hy}.
refine (let Cdf' := uniform_continuity_2d_1d (fun u v => Derive (fun z => f z u) v) a b x _ in _).
intros t Ht eps.
specialize (Cdf t Ht eps).
simpl in Cdf.
destruct Cdf as (d,Cdf).
exists d.
intros v u Hv Hu.
now apply Cdf.
intros eps. (* 8.4/8.5 compatibility: *) try clearbody Cdf'. clear Cdf.
assert (H': 0 < eps / Rabs (b - a)).
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
apply Rgt_not_eq.
now apply Rgt_minus.
move: (Cdf' (mkposreal _ H')) => {Cdf'} [d1 Cdf].
generalize (filter_and _ _ Df If). move => {Df If} [d2 DIf].
exists (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))) => /= y Hy.
assert (D1: ex_RInt (fun t => f y t) a b).
apply DIf.
apply Rlt_le_trans with (1 := Hy).
apply Rle_trans with (1 := Rmin_r _ _).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
assert (D2: ex_RInt (fun t => f x t) a b).
apply DIf.
apply ball_center.
rewrite /minus /plus /opp /=.
rewrite -!/(Rminus _ _) -RInt_minus //.
rewrite /scal /= /mult /=.
rewrite -RInt_scal //.
assert (D3: ex_RInt (fun t => f y t - f x t) a b).
  apply @ex_RInt_minus.
  by apply D1.
  by apply D2.
assert (D4: ex_RInt (fun t => (y - x) * Derive (fun u => f u t) x) a b) by now apply @ex_RInt_scal.
rewrite -RInt_minus //.
assert (D5: ex_RInt (fun t => f y t - f x t - (y - x) * Derive (fun u => f u t) x) a b) by now apply @ex_RInt_minus.
rewrite (RInt_Reals _ _ _ (ex_RInt_Reals_0 _ _ _ D5)).
assert (D6: ex_RInt (fun t => Rabs (f y t - f x t - (y - x) * Derive (fun u => f u t) x)) a b) by now apply ex_RInt_norm.
apply Rle_trans with (1 := RiemannInt_P17 _ (ex_RInt_Reals_0 _ _ _ D6) (Rlt_le _ _ H)).
refine (Rle_trans _ _ _ (RiemannInt_P19 _ (RiemannInt_P14 a b (eps / Rabs (b - a) * Rabs (y - x))) (Rlt_le _ _ H) _) _).
intros u Hu.
destruct (MVT_cor4 (fun t => f t u) (Derive (fun t => f t u)) x) with (eps := pos_div_2 d2) (b := y) as (z,Hz).
intros z Hz.
apply Derive_correct, DIf.
apply Rle_lt_trans with (1 := Hz).
apply: Rlt_eps2_eps.
apply cond_pos.
split ; now apply Rlt_le.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
rewrite (proj1 Hz).
rewrite Rmult_comm.
rewrite -Rmult_minus_distr_l Rabs_mult.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rlt_le.
apply Cdf.
split ; now apply Rlt_le.
apply Rabs_le_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le.
apply cond_pos.
split ; now apply Rlt_le.
apply Rabs_le_between'.
apply Rle_trans with (1 := proj2 Hz).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite RiemannInt_P15.
rewrite Rabs_pos_eq.
right.
rewrite /norm /= /abs /=.
field.
apply Rgt_not_eq.
now apply Rgt_minus.
apply Rge_le.
apply Rge_minus.
now apply Rgt_ge.
Qed.

Lemma is_derive_RInt_param : forall f a b x,
  locally x (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally x (fun y => ex_RInt (fun t => f y t) a b) ->
  is_derive (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply is_derive_RInt_param_aux; try easy.
apply ex_RInt_Reals_1.
clear H1 H3.
wlog: a b H2 / a < b => H.
case (total_order_T a b).
intro Y; case Y.
now apply H.
intros Heq; rewrite Heq.
apply RiemannInt_P7.
intros  Y.
apply RiemannInt_P1.
apply H.
intros; apply H2.
rewrite Rmin_comm Rmax_comm.
exact H0.
exact Y.
rewrite Rmin_left in H2.
2: now left.
rewrite Rmax_right in H2.
2: now left.
apply continuity_implies_RiemannInt.
now left.
intros y Hy eps Heps.
destruct (H2 _ Hy (mkposreal eps Heps)) as (d,Hd).
simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist; simpl.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
Qed.

Lemma is_derive_RInt_param_bound_comp_aux1: forall f a x,
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        a x-eps <= t <= a x+eps ->
        ex_derive (fun u : R => f u t) x0)) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->

  continuity_2d_pt
     (fun u v : R => Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) x (a x).
Proof.
intros f a x (d1,(d2,Ia)) (d3,(d4,Df)) Cdf e.
assert (J1:(continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x (a x)))
   by now apply locally_2d_singleton in Cdf.
destruct Cdf as (d5,Cdf).
destruct (J1 (mkposreal _ Rlt_0_1)) as (d6,Df1); simpl in Df1.
assert (J2: 0 < e / (Rabs (Derive (fun z : R => f z (a x)) x)+1)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
exists (mkposreal _ (Rmin_stable_in_posreal
                  (mkposreal _ (Rmin_stable_in_posreal
                        d1
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d2) d3))))
                  (mkposreal _ (Rmin_stable_in_posreal
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d4) d5))
                       (mkposreal _ (Rmin_stable_in_posreal d6 (mkposreal _ J2))))))).
simpl; intros u v Hu Hv.
rewrite (Derive_ext (fun z : R => RInt (fun t : R => f z t) (a x) (a x)) (fun z => 0)).
2: intros t; apply RInt_point.
replace (Derive (fun _ : R => 0) x) with 0%R.
2: apply sym_eq, Derive_const.
rewrite Rminus_0_r.
replace (Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) with
  (RInt (fun z => Derive (fun u => f u z) u) v (a x)).
(* *)
apply Rle_lt_trans with (Rabs (a x -v) *
   (Rabs (Derive (fun z : R => f z (a x)) x) +1)).
apply (norm_RInt_le_const_abs (fun z : R => Derive (fun u0 : R => f u0 z) u) v (a x)).
intros t Ht.
apply Rplus_le_reg_r with (-Rabs (Derive (fun z : R => f z (a x)) x)).
apply Rle_trans with (1:=Rabs_triang_inv _ _).
ring_simplify.
left; apply Df1.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply RInt_correct, @ex_RInt_continuous.
intros y Hy ; apply continuity_pt_filterlim.
intros eps Heps.
assert (Y1:(Rabs (u - x) < d5)).
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
assert (Y2:(Rabs (y - a x) < d5)).
apply Rle_lt_trans with (Rabs (v-a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
destruct (Cdf u y Y1 Y2 (mkposreal eps Heps)) as (d,Hd); simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
replace (a x -v) with (-(v - a x)) by ring; rewrite Rabs_Ropp.
apply Rlt_le_trans with ((e / (Rabs (Derive (fun z : R => f z (a x)) x) + 1))
  * (Rabs (Derive (fun z : R => f z (a x)) x) + 1)).
apply Rmult_lt_compat_r.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
right; field.
apply sym_not_eq, Rlt_not_eq.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
(* *)
apply sym_eq, is_derive_unique.
apply is_derive_RInt_param.
exists (pos_div_2 d4).
intros y Hy t Ht.
apply Df.
rewrite (double_var d4).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
by apply Hy.
apply (proj1 (Rabs_le_between' t (a x) d3)).
apply Rle_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
intros t Ht.
apply Cdf.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
exists (pos_div_2 d2).
intros y Hy.
apply (ex_RInt_inside (f y)) with (a x) d1.
apply Ia.
rewrite (double_var d2).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Hy.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
Qed.

Lemma is_derive_RInt_param_bound_comp_aux2 :
  forall f a b x da,
  (locally x (fun y => ex_RInt (fun t => f y t) (a x) b)) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) ->
  is_derive a x da ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
        ex_derive (fun u : R => f u t) x0)) ->
  (forall t : R,
          Rmin (a x) b <= t <= Rmax (a x) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
   continuity_pt (fun t => f x t) (a x) ->

  is_derive (fun x => RInt (fun t => f x t) (a x) b) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) b+(-f x (a x))*da).
Proof.
intros f a b x da Hi (d0,Ia) Da Df Cdf1 Cdf2 Cfa.
rewrite Rplus_comm.
apply is_derive_ext_loc with (fun x0 => plus (RInt (fun t : R => f x0 t) (a x0) (a x)) (RInt (fun t : R => f x0 t) (a x) b)).
apply RInt_Chasles_bound_comp_l_loc.
exact Hi.
now exists d0.
apply derivable_continuous_pt.
eexists.
apply is_derive_Reals, Da.
eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct.
by apply locally_filter.
(* *)
apply is_derive_Reals.
apply derivable_pt_lim_comp_2d with
   (f1 := fun x0 y => RInt (fun t : R => f x0 t) y (a x)).
apply derivable_differentiable_pt_lim.
(* . *)
destruct Df as (d1,(d2,Df)).
destruct Cdf2 as (d3,Cdf2).
destruct Ia as (d4,Ia).
exists (mkposreal _ (Rmin_stable_in_posreal
                (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2)))
                (mkposreal _ (Rmin_stable_in_posreal d3
                            (mkposreal _ (Rmin_stable_in_posreal d0 (pos_div_2 d4))))))).
simpl; intros u v Hu Hv.
eexists; eapply is_derive_RInt_param.
exists (pos_div_2 d2).
intros y Hy t Ht.
apply Df.
rewrite (double_var d2).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
by apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (a x - d1).
apply Rmin_l.
apply Rmin_glb.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x + d1); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (a x + d1).
apply Rmax_lub.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x); ring_simplify.
left; apply cond_pos.
apply Rmax_l.
intros t Ht.
apply Cdf2.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
exists (pos_div_2 d4).
intros y Hy.
apply (ex_RInt_inside (f y)) with (a x) d0.
apply Ia.
rewrite (double_var d4).
apply ball_triangle with u.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
by apply Hy.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
(* . *)
apply is_derive_RInt' with (a x).
apply locally_singleton in Ia.
exists d0 => /= y Hy.
apply RInt_correct.
generalize (proj1 (Rabs_lt_between' _ _ _) Hy) => {Hy} Hy.
eapply ex_RInt_Chasles.
eapply ex_RInt_Chasles, Ia.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_1, Ia.
split ; apply Rlt_le, Hy.
apply ex_RInt_swap.
eapply @ex_RInt_Chasles_2, Ia.
split ; apply Rminus_le_0 ; ring_simplify ; apply Rlt_le, d0.
by apply continuity_pt_filterlim, Cfa.
(* . *)
apply is_derive_RInt_param_bound_comp_aux1; try easy.
exists d0; exact Ia.
destruct Df as (d,Hd).
exists d.
move: Hd ; apply filter_imp.
intros y H t Ht.
apply H.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rmax_l.
(* . *)
apply derivable_pt_lim_id.
apply is_derive_Reals, Da.
(* *)
apply is_derive_RInt_param.
destruct Df as (d,Df).
move: Df ; apply filter_imp.
intros y Hy t Ht; apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x+d); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
exact Cdf1.
exact Hi.
move => /= y ; apply Rminus_diag_uniq.
rewrite /plus /scal /opp /= /mult /=.
ring_simplify.
rewrite -(Derive_ext (fun _ => 0)).
rewrite Derive_const.
by apply Rmult_0_r.
move => t.
by rewrite RInt_point.
Qed.

Lemma is_derive_RInt_param_bound_comp_aux3 :
  forall f a b x db,
  (locally x (fun y => ex_RInt (fun t => f y t) a (b x))) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps))) ->
  is_derive b x db ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        Rmin a (b x-eps) <= t <= Rmax a (b x+eps) ->
        ex_derive (fun u : R => f u t) x0)) ->
  (forall t : R,
          Rmin a (b x) <= t <= Rmax a (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (b x) ->

  is_derive (fun x => RInt (fun t => f x t) a (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db).
Proof.
intros f a b x db If Ib Db Df Cf1 Cf2 Cfb.
apply is_derive_ext with (fun x0 => - RInt (fun t : R => f x0 t) (b x0) a).
intros t; apply RInt_swap.
replace (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db) with
      (- ((RInt (fun t : R => Derive (fun u : R => f u t) x) (b x) a) + - f x (b x)*db)).
apply: is_derive_opp.
apply is_derive_RInt_param_bound_comp_aux2; try easy.
move: If ; apply filter_imp.
intros y H.
now apply ex_RInt_swap.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
now rewrite Rmin_comm Rmax_comm.
intros t Ht.
apply Cf1.
now rewrite Rmin_comm Rmax_comm.
rewrite <- RInt_swap.
ring.
Qed.


Lemma is_derive_RInt_param_bound_comp :
 forall f a b x da db,
  (locally x (fun y => ex_RInt (fun t => f y t) (a x) (b x))) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps))) ->
  (exists eps:posreal, locally x (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps))) ->
  is_derive a x da ->
  is_derive b x db ->
  (exists eps:posreal, locally x
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) (b x -eps) <= t <= Rmax (a x+eps) (b x+eps) ->
        ex_derive (fun u : R => f u t) x0)) ->
  (forall t : R,
          Rmin (a x) (b x) <= t <= Rmax (a x) (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (a x) ->   continuity_pt (fun t => f x t) (b x) ->

  is_derive (fun x => RInt (fun t => f x t) (a x) (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) (b x)+(-f x (a x))*da+(f x (b x))*db).
Proof.
intros f a b x da db If Ifa Ifb Da Db Df Cf Cfa Cfb Ca Cb.
apply is_derive_ext_loc with (fun x0 : R => RInt (fun t : R => f x0 t) (a x0) (a x)
    + RInt (fun t : R => f x0 t) (a x) (b x0)).
apply RInt_Chasles_bound_comp_loc ; trivial.
apply derivable_continuous_pt.
eexists.
apply is_derive_Reals, Da.
apply derivable_continuous_pt.
eexists.
apply is_derive_Reals, Db.
eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct.
by apply locally_filter.
(* *)
apply is_derive_RInt_param_bound_comp_aux2; try easy.
exists (mkposreal _ Rlt_0_1).
intros y Hy.
apply ex_RInt_point.
by apply Da.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
intros t Ht.
apply Cf.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
now right.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
now right.
(* *)
apply is_derive_RInt_param_bound_comp_aux3; try easy.
by apply Db.
destruct Df as (e,H).
exists e.
move: H ; apply filter_imp.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
rewrite RInt_point.
simpl => y.
rewrite /plus /scal /= /mult /=.
ring.
Qed.

(** * Power series *)

Definition PS_Int (a : nat -> R) (n : nat) : R :=
  match n with
    | O => 0
    | S n => a n / INR (S n)
  end.

Lemma CV_radius_Int (a : nat -> R) :
  CV_radius (PS_Int a) = CV_radius a.
Proof.
  rewrite -CV_radius_derive.
  apply CV_radius_ext.
  rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
  field.
  apply Rgt_not_eq, INRp1_pos.
Qed.

Lemma is_RInt_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Rabs x) (CV_radius a)
  -> is_RInt (PSeries a) 0 x (PSeries (PS_Int a) x).
Proof.
  move => Hx.
  have H : forall y, Rmin 0 x <= y <= Rmax 0 x -> Rbar_lt (Rabs y) (CV_radius a).
    move => y Hy.
    apply: Rbar_le_lt_trans Hx.
    apply Rabs_le_between.
    split.
    apply Rle_trans with (2 := proj1 Hy).
    rewrite /Rabs /Rmin.
    case: Rcase_abs ; case: Rle_dec => // Hx Hx' ; rewrite ?Ropp_involutive.
    by apply Rlt_le.
    by apply Req_le.
    apply Ropp_le_cancel ; by rewrite Ropp_involutive Ropp_0.
    by apply Rge_le in Hx'.
    apply Rle_trans with (1 := proj2 Hy).
    rewrite /Rabs /Rmax.
    case: Rcase_abs ; case: Rle_dec => // Hx Hx'.
    by apply Rlt_not_le in Hx'.
    apply Ropp_le_cancel, Rlt_le ; by rewrite Ropp_involutive Ropp_0.
    by apply Req_le.
    by apply Rge_le in Hx'.

  apply is_RInt_ext with (Derive (PSeries (PS_Int a))).
  move => y Hy.
  rewrite Derive_PSeries.
  apply PSeries_ext ; rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
  field.
  apply Rgt_not_eq, INRp1_pos.
  rewrite CV_radius_Int.
  by apply H ; split ; apply Rlt_le ; apply Hy.
  evar_last.
  apply is_RInt_derive.
  move => y Hy.
  apply Derive_correct, ex_derive_PSeries.
  rewrite CV_radius_Int.
  by apply H.
  move => y Hy.
  apply continuous_ext_loc with (PSeries a).

  apply locally_interval with (Rbar_opp (CV_radius a)) (CV_radius a).
  apply Rbar_opp_lt ; rewrite Rbar_opp_involutive.
  apply: Rbar_le_lt_trans (H _ Hy).
  apply Rabs_maj2.
  apply: Rbar_le_lt_trans (H _ Hy).
  apply Rle_abs.
  move => z Hz Hz'.
  rewrite Derive_PSeries.
  apply PSeries_ext ; rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
  field.
  apply Rgt_not_eq, INRp1_pos.
  rewrite CV_radius_Int.
  apply (Rbar_abs_lt_between z) ; by split.
  apply continuity_pt_filterlim, PSeries_continuity.
  by apply H.

  rewrite PSeries_0 /(PS_Int _ 0) ; by rewrite Rminus_0_r.
Qed.

Lemma ex_RInt_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Rabs x) (CV_radius a)
  -> ex_RInt (PSeries a) 0 x.
Proof.
  move => Hx.
  exists (PSeries (PS_Int a) x).
  by apply is_RInt_PSeries.
Qed.

Lemma RInt_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Rabs x) (CV_radius a)
  -> RInt (PSeries a) 0 x = PSeries (PS_Int a) x.
Proof.
  move => Hx.
  apply is_RInt_unique.
  by apply is_RInt_PSeries.
Qed.

Lemma is_pseries_RInt (a : nat -> R) :
  forall x, Rbar_lt (Rabs x) (CV_radius a)
    -> is_pseries (PS_Int a) x (RInt (PSeries a) 0 x).
Proof.
  move => x Hx.
  assert (Ha := is_RInt_PSeries _ _ Hx).
  apply is_RInt_unique in Ha.
  rewrite Ha.
  apply PSeries_correct.
  apply CV_radius_inside.
  by rewrite CV_radius_Int.
Qed.
