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

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Coquelicot.

(** This file describes some complex analysis results, including path
integrals. The final goal is to prove a version of Cauchy-Lipschitz
theorem. *)


(** * Additionnal Lemmas *)

(** ** Complex.v *)

Local Open Scope C_scope.

Lemma is_linear_C_R (l : C -> C) :
  is_linear (U := C_NormedModule) (V := C_NormedModule) l ->
  is_linear (U := C_R_NormedModule) (V := C_R_NormedModule) l.
Proof.
  intros Lf.
  - split.
    intros ; apply Lf.
    simpl ; intros.
    rewrite !scal_R_Cmult ; by apply Lf.
    case: Lf => _ _ [M Lf].
    exists M ; split.
    by apply Lf.
    intros.
    rewrite -!Cmod_norm.
    apply Lf.
Qed.
Lemma is_linear_C_id_1 :
  is_linear (U := C_NormedModule) (V := AbsRing_NormedModule C_AbsRing)
  (fun y : C => y).
Proof.
  split => //.
  exists 1 ; split.
  by apply Rlt_0_1.
  intros x ; apply Req_le.
  rewrite Rmult_1_l ; reflexivity.
Qed.
Lemma is_linear_C_id_2 :
  is_linear (U := AbsRing_NormedModule C_AbsRing) (V := C_NormedModule)
  (fun y : C_NormedModule => y).
Proof.
  split => //.
  exists 1 ; split.
  by apply Rlt_0_1.
  intros x ; apply Req_le.
  rewrite Rmult_1_l ; reflexivity.
Qed.

Lemma is_linear_RtoC : is_linear RtoC.
Proof.
  split => //=.
  by intros ; rewrite RtoC_plus.
  intros ; rewrite {2}/scal /= /prod_scal /= scal_zero_r.
  reflexivity.
  exists (sqrt 2) ; split.
  apply Rlt_sqrt2_0.
  intros.
  eapply Rle_trans.
  rewrite -Cmod_norm.
  apply Cmod_2Rmax.
  simpl.
  rewrite Rabs_R0.
  rewrite Rmax_left.
  apply Rle_refl.
  apply Rabs_pos.
Qed.

Lemma continuous_RtoC x : continuous RtoC x.
Proof.
  apply filterlim_locally.
  intros eps ; exists eps => /= y Hy.
  split => //=.
  by apply ball_center.
Qed.

Lemma continuous_C_id_1 (x : C) :
  continuous (T := C_UniformSpace) (U := AbsRing_UniformSpace C_AbsRing) (fun y => y) x.
Proof.
  intros P HP.
  by apply locally_C.
Qed.
Lemma continuous_C_id_2 (x : C) :
  continuous (T := AbsRing_UniformSpace C_AbsRing) (U := C_UniformSpace) (fun y => y) x.
Proof.
  intros P HP.
  by apply locally_C.
Qed.
Lemma continuous_C (f : C -> C) (x : C) :
  continuous (T := C_UniformSpace) (U := C_UniformSpace) f x
  <-> continuous (T := AbsRing_UniformSpace C_AbsRing) (U := AbsRing_UniformSpace C_AbsRing) f x.
Proof.
  split => H.
  - intros P HP.
    by apply locally_C, H, locally_C.
  - intros P HP.
    by apply locally_C, H, locally_C.
Qed.

Lemma is_derive_filterdiff_C_R (f : C -> C) (x : C) (df : C -> C) :
  is_linear df ->
  is_derive (V := C_NormedModule) f x (df 1)
  -> filterdiff (U := C_R_NormedModule) (V := C_R_NormedModule) f (locally x) df.
Proof.
  move => Hdf [Lf Hf].
  split => //.
  apply is_linear_C_R.
  split ; apply Hdf.

  intros y Hy eps.
  apply: locally_le_locally_norm.
  case: (fun Hy => locally_norm_le_locally _ _ (Hf y Hy eps)) => {Hf} /= delta Hf => //.
  apply locally_C, Hy.
  by apply locally_C, Hf.
  exists delta => /= z Hz.
  rewrite -!Cmod_norm.
  rewrite -{1}(Cmult_1_r (minus (G := C_R_NormedModule) z y)).
  rewrite linear_scal.
  by apply Hf.
  by apply Hdf.
Qed.
Lemma filterdiff_C_R_is_derive (f : C -> C) (x : C) (df : C) :
  filterdiff (U := C_R_NormedModule) (V := C_R_NormedModule) f (locally x) (fun u => mult u df)
  -> is_derive (V := C_NormedModule) f x df.
Proof.
  intros (Lf,Df).
  split.
  apply is_linear_scal_l.

  intros y Hy eps.
  apply: locally_le_locally_norm.
  case: (fun Hy => locally_norm_le_locally _ _ (Df y Hy eps)) => {Df} /= delta Df => //.
  apply locally_C, Hy.
  by apply locally_C, Df.
  exists delta => /= z Hz.
  rewrite /norm /= /abs /= !Cmod_norm.
  apply Df, Hz.
Qed.

(** * Intégrale le long d’un segment *)

Definition C_RInt (f : R -> C) (a b : R) : C :=
  (RInt (fun t => fst (f t)) a b, RInt (fun t => snd (f t)) a b).

Lemma is_C_RInt_unique (f : R -> C) (a b : R) (l : C) :
  is_RInt f a b l -> C_RInt f a b = l.
Proof.
  intros Hf.
  apply RInt_fct_extend_pair with (3 := Hf).
  by apply is_RInt_unique.
  by apply is_RInt_unique.
Qed.
Lemma C_RInt_correct (f : R -> C) (a b : R) :
  ex_RInt f a b -> is_RInt f a b (C_RInt f a b).
Proof.
  case => l Hf.
  replace (C_RInt f a b) with l.
  by [].
  by apply sym_eq, is_C_RInt_unique.
Qed.

Lemma C_RInt_ext (f g : R -> C) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> g x = f x)
    -> C_RInt g a b = C_RInt f a b.
Proof.
  intros Heq.
  apply injective_projections ; simpl ;
  apply RInt_ext => x Hx ; by rewrite Heq.
Qed.
Lemma C_RInt_swap (f : R -> C) (a b : R) :
  - C_RInt f a b = C_RInt f b a.
Proof.
  apply injective_projections ; simpl ;
  apply RInt_swap.
Qed.
Lemma C_RInt_scal_R (f : R -> C) (a b : R) (k : R) :
  C_RInt (fun t => scal k (f t)) a b = scal k (C_RInt f a b).
Proof.
  apply injective_projections ; simpl ;
  apply RInt_scal.
Qed.
Lemma C_RInt_const c a b :
  C_RInt (fun _ => c) a b = scal (b - a) c.
Proof.
  apply injective_projections ; simpl ;
  rewrite RInt_const ; ring.
Qed.

Lemma is_C_RInt_scal f a b (k : C) l :
  is_RInt f a b l -> is_RInt (fun t => k * f t) a b (k * l).
Proof.
  intros H.
  move: (is_RInt_fct_extend_fst _ _ _ _ H) => /= H1.
  move: (is_RInt_fct_extend_snd _ _ _ _ H) => /= {H} H2.
  apply is_RInt_fct_extend_pair ; simpl.
  by apply: is_RInt_minus ; apply: is_RInt_scal.
  by apply: is_RInt_plus ; apply: is_RInt_scal.
Qed.
Lemma ex_C_RInt_scal f k a b :
  ex_RInt f a b -> ex_RInt (fun t => k * f t) a b.
Proof.
  intros [lf If].
  eexists.
  apply is_C_RInt_scal ; eassumption.
Qed.
Lemma C_RInt_scal (f : R -> C) (k : C) (a b : R) :
  ex_RInt f a b ->
  C_RInt (fun t => k * f t) a b = k * C_RInt f a b.
Proof.
  intros Hf.
  apply is_C_RInt_unique.
  apply is_C_RInt_scal.
  by apply C_RInt_correct.
Qed.

Lemma C_RInt_opp (f : R -> C) (a b : R) :
  C_RInt (fun t => - f t) a b = - C_RInt f a b.
Proof.
  apply injective_projections ; simpl ;
  apply RInt_opp.
Qed.
Lemma C_RInt_comp_lin (f : R -> C) (u v a b : R) :
  C_RInt (fun y : R => (u * f (u * y + v)%R)) a b =
     C_RInt f (u * a + v) (u * b + v).
Proof.
  apply injective_projections ; simpl ;
  rewrite -RInt_comp_lin ; apply RInt_ext => x _ ; ring.
Qed.
Lemma C_RInt_Chasles (f : R -> C) (a b c : R) :
  ex_RInt f a b -> ex_RInt f b c ->
  C_RInt f a b + C_RInt f b c =
     C_RInt f a c.
Proof.
  intros Hf1 Hf2.
  apply sym_eq, is_C_RInt_unique.
  apply C_RInt_correct in Hf1.
  apply C_RInt_correct in Hf2.

  move: (is_RInt_fct_extend_fst _ _ _ _ Hf1) => /= Hf1_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf1) => /= Hf1_2.
  move: (is_RInt_fct_extend_fst _ _ _ _ Hf2) => /= Hf2_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf2) => /= Hf2_2.
  now apply @is_RInt_Chasles with b ; apply is_RInt_fct_extend_pair.
Qed.

(** ** Definition 2 *)

Definition complex_segment (a b : C) (z : C) :=
  exists (t : R), (0 <= t <= 1)%R /\ z = scal (1 - t)%R a + scal t b.

Definition is_C_RInt_segm f z1 z2 l :=
  is_RInt (fun t => (z2 - z1) * f (scal (1-t)%R z1 + scal t z2)) 0 1 l.
Definition ex_C_RInt_segm (f : C -> C) (z1 z2 : C) :=
  exists l : C, is_C_RInt_segm f z1 z2 l.
Definition C_RInt_segm (f : C -> C) (z1 z2 : C) : C :=
  (z2 - z1) * C_RInt (fun t => f (scal (1 - t)%R z1 + scal t z2)) 0 1.

Lemma is_C_RInt_segm_unique (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z1 z2 l -> C_RInt_segm f z1 z2 = l.
Proof.
  intros.
  unfold C_RInt_segm.
  rewrite -C_RInt_scal.
  by apply is_C_RInt_unique.
  case: (Ceq_dec z1 z2) => Hz.
  - rewrite Hz.
    apply ex_RInt_ext with (fun _ => f z2).
      move => x _.
      apply f_equal.
      rewrite -{1}(scal_one (V := C_R_ModuleSpace) z2).
      replace (one (K := R_Ring)) with ((1-x)+x)%R.
      by rewrite scal_distr_r.
      change one with 1 ; ring.
    apply ex_RInt_const.
  - eapply ex_RInt_ext.
    2: apply (fun f => ex_C_RInt_scal f (/(z2 - z1))).
    2: eexists ; apply H.
    simpl => x _.
    fold C.
    field.
    contradict Hz.
    replace z2 with (z1 + (z2 - z1)) by ring.
    rewrite Hz ; ring.
Qed.
Lemma C_RInt_segm_correct (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> is_C_RInt_segm f z1 z2 (C_RInt_segm f z1 z2).
Proof.
  intros [l If].
  now rewrite (is_C_RInt_segm_unique _ _ _ _ If).
Qed.

(** ** Proposition 3 *)

Lemma is_C_RInt_segm_swap (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z2 z1 l -> is_C_RInt_segm f z1 z2 (-l).
Proof.
  rewrite /is_C_RInt_segm => H.
  evar (k : C).
  replace (- l) with k.
  apply is_RInt_swap.
  apply is_RInt_ext with (fun t : R => scal (-1) ((z1 - z2) * f (scal (1 - (-1 * t + 1)%R)%R z2 + scal (-1 * t + 1)%R z1)%C)).
    move => x _.
    replace (scal (1 - (-1 * x + 1)%R)%R z2 + scal (-1 * x + 1)%R z1)
      with (scal (1 - x)%R z1 + scal x z2).
      2 : apply injective_projections ; rewrite /= /scal /= /mult /= ; ring.
    rewrite scal_opp_one.
    change opp with Copp.
    change eq with (@eq C).
    field.
  apply (is_RInt_comp_lin (fun t : R => (z1 - z2) * f (scal (1 - t)%R z2 + scal t z1)) (-1)%R (1)%R 1 0).
  ring_simplify (-1 * 1 + 1)%R (-1 * 0 + 1)%R.
  apply H.
  by [].
Qed.
Lemma ex_C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z2 z1 -> ex_C_RInt_segm f z1 z2.
Proof.
  intros [l Hl].
  exists (-l) ; by apply is_C_RInt_segm_swap.
Qed.
Lemma C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  - C_RInt_segm f z1 z2 = C_RInt_segm f z2 z1.
Proof.
  unfold C_RInt_segm.
  generalize (opp_mult_l (z2 - z1) (C_RInt (fun t : R => f (scal (1 - t)%R z1 + scal t z2)) 0 1)).
  rewrite /opp /mult /=.
  move => /= ->.
  apply f_equal2.
  apply Copp_minus_distr.
  rewrite (C_RInt_ext (fun t : R => opp
    ((-1) * (f (scal (1 - (-1 * t + 1)%R)%R z2 + scal (-1 * t + 1)%R z1)%C)))).
  rewrite C_RInt_opp.
  rewrite C_RInt_swap.
  rewrite (C_RInt_comp_lin (fun t : R => f (scal (1 - t)%R z2 + scal t z1)) (-1) (1) 1 0) ;
  apply f_equal2 ; ring.
  intros x _ ; simpl.
  apply injective_projections ; simpl ; ring_simplify ;
  apply f_equal ; apply f_equal ;
  apply injective_projections ; rewrite /= /scal /= /mult /= ; ring.
Qed.

Definition complex_line (z1 z2 : C) (z : C) :=
  exists p : R, z = scal (1-p)%R z1 + scal p z2.

Lemma is_C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) l1 l2 :
  complex_line z1 z3 z2
  -> is_C_RInt_segm f z1 z2 l1 -> is_C_RInt_segm f z2 z3 l2
    -> is_C_RInt_segm f z1 z3 (plus l1 l2).
Proof.
  rewrite /is_C_RInt_segm ;
  case => p -> H1 H2.

  case: (Req_dec p 0) => Hp0.
  rewrite Hp0 in H1 H2 => {p Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f (scal (1 - t)%R z1 + scal t z3))) in H2.
Focus 2.
  move => x _.
  by rewrite scal_zero_l Rminus_0_r scal_one Cplus_0_r.
  apply (is_RInt_ext _ (fun _ => zero)) in H1.
Focus 2.
  move => x _ ; simpl.
  by rewrite scal_zero_l Rminus_0_r scal_one Cplus_0_r /Cminus Cplus_opp_r Cmult_0_l.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_l.

  case: (Req_dec 1 p) => Hp1.
  rewrite -Hp1 in H1 H2 => {p Hp1 Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f (scal (1 - t)%R z1 + scal t z3))) in H1.
Focus 2.
  move => x _.
  by rewrite Rminus_eq_0 scal_zero_l scal_one Cplus_0_l.
  apply (is_RInt_ext _ (fun _ => zero)) in H2.
Focus 2.
  move => x _ ; simpl.
  by rewrite Rminus_eq_0 scal_zero_l scal_one Cplus_0_l /Cminus Cplus_opp_r Cmult_0_l.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_r.

  apply is_RInt_Chasles with p.
  eapply is_RInt_ext, (is_RInt_comp_lin _ (/ p) 0).
  2: replace (/ p * 0 + 0)%R with 0 by ring.
  2: replace (/ p * p + 0)%R with 1 by now field.
  2: by apply H1.
  intros x _ ; simpl.
  rewrite !scal_R_Cmult !RtoC_minus !RtoC_plus !RtoC_mult !RtoC_inv //.
  rewrite Cmult_assoc.
  replace (/ p * ((1 - p) * z1 + p * z3 - z1)) with (z3 - z1).
  2: now field ; contradict Hp0 ; injection Hp0.
  apply f_equal, f_equal.
  now field ; contradict Hp0 ; injection Hp0.

  apply Rminus_eq_contra in Hp1.
  eapply is_RInt_ext, (is_RInt_comp_lin _ (/ (1 - p)) (-p / (1 - p))).
  2: replace (/ (1 - p) * p + - p / (1 - p))%R with 0 by now field.
  2: replace (/ (1 - p) * 1 + - p / (1 - p))%R with 1 by now field.
  2: by apply H2.
  intros x _ ; simpl.
  rewrite !scal_R_Cmult !RtoC_minus !RtoC_plus !RtoC_mult !RtoC_inv //
          !RtoC_opp !RtoC_minus.
  rewrite Cmult_assoc.
  replace (/ (1 - p) * (z3 - ((1 - p) * z1 + p * z3))) with (z3 - z1).
  2: now field ; contradict Hp0 ; injection Hp0.
  apply f_equal, f_equal.
  now field ; contradict Hp0 ; injection Hp0.
Qed.
Lemma ex_C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) :
  complex_line z1 z3 z2
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
    -> ex_C_RInt_segm f z1 z3.
Proof.
  intros Hz2 [l1 H1] [l2 H2] ; exists (plus l1 l2) ;
  by apply is_C_RInt_segm_Chasles with z2.
Qed.
Lemma C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) :
  complex_line z1 z3 z2
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 = C_RInt_segm f z1 z3.
Proof.
  intros.
  apply sym_eq, is_C_RInt_segm_unique.
  now apply is_C_RInt_segm_Chasles with z2 ;
  try (by apply C_RInt_segm_correct).
Qed.

Lemma is_C_RInt_segm_const c z1 z2 :
  is_C_RInt_segm (fun _ => c) z1 z2 ((z2 - z1) * c).
Proof.
  unfold is_C_RInt_segm.
  evar_last.
  apply is_RInt_const.
  by rewrite Rminus_0_r @scal_one.
Qed.
Lemma ex_C_RInt_segm_const c z1 z2 :
  ex_C_RInt_segm (fun _ => c) z1 z2.
Proof.
  eexists ; by apply is_C_RInt_segm_const.
Qed.
Lemma C_RInt_segm_const c z1 z2 :
  C_RInt_segm (fun _ => c) z1 z2 = (z2 - z1) * c.
Proof.
  apply is_C_RInt_segm_unique.
  by apply is_C_RInt_segm_const.
Qed.

Lemma is_C_RInt_segm_plus (f g : C -> C) (z1 z2 If Ig : C) :
  is_C_RInt_segm f z1 z2 If -> is_C_RInt_segm g z1 z2 Ig
  -> is_C_RInt_segm (fun z => f z + g z) z1 z2 (If + Ig).
Proof.
  unfold is_C_RInt_segm.
  intros Hf Hg.
  move: (is_RInt_plus _ _ _ _ _ _ Hf Hg).
  apply is_RInt_ext.
  intros x _.
  change plus with Cplus.
  by simpl ; ring_simplify.
Qed.
Lemma ex_C_RInt_segm_plus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> ex_C_RInt_segm (fun z => f z + g z) z1 z2.
Proof.
  intros (If,Hf) (Ig,Hg).
  exists (If + Ig).
  by apply is_C_RInt_segm_plus.
Qed.
Lemma C_RInt_segm_plus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> C_RInt_segm (fun z => f z + g z) z1 z2 = C_RInt_segm f z1 z2 + C_RInt_segm g z1 z2.
Proof.
  intros Hf Hg.
  apply is_C_RInt_segm_unique.
  apply is_C_RInt_segm_plus ;
  by apply C_RInt_segm_correct.
Qed.

Lemma is_C_RInt_segm_opp (f : C -> C) (z1 z2 If : C) :
  is_C_RInt_segm f z1 z2 If
  -> is_C_RInt_segm (fun z => - f z) z1 z2 (- If).
Proof.
  unfold is_C_RInt_segm.
  intros Hf.
  move: (is_RInt_opp _ _ _ _ Hf).
  apply is_RInt_ext.
  intros x _.
  change opp with Copp.
  by simpl ; ring_simplify.
Qed.
Lemma ex_C_RInt_segm_opp (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2
  -> ex_C_RInt_segm (fun z => - f z) z1 z2.
Proof.
  intros (If,Hf).
  exists (- If).
  by apply is_C_RInt_segm_opp.
Qed.
Lemma C_RInt_segm_opp (f : C -> C) (z1 z2 : C) :
  C_RInt_segm (fun z => - f z) z1 z2 = - C_RInt_segm f z1 z2.
Proof.
  unfold C_RInt_segm.
  rewrite C_RInt_opp ; ring.
Qed.

Lemma is_C_RInt_segm_minus (f g : C -> C) (z1 z2 If Ig : C) :
  is_C_RInt_segm f z1 z2 If -> is_C_RInt_segm g z1 z2 Ig
  -> is_C_RInt_segm (fun z => f z - g z) z1 z2 (If - Ig).
Proof.
  intros.
  apply is_C_RInt_segm_plus => //.
  by apply is_C_RInt_segm_opp.
Qed.
Lemma ex_C_RInt_segm_minus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> ex_C_RInt_segm (fun z => f z - g z) z1 z2.
Proof.
  intros.
  apply ex_C_RInt_segm_plus => //.
  by apply ex_C_RInt_segm_opp.
Qed.
Lemma C_RInt_segm_minus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> C_RInt_segm (fun z => f z - g z) z1 z2 = C_RInt_segm f z1 z2 - C_RInt_segm g z1 z2.
Proof.
  intros.
  rewrite C_RInt_segm_plus => //.
  by rewrite C_RInt_segm_opp.
  by apply ex_C_RInt_segm_opp.
Qed.

(** ** Proposition 4 *)

Lemma is_C_RInt_segm_norm (f : C -> C) (z1 z2 : C) lf (m : R) :
  is_C_RInt_segm f z1 z2 lf
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod lf <= m * (Cmod (z1 - z2)).
Proof.
  intros Cf Hm.
  rewrite 2!Cmod_norm.
  apply: (norm_RInt_le (fun t => (z2 - z1) * f (scal (1 - t)%R z1 + scal t z2)) (fun _ => Rmult (Cmod (z2 - z1)) m) 0 1).
  by apply Rle_0_1.
  intros x Hx.
  rewrite <- Cmod_norm.
  rewrite Cmod_mult.
  apply Rmult_le_compat_l.
  by apply Cmod_ge_0.
  apply Hm.
  now exists x ; split.
  by apply Cf.
  evar_last.
  apply is_RInt_const.
  rewrite -Cmod_norm -Cmod_opp Copp_minus_distr ; simpl.
  rewrite /scal /= /mult /=.
  ring.
Qed.
Lemma C_RInt_segm_norm f z1 z2 m :
  ex_C_RInt_segm f z1 z2
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod (C_RInt_segm f z1 z2) <= m * (Cmod (z1 - z2)).
Proof.
  intros.
  apply is_C_RInt_segm_norm with f.
  by apply C_RInt_segm_correct.
  by [].
Qed.

(** ** Proposition 5 *)

Lemma is_C_RInt_derive (f df : R -> C) (a b : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> continuous (U := C_R_NormedModule) df x) ->
    is_RInt df a b (f b - f a).
Proof.
  intros.
  apply is_RInt_fct_extend_pair ; simpl.

  apply (is_RInt_derive (fun y => fst (f y)) (fun y => fst (df y))).
  intros x Hx.
  unfold is_derive.
  evar_last.
  apply (filterdiff_comp' f (@fst R R)).
  by apply H.
  apply filterdiff_linear, is_linear_fst.
  by simpl.
  intros x Hx.
  apply continuous_comp.
  by apply H0.
  apply continuous_fst.

  apply (is_RInt_derive (fun y => snd (f y)) (fun y => snd (df y))).
  intros x Hx.
  unfold is_derive.
  evar_last.
  apply (filterdiff_comp' f (@snd R R)).
  by apply H.
  apply filterdiff_linear, is_linear_snd.
  by simpl.
  intros x Hx.
  apply continuous_comp.
  by apply H0.
  apply continuous_snd.
Qed.

Lemma continuous_C_segm (f : C -> C) (z1 z2 : C) :
  (forall z : C, complex_segment z1 z2 z -> continuous f z) ->
  (forall z : R, 0 <= z <= 1 ->
    continuous (fun t : R => (z2 - z1) * f (scal (1 - t)%R z1 + scal t z2)) z).
Proof.
  intros Cf z Hz.
  apply @continuous_scal.
  apply continuous_const.
  apply continuous_comp.
  apply @continuous_plus.
  apply (continuous_scal_l (K := R_AbsRing) (V := C_R_NormedModule)).
  apply @continuous_minus.
  apply continuous_const.
  apply continuous_id.
  apply (continuous_scal_l (K := R_AbsRing) (V := C_R_NormedModule)).
  apply continuous_id.
  apply Cf.
  by exists z.
Qed.

Lemma is_C_RInt_segm_derive (f g : C -> C) (z1 z2 : C) :
  (forall z, complex_segment z1 z2 z -> is_derive g z (f z))
  -> (forall z, complex_segment z1 z2 z -> continuous f z)
  -> is_C_RInt_segm f z1 z2 (g z2 - g z1).
Proof.
  intros Dg Cf.
  unfold is_C_RInt_segm.
  evar_last.
  apply (is_C_RInt_derive (fun t : R => g (scal (1 - t)%R z1 + scal t z2))
                          (fun t => (z2 - z1) * f (scal (1 - t)%R z1 + scal t z2))).
    rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
    intros.
    eapply filterdiff_ext_lin.
    apply (filterdiff_comp' (U := R_NormedModule) (V := C_R_NormedModule)
      (fun t : R => (scal (1 - t)%R z1 + scal t z2)%C) g).
    apply @filterdiff_plus_fct.
    apply locally_filter.
    apply (filterdiff_scal_l_fct (U := R_NormedModule) (V := C_R_NormedModule)
      z1 (fun u : R => (1 - u)%R)).
    apply @filterdiff_minus_fct.
    by apply locally_filter.
    apply filterdiff_const.
    apply filterdiff_id.
    apply filterdiff_linear.
    move: (is_linear_scal_l (V := C_R_NormedModule) z2) => //=.
    apply is_derive_filterdiff_C_R.
    instantiate (1 := (fun y => y * f (scal (1 - x)%R z1 + scal x z2))).
    apply (is_linear_comp (U := C_NormedModule) (V := AbsRing_NormedModule C_AbsRing) (fun y => y)).
    apply is_linear_C_id_1.
    apply @is_linear_scal_l.
    simpl ; rewrite Cmult_1_l.
    apply Dg.
    by exists x.
  simpl.
  rewrite /= /scal /= /mult /= /prod_scal.
  change scal with Rmult.
  change plus with Cplus.
  change minus with Rminus.
  change zero with 0.
  intros y ; apply injective_projections ; simpl ; ring.

  rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
  by apply continuous_C_segm.

  rewrite Rminus_eq_0 Rminus_0_r !scal_one !scal_zero_l.
  by rewrite Cplus_0_l Cplus_0_r.
Qed.

(** ** Corollaire 6 *)

Lemma C_RInt_segm_derive (f : C -> C) (z1 z2 : C) :
  (forall z, complex_segment z1 z2 z -> ex_derive f z)
  -> (forall z, complex_segment z1 z2 z -> continuous (C_derive f) z)
  -> C_RInt_segm (C_derive f) z1 z2 = f z2 - f z1.
Proof.
  intros.
  apply is_C_RInt_segm_unique, is_C_RInt_segm_derive => //.
  intros z Hz.
  by apply C_derive_correct, H.
Qed.

(** ** Corolaire 7 *)

Lemma is_C_RInt_segm_triangle (f g : C -> C) (z1 z2 z3 : C) :
  (forall z, complex_segment z1 z2 z -> is_derive g z (f z))
  -> (forall z, complex_segment z2 z3 z -> is_derive g z (f z))
  -> (forall z, complex_segment z3 z1 z -> is_derive g z (f z))
  -> (forall z, complex_segment z1 z2 z -> continuous f z)
  -> (forall z, complex_segment z2 z3 z -> continuous f z)
  -> (forall z, complex_segment z3 z1 z -> continuous f z)
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 + C_RInt_segm f z3 z1 = 0.
Proof.
  intros.
  erewrite !is_C_RInt_segm_unique ; last first.
  apply is_C_RInt_segm_derive ; eassumption.
  apply is_C_RInt_segm_derive ; eassumption.
  apply is_C_RInt_segm_derive ; eassumption.
  ring.
Qed.

(** ** Proposition 8 *)

Definition is_starred (U : C -> Prop) (z0 : C) :=
  forall z1 : C, U z1 -> forall z, complex_segment z0 z1 z -> U z.

Lemma ex_C_RInt_segm_continuous f z1 z2 :
  (forall z, complex_segment z1 z2 z -> continuous f z)
  -> ex_C_RInt_segm f z1 z2.
Proof.
  intros Cf.
  apply (ex_RInt_continuous (V := C_R_CompleteNormedModule)).
  rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
  by apply continuous_C_segm.
Qed.

Lemma locally_C_segm (P : C -> Prop) :
  forall z0, locally z0 P
    -> locally z0 (fun z => forall y, complex_segment z0 z y -> P y).
Proof.
  intros z0 (e,He).
  assert (Hd : 0 < e / (norm_factor (V := C_NormedModule))).
    apply Rdiv_lt_0_compat.
    by apply e.
    by apply norm_factor_gt_0.
  set (d := mkposreal _ Hd).
  exists d => z Hz _ [x [Hx ->]].
  apply He.
  apply (norm_compat1 (V := C_NormedModule)).
  change minus with Cminus ;
  change norm with Cmod.
  replace (scal (1 - x)%R z0 + scal x z - z0) with (x * (z - z0)).
  2: rewrite !scal_R_Cmult RtoC_minus /= ; by ring_simplify.
  rewrite Cmod_mult.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_r.
  by apply Cmod_ge_0.
  rewrite Cmod_R Rabs_pos_eq ; apply Hx.
  rewrite Rmult_1_l.
  replace (pos e) with ((norm_factor (V := C_NormedModule)) * d)%R.
  by apply (norm_compat2 (V := C_NormedModule)).
  rewrite /d /= ; field.
  by apply Rgt_not_eq, norm_factor_gt_0.
Qed.

Lemma complex_segment_swap z1 z2 :
  forall z, complex_segment z1 z2 z -> complex_segment z2 z1 z.
Proof.
  move => _ [z [Hz ->]].
  exists (1 - z)%R ; split.
  split.
  apply Rle_minus_r ; ring_simplify ; apply Hz.
  apply Rminus_le_0 ; ring_simplify ; apply Hz.
  rewrite !scal_R_Cmult !RtoC_minus ; ring.
Qed.

Lemma ex_antiderive_segm (U : C -> Prop) (z0 : C) (f : C -> C) :
  open U -> is_starred U z0
  -> continuous_on U f
  -> (forall z1 z2 : C, U z1 -> U z2 ->
         (forall z, complex_segment z1 z2 z -> U z)
         -> C_RInt_segm f z0 z1 + C_RInt_segm f z1 z2 + C_RInt_segm f z2 z0 = 0)
  -> forall z, U z -> is_derive (C_RInt_segm f z0) z (f z).
Proof.
  intros oU sU Cf Hf.

  assert (forall z, U z -> locally z (ex_C_RInt_segm f z)).
    intros z Hz.
    move: (locally_C_segm _ _ (oU z Hz)).
    apply filter_imp => y Hy.
    apply ex_C_RInt_segm_continuous.
    intros z1 Hz1.
    apply continuous_continuous_on with U => //.
    by apply oU, Hy.

  intros z Hz.
  split.
  by apply @is_linear_scal_l.
  simpl => x Hx eps.
  change norm with Cmod ;
  change minus with Cminus.
  replace x with z.
  2: by apply @is_filter_lim_locally_unique in Hx.
  clear x Hx.
  eapply filter_imp.
  intros x Hx.
  rewrite {2}/Cminus C_RInt_segm_swap Cplus_comm.
  replace (C_RInt_segm f z z0 + C_RInt_segm f z0 x)
    with ((C_RInt_segm f z0 x + C_RInt_segm f x z + C_RInt_segm f z z0) + - (C_RInt_segm f x z))
    by ring.
  rewrite Hf => //.
  rewrite C_RInt_segm_swap.
  move: (@plus_zero_l _ (C_RInt_segm f z x)).
  change plus with Cplus ; change zero with (RtoC 0).
  move => ->.
  eapply (proj1 Hx).
  eapply (proj1 (proj2 Hx)).
  apply (proj2 (proj2 Hx)).
  repeat apply filter_and.
  2: by apply locally_C, (oU z).
  eapply filter_imp.
  intros x Hx.
  change scal with Cmult ;
  rewrite -C_RInt_segm_const.
  rewrite -C_RInt_segm_minus.
  2: eapply (proj1 Hx).
  rewrite -(Cmod_opp (_-_)).
  move: (opp_minus (G := C_AbelianGroup)).
  change opp with Copp ; change minus with Cminus.
  move => ->.
  apply is_C_RInt_segm_norm with (fun z1 : C => f z1 - f z).
  apply C_RInt_segm_correct.
  apply ex_C_RInt_segm_minus.
  by apply Hx.
  by apply ex_C_RInt_segm_const.
  apply (proj2 Hx).
  apply ex_C_RInt_segm_const.
  apply filter_and.
  by apply locally_C, H.
  apply locally_C.
  assert (He : 0 < eps / (norm_factor (V := C_NormedModule))).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply norm_factor_gt_0.
  set (e := mkposreal _ He).
  destruct (proj1 (filterlim_locally _ _) (continuous_continuous_on _ _ z (oU z Hz) Cf) e)
    as [d Hd].
  exists d => /= y Hy x Hx.
  replace (pos eps) with ((norm_factor (V := C_NormedModule)) * e)%R.
  apply Rlt_le, (norm_compat2 (V := C_NormedModule)).
  apply Hd.
  case: Hx => {x} x [Hx ->].
  split.
  rewrite /ball /= /AbsRing_ball.
  change minus with Rminus ; change abs with Rabs.
  change scal with Rmult ;
  replace ((1 - x) * fst z + x * fst y - fst z)%R
    with (x * (fst y - fst z))%R by ring.
  rewrite Rabs_mult.
  eapply Rle_lt_trans, (proj1 Hy).
  rewrite -(Rmult_1_l (abs _)).
  apply Rmult_le_compat_r.
  by apply abs_ge_0.
  rewrite Rabs_pos_eq ; apply Hx.
  rewrite /ball /= /AbsRing_ball.
  change minus with Rminus ; change abs with Rabs.
  change scal with Rmult ;
  replace ((1 - x) * snd z + x * snd y - snd z)%R
    with (x * (snd y - snd z))%R by ring.
  rewrite Rabs_mult.
  eapply Rle_lt_trans, (proj2 Hy).
  rewrite -(Rmult_1_l (abs _)).
  apply Rmult_le_compat_r.
  by apply abs_ge_0.
  rewrite Rabs_pos_eq ; apply Hx.
  rewrite /e /= ; field.
  by apply Rgt_not_eq, norm_factor_gt_0.
  apply locally_C.
  move: (locally_C_segm _ _ (oU z Hz)).
  apply filter_imp ; intros.
  by apply H0, complex_segment_swap.
Qed.

(** ** Definition 11 *)

Definition complex_triangle (a b c : C) (z : C) :=
  exists (a' b' c' : R), 0 <= a' /\ 0 <= b' /\ 0 <= c' /\ (a' + b' + c' = 1)%R
                      /\ z = scal a' a + scal b' b + scal c' c.

Definition complex_triangle_perimeter (a b c : C) : R :=
  (Cmod (a - c)%C + Cmod (b - a)%C + Cmod (c - b)%C)%R.
Definition complex_triangle_diameter (a b c : C) : R :=
  Rmax (Cmod (a - c)) (Rmax (Cmod (b - a)) (Cmod (c - b))).

Lemma complex_triangle_turn (a b c : C) (z : C) :
  complex_triangle a b c z -> complex_triangle b c a z.
Proof.
  intros (a',(b',(c',(Ha,(Hb,(Hc,(Habs,->))))))).
  exists b', c', a'.
  replace (b' + c' + a')%R with (a' + b' + c')%R by ring.
  repeat split => //.
  rewrite Cplus_comm Cplus_assoc.
  by rewrite Cplus_comm Cplus_assoc.
Qed.
Lemma complex_triangle_perimeter_turn  (a b c : C) :
  complex_triangle_perimeter a b c = complex_triangle_perimeter b c a.
Proof.
  unfold complex_triangle_perimeter ; ring.
Qed.
Lemma complex_triangle_diameter_turn  (a b c : C) :
  complex_triangle_diameter a b c = complex_triangle_diameter b c a.
Proof.
  unfold complex_triangle_diameter.
  apply sym_eq ; rewrite Rmax_assoc.
  apply Rmax_comm.
Qed.
Lemma complex_triangle_swap (a b c : C) (z : C) :
  complex_triangle a b c z -> complex_triangle a c b z.
Proof.
  intros (a',(b',(c',(Ha,(Hb,(Hc,(Habc,->))))))).
  exists a', c', b'.
  replace (a' + c' + b')%R with (a' + b' + c')%R by ring.
  repeat split => //.
  rewrite -!Cplus_assoc ; apply f_equal, Cplus_comm.
Qed.
Lemma complex_triangle_perimeter_swap  (a b c : C) :
  complex_triangle_perimeter a b c = complex_triangle_perimeter a c b.
Proof.
  unfold complex_triangle_perimeter.
  rewrite -3!(Cmod_opp (_-_)) !Copp_minus_distr ; ring.
Qed.
Lemma complex_triangle_diameter_swap  (a b c : C) :
  complex_triangle_diameter a b c = complex_triangle_diameter a c b.
Proof.
  unfold complex_triangle_diameter.
  rewrite -3!(Cmod_opp (_-_)) !Copp_minus_distr.
  rewrite Rmax_comm -Rmax_assoc.
  apply f_equal, Rmax_comm.
Qed.
Lemma complex_segment_triangle (a b c : C) (z : C) :
  complex_segment b c z -> complex_triangle a b c z.
Proof.
  intros (p,(Hp,->)).
  exists 0,(1-p)%R,p.
  repeat split => //.
  by apply Rle_refl.
  apply -> Rminus_le_0 ; apply Hp.
  by apply Hp.
  ring.
  rewrite !scal_R_Cmult !RtoC_minus.
  by ring_simplify.
Qed.

Lemma complex_triangle_diameter_segment (a b c : C) :
  forall z, complex_segment b c z
    -> Cmod (z - a) <= complex_triangle_diameter a b c.
Proof.
  intros _ (p,(Hp,->)).
  rewrite !scal_R_Cmult RtoC_minus.
  replace ((1 - p) * b + p * c - a)
    with ((1 - p) * (b - a) + p * (c - a))
    by ring.
  eapply Rle_trans.
  apply Cmod_triangle.
  rewrite !Cmod_mult -RtoC_minus !Cmod_R.
  eapply Rle_trans.
  apply Rplus_le_compat ; apply Rmult_le_compat_l ;
  try apply Rabs_pos.
  apply (Rmax_l _ (Cmod (c - a))).
  apply (Rmax_r (Cmod (b - a))).
  rewrite -Rmult_plus_distr_r.
  rewrite !Rabs_pos_eq.
  ring_simplify ; rewrite /complex_triangle_diameter.
  rewrite Rmax_comm -Cmod_opp Copp_minus_distr Rmax_assoc.
  by apply Rmax_l.
  apply Hp.
  apply -> Rminus_le_0 ; apply Hp.
Qed.
Lemma complex_triangle_diameter_corner (a b c : C) :
  forall z, complex_triangle a b c z
    -> Cmod (z - a) <= complex_triangle_diameter a b c.
Proof.
  intros _ [x [y [z [Hx [ Hy [ Hz [H ->]]]]]]].
  rewrite !scal_R_Cmult.
  case: (Req_dec y 1) => Hb.
(* z = b *)
  rewrite Hb {y Hb Hy} in H |- *.
  assert (x = 0).
    apply Rle_antisym => //.
    apply Rplus_le_reg_r with (1 + z)%R.
    rewrite -Rplus_assoc H.
    by apply Rminus_le_0 ; ring_simplify.
  rewrite H0 {x H0 Hx} in H |- *.
  assert (z = 0).
    replace z with ((0 + 1 + z)%R - 1)%R by ring.
    rewrite H ; ring.
  rewrite H0 !Cmult_0_l Cmult_1_l Cplus_0_l Cplus_0_r.
  eapply Rle_trans, Rmax_r.
  by apply Rmax_l.
(* z <> b *)
  assert (x + z <> 0)%R.
    contradict Hb.
    replace y with ((x + y + z) - (x + z))%R by ring.
    by rewrite Hb Rminus_0_r H.
  eapply Rle_trans.
  apply (complex_triangle_diameter_segment a b (scal (x / (x + z))%R a + scal (z / (x + z))%R c)).
  exists (x + z)%R ; split.
  split.
  by apply Rplus_le_le_0_compat.
  by rewrite -H ; apply Rminus_le_0 ; ring_simplify.
  rewrite -H !scal_R_Cmult RtoC_minus !RtoC_div // !RtoC_plus.
  field ; contradict H0 ; by injection H0.
  rewrite /complex_triangle_diameter.
  apply Rmax_le_compat.
  rewrite !scal_R_Cmult !RtoC_div // !RtoC_plus.
  replace (a - (x / (x + z) * a + z / (x + z) * c))
    with (z / (x + z) * (a - c)).
    2: field ; contradict H0 ; by injection H0.
  rewrite Cmod_mult -!RtoC_plus -RtoC_div // Cmod_R.
  rewrite -{2}(Rmult_1_l (Cmod _)) ;
  apply Rmult_le_compat_r.
  by apply Cmod_ge_0.
  rewrite Rabs_div // !Rabs_pos_eq //.
  2: by apply Rplus_le_le_0_compat.
  apply -> Rdiv_le_1.
  apply Rminus_le_0 ; by ring_simplify.
  assert (0 <= x + z) by now apply Rplus_le_le_0_compat.
  by apply sym_not_eq in H0 ; case: H1 => H1.
  apply Rmax_case.
  by apply Rmax_l.
  rewrite !scal_R_Cmult !RtoC_div // !RtoC_plus.
  replace (x / (x + z) * a + z / (x + z) * c - b)
    with (x / (x + z) * (a - b) + z / (x + z) * (c - b)).
    2: field ; contradict H0 ; by injection H0.
  eapply Rle_trans.
  eapply Rle_trans, Rplus_le_compat.
  apply Cmod_triangle.
  rewrite Cmod_mult -!RtoC_plus -RtoC_div // Cmod_R.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  rewrite -Cmod_opp Copp_minus_distr.
  apply (Rmax_l _ (Cmod (c - b))).
  rewrite Cmod_mult -!RtoC_plus -RtoC_div // Cmod_R.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply (Rmax_r (Cmod (b - a))).
  rewrite -Rmult_plus_distr_r.
  rewrite !Rabs_pos_eq.
  replace (x / (x + z) + z / (x + z))%R with 1 by now field.
  rewrite Rmult_1_l ; apply Rle_refl.
  apply Rdiv_le_0_compat => //.
  assert (0 <= x + z) by now apply Rplus_le_le_0_compat.
  by apply sym_not_eq in H0 ; case: H1 => H1.
  apply Rdiv_le_0_compat => //.
  assert (0 <= x + z) by now apply Rplus_le_le_0_compat.
  by apply sym_not_eq in H0 ; case: H1 => H1.
Qed.

Lemma complex_triangle_diameter_le (a b c z0 z : C) :
  complex_triangle a b c z0 ->
  complex_triangle a b c z
    -> Cmod (z - z0) <= complex_triangle_diameter a b c.
Proof.
  case => {z0} x0 [y0 [z0 [Hx0 [ Hy0 [ Hz0 [H0 ->]]]]]].
  case => {z} x' [y' [z' [Hx' [ Hy' [ Hz' [H' ->]]]]]].
  case: (Req_dec x0 1) => Ha0.
(* z0 = a *)
    replace (scal x0 a + scal y0 b + scal z0 c) with a.
    apply (complex_triangle_diameter_corner a b c).
    by exists x', y', z'.
    rewrite Ha0 scal_one Rplus_assoc -{2}(Rplus_0_r 1) {x0 Ha0 Hx0} in H0 |- *.
    apply Rplus_eq_reg_l in H0.
    replace y0 with 0.
    replace z0 with 0.
    rewrite !scal_zero_l.
    change zero with (RtoC 0).
    by rewrite !Cplus_0_r.
    eapply sym_eq, Rplus_eq_0_l => //.
    2: erewrite Rplus_comm ; apply H0.
    by [].
    eapply sym_eq, Rplus_eq_0_l => //.
    2: apply H0.
    by [].
  rewrite !scal_R_Cmult.
(* z0 est plus loin de a que z *)
  wlog: x' y' z' x0 y0 z0 Hx' Hy' Hz' H' Hx0 Hy0 Hz0 H0 Ha0 / (x0 <= x') => [Hw | Ha].
    case: (Rle_lt_dec x0 x') => Ha.
    by apply Hw.
    rewrite -Cmod_opp Copp_minus_distr.
    apply Hw => //.
    eapply Rlt_not_eq, Rlt_le_trans.
    by apply Ha.
    rewrite -H0 Rminus_le_0 ; ring_simplify.
    by apply Rplus_le_le_0_compat.
    by apply Rlt_le.
    assert (y0 + z0 <> 0)%R.
      contradict Ha0.
      rewrite -H0 Rplus_assoc Ha0 ; ring.
    assert (0 < y0 + z0).
       assert (0 <= y0 + z0) by now apply Rplus_le_le_0_compat.
       case: H1 => // H1.
       by apply sym_eq in H1.
    assert (y' + z' <= y0 + z0).
      replace (y' + z')%R with (1 - x')%R by (rewrite -H' ; ring).
      replace (y0 + z0)%R with (1 - x0)%R by (rewrite -H0 ; ring).
      apply Rplus_le_compat_l.
      by apply Ropp_le_contravar.
(* z0 \in [b;c] *)
  wlog: b c x0 y0 z0 x' y' z' Hx0 Hy0 Hz0 Hx' Hy' Hz' H' H0 Ha Ha0 H2 H H1 / (x0 = 0) => [Hw | {Hx0 Ha} Hx0].
    set (b' := scal x0 a + scal (y0 + z0)%R b).
    set (c' := scal x0 a + scal (y0 + z0)%R c).
    eapply Rle_trans.
    eapply Rle_trans, (Hw b' c' 0 (y0 / (y0 + z0))%R (z0 / (y0 + z0))%R
                                (x' - x0 * (y' + z') / (y0 + z0))%R (y' / (y0 + z0))%R (z' / (y0 + z0))%R) => //.
    apply Req_le ; apply f_equal.
    rewrite /b' /c' !scal_R_Cmult RtoC_minus !RtoC_div // RtoC_mult !RtoC_plus.
    field.
    by contradict H ; injection H.

    by apply Rle_refl.
    apply Rdiv_le_0_compat => //.
    apply Rdiv_le_0_compat => //.
    rewrite -Rminus_le_0 -(Rmult_1_r x') /Rdiv Rmult_assoc.
    apply Rmult_le_compat => //.
    apply Rdiv_le_0_compat => //.
    by apply Rplus_le_le_0_compat.
    apply -> Rdiv_le_1 => //.
    apply Rdiv_le_0_compat => //.
    apply Rdiv_le_0_compat => //.
    replace x0 with (1 - (y0 + z0))%R by (rewrite -H0 ; ring).
    replace x' with (1 - (y' + z'))%R by (rewrite -H' ; ring).
    now field.
    now field.
    rewrite -Rminus_le_0 -(Rmult_1_r x') /Rdiv Rmult_assoc.
    apply Rmult_le_compat => //.
    apply Rdiv_le_0_compat => //.
    by apply Rplus_le_le_0_compat.
    apply -> Rdiv_le_1 => //.
    by apply Rlt_not_eq, Rlt_0_1.
    rewrite /Rdiv -!Rmult_plus_distr_r.
    apply Rmult_le_compat_r => //.
    by apply Rlt_le, Rinv_0_lt_compat.
    replace (y0 / (y0 + z0) + z0 / (y0 + z0))%R with 1 by now field.
    by apply Rgt_not_eq, Rlt_0_1.
    replace (y0 / (y0 + z0) + z0 / (y0 + z0))%R with 1 by now field.
    by apply Rlt_0_1.

    rewrite /complex_triangle_diameter /c' /b' !scal_R_Cmult RtoC_plus.
    replace (a - (x0 * a + (y0 + z0) * c))
      with ((y0 + z0) * (a - c)).
    replace (x0 * a + (y0 + z0) * b - a)
      with ((y0 + z0) * (b - a)).
    replace (x0 * a + (y0 + z0) * c - (x0 * a + (y0 + z0) * b))
      with ((y0 + z0) * (c - b)) by ring.
    rewrite !Cmod_mult -RtoC_plus  Cmod_R.
    rewrite !RmaxRmult ; try by apply Rabs_pos.
    rewrite -{2}(Rmult_1_l (Rmax _ _)).
    apply Rmult_le_compat_r.
    eapply Rle_trans, Rmax_l ; apply Cmod_ge_0.
    rewrite Rabs_pos_eq.
    by rewrite Rminus_le_0 -H0 ; ring_simplify.
    by apply Rlt_le.
    replace x0 with (1 - (y0 + z0))%R by (rewrite -H0 ; ring).
    rewrite RtoC_minus RtoC_plus ; ring.
    replace x0 with (1 - (y0 + z0))%R by (rewrite -H0 ; ring).
    rewrite RtoC_minus RtoC_plus ; ring.
  rewrite Hx0 Cmult_0_l Cplus_0_l Rplus_0_l {x0 Hx0 Ha0 H H1} in H0 |- *.
  clear H2.
(* z est plus proche de [a;b] que z0 *)
  wlog: b c y' z' y0 z0 Hy' Hz' H' Hy0 Hz0 H0 / ((y' + z') * y0 <= y') => [Hw | Hab].
    case: (Rle_lt_dec ((y' + z') * y0)%R y') => Hab.
    by apply Hw.
    rewrite complex_triangle_diameter_swap.
    rewrite -Cplus_assoc !(Cplus_comm (_ * b)) Cplus_assoc.
    apply Hw => //.
    rewrite -H' ; ring.
    by rewrite Rplus_comm.
    rewrite Rplus_comm.
    pattern z' at 2 ; replace z' with ((y' + z') - y')%R by ring.
    replace z0 with (1 - y0)%R by (rewrite -H0 ; ring).
    rewrite Rmult_plus_distr_l Rmult_1_r.
    apply Rplus_le_compat_l.
    apply Ropp_le_cancel ; rewrite Ropp_involutive.
    eapply Rlt_le, Rlt_le_trans.
    apply Hab.
    apply Req_le ; ring.
  assert (Hac : z' <= (y' + z') * z0).
    pattern z' at 1 ; replace z' with ((y' + z') - y')%R by ring.
    replace z0 with (1 - y0)%R by (rewrite -H0 ; ring).
    rewrite Rmult_plus_distr_l Rmult_1_r.
    apply Rplus_le_compat_l.
    apply Ropp_le_cancel ; rewrite Ropp_involutive.
    eapply Rle_trans, Hab.
    apply Req_le ; ring.
  case: (Req_dec y0 1) => Hb.
(* z0 = b *)
  replace (y0 * b + z0 * c) with b.
    rewrite complex_triangle_diameter_turn.
    apply complex_triangle_diameter_corner.
    exists y', z', x' ; repeat split => //.
    rewrite -H' ; ring.
    rewrite !scal_R_Cmult ; ring.
    unfold complex_triangle_diameter.
    replace z0 with (1 - y0)%R by (rewrite -H0 ; ring).
    rewrite RtoC_minus Hb ; ring.
(* z0 = c *)
  assert (Hc : (z0 <> 0)%R).
    contradict Hb ; rewrite -H0 Hb ; ring.
  wlog: c y0 z0 y' z' Hy0 Hz0 H0 Hy' Hz' H' Hab Hac Hb Hc / (z0 = 1) => [Hw | {Hc} Hc].
    set (c' := (y0 * b + z0 * c)).
    eapply Rle_trans.
    eapply Rle_trans, (Hw c' 0 1) => //.
    rewrite /c' Cmult_plus_distr_l Cplus_assoc !Cmult_assoc.
    rewrite -(Cplus_assoc _ (_ * b) (_*b)) -Cmult_plus_distr_r.
    instantiate (2 := (z' / z0)%R).
    replace ((z' / z0)%R * z0) with (RtoC z').
    2: rewrite RtoC_div // ; now field ; contradict Hc ; injection Hc.
    replace ((z' / z0)%R * y0) with (z' / z0 - RtoC z').
    2: replace y0 with (1 - z0)%R by (rewrite -H0 ; ring).
    2: rewrite RtoC_div // RtoC_minus ; now field ; contradict Hc ; injection Hc.
    instantiate (1 := (y' - (z' / z0 - z'))%R).
    apply Req_le, f_equal.
    rewrite !RtoC_minus RtoC_div // ; ring.

    by apply Rle_refl.
    by apply Rle_0_1.
    ring.
    rewrite -Rminus_le_0 Rle_minus_l Rle_div_l //.
    apply sym_not_eq in Hc ; by case: Hz0.
    apply Rdiv_le_0_compat => //.
    apply sym_not_eq in Hc ; case: Hz0 => //.
    rewrite -H' ; ring.
    rewrite Rmult_0_r.
    rewrite -Rminus_le_0 Rle_minus_l Rle_div_l //.
    apply sym_not_eq in Hc ; by case: Hz0.
    rewrite Rmult_1_r.
    rewrite -Rle_minus_l Rminus_eq_0 -Rminus_le_0 Rle_minus_l Rle_div_l //.
    apply sym_not_eq in Hc ; by case: Hz0.
    by apply Rlt_not_eq, Rlt_0_1.
    by apply Rgt_not_eq, Rlt_0_1.

    rewrite /complex_triangle_diameter /c'.
    apply Rmax_case.
    replace (a - (y0 * b + z0 * c)) with
      (y0 * (a - b) + z0 * (a - c)).
    2: replace y0 with (1 - z0)%R by (rewrite -H0 ; ring).
    2: rewrite RtoC_minus ; ring.
    eapply Rle_trans.
    eapply Rle_trans, Rplus_le_compat.
    apply Cmod_triangle.
    rewrite Cmod_mult Cmod_R -Cmod_opp Copp_minus_distr.
    apply Rmult_le_compat_l.
    by apply Rabs_pos.
    apply (Rmax_r (Cmod (a - c))).
    rewrite Cmod_mult Cmod_R.
    apply Rmult_le_compat_l.
    by apply Rabs_pos.
    apply (Rmax_l _ (Cmod (b - a))).
    rewrite -Rmult_plus_distr_r.
    rewrite !Rabs_pos_eq // H0 Rmult_1_l.
    rewrite Rmax_assoc ; apply Rmax_l.
    apply Rmax_case.
    eapply Rle_trans, Rmax_r.
    apply Rmax_l.
    replace (y0 * b + z0 * c - b) with (z0 * (c - b)).
    2: replace y0 with (1 - z0)%R by (rewrite -H0 ; ring).
    2: rewrite RtoC_minus ; ring.
    rewrite Cmod_mult Cmod_R.
    eapply Rle_trans, Rmax_r.
    eapply Rle_trans, Rmax_r.
    rewrite -{2}(Rmult_1_l (Cmod _)).
    apply Rmult_le_compat_r.
    by apply Cmod_ge_0.
    rewrite Rabs_pos_eq // -H0 Rminus_le_0 ; by ring_simplify.
  replace (y0 * b + z0 * c) with c.
  2: replace y0 with (1 - z0)%R by (rewrite -H0 ; ring).
  2: rewrite Hc Rminus_eq_0 ; ring.
  rewrite -complex_triangle_diameter_turn.
  apply (complex_triangle_diameter_corner c a b).
  exists z', x', y' ; repeat split => //.
  rewrite -H' ; ring.
  rewrite !scal_R_Cmult ; ring.
Qed.

Lemma complex_triangle_diameter_ball (a b c z0 : C) (eps : R) :
  (complex_triangle_diameter a b c < eps) ->
  (complex_triangle a b c z0) ->
  forall z, complex_triangle a b c z -> ball z0 eps z.
Proof.
  intros Heps Hz0 z Hz.
  apply (norm_compat1 (V := C_NormedModule)).
  eapply Rle_lt_trans, Heps => {Heps}.
  by apply complex_triangle_diameter_le.
Qed.

(** ** Theorem 12 *)

Lemma complex_segment_Chasles (z1 z2 z3 : C) :
  complex_segment z1 z3 z2 ->
  forall (z : C), complex_segment z1 z2 z -> complex_segment z1 z3 z.
Proof.
  intros [p2 [Hp2 ->]] _ [p [Hp ->]].
  exists (p * p2)%R ; repeat split.
  apply Rmult_le_pos, Hp2 ; apply Hp.
  rewrite -(Rmult_1_r 1).
  apply Rmult_le_compat ; intuition.
  rewrite !scal_R_Cmult !RtoC_minus RtoC_mult ; ring.
Qed.

Lemma th12 (U : C -> Prop) (z1 z2 z3 : C) (f df : C -> C) :
  open U ->
  (forall z, complex_triangle z1 z2 z3 z -> U z) ->
  (forall z, U z -> is_derive f z (df z)) ->
  C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 + C_RInt_segm f z3 z1 = 0.
Proof.
  intros oU tU Df.
  assert (If : forall a b, (forall z, complex_segment a b z -> U z) -> ex_C_RInt_segm f a b).
    intros a b Hab.
    apply ex_C_RInt_segm_continuous => z Hz.
    eapply (continuous_comp (U := C_UniformSpace) (V := AbsRing_NormedModule C_AbsRing) (fun x => x) f).
    apply continuous_C_id_1.
    apply @filterdiff_continuous.
    eexists ; apply Df.
    by apply Hab.

  set (I z1 z2 z3 := C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 + C_RInt_segm f z3 z1).
  set (I_aux i z1 z2 z3 := let w1 := (z2 + z3) / 2 in
                         let w2 := (z1 + z3) / 2 in
                         let w3 := (z1 + z2) / 2 in
                         match i with
                         | 0%nat => I z1 w3 w2
                         | 1%nat => I w3 z2 w1
                         | 2%nat => I w1 z3 w2
                         | 3%nat => I w3 w1 w2
                         | _ => 0
                         end).
  assert (HI_aux : forall z1 z2 z3, (forall z : C, complex_triangle z1 z2 z3 z -> U z) ->
                           I z1 z2 z3 = I_aux 0%nat z1 z2 z3 + I_aux 1%nat z1 z2 z3
                                        + I_aux 2%nat z1 z2 z3 + I_aux 3%nat z1 z2 z3).
    clear z1 z2 z3 tU => z1 z2 z3 tU.
    unfold I_aux.
    set (w1 := (z2 + z3) / 2) ;
    set (w2 := (z1 + z3) / 2) ;
    set (w3 := (z1 + z2) / 2).
    assert (Hw1 : complex_segment z2 z3 w1).
      unfold w1.
      exists (/2)%R ; repeat split.
      by apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      rewrite -(Rmult_1_l (/2)) ; apply Rle_div_l.
      by apply Rlt_0_2.
      apply Rminus_le_0 ; ring_simplify ; apply Rle_0_1.
      rewrite !scal_R_Cmult RtoC_minus RtoC_inv.
      2: by apply Rgt_not_eq, Rlt_0_2.
      rewrite (RtoC_plus 1 1) ; field.
      rewrite Rplus_0_l => H ; injection H.
      by apply Rgt_not_eq, Rlt_0_2.
    assert (Hw2 : complex_segment z1 z3 w2).
      unfold w2.
      exists (/2)%R ; repeat split.
      by apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      rewrite -(Rmult_1_l (/2)) ; apply Rle_div_l.
      by apply Rlt_0_2.
      apply Rminus_le_0 ; ring_simplify ; apply Rle_0_1.
      rewrite !scal_R_Cmult RtoC_minus RtoC_inv.
      2: by apply Rgt_not_eq, Rlt_0_2.
      rewrite (RtoC_plus 1 1) ; field.
      rewrite Rplus_0_l => H ; injection H.
      by apply Rgt_not_eq, Rlt_0_2.
    assert (Hw3 : complex_segment z1 z2 w3).
      unfold w3.
      exists (/2)%R ; repeat split.
      by apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      rewrite -(Rmult_1_l (/2)) ; apply Rle_div_l.
      by apply Rlt_0_2.
      apply Rminus_le_0 ; ring_simplify ; apply Rle_0_1.
      rewrite !scal_R_Cmult RtoC_minus RtoC_inv.
      2: by apply Rgt_not_eq, Rlt_0_2.
      rewrite (RtoC_plus 1 1) ; field.
      rewrite Rplus_0_l => H ; injection H.
      by apply Rgt_not_eq, Rlt_0_2.
    unfold I.
    rewrite -(C_RInt_segm_Chasles f z1 w3 z2).
    rewrite -(C_RInt_segm_Chasles f z2 w1 z3).
    rewrite -(C_RInt_segm_Chasles f z3 w2 z1).
    rewrite -(C_RInt_segm_swap f w1 w3) -(C_RInt_segm_swap f w2 w1) -(C_RInt_segm_swap f w3 w2).
    ring.
    case: (complex_segment_swap _ _ _ Hw2) => p [Hp ->].
    by exists p.
    apply If => _ [z [Hz ->]].
    apply tU.
    apply complex_triangle_turn, complex_triangle_turn.
    apply complex_segment_triangle.
    apply complex_segment_Chasles with w2.
    by apply complex_segment_swap.
    by exists z.
    apply If => _ [z [Hz ->]].
    apply tU.
    apply complex_triangle_turn, complex_triangle_turn.
    apply complex_segment_triangle, complex_segment_swap.
    apply complex_segment_Chasles with w2.
    by [].
    by apply complex_segment_swap ; exists z.
    case: Hw1 => p [Hp ->].
    by exists p.
    apply If => _ [z [Hz ->]].
    apply tU.
    apply complex_segment_triangle.
    apply complex_segment_Chasles with w1.
    by [].
    by exists z.
    apply If => _ [z [Hz ->]].
    apply tU.
    apply complex_segment_triangle, complex_segment_swap.
    apply complex_segment_Chasles with w1.
    by apply complex_segment_swap.
    by apply complex_segment_swap ; exists z.
    case: Hw3 => p [Hp ->].
    by exists p.
    apply If => _ [z [Hz ->]].
    apply tU.
    apply complex_triangle_turn.
    apply complex_segment_triangle.
    apply complex_segment_Chasles with w3.
    by [].
    by exists z.
    apply If => _ [z [Hz ->]].
    apply tU.
    apply complex_triangle_turn.
    apply complex_segment_triangle, complex_segment_swap.
    apply complex_segment_Chasles with w3.
    by apply complex_segment_swap.
    by apply complex_segment_swap ; exists z.
  set (L (z1 z2 z3 : C) := complex_triangle_perimeter z1 z2 z3).
  set (D z1 z2 z3 := complex_triangle_diameter z1 z2 z3).

  assert (HT_n : forall z1 z2 z3 : C, (forall z : C, complex_triangle z1 z2 z3 z -> U z) ->
    {y : C * C * C | let y1 := fst (fst y) in
                     let y2 := snd (fst y) in
                     let y3 := snd y in
                     (forall z : C, complex_triangle y1 y2 y3 z -> complex_triangle z1 z2 z3 z)
                     /\ Cmod (I z1 z2 z3) / 4 <= Cmod (I y1 y2 y3)
                     /\ L y1 y2 y3 = (L z1 z2 z3 / 2)%R
                     /\ D y1 y2 y3 = (D z1 z2 z3 / 2)%R}).
    clear z1 z2 z3 tU => z1 z2 z3 tU.
    - case: (Rle_lt_dec (Cmod (I z1 z2 z3) / 4) (Cmod (I_aux O z1 z2 z3))) => /= H0.
      exists (z1, ((z1 + z2) / 2), ((z1 + z3) / 2)) ; simpl ; repeat split => //.
      intros _ (a,(b,(c,(Ha,(Hb,(Hc,(Habc,->))))))).
      exists (a+b/2+c/2)%R, (b/2)%R, (c/2)%R ; repeat split.
      apply Rplus_le_le_0_compat.
      apply Rplus_le_le_0_compat => //.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      rewrite -{9}Habc ; field.
      rewrite !scal_R_Cmult.
      rewrite !RtoC_plus !RtoC_div ; try apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      rewrite Rplus_0_l => H' ; injection H' ; by apply Rgt_not_eq, Rlt_0_2.
      unfold L, complex_triangle_perimeter.
      replace (z1 - (z1 + z3) / 2)%C with ((z1 - z3) / 2).
      replace ((z1 + z2) / 2 - z1)%C with ((z2 - z1) / 2).
      replace ((z1 + z3) / 2 - (z1 + z2) / 2) with ((z3 - z2) / 2).
      rewrite !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      field.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      unfold D, complex_triangle_diameter.
      replace (z1 - (z1 + z3) / 2)%C with ((z1 - z3) / 2).
      replace ((z1 + z2) / 2 - z1)%C with ((z2 - z1) / 2).
      replace ((z1 + z3) / 2 - (z1 + z2) / 2) with ((z3 - z2) / 2).
      rewrite !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      by rewrite -!Rmax_mult ; try apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
    - case: (Rle_lt_dec (Cmod (I z1 z2 z3) / 4) (Cmod (I_aux 1%nat z1 z2 z3))) => /= H1.
      exists  (((z1 + z2) / RtoC 2), z2, ((z2 + z3) / RtoC 2)) ; simpl ; repeat split => //.
      intros _ (a,(b,(c,(Ha,(Hb,(Hc,(Habc,->))))))).
      exists (a/2)%R, (a/2 + b + c/2)%R, (c/2)%R ; repeat split.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rplus_le_le_0_compat.
      apply Rplus_le_le_0_compat => //.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      rewrite -{9}Habc ; field.
      rewrite !scal_R_Cmult !RtoC_plus !RtoC_div ; try apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      rewrite Rplus_0_l => H' ; injection H' ; by apply Rgt_not_eq, Rlt_0_2.
      unfold L, complex_triangle_perimeter.
      replace ((z1 + z2) / 2 - (z2 + z3) / 2) with ((z1 - z3) / 2).
      replace (z2 - (z1 + z2) / 2) with ((z2 - z1) / 2).
      replace ((z2 + z3) / 2 - z2) with ((z3 - z2) / 2).
      rewrite !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      field.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      unfold D, complex_triangle_diameter.
      replace ((z1 + z2) / 2 - (z2 + z3) / 2) with ((z1 - z3) / 2).
      replace (z2 - (z1 + z2) / 2) with ((z2 - z1) / 2).
      replace ((z2 + z3) / 2 - z2) with ((z3 - z2) / 2).
      rewrite !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      by rewrite -!Rmax_mult ; try apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
    - case: (Rle_lt_dec (Cmod (I z1 z2 z3) / 4) (Cmod (I_aux 2%nat z1 z2 z3))) => /= H2.
      exists (((z2 + z3) / 2), z3, ((z1 + z3) / 2))  ; simpl ; repeat split => //.
      intros _ (a,(b,(c,(Ha,(Hb,(Hc,(Habc,->))))))).
      exists (c/2)%R, (a/2)%R, (a/2+b+c/2)%R ; repeat split.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rplus_le_le_0_compat.
      apply Rplus_le_le_0_compat => //.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      rewrite -{9}Habc ; field.
      rewrite !scal_R_Cmult !RtoC_plus !RtoC_div ; try apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      rewrite Rplus_0_l => H' ; injection H' ; by apply Rgt_not_eq, Rlt_0_2.
      unfold L, complex_triangle_perimeter.
      replace ((z2 + z3) / 2 - (z1 + z3) / 2) with ((z2 - z1) / 2).
      replace (z3 - (z2 + z3) / 2) with ((z3 - z2) / 2).
      replace ((z1 + z3) / 2 - z3) with ((z1 - z3) / 2).
      rewrite !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      field.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      unfold D, complex_triangle_diameter.
      replace ((z2 + z3) / 2 - (z1 + z3) / 2) with ((z2 - z1) / 2).
      replace (z3 - (z2 + z3) / 2) with ((z3 - z2) / 2).
      replace ((z1 + z3) / 2 - z3) with ((z1 - z3) / 2).
      rewrite !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      rewrite -!Rmax_mult ; try apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      unfold Rdiv ; apply f_equal2 => //.
      rewrite Rmax_comm -Rmax_assoc.
      by rewrite Rmax_comm -Rmax_assoc.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
    - case: (Rle_lt_dec (Cmod (I z1 z2 z3) / 4) (Cmod (I_aux 3%nat z1 z2 z3))) => /= H3.
      exists (((z1 + z2) / 2), ((z2 + z3) / 2), ((z1 + z3) / 2)) ; simpl ; repeat split => //.
      intros _ (a,(b,(c,(Ha,(Hb,(Hc,(Habc,->))))))).
      exists (a / 2 + c/2)%R, (a/2 + b / 2)%R, (b/2+c/2)%R ; repeat split.
      apply Rplus_le_le_0_compat ;
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rplus_le_le_0_compat ;
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      apply Rplus_le_le_0_compat ;
      apply Rdiv_le_0_compat => // ; apply Rlt_0_2.
      rewrite -{13}Habc ; field.
      rewrite !scal_R_Cmult !RtoC_plus !RtoC_div ; try apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      rewrite Rplus_0_l => H' ; injection H' ; by apply Rgt_not_eq, Rlt_0_2.
      unfold L, complex_triangle_perimeter.
      replace ((z1 + z2) / 2 - (z1 + z3) / 2) with (-((z3 - z2) / 2)).
      replace ((z2 + z3) / 2 - (z1 + z2) / 2) with (-((z1 - z3) / 2)).
      replace ((z1 + z3) / 2 - (z2 + z3) / 2) with (-((z2 - z1) / 2)).
      rewrite !Cmod_opp !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      field.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      unfold D, complex_triangle_diameter.
      replace ((z1 + z2) / 2 - (z1 + z3) / 2) with (-((z3 - z2) / 2)).
      replace ((z2 + z3) / 2 - (z1 + z2) / 2) with (-((z1 - z3) / 2)).
      replace ((z1 + z3) / 2 - (z2 + z3) / 2) with (-((z2 - z1) / 2)).
      rewrite !Cmod_opp !Cmod_div 1?Cmod_R 1?Rabs_pos_eq.
      rewrite -!Rmax_mult ; try apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
      unfold Rdiv ; apply f_equal2 => //.
      by rewrite Rmax_comm -Rmax_assoc.
      by apply Rlt_le, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      move => H' ; injection H' ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      rewrite RtoC_plus ; field.
      move => H' ; injection H' => _ ; apply Rgt_not_eq, Rlt_0_2.
      absurd (Cmod (I z1 z2 z3) < Cmod (I z1 z2 z3)).
      by apply Rlt_irrefl.
      rewrite {1}HI_aux.
      eapply Rlt_le_trans.
      eapply Rle_lt_trans.
      apply Cmod_triangle.
      apply Rplus_lt_compat, H3.
      eapply Rle_lt_trans.
      apply Cmod_triangle.
      apply Rplus_lt_compat, H2.
      eapply Rle_lt_trans.
      apply Cmod_triangle.
      apply Rplus_lt_compat, H1.
      apply H0.
      apply Req_le ; field.
      by apply tU.
  set (t := {z : C * C * C | forall y : C, complex_triangle (fst (fst z)) (snd (fst z)) (snd z) y -> U y}).
  set (T_0 (z : t) := proj1_sig (HT_n (fst (fst (proj1_sig z))) (snd (fst (proj1_sig z))) (snd (proj1_sig z)) (proj2_sig z))).
  assert (HT_0 : forall z, (forall y : C, complex_triangle (fst (fst (T_0 z))) (snd (fst (T_0 z))) (snd (T_0 z)) y -> U y)).
    intros (((y1,y2),y3),H) y ; unfold T_0 ; simpl.
    destruct (HT_n y1 y2 y3 _) ; simpl.
    case: x a => [[x1 x2] x3] /= Hx.
    intros Hy.
    by apply H, Hx.
  set (T_1 := fix f n := match n with | O => exist _ (z1,z2,z3) tU : t
                                    | S n => exist _ (T_0 (f n)) (HT_0 (f n)) : t end).
  set (T_n n := proj1_sig (T_1 n)).
  assert (LT : forall n, let y1 := fst (fst (T_n n)) in
                         let y2 := snd (fst (T_n n)) in
                         let y3 := snd (T_n n) in
                         L y1 y2 y3 = (L z1 z2 z3 / 2 ^ n)%R).
    rewrite /T_n /=.
    induction n ; simpl.
    by rewrite Rdiv_1.
    rewrite (proj1 (proj2 (proj2 (proj2_sig (HT_n _ _ _ _))))).
    move: IHn.
    destruct (T_1 n) as [[[y1 y2] y3] Hy] ; simpl.
    move => /= -> ; field.
    apply pow_nonzero, Rgt_not_eq, Rlt_0_2.
  assert (DT : forall n, let y1 := fst (fst (T_n n)) in
                         let y2 := snd (fst (T_n n)) in
                         let y3 := snd (T_n n) in
                         D y1 y2 y3 = (D z1 z2 z3 / 2 ^ n)%R).
    rewrite /T_n /=.
    induction n ; simpl.
    by rewrite Rdiv_1.
    rewrite (proj2 (proj2 (proj2 (proj2_sig (HT_n _ _ _ _))))).
    move: IHn.
    destruct (T_1 n) as [[[y1 y2] y3] Hy] ; simpl.
    move => /= -> ; field.
    apply pow_nonzero, Rgt_not_eq, Rlt_0_2.
  assert (IT : forall n, let y1 := fst (fst (T_n n)) in
                         let y2 := snd (fst (T_n n)) in
                         let y3 := snd (T_n n) in
                         Cmod (I z1 z2 z3) / 4 ^ n <= Cmod (I y1 y2 y3)).
    rewrite /T_n /=.
    induction n ; simpl.
    by rewrite Rdiv_1 ; apply Rle_refl.
    eapply Rle_trans, (proj1 (proj2 (proj2_sig (HT_n _ _ _ _)))).
    move: IHn.
    destruct (T_1 n) as [[[y1 y2] y3] Hy] ; simpl => H.
    apply Rmult_le_reg_l with 4.
    apply Rmult_lt_0_compat ; apply Rlt_0_2.
    replace (4 * (Cmod (I y1 y2 y3) / 4))%R with (Cmod (I y1 y2 y3)) by field.
    eapply Rle_trans, H.
    apply Req_le ; field.
    apply pow_nonzero, Rgt_not_eq, Rmult_lt_0_compat ;
    apply Rlt_0_2.
  assert (segmT : forall n, let y1 := fst (fst (T_n n)) in
                            let y2 := snd (fst (T_n n)) in
                            let y3 := snd (T_n n) in
                            forall z, complex_triangle y1 y2 y3 z -> U z).
    rewrite /T_n /= => n.
    apply (proj2_sig (T_1 n)).

  assert (exists z : C, forall n, let y1 := fst (fst (T_n n)) in
                                  let y2 := snd (fst (T_n n)) in
                                  let y3 := snd (T_n n) in
                                  complex_triangle y1 y2 y3 z).
  admit.

  case: H => z0 Hz0.
  set (g z := f z - (f z0 + (z - z0) * df z0)).
  assert (Hg : forall z1 z2 z3, (forall z : C, complex_triangle z1 z2 z3 z -> U z)
              -> C_RInt_segm g z1 z2 + C_RInt_segm g z2 z3 + C_RInt_segm g z3 z1 = I z1 z2 z3).
    clear -If => z1 z2 z3 tU.
    rewrite /I /g.
    assert (forall z : C, continuous (fun z => f z0 + (z - z0) * df z0) z).
      intros z.
      apply @continuous_plus.
      apply continuous_const.
      apply @continuous_scal.
      apply (continuous_minus (U := C_UniformSpace) (V := AbsRing_NormedModule C_AbsRing) (fun y => y) (fun _ => z0)).
      apply continuous_C_id_1.
      apply continuous_const.
      apply continuous_const.
    assert (forall z, is_derive (fun z => z * f z0 + (z - z0) * (z - z0) * df z0 / 2) z (f z0 + (z - z0) * df z0)).
      intros z.
      evar_last.
      apply @is_derive_plus.
      apply @is_derive_scal.

    rewrite !C_RInt_segm_minus.
    Search C_RInt_segm.
    admit. (* Corolaire 7 *)
  assert (Dg : forall z, U z -> is_derive g z (df z - df z0)).
    intros z Hz.
    unfold g.
    evar_last.
    apply @is_derive_minus.
    by apply Df.
    apply @is_derive_plus.
    apply is_derive_const.
    apply @is_derive_scal_l.
    apply @is_derive_minus.
    apply is_derive_id.
    apply is_derive_const.
    change plus with Cplus ;
    change minus with Cminus ;
    change zero with (RtoC 0) ;
    change scal with Cmult ;
    change one with (RtoC 1).
    ring.
Admitted.




























