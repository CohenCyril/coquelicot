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
Require Import Rbar Rcomplements Locally.

(** * Definitions of equivalent and dominant *)

Definition is_domin {T} (F : (T -> Prop) -> Prop) (f g : T -> R) :=
  forall eps : posreal, F (fun x => Rabs (g x) <= eps * Rabs (f x)).
Definition is_equiv {T} (F : (T -> Prop) -> Prop) (f g : T -> R) :=
  is_domin F g (fun x => g x - f x).

(** To be dominant is a partial strict order *)
Lemma domin_antisym :
  forall {T} {F : (T -> Prop) -> Prop} {FF : ProperFilter F} (f : T -> R),
  F (fun x => f x <> 0) -> ~ is_domin F f f.
Proof.
  intros T F FF f Hf H.
  move: (H (pos_div_2 (mkposreal _ Rlt_0_1))) => {H} /= H.
  have H0 : F (fun x => ~ (Rabs (f x) <= 1/2 * Rabs (f x))).
    move: Hf ; apply filter_imp.
    intros x Hf ; apply Rlt_not_le.
    apply Rminus_lt ; field_simplify ;
    rewrite Rdiv_1 /Rdiv Ropp_mult_distr_l_reverse ;
    apply Ropp_lt_gt_0_contravar, Rdiv_lt_0_compat.
    by apply Rabs_pos_lt.
    by apply Rlt_R0_R2.
  apply filter_const.
  generalize (filter_and _ _ H H0) => {H H0}.
  now apply filter_imp.
Qed.

Lemma domin_trans :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R),
  is_domin F f g -> is_domin F g h -> is_domin F f h.
Proof.
  intros T F FF f g h Hfg Hgh eps.
  apply (filter_imp (fun x => (Rabs (h x) <= sqrt eps * Rabs (g x)) /\ (Rabs (g x) <= sqrt eps * Rabs (f x)))).
  intros x [H0 H1].
  apply Rle_trans with (1 := H0).
  rewrite -{2}(sqrt_sqrt eps).
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  by apply sqrt_pos.
  apply H1.
  by apply Rlt_le, eps.
  apply filter_and.
  by apply (Hgh (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
  by apply (Hfg (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
Qed.

(** Relations between domination and equivalence *)

Lemma domin_rw_l :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g : T -> R),
  is_equiv F f1 f2 -> (is_domin F f1 g <-> is_domin F f2 g).
Proof.
  intros T F FF f1 f2 g Hf.
  split => Hfg.
(* Cas facile *)
  have : forall eps : posreal, F (fun x => Rabs (f1 x) <= (eps + 1) * Rabs (f2 x)).
    move => eps.
    move: (Hf eps) => {Hf}.
    apply filter_imp => x Hf.
    rewrite Rmult_plus_distr_r Rmult_1_l.
    replace (Rabs (f1 x)) with ((Rabs (f1 x) - Rabs (f2 x)) + Rabs (f2 x)) by ring.
    apply Rplus_le_compat_r.
    apply Rle_trans with (2 := Hf).
    rewrite -(Rabs_Ropp (_-_)) Ropp_minus_distr'.
    by apply Rabs_triang_inv.
  move => {Hf} Hf eps.
  move: (Hf (mkposreal _ Rlt_0_1)) (Hfg (pos_div_2 eps)) => /= {Hf Hfg} Hf Hfg.
  generalize (filter_and _ _ Hf Hfg) => {Hf Hfg}.
  apply filter_imp.
  intros x [Hf Hfg].
  apply Rle_trans with (1 := Hfg).
  pattern (pos eps) at 2 ;
  replace (pos eps) with ((eps/2)*2) by field.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  apply Rlt_le, is_pos_div_2.
  by apply Hf.
(* Cas compliqué *)
  have : forall eps : posreal, F (fun x => (1-eps) * Rabs (f2 x) <= Rabs (f1 x)).
    move => eps.
    move: (Hf eps) => {Hf}.
    apply filter_imp => x Hf.
    rewrite Rmult_minus_distr_r Rmult_1_l.
    replace (Rabs (f1 x)) with (Rabs (f2 x) - (Rabs (f2 x) - Rabs (f1 x))) by ring.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    apply Rle_trans with (2 := Hf).
    by apply Rabs_triang_inv.
  move => {Hf} Hf eps.
  move: (Hf (pos_div_2 (mkposreal _ Rlt_0_1))) (Hfg (pos_div_2 eps)) => /= {Hf Hfg} Hf Hfg.
  generalize (filter_and _ _ Hf Hfg) => {Hf Hfg}.
  apply filter_imp.
  intros x [Hf Hfg].
  replace (1 - 1 / 2) with (/2) in Hf by field.
  apply Rle_trans with (1 := Hfg).
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  by apply Hf.
Qed.

Lemma equiv_sym :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R),
  is_equiv F f g -> is_equiv F g f.
Proof.
  intros T F FF f g H.
  apply (domin_rw_l _ _ (fun x => f x - g x) H).
  move => eps ; move: (H eps).
  apply filter_imp => x Hx.
  by rewrite -Rabs_Ropp Ropp_minus_distr'.
Qed.

Lemma domin_rw_r :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g1 g2 : T -> R),
  is_equiv F g1 g2 -> (is_domin F f g1 <-> is_domin F f g2).
Proof.
  intros T F FF f g1 g2.
  assert (forall g1 g2,  is_equiv F g1 g2 -> is_domin F f g2 -> is_domin F f g1).
  clear g1 g2; intros g1 g2 Hg Hf eps.
  rewrite /is_equiv in Hg.
  rewrite /is_domin in Hg Hf.
  specialize (Hg (mkposreal _ Rlt_0_1)); simpl in Hg.
  specialize (Hf (pos_div_2 eps)).
  generalize (filter_and _ _ Hf Hg).
  apply filter_imp.
  intros x [H2 H1].
  replace (g1 x) with (-(g2 x - g1 x) + g2 x) by ring.
  apply Rle_trans with (1:=Rabs_triang _ _).
  rewrite Rabs_Ropp.
  apply Rle_trans with (1 * Rabs (g2 x)+ Rabs (g2 x)).
  now apply Rplus_le_compat_r.
  apply Rle_trans with (2*Rabs (g2 x));[right; ring|idtac].
  apply Rle_trans with (2*(pos_div_2 eps * Rabs (f x))).
  apply Rmult_le_compat_l.
  left; apply Rlt_0_2.
  apply H2.
  right; unfold pos_div_2; simpl; field.
  intros H'; split.
  apply H.
  now apply equiv_sym.
  now apply H.
Qed.

(** To be equivalent is an equivalence relation *)

Lemma equiv_refl :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> R),
  is_equiv F f f.
Proof.
  intros T F FF f eps.
  apply: filter_forall => x.
  rewrite Rminus_eq_0 Rabs_R0.
  apply Rmult_le_pos.
  by apply Rlt_le, eps.
  by apply Rabs_pos.
Qed.

Lemma equiv_trans :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R),
  is_equiv F f g -> is_equiv F g h -> is_equiv F f h.
Proof.
  intros T F FF f g h Hfg Hgh.
  apply (fun c => domin_rw_l _ _ c Hgh).
  intros eps.
  apply equiv_sym in Hgh.
  generalize (filter_and _ _ (Hfg (pos_div_2 eps)) (Hgh (pos_div_2 eps))) => {Hfg Hgh}.
  apply filter_imp => x /= [Hfg Hgh].
  replace (h x - f x) with ((g x - f x) - (g x - h x)) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps) Rmult_plus_distr_r.
  by apply Rplus_le_compat.
Qed.

Lemma equiv_carac_0 :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R),
  is_equiv F f g ->
  {o : T -> R | (forall x : T, f x = g x + o x) /\ is_domin F g o }.
Proof.
  intros T F FF f g H.
  exists (fun x => f x - g x).
  split.
  intro x ; ring.
  apply (domin_rw_l _ _ _ H).
  by apply equiv_sym.
Qed.

Lemma equiv_carac_1 :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g o : T -> R),
  (forall x, f x = g x + o x) -> is_domin F g o -> is_equiv F f g.
Proof.
  intros T F FF f g o Ho Hgo.
  intro eps ; move: (Hgo eps).
  apply filter_imp => x.
  replace (o x) with (f x - g x).
  by rewrite -(Rabs_Ropp (f x - g x)) Ropp_minus_distr'.
  rewrite Ho ; ring.
Qed.

(** * Vector space *)
(** is_domin is a vector space *)

Lemma domin_scal_r :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R) (c : R),
  is_domin F f g -> is_domin F f (fun x => c * g x).
Proof.
  intros T F FF f g c H.
  wlog: c / (0 < c) => [Hw  {H} | Hc].
    case: (Rlt_le_dec 0 c) => Hc.
    by apply Hw.
    case: Hc => Hc.
    apply Ropp_0_gt_lt_contravar in Hc.
    move: (Hw _ Hc) => {Hw} H eps ; move: (H eps).
    apply filter_imp => x.
    by rewrite Ropp_mult_distr_l_reverse Rabs_Ropp.
    rewrite Hc => {c Hc Hw} eps.
    apply: filter_forall => x.
    rewrite Rmult_0_l Rabs_R0.
    apply Rmult_le_pos.
    by apply Rlt_le, eps.
    by apply Rabs_pos.
  move => eps /=.
  have He : 0 < eps / c.
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply Hc.
  move: (H (mkposreal _ He)) => /= {H}.
  apply filter_imp => x H.
  rewrite Rabs_mult (Rabs_right c).
  replace (eps * Rabs (f x)) with (c*(eps / c * Rabs (f x))).
  apply Rmult_le_compat_l.
  by apply Rlt_le, Hc.
  by apply H.
  field ; by apply Rgt_not_eq.
  by apply Rle_ge, Rlt_le.
Qed.

Lemma domin_scal_l :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R) (c : R),
  c <> 0 -> is_domin F f g -> is_domin F (fun x => c * f x) g.
Proof.
  intros T F FF f g c Hc H eps.
  have He : (0 < eps * Rabs c).
    apply Rmult_lt_0_compat.
    by apply eps.
    by apply Rabs_pos_lt.
  move: (H (mkposreal _ He)) => /= {H}.
  apply filter_imp => x Hx.
  by rewrite Rabs_mult -Rmult_assoc.
Qed.

Lemma domin_plus :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g1 g2 : T -> R),
  is_domin F f g1 -> is_domin F f g2 -> is_domin F f (fun x => g1 x + g2 x).
Proof.
  intros T F FF f g1 g2 Hg1 Hg2 eps.
  generalize (filter_and _ _ (Hg1 (pos_div_2 eps)) (Hg2 (pos_div_2 eps))) 
    => /= {Hg1 Hg2}.
  apply filter_imp => x [Hg1 Hg2].
  apply Rle_trans with (1 := Rabs_triang _ _).
  replace (eps * Rabs (f x)) 
    with (eps / 2 * Rabs (f x) + eps / 2 * Rabs (f x))
    by field.
  by apply Rplus_le_compat.
Qed.

(** is_equiv is compatible with the vector space structure *)

Lemma equiv_scal :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R) (c : R),
  is_equiv F f g -> is_equiv F (fun x => c * f x) (fun x => c * g x).
Proof.
  intros T F FF f g c.
  case: (Req_dec c 0) ; move => Hc H.
(* c = 0 *)
  rewrite Hc => {c Hc}.
  move => eps /= ; apply: filter_forall => x.
  rewrite ?Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r.
  apply Rle_refl.
(* c <> 0 *)
  apply domin_scal_l.
  by apply Hc.
  move => eps /=.
  have : F (fun x => Rabs (c * (g x - f x)) <= eps * Rabs (g x)).
  apply (domin_scal_r g (fun x => g x - f x) c).
  by apply H.
  apply filter_imp => x.
  by rewrite Rmult_minus_distr_l.
Qed.

Lemma equiv_plus :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f o : T -> R),
  is_domin F f o -> is_equiv F (fun x => f x + o x) f.
Proof.
  intros T F FF f o H eps.
  move: (H eps) => {H}.
  apply filter_imp => x Hx.
  ring_simplify (f x - (f x + o x)).
  by rewrite Rabs_Ropp.
Qed.

(** * Multiplication and inverse *)
(** Domination *)

Lemma domin_mult_r :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R),
  is_domin F f g -> is_domin F (fun x => f x * h x) (fun x => g x * h x).
Proof.
  intros T F FF f g h H eps.
  move: (H eps) => {H}.
  apply filter_imp => x H1.
  rewrite ?Rabs_mult.
  rewrite -Rmult_assoc.
  apply Rmult_le_compat_r.
  by apply Rabs_pos.
  by apply H1.
Qed.

Lemma domin_mult_l :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g h : T -> R),
  is_domin F f g -> is_domin F (fun x => h x * f x) (fun x => h x * g x).
Proof.
  intros T F FF f g h H eps.
  generalize (domin_mult_r f g h H eps).
  apply filter_imp => x.
  by rewrite ?(Rmult_comm (h x)).
Qed.

Lemma domin_mult :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g1 g2 : T -> R),
  is_domin F f1 g1 -> is_domin F f2 g2 ->
  is_domin F (fun x => f1 x * f2 x) (fun x => g1 x * g2 x).
Proof.
  intros T F FF f1 f2 g1 g2 H1 H2 eps.
  move: (H1 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps))))
    (H2 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps)))) => {H1 H2} /= H1 H2.
  generalize (filter_and _ _ H1 H2) => {H1 H2}.
  apply filter_imp => x [H1 H2].
  rewrite ?Rabs_mult.
  rewrite -(sqrt_sqrt _ (Rlt_le _ _ (cond_pos eps))).
  replace (sqrt eps * sqrt eps * (Rabs (f1 x) * Rabs (f2 x))) 
    with ((sqrt eps * Rabs (f1 x))*(sqrt eps * Rabs (f2 x))) by ring.
  apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  by apply H1.
  by apply H2.
Qed.

Lemma domin_inv :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R),
  F (fun x => g x <> 0) -> is_domin F f g ->
  is_domin F (fun x => / g x) (fun x => / f x).
Proof.
  intros T F FF f g Hg H eps.
  have Hf : F (fun x => f x <> 0).
    generalize (filter_and _ _ Hg (H (mkposreal _ Rlt_0_1))) => /=.
    apply filter_imp => x {Hg H} [Hg H].
    case: (Req_dec (f x) 0) => Hf.
    rewrite Hf Rabs_R0 Rmult_0_r in H.
    apply Rlt_not_le in H.
    move => _ ; apply H.
    by apply Rabs_pos_lt.
    by [].
  generalize (filter_and _ _ (H eps) (filter_and _ _ Hf Hg)) => {H Hf Hg}.
  apply filter_imp => x [H [Hf Hg]].
  rewrite ?Rabs_Rinv => //.
  replace (/ Rabs (f x)) 
    with (Rabs (g x) / (Rabs (f x) * Rabs (g x)))
    by (field ; split ; by apply Rabs_no_R0).
  replace (eps * / Rabs (g x))
    with (eps * Rabs (f x) / (Rabs (f x) * Rabs (g x)))
    by (field ; split ; by apply Rabs_no_R0).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat ; apply Rabs_pos_lt => //.
  by apply H.
Qed.

(** Equivalence *)

Lemma equiv_mult :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g1 g2 : T -> R),
  is_equiv F f1 g1 -> is_equiv F f2 g2 ->
  is_equiv F (fun x => f1 x * f2 x) (fun x => g1 x * g2 x).
Proof.
  intros T F FF f1 f2 g1 g2 H1 H2.
  case: (equiv_carac_0 _ _ H1) => {H1} o1 [H1 Ho1].
  case: (equiv_carac_0 _ _ H2) => {H2} o2 [H2 Ho2].
  apply equiv_carac_1 with (fun x => o1 x * g2 x + g1 x * o2 x + o1 x * o2 x).
  move => x ; rewrite H1 H2 ; ring.
  apply domin_plus.
  apply domin_plus.
  by apply domin_mult_r.
  by apply domin_mult_l.
  by apply domin_mult.
Qed.

Lemma equiv_inv :
  forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f g : T -> R),
  F (fun x => g x <> 0) -> is_equiv F f g ->
  is_equiv F (fun x => / f x) (fun x => / g x).
Proof.
  intros T F FF f g Hg H.
  have Hf : F (fun x => f x <> 0).
    generalize (filter_and _ _ Hg (H (pos_div_2 (mkposreal _ Rlt_0_1)))) => /=.
    apply filter_imp => x {Hg H} [Hg H].
    case: (Req_dec (f x) 0) => Hf.
    rewrite Hf Rminus_0_r in H.
    apply Rle_not_lt in H.
    move => _ ; apply H.
    apply Rminus_lt ; field_simplify ; rewrite Rdiv_1 /Rdiv Ropp_mult_distr_l_reverse ; 
    apply Ropp_lt_gt_0_contravar.
    apply Rmult_lt_0_compat.
    by apply Rabs_pos_lt.
    by intuition.
    by[].
  apply equiv_sym in H.
  move => eps.
  generalize (filter_and _ _ (filter_and _ _ Hf Hg) (H eps)).
  clear -FF.
  apply filter_imp.
  intros x [[Hf Hg] H].
  replace (/ g x - / f x) 
    with ((f x - g x) / (f x * g x)).
  rewrite Rabs_div ?Rabs_Rinv ?Rabs_mult //.
  apply Rle_div_l.
  apply Rmult_lt_0_compat ; by apply Rabs_pos_lt.
  field_simplify ; rewrite ?Rdiv_1.
  by [].
  by apply Rabs_no_R0.
  by apply Rmult_integral_contrapositive_currified.
  field ; by split.
Qed.
