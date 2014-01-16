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

Require Import Reals Even Div2 ssreflect.
Require Import Rcomplements Rbar Limit Lub.
Require Import Continuity Derive Derive_2d RInt Seq_fct Series Hierarchy.

(** pow *)

Section pow_n.

Context {K : AbsRing}.

Fixpoint pow_n (x : K) (N : nat) {struct N} : K :=
  match N with
   | 0%nat => one
   | S i => mult x (pow_n x i)
  end.

Lemma pow_n_plus :
  forall (x : K) (n m : nat), pow_n x (n+m) = mult (pow_n x n) (pow_n x m).
Proof.
  intros x.
  elim => /= [ | n IH] m.
  by rewrite mult_one_l.
  by rewrite IH mult_assoc.
Qed.

Lemma pow_n_comm_1 :
  forall (x : K) (n : nat), mult (pow_n x n) x = mult x (pow_n x n).
Proof.
  intros x n.
  elim: n => /= [ | n IH].
  by rewrite mult_one_l mult_one_r.
  by rewrite -(mult_assoc _ (pow_n x n)) IH.
Qed.

Lemma pow_n_comm :
  forall (x : K) n m, mult (pow_n x n) (pow_n x m) = mult (pow_n x m) (pow_n x n).
Proof.
  intros x n m.
  rewrite -2!pow_n_plus.
  by apply f_equal, Plus.plus_comm.
Qed. 

Lemma abs_pow_n :
  forall (x : K) n,
  abs (pow_n x n) <= (abs x)^n.
Proof.
induction n.
apply Req_le, abs_one.
simpl.
apply: Rle_trans (abs_mult _ _) _.
apply Rmult_le_compat_l with (2 := IHn).
apply abs_ge_0.
Qed.

End pow_n.

Lemma pow_n_pow :
  forall (x : R) k, pow_n x k = x^k.
Proof.
intros x; induction k; simpl.
easy.
now rewrite IHk.
Qed.

(** * Definition *)

Section Definitions.

Context {K : AbsRing} {V : NormedModule K}.

Definition is_pseries (a : nat -> V) (x:K) (l : V) :=
  is_series (fun k => scal (pow_n x k) (a k)) l.

Definition ex_pseries (a : nat -> V) (x : K) :=
  ex_series (fun k => scal (pow_n x k) (a k)).

End Definitions.

Definition PSeries (a : nat -> R) (x : R) : R :=
  Series (fun k => a k * x ^ k).

Lemma ex_pseries_dec {V : NormedModule R_AbsRing} (a : nat -> R) (x : R) :
  {ex_pseries a x} + {~ ex_pseries a x}.
Proof.
  apply ex_series_dec.
Qed.

Lemma is_pseries_R (a : nat -> R) (x l : R) :
  is_pseries a x l <-> is_series (fun n : nat => a n * x ^ n) l.
Proof.
  split ; apply is_series_ext ;
  intros n ; rewrite pow_n_pow /= ; apply Rmult_comm.
Qed.

Lemma ex_pseries_R (a : nat -> R) (x : R) :
  ex_pseries a x <-> ex_series (fun n : nat => a n * x ^ n).
Proof.
  split ; apply ex_series_ext ;
  intros n ; rewrite pow_n_pow /= ; apply Rmult_comm.
Qed.

Lemma PSeries_eq (a : nat -> R) (x : R) : 
  PSeries a x = Series (fun k => scal (pow_n x k) (a k)).
Proof.
  apply Series_ext.
  intros n.
  apply Rmult_comm.
Qed.

Lemma is_pseries_unique (a : nat -> R) (x l : R) :
  is_pseries a x l -> PSeries a x = l.
Proof.
  move => Ha; rewrite PSeries_eq.
  by apply is_series_unique.
Qed.
Lemma PSeries_correct (a : nat -> R) (x : R) :
  ex_pseries a x -> is_pseries a x (PSeries a x).
Proof.
  move => Ha; rewrite PSeries_eq.
  apply Series_correct.
  by apply Ha.
Qed.

(** Equivalence with standard library Reals *)

Lemma is_pseries_Reals (a : nat -> R) (x l : R) :
  is_pseries a x l <-> Pser a x l.
Proof.
  split => H.
  move => e He ; set eps := mkposreal e He.
  apply (is_lim_seq_spec _ l) in H.
  case: (H eps) => {H} N H.
  exists N => n Hn.
  rewrite <- sum_n_sum_f_R0.
  rewrite (sum_n_ext _ (fun n0 : nat => scal (pow_n x n0) (a n0))).
  by apply H.
  intros k; rewrite pow_n_pow /=; apply Rmult_comm.
  apply (is_lim_seq_spec _ l).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  rewrite (sum_n_ext _ (fun n0 : nat => a n0 * x ^ n0)).
  rewrite sum_n_sum_f_R0.  
  by apply H.
  intros; now rewrite Rmult_comm pow_n_pow.
Qed.

(** Extensionality *)

Section Extensionality.

Context {K : AbsRing} {V : NormedModule K}.

Lemma is_pseries_ext (a b : nat -> V) (x : K) (l:V) :
  (forall n, a n = b n) -> (is_pseries a x l)
    -> is_pseries b x l.
Proof.
  move => Heq Ha.
  apply is_series_ext with (2 := Ha).
  move => n.
  by rewrite Heq.
Qed.

Lemma ex_pseries_ext (a b : nat -> V) (x : K) :
  (forall n, a n = b n) -> ex_pseries a x
    -> ex_pseries b x.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_pseries_ext with a.
Qed.

End Extensionality.

Lemma PSeries_ext (a b : nat -> R) (x : R) :
  (forall n, a n = b n) -> PSeries a x = PSeries b x.
Proof.
  move => Heq.
  apply Series_ext.
  move => n ;
  by rewrite Heq.
Qed.

(** * Convergence circle *)
(** A power series is always defined at 0 *)

Section ConvergenceCircle.

Context {K : AbsRing} {V : NormedModule K}.

Lemma is_pseries_0 (a : nat -> V) :
  is_pseries a zero (a O).
Proof.
  apply filterlim_ext with (fun _ => a O).
  elim => [ | n IH] /=.
  now rewrite scal_one.
  rewrite -IH.
  rewrite mult_zero_l.
  now rewrite scal_zero_l plus_zero_r.
  apply filterlim_const.
Qed.

Lemma ex_pseries_0 (a : nat -> V) :
  ex_pseries a zero.
Proof.
  exists (a O) ; by apply is_pseries_0.
Qed.

End ConvergenceCircle.

Lemma PSeries_0 (a : nat -> R) :
  PSeries a 0 = a O.
Proof.
  rewrite PSeries_eq.
  apply is_series_unique.
  apply @is_pseries_0.
Qed.

(** Convergence disk *)
Definition CV_disk (a : nat -> R) (r : R) :=
  ex_series (fun n => Rabs (a n * r^n)).

Lemma CV_disk_le (a : nat -> R) (r1 r2 : R) :
  Rabs r1 <= Rabs r2 -> CV_disk a r2 -> CV_disk a r1.
Proof.
  move => H.
  apply Comp_ex_series => n ; split.
  rewrite Rabs_mult ; apply Rmult_le_pos ; by apply Rabs_pos.
  rewrite ?Rabs_mult ; apply Rmult_le_compat_l.
  by apply Rabs_pos.
  rewrite -?RPow_abs ; apply pow_incr ; split.
  by apply Rabs_pos.
  by apply H.
Qed.
Lemma CV_disk_correct (a : nat -> R) (x : R) :
  CV_disk a x -> ex_pseries a x.
Proof.
  intros H; apply ex_series_Rabs.
  apply ex_series_ext with (2:=H).
  intros n; apply f_equal.
  now rewrite Rmult_comm pow_n_pow.
Qed.

Lemma CV_disk_0 (a : nat -> R) :
  CV_disk a 0.
Proof.
  exists (Rabs (a O)).
  apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a O))).
  elim => /= [ | n IH].
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
  by apply is_lim_seq_const.
Qed.

Definition CV_radius (a : nat -> R) : Rbar :=
  Lub_Rbar_ne (CV_disk a) (ex_intro _ 0 (CV_disk_0 _)).

Lemma CV_radius_ge_0 (a : nat -> R) :
  Rbar_le (Finite 0) (CV_radius a).
Proof.
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => /= l Hl.
  apply Hl, CV_disk_0.
Qed.

Lemma CV_radius_bounded (a : nat -> R) :
  is_lub_Rbar (fun r => exists M, forall n, Rabs (a n * r ^ n) <= M) (CV_radius a).
Proof.
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => cv /= [ub lub].
  split.

  move => r /= [M Hr].

  have : forall y, Rabs y < Rabs r -> (CV_disk a) y.
    move => y Hy ; rewrite /CV_disk /=.
  set l := (Rabs (y / r)).
  assert (ex_series (fun n => M * l ^ n)).
  apply ex_series_ext with (fun n : nat => scal M (l ^ n)).
    by elim.
  apply: ex_series_scal_l.
  apply ex_series_geom.
  rewrite /l Rabs_Rabsolu Rabs_div.
  apply Rlt_div_l.
  apply Rle_lt_trans with (2 := Hy), Rabs_pos.
  by rewrite Rmult_1_l.
  have H : (Rabs r <> 0).
  apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
  contradict H.
  by rewrite H Rabs_R0.
  apply Comp_ex_series with (2:=H) => n.
  split.
  by apply Rabs_pos.
  replace (Rabs (a n * y ^ n)) with (Rabs (a n * r ^ n) * l^n).
  apply Rmult_le_compat_r.
  apply pow_le ; by apply Rabs_pos.
  by apply Hr.
  rewrite ?Rabs_mult Rmult_assoc ; apply Rmult_eq_compat_l.

  rewrite /l RPow_abs -Rabs_mult.
  apply f_equal.
  elim: n  => /= [ | n IH].
  ring.
  rewrite -IH ; field.
  have Hr0 : Rabs r <> 0.
    apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
  contradict Hr0 ; by rewrite Hr0 Rabs_R0.

  move => H.

  have : forall y, Rabs y < Rabs r -> Rbar_le (Finite (y)) cv.
  move => y Hy.
  apply ub.
  by apply (H y Hy).

  have Hc0 : Rbar_le (Finite 0) cv.
  apply ub, CV_disk_0.
  case: (cv) Hc0 => [c | | ] // Hc0 Hcv.

  case: (Rle_lt_dec r 0) => Hr0.
  by apply Rle_trans with (1 := Hr0).

  have H0 : forall e, 0 < e <= r -> r - e <= c.
    intros.
    apply Hcv.
    apply Rlt_le_trans with (2 := Rle_abs _).
    rewrite Rabs_pos_eq.
    rewrite -(Rplus_0_r (r - e)).
    pattern r at 2 ; replace r with ((r-e)+e) by ring.
    apply Rplus_lt_compat_l, H0.
    rewrite -Rminus_le_0 ; by apply H0.

  apply Rnot_lt_le => H1.
  have H2: (c < ((c+r)/2) < r).
    pattern r at 3 ; replace r with ((r+r)/2) by field.
    pattern c at 1 ; replace c with ((c+c)/2) by field.
    split ; apply Rmult_lt_compat_r ; by intuition.
  have H3 : 0 < ((r-c)/2) <= r.
  split.
  apply Rdiv_lt_0_compat.
  by apply -> Rminus_lt_0.
  by apply Rlt_R0_R2.
  pattern r at 2 ; replace r with ((r+r)/2) by field.
  apply Rmult_le_compat_r ; intuition.
  apply Rplus_le_compat_l.
  apply Rle_trans with 0.
  rewrite -(Rminus_eq_0 c).
  rewrite -(Rplus_0_l (-c)).
  by apply Rplus_le_compat_r.
  by apply Rlt_le.
  move: (H0 _ H3).
  apply Rlt_not_le.
  rewrite -{1}(Rdiv_1 r).
  rewrite Rdiv_minus ; try by [intuition | apply Rgt_not_eq ; intuition].
  ring_simplify (r * 2 - (r - c) * 1) ; rewrite Rmult_1_l.
  rewrite Rplus_comm ; by apply H2.

(* lub *)
  move => b Hb.
  apply lub => x Hx.
  apply Hb.
  apply ex_series_lim_0 in Hx.
  apply is_lim_seq_spec in Hx.
  case: (Hx (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.

  set M := fix f N := match N with
    | O => Rabs (a O * x ^ O)
    | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
  exists (Rmax (M N) 1) => n.
  case: (le_lt_dec N n) => Hn.
  apply Rle_trans with (2 := Rmax_r _ _).
  move: (Hx n Hn).
  rewrite Rminus_0_r Rabs_Rabsolu.
  by apply Rlt_le.
  apply Rle_trans with (2 := Rmax_l _ _).
  elim: N n Hn {Hx} => [ | N IH] /= n Hn.
  by apply lt_n_O in Hn.
  apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
  apply Rle_trans with (2 := Rmax_l _ _).
  by apply IH.
  rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
Qed.

(** Convergence theorems *)

Lemma CV_disk_inside (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> ex_series (fun n => Rabs (a n * x ^ n)).
Proof.
  move => Ha.
  assert (H : ~ ~ ex_series (fun n => Rabs (a n * x ^ n))).
    contradict Ha.
    apply Rbar_le_not_lt.
    rewrite /CV_radius /Lub_Rbar_ne ;
    case: ex_lub_Rbar_ne => l /= [ub lub].
    apply: lub => r Hr.
    apply Rnot_lt_le ; contradict Ha.
    move: Hr.
    apply CV_disk_le.
    by apply Rlt_le, Rlt_le_trans with (2 := Rle_abs _).
  by case: (ex_series_dec (fun n => Rabs (a n * x ^ n))).
Qed.
Lemma CV_radius_inside (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> ex_pseries a x.
Proof.
  move => Ha.
  by apply CV_disk_correct, CV_disk_inside.
Qed.

Lemma CV_disk_outside (a : nat -> R) (x : R) :
  Rbar_lt (CV_radius a) (Finite (Rabs x))
    -> ~ is_lim_seq (fun n => a n * x ^ n) 0.
Proof.
  case: (CV_radius_bounded a) => ub lub.
  move => Hx.
  have H : ~ (fun r : R => exists M : R, forall n : nat, Rabs (a n * r ^ n) <= M) x.
    contradict Hx ; apply Rbar_le_not_lt.
    apply ub.
    case: Hx => M Hx.
    exists M => n.
    by rewrite Rabs_mult RPow_abs Rabs_Rabsolu -Rabs_mult.
  contradict H.

  apply is_lim_seq_spec in H.
  case: (H (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.

  set M := fix f N := match N with
    | O => Rabs (a O * x ^ O)
    | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
  exists (Rmax (M N) 1) => n.
  case: (le_lt_dec N n) => Hn.
  apply Rle_trans with (2 := Rmax_r _ _).
  move: (Hx n Hn).
  rewrite Rminus_0_r.
  by apply Rlt_le.
  apply Rle_trans with (2 := Rmax_l _ _).
  elim: N n Hn {Hx} => [ | N IH] /= n Hn.
  by apply lt_n_O in Hn.
  apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
  apply Rle_trans with (2 := Rmax_l _ _).
  by apply IH.
  rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
Qed.

Lemma CV_radius_ext (a b : nat -> R) :
  (forall n, a n = b n) -> CV_radius a = CV_radius b.
Proof.
  move => Heq.
  rewrite /CV_radius /Lub_Rbar_ne.
  case: ex_lub_Rbar_ne => la [ub_a lub_a] ;
  case: ex_lub_Rbar_ne => lb [ub_b lub_b] /=.
  apply Rbar_le_antisym.
  apply lub_a => x Hx.
  apply ub_b ; move: Hx.
  apply ex_series_ext => n ; by rewrite Heq.
  apply lub_b => x Hx.
  apply ub_a ; move: Hx.
  apply ex_series_ext => n ; by rewrite Heq.
Qed.

(** ** Convergence criteria *)
(** D'Alembert criterion for power series *)

Lemma CV_disk_DAlembert_aux (a : nat -> R) (x k : R) :
  x <> 0 -> (forall n, a n <> 0) ->
  (is_lim_seq (fun n => Rabs (a (S n) / a n)) k
    <-> is_lim_seq (fun n => Rabs ((a (S n) * x^(S n)) / (a n * x ^ n))) (Rabs x * k)).
Proof.
  move => Hx Ha ; split => H.
  evar (l : Rbar).
  replace (Finite (Rabs x * k)) with l.
  apply is_lim_seq_ext with (fun n => Rabs x * Rabs (a (S n) / a n)).
  move => n ; rewrite ?Rabs_div => //=.
  rewrite ?Rabs_mult.
  field.
  split ; apply Rabs_no_R0 => //.
  by apply pow_nonzero.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero.
  apply is_lim_seq_scal_l.
  apply H.
  by simpl.
  evar (l : Rbar).
  replace (Finite k) with l.
  apply is_lim_seq_ext with (fun n : nat => /Rabs x * Rabs (a (S n) * x ^ S n / (a n * x ^ n))).
  move => n ; rewrite /= ?Rabs_div ?Rabs_mult.
  field.
  repeat split ; apply Rabs_no_R0 => //.
  by apply pow_nonzero.
  by apply Ha.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero.
  apply is_lim_seq_scal_l.
  apply H.
  apply Rbar_finite_eq ; field.
  apply Rabs_no_R0 => //.
Qed.

Lemma CV_disk_DAlembert (a : nat -> R) (x:R) l :
  (forall n:nat, a n <> 0) ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) (Finite l) ->
  (l = 0 \/ (l <> 0 /\ Rabs x < / l))
    -> CV_disk a x.
Proof.
  move => Ha Hl H.
  case: (Req_dec x 0) => Hx.
  rewrite Hx.
  exists (Rabs (a O)).
  apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
  elim => /= [ | n IH].
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
  apply is_lim_seq_const.

  apply ex_series_DAlembert with (Rabs x * l).
  case: H => H.
  rewrite H Rmult_0_r ; by apply Rlt_0_1.
  replace 1 with (/ l * l) by (field ; apply H).
  apply Rmult_lt_compat_r.
  apply Rnot_le_lt ; case => H0.
  case: H => H.
  apply Rle_not_lt.
  apply Rlt_le, Rlt_le_trans with 0.
  by apply Rinv_lt_0_compat.
  by apply Rabs_pos.
  by case: H.
  by apply H.
  move => n ; apply Rmult_integral_contrapositive_currified.
  by apply Ha.
  by apply pow_nonzero.
  by apply CV_disk_DAlembert_aux.
Qed.

Lemma CV_radius_finite_DAlembert (a : nat -> R) (l : R) :
  (forall n:nat, a n <> 0) -> 0 < l ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  CV_radius a = Finite (/l).
Proof.
  move => Ha Hl Hda.
  apply Rbar_le_antisym.
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => /= cv [ub lub].
  apply lub => x Hax.
  case: (Rle_lt_dec x 0) => Hx.
  apply Rlt_le, Rle_lt_trans with 0.
  by apply Hx.
  by apply Rinv_0_lt_compat.
  rewrite -(Rabs_pos_eq x (Rlt_le _ _ Hx)).
  rewrite -(Rmult_1_l (/l)).
  replace (Rabs x) with ((Rabs x * l) /l) by (field ; apply Rgt_not_eq, Hl).
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rinv_0_lt_compat.
  apply Rnot_lt_le.
  contradict Hax.
  have : CV_disk a x -> is_lim_seq (fun n => a n * x ^ n) 0.
    move => H.
    apply ex_series_lim_0.
    by apply ex_series_Rabs.
  move => H H0.
  move: (H H0) => {H H0}.
  apply not_ex_series_DAlembert with (Rabs x * l) => //.
  move => n.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero, Rgt_not_eq.
  apply CV_disk_DAlembert_aux.
  by apply Rgt_not_eq.
  by apply Ha.
  by apply Hda.

  apply Rbar_not_lt_le.
  move : (CV_disk_outside a).
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ;
  case => [cv | | ] /= [ub lub] Hnot_ex H ; try by auto.
  suff H0 : cv < ((cv+/l)/2) < /l.
  absurd (ex_series (fun n => Rabs (a n * ((cv+/l)/2)^n))).

  suff H1 : cv < Rabs ((cv + / l) / 2).
  move: (Hnot_ex ((cv + / l) / 2) H1) => {Hnot_ex} Hnot_ex.
  contradict Hnot_ex ; by apply ex_series_lim_0, ex_series_Rabs.
  apply Rlt_le_trans with (2 := Rle_abs _), H0.
  apply (CV_disk_DAlembert) with l.
  by apply Ha.
  by apply Hda.
  right ; split.
  by apply Rgt_not_eq.
  rewrite Rabs_pos_eq.
  by apply H0.
  apply Rlt_le, Rle_lt_trans with (2 := proj1 H0).
  apply ub.
  exists (Rabs (a O)).
  apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
    elim => [ | n IH] /=.
    by rewrite Rmult_1_r.
    by rewrite Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
    by apply is_lim_seq_const.
  pattern (/l) at 3 ;
  replace (/ l) with ((/l + / l) / 2) by (field ; by apply Rgt_not_eq).
  pattern (cv) at 1 ;
  replace (cv) with ((cv + cv) / 2) by field.
  split ; apply Rmult_lt_compat_r ; by intuition.
  case: (ub 0) => //.
  exists (Rabs (a O)).
  apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
    elim => [ | n IH] /=.
    by rewrite Rmult_1_r.
    by rewrite Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
    by apply is_lim_seq_const.
Qed.

Lemma CV_radius_infinite_DAlembert (a : nat -> R) :
  (forall n:nat, a n <> 0) ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) 0 ->
  CV_radius a = p_infty.
Proof.
  move => Ha Hda.
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ; case => [cv | | ] //= [ub lub] ;
  have : False => //.
  have H : CV_disk a (cv + 1).
    have H : 0 < cv + 1.
      apply Rlt_le_trans with (0+1).
      rewrite Rplus_0_l ; by apply Rlt_0_1.
      apply Rplus_le_compat_r.
      apply ub.
      exists (Rabs (a O)).
      apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
      elim => [ | k IH] /=.
      by rewrite Rmult_1_r.
      by rewrite Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
      by apply is_lim_seq_const.

    apply ex_series_DAlembert with 0.
    by apply Rlt_0_1.
    move => n ; apply Rmult_integral_contrapositive_currified.
    by[].
    by apply Rgt_not_eq, pow_lt.
  rewrite -(Rmult_0_r (Rabs (cv + 1))).
  apply (CV_disk_DAlembert_aux a (cv + 1)).
  by apply Rgt_not_eq.
  by [].
  by [].
  move: (ub (cv+1) H).
  by apply Rbar_lt_not_le, Rlt_n_Sn.
  case: (ub 0) => //.
  exists (Rabs (a O)).
  apply (is_lim_seq_ext (fun _ => Rabs (a O)) _ (Rabs (a 0%nat))).
  elim => [ | k IH] /=.
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 /plus /= Rplus_0_r.
  by apply is_lim_seq_const.
Qed.

(** Equivalence with standard library Reals *)

Lemma CV_radius_Reals_0 (a : nat -> R) (r : posreal) :
  Rbar_lt (Finite r) (CV_radius a) -> CVN_r (fun n x => a n * x ^ n) r.
Proof.
  move => Hr.
  rewrite /CVN_r /Boule.
  have H := CV_radius_bounded a.
  exists (fun n => Rabs (a n * r ^ n)).
  exists (Series (fun n => Rabs (a n * r ^ n))) ; split.
  rewrite -(Rabs_pos_eq r (Rlt_le _ _ (cond_pos r))) in Hr.
  apply CV_disk_inside in Hr.
  apply Lim_seq_correct' in Hr ;
  rewrite -/(Series (fun n : nat => Rabs (a n * r ^ n))) in Hr.
  move => e He.
  apply is_lim_seq_spec in Hr.
  case: (Hr (mkposreal e He)) => /= {Hr} N Hr.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => Rabs (Rabs (a k * r ^ k))) n)
    with (sum_f_R0 (fun k : nat => (Rabs (a k * r ^ k))) n).
  rewrite <- sum_n_sum_f_R0; by apply Hr.
  elim: n {Hn} => /= [ | n IH] ; rewrite Rabs_Rabsolu.
  by [].
  by rewrite IH.
  move => n x Hx.
  rewrite ?Rabs_mult -?RPow_abs.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply pow_incr ; split.
  by apply Rabs_pos.
  rewrite (Rabs_pos_eq r).
  rewrite Rminus_0_r in Hx.
  by apply Rlt_le.
  by apply Rlt_le, r.
Qed.

Lemma CV_radius_Reals_1 (a : nat -> R) (r : posreal) :
  CVN_r (fun n x => a n * x ^ n) r -> Rbar_le (Finite r) (CV_radius a).
Proof.
  case => An [l [H H0]].
  have H1 : is_lub_Rbar (CV_disk a) (CV_radius a).
    rewrite /CV_radius /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  have H2 : forall (y : R), 0 < y < r -> (CV_disk a y).
    move => y Hy.
    apply Comp_ex_series with An.
    move => n ; split.
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rabs_pos_eq Rminus_0_r.
    by apply Hy.
    by apply Rlt_le, Hy.
    exists l.
    apply (is_lim_seq_spec _ l).
    intros eps.
    case: (H eps (cond_pos eps)) => N {H} H.
    exists N => n Hn.
    set v := sum_n _ _.
    replace v with (sum_n (fun k : nat => Rabs (An k)) n).
    rewrite sum_n_sum_f_R0; by apply H.
    rewrite /v {v}.
    elim: n {Hn} => /= [ | n IH].
    apply Rabs_pos_eq.
    apply Rle_trans with (Rabs (a O * 0 ^ O)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
    rewrite IH Rabs_pos_eq.
    by [].
    apply Rle_trans with (Rabs (a (S n) * 0 ^ (S n))).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
  have H3  : forall y, 0 < y < r -> Rbar_le (Finite (y)) (CV_radius a).
    move => y Hy.
    by apply H1, H2.
    have H4 := CV_radius_ge_0 a.
    case: (CV_radius a) H3 H4 => /= [cv | | ] // H3 H4.
    apply Rnot_lt_le => /= H5.
    have H6 : 0 < (cv+r)/2 < r.
      split.
      apply Rdiv_lt_0_compat.
      apply Rplus_le_lt_0_compat.
      by apply H4.
      by apply Rle_lt_trans with cv.
      by apply Rlt_R0_R2.
      pattern (pos r) at 2 ; replace (pos r) with ((r+r)/2) by field.
      apply Rmult_lt_compat_r ; by intuition.
    move: (H3 _ H6).
    apply Rlt_not_le.
    pattern cv at 1 ; replace cv with ((cv+cv)/2) by field.
    apply Rmult_lt_compat_r ; by intuition.
Qed.

Lemma CV_radius_Reals_2 (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
  -> exists r : posreal, CVU (fun n x => sum_f_R0 (fun k => a k * x ^ k) n) (PSeries a) x r.
Proof.
  move => Hx.
  have H : exists r : posreal, Rabs x < r /\ Rbar_lt (Finite r) (CV_radius a).
    case: (CV_radius a) Hx => /= [cv | | ] Hx.
    have H : 0 < (Rabs x + cv)/2.
    apply Rdiv_lt_0_compat.
    apply Rplus_le_lt_0_compat.
    by apply Rabs_pos.
    by apply Rle_lt_trans with (2 := Hx), Rabs_pos.
    by apply Rlt_R0_R2.
    exists (mkposreal _ H) => /=.
    pattern cv at 3 ; replace cv with ((cv+cv)/2) by field.
    pattern (Rabs x) at 1 ; replace (Rabs x) with ((Rabs x + Rabs x)/2) by field.
    split ; apply Rmult_lt_compat_r ; by intuition.
    have H : 0 < Rabs x + 1.
      apply Rle_lt_0_plus_1, Rabs_pos.
    exists (mkposreal _ H) => /=.
    split.
    by apply Rlt_plus_1.
    by [].
    by [].
  case: H => r H.
  apply CVN_CVU_r with r.
  by apply CV_radius_Reals_0, H.
  by apply H.
Qed.

(** * Operations *)

(** Addition of two power series *)

Section PS_plus.

Context {K : AbsRing} {V : NormedModule K}.

Definition PS_plus (a b : nat -> V) (n : nat) : V := plus (a n)  (b n).

Lemma is_pseries_plus (a b : nat -> V) (x :K) (la lb : V) :
  is_pseries a x la -> is_pseries b x lb
    -> is_pseries (PS_plus a b) x (plus la lb).
Proof.
  move => Ha Hb. 
  apply filterlim_ext with (f:=
    (fun n => plus (sum_n (fun k => scal (pow_n x k) (a k)) n) (sum_n (fun k => scal (pow_n x k) (b k)) n))).
  elim => [ | n IH].
  simpl ; rewrite /PS_plus.
  now repeat rewrite scal_one.
  simpl ; rewrite -IH /PS_plus.
  repeat rewrite -plus_assoc; apply f_equal.
  rewrite plus_comm -plus_assoc; apply f_equal.
  rewrite scal_distr_l; apply plus_comm.
  now apply filterlim_compose_2 with (3 := filterlim_plus _ _).
Qed.

Lemma ex_pseries_plus (a b : nat -> V) (x : K) :
  ex_pseries a x -> ex_pseries b x
    -> ex_pseries (PS_plus a b) x.
Proof.
  move => [la Ha] [lb Hb].
  exists (plus la lb).
  by apply is_pseries_plus.
Qed.

End PS_plus.

Lemma PSeries_plus (a b : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries b x
    -> PSeries (PS_plus a b) x = PSeries a x + PSeries b x.
Proof.
  intros Ha Hb.
  apply is_pseries_unique.
  apply: is_pseries_plus ; rewrite PSeries_eq ;
  apply Series_correct.
  by apply Ha.
  by apply Hb.
Qed.

Lemma CV_disk_plus (a b : nat -> R) (x : R) :
  (CV_disk a x) -> (CV_disk b x)
  -> (CV_disk (PS_plus a b) x).
Proof.
  move => Ha Hb.
  move: (ex_series_plus _ _ Ha Hb).
  apply Comp_ex_series => n ; split.
  by apply Rabs_pos.
  rewrite Rmult_plus_distr_r.
  by apply Rabs_triang.
Qed.
Lemma CV_radius_plus (a b : nat -> R) :
  Rbar_le (Rbar_min (CV_radius a) (CV_radius b)) (CV_radius (PS_plus a b)).
Proof.
  have Ha0 := CV_radius_ge_0 a.
  have Hb0 := CV_radius_ge_0 b.
  have Hab0 := CV_radius_ge_0 (PS_plus a b).
  have Hmin_0 : Rbar_le (Finite 0) (Rbar_min (CV_radius a) (CV_radius b)).
    rewrite /Rbar_min ; by case: Rbar_le_dec => H.
  apply is_lub_Rbar_subset
    with (CV_disk (PS_plus a b))
    (fun x => (CV_disk a x) /\ (CV_disk b x)).
  move => x [Ha Hb] ; by apply CV_disk_plus.
  rewrite /CV_radius /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  rewrite /Rbar_min ; case: Rbar_le_dec => Hle ;
    [case: (Rbar_le_lt_or_eq_dec _ _ Hle) => {Hle} Hle | ].

  apply is_lub_Rbar_eqset with (CV_disk a).
  move => x ; split => Hx.
  by apply Hx.
  split.
  by apply Hx.
  apply CV_disk_inside.
  apply Rbar_le_lt_trans with (2 := Hle).
  apply Rbar_not_lt_le => H1.
  apply (CV_disk_outside _ _ H1).
  by apply ex_series_lim_0, ex_series_Rabs.
  rewrite /CV_radius /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.

  have Ha : is_lub_Rbar (fun x : R => CV_disk a x) (CV_radius a).
    rewrite /CV_radius /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  have Hb : is_lub_Rbar (fun x : R => CV_disk b x) (CV_radius b).
    rewrite /CV_radius /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  rewrite -Hle in Hb.
  split => [x Hx | l Hl].
  case: Hx => Hx0 Hx1.
  by apply Ha.
  move: (proj2 Ha l) => {Ha} Ha.
  move: (proj2 Hb l) => {Hb} Hb.
  have H1 : Rbar_le (Finite 0) l.
    apply Hl ; split ; by apply CV_disk_0.
  case: l Hl Ha Hb H1 => [l | | ] Hl Ha Hb H1.
  apply Rbar_not_lt_le => H0.
  case: {1 2 3 5 6}(CV_radius a) H0 Hl Ha Hb (eq_refl (CV_radius a)) Ha0 => /= [c | | ] H0 Hl Ha Hb Heq Ha0.
  case: (Hl ((l+c)/2)).
  split ; apply CV_disk_inside ; rewrite -?Hle ?Heq /=.
  have H : 0 <= ((l + c) / 2).
    apply Rmult_le_pos ; intuition.
    by apply Rplus_le_le_0_compat.
  rewrite (Rabs_pos_eq _ H).
  pattern c at 2 ; replace c with ((c+c)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  have H : 0 <= ((l + c) / 2).
    apply Rmult_le_pos ; intuition.
    by apply Rplus_le_le_0_compat.
  rewrite (Rabs_pos_eq _ H).
  pattern c at 2 ; replace c with ((c+c)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  apply Rle_not_lt, Rlt_le.
  pattern l at 1 ; replace l with ((l+l)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  apply Rgt_not_eq.
  pattern l at 2 ; replace l with ((l+l)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  case: (Hl (l+1)).
  split ; apply CV_disk_inside ; by rewrite -?Hle ?Heq.
  apply Rle_not_lt, Rlt_le, Rlt_plus_1.
  apply Rgt_not_eq, Rlt_plus_1.
  by case: Ha0.
  by apply Rbar_not_lt_le => /=.
  by case: H1.

  apply Rbar_not_le_lt in Hle.
  apply is_lub_Rbar_eqset with (CV_disk b).
  move => x ; split => Hx.
  by apply Hx.
  split.
  apply CV_disk_inside.
  apply Rbar_le_lt_trans with (2 := Hle).
  apply Rbar_not_lt_le => H1.
  apply (CV_disk_outside _ _ H1).
  by apply ex_series_lim_0, ex_series_Rabs.
  by apply Hx.
  rewrite /CV_radius /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
Qed.

(** Scalar multiplication *)

Section PS_scal.

Context {K : AbsRing} {V : NormedModule K}.

Definition PS_scal (c : K) (a : nat -> V) (n : nat) : V := scal c (a n).

Lemma is_pseries_scal (c : K) (a : nat -> V) (x : K) (l : V) :
  mult x c = mult c x -> is_pseries a x l -> is_pseries (PS_scal c a) x (scal c l).
Proof.
  move => Hx Ha.
  apply (filterlim_ext (fun n => scal c (sum_n (fun k => scal (pow_n x k) (a k)) n))).
  elim => [ | n IH].
  simpl ; rewrite /PS_scal.
  now repeat rewrite scal_one.
  simpl ; rewrite -IH /PS_scal.
  rewrite scal_distr_l; apply f_equal.
  rewrite 2! scal_assoc.
  apply f_equal2.
  rewrite -/(pow_n x (S n)).
  clear -Hx.
  elim: (S n) => {n} /= [ | n IH].
  by rewrite mult_one_l mult_one_r.
  by rewrite -mult_assoc -IH 2!mult_assoc Hx.
  by [].
  now apply filterlim_compose with (2 := filterlim_scal _ _).
Qed.

Lemma ex_pseries_scal (c : K) (a : nat -> V) (x : K) :
  mult x c = mult c x -> ex_pseries a x -> ex_pseries (PS_scal c a) x.
Proof.
  move => Hx [l Ha].
  exists (scal c l).
  by apply is_pseries_scal.
Qed.

End PS_scal.

Lemma PSeries_scal (c : R) (a : nat -> R) (x : R) :
  PSeries (PS_scal c a) x = c * PSeries a x.
Proof.
  rewrite -Series_scal_l.
  apply Series_ext.
  move => n /=.
  apply Rmult_assoc.
Qed.

Lemma CV_disk_scal (c : R) (a : nat -> R) (x : R) :
  (CV_disk a x)
  -> (CV_disk (PS_scal c a) x).
Proof.
  move => Ha.
  apply ex_series_ext with (fun n => Rabs c * Rabs (a n * x ^ n)).
  move => n ; rewrite -Rabs_mult ; apply f_equal ;
  by rewrite /PS_scal /= Rmult_assoc.
  apply @ex_series_scal.
  by apply Ha.
Qed.

Lemma CV_radius_scal (c : R) (a : nat -> R) :
  Rbar_le (CV_radius a) (CV_radius (PS_scal c a)).
Proof.
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => la [ub_a lub_a] ;
  case: ex_lub_Rbar_ne => lc [ub_c lub_c] /=.
  apply lub_a => x Hx.
  by apply ub_c, CV_disk_scal.
Qed.

Definition PS_scal_r (c : R) (a : nat -> R) (n : nat) : R :=
  a n * c.
Lemma PSeries_scal_r (c : R) (a : nat -> R) (x : R) :
  PSeries (PS_scal_r c a) x = PSeries a x * c.
Proof.
  rewrite -Series_scal_r.
  apply Series_ext.
  move => n /=.
  rewrite /PS_scal_r ; ring.
Qed.

Lemma CV_disk_scal_r (c : R) (a : nat -> R) (x : R) :
  (CV_disk a x)
  -> (CV_disk (PS_scal_r c a) x).
Proof.
  move => Ha.
  apply ex_series_ext with (fun n => Rabs c * Rabs (a n * x ^ n)).
  move => n ; rewrite -Rabs_mult ; apply f_equal ;
  rewrite /PS_scal_r /= ; ring.
  by apply @ex_series_scal ; apply Ha.
Qed.
Lemma CV_radius_scal_r (c : R) (a : nat -> R) :
  Rbar_le (CV_radius a) (CV_radius (PS_scal_r c a)).
Proof.
  rewrite /CV_radius /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => la [ub_a lub_a] ;
  case: ex_lub_Rbar_ne => lc [ub_c lub_c] /=.
  apply lub_a => x Hx.
  by apply ub_c, CV_disk_scal_r.
Qed.

(** Multiplication and division by a variable *)

Section PS_incr.

Context {K : AbsRing} {V : NormedModule K}.

Definition PS_incr_1 (a : nat -> V) (n : nat) : V :=
  match n with
    | 0 => zero
    | S n => a n
  end.

Lemma is_pseries_incr_1 (a : nat -> V) (x:K) (l : V) :
  is_pseries a x l -> is_pseries (PS_incr_1 a) x (scal x l).
Proof.
  move => Ha.
  apply filterlim_ext_loc with  (fun n : nat => scal x (sum_n (fun k => scal (pow_n x k) (a k)) (pred n))).
  exists 1%nat; intros n; case n.
  intros Hn; contradict Hn ; apply lt_n_O.
  clear n; intros n _ ;induction n.
  simpl; now rewrite mult_one_r 2!scal_one plus_zero_l.
  apply trans_eq with (plus
   (sum_n (fun k : nat => scal (pow_n x k) (PS_incr_1 a k)) (S n))
      (scal (pow_n x (S (S n))) (PS_incr_1 a (S (S n))))).
 2: reflexivity.
 rewrite -IHn; simpl.
 rewrite scal_distr_l; apply f_equal.
 now rewrite scal_assoc.
 apply filterlim_compose with (f:= fun n => pred n) (G:=eventually)
  (g:=fun n => scal x (sum_n (fun k : nat => scal (pow_n x k) (a k)) n)). 
 apply eventually_subseq'.
 exists 1%nat.
 intros n Hn.
 rewrite -pred_Sn.
 now apply lt_pred_n_n.
 now apply filterlim_compose with (2 := filterlim_scal _ _).
Qed.

Lemma ex_pseries_incr_1 (a : nat -> V) (x : K) :
  ex_pseries a x -> ex_pseries (PS_incr_1 a) x.
Proof.
  move => [l Ha] ; exists (scal x l) ; by apply is_pseries_incr_1.
Qed.

Fixpoint PS_incr_n (a : nat -> V) (n k : nat) : V :=
  match n with
    | O => a k
    | S n => PS_incr_1 (PS_incr_n a n) k
  end.

Lemma PS_incr_n_simplify (a : nat -> V) (n k : nat) :
  PS_incr_n a n k =
  match (le_lt_dec n k) with
    | left _ => a (k-n)%nat
    | right _ => zero
  end.
Proof.
  case: le_lt_dec => H.
  elim: n k H => [ | n IH] k H.
  rewrite /PS_incr_n ; by case: k H.
  case: k H => [ | k] H.
  by apply le_Sn_0 in H.
  rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
  rewrite IH.
  apply f_equal.
  by elim: n k H {IH} => /= [ | n IH] k H.
  by apply le_S_n.
  elim: n k H => [ | n IH] k H.
  by apply lt_n_O in H.
  rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
  case: k H => [ | k] H.
  by [].
  by apply IH, lt_S_n.
Qed.

Lemma is_pseries_incr_n (a : nat -> V) (n : nat) (x : K) (l : V) :
  is_pseries a x l -> is_pseries (PS_incr_n a n) x (scal (pow_n x n) l).
Proof.
  move => Ha.
  elim: n => /= [ | n IH].
  by rewrite scal_one.
  rewrite -scal_assoc.
  by apply is_pseries_incr_1.
Qed.

Lemma ex_pseries_incr_n (a : nat -> V) (n : nat) (x : K) :
  ex_pseries a x -> ex_pseries (PS_incr_n a n) x.
Proof.
  move => [l Ha].
  exists (scal (pow_n x n) l) ; by apply is_pseries_incr_n.
Qed.

Definition PS_decr_1 (a : nat -> V) (n : nat) : V := a (S n).

Lemma is_pseries_decr_1 (a : nat -> V) (x y : K) (l : V) :
  mult y x = one -> is_pseries a x l
    -> is_pseries (PS_decr_1 a) x (scal y (plus l (opp (a O)))).
Proof.
  move => Hx Ha.
  apply filterlim_ext with  (fun n : nat => scal y 
    (sum_n (fun k => scal (pow_n x (S k)) (a (S k))) n)).
  intros n; induction n; unfold PS_decr_1; simpl.
  rewrite mult_one_r scal_one scal_assoc.
  rewrite Hx; try assumption.
  apply @scal_one.
  rewrite -IHn.
  rewrite scal_distr_l; apply f_equal.
  rewrite scal_assoc (mult_assoc y).
  rewrite Hx.
  now rewrite mult_one_l.
  apply filterlim_compose with (2 := filterlim_scal _ _).
  apply filterlim_ext with  (fun n : nat => plus 
    (sum_n (fun k => scal (pow_n x k) (a k)) (S n)) (opp (a 0%nat))).
  intros n; induction n; simpl.
  rewrite mult_one_r scal_one.
  rewrite plus_comm plus_assoc.
  now rewrite plus_opp_l plus_zero_l.
  rewrite -IHn.
  apply sym_eq; rewrite plus_comm plus_assoc.
  apply f_equal2;[idtac|reflexivity].
  now rewrite plus_comm.
  apply filterlim_compose_2 with (3 := filterlim_plus _ _).
  apply filterlim_compose with (f:= fun x => S x) (2:=Ha).
  apply eventually_subseq; intros n; omega.
  apply filterlim_const.
Qed.

Lemma ex_pseries_decr_1 (a : nat -> V) (x : K) :
 (x = zero \/ exists y, mult y x = one) -> 
 ex_pseries a x -> ex_pseries (PS_decr_1 a) x.
Proof.
 case => [H | [y Hx]] [l Ha].
 rewrite H ; by apply ex_pseries_0.
 exists (scal y (plus l (opp (a 0%nat)))).
 now apply is_pseries_decr_1.
Qed.

Definition PS_decr_n (a : nat -> V) (n k : nat) : V := a (n + k)%nat.

Lemma is_pseries_decr_n (a : nat -> V) (n : nat) (x y:K) (l : V) :
  mult y x = one -> (0 < n)%nat -> is_pseries a x l
    -> is_pseries (PS_decr_n a n) x (scal (pow_n y n) (plus l (opp (sum_n (fun k => scal (pow_n x k) (a k)) (n-1)%nat)))).
Proof.
  move => Hx Hn Ha.
  case: n Hn => [ | n] Hn.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl ; rewrite -minus_n_O /PS_decr_n /=.
  elim: n => /= [ | n IH].
  rewrite scal_one mult_one_r.
  now apply is_pseries_decr_1.
  set (ln := (scal (mult y (pow_n y n))
          (plus l (opp (sum_n (fun k : nat => scal (pow_n x k) (a k)) n))))) in IH.
  replace (scal (mult y (mult y (pow_n y n)))
     (plus l
        (opp
           (plus (sum_n (fun k : nat => scal (pow_n x k) (a k)) n)
              (scal (mult x (pow_n x n)) (a (S n)))))))
  with (scal y (plus ln (opp (a (S (n + 0)))))).
  assert (Y:is_pseries (fun k : nat => a (S (n + k))) x ln).
  apply IH.
  move: (is_pseries_decr_1 (fun k : nat => a (S (n + k))) x y ln Hx Y).
  rewrite /PS_decr_1 /=.
  apply is_pseries_ext => k.
  apply f_equal ; ring.
  rewrite -scal_assoc.
  apply f_equal; unfold ln.
  repeat rewrite (scal_distr_l _ l).
  rewrite -plus_assoc; apply f_equal.
  rewrite opp_plus scal_distr_l; apply f_equal.
  rewrite plus_0_r -scal_opp_l scal_assoc.
  apply trans_eq with (scal (opp (one : K)) (a (S n))).
  now rewrite scal_opp_l scal_one.
  apply f_equal2; try reflexivity.
  rewrite <- opp_mult_r; apply f_equal.
  clear -Hx.
  rewrite -?/(pow_n _ (S _)).
  elim: (S n) => {n} /= [ | n IH].
  by rewrite mult_one_l.
  rewrite -(pow_n_comm_1 x) mult_assoc.
  rewrite -(mult_assoc y (pow_n y n) (pow_n x n)).
  by rewrite -IH mult_one_r.
Qed.

Lemma ex_pseries_decr_n (a : nat -> V) (n : nat) (x : K) :
  (x = zero \/ exists y, mult y x = one) -> ex_pseries a x -> ex_pseries (PS_decr_n a n) x.
Proof.
  intros Hx H.
  induction n.
  unfold PS_decr_n; now simpl.
  apply ex_pseries_ext with ((PS_decr_1 (PS_decr_n a n))).
  intros m; unfold PS_decr_1, PS_decr_n.
  apply f_equal; ring.
  apply ex_pseries_decr_1.
  apply Hx.
  now apply IHn.
Qed.

End PS_incr.

Lemma PSeries_incr_1 a x :
  PSeries (PS_incr_1 a) x = x * PSeries a x.
Proof.
  rewrite -Series_scal_l.
  unfold PSeries, Series.
  rewrite -(Lim_seq_incr_1 (sum_n (fun k : nat => PS_incr_1 a k * x ^ k))) /=.
  apply f_equal, Lim_seq_ext.
  case.
  rewrite /plus /= /zero /=.
  ring.
  elim => /= [ | n IH].
  rewrite /plus /zero /=.
  ring.
  rewrite IH /plus /=.
  ring.
Qed.

Lemma PSeries_incr_n (a : nat -> R) (n : nat) (x : R) :
  PSeries (PS_incr_n a n) x = x^n * PSeries a x.
Proof.
  elim: n => /= [ | n IH].
  by rewrite Rmult_1_l.
  rewrite Rmult_assoc.
  by rewrite PSeries_incr_1 IH.
Qed.

Lemma PSeries_decr_1 (a : nat -> R) (x : R) :
  ex_pseries a x -> PSeries a x = a O + x * PSeries (PS_decr_1 a) x.
Proof.
  intros Ha.
  case: (Req_dec x 0) => Hx.
  rewrite Hx PSeries_0 ; ring.
  move: (is_pseries_decr_1 a x (/x) (PSeries a x) (Rinv_l _ Hx)
    (PSeries_correct _ _ Ha)) => Hb.
  rewrite (is_pseries_unique _ _ _ Hb).
  rewrite /plus /opp /scal /= /mult /=.
  now field.
Qed.

Lemma PSeries_decr_1_aux (a : nat -> R) (x : R) :
  a O = 0 -> (PSeries a x) = x * PSeries (PS_decr_1 a) x.
Proof.
  intros Ha0.
  rewrite -PSeries_incr_1.
  rewrite /PS_incr_1 /PS_decr_1 /=.
  apply Series_ext.
  case => //=.
  by rewrite Ha0.
Qed.

Lemma PSeries_decr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x
    -> PSeries a x = sum_f_R0 (fun k => a k * x^k) n + x^(S n) * PSeries (PS_decr_n a (S n)) x.
Proof.
  intros Ha.
  case: (Req_dec x 0) => Hx.
  rewrite Hx PSeries_0 ; simpl ; ring_simplify.
  elim: n => /= [ | n IH].
  ring.
  rewrite -IH ; ring.
  assert (V:(pow_n x (S n) <> 0)).
  rewrite pow_n_pow; now apply pow_nonzero.
  move: (is_pseries_decr_n a (S n) x (/x) (PSeries a x) (Rinv_l x Hx) (lt_0_Sn _) (PSeries_correct _ _ Ha)) => Hb.
  rewrite (is_pseries_unique _ _ _ Hb).
  rewrite (sum_n_ext _ (fun k : nat => a k * x ^ k)).
  rewrite sum_n_sum_f_R0.
  replace (S n -1)%nat with n.
  rewrite /scal /plus /opp /= /mult /=.
  rewrite pow_n_pow -Rinv_pow ; try assumption.
  field.
  split; try assumption.
  now apply pow_nonzero.
  now apply plus_minus.
  intros m; rewrite pow_n_pow.
  apply Rmult_comm.
Qed.

Lemma PSeries_decr_n_aux (a : nat -> R) (n : nat) (x : R) :
  (forall k : nat, (k < n)%nat -> a k = 0)
    -> PSeries a x = x^n * PSeries (PS_decr_n a n) x.
Proof.
  elim: n => /= [ | n IH] Ha.
  rewrite Rmult_1_l.
  apply PSeries_ext => n ; by intuition.
  rewrite IH.
  rewrite PSeries_decr_1_aux.
  rewrite (Rmult_comm _ (x^n)) Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  apply PSeries_ext => k ; rewrite /PS_decr_1 /PS_decr_n ; by intuition.
  apply Ha ; by intuition.
  move => k Hk.
  apply Ha ; by intuition.
Qed.

Lemma CV_radius_incr_1 (a : nat -> R) :
  CV_radius (PS_incr_1 a) = CV_radius a.
Proof.
  rewrite /CV_radius /CV_disk.

  apply Lub_Rbar_ne_eqset => x ; split => Hx ;
  case: (Req_dec x 0) => [-> | Hx0].

  exists (Rabs (a O)).
  apply filterlim_ext with (fun _ => Rabs (a 0%nat)).
  elim => /= [ | n <-].
  by rewrite Rmult_1_r.
  ring_simplify (a (S n) * (0 * 0 ^ n)).
  by rewrite /plus /= Rabs_R0 Rplus_0_r.
  by apply filterlim_const.

  apply ex_finite_lim_seq_correct in Hx.
  apply ex_finite_lim_seq_correct.
  case: Hx => Hex Hl.
  apply ex_lim_seq_incr_1 in Hex.
  rewrite -Lim_seq_incr_1 in Hl.
  split.
  apply ex_lim_seq_ext
    with (fun n => sum_n (fun k : nat => Rabs (PS_incr_1 a k * x ^ k)) (S n) / Rabs x).
  elim => /= [ | n <-] ;
  rewrite /plus /zero /= ?Rmult_1_r ?Rabs_R0 ?Rplus_0_l ?Rabs_mult ; field ;
  by apply Rabs_no_R0.
  by apply ex_lim_seq_scal_r.
  rewrite -(Lim_seq_ext
    (fun n => sum_n (fun k : nat => Rabs (PS_incr_1 a k * x ^ k)) (S n) / Rabs x)).
  rewrite Lim_seq_scal_r.
  case: (Lim_seq
          (fun n : nat =>
           sum_n (fun k : nat => Rabs (PS_incr_1 a k * x ^ k)) (S n))) Hl => //.
  elim => /= [ | n <-] ;
  rewrite /plus /= ?Rmult_1_r ?Rmult_0_r ?Rabs_R0 ?Rplus_0_l ?Rabs_mult ; field ;
  by apply Rabs_no_R0.

  exists (0).
  apply filterlim_ext with (fun _ => 0).
  elim => /= [ | n <-].
  by rewrite Rmult_1_r Rabs_R0.
  ring_simplify (a n * (0 * 0 ^ n)) ;
  by rewrite Rabs_R0 /plus /= Rplus_0_r.
  by apply filterlim_const.

  apply ex_finite_lim_seq_correct in Hx.
  apply ex_finite_lim_seq_correct.
  case: Hx => Hex Hl.
  split.
  apply ex_lim_seq_incr_1.
  apply ex_lim_seq_ext
    with (fun n => sum_n (fun k : nat => Rabs (a k * x ^ k)) n * Rabs x).
  elim => /= [ | n <-] ;
  rewrite /plus /= ?Rmult_1_r ?Rmult_0_r ?Rabs_R0 ?Rplus_0_l ?Rabs_mult ; field ;
  by apply Rabs_no_R0.
  by apply ex_lim_seq_scal_r.
  rewrite -Lim_seq_incr_1.
  rewrite -(Lim_seq_ext (fun n => sum_n (fun k : nat => Rabs (a k * x ^ k)) n * Rabs x)).
  rewrite Lim_seq_scal_r.
  case: (Lim_seq
          (fun n : nat =>
           sum_n (fun k : nat => Rabs (a k * x ^ k)) n)) Hl => //.
  elim => /= [ | n <-] ;
  rewrite /plus /= ?Rmult_1_r ?Rmult_0_r ?Rabs_R0 ?Rplus_0_l ?Rabs_mult ; field ;
  by apply Rabs_no_R0.
Qed.

Definition PS_mult (a b : nat -> R) n :=
  sum_f_R0 (fun k => a k * b (n - k)%nat) n.

Lemma is_pseries_mult (a b : nat -> R) (x la lb : R) :
  is_pseries a x la -> is_pseries b x lb
  -> Rbar_lt (Rabs x) (CV_radius a) -> Rbar_lt (Rabs x) (CV_radius b)
  -> is_pseries (PS_mult a b) x (la * lb).
Proof.
  move => Hla Hlb Ha Hb.
  apply is_series_ext with (fun n => sum_f_R0 (fun k => (fun l => a l * x ^ l) k * (fun l => b l * x ^ l) (n - k)%nat) n).
  move => n.
  rewrite /PS_mult /scal /= /mult /= scal_sum.
  apply sum_eq => i Hi.
  rewrite -{4}(NPeano.Nat.sub_add _ _ Hi).
  rewrite pow_n_pow pow_add.
  ring.
  apply (is_series_mult (fun l => a l * x ^ l) (fun l => b l * x ^ l)).
  now apply is_pseries_R.
  now apply is_pseries_R.
  by apply CV_disk_inside.
  by apply CV_disk_inside.
Qed.
Lemma ex_pseries_mult (a b : nat -> R) (x : R) :
  Rbar_lt (Rabs x) (CV_radius a) -> Rbar_lt (Rabs x) (CV_radius b)
  -> ex_pseries (PS_mult a b) x.
Proof.
  move => Ha Hb.
  exists ((PSeries a x) * (PSeries b x)).
  apply is_pseries_mult => // ; by apply PSeries_correct, CV_radius_inside.
Qed.
Lemma PSeries_mult (a b : nat -> R) (x : R) :
  Rbar_lt (Rabs x) (CV_radius a) -> Rbar_lt (Rabs x) (CV_radius b)
  -> PSeries (PS_mult a b) x = PSeries a x * PSeries b x.
Proof.
  move => Ha Hb.
  apply is_pseries_unique.
  apply is_pseries_mult => // ; by apply PSeries_correct, CV_radius_inside.
Qed.

(** Sums on even and odd *)

Lemma is_pseries_odd_even (a : nat -> R) (x l1 l2 : R) :
  is_pseries (fun n => a (2*n)%nat) (x^2) l1 -> is_pseries (fun n => a (2*n+1)%nat) (x^2) l2
    -> is_pseries a x (l1 + x * l2).
Proof.
  rewrite 3!is_pseries_R.
  move => H1 H2.
  apply filterlim_ext with (fun n =>
    (sum_n (fun k : nat => a (2 * k)%nat * (x ^ 2) ^ k) (div2 n)) +
    x * match n with | O => 0
    | S n => (sum_n (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 n)) end).
  case => [ | n].
  simpl ; ring.
  case: (even_odd_dec n) => Hn.
(* even n *)
  rewrite 3!sum_n_sum_f_R0.
  rewrite -(even_div2 _ Hn) {3}(even_double _ Hn).
  elim: (div2 n) => {n Hn} [ | n] ;
  rewrite ?double_S /sum_f_R0 -/sum_f_R0.
  rewrite /double /= ; ring.
  rewrite -pow_mult.
  replace (2 * S n)%nat with (S (S (double n)))
    by (rewrite -double_S /double ; ring).
  replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
  move => <- ; simpl ; ring.
(* odd n *)
  rewrite 3!sum_n_sum_f_R0.
  rewrite -(odd_div2 _ Hn) {3}(odd_double _ Hn).
  elim: (div2 n) => {n Hn} [ | n] ;
  rewrite ?double_S /sum_f_R0 -/sum_f_R0.
  rewrite /double /= ; ring.
  rewrite -?pow_mult.
  replace (2 * S n)%nat with (S (S (double n)))
    by (rewrite -double_S /double ; ring).
  replace (2 * S (S n))%nat with (S (S (S (S (double n)))))
    by (rewrite -double_S /double ; ring).
  replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
  move => <- ; simpl ; ring.
  apply (is_lim_seq_plus' _ _ l1 (x*l2)).
(* a(2k)x^(2k) *)
  apply filterlim_compose with (2:=H1).
  intros P [N HN].
  exists (2*N+1)%nat.
  intros n Hn; apply HN.
  apply le_double.
  apply plus_le_reg_l with 1%nat.
  rewrite Plus.plus_comm.
  apply le_trans with (1:=Hn).
  apply le_trans with (1+double (div2 n))%nat.
  case (even_or_odd n); intros J.
  rewrite <- even_double; try exact J.
  now apply le_S.
  rewrite <- odd_double; easy.
  simpl; now rewrite plus_0_r.
(* a(2k+1)x^(2k+1) *)
  apply (is_lim_seq_scal_l _ x l2) => //.
  apply filterlim_ext_loc with
    (fun n => sum_n (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) 
      (div2 (pred n))).
  exists 1%nat; intros y; case y.
  easy.
  intros n _; reflexivity.
  apply filterlim_compose with (2:=H2). 
  intros P [N HN].
  exists (2*N+2)%nat.
  intros n Hn; apply HN.
  apply le_double.
  apply plus_le_reg_l with 2%nat.
  rewrite Plus.plus_comm.
  apply le_trans with (1:=Hn).
  apply le_trans with (1+(1+double (div2 (pred n))))%nat.
  case (even_or_odd (pred n)); intros J.
  rewrite <- even_double; try exact J.
  case n.
  simpl; now apply le_S, le_S.
  intros m; simpl; now apply le_S.
  rewrite <- odd_double; try exact J.
  case n; simpl; try easy.
  now apply le_S.
  simpl; now rewrite plus_0_r.
Qed.
Lemma ex_pseries_odd_even (a : nat -> R) (x : R) :
  ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2)
    -> ex_pseries a x.
Proof.
  move => [l1 H1] [l2 H2].
  exists (l1 + x * l2).
  by apply is_pseries_odd_even.
Qed.
Lemma PSeries_odd_even (a : nat -> R) (x : R) :
  ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2)
    -> PSeries a x = PSeries (fun n => a (2*n)%nat) (x^2) + x * PSeries (fun n => a (2*n+1)%nat) (x^2).
Proof.
  move => H1 H2 ;
  apply is_pseries_unique.
  apply (is_pseries_odd_even a x); by apply PSeries_correct.
Qed.

Lemma PSeries_const_0 : forall x, PSeries (fun _ => 0) x = 0.
Proof.
  move => x.
  replace 0 with (real 0) by auto.
  apply (f_equal real).
  rewrite -{2}(Lim_seq_const 0) /=.
  apply Lim_seq_ext.
  elim => /= [ | n ->] ; rewrite /plus /= ; ring.
Qed.

Lemma CV_radius_const_0 : CV_radius (fun _ => 0) = p_infty.
Proof.
  suff : forall x, Rbar_le (Rabs x) (CV_radius (fun _ : nat => 0)).
  case H : (CV_radius (fun _ : nat => 0)) => [cv | | ] //= H0.
  case: (Rle_lt_dec 0 cv) => Hcv.
  move: (H0 (cv + 1)) => {H0} H0.
  contradict H0 ; apply Rlt_not_le => /=.
  apply Rlt_le_trans with (2 := Rle_abs _).
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  contradict Hcv ; apply (Rbar_le_not_lt cv 0).
  rewrite -Rabs_R0.
  by apply H0.
  move: (H0 0) => {H0} H0.
  contradict H0 ; by apply Rbar_lt_not_le.
  move => x ; apply Rbar_not_lt_le => Hx.
  apply CV_disk_outside in Hx.
  apply: Hx.
  apply is_lim_seq_ext with (fun _ => 0).
  move => n ; ring.
  by apply is_lim_seq_const.
Qed.

Section PS_opp.

Context {K : AbsRing} {V : NormedModule K}.

Definition PS_opp (a : nat -> V) (n : nat) : V := opp (a n).

Lemma is_pseries_opp (a : nat -> V) (x :K) (l : V) :
  is_pseries a x l -> is_pseries (PS_opp a) x (opp l).
Proof.
  intros H.
  replace (opp l) with (scal (opp (one : K)) l).
  2: now rewrite scal_opp_l scal_one.
  apply is_pseries_ext with (PS_scal (opp one) a).
  intros n; unfold PS_scal, PS_opp.
  now rewrite scal_opp_l scal_one.
  apply is_pseries_scal.
  rewrite -opp_mult_l -opp_mult_r.
  by rewrite mult_one_l mult_one_r.
  by apply H.
Qed.

Lemma ex_pseries_opp (a : nat -> V) (x : K) :
  ex_pseries a x -> ex_pseries (PS_opp a) x.
Proof.
  intros [l Hl].
  exists (opp l).
  now apply is_pseries_opp.
Qed.

End PS_opp.

Lemma PSeries_opp (a : nat -> R) (x : R) :
  PSeries (PS_opp a) x = - PSeries a x.
Proof.
  replace (- PSeries a x) with ((-1) * PSeries a x) by ring.
  rewrite -PSeries_scal.
  apply PSeries_ext => n.
  by rewrite /PS_scal /PS_opp scal_opp_one.
Qed.

Lemma CV_radius_opp (a : nat -> R) :
  (CV_radius a) = (CV_radius (PS_opp a)).
Proof.
  apply Rbar_le_antisym.
  rewrite (CV_radius_ext (PS_opp a) (PS_scal (-1) a)).
  by apply CV_radius_scal.
  by move => n ; rewrite /PS_scal /PS_opp scal_opp_one.
  rewrite (CV_radius_ext a (PS_scal (-1) (PS_opp a))).
  by apply CV_radius_scal.
  by move => n ; rewrite /PS_scal /PS_opp scal_opp_one opp_opp.
Qed.

Section PS_minus.

Context {K : AbsRing} {V : NormedModule K}.

Definition PS_minus (a b : nat -> V) (n : nat) : V := plus (a n) (opp (b n)).

Lemma is_pseries_minus (a b : nat -> V) (x:K) (la lb : V) :
  is_pseries a x la -> is_pseries b x lb
  -> is_pseries (PS_minus a b) x (plus la (opp lb)).
Proof.
  move => Ha Hb.
  apply is_pseries_plus.
  exact: Ha.
  by apply is_pseries_opp.
Qed.

Lemma ex_pseries_minus (a b : nat -> V) (x : K) :
  ex_pseries a x -> ex_pseries b x
  -> ex_pseries (PS_minus a b) x.
Proof.
  move => Ha Hb.
  apply ex_pseries_plus.
  exact: Ha.
  by apply ex_pseries_opp.
Qed.

End PS_minus.

Lemma PSeries_minus (a b : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries b x
  -> PSeries (PS_minus a b) x = PSeries a x - PSeries b x.
Proof.
  move => Ha Hb.
  rewrite PSeries_plus.
  by rewrite PSeries_opp.
  exact: Ha.
  by apply ex_pseries_opp.
Qed.

(** * Analysis *)

(** ** Continuity *)

Lemma PSeries_continuity (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> continuity_pt (PSeries a) x.
Proof.
  move => H.
  case: (CV_radius_Reals_2 a x H) => r H0.
  apply (CVU_continuity
    (fun (n : nat) (x : R) => sum_f_R0 (fun k : nat => a k * x ^ k) n)
    (PSeries a) x r H0).
  move => n y Hy.
  apply continuity_pt_finite_SF.
  move => k Hk.
  apply continuity_pt_scal.
  elim: k {Hk} => /= [ | k IH].
  by apply continuity_pt_const => d f.
  apply continuity_pt_mult.
  apply derivable_continuous_pt, derivable_pt_id.
  by apply IH.
  rewrite /Boule Rminus_eq_0 Rabs_R0 ; by apply r.
Qed.

(** ** Differentiability *)

Definition PS_derive (a : nat -> R) (n : nat) :=
  INR (S n) * a (S n).
Lemma CV_radius_derive (a : nat -> R) :
  CV_radius (PS_derive a) = CV_radius a.
Proof.
  have H := (CV_radius_bounded a).
  have H0 := (CV_radius_bounded (PS_derive a)).

  apply Rbar_le_antisym.
  apply is_lub_Rbar_subset with (2 := H) (3 := H0) => x [M Ha].
  exists (Rmax (Rabs (a O)) (Rabs x * M)) ; case => /= [ | n].
  rewrite Rmult_1_r ; by apply Rmax_l.
  apply Rle_trans with (2 := Rmax_r _ _).
  replace (a (S n) * (x * x ^ n))
    with (x  * ((PS_derive a n * x ^ n) / INR (S n)))
    by (rewrite /PS_derive ; field ; apply not_0_INR, sym_not_eq, O_S).
  rewrite Rabs_mult ; apply Rmult_le_compat_l.
  by apply Rabs_pos.
  rewrite Rabs_div ; [ | by apply not_0_INR, sym_not_eq, O_S].
  apply Rle_div_l.
  by apply Rabs_pos_lt, not_0_INR, sym_not_eq, O_S.
  apply Rle_trans with (1 := Ha n).
  rewrite -{1}(Rmult_1_r M).
  apply Rmult_le_compat_l.
  by apply Rle_trans with (2 := Ha O), Rabs_pos.
  by apply Rle_trans with (2 := Rle_abs _), (le_INR 1), le_n_S, le_O_n.

  apply H => x [M Hx].

  have H1 : Rbar_le (Finite 0) (CV_radius (PS_derive a)).
    apply H0 ; exists (Rabs (PS_derive a O)) ; case => /= [ | n].
    rewrite Rmult_1_r ; by apply Rle_refl.
    rewrite Rmult_0_l Rmult_0_r Rabs_R0 ; by apply Rabs_pos.
  wlog: x Hx / (0 < x) => [Hw |  Hx0].
    case: (Rle_lt_dec x 0) => Hx0.
    apply Rbar_le_trans with (Finite 0).
    exact Hx0.
    by apply H1.
    by apply Hw.

  suff : forall y, 0 < y < x -> Rbar_le (Finite y) (CV_radius (PS_derive a)).
    case: (CV_radius (PS_derive a)) H1 => [l | | ] //= H1 H2.
    apply Rnot_lt_le => /= H3.
    have H4 : (0 < (x+l)/2 < x).
      split.
      apply Rdiv_lt_0_compat.
      by apply Rplus_lt_le_0_compat.
      by apply Rlt_R0_R2.
      apply Rminus_lt, Ropp_lt_cancel ; field_simplify.
      rewrite Rdiv_1 ; apply Rdiv_lt_0_compat.
      by apply -> Rminus_lt_0.
      by apply Rlt_R0_R2.
    move: (H2 _ H4).
    apply Rlt_not_le.
    apply Rminus_lt, Ropp_lt_cancel ; field_simplify.
    rewrite Rdiv_1 ; apply Rdiv_lt_0_compat.
    rewrite Rplus_comm ; by apply -> Rminus_lt_0.
    by apply Rlt_R0_R2.
  move => y Hy.
  apply H0 ; rewrite /PS_derive.
  have H2 : is_lim_seq (fun n => INR (S n) / x * (y/x) ^ n) 0.
    apply ex_series_lim_0.
    apply ex_series_Rabs.
    apply CV_disk_DAlembert with 1.
    move => n.
    apply Rgt_not_eq, Rdiv_lt_0_compat.
    by apply lt_0_INR, lt_O_Sn.
    apply Rlt_trans with y ; by apply Hy.
    apply is_lim_seq_spec.
    move => eps.
    case: (nfloor_ex (/eps)) => [ | N HN].
    by apply Rlt_le, Rinv_0_lt_compat, eps.
    exists (S N) => n Hn.
    apply Rabs_lt_between'.
    replace (INR (S (S n)) / x / (INR (S n) / x))
      with (INR (S (S n)) / (INR (S n)))
      by (field ; split ; [apply Rgt_not_eq, Rlt_trans with y ; by apply Hy |
       by apply Rgt_not_eq, lt_0_INR, lt_O_Sn]).
    rewrite Rabs_pos_eq.
    split.
    apply Rlt_div_r.
    by apply lt_0_INR, lt_O_Sn.
    rewrite ?S_INR Rminus_lt_0 ; ring_simplify.
    rewrite Rplus_assoc.
    apply Rplus_le_lt_0_compat.
    apply Rmult_le_pos.
    by apply (le_INR O), le_O_n.
    by apply Rlt_le, eps.
    by apply Rle_lt_0_plus_1, Rlt_le, eps.
    apply Rlt_div_l.
    by apply lt_0_INR, lt_O_Sn.
    rewrite ?S_INR Rminus_lt_0 ; ring_simplify.
    rewrite /Rminus Rplus_assoc -/(Rminus eps 1).
    rewrite -(Ropp_involutive (eps-1)) -Rminus_lt_0 Ropp_minus_distr'.
    apply Rlt_trans with 1.
    apply Rminus_lt_0 ; ring_simplify ; by apply eps.
    replace 1 with (eps*/eps) by (field ; apply Rgt_not_eq, eps).
    apply Rmult_lt_compat_l.
    by apply eps.
    apply Rlt_le_trans with (1 := proj2 HN).
    rewrite -S_INR ; by apply le_INR.
    apply Rlt_le, Rdiv_lt_0_compat ; by apply lt_0_INR, lt_O_Sn.
    right ; split.
    by apply Rgt_not_eq, Rlt_0_1.
    rewrite Rinv_1 Rabs_pos_eq.
    apply -> Rdiv_lt_1.
    by apply Hy.
    apply Rlt_trans with y ; by apply Hy.
    apply Rlt_le, Rdiv_lt_0_compat.
    by apply Hy.
    apply Rlt_trans with y ; by apply Hy.
    apply is_lim_seq_spec in H2.
    case: (H2 (mkposreal _ (Rlt_0_1))) ;
    simpl pos => {H2} N HN.
    set My := fix f n := match n with
      | O => 1
      | S n => Rmax (Rabs (INR (S n) / x * (y / x) ^ n)) (f n)
    end.
    exists (M * My N) => n.
    replace (INR (S n) * a (S n) * y ^ n)
      with ((a (S n) * x ^ (S n)) * (INR (S n) /x * (y / x) ^ n))
      by (rewrite /pow -/pow ; apply Rminus_diag_uniq ; field_simplify ;
      [rewrite ?Rdiv_1 | apply Rgt_not_eq, Rlt_trans with y ; by apply Hy ] ;
      rewrite ?Rmult_assoc -(Rmult_minus_distr_l (a (S n))) ;
      apply Rmult_eq_0_compat_l ;
      rewrite Rmult_comm Rmult_assoc -(Rmult_minus_distr_l (INR (S n))) ;
      apply Rmult_eq_0_compat_l, Rminus_diag_eq ;
      elim: n => /= [ | n IH] ; [ring
      | rewrite -IH ; field ; apply Rgt_not_eq, Rlt_trans with y ; by apply Hy]).
    rewrite Rabs_mult ; apply Rmult_le_compat.
    by apply Rabs_pos.
    by apply Rabs_pos.
    by apply Hx.
    case: (le_lt_dec N n) => Hn.
    apply Rle_trans with 1.
    move: (HN n Hn) ; rewrite Rminus_0_r ; by apply Rlt_le.
    move: (HN n Hn) => {HN Hn} ;
    elim: N => [ | N IH] H2.
    simpl ; by apply Rle_refl.
    apply Rle_trans with (1 := IH H2) ;
    rewrite /My -/My ; by apply Rmax_r.
    elim: N n Hn {HN} => [ | N IH] n Hn.
    by apply lt_n_O in Hn.
    apply le_S_n in Hn ; case: (le_lt_eq_dec _ _ Hn) => {Hn} Hn.
    apply Rle_trans with (2 := Rmax_r _ (My N)) ; by apply IH.
    rewrite Hn ; by apply (Rmax_l _ (My N)).
Qed.

Lemma is_derive_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> is_derive (PSeries a) x (PSeries (PS_derive a) x).
Proof.
  move => Hx.

  case: (CV_radius_Reals_2 _ _ Hx) => r0 Hr0 ;
  rewrite -CV_radius_derive in Hx ;
  case: (CV_radius_Reals_2 _ _ Hx) => r1 Hr1 ;
  rewrite CV_radius_derive in Hx.
  apply CVU_dom_Reals in Hr0 ;
  apply CVU_dom_Reals in Hr1.
  have Hr : 0 < (Rmin r0 r1).
    apply Rmin_case.
    by apply r0.
    by apply r1.

  set D := (Boule x (mkposreal _ Hr)).

  assert (Ho : open D).
    move => y Hy.
    apply Rabs_lt_between' in Hy ; simpl in Hy.
    have H : 0 < Rmin ((x+Rmin r0 r1)-y) (y-(x-Rmin r0 r1)).
    apply Rmin_case.
    rewrite -(Rminus_eq_0 y) ; by apply Rplus_lt_compat_r, Hy.
    rewrite -(Rminus_eq_0 ((x-Rmin r0 r1))) /Rminus ;
    by apply Rplus_lt_compat_r , Hy.
    exists (mkposreal _ H) => /= z Hz.
    apply Rabs_lt_between' ; split ; apply (Rplus_lt_reg_l (-y)) ; simpl.
    apply Ropp_lt_cancel.
    apply Rle_lt_trans with (1 := Rabs_maj2 _).
    rewrite Ropp_plus_distr ?Ropp_involutive (Rplus_comm (-y)).
    apply Rlt_le_trans with (1 := Hz).
    exact: Rmin_r.
    apply Rle_lt_trans with (1 := Rle_abs _).
    rewrite ?(Rplus_comm (-y)).
    apply Rlt_le_trans with (1 := Hz).
    exact: Rmin_l.

  have Hc : is_connected D.
    move => x0 y z Hx0 Hy Hx0yz.
    rewrite /D.
    case: Hx0yz => H1 H2.
    apply (Rplus_le_compat_r (-x)) in H1.
    apply (Rplus_le_compat_r (-x)) in H2.
    move: (conj H1 H2) => {H1 H2} Hxyz.
    apply Rabs_le_between_Rmax in Hxyz.
    apply Rle_lt_trans with (1 := Hxyz) => /=.
    apply Rmax_case.
    apply Rle_lt_trans with (1 := Rle_abs _).
    exact: Hy.
    apply Rle_lt_trans with (1 := Rabs_maj2 _).
    exact: Hx0.

  have Hfn : CVU_dom
    (fun (n : nat) (y : R) => sum_f_R0 (fun k : nat => a k * y ^ k) n) D.
    apply CVU_dom_include with (Boule x r0).
    move => y Hy.
    by apply Rlt_le_trans with (1 := Hy), Rmin_l.
    exact: Hr0.

  have Idn : (forall (n : nat) (x : R), (0 < n)%nat ->
    is_derive (fun (y : R) =>
      sum_f_R0 (fun k : nat => a k * y ^ k) n) x
      (sum_f_R0 (fun k : nat => (PS_derive a) k * x ^ k) (pred n))).
    case => [ y Hn | n y _ ].
    by apply lt_irrefl in Hn.
    elim: n => [ | n] ; simpl pred ; rewrite /sum_f_R0 -/sum_f_R0.
    replace (PS_derive a 0 * y ^ 0)
      with (0 + a 1%nat * (1 * 1 + y * 0))
      by (rewrite /PS_derive /= ; ring).
    apply derivable_pt_lim_plus.
    simpl ; by apply derivable_pt_lim_const.
    apply derivable_pt_lim_scal, derivable_pt_lim_mult.
    by apply derivable_pt_lim_id.
    by apply derivable_pt_lim_const.
    move => IH ; apply derivable_pt_lim_plus.
    exact: IH.
    rewrite /PS_derive.
    replace (INR (S (S n)) * a (S (S n)) * y ^ S n)
      with (a (S (S n)) * (INR (S (S n)) * y^S n))
      by ring.
    by apply derivable_pt_lim_scal, derivable_pt_lim_pow.

  have Edn : (forall (n : nat) (x : R), D x ->
    ex_derive (fun (y : R) =>
      sum_f_R0 (fun k : nat => a k * y ^ k) n) x).
    case => [ | n] y Hy.
    exists 0 => /= ; by apply derivable_pt_lim_const.
    exists (sum_f_R0 (fun k : nat => PS_derive a k * y ^ k) (pred (S n))).
    apply (Idn (S n) y).
    by apply lt_O_Sn.

  have Cdn : (forall (n : nat) (x : R), D x ->
    continuity_pt
      (Derive ((fun (n0 : nat) (y : R) =>
        sum_f_R0 (fun k : nat => a k * y ^ k) n0) n)) x).
    have Cdn : (forall (n : nat) (x : R), D x ->
      continuity_pt (fun x => sum_f_R0 (fun k : nat => PS_derive a k * x ^ k) n) x).
      move => n y Hy.
      apply derivable_continuous_pt.
      elim: n => [ /= | n IH].
      exact: derivable_pt_const.
      apply derivable_pt_plus ; rewrite -/sum_f_R0.
      exact: IH.
      apply derivable_pt_scal, derivable_pt_pow.
    case => [ | n] y Hy.
    simpl ; by apply continuity_pt_const => z.
    move => e He ; case: (Cdn n y Hy e He) => {Cdn} d [Hd Cdn].
    destruct (Ho y Hy) as [d0 Hd0].
    have Hd1 : 0 < Rmin d d0.
      apply Rmin_case ; [exact: Hd | by apply d0].
    exists (mkposreal _ Hd1) ; split.
    exact: Hd1.
    move => z Hz ; simpl in Hz.
    rewrite (is_derive_unique _ _ _ (Idn (S n) z (lt_O_Sn _))).
    rewrite (is_derive_unique _ _ _ (Idn (S n) y (lt_O_Sn _))).
    apply (Cdn z) ; split.
    by apply Hz.
    apply Rlt_le_trans with (1 := proj2 Hz), Rmin_l.

  have Hdn : CVU_dom (fun (n : nat) (x : R) =>
          Derive
            ((fun (n0 : nat) (y : R) =>
              sum_f_R0 (fun k : nat => a k * y ^ k) n0) n) x) D.
    apply CVU_dom_include with (Boule x r1).
    move => y Hy.
    by apply Rlt_le_trans with (1 := Hy), Rmin_r.
    apply CVU_dom_cauchy ; apply CVU_dom_cauchy in Hr1.
    move => eps.
    case: (Hr1 eps) => {Hr1} N Hr1.
    exists (S N) => n m y Hy Hn Hm.
    case: n Hn => [ | n] Hn.
    by apply le_Sn_O in Hn.
    apply le_S_n in Hn.
    case: m Hm => [ | m] Hm.
    by apply le_Sn_O in Hm.
    apply le_S_n in Hm.
    rewrite (is_derive_unique _ _ _ (Idn (S n) y (lt_O_Sn _))).
    rewrite (is_derive_unique _ _ _ (Idn (S m) y (lt_O_Sn _))).
    by apply Hr1.

  have Hx' : D x.
    by rewrite /D /Boule /= Rminus_eq_0 Rabs_R0.
  have H := (CVU_Derive (fun n y => (sum_f_R0 (fun k : nat => a k * y ^ k)) n) D Ho Hc Hfn Edn Cdn Hdn x Hx').
  replace (PSeries (PS_derive a) x)
    with (real (Lim_seq
         (fun n : nat =>
          Derive (fun y : R => sum_f_R0 (fun k : nat => a k * y ^ k) n) x))).
  apply filterdiff_Reals.
  move/filterdiff_Reals: H ; apply filterdiff_ext => t.
  apply (f_equal real), Lim_seq_ext.
  intros n; apply sym_eq, sum_n_sum_f_R0.
  rewrite -Lim_seq_incr_1.
  apply (f_equal real), Lim_seq_ext => n.
  rewrite sum_n_sum_f_R0.
  apply is_derive_unique, Idn.
  by apply lt_O_Sn.
  move => y Hy.
  apply sym_eq.
  apply is_lim_seq_unique.
  apply is_lim_seq_spec.
  move => eps.
  case: (Hr1 eps (cond_pos eps)) => {Hr1} N Hr1.
  exists N => n Hn.
  rewrite -Rabs_Ropp Ropp_minus_distr'.
  by apply Hr1.
  move => y Hy.
  apply sym_eq.
  apply is_lim_seq_unique.
  apply is_lim_seq_spec.
  move => eps.
  case: (Hr0 eps (cond_pos eps)) => {Hr0} N Hr0.
  exists N => n Hn.
  rewrite -Rabs_Ropp Ropp_minus_distr'.
  by apply Hr0.
  move => y Hy.
  apply sym_eq.
  apply is_lim_seq_unique.
  apply is_lim_seq_spec.
  move => eps.
  case: (Hr1 eps (cond_pos eps)) => {Hr1} N Hr1.
  exists N => n Hn.
  rewrite -Rabs_Ropp Ropp_minus_distr'.
  by apply Hr1.
Qed.
Lemma ex_derive_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> ex_derive (PSeries a) x.
Proof.
  move => Hx ; exists (PSeries (PS_derive a) x).
  by apply is_derive_PSeries.
Qed.
Lemma Derive_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> Derive (PSeries a) x = PSeries (PS_derive a) x.
Proof.
  move => H.
  apply is_derive_unique.
  by apply is_derive_PSeries.
Qed.

Lemma ex_pseries_derive (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> ex_pseries (PS_derive a) x.
Proof.
  move => Hx.
  apply ex_series_Rabs; simpl.
  apply ex_series_ext with (fun n : nat => Rabs (PS_derive a n * x ^ n)).
  intros n; apply f_equal; rewrite pow_n_pow.
  apply Rmult_comm.
  apply CV_disk_inside.
  by rewrite CV_radius_derive.
Qed.

Definition PS_derive_n (n : nat) (a : nat -> R) :=
  (fun k => (INR (fact (k + n)%nat) / INR (fact k)) * a (k + n)%nat).

Lemma is_derive_n_PSeries (n : nat) (a : nat -> R) :
  forall x, Rbar_lt (Rabs x) (CV_radius a)
    -> is_derive_n (PSeries a) n x (PSeries (PS_derive_n n a) x).
Proof.
  elim: n => [ | n IH] x Hx.
  simpl ; rewrite /PS_derive_n /=.
  apply PSeries_ext => n.
  rewrite -plus_n_O.
  field.
  apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  simpl ; rewrite /PS_derive_n /=.
  apply filterdiff_Reals.
  eapply filterdiff_ext_lin.
  apply @filterdiff_ext_locally
    with (PSeries (fun k : nat => INR (fact (k + n)) / INR (fact k) * a (k + n)%nat)).
  case Ha : (CV_radius a) => [cva | | ].
  move: (Hx) ; rewrite Ha ; move/Rminus_lt_0 => Hx0.
  exists (mkposreal _ Hx0) => /= y Hy.
  apply sym_eq.
  apply is_derive_n_unique.
  apply IH.
  rewrite Ha /=.
  replace y with ((y-x) + x) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  by apply Rlt_minus_r.
  exists (mkposreal _ Rlt_0_1) => /= y Hy.
  apply sym_eq.
  apply is_derive_n_unique.
  apply IH.
  by rewrite Ha /=.
  by rewrite Ha in Hx.
  apply filterdiff_Reals.
  apply is_derive_PSeries.
  replace (CV_radius (fun k : nat => INR (fact (k + n)) / INR (fact k) * a (k + n)%nat))
    with (CV_radius a).
  by apply Hx.
  elim: n {IH} => [ | n IH].
  apply CV_radius_ext => n.
  rewrite -plus_n_O.
  field.
  apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  rewrite IH.
  rewrite -CV_radius_derive.
  apply CV_radius_ext => k.
  rewrite /PS_derive.
  rewrite -plus_n_Sm plus_Sn_m /fact -/fact ?mult_INR ?S_INR.
  field.
  rewrite -S_INR ; split ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  apply (lt_INR O), lt_O_Sn.
  move => /= y.
  apply f_equal.
  apply PSeries_ext.
  move => k ; rewrite /PS_derive.
  rewrite -plus_n_Sm plus_Sn_m /fact -/fact ?mult_INR ?S_INR.
  field.
  rewrite -S_INR ; split ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  apply (lt_INR O), lt_O_Sn.
Qed.
Lemma ex_derive_n_PSeries (n : nat) (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> ex_derive_n (PSeries a) n x.
Proof.
  elim: n a x => [ | n IH] a x Hx.
  by simpl.
  simpl.
  exists (PSeries (PS_derive_n (S n) a) x).
  by apply (is_derive_n_PSeries (S n)).
Qed.
Lemma Derive_n_PSeries (n : nat) (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_radius a)
    -> Derive_n (PSeries a) n x = PSeries (PS_derive_n n a) x.
Proof.
  move => H.
  apply is_derive_n_unique.
  by apply is_derive_n_PSeries.
Qed.

Lemma CV_radius_derive_n (n : nat) (a : nat -> R) :
  CV_radius (PS_derive_n n a) = CV_radius a.
Proof.
  elim: n a => [ | n IH] /= a.
  apply CV_radius_ext.
  move => k ; rewrite /PS_derive_n /=.
  rewrite plus_0_r ; field.
  by apply INR_fact_neq_0.
  rewrite -(CV_radius_derive a).
  rewrite -(IH (PS_derive a)).
  apply CV_radius_ext.
  move => k ; rewrite /PS_derive_n /PS_derive.
  rewrite -plus_n_Sm /fact -/fact mult_INR ; field.
  by apply INR_fact_neq_0.
Qed.

Lemma Derive_n_coef (a : nat -> R) (n : nat) :
  Rbar_lt (Finite 0) (CV_radius a)
    -> Derive_n (PSeries a) n 0 = a n * (INR (fact n)).
Proof.
  elim: n a => [ | n IH] a Ha.
  rewrite Rmult_1_r.
  rewrite /= /PSeries /Series -(Lim_seq_ext (fun _ => a O)).
  by rewrite Lim_seq_const.
  elim => /= [ | n IH].
  ring.
  rewrite -IH /plus /= ; ring.
  simpl Derive_n.
  replace (Derive (Derive_n (PSeries a) n) 0)
    with (Derive_n (PSeries (PS_derive a)) n 0).
  rewrite IH.
  rewrite /fact -/fact mult_INR /PS_derive ; ring.
  by rewrite CV_radius_derive.
  transitivity (Derive_n (Derive (PSeries a)) n 0).
  apply Derive_n_ext_loc.
  case: (Rbar_eq_dec (CV_radius a) p_infty) => H.
  exists (mkposreal _ Rlt_0_1) => /= x Hx.
  apply sym_eq ; apply Derive_PSeries.
  by rewrite H.
  have Hc : 0 < real (CV_radius a).
    case: (CV_radius a) Ha H => /= [c | | ] Ha H ; by [].
  exists (mkposreal _ Hc) => /= x Hx.
  apply sym_eq ; apply Derive_PSeries.
  case: (CV_radius a) Hx Ha => /= [c | | ] Hx Ha //.
  by rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= -/(Rminus _ _) Rminus_0_r in Hx.
  move: (Derive_n_comp (PSeries a) n 1%nat 0) => /= ->.
  by replace (n+1)%nat with (S n) by ring.
Qed.

Lemma PSeries_ext_recip (a b : nat -> R) (n : nat) :
  Rbar_lt (Finite 0) (CV_radius a) -> Rbar_lt (Finite 0) (CV_radius b)
  -> (forall x, Rbar_lt (Finite (Rabs x)) (CV_radius a) -> PSeries a x = PSeries b x)
    -> a n = b n.
Proof.
  move => Ha Hb Hab.
  have H : a n * (INR (fact n)) = b n * (INR (fact n)).
  rewrite -?Derive_n_coef.
  case: (Rbar_eq_dec (CV_radius a) p_infty) => H.
  apply Derive_n_ext => x.
  apply Hab ; by rewrite H.
  apply Derive_n_ext_loc.
  have Hc : 0 < real (CV_radius a).
    case: (CV_radius a) Ha H => /= [c | | ] Ha H ; by [].
  exists (mkposreal _ Hc) => /= x Hx.
  apply Hab.
  case: (CV_radius a) Hx Ha => /= [c | | ] Hx Ha //.
  by rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= -/(Rminus _ _) Rminus_0_r in Hx.
  exact: Hb.
  exact: Ha.
  replace (a n) with ((a n * INR (fact n)) / (INR (fact n))).
  rewrite H ; field ; exact: INR_fact_neq_0.
  field ; exact: INR_fact_neq_0.
Qed.

Lemma mk_pseries (f : R -> R) (M : R) (r : Rbar) :
  (forall n x, Rbar_lt (Finite (Rabs x)) r
    -> (ex_derive_n f n x) /\ Rabs (Derive_n f n x) <= M)
  -> forall x, Rbar_lt (Finite (Rabs x)) r
    -> is_pseries (fun n => Derive_n f n 0 / INR (fact n))  x (f x).
Proof.
  move => Hd x Hx.

  wlog: r Hx Hd /(Finite (real r) = r) => [Hw | Hr].
    case: r Hx Hd => /= [r | | ] Hx Hd.
    by apply (Hw (Finite r)).
    apply (Hw (Finite (Rabs x+1))).
    simpl ; exact: Rlt_plus_1.
    move => n y Hy ; by apply Hd.
    by [].
    by [].
    rewrite -Hr in Hx Hd.
    move: (real r) Hx Hd => /= {r Hr} r Hx Hd.

  wlog: x Hx f Hd / (0 < x) => [Hw | Hx'].
    case: (total_order_T 0 x) => Hx'.
    case: Hx' => Hx'.
    by apply Hw.
    rewrite -Hx'.
    replace (f 0) with (Derive_n f O 0 / INR (fact O))
      by (simpl ; field).
    apply @is_pseries_0.
    rewrite -Rabs_Ropp in Hx.
    suff Hf : (forall (n : nat) (x : R),
      ((Rabs x)) < r ->
      ex_derive_n (fun x0 : R => f (- x0)) n x /\
      Rabs (Derive_n (fun x0 : R => f (- x0)) n x) <= M).

   move: (Hw _ Hx (fun x => f (-x)) Hf (Ropp_0_gt_lt_contravar _ Hx')) => {Hw} Hw.
   rewrite Ropp_involutive in Hw.

   apply is_series_ext with (2:=Hw).
   intros n; rewrite Derive_n_comp_opp; simpl.
   rewrite /scal /= /mult /=.
   apply trans_eq with ((pow_n (- x) n * (-1) ^ n) * 
     (Derive_n f n (- 0) / INR (fact n)));[unfold Rdiv; ring|idtac].
   rewrite Ropp_0.
   apply f_equal2; try reflexivity.
   clear; induction n; simpl.
   apply Rmult_1_l.
   rewrite /mult /=.
   rewrite <- IHn; ring.
   rewrite Ropp_0 ;
    exists (mkposreal r (Rle_lt_trans _ _ _ (Rabs_pos _) Hx)) => /= y Hy k Hk.
   rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= -/(Rminus _ _) Rminus_0_r in Hy.
   by apply (Hd k).
   move => {x Hx Hx'} n x Hx.
   rewrite Derive_n_comp_opp.
   split.
   apply ex_derive_n_comp_opp.

    apply Rabs_lt_between in Hx.
    case: Hx => Hx1 Hx2.
    apply Rminus_lt_0 in Hx1.
    apply Rminus_lt_0 in Hx2.
    have Hx := Rmin_pos _ _ Hx1 Hx2 => {Hx1 Hx2}.
    exists (mkposreal _ Hx) => /= y Hy k Hk.
    rewrite /ball /= /AbsRing_ball /= in Hy.
    apply Rabs_lt_between' in Hy.
    rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
    case: Hy => Hy1 Hy2.
    apply Rle_lt_trans with (1 := Rmax_r _ _) in Hy1.
    ring_simplify in Hy1.
    apply Rlt_le_trans with (2 := Rmin_l _ _) in Hy2.
    ring_simplify in Hy2.
    apply (Hd k y).
    apply Rabs_lt_between.
    by split.

    rewrite Rabs_mult -RPow_abs Rabs_Ropp Rabs_R1 pow1 Rmult_1_l.
    apply Hd.
    by rewrite Rabs_Ropp.

    apply Rabs_lt_between in Hx.
    case: Hx => Hx1 Hx2.
    apply Rminus_lt_0 in Hx1.
    apply Rminus_lt_0 in Hx2.
    have Hx := Rmin_pos _ _ Hx1 Hx2 => {Hx1 Hx2}.
    exists (mkposreal _ Hx) => /= y Hy k Hk.
    rewrite /ball /= /AbsRing_ball /= in Hy.
    apply Rabs_lt_between' in Hy.
    rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l Rplus_min_distr_l in Hy.
    case: Hy => Hy1 Hy2.
    apply Rle_lt_trans with (1 := Rmax_r _ _) in Hy1.
    ring_simplify in Hy1.
    apply Rlt_le_trans with (2 := Rmin_l _ _) in Hy2.
    ring_simplify in Hy2.
    apply (Hd k y).
    apply Rabs_lt_between.
    by split.

  (* ? *)
  move => P [eps Heps].
  have : exists N, forall n, (N <= n)%nat -> r ^ (S n) * M / INR (fact (S n)) < eps.
    have H : is_lim_seq (fun n => r ^ n * M / INR (fact n)) 0.
    case: (Rlt_dec 0 M) => H.
    have H0 : forall n : nat, 0 < r ^ n * M / INR (fact n).
      move => n.
      apply Rdiv_lt_0_compat.
      apply Rmult_lt_0_compat.
      apply pow_lt.
      apply Rle_lt_trans with (2 := Hx), Rabs_pos.
      exact: H.
      exact: INR_fact_lt_0.

    apply ex_series_lim_0, ex_series_Rabs, ex_series_DAlembert with 0.
    exact: Rlt_0_1.
    move => n ; apply Rgt_not_eq, Rlt_gt, H0.

    apply is_lim_seq_ext with (fun n => r / INR (S n)).
    move => n ; rewrite Rabs_pos_eq.
    rewrite /fact -/fact /pow -/pow ?mult_INR ; field.
    repeat split ; apply Rgt_not_eq, Rlt_gt.
    exact: INR_fact_lt_0.
    by apply (lt_INR O), lt_O_Sn.
    exact: H.
    apply pow_lt, Rle_lt_trans with (Rabs x), Hx ; by apply Rabs_pos.
    apply Rlt_le, Rdiv_lt_0_compat ; by apply H0.
    rewrite -(Rmult_0_r r) ; apply (is_lim_seq_scal_l _ _ 0) => //.
    apply (is_lim_seq_incr_1 (fun n => / INR n)).
    replace (Finite 0) with (Rbar_inv p_infty) by auto.
    apply is_lim_seq_inv.
    by apply is_lim_seq_INR.
    by [].
    apply Rnot_lt_le in H ; case: H => H.
    contradict H.
    apply Rle_not_lt.
    apply Rle_trans with (Rabs (Derive_n f O x)).
    by apply Rabs_pos.
    by apply Hd.
    rewrite H.
    apply is_lim_seq_ext with (fun _ => 0).
    move => n ; rewrite /Rdiv ; ring.
    exact: is_lim_seq_const.
    apply is_lim_seq_incr_1 in H.
    apply is_lim_seq_spec in H.
    case: (H eps) => {H} N H.
    exists N => n Hn.
    apply Rle_lt_trans with (2 := H n Hn).
    rewrite Rminus_0_r.
    exact: Rle_abs.

  case => N HN.
  exists N => n Hn.
  apply Heps.

  case: (Taylor_Lagrange f n 0 x).
    by apply Hx'.
    move => t Ht k Hk.
    apply Hd.
    rewrite Rabs_right.
    apply Rle_lt_trans with (1 := proj2 Ht).
    by apply Rle_lt_trans with (1 := Rle_abs _), Hx.
    by apply Rle_ge, Ht.
  move => y [Hy ->].
  simpl ball.
  rewrite Rminus_0_r.
  rewrite (sum_n_ext _ (fun m : nat => x ^ m / INR (fact m) * Derive_n f m 0)).
  rewrite sum_n_sum_f_R0.
  apply Rle_lt_trans with (2 := HN n Hn).
  replace (r ^ S n * M / INR (fact (S n)))
    with ((r^S n / INR (fact (S n))) * M)
    by (rewrite /Rdiv ; ring).
  change minus with Rminus.
  ring_simplify (sum_f_R0 (fun m : nat => x ^ m / INR (fact m) * Derive_n f m 0) n
    - (sum_f_R0 (fun m : nat => x ^ m / INR (fact m) * Derive_n f m 0) n +
    x ^ S n / INR (fact (S n)) * Derive_n f (S n) y)).
  change abs with Rabs.
  rewrite Rabs_mult Rabs_Ropp.
  apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  rewrite Rabs_div.
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rlt_le, Rinv_0_lt_compat.
  apply Rabs_pos_lt.
  exact: INR_fact_neq_0.
  rewrite -RPow_abs.
  apply pow_incr ; split.
  apply Rabs_pos.
  by apply Rlt_le.
  apply Rle_Rinv.
  exact: (INR_fact_lt_0 (S n)).
  apply Rabs_pos_lt, INR_fact_neq_0.
  apply Rle_abs.
  apply INR_fact_neq_0.
  apply Hd.
  apply Rlt_trans with (2 := Hx).
  rewrite ?Rabs_pos_eq.
  by apply Hy.
  apply Rlt_le, Hx'.
  apply Rlt_le, Hy.
  intros m; rewrite pow_n_pow.
  rewrite /scal /= /mult /= /Rdiv ; ring.
Qed.

(** ** Riemann integrability *)

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
  by apply H.
  search_RInt.
  apply is_RInt_Derive.
  move => y Hy.
  apply ex_derive_PSeries.
  rewrite CV_radius_Int.
  by apply H.
  move => y Hy.
  apply continuity_pt_ext_loc with (PSeries a).

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
  apply PSeries_continuity.
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
