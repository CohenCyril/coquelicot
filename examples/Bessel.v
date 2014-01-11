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
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Limit.
Require Import AutoDerive.

(** An example of how to use power series *)

Definition Bessel1_seq (n k : nat) :=
  (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).

Lemma CV_Bessel1 (n : nat) :
  CV_radius (Bessel1_seq n) = p_infty.
Proof.
  apply CV_radius_infinite_DAlembert.
    move => k.
    rewrite /Bessel1_seq.
    apply Rmult_integral_contrapositive_currified.
    apply pow_nonzero, Ropp_neq_0_compat, R1_neq_R0.
    apply Rinv_neq_0_compat, Rmult_integral_contrapositive_currified ;
    apply INR_fact_neq_0.
  apply is_lim_seq_ext with (fun p => / (INR (S p) * INR (S (n + p)))).
  move => p ; rewrite /Bessel1_seq -plus_n_Sm /fact -/fact !mult_INR.
  simpl ((-1)^(S p)).
  field_simplify (-1 * (-1) ^ p /
    (INR (S p) * INR (fact p) * (INR (S (n + p)) * INR (fact (n + p)))) /
    ((-1) ^ p / (INR (fact p) * INR (fact (n + p))))).
  rewrite Rabs_div.
  rewrite Rabs_Ropp Rabs_R1 /Rdiv Rmult_1_l Rabs_pos_eq.
  by [].
  apply Rmult_le_pos ; apply pos_INR.
  apply Rgt_not_eq, Rmult_lt_0_compat ;
  apply lt_0_INR, lt_O_Sn.
  repeat split.
  by apply INR_fact_neq_0.
  by apply INR_fact_neq_0.
  by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
  by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
  by apply pow_nonzero, Rlt_not_eq, (IZR_lt (-1) 0).
  replace (Finite 0) with (Rbar_inv p_infty) by auto.
  apply is_lim_seq_inv.
  eapply is_lim_seq_mult.
  apply -> is_lim_seq_incr_1.
  by apply is_lim_seq_INR.
  apply is_lim_seq_ext with (fun k => INR (k + S n)).
  intros k.
  by rewrite (Plus.plus_comm n k) plus_n_Sm.
  apply is_lim_seq_incr_n.
  by apply is_lim_seq_INR.
  by [].
  by [].
Qed.

Lemma ex_Bessel1 (n : nat) (x : R) :
  ex_pseries (Bessel1_seq n) x.
Proof.
  apply CV_radius_inside.
  by rewrite CV_Bessel1.
Qed.

Definition Bessel1 (n : nat) (x : R) :=
  (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma is_derive_Bessel1 (n : nat) (x : R) :
  is_derive (Bessel1 n) x
      ((x / 2) ^ S n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2)
      + (INR n)/2 * (x / 2) ^ pred n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)).
Proof.
  rewrite /Bessel1.
  auto_derive.
  repeat split.
  apply ex_derive_PSeries.
  by rewrite CV_Bessel1.
  rewrite Derive_PSeries.
  rewrite /Rdiv ; simpl ; field.
  by rewrite CV_Bessel1.
Qed.

Lemma is_derive_2_Bessel1 (n : nat) (x : R) :
  is_derive_n (Bessel1 n) 2 x
    (((x/2)^(S (S n)) * PSeries (PS_derive (PS_derive (Bessel1_seq n))) ((x / 2) ^ 2))
    + ((INR (2*n+1)/2) * (x/2)^n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2))
    + (INR (n * pred n) / 4 * (x / 2) ^ pred (pred n) * PSeries (Bessel1_seq n) ((x / 2) ^ 2))).
Proof.
  rewrite plus_INR ?mult_INR ; simpl INR.
  apply filterdiff_Reals.
  apply filterdiff_ext
    with (fun x => ((x / 2) ^ S n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2)
    + (INR n)/2 * (x / 2) ^ pred n * PSeries (Bessel1_seq n) ((x / 2) ^ 2))).
  move => y ;
  by apply sym_eq, is_derive_unique, is_derive_Bessel1.
  apply filterdiff_Reals.
  auto_derive.
  repeat split.
  apply ex_derive_PSeries.
  by rewrite CV_radius_derive CV_Bessel1.
  apply ex_derive_PSeries.
  by rewrite CV_Bessel1.
  rewrite ?Derive_PSeries.
  case: n => [ | n] ; rewrite ?S_INR /Rdiv /= ;
  simpl ; field.
  by rewrite CV_Bessel1.
  by rewrite CV_radius_derive CV_Bessel1.
Qed.

Lemma Bessel1_correct (n : nat) (x : R) :
  x^2 * Derive_n (Bessel1 n) 2 x + x * Derive (Bessel1 n) x + (x^2 - (INR n)^2) * Bessel1 n x = 0.
Proof.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) ;
  rewrite /Derive_n (is_derive_unique _ _ _ (is_derive_2_Bessel1 _ _)) ;
  rewrite /Bessel1 plus_INR ?mult_INR ; simpl INR.
  set y := x/2 ; replace x with (2 * y) by (unfold y ; field).

  replace ((2 * y) ^ 2 *
    (y ^ S (S n) * PSeries (PS_derive (PS_derive (Bessel1_seq n))) (y ^ 2) +
    (2 * INR n + 1) / 2 * y ^ n * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2) +
    INR n * INR (pred n) / 4 * y ^ pred (pred n) *
    PSeries (Bessel1_seq n) (y ^ 2)) +
    2 * y *
    (y ^ S n * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2) +
    INR n / 2 * y ^ pred n * PSeries (Bessel1_seq n) (y ^ 2)) +
    ((2 * y) ^ 2 - INR n ^ 2) * (y ^ n * PSeries (Bessel1_seq n) (y ^ 2)))
  with (4 * y^S (S n) * (y^2 * PSeries (PS_derive (PS_derive (Bessel1_seq n))) (y ^ 2)
    + (INR n + 1) * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2)
    + PSeries (Bessel1_seq n) (y ^ 2))).
  Focus 2.
  case: n => [ | n] ; rewrite ?S_INR ; simpl INR ; simpl pred ; simpl pow ;
  field_simplify.
  field.
  case: n => [ | n] ; rewrite ?S_INR ; simpl INR ; simpl pred ; simpl pow ;
  field_simplify.
  field.
  field.

  apply Rmult_eq_0_compat_l.

  rewrite -PSeries_incr_1 -PSeries_scal -?PSeries_plus.

  unfold PS_derive, PS_incr_1, PS_scal, PS_plus.
  rewrite -(PSeries_const_0 (y^2)).
  apply PSeries_ext.
  case => [ | p] ; rewrite /Bessel1_seq ;
  rewrite -?plus_n_Sm ?plus_0_r /fact -/fact ?mult_INR ?S_INR ?plus_INR ; simpl INR ; simpl pow ;
  rewrite ?Rplus_0_l ?Rmult_1_l.
  simpl; field.
  split ; rewrite -?S_INR ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  simpl; field.
  repeat split ; rewrite -?plus_INR -?S_INR ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  by apply (lt_INR 0), lt_O_Sn.
  by apply (lt_INR 0), lt_O_Sn.

  apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  rewrite /Rbar_min ; case: Rbar_le_dec => _.
  by rewrite CV_radius_incr_1 ?CV_radius_derive CV_Bessel1.
  apply Rbar_lt_le_trans with (2 := CV_radius_scal _ _).
  by rewrite CV_radius_derive CV_Bessel1.
  by apply ex_Bessel1.
  apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
  by rewrite CV_radius_incr_1 ?CV_radius_derive CV_Bessel1.
  apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
  apply Rbar_lt_le_trans with (2 := CV_radius_scal _ _).
  by rewrite CV_radius_derive CV_Bessel1.
Qed.

Lemma Bessel1_equality_1 (n : nat) (x : R) : x <> 0
  -> Bessel1 (S n)%nat x = INR n * Bessel1 n x / x - Derive (Bessel1 n) x.
Proof.
  move => Hx.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
  set y := (x / 2).
  replace x with (2 * y) by (unfold y ; field).

(* Supprimer les PSeries *)
  have Hy : y <> 0.
  unfold y ; contradict Hx.
  replace x with (2 * (x/2)) by field ; rewrite Hx ; ring.
  case: n => [ | n] ; simpl ; field_simplify => // ; rewrite Rdiv_1 -/(pow _ 2).
(* * cas n = 0 *)
  replace (- 2 * y ^ 2 * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2) / (2 * y))
    with (y * ((-1) * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2)))
    by (simpl ; unfold y ; field => //).
  apply f_equal.
  rewrite -PSeries_scal.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal /PS_derive plus_0_l.
  replace (1+k)%nat with (S k) by ring.
  rewrite /fact -/fact mult_INR /pow -/pow.
  simpl; field ; split.
  exact: INR_fact_neq_0.
  replace (match k with
    | 0%nat => 1
    | S _ => INR k + 1
   end) with (INR (S k)) by reflexivity.
  by apply not_0_INR, not_eq_sym, O_S.
(* * cas S n *)
  replace (S n + 1)%nat with (S(S n)) by ring.
  replace (-2 * y ^ 2 * y ^ n * PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2) / 2)
    with (y^2 * y^n * (((-1)* PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2))))
    by (unfold y ; field => //).
  apply f_equal.
  rewrite -PSeries_scal.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal /PS_derive -?plus_n_Sm ?plus_Sn_m.
  rewrite /pow -/pow /fact -/fact ?mult_INR ?S_INR plus_INR.
  simpl; field.
  rewrite -plus_INR -?S_INR.
  repeat split ;
  try by [exact: INR_fact_neq_0 | apply not_0_INR, not_eq_sym, O_S].
Qed.

Lemma Bessel1_equality_2 (n : nat) (x : R) : (0 < n)%nat -> x<>0
  -> Bessel1 (S n)%nat x + Bessel1 (pred n)%nat x = (2*INR n)/x * Bessel1 n x.
Proof.
  case: n => [ | n] Hn Hx.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl pred.
  rewrite /Bessel1 S_INR.
  replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) +
      (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2))
    with ((x/2)^n *
      ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) +
      PSeries (Bessel1_seq n) ((x / 2) ^ 2)))
    by (simpl ; ring).
  replace (2 * (INR n + 1) / x *
      ((x / 2) ^ S n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    with ((x/2)^n * ((INR n + 1) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    by (simpl ; field ; exact: Hx).
  apply f_equal.
  rewrite -PSeries_incr_1 -PSeries_scal -PSeries_plus.
Focus 2. (* ex_pseries (PS_incr_1 (Bessel1_seq (S (S n))) (S (S n))) (x / 2) *)
  by apply ex_pseries_incr_1, ex_Bessel1.
Focus 2. (* ex_pseries (PS_incr_n (Bessel1_seq n) n) (x / 2) *)
  by apply ex_Bessel1.
  apply PSeries_ext => k.
(* egalité *)
  rewrite /PS_plus /PS_scal /PS_incr_1 /Bessel1_seq ;
  case: k => [ | k] ;
  rewrite ?plus_0_r -?plus_n_Sm ?plus_Sn_m
    /fact -/fact ?mult_INR ?S_INR ?plus_INR /=.
  field.
  rewrite -?S_INR ; split ;
  by [apply not_0_INR, sym_not_eq, O_S | apply INR_fact_neq_0].
  field ;
  rewrite -?plus_INR -?S_INR ; repeat split ;
  by [apply INR_fact_neq_0 | apply not_0_INR, sym_not_eq, O_S].
Qed.

Lemma Bessel1_equality_3 (n : nat) (x : R) : (0 < n)%nat ->
  Bessel1 (S n)%nat x - Bessel1 (pred n)%nat x = - 2 * Derive (Bessel1 n) x.
Proof.
  move => Hn.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
  case: n Hn => [ | n] Hn.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl pred.
  replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) -
      (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2))
    with ((x/2)^n *
      ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) -
      PSeries (Bessel1_seq n) ((x / 2) ^ 2)))
    by (simpl ; ring).
  replace (-2 *((x / 2) ^ S (S n) * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2) +
      INR (S n) / 2 * (x / 2) ^ n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    with ((x/2)^n * (-2 * ((x/2)^2  * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2)) -
      INR (S n) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    by (rewrite S_INR ; simpl ; field).
  set y := (x / 2).
  apply f_equal.
  rewrite -?PSeries_incr_1 -?PSeries_scal -?PSeries_minus.
  apply PSeries_ext => k.
  rewrite  /PS_minus /PS_incr_1 /PS_scal /PS_derive /Bessel1_seq.
  case: k => [ | k] ; rewrite -?plus_n_Sm ?plus_Sn_m /fact -/fact ?mult_INR ?S_INR -?plus_n_O ?plus_INR /= ;
  field ; rewrite -?plus_INR -?S_INR.
  split ; (apply INR_fact_neq_0 || apply not_0_INR, sym_not_eq, O_S).
  repeat split ; (apply INR_fact_neq_0 || apply not_0_INR, sym_not_eq, O_S).
  apply @ex_pseries_scal, @ex_pseries_incr_1, ex_pseries_derive.
  by apply Rmult_comm.
  by rewrite CV_Bessel1.
  apply ex_pseries_scal, ex_Bessel1.
  by apply Rmult_comm.
  by apply ex_pseries_incr_1, ex_Bessel1.
  by apply ex_Bessel1.
Qed.

(** * Unicity *)

Lemma Bessel1_uniqueness (a : nat -> R) (n : nat) : Rbar_lt 0 (CV_radius a) ->
  (forall x : R, Rbar_lt (Rabs x) (CV_radius a) ->
  x^2 * Derive_n (PSeries a) 2 x + x * Derive (PSeries a) x + (x^2 - (INR n)^2) * PSeries a x = 0)
  -> 
  (a 0%nat = 0 \/ n = O) /\
  (a 1%nat = 0 \/ n = 1%nat) /\
  (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0).
Proof.
  move => Ha H.
  cut (forall k, 
    (PS_plus (PS_plus (PS_incr_n (PS_derive_n 2 a) 2)
      (PS_incr_1 (PS_derive a))) (PS_plus (PS_incr_n a 2) (PS_scal (- INR n ^ 2) a))) k = 0).
  intros Haux.
  split ; [move: (Haux 0%nat) | move: (fun k => Haux (S k))] => {Haux} Haux.
(* n = 0 *)
  rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive in Haux.
  simpl in Haux; ring_simplify in Haux.
  apply Rmult_integral in Haux ; case: Haux => Haux.
  right.
  suff : ~ n <> 0%nat.
  by intuition.
  contradict Haux.
  apply Ropp_neq_0_compat.
  apply pow_nonzero.
  by apply not_0_INR.
  by left.
  split ; [move: (Haux 0%nat) | move: (fun k => Haux (S k))] => {Haux} Haux.
(* n = 1 *)
  rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive /= in Haux.
  ring_simplify in Haux.
  replace (- a 1%nat * INR n ^ 2 + a 1%nat) with ((1 - INR n ^ 2) * a 1%nat) in Haux.
  apply Rmult_integral in Haux ; case: Haux => Haux.
  right.
  suff : ~ n <> 1%nat.
  by intuition.
  contradict Haux.
  replace (1 - INR n ^ 2) with ((1-INR n) * (1 + INR n)) by ring.
  apply Rmult_integral_contrapositive_currified.
  apply Rminus_eq_contra.
  apply sym_not_eq.
  by apply not_1_INR.
  apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1).
  apply Rminus_le_0 ; ring_simplify.
  by apply pos_INR.
  by left.
  ring.

  move => k ; rewrite ?S_INR /= ;
  move: (Haux k) ;
  rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive -?S_INR.
  replace (k + 2)%nat with (S (S k)) by ring.
  rewrite /fact -/fact ?mult_INR ?S_INR => {Haux} Haux.
  simpl in Haux; field_simplify in Haux.
  field_simplify.
  by rewrite (Rmult_comm (INR n ^ 2)).
  move: Haux.
  by apply INR_fact_neq_0.

  move => k.
  apply (PSeries_ext_recip _ (fun _ => 0)).
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  rewrite /Rbar_min ; case: Rbar_le_dec => _.
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  rewrite /Rbar_min ; case: Rbar_le_dec => _.
  rewrite /PS_incr_n ?CV_radius_incr_1.
  by rewrite CV_radius_derive_n.
  rewrite CV_radius_incr_1.
  by rewrite CV_radius_derive.
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  rewrite /Rbar_min ; case: Rbar_le_dec => _.
  by rewrite /PS_incr_n ?CV_radius_incr_1.
  by apply Rbar_lt_le_trans with (2 := CV_radius_scal _ _).
  by rewrite CV_radius_const_0.
  move => x Hx.
  rewrite PSeries_const_0 ?PSeries_plus.
  rewrite ?PSeries_incr_n PSeries_incr_1 PSeries_scal -Derive_n_PSeries.
  rewrite -Derive_PSeries.
  rewrite -Rmult_plus_distr_r.
  apply H.
  
Admitted.

