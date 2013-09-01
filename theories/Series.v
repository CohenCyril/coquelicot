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
Require Import Rcomplements.
Require Import Limit Rbar.

(** * Definitions *)

Definition is_series (a : nat -> R) (l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k)) l.
Definition ex_series (a : nat -> R) :=
  ex_finite_lim_seq (sum_f_R0 (fun k => a k)).
Definition Series (a : nat -> R) : R :=
  real (Lim_seq (sum_f_R0 (fun k => a k))).

Lemma ex_series_dec (a : nat -> R) :
  {ex_series a} + {~ex_series a}.
Proof.
  case: (ex_lim_seq_dec (sum_f_R0 (fun k => a k))) => H.
  apply Lim_seq_correct in H.
  case: (Lim_seq (sum_f_R0 (fun k : nat => a k))) H => [l | | ] H.
  left ; by exists l.
  right ; case => l H0.
  absurd (p_infty = Finite l) => //.
  rewrite -(is_lim_seq_unique _ _ H).
  by apply is_lim_seq_unique.
  right ; case => l H0.
  absurd (m_infty = Finite l) => //.
  rewrite -(is_lim_seq_unique _ _ H).
  by apply is_lim_seq_unique.
  right ; case => l.
  contradict H.
  by exists l.
Qed.

Lemma is_series_unique (a : nat -> R) (l : R) :
  is_series a l -> Series a = l.
Proof.
  move => Ha.
  replace l with (real (Finite l)) by auto.
  apply (f_equal real).
  by apply is_lim_seq_unique.
Qed.
Lemma Series_correct (a : nat -> R) :
  ex_series a -> is_series a (Series a).
Proof.
  case => l Ha.
  by rewrite (is_series_unique a l).
Qed.

Ltac search_series := let l := fresh "l" in
evar (l : R) ;
match goal with
  | |- Series _ = ?lu => apply is_series_unique ; replace lu with l ; [ | unfold l]
  | |- is_series _ ?lu => replace lu with l ; [ | unfold l]
end.

Lemma is_series_equiv (a : nat -> R) (l : R) :
  is_series a l <-> infinite_sum a l.
Proof.
  split => H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 a n) with (sum_f_R0 (fun k : nat => a k) n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a k) n) with (sum_f_R0 a n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.
Lemma ex_series_equiv_0 (a : nat -> R) :
  ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
  move => H ;
  exists (Series a) ; case: H => l H.
  replace (Series a) with l.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 a n) with (sum_f_R0 (fun k : nat => a k) n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
  apply sym_eq.
  rewrite /Series.
  replace l with (real (Finite l)) by auto.
  apply f_equal.
  by apply is_lim_seq_unique.
Qed.
Lemma ex_series_equiv_1 (a : nat -> R) :
  { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l } -> ex_series a.
Proof.
  case => l H.
  exists l.
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a k) n) with (sum_f_R0 a n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.

(** Extensionality *)

Lemma is_series_ext (a b : nat -> R) (l : R) :
  (forall n, a n = b n) -> (is_series a l)
    -> is_series b l.
Proof.
  move => Heq.
  apply is_lim_seq_ext.
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.
Lemma ex_series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> ex_series a
    -> ex_series b.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_series_ext with a.
Qed.
Lemma Series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> Series a = Series b.
Proof.
  move => Heq.
  apply (f_equal real).
  apply Lim_seq_ext.
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.

(** Index offset *)

Lemma is_series_incr_1 (a : nat -> R) (l : R) :
  is_series a (l + a O)
    -> is_series (fun k => a (S k)%nat) l.
Proof.
  move => Ha eps.
  case: (Ha eps) => {Ha} N Ha.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a (S k)) n - l)
    with (a O + sum_f_R0 (fun k : nat => a (S k)) (pred (S n)) - (l + a O))
    by (simpl ; ring).
  rewrite -(decomp_sum (fun k => a k)).
  apply (Ha (S n)).
  by intuition.
  by apply lt_O_Sn.
Qed.
Lemma is_series_incr_n (a : nat -> R) (n : nat) (l : R) :
  (0 < n)%nat -> is_series a (l + sum_f_R0 a (pred n))
    -> is_series (fun k => a (n + k)%nat) l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n l Ha => [ | n IH] l Ha.
  by apply is_series_incr_1.
  apply is_series_ext with (fun k : nat => a (S (n + S k))).
    move => k ; apply f_equal ; ring.
  apply is_series_incr_1 with (a := fun k : nat => a (S (n + k))).
  rewrite plus_0_r.
  apply IH.
  by rewrite Rplus_assoc (Rplus_comm (a (S n))).
Qed.

Lemma is_series_decr_1 (a : nat -> R) (l : R) :
  is_series (fun k => a (S k)%nat) (l - a O) -> is_series a l.
Proof.
  move => Ha eps.
  case: (Ha eps) => {Ha} N Ha.
  exists (S N) ; elim => [ | n IH] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  rewrite decomp_sum /=.
  replace (a 0%nat + sum_f_R0 (fun i : nat => a (S i)) n - l)
    with(sum_f_R0 (fun k : nat => a (S k)) n - (l - a 0%nat)) by ring.
  by apply Ha.
  by apply lt_0_Sn.
Qed.
Lemma is_series_decr_n (a : nat -> R) (n : nat) (l : R) :
  (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (l - sum_f_R0 a (pred n))
    -> is_series a l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n a l Ha => [ | n IH] a l Ha.
  by apply is_series_decr_1.
  apply is_series_decr_1.
  apply IH.
  replace (l - a 0%nat - sum_f_R0 (fun k : nat => a (S k)) n)
    with (l - sum_f_R0 a (S n)).
  by apply Ha.
  rewrite decomp_sum /=.
  ring.
  by apply lt_O_Sn.
Qed.

Lemma ex_series_decal_1 (a : nat -> R) :
  ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
  split ; move => [la Ha].
  exists (la - a O).
  apply is_series_incr_1.
  by ring_simplify (la - a 0%nat + a 0%nat).
  exists (la + a O).
  apply is_series_decr_1.
  by ring_simplify (la + a 0%nat - a 0%nat).
Qed.
Lemma ex_series_decal_n (a : nat -> R) (n : nat) :
  ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
  case: n => [ | n].
  split ; apply ex_series_ext ; by intuition.
  split ; move => [la Ha].
  exists (la - sum_f_R0 a (pred (S n))).
  apply is_series_incr_n.
  by apply lt_O_Sn.
  by ring_simplify (la - sum_f_R0 a (pred (S n)) + sum_f_R0 a (pred (S n))).
  exists (la + sum_f_R0 a (pred (S n))).
  apply is_series_decr_n with (S n).
  by apply lt_O_Sn.
  by ring_simplify (la + sum_f_R0 a (pred (S n)) - sum_f_R0 a (pred (S n))).
Qed.

Lemma Series_decal_1 (a : nat -> R) :
  ex_series a -> Series a = a O + Series (fun k => a (S k)).
Proof.
  move => Ha.
  apply is_series_unique.
  rewrite Rplus_comm.
  apply is_series_decr_1 ;
  ring_simplify (Series (fun k : nat => a (S k)) + a 0%nat - a 0%nat).
  by apply Series_correct, (ex_series_decal_1 a).
Qed.
Lemma Series_decal_n (a : nat -> R) (n : nat) :
  (0 < n)%nat -> ex_series a
    -> Series a = sum_f_R0 a (pred n)  + Series (fun k => a (n + k)%nat).
Proof.
  move => Hn Ha.
  apply is_series_unique.
  rewrite Rplus_comm.
  apply is_series_decr_n with n.
  by [].
  ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) -
   sum_f_R0 a (pred n)).
  by apply Series_correct, (ex_series_decal_n a).
Qed.

Lemma Series_decal_1_aux (a : nat -> R) :
  a O = 0 -> Series a = Series (fun k => a (S k)).
Proof.
  move => Ha.
  rewrite /Series.
  rewrite -Lim_seq_incr_1.
  apply f_equal, Lim_seq_ext => n.
  rewrite decomp_sum /=.
  rewrite Ha ; by apply Rplus_0_l.
  by apply lt_O_Sn.
Qed.
Lemma Series_decal_n_aux (a : nat -> R) (n : nat) :
   (forall k, (k < n)%nat -> a k = 0)
     -> Series a = Series (fun k => a (n + k)%nat).
Proof.
  elim: n => [ | n IH] Ha.
  by apply Series_ext => k.
  rewrite IH.
  rewrite Series_decal_1_aux.
  apply Series_ext => k.
  apply f_equal ; ring.
  intuition.
  move => k Hk ; intuition.
Qed.

(** * Convergence theorems *)

Lemma Cauchy_ex_series (a : nat -> R) :
  ex_series a <-> (Cauchy_crit_series a).
Proof.
  split => Hcv.
  by apply cv_cauchy_1, ex_series_equiv_0.
  apply ex_series_equiv_1.
  apply R_complete.
  by apply Hcv.
Qed.

Lemma ex_series_lim_0 (a : nat -> R) :
  ex_series a -> is_lim_seq a 0.
Proof.
  move => Hs eps.
  apply Cauchy_ex_series in Hs.
  case: (Hs eps (cond_pos eps)) => {Hs} N Hs.
  exists (S N) ; case => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  replace (a (S n) - 0)
    with (sum_f_R0 a (S n) - sum_f_R0 a n)
    by (simpl ; ring).
  apply Hs ; by intuition.
Qed.

Lemma ex_series_Rabs (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) -> ex_series a.
Proof.
  move => H.
  apply Cauchy_ex_series.
  apply cauchy_abs.
  by apply Cauchy_ex_series.
Qed.

Lemma Series_Rabs (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) ->
    Rabs (Series a) <= Series (fun n => Rabs (a n)).
Proof.
  move => Hra.
  have Ha := (ex_series_Rabs a Hra).
  case: Hra => lra Hra.
  case: Ha => la Ha.
  rewrite /is_series in Hra Ha.
  rewrite /Series /=.
  replace (Lim_seq (sum_f_R0 (fun k : nat => a k))) with (Finite la).
  replace (Lim_seq (sum_f_R0 (fun k : nat => Rabs (a k)))) with (Finite lra).
  simpl.
  apply is_lim_seq_abs in Ha.
  apply Rbar_finite_le, (fun H => is_lim_seq_le _ _ _ _ H Ha Hra).
  elim => [ | n IH] /=.
  by apply Rle_refl.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_compat_r.
  by apply IH.
  by apply sym_eq, is_lim_seq_unique.
  by apply sym_eq, is_lim_seq_unique.
Qed.

(** Comparison *)

Lemma Comp_ex_series (a b : nat -> R) :
   (forall n : nat, 0 <= a n <= b n) ->
   ex_series b -> ex_series a.
Proof.
  move => H Hb.
  apply Cauchy_ex_series.
  apply Cauchy_ex_series in Hb.
  move => e He.
  case (Hb e He) => {Hb} N Hb.
  exists N => n m Hn Hm.
  wlog: n m Hn Hm /(n > m)%nat => [Hw | Hnm].
  case: (le_lt_dec n m) => Hnm.
  apply le_lt_eq_dec in Hnm ; case: Hnm => Hnm.
  rewrite /R_dist -Ropp_minus_distr' Rabs_Ropp ; by apply Hw.
  by rewrite Hnm /R_dist Rminus_eq_0 Rabs_R0.
  by apply Hw.
  move: (Hb n m Hn Hm).
  rewrite /R_dist (tech2 a m n Hnm) (tech2 b m n Hnm) ;
    ring_simplify (sum_f_R0 a m
    + sum_f_R0 (fun i : nat => a (S m + i)%nat) (n - S m)
    - sum_f_R0 a m) ;
    ring_simplify (sum_f_R0 b m
    + sum_f_R0 (fun i : nat => b (S m + i)%nat) (n - S m)
    - sum_f_R0 b m).
  apply Rle_lt_trans.
  apply Rle_trans with (2 := Rle_abs _).
  rewrite Rabs_pos_eq.
  elim: (n - S m)%nat => /= [ | k IH].
  by apply H.
  apply Rplus_le_compat.
  exact: IH.
  by apply H.
  elim: (n - S m)%nat => /= [ | k IH].
  by apply H.
  apply Rplus_le_le_0_compat.
  exact: IH.
  by apply H.
Qed.

Lemma Series_compar (a b : nat -> R) :
  (forall n : nat, 0 <= a n <= b n) ->
   ex_series b -> Series a <= Series b.
Proof.
  move => Hn Hb.
  have Ha := (Comp_ex_series _ _ Hn Hb).
  apply Lim_seq_correct' in Ha.
  apply Lim_seq_correct' in Hb.
  rewrite /Series.
  apply Rbar_finite_le.
  move: Ha Hb ; apply is_lim_seq_le.
  elim => [ | n IH] /=.
  by apply Hn.
  apply Rplus_le_compat.
  by apply IH.
  by apply Hn.
Qed.


(** * Operations *)

(** Additive operators *)

Lemma is_series_opp (a : nat -> R) (la : R) :
  is_series a la
    -> is_series (fun n => - a n) (- la).
Proof.
  move => Ha.
  apply is_lim_seq_ext
    with (fun n => - (sum_f_R0 (fun k => a k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  search_lim_seq.
  apply -> is_lim_seq_opp.
  by apply Ha.
  by simpl.
Qed.
Lemma ex_series_opp (a : nat -> R) :
  ex_series a
    -> ex_series (fun n => - a n).
Proof.
  move => [la Ha].
  exists (-la).
  by apply is_series_opp.
Qed.
Lemma Series_opp (a b : nat -> R) :
  Series (fun n => - a n) = - Series a.
Proof.
  rewrite /Series
    (Lim_seq_ext (sum_f_R0 (fun k : nat => - a k)) (fun n => - (sum_f_R0 (fun k => a k) n))).
  rewrite Lim_seq_opp.
  by rewrite Rbar_opp_real.
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite IH ; ring.
Qed.

Lemma is_series_plus (a b : nat -> R) (la lb : R) :
  is_series a la -> is_series b lb
    -> is_series (fun n => a n + b n) (la + lb).
Proof.
  move => Ha Hb.
  apply is_lim_seq_ext
    with (fun n => (sum_f_R0 (fun k => a k) n) + (sum_f_R0 (fun k => b k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  by apply (is_lim_seq_plus _ _ la lb).
Qed.
Lemma ex_series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> ex_series (fun n => a n + b n).
Proof.
  move => [la Ha] [lb Hb].
  exists (la + lb).
  by apply is_series_plus.
Qed.
Lemma Series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n + b n) = Series a + Series b.
Proof.
  intros Ha Hb.
  replace (Series a + Series b) with (real (Series a + Series b)) by auto.
  apply (f_equal real), is_lim_seq_unique, is_series_plus ;
  by apply Series_correct.
Qed.

Lemma is_series_minus (a b : nat -> R) (la lb : R) :
  is_series a la -> is_series b lb
    -> is_series (fun n => a n - b n) (la - lb).
Proof.
  move => Ha Hb.
  apply is_series_plus => //.
  apply is_series_opp => //.
Qed.
Lemma ex_series_minus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> ex_series (fun n => a n - b n).
Proof.
  move => Ha Hb.
  apply ex_series_plus => //.
  apply ex_series_opp => //.
Qed.
Lemma Series_minus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n - b n) = Series a - Series b.
Proof.
  intros Ha Hb.
  rewrite Series_plus => //.
  rewrite Series_opp => //.
  by apply ex_series_opp.
Qed.

(** Multiplication by a scalar *)

Lemma is_series_scal_l (c : R) (a : nat -> R) (l : R) :
  is_series a l -> is_series (fun n => c * a n) (c * l).
Proof.
  move => Ha.
  apply is_lim_seq_ext with (fun n => c * (sum_f_R0 (fun k => a k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  apply (is_lim_seq_scal_l _ c l).
  by apply Ha.
Qed.
Lemma ex_series_scal_l (c : R) (a : nat -> R) :
  ex_series a -> ex_series (fun n => c * a n).
Proof.
  move => [l Ha].
  exists (c * l).
  by apply is_series_scal_l.
Qed.
Lemma Series_scal_l (c : R) (a : nat -> R) :
  Series (fun n => c * a n) = c * Series a.
Proof.
  rewrite /Series.
  have H0 : (forall x, c * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite c) x)).
  case: (Req_dec c 0) => [-> | Hk].
  case => [x | | ] //= ; rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case => [x | | ] //= ; rewrite Rmult_0_r.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.

  rewrite H0 -(Lim_seq_scal_l _ c).
  apply f_equal, Lim_seq_ext.
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite IH ; ring.
Qed.

Lemma is_series_scal_r (c : R) (a : nat -> R) (l : R) :
  is_series a l -> is_series (fun n => a n * c) (l * c).
Proof.
  move => Ha.
  rewrite Rmult_comm.
  apply is_series_ext with (fun n : nat => c * a n).
  move => n ; apply Rmult_comm.
  by apply is_series_scal_l.
Qed.
Lemma ex_series_scal_r (c : R) (a : nat -> R) :
  ex_series a -> ex_series (fun n => a n * c).
Proof.
  move => [l Ha].
  exists (l * c).
  by apply is_series_scal_r.
Qed.
Lemma Series_scal_r (c : R) (a : nat -> R) :
  Series (fun n => a n * c) = Series a * c.
Proof.
  rewrite Rmult_comm -Series_scal_l.
  apply Series_ext.
  move => n ; apply Rmult_comm.
Qed.

Lemma is_series_mult_pos (a b : nat -> R) (la lb : R) :
  is_series a la -> is_series b lb ->
  (forall n, 0 <= a n) -> (forall n, 0 <= b n)
  -> is_series (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
  move => Hla Hlb Ha Hb.

  have H0 : forall n,
    sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) n
      <= sum_f_R0 a n * sum_f_R0 b n.
    case => [ | n].
    simpl ; apply Rle_refl.
    rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
    apply Rminus_le_0 ; ring_simplify.
    apply cond_pos_sum => m.
    apply cond_pos_sum => k.
    by apply Rmult_le_pos.
  have H1 : forall n, sum_f_R0 a n * sum_f_R0 b n
    <= sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) ((2*n)%nat).
    case => [ /= | n].
    by apply Rle_refl.
    rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
    rewrite Rplus_comm ; apply Rle_minus_r.
    replace (pred (S n)) with n by auto.
    replace (2 * S n)%nat with (S n + S n)%nat by ring.
    rewrite -sum_f_rw.
    rewrite /sum_f.
    simpl minus at 4.
    rewrite NPeano.Nat.add_sub.
    replace (pred (S n)) with n by auto.
    elim: {1 5 8}n (le_refl n) => [ | m IH] Hm ; rewrite /sum_f_R0 -/sum_f_R0.
    rewrite -minus_n_O plus_0_l ; simpl pred.
    rewrite -?sum_f_rw_0.
    replace (sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat))
      with ((sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat) -
        (fun p : nat => a p * b (S (S n) - p)%nat) 0%nat)
        + a O * b (S (S n))) by (rewrite -minus_n_O ; ring).
    rewrite -(sum_f_Sn_m _ O (S (S n))) ; [ | by apply lt_O_Sn].
    rewrite sum_f_u_Sk ; [ | by apply le_O_n].
    rewrite sum_f_n_Sm ; [ | by apply le_O_n].
    apply Rle_trans with (sum_f 0 n (fun l0 : nat => a (S (l0 + 0)) * b (S n - l0)%nat) +
      a (S (S n)) * b (S (S n) - S (S n))%nat + a 0%nat * b (S (S n))).
      apply Rminus_le_0 ; ring_simplify.
      apply Rplus_le_le_0_compat ; by apply Rmult_le_pos.
      repeat apply Rplus_le_compat_r.
      apply Req_le.
      rewrite ?sum_f_rw_0.
      elim: {1 4 6}n (le_refl n) => [ | k IH] Hk // ;
      rewrite /sum_f_R0 -/sum_f_R0.
      rewrite IH ; try by intuition.
      apply f_equal.
      by rewrite plus_0_r /=.
    apply Rplus_le_compat.
    apply IH ; intuition.
    rewrite -?sum_f_rw_0.
    rewrite NPeano.Nat.sub_succ_l ; try by intuition.
    replace (pred (S (n - S m))) with (n - S m)%nat by auto.
    rewrite plus_Sn_m -?plus_n_Sm.
    replace (sum_f 0 (S (S (S (m + n))))
      (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat))
      with (sum_f 1 (S (S (S (m + n))))
      (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat) + a O * b (S (S (S (m + n))))).
    rewrite -(Rplus_0_r (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite (sum_f_chasles _ O (S m) (S (S (S (m + n))))) ; try by intuition.
    rewrite -(Rplus_0_l (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite /sum_f.
    elim: (S m - 1)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
    by apply Rmult_le_pos.
    apply Rplus_le_le_0_compat.
    by apply IH.
    by apply Rmult_le_pos.
    replace (S (S m)) with (1 + S m)%nat by ring.
    replace (S (S (S (m + n)))) with (S (S n) + S m )%nat by ring.
    rewrite sum_f_u_add.
    rewrite (sum_f_chasles _ O (S (n - S m)) (S (S n))) ; try by intuition.
    rewrite -(Rplus_0_r (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite sum_f_u_Sk.
    rewrite ?sum_f_rw_0.
    apply Req_le.
    elim: (n - S m)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
    apply f_equal2 ; apply f_equal ; intuition.
    rewrite IH ; apply f_equal, f_equal2 ; apply f_equal.
    ring.
    rewrite ?(plus_comm _ (S m)) -minus_plus_simpl_l_reverse //=.
    apply le_O_n.
    rewrite /sum_f.
    elim: (S (S n) - S (S (n - S m)))%nat => {IH} [ | k IH] ;
    rewrite /sum_f_R0 -/sum_f_R0 //.
    by apply Rmult_le_pos.
    apply Rplus_le_le_0_compat => // ; by apply Rmult_le_pos.
    by apply le_n_S, le_O_n.
    by apply Rmult_le_pos.
    rewrite sum_f_Sn_m -?minus_n_O ; try by intuition.
    ring.
    elim: n => [ | n IH] //.
    rewrite -plus_n_Sm plus_Sn_m.
    apply lt_n_S ; intuition.
    have H2 : forall n, sum_f_R0 a (Div2.div2 n)%nat * sum_f_R0 b (Div2.div2 n)%nat <=
      sum_f_R0
      (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k)
      n.
      move => n.
      case: (even_odd_cor n) => k ; case => -> {n}.
      rewrite div2_double.
      by apply H1.
      rewrite div2_S_double.
      apply Rle_trans with (1 := H1 _).
      apply Rminus_le_0 ; rewrite -sum_f_rw ; try by intuition.
      rewrite /sum_f minus_diag /sum_f_R0 -/sum_f_R0.
      apply cond_pos_sum => l ; by apply Rmult_le_pos.


    rewrite /is_series.
    apply is_lim_seq_le_le with (u := fun n => sum_f_R0 a (Div2.div2 n) * sum_f_R0 b (Div2.div2 n))
    (w := fun n => sum_f_R0 a n * sum_f_R0 b n).
    by split.
    replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
    suff H : is_lim_seq
      (fun n : nat => sum_f_R0 a n * sum_f_R0 b n)
      (Rbar_mult la lb).
    move => eps.
    case: (H eps) => {H} N H.
    exists (S (2 * N))%nat => n Hn.
    apply H.
    apply le_double.
    apply le_S_n.
    apply le_trans with (1 := Hn).
    apply (Div2.ind_0_1_SS (fun n => (n <= S (2 * Div2.div2 n))%nat)).
    by apply le_O_n.
    by apply le_refl.
    move => k Hk.
    replace (Div2.div2 (S (S k))) with (S (Div2.div2 k)) by auto.
    replace (2 * S (Div2.div2 k))%nat with (S (S (2 * Div2.div2 k))) by ring.
    by repeat apply le_n_S.

    apply is_lim_seq_mult.
    by apply Hla.
    by apply Hlb.
    by [].
    replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
    apply is_lim_seq_mult.
    by apply Hla.
    by apply Hlb.
    by [].
Qed.

Lemma is_series_mult (a b : nat -> R) (la lb : R) :
  is_series a la -> is_series b lb
  -> ex_series (fun n => Rabs (a n)) -> ex_series (fun n => Rabs (b n))
  -> is_series (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
  move => Hla Hlb Ha Hb.

  set ap := fun n => (a n + Rabs (a n)) / 2.
  set am := fun n => - (a n - Rabs (a n)) / 2.
  set bp := fun n => (b n + Rabs (b n)) / 2.
  set bm := fun n => - (b n - Rabs (b n)) / 2.

  have Hap : forall n, 0 <= ap n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  have Sap : ex_series ap.
    apply ex_series_scal_r.
    apply ex_series_plus => //.
    by exists la.
  have Ham : forall n, 0 <= am n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (a _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  have Sam : ex_series am.
    apply ex_series_scal_r.
    apply ex_series_opp.
    apply ex_series_minus => //.
    by exists la.
  have Hbp : forall n, 0 <= bp n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  have Sbp : ex_series bp.
    apply ex_series_scal_r.
    apply ex_series_plus => //.
    by exists lb.
  have Hbm : forall n, 0 <= bm n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (b _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  have Sbm : ex_series bm.
    apply ex_series_scal_r.
    apply ex_series_opp.
    apply ex_series_minus => //.
    by exists lb.


  apply is_series_ext with (fun n => sum_f_R0 (fun k : nat => ap k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => am k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => ap k * bm (n - k)%nat) n
    + sum_f_R0 (fun k : nat => am k * bm (n - k)%nat) n).
  move => n.
  rewrite -?minus_sum -plus_sum.
  apply sum_eq => k _.
  rewrite /ap /am /bp /bm ; field.
  search_series.
  apply is_series_plus.
  apply is_series_minus.
  apply is_series_minus.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  replace (la) with (Series ap - Series am).
  replace (lb) with (Series bp - Series bm).
  ring.
  rewrite -Series_minus // -(is_series_unique _ _ Hlb) ; apply Series_ext => n.
  rewrite /ap /am /bp /bm ; field.
  rewrite -Series_minus // -(is_series_unique _ _ Hla) ; apply Series_ext => n.
  rewrite /ap /am /bp /bm ; field.
Qed.

(** * D'Alembert criterion *)

Lemma ex_series_DAlembert (a : nat -> R) (k : R) :
  k < 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) k
      -> ex_series (fun n => Rabs (a n)).
Proof.
  move => Hk Ha H.
  have : exists N, forall n, (N <= n)%nat -> Rabs (a (S n) / a n) <= (k+1)/2.
    case: (fun He => H (mkposreal ((1-k)/2) He)).
      move: (fun He => is_pos_div_2 (mkposreal (1-k) He)) => /= He ;
      apply: He.
      by apply -> Rminus_lt_0.
    move => {H} /= Hk1 N H.
    exists N => n Hn.
    move: (H n Hn) => {H} H.
    apply Rabs_lt_between' in H ; case: H => _ H ;
    field_simplify in H ; rewrite Rdiv_1 in H ; by apply Rlt_le.
  case => {H} N H.
  apply ex_series_decal_n with N.
  apply Comp_ex_series with (fun n => Rabs (a N) * ((k+1)/2)^n).
  move => n ; split.
  by apply Rabs_pos.
  rewrite Rmult_comm ; apply Rle_div_l.
  by apply Rabs_pos_lt.
  rewrite -Rabs_div.
  elim: n => [ | n IH].
  rewrite plus_0_r /Rdiv Rinv_r.
  rewrite Rabs_R1 ; by apply Rle_refl.
  by apply Ha.
  replace (Rabs (a (N + S n)%nat / a N))
    with (Rabs (a (S (N + n))/a (N+n)%nat) * Rabs (a (N + n)%nat / a N)).
  simpl ; apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  apply H, le_plus_l.
  by apply IH.
  rewrite -Rabs_mult ; apply f_equal.
  rewrite plus_n_Sm ; field ; split ; by apply Ha.
  by apply Ha.
  apply ex_series_scal_l.
  set k0 := ((k + 1) / 2).
  exists (/(1-k0) * (1-k0*0)).
  apply (is_lim_seq_ext (fun N => / (1 - k0) * (1 - k0 ^ S N)) (sum_f_R0 (fun k1 : nat => k0 ^ k1))).
  move => n ; rewrite tech3.
  by apply Rmult_comm.
  apply Rlt_not_eq.
  replace 1 with ((1+1)/2) by field ; rewrite /k0.
  apply Rmult_lt_compat_r ; by intuition.
  apply (is_lim_seq_scal_l (fun N0 => (1 - k0 ^ S N0)) (/ (1 - k0)) (Finite (1-k0*0))).
  apply (is_lim_seq_minus _ _ (Finite 1) (Finite (k0*0))).
  by apply is_lim_seq_const.
  simpl pow ; apply (is_lim_seq_scal_l _ _ (Finite 0)).
  apply (is_lim_seq_geom k0).
  rewrite Rabs_pos_eq.
  replace 1 with ((1+1)/2) by field ; rewrite /k0.
  apply Rmult_lt_compat_r ; by intuition.
  apply Rle_trans with (2 := H N (le_refl _)) ; by apply Rabs_pos.
  easy.
Qed.

Lemma not_ex_series_DAlembert (a : nat -> R) (l : R) :
  l > 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) l
      -> ~ is_lim_seq a 0.
Proof.
  move => Hl Ha Hda Ha0.
  set k := (l+1)/2.
  have Hk1 : 1 < k.
    apply Rminus_lt ; unfold k ; field_simplify ; rewrite Rdiv_1.
    rewrite -(Rmult_0_l (/2)) ; apply Rmult_lt_compat_r ; try by intuition.
    rewrite Rplus_comm ; by apply Rlt_minus.
  have : exists N, forall n, (N <= n)%nat -> k <= Rabs (a (S n) / a n).
    case: (fun H => Hda (mkposreal ((l-1)/2) H)) => [ | /= {Hda} H N Hda].
    apply Rdiv_lt_0_compat.
    by apply -> Rminus_lt_0.
    by apply Rlt_R0_R2.
    exists N => n Hn.
    move: (Hda n Hn) => {Hda} Hda.
    apply Rabs_lt_between' in Hda.
    replace (k) with (l - (l - 1) / 2) by (unfold k ; field).
    by apply Rlt_le, Hda.
  case => N H.
  apply is_lim_seq_abs_0, (is_lim_seq_incr_n _ N) in Ha0.
  have : forall n, Rabs (a N) * k ^ n <= Rabs (a (n + N)%nat).
    elim => /= [ | n IH].
    rewrite Rmult_1_r ; by apply Rle_refl.
    replace (Rabs (a (S (n + N))))
      with (Rabs (a (S (n+N)) / a (n+N)%nat) * Rabs (a (n+N)%nat))
      by (rewrite -Rabs_mult ; apply f_equal ; by field).
    replace (Rabs (a N) * (k * k ^ n)) with (k * (Rabs (a N) * k ^ n)) by ring.
    apply Rmult_le_compat.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H, le_plus_r.
    by apply IH.
  move => {H} H.
  have : Finite 0 = p_infty.
    rewrite -(Lim_seq_geom_p k Hk1).
    apply sym_equal.
    apply is_lim_seq_unique.
    apply is_lim_seq_ext with (fun n => / Rabs (a N) * (Rabs (a N) * k ^ n)).
    move => n ; field ; by apply Rabs_no_R0.
    rewrite -(Rmult_0_r (/Rabs (a N))).
    apply (is_lim_seq_scal_l _ _ (Finite 0)).
    apply is_lim_seq_le_le with (fun _ => 0) (fun n => Rabs (a (n + N)%nat)).
    move => n ; split.
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H.
    by apply is_lim_seq_const.
    by apply Ha0.
  by [].
Qed.

(** * Geometric series *)

Lemma is_series_geom (q : R) :
  Rabs q < 1 -> is_series (fun n => q ^ n) (/ (1-q)).
Proof.
  move => Hq.
  apply is_lim_seq_ext with (fun n => (1-q^(S n)) / (1-q)).
  move => n.
  rewrite tech3.
  reflexivity.
  apply Rlt_not_eq.
  apply Rle_lt_trans with (2 := Hq).
  apply Rle_abs.
  replace (Finite (/ (1 - q))) with (Rbar_mult (Rbar_minus 1 0) (/ (1 - q))).
  apply is_lim_seq_mult.
  apply is_lim_seq_minus.
  by apply is_lim_seq_const.
  apply (is_lim_seq_incr_1 (fun n => q^n)).
  by apply is_lim_seq_geom.
  easy.
  by apply is_lim_seq_const.
  by simpl.
  apply Rbar_finite_eq.
  ring.
Qed.
Lemma ex_series_geom (q : R) :
  Rabs q < 1 -> ex_series (fun n => q ^ n).
Proof.
  move => Hq.
  exists (/(1-q)).
  by apply is_series_geom.
Qed.
Lemma Series_geom (q : R) :
  Rabs q < 1 -> Series (fun n => q ^ n) = / (1-q).
Proof.
  move => Hq.
  apply is_series_unique.
  by apply is_series_geom.
Qed.
