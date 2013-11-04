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
Require Import Limit Rbar Hierarchy.

(** Sum *)

Fixpoint sum_n {G} {GG: AbelianGroup G} (a:nat -> G) (N : nat) {struct N} : G :=
  match N with
   | 0%nat => a 0%nat
   | S i => plus (sum_n a i)  (a (S i))
  end.

Lemma sum_n_ext_aux: forall {G} {GG: AbelianGroup G} (a b:nat-> G) N, 
   (forall n, (n < S N)%nat -> a n = b n) -> sum_n a N = sum_n b N.
Proof.
  intros G GG a b N H; induction N; simpl.
  apply H.
  by apply le_refl.
  rewrite IHN.
  by rewrite H.
  move => n Hn.
  now apply H, le_trans with (1 := Hn), le_n_Sn.
Qed.
Lemma sum_n_ext: forall {G} {GG: AbelianGroup G} (a b:nat-> G) N, 
   (forall n, a n = b n) -> sum_n a N = sum_n b N.
Proof.
  intros G GG a b N H; induction N; simpl.
  apply H.
  now rewrite IHN; rewrite H.
Qed.

Lemma sum_n_sum_f_R0: forall a N, sum_n a N = sum_f_R0 a N.
Proof.
  intros a; induction N; simpl.
  easy.
  now rewrite IHN.
Qed.

Lemma decomp_sum_n: forall {G} {GG: AbelianGroup G} (a:nat-> G) N, 
  (0 < N)%nat ->
   sum_n a N = plus (a 0%nat) (sum_n (fun i : nat => a (S i)) (pred N)).
Proof.
  intros G GG a N HN; destruct N; simpl.
  exfalso; omega.
  clear HN; induction N; simpl.
  easy.
  rewrite IHN.
  apply sym_eq, plus_assoc.
Qed.  

Lemma sum_n_plus {G} {GG : AbelianGroup G} : forall (u v : nat -> G) (n : nat),
  sum_n (fun k => plus (u k) (v k)) n = plus (sum_n u n) (sum_n v n).
Proof.
  intros u v.
  induction n ; simpl.
  by [].
  rewrite IHn ; clear IHn.
  rewrite -?plus_assoc.
  apply f_equal.
  rewrite ?plus_assoc.
  apply f_equal2.
  by apply plus_comm.
  by [].
Qed.

Lemma sum_n_switch {G} {GG : AbelianGroup G} : forall (u : nat -> nat -> G) (m n : nat),
  sum_n (fun i => sum_n (u i) n) m = sum_n (fun j => sum_n (fun i => u i j) m) n.
Proof.
  intros u.
  induction m ; simpl ; intros n.
  by [].
  rewrite IHm ; clear IHm.
  by rewrite -sum_n_plus.
Qed.

Lemma sum_n_nc_mult_r {K} {RK : ncRing K} :
 forall (a : K) (u : nat -> K) (n : nat),
  sum_n (fun k => nc_mult (u k) a) n = nc_mult (sum_n u n) a.
Proof.
  intros a u n.
  induction n ; simpl.
  by [].
  rewrite IHn.
  apply eq_sym.
  by apply nc_mult_distr_r.
Qed.

(** * Definitions *)

Definition is_series {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) (l : V) :=
   filterlim (sum_n a) (eventually) (locally l).

Definition ex_series {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) :=
   exists l : V, is_series a l.

Definition Series (a : nat -> R) : R :=
   real (Lim_seq (sum_n a)).

Lemma ex_series_dec (a : nat -> R) :
  {ex_series a} + {~ex_series a}.
Proof.
  case: (ex_lim_seq_dec (sum_n a)) => H.
  apply Lim_seq_correct in H.
  case: (Lim_seq (sum_n a)) H => [l | | ] H.
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
  apply (is_lim_seq_spec _ l) in H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  rewrite <- sum_n_sum_f_R0.
  by apply (H n Hn).
  apply (is_lim_seq_spec _ l).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  rewrite sum_n_sum_f_R0.
  by apply (H n Hn).
Qed.

Lemma ex_series_equiv_0 (a : nat -> R) :
  ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
  move => H ;
  exists (Series a) ; case: H => l H.
  replace (Series a) with l.
  move => e He ; set eps := mkposreal e He.
  apply (is_lim_seq_spec _ l) in H.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  rewrite <- sum_n_sum_f_R0.
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
  apply (is_lim_seq_spec _ l).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  rewrite sum_n_sum_f_R0.
  by apply (H n Hn).
Qed.

(** Extensionality *)

Lemma is_series_ext  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a b : nat -> V) (l : V) :
  (forall n, a n = b n) -> (is_series a l)
    -> is_series b l.
Proof.
  move => Heq.
  apply filterlim_ext.
  intros x; now apply sum_n_ext.
Qed.
Lemma ex_series_ext  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a b : nat -> V) :
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
  intros n; now apply sum_n_ext.
Qed.

(** Index offset *)

Lemma is_series_incr_1  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) (l : V) :
  is_series a (plus l  (a O))
    -> is_series (fun k => a (S k)%nat) l.
Proof.
  intros H.
  apply filterlim_ext with (fun k => plus (sum_n a (S k)) (opp (a 0%nat))).
  induction x; simpl.
  rewrite (plus_comm _ (a 1%nat)); rewrite <- plus_assoc.
  now rewrite plus_opp_r plus_zero_r.
  rewrite <- IHx; simpl.
  rewrite <- plus_assoc, <- (plus_assoc _ _ (a (S (S x)))).
  apply f_equal; apply plus_comm.
  apply filterlim_compose with (G:=(locally (plus l (a 0%nat)))) (g:=fun x => plus x (opp (a 0%nat))).
  (* . *)
  apply filterlim_compose with (f:= fun x => S x) (2:=H).
  apply eventually_subseq; intros n; omega.
  (* . *)
  pattern l at 2; replace l with (plus (plus l (a 0%nat)) (opp (a 0%nat))).
  apply filterlim_compose_2 with (3:=mvspace_plus _ _).
  apply filterlim_id.
  apply filterlim_const.
  rewrite <- plus_assoc, plus_opp_r.
  apply plus_zero_r.
Qed.

Lemma is_series_incr_n  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) (n : nat) (l : V) :
  (0 < n)%nat -> is_series a (plus l (sum_n a (pred n)))
    -> is_series (fun k => a (n + k)%nat) l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n l Ha => [ | n IH] l Ha.
  by apply is_series_incr_1.
  apply is_series_ext with (fun k : nat => a (S (n + S k))).
  move => k ; apply f_equal ; ring.
  apply (is_series_incr_1 (fun k : nat => a (S (n + k))) l).
  rewrite plus_0_r.
  apply IH.
  replace (plus (plus l (a (S n))) (sum_n a n)) with (plus l (sum_n a (S n))).
  assumption.
  rewrite <- plus_assoc; apply f_equal; simpl; apply plus_comm.
Qed.

Lemma is_series_decr_1  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) (l : V) :
  is_series (fun k => a (S k)%nat) (plus l (opp (a O))) -> is_series a l.
Proof.
  intros H.
  apply filterlim_ext_loc with (fun v => plus (a 0%nat) (sum_n (fun k : nat => a (S k)) (pred v))).
  exists 1%nat.
  intros n Hn; apply sym_eq.
  apply decomp_sum_n; omega.
  replace l with (plus (a 0%nat) (plus l (opp (a 0%nat)))).
  apply filterlim_compose_2 with (3:=mvspace_plus _ _).
  apply filterlim_id.
  apply filterlim_const.
  apply filterlim_compose with (f:= fun x => pred x) (2:=H).
  intros P (N1,HN1).
  exists (S N1).
  intros n Hn; apply HN1; omega.
  rewrite plus_comm; rewrite <- plus_assoc. 
  rewrite (plus_comm _ (a 0%nat)); rewrite plus_opp_r.
  apply plus_zero_r.
Qed.


Lemma is_series_decr_n  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) (n : nat) (l : V) :
  (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (plus l (opp (sum_n a (pred n))))
    -> is_series a l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n a l Ha => [ | n IH] a l Ha.
  by apply is_series_decr_1.
  apply is_series_decr_1.
  apply IH.
  replace (plus (plus l (opp (a 0%nat))) (opp (sum_n (fun k : nat => a (S k)) n)))
    with (plus l (opp (sum_n a (S n)))).
  by apply Ha.
  rewrite decomp_sum_n /=.
  rewrite <- plus_assoc.
  apply f_equal.
  now rewrite opp_plus.
  by apply lt_O_Sn.
Qed.

Lemma ex_series_decal_1  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) :
  ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
  split ; move => [la Ha].
  exists (plus la  (opp (a O))).
  apply is_series_incr_1.
  now rewrite <- plus_assoc, plus_opp_l, plus_zero_r.
  exists (plus la (a O)).
  apply is_series_decr_1.
  now rewrite <- plus_assoc, plus_opp_r, plus_zero_r.
Qed.
Lemma ex_series_decal_n (a : nat -> R) (n : nat) :
  ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
  case: n => [ | n].
  split ; apply ex_series_ext ; by intuition.
  split ; move => [la Ha].
  exists (plus la (opp (sum_n a (pred (S n))))).
  apply is_series_incr_n.
  by apply lt_O_Sn.
  now rewrite <- plus_assoc, plus_opp_l, plus_zero_r.
  exists (plus la (sum_n a (pred (S n)))).
  apply is_series_decr_n with (S n).
  by apply lt_O_Sn.
  now rewrite <- plus_assoc, plus_opp_r, plus_zero_r.
Qed.

Lemma Series_decal_1 (a : nat -> R) :
  ex_series a -> Series a = a O + Series (fun k => a (S k)).
Proof.
  move => Ha.
  apply is_series_unique.
  rewrite Rplus_comm.
  apply is_series_decr_1.
  unfold plus; simpl; ring_simplify (Series (fun k : nat => a (S k)) + a 0%nat +- a 0%nat).
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
  unfold plus; simpl; rewrite sum_n_sum_f_R0.
  ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) +-
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
  rewrite decomp_sum_n /=.
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
  apply cv_cauchy_2.
  by apply Hcv.
Qed.

Lemma ex_series_lim_0 (a : nat -> R) :
  ex_series a -> is_lim_seq a 0.
Proof.
  intros Hs.
  apply is_lim_seq_spec.
  intros eps.
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
  replace (Lim_seq (sum_n a)) with (Finite la).
  replace (Lim_seq (sum_n (fun k : nat => Rabs (a k)))) with (Finite lra).
  simpl.
  apply (is_lim_seq_abs _ la) in Ha.
  apply Rbar_finite_le.
  eapply is_lim_seq_le with (2:=Ha).
  2: apply Hra.
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

Lemma is_series_opp {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) (la : V) :
  is_series a la
    -> is_series (fun n => opp (a n)) (opp la).
Proof.
  move => Ha.
   apply filterlim_ext with (fun n => opp (sum_n a n)).
  elim => [ | n IH].
  simpl ; easy.
  simpl ; rewrite -IH.
  apply opp_plus.
  apply filterlim_compose with (1:=Ha).
  apply (filterlim_opp_2 la).
Qed.

Lemma ex_series_opp {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a : nat -> V) :
  ex_series a
    -> ex_series (fun n => opp (a n)).
Proof.
  move => [la Ha].
  exists (opp la).
  by apply is_series_opp.
Qed.
Lemma Series_opp (a : nat -> R) :
  Series (fun n => - a n) = - Series a.
Proof.
  rewrite /Series
    (Lim_seq_ext (sum_n (fun k : nat => - a k)) (fun n => - (sum_n (fun k => a k) n))).
  rewrite Lim_seq_opp.
  by rewrite Rbar_opp_real.
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite IH ; ring.
Qed.

Lemma is_series_plus  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a b : nat -> V) (la lb : V) :
  is_series a la -> is_series b lb
    -> is_series (fun n => plus (a n)  (b n)) (plus la  lb).
Proof.
  move => Ha Hb.
  apply filterlim_ext with (fun n => plus (sum_n a n) (sum_n b n)).
  elim => [ | n IH]; simpl.
  easy.
  rewrite -IH; rewrite <- 2!plus_assoc; apply f_equal.
  rewrite 2!plus_assoc; apply f_equal2; try easy.
  apply plus_comm.
  now apply filterlim_compose_2 with (3:=mvspace_plus _ _).
Qed.
Lemma ex_series_plus  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a b : nat -> V) :
  ex_series a -> ex_series b
    -> ex_series (fun n => plus (a n) (b n)).
Proof.
  move => [la Ha] [lb Hb].
  exists (plus la lb).
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

Lemma is_series_minus  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a b : nat -> V) (la lb : V) :
  is_series a la -> is_series b lb
    -> is_series (fun n => plus (a n) (opp (b n))) (plus la (opp lb)).
Proof.
  move => Ha Hb.
  apply is_series_plus => //.
  apply is_series_opp => //.
Qed.
Lemma ex_series_minus  {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (a b : nat -> V) :
  ex_series a -> ex_series b
    -> ex_series (fun n => plus (a n) (opp (b n))).
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
  apply ex_series_opp in Hb.
  now simpl in *.
Qed.

(** Multiplication by a scalar *)

Lemma is_series_scal {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (c : K) (a : nat -> V) (l : V) :
  is_series a l -> is_series (fun n => scal c  (a n)) (scal c l).
Proof.
  move => Ha.
  apply filterlim_ext with (fun n => scal c (sum_n a n)).
  elim => [ | n IH]; simpl.
  easy.
  rewrite -IH.
  apply scal_distr_l.
  now apply filterlim_compose with (2:=mvspace_scal _ _).
Qed.
Lemma is_series_scal_l {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K}: forall (c : K) (a : nat -> V) (l : V),
  is_series a l -> is_series (fun n => scal c  (a n)) (scal c l).
exact is_series_scal.
Qed.

Lemma ex_series_scal {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K} (c : K) (a : nat -> V) :
  ex_series a -> ex_series (fun n => scal c (a n)).
Proof.
  move => [l Ha].
  exists (scal c l).
  by apply: is_series_scal_l.
Qed.

Lemma ex_series_scal_l {K} {V} {FK : ncRing K} {VV : MetricVectorSpace V K}: forall (c : K) (a : nat -> V),
  ex_series a -> ex_series (fun n => scal c  (a n)).
exact ex_series_scal.
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
  is_series a l -> is_series (fun n => (a n) * c) (l * c).
Proof.
  move => Ha.
  rewrite Rmult_comm.
  apply is_series_ext with (fun n : nat => c * a n).
  move => n ; apply Rmult_comm.
  apply (is_series_scal_l _ _ _ Ha).
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
    replace (S n + S n - S (S n))%nat with n.
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
    rewrite ?(Coq.Arith.Plus.plus_comm _ (S m)) -minus_plus_simpl_l_reverse //=.
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
    replace (S (S n)) with (S n + 1)%nat.
    rewrite -minus_plus_simpl_l_reverse.
    simpl; apply minus_n_O.
    now rewrite Coq.Arith.Plus.plus_comm.
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

    change (is_lim_seq (sum_n (fun n : nat => sum_f_R0 (fun k : nat => a k * b (n - k)%nat) n)) (Finite (la * lb))).
    apply is_lim_seq_le_le with (u := fun n => sum_f_R0 a (Div2.div2 n) * sum_f_R0 b (Div2.div2 n))
    (w := fun n => sum_f_R0 a n * sum_f_R0 b n).
    intros n; rewrite sum_n_sum_f_R0.
    by split.
    replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
    suff H : is_lim_seq
      (fun n : nat => sum_f_R0 a n * sum_f_R0 b n)
      (Rbar_mult la lb).
    apply is_lim_seq_spec in H.
    apply is_lim_seq_spec.
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
    apply filterlim_ext with (2:=Hla); apply sum_n_sum_f_R0.
    apply filterlim_ext with (2:=Hlb); apply sum_n_sum_f_R0.
    by [].
    replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
    apply is_lim_seq_mult.
    apply filterlim_ext with (2:=Hla); apply sum_n_sum_f_R0.
    apply filterlim_ext with (2:=Hlb); apply sum_n_sum_f_R0.
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
  assert (Sap : ex_series ap).
    apply ex_series_scal_r.
    apply: ex_series_plus => //.
    by exists la.
  have Ham : forall n, 0 <= am n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (a _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  assert (Sam : ex_series am).
    apply ex_series_scal_r.
    apply: ex_series_opp.
    apply: ex_series_minus => //.
    by exists la.
  have Hbp : forall n, 0 <= bp n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  assert (Sbp : ex_series bp).
    apply ex_series_scal_r.
    apply: ex_series_plus => //.
    by exists lb.
  have Hbm : forall n, 0 <= bm n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (b _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  assert (Sbm : ex_series bm).
    apply ex_series_scal_r.
    apply: ex_series_opp.
    apply: ex_series_minus => //.
    by exists lb.

  apply is_series_ext with (fun n => sum_f_R0 (fun k : nat => ap k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => am k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => ap k * bm (n - k)%nat) n
    + sum_f_R0 (fun k : nat => am k * bm (n - k)%nat) n).
  move => n.
  rewrite -?minus_sum -plus_sum.
  apply sum_eq => k _.
  rewrite /ap /am /bp /bm ; field.
  replace (la*lb) with ((Series ap*Series bp-Series am*Series bp-Series ap*Series bm)+Series am*Series bm).
  apply: is_series_plus.
  apply: is_series_minus.
  apply: is_series_minus.
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
    apply is_lim_seq_spec in H.
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
  apply: ex_series_scal_l.
  set k0 := ((k + 1) / 2).
  exists (/(1-k0) * (1-k0*0)).
  apply filterlim_ext with (fun N => / (1 - k0) * (1 - k0 ^ S N)). 
  move => n ; rewrite sum_n_sum_f_R0; rewrite tech3.
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
    apply is_lim_seq_spec in Hda.
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
  apply filterlim_ext with (fun n => (1-q^(S n)) / (1-q)).
  move => n.
  rewrite sum_n_sum_f_R0; rewrite tech3.
  reflexivity.
  apply Rlt_not_eq.
  apply Rle_lt_trans with (2 := Hq).
  apply Rle_abs.
  change (is_lim_seq (fun n : nat => (1 - q ^ S n) / (1 - q)) (/(1-q))).
  replace ((/ (1 - q))) with (real (Rbar_mult (Rbar_minus 1 0) (/ (1 - q)))).
  unfold Rdiv.
  apply (is_lim_seq_scal_r (fun n : nat => (1 - q ^ S n)) (/ (1 - q)) (Rbar_minus 1 0)).
  apply is_lim_seq_minus.
  by apply is_lim_seq_const.
  apply (is_lim_seq_incr_1 (fun n => q^n)).
  by apply is_lim_seq_geom.
  easy.
  simpl; ring.  
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
