Require Export Reals Max.
Open Scope R_scope.

(** * Définitions de parties entières *)
(** ** Dans Z *)

Lemma floor_ex : forall x : R, {n : Z | IZR n <= x < IZR n + 1}.
Proof.
  intros.
  exists (up (x-1)) ; split.
  assert (Rw : x = 1 + (x-1)) ; [ring | pattern x at 2 ; rewrite Rw ; clear Rw].
  assert (Rw :IZR (up (x - 1))  = (IZR (up (x - 1)) - (x - 1)) + (x-1)) ; 
    [ring | rewrite Rw ; clear Rw].
  apply Rplus_le_compat_r, (proj2 (archimed _)).
  assert (Rw : x = (x-1) + 1) ; [ring | pattern x at 1 ; rewrite Rw ; clear Rw].
  apply Rplus_lt_compat_r, (proj1 (archimed _)).
Qed.
Definition floor x := projT1 (floor_ex x).

Lemma floor1_ex : forall x : R, {n : Z | IZR n < x <= IZR n + 1}.
Proof.
  intros.
  destruct (floor_ex x) as (n,(Hn1,Hn2)).
  destruct (Rle_lt_or_eq_dec (IZR n) x Hn1).
  exists n ; split.
  apply r.
  apply Rlt_le, Hn2.
  exists (Zpred n) ; rewrite <- e ; split.
  apply IZR_lt, Zlt_pred.
  rewrite <- (succ_IZR), <-Zsucc_pred ; apply Rle_refl.
Qed.
Definition floor1 x := projT1 (floor1_ex x).

(** ** Dans nat *)

Lemma nfloor_ex : forall x : R, 0 <= x -> {n : nat | INR n <= x < INR n + 1}.
Proof.
  intros.
  destruct (floor_ex x) as (m,Hm).
  destruct (Z_lt_le_dec m 0).
  apply Zlt_le_succ in z.
  contradict z.
  apply Zlt_not_le.
  apply lt_IZR.
  apply Rle_lt_trans with (1 := H).
  rewrite succ_IZR ; apply Hm.
  destruct m.
  exists O ; apply Hm.
  exists (nat_of_P p).
  rewrite INR_IZR_INZ.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  apply Hm.
  contradict z.
  apply Zlt_not_le.
  apply Zlt_neg_0.
Qed.
Definition nfloor x pr := projT1 (nfloor_ex x pr).

Lemma nfloor1_ex : forall x : R, 0 < x -> {n : nat | INR n < x <= INR n + 1}.
Proof.
  intros.
  destruct (nfloor_ex x (Rlt_le _ _ H)) as (n,(Hn1,Hn2)).
  destruct (Rle_lt_or_eq_dec (INR n) x Hn1).
  exists n ; split.
  apply r.
  apply Rlt_le, Hn2.
  destruct n.
  contradict H.
  rewrite <- e ; simpl ; apply Rlt_irrefl.
  exists n ; rewrite <- e ; split.
  apply lt_INR, lt_n_Sn.
  rewrite <- (S_INR) ; apply Rle_refl.
Qed.
Definition nfloor1 x pr := projT1 (nfloor1_ex x pr).

Lemma nfloor2_ex : forall x : R, x < 1 -> {n : nat | - INR n <= x < - INR n + 1}.
Proof.
  intros.
  destruct (nfloor1_ex (1-x) (Rlt_Rminus _ _ H)) as (n,(Hn1,Hn2)).
  exists n ; split.
  apply Ropp_le_cancel, (Rplus_le_reg_l 1) ; rewrite Ropp_involutive, <- (Rplus_comm (INR n)) ;
  apply Hn2.
  apply Ropp_lt_cancel.
  assert (Rw : - (- INR n + 1) = (INR n) + -1) ; 
    [ring|rewrite Rw ; clear Rw].
  assert (Rw : - x = (1-x) + -1) ; 
    [ring|rewrite Rw ; clear Rw].
  apply Rplus_lt_compat_r, Hn1.
Qed.
Definition nfloor2 x pr := projT1 (nfloor2_ex x pr).

Lemma nfloor3_ex : forall x : R, x <= 1 -> {n : nat | - INR n < x <= - INR n + 1}.
Proof.
  intros.
  destruct (nfloor_ex (1-x)) as (n,(Hn1,Hn2)).
  apply (Rplus_le_reg_l (-1)) ; ring_simplify ; apply Ropp_le_contravar, H.
  exists n ; split.
  apply Ropp_lt_cancel, (Rplus_lt_reg_r 1) ; rewrite Ropp_involutive, <- (Rplus_comm (INR n)) ;
  apply Hn2.
  apply Ropp_le_cancel.
  assert (Rw : - (- INR n + 1) = (INR n) + -1) ; 
    [ring|rewrite Rw ; clear Rw].
  assert (Rw : - x = (1-x) + -1) ; 
    [ring|rewrite Rw ; clear Rw].
  apply Rplus_le_compat_r, Hn1.
Qed.
Definition nfloor3 x pr := projT1 (nfloor3_ex x pr).

(** * Logarithme entier *)
(** ** Dans Z *)

Lemma Zlog_1_lt_x_ex (x y : R) : 1 < x -> 0 < y -> 
  {n : Z |  Rpower x (IZR n) <= y < Rpower x (IZR n + 1)}.
Proof.
  intros.
  assert (ln_x : 0 < ln x).
    rewrite <- ln_1 ; apply ln_increasing ; [apply Rlt_0_1|apply H].
  assert (Rw : ln y = (ln y / ln x) * ln x).
    field ; apply Rgt_not_eq, ln_x.
  destruct (floor_ex (ln y / ln x)) as (n,(Hn1,Hn2)).
  exists n ; rewrite <- (exp_ln y H0) ; split.
  destruct Hn1 as [Hn1|Hn1] ; [apply Rlt_le | apply Req_le].
  apply exp_increasing ;
  rewrite Rw ;
  apply Rmult_lt_compat_r with (1 := ln_x), Hn1.
  rewrite Hn1 ;
  pattern (ln y) at 2 ; rewrite Rw ;
  reflexivity.
  apply exp_increasing ;
  rewrite Rw ; 
  apply Rmult_lt_compat_r with (1 := ln_x), Hn2.
Qed.
Definition Zlog_1_lt_x (x y : R) pr_x pr_y := projT1 (Zlog_1_lt_x_ex x y pr_x pr_y).

Lemma Zlog_x_lt_1_ex (x y : R) : 0 < x < 1 -> 0 < y -> 
  {n : Z |  Rpower x (IZR n + 1) < y <= Rpower x (IZR n)}.
Proof.
  intros.
  assert (ln_x : 0 < - ln x).
    rewrite <- Ropp_0, <- ln_1 ; apply Ropp_lt_contravar, ln_increasing ; apply H.
  assert (Rw : ln y = (ln y / ln x) * ln x).
    field ; apply Rlt_not_eq, Ropp_lt_cancel ; rewrite Ropp_0 ; apply ln_x.
  destruct (floor_ex (ln y / ln x)) as (n,(Hn1,Hn2)).
  exists n ; rewrite <- (exp_ln y H0) ; split.
  apply exp_increasing ; rewrite Rw ;
  apply Ropp_lt_cancel ;
  repeat rewrite <- (Ropp_mult_distr_r_reverse) ;
  apply Rmult_lt_compat_r with (1 := ln_x), Hn2.
  destruct Hn1 as [Hn1|Hn1] ; [apply Rlt_le | apply Req_le].
  apply exp_increasing ; rewrite Rw ;
  apply Ropp_lt_cancel ;
  repeat rewrite <- (Ropp_mult_distr_r_reverse) ;
  apply Rmult_lt_compat_r with (1 := ln_x), Hn1.
  rewrite Hn1 ;
  pattern (ln y) at 1 ; rewrite Rw ;
  reflexivity.
Qed.
Definition Zlog_x_lt_1 (x y : R) pr_x pr_y := projT1 (Zlog_x_lt_1_ex x y pr_x pr_y).

(** ** dans nat *)

Lemma log_1_lt_x_ex (x y : R) : 1 < x -> 1 <= y -> {n : nat |  x^n <= y < x^(S n)}.
Proof.
  intros Hx Hy.
  assert (Hx1 : 0 < x).
    apply Rlt_trans with (1 := Rlt_0_1), Hx.
  assert (Hx2 : 0 < ln x).
    rewrite <- ln_1 ; apply ln_increasing ; [apply Rlt_0_1| apply Hx].
  assert (Hy1 : 0 < y).
    apply Rlt_le_trans with (1 := Rlt_0_1), Hy.
  assert (Hy2 : 0 <= ln y).
    rewrite <- ln_1 ;
    destruct (Rle_lt_or_eq_dec 1 y Hy).
    apply Rlt_le, ln_increasing ; [apply Rlt_0_1| apply r].
    rewrite e ; apply Rle_refl.
  destruct (nfloor_ex (ln y/ln x)) as (n,Hn).
    unfold Rdiv ; apply Rmult_le_pos.
    apply Hy2.
    apply Rlt_le, Rinv_0_lt_compat, Hx2.
  exists n.
  repeat rewrite <- (Rpower_pow _ _ Hx1).
  rewrite <- (exp_ln y Hy1).
  unfold Rpower ; split.
  destruct (Rle_lt_or_eq_dec (INR n) (ln y / ln x) (proj1 Hn)).
  apply Rlt_le, exp_increasing.
  assert (Rw : ln y = (ln y / ln x) * ln x) ; 
    [field ; apply Rgt_not_eq, Hx2|rewrite Rw ; clear Rw].
  apply Rmult_lt_compat_r with (1 := Hx2), r.
  assert (Rw : INR n * ln x = ln y) ; 
    [rewrite e ; field ; apply Rgt_not_eq, Hx2 | rewrite Rw ; clear Rw].
  apply Rle_refl.
  apply exp_increasing.
  assert (Rw : ln y = (ln y / ln x) * ln x) ; 
    [field ; apply Rgt_not_eq, Hx2|rewrite Rw ; clear Rw].
  rewrite S_INR ; apply Rmult_lt_compat_r with (1 := Hx2), Hn.
Qed.
Definition log_1_lt_x (x y : R) pr_x pr_y := projT1 (log_1_lt_x_ex x y pr_x pr_y).

Lemma log_x_lt_1_ex (x y : R) : 0 < x < 1 -> 0 < y <= 1 -> {n : nat |  x^(S n) < y <= x^n}.
Proof.
  intros.
  destruct (log_1_lt_x_ex (/x) (/y)) as (n,Hn).
  rewrite <- Rinv_1 ; apply Rinv_lt_contravar.
  rewrite Rmult_1_r ; apply H.
  apply H.
  rewrite <- Rinv_1 ; apply Rle_Rinv.
  apply H0.
  apply Rlt_0_1.
  apply H0.
  exists n ; split.
  assert (Rw : x ^ S n = (/y) * (y * x^(S n))) ;
    [field ; apply Rgt_not_eq, H0|rewrite Rw ; clear Rw].
  assert (Rw : y = (/x^(S n)) * (y * x^(S n))) ;
    [field ; apply Rgt_not_eq, pow_lt, H|pattern y at 3 ; rewrite Rw ; clear Rw].
  apply Rmult_lt_compat_r.
  apply Rmult_lt_0_compat.
  apply H0.
  apply pow_lt, H.
  rewrite Rinv_pow.
  apply Hn.
  apply Rgt_not_eq, H.
  assert (Rw : x ^ n = (/y) * (y * x^(n))) ;
    [field ; apply Rgt_not_eq, H0|rewrite Rw ; clear Rw].
  assert (Rw : y = (/x^( n)) * (y * x^( n))) ;
    [field ; apply Rgt_not_eq, pow_lt, H|pattern y at 1 ; rewrite Rw ; clear Rw].
  apply Rmult_le_compat_r.
  apply Rlt_le, Rmult_lt_0_compat.
  apply H0.
  apply pow_lt, H.
  rewrite Rinv_pow.
  apply Hn.
  apply Rgt_not_eq, H.
Qed.
Definition log_x_lt_1 (x y : R) pr_x pr_y := projT1 (log_x_lt_1_ex x y pr_x pr_y).