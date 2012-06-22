Require Import Reals Max.
Require Import ConstructiveEpsilon.
Open Scope R_scope.

(** * Integer part *)
(** ** to Z *)

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

(** ** to nat *)

Lemma nfloor_ex : forall x : R, 0 <= x -> {n : nat | INR n <= x < INR n + 1}.
Proof.
  intros.
  destruct (floor_ex x) as (m,Hm).
  destruct (Z_lt_le_dec m 0) as [z|z].
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

(** * Discrete logarithm *)

Lemma log_x_lt_1_ex (x y : R) : 0 < x < 1 -> 0 < y <= 1 -> {n : nat |  x^(S n) < y <= x^n}.
Proof.
  intros Hx Hy.
  apply constructive_indefinite_description_nat.
    intros n.
    destruct (Rle_dec y (x^n)) as [H1|H1].
    destruct (Rle_dec y (x^(S n))) as [H2|H2].
    right.
    intros H3.
    now apply Rle_not_lt with (1 := H2).
    left.
    split.
    now apply Rnot_le_lt with (1 := H2).
    exact H1.
    right.
    easy.
  assert (Hx': Rabs x < 1).
    rewrite Rabs_pos_eq.
    apply Hx.
    now apply Rlt_le.
  destruct (pow_lt_1_zero x Hx' y (proj1 Hy)) as [N H4].
  assert (HN: x^(S N) < y).
    rewrite <- (Rabs_pos_eq x).
    rewrite RPow_abs.
    apply H4.
    now apply le_S.
    now apply Rlt_le.
  clear H4.
  set (g := fix g n := if Rle_dec y (x^n) then n else match n with O => O | S n => g n end).
  exists (g N).
  induction N ; simpl.
    case Rle_dec.
    now split.
    easy.
  case Rle_dec.
  now split.
  intros H.
  apply IHN.
  now apply Rnot_le_lt.
Qed.
Definition log_x_lt_1 (x y : R) pr_x pr_y := projT1 (log_x_lt_1_ex x y pr_x pr_y).
