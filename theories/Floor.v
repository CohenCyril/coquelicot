Require Import RIneq.
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
