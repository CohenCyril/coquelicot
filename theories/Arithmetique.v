Require Import Reals.

Open Scope R_scope.

(** * Opérations sur Rdiv *)

Lemma Rdiv_1 : forall x : R, x = x/1.
Proof.
  intros.
  field.
Qed.

Lemma Rdiv_plus : forall a b c d : R, b <> 0 -> d <> 0 -> a/b+c/d = (a*d + c*b)/(b*d).
Proof.
  intros.
  field.
  split.
  apply H0.
  apply H.
Qed.

Lemma Rdiv_minus : forall a b c d : R, b <> 0 -> d <> 0 -> a/b-c/d = (a*d - c*b)/(b*d).
Proof.
  intros.
  field.
  split.
  apply H0.
  apply H.
Qed.

Lemma Rle_div : forall a b c, c>0 -> (a / c <= b <-> a <= b*c).
Proof.
  unfold Rdiv.
  split.
  intros.
  rewrite <-(Rmult_1_r a).
  rewrite <-(Rinv_l c).
  rewrite <-Rmult_assoc.
  apply Rmult_le_compat_r.
  apply Rlt_le.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.

  intros.
  rewrite <-(Rmult_1_r b).
  rewrite <-(Rinv_r c).
  rewrite <-Rmult_assoc.
  apply Rmult_le_compat_r.
  apply Rlt_le.
  apply Rinv_0_lt_compat.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.
Qed.

Lemma Rle_div2 : forall a b c, c>0 -> (a * c <= b <-> a <= b/c).
Proof.
  unfold Rdiv.
  split.
  intros.
  rewrite <-(Rmult_1_r a).
  rewrite <-(Rinv_r c).
  rewrite <-Rmult_assoc.
  apply Rmult_le_compat_r.
  apply Rlt_le.
  apply Rinv_0_lt_compat.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.

  intros.
  rewrite <-(Rmult_1_r b).
  rewrite <-(Rinv_l c).
  rewrite <-Rmult_assoc.
  apply Rmult_le_compat_r.
  apply Rlt_le.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.
Qed.

Lemma Rinv_eq_compat : forall r1 r2 : R, r1 = r2 -> /r1 = /r2.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(** * Opérations sur Rminus *)
Lemma Rminus_eq0 : forall r : R, r-r = 0.
Proof.
  intros.
  ring.
Qed.


Lemma Rle_minus2 : forall a b c,(a - c <= b <-> a <= b+c).
Proof.
  unfold Rminus.
  split.
  intros.
  rewrite <-(Rplus_0_r a).
  rewrite <-(Rplus_opp_l c).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  apply H.

  intros.
  rewrite <-(Rplus_0_r b).
  rewrite <-(Rplus_opp_r c).
  rewrite <-Rplus_assoc.
  apply Rplus_le_compat_r.
  apply H.
Qed.

Lemma Lem1 : forall a b c, b <> 0 -> a/b-c = (a-b*c)/b.
Proof.
    intros.
    field.
    apply H.
Qed.

Lemma Rlt_div : forall a b c, c>0 -> (a / c < b <-> a < b*c).
Proof.
  unfold Rdiv.
  split.
  intros.
  rewrite <-(Rmult_1_r a).
  rewrite <-(Rinv_l c).
  rewrite <-Rmult_assoc.
  apply Rmult_lt_compat_r.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.

  intros.
  rewrite <-(Rmult_1_r b).
  rewrite <-(Rinv_r c).
  rewrite <-Rmult_assoc.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.
Qed.

Lemma Lem5 : forall a b c, b > 0 -> (a < b * c <-> a / b < c).
Proof.
  split.

  intros.
  rewrite <-(Rmult_1_r c).
  rewrite (Rinv_r_sym b).
  rewrite <-Rmult_assoc.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat.
  apply Rgt_lt.
  apply H.
  rewrite Rmult_comm.
  apply H0.
  apply Rgt_not_eq.
  apply H.

  intros.
  rewrite <-(Rmult_1_r a).
  rewrite (Rinv_l_sym b).
  rewrite <-Rmult_assoc.
  rewrite (Rmult_comm b c).
  apply Rmult_lt_compat_r.
  apply Rgt_lt.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.
Qed.

Lemma Rdiv_lt_0_compat : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 0 < r1 / r2.
Proof.
  intros r1 r2 H1 H2.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  apply H1.
  apply Rinv_0_lt_compat.
  apply H2.
Qed.

Lemma Rdiv_le_pos : forall r1 r2 : R, 0 <= r1 -> 0 < r2 -> 0 <= r1 / r2.
Proof.
 intros.
 unfold Rdiv.
 apply Rmult_le_pos.
 apply H.
 apply Rlt_le.
 apply Rinv_0_lt_compat.
 apply H0.
Qed.

Lemma Rdiv_le_1 : forall r1 r2, 0 < r2 -> (r1 <= r2 <-> r1/r2 <= 1).
Proof.
  split.
  intros.
  unfold Rdiv.
  rewrite (Rinv_r_sym r2).
  apply Rmult_le_compat_r.
  apply Rlt_le.
  apply Rinv_0_lt_compat.
  apply H.
  apply H0.
  apply Rgt_not_eq.
  apply H.

  intros.
  apply (Rmult_le_reg_l (/r2)).
  apply Rinv_0_lt_compat.
  apply H.
  repeat rewrite (Rmult_comm (/r2)).
  rewrite <- Rinv_r_sym.
  apply H0.
  apply Rgt_not_eq.
  apply H.
Qed.

Lemma Rmult_minus_distr_r: forall r1 r2 r3 : R, (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
  intros.
  unfold Rminus.
  rewrite <- Ropp_mult_distr_l_reverse.
  apply Rmult_plus_distr_r.
Qed.

Lemma Rminus_eq_compat_l : forall r r1 r2 : R, r1 = r2 -> r - r1 = r - r2.
Proof.
  intros.
  unfold Rminus.
  apply Rplus_eq_compat_l.
  rewrite H.
  reflexivity.
Qed.

Lemma Ropp_plus_minus_distr : forall r1 r2 : R, - (r1 + r2) = - r1 - r2.
Proof.
  intros.
  unfold Rminus.
  apply Ropp_plus_distr.
Qed.

Lemma Ropp_minus_distr : forall r1 r2 : R, - (r1 - r2) = - r1 + r2.
Proof.
  intros.
  assert (- r1 + r2 = -r1 --r2).
    ring.
    rewrite H ; clear H.
  apply Ropp_plus_distr.
Qed.

Lemma Rminus_le_0 : forall a b, a <= b <-> 0 <= b - a.
Proof.
  split.
  intros.
  rewrite <- (Rminus_eq0 a).
  apply Rplus_le_compat_r.
  apply H.

  intros.
  rewrite <- (Rplus_0_r a).
  rewrite <- (Rplus_0_r b).
  rewrite <- (Rplus_opp_l a).
  repeat rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  rewrite Rplus_opp_r.
  apply H.
Qed.

Lemma Rminus_gt_0 : forall a b, a > b <-> 0 > b - a.
Proof.
  split.
  intros.
  rewrite <- (Rminus_eq0 a).
  apply Rplus_lt_compat_r.
  apply H.

  intros.
  rewrite <- (Rplus_0_r a).
  rewrite <- (Rplus_0_r b).
  rewrite <- (Rplus_opp_l a).
  repeat rewrite <- Rplus_assoc.
  apply Rplus_lt_compat_r.
  rewrite Rplus_opp_r.
  apply H.
Qed.

(** * Réécritures sur Rmin et Rmax *)

Lemma Rmin_eq_l : forall a b : R, a <= b -> Rmin a b = a.
Proof.
  intros.
  unfold Rmin.
  destruct (Rle_dec a b).
  reflexivity.
  elim n.
  apply H.
Qed.

Lemma Rmin_eq_r : forall a b : R, a > b -> Rmin a b = b.
Proof.
  intros.
  unfold Rmin.
  destruct (Rle_dec a b).
  apply Rgt_not_le in H.
  elim H.
  apply r.
  reflexivity.
Qed.

Lemma Rmax_eq_l : forall a b : R, a <= b -> Rmax a b = b.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a b).
  reflexivity.
  elim n.
  apply H.
Qed.

Lemma Rmax_eq_r : forall a b : R, a > b -> Rmax a b = a.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a b).
  apply Rgt_not_le in H.
  elim H.
  apply r.
  reflexivity.
Qed.


Lemma Rmax_le : forall a b c d, a <= b -> c <= d -> Rmax a c <= Rmax b d.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a c).
  destruct (Rle_dec b d).
    apply H0.
    apply Rnot_le_lt in n.
    apply (Rle_trans _ d).
    apply H0.
    apply (Rlt_le _ _ n).
  destruct (Rle_dec b d).
    apply (Rle_trans _ b).
    apply H.
    apply r.
    apply H.
Qed.

Lemma Rmax_opp_Rmin : forall a b, Rmax (-a) (-b) = - Rmin a b.
Proof.
  intros.
  destruct (Rtotal_order a b).

  rewrite Rmax_eq_r.
  rewrite Rmin_eq_l.
  reflexivity.
  apply Rlt_le.
  apply H.
  apply Ropp_lt_gt_contravar.
  apply H.
  destruct H.

  rewrite H.
  rewrite Rmax_eq_l.
  rewrite Rmin_eq_l.
  reflexivity.
  apply Req_le.
  reflexivity.
  apply Req_le.
  reflexivity.

  rewrite Rmax_eq_l.
  rewrite Rmin_eq_r.
  reflexivity.
  apply H.
  apply Ropp_ge_le_contravar.
  apply Rgt_ge.
  apply H.
Qed.

Lemma Rmax_mult : forall a b c, 0 <= c -> Rmax a b * c = Rmax (a * c) (b * c).
Proof.
  intros.
  repeat rewrite (Rmult_comm _ c).
  apply sym_eq.
  apply RmaxRmult.
  apply H.
Qed.

Lemma Rmax_le_Rplus : forall a b : R, 0 <= a -> 0 <= b -> Rmax a b <= a + b.
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  rewrite <- (Rplus_0_l (Rmax a b)).
  rewrite Rmax_eq_l.
  apply Rplus_le_compat_r.
  apply H.
  apply r.
  rewrite <- (Rplus_0_r (Rmax a b)).
  rewrite Rmax_eq_r.
  apply Rplus_le_compat_l.
  apply H0.
  apply r.
Qed.

Lemma Rplus_le_Rmax : forall a b : R, a + b <= 2*Rmax a b.
Proof.
  intros.
  rewrite double.
  destruct (Rle_lt_dec a b).
  rewrite Rmax_eq_l.
  apply Rplus_le_compat_r.
  apply r.
  apply r.
  rewrite Rmax_eq_r.
  apply Rplus_le_compat_l.
  apply Rlt_le.
  apply r.
  apply r.
Qed.

Lemma Rmin_Rmax : forall a b, Rmin a b <= Rmax a b.
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  rewrite (Rmin_eq_l _ _ r).
  rewrite (Rmax_eq_l _ _ r).
  apply r.
  rewrite (Rmin_eq_r _ _ r).
  rewrite (Rmax_eq_r _ _ r).
  apply Rlt_le.
  apply r.
Qed.

Lemma Rmin_Rmax_l : forall a b, Rmin a b <= a <= Rmax a b.
Proof.
  split.
  apply Rmin_l.
  apply RmaxLess1.
Qed.

Lemma Rmin_Rmax_r : forall a b, Rmin a b <= b <= Rmax a b.
Proof.
  split.
  apply Rmin_r.
  apply RmaxLess2.
Qed.

Lemma Rmin_le : forall a b c, a <= b -> a <= c -> a <= Rmin b c.
Proof.
  intros.
  unfold Rmin.
  destruct (Rle_dec b c).
  apply H.
  apply H0.
Qed.

Lemma Rmax_lub_lt : forall a b c, a < c -> b < c -> Rmax a b < c.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a b).
  apply H0.
  apply H.
Qed.

Lemma Rmax_lub : forall a b c, a <= c -> b <= c -> Rmax a b <= c.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a b).
  apply H0.
  apply H.
Qed.

(** * Rabs *)

Lemma Rabs_div : forall a b : R, b <> 0 -> Rabs (a/b) = (Rabs a) / (Rabs b).
Proof.
  intros.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_Rinv.
  reflexivity.
  apply H.
Qed.

Lemma Rabs_le_encadre : forall x y, (Rabs x <= y <-> -y <= x <= y).
Proof.
  split.

  split.
  rewrite <-(Ropp_involutive x).
  apply Ropp_le_contravar.
  apply (Rle_trans _ (Rabs x)).
  rewrite <-Rabs_Ropp.
  apply RRle_abs.
  apply H.
  apply (Rle_trans _ (Rabs x)).
  apply RRle_abs.
  apply H.

  intros.
  unfold Rabs.
  destruct (Rcase_abs x).
  rewrite <-(Ropp_involutive y).
  apply Ropp_le_contravar.
  apply H.
  apply H.
Qed.

Lemma Rabs_le_encadre_cor : forall x y z, Rabs (x - y) <= z <-> y-z <= x <= y+z.
Proof.
  split ; intros.
  cut (-z <= x-y <= z).
  intros ; split.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite Rplus_comm.
  apply H0.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite Rplus_comm.
  apply H0.
  apply (Rabs_le_encadre (x-y) z).
  apply H.

  apply (Rabs_le_encadre (x-y) z).
  split.
  rewrite <- (Rplus_0_r (-z)).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  rewrite Rplus_comm.
  apply H.
  rewrite <- (Rplus_0_r z).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  rewrite Rplus_comm.
  apply H.
Qed.

Lemma Rabs_lt_encadre : forall x y, (Rabs x < y <-> -y < x < y).
Proof.
  split.

  split.
  rewrite <-(Ropp_involutive x).
  apply Ropp_lt_contravar.
  apply (Rle_lt_trans _ (Rabs x)).
  rewrite <-Rabs_Ropp.
  apply RRle_abs.
  apply H.
  apply (Rle_lt_trans _ (Rabs x)).
  apply RRle_abs.
  apply H.

  intros.
  unfold Rabs.
  destruct (Rcase_abs x).
  rewrite <-(Ropp_involutive y).
  apply Ropp_lt_contravar.
  apply H.
  apply H.
Qed.

Lemma Rabs_lt_encadre_cor : forall x y z, Rabs (x - y) < z <-> y-z < x < y+z.
Proof.
  split ; intros.
  cut (-z < x-y < z).
  intros ; split.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_lt_compat_l.
  rewrite Rplus_comm.
  apply H0.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_lt_compat_l.
  rewrite Rplus_comm.
  apply H0.
  apply (Rabs_lt_encadre (x-y) z).
  apply H.

  apply (Rabs_lt_encadre (x-y) z).
  split.
  rewrite <- (Rplus_0_r (-z)).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_lt_compat_r.
  rewrite Rplus_comm.
  apply H.
  rewrite <- (Rplus_0_r z).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_lt_compat_r.
  rewrite Rplus_comm.
  apply H.
Qed.

Lemma Rabs_eq_0 : forall x, Rabs x = 0 -> x = 0.
Proof.
  intros.
  unfold Rabs in H.
  destruct Rcase_abs.
  rewrite <- (Ropp_involutive x).
  apply Ropp_eq_0_compat.
  apply H.
  apply H.
Qed.

Lemma Rabs_maj1 : forall x, x <= Rabs x.
Proof.
  intros ; unfold Rabs.
  destruct (Rcase_abs x).
  apply Rlt_le ;
  apply (Rlt_trans _ 0).
  apply r.
  apply Ropp_0_gt_lt_contravar.
  apply r.
  apply Rle_refl.
Qed.

Lemma Rabs_maj2 : forall x, -x <= Rabs x.
Proof.
  intros.
  rewrite <- Rabs_Ropp.
  apply Rabs_maj1.
Qed.


(** * Rplus *)

Lemma Rplus_eq_compat : forall r1 r2 r3 r4 : R, r1 = r2 -> r3 = r4 -> r1 + r3 = r2 + r4.
Proof.
  intros.
  assert (r1 + r3 = r1 + r4).
    apply Rplus_eq_compat_l.
    apply H0.
  apply (trans_eq H1).
  repeat rewrite <-(Rplus_comm r4).
  apply Rplus_eq_compat_l.
  apply H.
Qed.

(** * Rmult *)

Lemma Rmult_eq_compat : forall r1 r2 r3 r4 : R, r1 = r2 -> r3 = r4 -> r1 * r3 = r2 * r4.
Proof.
  intros.
  assert (r1 * r3 = r1 * r4).
    apply Rmult_eq_compat_l.
    apply H0.
  apply (trans_eq H1).
  repeat rewrite <-(Rmult_comm r4).
  apply Rmult_eq_compat_l.
  apply H.
Qed.

Lemma Rmult_le_reg_r : forall r r1 r2 : R, 0 < r -> r1 * r <= r2 * r -> r1 <= r2.
Proof.
  intros.
  apply (Rmult_le_reg_l r).
  apply H.
  repeat rewrite (Rmult_comm r).
  apply H0.
Qed.

Lemma Rle_mult_Rlt : forall c a b : R, 0 < b -> c < 1 -> a <= b*c -> a < b.
Proof.
  intros.
  apply Rle_lt_trans with (1 := H1).
  pattern b at 2 ; rewrite <-(Rmult_1_r b).
  apply Rmult_lt_compat_l ; auto.
Qed.

Lemma Rmult_le_0_r : forall a b, a <= 0 -> 0 <= b -> a * b <= 0.
Proof.
  intros ;
  rewrite <-(Rmult_0_r a) ;
  apply (Rmult_le_compat_neg_l a 0 b) with (1 := H) ; auto.
Qed.
Lemma Rmult_le_0_l : forall a b, 0 <= a -> b <= 0 -> a * b <= 0.
Proof.
  intros ; rewrite Rmult_comm ; apply Rmult_le_0_r ; auto.
Qed.

(** * Order *)

(** Req *)

Lemma Req_lt_aux : forall x y, (forall eps : posreal, Rabs (x - y) < eps) -> x = y.
Proof.
  intros.
  apply Rminus_diag_uniq.
  apply Rabs_eq_0.
  apply Rle_antisym.
  apply le_epsilon.
  intros.
  rewrite Rplus_0_l.
  apply Rlt_le.
  apply (H (mkposreal eps H0)).
  apply Rabs_pos.
Qed.

Lemma Req_le_aux : forall x y, (forall eps : posreal, Rabs (x - y) <= eps) -> x = y.
Proof.
  intros.
  apply Rminus_diag_uniq.
  apply Rabs_eq_0.
  apply Rle_antisym.
  apply le_epsilon.
  intros.
  rewrite Rplus_0_l.
  apply (H (mkposreal eps H0)).
  apply Rabs_pos.
Qed.

(** Rle *)

Lemma Rle_le : forall a b c, a <= b -> b <= c -> a <= b <= c.
Proof.
  split.
  apply H.
  apply H0.
Qed.

(* posreal *)

Lemma is_pos_div_2 (eps : posreal) : 0 < eps / 2.
Proof.
  unfold Rdiv ; apply Rmult_lt_0_compat ; 
  [apply eps | apply Rinv_0_lt_compat, Rlt_0_2].
Qed.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).