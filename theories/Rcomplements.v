Require Import Reals.

Open Scope R_scope.

(** * Operations on Rdiv *)

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


(** * Operations on Rminus *)
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

Lemma Rdiv_minus_distr : forall a b c, b <> 0 -> a/b-c = (a-b*c)/b.
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

Lemma Rdiv_lt_mult : forall a b c, b > 0 -> (a < b * c <-> a / b < c).
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

(** * Rewriting Rmin and Rmax *)

Lemma Rplus_max_distr_l :
  forall a b c, a + Rmax b c = Rmax (a + b) (a + c).
Proof.
intros a b c.
unfold Rmax.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
apply Rplus_le_reg_l with (1 := H').
Qed.

Lemma Rplus_max_distr_r :
  forall a b c, Rmax b c + a = Rmax (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
apply Rplus_max_distr_l.
Qed.

Lemma Rplus_min_distr_l :
  forall a b c, a + Rmin b c = Rmin (a + b) (a + c).
Proof.
intros a b c.
unfold Rmin.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
apply Rplus_le_reg_l with (1 := H').
Qed.

Lemma Rplus_min_distr_r :
  forall a b c, Rmin b c + a = Rmin (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
apply Rplus_min_distr_l.
Qed.

Lemma Rmax_le_compat : forall a b c d, a <= b -> c <= d -> Rmax a c <= Rmax b d.
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
  destruct (Rle_or_lt a b).

  rewrite Rmax_left.
  rewrite Rmin_left.
  reflexivity.
  apply H.
  apply Ropp_le_contravar.
  apply H.

  rewrite Rmax_right.
  rewrite Rmin_right.
  reflexivity.
  apply Rlt_le, H.
  apply Ropp_le_contravar.
  apply Rlt_le.
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
  rewrite Rmax_right.
  apply Rplus_le_compat_r.
  apply H.
  apply r.
  rewrite <- (Rplus_0_r (Rmax a b)).
  rewrite Rmax_left.
  apply Rplus_le_compat_l.
  apply H0.
  apply Rlt_le, r.
Qed.

Lemma Rplus_le_Rmax : forall a b : R, a + b <= 2*Rmax a b.
Proof.
  intros.
  rewrite double.
  destruct (Rle_lt_dec a b).
  rewrite Rmax_right.
  apply Rplus_le_compat_r.
  apply r.
  apply r.
  rewrite Rmax_left.
  apply Rplus_le_compat_l.
  apply Rlt_le.
  apply r.
  apply Rlt_le, r.
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

Lemma Rmin_Rmax : forall a b, Rmin a b <= Rmax a b.
Proof.
  intros.
  apply Rle_trans with a; apply Rmin_Rmax_l.
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

Lemma Rabs_le_between : forall x y, (Rabs x <= y <-> -y <= x <= y).
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

Lemma Rabs_le_between' : forall x y z, Rabs (x - y) <= z <-> y-z <= x <= y+z.
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
  apply (Rabs_le_between (x-y) z).
  apply H.

  apply (Rabs_le_between (x-y) z).
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

Lemma Rabs_lt_between : forall x y, (Rabs x < y <-> -y < x < y).
Proof.
  split.
  intros; split; now apply Rabs_def2.
  intros (H1,H2); now apply Rabs_def1.
Qed.

Lemma Rabs_lt_between' : forall x y z, Rabs (x - y) < z <-> y-z < x < y+z.
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
  apply (Rabs_lt_between (x-y) z).
  apply H.

  apply (Rabs_lt_between (x-y) z).
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

Lemma Rabs_le_between_min_max : forall x y z, Rmin x y <= z <= Rmax x y -> Rabs (z - y) <= Rabs (x - y).
Proof.
 intros x y z H.
 case (Rle_or_lt x y); intros H'.
 (* *)
 rewrite Rmin_left in H;[idtac|exact H'].
 rewrite Rmax_right in H;[idtac|exact H'].
 rewrite Rabs_left1.
 rewrite Rabs_left1.
 apply Ropp_le_contravar.
 apply Rplus_le_compat_r.
 apply H.
 apply Rle_minus; exact H'.
 apply Rle_minus; apply H.
 (* *)
 rewrite Rmin_right in H;[idtac|left; exact H'].
 rewrite Rmax_left in H;[idtac|left; exact H'].
 rewrite Rabs_right.
 rewrite Rabs_right.
 apply Rplus_le_compat_r.
 apply H.
 apply Rge_minus; left; apply H'.
 apply Rge_minus, Rle_ge; apply H.
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

Lemma Rabs_maj2 : forall x, -x <= Rabs x.
Proof.
  intros.
  rewrite <- Rabs_Ropp.
  apply Rle_abs.
Qed.



(** * Rmult *)


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


(** posreal *)

Lemma is_pos_div_2 (eps : posreal) : 0 < eps / 2.
Proof.
  unfold Rdiv ; apply Rmult_lt_0_compat ; 
  [apply eps | apply Rinv_0_lt_compat, Rlt_0_2].
Qed.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).


(** * Operations on the Riemann integral *)

(** Change of expression *)

Lemma Riemann_integrable_ext : forall (f g : R -> R) (a b : R),
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x)
    -> Riemann_integrable f a b -> Riemann_integrable g a b.
Proof.
  intros f g a b Heq pr_f.
  intro eps.
  elim (pr_f eps) ; clear pr_f ; intros phi (psi, pr_f).
  exists phi.
  exists psi.
  split ; intros.
  rewrite <- (Heq t H).
  apply (proj1 pr_f t H).
  apply pr_f.
Qed.

Lemma RiemannInt_ext : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (Heq : forall x, Rmin a b <= x <= Rmax a b -> f x = g x),
    RiemannInt pr_f = RiemannInt pr_g.
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  apply RiemannInt_P18.
  apply r.
  intros.
  apply Heq.
  split.
  rewrite (Rmin_left _ _ r).
  apply Rlt_le ; apply H.
  rewrite (Rmax_right _ _ r).
  apply Rlt_le ; apply H.
  rewrite (RiemannInt_P8 pr_f (RiemannInt_P1 pr_f)).
  rewrite (RiemannInt_P8 pr_g (RiemannInt_P1 pr_g)).
  apply Ropp_eq_compat.
  apply RiemannInt_P18.
  apply Rlt_le ; apply r.
  intros.
  apply Heq.
  split.
  rewrite (Rmin_right _ _ (Rlt_le _ _ r)).
  apply Rlt_le ; apply H.
  rewrite (Rmax_left _ _ (Rlt_le _ _ r)).
  apply Rlt_le ; apply H.
Qed.

(** Constant function *)

Lemma Riemann_integrable_const : forall (c a b : R),
  Riemann_integrable (fun x => c) a b.
Proof.
  intros.
  apply RiemannInt_P14.
Qed.

Lemma RiemannInt_const : forall (c a b : R) (pr : Riemann_integrable (fun x => c) a b),
  RiemannInt pr = c * (b-a).
Proof.
  intros.
  apply RiemannInt_P15.
Qed.

(** Addition *)

Lemma Riemann_integrable_plus : forall (f g : R -> R) (a b : R),
  Riemann_integrable f a b -> Riemann_integrable g a b ->
    Riemann_integrable (fun x => f x + g x) a b.
Proof.
  intros f g a b pr_f pr_g.
  apply (Riemann_integrable_ext (fun x => f x + 1 * g x)).
  intros ; ring.
  apply (RiemannInt_P10 1 pr_f pr_g).
Qed.

Lemma RiemannInt_plus : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (pr : Riemann_integrable (fun x => f x + g x) a b),
  RiemannInt pr = RiemannInt pr_f + RiemannInt pr_g.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_g)).
  rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 1 pr_f pr_g)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** Subtraction *)

Lemma Riemann_integrable_minus : forall (f g : R -> R) (a b : R),
  Riemann_integrable f a b -> Riemann_integrable g a b ->
    Riemann_integrable (fun x => f x - g x) a b.
Proof.
  intros f g a b pr_f pr_g.
  apply (Riemann_integrable_ext (fun x => f x + (-1) * g x)).
  intros ; ring.
  apply (RiemannInt_P10 (-1) pr_f pr_g).
Qed.

Lemma RiemannInt_minus : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (pr : Riemann_integrable (fun x => f x - g x) a b),
  RiemannInt pr = RiemannInt pr_f - RiemannInt pr_g.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_g)).
  unfold Rminus. rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 (-1) pr_f pr_g)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** Opposite *)

Lemma Riemann_integrable_opp : forall (f : R -> R) (a b : R),
  Riemann_integrable f a b ->
    Riemann_integrable (fun x => - f x) a b.
Proof.
  intros f a b pr_f.
  apply (Riemann_integrable_ext (fun x => 0 + (-1) * f x)).
  intros ; ring.
  apply (RiemannInt_P10 (-1) (Riemann_integrable_const _ _ _) pr_f).
Qed.

Lemma RiemannInt_opp : forall (f : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b)
  (pr : Riemann_integrable (fun x => - f x) a b),
  RiemannInt pr = - RiemannInt pr_f.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_f)).
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite <- (Rplus_0_l (-1 * RiemannInt pr_f)).
  assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
    rewrite RiemannInt_const.
    ring.
    rewrite H ; clear H.
  rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (-1) (Riemann_integrable_const 0 a b) pr_f)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** Multiplication by a scalar *)

Lemma Riemann_integrable_scal : forall (f : R -> R) (a b c : R),
  Riemann_integrable f a b ->
    Riemann_integrable (fun x => c * f x) a b.
Proof.
  intros f a b c pr_f.
  apply (Riemann_integrable_ext (fun x => 0 + c * f x)).
  intros ; ring.
  apply (RiemannInt_P10 (c) (Riemann_integrable_const _ _ _) pr_f).
Qed.

Lemma RiemannInt_scal : forall (f : R -> R) (a b c : R)
  (pr_f : Riemann_integrable f a b)
  (pr : Riemann_integrable (fun x => c * f x) a b),
  RiemannInt pr = c * RiemannInt pr_f.
Proof.
  intros.
  rewrite <- (Rplus_0_l (c * RiemannInt pr_f)).
  assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
    rewrite RiemannInt_const.
    ring.
    rewrite H ; clear H.
  rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (c) (Riemann_integrable_const 0 a b) pr_f)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.
