Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Derive RInt Differential Locally.
Require Import Continuity.

Lemma ex_RInt_ext :
  forall f g a b,
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  ex_RInt f a b -> ex_RInt g a b.
Proof.
intros f g a b Heq If.
apply ex_RInt_correct_3.
apply Riemann_integrable_ext with (1 := Heq).
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_point :
  forall f a, RInt f a a = 0.
Proof.
intros f a.
rewrite -(RiemannInt_P9 (RiemannInt_P7 f a)).
apply RInt_correct.
Qed.

Lemma RInt_swap :
  forall f a b,
  - RInt f a b = RInt f b a.
Proof.
intros f a b.
destruct (Req_dec a b) as [Hab|Hab].
rewrite Hab.
rewrite RInt_point.
apply Ropp_0.
unfold RInt.
destruct (Rle_dec a b) as [H|H].
destruct (Rle_dec b a) as [H'|H'].
elim Hab.
now apply Rle_antisym.
apply refl_equal.
apply Rnot_le_lt in H.
destruct (Rle_dec b a) as [H'|H'].
apply Ropp_involutive.
elim H'.
now apply Rlt_le.
Qed.

Lemma ex_RInt_opp :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => - f x) a b.
Proof.
intros f a b If.
apply ex_RInt_correct_3.
apply Riemann_integrable_opp.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_opp :
  forall f a b, ex_RInt f a b ->
  RInt (fun x => - f x) a b = - RInt f a b.
Proof.
intros f a b If.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ If)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ (ex_RInt_opp _ _ _ If))).
apply RiemannInt_opp.
Qed.

Lemma ex_RInt_abs :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => Rabs (f x)) a b.
Proof.
intros f a b If.
apply ex_RInt_correct_3.
apply RiemannInt_P16.
now apply ex_RInt_correct_2.
Qed.

Lemma ex_RInt_scal :
  forall f l a b, ex_RInt f a b ->
  ex_RInt (fun x => l * f x) a b.
Proof.
intros f l a b If.
apply ex_RInt_correct_3.
apply Riemann_integrable_scal.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_scal :
  forall f l a b, ex_RInt f a b ->
  RInt (fun x => l * f x) a b = l * RInt f a b.
Proof.
intros f l a b If.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ If)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ (ex_RInt_scal _ _ _ _ If))).
apply RiemannInt_scal.
Qed.

Lemma ex_RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  ex_RInt (fun x => f x + g x) a b.
Proof.
intros f g a b If Ig.
apply ex_RInt_correct_3.
apply Riemann_integrable_plus ; now apply ex_RInt_correct_2.
Qed.

Lemma RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof.
intros f g a b If Ig.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ If)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ Ig)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ (ex_RInt_plus _ _ _ _ If Ig))).
apply RiemannInt_plus.
Qed.

Lemma ex_RInt_minus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  ex_RInt (fun x => f x - g x) a b.
Proof.
intros f g a b If Ig.
apply ex_RInt_correct_3.
apply Riemann_integrable_minus ; now apply ex_RInt_correct_2.
Qed.

Lemma RInt_minus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof.
intros f g a b If Ig.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ If)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ Ig)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ (ex_RInt_minus _ _ _ _ If Ig))).
apply RiemannInt_minus.
Qed.

Lemma derivable_pt_lim_param : forall f a b x,
  locally (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) x ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally (fun y => ex_RInt (fun t => f y t) a b) x ->
  ex_RInt (fun t => Derive (fun u => f u t) x) a b ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x.
wlog: a b / a < b => H.
(* *)
destruct (total_order_T a b) as [[Hab|Hab]|Hab].
now apply H.
intros _ _ _ _.
rewrite Hab.
rewrite RInt_point.
apply (is_derive_ext (fun _ => 0)).
intros t.
apply sym_eq.
apply RInt_point.
apply derivable_pt_lim_const.
intros H1 H2 H3 H4.
apply (is_derive_ext (fun u => - RInt (fun t => f u t) b a)).
intros t.
apply RInt_swap.
rewrite -RInt_swap.
apply derivable_pt_lim_opp.
apply H.
exact Hab.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
apply: locally_impl H3.
apply locally_forall => y H3.
now apply ex_RInt_bound.
now apply ex_RInt_bound.
(* *)
rewrite Rmin_left. 2: now apply Rlt_le.
rewrite Rmax_right. 2: now apply Rlt_le.
intros Df Cdf If IDf.
apply equiv_deriv_pt_lim_1.
refine (let Cdf' := uniform_continuity_2d_1d (fun u v => Derive (fun z => f z u) v) a b x _ in _).
intros t Ht eps.
specialize (Cdf t Ht eps).
simpl in Cdf.
destruct Cdf as (d,Cdf).
exists d.
intros v u Hv Hu.
now apply Cdf.
intros eps. clear Cdf.
assert (H': 0 < eps / Rabs (b - a)).
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
apply Rgt_not_eq.
now apply Rgt_minus.
move: (Cdf' (mkposreal _ H')) => {Cdf'} [d1 Cdf].
move: (locally_and _ _ _ Df If) => {Df If} [d2 DIf].
exists (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))) => /= y Hy.
assert (D1: ex_RInt (fun t => f y t) a b).
apply DIf.
apply Rlt_le_trans with (1 := Hy).
apply Rle_trans with (1 := Rmin_r _ _).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
assert (D2: ex_RInt (fun t => f x t) a b).
apply DIf.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite -RInt_minus //.
rewrite Rmult_comm.
rewrite -RInt_scal //.
assert (D3: ex_RInt (fun t => f y t - f x t) a b) by now apply (ex_RInt_minus (fun u => f y u) (fun u => f x u)).
assert (D4: ex_RInt (fun t => (y - x) * Derive (fun u => f u t) x) a b) by now apply ex_RInt_scal.
rewrite -RInt_minus //.
assert (D5: ex_RInt (fun t => f y t - f x t - (y - x) * Derive (fun u => f u t) x) a b) by now apply ex_RInt_minus.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ D5)).
assert (D6: ex_RInt (fun t => Rabs (f y t - f x t - (y - x) * Derive (fun u => f u t) x)) a b) by now apply ex_RInt_abs.
apply Rle_trans with (1 := RiemannInt_P17 _ (ex_RInt_correct_2 _ _ _ D6) (Rlt_le _ _ H)).
refine (Rle_trans _ _ _ (RiemannInt_P19 _ (RiemannInt_P14 a b (eps / Rabs (b - a) * Rabs (y - x))) (Rlt_le _ _ H) _) _).
intros u Hu.
destruct (MVT_cor4 (fun t => f t u) x) with (eps := pos_div_2 d2) (b := y) as (z,Hz).
intros z Hz.
apply DIf.
apply Rle_lt_trans with (1 := Hz).
apply: Rlt_eps2_eps.
apply cond_pos.
split ; now apply Rlt_le.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
rewrite (proj1 Hz).
rewrite Rmult_comm.
rewrite -Rmult_minus_distr_l Rabs_mult.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rlt_le.
apply Cdf.
split ; now apply Rlt_le.
apply Rabs_le_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le.
apply cond_pos.
split ; now apply Rlt_le.
apply Rabs_le_between'.
apply Rle_trans with (1 := proj2 Hz).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite RiemannInt_P15.
rewrite Rabs_pos_eq.
right.
field.
apply Rgt_not_eq.
now apply Rgt_minus.
apply Rge_le.
apply Rge_minus.
now apply Rgt_ge.
Qed.
