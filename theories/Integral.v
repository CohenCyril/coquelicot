Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Derive RInt Differential Locally.
Require Import Continuity Lim_seq.

Lemma ex_RInt_ext :
  forall f g a b,
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  ex_RInt f a b -> ex_RInt g a b.
Proof.
intros f g a b Heq If.
apply ex_RInt_correct_1.
apply Riemann_integrable_ext with (1 := Heq).
now apply ex_RInt_correct_2.
Qed.

Lemma ex_RInt_point :
  forall f a, ex_RInt f a a.
Proof.
intros f a.
apply ex_RInt_correct_1.
apply RiemannInt_P7.
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

Lemma RInt_ext :
  forall f g a b,
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  RInt f a b = RInt g a b.
Proof.
intros f g a b.
wlog H: a b / a <= b.
intros H Heq.
destruct (Rle_dec a b) as [Hab|Hab].
now apply H.
rewrite -RInt_swap -(RInt_swap g).
rewrite H //.
apply Rlt_le.
now apply Rnot_le_lt.
now rewrite Rmin_comm Rmax_comm.
rewrite Rmin_left // Rmax_right //.
intros Heq.
unfold RInt.
destruct (Rle_dec a b) as [Hab|Hab].
clear H.
2: easy.
apply Lim_seq_ext => n.
rewrite /RInt /RInt_val.
apply f_equal.
rewrite /SF_val_ly /=.
change 0 with (INR 0) at 2 4.
rewrite -(minus_diag (pow2 n)).
generalize (le_refl (pow2 n)).
generalize (pow2 n) at 1 4 6 7 9 11 12.
elim => [|m IHm].
easy.
intros H.
rewrite minus_Sn_m //.
simpl.
rewrite IHm.
2: now apply le_Sn_le.
rewrite Heq //.
rewrite minus_INR //.
rewrite minus_INR.
2: now apply le_Sn_le.
replace (INR m) with (INR m + 1 - 1) by ring.
rewrite -S_INR.
rewrite pow2_INR.
replace ((a + (2 ^ n - INR (S m)) * (b - a) / 2 ^ n + (a + (2 ^ n - (INR (S m) - 1)) * (b - a) / 2 ^ n)) / 2)
  with (a + (b - a) * ((2 * (2 ^ n - INR (S m)) + 1) / (2 * 2 ^ n))).
pattern a at 1 ; replace a with (a + (b - a) * 0) by ring.
pattern b at 4 ; replace b with (a + (b - a) * 1) by ring.
assert (Hminus: forall x y, x <= y -> 0 <= y - x).
intros x y Hxy.
apply Rplus_le_reg_r with x.
now ring_simplify.
change (2 * 2 ^ n) with (2 ^ (S n)).
rewrite -pow2_INR -minus_INR // -(mult_INR 2) -(plus_INR _ 1).
split ; apply Rplus_le_compat_l ; apply Rmult_le_compat_l.
now apply Hminus.
apply Rdiv_le_pos.
apply pos_INR.
apply pow_lt, Rlt_R0_R2.
now apply Hminus.
apply Rmult_le_reg_r with (2 ^ (S n)).
apply pow_lt, Rlt_R0_R2.
rewrite Rmult_assoc Rinv_l.
rewrite Rmult_1_l Rmult_1_r -pow2_INR.
apply le_INR.
simpl pow2.
clear -H ; omega.
apply pow_nonzero.
now apply (IZR_neq 2 0).
field.
apply pow_nonzero.
now apply (IZR_neq 2 0).
Qed.

Lemma ex_RInt_const :
  forall v a b, ex_RInt (fun _ => v) a b.
Proof.
intros f a b.
apply ex_RInt_correct_1.
apply Riemann_integrable_const.
Qed.

Lemma RInt_const (a b c : R) :
  RInt (fun _ => c) a b = c * (b-a).
Proof.
rewrite (RInt_correct _ _ _ (Riemann_integrable_const _ _ _)).
apply RiemannInt_const.
Qed.

Lemma ex_RInt_abs :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => Rabs (f x)) a b.
Proof.
intros f a b If.
apply ex_RInt_correct_1.
apply RiemannInt_P16.
now apply ex_RInt_correct_2.
Qed.

Lemma ex_RInt_scal :
  forall f l a b, ex_RInt f a b ->
  ex_RInt (fun x => l * f x) a b.
Proof.
intros f l a b If.
apply ex_RInt_correct_1.
apply Riemann_integrable_scal.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_scal :
  forall f l a b,
  RInt (fun x => l * f x) a b = l * RInt f a b.
Proof.
intros f l.
(* *)
assert (forall a b, Lim_seq (RInt_val (fun x : R => l * f x) a b) = l * Lim_seq (RInt_val f a b)).
intros a b.
rewrite -Lim_seq_scal.
apply Lim_seq_ext => n.
unfold RInt_val.
replace (l * ((b - a) / 2 ^ n * seq.foldr Rplus 0 (SF_val_ly f a b n)))
  with ((b - a) / 2 ^ n * (l * seq.foldr Rplus 0 (SF_val_ly f a b n))) by ring.
apply f_equal.
unfold SF_val_ly.
apply eq_sym.
destruct (RInt_part a b n) as [|h q].
apply Rmult_0_r.
simpl.
revert h.
induction q => h.
apply Rmult_0_r.
simpl.
rewrite -IHq.
apply Rmult_plus_distr_l.
(* *)
intros a b.
unfold RInt.
case Rle_dec => _.
apply H.
rewrite H.
apply eq_sym, Ropp_mult_distr_r_reverse.
Qed.

Lemma ex_RInt_opp :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => - f x) a b.
Proof.
intros f a b If.
apply ex_RInt_correct_1.
apply Riemann_integrable_opp.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_opp :
  forall f a b,
  RInt (fun x => - f x) a b = - RInt f a b.
Proof.
intros f a b.
replace (-RInt f a b) with ((-1) * RInt f a b) by ring.
rewrite -RInt_scal.
apply RInt_ext => x _.
ring.
Qed.

Lemma ex_RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  ex_RInt (fun x => f x + g x) a b.
Proof.
intros f g a b If Ig.
apply ex_RInt_correct_1.
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
apply ex_RInt_correct_1.
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

Lemma ex_RInt_Chasles :
  forall f a b c, ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_1.
apply RiemannInt_P24 with b; now apply ex_RInt_correct_2.
Qed.

Lemma RInt_Chasles :
  forall f a b c,
  ex_RInt f a b -> ex_RInt f b c ->
  RInt f a b + RInt f b c = RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_2 in H1.
apply ex_RInt_correct_2 in H2.
rewrite (RInt_correct _ _ _ H1) (RInt_correct _ _ _ H2).
rewrite (RInt_correct _ _ _ (RiemannInt_P24 H1 H2)).
apply RiemannInt_P26.
Qed.

Lemma ex_RInt_included1: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_1.
apply RiemannInt_P22 with b;[now apply ex_RInt_correct_2|exact H2].
Qed.

Lemma ex_RInt_included2: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f c b.
intros f a b c H1 H2.
apply ex_RInt_correct_1.
apply RiemannInt_P23 with a;[now apply ex_RInt_correct_2|exact H2].
Qed.


Lemma derivable_pt_lim_param_aux : forall f a b x,
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
now apply ex_RInt_swap.
now apply ex_RInt_swap.
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


Lemma derivable_pt_lim_param : forall f a b x,
  locally (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) x ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally (fun y => ex_RInt (fun t => f y t) a b) x ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply derivable_pt_lim_param_aux; try easy.
apply ex_RInt_correct_1.
clear H1 H3.
wlog: a b H2 / a < b => H.
case (total_order_T a b).
intro Y; case Y.
now apply H.
intros Heq; rewrite Heq.
apply RiemannInt_P7.
intros  Y.
apply RiemannInt_P1.
apply H.
intros; apply H2.
rewrite Rmin_comm Rmax_comm.
exact H0.
exact Y.
rewrite Rmin_left in H2.
2: now left.
rewrite Rmax_right in H2.
2: now left.
apply continuity_implies_RiemannInt.
now left.
intros y Hy eps Heps.
destruct (H2 _ Hy (mkposreal eps Heps)) as (d,Hd).
simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist; simpl.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
Qed.



Lemma derivable_pt_lim_RInt' :
  forall f a x,
  ex_RInt f x a -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x ->
  derivable_pt_lim (fun x => RInt f x a) x (- f x).
Proof.
intros f a x Hi Ix Cx.
apply (is_derive_ext (fun u => - RInt f a u)).
intros t.
apply RInt_swap.
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt ; try easy.
apply ex_RInt_correct_1.
apply RiemannInt_P1.
now apply ex_RInt_correct_2.
Qed.

Lemma ex_RInt_inside :
  forall f a b x e,
  ex_RInt f (x-e) (x+e) -> Rabs (a-x) <= e -> Rabs (b-x) <= e ->
  ex_RInt f a b.
Proof.
intros f a b x e Hf Ha Hb.
wlog: a b Ha Hb / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
now left.
apply ex_RInt_included1 with (x+e).
apply ex_RInt_included2 with (x-e).
exact Hf.
now apply Rabs_le_between'.
split.
exact Hab.
assert (x-e <= b <= x+e) by now apply Rabs_le_between'.
apply H.
Qed.

Lemma RInt_Chasles_bound_comp_l_loc :
  forall f a b x,
  locally (fun y => ex_RInt (f y) (a x) b) x ->
  (exists eps : posreal, locally (fun y => ex_RInt (f y) (a x - eps) (a x + eps)) x) ->
  continuity_pt a x ->
  locally (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) b =
    RInt (f x') (a x') b) x.
Proof.
intros f a b x Hab (eps,Hae) Ca.
move /continuity_pt_locally: Ca => Ca.
apply: locally_impl (Ca eps).
apply: locally_impl Hab.
apply: locally_impl Hae.
apply locally_forall => y Hae Hab Hy.
apply RInt_Chasles with (2 := Hab).
apply ex_RInt_inside with (1 := Hae).
now apply Rlt_le.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
Qed.

Lemma RInt_Chasles_bound_comp_loc :
  forall f a b x,
  locally (fun y => ex_RInt (f y) (a x) (b x)) x ->
  (exists eps : posreal, locally (fun y => ex_RInt (f y) (a x - eps) (a x + eps)) x) ->
  (exists eps : posreal, locally (fun y => ex_RInt (f y) (b x - eps) (b x + eps)) x) ->
  continuity_pt a x ->
  continuity_pt b x ->
  locally (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) (b x') =
    RInt (f x') (a x') (b x')) x.
Proof.
intros f a b x Hab (ea,Hae) (eb,Hbe) Ca Cb.
move /continuity_pt_locally: Ca => Ca.
move /continuity_pt_locally: Cb => Cb.
set (e := mkposreal _ (Rmin_stable_in_posreal ea eb)).
apply: locally_impl (Ca e).
apply: locally_impl (Cb e).
apply: locally_impl Hab.
apply: locally_impl Hae.
apply: locally_impl Hbe.
apply locally_forall => y Hbe Hae Hab Hby Hay.
apply RInt_Chasles.
apply ex_RInt_inside with (1 := Hae).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hay).
exact: Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply ex_RInt_Chasles with (1 := Hab).
apply ex_RInt_inside with (1 := Hbe).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hby).
exact: Rmin_r.
Qed.

Lemma derivable_pt_lim_RInt_bound_comp :
  forall f a b da db x,
  ex_RInt f (a x) (b x) ->
  (exists eps : posreal, ex_RInt f (a x - eps) (a x + eps)) ->
  (exists eps : posreal, ex_RInt f (b x - eps) (b x + eps)) ->
  continuity_pt f (a x) ->
  continuity_pt f (b x) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  derivable_pt_lim (fun x => RInt f (a x) (b x)) x (db * f (b x) - da * f (a x)).
Proof.
intros f a b da db x Hi Ia Ib Ca Cb Da Db.
apply is_derive_ext_loc with (fun x0 => comp (fun y => RInt f y (a x)) a x0
  + comp (fun y => RInt f (a x) y) b x0).
(* *)
unfold comp.
apply RInt_Chasles_bound_comp_loc.
now apply locally_forall.
destruct Ia as (d1,H1).
exists d1.
now apply locally_forall.
destruct Ib as (d2,H2).
exists d2.
now apply locally_forall.
apply derivable_continuous_pt.
eexists ; eassumption.
apply derivable_continuous_pt.
eexists ; eassumption.
(* *)
replace (db * f (b x) - da * f (a x)) with (- f(a x) * da + f (b x) * db) by ring.
apply derivable_pt_lim_plus.
apply derivable_pt_lim_comp.
exact Da.
apply derivable_pt_lim_RInt' ; trivial.
apply ex_RInt_point.
apply derivable_pt_lim_comp.
exact Db.
now apply derivable_pt_lim_RInt.
Qed.

Lemma RInt_le: forall f g a b,
    a <= b ->
   ex_RInt f a b ->  ex_RInt g a b -> 
   (forall x,  a <= x <= b -> f x <= g x) ->
   RInt f a b <= RInt g a b.
intros f g a b H1 If Ig H2.
assert (Riemann_integrable f a b).
now apply ex_RInt_correct_2.
assert (Riemann_integrable g a b).
now apply ex_RInt_correct_2.
rewrite (RInt_correct _ _ _ X)(RInt_correct _ _ _ X0).
apply RiemannInt_P19.
exact H1.
intros; apply H2.
split; left; apply H.
Qed.



Lemma RInt_abs: forall f a b,
   a <= b -> ex_RInt f a b ->
   Rabs (RInt f a b) <= RInt (fun t => Rabs (f t)) a b.
intros f a b H1 If.
unfold Rabs at 1.
case (Rcase_abs (RInt f a b)); intros Y.
rewrite <- RInt_opp.
apply RInt_le.
exact H1.
now apply ex_RInt_opp.
now apply ex_RInt_abs.
intros.
rewrite <- Rabs_Ropp.
apply RRle_abs.
apply RInt_le.
exact H1.
exact If.
now apply ex_RInt_abs.
intros.
apply RRle_abs.
Qed.

Lemma RInt_le_const: forall f a b M,
  ex_RInt f a b ->
  (forall t, Rmin a b <= t <= Rmax a b -> Rabs (f t) <= M) ->
  Rabs (RInt f a b) <= Rabs (b-a) * M.
intros f a b M If H.
wlog: a b H If / (a <= b) => [Hw | Hab] .
(* *)
case (Rle_or_lt a b); intros Hab.
now apply Hw.
rewrite <- RInt_swap.
replace (b-a) with (-(a-b)) by ring.
rewrite 2! Rabs_Ropp.
apply Hw.
intros t Ht; apply H.
rewrite Rmin_comm Rmax_comm.
exact Ht.
apply ex_RInt_swap.
exact If.
now left.
(* *)
rewrite (Rabs_right (b-a)).
rewrite Rmult_comm; rewrite <- RInt_const.
apply Rle_trans with (1:=RInt_abs _ _ _ Hab If).
apply RInt_le.
exact Hab.
now apply ex_RInt_abs.
apply ex_RInt_correct_1.
apply continuity_implies_RiemannInt.
exact Hab.
intros x Hx eps Heps.
exists 1; split.
apply Rlt_0_1.
intros.
unfold dist; simpl; unfold R_dist; simpl.
rewrite /Rminus Rplus_opp_r Rabs_R0.
exact Heps.
intros x Hx; apply H.
rewrite (Rmin_left _ _ Hab).
now rewrite Rmax_right.
apply Rle_ge, Rplus_le_reg_l with a.
now ring_simplify.
Qed.


Lemma ex_RInt_cont: forall f a b, (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f x) -> ex_RInt f a b.
intros f a b H.
wlog: a b H / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H'.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
intros x; rewrite Rmin_comm Rmax_comm.
apply H.
now left.
apply ex_RInt_correct_1.
apply continuity_implies_RiemannInt.
exact Hab.
intros; apply H.
rewrite Rmin_left; try exact Hab.
now rewrite Rmax_right.
Qed. 

Lemma derivable_pt_lim_RInt_param_bound_comp_aux1: forall f a x,
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps)) x) ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        a x-eps <= t <= a x+eps ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->

  continuity_2d_pt
     (fun u v : R => Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) x (a x).
Proof.
intros f a x (d1,(d2,Ia)) (d3,(d4,Df)) Cdf e.
assert (J1:(continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x (a x)))
   by now apply locally_2d_singleton in Cdf.
destruct Cdf as (d5,Cdf).
destruct (J1 (mkposreal _ Rlt_0_1)) as (d6,Df1); simpl in Df1.
assert (J2: 0 < e / (Rabs (Derive (fun z : R => f z (a x)) x)+1)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
exists (mkposreal _ (Rmin_stable_in_posreal 
                  (mkposreal _ (Rmin_stable_in_posreal 
                        d1 
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d2) d3))))
                  (mkposreal _ (Rmin_stable_in_posreal 
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d4) d5))
                       (mkposreal _ (Rmin_stable_in_posreal d6 (mkposreal _ J2))))))). 
simpl; intros u v Hu Hv.
rewrite (Derive_ext (fun z : R => RInt (fun t : R => f z t) (a x) (a x)) (fun z => 0)).
2: intros t; apply RInt_point.
replace (Derive (fun _ : R => 0) x) with 0%R.
2: apply sym_eq, is_derive_unique, derivable_pt_lim_const.
rewrite Rminus_0_r.
replace (Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) with 
  (RInt (fun z => Derive (fun u => f u z) u) v (a x)).
(* *)
apply Rle_lt_trans with (Rabs (a x -v) *
   (Rabs (Derive (fun z : R => f z (a x)) x) +1)).
apply RInt_le_const.
apply ex_RInt_cont.
intros y Hy eps Heps.
assert (Y1:(Rabs (u - x) < d5)).
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
assert (Y2:(Rabs (y - a x) < d5)).
apply Rle_lt_trans with (Rabs (v-a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
destruct (Cdf u y Y1 Y2 (mkposreal eps Heps)) as (d,Hd); simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
intros t Ht.
apply Rplus_le_reg_r with (-Rabs (Derive (fun z : R => f z (a x)) x)).
apply Rle_trans with (1:=Rabs_triang_inv _ _).
ring_simplify.
left; apply Df1.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
replace (a x -v) with (-(v - a x)) by ring; rewrite Rabs_Ropp.
apply Rlt_le_trans with ((e / (Rabs (Derive (fun z : R => f z (a x)) x) + 1)) 
  * (Rabs (Derive (fun z : R => f z (a x)) x) + 1)).
apply Rmult_lt_compat_r.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
right; field.
apply sym_not_eq, Rlt_not_eq.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
(* *)
apply sym_eq, is_derive_unique.
apply derivable_pt_lim_param.
exists (pos_div_2 d4).
intros y Hy t Ht.
apply Df.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d4).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply (proj1 (Rabs_le_between' t (a x) d3)).
apply Rle_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
intros t Ht.
apply Cdf.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
exists (pos_div_2 d2).
intros y Hy.
apply ex_RInt_inside with (a x) d1.
apply Ia.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d2).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
Qed.






(* integral between a(x) and fixed b *)
Lemma derivable_pt_lim_RInt_param_bound_comp_aux2 :
  forall f a b x da,
  (locally (fun y => ex_RInt (fun t => f y t) (a x) b) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps)) x) ->
  derivable_pt_lim a x da ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (forall t : R,
          Rmin (a x) b <= t <= Rmax (a x) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> 
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
   continuity_pt (fun t => f x t) (a x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) b) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) b+(-f x (a x))*da).
Proof.
intros f a b x da Hi (d0,Ia) Da Df Cdf1 Cdf2 Cfa.
rewrite Rplus_comm.
apply is_derive_ext_loc with (fun x0 => RInt (fun t : R => f x0 t) (a x0) (a x) + RInt (fun t : R => f x0 t) (a x) b).
apply RInt_Chasles_bound_comp_l_loc.
exact Hi.
now exists d0.
apply derivable_continuous_pt.
eexists.
apply Da.
apply derivable_pt_lim_plus.
(* *)
replace (- f x (a x) * da) with (0*1+- f x (a x) * da) by ring.
apply derivable_pt_lim_comp_2d with 
   (f1 := fun x0 y => RInt (fun t : R => f x0 t) y (a x)).
replace 0 with (Derive (fun u => RInt (fun t : R => f u t) (a x) (a x)) x).
apply derivable_differentiable_pt_lim.
(* . *)
destruct Df as (d1,(d2,Df)).
destruct Cdf2 as (d3,Cdf2).
destruct Ia as (d4,Ia).
exists (mkposreal _ (Rmin_stable_in_posreal 
                (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2)))
                (mkposreal _ (Rmin_stable_in_posreal d3 
                            (mkposreal _ (Rmin_stable_in_posreal d0 (pos_div_2 d4))))))).
simpl; intros u v Hu Hv.
eexists; eapply derivable_pt_lim_param.
exists (pos_div_2 d2).
intros y Hy t Ht.
apply Df.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d2).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (a x - d1).
apply Rmin_l.
apply Rmin_glb.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x + d1); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (a x + d1).
apply Rmax_lub.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x); ring_simplify.
left; apply cond_pos.
apply Rmax_l.
intros t Ht.
apply Cdf2.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
exists (pos_div_2 d4).
intros y Hy.
apply ex_RInt_inside with (a x) d0.
apply Ia.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d4).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
(* . *)
apply derivable_pt_lim_RInt'.
apply ex_RInt_point.
apply locally_singleton in Ia.
now exists d0.
exact Cfa.
(* . *)
apply derivable_pt_lim_RInt_param_bound_comp_aux1; try easy.
exists d0; exact Ia.
destruct Df as (d,Hd).
exists d.
apply locally_impl with (2:=Hd).
apply locally_forall.
intros y H t Ht.
apply H.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rmax_l.
(* . *)
apply is_derive_unique.
apply is_derive_ext with (fun _ => 0).
intros t; apply sym_eq, RInt_point.
apply derivable_pt_lim_const.
(* . *)
apply derivable_pt_lim_id.
exact Da.
(* *)
apply derivable_pt_lim_param.
destruct Df as (d,Df).
apply locally_impl with (2:= Df).
apply locally_forall.
intros y Hy t Ht; apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x+d); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
exact Cdf1.
exact Hi.
Qed.



Lemma derivable_pt_lim_RInt_param_bound_comp_aux3 :
  forall f a b x db,
  (locally (fun y => ex_RInt (fun t => f y t) a (b x)) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps)) x) ->
  derivable_pt_lim b x db ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin a (b x-eps) <= t <= Rmax a (b x+eps) ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (forall t : R,
          Rmin a (b x) <= t <= Rmax a (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> 
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (b x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) a (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db).
Proof.
intros f a b x db If Ib Db Df Cf1 Cf2 Cfb.
apply is_derive_ext with (fun x0 => - RInt (fun t : R => f x0 t) (b x0) a).
intros t; apply RInt_swap.
replace (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db) with
      (- ((RInt (fun t : R => Derive (fun u : R => f u t) x) (b x) a) + - f x (b x)*db)).
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt_param_bound_comp_aux2; try easy.
apply locally_impl with (2:=If).
apply locally_forall.
intros y H.
now apply ex_RInt_swap.
destruct Df as (e,H).
exists e.
apply locally_impl with (2:=H).
apply locally_forall.
intros y H' t Ht.
apply H'.
now rewrite Rmin_comm Rmax_comm.
intros t Ht.
apply Cf1.
now rewrite Rmin_comm Rmax_comm.
rewrite <- RInt_swap.
ring.
Qed.


Lemma derivable_pt_lim_RInt_param_bound_comp :
 forall f a b x da db,
  (locally (fun y => ex_RInt (fun t => f y t) (a x) (b x)) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps)) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps)) x) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) (b x -eps) <= t <= Rmax (a x+eps) (b x+eps) ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (forall t : R,
          Rmin (a x) (b x) <= t <= Rmax (a x) (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> 
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
 (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (a x) ->   continuity_pt (fun t => f x t) (b x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) (b x)+(-f x (a x))*da+(f x (b x))*db).
Proof.
intros f a b x da db If Ifa Ifb Da Db Df Cf Cfa Cfb Ca Cb.
apply is_derive_ext_loc with (fun x0 : R => RInt (fun t : R => f x0 t) (a x0) (a x)
    + RInt (fun t : R => f x0 t) (a x) (b x0)).
apply RInt_Chasles_bound_comp_loc ; trivial.
apply derivable_continuous_pt.
eexists.
apply Da.
apply derivable_continuous_pt.
eexists.
apply Db.
replace (RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (b x) +
   - f x (a x) * da + f x (b x) * db) with
   ((RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (a x) + - f x (a x) * da) +
      (RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (b x) + f x (b x)*db)).
apply derivable_pt_lim_plus.
(* *)
apply derivable_pt_lim_RInt_param_bound_comp_aux2; try easy.
exists (mkposreal _ Rlt_0_1).
intros y Hy.
apply ex_RInt_point.
destruct Df as (e,H).
exists e.
apply locally_impl with (2:=H).
apply locally_forall.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
intros t Ht.
apply Cf.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
now right.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
now right.
(* *)
apply derivable_pt_lim_RInt_param_bound_comp_aux3; try easy.
destruct Df as (e,H).
exists e.
apply locally_impl with (2:=H).
apply locally_forall.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
rewrite RInt_point.
ring.
Qed.
