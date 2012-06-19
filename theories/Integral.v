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

Lemma ex_RInt_add_interval : forall f a b c, ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_3.
apply RiemannInt_P24 with b; now apply ex_RInt_correct_2.
Qed.

Lemma ex_RInt_included1: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_3.
apply RiemannInt_P22 with b;[now apply ex_RInt_correct_2|exact H2].
Qed.

Lemma ex_RInt_included2: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f c b.
intros f a b c H1 H2.
apply ex_RInt_correct_3.
apply RiemannInt_P23 with a;[now apply ex_RInt_correct_2|exact H2].
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
apply ex_RInt_correct_3.
apply RiemannInt_P1.
now apply ex_RInt_correct_2.
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
replace (db * f (b x) - da * f (a x)) with (- f(a x) * da + f (b x) * db) by ring.
apply derivable_pt_lim_comp_2d ; try easy.
replace (- f (a x)) with (Derive (fun u => RInt f u (b x)) (a x)).
replace (f (b x)) with (Derive (fun u => RInt f (a x) u) (b x)).
apply derivable_differentiable_pt_lim.
(* *)
destruct Ia as (d1,H1).
destruct Ib as (d2,H2).
exists (mkposreal _ (Rmin_stable_in_posreal d1  (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d1) d2)))).
simpl; intros u v Hu Hv.
exists (-f u).
apply (derivable_pt_lim_RInt' f v u).
apply ex_RInt_add_interval with (a x+d1).
apply ex_RInt_included2 with (a x - d1).
exact H1.
apply Rabs_le_between'.
apply Rlt_le, Rlt_le_trans with (1:=Hu), Rmin_l.
apply ex_RInt_add_interval with (a x).
apply ex_RInt_bound.
apply ex_RInt_included2 with (a x - d1).
exact H1.
pattern (a x) at 2 3; rewrite <- (Rplus_0_r (a x)).
split; apply Rplus_le_compat_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
left; apply cond_pos.
left; apply cond_pos.
apply ex_RInt_add_interval with (b x).
exact Hi.
apply ex_RInt_add_interval with (b x-d2).
apply ex_RInt_bound.
apply ex_RInt_included1 with (b x + d2).
exact H2.
pattern (b x) at 2 3; rewrite <- (Rplus_0_r (b x)).
split; apply Rplus_le_compat_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
left; apply cond_pos.
left; apply cond_pos.
apply ex_RInt_included1 with (b x + d2).
exact H2.
apply Rabs_le_between'.
apply Rlt_le, Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _), Rmin_r.
exists (pos_div_2 d1).
apply ex_RInt_included2 with (a x - d1).
apply ex_RInt_included1 with (a x + d1).
exact H1.
apply Rabs_le_between'.
replace (u + pos_div_2 d1 - a x) with ((u-a x)+pos_div_2 d1) by ring.
apply Rle_trans with (1:=Rabs_triang _ _).
rewrite (double_var d1).
apply Rplus_le_compat.
apply Rlt_le; apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _), Rmin_l.
rewrite Rabs_right.
now right.
apply Rle_ge, Rlt_le, cond_pos.
split.
apply Rplus_le_reg_l with (d1-u).
apply Rle_trans with (-(u-a x)).
right; ring.
apply Rle_trans with (1:= RRle_abs _).
rewrite Rabs_Ropp.
apply Rlt_le, Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _), Rle_trans with (1:=Rmin_l _ _).
pattern d1 at 1; rewrite (double_var d1).
right; simpl; ring.
apply Rplus_le_compat_l.
apply Rle_trans with 0.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
left; apply cond_pos.
left; apply cond_pos.
admit. (* hum.... f continue autour de a x ? *)
(* *)
apply Derive_correct.
exists (f (b x)).
now apply derivable_pt_lim_RInt.
(* *)

(* intros eps.
destruct (proj1 (continuity_pt_locally _ _) Ca eps) as (d1,H1).
destruct (proj1 (continuity_pt_locally _ _) Cb eps) as (d2,H2).
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)).
simpl; intros u v Hu Hv.
replace  (Derive (fun u => RInt f u (b x)) (a x)) with (- f (a x)).
replace  (Derive (fun z => RInt f z v) u) with (- f u).
admit.
apply sym_eq; apply is_derive_unique.
apply derivable_pt_lim_RInt'.
apply sym_eq; apply is_derive_unique.
now apply derivable_pt_lim_RInt'.
*)
admit.
(* *)
apply is_derive_unique.
now apply derivable_pt_lim_RInt.
apply is_derive_unique.
now apply derivable_pt_lim_RInt'.
Qed.


(* Il manque encore son copain avec f qui dépend aussi de x *)




