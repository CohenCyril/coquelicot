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


Lemma derivable_pt_lim_param : forall f a b x,
  locally (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) x ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally (fun y => ex_RInt (fun t => f y t) a b) x ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply derivable_pt_lim_param_aux; try easy.
apply ex_RInt_correct_3.
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
destruct Ia as (d1,H1).
apply is_derive_ext with (fun x0 => comp (fun y => RInt f y (a x + d1)) a x0 
  + comp (fun y => RInt f (a x + d1) y) b x0).
(* *)
intros t.
unfold comp.
apply sym_eq, RInt_Chasles.
replace (db * f (b x) - da * f (a x)) with (- f(a x) * da + f (b x) * db) by ring.
apply derivable_pt_lim_plus.
(* *)
apply derivable_pt_lim_comp.
exact Da.
apply derivable_pt_lim_RInt'.
apply ex_RInt_included2 with (a x - d1).
exact H1.
pattern (a x) at 2 3; rewrite <- (Rplus_0_r (a x)).
split; apply Rplus_le_compat_l.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
left; apply cond_pos.
left; apply cond_pos.
now exists d1.
exact Ca.
(* *)
apply derivable_pt_lim_comp.
exact Db.
apply derivable_pt_lim_RInt.
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
exact Hi.
exact Ib.
exact Cb.
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
exact If.
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
apply ex_RInt_bound.
exact If.
now left.
(* *)
rewrite (Rabs_right (b-a)).
rewrite Rmult_comm; rewrite <- RInt_const.
apply Rle_trans with (1:=RInt_abs _ _ _ Hab If).
apply RInt_le.
exact Hab.
now apply ex_RInt_abs.
apply ex_RInt_correct_3.
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



Lemma ex_RInt_cont_min_max: forall f a b ainf asup, 
  ainf <= a <= asup ->
   (forall t, Rmin ainf b <= t <= Rmax asup b -> continuity_pt f t) ->  
   ex_RInt f a b.
intros f a b ainf asup H1 H2.
case (Rle_or_lt a b); intros Hab.
apply ex_RInt_correct_3.
apply continuity_implies_RiemannInt.
exact Hab.
intros; apply H2.
split.
apply Rle_trans with (2:=proj1 H).
apply Rle_trans with (2:=proj1 H1).
apply Rmin_l.
apply Rle_trans with (1:=proj2 H).
apply Rmax_r.
apply ex_RInt_bound.
apply ex_RInt_correct_3.
apply continuity_implies_RiemannInt.
now left.
intros; apply H2.
split.
apply Rle_trans with (2:=proj1 H).
apply Rmin_r.
apply Rle_trans with (1:=proj2 H).
apply Rle_trans with (1:=proj2 H1).
apply Rmax_l.
Qed.


Lemma derivable_pt_lim_RInt_param_bound_comp_aux0: forall f a b x,  
  (exists eps:posreal,
       (locally (fun x' => forall t : R,
          Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x)) ->
  (locally_2d (fun u v =>
      ex_RInt (fun t => Derive (fun z => f z t) u)  v b) x (a x)).
intros f a b x (e,(d,H)).
exists (mkposreal _ (Rmin_stable_in_posreal e d)).
simpl; intros u v Hu Hv.
apply ex_RInt_cont_min_max with (a x -e) (a x + e).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rmin_l.
intros t Ht eps Heps.
assert (Rabs (u - x) < d).
apply Rlt_le_trans with (1:=Hu).
apply Rmin_r.
destruct (H u H0 t Ht (mkposreal _ Heps)) as (d2,Hd2); simpl in Hd2.
exists d2; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist.
intros z (_,Hz).
apply Hd2.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
Qed.


Lemma derivable_pt_lim_RInt_param_bound_comp_aux1: forall f a b x,  
  (locally (fun y => ex_RInt (fun t => f y t) (a x) b) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x -eps) (a x + eps)) x) ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (exists eps:posreal,
       (locally (fun x' => forall t : R,
          Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x)) ->

  continuity_2d_pt
     (fun u v : R => Derive (fun z : R => RInt (fun t : R => f z t) v b) u) x (a x).
Proof.
intros f a b x (d1,Ia) (d2,Ib) (d3,Df) Y.
destruct (derivable_pt_lim_RInt_param_bound_comp_aux0 _ _ _ _ Y) as (d7,Hd7).
destruct Y as (d4,(d0,Cdf)).
intros eps.
refine (let Cdf' := uniform_continuity_2d_1d' 
   (fun u v => Derive (fun z => f z v) u)  (Rmin (a x - d4) b) (Rmax (a x + d4) b)   x _ in _).
apply Cdf.
rewrite /Rminus Rplus_opp_r Rabs_R0; apply cond_pos.
assert (J1: 0 < eps/(Rabs (b-a x)+1)/2).
apply Rdiv_lt_0_compat.
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
destruct (Cdf' (mkposreal _ J1)) as (d5,Hd5).
assert (Rmin (a x - d4) b <= a x <= Rmax (a x + d4) b).
split.
apply Rle_trans with (1:= Rmin_l _ _).
apply Rplus_le_reg_l with (- a x + d4); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (2:= Rmax_l _ _).
apply Rplus_le_reg_l with (- a x); ring_simplify.
left; apply cond_pos.
assert (Rabs (x-x) < d0).
rewrite /Rminus Rplus_opp_r Rabs_R0; apply cond_pos.
destruct (Cdf x H0 (a x) H (mkposreal _ Rlt_0_1)) as (d6,Hd6).
simpl in Hd6.
assert (J2: 0 < eps / (Rabs (Derive (fun z : R => f z (a x)) x)+1) /2).
apply Rdiv_lt_0_compat.
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rle_lt_0_plus_1; apply Rlt_le; exact Rlt_0_1.
(*********************************************************)
exists (mkposreal _ (Rmin_stable_in_posreal 
                  (mkposreal _ (Rmin_stable_in_posreal  d4 d5))
                  (mkposreal _ (Rmin_stable_in_posreal  
                        (mkposreal _ (Rmin_stable_in_posreal d6 
                                (mkposreal _ (Rmin_stable_in_posreal d0 d7))))
                        (mkposreal _ (Rmin_stable_in_posreal 
                                     (mkposreal _ Rlt_0_1)
                                     (mkposreal _ J2))))))).
simpl; intros u v Hu Hv.
replace (Derive (fun z : R => RInt (fun t : R => f z t) v b) u) with 
  (RInt (fun z => Derive (fun u => f u z) u) v b).
replace (Derive (fun z : R => RInt (fun t : R => f z t) (a x) b) x) with
  (RInt (fun z => Derive (fun u => f u z) x) (a x) b).
replace (RInt (fun z : R => Derive (fun u0 : R => f u0 z) u) v b -
   RInt (fun z : R => Derive (fun u0 : R => f u0 z) x) (a x) b) with
  ((RInt (fun z : R => Derive (fun u0 : R => f u0 z) u) v b
        - RInt (fun z : R => Derive (fun u0 : R => f u0 z) x) v b) +
   (RInt (fun z : R => Derive (fun u0 : R => f u0 z) x) v b
        - RInt (fun z : R => Derive (fun u0 : R => f u0 z) x) (a x) b)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var eps).
apply Rplus_lt_compat.
rewrite <- RInt_minus.
apply Rle_lt_trans with (Rabs (b-v) * (eps/ (Rabs ( b - a x)+1)/2)).
apply RInt_le_const.
apply ex_RInt_minus.
apply Hd7.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
apply Hd7.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
intros t Ht.
simpl in Hd5.
left.
apply Hd5.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply (Rabs_le_between' _ _).
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply (Rabs_le_between' _ _).
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
split; apply Rplus_le_reg_l with (-x); ring_simplify.
rewrite <- Ropp_0; apply Ropp_le_contravar.
left; apply cond_pos.
left; apply cond_pos.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply (Rabs_le_between' _ _).
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply (Rabs_le_between' _ _).
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Rlt_le_trans with ((Rabs (b - a x) + 1)*(eps / (Rabs (b - a x) + 1) / 2)).
apply Rmult_lt_compat_r.
exact J1.
replace (b-v) with ((b-a x)+-(v-a x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
apply Rplus_lt_compat_l.
rewrite Rabs_Ropp.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
right; field.
apply sym_not_eq, Rlt_not_eq.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Hd7.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
apply Hd7.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
unfold Rminus; rewrite RInt_swap.
rewrite <- RInt_Chasles.
apply Rle_lt_trans with (Rabs (a x -v) *
   (Rabs (Derive (fun z : R => f z (a x)) x) +1)).
apply RInt_le_const.
apply ex_RInt_add_interval with b.
apply Hd7.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
apply ex_RInt_bound.
apply Hd7.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
intros t Ht.
apply Rplus_le_reg_r with (-Rabs (Derive (fun z : R => f z (a x)) x)).
apply Rle_trans with (1:=Rabs_triang_inv _ _).
apply Rle_trans with 1;[idtac|right; ring].
left; apply Hd6.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Rle_lt_trans with (Rabs (v-a x)).
unfold Rabs; case (Rcase_abs (t - a x)); case (Rcase_abs (v - a x)); intros Y1 Y2.
apply Ropp_le_contravar; apply Rplus_le_compat_r.
apply Rle_trans with (2:=proj1 Ht).
right; apply sym_eq, Rmin_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply Rle_lt_trans with (2:=Y1).
right; ring.
contradict Y2.
apply Rle_not_lt.
apply Rplus_le_reg_l with (a x); ring_simplify.
apply Rle_trans with (2:=proj1 Ht).
right; apply sym_eq, Rmin_right.
apply Rplus_le_reg_l with (-a x); ring_simplify.
apply Rge_le, Rge_trans with (2:=Y1).
right; ring.
case Y2; intros Y3.
contradict Y3.
apply Rle_not_lt.
apply Rplus_le_reg_l with (a x); ring_simplify.
apply Rle_trans with (1:=proj2 Ht).
right; apply Rmax_right.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply Rle_lt_trans with (2:=Y1).
right; ring.
rewrite Y3.
apply Rlt_le; apply Ropp_0_gt_lt_contravar; exact Y1.
apply Rplus_le_compat_r.
apply Rle_trans with (1:=proj2 Ht).
right; apply Rmax_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
apply Rge_le, Rge_trans with (2:=Y1).
right; ring.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Rlt_le_trans with ((eps / (Rabs (Derive (fun z : R => f z (a x)) x) + 1) / 2) * 
  (Rabs (Derive (fun z : R => f z (a x)) x) + 1)).
apply Rmult_lt_compat_r.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
replace (a x -v) with (-(v-a x)) by ring; rewrite Rabs_Ropp.
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
destruct Df as (d ,Hd).
exists d.
intros y Hy t Ht.
apply Hd.
exact Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
pattern (a x) at 2; replace (a x) with (a x-0) by ring.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
pattern (a x) at 1; replace (a x) with (a x+0) by ring.
apply Rplus_le_compat_l.
left; apply cond_pos.
intros t Ht.
apply Cdf.
rewrite /Rminus Rplus_opp_r Rabs_R0; apply cond_pos.
admit. (* ok *)
exists d1.
intros y Hy.
now apply Ia.
(* *)
apply sym_eq, is_derive_unique.
apply derivable_pt_lim_param.
admit. (* mouais faudra pe d3/2 ... *)
intros t Ht.
apply Cdf.
admit. (* ok *)
admit. (* ok *)
admit. (* see Df *)
Qed.






Lemma derivable_pt_lim_RInt_param_bound_comp_aux2 :
  forall f a b x da,
  (locally (fun y => ex_RInt (fun t => f y t) (a x) b) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x -eps) (a x + eps)) x) ->
  derivable_pt_lim a x da ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (exists eps:posreal, locally
   (fun x0 => 
       forall t : R,
          Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x0 t) x) ->
   continuity_pt (fun t => f x t) (a x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) b) x
    ((Derive (fun u => RInt (fun t : R => f u t) (a x) b) x)+(-f x (a x))*da).
Proof.
intros f a b x da Hi (d0,Ia) Da Df Cdf Cfa.
replace  (Derive (fun u => RInt (fun t : R => f u t) (a x) b) x) with 
   ((Derive (fun u => RInt (fun t : R => f u t) (a x) b) x)*1) by ring.
apply derivable_pt_lim_comp_2d with 
   (f1 := fun x0 y => RInt (fun t : R => f x0 t) y b).
(* *)
apply derivable_differentiable_pt_lim.
(* . *)
destruct Df as (d1,(d2,Hd12)).
destruct Cdf as (d3,(d4,Hd34)).
move: (locally_and _ _ _ Hi Ia) => Y.
destruct Y as (d5,Hd5).
exists (mkposreal _ (Rmin_stable_in_posreal  
                       (mkposreal _ (Rmin_stable_in_posreal (mkposreal _ (Rmin_stable_in_posreal d0 (pos_div_2 d5)))
                                    (mkposreal _ (Rmin_stable_in_posreal d3 d4))))
                       (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))))).
simpl; intros u v Hu Hv.
eexists; eapply derivable_pt_lim_param.
(* .. *)
exists (pos_div_2 d2).
intros y Hy t Ht.
apply Hd12.
replace (y-x) with ((y-u)+(u-x)) by ring.
rewrite (double_var d2).
apply Rle_lt_trans with (1:=Rabs_triang _ _).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (d1-v).
apply Rle_trans with (-(v- a x)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with d1;[idtac|right; ring].
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (- a x).
apply Rle_trans with (v- a x).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
apply Rle_trans with d1;[idtac|right; ring].
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
(* .. *)
intros t Ht.
apply Hd34.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (d3-v).
apply Rle_trans with (-(v- a x)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with d3;[idtac|right; ring].
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (- a x).
apply Rle_trans with (v- a x).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
apply Rle_trans with d3;[idtac|right; ring].
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
(* .. *)
exists (pos_div_2 d5).
intros y Hy.
apply ex_RInt_add_interval with (a x).
case (Rle_or_lt v (a x)); intros Y.
apply ex_RInt_included2 with (a x - d0).
apply ex_RInt_included1 with (a x + d0).
apply Hd5.
replace (y-x) with ((y-u)+(u-x)) by ring.
rewrite (double_var d5).
apply Rle_lt_trans with (1:=Rabs_triang _ _).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
split.
apply Rplus_le_reg_l with (-a x); ring_simplify.
rewrite <- Ropp_0.
apply Ropp_le_contravar; left; apply cond_pos.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
split.
apply Rplus_le_reg_l with (d0-v).
apply Rle_trans with (-(v- a x)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rle_trans with d0;[idtac|right; ring].
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
exact Y.
apply ex_RInt_bound.
apply ex_RInt_included1 with (a x + d0).
apply ex_RInt_included2 with (a x - d0).
apply Hd5.
replace (y-x) with ((y-u)+(u-x)) by ring.
rewrite (double_var d5).
apply Rle_lt_trans with (1:=Rabs_triang _ _).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
split.
apply Rplus_le_reg_l with (-a x); ring_simplify.
rewrite <- Ropp_0.
apply Ropp_le_contravar; left; apply cond_pos.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
split.
left; exact Y.
apply Rplus_le_reg_l with (-a x).
apply Rle_trans with ((v- a x)).
right; ring.
apply Rle_trans with (1:=RRle_abs _).
apply Rle_trans with d0;[idtac|right; ring].
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply Hd5.
replace (y-x) with ((y-u)+(u-x)) by ring.
rewrite (double_var d5).
apply Rle_lt_trans with (1:=Rabs_triang _ _).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
(* . *)
apply derivable_pt_lim_RInt'.
apply locally_singleton in Hi.
exact Hi.
apply locally_singleton in Ia.
now exists d0.
exact Cfa.
apply derivable_pt_lim_RInt_param_bound_comp_aux1.
exact Hi.
now exists d0.
exact Df.
exact Cdf.
apply derivable_pt_lim_id.
exact Da.
Qed.




