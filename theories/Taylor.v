Require Import Reals Rcomplements.
Require Import ssreflect.
Require Import Derive.
Require Import Locally Differential.

Lemma C_n_n: forall n, C n n = 1.
intros n; unfold C.
rewrite minus_diag.
simpl.
field.
apply INR_fact_neq_0.
Qed.

Lemma C_n_0: forall n, C n 0 = 1.
intros n; unfold C.
rewrite - minus_n_O.
simpl.
field.
apply INR_fact_neq_0.
Qed.

Definition partial_derive (m k : nat) (f : R -> R -> R) : R -> R -> R :=
  fun x y => Derive_n (fun t => Derive_n (fun z => f t z) k y) m x.

Definition differential (p : nat) (f : R -> R -> R) (x y dx dy : R) : R :=
  sum_f_R0 
    (fun m =>
      C p m *
      partial_derive m (p - m)%nat f x y *
      dx ^ m * dy ^ (p - m)%nat)
    p.

Definition DL_pol (n : nat) (f : R -> R -> R) (x y dx dy : R) : R :=
  sum_f_R0
    (fun p =>
      differential p f x y dx dy / INR (fact p))
    n.


Lemma partial_derive_ext_loc :
  forall f g p q x y,
  locally_2d (fun u v => f u v = g u v) x y ->
  partial_derive p q f x y = partial_derive p q g x y.
Proof.
intros f g p q x y H.
unfold partial_derive.
apply Derive_n_ext_loc.
destruct H as (e,He).
exists e.
intros u Hu.
apply Derive_n_ext_loc.
exists e.
intros v Hv.
now apply He.
Qed.

Lemma Schwarz_aux :
  forall f x y (eps : posreal),
  ( forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps ->
    ex_derive (fun z => f z v) u /\
    ex_derive (fun z => Derive (fun t => f t z) u) v ) ->
  forall h k, Rabs h < eps -> Rabs k < eps ->
  let phi k x := f x (y + k) - f x y in
  exists u, exists v,
  Rabs (u - x) <= Rabs h /\ Rabs (v - y) <= Rabs k /\
  phi k (x + h) - phi k x = h * k * (Derive (fun z => Derive (fun t => f t z) u) v).
Proof.
intros f x y eps HD h k Hh Hk phi.
assert (Hx: x + h - x = h) by ring.
assert (Hy: y + k - y = k) by ring.
(* . *)
destruct (MVT_cor4 (phi k) x (Rabs h)) with (b := x + h) as (u&Hu1&Hu2).
intros c Hc.
apply ex_derive_minus.
apply HD.
now apply Rle_lt_trans with (Rabs h).
now rewrite Hy.
apply HD.
now apply Rle_lt_trans with (Rabs h).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite Hx.
apply Rle_refl.
rewrite Hx in Hu1, Hu2.
exists u.
(* . *)
destruct (MVT_cor4 (fun v => Derive (fun t => f t v) u) y (Rabs k)) with (b := y + k) as (v&Hv1&Hv2).
intros c Hc.
apply HD.
now apply Rle_lt_trans with (Rabs h).
now apply Rle_lt_trans with (1 := Hc).
rewrite Hy.
apply Rle_refl.
rewrite Hy in Hv1, Hv2.
exists v.
(* . *)
refine (conj Hu2 (conj Hv2 _)).
rewrite Hu1 /phi Derive_minus.
rewrite Hv1.
ring.
apply HD.
now apply Rle_lt_trans with (Rabs h).
now rewrite Hy.
apply HD.
now apply Rle_lt_trans with (Rabs h).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
Qed.

Lemma Schwarz :
  forall f x y,
  locally_2d (fun u v =>
    ex_derive (fun z => f z v) u /\
    ex_derive (fun z => f u z) v /\
    ex_derive (fun z => Derive (fun t => f z t) v) u /\
    ex_derive (fun z => Derive (fun t => f t z) u) v) x y ->
  continuity2_pt (fun u v => Derive (fun z => Derive (fun t => f z t) v) u) x y ->
  continuity2_pt (fun u v => Derive (fun z => Derive (fun t => f t z) u) v) x y ->
  Derive (fun z => Derive (fun t => f z t) y) x = Derive (fun z => Derive (fun t => f t z) x) y.
Proof.
intros f x y (eps, HD) HC2 HC1.
refine (let H1 := Schwarz_aux f x y eps _ in _).
intros u v Hu Hv.
split ; now apply HD.
refine (let H2 := Schwarz_aux (fun x y => f y x) y x eps _ in _).
intros u v Hu Hv.
split ; now apply HD.
simpl in H1, H2.
apply Req_lt_aux.
intros e.
destruct (HC1 (pos_div_2 e)) as (d1,Hc1).
destruct (HC2 (pos_div_2 e)) as (d2,Hc2).
set (d := Rmin (Rmin (pos_div_2 d1) (pos_div_2 d2)) (pos_div_2 eps)).
assert (Hd: d > 0).
apply Rmin_glb_lt.
apply Rmin_stable_in_posreal.
apply cond_pos.
assert (K: Rabs d < eps).
rewrite Rabs_right.
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply (Rlt_eps2_eps eps).
apply cond_pos.
now apply Rgt_ge.
specialize (H1 d d K K).
specialize (H2 d d K K).
destruct H1 as (u1&v1&Hu1&Hv1&H1).
destruct H2 as (v2&u2&Hv2&Hu2&H2).
clear K.
rewrite (Rabs_right d (Rgt_ge _ _ Hd)) in Hu1 Hv1 Hu2 Hv2.
assert (K: forall a b, Rabs (a - b) <= d -> Rabs (a - b) < d1).
intros a b H.
apply Rle_lt_trans with (1 := H).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply (Rlt_eps2_eps d1).
apply cond_pos.
specialize (Hc1 u1 v1 (K _ _ Hu1) (K _ _ Hv1)).
clear K.
assert (K: forall a b, Rabs (a - b) <= d -> Rabs (a - b) < d2).
intros a b H.
apply Rle_lt_trans with (1 := H).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply (Rlt_eps2_eps d2).
apply cond_pos.
specialize (Hc2 u2 v2 (K _ _ Hu2) (K _ _ Hv2)).
clear -Hd H1 H2 Hc1 Hc2.
assert (H: forall a b c, b - c = -(a - b) + (a - c)) by (intros ; ring).
rewrite (H (Derive (fun z : R => Derive (fun t : R => f z t) v2) u2)).
clear H.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite Rabs_Ropp (double_var e).
apply Rplus_lt_compat.
exact Hc2.
replace (Derive (fun z : R => Derive (fun t : R => f z t) v2) u2) with
  (Derive (fun z : R => Derive (fun t : R => f t z) u1) v1).
exact Hc1.
apply Rmult_eq_reg_l with (d * d).
rewrite -H1 -H2.
ring.
apply Rgt_not_eq.
now apply Rmult_gt_0_compat.
Qed.

Theorem Taylor_Lagrange :
  forall f n x y, x < y ->
  ( forall t, x <= t <= y -> forall k, (k <= S n)%nat -> ex_derive_n f k t ) ->
  exists zeta, x < zeta < y /\
    f y =  sum_f_R0 (fun m => (y-x) ^ m / INR (fact m) * Derive_n f m x )  n
        + (y-x) ^ (S n) / INR (fact (S n)) * Derive_n f (S n) zeta.
Proof.
intros f n x y Hxy Df.
pose (c:= (f y - sum_f_R0 (fun m => (y-x) ^ m / INR (fact m) * Derive_n f m x )  n)
                / (y-x) ^ (S n)).
pose (g t := f y - sum_f_R0 (fun m => (y-t) ^ m / INR (fact m) * Derive_n f m t )  n
               - c * (y-t) ^ (S n)).
assert (Dg : forall t, x <= t <= y -> is_derive g t
  (- (y-t) ^ n / INR (fact n) * Derive_n f (S n) t + c * INR (S n) * (y-t) ^ n)).
intros t Ht.
unfold g.
assert (Dp: forall n, derivable_pt_lim (fun x0 : R => (y - x0) ^ S n) t (INR (S n) * (y - t) ^ n * (0 - 1))).
intros m.
apply (derivable_pt_lim_comp (fun t => y - t) (fun t => t ^ (S m))).
apply derivable_pt_lim_minus.
apply derivable_pt_lim_const.
apply derivable_pt_lim_id.
apply derivable_pt_lim_pow.
(* *)
apply derivable_pt_lim_plus.
(* . *)
clear c g.
rename n into N.
generalize (le_refl N).
generalize N at -2.
intros n.
induction n.
(* .. *)
intros _.
simpl.
replace (-1 / 1 * Derive (fun x0 : R => f x0) t) with (0 - (1/1 * Derive (fun x0 : R => f x0) t)) by field.
apply derivable_pt_lim_minus.
apply derivable_pt_lim_const.
apply derivable_pt_lim_scal with (f := fun u => f u).
apply Derive_correct.
apply (Df t Ht 1%nat).
apply le_n_S.
apply le_0_n.
(* .. *)
intros Hn.
apply is_derive_ext with (fun x0 : R =>
   (f y -
   (sum_f_R0 (fun m : nat => (y - x0) ^ m / INR (fact m) * Derive_n f m x0) n)) -
    (y - x0) ^ (S n) / INR (fact (S n)) *
     Derive_n f (S n) x0).
simpl.
intros; ring.
replace (- (y - t) ^ S n / INR (fact (S n)) * Derive_n f (S (S n)) t) with
  ((- (y - t) ^ n / INR (fact n) * Derive_n f (S n) t) -
      (- (y - t) ^ n / INR (fact n) * (Derive_n f (S n) t) +
       ( (y - t) ^ S n / INR (fact (S n)) * Derive_n f (S (S n)) t))).
2: rewrite /Rdiv Ropp_mult_distr_l_reverse ; ring.
apply derivable_pt_lim_plus.
apply IHn.
now apply lt_le_weak.
apply derivable_pt_lim_opp.
apply (derivable_pt_lim_mult (fun x0 => ((y - x0) ^ S n / INR (fact (S n)))) 
  (fun x0 => Derive_n f (S n) x0)).
replace (- (y - t) ^ n / INR (fact n)) with
   (/ INR (fact (S n)) * (INR (S n)*(y - t) ^ n*(0-1))).
apply is_derive_ext with (fun x0 : R => (/ INR (fact (S n)) * (y - x0) ^ S n)).
intros; unfold Rdiv; apply Rmult_comm.
now apply derivable_pt_lim_scal.
change (fact (S n)) with ((S n)*fact n)%nat.
rewrite mult_INR.
field.
split.
apply INR_fact_neq_0.
now apply not_0_INR.
apply Derive_correct.
apply (Df t Ht (S (S n))).
now apply le_n_S.
(* . *)
apply is_derive_ext with (fun x0 : R => -c * (y - x0) ^ S n).
intros; ring.
replace (c * INR (S n) * (y - t) ^ n) with ((-c) * ((INR (S n) * (y - t) ^ n) * (0-1))) by ring.
now apply derivable_pt_lim_scal.
(* *)
assert (Dg' : forall t : R, x <= t <= y -> derivable_pt g t).
intros t Ht.
exists (Derive g t).
apply Derive_correct.
eexists.
apply (Dg t Ht).
assert (pr : forall t : R, x < t < y -> derivable_pt g t).
intros t Ht.
apply Dg'.
split ; now apply Rlt_le.
(* *)
assert (Zxy: (y - x) ^ (S n) <> 0).
apply pow_nonzero.
apply Rgt_not_eq.
apply Rplus_gt_reg_l with x.
now ring_simplify.
(* *)
destruct (Rolle g x y pr) as (zeta, (Hzeta1,Hzeta2)).
intros t Ht.
apply derivable_continuous_pt.
now apply Dg'.
exact Hxy.
apply trans_eq with 0.
unfold g, c.
now field.
unfold g.
destruct n.
simpl; field.
rewrite decomp_sum.
rewrite sum_eq_R0.
simpl; field.
intros; simpl; field.
exact (INR_fact_neq_0 (S n0)).
apply lt_0_Sn.
exists zeta.
apply (conj Hzeta1).
rewrite Rmult_assoc.
replace (/ INR (fact (S n)) * Derive_n f (S n) zeta) with c.
unfold c.
now field.
apply Rmult_eq_reg_r with (INR (S n) * (y - zeta) ^ n).
apply Rplus_eq_reg_l with ((- (y - zeta) ^ n / INR (fact n) * Derive_n f (S n) zeta)).
change (fact (S n)) with (S n * fact n)%nat.
rewrite mult_INR.
apply trans_eq with R0.
rewrite -Rmult_assoc.
assert (H: x <= zeta <= y) by (split ; apply Rlt_le ; apply Hzeta1).
rewrite -(is_derive_unique _ _ _ (Dg _ H)).
destruct (pr zeta Hzeta1) as (x0,Hd).
simpl in Hzeta2.
rewrite Hzeta2 in Hd.
now apply is_derive_unique.
field.
split.
apply INR_fact_neq_0.
now apply not_0_INR.
apply Rmult_integral_contrapositive_currified.
now apply not_0_INR.
apply pow_nonzero.
apply Rgt_not_eq.
apply Rplus_gt_reg_l with zeta.
ring_simplify.
apply Hzeta1.
Qed.

Fixpoint ex_diff_n f n x y :=
  continuity2_pt f x y /\
  match n with
  | O => True
  | S n =>
    ex_derive (fun z => f z y) x /\
    ex_derive (fun z => f x z) y /\
    ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y /\
    ex_diff_n (fun u v => Derive (fun z => f u z) v) n x y
  end.

Lemma continuity2_pt_eta: forall f g x y,
    locally_2d (fun u v =>  f u v = g u v) x y 
      -> continuity2_pt f x y -> continuity2_pt g x y.
unfold continuity2_pt; intros f g x y H1 H2 eps.
specialize (H2 eps).
move: (locally_2d_and _ _ _ _ H1 H2) => {H1 H2} H.
apply locally_2d_align with (2:=H).
intros eps0 H1 u v H2 H3.
rewrite - (proj1 (H1 u v H2 H3)).
rewrite - (proj1 (H1 x y _ _)).
now apply H1.
rewrite Rminus_eq0 Rabs_R0; apply cond_pos.
rewrite Rminus_eq0 Rabs_R0; apply cond_pos.
Qed.



Lemma ex_diff_n_eta: forall f g n x y,
    locally_2d (fun u v =>  f u v = g u v) x y 
      -> ex_diff_n f n x y -> ex_diff_n g n x y.
intros f g n; revert f g.
induction n.
intros f g x y H; simpl.
intros (H1,_); split.
apply (continuity2_pt_eta _ _ _ _ H H1).
easy.
simpl.
intros f g x y H (H1&H2&H3&H4&H5).
split.
apply (continuity2_pt_eta _ _ _ _ H H1).
split.
apply ex_derive_ext_loc with (2:=H2).
apply locally_2d_1d_const_y with (1:=H).
split.
apply ex_derive_ext_loc with (2:=H3).
apply locally_2d_1d_const_x with (1:=H).
split.
apply IHn with (2:=H4).
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H6.
apply Derive_ext_loc.
apply locally_2d_1d_const_y with (1:=H6).
apply IHn with (2:=H5).
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H6.
apply Derive_ext_loc.
apply locally_2d_1d_const_x with (1:=H6).
Qed.



Lemma ex_diff_n_m : forall n m, (m <= n)%nat -> forall f x y, ex_diff_n f n x y -> ex_diff_n f m x y.
assert (forall n f x y, ex_diff_n f (S n) x y -> ex_diff_n f n x y).
induction n.
simpl.
intros f x y H; split; try apply H.
intros f x y H.
repeat (split; try apply H).
apply IHn.
apply H.
apply IHn.
apply H.
intros n m H1 f x y Hn.
induction n.
replace m with 0%nat.
exact Hn.
now apply le_n_0_eq.
case (le_lt_or_eq _ _ H1).
intros H2; apply IHn.
now apply gt_S_le.
apply (H _ _ _ _ Hn).
intros H2; now rewrite H2.
Qed.



Lemma ex_diff_n_deriv_aux1: forall f n x y, 
  ex_diff_n f (S n) x y -> ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y.
Proof.
intros f n x y.
case n.
simpl.
intros H; split; apply H.
clear n;intros n H.
simpl in H.
repeat split; apply H.
Qed.


Lemma ex_diff_n_deriv_aux2: forall f n x y, 
  ex_diff_n f (S n) x y -> ex_diff_n (fun u v => Derive (fun z => f u z) v) n x y.
Proof.
intros f n x y.
case n.
simpl.
intros H; split; apply H.
clear n;intros n H.
simpl in H.
repeat split; apply H.
Qed.



Lemma ex_diff_n_deriv: forall n p q, (p+q <= n)%nat -> forall f x y,
    ex_diff_n f n x y-> ex_diff_n (partial_derive p q f) (n -(p+q)) x y.
induction p.
(* . *)
intros q; rewrite plus_0_l.
induction q.
intros H f x y H1.
unfold partial_derive.
simpl.
rewrite - minus_n_O.
apply: (ex_diff_n_eta _ _ _ _ _ _ H1).
now apply locally_2d_forall.
intros H f x y H1.
apply (ex_diff_n_eta (fun u v => Derive (fun z => (partial_derive 0 q f) u z) v)).
apply locally_2d_forall.
intros u v; unfold partial_derive.
reflexivity.
apply ex_diff_n_deriv_aux2.
replace ((S (n - S q))) with (n-q)%nat by omega.
apply IHq.
now apply lt_le_weak.
exact H1.
(* . *)
intros q H f x y H1.
apply (ex_diff_n_eta (fun u v => Derive (fun z => (partial_derive p q f) z v) u)).
apply locally_2d_forall.
intros u v; unfold partial_derive.
reflexivity.
apply ex_diff_n_deriv_aux1.
replace ((S (n - (S p +q)))) with (n-(p+q))%nat by omega.
apply IHp.
now apply lt_le_weak.
exact H1.
Qed.


Lemma ex_diff_n_ex_deriv_inf_1 : forall n p k, (p+k < n)%nat -> forall f x y,
    ex_diff_n f n x y -> 
    ex_derive  (fun z : R => partial_derive p k f z y) x.
Proof.
intros n p; case p; clear p.
(* . *)
intros k; case k; clear k.
case n; clear n.
intros Hn; contradict Hn; apply lt_n_O.
intros n _ f x y H.
unfold partial_derive; simpl.
apply H.
intros n0 H f x y Hf.
assert (ex_diff_n (partial_derive 0 n0 f) (n -(0+n0)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
revert H0; rewrite plus_0_l.
case_eq (n-n0)%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1 H2.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive 0 n0 f z) t) y).
intros y0; unfold partial_derive; simpl.
reflexivity.
simpl in H2.
destruct H2 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T5.
apply T5.
(* . *)
intros p q H f x y Hf.
assert (ex_diff_n (partial_derive p q f) (n -(p+q)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
case_eq (n-(p+q))%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive p q f t) y) z).
intros x0; unfold partial_derive; simpl.
reflexivity.
rewrite H1 in H0; simpl in H0.
destruct H0 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T4.
apply T4.
Qed.


Lemma ex_diff_n_ex_deriv_inf_2 : forall n p k, (p+k < n)%nat -> forall f x y,
  ex_diff_n f n x y -> 
  ex_derive (fun z => partial_derive p k f x z) y.
Proof.
intros n p; case p; clear p.
(* . *)
intros k; case k; clear k.
case n; clear n.
intros Hn; contradict Hn; apply lt_n_O.
intros n _ f x y H.
unfold partial_derive; simpl.
apply H.
intros n0 H f x y Hf.
assert (ex_diff_n (partial_derive 0 n0 f) (n -(0+n0)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
revert H0; rewrite plus_0_l.
case_eq (n-n0)%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1 H2.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive 0 n0 f x) t) z).
intros y0; unfold partial_derive; simpl.
reflexivity.
simpl in H2.
destruct H2 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T5.
apply T5.
(* . *)
intros p q H f x y Hf.
assert (ex_diff_n (partial_derive p q f) (n -(p+q)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
case_eq (n-(p+q))%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive p q f t) z) x).
intros x0; unfold partial_derive; simpl.
reflexivity.
rewrite H1 in H0; simpl in H0.
destruct H0 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T4.
apply T4.
Qed.



Lemma ex_diff_n_continuity_inf_1 : forall n p k, (p+k < n)%nat -> forall f x y,
  ex_diff_n f n x y ->
  continuity2_pt (fun u v => Derive (fun z : R => partial_derive p k f z v) u) x y.
Proof.
intros n p k Hn f x y Hf.
assert (ex_diff_n (partial_derive (S p) k f) (n -(S p+k)) x y).
now apply ex_diff_n_deriv.
apply continuity2_pt_eta with (partial_derive (S p) k f).
apply locally_2d_forall.
intros u v; unfold partial_derive; simpl.
reflexivity.
revert H; case (n - (S p + k))%nat.
simpl; intros H; apply H.
intros n0; simpl; intros H; apply H.
Qed.


Lemma Schwarz_ext_aux: forall p f x y, 
  locally_2d (ex_diff_n f (S p)) x y ->
   partial_derive  1 p f x y = partial_derive 0 p (partial_derive  1 0 f) x y.
intros p; induction p.
intros f x y H.
unfold partial_derive; now simpl.
intros f x y H.
apply trans_eq with  (partial_derive 1 p (partial_derive 0 1 f) x y).
unfold partial_derive.
simpl.
apply Derive_ext.
intros t.
apply trans_eq with (Derive_n (Derive_n (fun z : R => f t z) p) 1 y).
reflexivity.
rewrite Derive_n_comp.
rewrite plus_comm.
rewrite -Derive_n_comp.
reflexivity.
rewrite IHp.
apply trans_eq with 
  (partial_derive 0 p (partial_derive 0 1 (partial_derive 1 0 f)) x y).
unfold partial_derive.
simpl.
apply Derive_n_ext_loc.
cut (locally_2d (fun u v => 
         Derive (fun x0 : R => Derive (fun x1 : R => f x0 x1) v) u =
         Derive (fun x0 : R => Derive (fun x1 : R => f x1 x0) u) v) x y).
apply locally_2d_1d_const_x.
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H1.
apply Schwarz.
apply locally_2d_impl with (2:=H1).
apply locally_2d_forall.
intros u' v' H2.
split.
apply H2.
split.
apply H2.
simpl in H2; destruct H2 as (T1&T2&T3&T4&T5).
split.
apply T5.
apply T4.
apply locally_2d_singleton in H1.
simpl in H1; destruct H1 as (T1&T2&T3&T4&T5).
destruct T5 as (Y1&Y2&Y3&Y4&Y5).
clear - Y4.
case p in Y4; simpl in Y4; apply Y4.
apply locally_2d_singleton in H1.
simpl in H1; destruct H1 as (T1&T2&T3&T4&T5).
destruct T4 as (Y1&Y2&Y3&Y4&Y5).
clear - Y5.
case p in Y5; simpl in Y5; apply Y5.
unfold partial_derive.
simpl.
apply trans_eq with (Derive_n (Derive_n (fun z => Derive (fun x0 => f x0 z) x) p) 1 y).
rewrite Derive_n_comp.
rewrite plus_comm.
rewrite -Derive_n_comp.
reflexivity.
reflexivity.
apply locally_2d_impl with (2:=H).
apply locally_2d_forall.
intros u v.
pattern (S p) at 2; replace (S p) with (S (S p) -(0+1))%nat.
apply ex_diff_n_deriv.
rewrite plus_0_l.
apply lt_le_S; apply lt_0_Sn.
rewrite plus_0_l.
omega.
Qed.

Lemma partial_derive_add_zero: forall f p q r s x y,
  (q=0)%nat \/ (r=0)%nat ->
  partial_derive p q (partial_derive r s f) x y
   = partial_derive (p+r) (q+s) f x y.
intros f p q r s x y H.
destruct H; rewrite H.
rewrite plus_0_l.
unfold partial_derive.
simpl.
rewrite -Derive_n_comp.
now apply Derive_n_ext.
rewrite plus_0_r.
unfold partial_derive.
simpl.
apply Derive_n_ext.
intros y0.
rewrite -Derive_n_comp.
now apply Derive_n_ext.
Qed.


Lemma Schwarz_ext_aux2: forall p k f x y, 
  locally_2d (ex_diff_n f (p+S k)) x y ->
  partial_derive 0 1 (partial_derive p k f) x y =
     partial_derive p (S k) f x y.
intros p; induction p.
intros; easy.
intros k f x y Y.
apply sym_eq.
apply trans_eq with
  (partial_derive p 0 (partial_derive 1 (S k) f) x y).
rewrite partial_derive_add_zero.
rewrite plus_0_l.
replace (S p) with (p+1)%nat by apply plus_comm.
easy.
now left.
apply trans_eq with 
  (partial_derive p 0 (partial_derive 0 (S k) (partial_derive 1 0 f)) x y).
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=Y).
apply locally_2d_forall.
intros u v H.
apply Schwarz_ext_aux.
apply locally_2d_impl with (2:=H).
apply locally_2d_forall.
intros u'' v''.
apply ex_diff_n_m.
omega.
apply trans_eq with (partial_derive p (S k) (partial_derive 1 0 f) x y).
rewrite partial_derive_add_zero.
now rewrite plus_0_l plus_0_r.
now right.
rewrite - IHp.
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=Y).
apply locally_2d_forall.
intros u v H.
apply trans_eq with 
 (partial_derive p 0 (partial_derive 0 k (partial_derive 1 0 f)) u v).
rewrite (partial_derive_add_zero _ _ 0%nat).
now rewrite plus_0_l plus_0_r.
now right.
apply trans_eq with 
 (partial_derive p 0 (partial_derive 1 k f) u v).
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u' v' H'.
apply sym_eq.
apply Schwarz_ext_aux.
apply locally_2d_impl with (2:=H').
apply locally_2d_forall.
intros u'' v''.
apply ex_diff_n_m.
apply le_plus_r.
rewrite partial_derive_add_zero.
rewrite plus_0_l.
replace (S p) with (p+1)%nat by apply plus_comm.
easy.
now left.
apply locally_2d_impl with (2:=Y).
apply locally_2d_forall.
intros u'' v''.
replace (p+ S k)%nat with ((S p+S k)-(1+0))%nat. 
apply ex_diff_n_deriv.
rewrite plus_0_r.
apply le_plus_trans; apply lt_le_S; apply lt_0_Sn.
rewrite plus_0_r.
omega.
Qed.


Lemma Schwarz_ext: forall p k f x y, 
  locally_2d (ex_diff_n f (p+S k)) x y ->
  Derive (fun v : R => partial_derive p k f x v) y =
     partial_derive p (S k) f x y.
intros p k f x y H.
generalize (Schwarz_ext_aux2 p k f x y H).
easy.
Qed.



Lemma ex_diff_n_continuity_inf_2 : forall n p k, (p+k < n)%nat -> forall f x y,
  ex_diff_n f n x y ->
  continuity2_pt (fun u v => Derive (fun z : R => partial_derive p k f u z) v) x y.
Proof.
intros n p k Hn f x y Hf.
assert (ex_diff_n (partial_derive p k f) (n -(p+k)) x y).
apply ex_diff_n_deriv.
now apply lt_le_weak.
exact Hf.
revert H; case_eq (n-(p+k))%nat.
intros H; contradict Hn.
omega.
intros n0 Hn0; simpl; intros (T1&T2&T3&T4&T5).
revert T5; case n0.
intros Y; apply Y.
intros n1 Y; apply Y.
Qed.





Definition DL_regular_n f m x y :=
  exists D, locally_2d (fun u v =>
    Rabs (f u v - DL_pol m f x y (u-x) (v-y)) <= D * (Rmax (Rabs (u-x)) (Rabs (v-y))) ^ (S m)) x y.



Theorem Taylor_Lagrange_2D : forall f n x y,
  locally_2d (fun u v => ex_diff_n f (S n) u v) x y -> DL_regular_n f n x y.
Proof.
intros f n x y Df.
(* *)
assert (exists D, locally_2d (fun u v => forall p, (p <= S n)%nat ->
  Rabs (partial_derive p (S n - p) f u v) <= D) x y).
(* . *)
assert (forall p, (p <= S n)%nat -> exists D, locally_2d (fun u v => Rabs (partial_derive p (S n - p) f u v) <= D) x y).
intros p Hp.
(* .. *)
assert (continuity2_pt (partial_derive p (S n - p) f) x y).
apply locally_2d_singleton in Df.
refine (proj1 (_: ex_diff_n (partial_derive p (S n - p) f) 0 x y)).
replace O with (S n - (p + (S n - p)))%nat by rewrite le_plus_minus_r // minus_diag //.
cut (p + (S n - p) <= S n)%nat.
2: now rewrite le_plus_minus_r.
generalize (S n - p)%nat.
clear Hp.
revert f Df p.
generalize (S n).
clear n.
induction n.
intros f (H,_) [|p] [|q] H' ; try inversion H'.
done.
intros f H [|p] q H'.
destruct q as [|q].
exact H.
now apply ex_diff_n_deriv.
now apply ex_diff_n_deriv.
(* .. *)
exists (Rabs (partial_derive p (S n - p) f x y) + 1).
specialize (H (mkposreal 1 Rlt_0_1)).
apply: locally_2d_impl H.
apply: locally_2d_forall => u v H.
replace (partial_derive p (S n - p) f u v) with (partial_derive p (S n - p) f x y + (partial_derive p (S n - p) f u v - partial_derive p (S n - p) f x y)) by ring.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat_l.
now apply Rlt_le.
(* . *)
clear -H.
generalize (le_refl (S n)).
generalize (S n) at 1 3.
intros p Hp.
induction p.
move: (H _ Hp) => {H} [D H].
exists D.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H [|p] Hp' //.
inversion Hp'.
move: (IHp (le_S _ _ (le_S_n _ _ Hp))) => {IHp} [D1 H1].
move: (H _ Hp) => {H} [D2 H2].
exists (Rmax D1 D2).
move: (locally_2d_and _ _ x y H1 H2) => {H1 H2} H.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H p' Hp'.
destruct (le_lt_or_eq _ _ Hp').
apply Rle_trans with (2 := Rmax_l _ _).
apply H.
now apply gt_S_le.
apply Rle_trans with (2 := Rmax_r _ _).
now rewrite H0.
(* *)
destruct H as (D,H).
exists  (/ INR (fact (S n)) * D * sum_f_R0 (fun i : nat => Rabs (C (S n) i)) (S n)).
move: (locally_2d_and _ _ _ _ Df H) => {Df H} HH.
apply locally_2d_1d_strong in HH.
apply: locally_2d_impl HH.
apply locally_2d_forall => u v HH.
set (g t := f (x + t * (u - x)) (y + t * (v - y))).
replace (f u v) with (g 1) by (rewrite /g 2!Rmult_1_l ; apply f_equal2 ; ring).
assert (forall k t, (k <= S n)%nat -> 0 <= t <= 1 ->
  is_derive_n g k t (sum_f_R0 (fun m => C k m * partial_derive m (k - m)%nat f (x+t*(u-x)) (y+t*(v-y)) *
         (u-x) ^ m * (v-y) ^ (k - m)%nat) k)).
intros k t Hk Ht.
specialize (HH t Ht).
revert HH.
pattern t ; apply locally_singleton.
induction k.
rewrite /C /partial_derive /g /=.
apply locally_forall.
intros ; field.
specialize (IHk (le_S _ _ (le_S_n _ _ Hk))).
rewrite /is_derive_n.
apply: locally_impl_strong IHk.
apply locally_forall => {t Ht} z IHk HH.
apply is_derive_ext_loc with (fun t => sum_f_R0 (fun m => C k m *
  partial_derive m (k - m) f (x + t * (u - x)) (y + t * (v - y)) * (u - x) ^ m * (v - y) ^ (k - m)) k).
apply: locally_impl IHk.
apply: locally_impl_strong HH.
apply locally_forall => {z} z Hz HH.
specialize (HH Hz).
apply sym_eq.
now apply is_derive_n_unique.
replace (sum_f_R0 (fun m : nat => C (S k) m *
    partial_derive m (S k - m) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ m * (v - y) ^ (S k - m)) (S k)) with
  (sum_f_R0 (fun m : nat => C k m * (u - x) ^ m  * (v - y) ^ (k - m) *
    ((u - x) * partial_derive (S m) (k - m) f (x + z * (u - x)) (y + z * (v - y)) +
     (v - y) * partial_derive m (S (k - m)) f (x + z * (u - x)) (y + z * (v - y)))) k).
apply derivable_pt_lim_sum_f_R0 => p Hp.
apply is_derive_ext with (fun u0 => C k p * (u - x) ^ p * (v - y) ^ (k - p) * partial_derive p (k - p) f (x + u0 * (u - x)) (y + u0 * (v - y))).
intros w.
ring.
apply derivable_pt_lim_scal.
rewrite (Rmult_comm (u - x)) (Rmult_comm (v - y)).
apply derivable_pt_lim_comp_2d.
apply locally_singleton in HH.
replace (partial_derive (S p) (k - p) f (x + z * (u - x)) (y + z * (v - y)))
  with (Derive (fun u : R => partial_derive p (k - p) f u (y + z * (v - y))) (x + z * (u - x))).
2: reflexivity.
replace (partial_derive p (S (k - p)) f (x + z * (u - x)) (y + z * (v - y))) with
  (Derive (fun v : R => partial_derive p (k - p) f  (x + z * (u - x)) v) (y + z * (v - y))).
apply derivable_differentiable_pt_lim.
apply locally_2d_impl with (2:=HH).
apply locally_2d_forall.
clear - Hk Hp; intros u v (H1,H2).
apply ex_diff_n_ex_deriv_inf_1 with (S n).
now rewrite - le_plus_minus.
exact H1.
apply locally_2d_impl with (2:=HH).
apply locally_2d_forall.
clear - Hk Hp; intros u v (H1,H2).
apply ex_diff_n_ex_deriv_inf_2 with (S n).
now rewrite - le_plus_minus.
exact H1.
apply locally_2d_singleton in HH.
apply ex_diff_n_continuity_inf_1 with (S n).
now rewrite - le_plus_minus.
apply HH.
apply locally_2d_singleton in HH.
apply ex_diff_n_continuity_inf_2 with (S n).
now rewrite - le_plus_minus.
apply HH.
apply Schwarz_ext.
apply locally_2d_impl with (2:=HH).
apply locally_2d_forall.
intros u' v' (Y,_).
apply ex_diff_n_m with (2:=Y).
omega.
pattern (u-x) at 2; replace (u-x) with (0+(u-x)*1) by ring.
apply derivable_pt_lim_plus.
apply derivable_pt_lim_const.
specialize (derivable_pt_lim_scal (fun x => x) (u - x) z 1 (derivable_pt_lim_id z)).
unfold derivable_pt_lim, mult_real_fct.
intros H e He; destruct (H e He) as (d, Hd).
exists d; intros h Hh1 Hh2.
apply Rle_lt_trans with (2:=Hd h Hh1 Hh2).
right; apply f_equal; unfold Rdiv; ring.
pattern (v-y) at 2; replace (v-y) with (0+(v-y)*1) by ring.
apply derivable_pt_lim_plus.
apply derivable_pt_lim_const.
specialize (derivable_pt_lim_scal (fun x => x) (v - y) z 1 (derivable_pt_lim_id z)).
unfold derivable_pt_lim, mult_real_fct.
intros H e He; destruct (H e He) as (d, Hd).
exists d; intros h Hh1 Hh2.
apply Rle_lt_trans with (2:=Hd h Hh1 Hh2).
right; apply f_equal; unfold Rdiv; ring.
rewrite -(sum_eq (fun m =>
  C k m * (u - x) ^ (S m) * (v - y) ^ (k - m) * partial_derive (S m) (k - m) f (x + z * (u - x)) (y + z * (v - y)) +
  C k m * (u - x) ^ m * (v - y) ^ (S (k - m)) * partial_derive m (S (k - m)) f (x + z * (u - x)) (y + z * (v - y)))).
2: intros ; simpl ; ring.
case k; clear Hk IHk k.
unfold C; simpl.
field.
intros k.
apply sym_eq.
rewrite (decomp_sum _ (S (S k))).
2: apply lt_0_Sn.
rewrite - pred_Sn.
rewrite tech5.
rewrite (sum_eq _ (fun i : nat =>
     (C (S k) i*
    partial_derive (S i) (S (S k) - S i) f (x + z * (u - x))
      (y + z * (v - y)) * (u - x) ^ S i * (v - y) ^ (S (S k) - S i))
     + (C (S k) (S i) *
       partial_derive (S i) (S (S k) - S i) f (x + z * (u - x))
      (y + z * (v - y)) * (u - x) ^ S i * (v - y) ^ (S (S k) - S i)))).
rewrite sum_plus.
apply sym_eq.
rewrite sum_plus.
rewrite tech5.
rewrite (tech2 _ 0 (S k)).
2: apply lt_0_Sn.
replace
 (sum_f_R0
   (fun l : nat =>
    C (S k) l * (u - x) ^ l * (v - y) ^ S (S k - l) *
    partial_derive l (S (S k - l)) f (x + z * (u - x)) (y + z * (v - y))) 0)
with  (C (S (S k)) 0 *
partial_derive 0 (S (S k) - 0) f (x + z * (u - x)) (y + z * (v - y)) *
(u - x) ^ 0 * (v - y) ^ (S (S k) - 0)).
replace (C (S k) (S k) * (u - x) ^ S (S k) * (v - y) ^ (S k - S k) *
   partial_derive (S (S k)) (S k - S k) f (x + z * (u - x)) (y + z * (v - y))) with
 (C (S (S k)) (S (S k)) *
 partial_derive (S (S k)) (S (S k) - S (S k)) f (x + z * (u - x))
   (y + z * (v - y)) * (u - x) ^ S (S k) * (v - y) ^ (S (S k) - S (S k))).
replace (sum_f_R0
  (fun l : nat =>
   C (S k) l *
   partial_derive (S l) (S (S k) - S l) f (x + z * (u - x)) (y + z * (v - y)) *
   (u - x) ^ S l * (v - y) ^ (S (S k) - S l)) k)
  with (sum_f_R0
  (fun l : nat =>
   C (S k) l * (u - x) ^ S l * (v - y) ^ (S k - l) *
   partial_derive (S l) (S k - l) f (x + z * (u - x)) (y + z * (v - y))) k).
replace (sum_f_R0
  (fun l : nat =>
   C (S k) (S l) *
   partial_derive (S l) (S (S k) - S l) f (x + z * (u - x)) (y + z * (v - y)) *
   (u - x) ^ S l * (v - y) ^ (S (S k) - S l)) k)
 with (sum_f_R0
  (fun i : nat =>
   C (S k) (1 + i) * (u - x) ^ (1 + i) * (v - y) ^ S (S k - (1 + i)) *
   partial_derive (1 + i) (S (S k - (1 + i))) f (x + z * (u - x))
     (y + z * (v - y))) (S k - 1)).
ring.
replace (S k - 1)%nat with k. 2: now apply plus_minus.
apply sum_eq.
intros i Hi.
replace (1+i)%nat with (S i) by reflexivity.
replace (S (S k - S i))%nat with (S (S k) - S i)%nat.
ring.
now (rewrite minus_Sn_m; try apply le_n_S).
apply sum_eq.
intros i Hi.
replace (S k - i)%nat with (S (S k) - S i)%nat by reflexivity.
ring.
rewrite 2!C_n_n 2!minus_diag.
ring.
simpl.
rewrite 2!C_n_0.
ring.
intros.
rewrite - (pascal (S k) i).
ring.
now apply le_lt_n_Sm.
(* *)
destruct (Taylor_Lagrange g n 0 1 Rlt_0_1) as (t&Ht&Hg).
intros t Ht.
intros [|k] Hk.
easy.
eexists.
now apply (H (S k)).
(* *)
rewrite Hg /DL_pol.
replace (1 - 0) with 1 by ring.
rewrite pow1 {1}/Rminus Rplus_assoc [_*_+_]Rplus_comm -Rplus_assoc -/(Rminus _ _).
assert (forall k t, (k <= S n)%nat -> 0 <= t <= 1 -> Derive_n g k t =
      (sum_f_R0 (fun m =>  C k m * partial_derive m (k - m)%nat f (x+t*(u-x)) (y+t*(v-y)) *
         (u-x) ^ m * (v-y) ^ (k - m)%nat) k)).
intros k t0 Hk Ht0.
apply is_derive_n_unique.
now apply H.
rewrite -minus_sum sum_eq_R0.
rewrite H0.
rewrite Rplus_0_l.
unfold differential.
rewrite Rabs_mult.
eapply Rle_trans.
apply Rmult_le_compat_l.
apply Rabs_pos.
eapply Rle_trans.
apply Rsum_abs.
apply sum_Rle.
intros n0 Hn0.
rewrite Rmult_assoc 3!Rabs_mult.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rmult_le_compat.
apply Rabs_pos.
apply Rmult_le_pos; apply Rabs_pos.
specialize (HH t (conj (Rlt_le _ _ (proj1 Ht)) (Rlt_le _ _ (proj2 Ht)))).
apply locally_singleton in HH.
apply locally_2d_singleton in HH.
now apply HH.
rewrite - 2!RPow_abs.
instantiate (1:=(Rmax (Rabs (u - x)) (Rabs (v - y)) ^ S n)).
apply Rle_trans with ((Rmax (Rabs (u - x)) (Rabs (v - y)) ^ n0) * (Rmax (Rabs (u - x)) (Rabs (v - y)) ^ (S n - n0))).
apply Rmult_le_compat.
apply pow_le ; apply Rabs_pos.
apply pow_le ; apply Rabs_pos.
apply pow_incr.
split.
apply Rabs_pos.
apply Rmax_l.
apply pow_incr.
split.
apply Rabs_pos.
apply Rmax_r.
rewrite -pow_add.
rewrite -le_plus_minus.
apply Rle_refl.
exact Hn0.
rewrite - scal_sum.
rewrite /Rdiv Rmult_1_l Rabs_right .
right; ring.
apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat.
apply INR_fact_lt_0.
apply le_refl.
split; apply Rlt_le, Ht.
intros n0 hn0.
rewrite H0.
rewrite 2!Rmult_0_l 2!Rplus_0_r pow1.
unfold differential, Rdiv; ring.
now apply le_S.
split; [apply Rle_refl | apply Rle_0_1].
Qed.
