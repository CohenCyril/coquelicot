(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2013 Sylvie Boldo
#<br />#
Copyright (C) 2011-2013 Catherine Lelay
#<br />#
Copyright (C) 2011-2013 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals Rbar.
Require Import ssreflect.
Require Import Limit.
Require Import Hierarchy Continuity.
Require Import Rcomplements.
Open Scope R_scope.

(** * Definitions *)

Notation is_derive f x l := (derivable_pt_lim f x l).
Definition ex_derive f x := exists l, is_derive f x l.
Definition Derive (f : R -> R) (x : R) := real (Lim (fun h => (f (x+h) - f x)/h) 0).

Lemma derivable_pt_lim_locally :
  forall f x l,
  derivable_pt_lim f x l <->
  forall eps : posreal, locally x (fun y => y <> x -> Rabs ((f y - f x) / (y - x) - l) < eps).
Proof.
intros f x l.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d H].
exists d => y Hy Zy.
specialize (H (y - x) (Rminus_eq_contra _ _ Zy) Hy).
now ring_simplify (x + (y - x)) in H.
intros H eps He.
move: (H (mkposreal _ He)) => {H} /= [d H].
exists d => h Zh Hh.
simpl in H.
specialize (H (x + h)).
rewrite /(Rminus _ x) in H.
ring_simplify (x + h + - x) in H.
apply H => //.
contradict Zh.
apply Rplus_eq_reg_l with x.
now rewrite Rplus_0_r.
Qed.

(** Derive is correct *)

Lemma is_derive_unique f x l :
  is_derive f x l -> Derive f x = l.
Proof.
  intros H.
  apply (@f_equal _ _ real _ l).
  apply is_lim_unique.
  apply is_lim_spec.
  intros eps.
  destruct (H eps (cond_pos _)) as [d Hd].
  exists d => h.
  rewrite /= Ropp_0 Rplus_0_r.
  intros Hu Zu.
  now apply Hd.
Qed.

Lemma Derive_correct f x :
  ex_derive f x -> is_derive f x (Derive f x).
Proof.
    intros (l,H).
  cut (Derive f x = l).
    intros ; rewrite H0 ; apply H.
  apply is_derive_unique, H.
Qed.

(** Equivalence with standard library Reals *)

Lemma ex_derive_Reals_0 (f : R -> R) (x : R) :
  ex_derive f x -> derivable_pt f x.
Proof.
  move => Hf.
  apply Derive_correct in Hf.
  by exists (Derive f x).
Qed.
Lemma ex_derive_Reals_1 (f : R -> R) (x : R) :
  derivable_pt f x -> ex_derive f x.
Proof.
  case => l Hf.
  by exists l.
Qed.

Lemma Derive_Reals (f : R -> R) (x : R) (pr : derivable_pt f x) :
  derive_pt f x pr = Derive f x.
Proof.
  apply sym_eq, is_derive_unique.
  by case: pr => /= l Hf.
Qed.

(** A tactic to simplify interactive proofs of differentiability *)

Ltac search_derive := let l := fresh "l" in
evar (l : R) ;
match goal with
  | |- Derive _ _ = ?lu => apply is_derive_unique ; replace lu with l ; [ | unfold l]
  | |- derivable_pt_lim _ _ ?lu => replace lu with l ; [ | unfold l]
end.

(** Extensionality *)

Lemma is_derive_ext_loc :
  forall f g x l,
  locally x (fun t => f t = g t) ->
  is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq Hf.
apply derivable_pt_lim_locally => eps.
move /derivable_pt_lim_locally :Hf => Hf.
generalize (filter_and _ _ Heq (Hf eps)).
apply filter_imp => {Hf} y [-> Hf].
by rewrite -(locally_singleton _ _ Heq).
Qed.
Lemma ex_derive_ext_loc :
  forall f g x,
  locally x (fun t => f t = g t) ->
  ex_derive f x -> ex_derive g x.
Proof.
intros f g x Hfg (l,Hf).
exists l.
apply: is_derive_ext_loc Hfg Hf.
Qed.
Lemma Derive_ext_loc :
  forall f g x,
  locally x (fun t => f t = g t) ->
  Derive f x = Derive g x.
Proof.
intros f g x Hfg.
rewrite /Derive /Lim.
apply f_equal, Lim_seq_ext_loc.
apply (filterlim_Rbar_loc_seq 0 (fun h => (f (x + h) - f x) / h = (g (x + h) - g x) / h)).
apply (filter_imp (fun h => f (x + h) = g (x + h))).
intros h ->.
by rewrite (locally_singleton _ _ Hfg).
destruct Hfg as [eps He].
exists eps => h H Hh.
apply He.
simpl.
now replace (x + h + - x) with (h - 0) by ring.
Qed.

Lemma is_derive_ext :
  forall f g x l,
  (forall t, f t = g t) ->
  is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq.
apply is_derive_ext_loc.
exact: filter_forall.
Qed.
Lemma ex_derive_ext :
  forall f g x,
  (forall t, f t = g t) ->
  ex_derive f x -> ex_derive g x.
Proof.
intros f g x Heq.
apply ex_derive_ext_loc.
exact: filter_forall.
Qed.
Lemma Derive_ext :
  forall f g x,
  (forall t, f t = g t) ->
  Derive f x = Derive g x.
Proof.
intros f g x Hfg.
apply Derive_ext_loc.
exact: filter_forall.
Qed.

(** * Operations *)
(** Constant functions *)

Lemma ex_derive_const :
  forall a x, ex_derive (fun _ => a) x.
Proof.
intros x.
exists 0.
apply derivable_pt_lim_const.
Qed.
Lemma Derive_const :
  forall a x,
  Derive (fun _ => a) x = 0.
Proof.
intros a x.
apply is_derive_unique.
apply derivable_pt_lim_const.
Qed.

(** Identity function *)

Lemma ex_derive_id :
  forall x, ex_derive id x.
Proof.
intros x.
exists 1.
apply derivable_pt_lim_id.
Qed.
Lemma Derive_id :
  forall x,
  Derive id x = 1.
Proof.
intros x.
apply is_derive_unique.
apply derivable_pt_lim_id.
Qed.

(** ** Additive operators *)
(** Opposite of functions *)

Lemma ex_derive_opp :
  forall f x, ex_derive f x ->
  ex_derive (fun x => - f x) x.
Proof.
intros f x (df,Df).
exists (-df).
now apply derivable_pt_lim_opp.
Qed.
Lemma Derive_opp :
  forall f x,
  Derive (fun x => - f x) x = - Derive f x.
Proof.
intros f x.
unfold Derive, Lim.
rewrite /Rbar_loc_seq.
rewrite -Rbar.Rbar_opp_real.
rewrite -Lim_seq_opp.
apply f_equal, Lim_seq_ext => n.
rewrite -Ropp_mult_distr_l_reverse.
apply (f_equal (fun v => v / _)).
ring.
Qed.

(** Addition of functions *)

Lemma ex_derive_plus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => f x + g x) x.
Proof.
intros f g x (df,Df) (dg,Dg).
exists (df + dg).
now apply derivable_pt_lim_plus.
Qed.
Lemma Derive_plus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  Derive (fun x => f x + g x) x = Derive f x + Derive g x.
Proof.
intros f g x Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_plus ;
  now apply Derive_correct.
Qed.

Lemma is_derive_sum (f : nat -> R -> R) (n : nat) (x : R) (l : nat -> R) :
  (forall k, (k <= n)%nat -> is_derive (f k) x (l k))
  -> is_derive (fun y => sum_f_R0 (fun k => f k y) n) x (sum_f_R0 l n).
Proof.
  elim: n => /= [ | n IH] Hf.
  by apply (Hf O).
  apply derivable_pt_lim_plus.
  apply IH => k Hk.
  by apply Hf, le_trans with (1 := Hk), le_n_Sn.
  by apply Hf.
Qed.
Lemma ex_derive_sum (f : nat -> R -> R) (n : nat) (x : R) :
  (forall k, (k <= n)%nat -> ex_derive (f k) x)
  -> ex_derive (fun y => sum_f_R0 (fun k => f k y) n) x.
Proof.
  elim: n => /= [ | n IH] Hf.
  by apply (Hf O).
  apply ex_derive_plus.
  apply IH => k Hk.
  by apply Hf, le_trans with (1 := Hk), le_n_Sn.
  by apply Hf.
Qed.
Lemma Derive_sum (f : nat -> R -> R) (n : nat) (x : R) :
  (forall k, (k <= n)%nat -> ex_derive (f k) x)
  -> Derive (fun y => sum_f_R0 (fun k => f k y) n) x = (sum_f_R0 (fun k => Derive (f k) x) n).
Proof.
  move => Hf.
  apply is_derive_unique, is_derive_sum.
  move => k Hk.
  by apply Derive_correct, Hf.
Qed.

(** Difference of functions *)

Lemma ex_derive_minus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => f x - g x) x.
Proof.
intros f g x (df,Df) (dg,Dg).
exists (df - dg).
now apply derivable_pt_lim_minus.
Qed.
Lemma Derive_minus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  Derive (fun x => f x - g x) x = Derive f x - Derive g x.
Proof.
intros f g x Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_minus ;
  now apply Derive_correct.
Qed.

(** ** Multiplicative operators *)
(** Multiplication of functions *)

Lemma derivable_pt_lim_inv (f : R -> R) (x l : R) :
  is_derive f x l -> f x <> 0
    -> is_derive (fun y => / f y) x (-l/(f x)^2).
Proof.
  move => Hf Hl.
  search_derive.
  apply is_derive_ext with (fun y => 1/f y).
  move => t ; by rewrite /Rdiv Rmult_1_l.
  apply derivable_pt_lim_div.
  apply derivable_pt_lim_const.
  apply Hf.
  apply Hl.
  rewrite /Rsqr ; by field.
Qed.
Lemma ex_derive_inv (f : R -> R) (x : R) :
  ex_derive f x -> f x <> 0
    -> ex_derive (fun y => / f y) x.
Proof.
  case => l Hf Hl.
  exists (-l/(f x)^2).
  by apply derivable_pt_lim_inv.
Qed.
Lemma Derive_inv  (f : R -> R) (x : R) :
  ex_derive f x -> f x <> 0
    -> Derive (fun y => / f y) x = - Derive f x / (f x) ^ 2.
Proof.
  move/Derive_correct => Hf Hl.
  apply is_derive_unique.
  by apply derivable_pt_lim_inv.
Qed.

Lemma ex_derive_scal :
  forall f k x, ex_derive f x ->
  ex_derive (fun x => k * f x) x.
Proof.
intros f k x (df,Df).
exists (k * df).
now apply derivable_pt_lim_scal.
Qed.
Lemma Derive_scal :
  forall f k x,
  Derive (fun x => k * f x) x = k * Derive f x.
Proof.
intros f k x.
unfold Derive, Lim.
have H : (forall x, k * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite k) x)).
  case: (Req_dec k 0) => [-> | Hk].
  case => [l | | ] //= ; rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case: Rle_dec (Rle_refl 0) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case => [l | | ] //= ; rewrite Rmult_0_r.
  case: Rle_dec => //= H.
  case: Rle_lt_or_eq_dec => //=.
  case: Rle_dec => //= H.
  case: Rle_lt_or_eq_dec => //=.
rewrite H.
rewrite -Lim_seq_scal_l.
apply f_equal, Lim_seq_ext => n.
rewrite -Rmult_assoc.
apply (f_equal (fun v => v / _)).
ring.
Qed.
Lemma derivable_pt_lim_scal_r (f : R -> R) (k x l : R) :
  is_derive f x l ->
  is_derive (fun x => f x * k) x (l*k).
Proof.
  move => Hf.
  search_derive.
  apply derivable_pt_lim_mult.
  apply Hf.
  apply derivable_pt_lim_const.
  simpl ; ring.
Qed.
Lemma ex_derive_scal_r (f : R -> R) (k x : R) :
  ex_derive f x ->
  ex_derive (fun x => f x * k) x.
Proof.
  case => l Hf.
  exists (l * k).
  by apply derivable_pt_lim_scal_r.
Qed.
Lemma Derive_scal_r (f : R -> R) (k x : R) :
  Derive (fun x => f x * k) x = Derive f x * k.
Proof.
  rewrite Rmult_comm -Derive_scal.
  apply Derive_ext => t ; by apply Rmult_comm.
Qed.

Lemma ex_derive_mult (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x
    -> ex_derive (fun x => f x * g x) x.
Proof.
  move => [d1 H1] [d2 H2].
  exists (d1 * g x + f x * d2) ; exact: derivable_pt_lim_mult.
Qed.
Lemma Derive_mult (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x
    -> Derive (fun x => f x * g x) x = Derive f x * g x + f x * Derive g x.
Proof.
  move => H1 H2.
  apply is_derive_unique.
  apply derivable_pt_lim_mult ; exact: Derive_correct.
Qed.

Lemma is_derive_pow (f : R -> R) (n : nat) (x : R) (l : R) :
  is_derive f x l -> is_derive (fun x => (f x)^n) x (INR n * l * (f x)^(pred n)).
Proof.
  move => H.
  rewrite (Rmult_comm _ l) Rmult_assoc Rmult_comm.
  apply (derivable_pt_lim_comp f (fun x => x^n)).
  by apply H.
  by apply derivable_pt_lim_pow.
Qed.
Lemma ex_derive_pow (f : R -> R) (n : nat) (x : R) :
  ex_derive f x -> ex_derive (fun x => (f x)^n) x.
Proof.
  case => l H.
  exists (INR n * l * (f x)^(pred n)).
  by apply is_derive_pow.
Qed.
Lemma Derive_pow (f : R -> R) (n : nat) (x : R) :
  ex_derive f x -> Derive (fun x => (f x)^n) x = (INR n * Derive f x * (f x)^(pred n)).
Proof.
  move => H.
  apply is_derive_unique.
  apply is_derive_pow.
  by apply Derive_correct.
Qed.

Lemma ex_derive_div (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x -> g x <> 0
    -> ex_derive (fun y => f y / g y) x.
Proof.
  move => Hf Hg Hl.
  apply ex_derive_mult.
  apply Hf.
  by apply ex_derive_inv.
Qed.
Lemma Derive_div (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x -> g x <> 0
    -> Derive (fun y => f y / g y) x = (Derive f x * g x - f x * Derive g x) / (g x) ^ 2.
Proof.
  move => Hf Hg Hl.
  search_derive.
  apply derivable_pt_lim_div.
  by apply Derive_correct.
  by apply Derive_correct.
  by apply Hl.
  rewrite /Rsqr ; by field.
Qed.

(** Inverse function *)

Lemma derivable_pt_lim_Rinv (x : R) :
  x <> 0
    -> is_derive (fun y => / y) x (-/x^2).
Proof.
  move => Hf.
  search_derive.
  apply derivable_pt_lim_inv.
  apply derivable_pt_lim_id.
  by [].
  simpl ; by field.
Qed.
Lemma ex_derive_Rinv (x : R) :
  x <> 0
    -> ex_derive (fun y => / y) x.
Proof.
  move => Hf.
  exists (-/x^2).
  by apply derivable_pt_lim_Rinv.
Qed.
Lemma Derive_Rinv (x : R) :
  x <> 0
    -> Derive (fun y => / y) x = - / x ^ 2.
Proof.
  move => Hl.
  apply is_derive_unique.
  by apply derivable_pt_lim_Rinv.
Qed.


(** Composition of functions *)

Lemma ex_derive_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x
    -> ex_derive (fun x => f (g x)) x.
Proof.
intros (df,Df) (dg,Dg).
exists (df * dg).
now apply derivable_pt_lim_comp.
Qed.
Lemma Derive_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x
    -> Derive (fun x => f (g x)) x = Derive f (g x) * Derive g x.
Proof.
intros Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_comp ;
  now apply Derive_correct.
Qed.

(** * Mean value theorem *)

Lemma MVT_gen (f : R -> R) (a b : R) :
  let a0 := Rmin a b in
  let b0 := Rmax a b in
  (forall x, a0 < x < b0 -> ex_derive f x)
  -> (forall x, a0 <= x <= b0 -> continuity_pt f x)
  -> exists c, a0 <= c <= b0 /\ f b - f a = Derive f c * (b - a).
Proof.
  move => a0 b0 Hd Hf.
  case: (Req_dec a0 b0) => Hab.
  exists a0 ; split.
  split ; by apply Req_le.
  replace b with a.
  ring.
  move: Hab ; rewrite /a0 /b0 /Rmin /Rmax ; by case: Rle_dec => Hab.
  have pr1 : forall c:R, a0 < c < b0 -> derivable_pt f c.
    move => x Hx ; exists (Derive f x).
    by apply Derive_correct, Hd.
  have pr2 : forall c:R, a0 < c < b0 -> derivable_pt id c.
    move => x Hx ; exists 1.
    by apply derivable_pt_lim_id.
  case: (MVT f id a0 b0 pr1 pr2).
  apply Rnot_le_lt ; contradict Hab ; apply Rle_antisym.
  by apply Rcomplements.Rmin_Rmax.
  by apply Hab.
  by apply Hf.
  move => x Hx ; apply derivable_continuous, derivable_id.
  move => /= c [Hc H].
  exists c ; split.
  split ; by apply Rlt_le, Hc.
  replace (Derive f c) with (derive_pt f c (pr1 c Hc)).
  move: H ; rewrite {1 2}/id /a0 /b0 /Rmin /Rmax ;
  case: Rle_dec => Hab0 H.
  rewrite Rmult_comm H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
  ring.
  replace (derive_pt f c (pr1 c Hc) * (b - a))
    with (-((a - b) * derive_pt f c (pr1 c Hc)))
    by ring.
  rewrite H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
  ring.
  case: (pr1 c Hc) => /= l Hl.
  apply sym_eq, is_derive_unique, Hl.
Qed.

Lemma incr_function (f : R -> R) (a b : Rbar) :
  (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> ex_derive f x)
  -> ((forall (x : R), Rbar_lt a x -> Rbar_lt x b -> Derive f x > 0)
    -> (forall (x y : R), Rbar_lt a x -> x < y -> Rbar_lt y b -> f x < f y)).
Proof.
  move => Df Hf x y Hax Hxy Hyb.
  apply Rminus_lt_0.
  case: (MVT_gen f x y) => [z Hz | z Hz | c [Hc ->]].
  apply Df.
  apply Rbar_lt_le_trans with (2 := proj2 (Rbar_finite_le _ _) (Rlt_le _ _ (proj1 Hz))).
  rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rbar_le_lt_trans with (1 := proj2 (Rbar_finite_le _ _) (Rlt_le _ _ (proj2 Hz))).
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply derivable_continuous_pt.
  exists (Derive f z) ; apply Derive_correct.
  apply Df.
  apply Rbar_lt_le_trans with (2 := proj2 (Rbar_finite_le _ _) (proj1 Hz)).
  rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rbar_le_lt_trans with (1 := proj2 (Rbar_finite_le _ _) (proj2 Hz)).
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rmult_lt_0_compat.
  apply Hf.
  apply Rbar_lt_le_trans with (2 := proj2 (Rbar_finite_le _ _) (proj1 Hc)).
  rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rbar_le_lt_trans with (1 := proj2 (Rbar_finite_le _ _) (proj2 Hc)).
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  by apply -> Rminus_lt_0.
Qed.

Lemma incr_function_le (f : R -> R) (a b : Rbar) :
  (forall (x : R), Rbar_le a x -> Rbar_le x b -> (ex_derive f) x)
  -> ((forall (x : R), Rbar_le a x -> Rbar_le x b -> Derive f x > 0)
    -> (forall (x y : R), Rbar_le a x -> x < y -> Rbar_le y b -> f x < f y)).
Proof.
  move => Df Hf x y Hax Hxy Hyb.
  apply Rminus_lt_0.
  case: (MVT_gen f x y) => [z Hz | z Hz | c [Hc ->]].
  apply Df.
  apply Rbar_le_trans with (2 := proj2 (Rbar_finite_le _ _) (Rlt_le _ _ (proj1 Hz))).
  rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rbar_le_trans with (1 := proj2 (Rbar_finite_le _ _) (Rlt_le _ _ (proj2 Hz))).
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply derivable_continuous_pt.
  exists (Derive f z) ; apply Derive_correct.
  apply Df.
  apply Rbar_le_trans with (2 := proj2 (Rbar_finite_le _ _) (proj1 Hz)).
  rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rbar_le_trans with (1 := proj2 (Rbar_finite_le _ _) (proj2 Hz)).
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rmult_lt_0_compat.
  apply Hf.
  apply Rbar_le_trans with (2 := proj2 (Rbar_finite_le _ _) (proj1 Hc)).
  rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  apply Rbar_le_trans with (1 := proj2 (Rbar_finite_le _ _) (proj2 Hc)).
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hxy) => //.
  by apply -> Rminus_lt_0.
Qed.

Lemma MVT_cor4:
  forall (f : R -> R) a eps,
  (forall c, Rabs (c - a) <= eps -> ex_derive f c) ->
  forall b, (Rabs (b - a) <= eps) ->
  exists c, f b - f a = Derive f c * (b - a) /\ (Rabs (c - a) <= Rabs (b - a)).
Proof.
intros f a eps Hf' b.
unfold Rabs at 1 3.
case Rcase_abs; intros H1 H2.
destruct (MVT_cor2 f (Derive f) b a).
rewrite -(Rplus_0_l a).
now apply Rlt_minus_l.
intros c Hc.
apply Derive_correct.
apply Hf'.
rewrite Rabs_left1.
apply Rle_trans with (2:=H2).
apply Ropp_le_contravar.
now apply Rplus_le_compat_r.
apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
rewrite -RIneq.Ropp_minus_distr (proj1 H).
ring.
rewrite Rabs_left.
apply Ropp_le_contravar.
left; now apply Rplus_lt_compat_r.
apply Rplus_lt_reg_r with a.
now ring_simplify.
destruct H1.
destruct (MVT_cor2 f (Derive f) a b).
apply Rplus_lt_reg_r with (-a).
ring_simplify.
now rewrite Rplus_comm.
intros c Hc.
apply Derive_correct.
apply Hf'.
rewrite Rabs_right.
apply Rle_trans with (2:=H2).
now apply Rplus_le_compat_r.
apply Rle_ge; apply Rplus_le_reg_r with a.
now ring_simplify.
exists x; split.
exact (proj1 H0).
rewrite Rabs_right.
left; now apply Rplus_lt_compat_r.
apply Rle_ge; apply Rplus_le_reg_r with a.
left; now ring_simplify.
exists a.
replace b with a.
split;[ring|idtac].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rle_refl.
apply Rplus_eq_reg_l with (-a).
ring_simplify.
rewrite - H; ring.
Qed.

Lemma bounded_variation :
  forall h D x y,
  (forall t, Rabs (t - x) <= Rabs (y - x) -> ex_derive h t /\ (Rabs (Derive h t) <= D)) ->
  Rabs (h y - h x) <= D * Rabs (y - x).
Proof.
intros h D x y H.
destruct (MVT_cor4 h x (Rabs (y - x))) with (b := y) as [t Ht].
intros c Hc.
specialize (H c Hc).
apply H.
apply Rle_refl.
rewrite (proj1 Ht).
rewrite Rabs_mult.
apply Rmult_le_compat_r.
apply Rabs_pos.
now apply H.
Qed.

(** * Newton integration *)

Lemma fn_eq_Derive_eq: forall f g a b,
  continuity_pt f a -> continuity_pt f b ->
  continuity_pt g a -> continuity_pt g b ->
  (forall x, a < x < b -> ex_derive f x) ->
  (forall x, a < x < b -> ex_derive g x) ->
  (forall x, a < x < b -> Derive f x = Derive g x) ->
  exists C, forall x, a <= x <= b -> f x = g x + C.
Proof.
intros f g a b Cfa Cfb Cga Cgb Df Dg Hfg.
pose (h := fun x => f x - g x).
assert  (pr : forall x : R, a < x < b -> derivable_pt h x).
intros x Hx.
apply derivable_pt_minus.
eexists; apply Derive_correct, Df, Hx.
eexists; apply Derive_correct, Dg, Hx.
assert (constant_D_eq h (fun x : R => a <= x <= b) (h a)).
apply null_derivative_loc with (pr:=pr).
intros x Hx.
case (proj1 Hx).
case (proj2 Hx).
intros Y1 Y2.
apply derivable_continuous_pt.
apply pr; now split.
intros Y1 _; rewrite Y1.
apply continuity_pt_minus.
apply Cfb.
apply Cgb.
intros Y1; rewrite <- Y1.
apply continuity_pt_minus.
apply Cfa.
apply Cga.
intros x P.
apply trans_eq with (Derive h x).
apply sym_eq, is_derive_unique.
now destruct (pr x P).
rewrite Derive_minus.
rewrite (Hfg _ P).
ring.
apply Df; split; apply P.
apply Dg; split; apply P.
unfold constant_D_eq in H.
exists (h a).
intros x Hx.
rewrite <- (H _ Hx).
unfold h; ring.
Qed.

(** * C1 extension *)

Lemma extension_cont (f g : R -> R) (a : R) :
  let h := fun x => match Rle_dec x a with
    | left _ => f x
    | right _ => g x
  end in
  continuity_pt f a -> continuity_pt g a
  -> f a = g a
  -> continuity_pt h a.
Proof.
  simpl => Cf Cg Heq e He.
  case: (Cf e He) => {Cf} /= df [Hdf Cf].
  case: (Cg e He) => {Cg} /= dg [Hdg Cg].
  exists (Rmin df dg) ; split.
  by apply Rmin_case.
  move => x Hx.
  case: (Rle_dec a a) (Rle_refl a) => //= _ _.
  case: Rle_dec => Hxa.
  apply Cf ; intuition.
  apply Rlt_le_trans with (1 := H0), Rmin_l.
  rewrite Heq.
  apply Cg ; intuition.
  apply Rlt_le_trans with (1 := H0), Rmin_r.
Qed.
Lemma extension_is_derive (f g : R -> R) (a l : R) :
  let h := fun x => match Rle_dec x a with
    | left _ => f x
    | right _ => g x
  end in
  is_derive f a l -> is_derive g a l
  -> f a = g a
  -> is_derive h a l.
Proof.
  simpl => Cf Cg Heq e He.
  case: (Cf e He) => {Cf} /= df Cf.
  case: (Cg e He) => {Cg} /= dg Cg.
  have Hd : 0 < Rmin df dg.
    case: (df) ; case: (dg) ; intros ; by apply Rmin_case.
  exists (mkposreal _ Hd) => /= h Hh0 Hh.
  case: (Rle_dec a a) (Rle_refl a) => //= _ _.
  case: Rle_dec => Hxa.
  apply Cf ; intuition.
  apply Rlt_le_trans with (1 := Hh), Rmin_l.
  rewrite Heq.
  apply Cg ; intuition.
  apply Rlt_le_trans with (1 := Hh), Rmin_r.
Qed.

Definition extension_C1 (f : R -> R) (a b : Rbar) (x : R) : R :=
  match Rbar_le_dec a x with
    | left _ => match Rbar_le_dec x b with
        | left _ => f x
        | right _ => f (real b) + (x - real b) * Derive f (real b)
      end
    | right _ => f (real a) + (x - real a) * Derive f (real a)
  end.

Lemma extension_C1_ext (f : R -> R) (a b : Rbar) :
  forall (x : R), Rbar_le a x -> Rbar_le x b -> (extension_C1 f a b) x = f x.
Proof.
  move => x Hax Hxb.
  rewrite /extension_C1.
  case: Rbar_le_dec => // _.
  case: Rbar_le_dec => // _.
Qed.

Lemma extension_C1_is_derive (f : R -> R) (a b : Rbar) (x l : R) :
  Rbar_le a x -> Rbar_le x b -> is_derive f x l
  -> is_derive (extension_C1 f a b) x l.
Proof.
  case => Hax ; case => Hxb Hf.
(* a < x < b *)
  move: Hf ; apply is_derive_ext_loc.
  apply (locally_interval _ x a b) => // y Hay Hyb.
  rewrite extension_C1_ext // ; by left.
(* a < x = b *)
  case: b Hxb Hax Hf => [b | | ] //= Hxb Hax Hf.
  apply Rbar_finite_eq in Hxb ; rewrite Hxb in Hax Hf |- * => {x Hxb}.
  apply is_derive_ext_loc with (fun x : R =>
     match Rle_dec x b with
      | left _ => f x
      | right _ =>  f (real b) + (x - real b) * Derive f (real b)
    end).
  case: (Rbar_lt_locally a p_infty b) => // d Hd.
  exists d => y Hy ; case: Rle_dec => Htb ;
  rewrite /extension_C1 ; repeat case: Rbar_le_dec => // ; intros.
  by apply Rbar_finite_le in Htb.
  contradict b0 ; apply Rbar_lt_le ; by apply Hd.
  by apply Rbar_finite_le in a0.
  contradict b0 ; apply Rbar_lt_le ; by apply Hd.
  apply extension_is_derive => //.
  simpl ; search_derive.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal_r.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  rewrite (is_derive_unique _ _ _ Hf) ; ring.
  simpl ; ring.
(* a = x < b *)
  case: a Hxb Hax Hf => [a | | ] Hxb //= Hax Hf.
  apply Rbar_finite_eq in Hax ; rewrite -Hax in Hxb Hf |- * => {x Hax}.
  apply is_derive_ext_loc with (fun x : R =>
     match Rle_dec x a with
      | left _ => f (real a) + (x - real a) * Derive f (real a)
      | right _ => f x
    end).
  case: (Rbar_lt_locally m_infty b a) => // d Hd.
  exists d => y Hy ; case: Rle_dec => Hat ;
  rewrite /extension_C1 ; case: Rbar_le_dec => // ; intros.
  apply Rbar_finite_le in a0.
  rewrite (Rle_antisym y a) => //=.
  apply Rbar_lt_le in Hxb ; case: Rbar_le_dec => //= _ ; ring.
  case: Rbar_le_dec => // Htb.
  contradict Htb ; apply Rbar_lt_le ; by apply Hd.
  contradict b0 ; by apply Rbar_lt_le, Rnot_le_lt.
  apply extension_is_derive => //.
  simpl ; search_derive.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal_r.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  rewrite (is_derive_unique _ _ _ Hf) ; ring.
  simpl ; ring.
(* a = x = b *)
  case: a Hax => [a | | ] //= -> {a}.
  case: b Hxb => [b | | ] //= <- {b}.
  apply is_derive_ext with (fun y => f (real x) + (y - real x) * Derive f (real x)).
  move => t ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  simpl ; rewrite (Rle_antisym t x) ; try by apply Rbar_finite_le.
  ring.
  simpl ; search_derive.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal_r.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  rewrite (is_derive_unique _ _ _ Hf) ; ring.
Qed.
Lemma extension_C1_is_derive_a (f : R -> R) (a : R) (b : Rbar) (x : R) :
  Rbar_le a b -> x <= a -> (ex_derive f a) ->
  is_derive (extension_C1 f a b) x (Derive f a).
Proof.
  move => Hab ; case => [Hax | -> {x}] Hf ;
  apply Derive_correct in Hf.
  apply is_derive_ext_loc with (fun x => f (real a) + (x - real a) * Derive f (real a)).
  case: (Rbar_lt_locally m_infty a x) => // d Hd.
  exists d => y Hy ; rewrite /extension_C1.
  specialize (Hd _ Hy).
  case: Hd => _ Hd.
  case: Rbar_le_dec => //= ; intros.
  contradict a0 ; by apply Rbar_lt_not_le.
  search_derive.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal_r.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  simpl ; ring.

  apply extension_C1_is_derive => //.
  by right.
Qed.
Lemma extension_C1_is_derive_b (f : R -> R) (a : Rbar) (b x : R) :
  Rbar_le a b -> b <= x -> (ex_derive f b) ->
  is_derive (extension_C1 f a b) x (Derive f b).
Proof.
  move => Hab ; case => [Hxb | <- {x}] Hf ;
  apply Derive_correct in Hf.
  apply is_derive_ext_loc with (fun x => f (real b) + (x - real b) * Derive f (real b)).
  case: (Rbar_lt_locally b p_infty x) => // d Hd.
  exists d => y Hy ; rewrite /extension_C1.
  specialize (Hd _ Hy).
  case: Hd => Hd _.
  repeat case: Rbar_le_dec => //= ; intros.
  contradict a0 ; by apply Rbar_lt_not_le.
  contradict Hab ; apply Rbar_lt_not_le, Rbar_lt_trans with y => // ;
  by apply Rbar_not_le_lt.
  search_derive.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_scal_r.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  simpl ; ring.

  apply extension_C1_is_derive => //.
  by right.
Qed.

Lemma extension_C1_ex_derive (f : R -> R) (a b : Rbar) :
  Rbar_le a b ->
  (forall (x : R), Rbar_le a x -> Rbar_le x b -> ex_derive f x)
  -> forall (x : R), ex_derive (extension_C1 f a b) x.
Proof.
  case => Hab Hf x.
  case: (Rbar_le_dec a x) => Hax.
  case: (Rbar_le_dec x b) => Hxb.
  case: (Hf x Hax Hxb) => {Hf} l Hf.
  exists l ; by apply extension_C1_is_derive.
  case: b Hab Hxb Hf => [b | | ] //= Hab Hxb Hf.
  exists (Derive f b).
  apply extension_C1_is_derive_b => //.
  by apply Rbar_lt_le.
  by apply Rlt_le, (Rbar_not_le_lt x b).
  apply Hf => //.
  by left.
  by right.
  by apply Rbar_not_le_lt in Hxb.
  case: a Hax Hab Hf => [a | | ] // Hax Hab Hf ; case: Hab => //.

  case: a Hab Hax Hf => [a | | ] Hab //= Hax Hf.
  exists (Derive f a).
  apply extension_C1_is_derive_a => //.
  by apply Rbar_lt_le.
  by apply Rbar_finite_le, Rbar_lt_le, Rbar_not_le_lt.
  apply Hf => //.
  by right.
  by left.
  by apply Rbar_not_le_lt in Hax.

  case: a Hab Hf => [a | | ] //= ;
  case: b => [b | | ] //= Hab Hf.
  rewrite -Hab in Hf |- * => {b Hab}.
  apply ex_derive_ext with (fun y => f (real a) + (y - real a) * Derive f (real a)).
  move => t ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  simpl ; rewrite (Rle_antisym t a) ; try by apply Rbar_finite_le.
  ring.
  apply ex_derive_plus.
  apply ex_derive_const.
  apply ex_derive_scal_r.
  apply ex_derive_minus.
  apply ex_derive_id.
  apply ex_derive_const.

  apply ex_derive_ext with (fun y => f 0 + (y - 0) * Derive f 0).
  move => t ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  by case: a0.
  apply ex_derive_plus.
  apply ex_derive_const.
  apply ex_derive_scal_r.
  apply ex_derive_minus.
  apply ex_derive_id.
  apply ex_derive_const.

  apply ex_derive_ext with (fun y => f 0 + (y - 0) * Derive f 0).
  move => t ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  by case: a.
  apply ex_derive_plus.
  apply ex_derive_const.
  apply ex_derive_scal_r.
  apply ex_derive_minus.
  apply ex_derive_id.
  apply ex_derive_const.
Qed.
Lemma extension_C1_Derive_cont (f : R -> R) (a b : Rbar) :
  Rbar_le a b
  -> (forall (x : R), Rbar_le a x -> Rbar_le x b -> ex_derive f x /\ continuity_pt (Derive f) x)
  -> forall x, continuity_pt (Derive (extension_C1 f a b)) x.
Proof.
  move => Hab Hf x.
  case: (Rbar_le_lt_dec a x) => Hax.
  case: Hax => Hax.
  case: (Rbar_le_lt_dec x b) => Hxb.
  case: Hxb => Hxb.
(* a < x < b *)
  apply continuity_pt_ext_loc with (Derive f).
  apply (locally_interval _ _ _ _ Hax Hxb) => y Hay Hyb.
  apply sym_eq, is_derive_unique, extension_C1_is_derive ; try by left.
  apply Derive_correct, Hf ; by left.
  apply Hf ; by left.
(* a < x = b *)
  case: b Hxb Hf Hab => [b | | ] // Hxb Hf Hab.
  apply Rbar_finite_eq in Hxb.
  rewrite Hxb in Hax |- * => {x Hxb Hab}.
  apply continuity_pt_ext_loc with (fun x : R =>
     match Rle_dec x b with
      | left _ => Derive f x
      | right _ =>  Derive f b
    end).
  case: (Rbar_lt_locally a p_infty b) => // d Hd.
  exists d => y Hy ; case: Rle_dec => Htb ; apply sym_eq, is_derive_unique.
  apply extension_C1_is_derive.
  left ; by apply Hd.
  by apply Rbar_finite_le.
  apply Derive_correct, Hf.
  left ; by apply Hd.
  by apply Rbar_finite_le.
  apply extension_C1_is_derive_b.
  by left.
  by apply Rlt_le, Rnot_le_lt.
  apply Hf.
  by left.
  by right.
  apply extension_cont.
  apply Hf.
  by left.
  by right.
  by apply continuity_pt_const.
  by [].
(* a <= b < x *)
  case: b Hab Hf Hxb => [b | | ] // Hab Hf Hxb.
  apply continuity_pt_ext_loc with (fun _ => Derive f b).
  apply (locally_interval _ _ b p_infty) => // y Hay Hyb.
  apply sym_eq, is_derive_unique.
  apply extension_C1_is_derive_b => //.
  by apply Rlt_le.
  apply Hf => //.
  by right.
  by apply continuity_pt_const.
  case: a Hax Hab Hf => [a | | ] Hax Hab Hf // ; try by case: Hab.
  apply continuity_pt_ext with (fun _ => Derive f 0).
    move => t.
    rewrite (Derive_ext (extension_C1 f m_infty m_infty)
      (fun y => f (real m_infty) + (y - real m_infty) * Derive f (real m_infty))).
    apply sym_eq ; search_derive.
    apply derivable_pt_lim_plus.
    apply derivable_pt_lim_const.
    apply derivable_pt_lim_scal_r.
    apply derivable_pt_lim_minus.
    apply derivable_pt_lim_id.
    apply derivable_pt_lim_const.
    simpl ; ring.
  move => /= t0 ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  by case: a.
  by apply continuity_pt_const.
(* a = x *)
  case: a Hab Hf Hax => [a | | ] // Hab Hf Hax.
  apply Rbar_finite_eq in Hax ; rewrite -Hax => {x Hax}.
  case: Hab => Hab.
  (* a < b *)
  apply continuity_pt_ext_loc with (fun x : R =>
     match Rle_dec x a with
      | left _ => Derive f a
      | right _ =>  Derive f x
    end).
  case: (Rbar_lt_locally m_infty b a) => // d Hd.
  exists d => y Hy ; case: Rle_dec => Htb ; apply sym_eq, is_derive_unique.
  apply extension_C1_is_derive_a.
  by left.
  by [].
  apply Hf.
  by right.
  by left.
  apply extension_C1_is_derive.
  by apply Rbar_lt_le, Rnot_le_lt.
  by apply Rbar_lt_le, Hd.
  apply Derive_correct, Hf.
  by apply Rbar_lt_le, Rnot_le_lt.
  by apply Rbar_lt_le, Hd.
  apply extension_cont.
  by apply continuity_pt_const.
  apply Hf.
  by right.
  by left.
  by [].
  (* a = b *)
  case: b Hf Hab => [b | | ] // Hf Hab.
  rewrite -Hab in Hf |- * => {b Hab}.
  apply continuity_pt_ext with (fun _ => Derive f a).
  move => t.
  rewrite (Derive_ext (extension_C1 f a a)
      (fun y => f (real a) + (y - real a) * Derive f (real a))).
  apply sym_eq ; search_derive.
    apply derivable_pt_lim_plus.
    apply derivable_pt_lim_const.
    apply derivable_pt_lim_scal_r.
    apply derivable_pt_lim_minus.
    apply derivable_pt_lim_id.
    apply derivable_pt_lim_const.
    simpl ; ring.
  move => /= t0 ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  rewrite (Rle_antisym t0 a) ; try by apply Rbar_finite_le.
  ring.
  by apply continuity_pt_const.
(* x < a *)
  case: a Hab Hf Hax => [a | | ] // Hab Hf Hax.
  apply continuity_pt_ext_loc with (fun _ => Derive f a).
  apply (locally_interval _ _ m_infty a) => // y Hay Hyb.
  apply sym_eq, is_derive_unique.
  apply extension_C1_is_derive_a => //.
  by apply Rlt_le.
  apply Hf => //.
  by right.
  by apply continuity_pt_const.
  case: b Hab Hf => [b | | ] Hab Hf // ; try by case: Hab.
  apply continuity_pt_ext with (fun _ => Derive f 0).
    move => t.
    rewrite (Derive_ext (extension_C1 f p_infty p_infty)
      (fun y => f (real p_infty) + (y - real p_infty) * Derive f (real p_infty))).
    apply sym_eq ; search_derive.
    apply derivable_pt_lim_plus.
    apply derivable_pt_lim_const.
    apply derivable_pt_lim_scal_r.
    apply derivable_pt_lim_minus.
    apply derivable_pt_lim_id.
    apply derivable_pt_lim_const.
    simpl ; ring.
  move => /= t0 ; rewrite /extension_C1.
  repeat case: Rbar_le_dec => // ; intros.
  by case: a0.
  by apply continuity_pt_const.
Qed.

(** Alternate definition of differentiability *)

Definition derivable_pt_lim_aux (f : R -> R) (x l : R) :=
  forall eps : posreal,
  locally x (fun y => Rabs (f y - f x - l * (y-x)) <= eps * Rabs (y-x)).

Lemma equiv_deriv_pt_lim_0 : forall f x l,
  derivable_pt_lim f x l -> derivable_pt_lim_aux f x l.
Proof.
  intros f x l.
  move /derivable_pt_lim_locally => H eps.
  specialize (H eps).
  apply: filter_imp H => y H.
  destruct (Req_dec y x) as [H'|H'].
  rewrite H'.
  ring_simplify (f x - f x - l * (x - x)).
  rewrite /Rminus Rplus_opp_r Rabs_R0 Rmult_0_r.
  apply Rle_refl.
  move: (H H') => {H} H.
  replace (f y - f x - l * (y - x)) with (((f y - f x) / (y - x) - l) * (y - x)).
  rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  now apply Rlt_le.
  field.
  contradict H'.
  now apply Rminus_diag_uniq.
Qed.

Lemma equiv_deriv_pt_lim_1 : forall f x l,
  derivable_pt_lim_aux f x l -> derivable_pt_lim f x l.
Proof.
  intros f x l Df.
  intros eps Heps.
  assert (He : 0 < eps/2).
    apply Rdiv_lt_0_compat.
    apply Heps.
    apply Rlt_R0_R2.
    set (eps2 := mkposreal _ He).
  elim (Df eps2) ; clear Df ; intros delta Df.
  exists delta ; intros.
  assert (x+h+ -x = h).
    ring.
  assert (((f (x + h) - f x) / h - l) = (f(x+h) - f x - l * ((x+h)-x))/((x+h)-x)).
    field.
    rewrite /Rminus H1 ;
    apply H.
    rewrite H2 ; clear H2.
  apply (Rle_lt_trans _ eps2).
  rewrite Rabs_div.
  apply (Rle_div_l _ _ (Rabs (x + h - x))).
  apply Rabs_pos_lt.
  rewrite /Rminus H1 ;
    apply H.
  apply (Df (x+h)).
  simpl.
  rewrite H1 ;
    apply H0.
    rewrite /Rminus H1 ; apply H.
  rewrite (double_var eps).
  rewrite <- (Rplus_0_r eps2).
  unfold eps2 ; simpl.
  apply Rplus_lt_compat_l.
  apply He.
Qed.

(** * Iterated differential *)

(** ** Definition *)

Fixpoint Derive_n (f : R -> R) (n : nat) x :=
  match n with
    | O => f x
    | S n => Derive (Derive_n f n) x
  end.

Definition ex_derive_n f n x :=
  match n with
  | O => True
  | S n => ex_derive (Derive_n f n) x
  end.

Definition is_derive_n f n x l :=
  match n with
  | O => f x = l
  | S n => is_derive (Derive_n f n) x l
  end.

Lemma is_derive_n_unique f n x l :
  is_derive_n f n x l -> Derive_n f n x = l.
Proof.
  case n.
  easy.
  simpl; intros n0 H.
  now apply is_derive_unique.
Qed.
Lemma Derive_n_correct f n x :
  ex_derive_n f n x -> is_derive_n f n x (Derive_n f n x).
Proof.
  case: n => /= [ | n] Hf.
  by [].
  by apply Derive_correct.
Qed.

(** Extensionality *)

Lemma Derive_n_ext_loc :
  forall f g n x,
  locally x (fun t => f t = g t) ->
  Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
pattern x ; apply locally_singleton.
induction n.
exact Heq.
apply (locally_open _ _) in IHn.
apply: filter_imp IHn.
intros t H.
now apply Derive_ext_loc.
Qed.
Lemma ex_derive_n_ext_loc :
  forall f g n x,
  locally x (fun t => f t = g t) ->
  ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
case: n => /= [ | n].
by [].
apply ex_derive_ext_loc.
apply (locally_open _ _) in Heq.
apply: filter_imp Heq.
by apply Derive_n_ext_loc.
Qed.
Lemma is_derive_n_ext_loc :
  forall f g n x l,
  locally x (fun t => f t = g t) ->
  is_derive_n f n x l -> is_derive_n g n x l.
Proof.
  intros f g n x l Heq.
  case: n => /= [ | n].
  move => <- ; apply sym_eq ;
  pattern x ; exact: locally_singleton.
  apply is_derive_ext_loc.
  apply (locally_open _ _) in Heq.
  apply: filter_imp Heq.
  by apply Derive_n_ext_loc.
Qed.

Lemma Derive_n_ext :
  forall f g n x,
  (forall t, f t = g t) ->
  Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
apply Derive_n_ext_loc.
exact: filter_forall.
Qed.
Lemma ex_derive_n_ext :
  forall f g n x,
  (forall t, f t = g t) ->
  ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
apply ex_derive_n_ext_loc.
exact: filter_forall.
Qed.
Lemma is_derive_n_ext :
  forall f g n x l,
  (forall t, f t = g t) ->
  is_derive_n f n x l -> is_derive_n g n x l.
Proof.
intros f g n x l Heq.
apply is_derive_n_ext_loc.
exact: filter_forall.
Qed.

Lemma Derive_n_comp: forall f n m x,
  Derive_n (Derive_n f m) n x = Derive_n f (n+m) x.
Proof.
intros f n m.
induction n.
now simpl.
simpl.
intros x.
now apply Derive_ext.
Qed.

Lemma is_derive_Sn (f : R -> R) (n : nat) (x l : R) :
  locally x (ex_derive f) ->
  (is_derive_n f (S n) x l <-> is_derive_n (Derive f) n x l).
Proof.
  move => Hf.
  case: n => /= [ | n].
  split => H.
  by apply is_derive_unique.
  rewrite -H ; apply Derive_correct.
  exact: locally_singleton.
  split ; apply is_derive_ext_loc ;
  apply: filter_imp Hf => y Hf ;
  rewrite (Derive_n_comp f n 1%nat y) -plus_n_Sm -plus_n_O => //.
Qed.


(** ** Operations *)
(** *** Additive operators *)
(** Opposite *)

Lemma Derive_n_opp (f : R -> R) (n : nat) (x : R) :
  Derive_n (fun x => - f x) n x = - Derive_n f n x.
Proof.
  elim: n x => [ | n IH] x /=.
  by [].
  rewrite -Derive_opp.
  by apply Derive_ext.
Qed.
Lemma ex_derive_n_opp (f : R -> R) (n : nat) (x : R) :
  ex_derive_n f n x -> ex_derive_n (fun x => -f x) n x.
Proof.
  case: n x => [ | n] /= x Hf.
  by [].
  apply ex_derive_opp in Hf.
  move: Hf.
  apply ex_derive_ext.
  move => y ; by rewrite Derive_n_opp.
Qed.
Lemma is_derive_n_opp (f : R -> R) (n : nat) (x l : R) :
  is_derive_n f n x l -> is_derive_n (fun x => -f x) n x (- l).
Proof.
  case: n x => [ | n] /= x Hf.
  by rewrite Hf.
  apply derivable_pt_lim_opp in Hf.
  move: Hf.
  apply is_derive_ext.
  move => y ; by rewrite Derive_n_opp.
Qed.

(** Addition of functions *)

Lemma Derive_n_plus (f g : R -> R) (n : nat) (x : R) :
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) ->
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) ->
  Derive_n (fun x => f x + g x) n x = Derive_n f n x + Derive_n g n x.
Proof.
  elim: n x => /= [ | n IH] x [rf Hf] [rg Hg].
  by [].
  rewrite -Derive_plus.
  apply Derive_ext_loc.
  set r := (mkposreal _ (Rmin_stable_in_posreal rf rg)) ;
  exists r => y Hy.
  simpl in Hy.
  apply Rabs_lt_between' in Hy.
  case: Hy ; move/Rlt_Rminus => Hy1 ; move/Rlt_Rminus => Hy2.
  set r0 := mkposreal _ (Rmin_pos _ _ Hy1 Hy2).
  apply IH ;
  exists r0 => z Hz k Hk.
  apply Hf.
  simpl in Hz.
  apply Rabs_lt_between' in Hz.
  rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l (Rplus_min_distr_l y) in Hz.
  case: Hz ; move => Hz1 Hz2.
  apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1 ; ring_simplify in Hz1.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2 ; ring_simplify in Hz2.
  have Hz := (conj Hz1 Hz2) => {Hz1 Hz2}.
  apply Rabs_lt_between' in Hz.
  apply Rlt_le_trans with (1 := Hz) => /= ; by apply Rmin_l.
  by apply le_trans with (1 := Hk), le_n_Sn.
  apply Hg.
  simpl in Hz.
  apply Rabs_lt_between' in Hz.
  rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l (Rplus_min_distr_l y) in Hz.
  case: Hz ; move => Hz1 Hz2.
  apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1 ; ring_simplify in Hz1.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2 ; ring_simplify in Hz2.
  have Hz := (conj Hz1 Hz2) => {Hz1 Hz2}.
  apply Rabs_lt_between' in Hz.
  apply Rlt_le_trans with (1 := Hz) => /= ; by apply Rmin_r.
  by apply le_trans with (1 := Hk), le_n_Sn.
  apply Hf with (k := (S n)).
  rewrite distance_refl.
  apply cond_pos.
  by apply le_refl.
  apply Hg with (k := S n).
  rewrite distance_refl.
  apply cond_pos.
  by apply le_refl.
Qed.
Lemma ex_derive_n_plus (f g : R -> R) (n : nat) (x : R) :
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) ->
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) ->
  ex_derive_n (fun x => f x + g x) n x.
Proof.
  case: n x => /= [ | n] x Hf Hg.
  by [].
  apply ex_derive_ext_loc with (fun y => Derive_n f n y + Derive_n g n y).
  apply (locally_open _ _) in Hf.
  apply (locally_open _ _) in Hg.
  generalize (filter_and _ _ Hf Hg).
  apply: filter_imp => {Hf Hg} y [Hf Hg].
  apply sym_eq, Derive_n_plus.
  apply: filter_imp Hf ; by intuition.
  apply: filter_imp Hg ; by intuition.
  apply ex_derive_plus.
  apply: locally_singleton ; apply: filter_imp Hf => y Hy.
  by apply (Hy (S n)).
  apply: locally_singleton ; apply: filter_imp Hg => y Hy.
  by apply (Hy (S n)).
Qed.
Lemma is_derive_n_plus (f g : R -> R) (n : nat) (x lf lg : R) :
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) ->
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) ->
  is_derive_n f n x lf -> is_derive_n g n x lg ->
  is_derive_n (fun x => f x + g x) n x (lf + lg).
Proof.
  case: n x lf lg => /= [ | n] x lf lg Hfn Hgn Hf Hg.
  by rewrite Hf Hg.
  apply is_derive_ext_loc with (fun y => Derive_n f n y + Derive_n g n y).
  apply (locally_open _ _) in Hfn.
  apply (locally_open _ _) in Hgn.
  generalize (filter_and _ _ Hfn Hgn).
  apply: filter_imp => {Hfn Hgn} y [Hfn Hgn].
  apply sym_eq, Derive_n_plus.
  apply: filter_imp Hfn ; by intuition.
  apply: filter_imp Hgn ; by intuition.
  by apply derivable_pt_lim_plus.
Qed.

(** Subtraction of functions *)

Lemma Derive_n_minus (f g : R -> R) (n : nat) (x : R) :
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) ->
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) ->
  Derive_n (fun x => f x - g x) n x = Derive_n f n x - Derive_n g n x.
Proof.
  move => Hf Hg.
  rewrite Derive_n_plus.
  by rewrite Derive_n_opp.
  by [].
  move: Hg ; apply filter_imp => y Hg k Hk.
  apply ex_derive_n_opp ; by apply Hg.
Qed.
Lemma ex_derive_n_minus (f g : R -> R) (n : nat) (x : R) :
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) ->
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) ->
  ex_derive_n (fun x => f x - g x) n x.
Proof.
  move => Hf Hg.
  apply ex_derive_n_plus.
  by [].
  move: Hg ; apply filter_imp => y Hg k Hk.
  apply ex_derive_n_opp ; by apply Hg.
Qed.
Lemma is_derive_n_minus (f g : R -> R) (n : nat) (x lf lg : R) :
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) ->
  locally x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) ->
  is_derive_n f n x lf -> is_derive_n g n x lg ->
  is_derive_n (fun x => f x - g x) n x (lf - lg).
Proof.
  move => Hf Hg Df Dg.
  apply is_derive_n_plus.
  by [].
  move: Hg ; apply filter_imp => y Hg k Hk.
  apply ex_derive_n_opp ; by apply Hg.
  by [].
  by apply is_derive_n_opp.
Qed.

(** *** Multiplicative operators *)

(** Scalar multiplication *)

Lemma Derive_n_scal_l (f : R -> R) (n : nat) (a x : R) :
  Derive_n (fun y => a * f y) n x = a * Derive_n f n x.
Proof.
  elim: n x => /= [ | n IH] x.
  by [].
  rewrite -Derive_scal.
  by apply Derive_ext.
Qed.
Lemma ex_derive_n_scal_l (f : R -> R) (n : nat) (a x : R) :
  ex_derive_n f n x -> ex_derive_n (fun y => a * f y) n x.
Proof.
  case: n x => /= [ | n] x Hf.
  by [].
  apply ex_derive_ext with (fun y => a * Derive_n f n y).
  move => t ; by rewrite Derive_n_scal_l.
  by apply ex_derive_scal.
Qed.
Lemma is_derive_n_scal_l (f : R -> R) (n : nat) (a x l : R) :
  is_derive_n f n x l -> is_derive_n (fun y => a * f y) n x (a * l).
Proof.
  case: n x => /= [ | n] x Hf.
  by rewrite Hf.
  apply is_derive_ext with (fun y => a * Derive_n f n y).
  move => t ; by rewrite Derive_n_scal_l.
  by apply derivable_pt_lim_scal.
Qed.

Lemma Derive_n_scal_r (f : R -> R) (n : nat) (a x : R) :
  Derive_n (fun y => f y * a) n x = Derive_n f n x * a.
Proof.
  rewrite Rmult_comm -Derive_n_scal_l.
  apply Derive_n_ext => y ; ring.
Qed.
Lemma ex_derive_n_scal_r (f : R -> R) (n : nat) (a x : R) :
  ex_derive_n f n x -> ex_derive_n (fun y => f y * a) n x.
Proof.
  move/(ex_derive_n_scal_l _ _ a).
  apply ex_derive_n_ext => y ; ring.
Qed.
Lemma is_derive_n_scal_r (f : R -> R) (n : nat) (a x l : R) :
  is_derive_n f n x l -> is_derive_n (fun y => f y * a) n x (l * a).
Proof.
  move/(is_derive_n_scal_l _ _ a).
  rewrite Rmult_comm.
  apply is_derive_n_ext => y ; ring.
Qed.

(** *** Composition *)

(** Composition with linear functions *)

Lemma Derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) :
  locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) ->
  Derive_n (fun y => f (a * y)) n x  = (a ^ n * Derive_n f n (a * x)).
Proof.
  case: (Req_dec a 0) => [ -> _ | Ha] /=.
  rewrite Rmult_0_l.
  elim: n x => [ | n IH] x /= ; rewrite ?Rmult_0_l.
  ring.
  rewrite (Derive_ext _ _ _ IH).
  by apply Derive_const.

  move => Hf.
  apply (locally_singleton _ (fun x => Derive_n (fun y : R => f (a * y)) n x = a ^ n * Derive_n f n (a * x))).
  elim: n Hf => [ | n IH] Hf.
  apply: filter_forall => /= y ; ring.

  case: IH => [ | r IH].
  case: Hf => r0 Hf.
  exists r0 => y Hy k Hk ; by intuition.
  case: Hf => r0 Hf.
  have Hr1 : 0 < Rmin (r0 / (Rabs a)) r.
    apply Rmin_case.
    apply Rdiv_lt_0_compat.
    by apply r0.
    by apply Rabs_pos_lt.
    by apply r.
  set r1 := mkposreal _ Hr1.
  exists r1 => y Hy /=.
  rewrite (Derive_ext_loc _ (fun y => a ^ n * Derive_n f n (a * y))).
  rewrite Derive_scal.
  rewrite (Rmult_comm a (a^n)) Rmult_assoc.
  apply f_equal.
  rewrite Derive_comp.
  rewrite (Derive_ext (Rmult a) (fun x => a * x)) => //.
  rewrite Derive_scal Derive_id ; ring.
  apply Hf with (k := S n).
  rewrite /= -/(Rminus _ _) -Rmult_minus_distr_l Rabs_mult.
  apply Rlt_le_trans with (Rabs a * r1).
  apply Rmult_lt_compat_l.
  by apply Rabs_pos_lt.
  by apply Hy.
  rewrite Rmult_comm ; apply Rle_div_r.
  by apply Rabs_pos_lt.
  rewrite /r1 ; by apply Rmin_l.
  by apply lt_n_Sn.
  apply ex_derive_ext with (2 := ex_derive_scal id a y (ex_derive_id _)).
  by [].
  simpl in Hy.
  apply Rabs_lt_between' in Hy.
  case: Hy => Hy1 Hy2.
  apply Rlt_Rminus in Hy1.
  apply Rlt_Rminus in Hy2.
  have Hy : 0 < Rmin (y - (x - r1)) (x + r1 - y).
  by apply Rmin_case.
  exists (mkposreal (Rmin (y - (x - r1)) (x + r1 - y)) Hy).
  set r2 := Rmin (y - (x - r1)) (x + r1 - y).
  move => t Ht.
  apply IH.
  apply Rabs_lt_between'.
  simpl in Ht.
  apply Rabs_lt_between' in Ht.
  simpl in Ht.
  split.
  apply Rle_lt_trans with (2 := proj1 Ht).
  rewrite /r2 ; apply Rle_trans with (y-(y-(x-r1))).
  ring_simplify ; apply Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /r1 ; apply Rmin_r.
  apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_l.
  apply Rlt_le_trans with (1 := proj2 Ht).
  rewrite /r2 ; apply Rle_trans with (y+((x+r1)-y)).
  apply Rplus_le_compat_l, Rmin_r.
  ring_simplify ; apply Rplus_le_compat_l.
  rewrite /r1 ; apply Rmin_r.
Qed.
Lemma ex_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) :
  locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x)
  -> ex_derive_n (fun y => f (a * y)) n x.
Proof.
  case: n f x => /= [ | n] f x Hf.
  by [].

  case: (Req_dec a 0) => Ha.
  rewrite Ha => {a Ha Hf}.
  apply ex_derive_ext with (fun _ => Derive_n (fun y : R => f (0 * y)) n 0).
  elim: n => /= [ | n IH] t.
  by rewrite ?Rmult_0_l.
  rewrite -?(Derive_ext _ _ _ IH).
  by rewrite ?Derive_const.
  by apply ex_derive_const.

  apply ex_derive_ext_loc with (fun x => a^n * Derive_n f n (a * x)).
  case: Hf => r Hf.
  have Hr0 : 0 < r / Rabs a.
    apply Rdiv_lt_0_compat.
    by apply r.
    by apply Rabs_pos_lt.
  exists (mkposreal _ Hr0) => /= y Hy.
  apply eq_sym, Derive_n_comp_scal.
  have : Rabs (a*y - a*x) < r.
    rewrite -Rmult_minus_distr_l Rabs_mult.
    replace (pos r) with (Rabs a * (r / Rabs a))
      by (field ; by apply Rgt_not_eq, Rabs_pos_lt).
    apply Rmult_lt_compat_l.
    by apply Rabs_pos_lt.
    by apply Hy.
    move => {Hy} Hy.
  apply Rabs_lt_between' in Hy ; case: Hy => Hy1 Hy2.
  apply Rlt_Rminus in Hy1.
  apply Rlt_Rminus in Hy2.
  exists (mkposreal _ (Rmin_pos _ _ Hy1 Hy2)) => /= z Hz k Hk.
  apply Rabs_lt_between' in Hz ; case: Hz => Hz1 Hz2.
  rewrite /Rminus -Rmax_opp_Rmin in Hz1.
  rewrite Rplus_min_distr_l in Hz2.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2.
  ring_simplify in Hz2.
  rewrite Rplus_max_distr_l in Hz1.
  apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1.
  ring_simplify in Hz1.
  apply Hf.
  apply Rabs_lt_between' ; by split.
  by intuition.
  apply ex_derive_scal.
  apply ex_derive_comp.
  apply (locally_singleton _ _) in Hf.
  by apply Hf with (k := S n).
  apply ex_derive_ext with (2 := ex_derive_scal id a x (ex_derive_id _)).
  by [].
Qed.
Lemma is_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x l : R) :
  locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x)
  -> is_derive_n f n (a * x) l
  -> is_derive_n (fun y => f (a * y)) n x (a ^ n * l).
Proof.
  case: n => /= [ | n] Hfn Hf.
  by rewrite Rmult_1_l.
  apply is_derive_unique in Hf.
  rewrite -Hf.
  rewrite -(Derive_n_comp_scal f a (S n) x) => //.
  apply Derive_correct.
  by apply (ex_derive_n_comp_scal f a (S n) x).
Qed.

Lemma Derive_n_comp_opp (f : R -> R) (n : nat) (x : R) :
  locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) ->
  Derive_n (fun y => f (- y)) n x  = ((-1) ^ n * Derive_n f n (-x)).
Proof.
  move => Hf.
  rewrite -(Derive_n_ext (fun y : R => f (-1 * y))).
  rewrite (Derive_n_comp_scal f (-1) n x).
  by replace (-1*x) with (-x) by ring.
  by replace (-1*x) with (-x) by ring.
  move => t ; by replace (-1*t) with (-t) by ring.
Qed.
Lemma ex_derive_n_comp_opp (f : R -> R) (n : nat) (x : R) :
  locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) ->
  ex_derive_n (fun y => f (- y)) n x.
Proof.
  move => Hf.
  apply (ex_derive_n_ext (fun y : R => f (-1 * y))).
  move => t ; by ring_simplify (-1*t).
  apply (ex_derive_n_comp_scal f (-1) n x).
  by replace (-1*x) with (-x) by ring.
Qed.
Lemma is_derive_n_comp_opp (f : R -> R) (n : nat) (x l : R) :
  locally (- x) (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) ->
  is_derive_n f n (-x) l ->
  is_derive_n (fun y => f (- y)) n x ((-1)^n * l).
Proof.
  move => Hfn Hf.
  apply (is_derive_n_ext (fun y : R => f (-1 * y))).
  move => t ; by ring_simplify (-1*t).
  apply (is_derive_n_comp_scal f (-1) n x).
  by replace (-1*x) with (-x) by ring.
  by replace (-1*x) with (-x) by ring.
Qed.

Lemma Derive_n_comp_trans (f : R -> R) (n : nat) (x b : R) :
  Derive_n (fun y => f (y + b)) n x  = Derive_n f n (x + b).
Proof.
  elim: n x => [ | n IH] x /=.
  by [].
  rewrite (Derive_ext _ _ _ IH) => {IH}.
  generalize (Derive_n f n) => {f} f.
  apply (f_equal real).
  apply Lim_ext => y.
  replace (x + b + y) with (x + y + b) by ring.
  by [].
Qed.
Lemma ex_derive_n_comp_trans (f : R -> R) (n : nat) (x b : R) :
  ex_derive_n f n (x + b) ->
  ex_derive_n (fun y => f (y + b)) n x.
Proof.
  case: n => [ | n] /= Df.
  by [].
  apply (ex_derive_ext _ _ _ (fun x => sym_eq (Derive_n_comp_trans f n x b))).
  move: (Derive_n f n) Df => {f} f Df.
  apply ex_derive_comp.
  by [].
  apply ex_derive_plus.
  by apply ex_derive_id.
  by apply ex_derive_const.
Qed.
Lemma is_derive_n_comp_trans (f : R -> R) (n : nat) (x b l : R) :
  is_derive_n f n (x + b) l ->
  is_derive_n (fun y => f (y + b)) n x l.
Proof.
  case: n => [ | n] /= Df.
  by [].
  apply (is_derive_ext _ _ _ _ (fun x => sym_eq (Derive_n_comp_trans f n x b))).
  move: (Derive_n f n) Df => {f} f Df.
  search_derive.
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_plus.
  by apply derivable_pt_lim_id.
  by apply derivable_pt_lim_const.
  by apply Df.
  ring.
Qed.

(** * Taylor-Lagrange formula *)

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
