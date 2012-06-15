Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Locally.
Require Import Compactness.

Definition continuity_2d_pt f x y :=
  forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.

Lemma uniform_continuity_2d :
  forall f a b c d,
  (forall x y, a <= x <= b -> c <= y <= d -> continuity_2d_pt f x y) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c <= y <= d ->
  a <= u <= b -> c <= v <= d ->
  Rabs (u - x) < delta -> Rabs (v - y) < delta ->
  Rabs (f u v - f x y) < eps.
Proof.
intros f a b c d Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x y Hx Hy => locally_2d_ex_dec (P x y) x y _ (Cf x y Hx Hy _))).
intros delta1.
set (delta2 x y := match Rle_dec a x, Rle_dec x b, Rle_dec c y, Rle_dec y d with
  left Ha, left Hb, left Hc, left Hd => pos_div_2 (projT1 (delta1 x y (conj Ha Hb) (conj Hc Hd))) |
  _, _, _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_2d a b c d delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux Hvy.
specialize (Hdelta x y Hx Hy).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&q&(Hap,Hpb)&(Hcq,Hqd)&Hxp&Hyq&Hd).
replace (f u v - f x y) with (f u v - f p q + (f p q - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hyq Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
case Rle_dec => Hcq' ; try easy.
case Rle_dec => Hqd' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hyq Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
replace (v - q) with (v - y + (y - q)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hyq).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hvy).
apply: Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_trans with (1 := Hyq).
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
edestruct (Rlt_dec _ _) ; [left|right] ; eassumption.
Qed.

Lemma uniform_continuity_2d_1d :
  forall f a b c,
  (forall x, a <= x <= b -> continuity_2d_pt f x c) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c - delta <= y <= c + delta ->
  a <= u <= b -> c - delta <= v <= c + delta ->
  Rabs (u - x) < delta ->
  Rabs (f u v - f x y) < eps.
Proof.
intros f a b c Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x Hx => locally_2d_ex_dec (P x c) x c _ (Cf x Hx _))).
intros delta1.
set (delta2 x := match Rle_dec a x, Rle_dec x b with
  left Ha, left Hb => pos_div_2 (projT1 (delta1 x (conj Ha Hb))) |
  _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_1d a b delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux.
specialize (Hdelta x Hx).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&(Hap,Hpb)&Hxp&Hd).
replace (f u v - f x y) with (f u v - f p c + (f p c - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
edestruct (Rlt_dec _ _) ; [left|right] ; eassumption.
Qed.

Lemma continuity_pt_ext :
  forall f g x,
  (forall x, f x = g x) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf eps Heps.
destruct (Cf eps Heps) as (d,(Hd1,Hd2)).
exists d.
split.
exact Hd1.
intros u Hu.
rewrite -2!Heq.
now apply Hd2.
Qed.

Lemma continuity_2d_pt_ext :
  forall f g x y,
  (forall x y, f x y = g x y) ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq Cf eps.
apply: locally_2d_impl (Cf eps).
apply locally_2d_forall => u v.
now rewrite 2!Heq.
Qed.

Axiom continuity_2d_pt_ext_loc :
  forall f g x y,
  locally_2d (fun u v => f u v = g u v) x y ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
