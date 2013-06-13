Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements Locally.
Require Import Compactness.

(** * Definitions *)

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
destruct (Rlt_dec (Rabs (f u v - f x y)) (pos_div_2 eps)) ; [left|right]; assumption.
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
destruct (Rlt_dec (Rabs (f u v - f x c)) (pos_div_2 eps)); [left|right] ; assumption.
Qed.

Lemma uniform_continuity_2d_1d' :
  forall f a b c,
  (forall x, a <= x <= b -> continuity_2d_pt f c x) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c - delta <= y <= c + delta ->
  a <= u <= b -> c - delta <= v <= c + delta ->
  Rabs (u - x) < delta ->
  Rabs (f v u - f y x) < eps.
Proof.
intros f a b c Cf eps.
assert (T:(forall x : R, a <= x <= b -> continuity_2d_pt (fun x0 y : R => f y x0) x c) ).
intros x Hx e.
destruct (Cf x Hx e) as (d,Hd).
exists d.
intros; now apply Hd.
destruct (uniform_continuity_2d_1d (fun x y => f y x) a b c T eps) as (d,Hd).
exists d; intros.
now apply Hd.
Qed.

Lemma continuity_2d_pt_neq_0 (f : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y -> f x y <> 0
  -> locally_2d (fun u v => f u v <> 0) x y.
Proof.
  wlog: f / (f x y > 0) => [Hw Cf Hf' | Hf Cf _].
    case: (Rlt_le_dec 0 (f x y)) => Hf.
    by apply Hw.
    case: Hf => // Hf.
    apply locally_2d_impl with (fun u v => - f u v <> 0).
    apply locally_2d_forall => u v H.
    contradict H ; by rewrite H Ropp_0.
    apply Hw.
    apply Ropp_lt_cancel ; by rewrite Ropp_involutive Ropp_0.
    move => eps ; case: (Cf eps) => {Cf} delta Cf ; exists delta => u v Hu Hv.
    rewrite /Rminus -Ropp_plus_distr Rabs_Ropp.
    by apply Cf.
    contradict Hf' ; by rewrite -(Ropp_involutive (f _ _)) Hf' Ropp_0.
  case: (Cf (mkposreal _ Hf)) => {Cf} /= delta Cf.
  exists delta => u v Hu Hv.
  move: (Cf u v Hu Hv) ; move/Rabs_lt_between' => {Cf} [Cf _].
  ring_simplify in Cf ; by apply Rgt_not_eq.
Qed.

(** * Operations *)

(** ** Extentionality *)

Lemma continuity_pt_ext_loc :
  forall f g x,
  (locally (fun x => f x = g x) x) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf eps Heps.
destruct (Cf eps Heps) as (d,(Hd1,Hd2)).
case: Heq => d0 Heq.
exists (Rmin d d0).
split.
apply Rmin_case.
exact Hd1.
by apply d0.
intros u Hu.
rewrite -2?Heq.
apply Hd2 ; intuition.
apply Rlt_le_trans with (1 := H0), Rmin_l.
rewrite Rminus_eq0 Rabs_R0 ; by apply d0.
apply Rlt_le_trans with (1 := proj2 Hu), Rmin_r.
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

Lemma continuity_2d_pt_ext_loc :
  forall f g x y,
  locally_2d (fun u v => f u v = g u v) x y ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y H1 H2 eps.
specialize (locally_2d_and _ _ _ _ H1 (H2 eps)).
apply locally_2d_impl.
apply locally_2d_forall.
intros u v (H3,H4).
rewrite <- H3.
apply locally_2d_singleton in H1.
rewrite <- H1.
exact H4.
Qed.

(** ** Composition *)

Lemma continuity_1d_2d_pt_comp :
 forall f g x y,
   continuity_pt f (g x y) ->
   continuity_2d_pt g x y ->
   continuity_2d_pt (fun x y => f (g x y)) x y.
intros f g x y cf cg eps.
destruct (cf eps (cond_pos eps)) as [delta [deltapos Pf]].
destruct (cg (mkposreal _ deltapos)) as [gamma Pg].
exists gamma; intros u v cu cv.
destruct (Req_EM_T (g x y) (g u v)) as [eqg | neqg].
 solve[rewrite eqg Rminus_eq0 Rabs_R0; apply cond_pos].
apply (Pf (g u v)).
split;[solve[unfold D_x, no_cond; tauto] | ].
apply (Pg u v); assumption.
Qed.

(** ** Additive *)

Lemma continuity_2d_pt_opp (f : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt (fun u v => - f u v) x y.
Proof.
  move => Hf eps ;
  case: (Hf eps) => {Hf} delta Hf ;
  exists delta => u v Hu Hv.
  rewrite /Rminus -Ropp_plus_distr Rabs_Ropp.
  by apply Hf.
Qed.

Lemma continuity_2d_pt_plus (f g : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt g x y ->
    continuity_2d_pt (fun u v => f u v + g u v) x y.
Proof.
  intros cf cg eps.
  destruct (cf (pos_div_2 eps)) as [delta1 P1].
  destruct (cg (pos_div_2 eps)) as [delta2 P2].
  assert (m0 : 0 < Rmin delta1 delta2).
    destruct delta1 as [d1 d1p]; destruct delta2 as [d2 d2p].
    simpl in d1p, d2p |- *; apply Rmin_glb_lt; assumption.
  exists (mkposreal _ m0); simpl; intros u v ux vy.
  replace (f u v + g u v - (f x y + g x y)) with
    ((f u v - f x y) + (g u v - g x y)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
  apply Rplus_lt_compat;[apply P1 | apply P2].
   solve[apply Rlt_le_trans with (1 := ux); apply Rmin_l].
  solve[apply Rlt_le_trans with (1 := vy); apply Rmin_l].
 solve[apply Rlt_le_trans with (1 := ux); apply Rmin_r].
solve[apply Rlt_le_trans with (1 := vy); apply Rmin_r].
Qed.

Lemma continuity_2d_pt_minus (f g : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt g x y ->
    continuity_2d_pt (fun u v => f u v - g u v) x y.
Proof.
  move => Cf Cg.
  apply continuity_2d_pt_plus.
  exact: Cf.
  by apply continuity_2d_pt_opp.
Qed.

(** ** Multiplicative *)

Lemma continuity_2d_pt_inv (f : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  f x y <> 0 ->
  continuity_2d_pt (fun u v => / f u v) x y.
Proof.
  wlog: f / (f x y > 0) => [Hw Cf Hf | Hf Cf _ eps].
    case: (Rlt_le_dec 0 (f x y)) => Hf'.
    by apply Hw.
    case: Hf' => // Hf'.
    apply continuity_2d_pt_ext_loc with (fun u v => - / - f u v).
    case: (continuity_2d_pt_neq_0 _ _ _ Cf Hf) => delta H.
    exists delta => u v Hu Hv.
    field.
    by apply H.
    apply continuity_2d_pt_opp.
    apply Hw.
    apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
    apply continuity_2d_pt_opp.
    by apply Cf.
    apply Rgt_not_eq, Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
  case: (Cf (pos_div_2 (mkposreal _ Hf))) => /= d0 C0.
  move: (fun u v Hu Hv => proj1 (proj1 (Rabs_lt_between' _ _ _) (C0 u v Hu Hv)))
    => {C0}.
  replace (f x y - f x y / 2) with (f x y / 2) by field ;
  move => C0.
  case: (Cf (mkposreal (eps * (f x y / 2 * f x y)) _)) => [ | {Cf} /= Hd1 d1 Cf].
  apply Rmult_lt_0_compat.
  by apply eps.
  apply Rmult_lt_0_compat.
  apply (is_pos_div_2 (mkposreal _ Hf)).
  by apply Hf.
  have Hd : 0 < Rmin d0 d1.
    apply Rmin_case ; [by apply d0 | by apply d1].
  exists (mkposreal _ Hd) => /= u v Hu Hv.
  replace (/ f u v - / f x y) with (- (f u v - f x y) / (f u v * f x y)).
  rewrite Rabs_div.
  rewrite Rabs_Ropp Rabs_mult.
  apply Rlt_div_l.
  apply Rmult_lt_0_compat.
  apply Rlt_le_trans with (2 := Rle_abs _).
  apply Rlt_trans with (1 := is_pos_div_2 (mkposreal _ Hf)) => /=.
  apply C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
  by apply Rlt_le_trans with (2 := Rle_abs _).
  apply Rlt_le_trans with (eps * (f x y / 2 * f x y)).
  apply Cf ; by apply Rlt_le_trans with (2 := Rmin_r d0 d1).
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  apply Rmult_le_compat.
  by apply Rlt_le, (is_pos_div_2 (mkposreal _ Hf)).
  by apply Rlt_le.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rlt_le, C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
  by apply Rle_abs.
  apply Rgt_not_eq, Rmult_lt_0_compat.
  apply Rlt_trans with (1 := is_pos_div_2 (mkposreal _ Hf)) => /=.
  apply C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
  by [].
  field ; split ; apply Rgt_not_eq.
  by [].
  apply Rlt_trans with (1 := is_pos_div_2 (mkposreal _ Hf)) => /=.
  apply C0 ; by apply Rlt_le_trans with (2 := Rmin_l d0 d1).
Qed.

Lemma continuity_2d_pt_mult (f g : R -> R -> R) (x y : R) :
    continuity_2d_pt f x y ->
    continuity_2d_pt g x y ->
    continuity_2d_pt (fun u v => f u v * g u v) x y.
Proof.
intros cf cg eps.
assert (rabs1_gt0 : forall x, 0 < Rabs x + 1) by
 (intros; apply Rplus_le_lt_0_compat;[apply Rabs_pos | apply Rlt_0_1 ]).
assert (neps0 : forall x, 0 < eps/(4 * (Rabs x + 1))).
 intros; apply Rmult_lt_0_compat;[apply cond_pos | apply Rinv_0_lt_compat].
 apply Rmult_lt_0_compat;[|apply rabs1_gt0] ; apply Rmult_lt_0_compat ; apply Rlt_0_2.
assert (ndf : 0 < eps/(4 * (Rabs (g x y) + 1))) by apply neps0.
assert (ndg : 0 < (Rmin (eps/(4 * (Rabs (f x y) + 1))) ((Rabs (g x y)) + 1))).
 apply Rmin_glb_lt;[apply neps0 |].
 by apply rabs1_gt0.
destruct (cf (mkposreal _ ndf)) as [delta1 P1].
destruct (cg (mkposreal _ ndg)) as [delta2 P2].
assert (m0 : 0 < Rmin delta1 delta2).
 destruct delta1 as [d1 d1p]; destruct delta2 as [d2 d2p].
 simpl in d1p, d2p |- *; apply Rmin_glb_lt; assumption.
exists (mkposreal _ m0); simpl; intros u v ux vy.
replace (f u v * g u v - f x y * g x y) with
   ((f u v - f x y) * g u v + f x y * (g u v - g x y)) by ring.
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
apply Rle_lt_trans with (1 := Rabs_triang _ _).
apply Rplus_lt_compat.
 rewrite Rabs_mult.
 apply Rle_lt_trans with (Rabs (f u v - f x y) * (2 * (Rabs (g x y) + 1))).
  apply Rmult_le_compat_l;[solve[apply Rabs_pos] | ].
  assert (Rabs (g u v - g x y) < Rabs (g x y) + 1).
   apply Rlt_le_trans with (2 := Rmin_r (eps/(4 * (Rabs (f x y) + 1))) _).
   apply P2; apply Rlt_le_trans with (2 := Rmin_r delta1 _); assumption.
  replace (g u v) with ((g u v - g x y) + g x y) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rle_minus_r ; ring_simplify.
  apply Rle_trans with (1 := Rlt_le _ _ H).
  apply Rplus_le_compat_l.
  apply Rle_minus_l ; ring_simplify.
  by apply Rle_0_1.
  replace (pos (pos_div_2 eps)) with
       (eps/ (4 * (Rabs (g x y) + 1)) * (2 * (Rabs (g x y) + 1)))
       by (simpl; field; 
      apply Rgt_not_eq, (Rplus_le_lt_0_compat _ _ (Rabs_pos _)), Rlt_0_1).
 apply Rmult_lt_compat_r;[apply Rmult_lt_0_compat;[apply Rlt_0_2|apply rabs1_gt0]|].
 apply P1; apply Rlt_le_trans with (2 := Rmin_l _ delta2); assumption.
rewrite Rabs_mult.
destruct (Req_EM_T (Rabs (f x y)) 0) as [fxy0 | fxyn0].
 rewrite fxy0 Rmult_0_l; case (pos_div_2 eps); intros; assumption. 
apply Rlt_trans with (Rabs (f x y) * (eps/(4*(Rabs (f x y) + 1)))).
 apply Rmult_lt_compat_l;[assert (t := Rabs_pos (f x y)) ; apply sym_not_eq in fxyn0 ; by case: t | ].
 apply Rlt_le_trans with (2 := Rmin_l _ (Rabs (g x y) + 1)).
 apply P2; apply Rlt_le_trans with (2 := Rmin_r delta1 _); assumption.
replace (pos (pos_div_2 eps)) with
   ((2 * (Rabs (f x y) + 1)) * (eps / (4 * (Rabs (f x y) + 1))));
  [ | destruct eps; simpl; field; apply Rgt_not_eq, rabs1_gt0].
apply Rmult_lt_compat_r;[apply neps0 | ].
assert (t := Rabs_pos (f x y)).
apply Rminus_lt_0 ; ring_simplify.
apply Rplus_le_lt_0_compat.
by apply Rabs_pos.
by apply Rlt_0_2.
Qed.

(** * Particular functions *)

(** Identities *)

Lemma continuity_2d_pt_id1 :
  forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

Lemma continuity_2d_pt_id2 :
  forall x y, continuity_2d_pt (fun u v => v) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

(** Constant functions *)

Lemma continuity_2d_pt_const :
  forall x y c, continuity_2d_pt (fun u v => c) x y.
Proof.
  intros x y c eps; exists eps; rewrite Rminus_eq0 Rabs_R0.
  intros; apply cond_pos.
Qed.
