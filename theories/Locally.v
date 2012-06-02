Require Import Reals.
Require Import ssreflect.
Require Import Rcomplements.

Open Scope R_scope.

Definition locally (P : R -> Prop) x :=
  exists delta : posreal, forall y, Rabs (y - x) < delta -> P y.

Definition locally_2d (P : R -> R -> Prop) x y :=
  exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.

Lemma locally_align :
  forall (P Q : R -> Prop) x,
  ( forall eps : posreal, (forall v, Rabs (v - x) < eps -> P v) ->
    forall u, Rabs (u - x) < eps -> Q u ) ->
  locally P x -> locally Q x.
Proof.
intros P Q x K (d,H).
exists d => y Hy.
now apply (K d).
Qed.

Lemma locally_2d_align :
  forall (P Q : R -> R -> Prop) x y,
  ( forall eps : posreal, (forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> P u v) ->
    forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> Q u v ) ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y K (d,H).
exists d => u v Hu Hv.
now apply (K d).
Qed.

Lemma locally_impl_strong :
  forall (P Q : R -> Prop) x, locally (fun y => locally P y -> Q y) x ->
  locally P x -> locally Q x.
Proof.
intros P Q x (dpq,Hpq) (dp,Hp).
exists (mkposreal _ (Rmin_stable_in_posreal dp dpq)) => /= y Hy.
apply Hpq.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
set (d := mkposreal _ (Rlt_Rminus _ _ Hy)).
exists d => z Hz.
apply Hp.
replace (z - x) with ((z - y) + (y - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos dp) with (d + (dp - d)) by ring.
apply Rplus_lt_le_compat with (1 := Hz).
simpl.
apply Rplus_le_reg_r with (- (Rabs (y - x))).
ring_simplify.
apply Rge_le.
apply Rge_minus.
apply Rle_ge.
apply Rmin_l.
Qed.

Lemma locally_2d_impl_strong :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => locally_2d P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y (dpq,Hpq) (dp,Hp).
exists (mkposreal _ (Rmin_stable_in_posreal dp dpq)) => /= u v Hu Hv.
apply Hpq.
apply Rlt_le_trans with (1 := Hu).
apply Rmin_r.
apply Rlt_le_trans with (1 := Hv).
apply Rmin_r.
assert (Huv: Rmax (Rabs (u - x)) (Rabs (v - y)) < Rmin dp dpq).
now apply Rmax_case.
set (d := mkposreal _ (Rlt_Rminus _ _ Huv)).
exists d => w z Hw Hz.
apply Hp.
replace (w - x) with ((w - u) + (u - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos dp) with (d + (dp - d)) by ring.
apply Rplus_lt_le_compat with (1 := Hw).
simpl.
apply Rplus_le_reg_r with (- Rmax (Rabs (u - x)) (Rabs (v - y))).
ring_simplify.
apply Rle_trans with R0.
apply Rle_minus.
apply Rmax_l.
apply Rge_le.
apply Rge_minus.
apply Rle_ge.
apply Rmin_l.
replace (z - y) with ((z - v) + (v - y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos dp) with (d + (dp - d)) by ring.
apply Rplus_lt_le_compat with (1 := Hz).
simpl.
apply Rplus_le_reg_r with (- Rmax (Rabs (u - x)) (Rabs (v - y))).
ring_simplify.
apply Rle_trans with R0.
apply Rle_minus.
apply Rmax_r.
apply Rge_le.
apply Rge_minus.
apply Rle_ge.
apply Rmin_l.
Qed.

Lemma locally_singleton :
  forall (P : R -> Prop) x, locally P x -> P x.
Proof.
intros P x (D,H).
apply H.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
Qed.

Lemma locally_2d_singleton :
  forall (P : R -> R -> Prop) x y, locally_2d P x y -> P x y.
Proof.
intros P x y (D,H).
apply H ;
  rewrite /Rminus Rplus_opp_r Rabs_R0 ;
  apply cond_pos.
Qed.

Lemma locally_impl :
  forall (P Q : R -> Prop) x, locally (fun y => P y -> Q y) x ->
  locally P x -> locally Q x.
Proof.
intros P Q x (d,H).
apply locally_impl_strong.
exists d => y Hy Hp.
apply H => //.
now apply locally_singleton.
Qed.

Lemma locally_2d_impl :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y (d,H).
apply locally_2d_impl_strong.
exists d => u v Hu Hv Hp.
apply H => //.
now apply locally_2d_singleton.
Qed.

Lemma locally_forall :
  forall (P : R -> Prop) x, (forall y, P y) -> locally P x.
Proof.
intros P x Hp.
now exists (mkposreal _ Rlt_0_1) => u _.
Qed.

Lemma locally_2d_forall :
  forall (P : R -> R -> Prop) x y, (forall u v, P u v) -> locally_2d P x y.
Proof.
intros P x y Hp.
now exists (mkposreal _ Rlt_0_1) => u v _ _.
Qed.

Lemma locally_and :
  forall (P Q : R -> Prop) x, locally P x -> locally Q x ->
  locally (fun y => P y /\ Q y) x.
Proof.
intros P Q x H.
apply: locally_impl.
apply: locally_impl H.
apply locally_forall.
now split.
Qed.

Lemma locally_2d_and :
  forall (P Q : R -> R -> Prop) x y, locally_2d P x y -> locally_2d Q x y ->
  locally_2d (fun u v => P u v /\ Q u v) x y.
Proof.
intros P Q x y H.
apply: locally_2d_impl.
apply: locally_2d_impl H.
apply locally_2d_forall.
now split.
Qed.

Lemma locally_2d_1d_const_x :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally (fun t => P x t) y.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
rewrite Rminus_eq0 Rabs_R0; apply cond_pos.
exact Hz.
Qed.


Lemma locally_2d_1d_const_y :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally (fun t => P t y) x.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
exact Hz.
rewrite Rminus_eq0 Rabs_R0; apply cond_pos.
Qed.



Lemma locally_2d_1d_strong :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 ->
    locally (fun z => locally_2d P (x + z * (u - x)) (y + z * (v - y))) t) x y.
Proof.
intros P x y.
apply locally_2d_align => eps HP u v Hu Hv t Ht.
assert (Zm: 0 <= Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmax_case ; apply Rabs_pos.
destruct Zm as [Zm|Zm].
(* *)
assert (H1: Rmax (Rabs (u - x)) (Rabs (v - y)) < eps).
now apply Rmax_case.
set (d1 := mkposreal _ (Rlt_Rminus _ _ H1)).
assert (H2: 0 < pos_div_2 d1 / Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_lt_0_compat.
apply cond_pos.
now apply Rinv_0_lt_compat.
set (d2 := mkposreal _ H2).
exists d2 => z Hz.
exists (pos_div_2 d1) => p q Hp Hq.
apply HP.
(* . *)
replace (p - x) with (p - (x + z * (u - x)) + (z - t + t) * (u - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 d1 + (eps - pos_div_2 d1)) by ring.
apply Rplus_lt_le_compat with (1 := Hp).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_l.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* . *)
replace (q - y) with (q - (y + z * (v - y)) + (z - t + t) * (v - y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 d1 + (eps - pos_div_2 d1)) by ring.
apply Rplus_lt_le_compat with (1 := Hq).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_r.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* *)
apply locally_forall => z.
exists eps => p q.
replace (u - x) with 0.
replace (v - y) with 0.
rewrite Rmult_0_r 2!Rplus_0_r.
apply HP.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_r.
apply Rabs_pos.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_l.
apply Rabs_pos.
Qed.

Lemma locally_2d_1d :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 -> locally_2d P (x + t * (u - x)) (y + t * (v - y))) x y.
Proof.
intros P x y H.
apply locally_2d_1d_strong in H.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H t Ht.
specialize (H t Ht).
now apply locally_singleton in H.
Qed.

Lemma continuity_pt_locally :
  forall f x,
  continuity_pt f x <->
  forall eps : posreal, locally (fun u => Rabs (f u - f x) < eps) x.
Proof.
intros f x.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
rewrite /= /R_dist /D_x /no_cond in H2.
exists (mkposreal d H1) => y H.
destruct (Req_dec x y) as [<-|Hxy].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
by apply H2.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d.
split.
apply cond_pos.
intros h [Zh Hh].
exact: H.
Qed.


Require Import Classical.

Lemma is_lub_eps: forall P x (eps:posreal), is_lub P x -> 
   exists y, x-eps <= y <= x /\ P y.
intros P x eps H.
case (classic (exists y : R, x - eps <= y <= x /\ P y)).
easy.
intros H1.
assert (forall y, ~(x - eps <= y <= x /\ P y)).
now apply not_ex_all_not.
absurd (is_upper_bound P (x-eps)).
intros H2.
absurd (x <= x-eps).
apply Rlt_not_le.
apply Rplus_lt_reg_r with (-x+eps).
ring_simplify.
apply cond_pos.
now apply H.
intros z Hz.
case (Rle_or_lt z (x-eps)).
easy.
intros Hz1.
case (Rle_or_lt z x); intros Hz2.
absurd (x - eps <= z <= x /\ P z).
apply H0.
split.
split.
now left.
exact Hz2.
exact Hz.
absurd (x < z).
apply Rle_not_lt.
now apply H.
exact Hz2.
Qed.



Lemma toto: forall a b (P : R -> R -> Prop),
  a <= b ->
  (forall x, a <= x <= b -> exists delta:posreal, forall y, (Rabs (y-x) < delta -> P x y)) ->
    exists delta:posreal, forall x y, a <= x <= b -> Rabs (y-x) < delta -> P x y.
intros a b P H1 H2.
pose (g:=fun r=> a <= r <= b /\  
    exists d:posreal, forall x, a <= x <= r -> forall y, Rabs (y - x) < d-> P x y).
(* *)
assert (g a).
unfold g.
split.
split.
now apply Req_le.
apply H1.
destruct (H2 a) as (da,Hda).
split.
now apply Req_le.
apply H1.
exists da.
intros x Hx.
replace x with a.
apply Hda.
apply Rle_antisym; apply Hx.
(* *)
destruct (completeness g) as (d,Hd).
unfold bound, is_upper_bound.
exists b; intros x; unfold g; intros Hx.
apply Hx.
now exists a.
(* *)
assert (g d).
assert (a <= d <= b).
split.
now apply Hd.
apply Hd.
unfold g; intros z Hz; apply Hz.
split.
exact H0.
destruct (H2 _ H0) as (s,Hs).
destruct (is_lub_eps _ _ s Hd) as (z,Hz).
destruct Hz as (Hz1,(Hz2,(dz,Hz3))).
exists (mkposreal _ (Rmin_stable_in_posreal dz s)).
intros x Hx y; simpl; intros Hy.
case (Rle_or_lt x z).
intros Hx1.
apply Hz3.
split.
apply Hx.
exact Hx1.
apply Rlt_le_trans with (1:=Hy).
apply Rmin_l.
intros Hx1.
apply H1 with s.
apply Hz3.
split.
apply Hx.
exact Hx1.
simpl.
apply Rmin_l.



(Rmin d1 d).



specialize (adherence_P3 g).
unfold adherence,point_adherent.


assert (U:(compact (fun r=> a <= r <= b))) by apply compact_P3.
apply compact_P2 in U.
apply adherence_P2 in U.
is_lub_eps


unfold adherence,point_adherent,included in U.



case (Rle_dec d b).
intros H; case H.

admit.
Bolzano_Weierstrass
admit.




intros H'.
rewrite H' in Hd.
destruct Hd as (Y1,Y2).
unfold is_upper_bound in Y1.


auto with real.





completeness


Lemma toto: forall a b (P:R->R->Prop),
 ( forall d x, (forall y : R, Rabs (y - x) < d -> P x y) ->
    exists delta : posreal,
     forall x0 : R,
       Rabs (x0 - x) < delta -> forall y : R, Rabs (y - x0) < d -> P x0 y) ->
   (forall x, a <= x <= b -> exists delta, forall y, (Rabs (y-x) < delta -> P x y)) ->
  exists delta, forall x y, a <= x <= b -> Rabs (y-x) < delta -> P x y.
intros a b P KK H.
assert (T1:(compact (fun r => a <= r <= b))).
apply compact_P3.
pose (ind := fun delta => 0 < delta).
pose (g:= fun delta x => 0 < delta /\ forall y : R, Rabs (y - x) < delta -> P x y).
assert (T2:(forall x : R, (exists y : R, g x y) -> ind x)).
unfold ind,g.
admit. (* easy.*)
pose (fam:=mkfamily ind g T2).
specialize (T1 fam).
assert (T3:covering_open_set (fun r : R => a <= r <= b) fam).
split.
unfold covering, fam, g.
simpl.
intros x Hx.
destruct (H x Hx) as (d,Hd).
exists d.
admit. (* exact Hd.*)

unfold family_open_set.
intros d; unfold fam,g.
simpl.
unfold open_set.
intros x H1.
unfold neighbourhood, included, disc.
apply KK.
apply H1.

specialize (T1 T3).
destruct T1 as (D, (HD1,HD2)).
unfold family_finite, domain_finite in HD1, HD2.
destruct HD2 as (l,Hl).
exists (MinRlist l).
intros x y Hx Hy.
destruct (HD1 x Hx).
destruct H0 as (Y1,Y2).
unfold fam,g in Y1;simpl in Y1.
apply Y1.
apply Rlt_le_trans with (1:=Hy).
apply MinRlist_P1.
apply Hl.
simpl; split.
unfold ind.
now exists x.
exact Y2.
Qed.


Lemma derivable_pt_lim_locally :
  forall f x l,
  derivable_pt_lim f x l <->
  forall eps : posreal, locally (fun y => y <> x -> Rabs ((f y - f x) / (y - x) - l) < eps) x.
Proof.
intros f x l.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d H].
exists d => y Hy Zy.
specialize (H (y - x) (Rminus_eq_contra _ _ Zy) Hy).
now ring_simplify (x + (y - x)) in H.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d => h Zh Hh.
specialize (H (x + h)).
ring_simplify (x + h - x) in H.
apply H => //.
contradict Zh.
apply Rplus_eq_reg_l with x.
now rewrite Rplus_0_r.
Qed.
