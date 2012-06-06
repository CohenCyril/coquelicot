Require Import Reals.
Require Import ssreflect.
Require Import List.

Open Scope R_scope.

Section Compactness.

Lemma completeness_any :
  forall P : R -> Prop,
  ( forall x y, x <= y -> P y -> P x ) ->
  forall He : (exists x, P x),
  forall Hb : (bound P),
  forall x, x < projT1 (completeness _ Hb He) ->
  ~ ~ P x.
Proof.
intros P HP He Hb x.
case completeness => y [Hy1 Hy2] /= Hxy Px.
apply Rle_not_lt with (2 := Hxy).
apply Hy2 => t Pt.
apply Rnot_lt_le => Hxt.
apply Px.
apply: HP Pt.
now apply Rlt_le.
Qed.

Variable a b : R.
Variable delta : R -> posreal.

Lemma compactness_list : ~~ exists l, forall x, a <= x <= b -> exists t, In t l /\ Rabs (x - t) < delta t.
Proof.
destruct (Rlt_or_le b a) as [Hab|Hab].
intros H.
apply H.
exists nil.
intros x Hx.
elim (Rlt_irrefl a).
apply Rle_lt_trans with (2 := Hab).
now apply Rle_trans with x.
set (P y := y <= b /\ exists l, forall x, a <= x <= y -> exists t, In t l /\ Rabs (x - t) < delta t).
assert (P1 : exists x, P x).
exists a.
split.
apply Hab.
exists (cons a nil).
intros x Hx.
replace x with a by now apply Rle_antisym.
exists a.
split.
now left.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
assert (P2 : bound P).
exists b => y Hy.
apply Hy.
assert (P3: forall x y, x <= y -> P y -> P x).
intros x y Hxy (Py1,(d,Py2)).
split.
now apply Rle_trans with y.
exists d => z Hz.
apply Py2.
split.
apply Hz.
now apply Rle_trans with (1 := proj2 Hz).
(* *)
destruct (Rle_or_lt a (b - delta b)) as [Ha|Ha].
destruct (Rle_or_lt b (projT1 (completeness _ P2 P1))) as [Hb|Hb].
(* . *)
generalize (completeness_any _ P3 P1 P2 (b - delta b)).
intros H.
refine (_ (H _)).
clear H => HP.
contradict HP.
contradict HP.
destruct HP as (H1,(l,H2)).
exists (b :: l).
simpl.
intros x Hx.
destruct (Rle_or_lt x (b - delta b)) as [Hx'|Hx'].
destruct (H2 x (conj (proj1 Hx) Hx')) as (t,Ht).
exists t.
split.
now right.
apply Ht.
exists b.
split.
now left.
rewrite Rabs_left1.
apply Rplus_lt_reg_r with (x - delta b).
replace (x - delta b + - (x - b)) with (b - delta b) by ring.
now rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
now apply Rle_minus.
apply Rlt_le_trans with (2 := Hb).
rewrite -{3}(Rplus_0_r b) -Ropp_0.
apply Rplus_lt_compat_l.
apply Ropp_lt_contravar.
apply cond_pos.
(* . *)
revert Hb.
generalize (completeness_any _ P3 P1 P2).
case completeness => y [Hy1 Hy2] /= Hy3 Hy4.
elimtype False.
apply (Hy3 (y - delta y)).
rewrite -{3}(Rplus_0_r y) -Ropp_0.
apply Rplus_lt_compat_l.
apply Ropp_lt_contravar.
apply cond_pos.
intros Hy5.
specialize (Hy1 (Rmin b (y + delta y / 2))).
apply (Rlt_not_le (Rmin b (y + delta y / 2)) y).
apply Rmin_case.
exact Hy4.
rewrite -{1}(Rplus_0_r y).
apply Rplus_lt_compat_l.
apply Fourier_util.Rlt_mult_inv_pos.
apply cond_pos.
apply Rlt_R0_R2.
apply Hy1.
split.
apply Rmin_l.
destruct Hy5 as (_,(l,Hl)).
exists (y :: l) => x Hx.
destruct (Rle_or_lt x (y - delta y)) as [Hx'|Hx'].
destruct (Hl x (conj (proj1 Hx) Hx')) as (t,Ht).
exists t.
split.
now right.
apply Ht.
exists y.
split.
now left.
unfold Rabs.
case Rcase_abs => Hxy.
apply Rplus_lt_reg_r with (x - delta y).
replace (x - delta y + - (x - y)) with (y - delta y) by ring.
now rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
apply Rplus_lt_reg_r with y.
ring_simplify (y + (x - y)).
apply Rle_lt_trans with (1 := proj2 Hx).
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply Rplus_lt_compat_l.
rewrite -{1}(Rplus_0_r (delta y / 2)).
rewrite {2}(double_var (delta y)).
apply Rplus_lt_compat_l.
apply Fourier_util.Rlt_mult_inv_pos.
apply cond_pos.
apply Rlt_R0_R2.
(* . *)
intro H.
apply H.
clear H.
exists (b :: nil) => x Hx.
exists b.
split.
now left.
rewrite Rabs_left1.
apply Rplus_lt_reg_r with (x - delta b).
replace (x - delta b + - (x - b)) with (b - delta b) by ring.
rewrite Rplus_assoc Rplus_opp_l Rplus_0_r.
apply Rlt_le_trans with (1 := Ha).
apply Hx.
now apply Rle_minus.
Qed.

Lemma compactness_value :
  exists d : posreal, forall x, a <= x <= b -> ~~ exists t, Rabs (x - t) < delta t /\ d <= delta t.
Proof.
set (P d := d <= 1 /\ forall x, a <= x <= b -> exists t, Rabs (x - t) < delta t /\ d <= delta t).
assert (P1 : exists d, P d).
exists 0.
split.
apply Rle_0_1.
intros x Hx.
exists x.
split.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Rlt_le.
apply cond_pos.
assert (P2 : bound P).
exists 1.
now intros d (Hd,_).
set (d := completeness P P2 P1).
(* *)
assert (P3 : 0 < projT1 d).
revert d.
case completeness.
intros d (Hd1,Hd2).
simpl.
apply Rnot_le_lt.
intros Hd3.
apply compactness_list.
intros (l,Hl).
set (v := fold_right (fun t acc => mkposreal _ (Rmin_stable_in_posreal (delta t) acc)) (mkposreal _ Rlt_0_1) l).
apply (Rlt_not_le _ _ (cond_pos v)).
apply Rle_trans with (2 := Hd3).
apply Hd1.
split.
unfold v.
clear.
induction l.
apply Rle_refl.
simpl.
apply Rle_trans with (2 := IHl).
apply Rmin_r.
intros x Hx.
destruct (Hl x Hx) as (t,(Ht1,Ht2)).
exists t.
split.
apply Ht2.
clear -Ht1.
induction l.
easy.
simpl in Ht1.
destruct Ht1 as [Ht1|Ht1].
simpl.
rewrite Ht1.
apply Rmin_l.
simpl.
eapply Rle_trans with (1 := Rmin_r _ _).
now apply IHl.
(* *)
exists (mkposreal _ (Fourier_util.Rlt_mult_inv_pos _ _ P3 Rlt_R0_R2)).
intros x Hx.
simpl.
refine (_ (completeness_any P _ P1 P2 (projT1 d / 2) _)).
intros HP.
contradict HP.
contradict HP.
destruct HP as (_,HP).
now apply HP.
intros u v Huv (Pv1,Pv2).
split.
now apply Rle_trans with v.
intros z Hz.
destruct (Pv2 z Hz) as (t,Ht).
exists t.
split.
apply Ht.
apply Rle_trans with (1 := Huv).
apply Ht.
fold d.
rewrite -(Rplus_0_r (projT1 d / 2)).
rewrite {2}(double_var (projT1 d)).
apply Rplus_lt_compat_l.
apply Fourier_util.Rlt_mult_inv_pos.
exact P3.
apply Rlt_R0_R2.
Qed.

End Compactness.