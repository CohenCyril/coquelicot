Require Import Reals ssreflect.
Require Import Rcomplements Rbar.
Require Import Continuity Derive Hierarchy.

(** * The set of complex numbers *)

Definition C := (R * R)%type.

Definition RtoC (x : R) : C := (x,0).
Coercion RtoC : R >-> C.

(** ** Constants and usual functions *)

Definition C0 : C := 0.
Definition C1 : C := 1.
Definition Ci : C := (0,1).

(** *** Arithmetic operations *)

Definition Cplus (x y : C) : C := (fst x + fst y, snd x + snd y).
Definition Copp (x : C) : C := (-fst x, -snd x).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition Cinv (x : C) : C := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).

Delimit Scope C_scope with C.
Local Open Scope C_scope.

Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.

(** *** Other usual functions *)

Definition Cmod (x : C) : R := sqrt (fst x ^ 2 + snd x ^ 2).

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Lemma Cmod_0 : Cmod 0 = R0.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l Rplus_0_l.
apply sqrt_0.
Qed.
Lemma Cmod_1 : Cmod 1 = R1.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l Rplus_0_r 2!Rmult_1_l.
apply sqrt_1.
Qed.

Lemma Cmod_opp : forall x, Cmod (-x) = Cmod x.
Proof.
unfold Cmod.
simpl.
intros x.
apply f_equal.
ring.
Qed.

Lemma Cmod_triangle : forall x y, Cmod (x + y) <= Cmod x + Cmod y.
Proof.
  intros x y ; rewrite /Cmod.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr ; simpl ; ring_simplify.
  rewrite /pow ?Rmult_1_r.
  rewrite ?sqrt_sqrt ; ring_simplify.
  replace (-2 * fst x * fst y - 2 * snd x * snd y)%R with (- (2 * (fst x * fst y + snd x * snd y)))%R by ring.
  rewrite Rmult_assoc -sqrt_mult.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  rewrite /Rsqr ?sqrt_sqrt ; ring_simplify.
  replace (fst x ^ 2 * snd y ^ 2 - 2 * fst x * snd x * fst y * snd y +
    snd x ^ 2 * fst y ^ 2)%R with ( (fst x * snd y - snd x * fst y)^2)%R
    by ring.
  apply pow2_ge_0.
  repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
  apply sqrt_pos.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  replace (fst x ^ 2 + 2 * fst x * fst y + fst y ^ 2 + snd x ^ 2 + 2 * snd x * snd y + snd y ^ 2)%R
    with ((fst x + fst y)^2 + (snd x + snd y)^2)%R by ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply sqrt_pos.
Qed.

Lemma Cmod_mult : forall x y, Cmod (x * y) = (Cmod x * Cmod y)%R.
Proof.
  intros x y.
  unfold Cmod.
  rewrite -sqrt_mult.
  apply f_equal ; simpl ; ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Qed.

(** ** C is a field *)

Lemma Cplus_comm (x y : C) : x + y = y + x.
Proof.
  apply injective_projections ; simpl ; apply Rplus_comm.
Qed.
Lemma Cplus_assoc (x y z : C) : x + (y + z) = (x + y) + z.
Proof.
  apply injective_projections ; simpl ; apply sym_eq, Rplus_assoc.
Qed.
Lemma Cplus_0_r (x : C) : x + 0 = x.
Proof.
  apply injective_projections ; simpl ; apply Rplus_0_r.
Qed.
Lemma Cplus_0_l (x : C) : 0 + x = x.
Proof.
  apply injective_projections ; simpl ; apply Rplus_0_l.
Qed.
Lemma Cplus_opp_r (x : C) : x + -x = 0.
Proof.
  apply injective_projections ; simpl ; apply Rplus_opp_r.
Qed.

Lemma Cmult_comm (x y : C) : x * y = y * x.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_assoc (x y z : C) : x * (y * z) = (x * y) * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_0_r (x : C) : x * 0 = 0.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_0_l (x : C) : 0 * x = 0.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_1_r (x : C) : x * 1 = x.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_1_l (x : C) : 1 * x = x.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma Cinv_r (r : C) : r <> 0 -> r * /r = 1.
Proof.
  move => H.
  apply injective_projections ; simpl ; field.
  contradict H.
  apply Rplus_sqr_eq_0 in H.
  apply injective_projections ; simpl ; by apply H.
  contradict H.
  apply Rplus_sqr_eq_0 in H.
  apply injective_projections ; simpl ; by apply H.
Qed.

Lemma Cmult_plus_distr_r (x y z : C) : (x + y) * z = x * z + y * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

Global Instance C_AbelianGroup : AbelianGroup C.
Proof.
econstructor.
apply Cplus_comm.
apply Cplus_assoc.
apply Cplus_0_r.
apply Cplus_opp_r.
Defined.

Global Instance C_Field_mixin : Field_mixin C _.
Proof.
econstructor.
apply Cmult_comm.
apply Cmult_assoc.
apply Cmult_1_r.
apply Cinv_r.
apply Cmult_plus_distr_r.
Defined.

Global Instance C_Field : Field C.
Proof.
econstructor.
apply C_Field_mixin.
Defined.

Global Instance C_AbsField_mixin : AbsField_mixin C _.
Proof.
econstructor.
apply Cmod_0.
rewrite Cmod_opp.
apply Cmod_1.
apply Cmod_triangle.
apply Cmod_mult.
Defined.

Global Instance C_AbsField : AbsField C.
Proof.
  econstructor.
  by apply C_AbsField_mixin.
Defined.

(* Require Export LegacyField.
Import LegacyRing_theory.
Lemma CLegacyTheory : Ring_Theory Cplus Cmult C1 C0 Copp (fun x y : C => false).
  split ; intros ; apply injective_projections ; simpl ; try ring ; by simpl in H.
Qed.
Add Legacy Field C Cplus Cmult C1 C0 Copp (fun x y : C => false) Cinv CLegacyTheory Cinv_l
  with minus := Cminus div := Cdiv.

Goal forall x y z : C, x * z + y * z = (x + y) * z.
intros.
field. *)

(** ** C is a metric space *)

Definition distC x y := Cmod (y - x).

Lemma distC_refl :
  forall x, distC x x = 0.
Proof.
  case => x y /=.
  rewrite /distC /Cmod /=.
  rewrite -sqrt_0.
  apply f_equal.
  ring.
Qed.

(* Lemma distR_comm :
  ∀ x y, distR x y = distR y x.
Admitted.

Lemma distR_triangle :
  ∀ x y z, distR x z ≤ distR x y + distR y z.
Admitted.

Global Instance R_metric : MetricSpace R. *)

(** * Limits *)

Definition is_C_lim (f : C -> C) (z l : C) :=
  filterlim f (locally' z) (locally l).
Definition ex_C_lim (f : C -> C) (z : C) :=
  exists (l : C), is_C_lim f z l.
Definition C_lim (f : C -> C) (z : C) : C :=
  (real (Lim (fun x => fst (f (x, snd z))) (fst z)),
  real (Lim (fun x => snd (f (x, snd z))) (fst z))).

Lemma is_C_lim_unique (f : C -> C) (z l : C) :
  is_C_lim f z l -> C_lim f z = l.
Proof.
  case: l => lx ly H.
  apply injective_projections ; simpl.

  apply (f_equal real (y := Finite lx)).
  apply is_lim_unique => /= P [eps Hp].
  destruct (H (fun z => P (fst z))) as [delta Hd].
  exists eps.
  intros y H'.
  apply Hp.
  apply Rle_lt_trans with (2 := H') ; simpl.
  rewrite -sqrt_Rsqr_abs /Cmod /Rsqr /=.
  move: (snd y + - ly)%R => t.
  apply sqrt_le_1_alt, Rminus_le_0 ; ring_simplify.
  by apply pow2_ge_0.
  exists delta.
  intros y By Hy.
  apply Hd.
  apply Rle_lt_trans with (2 := By) ; simpl.
  rewrite -sqrt_Rsqr_abs /Cmod /Rsqr /=.
  apply Req_le, f_equal ; ring.
  contradict Hy.
  clear -Hy.
  destruct z as [z1 z2].
  now injection Hy.
  
  apply (f_equal real (y := Finite ly)).
  apply is_lim_unique => /= P [eps Hp].
  destruct (H (fun z => P (snd z))) as [delta Hd].
  exists eps.
  intros y H'.
  apply Hp.
  apply Rle_lt_trans with (2 := H') ; simpl.
  rewrite -sqrt_Rsqr_abs /Cmod /Rsqr /=.
  move: (fst y + - lx)%R => t.
  apply sqrt_le_1_alt, Rminus_le_0 ; ring_simplify.
  by apply pow2_ge_0.
  exists delta.
  intros y By Hy.
  apply Hd.
  apply Rle_lt_trans with (2 := By) ; simpl.
  rewrite -sqrt_Rsqr_abs /Cmod /Rsqr /=.
  apply Req_le, f_equal ; ring.
  contradict Hy.
  clear -Hy.
  destruct z as [z1 z2].
  now injection Hy.
Qed.

(** * Derivatives *)

Lemma filter_le_prod_locally :
  forall (x y : R),
  filter_le (filter_prod (locally x) (locally y)) (locally ((x, y) : C)).
Proof.
intros x y P [eps HP].
exists (ball x (pos_div_2 eps)) (ball y (pos_div_2 eps)).
apply locally_ball.
apply locally_ball.
intros u v Bu Bv.
apply HP ; simpl.
unfold Cmod ; simpl.
rewrite -?/(Rminus _ _).
apply Rle_lt_trans with (Rabs (u - x) + Rabs (v - y))%R.
move: (u - x)%R (v - y)%R => l m.
apply Rsqr_incr_0_var.
rewrite -2!sqrt_Rsqr_abs /Rsqr Rminus_le_0 ; ring_simplify.
rewrite /pow ?Rmult_1_r ?sqrt_sqrt ; ring_simplify.
repeat apply Rmult_le_pos.
by apply Rlt_le, Rlt_0_2.
by apply sqrt_pos.
by apply sqrt_pos.
now apply Rplus_le_le_0_compat ; apply pow2_ge_0.
by apply pow2_ge_0.
by apply pow2_ge_0.
now apply Rplus_le_le_0_compat ; apply Rabs_pos.
rewrite (double_var eps).
apply Rplus_lt_compat.
by apply Bu.
by apply Bv.
Qed.

Lemma filter_le_locally_prod :
  forall (x y : R),
  filter_le (locally ((x, y) : C)) (filter_prod (locally x) (locally y)).
Proof.
intros x y P [Q1 Q2 [e1 B1] [e2 B2] HP].
exists (mkposreal _ (Rmin_stable_in_posreal e1 e2)).
intros [u v] B.
apply HP.
apply B1.
apply Rlt_le_trans with (2 := Rmin_l e1 e2).
apply Rle_lt_trans with (2 := B) ; simpl.
rewrite -sqrt_Rsqr_abs /Cmod /Rsqr /=.
move: (v + - y)%R => t.
apply sqrt_le_1_alt, Rminus_le_0 ; ring_simplify.
by apply pow2_ge_0.
apply B2.
apply Rlt_le_trans with (2 := Rmin_r e1 e2).
apply Rle_lt_trans with (2 := B) ; simpl.
rewrite -sqrt_Rsqr_abs /Cmod /Rsqr /=.
move: (u + - x)%R => t.
apply sqrt_le_1_alt, Rminus_le_0 ; ring_simplify.
by apply pow2_ge_0.
Qed.

Lemma filterlim_Cplus :
  forall x y : C,
  filterlim (fun z : C * C => Cplus (fst z) (snd z))
    (filter_prod (locally x) (locally y))
    (locally (Cplus x y)).
Proof.
  intros x y.
  apply filterlim_filter_le_2 with (1 := filter_le_prod_locally _ _).
  apply filterlim_pair.
  eapply filterlim_compose_2.
  eapply filterlim_compose.
  apply filterlim_fst.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_fst.
  eapply filterlim_compose.
  apply filterlim_snd.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_fst.
  now apply (filterlim_plus (fst x) (fst y)).
  eapply filterlim_compose_2.
  eapply filterlim_compose.
  apply filterlim_fst.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_snd.
  eapply filterlim_compose.
  apply filterlim_snd.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_snd.
  now apply (filterlim_plus (snd x) (snd y)).
Qed.

Lemma filterlim_Cscal :
  forall x y : C,
  filterlim (Cmult x) (locally y) (locally (Cmult x y)).
Proof.
  intros x y.
  unfold Cmult.
  apply filterlim_filter_le_2 with (1 := filter_le_prod_locally _ _).
  apply filterlim_pair.
  eapply filterlim_compose_2.
  eapply filterlim_compose.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_fst.
  apply (filterlim_scal_l (fst x) (fst y)).
  eapply filterlim_compose.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_snd.
  apply (filterlim_scal_l (snd x) (snd y)).
  unfold Rminus.
  eapply filterlim_compose_2.
  apply filterlim_fst.
  eapply filterlim_compose.
  apply filterlim_snd.
  apply filterlim_opp.
  now apply filterlim_plus.
  eapply filterlim_compose_2.
  eapply filterlim_compose.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_snd.
  apply (filterlim_scal_l (fst x) (snd y)).
  eapply filterlim_compose.
  eapply filterlim_filter_le_1 with (1 := filter_le_locally_prod _ _).
  apply filterlim_fst.
  apply (filterlim_scal_l (snd x) (fst y)).
  now apply filterlim_plus.
Qed.

Global Instance C_metric_vector : MetricVectorSpace C C.
Proof.
econstructor.
apply filterlim_Cplus.
apply filterlim_Cscal.
Defined.

Definition is_C_derive (f : C -> C) (z l : C) :=
  filterderive f z l.
Definition C_derive (f : C -> C) (z : C) := C_lim (fun h => (f (z + h) - f z) / h) 0.

(** * Integrals *)

(** * Complex power series *)
