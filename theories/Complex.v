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

(** * Limits *)

Definition is_C_lim (f : C -> C) (z l : C) :=
  let MS := Normed_MetricBall (AbsField_NormedVectorSpace C C_AbsField) in
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
  exists eps => y Hy.
  apply Hp.
  apply Rle_lt_trans with (2 := Hy).
  rewrite /= /Cmod.
  rewrite -sqrt_Rsqr_abs.
  apply sqrt_le_1_alt.
  move: (snd (y + - (lx, ly))) => t.
  rewrite /Rsqr Rminus_le_0 /= ; ring_simplify.
  by apply pow2_ge_0.
  exists delta.
  intros y By Hy.
  apply Hd.
  apply Rle_lt_trans with (2 := By).
  rewrite /= /Cmod.
  rewrite -sqrt_Rsqr_abs /Rsqr /=.
  apply Req_le, f_equal.
  ring.
  contradict Hy.
  clear -Hy.
  destruct z as [z1 z2].
  now injection Hy.
  
  apply (f_equal real (y := Finite ly)).
  apply is_lim_unique => /= P [eps Hp].
  destruct (H (fun z => P (snd z))) as [delta Hd].
  exists eps => y Hy.
  apply Hp.
  apply Rle_lt_trans with (2 := Hy).
  rewrite /= /Cmod.
  rewrite -sqrt_Rsqr_abs.
  apply sqrt_le_1_alt.
  move: (fst (y + - (lx, ly))) => t.
  rewrite /Rsqr Rminus_le_0 /= ; ring_simplify.
  by apply pow2_ge_0.
  exists delta.
  intros y By Hy.
  apply Hd.
  apply Rle_lt_trans with (2 := By).
  rewrite /= /Cmod.
  rewrite -sqrt_Rsqr_abs /Rsqr /=.
  apply Req_le, f_equal.
  ring.
  contradict Hy.
  clear -Hy.
  destruct z as [z1 z2].
  now injection Hy.
Qed.

(** * Derivatives *)

Definition is_C_derive (f : C -> C) (z l : C) :=
  filterderive f z l.
Definition ex_C_derive (f : C -> C) (z : C) :=
  exists l : C, is_C_derive f z l.
Definition C_derive (f : C -> C) (z : C) := C_lim (fun x => (f x - f z) / (x - z)) z.

Lemma C_derive_unique (f : C -> C) (z l : C) :
  is_C_derive f z l -> C_derive f z = l.
Proof.
  intros Df.
  apply is_C_lim_unique.
  apply filterlim_ext with (fun y : C => / (y + - z) * (f y + - f z)).
  intro x.
  apply Cmult_comm.
  by apply Df.
Qed.

(** * Integrals *)

(** * Complex power series *)
