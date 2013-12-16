Require Import Reals ssreflect.
Require Import Rcomplements Rbar.
Require Import Continuity Derive Hierarchy.

(** * The set of complex numbers *)

Definition C := (R * R)%type.

Definition RtoC (x : R) : C := (x,0).
Coercion RtoC : R >-> C.

Lemma RtoC_inj : forall (x y : R),
  RtoC x = RtoC y -> x = y.
Proof.
  intros x y H.
  now apply (f_equal (@fst R R)) in H.
Qed.

Lemma Ceq_dec (z1 z2 : C) : { z1 = z2 } + { z1 <> z2 }.
Proof.
  destruct z1 as [x1 y1].
  destruct z2 as [x2 y2].
  case: (Req_EM_T x1 x2) => [ -> | Hx ].
  case: (Req_EM_T y1 y2) => [ -> | Hy ].
  by left.
  right ; contradict Hy.
  now apply (f_equal (@snd R R)) in Hy ; simpl in Hy.
  right ; contradict Hx.
  now apply (f_equal (@fst R R)) in Hx ; simpl in Hx.
Qed.

(** ** Constants and usual functions *)

(** 0 and 1 for complex are defined as [RtoC 0] and [RtoC 1] *)
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

Definition Re (z : C) : R := fst z.

Definition Im (z : C) : R := snd z.

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

Lemma Rmax_Cmod : forall x,
  Rmax (Rabs (fst x)) (Rabs (snd x)) <= Cmod x.
Proof.
  case => x y /=.
  rewrite -!sqrt_Rsqr_abs.
  apply Rmax_case ; apply sqrt_le_1_alt, Rminus_le_0 ;
  rewrite /Rsqr /= ; ring_simplify ; by apply pow2_ge_0.
Qed.
Lemma Cmod_2Rmax : forall x,
  Cmod x <= sqrt 2 * Rmax (Rabs (fst x)) (Rabs (snd x)).
Proof.
  case => x y /= ; apply Rmax_case_strong => H0 ;
  rewrite -!sqrt_Rsqr_abs ;
  rewrite -?sqrt_mult ;
  try (by apply Rle_0_sqr) ;
  try (by apply Rlt_le, Rlt_0_2) ;
  apply sqrt_le_1_alt ; simpl ; [ rewrite Rplus_comm | ] ;
  rewrite /Rsqr ; apply Rle_minus_r ; ring_simplify ;
  apply Rsqr_le_abs_1 in H0 ; by rewrite /pow !Rmult_1_r.
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

Lemma Copp_plus_distr (z1 z2 : C) : - (z1 + z2) = (- z1 + - z2).
Proof.
  apply injective_projections ; by apply Ropp_plus_distr.
Qed.
Lemma Copp_minus_distr (z1 z2 : C) : - (z1 - z2) = z2 - z1.
Proof.
  apply injective_projections ; by apply Ropp_minus_distr.
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

Lemma Cinv_l (r : C) : r <> 0 -> /r * r = 1.
Proof.
intros Zr.
rewrite Cmult_comm.
now apply Cinv_r.
Qed.

Lemma Cmult_plus_distr_l (x y z : C) : x * (y + z) = x * y + x * z.
Proof.
  apply injective_projections ; simpl ; ring.
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

Lemma Copp_0 : Copp 0 = 0.
Proof.
  apply (@opp_zero C C_AbelianGroup).
Qed.

Global Instance Ring_mixin_C : Ring_mixin C _.
Proof.
econstructor.
apply Cmult_assoc.
apply Cmult_1_r.
apply Cmult_1_l.
apply Cmult_plus_distr_r.
apply Cmult_plus_distr_l.
Defined.

Global Instance Ring_C : Ring C.
Proof.
econstructor.
apply Ring_mixin_C.
Defined.

Global Instance AbsRing_mixin_C : AbsRing_mixin C _.
Proof.
econstructor.
apply Cmod_0.
rewrite Cmod_opp.
apply Cmod_1.
apply Cmod_triangle.
intros x y.
apply Req_le.
apply Cmod_mult.
Defined.

Global Instance AbsRing_C : AbsRing C.
Proof.
  econstructor.
  by apply AbsRing_mixin_C.
Defined.

Lemma Cmod_eq_0 :
  forall x, Cmod x = 0 -> x = 0.
Proof.
intros x H.
unfold Cmod, pow in H.
rewrite 2!Rmult_1_r -sqrt_0 in H.
apply sqrt_inj in H.
apply Rplus_sqr_eq_0 in H.
now apply injective_projections.
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
apply Rle_refl.
Qed.

Lemma Cmod_ge_0 :
  forall x, 0 <= Cmod x.
Proof.
intros x.
apply sqrt_pos.
Qed.
Lemma Cmod_gt_0 :
  forall (x : C), x <> 0 -> 0 < Cmod x.
Proof.
intros x Hx.
destruct (Cmod_ge_0 x) => //.
by apply sym_eq, Cmod_eq_0 in H.
Qed.

Lemma Cmod_norm :
  forall x : C, Cmod x = (@norm (R * R) R _ _ _ _ x).
Proof.
intros [u v].
unfold Cmod.
simpl.
apply (f_equal2 (fun x y => sqrt (x + y))) ;
  rewrite !Rmult_1_r ;
  apply Rsqr_abs.
Qed.

Lemma Cmod_R :
  forall x : R, Cmod x = Rabs x.
Proof.
intros x.
unfold Cmod.
simpl.
rewrite Rmult_0_l Rplus_0_r Rmult_1_r.
apply sqrt_Rsqr_abs.
Qed.

Lemma Cmod_inv :
  forall x : C, x <> 0 -> Cmod (/ x) = Rinv (Cmod x).
Proof.
intros x Zx.
apply Rmult_eq_reg_l with (Cmod x).
rewrite -Cmod_mult.
rewrite Rinv_r.
rewrite Cinv_r.
rewrite Cmod_R.
apply Rabs_R1.
exact Zx.
contradict Zx.
now apply Cmod_eq_0.
contradict Zx.
now apply Cmod_eq_0.
Qed.

Lemma Cmod_div (x y : C) : y <> 0 ->
  Cmod (x / y) = Rdiv (Cmod x) (Cmod y).
Proof.
  move => Hy.
  rewrite /Cdiv.
  rewrite Cmod_mult.
  by rewrite Cmod_inv.
Qed.

Lemma Cmult_neq_0 (z1 z2 : C) : z1 <> 0 -> z2 <> 0 -> z1 * z2 <> 0.
Proof.
  intros Hz1 Hz2 => Hz.
  assert (Cmod (z1 * z2) = 0).
  by rewrite Hz Cmod_0.
  rewrite Cmod_mult in H.
  apply Rmult_integral in H ; destruct H.
  now apply Hz1, Cmod_eq_0.
  now apply Hz2, Cmod_eq_0.
Qed.

Lemma Cminus_eq_contra : forall r1 r2 : C, r1 <> r2 -> r1 - r2 <> 0.
Proof.
  intros ; contradict H ; apply injective_projections ;
  apply Rminus_diag_uniq.
  now apply (f_equal (@fst R R)) in H.
  now apply (f_equal (@snd R R)) in H.
Qed.

Lemma C_field_theory : field_theory (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
constructor.
constructor.
exact Cplus_0_l.
exact Cplus_comm.
exact Cplus_assoc.
exact Cmult_1_l.
exact Cmult_comm.
exact Cmult_assoc.
exact Cmult_plus_distr_r.
easy.
exact Cplus_opp_r.
intros H.
injection H.
exact R1_neq_R0.
easy.
apply Cinv_l.
Qed.

Add Field C_field_field : C_field_theory.

(** * C is a NormedVectorSpace *)

(** on R *)

Global Instance R_NVS : NormedVectorSpace R R.
Proof.
  apply NormedVectorSpace_AbsRing.
Defined.

Global Instance C_R_NVS_mixin :
  NormedVectorSpace_mixin C R _ (MetricBall_prod _ _).
Proof.
  unfold C.
  exact (NormedVectorSpace_mixin_prod R_NVS R_NVS).
Defined.

Global Instance C_R_NVS : NormedVectorSpace C R.
  apply Build_NormedVectorSpace with (1 := C_R_NVS_mixin).
Defined.

(** on C (with the balls of R^2) *)

Global Instance C_NVS_mixin :
  NormedVectorSpace_mixin C C _ (MetricBall_prod _ _).
Proof.
  apply Build_NormedVectorSpace_mixin with Cmod.
  apply Cmod_triangle.
  intros x y.
  apply Req_le, Cmod_mult.
  intros x y eps.
  rewrite Cmod_norm.
  apply NormedVectorSpace_mixin_prod_norm_compat1.
  destruct (NormedVectorSpace_mixin_prod_norm_compat2 R_NVS R_NVS) as [M H].
  exists M.
  intros x y eps.
  rewrite Cmod_norm.
  apply H.
Defined.

Global Instance C_NVS : NormedVectorSpace C C.
  apply Build_NormedVectorSpace with (1 := C_NVS_mixin).
Defined.

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
  destruct (H (fun z => P (fst z))) as [delta Hd] ; clear H.
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
  destruct (H (fun z => P (snd z))) as [delta Hd] ; clear H.
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
  filterderive f (locally z) l.
Definition ex_C_derive (f : C -> C) (z : C) :=
  exists l : C, is_C_derive f z l.
Definition C_derive (f : C -> C) (z : C) := C_lim (fun x => (f x - f z) / (x - z)) z.

Lemma C_derive_unique (f : C -> C) (z l : C) :
  is_C_derive f z l -> C_derive f z = l.
Proof.
  intros Df.
  specialize (Df _ (fun P H => H)).
  apply is_C_lim_unique.
  intros P HP.
  destruct HP as [eps HP].
  destruct (Df (pos_div_2 eps)) as [eps' Df'].
  exists eps'.
  intros y Hy Hyz.
  apply HP.
  assert (y - z <> 0).
  contradict Hyz.
  replace y with (y - z + z) by ring.
  rewrite Hyz.
  apply Cplus_0_l.
  apply norm_compat1 ; simpl.
  replace ((f y - f z) / (y - z) + - l) with
    ((f y + - f z + - ((y + - z) * l)) / (y + - z)).
  2: by field.
  rewrite Cmod_div => //.
  apply Rlt_div_l.
  by apply Cmod_gt_0.
  eapply Rle_lt_trans.
  apply (Df' y Hy).
  simpl.
  rewrite /Rdiv Rmult_assoc.
  apply Rmult_lt_compat_l.
  by apply eps.
  rewrite Rmult_comm Rlt_div_l.
  apply Rminus_lt_0 ; ring_simplify.
  by apply Cmod_gt_0.
  by apply Rlt_0_2.
Qed.

(** * Integrals *)

(** * Complex power series *)
