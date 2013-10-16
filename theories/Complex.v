Require Import Reals ssreflect.
Require Import Coquelicot.

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

Definition Cre (x : C) : R := fst x.
Definition Cim (x : C) : R := snd x.

Definition Cmod (x : C) : R := sqrt (Cre x ^ 2 + Cim x ^ 2).
Parameter Carg : C -> R.
Axiom Carg_dec : 
  forall (x : C), x = (Cmod x) * (cos (Carg x), sin (Carg x)) /\ -PI < Carg x <= PI.

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

(** ** C is a field *)

Lemma Cplus_comm (x y : C) : x + y = y + x.
Proof.
  apply injective_projections ; simpl ; apply Rplus_comm.
Qed.
Lemma Cplus_assoc (x y z : C) : x + y + z = x + (y + z).
Proof.
  apply injective_projections ; simpl ; apply Rplus_assoc.
Qed.
Lemma Cplus_0_r (x : C) : x + 0 = x.
Proof.
  apply injective_projections ; simpl ; apply Rplus_0_r.
Qed.
Lemma Cplus_0_l (x : C) : 0 + x = x.
Proof.
  apply injective_projections ; simpl ; apply Rplus_0_l.
Qed.

Lemma Cmult_comm (x y : C) : x * y = y * x.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma Cmult_assoc (x y z : C) : x * y * z = x * (y * z).
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

Lemma Cinv_l (r : C) : r <> 0 -> / r * r = 1.
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

Definition is_C_lim_1 (f : C -> C) (z l : C) :=
  filterlim (fun x => f (x,Cim z)) (locally' (Cre z)) (locally l).
Definition ex_C_lim_1 (f : C -> C) (z : C) :=
  exists (l : C), is_C_lim_1 f z l.
Definition C_lim_1 (f : C -> C) (z : C) : C :=
  (real (Lim (fun x => Cre (f (x, Cim z))) (Cre z)),
  real (Lim (fun x => Cim (f (x, Cim z))) (Cre z))).

Lemma is_C_lim_1_unique (f : C -> C) (z l : C) :
  is_C_lim_1 f z l -> C_lim_1 f z = l.
Proof.
  case: l => lx ly H.
  apply injective_projections ; simpl.

  replace lx with (real (Finite lx)) by reflexivity.
  apply f_equal.
  apply is_lim_unique => /= P Hp.
  apply (H (fun z => P (Cre z))).
  case: Hp => d Hp.
  exists d ; case => x y /= Hd.
  apply Hp.
  rewrite /dist_prod /= in Hd.
  apply Rle_lt_trans with (2 := Hd).
  by apply Rmax_l.
  
  replace ly with (real (Finite ly)) by reflexivity.
  apply f_equal.
  apply is_lim_unique => /= P Hp.
  apply (H (fun z => P (Cim z))).
  case: Hp => d Hp.
  exists d ; case => x y /= Hd.
  apply Hp.
  rewrite /dist_prod /= in Hd.
  apply Rle_lt_trans with (2 := Hd).
  by apply Rmax_r.
Qed.

Definition is_C_lim_i (f : C -> C) (z l : C) :=
  filterlim (fun y => f (Cre z, y)) (locally' (Cim z)) (locally l).
Definition ex_C_lim_i (f : C -> C) (z : C) :=
  exists (l : C), is_C_lim_i f z l.
Definition C_lim_i (f : C -> C) (z : C) : C :=
  (real (Lim (fun y => Cre (f (Cre z,y))) (Cim z)),
  real (Lim (fun y => Cim (f (Cre z,y))) (Cim z))).

Lemma is_C_lim_i_unique (f : C -> C) (z l : C) :
  is_C_lim_1 f z l -> C_lim_1 f z = l.
Proof.
  case: l => lx ly H.
  apply injective_projections ; simpl.

  replace lx with (real (Finite lx)) by reflexivity.
  apply f_equal.
  apply is_lim_unique => /= P Hp.
  apply (H (fun z => P (Cre z))).
  case: Hp => d Hp.
  exists d ; case => x y /= Hd.
  apply Hp.
  rewrite /dist_prod /= in Hd.
  apply Rle_lt_trans with (2 := Hd).
  by apply Rmax_l.
  
  replace ly with (real (Finite ly)) by reflexivity.
  apply f_equal.
  apply is_lim_unique => /= P Hp.
  apply (H (fun z => P (Cim z))).
  case: Hp => d Hp.
  exists d ; case => x y /= Hd.
  apply Hp.
  rewrite /dist_prod /= in Hd.
  apply Rle_lt_trans with (2 := Hd).
  by apply Rmax_r.
Qed.

Definition is_C_lim (f : C -> C) (z l : C) :=
  filterlim f (locally' z) (locally l).
Definition ex_C_lim (f : C -> C) (z : C) :=
  exists (l : C), is_C_lim f z l.
Definition C_lim (f : C -> C) (z : C) : C :=
  (real (Lim (fun x => Lim (fun y => Cre (f (x,y))) (Cim z)) (Cre z)),
  real (Lim (fun x => Lim (fun y => Cim (f (x,y))) (Cim z)) (Cre z))).

Lemma is_C_lim_unique (f : C -> C) (z l : C) :
  is_C_lim f z l -> C_lim f z = l.
Proof.
  case: l => lx ly H.
  apply injective_projections ; simpl.
Admitted.

(** * Derivatives *)

Definition C_derive (f : C -> C) (z : C) := C_lim (fun h => (f (z + h) - f z) / h) 0.

(** * Integrals *)

(** * Complex power series *)
