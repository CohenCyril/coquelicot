Require Import Reals.
Require Import AutoDeriv.

Require Import Function1 Function2.
Require Import Probleme.

Require Import Partial_function.

Open Local Scope R_scope.

(** Dans ce fichier, toutes les preuves ont été faites à l'aide de la tactique AutoDerive *)

(** * Définition de alpha *)
Hypothesis d2_u0 : derivable2 u0.

Definition alpha x t := 1/2 * (u0 (x+c*t) + u0 (x-c*t)).

(** * Dérivées par rapport à x *)
(** Dérivée première *)
Definition alpha10 x t := 
  (1/2 * (derive u0 (d2_impl_d1 u0 d2_u0) (x + c * t) + derive u0 (d2_impl_d1 u0 d2_u0) (x - c*t))).

Lemma alpha10_lim : forall x t, derivable10_pt_lim alpha x t (alpha10 x t).
Proof.
  intros x t ; unfold alpha, alpha10.
  AutoDerive.
Qed.

(** Dérivée seconde *)
Definition alpha20 x t := (1/2 * (derive2 u0 d2_u0 (x + c * t) + derive2 u0 d2_u0 (x - c*t))).

Lemma alpha20_lim : forall x t, derivable20_pt_lim alpha x t (alpha20 x t).
Proof.
  intros.
  apply derivable20_10_pt_lim with (1 := fun x => alpha10_lim x t).
  unfold alpha10, alpha20.

  AutoDerive.

  apply derivable_pt_derive.
  apply d2_u0.
  apply derivable_pt_derive.
  apply d2_u0.
Qed.

(** * Dérivées par rapport à t *)
(** Dérivée première *)
Definition alpha01 x t := 
  (c/2 * (derive u0 (d2_impl_d1 u0 d2_u0) (x + c * t) - derive u0 (d2_impl_d1 u0 d2_u0) (x - c*t))).
Lemma alpha01_lim : forall x t, derivable01_pt_lim alpha x t (alpha01 x t).
Proof.
  intros ; unfold alpha, alpha01.
  AutoDerive.
Qed.

(** Dérivée seconde *)
Definition alpha02 x t := (c^2/2 * (derive2 u0 d2_u0 (x + c * t) + derive2 u0 d2_u0 (x - c*t))).

Lemma alpha02_lim : forall x t, derivable02_pt_lim alpha x t (alpha02 x t).
Proof.
  intros.
  apply derivable02_01_pt_lim with (1 := alpha01_lim x).
  unfold alpha01, alpha02.

  AutoDerive.

  apply derivable_pt_derive.
  apply d2_u0.
  apply derivable_pt_derive.
  apply d2_u0.
Qed.