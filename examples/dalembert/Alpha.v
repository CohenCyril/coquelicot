Require Import Reals.

Require Import Function1 Function2.
Require Import Probleme.

Open Local Scope R_scope.

(** Dans ce fichier, toutes les preuves ont été faites manuellement *)

(** * Définition de alpha *)
Hypothesis d2_u0 : derivable2 u0.

Definition alpha x t := 1/2 * (u0 (x+c*t) + u0 (x-c*t)).

(** * Dérivées par rapport à x *)
(** Dérivée première *)
Definition alpha10 x t := 
  1/2 * (derive u0 (d2_impl_d1 u0 d2_u0) (x + c * t) + derive u0 (d2_impl_d1 u0 d2_u0) (x - c*t)).
Lemma alpha10_lim : forall x t, derivable10_pt_lim alpha x t (alpha10 x t).
Proof.
  intros x t.
  assert (alpha10 x t =
    1/2 * (derive u0 (d2_impl_d1 u0 d2_u0) (x + c * t) * (1+0) +
    derive u0 (d2_impl_d1 u0 d2_u0) (x - c * t) * (1-0))).
    unfold alpha10 ; ring.
    rewrite H ; clear H.
  apply derivable_pt_lim_scal ;
  apply derivable_pt_lim_plus ;
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (d2_impl_d1 u0 d2_u0 (x+c*t))) ; unfold derive ; ring.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (d2_impl_d1 u0 d2_u0 (x-c*t))) ; unfold derive ; ring.
Qed.

(** Dérivée seconde *)
Definition alpha20 x t := 
  1/2 * (derive2 u0 d2_u0 (x + c * t) + derive2 u0 d2_u0 (x - c*t)).
Lemma alpha20_lim : forall x t, derivable20_pt_lim alpha x t (alpha20 x t).
Proof.
  intros.
  apply derivable20_10_pt_lim with (1 := fun x => alpha10_lim x t).
  assert (alpha20 x t = 
    1 / 2 * (derive2 u0 d2_u0 (x + c * t)*(1+0) + derive2 u0 d2_u0 (x - c * t)*(1-0))).
    unfold alpha20 ; ring.
    rewrite H ; clear H.

  apply derivable_pt_lim_scal ;
  apply derivable_pt_lim_plus ;
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_derive ;
  apply (derivable2_derive2 _ _ _ (d2_u0 _)) ;
  reflexivity.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_derive ;
  apply (derivable2_derive2 _ _ _ (d2_u0 _)) ;
  reflexivity.
Qed.

(** * Dérivées par rapport à t *)
(** Dérivée première *)
Definition alpha01 x t :=
  c/2 * (derive u0 (d2_impl_d1 u0 d2_u0) (x + c * t) - derive u0 (d2_impl_d1 u0 d2_u0) (x - c*t)).

Lemma alpha01_lim : forall x t, derivable01_pt_lim alpha x t (alpha01 x t).
Proof.
  intros.
  assert (alpha01 x t =
    1/2 * (derive u0 (d2_impl_d1 u0 d2_u0) (x + c * t) * (0+c*1) +
    derive u0 (d2_impl_d1 u0 d2_u0) (x - c * t) * (0-c*1))).
    unfold alpha01 ; field.
    rewrite H ; clear H.
  apply derivable_pt_lim_scal ;
  apply derivable_pt_lim_plus ;
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
  apply (derive_pt_eq_1 _ _ _ (d2_impl_d1 u0 d2_u0 (x+c*t))) ; unfold derive ; ring.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
  apply (derive_pt_eq_1 _ _ _ (d2_impl_d1 u0 d2_u0 (x-c*t))) ; unfold derive ; ring.
Qed.

(** Dérivée seconde *)
Definition alpha02 x t := (c^2/2 * (derive2 u0 d2_u0 (x + c * t) + derive2 u0 d2_u0 (x - c*t))).
Lemma alpha02_lim : forall x t, derivable02_pt_lim alpha x t (alpha02 x t).
Proof.
  intros.
  apply derivable02_01_pt_lim with (1 := alpha01_lim x).
  assert (alpha02 x t =
    c/2 * (derive2 u0 d2_u0 (x + c * t) * (0+c*1) -
    derive2 u0 d2_u0 (x - c * t) * (0-c*1))).
    unfold alpha02 ; field.
    rewrite H ; clear H.

  apply derivable_pt_lim_scal ;
  apply derivable_pt_lim_minus ;
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_derive ;
  apply (derivable2_derive2 _ _ _ (d2_u0 _)) ;
  reflexivity.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_derive ;
  apply (derivable2_derive2 _ _ _ (d2_u0 _)) ;
  reflexivity.
Qed.