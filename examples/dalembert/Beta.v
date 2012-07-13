Require Import Reals.
Require Import Rcomplements Derive RInt Locally Differential.
Require Import Function1 Function2.
Require Import Probleme.

Open Local Scope R_scope.

(** Dans ce fichier, toutes les preuves ont été faites manuellement *)

(** * Definition de Beta *)
Hypothesis d1_u1 : derivable u1.

Lemma RInt_u1 : forall a b, Riemann_integrable u1 a b.
Proof.
  intros.
  apply cont_impl_Rint.
  apply derivable_continuous.
  apply d1_u1.
Qed.

Definition beta (x t : R) :=
  1/(2*c) * RiemannInt (RInt_u1 (x-c*t) (x+c*t)).

(** * Dérivées par rapport à x *)
(** Dérivée première *)
Definition beta10 x t := (1/(2*c) * (u1 (x+c*t) - u1 (x-c*t))).
Lemma beta10_lim : forall x t, derivable10_pt_lim beta x t (beta10 x t).
Proof.
  intros.
  assert (beta10 x t =
    1/(2*c) * (fst (- u1 (x - c*t),u1 (x+c*t)) * (1-0) + snd (- u1 (x - c*t),u1 (x+c*t)) * (1+0))).
    unfold beta10 ; simpl ; ring.
    rewrite H ; clear H.
  assert (Cf : continuity u1).
    apply derivable_continuous.
    apply d1_u1.
  apply (derivable_pt_lim_expr (fun x => 1/(2*c)*Rint u1 (cont_impl_Rint u1 Cf) (x-c*t) (x+c*t))).
    intros ; unfold Rint, beta.
    rewrite (RiemannInt_P5 (RInt_u1 (y - c * t) (y + c * t))
    (cont_impl_Rint u1 Cf (y - c * t) (y + c * t))).
    reflexivity.
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_comp2 (fun a b => Rint u1 (cont_impl_Rint u1 Cf) a b)).
  apply differentiable_pt_lim_Rint.
  apply Cf.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
Qed.

(** Dérivée seconde *)
Definition beta20 x t := (1/(2*c) * ((derive u1 d1_u1) (x+c*t) - (derive u1 d1_u1) (x-c*t))).
Lemma beta20_lim : forall x t, derivable20_pt_lim beta x t (beta20 x t).
Proof.
  intros.
  apply derivable20_10_pt_lim with (1 := fun x => beta10_lim x t).
  assert (beta20 x t
    = 1 / (2 * c) * (derive u1 d1_u1 (x + c * t) * (1+0) - derive u1 d1_u1 (x - c * t) * (1-0))).
    unfold beta20 ; ring.
    rewrite H ; clear H.

  apply derivable_pt_lim_scal ;
  apply derivable_pt_lim_minus ;
  apply derivable_pt_lim_comp.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (d1_u1 (x+c*t))) ; reflexivity.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  apply (derive_pt_eq_1 _ _ _ (d1_u1 (x-c*t))) ; reflexivity.
Qed.

(** * Dérivées par rapport à t *)
(** Dérivée première *)
Definition beta01 x t := (1/2 * (u1 (x+c*t) + u1 (x-c*t))).

Lemma beta01_lim : forall x t, derivable01_pt_lim beta x t (beta01 x t).
Proof.
  intros.
  assert (beta01 x t =
    1/(2*c) * (fst (- u1 (x - c*t),u1 (x+c*t)) * (0-c*1)
    + snd (- u1 (x - c*t),u1 (x+c*t)) * (0+c*1))).
    unfold beta01 ; simpl ; field.
    apply Hc.
    rewrite H ; clear H.
  assert (Cf : continuity u1).
    apply derivable_continuous.
    apply d1_u1.
  apply derivable_pt_lim_scal.
  apply (derivable_pt_lim_comp2 (Rint u1 RInt_u1)).
  apply differentiable_pt_lim_Rint, Cf.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
Qed.

(** Dérivée seconde *)
Definition beta02 x t := (c/2 * ((derive u1 d1_u1) (x+c*t) - (derive u1 d1_u1) (x-c*t))).
Lemma beta02_lim : forall x t, derivable02_pt_lim beta x t (beta02 x t).
Proof.
  intros.
  apply derivable02_01_pt_lim with (1 := beta01_lim x).
  assert (beta02 x t =
    1 / 2 * (derive u1 d1_u1 (x + c * t) * (0 + c * 1) + derive u1 d1_u1 (x - c * t) * (0 - c * 1))).
    unfold beta02 ; field.
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
  apply (derive_pt_eq_1 _ _ _ (d1_u1 (x+c*t))) ; reflexivity.
  apply derivable_pt_lim_minus.
  apply derivable_pt_lim_const.
  apply (derivable_pt_lim_expr (fun t => c*t)).
    intros ; reflexivity.
  apply derivable_pt_lim_scal.
  apply derivable_pt_lim_id.
  apply (derive_pt_eq_1 _ _ _ (d1_u1 (x-c*t))) ; reflexivity.
Qed.
