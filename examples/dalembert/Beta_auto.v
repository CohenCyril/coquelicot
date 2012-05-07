Require Import Reals.
Require Import AutoDeriv.

Require Import Function1 Function2.
Require Import Probleme.

Open Local Scope R_scope.

(** Dans ce fichier, toutes les preuves ont été faites à l'aide de la tactique AutoDerive *)

(** * Definition de Beta *)
Hypothesis d1_u1 : derivable u1.

Lemma C_u1 : continuity u1.
Proof.
  intros.
  apply derivable_continuous.
  apply d1_u1.
Qed.


Definition beta (x t : R) :=
  1/(2*c) * RiemannInt (cont_impl_Rint u1 C_u1 (x-c*t) (x+c*t)).

(** * Dérivées par rapport à x *)
(** Dérivée première *)
Definition beta10 x t := (1/(2*c) * (u1 (x+c*t) - u1 (x-c*t))).
Lemma beta10_lim : forall x t, derivable10_pt_lim beta x t (beta10 x t).
Proof.
  intros ; unfold beta, beta10.
  AutoDerive.
Qed.

(** Dérivée seconde *)
Definition beta20 x t := (1/(2*c) * ((derive u1 d1_u1) (x+c*t) - (derive u1 d1_u1) (x-c*t))).

Lemma beta20_lim : forall x t, derivable20_pt_lim beta x t (beta20 x t).
Proof.
  intros.
  apply derivable20_10_pt_lim with (1 := fun x => beta10_lim x t).
  unfold beta10, beta20.
  AutoDerive.
Qed.

(** * Dérivées par rapport à t *)
(** Dérivée première *)
Definition beta01 x t := (1/2 * (u1 (x+c*t) + u1 (x-c*t))).

Lemma beta01_lim : forall x t, derivable01_pt_lim beta x t (beta01 x t).
Proof.
  intros ; unfold beta, beta01.

  AutoDerive.

  apply Hc.
Qed.

(** Dérivée seconde *)
Definition beta02 x t := (c/2 * ((derive u1 d1_u1) (x+c*t) - (derive u1 d1_u1) (x-c*t))).

Lemma beta02_lim : forall x t, derivable02_pt_lim beta x t (beta02 x t).
Proof.
  intros.
  apply derivable02_01_pt_lim with (1 := beta01_lim x).
  unfold beta01, beta02.
  AutoDerive.
Qed.