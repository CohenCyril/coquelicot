Require Import Reals.

Require Import Arithmetique Function1 Function2.
Require Import Probleme Alpha Beta Gamma.

Open Local Scope R_scope.

Definition sol x t := alpha x t + beta x t + gamma x t.
Definition sol10 x t := alpha10 x t + beta10 x t + gamma10 x t.
Definition sol20 x t := alpha20 x t + beta20 x t + gamma20 x t.
Definition sol01 x t := alpha01 x t + beta01 x t + gamma01 x t.
Definition sol02 x t := alpha02 x t + beta02 x t + gamma02 x t.

(** * Dérivées de sol *)
(** Par rapport à x *)

Lemma sol10_lim : forall x t, derivable10_pt_lim sol x t (sol10 x t).
Proof.
  intros x t ; unfold sol, sol10, derivable10_pt_lim.
  apply derivable_pt_lim_plus ;
  [apply derivable_pt_lim_plus|].
  apply alpha10_lim.
  apply beta10_lim.
  apply gamma10_lim.
Qed.

Lemma sol20_lim : forall x t, derivable20_pt_lim sol x t (sol20 x t).
Proof.
  intros x t.
  exists (fun x => sol10 x t) ; split.
  intros ; apply sol10_lim.
  apply derivable_pt_lim_plus ;
  [apply derivable_pt_lim_plus|].
  apply (derivable2_pt_lim_derivable_pt_lim_bis (fun x => alpha x t)) ;
    [ intros ; apply alpha10_lim | apply alpha20_lim].
  apply (derivable2_pt_lim_derivable_pt_lim_bis (fun x => beta x t)) ;
    [ intros ; apply beta10_lim | apply beta20_lim].
  apply (derivable2_pt_lim_derivable_pt_lim_bis (fun x => gamma x t)) ;
    [ intros ; apply gamma10_lim | apply gamma20_lim].
Qed.

(** par rapport à t *)

Lemma sol01_lim : forall x t, derivable01_pt_lim sol x t
  (alpha01 x t
  + beta01 x t
  + gamma01 x t).
Proof.
  intros x t ; unfold sol, derivable01_pt_lim.
  apply derivable_pt_lim_plus ;
  [apply derivable_pt_lim_plus|].
  apply alpha01_lim.
  apply beta01_lim.
  apply gamma01_lim.
Qed.

Lemma sol02_lim : forall x t, derivable02_pt_lim sol x t
  (alpha02 x t + beta02 x t + gamma02 x t).
Proof.
  intros x t.
  exists (fun t => sol01 x t) ; split.
  apply sol01_lim.
  apply derivable_pt_lim_plus ;
  [apply derivable_pt_lim_plus|].
  apply (derivable2_pt_lim_derivable_pt_lim_bis (fun t => alpha x t)) ;
    [ intros ; apply alpha01_lim | apply alpha02_lim].
  apply (derivable2_pt_lim_derivable_pt_lim_bis (fun t => beta x t)) ;
    [ intros ; apply beta01_lim | apply beta02_lim].
  apply (derivable2_pt_lim_derivable_pt_lim_bis (fun t => gamma x t)) ;
    [ intros ; apply gamma01_lim | apply gamma02_lim].
Qed.

(** * Vérification des conditions *)

Lemma cond1_sol : Cond1 sol sol20 sol02 sol20_lim sol02_lim.
Proof.
  intros x t.
  unfold sol20, sol02 ;
  unfold alpha20, alpha02 ;
  unfold beta20, beta02 ;
  unfold gamma20, gamma02.
  field ;
  apply Hc.
Qed.

Lemma cond2_sol : Cond2 sol.
Proof.
  intros x.
  unfold sol, alpha, beta, gamma.
  rewrite Rmult_0_r, Rplus_0_r, Rminus_0_r.
  repeat rewrite RiemannInt_P9.
  field ; apply Hc.
Qed.

Lemma cond3_sol : Cond3 sol sol01 sol01_lim.
Proof.
  intros x.
  unfold sol01.
  unfold alpha01, beta01, gamma01.
  rewrite Rmult_0_r, Rplus_0_r, Rminus_0_r.
  repeat rewrite RiemannInt_P9.
  field ; apply Hc.
Qed.

(** * Conclusion *)

Lemma prob_sol : Prob sol sol20 sol02 sol01 sol20_lim sol02_lim sol01_lim.
Proof.
  split ;
  [apply cond1_sol | split].
  apply cond2_sol.
  apply cond3_sol.
Qed.