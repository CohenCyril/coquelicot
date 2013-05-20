Require Import Reals Rbar_theory.
Require Import Lim_seq ssreflect.
Require Import Locally.
Open Scope R_scope.

(** * Limit *)
Definition Lim (f : R -> R) (x : R) := real (Lim_seq (fun n => f (Rbar_loc_seq x n))).

Definition is_lim f x l :=
  forall eps : posreal, locally (fun y => y <> x -> Rabs (f y - l) < eps) x.
Definition ex_lim f x := exists l, is_lim f x l.

(** ** Equivalence with Coq definition *)

Lemma is_lim_Coq_0 f x l :
  is_lim f x l -> limit1_in f (fun y => y <> x) l x.
Proof.
  intros H e He ; set (eps := mkposreal e He).
  elim (H eps) ; clear H ; intros (d,Hd) H.
  exists d ; split ; [apply Hd | ].
  intros y Hy ; apply (H y) ; apply Hy.
Qed.
Lemma is_lim_Coq_1 f x l :
  limit1_in f (fun y => y <> x) l x -> is_lim f x l.
Proof.
  intros H (e,He).
  elim (H e He) ; clear H ; intros d (Hd,H) ; set (delta := mkposreal d Hd).
  exists delta ; intros ; apply (H y).
  now split.
Qed.
Lemma is_lim_Coq f x l :
  limit1_in f (fun y => y <> x) l x <-> is_lim f x l.
Proof.
  split ; [apply is_lim_Coq_1|apply is_lim_Coq_0].
Qed.

(** ** Compute limit *)

Lemma is_lim_comp_seq f x l :
  is_lim f x l -> forall u : nat -> R, 
    (exists N, forall n, (N <= n)%nat -> u n <> x) ->
    is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
  intros Hf u (N,Hu) Hu' eps.
  elim (Hf eps) ; clear Hf ; intros delta Hf.
  elim (Hu' delta) ; clear Hu' ; intros N' Hu'.
  exists (N+N')%nat ; intros ; apply Hf.
  apply Hu', le_trans with (2 := H) ; intuition.
  apply Hu, le_trans with (2 := H) ; intuition.
Qed.

Lemma is_lim_unique f x l :
  is_lim f x l -> Lim f x = l.
Proof.
  intros.
  unfold Lim.
  rewrite (is_lim_seq_unique _ l) //.
  apply (is_lim_comp_seq f x l H).
  exists 1%nat ; intros ; apply Rgt_not_eq, Rlt_gt ;
  pattern x at 1 ; rewrite <- Rplus_0_r ; apply Rplus_lt_compat_l.
  apply Rinv_0_lt_compat, Rcomplements.INRp1_pos.
  rewrite -{2}(Rplus_0_r x).
  apply (is_lim_seq_plus (fun n => x) (fun n => /(INR n+1)) x 0).
  apply is_lim_seq_const.
  replace (Finite 0) with (Rbar_inv p_infty) by auto.
  apply is_lim_seq_inv => //.
  apply (is_lim_seq_plus _ _ p_infty (Finite 1)) => //.
  apply Rbar_is_lim_seq_id.
  apply is_lim_seq_const.
  simpl ; ring.
Qed.
Lemma Lim_correct f x :
  ex_lim f x -> is_lim f x (Lim f x).
Proof.
  intros (l,H).
  replace (Lim f x) with l.
    apply H.
  apply sym_eq, is_lim_unique, H.
Qed.

(** * Operations *)

Lemma is_lim_comp (f g : R -> R) (x l : R) : 
  is_lim f l (f l) -> is_lim g x l -> is_lim (fun x => f (g x)) x (f l).
Proof.
  intros Hf Hg eps.
  move: (Hf eps) => {Hf}[d0 Hf].
  move: (Hg d0) => {Hg}[delta Hg].
  exists delta ; intros.
  destruct (Req_EM_T (g y) l).
  rewrite e (Rminus_diag_eq _ _ (refl_equal _)) Rabs_R0 ; apply eps.
  apply: Hf n.
  apply (Hg _ H H0).
Qed.
Lemma ex_lim_comp (f g : R -> R) (x : R) : 
  is_lim f (Lim g x) (f (Lim g x)) -> ex_lim g x -> ex_lim (fun x => f (g x)) x.
Proof.
  intros.
  exists (f (Lim g x)) ; apply is_lim_comp.
  apply H.
  apply Lim_correct, H0.
Qed.
Lemma Lim_comp (f g : R -> R) (x : R) : 
  is_lim f (Lim g x) (f (Lim g x)) -> ex_lim g x -> Lim (fun x => f (g x)) x = f (Lim g x).
Proof.
  intros.
  apply is_lim_unique.
  apply is_lim_comp.
  apply H.
  apply Lim_correct, H0.
Qed.

Lemma is_lim_CL (f g : R -> R) (a x lf lg : R) :
  is_lim f x lf -> is_lim g x lg -> is_lim (fun x => f x + a * g x) x (lf + a * lg).
Proof.
  intros Hf Hg e0.
  assert (He : 0 < e0 / (1 + Rabs a)) ;
  [ unfold Rdiv ; apply Rmult_lt_0_compat ; [apply e0 | apply Rinv_0_lt_compat] ;
    apply Rlt_le_trans with (1 := Rlt_0_1) ; rewrite -{1}(Rplus_0_r 1) ;
    apply Rplus_le_compat_l, Rabs_pos
  | set (eps := mkposreal _ He)].
  move: (locally_and _ _ _ (Hf eps) (Hg eps)) => {Hf Hg}.
  apply locally_impl.
  apply locally_forall.
  intros y (Hf,Hg) H0.
  replace (f y + a * g y - (lf + a * lg)) with ((f y - lf) + a * (g y - lg)) by ring.
  replace (pos e0) with (eps + Rabs a * eps).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_le_compat.
  apply: Hf H0.
  rewrite Rabs_mult ; apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le.
  apply: Hg H0.
  simpl ; field ; apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1) ;
  rewrite -{1}(Rplus_0_r 1) ; apply Rplus_le_compat_l, Rabs_pos.
Qed.
Lemma ex_lim_CL (f g : R -> R) (a x : R) :
  ex_lim f x -> ex_lim g x -> ex_lim (fun x => f x + a * g x) x.
Proof.
  intros (lf,Hf) (lg,Hg).
  exists (lf + a * lg) ; apply is_lim_CL ; [apply Hf | apply Hg].
Qed.
Lemma Lim_CL (f g : R -> R) (a x : R) :
  ex_lim f x -> ex_lim g x -> Lim (fun x => f x + a * g x) x = Lim f x + a * Lim g x.
Proof.
  intros.
  apply is_lim_unique.
  apply is_lim_CL ; apply Lim_correct.
  apply H.
  apply H0.
Qed.

