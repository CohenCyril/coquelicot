Require Import Reals.
Require Import ssreflect.
Require Import Lim_fct.
Require Import Locally.
Open Scope R_scope.

(** * Deriv *)

Definition Deriv (f : R -> R) (x : R) := Lim (fun h => (f (x+h) - f x)/h) 0.

Definition is_deriv f x l := derivable_pt_lim f x l.
Definition ex_deriv f x := exists l, is_deriv f x l.

(** ** Compute Deriv *)

Lemma Deriv_correct f x l :
  is_deriv f x l -> Deriv f x = l.
Proof.
  intros.
  apply (uniqueness_step1 f x).
  apply is_lim_Coq_0.
  apply Lim_prop.
  exists l.
  apply is_lim_Coq_1.
  
  apply uniqueness_step2, H.
  apply uniqueness_step2, H.
Qed.

Lemma Deriv_prop f x :
  ex_deriv f x -> is_deriv f x (Deriv f x).
Proof.
    intros (l,H).
  cut (Deriv f x = l).
    intros ; rewrite H0 ; apply H.
  apply Deriv_correct, H.
Qed.

(** ** Equality *)

Lemma is_deriv_eta :
  forall f g x l,
  locally (fun t => f t = g t) x ->
  is_deriv f x l -> is_deriv g x l.
Proof.
intros f g x l Heq Hf.
apply derivable_pt_lim_locally => eps.
move /derivable_pt_lim_locally :Hf => Hf.
apply: locally_impl (Hf eps) => {Hf}.
move: Heq (Heq) => Heq [d Hfg].
exists d => y Hy H Zy.
rewrite -Hfg // -(locally_singleton _ _ Heq).
exact: H.
Qed.

Lemma ex_deriv_eta :
  forall f g x,
  locally (fun t => f t = g t) x ->
  ex_deriv f x -> ex_deriv g x.
Proof.
intros f g x Hfg (l,Hf).
exists l.
apply: is_deriv_eta Hfg Hf.
Qed.

Lemma Deriv_eta :
  forall f g x,
  locally (fun t => f t = g t) x ->
  Deriv f x = Deriv g x.
Proof.
intros f g x Hfg.
unfold Deriv, Lim, Lim_seq.Lim_seq.
apply f_equal.
rewrite 2!Sup_seq.LimSup_seq_correct.
apply Rbar_seq.Rbar_limsup_seq_eq_ge.
destruct Hfg as (e, He).
exists (Zabs_nat (up (/e))).
intros n Hn.
rewrite He.
rewrite He.
easy.
rewrite /Rminus Rplus_opp_r Rabs_R0; apply cond_pos.
(* *)
assert (0 < /e)%R.
apply Rinv_0_lt_compat, cond_pos.
assert (0 < IZR (up (/ e))).
apply Rlt_trans with (1:=H).
apply archimed.
assert (0 < n)%nat.
apply lt_le_trans with (2:=Hn).
apply INR_lt.
simpl.
rewrite INR_IZR_INZ inj_Zabs_nat.
rewrite Zabs_eq.
exact H0.
apply le_IZR.
simpl; now left.
replace (x + (0 + / INR n) - x) with (/ INR n) by ring.
rewrite Rabs_right.
rewrite <- (Rinv_involutive e).
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
exact H.
now apply lt_0_INR.
apply Rlt_le_trans with (IZR (up (/e))).
apply archimed.
apply Rle_trans with (INR (Zabs_nat (up (/ e)))).
right; rewrite INR_IZR_INZ.
rewrite inj_Zabs_nat.
apply f_equal.
apply sym_eq, Zabs_eq.
apply le_IZR.
simpl; now left.
now apply le_INR.
apply sym_not_eq, Rlt_not_eq, cond_pos.
apply Rle_ge; left; apply Rinv_0_lt_compat.
now apply lt_0_INR.
Qed.

(** * Operations *)

Lemma is_deriv_opp :
  forall f x, ex_deriv f x ->
  is_deriv (fun x => - f x) x (- Deriv f x).
Proof.
intros f x Df.
apply derivable_pt_lim_opp.
now apply Deriv_prop.
Qed.

Lemma ex_deriv_opp :
  forall f x, ex_deriv f x ->
  ex_deriv (fun x => - f x) x.
Proof.
intros f x Df.
eexists.
now apply is_deriv_opp.
Qed.

Lemma Deriv_opp :
  forall f x, ex_deriv f x ->
  Deriv (fun x => - f x) x = - Deriv f x.
Proof.
intros f x Df.
apply Deriv_correct.
now apply is_deriv_opp.
Qed.

Lemma is_deriv_plus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  is_deriv (fun x => f x + g x) x (Deriv f x + Deriv g x).
Proof.
intros f g x Df Dg.
apply derivable_pt_lim_plus ; now apply Deriv_prop.
Qed.

Lemma ex_deriv_plus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  ex_deriv (fun x => f x + g x) x.
Proof.
intros f g x Df Dg.
eexists.
now apply is_deriv_plus.
Qed.

Lemma Deriv_plus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  Deriv (fun x => f x + g x) x = Deriv f x + Deriv g x.
Proof.
intros f g x Df Dg.
apply Deriv_correct.
now apply is_deriv_plus.
Qed.

Lemma is_deriv_minus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  is_deriv (fun x => f x - g x) x (Deriv f x - Deriv g x).
Proof.
intros f g x Df Dg.
apply derivable_pt_lim_minus ; now apply Deriv_prop.
Qed.

Lemma ex_deriv_minus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  ex_deriv (fun x => f x - g x) x.
Proof.
intros f g x Df Dg.
eexists.
now apply is_deriv_minus.
Qed.

Lemma Deriv_minus :
  forall f g x, ex_deriv f x -> ex_deriv g x ->
  Deriv (fun x => f x - g x) x = Deriv f x - Deriv g x.
Proof.
intros f g x Df Dg.
apply Deriv_correct.
now apply is_deriv_minus.
Qed.

Lemma is_deriv_scal :
  forall f k x, ex_deriv f x ->
  is_deriv (fun x => k * f x) x (k * Deriv f x).
Proof.
intros f k x Df.
apply derivable_pt_lim_scal.
now apply Deriv_prop.
Qed.

Lemma ex_deriv_scal :
  forall f k x, ex_deriv f x ->
  ex_deriv (fun x => k * f x) x.
Proof.
intros f k x Df.
eexists.
now apply is_deriv_scal.
Qed.

Lemma Deriv_scal :
  forall f k x, ex_deriv f x ->
  Deriv (fun x => k * f x) x = k * Deriv f x.
Proof.
intros f k x Df.
apply Deriv_correct.
now apply is_deriv_scal.
Qed.

Lemma is_deriv_comp (f g : R -> R) (x df dg : R) : 
  is_deriv f (g x) df -> is_deriv g x dg -> is_deriv (fun x => f (g x)) x (df * dg).
Proof.
  intros Hf Hg.
  apply derivable_pt_lim_comp ; auto.
Qed.

Lemma ex_lim_comp (f g : R -> R) (x : R) : 
  ex_deriv f (g x) -> ex_deriv g x -> ex_deriv (fun x => f (g x)) x.
Proof.
  intros.
  exists (Deriv f (g x) * Deriv g x) ; apply is_deriv_comp.
  apply Deriv_prop, H.
  apply Deriv_prop, H0.
Qed.

Lemma Deriv_comp (f g : R -> R) (x : R) :
  ex_deriv f (g x) -> ex_deriv g x -> Deriv (fun x => f (g x)) x = Deriv f (g x) * Deriv g x.
Proof.
  intros.
  apply Deriv_correct.
  apply is_deriv_comp.
  apply Deriv_prop, H.
  apply Deriv_prop, H0.
Qed.

Lemma is_deriv_CL (f g : R -> R) (a x lf lg : R) :
  is_deriv f x lf -> is_deriv g x lg -> is_deriv (fun x => f x + a * g x) x (lf + a * lg).
Proof.
  intros Hf Hg.
  apply derivable_pt_lim_plus.
  apply Hf.
  apply derivable_pt_lim_scal, Hg.
Qed.

Lemma ex_deriv_CL (f g : R -> R) (a x : R) :
  ex_deriv f x -> ex_deriv g x -> ex_deriv (fun x => f x + a * g x) x.
Proof.
  intros (lf,Hf) (lg,Hg).
  exists (lf + a * lg) ; apply is_deriv_CL ; [apply Hf | apply Hg].
Qed.

Lemma Deriv_CL (f g : R -> R) (a x : R) :
  ex_deriv f x -> ex_deriv g x -> Deriv (fun x => f x + a * g x) x = Deriv f x + a * Deriv g x.
Proof.
  intros.
  apply Deriv_correct.
  apply is_deriv_CL ; apply Deriv_prop.
  apply H.
  apply H0.
Qed.

Lemma derivable_pt_lim_sum_f_R0 f d n x :
  (forall k, (k <= n)%nat -> derivable_pt_lim (fun u => f k u) x (d k)) ->
  derivable_pt_lim (fun u => sum_f_R0 (fun k => f k u) n) x (sum_f_R0 d n).
Proof.
induction n.
intros H.
simpl.
now apply H.
intros H.
simpl.
apply derivable_pt_lim_plus with (f2 := (fun u => f (S n) u)).
apply IHn => k Hk.
apply H.
now apply le_S.
now apply H.
Qed.

(** * nth deriv *)
Fixpoint Deriv_n (f : R -> R) (n : nat) x :=
  match n with
    | O => f x
    | S n => Deriv (Deriv_n f n) x
  end.

Definition ex_deriv_n f n x :=
  match n with
  | O => True
  | S n => ex_deriv (Deriv_n f n) x
  end.

Definition is_deriv_n f n x l :=
  match n with
  | O => f x = l
  | S n => is_deriv (Deriv_n f n) x l
  end.

Lemma Deriv_n_correct f n x l :
  is_deriv_n f n x l -> Deriv_n f n x = l.
Proof.
  case n.
  easy.
  simpl; intros n0 H.
  apply Deriv_correct, H.
Qed.

Lemma Deriv_n_eta :
  forall f g n x,
  locally (fun t => f t = g t) x ->
  Deriv_n f n x = Deriv_n g n x.
Proof.
intros f g n x Heq.
pattern x ; apply locally_singleton.
induction n.
exact Heq.
apply: locally_impl_strong IHn.
apply: locally_align Heq => d Heq y Hy IHn.
now apply Deriv_eta.
Qed.

Lemma Deriv_n_comp: forall f n m x,
  Deriv_n (Deriv_n f m) n x = Deriv_n f (n+m) x.
Proof.
intros f n m.
induction n.
now simpl.
simpl.
intros x.
apply Deriv_eta.
now apply locally_forall.
Qed.
