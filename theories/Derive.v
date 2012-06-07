Require Import Reals.
Require Import ssreflect.
Require Import Lim_fct.
Require Import Locally.
Open Scope R_scope.

(** * Deriv *)

Definition Derive (f : R -> R) (x : R) := Lim (fun h => (f (x+h) - f x)/h) 0.

Notation is_derive f x l := (derivable_pt_lim f x l).
Definition ex_derive f x := exists l, is_derive f x l.

(** ** Compute Deriv *)

Lemma is_derive_unique f x l :
  is_derive f x l -> Derive f x = l.
Proof.
  intros.
  apply (uniqueness_step1 f x).
  apply is_lim_Coq_0.
  apply Lim_correct.
  exists l.
  apply is_lim_Coq_1.
  
  apply uniqueness_step2, H.
  apply uniqueness_step2, H.
Qed.

Lemma Derive_correct f x :
  ex_derive f x -> is_derive f x (Derive f x).
Proof.
    intros (l,H).
  cut (Derive f x = l).
    intros ; rewrite H0 ; apply H.
  apply is_derive_unique, H.
Qed.

(** ** Equality *)

Lemma is_derive_ext_loc :
  forall f g x l,
  locally (fun t => f t = g t) x ->
  is_derive f x l -> is_derive g x l.
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

Lemma is_derive_ext :
  forall f g x l,
  (forall t, f t = g t) ->
  is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq.
apply is_derive_ext_loc.
now apply locally_forall.
Qed.

Lemma ex_derive_ext_loc :
  forall f g x,
  locally (fun t => f t = g t) x ->
  ex_derive f x -> ex_derive g x.
Proof.
intros f g x Hfg (l,Hf).
exists l.
apply: is_derive_ext_loc Hfg Hf.
Qed.

Lemma ex_derive_ext :
  forall f g x,
  (forall t, f t = g t) ->
  ex_derive f x -> ex_derive g x.
Proof.
intros f g x Heq.
apply ex_derive_ext_loc.
now apply locally_forall.
Qed.

Lemma Derive_ext_loc :
  forall f g x,
  locally (fun t => f t = g t) x ->
  Derive f x = Derive g x.
Proof.
intros f g x Hfg.
unfold Derive, Lim, Lim_seq.Lim_seq.
apply Rmult_eq_compat_r, f_equal.
rewrite 2!Sup_seq.LimInf_seq_correct 2!Sup_seq.LimSup_seq_correct.
apply f_equal2.
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

apply Rbar_seq.Rbar_liminf_seq_eq_ge.
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

Lemma Derive_ext :
  forall f g x,
  (forall t, f t = g t) ->
  Derive f x = Derive g x.
Proof.
intros f g x Hfg.
apply Derive_ext_loc.
now apply locally_forall.
Qed.

(** * Operations *)

Lemma ex_derive_opp :
  forall f x, ex_derive f x ->
  ex_derive (fun x => - f x) x.
Proof.
intros f x (df,Df).
exists (-df).
now apply derivable_pt_lim_opp.
Qed.

Lemma Derive_opp :
  forall f x, ex_derive f x ->
  Derive (fun x => - f x) x = - Derive f x.
Proof.
intros f x Df.
apply is_derive_unique.
apply derivable_pt_lim_opp.
now apply Derive_correct.
Qed.

Lemma ex_derive_plus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => f x + g x) x.
Proof.
intros f g x (df,Df) (dg,Dg).
exists (df + dg).
now apply derivable_pt_lim_plus.
Qed.

Lemma Derive_plus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  Derive (fun x => f x + g x) x = Derive f x + Derive g x.
Proof.
intros f g x Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_plus ;
  now apply Derive_correct.
Qed.

Lemma ex_derive_minus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => f x - g x) x.
Proof.
intros f g x (df,Df) (dg,Dg).
exists (df - dg).
now apply derivable_pt_lim_minus.
Qed.

Lemma Derive_minus :
  forall f g x, ex_derive f x -> ex_derive g x ->
  Derive (fun x => f x - g x) x = Derive f x - Derive g x.
Proof.
intros f g x Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_minus ;
  now apply Derive_correct.
Qed.

Lemma ex_derive_scal :
  forall f k x, ex_derive f x ->
  ex_derive (fun x => k * f x) x.
Proof.
intros f k x (df,Df).
exists (k * df).
now apply derivable_pt_lim_scal.
Qed.

Lemma Derive_scal : (* TODO : remove hypothesis *)
  forall f k x, ex_derive f x ->
  Derive (fun x => k * f x) x = k * Derive f x.
Proof.
intros f k x Df.
apply is_derive_unique.
apply derivable_pt_lim_scal.
now apply Derive_correct.
Qed.

Lemma ex_derive_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x -> ex_derive (fun x => f (g x)) x.
Proof.
intros (df,Df) (dg,Dg).
exists (df * dg).
now apply derivable_pt_lim_comp.
Qed.

Lemma Deriv_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x -> Derive (fun x => f (g x)) x = Derive f (g x) * Derive g x.
Proof.
intros Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_comp ;
  now apply Derive_correct.
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
Fixpoint Derive_n (f : R -> R) (n : nat) x :=
  match n with
    | O => f x
    | S n => Derive (Derive_n f n) x
  end.

Definition ex_derive_n f n x :=
  match n with
  | O => True
  | S n => ex_derive (Derive_n f n) x
  end.

Definition is_derive_n f n x l :=
  match n with
  | O => f x = l
  | S n => is_derive (Derive_n f n) x l
  end.

Lemma is_derive_n_unique f n x l :
  is_derive_n f n x l -> Derive_n f n x = l.
Proof.
  case n.
  easy.
  simpl; intros n0 H.
  now apply is_derive_unique.
Qed.

Lemma Derive_n_ext_loc :
  forall f g n x,
  locally (fun t => f t = g t) x ->
  Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
pattern x ; apply locally_singleton.
induction n.
exact Heq.
apply: locally_impl_strong IHn.
apply: locally_align Heq => d Heq y Hy IHn.
now apply Derive_ext_loc.
Qed.

Lemma Derive_n_ext :
  forall f g n x,
  (forall t, f t = g t) ->
  Derive_n f n x = Derive_n g n x.
Proof.
intros f g n x Heq.
apply Derive_n_ext_loc.
now apply locally_forall.
Qed.

Lemma Derive_n_comp: forall f n m x,
  Derive_n (Derive_n f m) n x = Derive_n f (n+m) x.
Proof.
intros f n m.
induction n.
now simpl.
simpl.
intros x.
now apply Derive_ext.
Qed.
