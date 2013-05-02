Require Import Reals.
Require Import ssreflect.
Require Import Lim_seq Lim_fct.
Require Import Locally.
Require Import Rcomplements.
Open Scope R_scope.

(** * Definitions *)

Notation is_derive f x l := (derivable_pt_lim f x l).
Definition ex_derive f x := exists l, is_derive f x l.
Definition Derive (f : R -> R) (x : R) := Lim (fun h => (f (x+h) - f x)/h) 0.

(** Derive is correct *)

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

Lemma ex_derive_equiv_0 (f : R -> R) (x : R) :
  ex_derive f x -> derivable_pt f x.
Proof.
  move => Hf.
  apply Derive_correct in Hf.
  by exists (Derive f x).
Qed.
Lemma ex_derive_equiv_1 (f : R -> R) (x : R) :
  derivable_pt f x -> ex_derive f x.
Proof.
  case => l Hf.
  by exists l.
Qed.

Lemma Derive_equiv (f : R -> R) (x : R) (pr : derivable_pt f x) :
  derive_pt f x pr = Derive f x.
Proof.
  apply sym_eq, is_derive_unique.
  by case: pr => /= l Hf.
Qed.

(** Extensionality *)

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
Lemma ex_derive_ext_loc :
  forall f g x,
  locally (fun t => f t = g t) x ->
  ex_derive f x -> ex_derive g x.
Proof.
intros f g x Hfg (l,Hf).
exists l.
apply: is_derive_ext_loc Hfg Hf.
Qed.
Lemma Derive_ext_loc :
  forall f g x,
  locally (fun t => f t = g t) x ->
  Derive f x = Derive g x.
Proof.
intros f g x Hfg.
unfold Derive, Lim, Lim_seq.
apply Rmult_eq_compat_r, f_equal.
rewrite 2!Sup_seq.LimInf_seq_correct 2!Sup_seq.LimSup_seq_correct.
apply f_equal2.
apply Rbar_seq.Rbar_limsup_seq_ext_loc.
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

apply Rbar_seq.Rbar_liminf_seq_ext_loc.
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

Lemma is_derive_ext :
  forall f g x l,
  (forall t, f t = g t) ->
  is_derive f x l -> is_derive g x l.
Proof.
intros f g x l Heq.
apply is_derive_ext_loc.
now apply locally_forall.
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
(** Constant functions *)

Lemma ex_derive_const :
  forall a x, ex_derive (fun _ => a) x.
Proof.
intros x.
exists 0.
apply derivable_pt_lim_const.
Qed.
Lemma Derive_const :
  forall a x,
  Derive (fun _ => a) x = 0.
Proof.
intros a x.
apply is_derive_unique.
apply derivable_pt_lim_const.
Qed.

(** Identity function *)

Lemma ex_derive_id :
  forall x, ex_derive id x.
Proof.
intros x.
exists 1.
apply derivable_pt_lim_id.
Qed.
Lemma Derive_id :
  forall x,
  Derive id x = 1.
Proof.
intros x.
apply is_derive_unique.
apply derivable_pt_lim_id.
Qed.

(** Opposite of functions *)

Lemma ex_derive_opp :
  forall f x, ex_derive f x ->
  ex_derive (fun x => - f x) x.
Proof.
intros f x (df,Df).
exists (-df).
now apply derivable_pt_lim_opp.
Qed.
Lemma Derive_opp :
  forall f x,
  Derive (fun x => - f x) x = - Derive f x.
Proof.
intros f x.
unfold Derive, Lim.
rewrite -Lim_seq_opp.
apply Lim_seq_ext => n.
rewrite -Ropp_mult_distr_l_reverse.
apply (f_equal (fun v => v / _)).
ring.
Qed.

(** Addition of functions *)

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

Lemma is_derive_sum (f : nat -> R -> R) (n : nat) (x : R) (l : nat -> R) :
  (forall k, (k <= n)%nat -> is_derive (f k) x (l k))
  -> is_derive (fun y => sum_f_R0 (fun k => f k y) n) x (sum_f_R0 l n).
Proof.
  elim: n => /= [ | n IH] Hf.
  by apply (Hf O).
  apply derivable_pt_lim_plus.
  apply IH => k Hk.
  by apply Hf, le_trans with (1 := Hk), le_n_Sn.
  by apply Hf.
Qed.
Lemma ex_derive_sum (f : nat -> R -> R) (n : nat) (x : R) :
  (forall k, (k <= n)%nat -> ex_derive (f k) x)
  -> ex_derive (fun y => sum_f_R0 (fun k => f k y) n) x.
Proof.
  elim: n => /= [ | n IH] Hf.
  by apply (Hf O).
  apply ex_derive_plus.
  apply IH => k Hk.
  by apply Hf, le_trans with (1 := Hk), le_n_Sn.
  by apply Hf.
Qed.
Lemma Derive_sum (f : nat -> R -> R) (n : nat) (x : R) :
  (forall k, (k <= n)%nat -> ex_derive (f k) x)
  -> Derive (fun y => sum_f_R0 (fun k => f k y) n) x = (sum_f_R0 (fun k => Derive (f k) x) n).
Proof.
  move => Hf.
  apply is_derive_unique, is_derive_sum.
  move => k Hk.
  by apply Derive_correct, Hf.
Qed.

(** Difference of functions *)

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

(** Multiplication of functions *)

Lemma ex_derive_scal :
  forall f k x, ex_derive f x ->
  ex_derive (fun x => k * f x) x.
Proof.
intros f k x (df,Df).
exists (k * df).
now apply derivable_pt_lim_scal.
Qed.
Lemma Derive_scal :
  forall f k x,
  Derive (fun x => k * f x) x = k * Derive f x.
Proof.
intros f k x.
unfold Derive, Lim.
rewrite -Lim_seq_scal.
apply Lim_seq_ext => n.
rewrite -Rmult_assoc.
apply (f_equal (fun v => v / _)).
ring.
Qed.

Lemma ex_derive_mult (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x
    -> ex_derive (fun x => f x * g x) x.
Proof.
  move => [d1 H1] [d2 H2].
  exists (d1 * g x + f x * d2) ; exact: derivable_pt_lim_mult.
Qed.
Lemma Derive_mult (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x
    -> Derive (fun x => f x * g x) x = Derive f x * g x + f x * Derive g x.
Proof.
  move => H1 H2.
  apply is_derive_unique.
  apply derivable_pt_lim_mult ; exact: Derive_correct.
Qed.

Lemma is_derive_pow (f : R -> R) (n : nat) (x : R) (l : R) :
  is_derive f x l -> is_derive (fun x => (f x)^n) x (INR n * l * (f x)^(pred n)).
Proof.
  move => H.
  rewrite (Rmult_comm _ l) Rmult_assoc Rmult_comm.
  apply (derivable_pt_lim_comp f (fun x => x^n)).
  by apply H.
  by apply derivable_pt_lim_pow.
Qed.
Lemma ex_derive_pow (f : R -> R) (n : nat) (x : R) :
  ex_derive f x -> ex_derive (fun x => (f x)^n) x.
Proof.
  case => l H.
  exists (INR n * l * (f x)^(pred n)).
  by apply is_derive_pow.
Qed.
Lemma Derive_pow (f : R -> R) (n : nat) (x : R) :
  ex_derive f x -> Derive (fun x => (f x)^n) x = (INR n * Derive f x * (f x)^(pred n)).
Proof.
  move => H.
  apply is_derive_unique.
  apply is_derive_pow.
  by apply Derive_correct.
Qed.

(** Composition of functions *)

Lemma ex_derive_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x 
    -> ex_derive (fun x => f (g x)) x.
Proof.
intros (df,Df) (dg,Dg).
exists (df * dg).
now apply derivable_pt_lim_comp.
Qed.
Lemma Derive_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x 
    -> Derive (fun x => f (g x)) x = Derive f (g x) * Derive g x.
Proof.
intros Df Dg.
apply is_derive_unique.
apply derivable_pt_lim_comp ;
  now apply Derive_correct.
Qed.

(** * Mean value theorem *)

Lemma MVT_gen (f : R -> R) (a b : R) :
  let a0 := Rmin a b in
  let b0 := Rmax a b in
  (forall x, a0 < x < b0 -> ex_derive f x)
  -> (forall x, a0 <= x <= b0 -> continuity_pt f x)
  -> exists c, a0 <= c <= b0 /\ f b - f a = Derive f c * (b - a).
Proof.
  move => a0 b0 Hd Hf.
  case: (Req_dec a0 b0) => Hab.
  exists a0 ; split.
  split ; by apply Req_le.
  replace b with a.
  ring.
  move: Hab ; rewrite /a0 /b0 /Rmin /Rmax ; by case: Rle_dec => Hab.
  have pr1 : forall c:R, a0 < c < b0 -> derivable_pt f c.
    move => x Hx ; exists (Derive f x).
    by apply Derive_correct, Hd.
  have pr2 : forall c:R, a0 < c < b0 -> derivable_pt id c.
    move => x Hx ; exists 1.
    by apply derivable_pt_lim_id.
  case: (MVT f id a0 b0 pr1 pr2).
  apply Rnot_le_lt ; contradict Hab ; apply Rle_antisym.
  by apply Rcomplements.Rmin_Rmax.
  by apply Hab.
  by apply Hf.
  move => x Hx ; apply derivable_continuous, derivable_id.
  move => /= c [Hc H].
  exists c ; split.
  split ; by apply Rlt_le, Hc.
  replace (Derive f c) with (derive_pt f c (pr1 c Hc)).
  move: H ; rewrite {1 2}/id /a0 /b0 /Rmin /Rmax ; 
  case: Rle_dec => Hab0 H.
  rewrite Rmult_comm H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
  ring.
  replace (derive_pt f c (pr1 c Hc) * (b - a))
    with (-((a - b) * derive_pt f c (pr1 c Hc)))
    by ring.
  rewrite H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
  ring.
  case: (pr1 c Hc) => /= l Hl.
  apply sym_eq, is_derive_unique, Hl.
Qed.

(** * Newton integration *)

Lemma fn_eq_Derive_eq: forall f g a b, 
  continuity_pt f a -> continuity_pt f b ->
  continuity_pt g a -> continuity_pt g b -> 
  (forall x, a < x < b -> ex_derive f x) ->
  (forall x, a < x < b -> ex_derive g x) ->
  (forall x, a < x < b -> Derive f x = Derive g x) ->
  exists C, forall x, a <= x <= b -> f x = g x + C.
Proof.
intros f g a b Cfa Cfb Cga Cgb Df Dg Hfg.
pose (h := fun x => f x - g x).
assert  (pr : forall x : R, a < x < b -> derivable_pt h x).
intros x Hx.
apply derivable_pt_minus.
eexists; apply Derive_correct, Df, Hx.
eexists; apply Derive_correct, Dg, Hx.
assert (constant_D_eq h (fun x : R => a <= x <= b) (h a)).
apply null_derivative_loc with (pr:=pr).
intros x Hx.
case (proj1 Hx).
case (proj2 Hx).
intros Y1 Y2.
apply derivable_continuous_pt.
apply pr; now split.
intros Y1 _; rewrite Y1.
apply continuity_pt_minus.
apply Cfb.
apply Cgb.
intros Y1; rewrite <- Y1.
apply continuity_pt_minus.
apply Cfa.
apply Cga.
intros x P.
apply trans_eq with (Derive h x).
apply sym_eq, is_derive_unique.
now destruct (pr x P).
rewrite Derive_minus.
rewrite (Hfg _ P).
ring.
apply Df; split; apply P.
apply Dg; split; apply P.
unfold constant_D_eq in H.
exists (h a).
intros x Hx.
rewrite <- (H _ Hx).
unfold h; ring.
Qed.

(** * Iterated differential *)

(** ** Definition *)

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
Lemma Derive_n_correct f n x :
  ex_derive_n f n x -> is_derive_n f n x (Derive_n f n x).
Proof.
  case: n => /= [ | n] Hf.
  by [].
  by apply Derive_correct.
Qed.

(** Extentionality *)

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
Lemma ex_derive_n_ext_loc :
  forall f g n x,
  locally (fun t => f t = g t) x ->
  ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
case: n => /= [ | n].
by [].
apply ex_derive_ext_loc.
move: Heq.
apply: locally_impl_strong.
apply locally_forall.
by apply Derive_n_ext_loc.
Qed.
Lemma is_derive_n_ext_loc :
  forall f g n x l,
  locally (fun t => f t = g t) x ->
  is_derive_n f n x l -> is_derive_n g n x l.
Proof.
  intros f g n x l Heq.
  case: n => /= [ | n].
  move => <- ; apply sym_eq ;
  pattern x ; by apply locally_singleton.
  apply is_derive_ext_loc.
  move: Heq ; apply: locally_impl_strong.
  apply locally_forall.
  by apply Derive_n_ext_loc.
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
Lemma ex_derive_n_ext :
  forall f g n x,
  (forall t, f t = g t) ->
  ex_derive_n f n x -> ex_derive_n g n x.
Proof.
intros f g n x Heq.
apply ex_derive_n_ext_loc.
now apply locally_forall.
Qed.
Lemma is_derive_n_ext :
  forall f g n x l,
  (forall t, f t = g t) ->
  is_derive_n f n x l -> is_derive_n g n x l.
Proof.
intros f g n x l Heq.
apply is_derive_n_ext_loc.
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

(** ** Operations *)
(** Addition of functions *)

Lemma Derive_n_plus (f g : R -> R) (n : nat) (x : R) :
  locally (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) x ->
  locally (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) x ->
  Derive_n (fun x => f x + g x) n x = Derive_n f n x + Derive_n g n x.
Proof.
  elim: n x => /= [ | n IH] x [rf Hf] [rg Hg].
  by [].
  rewrite -Derive_plus.
  apply Derive_ext_loc.
  set r := (mkposreal _ (Rmin_stable_in_posreal rf rg)) ;
  exists r => y Hy.
  apply Rabs_lt_between' in Hy.
  case: Hy ; move/Rlt_Rminus => Hy1 ; move/Rlt_Rminus => Hy2.
  set r0 := mkposreal _ (Rmin_pos _ _ Hy1 Hy2).
  apply IH ;
  exists r0 => z Hz k Hk.
  apply Hf.
  apply Rabs_lt_between' in Hz.
  rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l (Rplus_min_distr_l y) in Hz.
  case: Hz ; move => Hz1 Hz2.
  apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1 ; ring_simplify in Hz1.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2 ; ring_simplify in Hz2.
  have Hz := (conj Hz1 Hz2) => {Hz1 Hz2}.
  apply Rabs_lt_between' in Hz.
  apply Rlt_le_trans with (1 := Hz) => /= ; by apply Rmin_l.
  by apply le_trans with (1 := Hk), le_n_Sn.
  apply Hg.
  apply Rabs_lt_between' in Hz.
  rewrite /Rminus -Rmax_opp_Rmin Rplus_max_distr_l (Rplus_min_distr_l y) in Hz.
  case: Hz ; move => Hz1 Hz2.
  apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1 ; ring_simplify in Hz1.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2 ; ring_simplify in Hz2.
  have Hz := (conj Hz1 Hz2) => {Hz1 Hz2}.
  apply Rabs_lt_between' in Hz.
  apply Rlt_le_trans with (1 := Hz) => /= ; by apply Rmin_r.
  by apply le_trans with (1 := Hk), le_n_Sn.
  apply Hf with (k := (S n)).
  rewrite Rminus_eq0 Rabs_R0 ; by apply rf.
  by apply le_refl.
  apply Hg with (k := S n).
  rewrite Rminus_eq0 Rabs_R0 ; by apply rg.
  by apply le_refl.  
Qed.
Lemma ex_derive_n_plus (f g : R -> R) (n : nat) (x : R) :
  locally (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) x ->
  locally (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) x ->
  ex_derive_n (fun x => f x + g x) n x.
Proof.
  case: n x => /= [ | n] x Hf Hg.
  by [].
  apply ex_derive_ext_loc with (fun y => Derive_n f n y + Derive_n g n y).
  move: Hf ; apply locally_impl_strong.
  move: Hg ; apply locally_impl_strong.
  apply locally_forall => y Hg Hf.
  apply sym_eq, Derive_n_plus.
  move: Hf ; apply locally_impl, locally_forall ; by intuition.
  move: Hg ; apply locally_impl, locally_forall ; by intuition.
  apply ex_derive_plus.
  apply locally_singleton ; move: Hf ; apply locally_impl, locally_forall => y Hy.
  by apply (Hy (S n)).
  apply locally_singleton ; move: Hg ; apply locally_impl, locally_forall => y Hy.
  by apply (Hy (S n)).
Qed.
Lemma is_derive_n_plus (f g : R -> R) (n : nat) (x lf lg l : R) :
  locally (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y) x ->
  locally (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y) x ->
  is_derive_n f n x lf -> is_derive_n g n x lg ->
  l = lf + lg ->
  is_derive_n (fun x => f x + g x) n x l.
Proof.
  case: n x lf lg l => /= [ | n] x lf lg l Hfn Hgn Hf Hg ->.
  by rewrite Hf Hg.
  apply is_derive_ext_loc with (fun y => Derive_n f n y + Derive_n g n y).
  move: Hfn ; apply locally_impl_strong.
  move: Hgn ; apply locally_impl_strong.
  apply locally_forall => y Hgn Hfn.
  apply sym_eq, Derive_n_plus.
  move: Hfn ; apply locally_impl, locally_forall ; by intuition.
  move: Hgn ; apply locally_impl, locally_forall ; by intuition.
  by apply derivable_pt_lim_plus.
Qed.

(** Multiplication *)

Lemma Derive_n_scal (f : R -> R) (n : nat) (a x : R) :
  Derive_n (fun y => a * f y) n x = a * Derive_n f n x.
Proof.
  elim: n x => /= [ | n IH] x.
  by [].
  rewrite -Derive_scal.
  by apply Derive_ext.
Qed.
Lemma ex_derive_n_scal (f : R -> R) (n : nat) (a x : R) :
  ex_derive_n f n x -> ex_derive_n (fun y => a * f y) n x.
Proof.
  case: n x => /= [ | n] x Hf.
  by [].
  apply ex_derive_ext with (fun y => a * Derive_n f n y).
  move => t ; by rewrite Derive_n_scal.
  by apply ex_derive_scal.
Qed.
Lemma is_derive_n_scal (f : R -> R) (n : nat) (a x l : R) :
  is_derive_n f n x l -> is_derive_n (fun y => a * f y) n x (a * l).
Proof.
  case: n x => /= [ | n] x Hf.
  by rewrite Hf.
  apply is_derive_ext with (fun y => a * Derive_n f n y).
  move => t ; by rewrite Derive_n_scal.
  by apply derivable_pt_lim_scal.
Qed.

(** Simpl cases for Composition of functions *)

Lemma Derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) :
  locally (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) (a * x) ->
  Derive_n (fun y => f (a * y)) n x  = (a ^ n * Derive_n f n (a * x)).
Proof.
  case: (Req_dec a 0) => [ -> _ | Ha] /=.
  rewrite Rmult_0_l.
  elim: n x => [ | n IH] x /= ; rewrite ?Rmult_0_l.
  ring.
  rewrite (Derive_ext _ _ _ IH).
  by apply Derive_const.

  move => Hf.
  apply (locally_singleton (fun x => Derive_n (fun y : R => f (a * y)) n x = a ^ n * Derive_n f n (a * x))).
  elim: n Hf => [ | n IH] Hf.
  apply locally_forall => /= y ; ring.

  case: IH => [ | r IH].
  case: Hf => r0 Hf.
  exists r0 => y Hy k Hk ; by intuition.
  case: Hf => r0 Hf.
  have Hr1 : 0 < Rmin (r0 / (Rabs a)) r.
    apply Rmin_case.
    apply Rdiv_lt_0_compat.
    by apply r0.
    by apply Rabs_pos_lt.
    by apply r.
  set r1 := mkposreal _ Hr1.
  exists r1 => y Hy /=.
  rewrite (Derive_ext_loc _ (fun y => a ^ n * Derive_n f n (a * y))).
  rewrite Derive_scal.
  rewrite (Rmult_comm a (a^n)) Rmult_assoc.
  apply f_equal.
  rewrite Derive_comp.
  rewrite (Derive_ext (Rmult a) (fun x => a * x)) => //.
  rewrite Derive_scal Derive_id ; ring.
  apply Hf with (k := S n).
  rewrite -Rmult_minus_distr_l Rabs_mult.
  apply Rlt_le_trans with (Rabs a * r1).
  apply Rmult_lt_compat_l.
  by apply Rabs_pos_lt.
  by apply Hy.
  rewrite Rmult_comm ; apply Rle_div_r.
  by apply Rabs_pos_lt.
  rewrite /r1 ; by apply Rmin_l.
  by apply lt_n_Sn.
  apply ex_derive_ext with (2 := ex_derive_scal id a y (ex_derive_id _)).
  by [].
  apply Rabs_lt_between' in Hy.
  case: Hy => Hy1 Hy2.
  apply Rlt_Rminus in Hy1.
  apply Rlt_Rminus in Hy2.
  have Hy : 0 < Rmin (y - (x - r1)) (x + r1 - y).
  by apply Rmin_case.
  exists (mkposreal (Rmin (y - (x - r1)) (x + r1 - y)) Hy).
  set r2 := Rmin (y - (x - r1)) (x + r1 - y).
  move => t Ht.
  apply IH.
  apply Rabs_lt_between'.
  apply Rabs_lt_between' in Ht.
  simpl in Ht.
  split.
  apply Rle_lt_trans with (2 := proj1 Ht).
  rewrite /r2 ; apply Rle_trans with (y-(y-(x-r1))).
  ring_simplify ; apply Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /r1 ; apply Rmin_r.
  apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_l.
  apply Rlt_le_trans with (1 := proj2 Ht).
  rewrite /r2 ; apply Rle_trans with (y+((x+r1)-y)).
  apply Rplus_le_compat_l, Rmin_r.
  ring_simplify ; apply Rplus_le_compat_l.
  rewrite /r1 ; apply Rmin_r.
Qed.
Lemma ex_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) :
  locally (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) (a * x)
  -> ex_derive_n (fun y => f (a * y)) n x.
Proof.
  case: n f x => /= [ | n] f x Hf.
  by [].
  
  case: (Req_dec a 0) => Ha.
  rewrite Ha => {a Ha Hf}.
  apply ex_derive_ext with (fun _ => Derive_n (fun y : R => f (0 * y)) n 0).
  elim: n => /= [ | n IH] t.
  by rewrite ?Rmult_0_l.
  rewrite -?(Derive_ext _ _ _ IH).
  by rewrite ?Derive_const.
  by apply ex_derive_const.
  
  apply ex_derive_ext_loc with (fun x => a^n * Derive_n f n (a * x)).
  case: Hf => r Hf.
  have Hr0 : 0 < r / Rabs a.
    apply Rdiv_lt_0_compat.
    by apply r.
    by apply Rabs_pos_lt.
  exists (mkposreal _ Hr0) => /= y Hy.
  apply eq_sym, Derive_n_comp_scal.
  have : Rabs (a*y - a*x) < r.
    rewrite -Rmult_minus_distr_l Rabs_mult.
    replace (pos r) with (Rabs a * (r / Rabs a))
      by (field ; by apply Rgt_not_eq, Rabs_pos_lt).
    apply Rmult_lt_compat_l.
    by apply Rabs_pos_lt.
    by apply Hy.
    move => {Hy} Hy.
  apply Rabs_lt_between' in Hy ; case: Hy => Hy1 Hy2.
  apply Rlt_Rminus in Hy1.
  apply Rlt_Rminus in Hy2.
  exists (mkposreal _ (Rmin_pos _ _ Hy1 Hy2)) => /= z Hz k Hk.
  apply Rabs_lt_between' in Hz ; case: Hz => Hz1 Hz2.
  rewrite /Rminus -Rmax_opp_Rmin in Hz1.
  rewrite Rplus_min_distr_l in Hz2.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2.
  ring_simplify in Hz2.
  rewrite Rplus_max_distr_l in Hz1.
  apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1.
  ring_simplify in Hz1.
  apply Hf.
  apply Rabs_lt_between' ; by split.
  by intuition.
  apply ex_derive_scal.
  apply ex_derive_comp.
  apply locally_singleton in Hf.
  by apply Hf with (k := S n).
  apply ex_derive_ext with (2 := ex_derive_scal id a x (ex_derive_id _)).
  by [].
Qed.
Lemma is_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x l : R) :
  locally (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) (a * x)
  -> is_derive_n f n (a * x) l
  -> is_derive_n (fun y => f (a * y)) n x (a ^ n * l).
Proof.
  case: n => /= [ | n] Hfn Hf.
  by rewrite Rmult_1_l.
  apply is_derive_unique in Hf.
  rewrite -Hf.
  rewrite -(Derive_n_comp_scal f a (S n) x) => //.
  apply Derive_correct.
  by apply (ex_derive_n_comp_scal f a (S n) x).
Qed.

Lemma Derive_n_comp_opp (f : R -> R) (n : nat) (x : R) :
  locally (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) (- x) ->
  Derive_n (fun y => f (- y)) n x  = ((-1) ^ n * Derive_n f n (-x)).
Proof.
  move => Hf.
  rewrite -(Derive_n_ext (fun y : R => f (-1 * y))).
  rewrite (Derive_n_comp_scal f (-1) n x).
  by replace (-1*x) with (-x) by ring.
  by replace (-1*x) with (-x) by ring.
  move => t ; by replace (-1*t) with (-t) by ring.
Qed.
Lemma ex_derive_n_comp_opp (f : R -> R) (n : nat) (x : R) :
  locally (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) (- x) ->
  ex_derive_n (fun y => f (- y)) n x.
Proof.
  move => Hf.
  apply (ex_derive_n_ext (fun y : R => f (-1 * y))).
  move => t ; by ring_simplify (-1*t).
  apply (ex_derive_n_comp_scal f (-1) n x).
  by replace (-1*x) with (-x) by ring.
Qed.
Lemma is_derive_n_comp_opp (f : R -> R) (n : nat) (x l : R) :
  locally (fun y => (forall k, (k <= n)%nat -> ex_derive_n f k y)) (- x) ->
  is_derive_n f n (-x) l ->
  is_derive_n (fun y => f (- y)) n x ((-1)^n * l).
Proof.
  move => Hfn Hf.
  apply (is_derive_n_ext (fun y : R => f (-1 * y))).
  move => t ; by ring_simplify (-1*t).
  apply (is_derive_n_comp_scal f (-1) n x).
  by replace (-1*x) with (-x) by ring.
  by replace (-1*x) with (-x) by ring.
Qed.
