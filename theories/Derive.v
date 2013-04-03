Require Import Reals.
Require Import ssreflect.
Require Import Lim_seq Lim_fct.
Require Import Locally.
Require Import Rcomplements.
Open Scope R_scope.

(** * Derive *)

Definition Derive (f : R -> R) (x : R) := Lim (fun h => (f (x+h) - f x)/h) 0.

Notation is_derive f x l := (derivable_pt_lim f x l).
Definition ex_derive f x := exists l, is_derive f x l.

(** ** Compute Derive *)

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

(** ** Extensionality *)

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

Lemma is_derive_mult (f g : R -> R) (x : R) (d1 d2 : R) :
  is_derive f x d1 -> is_derive g x d2
    -> is_derive (fun x => f x * g x) x (d1 * g x + f x * d2).
Proof.
  exact: derivable_pt_lim_mult.
Qed.
Lemma ex_derive_mult (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x
    -> ex_derive (fun x => f x * g x) x.
Proof.
  move => [d1 H1] [d2 H2].
  exists (d1 * g x + f x * d2) ; exact: is_derive_mult.
Qed.
Lemma Derive_mult (f g : R -> R) (x : R) :
  ex_derive f x -> ex_derive g x
    -> Derive (fun x => f x * g x) x = Derive f x * g x + f x * Derive g x.
Proof.
  move => H1 H2.
  apply is_derive_unique.
  apply is_derive_mult ; exact: Derive_correct.
Qed.

Lemma ex_derive_comp (f g : R -> R) (x : R) :
  ex_derive f (g x) -> ex_derive g x -> ex_derive (fun x => f (g x)) x.
Proof.
intros (df,Df) (dg,Dg).
exists (df * dg).
now apply derivable_pt_lim_comp.
Qed.

Lemma Derive_comp (f g : R -> R) (x : R) :
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

(** * Iterated differential *)

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

Lemma Derive_n_scal (f : R -> R) (a : R) (n : nat) (x : R) :
  (forall k, (k < n)%nat -> locally (ex_derive (Derive_n f k)) (a * x)) ->
  locally (fun x => Derive_n (fun y => f (a * y)) n x  = (a ^ n * Derive_n f n (a*x))) x.
Proof.
  elim: n x => /= [ | n IH] x Hf.
  apply locally_forall => y ; ring.
  case: (IH x) => [ | {IH} r IH].
  move => k Hk ; apply Hf.
  apply lt_trans with (1 := Hk), lt_n_Sn.
  
  case: (Hf n (lt_n_Sn _)) => {Hf} r0 Hf.
  have Hr : 0 < Rmin r r0 / Rmax 1 (Rabs a).
    apply Rmult_lt_0_compat.
    apply Rmin_case ; [by apply r | by apply r0].
    apply Rinv_0_lt_compat, Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
  set r1 := (mkposreal _ Hr).
  exists r1 => y Hy /=.
  
  rewrite -(Derive_ext_loc (fun x => a ^ n * Derive_n f n (a * x))).
  rewrite Derive_scal.
  rewrite Derive_comp.
  rewrite (Derive_ext (Rmult a) (fun x => a * x)) => //.
  rewrite Derive_scal.
  rewrite Derive_id.
  ring.

  apply Hf.
  replace (a * y - (a * x))
    with (a*(y-x))
    by ring.
    rewrite Rabs_mult.
    apply Rle_lt_trans with (Rmax 1 (Rabs a) * Rabs (y - x)).
    apply Rmult_le_compat_r.
    by apply Rabs_pos.
    apply Rmax_r.
    apply Rlt_le_trans with (2 := Rmin_r r r0).
    replace (Rmin r r0)
      with (Rmax 1 (Rabs a) * (Rmin r r0 / Rmax 1 (Rabs a))).
    apply Rmult_lt_compat_l.
    apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
    exact: Hy.
    field ; apply Rgt_not_eq, Rlt_gt.
    apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
    
  apply (ex_derive_ext (fun x => a * x) (Rmult a)) => //.
  apply ex_derive_scal.
  apply ex_derive_id.
  
  have : Rabs (y - x) < r.
    apply Rlt_le_trans with (1 := Hy) ; simpl.
    apply Rle_trans with (2 := Rmin_l r r0).
    rewrite {2}(Rdiv_1 (Rmin _ _)).
    apply Rmult_le_compat_l.
    apply Rmin_case ; apply Rlt_le ; [by apply r | by apply r0].
    apply Rle_Rinv.
    apply Rlt_0_1.
    apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
    apply Rmax_l.
  move => {Hy} Hy.
  have H : 0 < Rmin ((x+r)-y) (y-(x-r)).
    apply Rmin_case.
    apply Rlt_Rminus.
    by apply Rabs_lt_between'.
    apply Rlt_Rminus.
    by apply Rabs_lt_between'.
  set r2 := mkposreal _ H.
  exists r2 => /= z Hz.
  apply sym_eq, IH.
  apply Rabs_lt_between' ; apply Rabs_lt_between' in Hz.
  rewrite Rplus_min_distr_l /Rminus -Rmax_opp_Rmin Rplus_max_distr_l in Hz.
  ring_simplify (y + - (x + r + - y)) (y + - (y + - (x + - r))) 
    (y + (x + r + - y)) (y + (y + - (x + - r))) in Hz.
  split.
  apply Rle_lt_trans with (2 := proj1 Hz), Rmax_r.
  apply Rlt_le_trans with (1 := proj2 Hz), Rmin_l.
Qed.

Lemma Derive_n_opp (f : R -> R) (a : R) (n : nat) (x : R) :
  (forall k, (k < n)%nat -> locally (ex_derive (Derive_n f k)) (- x)) ->
  locally (fun x => Derive_n (fun y => f (- y)) n x  = ((-1) ^ n * Derive_n f n (-x))) x.
Proof.
  move => Hf.
  case: (Derive_n_scal f (-1) n x) => [ | r H].
  move => k Hk.
  replace (-1 * x) with (-x) by ring.
  by apply Hf.
  exists r => y Hy.
  rewrite (Derive_n_ext (fun y0 : R => f (- y0)) (fun y0 : R => f (-1 * y0))).
  rewrite H.
  by ring_simplify (-1 * y).
  exact: Hy.
  move => t ; by ring_simplify (-1 * t).
Qed.

Lemma fn_eq_Derive_eq: forall f g a b, 
  continuity_pt f a -> continuity_pt f b ->
  continuity_pt g a -> continuity_pt g b -> 
  (forall x, a < x < b -> ex_derive f x) ->
  (forall x, a < x < b -> ex_derive g x) ->
  (forall x, a < x < b -> Derive f x = Derive g x) ->
  exists C, forall x, a <= x <= b -> f x = g x + C.
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

(** * Mean value theorem *)
Lemma MVT (f : R -> R) (a b : R) :
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