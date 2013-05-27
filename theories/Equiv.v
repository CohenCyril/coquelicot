Require Import Reals ssreflect.
Require Import Rbar Rcomplements.

(** * Definitions of equivalent and preponderant *)

Definition is_prepond (f : R -> R) (a : Rbar) (g : R -> R) :=
  forall eps : posreal, Rbar_locally (fun x => Rabs (g x) <= eps * Rabs (f x)) a.
Definition is_equiv (f g : R -> R) (a : Rbar) :=
  is_prepond g a (fun x => g x - f x).

(** ** Be preponderent is a partial strict order *)
Lemma prepond_anti_sym (f : R -> R) (a : Rbar) :
  Rbar_locally (fun x => f x <> 0) a -> ~ is_prepond f a f.
Proof.
  intros Hf H ;
  move: (H (pos_div_2 (mkposreal _ Rlt_0_1))) => {H} /= H.
  have H0 : Rbar_locally (fun x => ~ (Rabs (f x) <= 1/2 * Rabs (f x))) a.
    move: Hf ; apply Rbar_locally_imply, Rbar_locally_forall.
    intros x Hf ; apply Rlt_not_le.
    apply Rminus_lt ; field_simplify ;
    rewrite -Rdiv_1 /Rdiv Ropp_mult_distr_l_reverse ;
    apply Ropp_lt_gt_0_contravar, Rdiv_lt_0_compat.
    by apply Rabs_pos_lt.
    by apply Rlt_R0_R2.
  move: (Rbar_locally_and _ _ _ H H0) => {H H0} H.
  case: a {Hf} H => [a | | ] /= [delta H].
  case: (H a).
  rewrite Rminus_eq0 Rabs_R0 ; by apply delta.
  by [].
  case: (H (delta+1)).
  by apply Rlt_plus_1.
  by [].
  case: (H (delta-1)).
  pattern delta at 2 ;
  replace delta with ((delta+1)-1) by ring.
  by apply Rplus_lt_compat_r, Rlt_plus_1.
  by [].
Qed.

Lemma prepond_trans (f g h : R -> R) (a : Rbar) :
  is_prepond f a g -> is_prepond g a h -> is_prepond f a h.
Proof.
  move => Hfg Hgh eps.
  apply (Rbar_locally_imply (fun x => (Rabs (h x) <= sqrt eps * Rabs (g x)) /\ (Rabs (g x) <= sqrt eps * Rabs (f x)))).
  apply Rbar_locally_forall => x [H0 H1].
  apply Rle_trans with (1 := H0).
  rewrite -{2}(sqrt_sqrt eps).
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  by apply sqrt_pos.
  apply H1.
  by apply Rlt_le, eps.
  apply Rbar_locally_and.
  by apply (Hgh (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
  by apply (Hfg (mkposreal (sqrt eps) (sqrt_lt_R0 _ (cond_pos eps)))).
Qed.

(** ** Relations between preponderance and equivalence *)

Lemma prepond_rw_l (f1 f2 g : R -> R) (a : Rbar) :
  is_equiv f1 f2 a -> (is_prepond f1 a g <-> is_prepond f2 a g).
Proof.
  move => Hf ; split => Hfg.
(* Cas facile *)
  have : forall eps : posreal, Rbar_locally (fun x => Rabs (f1 x) <= (eps + 1) * Rabs (f2 x)) a.
    move => eps.
    move: (Hf eps) => {Hf}.
    apply Rbar_locally_imply, Rbar_locally_forall => x Hf.
    rewrite Rmult_plus_distr_r Rmult_1_l.
    replace (Rabs (f1 x)) with ((Rabs (f1 x) - Rabs (f2 x)) + Rabs (f2 x)) by ring.
    apply Rplus_le_compat_r.
    apply Rle_trans with (2 := Hf).
    rewrite -(Rabs_Ropp (_-_)) Ropp_minus_distr'.
    by apply Rabs_triang_inv.
  move => {Hf} Hf eps.
  move: (Hf (mkposreal _ Rlt_0_1)) (Hfg (pos_div_2 eps)) => /= {Hf Hfg} Hf Hfg.
  move: (Rbar_locally_and _ _ _ Hf Hfg) => {Hf Hfg}.
  apply Rbar_locally_imply.
  apply Rbar_locally_forall => x [Hf Hfg].
  apply Rle_trans with (1 := Hfg).
  pattern (pos eps) at 2 ;
  replace (pos eps) with ((eps/2)*2) by field.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  apply Rlt_le, is_pos_div_2.
  by apply Hf.
(* Cas compliqué *)
  have : forall eps : posreal, Rbar_locally (fun x => (1-eps) * Rabs (f2 x) <= Rabs (f1 x)) a.
    move => eps.
    move: (Hf eps) => {Hf}.
    apply Rbar_locally_imply, Rbar_locally_forall => x Hf.
    rewrite Rmult_minus_distr_r Rmult_1_l.
    replace (Rabs (f1 x)) with (Rabs (f2 x) - (Rabs (f2 x) - Rabs (f1 x))) by ring.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    apply Rle_trans with (2 := Hf).
    by apply Rabs_triang_inv.
  move => {Hf} Hf eps.
  move: (Hf (pos_div_2 (mkposreal _ Rlt_0_1))) (Hfg (pos_div_2 eps)) => /= {Hf Hfg} Hf Hfg.
  move: (Rbar_locally_and _ _ _ Hf Hfg) => {Hf Hfg}.
  apply Rbar_locally_imply.
  apply Rbar_locally_forall => x [Hf Hfg].
  replace (1 - 1 / 2) with (/2) in Hf by field.
  apply Rle_trans with (1 := Hfg).
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  by apply Hf.
Qed.

Lemma equiv_sym (f g : R -> R) (a : Rbar) :
  is_equiv f g a -> is_equiv g f a.
Proof.
  intros H.
  apply (prepond_rw_l _ _ (fun x : R => f x - g x) _ H).
  move => eps ; move: (H eps).
  apply Rbar_locally_imply, Rbar_locally_forall => x Hx.
  by rewrite -Rabs_Ropp Ropp_minus_distr'.
Qed.


Lemma prepond_rw_r (f g1 g2 : R -> R) (a : Rbar) :
  is_equiv g1 g2 a -> (is_prepond f a g1 <-> is_prepond f a g2).
Proof.
  assert (forall g1 g2,  is_equiv g1 g2 a -> is_prepond f a g2 -> is_prepond f a g1).
  clear g1 g2; intros g1 g2 Hg Hf eps.
  rewrite /is_equiv in Hg.
  rewrite /is_prepond in Hg Hf.
  specialize (Hg (mkposreal _ Rlt_0_1)); simpl in Hg.
  specialize (Hf (pos_div_2 eps)).
  apply Rbar_locally_imply with (2:=Hf).
  apply Rbar_locally_imply with (2:=Hg).
  apply Rbar_locally_forall.
  intros x H1 H2.
  replace (g1 x) with (-(g2 x - g1 x) + g2 x) by ring.
  apply Rle_trans with (1:=Rabs_triang _ _).
  rewrite Rabs_Ropp.
  apply Rle_trans with (1 * Rabs (g2 x)+ Rabs (g2 x)).
  now apply Rplus_le_compat_r.
  apply Rle_trans with (2*Rabs (g2 x));[right; ring|idtac].
  apply Rle_trans with (2*(pos_div_2 eps * Rabs (f x))).
  apply Rmult_le_compat_l.
  left; apply Rlt_0_2.
  apply H2.
  right; unfold pos_div_2; simpl; field.
  intros H'; split.
  apply H.
  now apply equiv_sym.
  now apply H.
Qed.



(** ** Be equivalent is a relation of equivalence *)

Lemma equiv_refl (f : R -> R) (a : Rbar) :
  is_equiv f f a.
Proof.
  move => eps /=.
  apply Rbar_locally_forall => x.
  rewrite Rminus_eq0 Rabs_R0.
  apply Rmult_le_pos.
  by apply Rlt_le, eps.
  by apply Rabs_pos.
Qed.



Lemma equiv_trans (f g h : R -> R) (a : Rbar) :
  is_equiv f g a -> is_equiv g h a -> is_equiv f h a.
Proof.
  intros Hfg Hgh.
  move: (fun c => prepond_rw_l _ _ c _ Hgh) => Hgh'.
  apply Hgh' => {Hgh'} eps.
  apply equiv_sym in Hgh.
  move: (Rbar_locally_and _ _ _ (Hfg (pos_div_2 eps)) (Hgh (pos_div_2 eps))) => {Hfg Hgh}.
  apply Rbar_locally_imply, Rbar_locally_forall => x /= [Hfg Hgh].
  replace (h x - f x) with ((g x - f x) - (g x - h x)) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps) Rmult_plus_distr_r.
  by apply Rplus_le_compat.
Qed.

Lemma equiv_carac_0 (f g : R -> R) (a : Rbar) :
  is_equiv f g a 
    -> {o : R -> R | (forall x : R, f x = g x + o x) /\ is_prepond g a o }.
Proof.
  intro H.
  exists (fun x => f x - g x).
  split.
  intro x ; ring.
  apply (prepond_rw_l _ _ _ _ H).
  by apply equiv_sym.
Qed.

Lemma equiv_carac_1 (f g : R -> R) (a : Rbar) :
  forall (o : R -> R), (forall x : R, f x = g x + o x) -> is_prepond g a o
    -> is_equiv f g a.
Proof.
  intros o Ho Hgo.
  intro eps ; move: (Hgo eps).
  apply Rbar_locally_imply, Rbar_locally_forall => x.
  replace (o x) with (f x - g x).
  by rewrite -(Rabs_Ropp (f x - g x)) Ropp_minus_distr'.
  rewrite Ho ; ring.
Qed.

(** * Vectorial space *)
(** ** is_preponderant is a vectorial space *)

Lemma prepond_scal_r (f g : R -> R) (a : Rbar) (c : R) :
  is_prepond f a g -> is_prepond f a (fun x => c * g x).
Proof.
  move => H.
  wlog: c / (0 < c) => [Hw  {H} | Hc].
    case: (Rlt_le_dec 0 c) => Hc.
    by apply Hw.
    case: Hc => Hc.
    apply Ropp_0_gt_lt_contravar in Hc.
    move: (Hw _ Hc) => {Hw} H eps ; move: (H eps).
    apply Rbar_locally_imply, Rbar_locally_forall => x.
    by rewrite Ropp_mult_distr_l_reverse Rabs_Ropp.
    rewrite Hc => {c Hc Hw} eps.
    apply Rbar_locally_forall => x.
    rewrite Rmult_0_l Rabs_R0.
    apply Rmult_le_pos.
    by apply Rlt_le, eps.
    by apply Rabs_pos.
  move => eps /=.
  have He : 0 < eps / c.
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply Hc.
  move: (H (mkposreal _ He)) => /= {H}.
  apply Rbar_locally_imply, Rbar_locally_forall => x H.
  rewrite Rabs_mult (Rabs_right c).
  replace (eps * Rabs (f x)) with (c*(eps / c * Rabs (f x))).
  apply Rmult_le_compat_l.
  by apply Rlt_le, Hc.
  by apply H.
  field ; by apply Rgt_not_eq.
  by apply Rle_ge, Rlt_le.
Qed.

Lemma prepond_scal_l (f g : R -> R) (a : Rbar) (c : R) :
  c <> 0 -> is_prepond f a g -> is_prepond (fun x => c * f x) a g.
Proof.
  intros Hc H eps.
  have He : (0 < eps * Rabs c).
    apply Rmult_lt_0_compat.
    by apply eps.
    by apply Rabs_pos_lt.
  move: (H (mkposreal _ He)) => /= {H}.
  apply Rbar_locally_imply, Rbar_locally_forall => x Hx.
  by rewrite Rabs_mult -Rmult_assoc.
Qed.

Lemma prepond_plus (f g1 g2 : R -> R) (a : Rbar) :
  is_prepond f a g1 -> is_prepond f a g2 
    -> is_prepond f a (fun x => g1 x + g2 x).
Proof.
  intros Hg1 Hg2 eps.
  move: (Rbar_locally_and _ _ _ (Hg1 (pos_div_2 eps)) (Hg2 (pos_div_2 eps))) 
    => /= {Hg1 Hg2}.
  apply Rbar_locally_imply, Rbar_locally_forall => x [Hg1 Hg2].
  apply Rle_trans with (1 := Rabs_triang _ _).
  replace (eps * Rabs (f x)) 
    with (eps / 2 * Rabs (f x) + eps / 2 * Rabs (f x))
    by field.
  by apply Rplus_le_compat.
Qed.

(** ** is_equiv is compatible with vectorial space structure *)

Lemma equiv_scal (f g : R -> R) (a : Rbar) (c : R) :
  is_equiv f g a -> is_equiv (fun x => c * f x) (fun x => c * g x) a.
Proof.
  case: (Req_dec c 0) ; move => Hc H.
(* c = 0 *)
  rewrite Hc => {c Hc}.
  move => eps /= ; apply Rbar_locally_forall => x.
  rewrite ?Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r.
  apply Rle_refl.
(* c <> 0 *)
  apply prepond_scal_l.
  by apply Hc.
  move => eps /=.
  have : Rbar_locally (fun x : R => Rabs (c * (g x - f x)) <= eps * Rabs (g x)) a.
  apply (prepond_scal_r g (fun x => g x - f x) a c).
  by apply H.
  apply Rbar_locally_imply, Rbar_locally_forall => x.
  by rewrite Rmult_minus_distr_l.
Qed.

Lemma equiv_plus (f o : R -> R) (a : Rbar) :
  is_prepond f a o -> is_equiv (fun x => f x + o x) f a.
Proof.
  intros H eps.
  move: (H eps) => {H}.
  apply Rbar_locally_imply, Rbar_locally_forall => x Hx.
  ring_simplify (f x - (f x + o x)).
  by rewrite Rabs_Ropp.
Qed.

(** * Multiplication and inverse *)
(** ** Preponderance *)

Lemma prepond_mult_r (f g h : R -> R) (a : Rbar) :
  is_prepond f a g 
    -> is_prepond (fun x => f x * h x) a (fun x => g x * h x).
Proof.
  move => H eps.
  move: (H eps) => {H} H.
  move: H.
  apply Rbar_locally_imply, Rbar_locally_forall => x H1.
  rewrite ?Rabs_mult.
  rewrite -Rmult_assoc.
  apply Rmult_le_compat_r.
  by apply Rabs_pos.
  by apply H1.
Qed.

Lemma prepond_mult_l (f g h : R -> R) (a : Rbar) :
  is_prepond f a g 
    -> is_prepond (fun x => h x * f x) a (fun x => h x * g x).
Proof.
  intros => eps.
  move: (prepond_mult_r f g h a H eps).
  apply Rbar_locally_imply, Rbar_locally_forall => x.
  by rewrite ?(Rmult_comm (h x)).
Qed.

Lemma prepond_mult (f1 f2 g1 g2 : R -> R) (a : Rbar) :
  is_prepond f1 a g1 -> is_prepond f2 a g2 
    -> is_prepond (fun x => f1 x * f2 x) a (fun x => g1 x * g2 x).
Proof.
  move => H1 H2 eps.
  move: (H1 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps))))
    (H2 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps)))) => {H1 H2} /= H1 H2.
  move: (Rbar_locally_and _ _ _ H1 H2) => {H1 H2}.
  apply Rbar_locally_imply, Rbar_locally_forall => x [H1 H2].
  rewrite ?Rabs_mult.
  rewrite -(sqrt_sqrt _ (Rlt_le _ _ (cond_pos eps))).
  replace (sqrt eps * sqrt eps * (Rabs (f1 x) * Rabs (f2 x))) 
    with ((sqrt eps * Rabs (f1 x))*(sqrt eps * Rabs (f2 x))) by ring.
  apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  by apply H1.
  by apply H2.
Qed.

Lemma prepond_inv (f g : R -> R) (a : Rbar) :
  Rbar_locally (fun x => g x <> 0) a -> is_prepond f a g 
    -> is_prepond (fun x => / g x) a (fun x => / f x).
Proof.
  intros Hg H eps.
  have Hf : Rbar_locally (fun x => f x <> 0) a.
    move: (Rbar_locally_and _ _ _ Hg (H (mkposreal _ Rlt_0_1))) => /=.
    apply Rbar_locally_imply, Rbar_locally_forall => x {Hg H} [Hg H].
    case: (Req_dec (f x) 0) => Hf.
    rewrite Hf Rabs_R0 Rmult_0_r in H.
    apply Rlt_not_le in H.
    move => _ ; apply H.
    by apply Rabs_pos_lt.
    by [].
  move: (Rbar_locally_and _ _ _ (H eps) (Rbar_locally_and _ _ _ Hf Hg)) => {H Hf Hg}.
  apply Rbar_locally_imply, Rbar_locally_forall => x [H [Hf Hg]].
  rewrite ?Rabs_Rinv => //.
  replace (/ Rabs (f x)) 
    with (Rabs (g x) / (Rabs (f x) * Rabs (g x)))
    by (field ; split ; by apply Rabs_no_R0).
  replace (eps * / Rabs (g x))
    with (eps * Rabs (f x) / (Rabs (f x) * Rabs (g x)))
    by (field ; split ; by apply Rabs_no_R0).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat ; apply Rabs_pos_lt => //.
  by apply H.
Qed.

(** ** Equivalence *)

Lemma equiv_mult (f1 f2 g1 g2 : R -> R) (a : Rbar) :
  is_equiv f1 g1 a -> is_equiv f2 g2 a
    -> is_equiv (fun x => f1 x * f2 x) (fun x => g1 x * g2 x) a.
Proof.
  intros H1 H2.
  case: (equiv_carac_0 _ _ _ H1) => {H1} o1 [H1 Ho1].
  case: (equiv_carac_0 _ _ _ H2) => {H2} o2 [H2 Ho2].
  apply equiv_carac_1 with (fun x => o1 x * g2 x + g1 x * o2 x + o1 x * o2 x).
  move => x ; rewrite H1 H2 ; ring.
  apply prepond_plus.
  apply prepond_plus.
  by apply prepond_mult_r.
  by apply prepond_mult_l.
  by apply prepond_mult.
Qed.

Lemma equiv_inv (f g : R -> R) (a : Rbar) :
  Rbar_locally (fun x => g x <> 0) a -> is_equiv f g a 
    -> is_equiv (fun x => / f x) (fun x => / g x) a.
Proof.
  intros Hg H.
  have Hf : Rbar_locally (fun x => f x <> 0) a.
    move: (Rbar_locally_and _ _ _ Hg (H (pos_div_2 (mkposreal _ Rlt_0_1)))) => /=.
    apply Rbar_locally_imply, Rbar_locally_forall => x {Hg H} [Hg H].
    case: (Req_dec (f x) 0) => Hf.
    rewrite Hf Rminus_0_r in H.
    apply Rle_not_lt in H.
    move => _ ; apply H.
    apply Rminus_lt ; field_simplify ; rewrite -Rdiv_1 /Rdiv Ropp_mult_distr_l_reverse ; 
    apply Ropp_lt_gt_0_contravar.
    apply Rmult_lt_0_compat.
    by apply Rabs_pos_lt.
    by intuition.
    by[].
  apply equiv_sym in H.
  move => eps ; 
  move: (H eps) ; apply Rbar_locally_imply ;
  move: Hf ; apply Rbar_locally_imply ;
  move: Hg ; apply Rbar_locally_imply, Rbar_locally_forall => {H} x Hg Hf H.
  replace (/ g x - / f x) 
    with ((f x - g x) / (f x * g x)).
  rewrite Rabs_div ?Rabs_Rinv ?Rabs_mult //.
  apply Rle_div_l.
  apply Rmult_lt_0_compat ; by apply Rabs_pos_lt.
  field_simplify ; rewrite -?Rdiv_1.
  by [].
  by apply Rabs_no_R0.
  by apply Rmult_integral_contrapositive_currified.
  field ; by split.
Qed.
