Require Import Reals ssreflect.
Require Import Coquelicot.

Open Local Scope C_scope.

(** * New in Coquelicot *)

(* Global Instance C_R_VS_mixin : VectorSpace_mixin C R C_AbelianGroup.
Proof.
  apply Build_VectorSpace_mixin with (fun (x : R) (y : C) => x * y).
  intros x y u.
  now apply injective_projections ; simpl ; ring.
  intro u.
  now apply injective_projections ; simpl ; ring.
  intros x u v.
  now apply injective_projections ; simpl ; ring.
  intros x y u.
  now apply injective_projections ; simpl ; ring.
Defined.
Global Instance C_R_MVS : MetricVectorSpace C R.
Proof.
  apply (Build_MetricVectorSpace C R _ C_AbelianGroup _ (Normed_MetricBall _)).
  - intros x y ;
    apply filterlim_locally => eps.
    exists (@ball _ (Normed_MetricBall _) x (pos_div_2 eps))
           (@ball _ (Normed_MetricBall _) y (pos_div_2 eps)).
    apply locally_ball.
    apply locally_ball.
    simpl ; intros u v Hu Hv.
    rewrite (double_var eps).
    apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ Hu Hv).
    rewrite -/(Cplus u v) -/(Cplus x y).
    replace (u + v + - (x + y)) with ((u - x) + (v - y))
    by (apply injective_projections ; simpl ; ring).
    apply Cmod_triangle.
  - intros x u ;
    apply filterlim_locally => eps.
    have He : 0 < eps / Rmax 1 (Cmod x).
      apply Rdiv_lt_0_compat.
      by apply eps.
      apply Rlt_le_trans with (2 := Rmax_l _ _).
      by apply Rlt_0_1.
    exists (mkposreal _ He) ; simpl => v Hv.
    replace (x * v + - (x * u))
      with (x * (v - u))
      by (apply injective_projections ; simpl ; ring).
    rewrite Cmod_mult.
    apply Rle_lt_trans with (Cmod (v - u)%C * Rmax 1 (Cmod x))%R.
    rewrite Rmult_comm ; apply Rmult_le_compat_l.
    by apply sqrt_pos.
    by apply Rmax_r.
    apply Rlt_div_r.
    apply Rlt_le_trans with (2 := Rmax_l _ _).
    by apply Rlt_0_1.
    by [].
Defined. *)

Lemma Normed_Metric_prod_equiv {U V} {K} {FK : AbsField K} :
  forall (VU : NormedVectorSpace U K) (VV : NormedVectorSpace V K) (x : U*V) (P : U*V -> Prop),
  let H := MetricVectorSpace_prod (Normed_MetricVectorSpace VU) (Normed_MetricVectorSpace VV) in
  let H0 := Normed_MetricVectorSpace (NormedVectorSpace_prod VU VV) in
  @locally _ (@mvspace_metric (U*V) K _ H) x P
    <-> @locally _ (@mvspace_metric (U*V) K _ H0) x P.
Proof.
  intros.
  split ; case => eps /= Hl ; exists eps ; simpl => y Hy ; apply Hl.
  split ; apply Rle_lt_trans with (2 := Hy).
  by apply Rmax_l.
  by apply Rmax_r.
  apply Rmax_case ; by apply Hy.
Qed.

Definition C_RInt (f : R -> C) (a b : R) : C :=
  (RInt (fun t => fst (f t)) a b, RInt (fun t => snd (f t)) a b).

Lemma is_C_RInt_unique (f : R -> C) (a b : R) (l : C) :
  is_RInt f a b l -> C_RInt f a b = l.
Proof.
  intros Hf.
  apply RInt_fct_extend_pair.
  by apply is_RInt_unique.
  by apply is_RInt_unique.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) Hf eps) ; case => d /= {Hf} Hf.
  exists d ; simpl ; intros.
  specialize (Hf y H H0).
  split ; apply Rle_lt_trans with (2 := Hf).
  by apply Rmax_l.
  by apply Rmax_r.
Qed.
Lemma C_RInt_correct (f : R -> C) (a b : R) :
  ex_RInt f a b -> is_RInt f a b (C_RInt f a b).
Proof.
  case => l Hf.
  replace (C_RInt f a b) with l.
  by [].
  by apply sym_eq, is_C_RInt_unique.
Qed.

Lemma C_RInt_ext (f g : R -> C) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> g x = f x)
    -> C_RInt g a b = C_RInt f a b.
Proof.
  intros Heq.
  apply injective_projections ; simpl ;
  apply RInt_ext => x Hx ; by rewrite Heq.
Qed.
Lemma C_RInt_swap (f : R -> C) (a b : R) :
  - C_RInt f a b = C_RInt f b a.
Proof.
  apply injective_projections ; simpl ;
  apply RInt_swap.
Qed.
Lemma C_RInt_scal (f : R -> C) (k : C) (a b : R) :
  ex_RInt f a b ->
  C_RInt (fun t => scal k (f t)) a b = scal k (C_RInt f a b).
Proof.
  intros Hf.
  apply injective_projections ; simpl ;
  rewrite -?RInt_scal ?RInt_minus ?RInt_plus // ;
  apply ex_RInt_scal.
  case: Hf => l Hf ; exists (fst l) ;
  apply is_RInt_fct_extend_fst.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) Hf eps) ; case => d /= {Hf} Hf.
  exists d ; simpl ; intros.
  specialize (Hf y H H0).
  split ; apply Rle_lt_trans with (2 := Hf).
  by apply Rmax_l.
  by apply Rmax_r.
  case: Hf => l Hf ; exists (snd l) ;
  apply is_RInt_fct_extend_snd.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) Hf eps) ; case => d /= {Hf} Hf.
  exists d ; simpl ; intros.
  specialize (Hf y H H0).
  split ; apply Rle_lt_trans with (2 := Hf).
  by apply Rmax_l.
  by apply Rmax_r.
  case: Hf => l Hf ; exists (snd l) ;
  apply is_RInt_fct_extend_snd.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) Hf eps) ; case => d /= {Hf} Hf.
  exists d ; simpl ; intros.
  specialize (Hf y H H0).
  split ; apply Rle_lt_trans with (2 := Hf).
  by apply Rmax_l.
  by apply Rmax_r.
  case: Hf => l Hf ; exists (fst l) ;
  apply is_RInt_fct_extend_fst.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) Hf eps) ; case => d /= {Hf} Hf.
  exists d ; simpl ; intros.
  specialize (Hf y H H0).
  split ; apply Rle_lt_trans with (2 := Hf).
  by apply Rmax_l.
  by apply Rmax_r.
Qed.
Lemma C_RInt_opp (f : R -> C) (a b : R) :
  C_RInt (fun t => - f t) a b = - C_RInt f a b.
Proof.
  apply injective_projections ; simpl ;
  apply RInt_opp.
Qed.
Lemma C_RInt_comp_lin (f : R -> C) (u v a b : R) :
  C_RInt (fun y : R => (u * f (u * y + v)%R)) a b =
     C_RInt f (u * a + v) (u * b + v).
Proof.
  apply injective_projections ; simpl ;
  rewrite -RInt_comp_lin ; apply RInt_ext => x _ ; ring.
Qed.
Lemma C_RInt_Chasles_0 (f : R -> C) (a b c : R) :
  ex_RInt f a b -> ex_RInt f b c ->
  C_RInt f a b + C_RInt f b c =
     C_RInt f a c.
Proof.
  intros H1 H2.
  apply injective_projections ; simpl ;
  rewrite RInt_Chasles => //.
  case: H1 => l H1 ; exists (fst l) ;
  apply is_RInt_fct_extend_fst.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) H1 eps) ; case => d /= {H1} H1.
  exists d ; simpl ; intros.
  specialize (H1 y H H0).
  split ; apply Rle_lt_trans with (2 := H1).
  by apply Rmax_l.
  by apply Rmax_r.
  case: H2 => l H2 ; exists (fst l) ;
  apply is_RInt_fct_extend_fst.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) H2 eps) ; case => d /= {H2} H2.
  exists d ; simpl ; intros.
  specialize (H2 y H H0).
  split ; apply Rle_lt_trans with (2 := H2).
  by apply Rmax_l.
  by apply Rmax_r.
  case: H1 => l H1 ; exists (snd l) ;
  apply is_RInt_fct_extend_snd.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) H1 eps) ; case => d /= {H1} H1.
  exists d ; simpl ; intros.
  specialize (H1 y H H0).
  split ; apply Rle_lt_trans with (2 := H1).
  by apply Rmax_l.
  by apply Rmax_r.
  case: H2 => l H2 ; exists (snd l) ;
  apply is_RInt_fct_extend_snd.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) H2 eps) ; case => d /= {H2} H2.
  exists d ; simpl ; intros.
  specialize (H2 y H H0).
  split ; apply Rle_lt_trans with (2 := H2).
  by apply Rmax_l.
  by apply Rmax_r.
Qed.

(** * Definition 2 *)

Definition ex_C_RInt_segm (f : C -> C) (z1 z2 : C) :=
  ex_RInt (fun t => f ((1 - t) * z1 + t * z2)) 0 1.
Definition C_RInt_segm (f : C -> C) (z1 z2 : C) : C :=
  (z2 - z1) * C_RInt (fun t => f ((1 - t) * z1 + t * z2)) 0 1.
Definition is_C_RInt_segm (f : C -> C) (z1 z2 l : C) :=
  ex_C_RInt_segm f z1 z2 /\ C_RInt_segm f z1 z2 = l.

Lemma is_C_RInt_segm_unique (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z1 z2 l -> C_RInt_segm f z1 z2 = l.
Proof.
  by case.
Qed.
Lemma ex_C_RInt_segm_usual (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 <-> exists l, is_C_RInt_segm f z1 z2 l.
Proof.
  split => H.
  exists (C_RInt_segm f z1 z2) ; by split.
  case: H => l ; by case.
Qed.
Lemma C_RInt_segm_correct (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> is_C_RInt_segm f z1 z2 (C_RInt_segm f z1 z2).
Proof.
  by split.
Qed.

(** * Proposition 3 *)

Lemma ex_C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z2 z1 -> ex_C_RInt_segm f z1 z2.
Proof.
  rewrite /ex_C_RInt_segm => H.
  apply ex_RInt_swap.
  apply ex_RInt_ext with (fun t : R => opp (scal (-1) (f ((1 - (-1 * t + 1)%R) * z2 + (-1 * t + 1)%R * z1)%C))).
    move => x _.
    simpl.
    apply injective_projections ; simpl ; ring_simplify ;
    apply f_equal ; apply f_equal ;
    apply injective_projections ; simpl ; ring.
  apply ex_RInt_opp.
  generalize (ex_RInt_comp_lin (fun t : R => f ((1 - t) * z2 + t * z1)) (-1) (1) 1 0) => H0.
  apply H0.
  now ring_simplify (-1 * 1 + 1)%R (-1 * 0 + 1)%R.
Qed.
Lemma C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  - C_RInt_segm f z1 z2 = C_RInt_segm f z2 z1.
Proof.
  unfold C_RInt_segm.
  generalize (opp_mult_l (FK := AbsField_Field C_AbsField) (z2 - z1) (C_RInt (fun t : R => f ((1 - t) * z1 + t * z2)) 0 1))
    => /= ->.
  apply f_equal2.
  apply injective_projections ; simpl ; ring.
  rewrite (C_RInt_ext (fun t : R => opp 
    ((-1) * (f ((1 - (-1 * t + 1)%R) * z2 + (-1 * t + 1)%R * z1)%C)))).
  rewrite C_RInt_opp.
  rewrite C_RInt_swap.
  rewrite (C_RInt_comp_lin (fun t : R => f ((1 - t) * z2 + t * z1)) (-1) (1) 1 0) ;
  apply f_equal2 ; ring.
  intros x _ ; simpl.
  apply injective_projections ; simpl ; ring_simplify ;
  apply f_equal ; apply f_equal ;
  apply injective_projections ; simpl ; ring.
Qed.
Lemma is_C_RInt_segm_swap (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z2 z1 l -> is_C_RInt_segm f z1 z2 (-l).
Proof.
  case => Hex Hl ; split.
  by apply ex_C_RInt_segm_swap.
  rewrite -Hl ; by apply sym_eq, C_RInt_segm_swap.
Qed.

Lemma ex_C_RInt_segm_Chasles_0 (f : C -> C) (z1 z2 z3 : C) :
  (exists p, 0 <= p <= 1 /\ z2 = ((1 - p) * z1 + p * z3))
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
    -> ex_C_RInt_segm f z1 z3.
Proof.
  rewrite /ex_C_RInt_segm ;
  case => p [Hp ->] H1 H2.
  case: Hp => Hp0 Hp1.
  case: Hp0 => Hp0.
  case: Hp1 => Hp1.
  apply ex_RInt_Chasles_0 with p.
  split ; by apply Rlt_le.
  replace 0%R with (/p * 0 + 0)%R in H1 by ring.
  pattern 1%R at 3 in H1.
  replace 1%R with (/p * p + 0)%R in H1 by (field ; by apply Rgt_not_eq).
  apply (ex_RInt_comp_lin (fun t : R => f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))
    (/p) 0 0 p) in H1.
  apply (ex_RInt_scal _ _ _ _ _ p) in H1.
  move: H1 ; apply ex_RInt_ext => x Hx.
  apply injective_projections ; simpl ; field_simplify ; try (by apply Rgt_not_eq) ;
  rewrite ?Rdiv_1 ; apply f_equal, f_equal ;
  apply injective_projections ; simpl ; field ; by apply Rgt_not_eq.
  clear H1.
  replace 0%R with ((/(1-p)) * p + -/(1-p)*p)%R in H2 by ring.
  pattern 1%R at 5 in H2.
  replace 1%R with ((/(1-p)) * 1 + -/(1-p)*p)%R in H2
    by (field ; apply Rgt_not_eq ; by apply -> Rminus_lt_0).
  apply (ex_RInt_comp_lin (fun t : R => f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))
    (/(1-p)) (-/(1-p)*p) p 1) in H2.
  apply (ex_RInt_scal _ _ _ _ _ (1-p)) in H2.
  move: H2 ; apply ex_RInt_ext => x Hx.
  apply injective_projections ; simpl ; field_simplify ;
  try (by apply Rgt_not_eq ; apply -> Rminus_lt_0) ;
  rewrite ?Rdiv_1 ; apply f_equal, f_equal ;
  apply injective_projections ; simpl ; field ; by apply Rgt_not_eq ; apply -> Rminus_lt_0.
  
  rewrite Hp1 in H1.
  move: H1 ; apply ex_RInt_ext => x Hx.
  apply f_equal.
  apply injective_projections ; simpl ; ring.
  
  rewrite -Hp0 in H2.
  move: H2 ; apply ex_RInt_ext => x Hx.
  apply f_equal.
  apply injective_projections ; simpl ; ring.
Qed.
Lemma C_RInt_segm_Chasles_0 (f : C -> C) (z1 z2 z3 : C) :
  (exists p, 0 <= p <= 1 /\ z2 = ((1 - p) * z1 + p * z3))
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 = C_RInt_segm f z1 z3.
Proof.
  rewrite /C_RInt_segm ;
  case => p [Hp ->] H1 H2.
  case: Hp => Hp0 Hp1.
  case: Hp0 => Hp0.
  case: Hp1 => Hp1.

  unfold ex_C_RInt_segm in H1, H2.

  move: H1.
  pattern 0%R at 1 2.
  replace 0%R with (/p * 0 + 0)%R by ring.
  pattern 1%R at 3 7.
  replace 1%R with (/p * p + 0)%R by (field ; by apply Rgt_not_eq).
  move => H1.
  rewrite -(C_RInt_comp_lin (fun t : R => f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))
    (/p) 0 0 p).
  apply (ex_RInt_comp_lin (fun t : R => f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))
    (/p) 0 0 p) in H1.
  apply (ex_RInt_scal _ _ _ _ _ p) in H1.
  rewrite C_RInt_scal.
  
  move: H2.
  pattern 0%R at 1 5.
  replace 0%R with ((/(1-p)) * p + -/(1-p)*p)%R by ring.
  pattern 1%R at 5 14.
  replace 1%R with ((/(1-p)) * 1 + -/(1-p)*p)%R
    by (field ; apply Rgt_not_eq ; by apply -> Rminus_lt_0).
  move => H2.
  rewrite -(C_RInt_comp_lin (fun t : R => f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))
    (/(1-p)) (-/(1-p)*p) p 1).
  apply (ex_RInt_comp_lin (fun t : R => f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))
    (/(1-p)) (-/(1-p)*p) p 1) in H2.
  apply (ex_RInt_scal _ _ _ _ _ (1-p)) in H2.
  rewrite C_RInt_scal.
  rewrite -(C_RInt_Chasles_0 (fun t : R => f ((1 - t) * z1 + t * z3)) _ p).
  rewrite (C_RInt_ext (fun t : R => f ((1 - t) * z1 + t * z3))).
  rewrite (C_RInt_ext (fun t : R => f ((1 - t) * z1 + t * z3)) _ p 1).
  apply injective_projections ; simpl ; field ; split.
  by apply Rgt_not_eq ; apply -> Rminus_lt_0.
  by apply Rgt_not_eq.
  by apply Rgt_not_eq ; apply -> Rminus_lt_0.
  by apply Rgt_not_eq.
  intros x Hx ; apply f_equal.
  apply injective_projections ; simpl ; field ;
  by apply Rgt_not_eq ; apply -> Rminus_lt_0.
  intros x Hx ; apply f_equal.
  apply injective_projections ; simpl ; field ;
  by apply Rgt_not_eq.
  
  move: H1 ; apply ex_RInt_ext.
  intros x Hx.
  apply injective_projections ; simpl ; field_simplify ; try (by apply Rgt_not_eq) ;
  rewrite ?Rdiv_1 ; apply f_equal, f_equal ;
  apply injective_projections ; simpl ; field ; by apply Rgt_not_eq.
  clear H1.
  move: H2 ; apply ex_RInt_ext.
  intros x Hx.
  apply injective_projections ; simpl ; field_simplify ; try (by apply Rgt_not_eq ; apply -> Rminus_lt_0) ;
  rewrite ?Rdiv_1 ; apply f_equal, f_equal ;
  apply injective_projections ; simpl ; field ; by apply Rgt_not_eq ; apply -> Rminus_lt_0.
  move: H2 ; apply ex_RInt_ext.
  intros x Hx.
  apply injective_projections ; simpl ; field_simplify ; try (by apply Rgt_not_eq ; apply -> Rminus_lt_0) ;
  rewrite ?Rdiv_1 ; apply f_equal, f_equal ;
  apply injective_projections ; simpl ; field ; by apply Rgt_not_eq ; apply -> Rminus_lt_0.
  move: H1 ; apply ex_RInt_ext.
  intros x Hx.
  apply injective_projections ; simpl ; field_simplify ; try (by apply Rgt_not_eq) ;
  rewrite ?Rdiv_1 ; apply f_equal, f_equal ;
  apply injective_projections ; simpl ; field ; by apply Rgt_not_eq.
  
  rewrite Hp1 in H1 |- *.
  apply injective_projections ; simpl ; ring_simplify ;
  rewrite 2?(RInt_ext (fun t : R => fst (f ((1 - t) * z1 + t * ((1 - 1) * z1 + 1 * z3))%C))
                    (fun t : R => fst (f ((1 - t) * z1 + t * z3)%C))) ;
  rewrite 2?(RInt_ext (fun t : R => snd (f ((1 - t) * z1 + t * ((1 - 1) * z1 + 1 * z3))%C))
                    (fun t : R => snd (f ((1 - t) * z1 + t * z3)%C))) ;
  try (by simpl) ; move => x Hx ;
  apply f_equal, f_equal ;
  apply injective_projections ; simpl ; ring.
  
  rewrite -Hp0 in H2 |- *.
  apply injective_projections ; simpl ; ring_simplify ;
  rewrite 2?(RInt_ext (fun t : R => fst (f ((1 - t) * ((1 - 0) * z1 + 0 * z3) + t * z3)%C))
                    (fun t : R => fst (f ((1 - t) * z1 + t * z3)%C))) ;
  rewrite 2?(RInt_ext (fun t : R => snd (f ((1 - t) * ((1 - 0) * z1 + 0 * z3) + t * z3)%C))
                    (fun t : R => snd (f ((1 - t) * z1 + t * z3)%C))) ;
  try (by simpl) ; move => x Hx ;
  apply f_equal, f_equal ;
  apply injective_projections ; simpl ; ring.
Qed.
Lemma is_C_RInt_segm_Chasles_0 (f : C -> C) (z1 z2 z3 l1 l2 : C) :
  (exists p, 0 <= p <= 1 /\ z2 = ((1 - p) * z1 + p * z3))
  -> is_C_RInt_segm f z1 z2 l1 -> is_C_RInt_segm f z2 z3 l2
    -> is_C_RInt_segm f z1 z3 (l1 + l2).
Proof.
  intros H [H1 <-] [H2 <-] ; split.
  by apply ex_C_RInt_segm_Chasles_0 with z2.
  apply sym_eq ; by apply C_RInt_segm_Chasles_0.
Qed.
