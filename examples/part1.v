Require Import Reals ssreflect.
Require Import Coquelicot.

Open Local Scope C_scope.

(** * New in Coquelicot *)

Global Instance C_NVS_mixin :
  NormedVectorSpace_mixin C R (VectorSpace_prod _ _).
Proof.
  apply Build_NormedVectorSpace_mixin with Cmod.
  by apply Cmod_triangle.
  move => l x /=.
  rewrite -Cmod_R -Cmod_mult.
  apply Req_le, f_equal.
  apply injective_projections ; simpl ; ring.
Defined.

Global Instance C_NVS :
  NormedVectorSpace C R.
Proof.
  apply Build_NormedVectorSpace with (AbelianGroup_prod _ _) (VectorSpace_mixin_prod _ _).
  by apply C_NVS_mixin.
Defined.

Definition C_RInt (f : R -> C) (a b : R) : C :=
  (RInt (fun t => fst (f t)) a b, RInt (fun t => snd (f t)) a b).

Lemma is_C_R2_RInt_compat : forall (f : R -> C) a b (l : C),
  is_RInt (VV := NormedVectorSpace_prod _ _) f a b l
  <-> is_RInt f a b l.
Proof.
  move => f a b l ; split => Hf ;
  apply filterlim_locally => eps.
  - assert (0 < eps / sqrt 2).
      apply Rdiv_lt_0_compat.
      by apply eps.
      by apply sqrt_lt_R0, Rlt_0_2.
    generalize (proj1 (filterlim_locally _ _) Hf (mkposreal _ H)) ; case => d {Hf} /= Hf.
    exists d ; simpl ; intros.
    apply Rle_lt_trans with (1 := Cmod_2Rmax _).
    rewrite Rmult_comm ; apply Rlt_div_r.
    by apply sqrt_lt_R0, Rlt_0_2.
    by apply (Hf y).

  - generalize (proj1 (filterlim_locally _ _) Hf eps) ; case => d {Hf} Hf.
    exists d ; simpl ; intros.
    eapply Rle_lt_trans, (Hf y H H0).
    eapply Rle_trans, Rmax_Cmod.
    simpl ; by apply Rle_refl.
Qed.
Lemma ex_C_R2_RInt_compat : forall (f : R -> C) a b,
  ex_RInt (VV := NormedVectorSpace_prod _ _) f a b
  <-> ex_RInt f a b.
Proof.
  intros f a b.
  split ; intros [l Hl] ; exists l ; by apply is_C_R2_RInt_compat.
Qed.

Lemma is_C_RInt_unique (f : R -> C) (a b : R) (l : C) :
  is_RInt f a b l -> C_RInt f a b = l.
Proof.
  intros Hf.
  apply RInt_fct_extend_pair.
  by apply is_RInt_unique.
  by apply is_RInt_unique.
  by apply is_C_R2_RInt_compat.
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
Lemma C_RInt_scal_R (f : R -> C) (a b : R) (k : R) :
  C_RInt (fun t => scal k (f t)) a b = scal k (C_RInt f a b).
Proof.
  apply injective_projections ; simpl ;
  by rewrite -?RInt_scal.
Qed.
Lemma is_C_RInt_scal f a b (k : C) l :
  is_RInt f a b l -> is_RInt (fun t => k * f t) a b (k * l).
Proof.
  move/is_C_R2_RInt_compat => H.
  apply is_C_R2_RInt_compat.
 
  move: (is_RInt_fct_extend_fst _ _ _ _ H) => /= H1.
  move: (is_RInt_fct_extend_snd _ _ _ _ H) => /= {H} H2.
  apply is_RInt_fct_extend_pair ; simpl.

  apply (is_RInt_minus (VV := AbsRing_NormedVectorSpace _ _)) ;
  apply (is_RInt_scal (VV := AbsRing_NormedVectorSpace _ _)).
  by apply H1.
  by apply H2.
  
  apply (is_RInt_plus (VV := AbsRing_NormedVectorSpace _ _)) ;
  apply (is_RInt_scal (VV := AbsRing_NormedVectorSpace _ _)).
  by apply H2.
  by apply H1.
Qed.
Lemma ex_C_RInt_scal f k a b :
  ex_RInt f a b -> ex_RInt (fun t => k * f t) a b.
Admitted.
Lemma C_RInt_scal (f : R -> C) (k : C) (a b : R) :
  ex_RInt f a b ->
  C_RInt (fun t => k * f t) a b = k * C_RInt f a b.
Proof.
  intros Hf.
  apply is_C_RInt_unique.
  apply is_C_RInt_scal.
  by apply C_RInt_correct.
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
Lemma C_RInt_Chasles (f : R -> C) (a b c : R) :
  ex_RInt f a b -> ex_RInt f b c ->
  C_RInt f a b + C_RInt f b c =
     C_RInt f a c.
Proof.
  intros Hf1 Hf2.
  apply sym_eq, is_C_RInt_unique.
  apply C_RInt_correct, is_C_R2_RInt_compat in Hf1.
  apply C_RInt_correct, is_C_R2_RInt_compat in Hf2.
  
  move: (is_RInt_fct_extend_fst _ _ _ _ Hf1) => /= Hf1_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf1) => /= Hf1_2.
  move: (is_RInt_fct_extend_fst _ _ _ _ Hf2) => /= Hf2_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf2) => /= Hf2_2.
  apply is_C_R2_RInt_compat.
  now apply @is_RInt_Chasles with b ; apply @is_RInt_fct_extend_pair.
Qed.

(** * Definition 2 *)

Definition complex_segment (a b : C) (z : C) :=
  exists (t : R), (0 <= t <= 1)%R /\ z = (1 - t) * a + t * b.

Definition is_C_RInt_segm f z1 z2 l :=
  is_RInt (fun t => (z2 - z1) * f ((1-t)*z1+t*z2)) 0 1 l.
Definition ex_C_RInt_segm (f : C -> C) (z1 z2 : C) :=
  exists l : C, is_C_RInt_segm f z1 z2 l.
Definition C_RInt_segm (f : C -> C) (z1 z2 : C) : C :=
  (z2 - z1) * C_RInt (fun t => f ((1 - t) * z1 + t * z2)) 0 1.

Lemma is_C_RInt_segm_unique (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z1 z2 l -> C_RInt_segm f z1 z2 = l.
Proof.
Admitted.
Lemma C_RInt_segm_correct (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> is_C_RInt_segm f z1 z2 (C_RInt_segm f z1 z2).
Proof.
Admitted.

(** * Proposition 3 *)

Lemma is_C_RInt_segm_swap (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z2 z1 l -> is_C_RInt_segm f z1 z2 (-l).
Proof.
  rewrite /is_C_RInt_segm => H.
  evar (k : C).
  replace (- l) with k.
  apply (is_RInt_swap (VV := C_NVS)).
  apply is_RInt_ext with (fun t : R => scal (-1)((z1 - z2) * f ((1 - (-1 * t + 1)%R) * z2 + (-1 * t + 1)%R * z1)%C)).
    move => x _.
    replace ((1 - (-1 * x + 1)%R) * z2 + (-1 * x + 1)%R * z1)
      with ((1 - x) * z1 + x * z2)
      by (apply injective_projections ; simpl ; ring).
    apply injective_projections ; simpl ; ring.
  apply (is_RInt_comp_lin (VV := C_NVS)  (fun t : R => (z1 - z2) * f ((1 - t) * z2 + t * z1)) (-1) (1) 1 0).
  ring_simplify (-1 * 1 + 1)%R (-1 * 0 + 1)%R.
  apply H.
  by [].
Qed.
Lemma ex_C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z2 z1 -> ex_C_RInt_segm f z1 z2.
Proof.
  intros [l Hl].
  exists (-l) ; by apply is_C_RInt_segm_swap.
Qed.
Lemma C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  - C_RInt_segm f z1 z2 = C_RInt_segm f z2 z1.
Proof.
  unfold C_RInt_segm.
  generalize (opp_mult_l (RK := AbsRing_Ring _) (z2 - z1) (C_RInt (fun t : R => f ((1 - t) * z1 + t * z2)) 0 1)).
  move => /= ->.
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

Lemma is_C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) l1 l2 :
  (exists p : R, z2 = ((1 - p) * z1 + p * z3))
  -> is_C_RInt_segm f z1 z2 l1 -> is_C_RInt_segm f z2 z3 l2
    -> is_C_RInt_segm f z1 z3 (plus l1 l2).
Proof.
  rewrite /is_C_RInt_segm ;
  case => p -> H1 H2.
  
  case: (Req_dec p 0) => Hp0.
  rewrite Hp0 in H1 H2 => {p Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f ((1 - t) * z1 + t * z3))) in H2.
Focus 2.
  move => x _.
  replace ((1 - x) * ((1 - 0) * z1 + 0 * z3) + x * z3) with ((1 - x) * z1 + x * z3) by ring.
  ring.
  apply (is_RInt_ext _ (fun _ => zero)) in H1.
Focus 2.
  move => x _ ; simpl ; ring.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_l.

  case: (Req_dec 1 p) => Hp1.
  rewrite -Hp1 in H1 H2 => {p Hp1 Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f ((1 - t) * z1 + t * z3))) in H1.
Focus 2.
  move => x _.
  replace ((1 - x) * z1 + x * ((1 - 1) * z1 + 1 * z3)) with ((1 - x) * z1 + x * z3) by ring.
  ring.
  apply (is_RInt_ext _ (fun _ => zero)) in H2.
Focus 2.
  move => x _ ; simpl ; ring.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_r.

  case: (Ceq_dec z1 z3) => Hz.
  rewrite -Hz in H1 H2 |- * => {z3 Hz}.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
    apply is_RInt_ext => x _.
    replace ((1 - x) * z1 + x * ((1 - p) * z1 + p * z1)) with z1 by ring.
    replace ((1 - x) * ((1 - p) * z1 + p * z1) + x * z1) with z1 by ring.
    replace ((1 - x) * z1 + x * z1) with z1 by ring.
    apply injective_projections ; simpl ; ring.

  apply (is_C_RInt_scal _ _ _ (/((1 - p) * z1 + p * z3 - z1))) in H1.
  apply (is_RInt_ext _ (fun t => ( (f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))))) in H1.
Focus 2.
  move => x _ ; field.
  replace (((1, 0) - p) * z1 + p * z3 - z1) with (p * (z3 - z1))
    by (apply injective_projections ; simpl ; ring).
  apply Cmult_neq_0.
  contradict Hp0.
  now apply (f_equal (@fst R R)) in Hp0 ; simpl in Hp0.
  now apply Cminus_eq_contra, sym_not_eq.
  apply (is_RInt_ext _ (fun t => opp (scal (-1)%R (f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))))) in H1.
Focus 2.
  move => x _ ; apply injective_projections ; simpl ; ring.

  apply (is_C_RInt_scal _ _ _ (/(z3 - ((1 - p) * z1 + p * z3)))) in H2.
  apply (is_RInt_ext _ (fun t => f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))) in H2.
Focus 2.
  move => x _ ; field.
  replace (z3 - (((1, 0) - p) * z1 + p * z3)) with ((1-p) * (z3 - z1))
    by (apply injective_projections ; simpl ; ring).
  apply Cmult_neq_0.
  contradict Hp1.
  apply (f_equal (@fst R R)) in Hp1 ; simpl in Hp1.
  now apply Rminus_diag_uniq.
  now apply Cminus_eq_contra, sym_not_eq.
  apply (is_RInt_ext _ (fun t => opp (scal (-1)%R (f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))))) in H2.
Focus 2.
  move => x _ ; apply injective_projections ; simpl ; ring.

  evar (k : C).
  replace (plus l1 l2) with k.
  apply is_C_RInt_scal.

  apply @is_RInt_Chasles with p.
  replace 0%R with (/p * 0 + 0)%R in H1 by ring.
  pattern 1%R at 4 in H1.
  replace 1%R with (/p * p + 0)%R in H1 by (by field).
  apply (is_RInt_comp_lin _ (/p) 0 0 p) in H1.
  apply (is_C_RInt_scal _ _ _ p) in H1.
  move: H1 ; apply is_RInt_ext => x Hx.
  replace ((1 - (/ p * x + 0)%R) * z1 + (/ p * x + 0)%R * ((1 - p) * z1 + p * z3))
    with ((1 - x) * z1 + x * z3).
  simpl ; apply injective_projections ; simpl ; by field. 
  apply injective_projections ; simpl ; by field.
  
  clear H1.
  replace 0%R with ((/(1-p)) * p + -/(1-p)*p)%R in H2 by ring.
  pattern 1%R at 6 in H2.
  replace 1%R with ((/(1-p)) * 1 + -/(1-p)*p)%R in H2 by
    (by field ; apply Rminus_eq_contra).
  apply (is_RInt_comp_lin _ (/(1-p)) (-/(1-p)*p) p 1) in H2.
  apply (is_C_RInt_scal _ _ _ (1-p)) in H2.
  move: H2 ; apply is_RInt_ext => x Hx.
  replace ((1 - (/ (1 - p) * x + - / (1 - p) * p)%R) * ((1 - p) * z1 + p * z3) +
      (/ (1 - p) * x + - / (1 - p) * p)%R * z3)
    with ((1 - x) * z1 + x * z3).
  now apply injective_projections ; simpl ; field ; apply Rminus_eq_contra.
  now apply injective_projections ; simpl ; field ; apply Rminus_eq_contra.
  
  apply injective_projections ; simpl ; field.
  replace ((fst z3 + - ((1 + - p) * fst z1 + p * fst z3)) *
    (fst z3 + - ((1 + - p) * fst z1 + p * fst z3)) +
    (snd z3 + - ((1 + - p) * snd z1 + p * snd z3)) *
    (snd z3 + - ((1 + - p) * snd z1 + p * snd z3)))%R
    with ((1 - p) ^ 2 * ((fst z3 - fst z1)² + (snd z3 - snd z1)²))%R
    by (now rewrite /Rsqr /= ; field).
  replace (((1 + - p) * fst z1 + p * fst z3 + - fst z1) *
    ((1 + - p) * fst z1 + p * fst z3 + - fst z1) +
    ((1 + - p) * snd z1 + p * snd z3 + - snd z1) *
    ((1 + - p) * snd z1 + p * snd z3 + - snd z1))%R
    with (p ^ 2 * ((fst z3 - fst z1)² + (snd z3 - snd z1)²))%R
    by (now rewrite /Rsqr /= ; field).
  split ; apply Rmult_integral_contrapositive_currified ;
  try (apply pow_nonzero) ; try (apply Rminus_eq_contra) ; auto ;
  contradict Hz ; apply Rplus_sqr_eq_0 in Hz ;
  now apply sym_eq, injective_projections ; apply Rminus_diag_uniq.
  
  replace ((fst z3 + - ((1 + - p) * fst z1 + p * fst z3)) *
    (fst z3 + - ((1 + - p) * fst z1 + p * fst z3)) +
    (snd z3 + - ((1 + - p) * snd z1 + p * snd z3)) *
    (snd z3 + - ((1 + - p) * snd z1 + p * snd z3)))%R
    with ((1 - p) ^ 2 * ((fst z3 - fst z1)² + (snd z3 - snd z1)²))%R
    by (now rewrite /Rsqr /= ; field).
  replace (((1 + - p) * fst z1 + p * fst z3 + - fst z1) *
    ((1 + - p) * fst z1 + p * fst z3 + - fst z1) +
    ((1 + - p) * snd z1 + p * snd z3 + - snd z1) *
    ((1 + - p) * snd z1 + p * snd z3 + - snd z1))%R
    with (p ^ 2 * ((fst z3 - fst z1)² + (snd z3 - snd z1)²))%R
    by (now rewrite /Rsqr /= ; field).
  split ; apply Rmult_integral_contrapositive_currified ;
  try (apply pow_nonzero) ; try (apply Rminus_eq_contra) ; auto ;
  contradict Hz ; apply Rplus_sqr_eq_0 in Hz ;
  now apply sym_eq, injective_projections ; apply Rminus_diag_uniq.
Qed.
Lemma ex_C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) :
  (exists p : R, z2 = ((1 - p) * z1 + p * z3))
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
    -> ex_C_RInt_segm f z1 z3.
Proof.
  intros Hz2 [l1 H1] [l2 H2] ; exists (plus l1 l2) ;
  by apply is_C_RInt_segm_Chasles with z2.
Qed.
Lemma C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) :
  (exists p : R, z2 = ((1 - p) * z1 + p * z3))
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 = C_RInt_segm f z1 z3.
Proof.
  intros.
  apply sym_eq, is_C_RInt_segm_unique.
  now apply is_C_RInt_segm_Chasles with z2 ;
  try (by apply C_RInt_segm_correct).
Qed.

(** * Proposition 4 *)

Lemma prop4 (f : C -> C) (z1 z2 : C) lf (m : R) :
  is_C_RInt_segm f z1 z2 lf
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod lf <= m * (Cmod (z1 - z2)).
Proof.
  intros Cf Hm.
  apply (RInt_norm (VV := C_NVS)) with (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun _ => Rmult (Cmod (z2 - z1)) m) 0 1.
  by apply Rle_0_1.
  move => x Hx /=.
  rewrite Cmod_mult.
  apply Rmult_le_compat_l.
  by apply Cmod_ge_0.
  apply Hm.
  now exists x ; split.
  by apply Cf.
  replace (m * Cmod (z1 - z2)%C)%R
    with (scal (1 - 0)%R (Cmod (z2 - z1)%C * m)%R).
  apply is_RInt_const.
  rewrite -Cmod_opp Copp_minus_distr ; simpl ; ring.
Qed.

Require Import seq.

Lemma ex_RInt_norm {V} {VV : CompleteNormedVectorSpace V R} (f : R -> V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun x => norm (f x)) a b.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    move/ex_RInt_swap => H ; apply ex_RInt_swap.
    apply Hw.
    by apply Rlt_le.
    by [].
  case: Hab => Hab Hf.
  destruct (proj1 (filterlim_locally_cauchy (fun ptd : SF_seq =>
     scal (sign (b - a)) (Riemann_sum (fun x : R => norm (f x)) ptd))
     (F := Riemann_fine a b))).
Focus 2.
  exists x ; by apply H.

  simpl ; intros.
  destruct (proj2 (filterlim_locally_cauchy (F := (Riemann_fine a b)) (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum f ptd))) Hf eps) as [P [FP HP]].
  simpl in HP.
  clear Hf.
  exists P ; split ; intros.
  by apply FP.
  eapply Rle_lt_trans.
  2: by apply (HP u v).
  apply Rminus_lt_0 in Hab.
  rewrite /sign ; case: Rle_dec (Rlt_le _ _ Hab) => // Hab' _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hab) => // _ _ {Hab'}.
  rewrite !scal_one !Rmult_1_l.
  clear HP.
  wlog: u H / (exists x h, u = mkSF_seq x ([:: h])) => [Hw | Hu].
  move: H ; apply SF_cons_ind with (s := u) => {u} [x0 | h u IH] H.
  
Admitted.

Lemma cont_unif {V} {VV : NormedVectorSpace V R} (f : R -> V) a b :
  (forall x : R, Rmin a b <= x <= Rmax a b -> filterlim f (locally x) (locally (f x)))
  -> forall eps : posreal, exists delta : posreal,
    forall x y, Rmin a b <= x <= Rmax a b -> Rmin a b <= y <= Rmax a b ->
     ball x delta y -> ball (f x) eps (f y).
Proof.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm.
    by apply Hw, Rlt_le.
  rewrite /Rmin /Rmax ; case: Rle_dec => //= _.
  intros Cf eps.

  generalize (fun x Hx => proj1 (filterlim_locally _ _) (Cf x Hx) (pos_div_2 eps)).
  simpl => {Cf} Cf.
  set (P := fun c => a <= c <= b /\
  exists delta : posreal,
    forall x y : R,
    a <= x <= c ->
    a <= y <= c -> Rabs (y + - x) < delta -> norm (minus (f y) (f x)) < eps).
  assert (is_upper_bound P b).
    move => y Hy.
    by apply Hy.
  assert (P a).
    split.
    split => // ; by apply Rle_refl.
    exists (mkposreal _ Rlt_0_1) => x y Hx Hy Hxy.
    replace y with a.
    2: now apply Rle_antisym.
    replace x with a.
    2: now apply Rle_antisym.
    rewrite /minus plus_opp_r norm_zero.
    by apply eps.
  assert (forall x, a <= x <= b -> (forall y, a <= y < x -> P y) -> P x).
    intros.
    case: (Req_dec a x) => Hax.
    by rewrite -Hax.
    split => //.
    destruct (Cf _ H1) as [d1 Hd1].
    destruct (H2 (Rmax a (x - d1 / 2))) as [H3 [d2 Hd2]].
    split.
    apply Rmax_l.
    apply Rmax_case.
    destruct H1.
    by case: H1.
    apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
    exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; simpl ; intros.
    case: (Rle_lt_dec x0 (Rmax a (x - d1 / 2))) => H7.
    
    apply Hd2 ; intuition.
  destruct (completeness P) as [c Hc].
  - by exists b.
  - by exists a.
Admitted.

Lemma ex_RInt_cont {V} {VV : CompleteNormedVectorSpace V R} :
   forall (f : R -> V) (a b : R),
   (forall x : R, Rmin a b <= x <= Rmax a b -> filterlim f (locally x) (locally (f x))) ->
   ex_RInt f a b.
Proof.
  intros f a b.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    rewrite Rmin_comm Rmax_comm => Cf.
    apply ex_RInt_swap.
    apply Hw => //.
    by left.
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ Cf.
  destruct (proj1 (filterlim_locally_cauchy (fun ptd : SF_seq =>
     scal (sign (b - a)) (Riemann_sum (fun x : R => f x) ptd))
     (F := Riemann_fine a b))).

Focus 2.
  exists x.
  by apply H.
  
  move => eps.
  
Admitted.





