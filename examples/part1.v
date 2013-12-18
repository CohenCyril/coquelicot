Require Import Reals ssreflect.
Require Import Coquelicot.

Open Local Scope C_scope.

(** * New in Coquelicot *)

Definition C_RInt (f : R -> C) (a b : R) : C :=
  (RInt (fun t => fst (f t)) a b, RInt (fun t => snd (f t)) a b).

Lemma is_C_RInt_unique (f : R -> C) (a b : R) (l : C) :
  is_RInt f a b l -> C_RInt f a b = l.
Proof.
  intros Hf.
  apply RInt_fct_extend_pair with (3 := Hf).
  by apply is_RInt_unique.
  by apply is_RInt_unique.
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
  intros H.
  move: (is_RInt_fct_extend_fst _ _ _ _ H) => /= H1.
  move: (is_RInt_fct_extend_snd _ _ _ _ H) => /= {H} H2.
  apply (is_RInt_fct_extend_pair (MU := R_NVS) (MV := R_NVS)) ; simpl.

  apply (is_RInt_minus (VV := R_NVS)) ;
  apply (is_RInt_scal (VV := R_NVS)).
  by apply H1.
  by apply H2.

  apply (is_RInt_plus (VV := R_NVS)) ;
  apply (is_RInt_scal (VV := R_NVS)).
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
  apply C_RInt_correct in Hf1.
  apply C_RInt_correct in Hf2.
  
  move: (is_RInt_fct_extend_fst _ _ _ _ Hf1) => /= Hf1_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf1) => /= Hf1_2.
  move: (is_RInt_fct_extend_fst _ _ _ _ Hf2) => /= Hf2_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf2) => /= Hf2_2.
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
  apply is_RInt_swap.
  apply is_RInt_ext with (fun t : R => scal (-1)((z1 - z2) * f ((1 - (-1 * t + 1)%R) * z2 + (-1 * t + 1)%R * z1)%C)).
    move => x _.
    replace ((1 - (-1 * x + 1)%R) * z2 + (-1 * x + 1)%R * z1)
      with ((1 - x) * z1 + x * z2)
      by (apply injective_projections ; simpl ; ring).
    apply injective_projections ; simpl ; ring.
  apply: (is_RInt_comp_lin (fun t : R => (z1 - z2) * f ((1 - t) * z2 + t * z1)) (-1) (1) 1 0).
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
  generalize (opp_mult_l (z2 - z1) (C_RInt (fun t : R => f ((1 - t) * z1 + t * z2)) 0 1)).
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

  unfold k ; change plus with Cplus.
  field.
  change (1, 0) with (RtoC 1).
  split.
  replace (z3 - ((1 - p) * z1 + p * z3)) with ((1 - p) * (z3 - z1)) by ring.
  apply Cmult_neq_0.
  apply Cminus_eq_contra.
  contradict Hp1 ; by apply RtoC_inj.
  by apply Cminus_eq_contra, sym_not_eq.
  replace ((1 - p) * z1 + p * z3 - z1) with (p * (z3 - z1)) by ring.
  apply Cmult_neq_0.
  contradict Hp0 ; by apply RtoC_inj.
  by apply Cminus_eq_contra, sym_not_eq.
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
  rewrite 2!Cmod_norm.
  apply: (RInt_norm (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun _ => Rmult (Cmod (z2 - z1)) m) 0 1).
  by apply Rle_0_1.
  intros x Hx.
  rewrite <- Cmod_norm.
  rewrite Cmod_mult.
  apply Rmult_le_compat_l.
  by apply Cmod_ge_0.
  apply Hm.
  now exists x ; split.
  by apply Cf.
  replace (m * norm (z1 - z2)%C)%R
    with (scal (1 - 0)%R (Cmod (z2 - z1)%C * m)%R).
  apply @is_RInt_const.
  rewrite -Cmod_norm -Cmod_opp Copp_minus_distr ; simpl ; ring.
Qed.

(** * Proposition 5 *)

Section Prop5_filter.

Context {T : Type}.

Definition filter_sqr (F : (T -> Prop) -> Prop) (P : (T * T -> Prop)) : Prop :=
  exists Q, F Q /\ (forall x y, Q x -> Q y -> P (x,y)).

Global Instance filter_sqr_filter :
  forall {F} {FF : Filter F}, Filter (filter_sqr F).
Proof.
  intros F FF.
  constructor.
  - exists (fun _ => True) ; split => //.
    by apply filter_true.
  - intros P1 P2 [Q1 H1] [Q2 H2].
    exists (fun x => Q1 x /\ Q2 x) ; split.
    now apply filter_and.
    intros ; split.
    now apply H1.
    now apply H2.
  - intros P1 P2 H [Q1 H1].
    exists Q1 ; split.
    by apply H1.
    now intros ; apply H, H1.
Qed.

Global Instance filter_sqr_properfilter :
  forall {F} {FF : ProperFilter F}, ProperFilter (filter_sqr F).
Proof.
  intros F FF.
  constructor.
  move => P [Q [FQ H]].
  destruct (filter_ex _ FQ).
  exists (x,x).
  by apply H.
  by apply filter_sqr_filter.
Qed.

Goal forall F G, filter_le F G -> filter_le (filter_sqr F) (filter_sqr G).
Admitted.

End Prop5_filter.

Section Prop5_metric.

Context {U V : Type} {MU : MetricBall U} {MV : MetricBall V}.

Lemma is_filter_lim_filtermap : forall F x (f : U -> V),
  filterlim f (locally x) (locally (f x))
  -> is_filter_lim F x
  -> is_filter_lim (filtermap f F) (f x).
Proof.
  intros F x f Cf Fx P HP.
  apply Cf in HP.
  now apply Fx.
Qed.

End Prop5_metric.

Section Prop5_derive.

Context {K : Type} {FK : AbsRing K}.

Lemma filterdiff_mult : forall (x : K * K), 
  filterdiff (fun t => mult (fst t) (snd t)) (locally x)
    (fun t => plus (mult (fst x) (snd t)) (mult (fst t) (snd x))).
Proof.
  move => x ; split.
  - admit.
  - move => y Hy.
    generalize (is_filter_lim_locally_unique _ _ Hy) => {Hy} /= Hy.
    simpl => eps.
    apply filter_forall => z.
    rewrite /minus mult_distr_l mult_distr_r !opp_plus ;
    rewrite -(opp_mult_l (RK := absring_ring)) -(opp_mult_r (RK := absring_ring)) ;
    rewrite !opp_opp.
    rewrite (opp_mult_l (RK := absring_ring) _ (snd z)) (opp_mult_r (RK := absring_ring) (fst z)).
    
Admitted.

Context {U} {VU : NormedVectorSpace U K}.

Lemma filterdiff_mult_fct (f g : U -> K) F (lf lg : U -> K) :
  filterdiff f F lf -> filterdiff g F lg
  -> filterdiff (fun t => mult (f t) (g t)) F (fun t => mult (lf t) (lg t)).
Proof.
Admitted.

End Prop5_derive.

Section Prop5_diff.

Context {U V K : Type} {FK : AbsRing K} {VU : NormedVectorSpace U K} {VV : NormedVectorSpace V K}.

Lemma filterdiff_locally F (f : U -> V) x l :
  is_filter_lim F x ->
  filterdiff f (locally x) l ->
  filterdiff f F l.
Proof.
intros Fx [Hl Df].
split.
exact Hl.
intros z Fz eps.
specialize (Df _ (fun P H => H) eps).
apply Fz.
simpl in Df.
Admitted.

Lemma is_linear_pair_fct (l1 l2 : U -> V) :
  is_linear l1 -> is_linear l2 -> is_linear (fun t => (l1 t, l2 t)).
Proof.
  intros [Hp1 Hs1 [M1 Hn1]] [Hp2 Hs2 [M2 Hn2]] ; split ; simpl.
  - move => x y ; by rewrite Hp1 Hp2.
  - move => k x ; by rewrite Hs1 Hs2.
  - exists (sqrt (M1 ^ 2 + M2 ^ 2)) ; split.
    apply sqrt_pos.
    intros x ; ring_simplify (norm (l1 x) * (norm (l1 x) * 1) + norm (l2 x) * (norm (l2 x) * 1))%R.
    eapply Rle_trans.
    apply sqrt_le_1_alt.
    apply Rplus_le_compat ;
    apply pow_incr ; split.
    by apply norm_ge_0.
    by apply Hn1.
    by apply norm_ge_0.
    by apply Hn2.
    apply Req_le.
    apply Rsqr_inj.
    by apply sqrt_pos.
    apply Rmult_le_pos.
    by apply sqrt_pos.
    by apply norm_ge_0.
    rewrite /Rsqr sqrt_sqrt.
    rewrite {1}(Rmult_comm (sqrt (M1 ^ 2 + M2 ^ 2))) Rmult_assoc.
    rewrite -(Rmult_assoc (sqrt (M1 ^ 2 + M2 ^ 2))) sqrt_sqrt.
    ring.
    apply Rplus_le_le_0_compat ; apply pow2_ge_0.
    apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Qed.

Lemma filterdiff_plus_fct {F} {FF : Filter F} (f g : U -> V) (lf lg : U -> V) :
  filterdiff f F lf -> filterdiff g F lg
  -> filterdiff (fun t => plus (f t) (g t)) F (fun t => plus (lf t) (lg t)).
Proof.
  intros [Lf Df] [Lg Dg].
  split.
  admit.
  move => x Hx /=.
  generalize (Df _ Hx) => {Df} Df.
  generalize (Dg _ Hx) => {Dg} Dg.
  generalize (domin_plus _ _ _ Df Dg) ; simpl.
  apply domin_rw_r.
  apply equiv_ext_loc, filter_forall => y /=.
  rewrite /minus (linear_plus lf Lf) (linear_plus lg Lg)
    (linear_opp lf _ Lf) (linear_opp lg _ Lg).
  rewrite !opp_plus !opp_opp -!plus_assoc.
  apply f_equal.
  rewrite !(plus_comm (g y)) -!plus_assoc.
  apply f_equal.
  by rewrite !(plus_comm (opp (g x))) -!plus_assoc.
Qed.

Lemma filterdiff_linear {F} {FF : Filter F} (l : U -> V) :
  is_linear l -> filterdiff l F l.
Proof.
  intros Hl.
  split.
  by apply Hl.
  move => x Hx eps.
  apply filter_forall => y.
  rewrite /minus linear_plus //.
  rewrite (linear_opp l) //.
  rewrite plus_opp_r norm_zero.
  apply Rmult_le_pos.
  by apply Rlt_le, eps.
  by apply norm_ge_0.
Qed.

End Prop5_diff.

Section Prop5_RInt.

Context {V} {VV : NormedVectorSpace V R}.

Lemma prop5_R (f g : R -> V) (a b : R) :
  (forall z, Rmin a b <= z <= Rmax a b -> filterdiff g (locally z) (fun y => scal y (f z)))
  -> (forall z, filterlim f (locally z) (locally (f z)))
  -> is_RInt f a b (minus (g b) (g a)).
Admitted.

End Prop5_RInt.

Lemma filterdiff_R2_C (f : C -> C) (z : C) (l : C) :
  let VV := NormedVectorSpace_prod R_NVS R_NVS in
  is_C_derive f z l -> filterdiff (VV := VV) f (locally z) (fun z => scal z l).
Admitted.

Lemma prop5 (f g : C -> C) (z1 z2 : C) :
  (forall z, is_C_derive g z (f z))
  -> (forall z, filterlim f (locally z) (locally (f z)))
  -> is_C_RInt_segm f z1 z2 (g z2 - g z1).
Proof.
  intros Dg Cf.
  unfold is_C_RInt_segm.
    replace (g z2 - g z1)
      with (minus (g ((1 - 1) * z1 + 1 * z2)) (g ((1 - 0) * z1 + 0 * z2))).
    2: simpl ; congr (g _- g _) ; ring.
    apply (prop5_R (VV := NormedVectorSpace_prod R_NVS R_NVS) (fun t : R => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun t => g ((1 - t) * z1 + t * z2)) 0 1).
    + intros z Hz.
      eapply filterdiff_ext_lin.
      apply (filterdiff_comp (fun t : R => (1 - t) * z1 + t * z2) g (fun y : R => scal y (z2 - z1)) (fun t => scal t (f ((1 - z) * z1 + z * z2)))).
      apply filterdiff_ext with (fun t : R => z1 + scal t (z2 - z1)).
      intro y ; apply injective_projections ; simpl ; ring.
      apply filterdiff_ext_lin with (fun y => plus zero (scal y (z2 - z1))).
      apply: filterdiff_plus_fct.
      apply: filterdiff_const.
      apply filterdiff_linear.
      by apply: is_linear_scal.
      move => y.
      by apply plus_zero_l.
      unfold is_C_derive in Dg.
      destruct (Dg ((1 - z) * z1 + z * z2)) as [Lf Dg'].
      apply filterdiff_locally with ((1 - z) * z1 + z * z2).
      apply (is_filter_lim_filtermap _ _ (fun t : R => (1 - t) * z1 + t * z2)).
      admit.
      now intros P HP.
      apply (filterdiff_R2_C g ((1 - z) * z1 + z * z2) (f ((1 - z) * z1 + z * z2))).
      apply (Dg ((1 - z) * z1 + z * z2)).
      intros ; apply injective_projections ; simpl ; ring.


  admit.
Qed.

Require Import seq.

Lemma ex_RInt_norm {V} {VV : CompleteNormedVectorSpace V R} (f : R -> V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun x => norm (f x)) a b.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab] Hf.
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    apply ex_RInt_swap in Hf ; apply ex_RInt_swap.
    apply Hw.
    by apply Rlt_le.
    by [].
  destruct (ex_RInt_ub f a b Hf) as [Mf Hm].
  move: Hm ; rewrite /Rmin /Rmax ; case: Rle_dec => //= _ Hm.
  case: Hab => Hab.
  destruct (proj1 (filterlim_locally_cauchy (fun ptd : SF_seq =>
     scal (sign (b - a)) (Riemann_sum (fun x : R => norm (f x)) ptd))
     (F := Riemann_fine a b))) ; [ | exists x ; by apply H].

  simpl ; intros.

(*
  destruct (proj2 (filterlim_locally_cauchy (F := (Riemann_fine a b))
    (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum f ptd)))
    Hf (pos_div_2 eps)) as [P [[dP FP] HP]].
  simpl in HP.
  
  cut (exists P0 : SF_seq -> Prop, Riemann_fine a b P0 /\
    (forall u v : SF_seq, SF_lx u = SF_lx v ->
    P0 u -> P0 v ->
    Rabs (Riemann_sum (fun x : R => norm (f x)) v 
      - Riemann_sum (fun x : R => norm (f x)) u) < eps)).
  case => P0 [RP0 HP0].
  exists P0 ; split.
  by apply RP0.
  intros.
  rewrite (proj1 (sign_0_lt _)) ?Rmult_1_l.
  move: v H H0 ;
  apply SF_cons_ind with (s := u) => {u} [x0 | h u IH] v H H0.
  rewrite {2}/Riemann_sum /= Ropp_R0 Rplus_.
*)
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
(*
  destruct (proj1 (filterlim_locally_cauchy (fun ptd : SF_seq =>
     scal (sign (b - a)) (Riemann_sum (fun x : R => f x) ptd))
     (F := Riemann_fine a b))).

Focus 2.
  exists x.
  by apply H.
  
  move => eps.
*)
Admitted.





