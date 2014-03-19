Require Import Reals ssreflect.
Require Import Coquelicot.

(** Exponential *)

Section INK.

Context {K : Ring}.

Fixpoint INK (n : nat) : K :=
  match n with
  | O => zero
  | S n => plus one (INK n)
  end.
Definition IZK (n : Z) : K :=
  match n with
  | 0%Z => zero
  | Z.pos n => INK (Pos.to_nat n)
  | Z.neg n => opp (INK (Pos.to_nat n))
  end.

End INK.

(* Search UniformSpace AbsRing.

Lemma ex_exp {K : AbsRing} {CK : @CompleteSpace.mixin_of (AbsRing_UniformSpace K)}
  (a : nat -> K) (x : K) :
  (forall k, mult (a k) (INK (fact k)) = one) ->
  ex_pseries a x.
Proof.
  intros Hfact.
  unfold ex_pseries, ex_series, is_series.
  assert (H := proj1 (filterlim_locally_cauchy (F := eventually) (sum_n (fun k : nat => scal (pow_n x k) (a k))))) ;
  destruct H as [l Hl].
  intros eps.
  rewrite /ball /=.
Qed.*)

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
  apply RInt_scal.
Qed.

Lemma is_C_RInt_scal f a b (k : C) l :
  is_RInt f a b l -> is_RInt (fun t => k * f t) a b (k * l).
Proof.
  intros H.
  move: (is_RInt_fct_extend_fst _ _ _ _ H) => /= H1.
  move: (is_RInt_fct_extend_snd _ _ _ _ H) => /= {H} H2.
  apply is_RInt_fct_extend_pair ; simpl.
  by apply: is_RInt_minus ; apply: is_RInt_scal.
  by apply: is_RInt_plus ; apply: is_RInt_scal.
Qed.

Lemma ex_C_RInt_scal f k a b :
  ex_RInt f a b -> ex_RInt (fun t => k * f t) a b.
Proof.
  intros [lf If].
  eexists.
  apply is_C_RInt_scal ; eassumption.
Qed.
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
  now apply @is_RInt_Chasles with b ; apply is_RInt_fct_extend_pair.
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
  intros.
  unfold C_RInt_segm.
  rewrite -C_RInt_scal.
  by apply is_C_RInt_unique.
  case: (Ceq_dec z1 z2) => Hz.
  - rewrite Hz.
    apply ex_RInt_ext with (fun _ => f z2).
      move => x _.
      apply f_equal ; ring.
    apply ex_RInt_const.
  - eapply ex_RInt_ext.
    2: apply (fun f => ex_C_RInt_scal f (/(z2 - z1))).
    2: eexists ; apply H.
    simpl => x _.
    fold C.
    field.
    contradict Hz.
    replace z2 with (z1 + (z2 - z1)) by ring.
    rewrite Hz ; ring.
Qed.
Lemma C_RInt_segm_correct (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> is_C_RInt_segm f z1 z2 (C_RInt_segm f z1 z2).
Proof.
  intros [l If].
  now rewrite (is_C_RInt_segm_unique _ _ _ _ If).
Qed.

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
    rewrite scal_opp_one.
    change opp with Copp.
    change eq with (@eq C).
    field.
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
  rewrite /opp /mult /=.
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

Lemma scal_R_Cmult :
  forall (x : R) (y : C),
  scal (V := C_R_ModuleSpace) x y = Cmult x y.
Proof.
intros x y.
apply injective_projections ;
  rewrite /scal /= /scal /= /mult /= ; ring.
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
  change eq with (@eq C).
  ring.
  apply (is_RInt_ext _ (fun _ => zero)) in H1.
Focus 2.
  move => x _ ; simpl.
  change zero with (RtoC 0).
  change eq with (@eq C).
  ring.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_l.

  case: (Req_dec 1 p) => Hp1.
  rewrite -Hp1 in H1 H2 => {p Hp1 Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f ((1 - t) * z1 + t * z3))) in H1.
Focus 2.
  move => x _.
  replace ((1 - x) * z1 + x * ((1 - 1) * z1 + 1 * z3)) with ((1 - x) * z1 + x * z3) by ring.
  change eq with (@eq C).
  ring.
  apply (is_RInt_ext _ (fun _ => zero)) in H2.
Focus 2.
  move => x _ ; simpl.
  change zero with (RtoC 0).
  change eq with (@eq C).
  ring.
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
    apply injective_projections ; rewrite /= /plus /= ; ring.

  apply (is_C_RInt_scal _ _ _ (/((1 - p) * z1 + p * z3 - z1))) in H1.
  apply (is_RInt_ext _ (fun t => ( (f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))))) in H1.
Focus 2.
  move => x _.
  change eq with (@eq C).
  field.
  replace (((1, 0) - p) * z1 + p * z3 - z1) with (p * (z3 - z1))
    by (apply injective_projections ; simpl ; ring).
  apply Cmult_neq_0.
  contradict Hp0.
  now apply (f_equal (@fst R R)) in Hp0 ; simpl in Hp0.
  now apply Cminus_eq_contra, sym_not_eq.
  apply (is_RInt_ext _ (fun t => opp (scal (-1)%R (f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))))) in H1.
Focus 2.
  intros x _.
  by rewrite scal_opp_one opp_opp.

  apply (is_C_RInt_scal _ _ _ (/(z3 - ((1 - p) * z1 + p * z3)))) in H2.
  apply (is_RInt_ext _ (fun t => f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))) in H2.
Focus 2.
  move => x _.
  change eq with (@eq C).
  field.
  change (1, 0)%R with (RtoC 1).
  replace (z3 - ((1 - p) * z1 + p * z3)) with ((1-p) * (z3 - z1)) by ring.
  apply Cmult_neq_0.
  contradict Hp1.
  apply (f_equal (@fst R R)) in Hp1 ; simpl in Hp1.
  now apply Rminus_diag_uniq.
  now apply Cminus_eq_contra, sym_not_eq.
  apply (is_RInt_ext _ (fun t => opp (scal (-1)%R (f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))))) in H2.
Focus 2.
  intros x _.
  by rewrite scal_opp_one opp_opp.

  evar (k : C).
  replace (plus l1 l2) with k.
  apply is_C_RInt_scal.

  apply is_RInt_Chasles with p.
  replace 0%R with (/p * 0 + 0)%R in H1 by ring.
  pattern 1%R at 4 in H1.
  replace 1%R with (/p * p + 0)%R in H1 by (by field).
  apply (is_RInt_comp_lin _ (/p) 0 0 p) in H1.
  apply (is_C_RInt_scal _ _ _ p) in H1.
  move: H1 ; apply is_RInt_ext => x Hx.
  replace ((1 - (/ p * x + 0)%R) * z1 + (/ p * x + 0)%R * ((1 - p) * z1 + p * z3))
    with ((1 - x) * z1 + x * z3).
  rewrite scal_opp_one opp_opp scal_R_Cmult.
  apply injective_projections ; simpl ; by field.
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
  rewrite scal_opp_one opp_opp scal_R_Cmult.
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
  replace (m * _)%R
    with (scal (1 - 0)%R (Cmod (z2 - z1)%C * m)%R).
  apply: is_RInt_const.
  rewrite -Cmod_norm -Cmod_opp Copp_minus_distr ; simpl.
  rewrite /scal /= /mult /=.
  ring.
Qed.

(** * Proposition 5 *)

Section Continuity.

Context {U V : UniformSpace}.

Lemma continuous_ext_loc (f g : U -> V) x :
  continuous f x -> locally x (fun x => f x = g x)
  -> continuous g x.
Proof.
  intros Cf Heq.
  eapply filterlim_ext_loc.
  apply Heq.
  replace (g x) with (f x).
  by apply Cf.
  by apply (locally_singleton x (fun x : U => f x = g x)).
Qed.

Lemma continuous_const (a : V) x :
  continuous (fun (_ : U) => a) x.
Proof.
  by apply filterlim_const.
Qed.

End Continuity.

Section C1_ext.

Context {V : NormedModule R_AbsRing}.

Lemma C1_extension_right (f g : R -> V) lb (a b : R) :
   a < b ->
   (forall c : R, a < c < b -> continuous f c) ->
   (filterlim f (at_left b) (locally lb)) ->
   (forall c : R, a < c < b -> is_derive g c (f c)) ->
   (filterdiff g (at_left b) (fun x => scal x lb)) ->
   {g0 : R -> V &
   {f0 : R -> V | (forall c : R, a < c -> continuous f0 c)
                /\ (forall c : R, a < c -> is_derive g0 c (f0 c))
                /\ (forall c : R, c < b -> g0 c = g c /\ f0 c = f c)
                /\ f0 b = lb}}.
Proof.
  intros Hab Cf Cfb Dg Dgb.
  set g0 := fun x => match Rlt_dec x b with
                     | left _ => g x
                     | right _ => plus (g b) (scal (x - b)%R lb)
                     end.
  set f0 := fun x => match Rlt_dec x b with
                     | left _ => f x
                     | right _ => lb
                     end.
  exists g0, f0.
  assert (Hg0 : forall c : R, c < b -> g0 c = g c).
    intros c Hc.
    rewrite /g0.
    case: Rlt_dec => //.
  assert (Hf0 : forall c : R, c < b -> f0 c = f c).
    intros c Hc.
    rewrite /f0.
    case: Rlt_dec => //.
  assert (Hf0b : f0 b = lb).
    rewrite /f0.
    case: Rlt_dec (Rlt_irrefl b) => //.
  split.
  - intros c Hac.
    case: (Rlt_le_dec c b) => Hcb.
    eapply continuous_ext_loc.
    apply Cf ; by split.
    apply (locally_interval _ _ m_infty b) => //= y _ Hyb.
    by apply sym_eq, Hf0.
    case: Hcb => Hcb.
    apply (continuous_ext_loc (fun _ => lb)).
    apply continuous_const.
    apply (locally_interval _ _ b p_infty) => //= y Hyb _.
    rewrite /f0.
    case: Rlt_dec => // H.
    contradict H.
    by apply Rle_not_lt, Rlt_le.
    rewrite -Hcb.
    apply filterlim_locally => eps.
    destruct (proj1 (filterlim_locally _ _) Cfb eps) as [d Hd].
    rewrite Hf0b.
    exists d => /= y Hy.
    rewrite /f0 ; case: Rlt_dec => Hyb.
    by apply Hd.
    by apply ball_center.
  split.
  - intros c Hac.
    case: (Rlt_le_dec c b) => Hcb.
    eapply is_derive_ext_loc.
    2: rewrite Hf0 // ; apply Dg ; by split.
    apply (locally_interval _ _ m_infty b) => //= y _ Hyb.
    by apply sym_eq, Hg0.
    case: Hcb => Hcb.
    apply (is_derive_ext_loc (fun x => plus (g b) (scal (x - b)%R lb))).
    apply (locally_interval _ _ b p_infty) => //= y Hyb _.
    rewrite /g0.
    case: Rlt_dec => // H.
    contradict H.
    by apply Rle_not_lt, Rlt_le.
    evar_last.
    apply is_derive_plus.
    apply is_derive_const.
    apply @is_derive_scal_l.
    apply @is_derive_minus.
    apply is_derive_id.
    apply is_derive_const.
    rewrite plus_zero_l minus_zero_r scal_one.
    rewrite /f0 ; case: Rlt_dec => // H.
    contradict H.
    by apply Rle_not_lt, Rlt_le.
    rewrite -Hcb.
    split.
    by apply is_linear_scal_l.
    simpl => x Hx.
    case: Dgb => /= Lgb Dgb.
    apply is_filter_lim_locally_unique_R in Hx.
    rewrite -Hx.
    intros eps.
    destruct (fun H => Dgb b H eps) as [d Hd].
    intros P [eP HP].
    exists eP => y Hy _ ; by apply HP.
    exists d => /= y Hy.
    rewrite /g0 /f0.
    case: Rlt_dec => /= Hyb ;
    case: Rlt_dec (Rlt_irrefl b) => // _ _ ;
    rewrite Rminus_eq_0 scal_zero_l plus_zero_r.
    by apply Hd.
    rewrite plus_comm {2}/minus -plus_assoc plus_opp_r 
      plus_zero_r minus_eq_zero norm_zero.
    apply Rmult_le_pos.
    by apply Rlt_le, eps.
    by apply norm_ge_0.
    repeat split.
    by apply Hg0.
    by apply Hf0.
    by apply Hf0b.
Qed.

End C1_ext.

Section Prop5_RInt.

Context {V : NormedModule R_AbsRing}.

Lemma FTA (f g : R -> V) (a b : R) :
  (forall z, Rmin a b <= z <= Rmax a b -> is_derive g z (f z))
  -> (forall z, Rmin a b <= z <= Rmax a b -> continuous f z)
  -> is_RInt f a b (minus (g b) (g a)).
Proof.
  wlog: a b / (a < b) => [Hw | Hab] Dg Cf.
  
  
Admitted.

End Prop5_RInt.



Lemma prop5 (f g : C -> C) (z1 z2 : C) :
  (forall z, is_C_derive g z (f z))
  -> (forall z, continuous f z)
  -> is_C_RInt_segm f z1 z2 (g z2 - g z1).
Proof.
  intros Dg Cf.
  
Qed.




Lemma filterdiff_R2_C (f : C -> C) (z : C) (l : C) :
  is_C_derive f z l -> filterdiff (V := C_R_NormedModule) f (locally z) (fun z : C => scal z l).
Admitted.

Lemma C_complete :
  forall F : (C -> Prop) -> Prop,
  ProperFilter F -> cauchy F ->
  {x : C | forall eps : posreal, F (ball x eps)}.
Proof.
  intros.

  set (F1 := fun (P : R -> Prop) => exists Q, F Q /\ forall z : C, Q z -> P (fst z)).
  destruct (complete_cauchy F1) as [x Hx].
  repeat split.
  - intros P [Q [HQ HP]].
    destruct (filter_ex Q HQ).
    exists (fst x).
    by apply HP.
  - exists (fun _ => True) ; split => //.
    by apply filter_forall.
  - intros P1 P2 [Q1 [HQ1 HP1]] [Q2 [HQ2 HP2]].
    exists (fun x => Q1 x /\ Q2 x) ; split.
    by apply filter_and.
    split ; intuition.
  - intros P1 P2 H1 [Q1 [HQ1 HP1]].
    exists Q1 ; split ; intuition.
  - intros eps.
    destruct (H0 eps).
    exists (fst x).
    eexists ; split.
    apply H1.
    simpl ; intros.
    by apply H2.

  set (F2 := fun (P : R -> Prop) => exists Q, F Q /\ forall z : C, Q z -> P (snd z)).
  destruct (complete_cauchy F2) as [y Hy].
  repeat split.
  - intros P [Q [HQ HP]].
    destruct (filter_ex Q HQ).
    exists (snd x0).
    by apply HP.
  - exists (fun _ => True) ; split => //.
    by apply filter_forall.
  - intros P1 P2 [Q1 [HQ1 HP1]] [Q2 [HQ2 HP2]].
    exists (fun x => Q1 x /\ Q2 x) ; split.
    by apply filter_and.
    split ; intuition.
  - intros P1 P2 H1 [Q1 [HQ1 HP1]].
    exists Q1 ; split ; intuition.
  - intros eps.
    destruct (H0 eps).
    exists (snd x0).
    eexists ; split.
    apply H1.
    simpl ; intros.
    by apply H2.

  exists (x,y) => eps.
  destruct (Hx eps) as [Qx [HQx HPx]].
  destruct (Hy eps) as [Qy [HQy HPy]].
  generalize (filter_and _ _ HQx HQy).
  apply filter_imp => z [Qxz Qyz].
  split.
  by apply HPx.
  by apply HPy.
Qed.

Definition C_CompleteSpace_mixin :=
  CompleteSpace.Mixin C_UniformSpace C_complete.

Canonical C_CompleteSpace :=
  CompleteSpace.Pack C (CompleteSpace.Class _ _ C_CompleteSpace_mixin) C.

Canonical C_R_CompleteNormedModule :=
  CompleteNormedModule.Pack R_AbsRing C (CompleteNormedModule.Class _ _ (NormedModule.class _ C_R_NormedModule) (CompleteSpace.class C_CompleteSpace)) C.


Require Import seq.

Lemma ex_RInt_norm {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b : R) :
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

Admitted.