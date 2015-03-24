Require Import Reals Ssreflect.ssreflect.
Require Import Coquelicot.

(** * Additionnal Lemmas *)

(** ** Complex.v *)

Open Local Scope C_scope.

Lemma scal_R_Cmult :
  forall (x : R) (y : C),
  scal (V := C_R_ModuleSpace) x y = Cmult x y.
Proof.
intros x y.
apply injective_projections ;
  rewrite /scal /= /scal /= /mult /= ; ring.
Qed.
Lemma RtoC_plus (x y : R) :
  RtoC (x + y) = RtoC x + RtoC y.
Proof.
  unfold RtoC, Cplus ; simpl.
  by rewrite Rplus_0_r.
Qed.
Lemma RtoC_opp (x : R) :
  RtoC (- x) = - RtoC x.
Proof.
  unfold RtoC, Copp ; simpl.
  by rewrite Ropp_0.
Qed.
Lemma RtoC_minus (x y : R) :
  RtoC (x - y) = RtoC x - RtoC y.
Proof.
  by rewrite /Cminus -RtoC_opp -RtoC_plus.
Qed.
Lemma RtoC_mult (x y : R) :
  RtoC (x * y) = RtoC x * RtoC y.
Proof.
  unfold RtoC, Cmult ; simpl.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma is_linear_C_R (l : C -> C) :
  is_linear (U := C_NormedModule) (V := C_NormedModule) l ->
  is_linear (U := C_R_NormedModule) (V := C_R_NormedModule) l.
Proof.
  intros Lf.
  split.
  intros ; apply Lf.
  simpl ; intros.
  rewrite !scal_R_Cmult ; by apply Lf.
  case: Lf => _ _ [M Lf].
  exists M ; split.
  by apply Lf.
  intros.
  rewrite -!Cmod_norm.
  apply Lf.
Qed.

Lemma is_linear_RtoC : is_linear RtoC.
Proof.
  split => //=.
  by intros ; rewrite RtoC_plus.
  intros ; rewrite {2}/scal /= /prod_scal /= scal_zero_r.
  reflexivity.
  exists (sqrt 2) ; split.
  apply Rlt_sqrt2_0.
  intros.
  eapply Rle_trans.
  rewrite -Cmod_norm.
  apply Cmod_2Rmax.
  simpl.
  rewrite Rabs_R0.
  rewrite Rmax_left.
  apply Rle_refl.
  apply Rabs_pos.
Qed.

Lemma continuous_RtoC x : continuous RtoC x.
Proof.
  apply filterlim_locally.
  intros eps ; exists eps => /= y Hy.
  split => //=.
  by apply ball_center.
Qed.

Lemma locally_C x P :
  locally (T := C_UniformSpace) x P <-> locally (T := AbsRing_UniformSpace C_AbsRing) x P.
Proof.
  split => [[e He] | [e He]].
  - exists e => /= y Hy.
    apply He.
    split.
    eapply Rle_lt_trans, Hy.
    eapply Rle_trans, Rmax_Cmod.
    apply Rmax_l.
    eapply Rle_lt_trans, Hy.
    eapply Rle_trans, Rmax_Cmod.
    apply Rmax_r.
  - assert (Hd : 0 < e / sqrt 2).
    apply Rdiv_lt_0_compat.
    by apply e.
    apply Rlt_sqrt2_0.
    exists (mkposreal _ Hd) => /= y [Hy1 Hy2].
    apply He.
    eapply Rle_lt_trans.
    apply Cmod_2Rmax.
    rewrite Rmult_comm ; apply Rlt_div_r.
    apply Rlt_sqrt2_0.
    apply Rmax_case.
    by apply Hy1.
    by apply Hy2.
Qed.
Lemma continuous_C_id_1 (x : C) :
  continuous (T := C_UniformSpace) (U := AbsRing_UniformSpace C_AbsRing) (fun y => y) x.
Proof.
  intros P HP.
  by apply locally_C.
Qed.
Lemma continuous_C_id_2 (x : C) :
  continuous (T := AbsRing_UniformSpace C_AbsRing) (U := C_UniformSpace) (fun y => y) x.
Proof.
  intros P HP.
  by apply locally_C.
Qed.
Lemma continuous_C (f : C -> C) (x : C) :
  continuous (T := C_UniformSpace) (U := C_UniformSpace) f x
  <-> continuous (T := AbsRing_UniformSpace C_AbsRing) (U := AbsRing_UniformSpace C_AbsRing) f x.
Proof.
  split => H.
  - intros P HP.
    by apply locally_C, H, locally_C.
  - intros P HP.
    by apply locally_C, H, locally_C.
Qed.

Lemma is_C_derive_filterdiff f x df:
  is_C_derive f x df
  -> filterdiff (U := C_R_NormedModule) (V := C_R_NormedModule) f (locally x) (fun u => scal u df).
Proof.
  case => Lf Hf.
  split.
  by apply is_linear_C_R.
  intros y Hy.
  apply Hf in Hy => {Hf}.
  intros eps.
  case: (Hy eps) => {Hy} /= delta Hy.
  assert (Hd : 0 < delta / sqrt 2).
    apply Rdiv_lt_0_compat.
    by apply delta.
    apply sqrt_lt_R0, Rlt_0_2.
  eexists (mkposreal _ Hd) => /= z [Hz1 Hz2].
  rewrite -!Cmod_norm.
  apply Hy.
  apply C_NormedModule_mixin_compat1.
  eapply Rle_lt_trans.
  apply Cmod_2Rmax.
  apply Rmax_case ; rewrite Rmult_comm ; apply Rlt_div_r.
  apply sqrt_lt_R0, Rlt_0_2.
  apply Hz1.
  apply sqrt_lt_R0, Rlt_0_2.
  apply Hz2.
Qed.

(** * Intégrale le long d’un segment *)

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
Lemma C_RInt_const c a b :
  C_RInt (fun _ => c) a b = scal (b - a) c.
Proof.
  apply injective_projections ; simpl ;
  rewrite RInt_const ; ring.
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

Lemma is_C_RInt_segm_const c z1 z2 :
  is_C_RInt_segm (fun _ => c) z1 z2 ((z2 - z1) * c).
Proof.
  unfold is_C_RInt_segm.
  evar_last.
  apply is_RInt_const.
  by rewrite Rminus_0_r @scal_one.
Qed.
Lemma ex_C_RInt_segm_const c z1 z2 :
  ex_C_RInt_segm (fun _ => c) z1 z2.
Proof.
  eexists ; by apply is_C_RInt_segm_const.
Qed.
Lemma C_RInt_segm_const c z1 z2 :
  C_RInt_segm (fun _ => c) z1 z2 = (z2 - z1) * c.
Proof.
  apply is_C_RInt_segm_unique.
  by apply is_C_RInt_segm_const.
Qed.

Lemma is_C_RInt_segm_plus (f g : C -> C) (z1 z2 If Ig : C) :
  is_C_RInt_segm f z1 z2 If -> is_C_RInt_segm g z1 z2 Ig
  -> is_C_RInt_segm (fun z => f z + g z) z1 z2 (If + Ig).
Proof.
  unfold is_C_RInt_segm.
  intros Hf Hg.
  move: (is_RInt_plus _ _ _ _ _ _ Hf Hg).
  apply is_RInt_ext.
  intros x _.
  change plus with Cplus.
  by simpl ; ring_simplify.
Qed.
Lemma ex_C_RInt_segm_plus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> ex_C_RInt_segm (fun z => f z + g z) z1 z2.
Proof.
  intros (If,Hf) (Ig,Hg).
  exists (If + Ig).
  by apply is_C_RInt_segm_plus.
Qed.
Lemma C_RInt_segm_plus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> C_RInt_segm (fun z => f z + g z) z1 z2 = C_RInt_segm f z1 z2 + C_RInt_segm g z1 z2.
Proof.
  intros Hf Hg.
  apply is_C_RInt_segm_unique.
  apply is_C_RInt_segm_plus ;
  by apply C_RInt_segm_correct.
Qed.

Lemma is_C_RInt_segm_opp (f : C -> C) (z1 z2 If : C) :
  is_C_RInt_segm f z1 z2 If
  -> is_C_RInt_segm (fun z => - f z) z1 z2 (- If).
Proof.
  unfold is_C_RInt_segm.
  intros Hf.
  move: (is_RInt_opp _ _ _ _ Hf).
  apply is_RInt_ext.
  intros x _.
  change opp with Copp.
  by simpl ; ring_simplify.
Qed.
Lemma ex_C_RInt_segm_opp (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2
  -> ex_C_RInt_segm (fun z => - f z) z1 z2.
Proof.
  intros (If,Hf).
  exists (- If).
  by apply is_C_RInt_segm_opp.
Qed.
Lemma C_RInt_segm_opp (f : C -> C) (z1 z2 : C) :
  C_RInt_segm (fun z => - f z) z1 z2 = - C_RInt_segm f z1 z2.
Proof.
  unfold C_RInt_segm.
  rewrite C_RInt_opp ; ring.
Qed.

Lemma is_C_RInt_segm_minus (f g : C -> C) (z1 z2 If Ig : C) :
  is_C_RInt_segm f z1 z2 If -> is_C_RInt_segm g z1 z2 Ig
  -> is_C_RInt_segm (fun z => f z - g z) z1 z2 (If - Ig).
Proof.
  intros.
  apply is_C_RInt_segm_plus => //.
  by apply is_C_RInt_segm_opp.
Qed.
Lemma ex_C_RInt_segm_minus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> ex_C_RInt_segm (fun z => f z - g z) z1 z2.
Proof.
  intros.
  apply ex_C_RInt_segm_plus => //.
  by apply ex_C_RInt_segm_opp.
Qed.
Lemma C_RInt_segm_minus (f g : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm g z1 z2
  -> C_RInt_segm (fun z => f z - g z) z1 z2 = C_RInt_segm f z1 z2 - C_RInt_segm g z1 z2.
Proof.
  intros.
  rewrite C_RInt_segm_plus => //.
  by rewrite C_RInt_segm_opp.
  by apply ex_C_RInt_segm_opp.
Qed.

(** * Proposition 4 *)

Lemma is_C_RInt_segm_norm (f : C -> C) (z1 z2 : C) lf (m : R) :
  is_C_RInt_segm f z1 z2 lf
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod lf <= m * (Cmod (z1 - z2)).
Proof.
  intros Cf Hm.
  rewrite 2!Cmod_norm.
  apply: (norm_RInt_le (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun _ => Rmult (Cmod (z2 - z1)) m) 0 1).
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
Lemma C_RInt_segm_norm f z1 z2 m :
  ex_C_RInt_segm f z1 z2
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod (C_RInt_segm f z1 z2) <= m * (Cmod (z1 - z2)).
Proof.
  intros.
  apply is_C_RInt_segm_norm with f.
  by apply C_RInt_segm_correct.
  by [].
Qed.

(** * Proposition 5 *)

Lemma is_C_RInt_derive (f df : R -> C) (a b : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> filterdiff f (locally x) (fun y => scal y (df x))) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> continuous (U := C_R_NormedModule) df x) ->
    is_RInt df a b (f b - f a).
Proof.
  intros.
  apply is_RInt_fct_extend_pair ; simpl.
  
  apply (is_RInt_derive (fun y => fst (f y)) (fun y => fst (df y))).
  intros x Hx.
  unfold is_derive.
  evar_last.
  apply (filterdiff_comp' f (@fst R R)).
  by apply H.
  apply filterdiff_linear, is_linear_fst.
  by simpl.
  intros x Hx.
  apply continuous_comp.
  by apply H0.
  apply continuous_fst.
  
  apply (is_RInt_derive (fun y => snd (f y)) (fun y => snd (df y))).
  intros x Hx.
  unfold is_derive.
  evar_last.
  apply (filterdiff_comp' f (@snd R R)).
  by apply H.
  apply filterdiff_linear, is_linear_snd.
  by simpl.
  intros x Hx.
  apply continuous_comp.
  by apply H0.
  apply continuous_snd.
Qed.

Lemma continuous_C_segm (f : C -> C) (z1 z2 : C) :
  (forall z : C, complex_segment z1 z2 z -> continuous f z) ->
  (forall z : R, 0 <= z <= 1 ->
    continuous (fun t : R => (z2 - z1) * f ((1 - t) * z1 + t * z2)) z).
Proof.
  intros Cf z Hz.
  apply (continuous_comp RtoC ((fun t : C => (z2 - z1) * f ((1 - t) * z1 + t * z2)))).
  apply continuous_RtoC.
  eapply (continuous_comp (V := AbsRing_UniformSpace C_AbsRing) (W := C_UniformSpace) (fun t : C => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun x => x)),
         continuous_C_id_2.
  apply (continuous_scal_r (V := AbsRing_NormedModule C_AbsRing)).
  apply (continuous_comp (V := AbsRing_UniformSpace C_AbsRing)).
  apply (continuous_plus (V := AbsRing_NormedModule C_AbsRing)).
  apply @continuous_scal_l.
  apply (continuous_minus (U := C_UniformSpace) (V := (AbsRing_NormedModule C_AbsRing)) (fun _ => RtoC 1) (fun x => x) (RtoC z)).
  apply continuous_const.
  apply continuous_C_id_1.
  apply @continuous_scal_l.
  apply continuous_C_id_1.
  apply continuous_C, Cf.
  by exists z.
Qed.

Lemma is_C_RInt_segm_derive (f g : C -> C) (z1 z2 : C) :
  (forall z, complex_segment z1 z2 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z1 z2 z -> continuous f z)
  -> is_C_RInt_segm f z1 z2 (g z2 - g z1).
Proof.
  intros Dg Cf.
  unfold is_C_RInt_segm.
  evar_last.
  apply (is_C_RInt_derive (fun t : R => g ((1 - t) * z1 + t * z2))
                          (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2))).
    rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
    intros.
    eapply filterdiff_ext_lin.
    apply (filterdiff_comp' (U := R_NormedModule) (V := C_R_NormedModule) (fun t : R => ((1 - t) * z1 + t * z2)%C) g).
    apply @filterdiff_plus_fct.
    apply locally_filter.
    eapply filterdiff_ext.
    2: apply (filterdiff_scal_l_fct (K := R_AbsRing) (U := R_NormedModule) (V := C_R_NormedModule)
      z1 (fun u : R => (1 - u)%R)).
    simpl ; intros.
    by rewrite scal_R_Cmult RtoC_minus.
    apply @filterdiff_minus_fct.
    by apply locally_filter.
    apply filterdiff_const.
    apply filterdiff_id.
    apply filterdiff_linear.
    move: (is_linear_scal_l (K := R_AbsRing) (V := C_R_NormedModule) z2) => //=.
    apply is_linear_ext.
    intros ; apply scal_R_Cmult.
    apply is_C_derive_filterdiff, Dg.
    exists x ; by split.
  rewrite /= /scal /= /mult /= /prod_scal.
  change scal with Rmult.
  change plus with Cplus.
  change minus with Rminus.
  change zero with R0.
  intros y ; apply injective_projections ; simpl ; ring.
  
  rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
  by apply continuous_C_segm.

  ring_simplify ((1 - 1) * z1 + 1 * z2).
  ring_simplify ((1 - 0) * z1 + 0 * z2).
  reflexivity.
Qed.

(** * Corollaire 6 *)

Lemma C_RInt_segm_derive (f : C -> C) (z1 z2 : C) :
  (forall z, complex_segment z1 z2 z -> ex_C_derive f z)
  -> (forall z, complex_segment z1 z2 z -> continuous (C_derive f) z)
  -> C_RInt_segm (C_derive f) z1 z2 = f z2 - f z1.
Proof.
  intros.
  apply is_C_RInt_segm_unique, is_C_RInt_segm_derive => //.
  intros z Hz.
  case: (H z Hz) => [df Hdf].
  by rewrite (C_derive_unique _ _ _ Hdf).
Qed.

(** * Corolaire 7 *)

Lemma is_C_RInt_segm_triangle (f g : C -> C) (z1 z2 z3 : C) :
  (forall z, complex_segment z1 z2 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z2 z3 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z3 z1 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z1 z2 z -> continuous f z)
  -> (forall z, complex_segment z2 z3 z -> continuous f z)
  -> (forall z, complex_segment z3 z1 z -> continuous f z)
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 + C_RInt_segm f z3 z1 = 0.
Proof.
  intros.
  erewrite !is_C_RInt_segm_unique ; last first.
  apply is_C_RInt_segm_derive ; eassumption.
  apply is_C_RInt_segm_derive ; eassumption.
  apply is_C_RInt_segm_derive ; eassumption.
  ring.
Qed.

(** * Proposition 8 *)

Definition is_starred (U : C -> Prop) (z0 : C) :=
  forall z1 : C, U z1 -> forall z, complex_segment z0 z1 z -> U z.

Lemma ex_C_RInt_segm_continuous f z1 z2 :
  (forall z, complex_segment z1 z2 z -> continuous f z)
  -> ex_C_RInt_segm f z1 z2.
Proof.
  intros Cf.
  apply (ex_RInt_continuous (V := C_R_CompleteNormedModule)).
  rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
  by apply continuous_C_segm.
Qed.

Lemma locally_C_segm (P : C -> Prop) :
  forall z0, locally z0 P
    -> locally z0 (fun z => forall y, complex_segment z0 z y -> P y).
Proof.
  intros z0 (e,He).
  assert (Hd : 0 < e / (norm_factor (V := C_NormedModule))).
    apply Rdiv_lt_0_compat.
    by apply e.
    by apply norm_factor_gt_0.
  set (d := mkposreal _ Hd).
  exists d => z Hz _ [x [Hx ->]].
  apply He.
  apply (norm_compat1 (V := C_NormedModule)).
  change minus with Cminus ;
  change norm with Cmod.
  replace ((1 - x) * z0 + x * z - z0) with (x * (z - z0)) by ring.
  rewrite Cmod_mult.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_r.
  by apply Cmod_ge_0.
  rewrite Cmod_R Rabs_pos_eq ; apply Hx.
  rewrite Rmult_1_l.
  replace (pos e) with ((norm_factor (V := C_NormedModule)) * d)%R.
  by apply (norm_compat2 (V := C_NormedModule)).
  rewrite /d /= ; field.
  by apply Rgt_not_eq, norm_factor_gt_0.
Qed.

Lemma complex_segment_swap z1 z2 :
  forall z, complex_segment z1 z2 z -> complex_segment z2 z1 z.
Proof.
  move => _ [z [Hz ->]].
  exists (1 - z)%R ; split.
  split.
  apply Rle_minus_r ; ring_simplify ; apply Hz.
  apply Rminus_le_0 ; ring_simplify ; apply Hz.
  rewrite RtoC_minus ; ring.
Qed.

Lemma ex_antiderive (U : C -> Prop) (z0 : C) (f : C -> C) :
  open U -> is_starred U z0
  -> continuous_on U f
  -> (forall z1 z2 : C, U z1 -> U z2 ->
         (forall z, complex_segment z1 z2 z -> U z)
         -> C_RInt_segm f z0 z1 + C_RInt_segm f z1 z2 + C_RInt_segm f z2 z0 = 0)
  -> exists (g : C -> C), forall z, U z -> is_derive g z (f z).
Proof.
  intros oU sU Cf Hf.

  assert (forall z, U z -> locally z (ex_C_RInt_segm f z)).
    intros z Hz.
    move: (locally_C_segm _ _ (oU z Hz)).
    apply filter_imp => y Hy.
    apply ex_C_RInt_segm_continuous.
    intros z1 Hz1.
    apply continuous_continuous_on with U => //.
    by apply oU, Hy.

  exists (C_RInt_segm f z0).
  intros z Hz.
  split.
  by apply is_linear_scal_l.
  simpl => x Hx eps.
  change norm with Cmod ;
  change minus with Cminus.
  replace x with z.
  2: by apply @is_filter_lim_locally_unique in Hx.
  clear x Hx.
  eapply filter_imp.
  intros x Hx.
  rewrite {2}/Cminus C_RInt_segm_swap Cplus_comm.
  replace (C_RInt_segm f z z0 + C_RInt_segm f z0 x)
    with ((C_RInt_segm f z0 x + C_RInt_segm f x z + C_RInt_segm f z z0) + - (C_RInt_segm f x z))
    by ring.
  rewrite Hf => //.
  rewrite C_RInt_segm_swap.
  move: (@plus_zero_l _ (C_RInt_segm f z x)).
  change plus with Cplus ; change zero with (RtoC 0).
  move => ->.
  eapply (proj1 Hx).
  eapply (proj1 (proj2 Hx)).
  apply (proj2 (proj2 Hx)).
  repeat apply filter_and.
  2: by apply locally_C, (oU z).
  eapply filter_imp.
  intros x Hx.
  change scal with Cmult ;
  rewrite -C_RInt_segm_const.
  rewrite -C_RInt_segm_minus.
  2: eapply (proj1 Hx).
  rewrite -(Cmod_opp (_-_)).
  move: (opp_minus (G := C_AbelianGroup)).
  change opp with Copp ; change minus with Cminus.
  move => ->.
  apply is_C_RInt_segm_norm with (fun z1 : C => f z1 - f z).
  apply C_RInt_segm_correct.
  apply ex_C_RInt_segm_minus.
  by apply Hx.
  by apply ex_C_RInt_segm_const.
  apply (proj2 Hx).
  apply ex_C_RInt_segm_const.
  apply filter_and.
  by apply locally_C, H.
  apply locally_C.
  assert (He : 0 < eps / (norm_factor (V := C_NormedModule))).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply norm_factor_gt_0.
  set (e := mkposreal _ He).
  destruct (proj1 (filterlim_locally _ _) (continuous_continuous_on _ _ z (oU z Hz) Cf) e)
    as [d Hd].
  exists d => /= y Hy x Hx.
  replace (pos eps) with ((norm_factor (V := C_NormedModule)) * e)%R.
  apply Rlt_le, (norm_compat2 (V := C_NormedModule)).
  apply Hd.
  case: Hx => {x} x [Hx ->].
  split.
  rewrite /ball /= /AbsRing_ball.
  change minus with Rminus ; change abs with Rabs.
  replace ((1 + - x) * fst z - (0 + - 0) * snd z + (x * fst y - 0 * snd y) - fst z)%R
    with (x * (fst y - fst z))%R by ring.
  rewrite Rabs_mult.
  eapply Rle_lt_trans, (proj1 Hy).
  rewrite -(Rmult_1_l (abs _)).
  apply Rmult_le_compat_r.
  by apply abs_ge_0.
  rewrite Rabs_pos_eq ; apply Hx.
  rewrite /ball /= /AbsRing_ball.
  change minus with Rminus ; change abs with Rabs.
  replace ((1 + - x) * snd z + (0 + - 0) * fst z + (x * snd y + 0 * fst y) - snd z)%R
    with (x * (snd y - snd z))%R by ring.
  rewrite Rabs_mult.
  eapply Rle_lt_trans, (proj2 Hy).
  rewrite -(Rmult_1_l (abs _)).
  apply Rmult_le_compat_r.
  by apply abs_ge_0.
  rewrite Rabs_pos_eq ; apply Hx.
  rewrite /e /= ; field.
  by apply Rgt_not_eq, norm_factor_gt_0.
  apply locally_C.
  move: (locally_C_segm _ _ (oU z Hz)).
  apply filter_imp ; intros.
  by apply H0, complex_segment_swap.
Qed.
