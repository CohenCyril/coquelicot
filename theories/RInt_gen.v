Require Import Reals ssreflect.
Require Import Rbar Hierarchy RInt Limit Continuity Derive.
Require Import Rcomplements.

Open Scope R_scope.

(** * Generalized Riemann integral *)

Section RInt_gen.

Context {V : NormedModule R_AbsRing}.

Definition is_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) (l : V) :=
  exists (If : R * R -> V),
   filter_prod Fa Fb (fun ab => is_RInt f (fst ab) (snd ab) (If ab))
    /\ filterlim If (filter_prod Fa Fb) (locally l).
Definition ex_RInt_gen (f : R -> V) (Fa Fb : (R -> Prop) -> Prop) :=
  exists l : V, is_RInt_gen f Fa Fb l.

Definition is_RInt_gen_at_point f a b l :
  is_RInt_gen f (at_point a) (at_point b) l
    <-> is_RInt f a b l.
Proof.
  split.
  - case => If [[P Q Pa Qb Hif] Hl].
    apply filterlim_locally => eps.
    eapply filter_imp.
    intros x Hx.
    rewrite (double_var eps).
    apply ball_triangle with (If (a,b)).
    apply (fun H => proj1 (filterlim_locally _ _) H (pos_div_2 eps)) in Hl.
    case: Hl => P' Q' P'a Q'b Hl.
    apply Hl.
    apply P'a => ? ; apply ball_center.
    apply Q'b => ? ; apply ball_center.
    by apply Hx.
    apply Hif.
    apply Pa => ? ; apply ball_center.
    apply Qb => ? ; apply ball_center.
    by apply (locally_ball _ (pos_div_2 eps)).
  - intros Hl.
    exists (fun _ => l) ; split.
    exists (fun x => x = a) (fun x => x = b).
    intros x H. now apply eq_sym, ball_eq.
    intros x H. now apply eq_sym, ball_eq.
    by move => x y -> ->.
    by apply filterlim_const.
Qed.

End RInt_gen.

(** * Basic properties of integrals *)

Section Property.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_gen_ext {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (l : V) :
  filter_prod Fa Fb (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab)
                               -> f x = g x) ->
  is_RInt_gen f Fa Fb l -> is_RInt_gen g Fa Fb l.
Proof.
  intros Heq [If [Hf Hl]].
  exists If ; split.
  generalize (filter_and _ _ Heq Hf) ; clear Heq Hf.
  apply filter_imp.
  intros x [Heq Hf].
  eapply is_RInt_ext.
  by apply Heq.
  by apply Hf.
  by apply Hl.
Qed.

Lemma is_RInt_gen_point (f : R -> V) (a : R) :
  is_RInt_gen f (at_point a) (at_point a) zero.
Proof.
  apply is_RInt_gen_at_point.
  by apply is_RInt_point.
Qed.

Lemma is_RInt_gen_swap {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fb Fa l -> is_RInt_gen f Fa Fb (opp l).
Proof.
  case => If [[P Q /= HP HQ Hif] Hl].
  exists (fun x => opp (If (snd x,fst x))) ; split.
  exists Q P.
  exact: HQ.
  exact: HP.
  move => /= a b Qa Pb.
  apply is_RInt_swap.
  by apply Hif.
  eapply filterlim_comp, filterlim_opp.
  apply filterlim_locally => eps.
  apply (fun H => proj1 (filterlim_locally _ _) H eps) in Hl.
  clear -Hl ; case: Hl => P Q /= HP HQ Hif.
  exists Q P.
  exact: HQ.
  exact: HP.
  move => /= a b Qa Pb.
  by apply Hif.
Qed.

Lemma is_RInt_gen_Chasles {Fa Fc : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFc : Filter Fc}
  (f : R -> V) (b : R) (l1 l2 : V) : 
  is_RInt_gen f Fa (at_point b) l1 -> is_RInt_gen f (at_point b) Fc l2
  -> is_RInt_gen f Fa Fc (plus l1 l2).
Proof.
  case => If1 [[P1 Q1 /= HP1 HQ1 Hf1] Hl1].
  case => If2 [[P2 Q2 /= HP2 HQ2 Hf2] Hl2].
  exists (fun x => plus (If1 (fst x,b)) (If2 (b,snd x))) ; split.
  exists P1 Q2.
  exact: HP1.
  exact: HQ2.
  move => /= a c P1a Q2c.
  apply is_RInt_Chasles with b.
  apply Hf1 => //.
  apply HQ1 => ? ; apply ball_center.
  apply Hf2 => //.
  apply HP2 => ? ; apply ball_center.
  eapply filterlim_comp_2, filterlim_plus.
  eapply filterlim_comp , Hl1.
  clear -FFa FFc.
  intros P [P0 P1 P0a P1b HP].
  unfold filtermap.
  exists P0 (fun _ => True).
  exact: P0a.
  exact: filter_true.
  intros a c Q0a _ ; simpl.
  apply HP.
  by apply Q0a.
  apply P1b => ? ; apply ball_center.
  eapply filterlim_comp , Hl2.
  clear -FFa FFc.
  intros P [P0 P1 P0a P1b HP].
  unfold filtermap.
  exists (fun _ => True) P1.
  exact: filter_true.
  exact: P1b.
  intros a c _ Q0c ; simpl.
  apply HP.
  apply P0a => ? ; apply ball_center.
  by apply Q0c.
Qed.

End Property.

(** * Composition *)

Section Compose.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_gen_comp_opp {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f (filtermap opp Fa) (filtermap opp Fb) l ->
  is_RInt_gen (fun y => opp (f (- y))) Fa Fb l.
Proof.
  case => If [Hf Hl].
  exists (fun x => If (opp x)) ; split.
  case: Hf => P Q ;
  unfold filtermap => Pa Qb H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply is_RInt_comp_opp, H.
  eapply filterlim_comp, Hl.
  intros P [Q1 Q2] ;
  unfold filtermap => Q1a Q2b H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply H.
Qed.

Lemma is_RInt_gen_comp_lin {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (u v : R) (l : V) :
  is_RInt_gen f (filtermap (fun a => u * a + v) Fa) (filtermap (fun b => u * b + v) Fb) l
    -> is_RInt_gen (fun y => scal u (f (u * y + v))) Fa Fb l.
Proof.
  case => If [Hf Hl].
  exists (fun x => If (plus (scal u x) (v,v))) ; split.
  case: Hf => P Q ;
  unfold filtermap => Pa Qb H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply is_RInt_comp_lin, H.
  eapply filterlim_comp, Hl.
  intros P [Q1 Q2] ;
  unfold filtermap => Q1a Q2b H.
  eexists ; try eassumption.
  move => /= a b Ha Hb.
  by apply H.
Qed.

End Compose.

(** * Operations *)

Section Operations.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_gen_scal {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (k : R) (l : V) :
  is_RInt_gen f Fa Fb l ->
  is_RInt_gen (fun y => scal k (f y)) Fa Fb (scal k l).
Proof.
  case => If [Hf Hl].
  exists (fun x => scal k (If x)) ; split.
  move: Hf ; apply filter_imp => x.
  by apply is_RInt_scal.
  by eapply filterlim_comp, @filterlim_scal.
Qed.

Lemma is_RInt_gen_opp {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f : R -> V) (l : V) :
  is_RInt_gen f Fa Fb l ->
  is_RInt_gen (fun y => opp (f y)) Fa Fb (opp l).
Proof.
  case => If [Hf Hl].
  exists (fun x => opp (If x)) ; split.
  move: Hf ; apply filter_imp => x.
  by apply is_RInt_opp.
  by eapply filterlim_comp, filterlim_opp.
Qed.

Lemma is_RInt_gen_plus {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (lf lg : V) :
  is_RInt_gen f Fa Fb lf ->
  is_RInt_gen g Fa Fb lg ->
  is_RInt_gen (fun y => plus (f y) (g y)) Fa Fb (plus lf lg).
Proof.
  case => If [Hf Hlf].
  case => Ig [Hg Hlg].
  exists (fun x => plus (If x) (Ig x)) ; split.
  generalize (filter_and _ _ Hf Hg) ;
  apply filter_imp => {Hf Hg} x [Hf Hg].
  by apply is_RInt_plus.
  by eapply filterlim_comp_2, filterlim_plus.
Qed.

Lemma is_RInt_gen_minus {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} (f g : R -> V) (a b : R) (lf lg : V) :
  is_RInt_gen f Fa Fb lf ->
  is_RInt_gen g Fa Fb lg ->
  is_RInt_gen (fun y => minus (f y) (g y)) Fa Fb (minus lf lg).
Proof.
  intros Hf Hg.
  apply is_RInt_gen_plus.
  by [].
  by apply is_RInt_gen_opp.
Qed.

End Operations.

Lemma RInt_gen_norm {V : NormedModule R_AbsRing} {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) (g : R -> R) (lf : V) (lg : R) :
  filter_prod Fa Fb (fun ab => fst ab <= snd ab)
  -> filter_prod Fa Fb (fun ab => forall x, fst ab <= x <= snd ab -> norm (f x) <= g x)
  -> is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg
    -> norm lf <= lg.
Proof.
  intros Hab Hle.
  case => If [Hf Hlf].
  case => Ig [Hg Hlg].
  apply (filterlim_le (F := filter_prod Fa Fb) (fun x => norm (If x)) Ig (norm lf) lg).
  generalize (filter_and _ _ Hab Hle) => {Hab Hle} H.
  generalize (filter_and _ _ H Hf) => {H Hf} H.
  generalize (filter_and _ _ H Hg) => {H Hg}.
  apply filter_imp => x [[[Hab Hle] Hf] Hg].
  eapply norm_RInt_le ; try by eassumption.
  by eapply filterlim_comp, filterlim_norm.
  by apply Hlg.
Qed.

Lemma is_RInt_gen_Derive {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa} {FFb : Filter Fb}
  (f : R -> R) (la lb : R) :
  filter_prod Fa Fb
    (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> ex_derive f x)
  -> filter_prod Fa Fb
    (fun ab => forall x : R, Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> continuous (Derive f) x)
  -> filterlim f Fa (locally la) -> filterlim f Fb (locally lb)
  -> is_RInt_gen (Derive f) Fa Fb (lb - la).
Proof.
  intros Df Cf Lfa Lfb.
  exists (fun ab => f (snd ab) - f (fst ab)) ; split.
  generalize (filter_and _ _ Df Cf) => {Df Cf}.
  apply filter_imp => [[a b]] /= [Df Cf].
  by apply is_RInt_Derive.
  rewrite /Rminus.
  eapply filterlim_comp_2, (filterlim_plus lb (- la)).
  eapply filterlim_comp, Lfb.
  by apply filterlim_snd.
  eapply filterlim_comp, @filterlim_opp.
  eapply filterlim_comp, Lfa.
  by apply filterlim_fst.
Qed.

Goal forall x : R, 0 < x -> is_RInt_gen ln (at_right 0) (at_point x) (x * ln x - x).
Proof.
  assert (forall x, 0 < x -> is_derive (fun x => x * ln x - x) x (ln x)).
    intros x Hx.
    evar_last.
    apply @is_derive_minus.
    apply @is_derive_mult.
    by apply is_derive_id.
    by apply is_derive_Reals, derivable_pt_lim_ln.
    by apply is_derive_id.
    rewrite /minus /plus /one /opp /= ; field.
    by apply Rgt_not_eq.
  intros x Hx.
  evar_last.
  eapply is_RInt_gen_ext.
  2: apply is_RInt_gen_Derive.
  exists (fun x => 0 < x) (fun y => y = x).
  by exists (mkposreal _ Hx).
  intros y Hy.
  now apply eq_sym, ball_eq.
  move => /= a _ Ha -> y Hy.
  apply is_derive_unique, H.
  eapply Rlt_trans, Hy.
  by apply Rmin_case.
  exists (fun x => 0 < x) (fun y => y = x).
  by exists (mkposreal _ Hx).
  intros y Hy.
  now apply eq_sym, ball_eq.
  move => /= a _ Ha -> y Hy.
  eexists ; apply H.
  eapply Rlt_le_trans, Hy.
  by apply Rmin_case.
  exists (fun x => 0 < x) (fun y => y = x).
  by exists (mkposreal _ Hx).
  intros y Hy.
  now apply eq_sym, ball_eq.
  move => /= a _ Ha -> y Hy.
  eapply continuous_ext_loc.
  apply locally_interval with 0 p_infty.
  eapply Rlt_le_trans, Hy.
  by apply Rmin_case.
  by [].
  move => /= z Hz _.
  by apply sym_eq, is_derive_unique, H.
  apply continuity_pt_filterlim, derivable_continuous_pt.
  eexists ; apply derivable_pt_lim_ln.
  eapply Rlt_le_trans, Hy.
  by apply Rmin_case.
  rewrite /Rminus.
  eapply filterlim_comp_2, @filterlim_plus.
  instantiate (1 := 0).
  admit.
  eapply filterlim_filter_le_1.
  2: apply @filterlim_opp.
  intros P [d Hd].
  exists d => y Hy _.
  apply Hd, Hy.
  eapply filterlim_filter_le_1.
  2: apply continuity_pt_filterlim.
  intros P [d Hd].
  move => y Hy.
  apply Hd, Hy.
  apply continuity_pt_minus.
  apply continuity_pt_mult.
  apply continuity_pt_id.
  apply derivable_continuous_pt.
  eexists ; by apply derivable_pt_lim_ln.
  apply continuity_pt_id.
  by rewrite opp_zero plus_zero_r Rminus_0_r.
Qed.
