Require Import Reals.
Require Import ssreflect seq.
Require Import Rcomplements Rbar_theory Derive SF_seq RInt Differential Locally.
Require Import Continuity Lim_seq Lim_fct.


(** * Basic properties of integration *)

(** ** Integrals over intervals of length zero *)

Lemma is_RInt_point (f : R -> R) (a : R) :
  is_RInt f a a 0.
Proof.
  move => eps ; exists (mkposreal _ Rlt_0_1) => ptd _ _ _ _.
  rewrite Rminus_eq0 /signe.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rle_not_lt _ _ H) => // _ _.
  rewrite Rmult_0_l Rminus_0_r Rabs_R0.
  by apply eps.
Qed.

Lemma ex_RInt_point :
  forall f a, ex_RInt f a a.
Proof.
intros f a.
exists 0 ; by apply is_RInt_point.
Qed.

Lemma RInt_point :
  forall f a, RInt f a a = 0.
Proof.
intros f a.
replace 0 with (Rbar.real (Rbar.Finite 0)) by auto.
rewrite -(Lim_seq_const 0).
rewrite /RInt ; case: Rle_dec (Rle_refl a) => // _ _ ;
apply f_equal, Lim_seq_ext.
move => n ; rewrite /RInt_val ; field ; apply Rgt_not_eq, INRp1_pos.
Qed.

(** ** Reversing limits of integration *)

Lemma RInt_swap :
  forall f a b,
  - RInt f a b = RInt f b a.
Proof.
intros f a b.
destruct (Req_dec a b) as [Hab|Hab].
rewrite Hab.
rewrite RInt_point.
apply Ropp_0.
unfold RInt.
destruct (Rle_dec a b) as [H|H].
destruct (Rle_dec b a) as [H'|H'].
elim Hab.
now apply Rle_antisym.
apply refl_equal.
apply Rnot_le_lt in H.
destruct (Rle_dec b a) as [H'|H'].
apply Ropp_involutive.
elim H'.
now apply Rlt_le.
Qed.

(** ** Chasles relation *)

Lemma ex_RInt_Chasles :
  forall f a b c, ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_1.
apply RiemannInt_P24 with b; now apply ex_RInt_correct_2.
Qed.

Lemma RInt_Chasles :
  forall f a b c,
  ex_RInt f a b -> ex_RInt f b c ->
  RInt f a b + RInt f b c = RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_2 in H1.
apply ex_RInt_correct_2 in H2.
rewrite (RInt_correct _ _ _ H1) (RInt_correct _ _ _ H2).
rewrite (RInt_correct _ _ _ (RiemannInt_P24 H1 H2)).
apply RiemannInt_P26.
Qed.

Lemma ex_RInt_included1: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f a c.
Proof.
intros f a b c H1 H2.
apply ex_RInt_correct_1.
apply RiemannInt_P22 with b;[now apply ex_RInt_correct_2|exact H2].
Qed.

Lemma ex_RInt_included2: forall f a b c, ex_RInt f a b -> a <= c <= b -> ex_RInt f c b.
intros f a b c H1 H2.
apply ex_RInt_correct_1.
apply RiemannInt_P23 with a;[now apply ex_RInt_correct_2|exact H2].
Qed.

(** * Unicity *)

Lemma is_RInt_unique (f : R -> R) (a b l : R) :
  is_RInt f a b l -> RInt f a b = l.
Proof.
  wlog : a b l /(a < b) => [Hw | Hab].
    case: (Rlt_le_dec a b) => Hab.
    by apply Hw.
    case: Hab => [Hab | -> {b}] Hf.
    rewrite -RInt_swap.
    rewrite -(Ropp_involutive l).
    apply Ropp_eq_compat.
    apply Hw.
    by apply Hab.
    apply is_RInt_swap.
    by rewrite Ropp_involutive.
    rewrite RInt_point.
    apply Req_lt_aux => eps.
    rewrite Rminus_0_l Rabs_Ropp.
    case: (Hf eps) => {Hf} alpha Hf.
    set ptd := SF_seq_f2 (fun x y => (x + y) / 2) (RInt_part a a O) 0.
    replace l with (l - signe (a - a) * Riemann_sum f ptd).
    apply Hf.
    rewrite /ptd => i ;
    rewrite SF_size_f2 SF_lx_f2 ;
    move => /= Hi.
    case: i Hi => [ | i] //= Hi.
    split ; apply Req_le ; field.
    by apply lt_S_n, lt_n_0 in Hi.
    rewrite /seq_step SF_lx_f2 /=.
    replace (a + 1 * (a - a) / (0 + 1) - (a + 0 * (a - a) / (0 + 1))) with 0 by field.
    rewrite Rabs_R0.
    rewrite /Rmax ; case: Rle_dec (Rle_refl 0) => // _ _.
    by apply alpha.
    rewrite /ptd /=.
    rewrite /Rmin ; case: Rle_dec (Rle_refl a) => // _ _.
    field.
    rewrite SF_lx_f2 /=.
    rewrite /Rmax ; case: Rle_dec (Rle_refl a) => // _ _.
    field.
    apply Rminus_diag_uniq ; ring_simplify.
    apply Rmult_eq_0_compat_r.
    apply Ropp_eq_0_compat.
    rewrite Rminus_eq0.
    rewrite /signe.
    case: Rle_dec (Rle_refl 0) => // H _.
    case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //.
  move => Hf.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (is_lim_seq_unique _ l) => //.
  by apply ex_RInt_correct_aux_2.
Qed.

Ltac search_RInt := let l := fresh "l" in
evar (l : R) ;
match goal with
  | |- RInt _ _ _ = ?lu => apply is_RInt_unique ; replace lu with l ; [ | unfold l]
  | |- is_RInt _ _ _ ?lu => replace lu with l ; [ | unfold l]
end.

Lemma ex_RInt_cont: forall f a b, (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f x) 
  -> ex_RInt f a b.
intros f a b H.
wlog: a b H / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H'.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
intros x; rewrite Rmin_comm Rmax_comm.
apply H.
now left.
apply ex_RInt_correct_1.
apply continuity_implies_RiemannInt.
exact Hab.
intros; apply H.
rewrite Rmin_left; try exact Hab.
now rewrite Rmax_right.
Qed. 


(** * Operations *)

(** ** Extentionality *)

Lemma is_RInt_ext (f g : R -> R) (a b l : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  is_RInt f a b l -> is_RInt g a b l.
Proof.
  move => Heq Hex eps.
case: (Hex eps) => {Hex} alpha Hex ;
exists alpha => ptd Hptd Hstep Hhead Hlast.
replace (Riemann_sum g ptd) with (Riemann_sum f ptd).
by apply Hex.
move: (Rmin a b) (Rmax a b) Heq Hhead Hlast Hptd.
apply SF_seq.SF_cons_ind with (s := ptd)
  => /= [x0 | [x0 y0] s IH] /= a' b' Heq Hhead Hlast Hptd.
reflexivity.
rewrite !Riemann_sum_cons /= ; apply f_equal2.
rewrite Heq.
reflexivity.
rewrite -Hhead -Hlast ; split.
by apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_seq.SF_h s).
by apply (Hptd O (lt_O_Sn _)).
apply (SF_seq.sorted_last (seq.Cons _ (SF_seq.SF_h s) (seq.unzip1 (SF_seq.SF_t s))) O)
  with (x0 := 0).
apply ptd_sort, ptd_cons with (1 := Hptd).
by apply lt_O_Sn.
apply (IH (SF_seq.SF_h s) b').
move => x Hx ; apply Heq ; split.
apply Rle_trans with (SF_seq.SF_h s).
rewrite -Hhead ; by apply (ptd_sort _ Hptd).
by apply Hx.
by apply Hx.
reflexivity.
by apply Hlast.
by apply ptd_cons with (1 := Hptd).
Qed.

Lemma ex_RInt_ext :
  forall f g a b,
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  ex_RInt f a b -> ex_RInt g a b.
Proof.
intros f g a b Heq If.
case: If => If Hex ; exists If => eps.
case: (Hex eps) => {Hex} alpha Hex ;
exists alpha => ptd Hptd Hstep Hhead Hlast.
replace (Riemann_sum g ptd) with (Riemann_sum f ptd).
by apply Hex.
move: (Rmin a b) (Rmax a b) Heq Hhead Hlast Hptd.
apply SF_seq.SF_cons_ind with (s := ptd)
  => /= [x0 | [x0 y0] s IH] /= a' b' Heq Hhead Hlast Hptd.
reflexivity.
rewrite !Riemann_sum_cons /= ; apply f_equal2.
rewrite Heq.
reflexivity.
rewrite -Hhead -Hlast ; split.
by apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_seq.SF_h s).
by apply (Hptd O (lt_O_Sn _)).
apply (SF_seq.sorted_last (seq.Cons _ (SF_seq.SF_h s) (seq.unzip1 (SF_seq.SF_t s))) O)
  with (x0 := 0).
apply ptd_sort, ptd_cons with (1 := Hptd).
by apply lt_O_Sn.
apply (IH (SF_seq.SF_h s) b').
move => x Hx ; apply Heq ; split.
apply Rle_trans with (SF_seq.SF_h s).
rewrite -Hhead ; by apply (ptd_sort _ Hptd).
by apply Hx.
by apply Hx.
reflexivity.
by apply Hlast.
by apply ptd_cons with (1 := Hptd).
Qed.

Lemma RInt_ext :
  forall f g a b,
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x) ->
  RInt f a b = RInt g a b.
Proof.
intros f g a b.
wlog H: a b / a <= b.
intros H Heq.
destruct (Rle_dec a b) as [Hab|Hab].
now apply H.
rewrite -RInt_swap -(RInt_swap g).
rewrite H //.
apply Rlt_le.
now apply Rnot_le_lt.
now rewrite Rmin_comm Rmax_comm.
rewrite Rmin_left // Rmax_right //.
intros Heq.
unfold RInt.
destruct (Rle_dec a b) as [Hab|Hab].
clear H.
2: easy.
apply f_equal, Lim_seq_ext => n.
rewrite /RInt /RInt_val.
apply f_equal.
rewrite /SF_val_ly.
move: Heq.
pattern b at 1 ; replace b with (seq.last 0 (RInt_part a b n)).
pattern a at 1 ; replace a with (seq.head 0 (RInt_part a b n)).
move: (RInt_part_sort a b n Hab).
elim: (RInt_part a b n) => [ | x0].
by [].
case => /= [ | x1 s] IH Hs Heq.
by [].
apply f_equal2.
apply Heq ; split.
pattern x0 at 1 ; replace x0 with ((x0+x0)/2) by field.
apply Rmult_le_compat_r ; by intuition.
apply Rle_trans with x1.
pattern x1 at 2 ; replace x1 with ((x1+x1)/2) by field.
apply Rmult_le_compat_r ; by intuition.
apply (SF_seq.sorted_last (seq.Cons _ x1 s) O (proj2 Hs) (lt_O_Sn _) 0).
apply IH.
by apply Hs.
move => x Hx ; apply: Heq ; split.
apply Rle_trans with (2 := proj1 Hx) ; by apply Hs.
by apply Hx.
simpl ; field ; by apply Rgt_not_eq, INRp1_pos.
rewrite -seq.nth_last seq.size_mkseq seq.nth_mkseq.
simpl ssrnat.predn ; rewrite S_INR ;
field ; by apply Rgt_not_eq, INRp1_pos.
by [].
Qed.

(** ** Constant functions *)

Lemma is_RInt_const (v a b : R) :
  is_RInt (fun _ => v) a b (v * (b - a)).
Proof.
wlog: a b /(a < b) => [Hw | Hab].
  case: (Rle_lt_dec a b) => Hab.
  case: Hab => Hab.
  by apply Hw.
  rewrite Hab ; rewrite Rminus_eq0 Rmult_0_r.
  by apply is_RInt_point.
  apply is_RInt_swap.
  replace (- (v * (b - a))) with (v * (a - b)) by ring.
  by apply Hw.
move => eps ; exists (mkposreal _ Rlt_0_1) => ptd _ _.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
rewrite /signe ; case: Rle_dec (Rlt_le _ _ (Rgt_minus _ _ Hab)) => // H _ ;
case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rgt_minus _ _ Hab)) => // {H} _ _ ;
rewrite Rmult_1_l => Ha Hb.
replace (Riemann_sum _ _) with (v * (b-a)).
rewrite Rminus_eq0 Rabs_R0 ; by apply eps.
rewrite -Ha -Hb => {Ha Hb} ;
apply SF_seq.SF_cons_ind with (s := ptd) => {ptd} [ x0 | [x0 y0] s IH] /= .
rewrite /Riemann_sum /SF_seq.RInt_seq /= ; ring.
rewrite Riemann_sum_cons /= -IH /= ; ring.
Qed.

Lemma ex_RInt_const :
  forall v a b, ex_RInt (fun _ => v) a b.
Proof.
intros f a b.
exists (f * (b-a)) ; by apply is_RInt_const.
Qed.

Lemma RInt_const (a b c : R) :
  RInt (fun _ => c) a b = c * (b-a).
Proof.
wlog: a b /(a <= b) => [Hw | Hab].
  case: (Rle_lt_dec a b) => Hab.
  by apply Hw.
  rewrite -RInt_swap Hw.
  ring.
  by apply Rlt_le.
rewrite /RInt ; case: Rle_dec => // _.
replace (c * (b - a)) with (Rbar.real (Rbar.Finite (c * (b - a)))) by auto.
rewrite -(Lim_seq_const (c * (b-a))).
apply f_equal, Lim_seq_ext => n.
rewrite /RInt_val.
replace (seq.foldr _ 0 _) with (c * (INR n + 1)).
field ; apply Rgt_not_eq, INRp1_pos.
rewrite /SF_val_ly -S_INR.
replace (S n) with (Peano.pred (seq.size (RInt_part a b n))).
elim: (RInt_part a b n) => [ | x0] /=.
ring.
case => [ | x1 s] ; rewrite ?(S_INR (seq.size s)) => /= IH.
ring.
rewrite -IH /= ; ring.
by rewrite seq.size_mkseq.
Qed.

(** ** Scalar multiplication *)

Lemma ex_RInt_scal :
  forall f l a b, ex_RInt f a b ->
  ex_RInt (fun x => l * f x) a b.
Proof.
intros f l a b If.
apply ex_RInt_correct_1.
apply Riemann_integrable_scal.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_scal :
  forall f l a b,
  RInt (fun x => l * f x) a b = l * RInt f a b.
Proof.
intros f l.
(* *)
assert (forall a b, Lim_seq (RInt_val (fun x : R => l * f x) a b) = Rbar.Rbar_mult (Rbar.Finite l) (Lim_seq (RInt_val f a b))).
intros a b.
rewrite -Lim_seq_scal.
apply Lim_seq_ext => n.
unfold RInt_val.
replace (l * ((b - a) / (INR n + 1) * seq.foldr Rplus 0 (SF_val_ly f a b n)))
  with ((b - a) / (INR n + 1) * (l * seq.foldr Rplus 0 (SF_val_ly f a b n))) by ring.
apply f_equal.
unfold SF_val_ly.
apply eq_sym.
destruct (RInt_part a b n) as [|h q].
apply Rmult_0_r.
simpl.
revert h.
induction q => h.
apply Rmult_0_r.
simpl.
rewrite -IHq.
apply Rmult_plus_distr_l.
(* *)
intros a b.
unfold RInt.
have H0 : (forall x, l * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite l) x)).
  case: (Req_dec l 0) => [-> | Hk].
  case => [x | | ] //= ; rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case => [x | | ] //= ; rewrite Rmult_0_r.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.

case Rle_dec => _.
by rewrite H0 H.
rewrite -?Rbar.Rbar_opp_real H0 H.
apply f_equal.
case: (Lim_seq (RInt_val f b a)) => [x | | ] /=.
apply f_equal ; ring.
case: Rle_dec => // H1.
case: Rle_lt_or_eq_dec => H2 //=.
by rewrite Ropp_0.
case: Rle_dec => // H1.
case: Rle_lt_or_eq_dec => H2 //=.
by rewrite Ropp_0.
Qed.

Lemma is_RInt_scal (f : R -> R) (k a b l : R) :
  is_RInt f a b l -> is_RInt (fun y => k * f y) a b (k * l).
Proof.
  move => If.
  rewrite -(is_RInt_unique _ _ _ _ If).
  rewrite -RInt_scal.
  have Hex : ex_RInt f a b.
    by exists l.
  case: (ex_RInt_scal f k a b Hex) => kl H.
  by rewrite (is_RInt_unique _ _ _ kl).
Qed.

(** ** Additive *)

Lemma ex_RInt_opp :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => - f x) a b.
Proof.
intros f a b If.
apply ex_RInt_correct_1.
apply Riemann_integrable_opp.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_opp :
  forall f a b,
  RInt (fun x => - f x) a b = - RInt f a b.
Proof.
intros f a b.
replace (-RInt f a b) with ((-1) * RInt f a b) by ring.
rewrite -RInt_scal.
apply RInt_ext => x _.
ring.
Qed.

Lemma is_RInt_opp (f : R -> R) (a b l : R) :
  is_RInt f a b l -> is_RInt (fun y => - f y) a b (-l).
Proof.
  move => If.
  apply is_RInt_ext with (fun y => -1 * f y).
  move => x _ ; ring.
  replace (-l) with (-1 * l) by ring.
  by apply is_RInt_scal.
Qed.

Lemma ex_RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  ex_RInt (fun x => f x + g x) a b.
Proof.
intros f g a b If Ig.
apply ex_RInt_correct_1.
apply Riemann_integrable_plus ; now apply ex_RInt_correct_2.
Qed.

Lemma RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof.
intros f g a b If Ig.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ If)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ Ig)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ (ex_RInt_plus _ _ _ _ If Ig))).
apply RiemannInt_plus.
Qed.

Lemma is_RInt_plus (f g : R -> R) (a b lf lg : R) :
  is_RInt f a b lf -> is_RInt g a b lg ->
  is_RInt (fun x => f x + g x) a b (lf + lg).
Proof.
  move => If Ig.
  rewrite -(is_RInt_unique _ _ _ _ If) -(is_RInt_unique _ _ _ _ Ig).
  have Hf : ex_RInt f a b.
    by exists lf.
  have Hg : ex_RInt g a b.
    by exists lg.
  rewrite -RInt_plus => //.
  case: (ex_RInt_plus _ _ _ _ Hf Hg) => l H.
  by rewrite (is_RInt_unique _ _ _ _ H).
Qed.

Lemma ex_RInt_minus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  ex_RInt (fun x => f x - g x) a b.
Proof.
intros f g a b If Ig.
apply ex_RInt_correct_1.
apply Riemann_integrable_minus ; now apply ex_RInt_correct_2.
Qed.

Lemma RInt_minus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof.
intros f g a b If Ig.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ If)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ Ig)).
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ (ex_RInt_minus _ _ _ _ If Ig))).
apply RiemannInt_minus.
Qed.

Lemma is_RInt_minus (f g : R -> R) (a b lf lg : R) :
  is_RInt f a b lf -> is_RInt g a b lg ->
  is_RInt (fun x => f x - g x) a b (lf - lg).
Proof.
  move => If Ig.
  apply is_RInt_plus.
  by [].
  by apply is_RInt_opp.
Qed.

(** ** Composition *)

Lemma is_RInt_comp_opp (f : R -> R) (a b l : R) :
  is_RInt f (-a) (-b) l 
    -> is_RInt (fun y => - f (- y)) a b l.
Proof.
  move => If eps.
  case: (If eps) => {If} alp If.
  exists alp => ptd Hptd Hstep Hh Hl.
  rewrite /Rminus -Ropp_plus_distr Ropp_signe in If.
  set ptd' := (mkSF_seq (-SF_h ptd)
    (seq.map (fun X => (- fst X,- snd X)) (SF_t ptd))).
  replace (l - signe (b - a) * Riemann_sum (fun y : R => - f (- y)) ptd)
    with (l + - (- signe (b + - a) * Riemann_sum f (SF_rev ptd'))).
Focus 2.
  apply Rminus_diag_uniq ; ring_simplify.
  rewrite -Rmult_plus_distr_l.
  apply Rmult_eq_0_compat_l.
  replace (Riemann_sum (fun y : R => - f (- y)) ptd)
    with (- Riemann_sum f (SF_rev ptd')).
    ring.
  revert ptd' ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | h ptd' IH].
  rewrite /Riemann_sum /RInt_seq /=.
  by apply Ropp_0.
  rewrite Riemann_sum_cons.
  rewrite (SF_rev_cons (-fst h, -snd h)
    (mkSF_seq (- SF_h ptd') (seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd')))).
  rewrite -IH => {IH}.
  set s := {|
        SF_h := - SF_h ptd';
        SF_t := seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd') |}.
  rewrite Riemann_sum_rcons.
  rewrite SF_lx_rev.
  have H : (forall s x0, last x0 (rev s) = head x0 s).
    move => T s0 x0.
    case: s0 => [ | x1 s0] //=.
    rewrite rev_cons.
    by rewrite last_rcons.
  rewrite H /= ; ring.
  have H : SF_size ptd = SF_size ptd'.
    rewrite /SF_size /=.
    by rewrite size_map.
  apply If.
  revert ptd' Hptd H ;
  apply SF_cons_ind with (s := ptd) => [ x0 | h0 s IH] s' Hs' H i Hi ;
  rewrite SF_size_rev -H in Hi.
  by apply lt_n_O in Hi.
  rewrite SF_size_cons in Hi.
  apply lt_n_Sm_le in Hi.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h0,-snd h0) s'').
  rewrite SF_size_cons (SF_size_cons (-fst h0,-snd h0) s'') in H.
  apply eq_add_S in H.
  rewrite SF_lx_rcons SF_ly_rcons.
  rewrite ?nth_rcons.
  rewrite ?SF_size_lx ?SF_size_ly ?SF_size_rev -H.
  move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ;
  case: (ssrnat.leq (S i) (S (SF_size s))) => // _.
  apply le_lt_eq_dec in Hi ; case: Hi => [Hi | -> {i}].
  apply lt_le_S in Hi.
  move: (proj2 (SSR_leq _ _) Hi) ;
  case: (ssrnat.leq (S i) (SF_size s)) => // _.
  move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ;
  case: (ssrnat.leq (S (S i)) (S (SF_size s))) => // _.
  apply IH.
  move: Hs' ; apply ptd_cons.
  apply H.
  rewrite SF_size_rev -H.
  intuition.
  have : ~ is_true (ssrnat.leq (S (SF_size s)) (SF_size s)).
    have H0 := lt_n_Sn (SF_size s).
    contradict H0.
    apply SSR_leq in H0.
    by apply le_not_lt.
  case: (ssrnat.leq (S (SF_size s)) (SF_size s)) => // _.
  move: (@eqtype.eq_refl ssrnat.nat_eqType (SF_size s)) ;
  case: (@eqtype.eq_op ssrnat.nat_eqType (SF_size s) (SF_size s)) => // _.
  have : ~ is_true (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))).
    have H0 := lt_n_Sn (SF_size s).
    contradict H0.
    apply SSR_leq in H0.
    by apply le_not_lt, le_S_n.
  case: (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))) => // _.
  move: (@eqtype.eq_refl ssrnat.nat_eqType (S (SF_size s))) ;
  case: (@eqtype.eq_op ssrnat.nat_eqType (S (SF_size s)) (S (SF_size s))) => // _.
  rewrite H SF_lx_rev nth_rev SF_size_lx //=.
  replace (ssrnat.subn (S (SF_size s'')) (S (SF_size s'')))
    with 0%nat by intuition.
  simpl.
  split ; apply Ropp_le_contravar ; apply (Hs' 0%nat) ;
  rewrite SF_size_cons ; by apply lt_O_Sn.
  clear H ;
  revert ptd' Hstep ;
  apply SF_cons_dec with (s := ptd) => [ x0  s' Hs'| h0 s] ;
  rewrite /seq_step.
  simpl ; by apply alp.
  set s' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h0,-snd h0) s').
  rewrite SF_lx_rcons.
  rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
  rewrite head_rcons.
  rewrite SF_lx_cons.
  revert h0 s' ;
  move: {1 3}(0) ;
  apply SF_cons_ind with (s := s) => {s} [ x1 | h1 s IH] x0 h0 s' Hs' ;
  simpl in Hs'.
  rewrite /= -Ropp_minus_distr' /Rminus -Ropp_plus_distr Ropp_involutive.
  by apply Hs'.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h1,-snd h1) s'').
  rewrite SF_lx_rcons.
  rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
  rewrite head_rcons.
  rewrite pairmap_rcons.
  rewrite foldr_rcons.
  apply: IH => /=.
  replace (Rmax (Rabs (SF_h s - fst h1))
  (foldr Rmax (Rmax (Rabs (- fst h0 - - fst h1)) x0)
     (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s)))))
    with (Rmax (Rabs (fst h1 - fst h0))
        (Rmax (Rabs (SF_h s - fst h1))
           (foldr Rmax x0
              (pairmap (fun x y : R => Rabs (y - x)) (SF_h s)
                 (unzip1 (SF_t s)))))).
  by [].
  rewrite Rmax_assoc (Rmax_comm (Rabs _)) -Rmax_assoc.
  apply f_equal.
  rewrite -(Ropp_minus_distr' (-fst h0)) /Rminus -Ropp_plus_distr Ropp_involutive.
  elim: (pairmap (fun x y : R => Rabs (y + - x)) (SF_h s) (unzip1 (SF_t s)))
    x0 {Hs'} (Rabs (fst h1 + - fst h0)) => [ | x2 t IH] x0 x1 /=.
    by [].
    rewrite Rmax_assoc (Rmax_comm x1) -Rmax_assoc.
    apply f_equal.
    by apply IH.
  rewrite Rmin_opp_Rmax -Hl.
  simpl.
  clear H.
  revert ptd' ;
  move: (0) ;
  apply SF_cons_ind with (s := ptd) => [ h0 | h0 s IH] x0 s'.
  by simpl.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
  rewrite head_rcons.
  by apply IH.
  rewrite Rmax_opp_Rmin -Hh.
  simpl.
  clear H.
  revert ptd' ;
  move: (0) ;
  apply SF_cons_dec with (s := ptd) => [ h0 | h0 s] x0 s'.
  by simpl.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
  rewrite head_rcons.
  rewrite behead_rcons ; [ | rewrite size_rev SF_size_lx ; by apply lt_O_Sn].
  rewrite unzip1_zip.
  by rewrite last_rcons.
  rewrite size_rcons size_behead ?size_rev SF_size_ly SF_size_lx //=.
Qed.
Lemma ex_RInt_comp_opp (f : R -> R) (a b : R) :
  ex_RInt f (-a) (-b) 
    -> ex_RInt (fun y => - f (- y)) a b.
Proof.
  case => l Hf.
  exists l.
  by apply is_RInt_comp_opp.
Qed.
Lemma RInt_comp_opp (f : R -> R) (a b : R) :
  RInt (fun y => - f (- y)) a b = RInt f (-a) (-b).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
  by rewrite ?RInt_point.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -(RInt_swap _ b) -(RInt_swap _ (-b)).
    rewrite Hw => //.
    by apply Rlt_not_eq.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  case: Rle_dec (Rlt_not_le _ _ (Ropp_lt_contravar _ _ Hab)) => // _ _.
  rewrite -Rbar_opp_real.
  apply f_equal.
  rewrite -Lim_seq_opp.
  apply Lim_seq_ext => n.
  rewrite -RInt_val_swap.
  rewrite /RInt_val.
  replace ((- b - - a) / (INR n + 1) * foldr Rplus 0 (SF_val_ly f (- a) (- b) n))
  with ((b - a) / (INR n + 1) * (- foldr Rplus 0 (SF_val_ly f (- a) (- b) n)))
  by (rewrite /Rdiv ; ring).
  apply f_equal.
  rewrite /SF_val_ly /RInt_part.
  case: (S (S n)) => /= [ | m].
  by rewrite Ropp_0.
  pattern 0 at 2 4 ;
  replace 0 with (INR O) by auto.
  elim: m (0%nat) => [ | m IH] m0.
  simpl ; by rewrite Ropp_0.
  simpl iota.
  rewrite ?map_cons S_INR.
  simpl.
  rewrite -(S_INR m0) IH S_INR.
  have Hn : INR n + 1 <> 0.
    rewrite -S_INR.
    apply not_0_INR, sym_not_eq, O_S.
  field_simplify (- ((a + INR m0 * (b - a) / (INR n + 1) +
     (a + (INR m0 + 1) * (b - a) / (INR n + 1))) / 2)) => //.
  field_simplify ((- a + INR m0 * (- b - - a) / (INR n + 1) +
     (- a + (INR m0 + 1) * (- b - - a) / (INR n + 1))) / 2) => //.
  ring.
Qed.

Lemma is_RInt_comp_lin (f : R -> R) (u v a b l : R) :
  is_RInt f (u * a + v) (u * b + v) l 
    -> is_RInt (fun y => u * f (u * y + v)) a b l.
Proof.
  wlog : u / (u <> 0) => [Hw |].
    case: (Req_dec u 0) => [-> {u} | Hu] If.
    evar (l' : R) ; replace l with l'.
    apply is_RInt_ext with (fun _ => 0).
    move => x _ ; by rewrite Rmult_0_l.
    apply is_RInt_const.
    rewrite ?Rmult_0_l Rplus_0_l in If.
    rewrite -(is_RInt_unique _ _ _ _ If).
    rewrite RInt_point /l' ; ring.
    by apply Hw.
  wlog: u a b / (u > 0) => [Hw | Hu _].
    case: (Rlt_le_dec 0 u) => Hu.
    by apply Hw.
    case: Hu => // Hu _ If.
    apply is_RInt_ext with (fun y => - (- u * f ((- u) * (- y) + v))).
    move => x _ ; ring_simplify.
    apply f_equal.
    apply f_equal ; ring.
    apply (is_RInt_comp_opp (fun y => (- u * f (- u * y + v)))).
    apply Hw.
    by apply Ropp_gt_lt_0_contravar.
    by apply Ropp_neq_0_compat, Rlt_not_eq.
    by rewrite ?Rmult_opp_opp.
  wlog: a b l / (a < b) => [Hw | Hab].
    case: (Rlt_le_dec a b) => Hab If.
    by apply Hw.
    case: Hab If => [Hab | -> {b}] If.
    apply is_RInt_swap.
    apply Hw.
    by [].
    apply is_RInt_swap ; by rewrite Ropp_involutive.
    rewrite -(is_RInt_unique _ _ _ _ If) RInt_point.
    by apply is_RInt_point.
  move => If eps.
  case: (If eps) => {If} alpha If.
  have Ha : 0 < alpha / Rabs u.
    apply Rdiv_lt_0_compat.
    by apply alpha.
    by apply Rabs_pos_lt, Rgt_not_eq.
  exists (mkposreal _ Ha) => /= ptd Hptd Hstep Hfirst Hlast.
  set ptd' := mkSF_seq (u * SF_h ptd + v) (map (fun X => (u * fst X + v,u * snd X + v)) (SF_t ptd)).
  replace (l - signe (b - a) * Riemann_sum (fun y : R => u * f (u * y + v)) ptd)
  with (l - signe (u * b + v - (u * a + v)) * Riemann_sum f ptd').
  apply: If.
  revert ptd' ;
  case: (ptd) Hptd => x0 s Hs /= i Hi ; 
  rewrite /SF_size size_map /= in Hi ;
  move: (Hs i) => {Hs} Hs ;
  rewrite /SF_size /= in Hs ;
  move: (Hs Hi) => {Hs} ;
  rewrite /SF_lx /SF_ly /= => Hs.
  elim: s i x0 Hi Hs => /= [ | [x1 y0] s IH] i x0 Hi Hs.
  by apply lt_n_O in Hi.
  case: i Hi Hs => /= [ | i] Hi Hs.
  split ; apply Rplus_le_compat_r ;
  apply Rmult_le_compat_l ;
  try by apply Rlt_le.
  by apply Hs.
  by apply Hs.
  apply IH.
  by apply lt_S_n.
  by apply Hs.
  revert ptd' ;
  case: (ptd) Hstep => x0 s Hs /= ; 
  rewrite /seq_step /= in Hs |- *.
  elim: s x0 Hs => [ | [x1 y0] s IH] /= x0 Hs.
  by apply alpha.
  apply Rmax_case.
  replace (u * x1 + v - (u * x0 + v)) with (u * (x1 - x0)) by ring.
  rewrite Rabs_mult Rmult_comm ; apply Rlt_div_r.
  by apply Rabs_pos_lt, Rgt_not_eq.
  by apply Rle_lt_trans with (2 := Hs), Rmax_l.
  apply IH.
  by apply Rle_lt_trans with (2 := Hs), Rmax_r.
  rewrite /ptd' /= Hfirst.
  rewrite -Rplus_min_distr_r.
  rewrite -Rmult_min_distr_l.
  reflexivity.
  by apply Rlt_le.
  rewrite -Rplus_max_distr_r.
  rewrite -Rmult_max_distr_l.
  rewrite -Hlast.
  rewrite /ptd' /=.
  elim: (SF_t ptd) (SF_h ptd) => [ | [x1 _] /= s IH] x0 //=.
  by apply Rlt_le.
  apply f_equal.
  apply f_equal2.
  replace (u * b + v - (u * a + v)) with (u * (b - a)) by ring.
  rewrite /signe.
  case: (Rle_dec 0 (b - a)) (proj1 (Rminus_le_0 _ _) (Rlt_le _ _ Hab)) => // H _.
  case: Rle_dec (Rmult_le_pos _ _ (Rlt_le _ _ Hu) H) => // H0 _.
  case: (Rle_lt_or_eq_dec 0 (b - a)) (Rlt_not_eq _ _ (proj1 (Rminus_lt_0 _ _) Hab)) => // _ H1.
  case: Rle_lt_or_eq_dec (sym_not_eq (Rmult_integral_contrapositive_currified _ _ (Rgt_not_eq _ _ Hu) (sym_not_eq H1))) => //.
  
  revert ptd' ;
  apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] //=.
  set s' := {|
      SF_h := u * SF_h s + v;
      SF_t := [seq (u * fst X + v, u * snd X + v)
                 | X <- SF_t s] |}.
  rewrite Riemann_sum_cons (Riemann_sum_cons _  (u * x0 + v,u * y0 + v) s') /=.
  rewrite IH ; ring.
Qed.
Lemma ex_RInt_comp_lin (f : R -> R) (u v a b : R) :
  ex_RInt f (u * a + v) (u * b + v)
    -> ex_RInt (fun y => u * f (u * y + v)) a b.
Proof.
  case => l Hf.
  exists l.
  by apply is_RInt_comp_lin.
Qed.
Lemma RInt_comp_lin (f : R -> R) (u v a b : R) :
  RInt (fun y => u * f (u * y + v)) a b = RInt f (u * a + v) (u * b + v).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
  by rewrite ?RInt_point.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -(RInt_swap _ b) -(RInt_swap _ (u * b + v)).
    rewrite Hw => //.
    by apply Rlt_not_eq.
  case: (Req_dec 0 u) => [<- {u} | Hu].
    ring_simplify (0 * a + v) (0 * b + v).
    rewrite RInt_point.
    rewrite -(RInt_ext (fun _ => 0)).
    rewrite RInt_const ; ring.
    move => x _ ; ring.
  wlog: u v Hu f / (0 < u) => [Hw | {Hu} Hu].
    case: (Rle_lt_dec 0 u) => Hu'.
    case: Hu' => // Hu'.
    by apply Hw.
    replace (u * a + v) with (-((-u) * a + (-v))) by ring.
    replace (u * b + v) with (-((-u) * b + (-v))) by ring.
    rewrite -RInt_comp_opp.
    rewrite -Hw.
    apply RInt_ext => x _.
    ring_simplify (- (- u * x + - v)) ; ring.
    apply Rlt_not_eq, Ropp_lt_cancel ;
    by rewrite Ropp_0 Ropp_involutive.
    apply Ropp_lt_cancel ;
    by rewrite Ropp_0 Ropp_involutive.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  have : (u * a + v) <= (u * b + v).
    by apply Rlt_le, Rplus_lt_compat_r, Rmult_lt_compat_l.
  case: Rle_dec => // _ _.
  apply f_equal.
  apply Lim_seq_ext => n.
  rewrite /RInt_val.
  replace ((u * b + v - (u * a + v)) / (INR n + 1) * foldr Rplus 0 (SF_val_ly f (u * a + v) (u * b + v) n))
  with ((b - a) / (INR n + 1) * (u * foldr Rplus 0 (SF_val_ly f (u * a + v) (u * b + v) n)))
  by (rewrite /Rdiv ; ring).
  apply f_equal.
  rewrite /SF_val_ly /RInt_part.
  case: (S (S n)) => /= [ | m].
  by rewrite Rmult_0_r.
  pattern 0 at 2 4 ;
  replace 0 with (INR O) by auto.
  elim: m (0%nat) => [ | m IH] m0.
  simpl ; by rewrite Rmult_0_r.
  simpl iota.
  rewrite ?map_cons S_INR.
  simpl.
  rewrite -(S_INR m0) IH S_INR.
  rewrite -Rmult_plus_distr_l.
  apply f_equal.
  apply (f_equal (fun y => y + _)).
  apply f_equal.
  field.
  rewrite -S_INR.
  apply not_0_INR, sym_not_eq, O_S.
Qed.

(** * Order *)

Lemma RInt_le: forall f g a b,
    a <= b ->
   ex_RInt f a b ->  ex_RInt g a b -> 
   (forall x,  a <= x <= b -> f x <= g x) ->
   RInt f a b <= RInt g a b.
Proof.
intros f g a b H1 If Ig H2.
assert (Riemann_integrable f a b).
now apply ex_RInt_correct_2.
assert (Riemann_integrable g a b).
now apply ex_RInt_correct_2.
rewrite (RInt_correct _ _ _ X)(RInt_correct _ _ _ X0).
apply RiemannInt_P19.
exact H1.
intros; apply H2.
split; left; apply H.
Qed.

Lemma is_RInt_le: forall f g a b If Ig,
  a <= b ->
   is_RInt f a b If ->  is_RInt g a b Ig -> 
   (forall x,  a <= x <= b -> f x <= g x) ->
   If <= Ig.
Proof.
intros f g a b If Ig Hab Hf Hg Heq.
rewrite -(is_RInt_unique _ _ _ _ Hf).
rewrite -(is_RInt_unique _ _ _ _ Hg).
apply RInt_le => //.
by exists If.
by exists Ig.
Qed.

(** ** Absolute value *)

Lemma ex_RInt_abs :
  forall f a b, ex_RInt f a b ->
  ex_RInt (fun x => Rabs (f x)) a b.
Proof.
intros f a b If.
apply ex_RInt_correct_1.
apply RiemannInt_P16.
now apply ex_RInt_correct_2.
Qed.

Lemma RInt_abs: forall f a b,
   a <= b -> ex_RInt f a b ->
   Rabs (RInt f a b) <= RInt (fun t => Rabs (f t)) a b.
intros f a b H1 If.
unfold Rabs at 1.
case (Rcase_abs (RInt f a b)); intros Y.
rewrite <- RInt_opp.
apply RInt_le.
exact H1.
now apply ex_RInt_opp.
now apply ex_RInt_abs.
intros.
rewrite <- Rabs_Ropp.
apply RRle_abs.
apply RInt_le.
exact H1.
exact If.
now apply ex_RInt_abs.
intros.
apply RRle_abs.
Qed.

Lemma RInt_le_const: forall f a b M,
  ex_RInt f a b ->
  (forall t, Rmin a b <= t <= Rmax a b -> Rabs (f t) <= M) ->
  Rabs (RInt f a b) <= Rabs (b-a) * M.
intros f a b M If H.
wlog: a b H If / (a <= b) => [Hw | Hab] .
(* *)
case (Rle_or_lt a b); intros Hab.
now apply Hw.
rewrite <- RInt_swap.
replace (b-a) with (-(a-b)) by ring.
rewrite 2! Rabs_Ropp.
apply Hw.
intros t Ht; apply H.
rewrite Rmin_comm Rmax_comm.
exact Ht.
apply ex_RInt_swap.
exact If.
now left.
(* *)
rewrite (Rabs_right (b-a)).
rewrite Rmult_comm; rewrite <- RInt_const.
apply Rle_trans with (1:=RInt_abs _ _ _ Hab If).
apply RInt_le.
exact Hab.
now apply ex_RInt_abs.
apply ex_RInt_correct_1.
apply continuity_implies_RiemannInt.
exact Hab.
intros x Hx eps Heps.
exists 1; split.
apply Rlt_0_1.
intros.
unfold dist; simpl; unfold R_dist; simpl.
rewrite /Rminus Rplus_opp_r Rabs_R0.
exact Heps.
intros x Hx; apply H.
rewrite (Rmin_left _ _ Hab).
now rewrite Rmax_right.
apply Rle_ge, Rplus_le_reg_l with a.
now ring_simplify.
Qed.

(** Continuity *)

Lemma continuity_RInt: forall f a b,
  ex_RInt f a b ->
  (exists eps:posreal, ex_RInt f (b-eps) (b+eps)) ->
  continuity_pt (fun x : R => RInt f a x) b.
Proof.
intros f a b If (eps,Ifb) e He.
have : exists M : R, 
  forall x, b - eps <= x <= b + eps -> Rabs (f x) <= M.
  case: (ex_RInt_bounded _ _ _ Ifb) => m ; case => M H.
  exists (Rmax M (-m)) => x Hx.
  apply Rabs_le_between_Rmax.
  apply H.
  split.
  apply Rle_trans with (2 := proj1 Hx), Rmin_l.
  apply Rle_trans with (1 := proj2 Hx), Rmax_r.
case => M HM.
have Hd : 0 < Rmin eps (e / (M + 1)).
  apply Rmin_case.
  by apply eps.
  apply Rdiv_lt_0_compat.
  by apply He.
  apply Rle_lt_0_plus_1.
  apply Rle_trans with (1 := Rabs_pos (f b)).
  apply HM.
  split ; apply Rminus_le_0 ; ring_simplify ; apply Rlt_le, eps.
set d := mkposreal _ Hd.
exists d.

split.
by apply d.
intros x (Hx1,Hx2).
assert (ex_RInt f b x).
case (Rle_or_lt b x); intros Y.
apply ex_RInt_included1 with (b+eps).
apply ex_RInt_included2 with (b-eps).
exact Ifb.
split ; apply Rminus_le_0 ; ring_simplify ; apply Rlt_le, eps.
split.
exact Y.
assert (b - eps < x < b+eps).
apply Rabs_lt_between'.
apply Rlt_le_trans with (1:=Hx2).
apply Rmin_l.
left; apply H.
apply ex_RInt_swap.
apply ex_RInt_included1 with (b+eps).
apply ex_RInt_included2 with (b-eps).
exact Ifb.
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hx2).
apply Rmin_l.
split.
left; exact Y.
apply Rplus_le_reg_l with (-b); ring_simplify.
left; apply cond_pos.
simpl ; unfold R_dist.
unfold Rminus; rewrite RInt_swap Rplus_comm.
rewrite RInt_Chasles.
apply Rle_lt_trans with (Rabs (x-b)*(M+1)).
apply RInt_le_const.
exact H.
intros t Ht.
apply Rle_trans with M.
apply HM.
apply Rabs_le_between'.
apply Rle_trans with (Rabs (x-b)).
apply Rabs_le_between_min_max.
now rewrite Rmin_comm Rmax_comm.
apply Rlt_le, Rlt_le_trans with (1 := Hx2), Rmin_l.
apply Rminus_le_0 ; ring_simplify ; apply Rle_0_1.
apply Rlt_div_r.
apply Rle_lt_0_plus_1.
apply Rle_trans with (1 := Rabs_pos (f b)).
apply HM.
split ; apply Rminus_le_0 ; ring_simplify ; apply Rlt_le, eps.
apply Rlt_le_trans with (1:=Hx2).
apply Rmin_r.
now apply ex_RInt_swap.
now apply ex_RInt_Chasles with b.
Qed.

(** * Riemann integral and derivative *)

Lemma derivable_pt_lim_RInt (f : R -> R) (a : R) (x : R) :
  ex_RInt f a x -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x -> derivable_pt_lim (fun x => RInt f a x) x (f x).
Proof.
  move => Iax Iloc Cx.
  apply equiv_deriv_pt_lim_1.
  intros eps.
  destruct (Cx eps (cond_pos eps)) as (d,(Hd1,Hd2)).
  unfold dist in Hd2; simpl in Hd2; unfold R_dist in Hd2.
  destruct Iloc as (e,He).
  exists (mkposreal _ (Rmin_stable_in_posreal e (mkposreal _ Hd1))).
  (* *)
  simpl; intros y Hy.
  assert (ex_RInt f x y).
  assert (x-e <= y <= x+e).
  apply Rabs_le_between'.
  left; apply Rlt_le_trans with (1:=Hy); apply Rmin_l.
  case (Rle_or_lt x y); intros M.
  apply ex_RInt_included1 with (x+e).
  apply ex_RInt_included2 with (x-e).
  exact He.
  split; apply Rplus_le_reg_r with (-x); ring_simplify.
  apply Rplus_le_reg_r with e; ring_simplify.
  left; apply cond_pos.
  left; apply cond_pos.
  split;[exact M|apply H].
  apply ex_RInt_swap.
  apply ex_RInt_included1 with (x+e).
  apply ex_RInt_included2 with (x-e).
  exact He.
  exact H.
  split;[left; exact M|idtac].
  apply Rplus_le_reg_r with (-x); ring_simplify.
  left; apply cond_pos.
  assert (ex_RInt f a y).
  now apply ex_RInt_Chasles with x.
  (* *)
  replace (RInt f a y - RInt f a x - f x * (y - x)) with
    (RInt (fun z => f z - f x) x y).
  rewrite Rmult_comm.
  apply RInt_le_const.
  apply ex_RInt_minus.
  exact H.
  apply ex_RInt_const.
  intros t Ht.
  case (Req_dec x t); intros Hxt.
  unfold Rminus; rewrite Hxt Rplus_opp_r Rabs_R0.
  left; apply cond_pos.
  left; apply Hd2.
  split.
  now split.
  apply Rle_lt_trans with (Rabs (y - x)).
  apply Rabs_le_between_min_max.
  now rewrite Rmin_comm Rmax_comm.
  apply Rlt_le_trans with (1:=Hy); apply Rmin_r.
  (* *)
  rewrite RInt_minus.
  rewrite RInt_const.
  rewrite <- (RInt_Chasles f x a y).
  unfold Rminus; rewrite RInt_swap.
  ring.
  now apply ex_RInt_swap.
  exact H0.
  exact H.
  apply ex_RInt_const.
Qed.


Lemma RInt_Derive (f : R -> R) (a b : R):
  (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) -> 
  (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt (Derive f) x) ->
  RInt (Derive f) a b = f b - f a.
Proof.
intros Df Cdf.
wlog: a b Df Cdf /(a <= b) => [Hw | Hab ].
case (Rle_or_lt a b); intros Hab.
now apply Hw.
rewrite <- RInt_swap.
rewrite Hw; try easy.
ring.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
now left.
rewrite Rmin_left in Df Cdf; try exact Hab.
rewrite Rmax_right in Df Cdf; try exact Hab.

wlog : f Df Cdf /((forall x, ex_derive f x) /\ (forall x, continuity_pt (Derive f) x))
  => [Hw | {Df Cdf} [Df Cdf]].
  rewrite -?(extension_C1_ext f a b) ; try (apply Rbar_finite_le ; intuition).
  rewrite -(RInt_ext (Derive (extension_C1 f a b))).
  apply Hw.
  move => x Hx.
  apply extension_C1_ex_derive.
  by apply Rbar_finite_le.
  move => y Hay Hyb.
  apply Df ; split ; by apply Rbar_finite_le.
  move => y Hy.
  apply extension_C1_Derive_cont.
  by apply Rbar_finite_le.
  move => x Hax Hxb ; split.
  apply Df ; split ; by apply Rbar_finite_le.
  apply Cdf ; split ; by apply Rbar_finite_le.
  split => x.
  apply extension_C1_ex_derive.
  by apply Rbar_finite_le.
  move => y Hay Hyb.
  apply Df ; split ; by apply Rbar_finite_le.
  apply extension_C1_Derive_cont.
  by apply Rbar_finite_le.
  move => y Hay Hyb ; split.
  apply Df ; split ; by apply Rbar_finite_le.
  apply Cdf ; split ; by apply Rbar_finite_le.
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ x Hx.
  apply is_derive_unique, extension_C1_is_derive.
  by apply Rbar_finite_le, Hx.
  by apply Rbar_finite_le, Hx.
  apply Derive_correct.
  by apply Df.

assert (forall x, continuity_pt f x).
intros x.
destruct (Df x) as (y,Hy).
apply derivable_continuous_pt.
now exists y.
(* *)
destruct (fn_eq_Derive_eq f (fun x => RInt (Derive f) a x) a b).
apply H.
apply H.
apply continuity_RInt.
apply ex_RInt_point.
exists (mkposreal _ Rlt_0_1).
by apply ex_RInt_cont.
apply continuity_RInt.
by apply ex_RInt_cont.
exists (mkposreal _ Rlt_0_1).
by apply ex_RInt_cont.
intros x Hx; apply Df.
intros x Hx.
eexists.
apply derivable_pt_lim_RInt.
by apply ex_RInt_cont.
exists (mkposreal _ Rlt_0_1).
by apply ex_RInt_cont.
apply Cdf.
intros x Hx.
apply sym_eq, is_derive_unique.
apply derivable_pt_lim_RInt.
by apply ex_RInt_cont.
exists (mkposreal _ Rlt_0_1).
by apply ex_RInt_cont.
apply Cdf.
rewrite (H0 a).
rewrite (H0 b).
rewrite RInt_point.
ring.
split;[apply Hab|apply Rle_refl].
split;[apply Rle_refl | apply Hab].
Qed.


Lemma is_RInt_Derive (f : R -> R) (a b : R) :
  (forall x, Rmin a b  <= x <= Rmax a b  -> ex_derive f x) -> 
  (forall x, Rmin a b  <= x <= Rmax a b  -> continuity_pt (Derive f) x) ->
  is_RInt (Derive f) a b (f b - f a).
Proof.
  move => Df Cdf.
  rewrite -(RInt_Derive _ _ _ Df Cdf).
  suff : ex_RInt (Derive f) a b.
    case => l H.
    by rewrite (is_RInt_unique _ _ _ _ H).
  apply ex_RInt_cont.
  move => x Hx.
  by apply Cdf.
Qed.

Lemma derivable_pt_lim_param_aux : forall f a b x,
  locally (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) x ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally (fun y => ex_RInt (fun t => f y t) a b) x ->
  ex_RInt (fun t => Derive (fun u => f u t) x) a b ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x.
wlog: a b / a < b => H.
(* *)
destruct (total_order_T a b) as [[Hab|Hab]|Hab].
now apply H.
intros _ _ _ _.
rewrite Hab.
rewrite RInt_point.
apply (is_derive_ext (fun _ => 0)).
intros t.
apply sym_eq.
apply RInt_point.
apply derivable_pt_lim_const.
intros H1 H2 H3 H4.
apply (is_derive_ext (fun u => - RInt (fun t => f u t) b a)).
intros t.
apply RInt_swap.
rewrite -RInt_swap.
apply derivable_pt_lim_opp.
apply H.
exact Hab.
now rewrite Rmin_comm Rmax_comm.
now rewrite Rmin_comm Rmax_comm.
apply: locally_impl H3.
apply locally_forall => y H3.
now apply ex_RInt_swap.
now apply ex_RInt_swap.
(* *)
rewrite Rmin_left. 2: now apply Rlt_le.
rewrite Rmax_right. 2: now apply Rlt_le.
intros Df Cdf If IDf.
apply equiv_deriv_pt_lim_1.
refine (let Cdf' := uniform_continuity_2d_1d (fun u v => Derive (fun z => f z u) v) a b x _ in _).
intros t Ht eps.
specialize (Cdf t Ht eps).
simpl in Cdf.
destruct Cdf as (d,Cdf).
exists d.
intros v u Hv Hu.
now apply Cdf.
intros eps. clear Cdf.
assert (H': 0 < eps / Rabs (b - a)).
apply Rmult_lt_0_compat.
apply cond_pos.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt.
apply Rgt_not_eq.
now apply Rgt_minus.
move: (Cdf' (mkposreal _ H')) => {Cdf'} [d1 Cdf].
move: (locally_and _ _ _ Df If) => {Df If} [d2 DIf].
exists (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2))) => /= y Hy.
assert (D1: ex_RInt (fun t => f y t) a b).
apply DIf.
apply Rlt_le_trans with (1 := Hy).
apply Rle_trans with (1 := Rmin_r _ _).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
assert (D2: ex_RInt (fun t => f x t) a b).
apply DIf.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite -RInt_minus //.
rewrite Rmult_comm.
rewrite -RInt_scal //.
assert (D3: ex_RInt (fun t => f y t - f x t) a b) by now apply (ex_RInt_minus (fun u => f y u) (fun u => f x u)).
assert (D4: ex_RInt (fun t => (y - x) * Derive (fun u => f u t) x) a b) by now apply ex_RInt_scal.
rewrite -RInt_minus //.
assert (D5: ex_RInt (fun t => f y t - f x t - (y - x) * Derive (fun u => f u t) x) a b) by now apply ex_RInt_minus.
rewrite (RInt_correct _ _ _ (ex_RInt_correct_2 _ _ _ D5)).
assert (D6: ex_RInt (fun t => Rabs (f y t - f x t - (y - x) * Derive (fun u => f u t) x)) a b) by now apply ex_RInt_abs.
apply Rle_trans with (1 := RiemannInt_P17 _ (ex_RInt_correct_2 _ _ _ D6) (Rlt_le _ _ H)).
refine (Rle_trans _ _ _ (RiemannInt_P19 _ (RiemannInt_P14 a b (eps / Rabs (b - a) * Rabs (y - x))) (Rlt_le _ _ H) _) _).
intros u Hu.
destruct (MVT_cor4 (fun t => f t u) x) with (eps := pos_div_2 d2) (b := y) as (z,Hz).
intros z Hz.
apply DIf.
apply Rle_lt_trans with (1 := Hz).
apply: Rlt_eps2_eps.
apply cond_pos.
split ; now apply Rlt_le.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
rewrite (proj1 Hz).
rewrite Rmult_comm.
rewrite -Rmult_minus_distr_l Rabs_mult.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
apply Rabs_pos.
apply Rlt_le.
apply Cdf.
split ; now apply Rlt_le.
apply Rabs_le_between'.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le.
apply cond_pos.
split ; now apply Rlt_le.
apply Rabs_le_between'.
apply Rle_trans with (1 := proj2 Hz).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite RiemannInt_P15.
rewrite Rabs_pos_eq.
right.
field.
apply Rgt_not_eq.
now apply Rgt_minus.
apply Rge_le.
apply Rge_minus.
now apply Rgt_ge.
Qed.


Lemma derivable_pt_lim_param : forall f a b x,
  locally (fun x => forall t, Rmin a b <= t <= Rmax a b -> ex_derive (fun u => f u t) x) x ->
  (forall t, Rmin a b <= t <= Rmax a b -> continuity_2d_pt (fun u v => Derive (fun z => f z v) u) x t) ->
  locally (fun y => ex_RInt (fun t => f y t) a b) x ->
  derivable_pt_lim (fun x => RInt (fun t => f x t) a b) x
    (RInt (fun t => Derive (fun u => f u t) x) a b).
Proof.
intros f a b x H1 H2 H3.
apply derivable_pt_lim_param_aux; try easy.
apply ex_RInt_correct_1.
clear H1 H3.
wlog: a b H2 / a < b => H.
case (total_order_T a b).
intro Y; case Y.
now apply H.
intros Heq; rewrite Heq.
apply RiemannInt_P7.
intros  Y.
apply RiemannInt_P1.
apply H.
intros; apply H2.
rewrite Rmin_comm Rmax_comm.
exact H0.
exact Y.
rewrite Rmin_left in H2.
2: now left.
rewrite Rmax_right in H2.
2: now left.
apply continuity_implies_RiemannInt.
now left.
intros y Hy eps Heps.
destruct (H2 _ Hy (mkposreal eps Heps)) as (d,Hd).
simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist; simpl.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
Qed.



Lemma derivable_pt_lim_RInt' :
  forall f a x,
  ex_RInt f x a -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x ->
  derivable_pt_lim (fun x => RInt f x a) x (- f x).
Proof.
intros f a x Hi Ix Cx.
apply (is_derive_ext (fun u => - RInt f a u)).
intros t.
apply RInt_swap.
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt ; try easy.
apply ex_RInt_correct_1.
apply RiemannInt_P1.
now apply ex_RInt_correct_2.
Qed.

Lemma ex_RInt_inside :
  forall f a b x e,
  ex_RInt f (x-e) (x+e) -> Rabs (a-x) <= e -> Rabs (b-x) <= e ->
  ex_RInt f a b.
Proof.
intros f a b x e Hf Ha Hb.
wlog: a b Ha Hb / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
now left.
apply ex_RInt_included1 with (x+e).
apply ex_RInt_included2 with (x-e).
exact Hf.
now apply Rabs_le_between'.
split.
exact Hab.
assert (x-e <= b <= x+e) by now apply Rabs_le_between'.
apply H.
Qed.

Lemma RInt_Chasles_bound_comp_l_loc :
  forall f a b x,
  locally (fun y => ex_RInt (f y) (a x) b) x ->
  (exists eps : posreal, locally (fun y => ex_RInt (f y) (a x - eps) (a x + eps)) x) ->
  continuity_pt a x ->
  locally (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) b =
    RInt (f x') (a x') b) x.
Proof.
intros f a b x Hab (eps,Hae) Ca.
move /continuity_pt_locally: Ca => Ca.
apply: locally_impl (Ca eps).
apply: locally_impl Hab.
apply: locally_impl Hae.
apply locally_forall => y Hae Hab Hy.
apply RInt_Chasles with (2 := Hab).
apply ex_RInt_inside with (1 := Hae).
now apply Rlt_le.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
Qed.

Lemma RInt_Chasles_bound_comp_loc :
  forall f a b x,
  locally (fun y => ex_RInt (f y) (a x) (b x)) x ->
  (exists eps : posreal, locally (fun y => ex_RInt (f y) (a x - eps) (a x + eps)) x) ->
  (exists eps : posreal, locally (fun y => ex_RInt (f y) (b x - eps) (b x + eps)) x) ->
  continuity_pt a x ->
  continuity_pt b x ->
  locally (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) (b x') =
    RInt (f x') (a x') (b x')) x.
Proof.
intros f a b x Hab (ea,Hae) (eb,Hbe) Ca Cb.
move /continuity_pt_locally: Ca => Ca.
move /continuity_pt_locally: Cb => Cb.
set (e := mkposreal _ (Rmin_stable_in_posreal ea eb)).
apply: locally_impl (Ca e).
apply: locally_impl (Cb e).
apply: locally_impl Hab.
apply: locally_impl Hae.
apply: locally_impl Hbe.
apply locally_forall => y Hbe Hae Hab Hby Hay.
apply RInt_Chasles.
apply ex_RInt_inside with (1 := Hae).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hay).
exact: Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply ex_RInt_Chasles with (1 := Hab).
apply ex_RInt_inside with (1 := Hbe).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hby).
exact: Rmin_r.
Qed.

Lemma derivable_pt_lim_RInt_bound_comp :
  forall f a b da db x,
  ex_RInt f (a x) (b x) ->
  (exists eps : posreal, ex_RInt f (a x - eps) (a x + eps)) ->
  (exists eps : posreal, ex_RInt f (b x - eps) (b x + eps)) ->
  continuity_pt f (a x) ->
  continuity_pt f (b x) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  derivable_pt_lim (fun x => RInt f (a x) (b x)) x (db * f (b x) - da * f (a x)).
Proof.
intros f a b da db x Hi Ia Ib Ca Cb Da Db.
apply is_derive_ext_loc with (fun x0 => comp (fun y => RInt f y (a x)) a x0
  + comp (fun y => RInt f (a x) y) b x0).
(* *)
unfold comp.
apply RInt_Chasles_bound_comp_loc.
now apply locally_forall.
destruct Ia as (d1,H1).
exists d1.
now apply locally_forall.
destruct Ib as (d2,H2).
exists d2.
now apply locally_forall.
apply derivable_continuous_pt.
eexists ; eassumption.
apply derivable_continuous_pt.
eexists ; eassumption.
(* *)
replace (db * f (b x) - da * f (a x)) with (- f(a x) * da + f (b x) * db) by ring.
apply derivable_pt_lim_plus.
apply derivable_pt_lim_comp.
exact Da.
apply derivable_pt_lim_RInt' ; trivial.
apply ex_RInt_point.
apply derivable_pt_lim_comp.
exact Db.
now apply derivable_pt_lim_RInt.
Qed.







Lemma derivable_pt_lim_RInt_param_bound_comp_aux1: forall f a x,
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps)) x) ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        a x-eps <= t <= a x+eps ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->

  continuity_2d_pt
     (fun u v : R => Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) x (a x).
Proof.
intros f a x (d1,(d2,Ia)) (d3,(d4,Df)) Cdf e.
assert (J1:(continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x (a x)))
   by now apply locally_2d_singleton in Cdf.
destruct Cdf as (d5,Cdf).
destruct (J1 (mkposreal _ Rlt_0_1)) as (d6,Df1); simpl in Df1.
assert (J2: 0 < e / (Rabs (Derive (fun z : R => f z (a x)) x)+1)).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
exists (mkposreal _ (Rmin_stable_in_posreal 
                  (mkposreal _ (Rmin_stable_in_posreal 
                        d1 
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d2) d3))))
                  (mkposreal _ (Rmin_stable_in_posreal 
                       (mkposreal _ (Rmin_stable_in_posreal (pos_div_2 d4) d5))
                       (mkposreal _ (Rmin_stable_in_posreal d6 (mkposreal _ J2))))))). 
simpl; intros u v Hu Hv.
rewrite (Derive_ext (fun z : R => RInt (fun t : R => f z t) (a x) (a x)) (fun z => 0)).
2: intros t; apply RInt_point.
replace (Derive (fun _ : R => 0) x) with 0%R.
2: apply sym_eq, is_derive_unique, derivable_pt_lim_const.
rewrite Rminus_0_r.
replace (Derive (fun z : R => RInt (fun t : R => f z t) v (a x)) u) with 
  (RInt (fun z => Derive (fun u => f u z) u) v (a x)).
(* *)
apply Rle_lt_trans with (Rabs (a x -v) *
   (Rabs (Derive (fun z : R => f z (a x)) x) +1)).
apply RInt_le_const.
apply ex_RInt_cont.
intros y Hy eps Heps.
assert (Y1:(Rabs (u - x) < d5)).
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
assert (Y2:(Rabs (y - a x) < d5)).
apply Rle_lt_trans with (Rabs (v-a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
destruct (Cdf u y Y1 Y2 (mkposreal eps Heps)) as (d,Hd); simpl in Hd.
exists d; split.
apply cond_pos.
unfold dist; simpl; unfold R_dist.
intros z (_,Hz).
apply Hd.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
exact Hz.
intros t Ht.
apply Rplus_le_reg_r with (-Rabs (Derive (fun z : R => f z (a x)) x)).
apply Rle_trans with (1:=Rabs_triang_inv _ _).
ring_simplify.
left; apply Df1.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
replace (a x -v) with (-(v - a x)) by ring; rewrite Rabs_Ropp.
apply Rlt_le_trans with ((e / (Rabs (Derive (fun z : R => f z (a x)) x) + 1)) 
  * (Rabs (Derive (fun z : R => f z (a x)) x) + 1)).
apply Rmult_lt_compat_r.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
right; field.
apply sym_not_eq, Rlt_not_eq.
apply Rlt_le_trans with (0+1).
rewrite Rplus_0_l; apply Rlt_0_1.
apply Rplus_le_compat_r; apply Rabs_pos.
(* *)
apply sym_eq, is_derive_unique.
apply derivable_pt_lim_param.
exists (pos_div_2 d4).
intros y Hy t Ht.
apply Df.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d4).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply (proj1 (Rabs_le_between' t (a x) d3)).
apply Rle_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
intros t Ht.
apply Cdf.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
exists (pos_div_2 d2).
intros y Hy.
apply ex_RInt_inside with (a x) d1.
apply Ia.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d2).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
Qed.






(* integral between a(x) and fixed b *)
Lemma derivable_pt_lim_RInt_param_bound_comp_aux2 :
  forall f a b x da,
  (locally (fun y => ex_RInt (fun t => f y t) (a x) b) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps)) x) ->
  derivable_pt_lim a x da ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) b <= t <= Rmax (a x+eps) b ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (forall t : R,
          Rmin (a x) b <= t <= Rmax (a x) b ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> 
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
   continuity_pt (fun t => f x t) (a x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) b) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) b+(-f x (a x))*da).
Proof.
intros f a b x da Hi (d0,Ia) Da Df Cdf1 Cdf2 Cfa.
rewrite Rplus_comm.
apply is_derive_ext_loc with (fun x0 => RInt (fun t : R => f x0 t) (a x0) (a x) + RInt (fun t : R => f x0 t) (a x) b).
apply RInt_Chasles_bound_comp_l_loc.
exact Hi.
now exists d0.
apply derivable_continuous_pt.
eexists.
apply Da.
apply derivable_pt_lim_plus.
(* *)
replace (- f x (a x) * da) with (0*1+- f x (a x) * da) by ring.
apply derivable_pt_lim_comp_2d with 
   (f1 := fun x0 y => RInt (fun t : R => f x0 t) y (a x)).
replace 0 with (Derive (fun u => RInt (fun t : R => f u t) (a x) (a x)) x).
apply derivable_differentiable_pt_lim.
(* . *)
destruct Df as (d1,(d2,Df)).
destruct Cdf2 as (d3,Cdf2).
destruct Ia as (d4,Ia).
exists (mkposreal _ (Rmin_stable_in_posreal 
                (mkposreal _ (Rmin_stable_in_posreal d1 (pos_div_2 d2)))
                (mkposreal _ (Rmin_stable_in_posreal d3 
                            (mkposreal _ (Rmin_stable_in_posreal d0 (pos_div_2 d4))))))).
simpl; intros u v Hu Hv.
eexists; eapply derivable_pt_lim_param.
exists (pos_div_2 d2).
intros y Hy t Ht.
apply Df.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d2).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_r.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (a x - d1).
apply Rmin_l.
apply Rmin_glb.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x + d1); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (a x + d1).
apply Rmax_lub.
assert (a x - d1 <= v <= a x + d1).
apply Rabs_le_between'.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_l _ _).
apply Rmin_l.
apply H.
apply Rplus_le_reg_l with (- a x); ring_simplify.
left; apply cond_pos.
apply Rmax_l.
intros t Ht.
apply Cdf2.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
apply Rle_lt_trans with (Rabs (v - a x)).
now apply Rabs_le_between_min_max.
apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
exists (pos_div_2 d4).
intros y Hy.
apply ex_RInt_inside with (a x) d0.
apply Ia.
replace (y-x) with ((y-u)+(u-x)) by ring.
apply Rle_lt_trans with (1:=Rabs_triang _ _).
rewrite (double_var d4).
apply Rplus_lt_compat.
exact Hy.
apply Rlt_le_trans with (1:=Hu).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_r.
left; apply Rlt_le_trans with (1:=Hv).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rle_trans with (1:=Rmin_r _ _).
apply Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
left; apply cond_pos.
(* . *)
apply derivable_pt_lim_RInt'.
apply ex_RInt_point.
apply locally_singleton in Ia.
now exists d0.
exact Cfa.
(* . *)
apply derivable_pt_lim_RInt_param_bound_comp_aux1; try easy.
exists d0; exact Ia.
destruct Df as (d,Hd).
exists d.
apply locally_impl with (2:=Hd).
apply locally_forall.
intros y H t Ht.
apply H.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rmin_l.
apply Rle_trans with (1:=proj2 Ht).
apply Rmax_l.
(* . *)
apply is_derive_unique.
apply is_derive_ext with (fun _ => 0).
intros t; apply sym_eq, RInt_point.
apply derivable_pt_lim_const.
(* . *)
apply derivable_pt_lim_id.
exact Da.
(* *)
apply derivable_pt_lim_param.
destruct Df as (d,Df).
apply locally_impl with (2:= Df).
apply locally_forall.
intros y Hy t Ht; apply Hy.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x+d); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
exact Cdf1.
exact Hi.
Qed.



Lemma derivable_pt_lim_RInt_param_bound_comp_aux3 :
  forall f a b x db,
  (locally (fun y => ex_RInt (fun t => f y t) a (b x)) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps)) x) ->
  derivable_pt_lim b x db ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin a (b x-eps) <= t <= Rmax a (b x+eps) ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (forall t : R,
          Rmin a (b x) <= t <= Rmax a (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> 
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (b x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) a (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db).
Proof.
intros f a b x db If Ib Db Df Cf1 Cf2 Cfb.
apply is_derive_ext with (fun x0 => - RInt (fun t : R => f x0 t) (b x0) a).
intros t; apply RInt_swap.
replace (RInt (fun t : R => Derive (fun u => f u t) x) a (b x) +f x (b x)*db) with
      (- ((RInt (fun t : R => Derive (fun u : R => f u t) x) (b x) a) + - f x (b x)*db)).
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt_param_bound_comp_aux2; try easy.
apply locally_impl with (2:=If).
apply locally_forall.
intros y H.
now apply ex_RInt_swap.
destruct Df as (e,H).
exists e.
apply locally_impl with (2:=H).
apply locally_forall.
intros y H' t Ht.
apply H'.
now rewrite Rmin_comm Rmax_comm.
intros t Ht.
apply Cf1.
now rewrite Rmin_comm Rmax_comm.
rewrite <- RInt_swap.
ring.
Qed.


Lemma derivable_pt_lim_RInt_param_bound_comp :
 forall f a b x da db,
  (locally (fun y => ex_RInt (fun t => f y t) (a x) (b x)) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (a x - eps) (a x + eps)) x) ->
  (exists eps:posreal, locally (fun y => ex_RInt (fun t => f y t) (b x - eps) (b x + eps)) x) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  (exists eps:posreal, locally
    (fun x0 : R =>
       forall t : R,
        Rmin (a x-eps) (b x -eps) <= t <= Rmax (a x+eps) (b x+eps) ->
        ex_derive (fun u : R => f u t) x0) x) ->
  (forall t : R,
          Rmin (a x) (b x) <= t <= Rmax (a x) (b x) ->
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x t) -> 
  (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (a x)) ->
 (locally_2d (fun x' t =>
         continuity_2d_pt (fun u v : R => Derive (fun z : R => f z v) u) x' t) x (b x)) ->
   continuity_pt (fun t => f x t) (a x) ->   continuity_pt (fun t => f x t) (b x) ->   

 derivable_pt_lim (fun x => RInt (fun t => f x t) (a x) (b x)) x
    (RInt (fun t : R => Derive (fun u => f u t) x) (a x) (b x)+(-f x (a x))*da+(f x (b x))*db).
Proof.
intros f a b x da db If Ifa Ifb Da Db Df Cf Cfa Cfb Ca Cb.
apply is_derive_ext_loc with (fun x0 : R => RInt (fun t : R => f x0 t) (a x0) (a x)
    + RInt (fun t : R => f x0 t) (a x) (b x0)).
apply RInt_Chasles_bound_comp_loc ; trivial.
apply derivable_continuous_pt.
eexists.
apply Da.
apply derivable_continuous_pt.
eexists.
apply Db.
replace (RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (b x) +
   - f x (a x) * da + f x (b x) * db) with
   ((RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (a x) + - f x (a x) * da) +
      (RInt (fun t : R => Derive (fun u : R => f u t) x) (a x) (b x) + f x (b x)*db)).
apply derivable_pt_lim_plus.
(* *)
apply derivable_pt_lim_RInt_param_bound_comp_aux2; try easy.
exists (mkposreal _ Rlt_0_1).
intros y Hy.
apply ex_RInt_point.
destruct Df as (e,H).
exists e.
apply locally_impl with (2:=H).
apply locally_forall.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
intros t Ht.
apply Cf.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_trans with (1:=Rmin_l _ _).
right; apply sym_eq, Rmin_left.
now right.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_trans with (2:=Rmax_l _ _).
right; apply Rmax_left.
now right.
(* *)
apply derivable_pt_lim_RInt_param_bound_comp_aux3; try easy.
destruct Df as (e,H).
exists e.
apply locally_impl with (2:=H).
apply locally_forall.
intros y H' t Ht.
apply H'.
split.
apply Rle_trans with (2:=proj1 Ht).
apply Rle_min_compat_r.
apply Rplus_le_reg_l with (-a x + e); ring_simplify.
left; apply cond_pos.
apply Rle_trans with (1:=proj2 Ht).
apply Rle_max_compat_r.
apply Rplus_le_reg_l with (-a x); ring_simplify.
left; apply cond_pos.
rewrite RInt_point.
ring.
Qed.

Lemma is_RInt_comp (f g : R -> R) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt f (g x))
  -> (forall x, Rmin a b <= x <= Rmax a b -> ex_derive g x /\ continuity_pt (Derive g) x)
  -> is_RInt (fun y => Derive g y * f (g y)) a b (RInt f (g a) (g b)).
Proof.
  case: (Req_dec a b) => [<- {b} | Hab].
    move => Hf Hg.
    rewrite RInt_point ; by apply is_RInt_point.
  wlog: a b Hab /(a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab' Hf Hg.
    case: Hab' => // Hab'.
    by apply Hw.
    apply is_RInt_swap ; rewrite RInt_swap.
    apply Hw => //.
    by apply sym_not_eq.
    rewrite Rmin_comm Rmax_comm.
    by apply Hf.
    rewrite Rmin_comm Rmax_comm.
    by apply Hg.
  rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab)
    => // _ _.
    
  wlog: g / (forall x : R, ex_derive g x /\ continuity_pt (Derive g) x) => [Hw Hf Hg | Hg Hf _].
    rewrite -?(extension_C1_ext g a b) ; try by [left | right].
    set g0 := extension_C1 g a b.
    apply is_RInt_ext with (fun y : R => Derive g0 y * f (g0 y)).
    rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
    apply f_equal2.
    apply is_derive_unique.
    apply extension_C1_is_derive.
    by apply Rbar_finite_le, Hx.
    by apply Rbar_finite_le, Hx.
    by apply Derive_correct, Hg.
    apply f_equal.
    apply extension_C1_ext.
    by apply Rbar_finite_le, Hx.
    by apply Rbar_finite_le, Hx.
    have Hg0 : forall x : R, ex_derive g0 x /\ continuity_pt (Derive g0) x.
    move => x ; rewrite /g0 ; split.
    apply extension_C1_ex_derive.
    by left.
    move => y Hay Hyb ; apply Hg.
    split ; by apply Rbar_finite_le.
    apply extension_C1_Derive_cont.
    by left.
    move => y Hay Hyb.
    apply Hg.
    split ; by apply Rbar_finite_le.
    apply Hw.
    by apply Hg0.
    move => x Hx.
    rewrite /g0 extension_C1_ext.
    by apply Hf.
    by apply Rbar_finite_le, Hx.
    by apply Rbar_finite_le, Hx.
    move => x Hx.
    by apply Hg0.
  wlog: f Hf / (forall x, continuity_pt f x) => [Hw | {Hf} Hf].
    case: (continuity_ab_maj g a b (Rlt_le _ _ Hab)) => [ | M HM].
      move => x Hx.
      apply derivable_continuous_pt.
      exists (Derive g x) ; apply Derive_correct.
      by apply Hg.
    case: (continuity_ab_min g a b (Rlt_le _ _ Hab)) => [ | m Hm].
      move => x Hx.
      apply derivable_continuous_pt.
      exists (Derive g x) ; apply Derive_correct.
      by apply Hg.
    have H : g m <= g M.
      apply Hm ; intuition.
    case: (prolongement_C0 f (g m) (g M)) => [ | y Hy | f0 Hf0].
    by [].
    case: (IVT_gen g m M y).
    move => x ; apply derivable_continuous_pt.
    exists (Derive g x) ; apply Derive_correct.
    by apply Hg.
    rewrite /Rmin /Rmax ; case: Rle_dec => //.
    move => x [Hx <-].
    apply Hf ; split.
    apply Rle_trans with (2 := proj1 Hx).
    apply Rmin_case ; intuition.
    apply Rle_trans with (1 := proj2 Hx).
    apply Rmax_case ; intuition.
    replace (RInt f (g a) (g b)) with (RInt f0 (g a) (g b)).
    apply is_RInt_ext with (fun y : R => Derive g y * f0 (g y)).
    rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hc.
    apply f_equal.
    apply Hf0 ; split.
    by apply Hm.
    by apply HM.
    apply Hw.
    move => x Hx ; apply Hf0.
    apply Hf0.
    apply RInt_ext => x Hx.
    apply Hf0 ; split.
    apply Rle_trans with (2 := proj1 Hx).
    apply Rmin_case ; intuition.
    apply Rle_trans with (1 := proj2 Hx).
    apply Rmax_case ; intuition.
  suff : ex_RInt (fun y : R => Derive g y * f (g y)) a b 
    /\ RInt (fun y : R => Derive g y * f (g y)) a b = (RInt f (g a) (g b)).
  case => [[If H] <-].
  by rewrite (is_RInt_unique _ _ _ _ H).
  have H : forall x, continuity_pt (fun y : R => Derive g y * f (g y)) x.
    move => x.
    apply continuity_pt_mult.
    by apply Hg.
    apply continuity_pt_comp.
    apply derivable_continuous_pt.
    exists (Derive g x) ; apply Derive_correct.
    by apply Hg.
    by apply Hf.
  have H0 : forall a b, ex_RInt (fun y : R => Derive g y * f (g y)) a b.
    move => a0 b0.
    apply ex_RInt_cont => x Hx.
    by apply H.
  split.
  by apply H0.
  case: (fn_eq_Derive_eq (fun b => RInt (fun y : R => Derive g y * f (g y)) a b)
    (fun b => RInt f (g a) (g b)) a b).
  apply continuity_RInt.
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply H0.
  apply continuity_RInt.
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply H0.
  apply (continuity_pt_comp g).
  apply derivable_continuous_pt.
  exists (Derive g a) ; apply Derive_correct.
  by apply Hg.
  apply continuity_RInt.
  apply ex_RInt_cont => x Hx.
  by apply Hf.
  exists (mkposreal _ Rlt_0_1) => /=.
  apply ex_RInt_cont => x Hx.
  by apply Hf.
  apply (continuity_pt_comp g).
  apply derivable_continuous_pt.
  exists (Derive g b) ; apply Derive_correct.
  by apply Hg.
  apply continuity_RInt.
  apply ex_RInt_cont => x Hx.
  by apply Hf.
  exists (mkposreal _ Rlt_0_1) => /=.
  apply ex_RInt_cont => x Hx.
  by apply Hf.
  move => x Hx.
  evar (l : R) ; exists l ; unfold l.
  apply (derivable_pt_lim_RInt (fun y : R => Derive g y * f (g y)) a x).
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply H0.
  by apply H.
  move => x Hx.
  evar (l : R) ; exists l ; unfold l.
  apply derivable_pt_lim_comp.
  apply Derive_correct.
  by apply Hg.
  apply (derivable_pt_lim_RInt f (g a) (g x)).
  by apply ex_RInt_cont.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply ex_RInt_cont.
  by apply Hf.
  move => x Hx.
  search_derive.
  unfold l.
  apply (derivable_pt_lim_RInt (fun y : R => Derive g y * f (g y)) a x).
  by apply H0.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply H0.
  by apply H.
  apply sym_eq ; search_derive.
  apply derivable_pt_lim_comp.
  apply Derive_correct.
  by apply Hg.
  apply (derivable_pt_lim_RInt f (g a) (g x)).
  by apply ex_RInt_cont.
  exists (mkposreal _ Rlt_0_1) => /=.
  by apply ex_RInt_cont.
  by apply Hf.
  by apply Rmult_comm.
  move => x H1.
  rewrite H1 ; intuition.
  apply Rminus_diag_uniq ; ring_simplify.
  move: (H1 a (conj (Rle_refl _) (Rlt_le _ _ Hab))) => {H1}.
  rewrite ?RInt_point Rplus_0_l.
  by apply sym_eq.
Qed.
