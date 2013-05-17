Require Import Reals Decidable Rbar Markov Floor Rcomplements.

(** * Upper and lower bounds *)

(** ** Upper bound *)

Definition Rbar_is_upper_bound (E : Rbar -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le x l.

(** Specific upper bounds *)

Lemma Rbar_ub_p_infty (E : Rbar -> Prop) :
  Rbar_is_upper_bound E p_infty.
Proof.
  intro x ; destruct x as [x | | ] ; intro Hx.
  left ; simpl ; auto.
  right ; simpl ; auto.
  left ; simpl ; auto.
Qed.

Lemma Rbar_ub_Finite (E : Rbar -> Prop) (l : R) :
  Rbar_is_upper_bound E (Finite l) -> 
    is_upper_bound (fun x => E (Finite x)) l.
Proof.
  intros H x Ex.
  apply Rbar_finite_le, H ; auto.
Qed.

Lemma Rbar_ub_m_infty (E : Rbar -> Prop) :
  Rbar_is_upper_bound E m_infty -> forall x, E x -> x = m_infty.
Proof.
  intros H x ;
  destruct x as [x | | ] ; intro Hx ;
  destruct (H _ Hx) as [H0|H0] ; simpl in H0 ; intuition.
Qed.

(** Decidability *)

Lemma Rbar_ub_dec (E : Rbar -> Prop) (Hp : ~ E p_infty) :
  {M : R | Rbar_is_upper_bound E (Finite M)} 
    + {(forall M, ~Rbar_is_upper_bound E (Finite M))}.
Proof.
  set (G n := fun x => x = 0 \/ (E (Finite x) /\ x <= INR n)).
  assert (Hne : (forall n, exists x, G n x)).
    intro n ; exists 0 ; left ; intuition.
  assert (Hub : (forall n, bound (G n))).
    intro n ; exists (INR n) ; intros x Hx ; destruct Hx as [Hx|Hx].
    rewrite Hx ; apply pos_INR.
    apply Hx.
  set (g n := projT1 (completeness _ (Hub n) (Hne n))).
  cut ({N : nat | forall n, (g n <= INR N)} + {(forall N, exists n, (INR N < g n))}).
  intro H ; destruct H as[(N, H) | H].
  left ; exists (INR N) ; intros x Hx ; destruct x as [x | | ] ; intuition.
  apply Rbar_finite_le ; case (Rlt_le_dec 0 x) ; intro Hx0.
  apply Rle_trans with (2 := H (S (nfloor1 _ Hx0))) ; clear H ;
  unfold nfloor1 ; case (nfloor1_ex _ _) ; simpl ; intros n Hn ;
  unfold g ; case (completeness _ _ _) ; intros l (Hl, Hl') ; apply Hl ;
  right ; intuition ; rewrite S_INR ; apply H0.
  apply Rle_trans with (1 := Hx0), pos_INR.
  left ; simpl ; auto.
  right ; intro M ; case (Rlt_le_dec 0 M) ; intro Hm0.
  case (H (S (nfloor1 M Hm0))) ; clear H ; intros n Hn.
  contradict Hn.
  unfold nfloor1 ; case (nfloor1_ex _ _) ; intros m Hm ; simpl projT1.
  rewrite S_INR ; apply Rle_not_lt, Rle_trans with (2 := proj2 Hm).
  unfold g ; case (completeness _ _ _) ; simpl ; intros x (Hx, Hx').
  apply Hx' ; intros x0 Hx0 ; case Hx0 ; clear Hx0 ; intros Hx0.
  rewrite Hx0 ; apply Rlt_le, Hm0.
  apply Rbar_finite_le, Hn, Hx0.
  case (H O) ; clear H ; intros n Hn ; contradict Hn.
  unfold g ; case (completeness _ _ _) ; simpl ; intros m (Hm, Hm').
  apply Rle_not_lt, Hm' ; intros x Hx ; case Hx ; clear Hx ; intro Hx.
  apply Req_le, Hx.
  apply Rle_trans with (2 := Hm0), Rbar_finite_le, Hn, Hx.
  cut ({n : nat | forall n0 : nat, g n0 <= INR n} +
  {(forall n : nat, ~ (forall n0 : nat, g n0 <= INR n))}).
  intro H ; destruct H as [(N, H)|H].
  left ; exists N ; auto.
  right ; intro N ; generalize (H N) ; clear H ; intro H.
  apply Markov_cor1.
  intro n ; apply Rlt_dec.
  contradict H ; intro n ; apply Rnot_lt_le, H.
  apply (Markov (fun N => forall n : nat, g n <= INR N)).
  intro N.
  cut ({n : nat | INR N < g n} + {(forall n : nat, ~ INR N < g n)}).
  intro H ; destruct H as [(n, H)|H].
  right ; contradict H ; apply Rle_not_lt, H.
  left ; intro n ; apply Rnot_lt_le, H.
  apply (Markov (fun n => INR N < g n)).
  intro n ; apply Rlt_dec.
Qed.

(** Order *)

Lemma Rbar_is_ub_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_upper_bound E2 l) -> (Rbar_is_upper_bound E1 l).
Proof.
  intros Hs Hl x Ex ; apply Hl, Hs ; auto.
Qed.

(** ** Lower bound *)

Definition Rbar_is_lower_bound (E : Rbar -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le l x.

(** Equivalence with upper bound *)

Lemma Rbar_ub_lb (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_upper_bound (fun x => E (Rbar_opp x)) (Rbar_opp l) 
    <-> Rbar_is_lower_bound E l.
Proof.
  split ; 
  destruct l as [l | | ] ; intros Hl x ;
  destruct x as [x | | ] ; simpl ; intro Hx.
(* -> *)
  apply Rbar_finite_le, Ropp_le_cancel, Rbar_finite_le, Hl ; simpl ; rewrite Ropp_involutive ; auto.
  left ; simpl ; auto.
  now case (Hl p_infty Hx).
  rewrite <-(Ropp_involutive x) in Hx ; now case (Hl (Finite (-x)) Hx).
  right ; auto.
  case (Hl p_infty Hx) ; simpl ; intuition.
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; simpl ; auto.
(* <- *)
  apply Rbar_finite_le, Ropp_le_cancel, Rbar_finite_le ; simpl ; rewrite Ropp_involutive ; apply Hl ; auto.
  now case (Hl m_infty Hx).
  left ; simpl ; auto.
  now case (Hl (Finite (-x)) Hx).
  case (Hl m_infty Hx) ; simpl ; intuition.
  right ; auto.
  left ; simpl ; auto.
  right ; auto.
  left ; simpl ; auto.
Qed.

Lemma Rbar_lb_ub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lower_bound (fun x => E (Rbar_opp x)) (Rbar_opp l) 
    <-> Rbar_is_upper_bound E l.
Proof.
  split ; 
  destruct l as [l | | ] ; intros Hl x ;
  destruct x as [x | | ] ; intro Hx.
(* -> *)
  apply Rbar_finite_le, Ropp_le_cancel, Rbar_finite_le, Hl ; simpl ; rewrite Ropp_involutive ; auto.
  now case (Hl m_infty Hx).
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; auto.
  left ; simpl ; auto.
  rewrite <-(Ropp_involutive x) in Hx ; now case (Hl (Finite (-x)) Hx).
  case (Hl m_infty Hx) ; simpl ; intuition.
  right ; auto.
(* <- *)
  apply Rbar_finite_le, Ropp_le_cancel, Rbar_finite_le ; simpl ; rewrite Ropp_involutive ; apply Hl ; auto.
  left ; simpl ; auto.
  now  case (Hl p_infty Hx).
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; auto.
  now case (Hl (Finite (-x)) Hx).
  right ; auto.
  case (Hl p_infty Hx) ; simpl ; intuition.
Qed.

Lemma Rbar_lb_le_ub (E : Rbar -> Prop) (l1 l2 : Rbar) : (exists x, E x) ->
  Rbar_is_lower_bound E l1 -> Rbar_is_upper_bound E l2 -> Rbar_le l1 l2.
Proof.
  intros (x, Hex) Hl Hu ;
  apply Rbar_le_trans with (y := x) ; [apply Hl | apply Hu] ; auto.
Qed.

Lemma Rbar_lb_eq_ub (E : Rbar -> Prop) (l : Rbar) : 
  Rbar_is_lower_bound E l -> Rbar_is_upper_bound E l -> forall x, E x -> x = l.
Proof.
  intros Hl Hu x Hx.
  apply Rbar_le_antisym ; [apply Hu | apply Hl] ; auto.
Qed.

(** Particular lower bounds *)

Lemma Rbar_lb_p_infty (E : Rbar -> Prop) :
  Rbar_is_lower_bound E p_infty -> (forall x, E x -> x = p_infty).
Proof.
  intros H x ;
  case x ; auto ; clear x ; [intros x| ] ; intros Hx.
  case (H _ Hx) ; simpl ; intuition.
  case (H _ Hx) ; simpl ; intuition.
Qed.

Lemma Rbar_lb_Finite (E : Rbar -> Prop) (l : R) :
  Rbar_is_lower_bound E (Finite l) -> is_upper_bound (fun x => E (Finite (- x))) (- l).
Proof.
  intros H x Ex.
  apply Ropp_le_cancel ; rewrite Ropp_involutive ;
  apply Rbar_finite_le, H ; auto.
Qed.

Lemma Rbar_lb_m_infty (E : Rbar -> Prop) :
  Rbar_is_lower_bound E m_infty.
Proof.
  intro x ; destruct x as [x | | ] ; intro Hx.
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; auto.
Qed.

(** Decidability *)

Lemma Rbar_lb_dec (E : Rbar -> Prop) (Hm : ~ E m_infty) :
  {M : R | Rbar_is_lower_bound E (Finite M)}
    + {(forall M, ~Rbar_is_lower_bound E (Finite M))}.
Proof.
  destruct (Rbar_ub_dec (fun x => E (Rbar_opp x)) Hm) as [(M, H)|H].
  left ; exists (-M).
  apply Rbar_ub_lb ; simpl ; rewrite (Ropp_involutive M) ; auto.
  right ; intro M ; generalize (H (-M)) ; clear H ; intro H ; contradict H ;
  apply (Rbar_ub_lb E (Finite M)) ; auto.
Qed.

(** Order *)

Lemma Rbar_is_lb_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_lower_bound E2 l) -> (Rbar_is_lower_bound E1 l).
Proof.
  intros Hs Hl x Ex ; apply Hl, Hs ; auto.
Qed.

(** * Least upper bound and Greatest lower bound *)

(** ** Least Upper Bound *)

Definition Rbar_is_lub (E : Rbar -> Prop) (l : Rbar) :=
  Rbar_is_upper_bound E l /\ 
    (forall b : Rbar, Rbar_is_upper_bound E b -> Rbar_le l b).

Lemma Rbar_ex_lub_ne (E : Rbar -> Prop) : {E p_infty} + {~ E p_infty} -> 
  (exists x, E (Finite x)) -> {l : Rbar | Rbar_is_lub E l}.
Proof.
  intros Hp Hex ; destruct Hp as [Hp|Hp].
(* E p_infty *)
  exists p_infty ; split.
  apply Rbar_ub_p_infty.
  intros b ; destruct b as [b | | ] ; intro ub.
  apply (ub _ Hp).
  right ; auto.
  apply (ub _ Hp).
(* ~ E p_infty *)
  case (Rbar_ub_dec _ Hp).
(* bound E *)
  intros (M, HM) ; case (completeness (fun x => E (Finite x))) ; intuition.
  exists M ; apply Rbar_ub_Finite, HM.
  rename x into l ; destruct i as (ub,lub).
  exists (Finite l) ; split.
  intro x ; case x ; clear x ; [intro x | | ] ; intro Hx.
  apply Rbar_finite_le, ub ; auto.
  generalize (Hp Hx) ; intuition.
  left ; simpl ; auto.
  intro b ; destruct b as [b | | ] ; intro Hb.
  apply Rbar_finite_le, lub, Rbar_ub_Finite, Hb.
  left ; simpl ; auto.
  generalize (Rbar_ub_m_infty _ Hb) ; clear Hb ; intro Hb.
  case Hex ; intros x Hx.
  discriminate (Hb _ Hx).
(* ~ bound E *)
  intro H ; exists p_infty ; split.
  apply Rbar_ub_p_infty.
  intro b ; destruct b as [b | | ] ; intro Hb.
  contradict Hb ; auto.
  right ; auto.
  case Hex ; intros x Hx.
  generalize (Hb _ Hx) ; clear Hb Hx ; intro Hb.
  contradict Hb ; apply Rbar_lt_not_le ; simpl ; auto.
Qed.

Definition Rbar_lub_ne (E : Rbar -> Prop) (Hp : {E p_infty} + {~ E p_infty}) 
  (Hex : exists x, E (Finite x)) := projT1 (Rbar_ex_lub_ne E Hp Hex).

(** Order *)

Lemma Rbar_is_lub_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2)
  -> Rbar_le l1 l2.
Proof.
  intros Hs (_,H1) (H2, _).
  apply H1 ; intros x Hx ; apply H2, Hs, Hx.
Qed.

Lemma Rbar_is_lub_rw (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2)
  -> l1 = l2.
Proof.
  intros Hs H1 H2 ; apply Rbar_le_antisym ; 
  [apply (Rbar_is_lub_subset E1 E2) | apply (Rbar_is_lub_subset E2 E1) ] ; auto ; intros x H ; 
  apply Hs ; auto.
Qed.

Lemma Rbar_is_lub_eq (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l) -> (Rbar_is_lub E2 l).
Proof.
  intros Heq (H1,H2) ; split.
  apply (Rbar_is_ub_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
  intros b Hb ; apply H2 ; apply (Rbar_is_ub_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
Qed.

Lemma Rbar_lub_subset (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E1 x -> E2 x) -> Rbar_le (Rbar_lub_ne E1 Hp1 Hex1) (Rbar_lub_ne E2 Hp2 Hex2).
Proof.
  intros Hs ; unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne E1 _ _) ; intros l1 Hl1 ;
  case (Rbar_ex_lub_ne E2 _ _) ; simpl ; intros l2 Hl2 ; apply (Rbar_is_lub_subset E1 E2) ; auto.
Qed.

Lemma Rbar_lub_rw (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E1 x <-> E2 x) -> (Rbar_lub_ne E1 Hp1 Hex1) = (Rbar_lub_ne E2 Hp2 Hex2).
Proof.
  intro Hs ; apply Rbar_le_antisym ; apply Rbar_lub_subset ; intros x H ; apply Hs ; auto.
Qed.

(** ** Greatest Lower Bound *)

Definition Rbar_is_glb (E : Rbar -> Prop) (l : Rbar) :=
  Rbar_is_lower_bound E l /\ 
    (forall b : Rbar, Rbar_is_lower_bound E b -> Rbar_le b l).

(** Equivalents between LUB and GLB *)

Lemma Rbar_lub_glb (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lub (fun x => E (Rbar_opp x)) (Rbar_opp l) 
    <-> Rbar_is_glb E l.
Proof.
  split ; [intros (ub, lub) | intros (lb, glb)] ; split.
  apply Rbar_ub_lb ; auto.
  intros b Hb ; generalize (lub _ (proj2 (Rbar_ub_lb _ _) Hb)) ; apply Rbar_opp_le.
  apply Rbar_lb_ub ; intros x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply lb.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply glb, Rbar_ub_lb ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

Lemma Rbar_glb_lub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_glb (fun x => E (Rbar_opp x)) (Rbar_opp l) 
    <-> Rbar_is_lub E l.
Proof.
  split ; [ intros (lb, glb) | intros (ub, lub)] ; split.
  apply Rbar_lb_ub ; auto.
  intros b Hb ; generalize (glb _ (proj2 (Rbar_lb_ub _ _) Hb)) ; apply Rbar_opp_le.
  apply Rbar_ub_lb ; intro x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply ub.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply lub, Rbar_lb_ub ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

(** The Rbar_glb function *)

Lemma Rbar_ex_glb_ne (E : Rbar -> Prop) : {E m_infty} + {~ E m_infty} -> 
  (exists x, E (Finite x)) -> {l : Rbar | Rbar_is_glb E l}.
Proof.
  intros Hm Hex ;
  case (Rbar_ex_lub_ne (fun x => E (Rbar_opp x))) ; auto.
  case Hex ; clear Hex ; intros x Hx ; exists (-x) ; simpl ; rewrite Ropp_involutive ; auto.
  intros l Hl ; exists (Rbar_opp l) ;
  apply Rbar_lub_glb ; rewrite Rbar_opp_involutive ; auto.
Qed.

Definition Rbar_glb_ne (E : Rbar -> Prop) (Hp : {E m_infty} + {~ E m_infty}) 
  (Hex : exists x, E (Finite x)) := projT1 (Rbar_ex_glb_ne E Hp Hex).

(** Order *)

Lemma Rbar_is_glb_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E2 x -> E1 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2)
  -> Rbar_le l1 l2.
Proof.
  intros Hs (H1, _) (_, H2).
  apply H2 ; intros x Hx ; apply H1, Hs, Hx.
Qed.

Lemma Rbar_is_glb_rw (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2)
  -> l1 = l2.
Proof.
  intros Hs H1 H2 ; apply Rbar_le_antisym ; 
  [apply (Rbar_is_glb_subset E1 E2) | apply (Rbar_is_glb_subset E2 E1) ] ; auto ; intros x H ; 
  apply Hs ; auto.
Qed.

Lemma Rbar_is_glb_eq (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l) -> (Rbar_is_glb E2 l).
Proof.
  intros Heq (H1, H2) ; split.
  apply (Rbar_is_lb_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
  intros b Hb ; apply H2 ; apply (Rbar_is_lb_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
Qed.

Lemma Rbar_glb_subset (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E2 x -> E1 x) -> Rbar_le (Rbar_glb_ne E1 Hp1 Hex1) (Rbar_glb_ne E2 Hp2 Hex2).
Proof.
  intro Hs ; unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne E1 _ _) ; intros l1 Hl1 ;
  case (Rbar_ex_glb_ne E2 _ _) ; simpl ; intros l2 Hl2 ; apply (Rbar_is_glb_subset E1 E2) ; auto.
Qed.

Lemma Rbar_glb_rw (E1 E2 : Rbar -> Prop) Hp1 Hp2 Hex1 Hex2 :
  (forall x, E1 x <-> E2 x) -> (Rbar_glb_ne E1 Hp1 Hex1) = (Rbar_glb_ne E2 Hp2 Hex2).
Proof.
  intros Hs ; apply Rbar_le_antisym ; apply Rbar_glb_subset ; intros x H ; apply Hs ; auto.
Qed.

(** Other lemmas about lub and glb *)

Lemma Rbar_glb_le_lub (E : Rbar -> Prop) Hp Hm Hex1 Hex2 :
  Rbar_le (Rbar_glb_ne E Hm Hex1) (Rbar_lub_ne E Hp Hex2).
Proof.
  case Hex1 ; intros x Hex.
  apply Rbar_le_trans with (y := Finite x).
  unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne _ _ _) ; simpl ; intros g (Hg, _) ; apply Hg ; auto.
  unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne _ _ _) ; simpl ; intros l (Hl, _) ; apply Hl ; auto.
Qed.

Lemma Rbar_opp_glb_lub (E : Rbar -> Prop) Hp Hm Hex1 Hex2 :
  Rbar_glb_ne (fun x => E (Rbar_opp x)) Hm Hex1 = Rbar_opp (Rbar_lub_ne E Hp Hex2).
Proof.
  unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne _ _ _) ; simpl ; intros g [Hg Hg'] ;
  unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne _ _ _) ; simpl ; intros l [Hl Hl'] ;
  apply Rbar_le_antisym.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hl', Rbar_lb_ub ; 
  rewrite Rbar_opp_involutive ; auto.
  apply Hg', Rbar_lb_ub ; auto.
Qed.

Lemma Rbar_opp_lub_glb (E : Rbar -> Prop) Hp Hm Hex1 Hex2 :
  Rbar_lub_ne (fun x => E (Rbar_opp x)) Hp Hex1 = Rbar_opp (Rbar_glb_ne E Hm Hex2).
Proof.
  unfold Rbar_glb_ne ; case (Rbar_ex_glb_ne _ _ _) ; simpl ; intros g (Hg, Hg') ;
  unfold Rbar_lub_ne ; case (Rbar_ex_lub_ne _ _ _) ; simpl ; intros l [Hl Hl'] ;
  apply Rbar_le_antisym.
  apply Hl', Rbar_lb_ub ; rewrite Rbar_opp_involutive ;
  apply (Rbar_is_lb_subset _ E) ; auto ; intros x ; rewrite Rbar_opp_involutive ; auto.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hg', Rbar_ub_lb ; 
  rewrite Rbar_opp_involutive ; auto.
Qed.
