Require Export Reals Decidable Rbar_theory.
Require Import ssreflect.
Open Scope R_scope.

(** * Upper bound *)
(** ** More in R *)

Lemma Rbar_ub_R_ub (E : R -> Prop) (l : R) :
  Rbar_is_upper_bound (fun x => exists y, x = Finite y /\ E y) (Finite l) 
  <-> is_upper_bound E l.
Proof.
  split => [H x Hx | H _ [x [-> Hx]]] ; apply Rbar_finite_le, H => // ;
  by exists x.
Qed.

Lemma u_bound_dec (E : R -> Prop) :
  {l : R | is_upper_bound E l} + {(forall l, ~ is_upper_bound E l)}.
Proof.
  case: (Rbar_ub_dec (fun x => exists y, x = Finite y /\ E y)).
  move => [y [Hy _]] //.
  case => M Hub ; left ; exists M ; by apply Rbar_ub_R_ub.
  move => Hub ; right => M ; move : (Hub M) => {Hub} Hub ; contradict Hub ;
  by apply Rbar_ub_R_ub.
Qed.

(** ** in Rbar *)

Definition is_ub_Rbar (E : R -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le (Finite x) l.
Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) :=
  is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).

Lemma is_ub_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_ub_Rbar E l <-> Rbar_is_upper_bound (fun x => exists y, x = Finite y /\ E y) l.
Proof.
  split => [H _ [x [-> Hx]] | H x Hx] ; apply H => // ;
  by exists x.
Qed.
Lemma is_lub_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_lub_Rbar E l <-> Rbar_is_lub (fun x => exists y, x = Finite y /\ E y) l.
Proof.
  split => [[Hub Hlub]|[Hub Hlub]].
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
Qed.

Lemma ex_lub_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) : 
  {l : Rbar | is_lub_Rbar E l}.
Proof.
  case: (Rbar_ex_lub_ne (fun x => exists y, x = Finite y /\ E y)) => [ | | l Hl].
  right ; case => y [H H0] //.
  case: Hex => x Hx ; exists x ; by exists x.
  exists l ; by apply is_lub_Rbar_correct.
Qed.

Definition Lub_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) := projT1 (ex_lub_Rbar_ne E Hex).

(** * Lower bound *)
(** ** in R *)

Definition is_lower_bound (E : R -> Prop) (l : R) :=
  forall x, E x -> l <= x.
Lemma Rbar_lb_R_lb (E : R -> Prop) (l : R) :
  Rbar_is_lower_bound (fun x => exists y, x = Finite y /\ E y) (Finite l)
  <-> is_lower_bound E l.
Proof.
  split => [H x Hx | H _ [x [-> Hx]]] ; apply Rbar_finite_le, H => // ;
  by exists x.
Qed.

Lemma l_bound_dec (E : R -> Prop) :
  {l : R | is_lower_bound E l} + 
    {(forall l, ~ is_lower_bound E l)}.
Proof.
  case: (Rbar_lb_dec (fun x => exists y, x = Finite y /\ E y)).
  move => [y [Hy _]] //.
  case => M Hub ; left ; exists M ; by apply Rbar_lb_R_lb.
  move => Hub ; right => M ; move : (Hub M) => {Hub} Hub ; contradict Hub ;
  by apply Rbar_lb_R_lb.
Qed.

(** ** in Rbar *)

Definition is_lb_Rbar (E : R -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le l (Finite x).
Definition is_glb_Rbar (E : R -> Prop) (l : Rbar) :=
  is_lb_Rbar E l /\ (forall b, is_lb_Rbar E b -> Rbar_le b l).

Lemma is_lb_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_lb_Rbar E l <-> Rbar_is_lower_bound (fun x => exists y, x = Finite y /\ E y) l.
Proof.
  split => [H _ [x [-> Hx]] | H x Hx] ; apply H => // ;
  by exists x.
Qed.
Lemma is_glb_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_glb_Rbar E l <-> Rbar_is_glb (fun x => exists y, x = Finite y /\ E y) l.
Proof.
  split => [[Hub Hlub]|[Hub Hlub]].
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
Qed.

Lemma ex_glb_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) :
  {l : Rbar | is_glb_Rbar E l}.
Proof.
  case: (Rbar_ex_glb_ne (fun x => exists y, x = Finite y /\ E y)) => [ | | l Hl].
  right ; case => y [H H0] //.
  case: Hex => x Hx ; exists x ; by exists x.
  exists l ; by apply is_glb_Rbar_correct.
Qed.

Definition Glb_Rbar_ne (E : R -> Prop) (Hex : exists x, E x) := projT1 (ex_glb_Rbar_ne E Hex).

(** * Order on upper and lower bound *)
(** ** with upper bound *)
Lemma is_ub_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_ub_Rbar E1 l -> is_ub_Rbar E2 l.
Proof.
  move => H ub1 x Hx.
  apply: ub1 ; by apply: H.
Qed.
Lemma is_lub_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_lub_Rbar E1 l1 -> is_lub_Rbar E2 l2
    -> Rbar_le l2 l1.
Proof.
  move => H [ub1 _] [_ lub2].
  apply: lub2 ; by apply (is_ub_Rbar_subset E1), ub1.
Qed.
Lemma is_lub_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x <-> E1 x) -> is_lub_Rbar E1 l -> is_lub_Rbar E2 l.
Proof.
  move => H [ub1 lub1] ; split.
  apply (is_ub_Rbar_subset E1) ; [apply H | apply ub1].
  move => b Hb ; apply: lub1 ; apply (is_ub_Rbar_subset E2) ; [apply H | apply Hb].
Qed.

Lemma Lub_Rbar_ne_eqset (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Lub_Rbar_ne E1 pr1 = Lub_Rbar_ne E2 pr2.
Proof.
  move => H ; rewrite /Lub_Rbar_ne ;
  case: (ex_lub_Rbar_ne E1 pr1) => {pr1} l1 H1 ;
  case: (ex_lub_Rbar_ne E2 pr2) => {pr2} l2 H2 /=.
  apply Rbar_le_antisym ; 
  [ apply (is_lub_Rbar_subset E2 E1) 
  | apply (is_lub_Rbar_subset E1 E2)] => //= x ; by apply H.
Qed.

(** ** with lower bound *)

Lemma is_lb_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_lb_Rbar E1 l -> is_lb_Rbar E2 l.
Proof.
  move => H ub1 x Hx.
  apply: ub1 ; by apply: H.
Qed.
Lemma is_glb_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_glb_Rbar E1 l1 -> is_glb_Rbar E2 l2
    -> Rbar_le l1 l2.
Proof.
  move => H [ub1 _] [_ lub2].
  apply: lub2 ; by apply (is_lb_Rbar_subset E1), ub1.
Qed.
Lemma is_glb_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x <-> E1 x) -> is_glb_Rbar E1 l -> is_glb_Rbar E2 l.
Proof.
  move => H [ub1 lub1] ; split.
  apply (is_lb_Rbar_subset E1) ; [apply H | apply ub1].
  move => b Hb ; apply: lub1 ; apply (is_lb_Rbar_subset E2) ; [apply H | apply Hb].
Qed.

Lemma Glb_Rbar_ne_eqset (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Glb_Rbar_ne E1 pr1 = Glb_Rbar_ne E2 pr2.
Proof.
  move => H ; rewrite /Glb_Rbar_ne ;
  case: (ex_glb_Rbar_ne E1 pr1) => {pr1} l1 H1 ;
  case: (ex_glb_Rbar_ne E2 pr2) => {pr2} l2 H2 /=.
  apply Rbar_le_antisym ; 
  [ apply (is_glb_Rbar_subset E1 E2) 
  | apply (is_glb_Rbar_subset E2 E1)] => //= x ; by apply H.
Qed.

(** * Decidability of empty *)

Lemma not_empty_0 (E : R -> Prop) :
  let F := fun x => x = 0 \/ E x in exists x, F x.
Proof.
  intros ; exists 0 ; left ; reflexivity.
Qed.

Lemma not_empty_1 (E : R -> Prop) :
  let F := fun x => x = 1 \/ E x in exists x, F x.
Proof.
  intros ; exists 1 ; left ; reflexivity.
Qed.

Definition Empty (E : R -> Prop) :=
  Lub_Rbar_ne _ (not_empty_0 E) = Glb_Rbar_ne _ (not_empty_0 E)
  /\ Lub_Rbar_ne _ (not_empty_1 E) = Glb_Rbar_ne _ (not_empty_1 E).

Lemma Empty_correct_1 (E : R -> Prop) :
  Empty E -> forall x, ~ E x.
Proof.
  case => E0 E1 x Ex.
  rewrite /Lub_Rbar_ne /Glb_Rbar_ne in E0 ;
  case : (ex_lub_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) E0 => /= s0 Hs0 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) => i0 Hi0 /= E0.
  have : (x = 0) ; last move => {s0 Hs0 i0 Hi0 E0}.
  apply: Rle_antisym ; apply (Rbar_finite_le _ _).
  apply Rbar_le_trans with (y := s0).
  apply Hs0 ; by right.
  rewrite E0 ; apply Hi0 ; by left.
  apply Rbar_le_trans with (y := s0).
  apply Hs0 ; by left.
  rewrite E0 ; apply Hi0 ; by right.
  rewrite /Lub_Rbar_ne /Glb_Rbar_ne in E1 ;
  case : (ex_lub_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) E1 => /= s1 Hs1 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) => i1 Hi1 /= E1.
  have : (x = 1) ; last move => {s1 Hs1 i1 Hi1 E1}.
  apply: Rle_antisym ; apply (Rbar_finite_le _ _).
  apply Rbar_le_trans with (y := s1).
  apply Hs1 ; by right.
  rewrite E1 ; apply Hi1 ; by left.
  apply Rbar_le_trans with (y := s1).
  apply Hs1 ; by left.
  rewrite E1 ; apply Hi1 ; by right.
  move => -> ; apply R1_neq_R0.
Qed.
Lemma Empty_correct_2 (E : R -> Prop) :
  (forall x, ~ E x) -> Empty E.
Proof.
  move => H ; split ;
  rewrite /Glb_Rbar_ne /Lub_Rbar_ne ; 
  [ case : (ex_lub_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) => s0 Hs0 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 0 \/ E x) (not_empty_0 E)) => i0 Hi0 /= 
  | case : (ex_lub_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) => s1 Hs1 ;
  case : (ex_glb_Rbar_ne (fun x : R => x = 1 \/ E x) (not_empty_1 E)) => i1 Hi1 /=].
  have : (i0 = Finite 0) ; last move => -> ; 
  apply: Rbar_le_antisym.
  apply Hi0 ; by left.
  apply Hi0 => y ; case => H0.
  rewrite H0 ; by right.
  contradict H0 ; apply H.
  apply Hs0 => y ; case => H0.
  rewrite H0 ; by right.
  contradict H0 ; apply H.
  apply Hs0 ; by left.
  have : (i1 = Finite 1) ; last move => -> ; 
  apply: Rbar_le_antisym.
  apply Hi1 ; by left.
  apply Hi1 => y ; case => H1.
  rewrite H1 ; by right.
  contradict H1 ; apply H.
  apply Hs1 => y ; case => H1.
  rewrite H1 ; by right.
  contradict H1 ; apply H.
  apply Hs1 ; by left.
Qed.

Lemma Empty_dec (E : R -> Prop) : 
  {~Empty E}+{Empty E}.
Proof.
  case: (Rbar_eq_dec (Lub_Rbar_ne _ (not_empty_0 E)) (Glb_Rbar_ne _ (not_empty_0 E))) => H0 ; 
    [ | left].
  case: (Rbar_eq_dec (Lub_Rbar_ne _ (not_empty_1 E)) (Glb_Rbar_ne _ (not_empty_1 E))) => H1 ; 
    [by right | left].
  contradict H1 ; apply H1.
  contradict H0 ; apply H0.
Qed.
Lemma not_Empty_dec (E : R -> Prop) : (decidable (exists x, E x)) ->
  {(exists x, E x)} + {(forall x, ~ E x)}.
Proof.
  move => He ;
  case: (Empty_dec E) => Hx ;
  [left|right].
  case: He => // He.
  contradict Hx ;
  apply: Empty_correct_2 => x ; contradict He ; by exists x.
  by apply: Empty_correct_1.
Qed.

(** * More general lub and glb *)

Lemma Lub_Rbar_ex (E : R -> Prop) (pr : decidable (exists x, E x)) :
  {l : Rbar | is_lub_Rbar E l}.
Proof.
  intros.
  destruct (not_Empty_dec _ pr).
  destruct (ex_lub_Rbar_ne _ e) as (l,lub).
  exists l ; apply lub.
  exists m_infty ; split.
  intros x Ex ; contradict Ex ; apply n.
  intros ; destruct b ; simpl.
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; reflexivity.
Qed.
Definition Lub_Rbar (E : R -> Prop) (pr : decidable (exists x, E x)) :=
  projT1 (Lub_Rbar_ex E pr).

Lemma Lub_Rbar_eq_seq (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Lub_Rbar E1 pr1 = Lub_Rbar E2 pr2.
Proof.
  move => H ; rewrite /Lub_Rbar ;
  case: (Lub_Rbar_ex E1 pr1) => {pr1} l1 H1 ;
  case: (Lub_Rbar_ex E2 pr2) => {pr2} l2 H2 /=.
  apply Rbar_le_antisym ; 
  [ apply (is_lub_Rbar_subset E2 E1) 
  | apply (is_lub_Rbar_subset E1 E2)] => //= x ; by apply H.
Qed.

Lemma Glb_Rbar_ex (E : R -> Prop) (pr : decidable (exists x, E x)) :
  {l : Rbar | is_glb_Rbar E l}.
Proof.
  intros.
  destruct (not_Empty_dec _ pr).
  destruct (ex_glb_Rbar_ne _ e) as (l,lub).
  exists l ; apply lub.
  exists p_infty ; split.
  intros x Ex ; contradict Ex ; apply n.
  intros ; destruct b ; simpl.
  left ; simpl ; auto.
  right ; reflexivity.
  left ; simpl ; auto.
Qed.
Definition Glb_Rbar (E : R -> Prop) (pr : decidable (exists x, E x)) :=
  projT1 (Glb_Rbar_ex E pr).

Lemma Glb_Rbar_eq_seq (E1 E2 : R -> Prop) pr1 pr2 :
  (forall x, E1 x <-> E2 x) -> Glb_Rbar E1 pr1 = Glb_Rbar E2 pr2.
Proof.
  move => H ; rewrite /Glb_Rbar ;
  case: (Glb_Rbar_ex E1 pr1) => {pr1} l1 H1 ;
  case: (Glb_Rbar_ex E2 pr2) => {pr2} l2 H2 /=.
  apply Rbar_le_antisym ; 
  [ apply (is_glb_Rbar_subset E1 E2) 
  | apply (is_glb_Rbar_subset E2 E1)] => //= x ; by apply H.
Qed.