Require Import Reals ssreflect.
Require Import Rcomplements.
Require Import Rbar Lub Markov Locally.

Open Scope R_scope.

(** * Sup and Inf of sequences in Rbar *)

(** ** Definitions *)

Definition is_sup_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), (forall n, Rbar_lt (u n) (l+eps))
                                       /\ (exists n, Rbar_lt (l-eps) (u n))
    | p_infty => forall M : R, exists n, Rbar_lt M (u n)
    | m_infty => forall M : R, forall n, Rbar_lt (u n) M
  end.
Definition is_inf_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), (forall n, Rbar_lt (Finite (l-eps)) (u n))
                                       /\ (exists n, Rbar_lt (u n) (Finite (l+eps)))
    | p_infty => forall M : R, forall n, Rbar_lt (Finite M) (u n)
    | m_infty => forall M : R, exists n, Rbar_lt (u n) (Finite M)
  end.

(** Equivalent forms *)

Lemma is_inf_opp_sup_seq (u : nat -> Rbar) (l : Rbar) :
  is_inf_seq (fun n => Rbar_opp (u n)) (Rbar_opp l) 
  <-> is_sup_seq u l.
Proof.
  destruct l as [l | | ] ; split ; intros Hl.
(* l = Finite l *)
  intro eps ; case (Hl eps) ; clear Hl ; intros lb (n, glb) ; split.
  intro n0 ; apply Rbar_opp_lt ; simpl ; rewrite (Ropp_plus_distr l eps) ; apply lb.
  exists n ; apply Rbar_opp_lt ; assert (Rw : -(l-eps) = -l+eps).
  ring.
  simpl ; rewrite Rw ; clear Rw ; auto.
  intro eps ; case (Hl eps) ; clear Hl ; intros ub (n, lub) ; split.
  intros n0 ; unfold Rminus ; rewrite <-(Ropp_plus_distr l eps) ; 
  apply (Rbar_opp_lt (Finite (l+eps)) (u n0)) ; simpl ; apply ub.
  exists n ; assert (Rw : -(l-eps) = -l+eps).
  ring.
  simpl ; rewrite <-Rw ; apply (Rbar_opp_lt (u n) (Finite (l-eps))) ; auto.
(* l = p_infty *)
  intro M ; case (Hl (-M)) ; clear Hl ; intros n Hl ; exists n ; apply Rbar_opp_lt ; auto.
  intro M ; case (Hl (-M)) ; clear Hl ; intros n Hl ; exists n ; apply Rbar_opp_lt ;
  rewrite Rbar_opp_involutive ; auto.
(* l = m_infty *)
  intros M n ; apply Rbar_opp_lt, Hl.
  intros M n ; apply Rbar_opp_lt ; rewrite Rbar_opp_involutive ; apply Hl.
Qed.
Lemma is_sup_opp_inf_seq (u : nat -> Rbar) (l : Rbar) :
  is_sup_seq (fun n => Rbar_opp (u n)) (Rbar_opp l) 
  <-> is_inf_seq u l.
Proof.
  case: l => [l | | ] ; split => Hl.
(* l = Finite l *)
  move => eps ; case: (Hl eps) => {Hl} [lb [n lub]] ; split.
  move => n0 ; apply Rbar_opp_lt ; have : (-(l-eps) = -l+eps) ; first by ring.
  by move => /= ->.
  exists n ; apply Rbar_opp_lt ; rewrite /= (Ropp_plus_distr l eps) ; apply lub.
  move => eps ; case: (Hl eps) => {Hl} [ub [n lub]] ; split.
  move => n0 ; have : (-(l-eps) = (-l+eps)) ; first by ring.
  move => /= <- ; by apply (Rbar_opp_lt (u n0) (Finite (l-eps))).
  exists n ; rewrite /Rminus -(Ropp_plus_distr l eps) ; 
  by apply (Rbar_opp_lt (Finite (l+eps)) (u n)).
(* l = p_infty *)
  move => M n ; apply Rbar_opp_lt, Hl.
  move => M n ; apply Rbar_opp_lt ; rewrite Rbar_opp_involutive ; apply Hl.
(* l = m_infty *)
  move => M ; case: (Hl (-M)) => {Hl} n Hl ; exists n ; by apply Rbar_opp_lt.
  move => M ; case: (Hl (-M)) => {Hl} n Hl ; exists n ; apply Rbar_opp_lt ;
  by rewrite Rbar_opp_involutive.
Qed.

Lemma is_sup_seq_lub (u : nat -> Rbar) (l : Rbar) :
  is_sup_seq u l -> Rbar_is_lub (fun x => exists n, x = u n) l.
Proof.
  destruct l as [l | | ] ; intro Hl ; split.
(* l = Finite l *)
  intro x ; destruct x as [x | | ] ; simpl ; intros (n, Hn).
  apply Rbar_finite_le, le_epsilon ; intros e He ; set (eps := mkposreal e He) ; 
  apply Rbar_finite_le ; rewrite Hn ; apply Rbar_lt_le, (Hl eps).
  generalize (proj1 (Hl (mkposreal _ Rlt_0_1)) n) ; clear Hl ; simpl ; intros Hl ; rewrite <-Hn in Hl ; 
  case Hl ; auto.
  left ; simpl ; auto.
  intros b ; destruct b as [b | | ] ; intros Hb ; apply Rbar_not_lt_le ; auto ; intros He.
  set (eps := mkposreal _ (Rlt_Rminus _ _ He)) ; case (proj2 (Hl eps)) ; clear Hl ; intros n.
  apply Rbar_le_not_lt ; assert (l - eps = b) .
  simpl ; ring.
  rewrite H ; clear H ; apply Hb ; exists n ; auto.
  generalize (Rbar_ub_m_infty _ Hb) ; clear Hb ; intros Hb.
  case (proj2 (Hl (mkposreal _ Rlt_0_1))) ; clear Hl ; simpl ; intros n Hl.
  assert (H : (exists n0 : nat, u n = u n0)).
  exists n ; auto.
  generalize (Hb (u n) H) Hl ; clear Hb ; now case (u n).
(* l = p_infty *)
  apply Rbar_ub_p_infty.
  intro b ; destruct b as [b | | ] ; simpl ; intro Hb.
  case (Hl b) ; clear Hl ; intros n Hl.
  contradict Hl ; apply Rbar_le_not_lt, Hb ; exists n ; auto.
  right ; auto.
  generalize (Rbar_ub_m_infty _ Hb) ; clear Hb ; intro Hb.
  case (Hl 0) ; clear Hl; intros n Hl.
  assert (H : (exists n0 : nat, u n = u n0)).
  exists n ; auto.
  generalize (Hb (u n) H) Hl ; clear Hl ; now case (u n).
(* l = m_infty *)
  intro x ; destruct x as [x | | ] ; intros (n, Hx).
  generalize (Hl x n) ; clear Hl ; intro Hl ; rewrite <-Hx in Hl ; apply Rbar_finite_lt, Rlt_irrefl in Hl ; intuition.
  generalize (Hl 0 n) ; rewrite <-Hx ; intuition.
  simpl in H ; intuition.
  right ; auto.
  intros b ; destruct b as [b | | ] ; simpl ; intro Hb.
  left ; simpl ; auto.
  left ; simpl ; auto.
  right ; auto.
Qed.

Lemma Rbar_is_lub_sup_seq (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_lub (fun x => exists n, x = u n) l -> is_sup_seq u l.
Proof.
  destruct l as [l | | ] ; intros (ub, lub).
(* l = Finite l *)
  intro eps ; split.
  intro n ; apply Rbar_le_lt_trans with (y := Finite l).
  apply ub ; exists n ; auto.
  pattern l at 1 ; rewrite <-(Rplus_0_r l) ; apply Rplus_lt_compat_l, eps.
  apply Markov_cor1.
  intro n ; apply Rbar_lt_dec.
  intro H.
  assert (H0 : (Rbar_is_upper_bound (fun x : Rbar => exists n : nat, x = u n) (Finite (l - eps)))).
  intros x (n,Hn) ; rewrite Hn ; clear Hn ; apply Rbar_not_lt_le, H.
  generalize (lub _ H0) ; clear lub ; apply Rbar_lt_not_le ; pattern l at 2 ; 
  rewrite <-(Rplus_0_r l) ; 
  apply Rplus_lt_compat_l, Ropp_lt_gt_0_contravar, eps.
(* l = p_infty *)
  intro M ; apply Markov_cor1.
  intro n ; apply Rbar_lt_dec.
  intro H.
  assert (H0 : Rbar_is_upper_bound (fun x : Rbar => exists n : nat, x = u n) (Finite M)).
  intros x (n,Hn) ; rewrite Hn ; clear Hn ; apply Rbar_not_lt_le, H.
  generalize (lub _ H0) ; clear lub ; apply Rbar_lt_not_le ; simpl ; auto.
(* l = m_infty *)
  intros M n.
  apply Rbar_le_lt_trans with (y := m_infty) ; simpl ; auto.
  apply ub ; exists n ; auto.
Qed.

Lemma is_inf_seq_glb (u : nat -> Rbar) (l : Rbar) :
  is_inf_seq u l -> Rbar_is_glb (fun x => exists n, x = u n) l.
Proof.
  move => H ;
  apply Rbar_lub_glb ;
  apply (Rbar_is_lub_eq (fun x : Rbar => exists n : nat, x = Rbar_opp (u n))).
  move => x ; split ; case => n Hn ; exists n.
  by rewrite Hn Rbar_opp_involutive.
  by rewrite -Hn Rbar_opp_involutive.
  apply (is_sup_seq_lub (fun n => Rbar_opp (u n)) (Rbar_opp l)) ;
  by apply is_sup_opp_inf_seq.
Qed.
Lemma Rbar_is_glb_inf_seq (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_glb (fun x => exists n, x = u n) l -> is_inf_seq u l.
Proof.
  move => H ;
  apply is_sup_opp_inf_seq ;
  apply Rbar_is_lub_sup_seq ;
  apply Rbar_glb_lub.
  rewrite Rbar_opp_involutive ;
  apply (Rbar_is_glb_eq (fun x : Rbar => exists n : nat, x = u n)) => // x ;
  split ; case => n Hx ; exists n ; by apply Rbar_opp_eq.
Qed.

(** Extentionality *)

Lemma is_sup_seq_ext (u v : nat -> Rbar) (l : Rbar) :
  (forall n, u n = v n)
  -> is_sup_seq u l -> is_sup_seq v l.
Proof.
  case: l => [l | | ] Heq ; rewrite /is_sup_seq => Hu.
(* l \in R *)
  move => eps ; case: (Hu eps) => {Hu} Hu1 Hu2 ; split.
  move => n ; by rewrite -Heq.
  case: Hu2 => n Hu2 ; exists n ; by rewrite -Heq.
(* l = p_infty *)
  move => M ; case: (Hu M) => {Hu} n Hu ; exists n ; by rewrite -Heq.
(* l = m_infty *)
  move => M n ; by rewrite -Heq.
Qed.
Lemma is_inf_seq_ext (u v : nat -> Rbar) (l : Rbar) :
  (forall n, u n = v n)
  -> is_inf_seq u l -> is_inf_seq v l.
Proof.
  case: l => [l | | ] Heq ; rewrite /is_inf_seq => Hu.
(* l \in R *)
  move => eps ; case: (Hu eps) => {Hu} Hu1 Hu2 ; split.
  move => n ; by rewrite -Heq.
  case: Hu2 => n Hu2 ; exists n ; by rewrite -Heq.
(* l = p_infty *)
  move => M n ; by rewrite -Heq.
(* l = m_infty *)
  move => M ; case: (Hu M) => {Hu} n Hu ; exists n ; by rewrite -Heq.
Qed.

(** Existence *)

Lemma ex_sup_seq (u : nat -> Rbar) : {l : Rbar | is_sup_seq u l}.
Proof.
  case (Markov (fun n => exists x, Finite x = u n)).
  intro n ; destruct (u n) as [x | | ].
  left ; exists x ; auto.
  right ; now intros (x,Hx).
  right ; now intros (x,Hx).
  intro H ; case (Rbar_ex_lub_ne (fun x => exists n, x = u n)).
  case (Markov (fun n => p_infty = u n)).
  intro n0 ; destruct (u n0) as [r | | ].
  now right.
  left ; auto.
  now right.
  intros (n0,Hn0) ; left ; exists n0 ; auto.
  intros H0 ; right ; intros (n0, Hn0) ; generalize Hn0 ; apply H0.
  destruct H as (n, (x, Hnx)).
  exists x ; exists n ; auto.
  intros l Hl ; exists l ; apply Rbar_is_lub_sup_seq ; auto.
  intro H.
  case (Markov (fun n => p_infty = u n)).
  intros n ; apply Rbar_eq_dec.
  intros (n, Hn) ; exists p_infty ; intro M ; exists n ; rewrite <-Hn ; simpl ; auto.
  intro H0 ; exists m_infty.
  assert (H1 : forall n, u n = m_infty).
  intro n ; generalize (H n) (H0 n) ; case (u n) ; intuition ;
  contradict H1 ; exists r ; auto.
  intros M n ; rewrite H1 ; simpl ; auto.
Qed.

Lemma ex_inf_seq (u : nat -> Rbar) : {l : Rbar | is_inf_seq u l}.
Proof.
  case : (ex_sup_seq (fun n => Rbar_opp (u n))) => l Hl.
  exists (Rbar_opp l) ; apply is_sup_opp_inf_seq ; by rewrite Rbar_opp_involutive.
Qed.

(** Notations *)

Definition Sup_seq (u : nat -> Rbar) := projT1 (ex_sup_seq u).

Definition Inf_seq (u : nat -> Rbar) := projT1 (ex_inf_seq u).

Lemma is_sup_seq_unique (u : nat -> Rbar) (l : Rbar) :
  is_sup_seq u l -> Sup_seq u = l.
Proof.
  move => Hl ; rewrite /Sup_seq ; case: (ex_sup_seq _) => l0 Hl0 /= ;
  case: l Hl => [l | | ] Hl ; case: l0 Hl0 => [l0 | | ] Hl0 //.
  apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; 
  set eps := mkposreal e He ; apply Rlt_le ;
  case: (Hl (pos_div_2 eps)) => {Hl} Hl [n Hn] ;
  case: (Hl0 (pos_div_2 eps)) => {Hl0} Hl0 [n0 Hn0].
  have: (l0 = (l0 - eps/2) + eps/2) ; [by field | move => -> ] ;
  have : (l + e = (l + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ;
  apply Rplus_lt_compat_r, (Rbar_lt_trans 
    (Finite (l0 - eps/2)) (u n0) (Finite (l + eps/2)) Hn0 (Hl _)).
  have: (l = (l - eps/2) + eps/2) ; [by field | move => -> ] ;
  have : (l0 + e = (l0 + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ;
  apply Rplus_lt_compat_r, (Rbar_lt_trans 
    (Finite (l - eps/2)) (u n) (Finite (l0 + eps/2)) Hn (Hl0 _)).
  case: (Hl0 (l + 1)) => n {Hl0} Hl0 ; contradict Hl0 ; 
    apply Rbar_le_not_lt, Rbar_lt_le, (Hl (mkposreal _ Rlt_0_1)).
  case: (Hl (mkposreal _ Rlt_0_1)) => {Hl} _ [n Hl] ; contradict Hl ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
  case: (Hl (l0 + 1)) => n {Hl} Hl ; contradict Hl ; 
    apply Rbar_le_not_lt, Rbar_lt_le, (Hl0 (mkposreal _ Rlt_0_1)).
  case: (Hl 0) => n {Hl} Hl ; contradict Hl ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
  case: (Hl0 (mkposreal _ Rlt_0_1)) => {Hl0} _ [n Hl0] ; contradict Hl0 ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl.
  case: (Hl0 0) => n {Hl0} Hl0 ; contradict Hl0 ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl.
Qed.
Lemma Sup_seq_correct (u : nat -> Rbar) :
  is_sup_seq u (Sup_seq u).
Proof.
  rewrite /Sup_seq ; case: (ex_sup_seq _) => l Hl //.
Qed.
Lemma is_inf_seq_unique (u : nat -> Rbar) (l : Rbar) :
  is_inf_seq u l -> Inf_seq u = l.
Proof.
  move => Hl ; rewrite /Inf_seq ; case: (ex_inf_seq _) => l0 Hl0 /= ;
  case: l Hl => [l | | ] Hl ; case: l0 Hl0 => [l0 | | ] Hl0 //.
  apply Rbar_finite_eq, Rle_antisym ; apply le_epsilon => e He ; 
  set eps := mkposreal e He ; apply Rlt_le ;
  case: (Hl (pos_div_2 eps)) => {Hl} Hl [n Hn] ;
  case: (Hl0 (pos_div_2 eps)) => {Hl0} Hl0 [n0 Hn0].
  have: (l0 = (l0 - eps/2) + eps/2) ; [by field | move => -> ] ;
  have : (l + e = (l + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ;
  apply Rplus_lt_compat_r, (Rbar_lt_trans 
    (Finite (l0 - eps/2)) (u n) (Finite (l + eps/2)) (Hl0 _) Hn).
  have: (l = (l - eps/2) + eps/2) ; [by field | move => -> ] ;
  have : (l0 + e = (l0 + eps/2) + eps/2) ; [ simpl ; field | move => -> ] ;
  apply Rplus_lt_compat_r, (Rbar_lt_trans 
    (Finite (l - eps/2)) (u n0) (Finite (l0 + eps/2)) (Hl _) Hn0).
  case: (Hl (mkposreal _ Rlt_0_1)) => {Hl} _ [n Hl] ; contradict Hl ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
  case: (Hl0 (l - 1)) => n {Hl0} Hl0 ; contradict Hl0 ; 
    apply Rbar_le_not_lt, Rbar_lt_le, (Hl (mkposreal _ Rlt_0_1)).
  case: (Hl0 (mkposreal _ Rlt_0_1)) => {Hl0} _ [n Hl0] ; contradict Hl0 ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl.
  case: (Hl0 0) => n {Hl0} Hl0 ; contradict Hl0 ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl.
  case: (Hl (l0 - 1)) => n {Hl} Hl ; contradict Hl ; 
    apply Rbar_le_not_lt, Rbar_lt_le, (Hl0 (mkposreal _ Rlt_0_1)).
  case: (Hl 0) => n {Hl} Hl ; contradict Hl ; 
    apply Rbar_le_not_lt, Rbar_lt_le, Hl0.
Qed.
Lemma Inf_seq_correct (u : nat -> Rbar) :
  is_inf_seq u (Inf_seq u).
Proof.
  rewrite /Inf_seq ; case: (ex_inf_seq _) => l Hl //.
Qed.

Lemma Sup_seq_ext (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) -> Sup_seq u = Sup_seq v.
Proof.
  intro Heq ; rewrite {2}/Sup_seq ;
  case (ex_sup_seq v) ; simpl ; intros l2 Hv.
  by apply (is_sup_seq_unique u), is_sup_seq_ext with v.
Qed.
Lemma Inf_seq_ext (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) -> Inf_seq u = Inf_seq v.
Proof.
  intro Heq ; rewrite {2}/Inf_seq ;
  case (ex_inf_seq v) ; simpl ; intros l2 Hv.
  by apply (is_inf_seq_unique u), is_inf_seq_ext with v.
Qed.

Lemma Rbar_sup_eq_lub (u : nat -> Rbar) Hp Hex :
  Sup_seq u = Rbar_lub_ne (fun x => exists n, x = u n) Hp Hex.
Proof.
  rewrite /Sup_seq ; case: (ex_sup_seq _) => /= s Hs.
  rewrite /Rbar_lub_ne ; case: (Rbar_ex_lub_ne _ _ _) => /= l Hl.
  apply (Rbar_is_lub_rw 
    (fun x : Rbar => exists n : nat, x = u n) 
    (fun x : Rbar => exists n : nat, x = u n)) => // ;
  by apply is_sup_seq_lub.
Qed.
Lemma Inf_eq_glb (u : nat -> Rbar) Hm Hex :
  Inf_seq u = Rbar_glb_ne (fun x => exists n, x = u n) Hm Hex.
Proof.
  rewrite /Inf_seq ; case: (ex_inf_seq _) => /= s Hs.
  rewrite /Rbar_glb_ne ; case: (Rbar_ex_glb_ne _ _ _) => /= l Hl.
  apply (Rbar_is_glb_rw 
    (fun x : Rbar => exists n : nat, x = u n) 
    (fun x : Rbar => exists n : nat, x = u n)) => // ;
  by apply is_inf_seq_glb.
Qed.

Lemma Rbar_sup_opp_inf (u : nat -> Rbar) :
  Sup_seq u = Rbar_opp (Inf_seq (fun n => Rbar_opp (u n))).
Proof.
  rewrite /Inf_seq ; case: (ex_inf_seq _) => iu Hiu /=.
  apply is_sup_seq_unique.
  apply is_inf_opp_sup_seq.
  by rewrite Rbar_opp_involutive.
Qed.
Lemma Inf_opp_sup (u : nat -> Rbar) :
  Inf_seq u = Rbar_opp (Sup_seq (fun n => Rbar_opp (u n))).
Proof.
  rewrite Rbar_sup_opp_inf Rbar_opp_involutive.
  rewrite /Inf_seq.
  repeat (case: ex_inf_seq ; intros) => /=.
  apply is_inf_seq_glb in p.
  apply is_inf_seq_glb in p0.
  move: p p0 ; apply Rbar_is_glb_rw.
  move => x1 ; split ; case => n -> ; exists n ; by rewrite Rbar_opp_involutive.
Qed.

(** ** Order *)

Lemma is_sup_seq_le (u v : nat -> Rbar) {l1 l2 : Rbar} :
  (forall n, Rbar_le (u n) (v n)) 
  -> (is_sup_seq u l1) -> (is_sup_seq v l2) -> Rbar_le l1 l2.
Proof.
  destruct l1 as [l1 | | ] ; destruct l2 as [l2 | | ] ; intros Hle Hu Hv ;
  case (is_sup_seq_lub _ _ Hu) ; clear Hu ; intros _ Hu ;
  case (is_sup_seq_lub _ _ Hv) ; clear Hv ; intros Hv _ ;
  apply Hu ; intros x (n,Hn) ; rewrite Hn ; clear x Hn ; apply Rbar_le_trans with (1 := Hle _), Hv ; exists n ; auto.
Qed.
Lemma is_inf_seq_le (u v : nat -> Rbar) {l1 l2 : Rbar} :
  (forall n, Rbar_le (u n) (v n)) 
  -> (is_inf_seq u l1) -> (is_inf_seq v l2) -> Rbar_le l1 l2.
Proof.
  case: l1 => [l1 | | ] ; case: l2 => [l2 | | ] Hle Hu Hv ;
  case: (is_inf_seq_glb _ _ Hu) => {Hu} Hu _ ;
  case: (is_inf_seq_glb _ _ Hv) => {Hv} _ Hv ;
  apply Hv => _ [n ->] ; apply Rbar_le_trans with (2 := Hle _), Hu ; by exists n.
Qed.

Lemma Sup_seq_le (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Sup_seq u) (Sup_seq v).
Proof.
  intros Heq ; unfold Sup_seq ;
  case (ex_sup_seq u) ; intros l1 Hu ; case (ex_sup_seq v) ; simpl ; intros l2 Hv.
  apply (is_sup_seq_le u v) ; auto.
Qed.
Lemma Inf_seq_le (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Inf_seq u) (Inf_seq v).
Proof.
  move => Heq ; rewrite /Inf_seq ;
  case: (ex_inf_seq u) => l1 Hu ; case: (ex_inf_seq v) => /= l2 Hv.
  by apply (is_inf_seq_le u v).
Qed.

Lemma Inf_le_sup (u : nat -> Rbar) : Rbar_le (Inf_seq u) (Sup_seq u).
Proof.
  rewrite /Inf_seq ; case: (ex_inf_seq _) ; case => [iu | | ] Hiu ;
  rewrite /Sup_seq ; case: (ex_sup_seq _) ; case => [su | | ] Hsu /=.
(* Finite, Finite *)
  apply Rbar_finite_le, le_epsilon => e He ; set eps := mkposreal e He ;
  case: (Hiu (pos_div_2 eps)) => {Hiu} Hiu _ ; 
  case: (Hsu (pos_div_2 eps)) => {Hsu} Hsu _ ;
  apply Rlt_le.
  have : (iu = iu - e/2 + e/2) ; first by ring.
  move => -> ; have : (su+e = su + e/2 + e/2) ; first by field.
  by move => -> ; apply Rplus_lt_compat_r, 
  (Rbar_lt_trans (Finite (iu - e/2)) (u O) (Finite (su + e/2))).
(* Finite, p_infty *)
  by left.
(* Finite, m_infty *)
  set eps := mkposreal _ Rlt_0_1 ; case: (Hiu eps) => {Hiu} Hiu _ ;
  left ; move: (Hiu O) => {Hiu} ; apply Rbar_le_not_lt, Rbar_lt_le, Hsu.
(* p_infty, Finite *)
  set eps := mkposreal _ Rlt_0_1 ; case: (Hsu eps) => {Hsu} Hsu _ ;
  left ; move: (Hsu O) => {Hsu} ; apply Rbar_le_not_lt, Rbar_lt_le, Hiu.
(* p_infty, p_infty *)
  by right.
(* p_infty, m_infty *)
  left ; move: (Hiu 0 O) => {Hiu} ; apply Rbar_le_not_lt, Rbar_lt_le, Hsu.
(* m_infty, Finite *)
  by left.
(* m_infty, p_infty *)
  by left.
(* m_infty, m_infty *)
  by right.
Qed.

Lemma is_sup_seq_major (u : nat -> Rbar) (l : Rbar) (n : nat) :
  is_sup_seq u l -> Rbar_le (u n) l.
Proof.
  case: l => [l | | ] /= Hl.
  move: (fun eps => proj1 (Hl eps) n) => {Hl}.
  case: (u n) => [un | | ] /= Hun.
  apply Rbar_finite_le, le_epsilon => e He ; apply Rlt_le.
  apply: Hun (mkposreal e He).
  by move: (Hun (mkposreal _ Rlt_0_1)).
  by left.
  case: (u n) => [un | | ].
  by left.
  by right.
  by left.
  move: (Hl (u n) n) ; case: (u n) => [un | | ] /= {Hl} Hl.
  by apply Rlt_irrefl in Hl.
  by [].
  by right.
Qed.
Lemma Sup_seq_minor_lt (u : nat -> Rbar) (M : R) :
  Rbar_lt M (Sup_seq u) <-> exists n, Rbar_lt M (u n).
Proof.
  rewrite /Sup_seq ; case: ex_sup_seq => l Hl ; simpl projT1 ; split => H.
  case: l Hl H => [l | | ] Hl H.
  apply Rminus_lt_0 in H.
  case: (proj2 (Hl (mkposreal _ H))) ; simpl pos => {Hl} n Hl.
  exists n.
  replace M with (l - (l - M)) by ring.
  by apply Hl.
  apply (Hl M).
  by [].
  case: H => n Hn.
  apply Rbar_lt_le_trans with (u n).
  exact: Hn.
  by apply is_sup_seq_major.
Qed.
Lemma Sup_seq_minor_le (u : nat -> Rbar) (M : R) (n : nat) :
  Rbar_le M (u n) -> Rbar_le M (Sup_seq u).
Proof.
  case => H.
  left ; apply Sup_seq_minor_lt.
  by exists n.
  rewrite H.
  rewrite /Sup_seq ; case: ex_sup_seq => l Hl ; simpl projT1.
  by apply is_sup_seq_major.
Qed.

(** * LimSup and LimInf of sequences *)

(** ** Definitions *)

Definition is_LimSup_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, 
        (forall N : nat, exists n : nat, (N <= n)%nat /\ l - eps < u n)
        /\ (exists N : nat, forall n : nat, (N <= n)%nat -> u n < l + eps)
    | p_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ M < u n)
    | m_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> u n < M)
  end.

Definition is_LimInf_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, 
        (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < l + eps)
        /\ (exists N : nat, forall n : nat, (N <= n)%nat -> l - eps < u n)
    | p_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> M < u n)
    | m_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ u n < M)
  end.


(** Equivalent forms *)

Lemma is_LimInf_opp_LimSup_seq (u : nat -> R) (l : Rbar) :
  is_LimInf_seq (fun n => - u n) (Rbar_opp l) 
    <-> is_LimSup_seq u l.
Proof.
  case: l => [l | | ] /= ; split => Hl.
(* l \in R *)
(* * -> *)
  move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
  move => N ; case: (H1 N) => {H1} n [Hn H1].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel.
  apply Rlt_le_trans with (1 := H1) ; right ; ring.
  case: H2 => N H2.
  exists N => n Hn.
  apply Ropp_lt_cancel.
  apply Rle_lt_trans with (2 := H2 _ Hn) ; right ; ring.
(* * <- *)
  move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
  move => N ; case: (H1 N) => {H1} n [Hn H1].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  apply Rle_lt_trans with (2 := H1) ; right ; ring.
  case: H2 => N H2.
  exists N => n Hn.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  apply Rlt_le_trans with (1 := H2 _ Hn) ; right ; ring.
(* l = p_infty *)
  move => M N.
  case: (Hl (-M) N) => {Hl} n [Hn Hl].
  exists n ; split.
  by [].
  by apply Ropp_lt_cancel.
  move => M N.
  case: (Hl (-M) N) => {Hl} n [Hn Hl].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
(* l = m_infty *)
  move => M.
  case: (Hl (-M)) => {Hl} N Hl.
  exists N => n Hn.
  apply Ropp_lt_cancel.
  by apply Hl.
  move => M.
  case: (Hl (-M)) => {Hl} N Hl.
  exists N => n Hn.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  by apply Hl.
Qed.
Lemma is_LimSup_opp_LimInf_seq (u : nat -> R) (l : Rbar) :
  is_LimSup_seq (fun n => - u n) (Rbar_opp l) 
    <-> is_LimInf_seq u l.
Proof.
Proof.
  case: l => [l | | ] /= ; split => Hl.
(* l \in R *)
(* * -> *)
  move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
  move => N ; case: (H1 N) => {H1} n [Hn H1].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel.
  apply Rle_lt_trans with (2 := H1) ; right ; ring.
  case: H2 => N H2.
  exists N => n Hn.
  apply Ropp_lt_cancel.
  apply Rlt_le_trans with (1 := H2 _ Hn) ; right ; ring.
(* * <- *)
  move => eps ; case: (Hl eps) => {Hl} H1 H2 ; split.
  move => N ; case: (H1 N) => {H1} n [Hn H1].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  apply Rlt_le_trans with (1 := H1) ; right ; ring.
  case: H2 => N H2.
  exists N => n Hn.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  apply Rle_lt_trans with (2 := H2 _ Hn) ; right ; ring.
(* l = p_infty *)
  move => M.
  case: (Hl (-M)) => {Hl} N Hl.
  exists N => n Hn.
  apply Ropp_lt_cancel.
  by apply Hl.
  move => M.
  case: (Hl (-M)) => {Hl} N Hl.
  exists N => n Hn.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  by apply Hl.
(* l = m_infty *)
  move => M N.
  case: (Hl (-M) N) => {Hl} n [Hn Hl].
  exists n ; split.
  by [].
  by apply Ropp_lt_cancel.
  move => M N.
  case: (Hl (-M) N) => {Hl} n [Hn Hl].
  exists n ; split.
  by [].
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
Qed.

Lemma is_LimSup_infSup_seq (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l <-> is_inf_seq (fun m => Sup_seq (fun n => u (n + m)%nat)) l.
Proof.
  case: l => [l | | ] ;
  rewrite /is_LimSup_seq /is_inf_seq ;
  split => Hl.
(* l \in R *)
(* * -> *)
  split.
  move => N.
  apply Sup_seq_minor_lt.
  case: (proj1 (Hl eps) N) => {Hl} n Hl.
  exists (n - N)%nat.
  rewrite NPeano.Nat.sub_add ; intuition.
  case: (proj2 (Hl (pos_div_2 eps))) => /= {Hl} N Hl.
  exists N ; rewrite /Sup_seq ; case: ex_sup_seq => un Hun ; simpl projT1.
  case: un Hun => [un | | ] /= Hun.
  case: (proj2 (Hun (pos_div_2 eps))) => {Hun} /= n Hun.
  apply Rlt_minus_l in Hun.
  apply Rlt_trans with (1 := Hun).
  apply Rlt_minus_r.
  apply Rlt_le_trans with (1 := Hl _ (le_plus_r _ _)) ; right ; field.
  case: (Hun (l + eps / 2)) => {Hun} n.
  apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
  by [].
(* * <- *)
  split.
  move => N.
  move: (proj1 (Hl eps) N) => {Hl} Hl.
  apply Sup_seq_minor_lt in Hl.
  case: Hl => /= n Hl.
  exists (n + N)%nat ; intuition.
  case: (proj2 (Hl eps)) => {Hl} N Hl.
  exists N => n Hn.
  apply (Rbar_not_le_lt (l + eps) (u n)).
  contradict Hl.
  apply Rbar_le_not_lt.
  apply Sup_seq_minor_le with (n - N)%nat.
  by rewrite NPeano.Nat.sub_add.
(* l = p_infty *)
  move => M N.
  case: (Hl M N) => {Hl} n Hl.
  apply Sup_seq_minor_lt.
  exists (n - N)%nat.
  rewrite NPeano.Nat.sub_add ; intuition.
  move => M N.
  move: (Hl M N) => {Hl} Hl.
  apply Sup_seq_minor_lt in Hl.
  case: Hl => /= n Hl.
  exists (n + N)%nat ; intuition.
(* l = m_infty *)
  move => M.
  case: (Hl (M-1)) => {Hl} N Hl.
  exists N ; rewrite /Sup_seq ; case: ex_sup_seq => un Hun ; simpl projT1.
  case: un Hun => [un | | ] /= Hun.
  case: (proj2 (Hun (mkposreal _ Rlt_0_1))) => {Hun} /= n Hun.
  apply Rlt_minus_l in Hun.
  apply Rlt_trans with (1 := Hun).
  apply Rlt_minus_r.
  apply Hl ; intuition.
  case: (Hun (M-1)) => {Hun} n.
  apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
  by [].
  move => M.
  case: (Hl M) => {Hl} N Hl.
  exists N => n Hn.
  apply (Rbar_not_le_lt M (u n)).
  contradict Hl.
  apply Rbar_le_not_lt.
  apply Sup_seq_minor_le with (n - N)%nat.
  by rewrite NPeano.Nat.sub_add.
Qed.
Lemma is_LimInf_supInf_seq (u : nat -> R) (l : Rbar) :
  is_LimInf_seq u l <-> is_sup_seq (fun m => Inf_seq (fun n => u (n + m)%nat)) l.
Proof.
  rewrite -is_LimSup_opp_LimInf_seq.
  rewrite is_LimSup_infSup_seq.
  rewrite -is_sup_opp_inf_seq.
  rewrite Rbar_opp_involutive.
  split ; apply is_sup_seq_ext => n ;
  by rewrite Inf_opp_sup.
Qed.

(** Extentionality *)

Lemma is_LimSup_seq_ext_loc (u v : nat -> R) (l : Rbar) :
  (exists N, forall n, (N <= n)%nat -> u n = v n)
  -> is_LimSup_seq u l -> is_LimSup_seq v l.
Proof.
  case: l => [l | | ] /= [Next Hext] Hu.
  move => eps.
  case: (Hu eps) => {Hu} H1 H2 ; split.
  move => N.
  case: (H1 (N + Next)%nat) => {H1} n [Hn H1].
  exists n ; rewrite -Hext ; intuition.
  case: H2 => N H2.
  exists (N + Next)%nat => n Hn.
  rewrite -Hext ; intuition.
  move => M N.
  case: (Hu M (N + Next)%nat) => {Hu} n [Hn Hu].
  exists n ; rewrite -Hext ; intuition.
  move => M.
  case: (Hu M) => {Hu} N Hu.
  exists (N + Next)%nat => n Hn.
  rewrite -Hext ; intuition.
Qed.
Lemma is_LimSup_seq_ext (u v : nat -> R) (l : Rbar) :
  (forall n, u n = v n)
  -> is_LimSup_seq u l -> is_LimSup_seq v l.
Proof.
  move => Hext.
  apply is_LimSup_seq_ext_loc.
  exists O => n _ ; by apply Hext.
Qed.

Lemma is_LimInf_seq_ext_loc (u v : nat -> R) (l : Rbar) :
  (exists N, forall n, (N <= n)%nat -> u n = v n)
  -> is_LimInf_seq u l -> is_LimInf_seq v l.
Proof.
  case => N Hext Hu.
  apply is_LimSup_opp_LimInf_seq.
  apply is_LimSup_seq_ext_loc with (fun n => - u n).
  exists N => n Hn ; by rewrite Hext.
  by apply is_LimSup_opp_LimInf_seq.
Qed.
Lemma is_LimInf_seq_ext (u v : nat -> R) (l : Rbar) :
  (forall n, u n = v n)
  -> is_LimInf_seq u l -> is_LimInf_seq v l.
Proof.
  move => Hext.
  apply is_LimInf_seq_ext_loc.
  exists O => n _ ; by apply Hext.
Qed.

(** Existance *)

Lemma ex_LimSup_seq (u : nat -> R) : 
  {l : Rbar | is_LimSup_seq u l}.
Proof.
  case: (ex_inf_seq (fun m : nat => Sup_seq (fun n : nat => u (n + m)%nat))) => l Hl.
  exists l.
  by apply is_LimSup_infSup_seq.
Qed.
Lemma ex_LimInf_seq (u : nat -> R) : 
  {l : Rbar | is_LimInf_seq u l}.
Proof.
  case: (ex_sup_seq (fun m : nat => Inf_seq (fun n : nat => u (n + m)%nat))) => l Hl.
  exists l.
  by apply is_LimInf_supInf_seq.
Qed.

(** Functions *)

Definition LimSup_seq (u : nat -> R) :=
  projT1 (ex_LimSup_seq u).
Definition LimInf_seq (u : nat -> R) :=
  projT1 (ex_LimInf_seq u).

(** Unicity *)

Lemma is_LimSup_seq_unique (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l -> LimSup_seq u = l.
Proof.
  move => H.
  rewrite /LimSup_seq.
  case: ex_LimSup_seq => lu Hu /=.
  apply is_LimSup_infSup_seq in H.
  apply is_LimSup_infSup_seq in Hu.
  rewrite -(is_inf_seq_unique _ _ Hu).
  by apply is_inf_seq_unique.
Qed.
Lemma is_LimInf_seq_unique (u : nat -> R) (l : Rbar) :
  is_LimInf_seq u l -> LimInf_seq u = l.
Proof.
  move => H.
  rewrite /LimInf_seq.
  case: ex_LimInf_seq => lu Hu /=.
  apply is_LimInf_supInf_seq in H.
  apply is_LimInf_supInf_seq in Hu.
  rewrite -(is_sup_seq_unique _ _ Hu).
  by apply is_sup_seq_unique.
Qed.

(** ** Operations and order *)

Lemma is_LimSup_LimInf_seq_le (u : nat -> R) (ls li : Rbar) :
  is_LimSup_seq u ls -> is_LimInf_seq u li -> Rbar_le li ls.
Proof.
  case: ls => [ls | | ] ; case: li => [li | | ] //= Hls Hli ;
  try by [right | left].
  apply Rbar_finite_le, le_epsilon => e He ;
  set eps := pos_div_2 (mkposreal e He).
  replace li with ((li - eps) + eps) by ring.
  replace (ls + e) with ((ls + eps) + eps) by (simpl ; field).
  apply Rplus_le_compat_r, Rlt_le.
  case: (proj2 (Hls eps)) => {Hls} Ns Hls.
  case: (proj2 (Hli eps)) => {Hli} Ni Hli.
  apply Rlt_trans with (u (Ns + Ni)%nat).
  apply Hli ; by intuition.
  apply Hls ; by intuition.
  case: (proj2 (Hls (mkposreal _ Rlt_0_1))) => {Hls} /= Ns Hls.
  case: (Hli (ls + 1)) => {Hli} Ni Hli.
  absurd (ls + 1 < u (Ns + Ni)%nat).
  apply Rle_not_lt, Rlt_le, Hls ; by intuition.
  apply Hli ; by intuition.
  case: (proj2 (Hli (mkposreal _ Rlt_0_1))) => {Hli} /= Ni Hli.
  case: (Hls (li - 1)) => {Hls} Ns Hls.
  absurd (li - 1 < u (Ns + Ni)%nat).
  apply Rle_not_lt, Rlt_le, Hls ; by intuition.
  apply Hli ; by intuition.
  case: (Hli 0) => {Hli} /= Ni Hli.
  case: (Hls 0) => {Hls} Ns Hls.
  absurd (0 < u (Ns + Ni)%nat).
  apply Rle_not_lt, Rlt_le, Hls ; by intuition.
  apply Hli ; by intuition.
Qed.
Lemma LimSup_LimInf_seq_le (u : nat -> R) :
  Rbar_le (LimInf_seq u) (LimSup_seq u).
Proof.
  rewrite /LimInf_seq ; case: ex_LimInf_seq => /= li Hli.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= ls Hls.
  by apply is_LimSup_LimInf_seq_le with u.
Qed.

(** Opposite *)

Lemma LimSup_seq_opp (u : nat -> R) :
  LimSup_seq (fun n => - u n) = Rbar_opp (LimInf_seq u).
Proof.
  rewrite /LimInf_seq ; case: ex_LimInf_seq => /= li Hli.
  apply is_LimSup_opp_LimInf_seq in Hli.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= ls Hls.
  rewrite -(is_LimSup_seq_unique _ _ Hls).
  by apply is_LimSup_seq_unique.
Qed.
Lemma LimInf_seq_opp (u : nat -> R) :
  LimInf_seq (fun n => - u n) = Rbar_opp (LimSup_seq u).
Proof.
  rewrite /LimInf_seq ; case: ex_LimInf_seq => /= li Hli.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= ls Hls.
  apply is_LimInf_opp_LimSup_seq in Hls.
  rewrite -(is_LimInf_seq_unique _ _ Hli).
  by apply is_LimInf_seq_unique.
Qed.

(** Scalar multplication *)

Lemma is_LimSup_seq_scal_pos (a : R) (u : nat -> R) (l : Rbar) :
  (0 < a) -> is_LimSup_seq u l ->
    is_LimSup_seq (fun n => a * u n) (Rbar_mult a l).
Proof.
  case: l => [l | | ] /= Ha Hu.
  move => eps.
  suff He : 0 < eps / a.
  case: (Hu (mkposreal _ He)) => {Hu} /= H1 H2 ; split.
  move => N ; case: (H1 N) => {H1} n [Hn H1].
  exists n ; split.
  by [].
  rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_l.
  by [].
  apply Rle_lt_trans with (2 := H1) ; right ; field ; by apply Rgt_not_eq.
  case: H2 => N H2.
  exists N => n Hn.
  rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_r.
  by [].
  apply Rlt_le_trans with (1 := H2 _ Hn) ; right ; field ; by apply Rgt_not_eq.
  apply Rdiv_lt_0_compat ; [ by case eps | by [] ].
  case: Rle_dec (Rlt_le _ _ Ha) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => {H} // _ _.
  move => M N.
  case: (Hu (M / a) N) => {Hu} n [Hn Hu].
  exists n ; split.
  by [].
  rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_l.
  by [].
  by [].
  case: Rle_dec (Rlt_le _ _ Ha) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => {H} // _ _.
  move => M.
  case: (Hu (M / a)) => {Hu} N Hu.
  exists N => n Hn.
  rewrite (Rmult_comm _ (u n)) ; apply Rlt_div_r.
  by [].
  by apply Hu.
Qed.
Lemma is_LimInf_seq_scal_pos (a : R) (u : nat -> R) (l : Rbar) :
  (0 < a) -> is_LimInf_seq u l ->
    is_LimInf_seq (fun n => a * u n) (Rbar_mult a l).
Proof.
  move => Ha Hu.
  apply is_LimSup_opp_LimInf_seq in Hu.
  apply is_LimSup_opp_LimInf_seq.
  replace (Rbar_opp (Rbar_mult a l)) with (Rbar_mult a (Rbar_opp l)).
  apply is_LimSup_seq_ext with (fun n => a * - u n).
  move => n ; ring.
  by apply is_LimSup_seq_scal_pos.
  case: (l) => [x | | ] /=.
  apply f_equal ; ring.
  case: Rle_dec (Rlt_le _ _ Ha) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => // H _.
  case: Rle_dec (Rlt_le _ _ Ha) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => // H _.
Qed.

(** Index shifting *)

Lemma is_LimSup_seq_ind_1 (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l <->
    is_LimSup_seq (fun n => u (S n)) l.
Proof.
  case: l => [l | | ] ; split => //= Hu.
(* l \in R *)
  move => eps.
  case: (Hu eps) => {Hu} H1 H2 ; split.
  move => N.
  case: (H1 (S N)) => {H1} n [Hn H1].
  exists (pred n).
  case: (n) Hn H1 => /= [ | m] Hm H1.
  by apply le_Sn_O in Hm.
  split.
  by apply le_S_n.
  by apply H1.
  case: H2 => N H2.
  exists N => n Hn.
  apply H2 ; intuition.
  move => eps.
  case: (Hu eps) => {Hu} H1 H2 ; split.
  move => N.
  case: (H1 N) => {H1} n [Hn H1].
  exists (S n) ; intuition.
  case: H2 => N H2.
  exists (S N) => n Hn.
  case: (n) Hn => /= [ | m] Hm.
  by apply le_Sn_O in Hm.
  apply H2 ; intuition.
(* l = p_infty *)
  move => M N.
  case: (Hu M (S N)) => {Hu} n [Hn Hu].
  exists (pred n).
  case: (n) Hn Hu => /= [ | m] Hm Hu.
  by apply le_Sn_O in Hm.
  split.
  by apply le_S_n.
  by apply Hu.
  move => M N.
  case: (Hu M N) => {Hu} n [Hn Hu].
  exists (S n) ; intuition.
(* l = m_infty *)
  move => M.
  case: (Hu M) => {Hu} N Hu.
  exists N => n Hn.
  apply Hu ; intuition.
  move => M.
  case: (Hu M) => {Hu} N Hu.
  exists (S N) => n Hn.
  case: (n) Hn => /= [ | m] Hm.
  by apply le_Sn_O in Hm.
  apply Hu ; intuition.
Qed.
Lemma is_LimInf_seq_ind_1 (u : nat -> R) (l : Rbar) :
  is_LimInf_seq u l <->
    is_LimInf_seq (fun n => u (S n)) l.
Proof.
  rewrite -?is_LimSup_opp_LimInf_seq.
  by apply is_LimSup_seq_ind_1.
Qed.

Lemma is_LimSup_seq_ind_k (u : nat -> R) (k : nat) (l : Rbar) :
  is_LimSup_seq u l <->
    is_LimSup_seq (fun n => u (n + k)%nat) l.
Proof.
  elim: k u => [ | k IH] /= u.
  split ; apply is_LimSup_seq_ext => n ; by rewrite -plus_n_O.
  rewrite is_LimSup_seq_ind_1.
  rewrite (IH (fun n => u (S n))).
  split ; apply is_LimSup_seq_ext => n ; by rewrite plus_n_Sm.
Qed.
Lemma is_LimInf_seq_ind_k (u : nat -> R) (k : nat) (l : Rbar) :
  is_LimInf_seq u l <->
    is_LimInf_seq (fun n => u (n + k)%nat) l.
Proof.
  rewrite -?is_LimSup_opp_LimInf_seq.
  by apply (is_LimSup_seq_ind_k (fun n => - u n)).
Qed.

(** * Limit of sequences *)

(** ** Definition *)

Definition is_lim_seq (u : nat -> R) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, exists N : nat, forall n : nat,
                    (N <= n)%nat -> Rabs (u n - l) < eps
    | p_infty => forall M : R, exists N : nat, forall n : nat, (N <= n)%nat -> M < u n
    | m_infty => forall M : R, exists N : nat, forall n : nat, (N <= n)%nat -> u n < M
  end.
Definition ex_lim_seq (u : nat -> R) :=
  exists l, is_lim_seq u l.
Definition ex_finite_lim_seq (u : nat -> R) :=
  exists l : R, is_lim_seq u l.
Definition Lim_seq (u : nat -> R) : Rbar := 
  Rbar_div_pos (Rbar_plus (LimSup_seq u) (LimInf_seq u))
    {| pos := 2; cond_pos := Rlt_R0_R2 |}.

(** Equivalences *)

Lemma is_lim_seq_Un_cv (u : nat -> R) (l : R) :
  is_lim_seq u l <-> Un_cv u l.
Proof.
  split => Hl.
  move => e He.
  case: (Hl (mkposreal e He)) => {Hl} /= N Hl.
  exists N => n Hn.
  by apply (Hl n Hn).
  case => e He.
  case: (Hl e He) => {Hl} /= N Hl.
  exists N => n Hn.
  by apply (Hl n Hn).
Qed.

Lemma is_lim_LimSup_seq (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_LimSup_seq u l.
Proof.
  case: l => [l | | ] /= Hu.
  move => eps ; case: (Hu eps) => {Hu} N Hu ; split.
  move => N0.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Rabs_lt_between', Hu, le_plus_l.
  exists N => n Hn.
  by apply Rabs_lt_between', Hu.
  move => M N0.
  case: (Hu M) => {Hu} N Hu.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Hu, le_plus_l.
  by [].
Qed.
Lemma is_lim_LimInf_seq (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_LimInf_seq u l.
Proof.
  case: l => [l | | ] /= Hu.
  move => eps ; case: (Hu eps) => {Hu} N Hu ; split.
  move => N0.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Rabs_lt_between', Hu, le_plus_l.
  exists N => n Hn.
  by apply Rabs_lt_between', Hu.
  by [].
  move => M N0.
  case: (Hu M) => {Hu} N Hu.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Hu, le_plus_l.
Qed.
Lemma is_LimSup_LimInf_lim_seq (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l -> is_LimInf_seq u l -> is_lim_seq u l.
Proof.
  case: l => [l | | ] /= Hs Hi.
  move => eps.
  case: (proj2 (Hs eps)) => {Hs} Ns Hs.
  case: (proj2 (Hi eps)) => {Hi} Ni Hi.
  exists (Ns + Ni)%nat => n Hn.
  apply Rabs_lt_between' ; split.
  apply Hi ; intuition.
  apply Hs ; intuition.
  by apply Hi.
  by apply Hs.
Qed.

Lemma ex_lim_LimSup_LimInf_seq (u : nat -> R) :
  ex_lim_seq u <-> LimSup_seq u = LimInf_seq u.
Proof.
  split => Hl.
  case: Hl => l Hu.
  transitivity l.
  apply is_LimSup_seq_unique.
  by apply is_lim_LimSup_seq.
  apply sym_eq, is_LimInf_seq_unique.
  by apply is_lim_LimInf_seq.
  exists (LimSup_seq u).
  apply is_LimSup_LimInf_lim_seq.
  rewrite /LimSup_seq ; by case: ex_LimSup_seq.
  rewrite Hl /LimInf_seq ; by case: ex_LimInf_seq.
Qed.

(** Extentionality *)

Lemma is_lim_seq_ext_loc (u v : nat -> R) (l : Rbar) : 
  (exists N, forall n, (N <= n)%nat -> u n = v n) 
    -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  move => Hext Hu.
  apply is_LimSup_LimInf_lim_seq.
  apply is_LimSup_seq_ext_loc with u.
  by [].
  by apply is_lim_LimSup_seq.
  apply is_LimInf_seq_ext_loc with u.
  by [].
  by apply is_lim_LimInf_seq.
Qed.
Lemma ex_lim_seq_ext_loc (u v : nat -> R) : 
  (exists N, forall n, (N <= n)%nat -> u n = v n)
    -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => H [l H0].
  exists l ; by apply is_lim_seq_ext_loc with u.
Qed.
Lemma Lim_seq_ext_loc (u v : nat -> R) : 
  (exists N, forall n, (N <= n)%nat -> u n = v n) -> 
  Lim_seq u = Lim_seq v.
Proof.
  intros.
  rewrite /Lim_seq.
  apply (f_equal (fun x => Rbar_div_pos x _)).
  apply f_equal2 ; apply sym_eq.
  apply is_LimSup_seq_unique.
  apply is_LimSup_seq_ext_loc with u.
  by [].
  rewrite /LimSup_seq ; by case: ex_LimSup_seq.
  apply is_LimInf_seq_unique.
  apply is_LimInf_seq_ext_loc with u.
  by [].
  rewrite /LimInf_seq ; by case: ex_LimInf_seq.
Qed.

Lemma is_lim_seq_ext (u v : nat -> R) (l : Rbar) : 
  (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  move => Hext.
  apply is_lim_seq_ext_loc.
  by exists O.
Qed.
Lemma ex_lim_seq_ext (u v : nat -> R) : 
  (forall n, u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => H [l H0].
  exists l ; by apply is_lim_seq_ext with u.
Qed.
Lemma Lim_seq_ext (u v : nat -> R) : 
  (forall n, u n = v n) -> 
  Lim_seq u = Lim_seq v.
Proof.
  move => Hext.
  apply Lim_seq_ext_loc.
  by exists O.
Qed.

(** Unicity *)

Lemma is_lim_seq_unique (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> Lim_seq u = l.
Proof.
  move => Hu.
  rewrite /Lim_seq.
  replace l with (Rbar_div_pos (Rbar_plus l l) {| pos := 2; cond_pos := Rlt_R0_R2 |})
    by (case: (l) => [x | | ] //= ; apply f_equal ; field).
  apply (f_equal (fun x => Rbar_div_pos x _)).
  apply f_equal2.
  apply is_LimSup_seq_unique.
  by apply is_lim_LimSup_seq.
  apply is_LimInf_seq_unique.
  by apply is_lim_LimInf_seq.
Qed.
Lemma Lim_seq_correct (u : nat -> R) :
  ex_lim_seq u -> is_lim_seq u (Lim_seq u).
Proof.
  intros (l,H).
  cut (Lim_seq u = l).
    intros ; rewrite H0 ; apply H.
  apply is_lim_seq_unique, H.
Qed.
Lemma Lim_seq_correct' (u : nat -> R) :
  ex_finite_lim_seq u -> is_lim_seq u (real (Lim_seq u)).
Proof.
  intros (l,H).
  cut (real (Lim_seq u) = l).
    intros ; rewrite H0 ; apply H.
  replace l with (real l) by auto.
  apply f_equal, is_lim_seq_unique, H.
Qed.

Ltac search_lim_seq := let l := fresh "l" in
evar (l : Rbar) ;
match goal with
  | |- Lim_seq _ = ?lu => apply is_lim_seq_unique ; replace lu with l ; [ | unfold l]
  | |- is_lim_seq _ ?lu => replace lu with l ; [ | unfold l]
end.

Lemma ex_finite_lim_seq_correct (u : nat -> R) :
  ex_finite_lim_seq u <-> ex_lim_seq u /\ is_finite (Lim_seq u).
Proof.
  split.
  case => l Hl.
  split.
  by exists l.
  by rewrite (is_lim_seq_unique _ _ Hl).
  case ; case => l Hl H.
  exists l.
  rewrite -(is_lim_seq_unique _ _ Hl).
  by rewrite H (is_lim_seq_unique _ _ Hl).
Qed.

Lemma ex_lim_seq_dec (u : nat -> R) :
  {ex_lim_seq u} + {~ex_lim_seq u}.
Proof.
  case: (Rbar_eq_dec (LimSup_seq u) (LimInf_seq u)) => H.
  left ; by apply ex_lim_LimSup_LimInf_seq.
  right ; contradict H ; by apply ex_lim_LimSup_LimInf_seq.
Qed.

Lemma ex_finite_lim_seq_dec (u : nat -> R) :
  {ex_finite_lim_seq u} + {~ ex_finite_lim_seq u}.
Proof.
  case: (ex_lim_seq_dec u) => H.
  apply Lim_seq_correct in H.
  case: (Lim_seq u) H => [l | | ] H.
  left ; by exists l.
  right ; rewrite ex_finite_lim_seq_correct.
  rewrite (is_lim_seq_unique _ _ H) /is_finite //= ; by case.
  right ; rewrite ex_finite_lim_seq_correct.
  rewrite (is_lim_seq_unique _ _ H) /is_finite //= ; by case.
  right ; rewrite ex_finite_lim_seq_correct.
  contradict H ; by apply H.
Qed.

Definition ex_lim_seq_cauchy (u : nat -> R) :=
  forall eps : posreal, exists N : nat, forall n m,
    (N <= n)%nat -> (N <= m)%nat -> Rabs (u n - u m) < eps.
Lemma ex_lim_seq_cauchy_corr (u : nat -> R) :
  (ex_finite_lim_seq u) <-> ex_lim_seq_cauchy u.
Proof.
  split => Hcv.
  
  apply Lim_seq_correct' in Hcv.
  move => eps.
  case: (Hcv (pos_div_2 eps)) => /= {Hcv} N H.
  exists N => n m Hn Hm.
  replace (u n - u m) with ((u n - (real (Lim_seq u))) - (u m - (real (Lim_seq u)))) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps).
  apply Rplus_lt_compat ; by apply H.
  
  exists (LimSup_seq u) => eps.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= l Hl.
  case: (Hcv (pos_div_2 eps)) => {Hcv} /= Ncv Hcv.
  case: l Hl => [l | | ] /= Hl.
  case: (Hl (pos_div_2 eps)) => {Hl} /= H1 [Nl H2].
  exists (Ncv + Nl)%nat => n Hn.
  apply Rabs_lt_between' ; split.
  case: (H1 Ncv) => {H1} m [Hm H1].
  replace (l - eps) with ((l - eps / 2) - eps / 2) by field.
  apply Rlt_trans with (u m - eps / 2).
  by apply Rplus_lt_compat_r.
  apply Rabs_lt_between'.
  apply Hcv ; intuition.
  apply Rlt_trans with (l + eps / 2).
  apply H2 ; intuition.
  apply Rminus_lt_0 ; field_simplify ; rewrite ?Rdiv_1.
  by apply is_pos_div_2.
  move: (fun n Hn => proj2 (proj1 (Rabs_lt_between' _ _ _) (Hcv n Ncv Hn (le_refl _))))
  => {Hcv} Hcv.
  case: (Hl (u Ncv + eps / 2) Ncv) => {Hl} n [Hn Hl].
  contradict Hl ; apply Rle_not_lt, Rlt_le.
  by apply Hcv.
  move: (fun n Hn => proj1 (proj1 (Rabs_lt_between' _ _ _) (Hcv n Ncv Hn (le_refl _))))
  => {Hcv} Hcv.
  case: (Hl (u Ncv - eps / 2)) => {Hl} N Hl.
  move: (Hcv _ (le_plus_l Ncv N)) => H.
  contradict H ; apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
Qed.

(** ** Arithmetic operations and order *)

(** Identity *)

Lemma is_lim_seq_id :
  is_lim_seq INR p_infty.
Proof.
  move => M.
  suff Hm : 0 <= Rmax 0 M.
  exists (S (nfloor (Rmax 0 M) Hm)) => n Hn.
  apply Rlt_le_trans with (2 := le_INR _ _ Hn).
  rewrite /nfloor S_INR.
  case: nfloor_ex => {n Hn} /= n Hn.
  apply Rle_lt_trans with (1 := Rmax_r 0 M).
  by apply Hn.
  apply Rmax_l.
Qed.
Lemma ex_lim_seq_id :
  ex_lim_seq INR.
Proof.
  exists p_infty ; by apply is_lim_seq_id.
Qed.
Lemma Lim_seq_id :
  Lim_seq INR = p_infty.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_id.
Qed.

(** Constants *)

Lemma is_lim_seq_const (a : R) :
  is_lim_seq (fun n => a) a.
Proof.
  intros eps ; exists O ; intros.
  unfold Rminus ; rewrite (Rplus_opp_r a) Rabs_R0 ; apply eps.
Qed.
Lemma ex_lim_seq_const (a : R) :
  ex_lim_seq (fun n => a).
Proof.
  exists a ; by apply is_lim_seq_const.
Qed.
Lemma Lim_seq_const (a : R) :
  Lim_seq (fun n => a) = a.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_const.
Qed.

(** Subsequences *)

Lemma is_lim_seq_subseq (u : nat -> R) (l : Rbar) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> is_lim_seq u l
    -> is_lim_seq (fun n => u (phi n)) l.
Proof.
  move => Hphi Hu.

  have Hphi' : forall n : nat, (n <= phi n)%nat.
    elim => [ | n IH].
    by apply le_O_n.
    apply lt_le_S.
    apply le_lt_trans with (1 := IH).
    by apply Hphi.

  case: l Hu => [l | | ] Hu.
  move => eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  apply Hu.
  apply le_trans with (1 := Hn).
  by apply Hphi'.
  
  move => M.
  case: (Hu M) => {Hu} N Hu.
  exists N => n Hn.
  apply Hu.
  apply le_trans with (1 := Hn).
  by apply Hphi'.
  
  move => M.
  case: (Hu M) => {Hu} N Hu.
  exists N => n Hn.
  apply Hu.
  apply le_trans with (1 := Hn).
  by apply Hphi'.
Qed.
Lemma ex_lim_seq_subseq (u : nat -> R) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> ex_lim_seq u
    -> ex_lim_seq (fun n => u (phi n)).
Proof.
  move => Hphi [l Hu].
  exists l.
  by apply is_lim_seq_subseq.
Qed.
Lemma Lim_seq_subseq (u : nat -> R) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> ex_lim_seq u
    -> Lim_seq (fun n => u (phi n)) = Lim_seq u.
Proof.
  move => Hphi Hu.
  apply is_lim_seq_unique.
  apply is_lim_seq_subseq.
  by apply Hphi.
  by apply Lim_seq_correct.
Qed.

Lemma is_lim_seq_incr_1 (u : nat -> R) (l : Rbar) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (S n)) l.
Proof.
  split ; move => H.
  apply is_lim_seq_subseq.
  move => n ; by apply lt_n_Sn.
  by apply H.
  case: l H => [l | | ] H eps ;
  case: (H eps) => {H} N H ;
  exists (S N) ;
  case => [ | n] Hn ; intuition ;
  by apply le_Sn_0 in Hn.
Qed.
Lemma ex_lim_seq_incr_1 (u : nat -> R) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (S n)).
Proof.
  split ; move => [l H] ; exists l.
  by apply -> is_lim_seq_incr_1.
  by apply is_lim_seq_incr_1.
Qed.
Lemma Lim_seq_incr_1 (u : nat -> R) :
  Lim_seq (fun n => u (S n)) = Lim_seq u.
Proof.
  rewrite /Lim_seq.
  replace (LimSup_seq (fun n : nat => u (S n))) 
    with (LimSup_seq u).
  replace (LimInf_seq (fun n : nat => u (S n))) 
    with (LimInf_seq u).
  by [].
(* LimInf *)
  rewrite /LimInf_seq ;
  case: ex_LimInf_seq => l1 H1 ;
  case: ex_LimInf_seq => l2 H2 /= ;
  case: l1 H1 => [l1 | | ] /= H1 ;
  case: l2 H2 => [l2 | | ] /= H2.
  apply Rbar_finite_eq, Rle_antisym ; 
  apply le_epsilon => e He ; set eps := mkposreal e He ;
  apply Rlt_le.
  case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
  case: (proj1 (H2 (pos_div_2 eps)) N) => /= {H2} n [Hn H2].
  apply Rlt_trans with (u (S n) + e/2).
  replace l1 with ((l1-e/2)+e/2) by ring.
  apply Rplus_lt_compat_r.
  apply H1.
  apply le_trans with (1 := Hn).
  apply le_n_Sn.
  replace (l2+e) with ((l2+e/2)+e/2) by field.
  by apply Rplus_lt_compat_r, H2.
  case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
  case: (proj1 (H1 (pos_div_2 eps)) (S N)) => /= {H1} .
  case => [ | n] [Hn H1].
  by apply le_Sn_0 in Hn.
  apply Rlt_trans with (u (S n) + e/2).
  replace l2 with ((l2-e/2)+e/2) by ring.
  apply Rplus_lt_compat_r.
  apply H2.
  by apply le_S_n, Hn.
  replace (l1+e) with ((l1+e/2)+e/2) by field.
  by apply Rplus_lt_compat_r, H1.
  have : False => //.
  case: (H2 (l1+1)) => {H2} N /= H2.
  case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ;
  case => /= {H1} [ | n] [Hn].
  by apply le_Sn_0 in Hn.
  apply Rle_not_lt, Rlt_le, H2.
  by apply le_S_n.
  have : False => //.
  case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => {H1} N /= H1.
  case: ((H2 (l1-1)) N) => /= {H2}  n [Hn].
  apply Rle_not_lt, Rlt_le, H1.
  by apply le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (H1 (l2+1)) => {H1} N /= H1.
  case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2}  n [Hn].
  apply Rle_not_lt, Rlt_le, H1.
  by apply le_trans with (2 := le_n_Sn _).
  by [].
  have : False => //.
  case: (H1 0) => {H1} N H1.
  case: (H2 0 N)=> {H2} n [Hn].
  apply Rle_not_lt, Rlt_le, H1.
  by apply le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => /= {H2} N H2.
  case: (H1 (l2-1) (S N)) ;
  case => [ | n] [Hn].
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  have : False => //.
  case: (H2 0) => {H2} N H2.
  case: (H1 0 (S N)) ;
  case => [ | n] [Hn].
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  by [].
(* LimSup *)
  rewrite /LimSup_seq ;
  case: ex_LimSup_seq => l1 H1 ;
  case: ex_LimSup_seq => l2 H2 /= ;
  case: l1 H1 => [l1 | | ] /= H1 ;
  case: l2 H2 => [l2 | | ] /= H2.
  apply Rbar_finite_eq, Rle_antisym ; 
  apply le_epsilon => e He ; set eps := mkposreal e He ;
  apply Rlt_le.
  case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
  case: ((proj1 (H1 (pos_div_2 eps))) (S N)) ;
  case => /= {H1} [ | n] [Hn H1].
  by apply le_Sn_0 in Hn.
  replace l1 with ((l1-e/2)+e/2) by ring.
  replace (l2+e) with ((l2+e/2)+e/2) by field.
  apply Rplus_lt_compat_r.
  apply Rlt_trans with (1 := H1).
  by apply H2, le_S_n.
  case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
  case: ((proj1 (H2 (pos_div_2 eps))) N) => /= {H2} n [Hn H2].
  replace l2 with ((l2-e/2)+e/2) by ring.
  replace (l1+e) with ((l1+e/2)+e/2) by field.
  apply Rplus_lt_compat_r.
  apply Rlt_trans with (1 := H2).
  by apply H1, le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => /= {H1} N H1.
  case: (H2 (l1+1) N) => n [Hn].
  by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (H2 (l1-1)) => {H2} N H2.
  case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ;
  case => [ | n] [Hn] /= .
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  have : False => //.
  case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => {H2} /= N H2.
  case: (H1 (l2+1) (S N)) ;
  case => [ | n] [Hn] /= .
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  by [].
  have : False => //.
  case: (H2 0) => {H2} N H2.
  case: (H1 0 (S N)) ;
  case => [ | n] [Hn] /= .
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  have : False => //.
  case: (H1 (l2-1)) => {H1} N H1.
  case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2} n [Hn].
  by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (H1 0) => {H1} N H1.
  case: (H2 0 N) => {H2} n [Hn].
  by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
  by [].
Qed.

Lemma is_lim_seq_incr_n (u : nat -> R) (N : nat) (l : Rbar) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (n + N)%nat) l.
Proof.
  split.
  elim: N u => [ | N IH] u Hu.
  move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
  apply is_lim_seq_incr_1, IH in Hu.
  move: Hu ; by apply is_lim_seq_ext => n ; by rewrite plus_n_Sm.
  elim: N u => [ | N IH] u Hu.
  move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
  apply is_lim_seq_incr_1, IH.
  move: Hu ; by apply is_lim_seq_ext => n ; by rewrite plus_n_Sm.
Qed.
Lemma ex_lim_seq_incr_n (u : nat -> R) (N : nat) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (n + N)%nat).
Proof.
  split ; move => [l H] ; exists l.
  by apply -> is_lim_seq_incr_n.
  by apply is_lim_seq_incr_n in H.
Qed.
Lemma Lim_seq_incr_n (u : nat -> R) (N : nat) :
  Lim_seq (fun n => u (n + N)%nat) = Lim_seq u.
Proof.
  elim: N u => [ | N IH] u.
  apply Lim_seq_ext => n ; by rewrite plus_0_r.
  rewrite -(Lim_seq_incr_1 u) -(IH (fun n => u (S n))).
  apply Lim_seq_ext => n ; by rewrite plus_n_Sm.
Qed.

(** *** Additive *)

(** Opposite *)

Lemma is_lim_seq_opp (u : nat -> R) (l : Rbar) :
  is_lim_seq u l <-> is_lim_seq (fun n => -u n) (Rbar_opp l).
Proof.
  split ; move => Hu.
  apply is_LimSup_LimInf_lim_seq.
  apply is_LimSup_opp_LimInf_seq.
  by apply is_lim_LimInf_seq.
  apply is_LimInf_opp_LimSup_seq.
  by apply is_lim_LimSup_seq.
  apply is_LimSup_LimInf_lim_seq.
  apply is_LimInf_opp_LimSup_seq.
  by apply is_lim_LimInf_seq.
  apply is_LimSup_opp_LimInf_seq.
  by apply is_lim_LimSup_seq.
Qed.
Lemma ex_lim_seq_opp (u : nat -> R) :
  ex_lim_seq u <-> ex_lim_seq (fun n => -u n).
Proof.
  split ; case => l Hl ; exists (Rbar_opp l).
  by apply -> is_lim_seq_opp.
  apply is_lim_seq_ext with (fun n => - - u n).
  move => n ; by apply Ropp_involutive.
  by apply -> is_lim_seq_opp.
Qed.
Lemma Lim_seq_opp (u : nat -> R) :
  Lim_seq (fun n => - u n) = Rbar_opp (Lim_seq u).
Proof.
  rewrite /Lim_seq.
  rewrite LimSup_seq_opp LimInf_seq_opp.
  case: (LimInf_seq u) => [li | | ] ;
  case: (LimSup_seq u) => [ls | | ] //= ;
  apply f_equal ; field.
Qed.

(** Addition *)

Lemma is_lim_seq_plus (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> 
    is_Rbar_plus l1 l2 (Rbar_plus l1 l2) ->
    is_lim_seq (fun n => u n + v n) (Rbar_plus l1 l2).
Proof.
  wlog: l1 l2 u v / (Rbar_le l1 l2) => [Hw |].
    case: (Rbar_le_dec l1 l2) => Hl.
    by apply Hw.
    rewrite Rbar_plus_comm => Hu Hv ; move/is_Rbar_plus_comm => H.
    apply is_lim_seq_ext with (fun n : nat => v n + u n).
    move => n ; by apply Rplus_comm.
    apply Hw => //.
    by apply Rbar_lt_le, Rbar_not_le_lt.
  case: l1 => [l1 | | ] ; case: l2 => [l2 | | ] //= Hl Hu Hv _ ; try by case: Hl.
  move => eps.
  case: (Hu (pos_div_2 eps)) => {Hu} Nu Hu.
  case: (Hv (pos_div_2 eps)) => {Hv} Nv Hv.
  exists (Nu + Nv)%nat => n Hn.
  replace (u n + v n - (l1 + l2)) with ((u n - l1) + (v n - l2)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite (double_var eps).
  apply Rplus_lt_compat.
  apply Hu ; intuition.
  apply Hv ; intuition.
  move => M.
  case: (Hu (mkposreal _ Rlt_0_1)) => {Hu} /= Nu Hu.
  move: (fun n Hn => proj1 (proj1 (Rabs_lt_between' _ _ _) (Hu n Hn))) => {Hu} Hu.
  case: (Hv (M - (l1 - 1))) => {Hv} Nv Hv.
  exists (Nu + Nv)%nat => n Hn.
  replace M with ((l1 - 1) + (M - (l1 - 1))) by ring.
  apply Rplus_lt_compat.
  apply Hu ; intuition.
  apply Hv ; intuition.
  move => M.
  case: (Hu (M / 2)) => {Hu} Nu Hu.
  case: (Hv (M / 2)) => {Hv} Nv Hv.
  exists (Nu + Nv)%nat => n Hn.
  rewrite (double_var M).
  apply Rplus_lt_compat.
  apply Hu ; intuition.
  apply Hv ; intuition.
  move => M.
  case: (Hv (mkposreal _ Rlt_0_1)) => {Hv} /= Nv Hv.
  move: (fun n Hn => proj2 (proj1 (Rabs_lt_between' _ _ _) (Hv n Hn))) => {Hv} Hv.
  case: (Hu (M - (l2 + 1))) => {Hu} Nu Hu.
  exists (Nu + Nv)%nat => n Hn.
  replace M with ((M - (l2 + 1)) + (l2 + 1)) by ring.
  apply Rplus_lt_compat.
  apply Hu ; intuition.
  apply Hv ; intuition.
  move => M.
  case: (Hu (M / 2)) => {Hu} Nu Hu.
  case: (Hv (M / 2)) => {Hv} Nv Hv.
  exists (Nu + Nv)%nat => n Hn.
  rewrite (double_var M).
  apply Rplus_lt_compat.
  apply Hu ; intuition.
  apply Hv ; intuition.
Qed.
Lemma ex_lim_seq_plus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v 
  -> (exists l, is_Rbar_plus (Lim_seq u) (Lim_seq v) l)
  -> ex_lim_seq (fun n => u n + v n).
Proof.
  case => lu Hu [lv Hv] [l Hl] ; exists (Rbar_plus lu lv).
  apply is_lim_seq_plus.
  apply Hu.
  apply Hv.
  rewrite -(is_lim_seq_unique u lu) //.
  rewrite -(is_lim_seq_unique v lv) //.
  rewrite (Rbar_plus_correct _ _ l) //.
Qed.
Lemma Lim_seq_plus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  (exists l, is_Rbar_plus (Lim_seq u) (Lim_seq v) l)
  -> Lim_seq (fun n => u n + v n) = Rbar_plus (Lim_seq u) (Lim_seq v).
Proof.
  intros (l1,Hu) (l2,Hv) (l,Hl).
  apply is_lim_seq_unique.
  rewrite (is_lim_seq_unique _ _ Hu).
  rewrite (is_lim_seq_unique _ _ Hv).
  apply is_lim_seq_plus with (l1 := l1) (l2 := l2) ; intuition.
  rewrite -(is_lim_seq_unique u l1) //.
  rewrite -(is_lim_seq_unique v l2) //.
  rewrite (Rbar_plus_correct _ _ l) //.
Qed.

(** Substraction *)

Lemma is_lim_seq_minus (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 
  -> (is_Rbar_minus l1 l2 (Rbar_minus l1 l2))
    -> is_lim_seq (fun n => u n - v n) (Rbar_minus l1 l2).
Proof.
  move => H1 H2.
  apply (is_lim_seq_plus _ _ l1 (Rbar_opp l2)).
  exact: H1.
  by apply -> is_lim_seq_opp.
Qed.
Lemma ex_lim_seq_minus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v 
  -> (exists l : Rbar, is_Rbar_minus (Lim_seq u) (Lim_seq v) l)
    -> ex_lim_seq (fun n => u n - v n).
Proof.
  case => lu Hu [lv Hv] [l Hl] ; exists (Rbar_minus lu lv).
  apply is_lim_seq_minus.
  apply Hu.
  apply Hv.
  rewrite -(is_lim_seq_unique u lu) //.
  rewrite -(is_lim_seq_unique v lv) //.
  rewrite /Rbar_minus (Rbar_plus_correct _ _ l) //.
Qed.
Lemma Lim_seq_minus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v -> 
    (exists l : Rbar, is_Rbar_minus (Lim_seq u) (Lim_seq v) l)
    -> Lim_seq (fun n => u n - v n) = Rbar_minus (Lim_seq u) (Lim_seq v).
Proof.
  move => H1 H2 [l H3].
  apply is_lim_seq_unique, is_lim_seq_minus ; try by apply Lim_seq_correct.
  rewrite /Rbar_minus (Rbar_plus_correct _ _ l) //.
Qed.

(** *** Multiplicative *)

(** Inverse *)

Lemma is_lim_seq_inv (u : nat -> R) (l : Rbar) :
  is_lim_seq u l 
    -> l <> 0 -> 
    is_lim_seq (fun n => / u n) (Rbar_inv l).
Proof.
  wlog: l u / (Rbar_lt 0 l) => [Hw |].
    case: (Rbar_lt_le_dec 0 l) => Hl.
    by apply Hw.
    case: Hl => // Hl Hu Hl0.
    apply is_lim_seq_opp.
    replace (Rbar_opp (Rbar_inv l)) with (Rbar_inv (Rbar_opp l))
    by (case: (l) Hl0 => [x | | ] //= Hl0 ; apply f_equal ;
      field ; contradict Hl0 ; by apply f_equal).
    apply is_lim_seq_ext_loc with (fun n => / (- u n)).
    case: l Hl Hu {Hl0} => [l | | ] //= Hl Hu.
    apply Ropp_0_gt_lt_contravar in Hl.
    case: (Hu (mkposreal _ Hl)) => /= {Hu} N H.
    exists N => n Hn.
    field ; apply Rlt_not_eq.
    move: (H n Hn) => {H} H.
    apply Rabs_lt_between' in H.
    apply Rlt_le_trans with (1 := proj2 H), Req_le.
    ring.
    case: (Hu 0) => /= {Hu} N H.
    exists N => n Hn.
    field ; apply Rlt_not_eq.
    by apply H.
    apply Hw.
    apply Rbar_opp_lt.
    rewrite Rbar_opp_involutive /= Ropp_0 ; by apply Hl.
    by apply -> is_lim_seq_opp.
    contradict Hl0.
    rewrite -(Rbar_opp_involutive l) Hl0 /= ; apply f_equal ; ring.
  case: l => [l | | ] //= Hl Hu _.
  move => eps.
  case: (Hu (pos_div_2 (mkposreal _ Hl))) => /= N1 H1.
  move: (fun n Hn => proj1 (proj1 (Rabs_lt_between' _ _ _) (H1 n Hn)))
    => {H1} H1.
  suff He : 0 < eps * Rabs ((l - l / 2) * l).
  case: (Hu (mkposreal _ He)) => {Hu} /= N Hu.
  exists (N1 + N)%nat => n Hn.
  replace (/ u n - / l) with (- (u n - l) / (u n * l)).
Focus 2.
field ; split ; apply Rgt_not_eq => //.
apply Rlt_trans with (l / 2).
apply Rdiv_lt_0_compat ; intuition.
apply Rle_lt_trans with (l - l / 2).
apply Req_le ; field.
apply H1 ; intuition.
  rewrite Rabs_div.
  rewrite Rabs_Ropp.
  apply Rlt_div_l.
  apply Rabs_pos_lt, Rgt_not_eq.
  apply Rmult_lt_0_compat.
  apply Rlt_trans with (l / 2).
  apply Rdiv_lt_0_compat ; intuition.
  apply Rle_lt_trans with (l - l / 2).
  apply Req_le ; field.
  apply H1 ; intuition.
  by [].
  apply Rlt_le_trans with (eps * Rabs ((l - l / 2) * l)).
  apply Hu ; intuition.
  apply Rmult_le_compat_l.
  apply Rlt_le, eps.
  rewrite ?Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  apply Rle_trans with (2 := Rle_abs _).
  rewrite Rabs_pos_eq.
  apply Rlt_le, H1 ; intuition.
  field_simplify ; rewrite Rdiv_1 ; apply Rlt_le, Rdiv_lt_0_compat ; intuition.
  apply Rgt_not_eq.
  apply Rmult_lt_0_compat.
  apply Rlt_trans with (l / 2).
  apply Rdiv_lt_0_compat ; intuition.
  apply Rle_lt_trans with (l - l / 2).
  apply Req_le ; field.
  apply H1 ; intuition.
  by [].
  apply Rmult_lt_0_compat.
  by apply eps.
  apply Rabs_pos_lt, Rgt_not_eq.
  apply Rmult_lt_0_compat.
  field_simplify ; rewrite Rdiv_1 ; apply Rdiv_lt_0_compat ; intuition.
  by [].
  move => eps.
  case: (Hu (/eps)) => {Hu} N Hu.
  exists N => n Hn.
  rewrite Rminus_0_r Rabs_Rinv.
  replace (pos eps) with (/ / eps).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat, eps.
  apply Rabs_pos_lt, Rgt_not_eq, Rlt_trans with (/eps).
  apply Rinv_0_lt_compat, eps.
  by apply Hu.
  apply Rlt_le_trans with (2 := Rle_abs _).
  by apply Hu.
  field ; apply Rgt_not_eq, eps.
  apply Rgt_not_eq, Rlt_trans with (/eps).
  apply Rinv_0_lt_compat, eps.
  by apply Hu.
Qed.
Lemma ex_lim_seq_inv (u : nat -> R) :
  ex_lim_seq u
  -> Lim_seq u <> 0
    -> ex_lim_seq (fun n => / u n).
Proof.
  intros.
  apply Lim_seq_correct in H.
  exists (Rbar_inv (Lim_seq u)).
  by apply is_lim_seq_inv.
Qed.
Lemma Lim_seq_inv (u : nat -> R) :
  ex_lim_seq u -> (Lim_seq u <> 0) 
    -> Lim_seq (fun n => / u n) = Rbar_inv (Lim_seq u).
Proof.
  move => Hl Hu.
  apply is_lim_seq_unique.
  apply is_lim_seq_inv.
  by apply Lim_seq_correct.
  by apply Hu.
Qed.

(** Multiplication *)

Lemma is_lim_seq_mult (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 
  -> is_Rbar_mult l1 l2 (Rbar_mult l1 l2)
    -> is_lim_seq (fun n => u n * v n) (Rbar_mult l1 l2).
Proof.
  wlog: l1 u / (Rbar_le 0 l1) => [Hw | ].
    case: (Rbar_le_lt_dec 0 l1) => Hl1 Hu Hv H.
    by apply Hw.
    apply is_lim_seq_opp.
    rewrite -Rbar_mult_opp_r.
    apply is_lim_seq_ext with (fun n => - u n * v n).
    move => n ; ring.
    apply Hw.
    apply Rbar_opp_le.
    rewrite Rbar_opp_involutive /= Ropp_0.
    by apply Rbar_lt_le.
    by apply -> is_lim_seq_opp.
    by [].
    rewrite Rbar_mult_opp_r.
    by apply is_Rbar_mult_opp_r.
  wlog: l2 v / (Rbar_le 0 l2) => [Hw | ].
    case: (Rbar_le_lt_dec 0 l2) => Hl1 Hl2 Hu Hv H.
    by apply Hw.
    apply is_lim_seq_opp.
    rewrite -Rbar_mult_opp_l.
    apply is_lim_seq_ext with (fun n => u n * - v n).
    move => n ; ring.
    apply Hw.
    apply Rbar_opp_le.
    rewrite Rbar_opp_involutive /= Ropp_0.
    by apply Rbar_lt_le.
    by [].
    by [].
    by apply -> is_lim_seq_opp.
    rewrite Rbar_mult_opp_l.
    by apply is_Rbar_mult_opp_l.
  wlog: l1 l2 u v / (Rbar_le l1 l2) => [Hw | ].
    case: (Rbar_le_lt_dec l1 l2) => Hl Hl1 Hl2 Hu Hv H.
    by apply Hw.
    rewrite Rbar_mult_comm.
    apply is_lim_seq_ext with (fun n => v n * u n).
    move => n ; ring.
    apply Hw.
    by apply Rbar_lt_le.
    by [].
    by [].
    by [].
    by [].
    rewrite Rbar_mult_comm ; by apply is_Rbar_mult_comm.
  case: l1 => [l1 | | ] ; case: l2 => [l2 | | ] /= Hl Hl1 Hl2 Hu Hv H ;
  try (by case: Hl) || (by case: Hl1) || (by case: Hl2).
(* l1 l2 \in R *)
  move => eps.
  case: (Hu (mkposreal _ Rlt_0_1)) => /= Nu1 Hu1.
  move: (fun n Hn => proj1 (Rlt_minus_l _ _ _) (Rle_lt_trans _ _ _ (Rabs_triang_inv _ _) (Hu1 n Hn)))
    => {Hu1} Hu1.
  suff He_u : 0 < (eps / 2) / (1 + Rabs l2).
  case: (Hu (mkposreal _ He_u)) => {Hu} /= Nu Hu.
  suff He_v : 0 < (eps / 2) / (1 + Rabs l1).
  case: (Hv (mkposreal _ He_v)) => {Hv} /= Nv Hv.
  exists (Nu + Nv + Nu1)%nat => n Hn.
  replace (u n * v n - l1 * l2) 
    with ((v n - l2) * u n + (u n - l1) * l2) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite ?Rabs_mult (double_var eps).
  apply Rplus_lt_compat.
  apply Rle_lt_trans with (Rabs (v n - l2) * (1 + Rabs l1)).
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply Rlt_le, Hu1 ; intuition.
  apply Rlt_div_r.
  apply Rlt_le_trans with (1 := Rlt_0_1) ; apply Rminus_le_0 ;
  ring_simplify ; by apply Rabs_pos.
  apply Hv ; intuition.
  apply Rle_lt_trans with (Rabs (u n - l1) * (1 + Rabs l2)).
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply Rminus_le_0 ;
  ring_simplify ; by apply Rle_0_1.
  apply Rlt_div_r.
  apply Rlt_le_trans with (1 := Rlt_0_1) ; apply Rminus_le_0 ;
  ring_simplify ; by apply Rabs_pos.
  apply Hu ; intuition.
  apply Rdiv_lt_0_compat.
  by apply is_pos_div_2.
  apply Rlt_le_trans with (1 := Rlt_0_1) ; apply Rminus_le_0 ;
  ring_simplify ; by apply Rabs_pos.
  apply Rdiv_lt_0_compat.
  by apply is_pos_div_2.
  apply Rlt_le_trans with (1 := Rlt_0_1) ; apply Rminus_le_0 ;
  ring_simplify ; by apply Rabs_pos.
(* l1 \in R et l2 = p_infty *)
  case: Rle_dec H => // Hl2' H.
  case: Rle_lt_or_eq_dec H => // {Hl2 Hl2'} Hl2 _.
  move => M.
  case: (Hu (pos_div_2 (mkposreal _ Hl2))) => {Hu} /= Nu Hu.
  move: (fun n Hn => proj1 (proj1 (Rabs_lt_between' _ _ _) (Hu n Hn)))
    => {Hu} Hu.
  case: (Hv (Rmax 0 (M / (l1 / 2)))) => {Hv} Nv Hv.
  exists (Nu + Nv)%nat => n Hn.
  apply Rle_lt_trans with ((l1 - l1 / 2) * Rmax 0 (M / (l1 / 2))).
  apply Rmax_case_strong => H.
  rewrite Rmult_0_r ; apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
  repeat apply Rdiv_lt_0_compat => //.
  by apply Rlt_R0_R2.
  apply Req_le ; field.
  by apply Rgt_not_eq.
  apply Rmult_le_0_lt_compat.
  field_simplify ; rewrite Rdiv_1 ; apply Rlt_le, Rdiv_lt_0_compat ; intuition.
  apply Rmax_l.
  apply Hu ; intuition.
  apply Hv ; intuition.
  by apply Rbar_finite_le in Hl2.
(* l1 = l2 = p_infty *)
  move => M.
  case: (Hu 1) => {Hu} Nu Hu.
  case: (Hv (Rabs M)) => {Hv} Nv Hv.
  exists (Nu + Nv)%nat => n Hn.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite -(Rmult_1_l (Rabs M)).
  apply Rmult_le_0_lt_compat.
  by apply Rle_0_1.
  by apply Rabs_pos.
  apply Hu ; intuition.
  apply Hv ; intuition.
Qed.
Lemma ex_lim_seq_mult (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v 
  -> (exists l, is_Rbar_mult (Lim_seq u) (Lim_seq v) l)
    -> ex_lim_seq (fun n => u n * v n).
Proof.
  case => lu Hu [lv Hv] [l Hl] ; exists (Rbar_mult lu lv).
  apply is_lim_seq_mult.
  apply Hu.
  apply Hv.
  rewrite -(is_lim_seq_unique u lu) //.
  rewrite -(is_lim_seq_unique v lv) //.
  rewrite (Rbar_mult_correct _ _ l) //.
Qed.
Lemma Lim_seq_mult (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v
  -> (exists l, is_Rbar_mult (Lim_seq u) (Lim_seq v) l)
    -> Lim_seq (fun n => u n * v n) = Rbar_mult (Lim_seq u) (Lim_seq v).
Proof.
  move => H1 H2 [l H3].
  apply is_lim_seq_unique.
  apply is_lim_seq_mult.
  by apply Lim_seq_correct.
  by apply Lim_seq_correct.
  rewrite (Rbar_mult_correct _ _ l) //.
Qed.

(** Multiplication by a scalar *)

Lemma is_lim_seq_scal_l (u : nat -> R) (a : R) (lu : Rbar) :
  is_lim_seq u lu -> 
    is_lim_seq (fun n => a * u n) (Rbar_mult a lu).
Proof.
  move => Hu.
  case: (Req_dec a 0) => Ha.
  rewrite Ha => {a Ha}.
  apply is_lim_seq_ext with (fun n => 0).
  move => n ; by rewrite Rmult_0_l.
  replace (Rbar_mult 0 lu) with (Finite 0).
  by apply is_lim_seq_const.
  case: (lu) => [x | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  
  apply is_lim_seq_mult.
  by apply is_lim_seq_const.
  by [].
  case: (lu) => [x | | ] //=.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  by apply sym_not_eq.
  by apply Rnot_le_lt.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  by apply sym_not_eq.
  by apply Rnot_le_lt.
Qed.
Lemma ex_lim_seq_scal_l (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => a * u n).
Proof.
  move => [l H].
  exists (Rbar_mult a l).
  by apply is_lim_seq_scal_l.
Qed.
Lemma Lim_seq_scal_l (u : nat -> R) (a : R) : 
  Lim_seq (fun n => a * u n) = Rbar_mult a (Lim_seq u).
Proof.
  case: (Req_dec a 0) => [ -> | Ha].
  rewrite -(Lim_seq_ext (fun _ => 0)) /=.
  rewrite Lim_seq_const.
  case: (Lim_seq u) => [x | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  move => n ; by rewrite Rmult_0_l.

  wlog: a u Ha / (0 < a) => [Hw | {Ha} Ha].
    case: (Rlt_le_dec 0 a) => Ha'.
    by apply Hw.
    case: Ha' => // Ha'.
    rewrite -(Lim_seq_ext (fun n => - a * - u n)).
    rewrite -Rbar_mult_opp.
    rewrite -Lim_seq_opp.
    apply Hw.
    contradict Ha ; rewrite -(Ropp_involutive a) Ha ; ring.
    apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
    move => n ; ring.
  rewrite /Lim_seq.
  rewrite {2}/LimSup_seq ; case: ex_LimSup_seq => ls Hs ;
  rewrite {2}/LimInf_seq ; case: ex_LimInf_seq => li Hi ; simpl projT1.
  apply (is_LimSup_seq_scal_pos a) in Hs => //.
  apply (is_LimInf_seq_scal_pos a) in Hi => //.
  rewrite (is_LimSup_seq_unique _ _ Hs).
  rewrite (is_LimInf_seq_unique _ _ Hi).
  case: ls {Hs} => [ls | | ] ; case: li {Hi} => [li | | ] //= ;
  case: (Rle_dec 0 a) (Rlt_le _ _ Ha) => // Ha' _ ;
  case: (Rle_lt_or_eq_dec 0 a Ha') (Rlt_not_eq _ _ Ha) => //= _ _ ;
  apply f_equal ; field.
Qed.
Lemma is_lim_seq_scal_r (u : nat -> R) (a : R) (lu : Rbar) :
  is_lim_seq u lu -> 
    is_lim_seq (fun n => u n * a) (Rbar_mult lu a).
Proof.
  move => Hu.
  apply is_lim_seq_ext with ((fun n : nat => a * u n)) ; try by intuition.
  rewrite Rbar_mult_comm.
  apply is_lim_seq_scal_l.
  by apply Hu.
Qed.
Lemma ex_lim_seq_scal_r (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => u n * a).
Proof.
  move => Hu.
  apply ex_lim_seq_ext with ((fun n : nat => a * u n)) ; try by intuition.
  apply ex_lim_seq_scal_l.
  by apply Hu.
Qed.
Lemma Lim_seq_scal_r (u : nat -> R) (a : R) : 
  Lim_seq (fun n => u n * a) = Rbar_mult (Lim_seq u) a.
Proof.
  rewrite Rbar_mult_comm -Lim_seq_scal_l.
  apply Lim_seq_ext ; by intuition.
Qed.

(** Division *)

Lemma is_lim_seq_div (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l2 <> 0 ->
  is_Rbar_div l1 l2 (Rbar_div l1 l2)
    -> is_lim_seq (fun n => u n / v n) (Rbar_div l1 l2).
Proof.
  intros.
  apply is_lim_seq_mult.
  by [].
  by apply is_lim_seq_inv.
  by [].
Qed.
Lemma ex_lim_seq_div (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v
    -> Lim_seq v <> 0
    -> (exists l, is_Rbar_div (Lim_seq u) (Lim_seq v) l)
    -> ex_lim_seq (fun n => u n / v n).
Proof.
  intros.
  apply Lim_seq_correct in H.
  apply Lim_seq_correct in H0.
  exists (Rbar_div (Lim_seq u) (Lim_seq v)).
  apply is_lim_seq_div.
  by apply H.
  by apply H0.
  by apply H1.
  case: H2 => l H2.
  rewrite /Rbar_div (Rbar_mult_correct _ _ l) //.
Qed.
Lemma Lim_seq_div (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v
    -> (Lim_seq v <> 0) -> 
    (exists l, is_Rbar_div (Lim_seq u) (Lim_seq v) l)
    -> Lim_seq (fun n => u n / v n) = Rbar_div (Lim_seq u) (Lim_seq v).
Proof.
  move => Hl2 H1 H2 H3.
  apply is_lim_seq_unique.
  apply is_lim_seq_div.
  by apply Lim_seq_correct.
  by apply Lim_seq_correct.
  exact: H2.
  case: H3 => l H3.
  rewrite /Rbar_div (Rbar_mult_correct _ _ l) //.
Qed.

(** *** Order *)

Lemma is_lim_seq_le_loc (u v : nat -> R) (l1 l2 : Rbar) : 
  is_lim_seq u l1 -> is_lim_seq v l2
  -> (exists N, forall n, (N <= n)%nat -> u n <= v n)
  -> Rbar_le l1 l2.
Proof.
  move => Hu Hv H.
  apply Rbar_not_lt_le => Hl.
  case: l1 l2 Hu Hv Hl => [lu | | ] ;
  case => [lv | | ] //= Hu Hv Hl.
  
  apply Rminus_lt_0 in Hl.
  case: H => N H.
  case: (Hu (pos_div_2 (mkposreal _ Hl))) => {Hu} /= Nu Hu.
  case: (Hv (pos_div_2 (mkposreal _ Hl))) => {Hv} /= Nv Hv.
  move: (H _ (le_plus_l N (Nu + Nv)%nat)) => {H}.
  apply Rlt_not_le.
  apply Rlt_trans with ((lu + lv) / 2).
  replace ((lu + lv) / 2) with (lv + ((lu - lv) / 2)) by field.
  apply Rabs_lt_between', Hv ; by intuition.
  replace ((lu + lv) / 2) with (lu - ((lu - lv) / 2)) by field.
  apply Rabs_lt_between', Hu ; by intuition.
  
  case: H => N H.
  case: (Hu (mkposreal _ Rlt_0_1)) => {Hu} /= Nu Hu.
  case: (Hv (lu - 1)) => {Hv} /= Nv Hv.
  move: (H _ (le_plus_l N (Nu + Nv)%nat)) => {H}.
  apply Rlt_not_le.
  apply Rlt_trans with (lu - 1).
  apply Hv ; by intuition.
  apply Rabs_lt_between', Hu ; by intuition.
  
  case: H => N H.
  case: (Hu (lv + 1)) => {Hu} /= Nu Hu.
  case: (Hv (mkposreal _ Rlt_0_1)) => {Hv} /= Nv Hv.
  move: (H _ (le_plus_l N (Nu + Nv)%nat)) => {H}.
  apply Rlt_not_le.
  apply Rlt_trans with (lv + 1).
  apply Rabs_lt_between', Hv ; by intuition.
  apply Hu ; by intuition.
  
  case: H => N H.
  case: (Hu 0) => {Hu} /= Nu Hu.
  case: (Hv 0) => {Hv} /= Nv Hv.
  move: (H _ (le_plus_l N (Nu + Nv)%nat)) => {H}.
  apply Rlt_not_le.
  apply Rlt_trans with 0.
  apply Hv ; by intuition.
  apply Hu ; by intuition.
Qed.

Lemma is_lim_seq_le (u v : nat -> R) (l1 l2 : Rbar) : 
  (forall n, u n <= v n) -> is_lim_seq u l1 -> is_lim_seq v l2 -> Rbar_le l1 l2.
Proof.
  move => Heq Hu Hv.
  apply (is_lim_seq_le_loc u v) => //.
  by exists O.
Qed.

Lemma is_lim_seq_le_le (u v w : nat -> R) (l : Rbar) : 
  (forall n, u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
  case: l => [l | | ] /= Hle Hu Hw.
  move => eps.
  case: (Hu eps) => {Hu} N1 Hu.
  case: (Hw eps) => {Hw} N2 Hw.
  exists (N1+N2)%nat => n Hn.
  move: (Hu _ (le_trans _ _ _ (le_plus_l N1 N2) Hn)) => {Hu} Hu.
  move: (Hw _ (le_trans _ _ _ (le_plus_r N1 N2) Hn)) => {Hw} Hw.
  apply Rabs_lt_between' in Hu.
  apply Rabs_lt_between' in Hw.
  apply Rabs_lt_between' ; split.
  by apply Rlt_le_trans with (1 := proj1 Hu), Hle.
  by apply Rle_lt_trans with (2 := proj2 Hw), Hle.
  move => M ; case: (Hu M) => {Hu} N Hu.
  exists N =>n Hn.
  by apply Rlt_le_trans with (2 := proj1 (Hle _)), Hu.
  move => M ; case: (Hw M) => {Hw} N Hw.
  exists N =>n Hn.
  by apply Rle_lt_trans with (1 := proj2 (Hle _)), Hw.
Qed.

Lemma is_lim_seq_le_p_loc (u v : nat -> R) : 
  is_lim_seq u p_infty
  -> (exists N, forall n, (N <= n)%nat -> u n <= v n) 
  -> is_lim_seq v p_infty.
Proof.
  move => Hu H M.
  case: H => N H.
  case: (Hu M) => {Hu} /= Nu Hu.
  exists (N+Nu)%nat => n Hn.
  apply Rlt_le_trans with (u n).
  apply Hu ; by intuition.
  apply H ; by intuition.
Qed.

Lemma is_lim_seq_le_m_loc (u v : nat -> R) : 
  is_lim_seq u m_infty
  -> (exists N, forall n, (N <= n)%nat -> v n <= u n) 
  -> is_lim_seq v m_infty.
Proof.
  move => Hu H M.
  case: H => N H.
  case: (Hu M) => {Hu} /= Nu Hu.
  exists (N+Nu)%nat => n Hn.
  apply Rle_lt_trans with (u n).
  apply H ; by intuition.
  apply Hu ; by intuition.
Qed.

Lemma is_lim_seq_decr_compare (u : nat -> R) (l : R) :
  is_lim_seq u l
  -> (forall n, (u (S n)) <= (u n))
  -> forall n, l <= u n.
Proof.
  move => Hu H n.
  apply Rnot_lt_le => H0.
  apply Rminus_lt_0 in H0.
  case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
  move: (Hu _ (le_plus_r n Nu)).
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rabs_maj2 _).
  rewrite Ropp_minus_distr'.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar.
  elim: (Nu) => [ | m IH].
  rewrite plus_0_r ; by apply Rle_refl.
  rewrite -plus_n_Sm.
  apply Rle_trans with (2 := IH).
  by apply H.
Qed.
Lemma is_lim_seq_incr_compare (u : nat -> R) (l : R) :
  is_lim_seq u l
  -> (forall n, (u n) <= (u (S n)))
  -> forall n, u n <= l.
Proof.
  move => Hu H n.
  apply Rnot_lt_le => H0.
  apply Rminus_lt_0 in H0.
  case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
  move: (Hu _ (le_plus_r n Nu)).
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: (Nu) => [ | m IH].
  rewrite plus_0_r ; by apply Rle_refl.
  rewrite -plus_n_Sm.
  apply Rle_trans with (1 := IH).
  by apply H.
Qed.

Lemma ex_lim_seq_decr (u : nat -> R) :
  (forall n, (u (S n)) <= (u n))
    -> ex_lim_seq u.
Proof.
  move => H.
  exists (Inf_seq u).
  rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
  move => eps ; case: (Hl eps) => Hl1 [N Hl2].
  exists N => n Hn.
  apply Rabs_lt_between' ; split.
  by apply Hl1.
  apply Rle_lt_trans with (2 := Hl2).
  elim: n N {Hl2} Hn => [ | n IH] N Hn.
  rewrite (le_n_O_eq _ Hn).
  apply Rle_refl.
  apply le_lt_eq_dec in Hn.
  case: Hn => [Hn | ->].
  apply Rle_trans with (1 := H _), IH ; intuition.
  by apply Rle_refl.
  move => M ; exists O => n _ ; by apply Hl.
  move => M.
  case: (Hl M) => {Hl} N Hl.
  exists N => n Hn.
  apply Rle_lt_trans with (2 := Hl).
  elim: Hn => [ | {n} n Hn IH].
  by apply Rle_refl.
  apply Rle_trans with (2 := IH).
  by apply H.
Qed.
Lemma ex_lim_seq_incr (u : nat -> R) :
  (forall n, (u n) <= (u (S n)))
    -> ex_lim_seq u.
Proof.
  move => H.
  exists (Sup_seq u).
  rewrite /Sup_seq ; case: ex_sup_seq ; case => [l | | ] //= Hl.
  move => eps ; case: (Hl eps) => Hl1 [N Hl2].
  exists N => n Hn.
  apply Rabs_lt_between' ; split.
  apply Rlt_le_trans with (1 := Hl2).
  elim: Hn => [ | {n} n Hn IH].
  by apply Rle_refl.
  apply Rle_trans with (1 := IH).
  by apply H.
  by apply Hl1.
  move => M.
  case: (Hl M) => {Hl} N Hl.
  exists N => n Hn.
  apply Rlt_le_trans with (1 := Hl).
  elim: Hn => [ | {n} n Hn IH].
  by apply Rle_refl.
  apply Rle_trans with (1 := IH).
  by apply H.
  move => M ; exists O => n Hn ; by apply Hl.
Qed.


Lemma ex_finite_lim_seq_decr (u : nat -> R) (M : R) :
  (forall n, (u (S n)) <= (u n)) -> (forall n, M <= u n)
    -> ex_finite_lim_seq u.
Proof.
  intros.
  apply ex_finite_lim_seq_correct.
  have H1 : ex_lim_seq u.
  exists (real (Inf_seq u)).
  rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
  move => eps ; case: (Hl eps) => Hl1 [N Hl2].
  exists N => n Hn.
  apply Rabs_lt_between' ; split.
  by apply Hl1.
  apply Rle_lt_trans with (2 := Hl2).
  elim: n N {Hl2} Hn => [ | n IH] N Hn.
  rewrite (le_n_O_eq _ Hn).
  apply Rle_refl.
  apply le_lt_eq_dec in Hn.
  case: Hn => [Hn | ->].
  apply Rle_trans with (1 := H _), IH ; intuition.
  by apply Rle_refl.
  move: (Hl (u O) O) => H1 ; by apply Rlt_irrefl in H1.
  case: (Hl M) => {Hl} n Hl.
  apply Rlt_not_le in Hl.
  by move: (Hl (H0 n)).
  split => //.
  apply Lim_seq_correct in H1.
  case: (Lim_seq u) H1 => [l | | ] /= Hu.
  by [].
  case: (Hu (u O)) => {Hu} N Hu.
  move: (Hu N (le_refl _)) => {Hu} Hu.
  contradict Hu ; apply Rle_not_lt.
  elim: N => [ | N IH].
  by apply Rle_refl.
  by apply Rle_trans with (1 := H _).
  case: (Hu M) => {Hu} N Hu.
  move: (Hu N (le_refl _)) => {Hu} Hu.
  contradict Hu ; by apply Rle_not_lt.
Qed.
Lemma ex_finite_lim_seq_incr (u : nat -> R) (M : R) :
  (forall n, (u n) <= (u (S n))) -> (forall n, u n <= M)
    -> ex_finite_lim_seq u.
Proof.
  intros.
  case: (ex_finite_lim_seq_decr (fun n => - u n) (- M)).
  move => n ; by apply Ropp_le_contravar.
  move => n ; by apply Ropp_le_contravar.
  move => l ; move/is_lim_seq_opp => Hu.
  exists (- l) ; move: Hu.
  apply is_lim_seq_ext.
  move => n ; by apply Ropp_involutive.
Qed.

Lemma ex_lim_seq_adj (u v : nat -> R) :
  (forall n, u n <= u (S n)) -> (forall n, v (S n) <= v n)
  -> is_lim_seq (fun n => v n - u n) 0
  -> ex_finite_lim_seq u /\ ex_finite_lim_seq v /\ Lim_seq u = Lim_seq v.
Proof.
  move => Hu Hv H0.
  suff H : forall n, u n <= v n.
  suff Eu : ex_finite_lim_seq u.
    split ; try auto.
  suff Ev : ex_finite_lim_seq v.
    split ; try auto.

  apply is_lim_seq_unique in H0.
  rewrite Lim_seq_minus in H0 ; try by intuition.
  apply ex_finite_lim_seq_correct in Eu.
  apply ex_finite_lim_seq_correct in Ev.
  rewrite -(proj2 Eu) -(proj2 Ev) /= in H0 |- *.
  apply Rbar_finite_eq in H0 ; apply Rbar_finite_eq.
  by apply sym_eq, Rminus_diag_uniq, H0.
  by apply ex_finite_lim_seq_correct.
  by apply ex_finite_lim_seq_correct.
  exists (Rbar_minus (Lim_seq v) (Lim_seq u)).
  apply ex_finite_lim_seq_correct in Eu.
  apply ex_finite_lim_seq_correct in Ev.
  by rewrite -(proj2 Eu) -(proj2 Ev).
  apply ex_finite_lim_seq_decr with (u O) => //.
  move => n ; apply Rle_trans with (2 := H _).
  elim: n => [ | n IH].
  by apply Rle_refl.
  by apply Rle_trans with (2 := Hu _).
  apply ex_finite_lim_seq_incr with (v O) => //.
  move => n ; apply Rle_trans with (1 := H _).
  elim: n => [ | n IH].
  by apply Rle_refl.
  by apply Rle_trans with (1 := Hv _).
  move => n0 ; apply Rnot_lt_le ; move/Rminus_lt_0 => H.
  case: (H0 (mkposreal _ H)) => /= {H0} N H0.
  move: (H0 _ (le_plus_r n0 N)) ; apply Rle_not_lt.
  rewrite Rminus_0_r ; apply Rle_trans with (2 := Rabs_maj2 _).
  rewrite Ropp_minus_distr'.
  apply Rplus_le_compat, Ropp_le_contravar.
  elim: (N) => [ | m IH].
  rewrite plus_0_r ; apply Rle_refl.
  rewrite -plus_n_Sm ; by apply Rle_trans with (2 := Hu _).
  elim: (N) => [ | m IH].
  rewrite plus_0_r ; apply Rle_refl.
  rewrite -plus_n_Sm ; by apply Rle_trans with (1 := Hv _).
Qed.

(** *** Additional limits *)

(** Image by a continuous function *)

Lemma is_lim_seq_continuous (f : R -> R) (u : nat -> R) (l : R) :
  continuity_pt f l -> is_lim_seq u l
  -> is_lim_seq (fun n => f (u n)) (f l).
Proof.
  move => Cf Hu.
  apply is_lim_seq_Un_cv, continuity_seq.
  apply Cf.
  by apply is_lim_seq_Un_cv.
Qed.

(** Absolute value *)

Lemma is_lim_seq_abs (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_lim_seq (fun n => Rabs (u n)) (Rbar_abs l).
Proof.
  case: l => [l | | ] /= Hu.

  move => eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  by apply Rle_lt_trans with (1 := Rabs_triang_inv2 _ _), Hu.
  
  move => M.
  case: (Hu M) => {Hu} N Hu.
  exists N => n Hn.
  by apply Rlt_le_trans with (2 := Rle_abs _), Hu.
  
  move => M.
  case: (Hu (-M)) => {Hu} N Hu.
  exists N => n Hn.
  apply Rlt_le_trans with (2 := Rabs_maj2 _), Ropp_lt_cancel.
  rewrite Ropp_involutive ; by apply Hu.
Qed.
Lemma ex_lim_seq_abs (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => Rabs (u n)).
Proof.
  move => [l Hu].
  exists (Rbar_abs l) ; by apply is_lim_seq_abs.
Qed.
Lemma Lim_seq_abs (u : nat -> R) :
  ex_lim_seq u ->
  Lim_seq (fun n => Rabs (u n)) = Rbar_abs (Lim_seq u).
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_abs.
  by apply Lim_seq_correct.
Qed.

Lemma is_lim_seq_abs_0 (u : nat -> R) :
  is_lim_seq u 0 <-> is_lim_seq (fun n => Rabs (u n)) 0.
Proof.
  split => Hu.
  rewrite -Rabs_R0.
  by apply (is_lim_seq_abs _ 0).
  move => eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  move: (Hu n Hn) ;
  by rewrite ?Rminus_0_r Rabs_Rabsolu.
Qed.

(** Geometric sequences *)

Lemma is_lim_seq_geom (q : R) :
  Rabs q < 1 -> is_lim_seq (fun n => q ^ n) 0.
Proof.
  move => Hq [e He] /=.
  case: (pow_lt_1_zero q Hq e He) => N H.
  exists N => n Hn.
  rewrite Rminus_0_r ; by apply H.
Qed.
Lemma ex_lim_seq_geom (q : R) :
  Rabs q < 1 -> ex_lim_seq (fun n => q ^ n).
Proof.
  move => Hq ; exists 0 ; by apply is_lim_seq_geom.
Qed.
Lemma Lim_seq_geom (q : R) :
  Rabs q < 1 -> Lim_seq (fun n => q ^ n) = 0.
Proof.
  intros.
  apply is_lim_seq_unique.
  by apply is_lim_seq_geom.
Qed.

Lemma is_lim_seq_geom_p (q : R) :
  1 < q -> is_lim_seq (fun n => q ^ n) p_infty.
Proof.
  move => Hq M /=.
  case: (fun Hq => Pow_x_infinity q Hq (M+1)) => [ | N H].
  by apply Rlt_le_trans with (1 := Hq), Rle_abs.
  exists N => n Hn.
  apply Rlt_le_trans with (M+1).
  rewrite -{1}(Rplus_0_r M) ; by apply Rplus_lt_compat_l, Rlt_0_1.
  rewrite -(Rabs_pos_eq (q^n)).
  by apply Rge_le, H.
  by apply pow_le, Rlt_le, Rlt_trans with (1 := Rlt_0_1).
Qed.
Lemma ex_lim_seq_geom_p (q : R) :
  1 < q -> ex_lim_seq (fun n => q ^ n).
Proof.
  move => Hq ; exists p_infty ; by apply is_lim_seq_geom_p.
Qed.
Lemma Lim_seq_geom_p (q : R) :
  1 < q -> Lim_seq (fun n => q ^ n) = p_infty.
Proof.
  intros.
  apply is_lim_seq_unique.
  by apply is_lim_seq_geom_p.
Qed.

Lemma ex_lim_seq_geom_m (q : R) :
  q <= -1 -> ~ ex_lim_seq (fun n => q ^ n).
Proof.
  move => Hq ; case ; case => [l | | ] /= H.
  case: Hq => Hq.
(* ~ is_lim_seq (q^n) l *)
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  move: (fun n Hn => Rabs_lt_between_Rmax _ _ _ (proj1 (Rabs_lt_between' _ _ _) (H n Hn))).
  set M := Rmax (l + 1) (- (l - 1)) => H0.
  case: (fun Hq => Pow_x_infinity q Hq M) => [ | N0 H1].
  rewrite Rabs_left.
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
  apply Rlt_trans with (1 := Hq) ;
  apply Ropp_lt_cancel ;
  rewrite Ropp_involutive Ropp_0 ;
  by apply Rlt_0_1.
  move: (H0 _ (le_plus_l N N0)).
  by apply Rle_not_lt, Rge_le, H1, le_plus_r.
(* ~ is_lim_seq ((-1)^n) l *)
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  rewrite Hq in H => {q Hq}.
  move: (H _ (le_n_2n _)) ; rewrite pow_1_even ; case/Rabs_lt_between' => _ H1.
  have H2 : (N <= S (2 * N))%nat.
    by apply le_trans with (1 := le_n_2n _), le_n_Sn.
  move: (H _ H2) ; rewrite pow_1_odd ; case/Rabs_lt_between' => {H H2} H2 _.
  move: H1 ; apply Rle_not_lt, Rlt_le.
  pattern 1 at 2 ; replace (1) with ((-1)+2) by ring.
  replace (l+1) with ((l-1)+2) by ring.
  by apply Rplus_lt_compat_r.
(* ~ Rbar_is_lim_seq (q^n) p_infty *)
  case: (H 0) => {H} N H.
  have H0 : (N <= S (2 * N))%nat.
    by apply le_trans with (1 := le_n_2n _), le_n_Sn.
  move: (H _ H0) ; apply Rle_not_lt ; rewrite /pow -/pow.
  apply Rmult_le_0_r.
  apply Rle_trans with (1 := Hq), Ropp_le_cancel ;
  rewrite Ropp_involutive Ropp_0 ;
  by apply Rle_0_1.
  apply Ropp_le_contravar in Hq ; rewrite Ropp_involutive in Hq.
  rewrite pow_sqr -Rmult_opp_opp ; apply pow_le, Rmult_le_pos ;
  apply Rle_trans with (2 := Hq), Rle_0_1.
(* ~ Rbar_is_lim_seq (q^n) m_infty *)
  case: (H 0) => {H} N H.
  move: (H _ (le_n_2n _)).
  apply Rle_not_lt.
  apply Ropp_le_contravar in Hq ; rewrite Ropp_involutive in Hq.
  rewrite pow_sqr -Rmult_opp_opp ; apply pow_le, Rmult_le_pos ;
  apply Rle_trans with (2 := Hq), Rle_0_1.
Qed.

(** Rbar_loc_seq is a good sequence *)

Lemma is_lim_seq_Rbar_loc_seq (x : Rbar) :
  is_lim_seq (Rbar_loc_seq x) x.
Proof.
  case: x => [x | | ].
  evar (l : Rbar).
  pattern (Finite x) at 2.
  replace (Finite x) with l.
  apply is_lim_seq_plus.
  by apply is_lim_seq_const.
  apply is_lim_seq_inv.
  apply is_lim_seq_plus.
  by apply is_lim_seq_id.
  by apply is_lim_seq_const.
  by [].
  by [].
  by [].
  rewrite /l /= ; by apply Rbar_finite_eq, Rplus_0_r.
  apply is_lim_seq_id.
  evar (l : Rbar).
  pattern m_infty at 2.
  replace m_infty with l.
  apply -> is_lim_seq_opp ; simpl.
  by apply is_lim_seq_id.
  by [].
Qed.
