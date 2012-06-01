Require Import Reals Markov.
Require Import ssreflect.
Require Import Rbar Rbar_bound Rcomplements.

(** * Sup of a sequence *)

Definition Rbar_is_sup_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), (forall n, Rbar_lt (u n) (Finite (l+eps)))
                                       /\ (exists n, Rbar_lt (Finite (l-eps)) (u n))
    | p_infty => forall M : R, exists n, Rbar_lt (Finite M) (u n)
    | m_infty => forall M : R, forall n, Rbar_lt (u n) (Finite M)
  end.

(** ** Sup and lub *)

Lemma Rbar_sup_seq_lub (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_sup_seq u l -> Rbar_is_lub (fun x => exists n, x = u n) l.
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

Lemma Rbar_lub_sup_seq (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_lub (fun x => exists n, x = u n) l -> Rbar_is_sup_seq u l.
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

(** ** The Sup_seq definition *)

Lemma Rbar_ex_sup_seq (u : nat -> Rbar) : {l : Rbar | Rbar_is_sup_seq u l}.
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
  intros l Hl ; exists l ; apply Rbar_lub_sup_seq ; auto.
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

Definition Rbar_sup_seq (u : nat -> Rbar) := projT1 (Rbar_ex_sup_seq u).

(** ** Equalities and order *)

Lemma Rbar_is_sup_seq_le (u v : nat -> Rbar) {l1 l2 : Rbar} :
  (forall n, Rbar_le (u n) (v n)) 
  -> (Rbar_is_sup_seq u l1) -> (Rbar_is_sup_seq v l2) -> Rbar_le l1 l2.
Proof.
  destruct l1 as [l1 | | ] ; destruct l2 as [l2 | | ] ; intros Hle Hu Hv ;
  case (Rbar_sup_seq_lub _ _ Hu) ; clear Hu ; intros _ Hu ;
  case (Rbar_sup_seq_lub _ _ Hv) ; clear Hv ; intros Hv _ ;
  apply Hu ; intros x (n,Hn) ; rewrite Hn ; clear x Hn ; apply Rbar_le_trans with (1 := Hle _), Hv ; exists n ; auto.
Qed.

Lemma Rbar_is_sup_seq_rw (u v : nat -> Rbar) {l1 l2 : Rbar} :
  (forall n, (u n) = (v n)) 
  -> (Rbar_is_sup_seq u l1) -> (Rbar_is_sup_seq v l2) -> l1 = l2.
Proof.
  intros Heq Hu Hv ; apply Rbar_le_antisym ; 
  [apply (Rbar_is_sup_seq_le u v) | apply (Rbar_is_sup_seq_le v u)] ; auto ;
  intros n ; right ; rewrite Heq ; auto.
Qed.

Lemma Rbar_is_sup_seq_eq (u v : nat -> Rbar) {l : Rbar} :
  (forall n, (u n) = (v n)) -> (Rbar_is_sup_seq u l) -> (Rbar_is_sup_seq v l).
Proof.
  destruct l as [l | | ] ; intros Heq Hl.
  intros eps ; case (Hl eps) ; clear Hl ; intros ub (n, lub) ; split.
  intro n0 ; rewrite <-Heq ; auto.
  exists n ; rewrite <-Heq ; auto.
  intro M ; case (Hl M) ; clear Hl ; intros n Hl ; exists n ; rewrite <-Heq ; auto.
  intros M n ; rewrite <-Heq ; auto.
Qed.

Lemma Rbar_sup_seq_le (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Rbar_sup_seq u) (Rbar_sup_seq v).
Proof.
  intros Heq ; unfold Rbar_sup_seq ;
  case (Rbar_ex_sup_seq u) ; intros l1 Hu ; case (Rbar_ex_sup_seq v) ; simpl ; intros l2 Hv.
  apply (Rbar_is_sup_seq_le u v) ; auto.
Qed.

Lemma Rbar_sup_seq_rw (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) -> Rbar_sup_seq u = Rbar_sup_seq v.
Proof.
  intro Heq ; unfold Rbar_sup_seq ;
  case (Rbar_ex_sup_seq u) ; intros l1 Hu ; case (Rbar_ex_sup_seq v) ; simpl ; intros l2 Hv.
  apply (Rbar_is_sup_seq_rw u v) ; auto.
Qed.

Lemma Rbar_sup_seq_correct (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_sup_seq u l -> Rbar_sup_seq u = l.
Proof.
  move => Hl ; rewrite /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => l0 Hl0 /= ;
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
Lemma Rbar_sup_seq_correct_0 (u : nat -> Rbar) :
  Rbar_is_sup_seq u (Rbar_sup_seq u).
Proof.
  rewrite /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => l Hl //.
Qed.


(** * Inf of a sequence *)

Definition Rbar_is_inf_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), (forall n, Rbar_lt (Finite (l-eps)) (u n))
                                       /\ (exists n, Rbar_lt (u n) (Finite (l+eps)))
    | p_infty => forall M : R, forall n, Rbar_lt (Finite M) (u n)
    | m_infty => forall M : R, exists n, Rbar_lt (u n) (Finite M)
  end.

(** ** Inf and Sup *)

Lemma Rbar_inf_sup_seq (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_inf_seq (fun n => Rbar_opp (u n)) (Rbar_opp l) 
  <-> Rbar_is_sup_seq u l.
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
Lemma Rbar_sup_inf_seq (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_sup_seq (fun n => Rbar_opp (u n)) (Rbar_opp l) 
  <-> Rbar_is_inf_seq u l.
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

(** ** Inf and glb *)

Lemma Rbar_inf_seq_glb (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_inf_seq u l -> Rbar_is_glb (fun x => exists n, x = u n) l.
Proof.
  move => H ;
  apply Rbar_lub_glb ;
  apply (Rbar_is_lub_eq (fun x : Rbar => exists n : nat, x = Rbar_opp (u n))).
  move => x ; split ; case => n Hn ; exists n.
  by rewrite Hn Rbar_opp_involutive.
  by rewrite -Hn Rbar_opp_involutive.
  apply (Rbar_sup_seq_lub (fun n => Rbar_opp (u n)) (Rbar_opp l)) ;
  by apply Rbar_sup_inf_seq.
Qed.

Lemma Rbar_glb_inf_seq (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_glb (fun x => exists n, x = u n) l -> Rbar_is_inf_seq u l.
Proof.
  move => H ;
  apply Rbar_sup_inf_seq ;
  apply Rbar_lub_sup_seq ;
  apply Rbar_glb_lub.
  rewrite Rbar_opp_involutive ;
  apply (Rbar_is_glb_eq (fun x : Rbar => exists n : nat, x = u n)) => // x ;
  split ; case => n Hx ; exists n ; by apply Rbar_opp_eq.
Qed.

(** ** The Inf_seq definition *)

Lemma Rbar_ex_inf_seq (u : nat -> Rbar) : {l : Rbar | Rbar_is_inf_seq u l}.
Proof.
  case : (Rbar_ex_sup_seq (fun n => Rbar_opp (u n))) => l Hl.
  exists (Rbar_opp l) ; apply Rbar_sup_inf_seq ; by rewrite Rbar_opp_involutive.
Qed.

Definition Rbar_inf_seq (u : nat -> Rbar) := projT1 (Rbar_ex_inf_seq u).

(** ** Equalities and order *)

Lemma Rbar_is_inf_seq_le (u v : nat -> Rbar) {l1 l2 : Rbar} :
  (forall n, Rbar_le (u n) (v n)) 
  -> (Rbar_is_inf_seq u l1) -> (Rbar_is_inf_seq v l2) -> Rbar_le l1 l2.
Proof.
  case: l1 => [l1 | | ] ; case: l2 => [l2 | | ] Hle Hu Hv ;
  case: (Rbar_inf_seq_glb _ _ Hu) => {Hu} Hu _ ;
  case: (Rbar_inf_seq_glb _ _ Hv) => {Hv} _ Hv ;
  apply Hv => _ [n ->] ; apply Rbar_le_trans with (2 := Hle _), Hu ; by exists n.
Qed.

Lemma Rbar_is_inf_seq_rw (u v : nat -> Rbar) {l1 l2 : Rbar} :
  (forall n, (u n) = (v n)) 
  -> (Rbar_is_inf_seq u l1) -> (Rbar_is_inf_seq v l2) -> l1 = l2.
Proof.
  move => Heq Hu Hv ; apply Rbar_le_antisym ; 
  [apply (Rbar_is_inf_seq_le u v) | apply (Rbar_is_inf_seq_le v u)] ;
  move => // n ; right ; by rewrite Heq.
Qed.

Lemma Rbar_is_inf_seq_eq (u v : nat -> Rbar) {l : Rbar} :
  (forall n, (u n) = (v n)) -> (Rbar_is_inf_seq u l) -> (Rbar_is_inf_seq v l).
Proof.
  case : l => [l | | ] Heq Hl.
  move => eps ; case: (Hl eps) => {Hl} ub [n lub] ; split.
  move => n0 ; by rewrite -Heq.
  exists n ; by rewrite -Heq.
  move => M n ; by rewrite -Heq.
  move => M ; case: (Hl M) => {Hl} n Hl ; exists n ; by rewrite -Heq.
Qed.

Lemma Rbar_inf_seq_le (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Rbar_inf_seq u) (Rbar_inf_seq v).
Proof.
  move => Heq ; rewrite /Rbar_inf_seq ;
  case: (Rbar_ex_inf_seq u) => l1 Hu ; case: (Rbar_ex_inf_seq v) => /= l2 Hv.
  by apply (Rbar_is_inf_seq_le u v).
Qed.

Lemma Rbar_inf_seq_rw (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) -> Rbar_inf_seq u = Rbar_inf_seq v.
Proof.
  move => Heq ; rewrite /Rbar_inf_seq ;
  case: (Rbar_ex_inf_seq u) => l1 Hu ; case: (Rbar_ex_inf_seq v) => /= l2 Hv.
  by apply (Rbar_is_inf_seq_rw u v).
Qed.

(** * Other proprieties about sup and inf *)

Lemma Rbar_sup_eq_lub (u : nat -> Rbar) Hp Hex :
  Rbar_sup_seq u = Rbar_lub_ne (fun x => exists n, x = u n) Hp Hex.
Proof.
  rewrite /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => /= s Hs.
  rewrite /Rbar_lub_ne ; case: (Rbar_ex_lub_ne _ _ _) => /= l Hl.
  apply (Rbar_is_lub_rw 
    (fun x : Rbar => exists n : nat, x = u n) 
    (fun x : Rbar => exists n : nat, x = u n)) => // ;
  by apply Rbar_sup_seq_lub.
Qed.
Lemma Rbar_inf_eq_glb (u : nat -> Rbar) Hm Hex :
  Rbar_inf_seq u = Rbar_glb_ne (fun x => exists n, x = u n) Hm Hex.
Proof.
  rewrite /Rbar_inf_seq ; case: (Rbar_ex_inf_seq _) => /= s Hs.
  rewrite /Rbar_glb_ne ; case: (Rbar_ex_glb_ne _ _ _) => /= l Hl.
  apply (Rbar_is_glb_rw 
    (fun x : Rbar => exists n : nat, x = u n) 
    (fun x : Rbar => exists n : nat, x = u n)) => // ;
  by apply Rbar_inf_seq_glb.
Qed.

Lemma Rbar_inf_le_sup (u : nat -> Rbar) : Rbar_le (Rbar_inf_seq u) (Rbar_sup_seq u).
Proof.
  rewrite /Rbar_inf_seq ; case: (Rbar_ex_inf_seq _) ; case => [iu | | ] Hiu ;
  rewrite /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) ; case => [su | | ] Hsu /=.
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

Lemma Rbar_inf_opp_sup (u : nat -> Rbar) :
  Rbar_inf_seq u = Rbar_opp (Rbar_sup_seq (fun n => Rbar_opp (u n))).
Proof.
  rewrite /Rbar_inf_seq ; case: (Rbar_ex_inf_seq _) => iu Hiu ;
  rewrite /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => su Hsu /=.
  apply (Rbar_is_inf_seq_rw u u) => // ;
  apply Rbar_sup_inf_seq ; by rewrite Rbar_opp_involutive.
Qed.
Lemma Rbar_sup_opp_inf (u : nat -> Rbar) :
  Rbar_sup_seq u = Rbar_opp (Rbar_inf_seq (fun n => Rbar_opp (u n))).
Proof.
  rewrite /Rbar_inf_seq ; case: (Rbar_ex_inf_seq _) => iu Hiu ;
  rewrite /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => su Hsu /=.
  apply (Rbar_is_sup_seq_rw u u) => // ;
  apply Rbar_inf_sup_seq ; by rewrite Rbar_opp_involutive.
Qed.

(** * Lim sup *)

Definition Rbar_is_limsup_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), 
        (exists N, forall n, (N <= n)%nat -> Rbar_lt (u n) (Finite (l+eps)))
        /\ (forall N, exists n, (N <= n)%nat /\ Rbar_lt (Finite (l-eps)) (u n))
    | p_infty => forall M, forall N, exists n, (N <= n)%nat /\ Rbar_lt (Finite M) (u n)
    | m_infty => forall M, exists N, forall n, (N <= n)%nat -> Rbar_lt (u n) (Finite M)
  end.

Lemma Rbar_limsup_caract_0 (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_inf_seq (fun n => Rbar_sup_seq (fun m => u (n+m)%nat)) l
    -> Rbar_is_limsup_seq u l.
Proof.
  set v := fun n : nat => Rbar_sup_seq (fun m : nat => u (n + m)%nat) ;
  case: l => [l | | ] Hl.
(* l = Finite l *)
  move => e ; set eps := pos_div_2 e ; split.
  case : (Hl eps) => {Hl} _ [N Hl].
  exists N => n Hn ; apply Rbar_le_lt_trans with (y := v N), 
  Rbar_lt_trans with (y := Finite (l+eps)).
  rewrite /v /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => /= vN HvN ; 
  apply Rbar_sup_seq_lub in HvN ; apply HvN.
  exists (n-N)%nat ; by rewrite -le_plus_minus.
  apply Hl.
  rewrite -(Rplus_0_r (l+eps)) ; have : (l + e = l + eps + eps) ; simpl ; first by field.
  move => -> ; apply Rplus_lt_compat_l, is_pos_div_2.
  move => N ; move: (proj1 (Hl eps) N) => {Hl} Hl.
  move : Hl ; rewrite /v /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) ; 
  simpl projT1 ; case => // [vN | ] HvN Hl.
  case: (HvN eps) => {HvN} _ [n HvN].
  exists (N+n)%nat ; intuition.
  apply Rbar_lt_trans with (y := Finite (vN - eps)), HvN.
  have : (l-e = l-eps-eps) ; simpl ; first by field.
  move => -> ; apply Rplus_lt_compat_r, Hl.
  case: (HvN (l - e)) => {HvN} n HvN.
  exists (N + n)%nat ; intuition.
(* l = p_infty *)
  move => M N ; move: (Hl (M+1) N).
  rewrite /v /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) ; simpl projT1 ; 
  case => // [vN | ] HvN Hm.
  case: (HvN (mkposreal _ Rlt_0_1)) => {HvN} _ [n HvN] ; exists (N+n)%nat ; intuition.
  apply Rbar_lt_trans with (y := Finite (vN-1)), HvN ;
  have : (M = M+1-1) ; first by ring.
  move => -> ; apply Rplus_lt_compat_r, Hm.
  case: (HvN M) => n Hn ; exists (N+n)%nat ; intuition.
(* l = m_infty *)
  move => M ; case: (Hl M) => {Hl} N HvN ; exists N => n Hn.
  move: HvN ; rewrite /v /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) ; simpl projT1 => vN HvN HN.
  apply Rbar_sup_seq_lub in HvN ; apply Rbar_le_lt_trans with (y := vN), HN.
  apply (proj1 HvN) ; exists (n-N)%nat ; by rewrite -le_plus_minus.
Qed.
Lemma Rbar_limsup_caract_1 (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_limsup_seq u l
  -> Rbar_is_inf_seq (fun n => Rbar_sup_seq (fun m => u (n+m)%nat)) l.
Proof.
  set v := fun n : nat => Rbar_sup_seq (fun m : nat => u (n + m)%nat) ;
  case: l => [l | | ] Hl.
(* l = Finite l *)
  move => eps ; split.
  case : (Hl eps) => {Hl} _ Hl N ; case: (Hl N) => {Hl} n [Hn Hl].
  rewrite /v /Rbar_sup_seq ; case (Rbar_ex_sup_seq _) ; case => // [vN | ] HvN ; simpl projT1 ;
  apply Rbar_lt_le_trans with (y := u n) => // ;
  apply Rbar_sup_seq_lub in HvN ; apply HvN ; exists (n-N)%nat ; by rewrite -le_plus_minus.
  case : (Hl (pos_div_2 eps)) => {Hl} [[N Hl] _].
  exists N ; rewrite /v /Rbar_sup_seq ; case (Rbar_ex_sup_seq _) ; 
  case => // [vN | ] HvN ; simpl projT1.
  apply Rbar_le_lt_trans with (y := Finite (l+eps/2)) => //.
  apply Rbar_sup_seq_lub in HvN ; apply (proj2 HvN) => _ [n ->].
  apply Rbar_lt_le, Hl ; intuition.
  have : (l+eps = l+eps/2 + eps/2) ; first by field.
  move => -> ; rewrite -{1}(Rplus_0_r (l+eps/2)) ; apply Rplus_lt_compat_l, is_pos_div_2.
  apply Rbar_le_lt_trans with (y := Finite (l+eps/2)) => //.
  apply Rbar_sup_seq_lub in HvN ; apply (proj2 HvN) => _ [n ->].
  apply Rbar_lt_le, Hl ; intuition.
  have : (l+eps = l+eps/2 + eps/2) ; first by field.
  move => -> ; rewrite -{1}(Rplus_0_r (l+eps/2)) ; apply Rplus_lt_compat_l, is_pos_div_2.
(* l = p_infty *)
  move => M N ; case : (Hl M N) => {Hl} n [Hn Hl].
  apply Rbar_lt_le_trans with (y := u n) => // ; rewrite /v /Rbar_sup_seq ; 
  case: (Rbar_ex_sup_seq _) => vN HvN ; simpl projT1 ;
  apply Rbar_sup_seq_lub in HvN ; apply HvN ; exists (n-N)%nat ; by rewrite -le_plus_minus.
(* l = m_infty *)
  move => M ; case : (Hl (M - 1)) => {Hl} N Hl ; exists N ;
  rewrite /v /Rbar_sup_seq ; case: (Rbar_ex_sup_seq _) => vN HvN ; simpl projT1.
  apply Rbar_sup_seq_lub in HvN ; apply Rbar_le_lt_trans with (y := Finite (M-1)).
  apply HvN => _ [n ->] ; apply Rbar_lt_le, Hl ; intuition.
  rewrite -{2}(Rplus_0_r M) ; apply Rplus_lt_compat_l, Ropp_lt_gt_0_contravar, Rlt_0_1.
Qed.

Lemma Rbar_ex_limsup_seq (u : nat -> Rbar) : {l : Rbar | Rbar_is_limsup_seq u l}.
Proof.
  case: (Rbar_ex_inf_seq (fun n => Rbar_sup_seq (fun m => u (n+m)%nat))) => l Hl ;
  exists l ; apply Rbar_limsup_caract_0, Hl.
Qed.

Definition Rbar_limsup_seq (u : nat -> Rbar) := projT1 (Rbar_ex_limsup_seq u).

(** ** LimSup order *)

Lemma Rbar_is_limsup_leq (u v : nat -> Rbar) (l1 l2 : Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_is_limsup_seq u l1
  -> Rbar_is_limsup_seq v l2 -> Rbar_le l1 l2.
Proof.
  move => Huv ; move/Rbar_limsup_caract_1 => Hl1 ; move/Rbar_limsup_caract_1 => Hl2.
  apply (Rbar_is_inf_seq_le (fun n : nat => Rbar_sup_seq (fun m : nat => u (n + m)%nat)) 
    (fun n : nat => Rbar_sup_seq (fun m : nat => v (n + m)%nat))) => // n.
  apply Rbar_sup_seq_le => m //.
Qed.

Lemma Rbar_is_limsup_eq (u v : nat -> Rbar) (l1 l2 : Rbar) :
  (forall n, (u n) = (v n)) -> Rbar_is_limsup_seq u l1
  -> Rbar_is_limsup_seq v l2 -> l1 = l2.
Proof.
  move => Huv Hl1 Hl2 ; apply Rbar_le_antisym.
  apply (Rbar_is_limsup_leq u v) => // n ; by right.
  apply (Rbar_is_limsup_leq v u) => // n ; by right.
Qed.

Lemma Rbar_limsup_leq (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Rbar_limsup_seq u) (Rbar_limsup_seq v).
Proof.
  move => Huv ; rewrite /Rbar_limsup_seq ; case (Rbar_ex_limsup_seq u) => l1 Hl1 ;
  case (Rbar_ex_limsup_seq v) => l2 Hl2 /= ; by apply (Rbar_is_limsup_leq u v).
Qed.

Lemma Rbar_limsup_eq (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) -> Rbar_limsup_seq u = Rbar_limsup_seq v.
Proof.
  move => Huv ; rewrite /Rbar_limsup_seq ; case (Rbar_ex_limsup_seq u) => l1 Hl1 ;
  case (Rbar_ex_limsup_seq v) => l2 Hl2 /= ; by apply (Rbar_is_limsup_eq u v).
Qed.



Lemma Rbar_limsup_seq_shift: forall u k,
   (Rbar_limsup_seq u  = Rbar_limsup_seq (fun n => u (n+k)%nat)).
intros u k.
unfold Rbar_limsup_seq at 1.
case (Rbar_ex_limsup_seq u).
intros x Hx; simpl.
assert (Rbar_is_limsup_seq (fun n : nat => u (n + k)%nat) x).
revert Hx; case x.
(* . *)
simpl; intros r H eps.
specialize (H eps).
split.
destruct H as ((N1,H1),_).
exists N1.
intros n Hn.
apply H1.
now apply le_plus_trans.
intros N.
destruct H as (_,H1).
destruct (H1 (N+k)%nat) as (m,(Hm1,Hm2)).
exists (m-k)%nat; split.
omega.
replace (m-k+k)%nat with m.
exact Hm2.
omega.
(* . *)
simpl.
intros H M N.
destruct (H M (N+k)%nat) as (m,(Hm1,Hm2)).
exists (m-k)%nat; split.
omega.
replace (m-k+k)%nat with m.
exact Hm2.
omega.
(* . *)
simpl.
intros H M.
destruct (H M) as (m, Hm).
exists m.
intros n Hn.
apply Hm.
now apply le_plus_trans.
(* *)
unfold Rbar_limsup_seq; case (Rbar_ex_limsup_seq (fun n : nat => u (n + k)%nat)).
intros y Hy; simpl.
apply: (Rbar_is_limsup_eq _ _ _ _ _ H Hy).
easy.
Qed.



Lemma Rbar_limsup_seq_eq_ge: forall u v,
  (exists N, forall n, (N <= n)%nat -> (u n) = (v n)) -> Rbar_limsup_seq u = Rbar_limsup_seq v.
intros u v (N,H).
rewrite (Rbar_limsup_seq_shift u N). 
rewrite (Rbar_limsup_seq_shift v N).
apply Rbar_limsup_eq.
intros n; apply H.
now apply le_plus_r.
Qed.





(** * Lim inf *)

Definition Rbar_is_liminf_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), 
        (exists N, forall n, (N <= n)%nat -> Rbar_lt (Finite (l-eps)) (u n))
        /\ (forall N, exists n, (N <= n)%nat /\ Rbar_lt (u n) (Finite (l+eps)))
    | p_infty => forall M, exists N, forall n, (N <= n)%nat -> Rbar_lt (Finite M) (u n)
    | m_infty => forall M, forall N, exists n, (N <= n)%nat /\ Rbar_lt (u n) (Finite M)
  end.

(** ** Liminf and Limsup *)

Lemma Rbar_is_liminf_limsup (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_liminf_seq (fun n => Rbar_opp (u n)) (Rbar_opp l) <->
    Rbar_is_limsup_seq u l.
Proof.
  case: l => [l | | ] ; split => Hl.
(* Finite 1 *)
  move => eps ; case: (Hl eps) => [[N Hli] Hls] ; split.
  exists N => n Hn ; apply Rbar_opp_lt ;
  rewrite /= Ropp_plus_distr ; by apply Hli.
  move => N0 ; case: (Hls N0) => {Hls} n [Hn Hls] ;
  exists n ; split => // ; apply Rbar_opp_lt ;
  by rewrite /= Ropp_minus_distr.
(* Finite 2 *)
  move => eps ; case: (Hl eps) => [[N Hli] Hls] ; split.
  exists N => n Hn ; apply Rbar_opp_lt ;
  rewrite /= Ropp_plus_distr !Ropp_involutive Rbar_opp_involutive ; by apply Hli.
  move => N0 ; case: (Hls N0) => {Hls} n [Hn Hls] ;
  exists n ; split => // ; apply Rbar_opp_lt.
  by rewrite /= Rbar_opp_involutive Ropp_plus_distr Ropp_involutive.
(* p_infty 1 *)
  move => M N ; case: (Hl (-M) N) => {Hl} n [Hn Hl] ; exists n ; split => // ;
  by apply Rbar_opp_lt.
(* p_infty 2 *)
  move => M N ; case: (Hl (-M) N) => {Hl} n [Hn Hl] ; exists n ; split => // ;
  apply Rbar_opp_lt ; by rewrite Rbar_opp_involutive.
(* m_infty 1 *)
  move => M ; case: (Hl (-M)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt, Hl, Hn.
(* m_infty 2 *)
  move => M ; case: (Hl (-M)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt ; rewrite Rbar_opp_involutive ; apply Hl, Hn.
Qed.

Lemma Rbar_is_limsup_liminf (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_limsup_seq (fun n => Rbar_opp (u n)) (Rbar_opp l) <->
    Rbar_is_liminf_seq u l.
Proof.
  case: l => [l | | ] ; split => Hl.
(* Finite 1 *)
  move => eps ; case: (Hl eps) => [[N Hli] Hls] ; split.
  exists N => n Hn ; apply Rbar_opp_lt ;
  rewrite /= Ropp_plus_distr Ropp_involutive ; by apply Hli.
  move => N0 ; case: (Hls N0) => {Hls} n [Hn Hls] ;
  exists n ; split => // ; apply Rbar_opp_lt ;
  by rewrite /= Ropp_plus_distr.
(* Finite 2 *)
  move => eps ; case: (Hl eps) => [[N Hli] Hls] ; split.
  exists N => n Hn ; apply Rbar_opp_lt ;
  rewrite /= Ropp_plus_distr !Ropp_involutive Rbar_opp_involutive ; by apply Hli.
  move => N0 ; case: (Hls N0) => {Hls} n [Hn Hls] ;
  exists n ; split => // ; apply Rbar_opp_lt.
  by rewrite /= Rbar_opp_involutive Ropp_plus_distr ?Ropp_involutive.
(* p_infty 1 *)
  move => M ; case: (Hl (-M)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt, Hl, Hn.
(* p_infty 2 *)
  move => M ; case: (Hl (-M)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt ; rewrite Rbar_opp_involutive ; apply Hl, Hn.
(* m_infty 1 *)
  move => M N ; case: (Hl (-M) N) => {Hl} n [Hn Hl] ; exists n ; split => // ;
  by apply Rbar_opp_lt.
(* m_infty 2 *)
  move => M N ; case: (Hl (-M) N) => {Hl} n [Hn Hl] ; exists n ; split => // ;
  apply Rbar_opp_lt ; by rewrite Rbar_opp_involutive.
Qed.

(** ** Lim inf caract *)

Lemma Rbar_liminf_caract_0 (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_sup_seq (fun n => Rbar_inf_seq (fun m => u (n+m)%nat)) l
    -> Rbar_is_liminf_seq u l.
Proof.
  move => Hsi ; apply Rbar_is_limsup_liminf, Rbar_limsup_caract_0.
  apply Rbar_sup_inf_seq, 
  (Rbar_is_sup_seq_eq (fun n : nat => Rbar_inf_seq (fun m : nat => u (n + m)%nat))).
  move => n ; apply Rbar_inf_opp_sup.
  by rewrite Rbar_opp_involutive.
Qed.
Lemma Rbar_liminf_caract_1 (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_liminf_seq u l
  -> Rbar_is_sup_seq (fun n => Rbar_inf_seq (fun m => u (n+m)%nat)) l.
Proof.
  move => Hsi.
  apply Rbar_inf_sup_seq.
  apply (Rbar_is_inf_seq_eq (fun n : nat =>  (Rbar_sup_seq (fun m : nat => (fun n => Rbar_opp (u n)) (n + m)%nat)))).
  move => n ; rewrite Rbar_inf_opp_sup ; by rewrite Rbar_opp_involutive.
  apply (Rbar_limsup_caract_1 (fun n => Rbar_opp (u n))) ;
  by apply Rbar_is_limsup_liminf.
Qed.

(** ** The function Liminf *)

Lemma Rbar_ex_liminf_seq (u : nat -> Rbar) : {l : Rbar | Rbar_is_liminf_seq u l}.
Proof.
  case: (Rbar_ex_sup_seq (fun n => Rbar_inf_seq (fun m => u (n+m)%nat))) => l Hl ;
  exists l ; apply Rbar_liminf_caract_0, Hl.
Qed.

Definition Rbar_liminf_seq (u : nat -> Rbar) := projT1 (Rbar_ex_liminf_seq u).

(** ** LimSup order *)

Lemma Rbar_is_liminf_leq (u v : nat -> Rbar) (l1 l2 : Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_is_liminf_seq u l1
  -> Rbar_is_liminf_seq v l2 -> Rbar_le l1 l2.
Proof.
  move => Huv ; move/Rbar_liminf_caract_1 => Hl1 ; move/Rbar_liminf_caract_1 => Hl2.
  apply (Rbar_is_sup_seq_le (fun n : nat => Rbar_inf_seq (fun m : nat => u (n + m)%nat)) 
    (fun n : nat => Rbar_inf_seq (fun m : nat => v (n + m)%nat))) => // n.
  apply Rbar_inf_seq_le => m //.
Qed.

Lemma Rbar_is_liminf_eq (u v : nat -> Rbar) (l1 l2 : Rbar) :
  (forall n, (u n) = (v n)) -> Rbar_is_liminf_seq u l1
  -> Rbar_is_liminf_seq v l2 -> l1 = l2.
Proof.
  move => Huv Hl1 Hl2 ; apply Rbar_le_antisym.
  apply (Rbar_is_liminf_leq u v) => // n ; by right.
  apply (Rbar_is_liminf_leq v u) => // n ; by right.
Qed.

Lemma Rbar_liminf_leq (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) -> Rbar_le (Rbar_liminf_seq u) (Rbar_liminf_seq v).
Proof.
  move => Huv ; rewrite /Rbar_liminf_seq ; case (Rbar_ex_liminf_seq u) => l1 Hl1 ;
  case (Rbar_ex_liminf_seq v) => l2 Hl2 /= ; by apply (Rbar_is_liminf_leq u v).
Qed.

Lemma Rbar_liminf_eq (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) -> Rbar_liminf_seq u = Rbar_liminf_seq v.
Proof.
  move => Huv ; rewrite /Rbar_liminf_seq ; case (Rbar_ex_liminf_seq u) => l1 Hl1 ;
  case (Rbar_ex_liminf_seq v) => l2 Hl2 /= ; by apply (Rbar_is_liminf_eq u v).
Qed.

(** * Limit *)

Definition Rbar_is_lim_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall (eps : posreal), (exists N, forall n, (N <= n)%nat -> 
        Rbar_lt (Finite (l-eps)) (u n) /\ Rbar_lt (u n) (Finite (l+eps)))
    | p_infty => forall M, exists N, forall n, (N <= n)%nat -> Rbar_lt (Finite M) (u n)
    | m_infty => forall M, exists N, forall n, (N <= n)%nat -> Rbar_lt (u n) (Finite M)
  end.
Definition Rbar_ex_lim_seq (u : nat -> Rbar) := exists l, Rbar_is_lim_seq u l.
Definition Rbar_lim_seq (u : nat -> Rbar) := Rbar_limsup_seq u.

(** ** limsup, liminf and limit *)
Lemma Rbar_is_lim_limsup (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_lim_seq u l -> Rbar_is_limsup_seq u l.
Proof.
  case: l => [l | | ] Hl ; move => M ; case: (Hl M) => {Hl} N Hl.
(* l = Finite l *)
  split.
  exists N => n Hn ; by apply Hl.
  move => N0 ; exists (N + N0)%nat ; intuition ; apply Hl ; intuition.
(* l = p_infty *)  
  move => N0 ; exists (N + N0)%nat ; intuition ; apply Hl ; intuition.
(* l = m_infty *)
  exists N => n Hn ; by apply Hl.
Qed.

Lemma Rbar_is_lim_liminf (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_lim_seq u l -> Rbar_is_liminf_seq u l.
Proof.
  case: l => [l | | ] Hl ; move => M ; case: (Hl M) => {Hl} N Hl.
(* l = Finite l *)
  split.
  exists N => n Hn ; by apply Hl.
  move => N0 ; exists (N + N0)%nat ; intuition ; apply Hl ; intuition.
(* l = p_infty *)
  exists N => n Hn ; by apply Hl.
(* l = m_infty *)  
  move => N0 ; exists (N + N0)%nat ; intuition ; apply Hl ; intuition.
Qed.

Lemma Rbar_is_limsup_liminf_lim (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_limsup_seq u l -> Rbar_is_liminf_seq u l -> Rbar_is_lim_seq u l.
Proof.
  case: l => [l | | ] Hls Hli.
(* l = Finite l *)
  move => eps ; case: (Hls eps) => {Hls} [[N Hls] _] ; 
  case: (Hli eps) => {Hli} [[N' Hli] _] ; exists (N+N')%nat => n Hn ; split.
  apply Hli ; apply le_trans with (2 := Hn) ; intuition.
  apply Hls ; apply le_trans with (2 := Hn) ; intuition.
(* l = p_infty *)
  move => M ; case: (Hli M) => {Hli} N Hli ; by exists N.
(* l = m_infty *)
  move => M ; case: (Hls M) => {Hls} N Hls ; by exists N.
Qed.

Lemma Rbar_is_lim_correct (u : nat -> Rbar) (l : Rbar) :
  Rbar_is_lim_seq u l -> Rbar_lim_seq u = l.
Proof.
  move => Hl ; rewrite /Rbar_lim_seq /Rbar_limsup_seq ; 
  case Rbar_ex_limsup_seq => l' Hl' /= ;
  apply (Rbar_is_limsup_eq u u) => // ;
  by apply Rbar_is_lim_limsup.
Qed.

Lemma Rbar_ex_lim_is_lim (u : nat -> Rbar) :
  Rbar_ex_lim_seq u -> Rbar_is_lim_seq u (Rbar_lim_seq u).
Proof.
  case => l Hl ; have H : (Rbar_lim_seq u = l).
  by apply Rbar_is_lim_correct.
  by rewrite H.
Qed.

(** ** Limit and opposite *)

Lemma Rbar_is_lim_seq_opp (u : nat -> Rbar) l : 
  Rbar_is_lim_seq u l <-> Rbar_is_lim_seq (fun n => Rbar_opp (u n)) (Rbar_opp l).
Proof.
  case: l => [l | | ] ; rewrite /Rbar_is_lim_seq ; simpl Rbar_opp ; 
  split => Hl e.
  case: (Hl e) => {Hl} N Hl ; exists N => n Hn ;
  have: ((- l - e) = -(l+e)) ; first by ring.
  move => -> ; have: ((- l + e) = -(l-e)) ; first by ring.
  move => -> ; split ; apply Rbar_opp_lt ; rewrite /= ?Ropp_involutive ?Rbar_opp_involutive ;
  by apply Hl.
  case: (Hl e) => {Hl} N Hl ; exists N => n Hn ;
  have: (-(- l - e) = (l+e)) ; first by ring.
  move => <- ; have: (-(- l + e) = (l-e)) ; first by ring.
  move => <- ; split ; apply Rbar_opp_lt ; rewrite /= ?Ropp_involutive ?Rbar_opp_involutive ;
  by apply Hl.
  case: (Hl (-e)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt ; rewrite /= ?Rbar_opp_involutive ; by apply Hl.
  case: (Hl (-e)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt ; rewrite /= ?Rbar_opp_involutive ; by apply Hl.
  case: (Hl (-e)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt ; rewrite /= ?Rbar_opp_involutive ; by apply Hl.
  case: (Hl (-e)) => {Hl} N Hl ; exists N => n Hn ;
  apply Rbar_opp_lt ; rewrite /= ?Rbar_opp_involutive ; by apply Hl.
Qed.
