Require Import Reals Markov.
Require Import ssreflect.
Require Import Rbar Rbar_bound Rcomplements Floor.

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

(** * Other properties about sup and inf *)

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



Lemma Rbar_limsup_seq_ext_loc : forall u v,
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

Lemma Rbar_liminf_seq_shift: forall u k,
   (Rbar_liminf_seq u  = Rbar_liminf_seq (fun n => u (n+k)%nat)).
intros u k.
unfold Rbar_liminf_seq at 1.
case (Rbar_ex_liminf_seq u).
intros x Hx; simpl.
assert (Rbar_is_liminf_seq (fun n : nat => u (n + k)%nat) x).
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
intros H M.
destruct (H M) as (m, Hm).
exists m.
intros n Hn.
apply Hm.
now apply le_plus_trans.
(* . *)
simpl.
intros H M N.
destruct (H M (N+k)%nat) as (m,(Hm1,Hm2)).
exists (m-k)%nat; split.
omega.
replace (m-k+k)%nat with m.
exact Hm2.
omega.
(* *)
unfold Rbar_liminf_seq; case (Rbar_ex_liminf_seq (fun n : nat => u (n + k)%nat)).
intros y Hy; simpl.
apply: (Rbar_is_liminf_eq _ _ _ _ _ H Hy).
easy.
Qed.

Lemma Rbar_liminf_seq_ext_loc : forall u v,
  (exists N, forall n, (N <= n)%nat -> (u n) = (v n)) -> Rbar_liminf_seq u = Rbar_liminf_seq v.
intros u v (N,H).
rewrite (Rbar_liminf_seq_shift u N). 
rewrite (Rbar_liminf_seq_shift v N).
apply Rbar_liminf_eq.
intros n; apply H.
now apply le_plus_r.
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
Definition Rbar_lim_seq (u : nat -> Rbar) := 
  Rbar_div_pos (Rbar_plus (Rbar_limsup_seq u) (Rbar_liminf_seq u)) (mkposreal 2 (Rlt_R0_R2)).

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
  move => Hl ; rewrite /Rbar_lim_seq /Rbar_limsup_seq /Rbar_liminf_seq ; 
  case Rbar_ex_limsup_seq => ls Hls /= ; case Rbar_ex_liminf_seq => li Hli /=. 
  replace ls with l.
  replace li with l.
  case: (l) => //= l' ; apply Rbar_finite_eq ; field.
  apply Rbar_is_lim_liminf in Hl ;
  apply (Rbar_is_liminf_eq u u) => //.
  apply Rbar_is_lim_limsup in Hl ;
  apply (Rbar_is_limsup_eq u u) => //.
Qed.

Lemma Rbar_ex_lim_is_lim (u : nat -> Rbar) :
  Rbar_ex_lim_seq u -> Rbar_is_lim_seq u (Rbar_lim_seq u).
Proof.
  case => l Hl ; have H : (Rbar_lim_seq u = l).
  by apply Rbar_is_lim_correct.
  by rewrite H.
Qed.

Lemma Rbar_ex_lim_seq_dec (u : nat -> Rbar) :
  {Rbar_ex_lim_seq u} + {~Rbar_ex_lim_seq u}.
Proof.
  case: (Rbar_eq_dec (Rbar_limsup_seq u) (Rbar_liminf_seq u)) ;
  rewrite /Rbar_limsup_seq ;
  case: Rbar_ex_limsup_seq => /= ls Hs ;
  rewrite /Rbar_liminf_seq ;
  case: Rbar_ex_liminf_seq => /= li Hi Heq.
  left.
  rewrite Heq in Hs => {ls Heq}.
  exists li ; by apply Rbar_is_limsup_liminf_lim.
  right ; contradict Heq.
  case: Heq => l Hl.
  set Hs0 := Rbar_is_lim_limsup u l Hl.
  set Hi0 := Rbar_is_lim_liminf u l Hl.
  rewrite (Rbar_is_limsup_eq u u ls l) => //.
  rewrite (Rbar_is_liminf_eq u u li l) => //.
Qed.

(** ** Operations *)

(** Extentionality *)

Lemma Rbar_is_lim_seq_ext_loc (u v : nat -> Rbar) (l : Rbar) :
  (exists N, forall n, (N <= n)%nat -> (u n) = (v n)) 
  -> Rbar_is_lim_seq u l -> Rbar_is_lim_seq v l.
Proof.
  case: l => [l | | ] [N1 Heq] Hu M ;
  case: (Hu M) => {Hu} N2 Hu ; exists (N1 + N2)%nat => n Hn ;
  rewrite -Heq ; intuition ; apply Hu ; intuition.
Qed.
Lemma Rbar_ex_lim_seq_ext_loc (u v : nat -> Rbar) :
  (exists N, forall n, (N <= n)%nat -> (u n) = (v n)) 
  -> Rbar_ex_lim_seq u -> Rbar_ex_lim_seq v.
Proof.
  move => Heq [l Hu] ; exists l ; by apply Rbar_is_lim_seq_ext_loc with u.
Qed.
Lemma Rbar_lim_seq_ext_loc : forall u v,
  (exists N, forall n, (N <= n)%nat -> (u n) = (v n))
    -> Rbar_lim_seq u = Rbar_lim_seq v.
Proof.
  intros.
  rewrite /Rbar_lim_seq.
  apply (f_equal (fun x => Rbar_div_pos x _)).
  apply f_equal2.
  by apply Rbar_limsup_seq_ext_loc.
  by apply Rbar_liminf_seq_ext_loc.
Qed.

Lemma Rbar_is_lim_seq_ext (u v : nat -> Rbar) (l : Rbar) :
  (forall n, (u n) = (v n)) 
  -> Rbar_is_lim_seq u l -> Rbar_is_lim_seq v l.
Proof.
  move => Heq Hu ; apply Rbar_is_lim_seq_ext_loc with u.
  by exists O.
  by [].
Qed.
Lemma Rbar_ex_lim_seq_ext (u v : nat -> Rbar) :
  (forall n, (u n) = (v n)) 
  -> Rbar_ex_lim_seq u -> Rbar_ex_lim_seq v.
Proof.
  move => Heq [l Hu] ; exists l ; by apply Rbar_is_lim_seq_ext with u.
Qed.
Lemma Rbar_lim_seq_ext : forall u v,
  (forall n, (u n) = (v n)) -> Rbar_lim_seq u = Rbar_lim_seq v.
Proof.
  intros.
  apply Rbar_lim_seq_ext_loc.
  by exists O.
Qed.

(** Additive *)

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
Lemma Rbar_ex_lim_seq_opp (u : nat -> Rbar) :
  Rbar_ex_lim_seq u <-> Rbar_ex_lim_seq (fun n => Rbar_opp (u n)).
Proof.
  split ; case => l Hu ; exists (Rbar_opp l).
  by apply -> Rbar_is_lim_seq_opp.
  apply Rbar_is_lim_seq_opp ; by rewrite Rbar_opp_involutive.
Qed.
Lemma Rbar_lim_seq_opp (u : nat -> Rbar) :
  Rbar_lim_seq (fun n => Rbar_opp (u n)) = Rbar_opp (Rbar_lim_seq u).
Proof.
  rewrite /Rbar_lim_seq.
  replace (Rbar_limsup_seq (fun n : nat => Rbar_opp (u n)))
    with (Rbar_opp (Rbar_liminf_seq u)).
  replace (Rbar_liminf_seq (fun n : nat => Rbar_opp (u n)))
    with (Rbar_opp (Rbar_limsup_seq u)).
  case: (Rbar_limsup_seq u) => [ls | | ] ;
  case: (Rbar_liminf_seq u) => [li | | ] //= ;
  apply f_equal ; field.

  rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq ; case => [ls | | ] Hls ;
  rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq ; case => [li | | ] Hli //=.
  apply f_equal, Rle_antisym ; apply le_epsilon => e He ;
  set eps := mkposreal e He ; apply Rlt_le.
  case: (Hls (pos_div_2 eps)) ; case => {Hls} N Hls _.
  case: (Hli (pos_div_2 eps)) => {Hli} _ Hli.
  case: (Hli N) => {Hli} n [Hn Hli].
  replace (-ls) with (-(ls + eps/2) + eps/2) by ring.
  replace (li + e) with ((li + eps/2) + eps/2) by (simpl ; field).
  apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite _) (Rbar_opp (u n)) (Finite _)).
  apply <- (Rbar_opp_lt (Finite (ls + eps/2))).
  by apply Hls.
  by apply Hli.
  case: (Hls (pos_div_2 eps)) => {Hls} _ Hls.
  case: (Hli (pos_div_2 eps)) ; case => {Hli} N Hli _.
  case: (Hls N) => {Hls} n [Hn Hls].
  replace (li) with ((li - eps/2) + eps/2) by ring.
  replace (-ls + e) with (-(ls - eps/2) + eps/2) by (simpl ; field).
  apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite _) (Rbar_opp (u n)) (Finite _)).
  by apply Hli.
  apply <- (Rbar_opp_lt (u n) (Finite (ls - eps / 2))).
  by apply Hls.
  
  case: (Hls (mkposreal _ Rlt_0_1)) => {Hls} _ Hls.
  case: (Hli (-(ls - 1))) => {Hli} N Hli.
  case: (Hls N) => {Hls} n [Hn Hls].
  contradict Hls.
  by apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt, Hli.
  
  case: (Hls (mkposreal _ Rlt_0_1)) ; case => {Hls} N Hls _.
  case: (Hli (-(ls + 1)) N) => {Hli} n [Hn Hli].
  contradict Hli.
  by apply Rbar_le_not_lt, Rbar_lt_le, (Rbar_opp_lt (Finite _) (u n)), Hls.
  
  case: (Hli (mkposreal _ Rlt_0_1)) ; case => {Hli} N Hli _.
  case: (Hls (-(li - 1)) N) => {Hls} n [Hn Hls].
  contradict Hls.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite (Rbar_opp_involutive (Finite _)).
  by apply Hli.
  
  case: (Hli 0) => {Hli} N Hli.
  case: (Hls 0 N) => {Hls} n [Hn Hls].
  contradict Hls.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite /= Ropp_0.
  by apply Hli.
  
  case: (Hls (-(li + 1))) => {Hls} N Hls.
  case: (Hli (mkposreal _ Rlt_0_1)) => {Hli} _ Hli.
  case: (Hli N) => {Hli} n [Hn Hli].
  contradict Hli.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite Rbar_opp_involutive.
  by apply Hls.
  
  case: (Hls 0) => {Hls} N Hls.
  case: (Hli 0 N) => {Hli} n [Hn Hli].
  contradict Hli.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite /= Ropp_0 Rbar_opp_involutive.
  by apply Hls.
  
  rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq ; case => [li | | ] Hli ;
  rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq ; case => [ls | | ] Hls //=.
  apply f_equal, Rle_antisym ; apply le_epsilon => e He ;
  set eps := mkposreal e He ; apply Rlt_le.
  case: (Hls (pos_div_2 eps)) ; case => {Hls} N Hls _.
  case: (Hli (pos_div_2 eps)) => {Hli} _ Hli.
  case: (Hli N) => {Hli} n [Hn Hli].
  replace (-li) with (-(li + eps/2) + eps/2) by ring.
  replace (ls + e) with ((ls + eps/2) + eps/2) by (simpl ; field).
  apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite _) (Rbar_opp (u n)) (Finite _)).
  apply <- (Rbar_opp_lt (Finite (li + eps/2))).
  by apply Hli.
  by apply Hls.
  case: (Hls (pos_div_2 eps)) => {Hls} _ Hls.
  case: (Hli (pos_div_2 eps)) ; case => {Hli} N Hli _.
  case: (Hls N) => {Hls} n [Hn Hls].
  replace (ls) with ((ls - eps/2) + eps/2) by ring.
  replace (-li + e) with (-(li - eps/2) + eps/2) by (simpl ; field).
  apply Rplus_lt_compat_r, (Rbar_lt_trans (Finite _) (Rbar_opp (u n)) (Finite _)).
  by apply Hls.
  apply <- (Rbar_opp_lt (u n) (Finite (li - eps / 2))).
  by apply Hli.
  
  case: (Hli (mkposreal _ Rlt_0_1)) ; case => {Hli} N Hli _.
  case: (Hls (-(li - 1)) N) => {Hls} n [Hn Hls].
  contradict Hls.
  by apply Rbar_le_not_lt, Rbar_lt_le, (Rbar_opp_lt (u n) (Finite _)), Hli.
  
  case: (Hli (mkposreal _ Rlt_0_1)) => {Hli} _ Hli.
  case: (Hls (-(li + 1))) => {Hls} N Hls.
  case: (Hli N) => {Hli} n [Hn Hli].
  contradict Hli.
  by apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt, Hls.
  
  case: (Hls (mkposreal _ Rlt_0_1)) => {Hls} _ Hls.
  case: (Hli (-(ls - 1))) => {Hli} N Hli.
  case: (Hls N) => {Hls} n [Hn Hls].
  contradict Hls.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite Rbar_opp_involutive.
  by apply Hli.
  
  case: (Hli 0) => {Hli} N Hli.
  case: (Hls 0 N) => {Hls} n [Hn Hls].
  contradict Hls.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite /= Ropp_0 Rbar_opp_involutive.
  by apply Hli.
  
  case: (Hls (mkposreal _ Rlt_0_1)) ; case => {Hls} N Hls _.
  case: (Hli (-(ls + 1)) N) => {Hli} n [Hn Hli].
  contradict Hli.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite (Rbar_opp_involutive (Finite _)).
  by apply Hls.
  
  case: (Hls 0) => {Hls} N Hls.
  case: (Hli 0 N) => {Hli} n [Hn Hli].
  contradict Hli.
  apply Rbar_le_not_lt, Rbar_lt_le, Rbar_opp_lt.
  rewrite /= Ropp_0.
  by apply Hls.
Qed.

Lemma Rbar_is_lim_seq_plus (u v : nat -> Rbar) (lu lv l : Rbar) :
  Rbar_is_lim_seq u lu -> Rbar_is_lim_seq v lv
  -> is_Rbar_plus lu lv l
  -> Rbar_is_lim_seq (fun n => Rbar_plus (u n) (v n)) l.
Proof.
  case: lu => [lu | | ] ; case: lv => [lv | | ] ;
  case: l => [l | | ] // Hu Hv Hp ; simpl in Hp.

  move => eps.
  case: (Hu (pos_div_2 eps)) => {Hu} N1 Hu.
  case: (Hv (pos_div_2 eps)) => {Hv} N2 Hv.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vu | | ] //= Hu Hv.
  rewrite -Hp ; 
  replace (lu + lv - eps) with ((lu - eps / 2) + (lv - eps / 2)) by field ;
  replace (lu + lv + eps) with ((lu + eps / 2) + (lv + eps / 2)) by field.
  split ; apply Rplus_lt_compat ; by intuition.
  by case: Hu.
  by case: Hu.
  
  move => M.
  case: (Hu (mkposreal _ Rlt_0_1)) => {Hu} N1 Hu.
  case: (Hv (M - (lu - 1))) => {Hv} N2 Hv.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vn | | ] //= Hu Hv.
  replace M with ((lu - 1) + (M - (lu - 1))) by ring.
  apply Rplus_lt_compat ; by intuition.
  by case: Hu.
  by case: Hu.
  
  move => M.
  case: (Hu (mkposreal _ Rlt_0_1)) => {Hu} N1 Hu.
  case: (Hv (M - (lu + 1))) => {Hv} N2 Hv.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vn | | ] //= Hu Hv.
  replace M with ((lu + 1) + (M - (lu + 1))) by ring.
  apply Rplus_lt_compat ; by intuition.
  by case: Hu.
  by case: Hu.
  
  move => M.
  case: (Hv (mkposreal _ Rlt_0_1)) => {Hv} N2 Hv.
  case: (Hu (M - (lv - 1))) => {Hu} N1 Hu.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vn | | ] //= Hu Hv.
  replace M with ((M - (lv - 1)) + (lv - 1)) by ring.
  apply Rplus_lt_compat ; by intuition.
  by case: Hv.
  by case: Hv.
  
  move => M.
  case: (Hu (M/2)) => {Hu} N1 Hu.
  case: (Hv (M /2)) => {Hv} N2 Hv.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vn | | ] //= Hu Hv.
  replace M with (M/2 + M/2) by field.
  apply Rplus_lt_compat ; by intuition.
  
  move => M.
  case: (Hv (mkposreal _ Rlt_0_1)) => {Hv} N2 Hv.
  case: (Hu (M - (lv + 1))) => {Hu} N1 Hu.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vn | | ] //= Hu Hv.
  replace M with ((M - (lv + 1)) + (lv + 1)) by ring.
  apply Rplus_lt_compat ; by intuition.
  by case: Hv.
  by case: Hv.

  move => M.
  case: (Hu (M/2)) => {Hu} N1 Hu.
  case: (Hv (M /2)) => {Hv} N2 Hv.
  exists (N1 + N2)%nat => n Hn.
  case : (u n) (v n) (Hu n (le_trans _ _ _ (le_plus_l _ _) Hn))
    (Hv n (le_trans _ _ _ (le_plus_r _ _) Hn)) => {u v Hu Hv}
    [un | | ] ; case => [vn | | ] //= Hu Hv.
  replace M with (M/2 + M/2) by field.
  apply Rplus_lt_compat ; by intuition.
Qed.
Lemma Rbar_lim_seq_plus (u v : nat -> Rbar) :
  Rbar_ex_lim_seq u -> Rbar_ex_lim_seq v
  -> (exists l, is_Rbar_plus (Rbar_lim_seq u) (Rbar_lim_seq v) l)
  -> Rbar_lim_seq (fun n => Rbar_plus (u n) (v n)) = Rbar_plus (Rbar_lim_seq u) (Rbar_lim_seq v).
Proof.
  move/Rbar_ex_lim_is_lim => Hu.
  move/Rbar_ex_lim_is_lim => Hv.
  case => l Hp.
  rewrite (Rbar_plus_correct _ _ _ Hp).
  apply Rbar_is_lim_correct.
  eapply Rbar_is_lim_seq_plus.
  by apply Hu.
  by apply Hv.
  by apply Hp.
Qed.

Lemma is_Rbar_plus_coeh (x y z : Rbar) :
  (forall (u v : nat -> R), Rbar_is_lim_seq (fun n => Finite (u n)) x
    -> Rbar_is_lim_seq (fun n => Finite (v n)) y
    -> Rbar_is_lim_seq (fun n => Finite (u n + v n)) z)
    <-> is_Rbar_plus x y z.
Proof.
split.
  move => Huv.
  set x_seq := fun (x : Rbar) (n : nat) => match x with 
    | Finite x => x
    | p_infty => INR n
    | m_infty => - INR n
  end.
  
  move: (Huv (x_seq x) (x_seq y)) => H.
  have Hx : forall x, Rbar_is_lim_seq (fun n => Finite (x_seq x n)) x.
    case => [l | | ] /= eps.
    exists O => _ _.
    rewrite -Rabs_lt_between' Rminus_eq0 Rabs_R0 ; by apply eps.
    exists (S (nfloor (Rmax 0 eps) (Rmax_l _ _))) => n Hn.
    apply Rlt_le_trans with (2 := le_INR _ _ Hn).
    rewrite /nfloor S_INR ; case: nfloor_ex => /= N HN.
    apply Rle_lt_trans with (2 := proj2 HN).
    by apply Rmax_r.
    exists (S (nfloor (Rmax 0 (-eps)) (Rmax_l _ _))) => n Hn.
    apply Ropp_lt_cancel ; rewrite Ropp_involutive.
    apply Rlt_le_trans with (2 := le_INR _ _ Hn).
    rewrite /nfloor S_INR ; case: nfloor_ex => /= N HN.
    apply Rle_lt_trans with (2 := proj2 HN).
    by apply Rmax_r.
  move: (H (Hx x)) => {H} H.
  move: (H (Hx y)) => {H} H.

  case: x y Huv H => [x | | ] ; case => [y | | ] Huv /= H.
(* x \in R *)
(* * y \in R *)
  case: z Huv H => [z | | ] Huv /= H.
  apply Req_lt_aux => eps.
  case: (H eps) => {H} N H.
  by apply Rabs_lt_between', (H N).
  case: (H (x+y)) => {H} N H.
  move: (H N (le_refl _)) => {H} H.
  by apply Rlt_irrefl in H.
  case: (H (x+y)) => {H} N H.
  move: (H N (le_refl _)) => {H} H.
  by apply Rlt_irrefl in H.
(* * y = p_infty *)
  case: z Huv H => [z | | ] Huv /= H.
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  case: (H (S (nfloor1 (Rmax 1 (z+1-x)) _)+N)%nat (le_plus_r _ _)) => [ | Hn _].
  by apply Rlt_le_trans with (1 := Rlt_0_1), Rmax_l.
  apply Rle_not_lt.
  rewrite (Rplus_comm x).
  apply Rle_minus_l.
  apply Rle_trans with (2 := le_INR _ _ (le_plus_l _ _)).
  rewrite /nfloor1 S_INR ; case: nfloor1_ex => /= n Hn'.
  apply Rle_trans with (2 := proj2 Hn').
  by apply Rmax_r.
  by [].
  case: (H x) => {H} N H.
  move: (H N (le_refl _)) ; apply Rle_not_lt, Rminus_le_0 ; ring_simplify.
  apply (le_INR O), le_O_n.
(* * y = m_infty *)
  case: z Huv H => [z | | ] Huv /= H.
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  case: (H _ (le_plus_r (S (nfloor (Rmax 0 (x-(z-1))) (Rmax_l _ _))) N))
    => {H} H _ ; move: H ; apply Rle_not_lt.
  apply Rle_minus_l.
  rewrite Rplus_comm.
  apply Rle_minus_l.
  apply Rle_trans with (1 := Rmax_r 0 _).
  apply Rle_trans with (2 := le_INR _ _ (le_plus_l _ _)).
  rewrite S_INR.
  rewrite /nfloor ; case: nfloor_ex => /= n Hn.
  apply Rlt_le, Hn.
  case: (H x) => {H} N H.
  move: (H N (le_refl _)) ; apply Rle_not_lt, Rminus_le_0 ; ring_simplify.
  apply (le_INR O), le_O_n.
  by [].
(* x = p_infty *)
(* * y \in R *)
  case: z Huv H => [z | | ] Huv /= H.
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  case: (H (S (nfloor1 (Rmax 1 (z+1-y)) _)+N)%nat (le_plus_r _ _)) => [ | Hn _].
  by apply Rlt_le_trans with (1 := Rlt_0_1), Rmax_l.
  apply Rle_not_lt.
  apply Rle_minus_l.
  apply Rle_trans with (2 := le_INR _ _ (le_plus_l _ _)).
  rewrite /nfloor1 S_INR ; case: nfloor1_ex => /= n Hn'.
  apply Rle_trans with (2 := proj2 Hn').
  by apply Rmax_r.
  by [].
  case: (H y) => {H} N H.
  move: (H N (le_refl _)) ; apply Rle_not_lt, Rminus_le_0 ; ring_simplify.
  apply (le_INR O), le_O_n.
(* * y = p_infty *)
  case: z Huv H => [z | | ] Huv /= H.
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  case: (H _ (le_plus_r (S (nfloor (Rmax 0 ((z+1)/2)) (Rmax_l _ _))) N))
    => {H} _ ; apply Rle_not_lt.
  rewrite -plus_INR ?plus_Sn_m S_INR -plus_n_Sm S_INR.
  ring_simplify ((nfloor (Rmax 0 ((z + 1) / 2)) (Rmax_l 0 ((z + 1) / 2))) + N +
   ((nfloor (Rmax 0 ((z + 1) / 2)) (Rmax_l 0 ((z + 1) / 2))) + N))%nat.
  rewrite -?S_INR -2?plus_Sn_m.
  apply Rle_trans with (2 := le_INR _ _ (le_plus_l _ _)).
  rewrite ?S_INR.
  rewrite /nfloor ; case: nfloor_ex => n Hn.
  simpl projT1.
  rewrite mult_INR /= .
  replace (2 * INR n + 1 + 1) with ((INR n + 1) * 2) by ring.
  apply Rle_div_l.
  by apply Rlt_R0_R2.
  apply Rle_trans with (1 := Rmax_r 0 _).
  by apply Rlt_le, Hn.
  by [].
  case: (H (0+0)) => {H} N H.
  move: (H N (le_refl _)) ; apply Rle_not_lt, Rplus_le_compat ;
  apply (le_INR O), le_O_n.
(* * y = m_infty *)
  case: z Huv H => [z | | ] Huv /= H.
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  case: (H N (le_refl _)) ; ring_simplify (INR N + - INR N) => {H N} H _.
  apply Rlt_minus_l in H ; rewrite Rplus_0_l in H.
  move: (fun H => Huv (fun n => INR n + 2) (x_seq m_infty) H (Hx m_infty)) => {Huv} Huv.
  have Hu : Rbar_is_lim_seq (fun n : nat => Finite (INR n + 2)) p_infty.
    move => /= M.
    exists ((nfloor (Rmax 0 M) (Rmax_l _ _))) => n Hn.
    apply Rle_lt_trans with (1 := Rmax_r 0 M).
    apply Rlt_le_trans with (INR (nfloor (Rmax 0 M) (Rmax_l 0 M)) + 1).
    rewrite /nfloor ; case: nfloor_ex => /= N HN.
    by apply HN.
    apply Rle_minus_r ; ring_simplify.
    rewrite -S_INR ; by intuition.
  move: (Huv Hu) => {Huv Hu} Hu.
  case: (Hu (mkposreal _ Rlt_0_1)) => /= {Hu} N Hu.
  case: (Hu N (le_refl _)) => _.
  apply Rle_not_lt.
  apply -> Rle_minus_r.
  ring_simplify.
  by apply Rlt_le.
  case: (H 0) => {H} N H.
  move: (H N (le_refl _)) => {H} ; apply Rle_not_lt ; ring_simplify.
  by apply Rle_refl.
  case: (H 0) => {H} N H.
  move: (H N (le_refl _)) => {H} ; apply Rle_not_lt ; ring_simplify.
  by apply Rle_refl.
(* x = m_infty *)
(* * y \in R *)
  case: z Huv H => [z | | ] Huv /= H.
admit.
  case: (H y) => {H} N H.
  move: (H N (le_refl _)) ; apply Rle_not_lt, Rminus_le_0 ; ring_simplify.
  apply (le_INR O), le_O_n.
  case: (H y) => {H} N H.
  by [].
(* * y = p_infty *)
  case: z Huv H => [z | | ] Huv /= H.
admit.
  case: (H 0) => {H} N H.
  move: (H N (le_refl _)) => {H} ; apply Rle_not_lt ; ring_simplify.
  by apply Rle_refl.
  case: (H 0) => {H} N H.
  move: (H N (le_refl _)) => {H} ; apply Rle_not_lt ; ring_simplify.
  by apply Rle_refl.
(* * y = m_infty *)
  case: z Huv H => [z | | ] Huv /= H.
admit.
  case: (H (0+0)) => {H} N H.
  move: (H N (le_refl _)) ; apply Rle_not_lt, Rplus_le_compat ;
  apply Ropp_le_cancel ; rewrite Ropp_0 Ropp_involutive ; apply (le_INR O), le_O_n.
  by [].

intros.
  eapply (Rbar_is_lim_seq_plus (fun n => Finite (u n)) (fun n => Finite (v n))).
  by apply H0.
  by apply H1.
  by apply H.
Qed.

Lemma Rbar_is_lim_seq_minus (u v : nat -> Rbar) (lu lv l : Rbar) :
  Rbar_is_lim_seq u lu -> Rbar_is_lim_seq v lv
  -> is_Rbar_minus lu lv l
  -> Rbar_is_lim_seq (fun n => Rbar_minus (u n) (v n)) l.
Proof.
  move => Hu Hv Hm.
  eapply Rbar_is_lim_seq_plus.
  by apply Hu.
  apply -> Rbar_is_lim_seq_opp.
  by apply Hv.
  by apply Hm.
Qed.
Lemma Rbar_lim_seq_minus (u v : nat -> Rbar) :
  Rbar_ex_lim_seq u -> Rbar_ex_lim_seq v
  -> (exists l, is_Rbar_minus (Rbar_lim_seq u) (Rbar_lim_seq v) l)
  -> Rbar_lim_seq (fun n => Rbar_minus (u n) (v n)) = Rbar_minus (Rbar_lim_seq u) (Rbar_lim_seq v).
Proof.
  move => Hu Hv Hm.
  rewrite /Rbar_minus -(Rbar_lim_seq_opp v).
  apply (Rbar_lim_seq_plus u (fun n => Rbar_opp (v n))).
  by apply Hu.
  by apply -> Rbar_ex_lim_seq_opp.
  by rewrite Rbar_lim_seq_opp.
Qed.

(** Multiplicative *)

