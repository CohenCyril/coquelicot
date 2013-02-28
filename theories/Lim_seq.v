Require Import Reals Rcomplements Markov Floor.
Require Import Sup_seq Rbar_theory Total_sup ssreflect.
Open Scope R_scope.

(** * Limit sequence *)

Definition is_lim_seq (u : nat -> R) (l : R) :=
  forall eps : posreal, exists N : nat, forall n : nat,
    (N <= n)%nat -> Rabs (u n - l) < eps.
Definition ex_lim_seq (u : nat -> R) :=
  exists l, is_lim_seq u l.
Definition Lim_seq (u : nat -> R) : R := (real (Rbar_plus (LimSup_seq u) (LimInf_seq u)))/2.

Lemma is_lim_seq_correct (u : nat -> R) (l : R) :
  is_lim_seq u l <-> Rbar_is_lim_seq (fun n => Finite (u n)) (Finite l).
Proof.
  split => /= Hl eps ; case: (Hl eps) => {Hl} N Hl ; exists N => n Hn ;
  by apply Rabs_lt_between', Hl.
Qed.
Lemma Lim_seq_Rbar (u : nat -> R) :
  Lim_seq u = real (Rbar_lim_seq (fun n => Finite (u n))).
Proof.
  rewrite /Lim_seq /Rbar_lim_seq.
  rewrite (LimSup_seq_correct u) (LimInf_seq_correct u) /= ;
  case: (Rbar_plus _ _) => //= ; field.
Qed.

Lemma ex_lim_seq_dec (u : nat -> R) :
  {ex_lim_seq u} + {~ex_lim_seq u}.
Proof.
  case: (Rbar_ex_lim_seq_dec (fun n => Finite (u n))) => H.
  apply Rbar_ex_lim_is_lim in H.
  case: (Rbar_lim_seq (fun n : nat => Finite (u n))) H => [l | | ] H.
  left ; exists l ; by apply is_lim_seq_correct.
  right => H0.
  case: H0 => l Hl.
  apply is_lim_seq_correct in Hl.
  absurd (p_infty = (Finite l)) => //.
  apply Rbar_is_lim_limsup in H ;
  apply Rbar_is_lim_limsup in Hl ;
  rewrite (Rbar_is_limsup_eq _ _ p_infty (Finite l) _ H Hl) => //.
  right => H0.
  case: H0 => l Hl.
  apply is_lim_seq_correct in Hl.
  absurd (m_infty = (Finite l)) => //.
  apply Rbar_is_lim_limsup in H ;
  apply Rbar_is_lim_limsup in Hl ;
  rewrite (Rbar_is_limsup_eq _ _ m_infty (Finite l) _ H Hl) => //.
  right ; contradict H.
  case: H => l Hl.
  exists (Finite l) ; by apply is_lim_seq_correct.
Qed.

(** ** Correction of Lim_seq *)

Lemma is_lim_seq_unique (u : nat -> R) :
  forall l, is_lim_seq u l -> Lim_seq u = l.
Proof.
  move => l ; move/is_lim_seq_correct => Hl ; rewrite Lim_seq_Rbar ;
  by rewrite (Rbar_is_lim_correct _ _ Hl).
Qed.
Lemma Lim_seq_correct (u : nat -> R) :
  ex_lim_seq u -> is_lim_seq u (Lim_seq u).
Proof.
  intros (l,H).
  cut (Lim_seq u = l).
    intros ; rewrite H0 ; apply H.
  apply is_lim_seq_unique, H.
Qed.

(** * Usual rewritings *)

(** ** Extentionality *)

(** Order *)
  
Lemma is_lim_seq_le (u v : nat -> R) (l1 l2 : R) : 
  (forall n, u n <= v n) -> is_lim_seq u l1 -> is_lim_seq v l2 -> l1 <= l2.
Proof.
  move => Heq Hu Hv.
  apply Rnot_lt_le => Hl.
  have He : 0 < ((l1 - l2) / 2).
    apply Rdiv_lt_0_compat.
    by apply Rlt_Rminus.
    by apply Rlt_R0_R2.
  set eps := mkposreal _ He.
  case: (Hu eps) => {Hu} N1 Hu.
  case: (Hv eps) => {Hv} N2 Hv.
  move: (Hu _ (le_plus_l N1 N2)) => {Hu} Hu.
  move: (Hv _ (le_plus_r N1 N2)) => {Hv} Hv.
  apply Rabs_lt_between' in Hu.
  apply Rabs_lt_between' in Hv.
  case: Hu ; rewrite /eps /= ; field_simplify (l1 - (l1 - l2) / 2) => Hu _.
  case: Hv ; rewrite /eps /= ; field_simplify (l2 + (l1 - l2) / 2) ;
  rewrite Rplus_comm => _ Hv.
  move: (Heq (N1 + N2)%nat) ; apply Rlt_not_le.
  by apply Rlt_trans with ((l1 + l2) / 2).
Qed.

Lemma is_lim_seq_le_le (u v w : nat -> R) (l : R) : 
  (forall n, u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
  move => Hle Hu Hw.
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
Qed.

(** Extentionality *)

Lemma is_lim_seq_ext : forall u v l, 
  (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  intros.
  move => eps.
  case: (H0 eps) => {H0} N H0.
  exists N => n H1.
  rewrite -(H n).
  by apply H0.
Qed.
Lemma ex_lim_seq_ext : forall u v, 
  (forall n, u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => u v H [l H0].
  exists l ; by apply is_lim_seq_ext with u.
Qed.
Lemma Lim_seq_ext:  forall u v, 
  (forall n, u n = v n) -> 
  Lim_seq u = Lim_seq v.
Proof.
intros u v H.
unfold Lim_seq, LimSup_seq, LimInf_seq.
destruct (ex_LimSup_seq u) as (lu1,Hlu1).
destruct (ex_LimSup_seq v) as (lv1,Hlv1).
destruct (ex_LimInf_seq u) as (lu2,Hlu2).
destruct (ex_LimInf_seq v) as (lv2,Hlv2).
simpl.
rewrite (is_LimSup_seq_eq _ _ _ _ H Hlu1 Hlv1).
rewrite (is_LimInf_seq_eq _ _ _ _ H Hlu2 Hlv2).
easy.
Qed.

(** ** Sub-sequences *)

Lemma is_lim_seq_subseq (u : nat -> R) (l : R) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> is_lim_seq u l
    -> is_lim_seq (fun n => u (phi n)) l.
Proof.
  move => Hphi Hu eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  apply Hu.
  apply le_trans with (1 := Hn).
  elim: n {Hn} => [ | n IH].
  by apply le_O_n.
  apply lt_le_S.
  apply le_lt_trans with (1 := IH).
  by apply Hphi.
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

Lemma is_lim_seq_incr (u : nat -> R) (l : R) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (S n)) l.
Proof.
  split ; move => H.
  apply is_lim_seq_subseq.
  move => n ; by apply lt_n_Sn.
  by apply H.
  move => eps.
  case: (H eps) => {H} N H.
  exists (S N) ;
  case => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  by apply H, le_S_n.
Qed.
Lemma ex_lim_seq_incr (u : nat -> R) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (S n)).
Proof.
  split ; move => [l H] ; exists l.
  by apply -> is_lim_seq_incr.
  by apply is_lim_seq_incr.
Qed.
Lemma Lim_seq_incr (u : nat -> R) :
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

Lemma is_lim_seq_incr_n (u : nat -> R) (N : nat) (l : R) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (n + N)%nat) l.
Proof.
  split.
  elim: N u => [ | N IH] u Hu.
  move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
  apply is_lim_seq_incr, IH in Hu.
  move: Hu ; by apply is_lim_seq_ext => n ; by rewrite plus_n_Sm.
  elim: N u => [ | N IH] u Hu.
  move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
  apply is_lim_seq_incr, IH.
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
  rewrite -(Lim_seq_incr u) -(IH (fun n => u (S n))).
  apply Lim_seq_ext => n ; by rewrite plus_n_Sm.
Qed.

(** * Operations *)
(** ** Linear combination *)

Lemma is_lim_seq_CL (u v : nat -> R) (a l1 l2 : R) {l : R} :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l = l1 + a * l2 ->
    is_lim_seq (fun n => u n + a * v n) l.
Proof.
  intros Hf Hg Hl e0 ; rewrite Hl ; clear Hl.
  assert (He : 0 < e0 / (1 + Rabs a)).
    unfold Rdiv ; apply Rmult_lt_0_compat ; [apply e0 | apply Rinv_0_lt_compat] ;
    apply Rlt_le_trans with (1 := Rlt_0_1) ; rewrite -{1}(Rplus_0_r 1) ;
    apply Rplus_le_compat_l, Rabs_pos.
  set (eps := mkposreal _ He).
  move: (Hf eps) => {Hf} [Nf Hf].
  move: (Hg eps) => {Hg} [Ng Hg].
  exists (Nf+Ng)%nat ; intros.
  assert (Rw : u n + a * v n - (l1 + a * l2) = (u n - l1) + a * (v n - l2)) ; 
  [ ring | rewrite Rw ; clear Rw].
  assert (Rw : (pos e0) = eps + Rabs a * eps) ;
  [ simpl ; field ; apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1) ; 
    rewrite -{1}(Rplus_0_r 1) ; apply Rplus_le_compat_l, Rabs_pos
  | rewrite Rw ; clear Rw].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_le_compat.
  apply Hf, le_trans with (2 := H) ; intuition.
  rewrite Rabs_mult ; apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, Hg, le_trans with (2 := H) ; intuition.
Qed.
Lemma ex_lim_seq_CL (u v : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq v -> ex_lim_seq (fun n => u n + a * v n).
Proof.
  intros (lf,Hf) (lg,Hg).
  exists (lf + a * lg) ; apply (is_lim_seq_CL u v a lf lg) ; [apply Hf | apply Hg | ring].
Qed.
Lemma Lim_seq_CL (u v : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq (fun n => u n + a * v n) = Lim_seq u + a * Lim_seq v.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply (is_lim_seq_CL _ _ _ (Lim_seq u) (Lim_seq v)).
  apply Lim_seq_correct, H.
  apply Lim_seq_correct, H0.
  reflexivity.
Qed.

(** ** Addition *)

Lemma is_lim_seq_plus (u v : nat -> R) {l : R} (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l = l1 + l2 ->
    is_lim_seq (fun n => u n + v n) l.
Proof.
  intros.
  rewrite H1 ; clear H1 ; intros eps.
  assert (He2 : 0 < eps / 2) ; 
    [unfold Rdiv ; destruct eps ; apply Rmult_lt_0_compat ; intuition | ].
  elim (H (mkposreal _ He2)) ; clear H ; simpl ; intros N1 H.
  elim (H0 (mkposreal _ He2)) ; clear H0 ; simpl ; intros N2 H0.
  exists (N1+N2)%nat ; intros.
  assert (Rw : (u n + v n - (l1 + l2)) = (u n - l1) + (v n - l2)) ;
    [ring | rewrite Rw ; clear Rw].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite (double_var eps) ; apply Rplus_lt_compat ; intuition.
Qed.
Lemma Lim_seq_plus (u v : nat -> R) :
  let w := fun n => u n + v n in
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq w = Lim_seq u + Lim_seq v.
Proof.
  intros w (l1,Hu) (l2,Hv).
  apply is_lim_seq_unique.
  rewrite (is_lim_seq_unique _ _ Hu).
  rewrite (is_lim_seq_unique _ _ Hv).
  apply is_lim_seq_plus with (l1 := l1) (l2 := l2) ; intuition.
Qed.

(** ** Constant sequences *)

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

(** ** Scalar multiplication *)

Lemma is_lim_seq_scal (u : nat -> R) (a l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => a * u n) (a * l).
Proof.
  move => H.
  apply is_lim_seq_ext with (fun n => 0 + a * u n).
  intro ; ring.
  apply is_lim_seq_CL with 0 l.
  by apply is_lim_seq_const.
  by apply H.
  ring.
Qed.
Lemma ex_lim_seq_scal (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => a * u n).
Proof.
  move => [l H].
  exists (a * l).
  by apply is_lim_seq_scal.
Qed.
Lemma Lim_seq_scal (u : nat -> R) (a : R) :
  Lim_seq (fun n => a * u n) = a * Lim_seq u.
Proof.
  wlog: u a / (0 <= a) => [Hw | Ha].
    case: (Rle_lt_dec 0 a) => Ha.
    by apply Hw.
    apply Ropp_0_gt_lt_contravar, Rlt_le in Ha ; 
    move: (Hw (fun n => - u n) _ Ha) => {Hw}.
    rewrite /Lim_seq.
    have H : (forall u, Rbar_limsup_seq u = 
      Rbar_inf_seq (fun n => Rbar_sup_seq (fun m => u (n+m)%nat))).
      move => u0 ; rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq => ls Hls ;
      rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq => i Hi /=.
      apply (Rbar_is_inf_seq_rw (fun n : nat => Rbar_sup_seq (fun m : nat => u0 (n + m)%nat)) 
      (fun n : nat => Rbar_sup_seq (fun m : nat => u0 (n + m)%nat))) => //.
      by apply Rbar_limsup_caract_1.
    rewrite ?LimSup_seq_correct ?H => {H}.
    have H : (forall u, Rbar_liminf_seq u = 
      Rbar_sup_seq (fun n => Rbar_inf_seq (fun m => u (n+m)%nat))).
      move => u0 ; rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq => ls Hls ;
      rewrite /Rbar_sup_seq ; case: Rbar_ex_sup_seq => i Hi /=.
      apply (Rbar_is_sup_seq_rw (fun n : nat => Rbar_inf_seq (fun m : nat => u0 (n + m)%nat)) 
      (fun n : nat => Rbar_inf_seq (fun m : nat => u0 (n + m)%nat))) => //.
      by apply Rbar_liminf_caract_1.
    rewrite ?LimInf_seq_correct ?H => {H}.
    move => Hw.
    rewrite (Rbar_inf_seq_rw (fun n : nat =>
      Rbar_sup_seq (fun m : nat => Finite (a * u (n + m)%nat))) 
      (fun n : nat =>
      Rbar_sup_seq (fun m : nat => Finite (-a * -u (n + m)%nat)))).
    rewrite (Rbar_sup_seq_rw (fun n : nat =>
      Rbar_inf_seq (fun m : nat => Finite (a * u (n + m)%nat))) 
      (fun n : nat =>
      Rbar_inf_seq (fun m : nat => Finite (-a * -u (n + m)%nat)))).
    rewrite Hw => {Hw} ;
    rewrite Ropp_mult_distr_l_reverse -Ropp_mult_distr_r_reverse ;
    apply Rmult_eq_compat_l ; rewrite -Ropp_mult_distr_l_reverse ;
    apply Rmult_eq_compat_r.
    rewrite -Rbar_opp_real.
    have : (forall x y, Rbar_opp (Rbar_plus x y) = Rbar_plus (Rbar_opp x) (Rbar_opp y)).
      case => [x | | ] ; case => [y | | ] //= ; apply Rbar_finite_eq ; intuition.
    move => ->.
    rewrite Rbar_plus_comm.
    rewrite Rbar_inf_opp_sup Rbar_opp_involutive ;
    rewrite Rbar_sup_opp_inf Rbar_opp_involutive.
    rewrite (Rbar_inf_seq_rw (fun n : nat =>
      Rbar_opp (Rbar_inf_seq (fun m : nat => Finite (- u (n + m)%nat))))
      (fun n : nat => Rbar_sup_seq (fun m : nat => Finite (u (n + m)%nat)))).
    rewrite (Rbar_sup_seq_rw (fun n : nat =>
      Rbar_opp (Rbar_sup_seq (fun m : nat => Finite (- u (n + m)%nat))))
      (fun n : nat => Rbar_inf_seq (fun m : nat => Finite (u (n + m)%nat)))) //.
    move => n ; by rewrite -(Rbar_inf_opp_sup (fun m => Finite (u (n+m)%nat))).
    move => n ; by rewrite -(Rbar_sup_opp_inf (fun m => Finite (u (n+m)%nat))).
    move => n ; apply Rbar_inf_seq_rw => m ; apply Rbar_finite_eq ; ring.
    move => n ; apply Rbar_sup_seq_rw => m ; apply Rbar_finite_eq ; ring.
  
  rewrite /Lim_seq /LimSup_seq /LimInf_seq ;
  case: ex_LimSup_seq => ls' Hls' ; case: ex_LimSup_seq => ls Hls ;
  case: ex_LimInf_seq => li' Hli' ; case: ex_LimInf_seq => li Hli /=.
  apply Rle_lt_or_eq_dec in Ha ; case: Ha => Ha.
(* 0 < a *)
  replace ls' with (Rbar_mult_pos ls (mkposreal _ Ha)).
  replace li' with (Rbar_mult_pos li (mkposreal _ Ha)).
  case: (ls) ; case: (li) => //= ; intros ; field.
(* a*li = li'*)
  apply (is_LimInf_seq_eq (fun n => a * u n) (fun n => a * u n)) => // ;
  case: li Hli => [li | | ] /= Hli.
  move => eps ; have He : (0 < eps / a) ; 
  [apply Rdiv_lt_0_compat => // ; apply eps | set e := mkposreal _ He ].
  move: (Hli e) => {Hli} Hli.
  split ; [case: Hli => Hli _ | case: Hli => _ [N Hli]].
  move => N ; case: (Hli N) => {Hli} n Hli ; exists n ; intuition.
  replace (_*_+_) with (a * (li+e)).
  by apply Rmult_lt_compat_l.
  simpl ; field ; by apply Rgt_not_eq.
  exists N => n Hn.
  replace (_*_-_) with (a * (li-e)).
  by apply Rmult_lt_compat_l, Hli.
  simpl ; field ; by apply Rgt_not_eq.
  move => M ; case: (Hli (M/a)) => {Hli} N Hli ; 
  exists N => n Hn.
  replace M with (a*(M/a)).
  by apply Rmult_lt_compat_l, Hli.
  field ; by apply Rgt_not_eq.
  move => M N ; case: (Hli (M/a) N) => {Hli} n Hli.
  exists n ; replace M with (a*(M/a)) ; intuition.
  field ; by apply Rgt_not_eq.
  (* a*ls = ls'*)
  apply (is_LimSup_seq_eq (fun n => a * u n) (fun n => a * u n)) => // ;
  case: ls Hls => [ls | | ] /= Hls.
  move => eps ; have He : (0 < eps / a) ; 
  [apply Rdiv_lt_0_compat => // ; apply eps | set e := mkposreal _ He ].
  move: (Hls e) => {Hls} Hls.
  split ; [case: Hls => Hls _ | case: Hls => _ [N Hls]].
  move => N ; case: (Hls N) => {Hls} n Hls ; exists n ; intuition.
  replace (_*_-_) with (a * (ls-e)).
  by apply Rmult_lt_compat_l.
  simpl ; field ; by apply Rgt_not_eq.
  exists N => n Hn.
  replace (_*_+_) with (a * (ls+e)).
  by apply Rmult_lt_compat_l, Hls.
  simpl ; field ; by apply Rgt_not_eq.
  move => M N ; case: (Hls (M/a) N) => {Hls} n Hls.
  exists n ; replace M with (a*(M/a)) ; intuition.
  field ; by apply Rgt_not_eq.
  move => M ; case: (Hls (M/a)) => {Hls} N Hls ; 
  exists N => n Hn.
  replace M with (a*(M/a)).
  by apply Rmult_lt_compat_l, Hls.
  field ; by apply Rgt_not_eq.
(* a = 0 *)
  rewrite -Ha in Hls' Hli' |- *.
  replace ls' with (Finite 0).
  replace li' with (Finite 0).
  simpl ; field.
(* li' = 0*)
  apply (is_LimInf_seq_eq (fun n => 0 * u n) (fun n => 0 * u n)) => //= ;
  intuition ; [exists N | exists O] ; intuition ; ring_simplify ; 
  case: eps ; intuition.
(* ls' = 0*)
  apply (is_LimSup_seq_eq (fun n => 0 * u n) (fun n => 0 * u n)) => //= ;
  intuition ; [exists N | exists O] ; intuition ; ring_simplify ; 
  case: eps ; intuition.
Qed.

(** ** Opposite *)

Lemma is_lim_seq_opp (u : nat -> R) (l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => -u n) (-l).
Proof.
  move => H eps ; case: (H eps) => {H} N H ; exists N => n Hn.
  replace (-u n--l) with (-(u n-l)) by ring ;
  rewrite Rabs_Ropp ; by apply H.
Qed.
Lemma ex_lim_seq_opp (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => -u n).
Proof.
  case => l Hl ; exists (-l) ; by apply is_lim_seq_opp.
Qed.
Lemma Lim_seq_opp :
  forall u,
  Lim_seq (fun n => - u n) = - Lim_seq u.
Proof.
intros u.
rewrite -(Rmult_1_l (Lim_seq u)) -Ropp_mult_distr_l_reverse.
rewrite -Lim_seq_scal.
apply Lim_seq_ext => n.
now rewrite Ropp_mult_distr_l_reverse Rmult_1_l.
Qed.

(** ** Absolute value *)

Lemma is_lim_seq_abs (u : nat -> R) (l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => Rabs (u n)) (Rabs l).
Proof.
  move => Hu eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  by apply Rle_lt_trans with (1 := Rabs_triang_inv2 _ _), Hu.
Qed.
Lemma ex_lim_seq_abs (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => Rabs (u n)).
Proof.
  move => [l Hu].
  exists (Rabs l) ; by apply is_lim_seq_abs.
Qed.
Lemma Lim_seq_abs (u : nat -> R) :
  ex_lim_seq u ->
  Lim_seq (fun n => Rabs (u n)) = Rabs (Lim_seq u).
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
  rewrite -Rabs_R0 ; by apply is_lim_seq_abs.
  move => eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  move: (Hu n Hn) ;
  by rewrite ?Rminus_0_r Rabs_Rabsolu.
Qed.

(** ** Particular limits *)

(** Inverse sequence *)

Lemma is_lim_seq_inv_n :
  is_lim_seq (fun n => /INR n) 0.
Proof.
  intros eps.
  assert (He : 0 <= /eps) ; 
    [apply Rlt_le, Rinv_0_lt_compat, eps|].
  destruct (nfloor_ex _ He) as (N,HN).
  exists (S N) ; intros.
  assert (Rw : (pos eps) = INR n * (eps / INR n)) ; 
    [field ; apply Rgt_not_eq, Rlt_gt, lt_0_INR, lt_le_trans with (2 := H), lt_O_Sn 
    | rewrite Rw ; clear Rw].
  assert (Rw : Rabs (/ INR n - 0) = /eps * (eps/INR n)) ; 
    [rewrite Rminus_0_r Rabs_right ; intuition ; field ; split ; 
    [ apply Rgt_not_eq ; intuition | apply Rgt_not_eq, eps ]
    | rewrite Rw ; clear Rw ].
  apply Rmult_lt_compat_r.
  unfold Rdiv ; apply Rmult_lt_0_compat ; intuition ; apply eps.
  apply Rlt_le_trans with (1 := proj2 HN).
  rewrite <- S_INR ; apply le_INR, H.
Qed.
Lemma ex_lim_seq_inv_n :
  ex_lim_seq (fun n => /INR n).
Proof.
  exists 0 ; by apply is_lim_seq_inv_n.
Qed.
Lemma Lim_seq_inv_n (a : R) :
  Lim_seq (fun n => /INR n) = 0.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_inv_n.
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

Lemma Rbar_is_lim_seq_geom_p (q : R) :
  1 < q -> Rbar_is_lim_seq (fun n => Finite (q ^ n)) p_infty.
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
Lemma Rbar_ex_lim_seq_geom_p (q : R) :
  1 < q -> Rbar_ex_lim_seq (fun n => Finite (q ^ n)).
Proof.
  move => Hq ; exists p_infty ; by apply Rbar_is_lim_seq_geom_p.
Qed.
Lemma Rbar_lim_seq_geom_p (q : R) :
  1 < q -> Rbar_lim_seq (fun n => Finite (q ^ n)) = p_infty.
Proof.
  intros.
  apply Rbar_is_lim_correct.
  by apply Rbar_is_lim_seq_geom_p.
Qed.

Lemma Rbar_ex_lim_seq_geom_m (q : R) :
  q <= -1 -> ~ Rbar_ex_lim_seq (fun n => Finite (q ^ n)).
Proof.
  move => Hq ; case ; case => [l | | ] /= H.
  case: Hq => Hq.
(* ~ is_lim_seq (q^n) l *)
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  move: (fun n Hn => Rabs_lt_between_Rmax _ _ _ (H n Hn)).
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
  move: (H _ (le_n_2n _)) ; rewrite pow_1_even ; case => _ H1.
  have H2 : (N <= S (2 * N))%nat.
    by apply le_trans with (1 := le_n_2n _), le_n_Sn.
  move: (H _ H2) ; rewrite pow_1_odd ; case => {H H2} H2 _.
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

(** * A new theorem R_complete *)
Lemma R_complete : forall Un:nat -> R, Cauchy_crit Un -> { l:R | Un_cv Un l } .
Proof.
  move => u Hcv.
  have H : (Rbar_ex_lim_seq (fun n => Finite (u n))).
  have H : Rbar_limsup_seq (fun n => Finite (u n)) = Rbar_liminf_seq (fun n => Finite (u n)).
  rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq ; case => /= [ls | | ] Hls.
  rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq ; case => /= [li | | ] Hli.
  apply Rbar_finite_eq ; apply Rle_antisym ;
  apply le_epsilon => e He ; apply Rlt_le ; set eps := mkposreal e He ;
  case: (Hcv _ (is_pos_div_2 eps)) => {Hcv} /= Ncv Hcv.
  case: (proj2 (Hls (pos_div_2 (pos_div_2 eps))) Ncv) => {Hls} /= ns [Hns Hls].
  case: (proj2 (Hli (pos_div_2 (pos_div_2 eps))) Ncv) => {Hli} /= ni [Hni Hli].
  apply Rlt_trans with (u ns + e/4).
  replace ls with ((ls - e / 2 / 2) + e/4) by field ;
  by apply Rplus_lt_compat_r.
  apply Rlt_trans with (u ni + 3*e/4).
  replace (u ns + e/4) with ((u ns - u ni) + (u ni + e/4)) by ring ;
  replace (u ni + 3 * e / 4) with (e/2 + (u ni + e/4)) by field ;
  by apply Rplus_lt_compat_r, Rle_lt_trans with (1 := Rle_abs _), Hcv.
  replace (li + e) with ((li + e / 2 / 2) + 3*e/4) by field ;
  by apply Rplus_lt_compat_r.
  case: (proj1 (Hls (pos_div_2 eps))) => {Hls} /= Ns Hls.
  case: (proj1 (Hli (pos_div_2 eps))) => {Hli} /= Ni Hli.
  apply Rlt_trans with (u (Ns + Ni)%nat + e/2).
  replace li with ((li-e/2) +e/2) by ring ;
  by apply Rplus_lt_compat_r, Hli, le_plus_r.
  replace (ls+e) with ((ls+e/2) +e/2) by field ;
  by apply Rplus_lt_compat_r, Hls, le_plus_l.
  case: (Hcv 1 Rlt_0_1) => {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hli (u Ncv + 1)) => {Hli} Ni Hli.
  move: (Hcv (Ncv + Ni)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj2 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, Hli, le_plus_r.
  case: (Hcv 1 Rlt_0_1) => {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hli (u Ncv - 1) Ncv) => {Hli} ni [Hni Hli].
  move: (Hcv ni Hni) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj1 Hcv) ; 
  apply Rle_not_lt, Rlt_le, Hli.
  case: (Hcv 1 Rlt_0_1) => {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hls (u Ncv + 1) Ncv) => {Hls} ns [Hns Hls].
  move: (Hcv ns Hns) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj2 Hcv) ; 
  apply Rle_not_lt, Rlt_le, Hls.
  case: (Hcv 1 Rlt_0_1) => {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hls (u Ncv - 1)) => {Hls} Ns Hls.
  move: (Hcv (Ncv + Ns)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj1 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, Hls, le_plus_r.
  exists (Rbar_limsup_seq (fun n : nat => Finite (u n))).
  apply Rbar_is_limsup_liminf_lim.
  rewrite /Rbar_limsup_seq ; by case: Rbar_ex_limsup_seq.
  rewrite H ; rewrite /Rbar_liminf_seq ; by case: Rbar_ex_liminf_seq.
  exists (Lim_seq u).
  case: H ; case => [l | | ] H.
  apply is_lim_seq_correct in H.
  rewrite (is_lim_seq_unique _ _ H) => e He.
  by apply (H (mkposreal e He)).
  case: (Hcv 1 Rlt_0_1) => {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (H (u Ncv + 1)) => {H} /= N H.
  move: (Hcv (Ncv + N)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj2 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, H, le_plus_r.
  case: (Hcv 1 Rlt_0_1) => {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (H (u Ncv - 1)) => {H} /= N H.
  move: (Hcv (Ncv + N)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj1 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, H, le_plus_r.
Qed.
