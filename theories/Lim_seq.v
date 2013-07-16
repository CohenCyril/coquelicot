Require Import Reals Rcomplements Markov.
Require Import Sup_seq Rbar_theory Total_sup ssreflect.
Open Scope R_scope.

(** * Definition and unicity *)

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
Definition ex_f_lim_seq (u : nat -> R) :=
  exists l : R, is_lim_seq u l.
Definition Lim_seq (u : nat -> R) : Rbar := 
  Rbar_div_pos (Rbar_plus (LimSup_seq u) (LimInf_seq u))
    {| pos := 2; cond_pos := Rlt_R0_R2 |}.

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

Lemma is_lim_seq_correct (u : nat -> R) (l : Rbar) :
  is_lim_seq u l <-> Rbar_is_lim_seq (fun n => Finite (u n)) l.
Proof.
  split ; by case: l.
Qed.
Lemma Lim_seq_Rbar (u : nat -> R) :
  Lim_seq u = Rbar_lim_seq (fun n => Finite (u n)).
Proof.
  rewrite /Lim_seq /Rbar_lim_seq.
  rewrite (LimSup_seq_correct u) (LimInf_seq_correct u) /= ;
  case: (Rbar_plus _ _) => //= ; field.
Qed.
Lemma ex_f_lim_seq_correct (u : nat -> R) :
  ex_f_lim_seq u <-> ex_lim_seq u /\ is_finite (Lim_seq u).
Proof.
  split.
  case => l Hl.
  split.
  by exists l.
  rewrite Lim_seq_Rbar (Rbar_is_lim_seq_uniq _ l).
  by [].
  by apply is_lim_seq_correct.
  case ; case => l Hl Hl0.
  exists (real (Lim_seq u)).
  rewrite Hl0.
  rewrite Lim_seq_Rbar is_lim_seq_correct.
  apply Rbar_lim_seq_correct.
  by exists l.
Qed.

Lemma ex_lim_seq_dec (u : nat -> R) :
  {ex_lim_seq u} + {~ex_lim_seq u}.
Proof.
  apply (Rbar_ex_lim_seq_dec (fun n => Finite (u n))).
Qed.

(** ** Unicity *)

Lemma is_lim_seq_unique (u : nat -> R) :
  forall l, is_lim_seq u l -> Lim_seq u = l.
Proof.
  move => l ; move/is_lim_seq_correct => Hl ; rewrite Lim_seq_Rbar ;
  by rewrite (Rbar_is_lim_seq_uniq _ _ Hl).
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
  ex_f_lim_seq u -> is_lim_seq u (real (Lim_seq u)).
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

(** * Operations *)

(** Extentionality *)

Lemma is_lim_seq_ext_loc : forall u v l, 
  (exists N, forall n, (N <= n)%nat -> u n = v n) 
    -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  intros.
  apply (Rbar_is_lim_seq_ext_loc (fun n => Finite (u n)) (fun n => Finite (v n))).
  case: H => N H.
  exists N => n Hn ; by apply Rbar_finite_eq, H.
  apply H0.
Qed.
Lemma ex_lim_seq_ext_loc : forall u v, 
  (exists N, forall n, (N <= n)%nat -> u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => u v H [l H0].
  exists l ; by apply is_lim_seq_ext_loc with u.
Qed.
Lemma Lim_seq_ext_loc :  forall u v, 
  (exists N, forall n, (N <= n)%nat -> u n = v n) -> 
  Lim_seq u = Lim_seq v.
Proof.
  intros.
  rewrite /Lim_seq.
  apply (f_equal (fun x => Rbar_div_pos x _)).
  case: H => N H.
  apply f_equal2.
  rewrite ?LimSup_seq_correct.
  apply Rbar_limsup_seq_ext_loc.
  exists N => n Hn ; by apply Rbar_finite_eq, H.
  rewrite ?LimInf_seq_correct.
  apply Rbar_liminf_seq_ext_loc.
  exists N => n Hn ; by apply Rbar_finite_eq, H.
Qed.

Lemma is_lim_seq_ext : forall u v l, 
  (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  intros.
  apply (Rbar_is_lim_seq_ext (fun n => Finite (u n)) (fun n => Finite (v n))).
  move => n ; apply f_equal, H.
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

(** Sub sequences *)

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

(** Additive *)

Lemma is_lim_seq_opp (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_lim_seq (fun n => -u n) (Rbar_opp l).
Proof.
  move => Hu.
  apply is_lim_seq_correct.
  eapply (Rbar_is_lim_seq_opp (fun n => Finite _)).
  by apply Hu.
  by [].
Qed.
Lemma ex_lim_seq_opp (u : nat -> R) :
  ex_lim_seq u <-> ex_lim_seq (fun n => -u n).
Proof.
  split ; case => l Hl ; exists (Rbar_opp l).
  by apply is_lim_seq_opp.
  apply is_lim_seq_ext with (fun n => - - u n).
  move => n ; by apply Ropp_involutive.
  by apply is_lim_seq_opp.
Qed.
Lemma Lim_seq_opp :
  forall u,
  Lim_seq (fun n => - u n) = Rbar_opp (Lim_seq u).
Proof.
  intros u.
  rewrite 2?Lim_seq_Rbar.
  by apply (Rbar_lim_seq_opp (fun n => u n)).
Qed.

Lemma is_lim_seq_plus (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> 
    is_Rbar_plus l1 l2 (Rbar_plus l1 l2) ->
    is_lim_seq (fun n => u n + v n) (Rbar_plus l1 l2).
Proof.
  intros.
  apply is_lim_seq_correct.
  eapply (Rbar_is_lim_seq_plus (fun n => Finite _) (fun n => Finite _)).
  by apply H.
  by apply H0.
  by apply H1.
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

Lemma is_lim_seq_minus (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 
  -> (is_Rbar_minus l1 l2 (Rbar_minus l1 l2))
    -> is_lim_seq (fun n => u n - v n) (Rbar_minus l1 l2).
Proof.
  move => H1 H2.
  apply (is_lim_seq_plus _ _ l1 (Rbar_opp l2)).
  exact: H1.
  exact: is_lim_seq_opp.
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

(** Multiplicative *)

Lemma is_lim_seq_inv (u : nat -> R) (l : Rbar) :
  is_lim_seq u l 
    -> l <> 0 -> 
    is_lim_seq (fun n => / u n) (Rbar_inv l).
Proof.
  intros.
  apply is_lim_seq_correct.
  eapply (Rbar_is_lim_seq_inv (fun n => Finite _)).
  by apply H.
  by apply H0.
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

Lemma is_lim_seq_scal_l (u : nat -> R) (a : R) (lu : Rbar) :
  is_lim_seq u lu -> is_Rbar_mult a lu (Rbar_mult a lu) ->
    is_lim_seq (fun n => a * u n) (Rbar_mult a lu).
Proof.
  move => Hu Hl.
  apply is_lim_seq_correct.
  eapply (Rbar_is_lim_seq_mult (fun n => Finite _) (fun n => Finite _)).
  by apply Rbar_is_lim_seq_const.
  by apply Hu.
  by apply Hl.
Qed.
Lemma ex_lim_seq_scal_l (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => a * u n).
Proof.
  move => [l H].
  case: (Req_dec a 0) => Ha.
  exists 0.
  apply is_lim_seq_ext with (fun _ => 0).
  move => n ; rewrite Ha ; by rewrite Rmult_0_l.
  by apply is_lim_seq_correct, Rbar_is_lim_seq_const.
  exists (Rbar_mult a l).
  eapply is_lim_seq_scal_l.
  apply H.
  apply sym_not_eq in Ha.
  case: (l) => [x | | ] //= ; case: Rle_dec => // Hx.
  by case: Rle_lt_or_eq_dec.
  by apply Rnot_le_lt.
  by case: Rle_lt_or_eq_dec.
  by apply Rnot_le_lt.
Qed.
Lemma Lim_seq_scal_l (u : nat -> R) (a : R) : 
  Lim_seq (fun n => a * u n) = Rbar_mult a (Lim_seq u).
Proof.
  case: (Req_dec a 0) => [ -> | Ha].
    rewrite -(Lim_seq_ext (fun _ => 0)) /=.
    rewrite Lim_seq_Rbar Rbar_lim_seq_const.
    case: (Lim_seq u) => [l | | ] //.
    by rewrite Rmult_0_l.
    case: Rle_dec (Rle_refl 0) => // H _.
    case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //.
    case: Rle_dec (Rle_refl 0) => // H _.
    case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //.
    move => n ; by rewrite Rmult_0_l.
  wlog: u a Ha / (0 < a) => [Hw | {Ha} Ha].
    case: (Rle_lt_dec 0 a) => Ha'.
    apply Hw.
    by apply Ha.
    apply sym_not_eq in Ha ; by case: Ha'.
    have Ha0 := Ropp_0_gt_lt_contravar _ Ha' ; 
    move: (Hw (fun n => - u n) _ (Ropp_neq_0_compat a Ha) Ha0) => {Hw}.
    rewrite (Lim_seq_ext (fun n : nat => - a * - u n) (fun n : nat => a * u n)).
    move => ->.
    rewrite /Lim_seq.
    rewrite LimSup_seq_opp.
    rewrite LimInf_seq_opp.
    case: (LimInf_seq u) => [li | | ] ; case: (LimSup_seq u) => [ls | | ] //=.
    apply Rbar_finite_eq ; field.
    case: Rle_dec (Rlt_le _ _ Ha0) => // Ha1 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha0) => // {Ha1} _ _.
    case: Rle_dec (Rlt_not_le _ _ Ha') => // Ha1 _.
    case: Rle_dec (Rlt_le _ _ Ha0) => // Ha1 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha0) => // {Ha1} _ _.
    case: Rle_dec (Rlt_not_le _ _ Ha') => // Ha1 _.
    case: Rle_dec (Rlt_le _ _ Ha0) => // Ha1 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha0) => // {Ha1} _ _.
    case: Rle_dec (Rlt_not_le _ _ Ha') => // Ha1 _.
    case: Rle_dec (Rlt_le _ _ Ha0) => // Ha1 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha0) => // {Ha1} _ _.
    case: Rle_dec (Rlt_not_le _ _ Ha') => // Ha1 _.
    apply Rbar_finite_eq ; field.
    case: Rle_dec (Rlt_le _ _ Ha0) => // Ha1 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha0) => // {Ha1} _ _.
    case: Rle_dec (Rlt_not_le _ _ Ha') => // Ha1 _.
    apply Rbar_finite_eq ; field.
    case: Rle_dec (Rlt_le _ _ Ha0) => // Ha1 _.
    case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha0) => // {Ha1} _ _.
    case: Rle_dec (Rlt_not_le _ _ Ha') => // Ha1 _.
    move => n ; ring.
  
  rewrite /Lim_seq /LimSup_seq /LimInf_seq ;
  case: ex_LimSup_seq => ls' Hls' ; case: ex_LimSup_seq => ls Hls ;
  case: ex_LimInf_seq => li' Hli' ; case: ex_LimInf_seq => li Hli /=.
  case: Rle_dec (Rlt_le _ _ Ha) => // Ha' _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Ha) => // {Ha'} _ _.
(* 0 < a *)
  replace ls' with (Rbar_mult_pos ls (mkposreal _ Ha)).
  replace li' with (Rbar_mult_pos li (mkposreal _ Ha)).
  case: (ls) ; case: (li) => //= ; intros ; apply Rbar_finite_eq ; field.
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
Qed.
Lemma is_lim_seq_scal_r (u : nat -> R) (a : R) (lu : Rbar) :
  is_lim_seq u lu -> is_Rbar_mult lu a (Rbar_mult lu a) ->
    is_lim_seq (fun n => u n * a) (Rbar_mult lu a).
Proof.
  move => Hu Hl.
  apply is_lim_seq_ext with ((fun n : nat => a * u n)) ; try by intuition.
  rewrite Rbar_mult_comm.
  apply is_lim_seq_scal_l.
  by apply Hu.
  rewrite Rbar_mult_comm.
  by apply is_Rbar_mult_comm.
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

Lemma is_lim_seq_mult (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 
  -> is_Rbar_mult l1 l2 (Rbar_mult l1 l2)
    -> is_lim_seq (fun n => u n * v n) (Rbar_mult l1 l2).
Proof.
  intros.
  apply is_lim_seq_correct.
  eapply (Rbar_is_lim_seq_mult (fun n => Finite _) (fun n => Finite _)).
  by apply H.
  by apply H0.
  by apply H1.
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

Lemma is_lim_seq_div (u v : nat -> R) (l1 l2 : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l2 <> 0 ->
  is_Rbar_div l1 l2 (Rbar_div l1 l2)
    -> is_lim_seq (fun n => u n / v n) (Rbar_div l1 l2).
Proof.
  intros.
  apply is_lim_seq_correct.
  eapply (Rbar_is_lim_seq_div (fun n => Finite (u n)) (fun n => Finite (v n))).
  by apply H.
  by apply H0.
  by apply H1.
  by apply H2.
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

(** * Convergence critrium *)

(** ** Cauchy criterium *)

Definition ex_lim_seq_cauchy (u : nat -> R) :=
  forall eps : posreal, exists N : nat, forall n m,
    (N <= n)%nat -> (N <= m)%nat -> Rabs (u n - u m) < eps.
Lemma ex_lim_seq_cauchy_corr (u : nat -> R) :
  (ex_f_lim_seq u) <-> ex_lim_seq_cauchy u.
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
  
  have H : (Rbar_ex_lim_seq (fun n => Finite (u n))).
  have H : Rbar_limsup_seq (fun n => Finite (u n)) = Rbar_liminf_seq (fun n => Finite (u n)).
  rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq ; case => /= [ls | | ] Hls.
  rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq ; case => /= [li | | ] Hli.
  apply Rbar_finite_eq ; apply Rle_antisym ;
  apply le_epsilon => e He ; apply Rlt_le ; set eps := mkposreal e He ;
  case: (Hcv (pos_div_2 eps)) => {Hcv} /= Ncv Hcv.
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
  case: (Hcv (mkposreal _ Rlt_0_1)) => {Hcv} /= Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hli (u Ncv + 1)) => {Hli} Ni Hli.
  move: (Hcv (Ncv + Ni)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj2 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, Hli, le_plus_r.
  case: (Hcv (mkposreal _ Rlt_0_1)) => {Hcv} /= Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hli (u Ncv - 1) Ncv) => {Hli} ni [Hni Hli].
  move: (Hcv ni Hni) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj1 Hcv) ; 
  apply Rle_not_lt, Rlt_le, Hli.
  case: (Hcv (mkposreal 1 Rlt_0_1)) => {Hcv} /= Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (Hls (u Ncv + 1) Ncv) => {Hls} ns [Hns Hls].
  move: (Hcv ns Hns) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj2 Hcv) ; 
  apply Rle_not_lt, Rlt_le, Hls.
  case: (Hcv (mkposreal 1 Rlt_0_1)) => {Hcv} /= Ncv Hcv.
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
  case: H => l H ; replace (Lim_seq u) with l.
  exists (real l) ; case: l H => [l | | ] H.
  by apply is_lim_seq_correct in H.
  case: (Hcv (mkposreal 1 Rlt_0_1)) => /= {Hcv} Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (H (u Ncv + 1)) => {H} /= N H.
  move: (Hcv (Ncv + N)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj2 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, H, le_plus_r.
  case: (Hcv (mkposreal 1 Rlt_0_1)) => {Hcv} /= Ncv Hcv.
  move: (fun n Hn => Hcv n Ncv Hn (le_refl _)) ; rewrite /R_dist => {Hcv} Hcv.
  case: (H (u Ncv - 1)) => {H} /= N H.
  move: (Hcv (Ncv + N)%nat (le_plus_l _ _)) => {Hcv} Hcv.
  apply Rabs_lt_between' in Hcv.
  have : False => // ; move: (proj1 Hcv) ; 
  by apply Rle_not_lt, Rlt_le, H, le_plus_r.
  by apply sym_equal, is_lim_seq_unique.
Qed.

(** ** Order of limits *)
  
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
  apply Rbar_is_lim_seq_le with u v.
  by apply Hu.
  by apply Hv.
  move => n ; by apply Rbar_finite_le.
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
Qed.


Lemma ex_f_lim_seq_decr (u : nat -> R) (M : R) :
  (forall n, (u (S n)) <= (u n)) -> (forall n, M <= u n)
    -> ex_f_lim_seq u.
Proof.
  intros.
  apply ex_f_lim_seq_correct.
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
Lemma ex_f_lim_seq_incr (u : nat -> R) (M : R) :
  (forall n, (u n) <= (u (S n))) -> (forall n, u n <= M)
    -> ex_f_lim_seq u.
Proof.
  intros.
  case: (ex_f_lim_seq_decr (fun n => - u n) (- M)).
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
  -> ex_f_lim_seq u /\ ex_f_lim_seq v /\ Lim_seq u = Lim_seq v.
Proof.
  move => Hu Hv H0.
  suff H : forall n, u n <= v n.
  suff Eu : ex_f_lim_seq u.
    split ; try auto.
  suff Ev : ex_f_lim_seq v.
    split ; try auto.

  apply is_lim_seq_unique in H0.
  rewrite Lim_seq_minus in H0 ; try by intuition.
  apply ex_f_lim_seq_correct in Eu.
  apply ex_f_lim_seq_correct in Ev.
  rewrite -(proj2 Eu) -(proj2 Ev) /= in H0 |- *.
  apply Rbar_finite_eq in H0 ; apply Rbar_finite_eq.
  by apply sym_eq, Rminus_diag_uniq, H0.
  by apply ex_f_lim_seq_correct.
  by apply ex_f_lim_seq_correct.
  exists (Rbar_minus (Lim_seq v) (Lim_seq u)).
  apply ex_f_lim_seq_correct in Eu.
  apply ex_f_lim_seq_correct in Ev.
  by rewrite -(proj2 Eu) -(proj2 Ev).
  apply ex_f_lim_seq_decr with (u O) => //.
  move => n ; apply Rle_trans with (2 := H _).
  elim: n => [ | n IH].
  by apply Rle_refl.
  by apply Rle_trans with (2 := Hu _).
  apply ex_f_lim_seq_incr with (v O) => //.
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

(** * Particular limits *)

(** Constant sequences *)

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

(** Identity sequence *)

Lemma is_lim_seq_id :
  is_lim_seq INR p_infty.
Proof.
  apply Rbar_is_lim_seq_id.
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
  apply is_lim_seq_opp.
  by apply is_lim_seq_id.
  by [].
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
  have : ex_lim_seq (fun n : nat => u n).
    case: H => l H ; exists l ; by apply is_lim_seq_correct.
  move => {H} H.
  apply Lim_seq_correct in H.
  exists (real (Lim_seq (fun n : nat => u n))).
  case: (Lim_seq (fun n : nat => u n)) H => [l | | ] /= H.
  move => e He.
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
