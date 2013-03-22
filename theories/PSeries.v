Require Import Reals Even Div2 MinMax ssreflect.
Require Import Lim_seq Floor Rcomplements Rbar_theory Sup_seq Total_sup.
Require Import Lim_fct Derive RInt.

(** todo: move this to Rcomplements.v *)

Definition Zpow (x : R) (n : Z) : R :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ (nat_of_P p)
    | Zneg p => / x ^ (nat_of_P p)
  end.

Fixpoint is_even (n : nat) :=
  match n with
    | O => 1
    | 1%nat => 0
    | S (S n) => is_even n
  end.
Definition is_odd (n : nat) := is_even (S n).

Lemma is_even_simplify (n : nat) :
  is_even n = match (even_odd_dec n) with
    | left _ => 1
    | right _ => 0
  end.
Proof.
  move: n ; apply ind_0_1_SS => // n Hn.
  simpl.
  by case: (even_odd_dec n) Hn => /=.
Qed.

Lemma sum_f_rw (a : nat -> R) (n m : nat) :
  (n < m)%nat -> sum_f (S n) m a = sum_f_R0 a m - sum_f_R0 a n.
Proof.
  move => Hnm ; rewrite /sum_f.
  elim: m a n Hnm => [ | m IH] a n Hnm.
  by apply lt_n_O in Hnm.
  rewrite (decomp_sum _ _ (lt_O_Sn _)) /=.
  case: n Hnm => [ | n] Hnm.
  rewrite -minus_n_O /= ; ring_simplify.
  elim: (m) {IH} => /= [ | k IH].
  by [].
  by rewrite -plus_n_Sm plus_0_r IH.
  rewrite (decomp_sum _ _ (lt_O_Sn _)) /= ; ring_simplify.
  apply lt_S_n in Hnm.
  rewrite -(IH _ _ Hnm).
  elim: (m - S n)%nat {IH} => /= [ | k IH].
  by [].
  by rewrite -plus_n_Sm IH.
Qed.

Lemma Rdiv_lt (a b c : R) :
  c > 0 -> (a * c < b <-> a < b / c).
Proof.
  move => Hc.
  split => H.
  replace a with ((a*c)/c) by (field ; apply Rgt_not_eq, Hc).
  apply Rmult_lt_compat_r.
  by apply Rinv_0_lt_compat.
  exact: H.
  replace b with ((b/c)*c) by (field ; apply Rgt_not_eq, Hc).
  by apply Rmult_lt_compat_r.
Qed.

Lemma Rlt_Rminus (r1 r2 : R) :
  r1 < r2 <-> 0 < r2 - r1.
Proof.
  split => H.
  by apply Rlt_Rminus.
  rewrite -(Rplus_0_l r1).
  replace r2 with ((r2-r1) + r1) by ring.
  by apply Rplus_lt_compat_r.
Qed.

Definition Rbar_min (x y : Rbar) :=
  match (Rbar_le_dec x y) with
    | left _ => x
    | right _ => y
  end.

Lemma ex_sqrt (x : R) : {l : R | (l^2 = x /\ 0 <= l) \/ (x < 0 /\ l = 0)}.
Proof.
  case: (total_order_T x 0) => Hx0.
  case: Hx0 => Hx0.
  exists 0 ; by right.
  exists 0 ; left ; rewrite Hx0 /= ; split ; [ ring | by apply Rle_refl ].
  wlog: x Hx0 / (x < 1) => [Hw | Hx1].
    case: (total_order_T 1 x) => Hx1.
    case: Hx1 => Hx1.
    case: (Hw (/x)) => {Hw} [ | | l Hw].
    by apply Rlt_gt, Rinv_0_lt_compat.
    by rewrite -(Rmult_1_l (/x)) -Rdiv_lt_1.
    exists (/l) ; case: Hw => Hw.
    left ; rewrite -Rinv_pow.
    split.
    rewrite (proj1 Hw) Rinv_involutive.
    by [].
    by apply Rgt_not_eq, Rlt_gt.
    apply Rlt_le, Rinv_0_lt_compat.
    case: Hw => Hw ; case => Hw0.
    by [].
    contradict Hw0 ; apply sym_not_eq.
    contradict Hw ; rewrite Hw pow_ne_zero.
    by apply Rlt_not_eq, Rinv_0_lt_compat.
    by [].
    case: Hw => Hw Hw0.
    contradict Hw ; rewrite Hw pow_ne_zero.
    by apply Rlt_not_eq, Rinv_0_lt_compat.
    by [].
    case: Hw => Hw _.
    by apply Rinv_0_lt_compat, Rlt_le, Rle_not_lt in Hx0.
    exists 1 ; left.
    rewrite -Hx1 ; split ; [ring | exact: Rle_0_1].
    by apply Hw.
  
  set Xn := fix f n := match n with
    | O => (0,1)
    | S n => let a := fst (f n) in
             let b := snd (f n) in
             let c := (a+b)/2 in
             match (Rlt_dec (c^2) x) with
               | left _ => (c,b)
               | right _ => (a,c)
             end
  end.
  have H : forall n, snd (Xn n) = fst (Xn n) + /2^n.
    elim => /= [ | n ->].
    field.
    case: Rlt_dec => /= _ ; field ;
    apply Rgt_not_eq, Rlt_gt, pow_lt, Rlt_R0_R2.
  have H0 : (forall n m, (n <= m)%nat -> fst (Xn n) <= fst (Xn m)) 
         /\ (forall n m, (n <= m)%nat -> snd (Xn m) <= snd (Xn n)).
    suff H0 : forall n,
      fst (Xn n) <= fst (Xn (S n)) /\ snd (Xn (S n)) <= snd (Xn n).
      split ; move => n m ; elim: m n => [ | m IH] n Hn.
      rewrite (le_n_0_eq _ Hn) ; by apply Rle_refl.
      apply le_lt_eq_dec in Hn ; case: Hn => [Hn | <-].
      apply Rle_trans with (fst (Xn m)).
      by apply IH, lt_n_Sm_le.
      by apply H0.
      by apply Rle_refl.
      rewrite (le_n_0_eq _ Hn) ; by apply Rle_refl.
      apply le_lt_eq_dec in Hn ; case: Hn => [Hn | <-].
      apply Rle_trans with (snd (Xn m)).
      by apply H0.
      by apply IH, lt_n_Sm_le.
      by apply Rle_refl.
    elim => [ | n IH] /=.
    case: Rlt_dec => /= _ ; rewrite Rplus_0_l /Rdiv Rmult_1_l ; split ;
    try by intuition.
    apply Rlt_le, Rlt_Rminus ; field_simplify ;
    rewrite -Rdiv_1  /Rdiv Rmult_1_l ; by intuition.
    rewrite -/(Xn (S _)) ; case: Rlt_dec => /= _ ; rewrite -/(Xn (S _)) H ;
    split ; try by intuition.
    apply Rlt_le, Rlt_Rminus ; field_simplify.
    rewrite -Rdiv_1 /Rdiv Rmult_1_l -/(pow _ (S (S n))).
    apply Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt, pow_lt, Rlt_R0_R2.
    apply Rlt_le, Rlt_Rminus ; field_simplify.
    rewrite -Rdiv_1 /Rdiv Rmult_1_l -/(pow _ (S (S n))).
    apply Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt, pow_lt, Rlt_R0_R2.
  
  exists (Lim_seq (fun n => fst (Xn n))) ; left.
  have H1 : forall (u : nat -> R) (l : R), is_lim_seq u l -> 
    is_lim_seq (fun n => (u n) ^ 2) (l ^ 2).
    move => u l Hu eps.
    case: (Hu (mkposreal _ Rlt_0_1)) => N0 H1.
    have : forall n : nat, (N0 <= n)%nat -> Rabs (u n) < Rabs l + 1.
    move => n Hn.
    replace (Rabs (u n)) with (Rabs l + (Rabs (u n) - Rabs l)) by ring.
    apply Rplus_lt_compat_l.
    apply Rle_lt_trans with (1 := Rabs_triang_inv _ _).
    by apply H1.
    move => {H1} H2.
    case: (fun He => Hu (mkposreal (eps/(2 * Rabs l + 1)) He)) 
      => [ | {Hu} He N1 Hu] ; simpl in Hu.
      apply Rdiv_lt_0_compat.
      by apply eps.
      apply Rplus_le_lt_0_compat.
      apply Rmult_le_pos.
      by apply Rlt_le, Rlt_R0_R2.
      by apply Rabs_pos.
      by apply Rlt_0_1.
    exists (N0 + N1)%nat => n Hn.
    replace (u n ^ 2 - l ^ 2) 
      with ((u n - l) * (u n + l)) by (simpl ; ring).
    rewrite Rabs_mult.
    replace (pos eps) with ((eps / (2 * Rabs l + 1)) * ((Rabs l + 1) + Rabs l)).
    apply Rmult_le_0_lt_compat.
    by apply Rabs_pos.
    by apply Rabs_pos.
    apply Hu ; by intuition.
    apply Rle_lt_trans with (1 := Rabs_triang _ _).
    apply Rplus_lt_compat_r.
    apply H2 ; by intuition.
    field ; apply Rgt_not_eq, Rlt_gt.
    apply Rplus_le_lt_0_compat.
    apply Rmult_le_pos.
    by apply Rlt_le, Rlt_R0_R2.
    by apply Rabs_pos.
    by apply Rlt_0_1.
  have H2 : is_lim_seq (fun n : nat => fst (Xn n)) (Lim_seq (fun n : nat => fst (Xn n))).
    apply Lim_seq_correct.
    apply ex_lim_seq_cauchy_corr => eps.
    have : exists N, forall n, (N <= n)%nat -> /2^n < eps.
    case: (fun H => pow_lt_1_zero (/2) H eps (cond_pos eps)) => [ | N H2].
    rewrite Rabs_pos_eq.
    apply Rlt_Rminus ; rewrite {1}(double_var 1) /Rdiv Rmult_1_l ;
    ring_simplify ; by intuition.
    apply Rlt_le ; by intuition.
    exists N => n Hn ;
    replace (/2^n) with (Rabs ((/2)^n)).
    apply H2, Hn.
    rewrite Rinv_pow.
    apply Rabs_pos_eq.
    apply pow_le, Rlt_le ; by intuition.
    apply Rgt_not_eq, Rlt_gt, Rlt_R0_R2.
    case => N H2.
    exists N => n m Hn Hm.
    apply Rle_lt_trans with (/2^(min n m)).
    wlog : n m Hn Hm / (m < n)%nat => [ Hw | Hnm ].
    case: (le_lt_dec m n) => Hnm.
    apply le_lt_eq_dec in Hnm ; case: Hnm => Hnm.
    by apply Hw.
    rewrite Hnm Rminus_eq0 Rabs_R0.
    apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
    rewrite -Ropp_minus_distr' Rabs_Ropp min_comm.
    by apply Hw.
    case: (min_spec n m) ; case => H3 H4.
    by apply lt_le_weak, le_not_lt in H3.
    rewrite H4.
    clear H3 H4 Hn Hm.
    rewrite Rabs_pos_eq.
    replace (/ 2 ^ m) with ((snd (Xn m)) - (fst (Xn m))).
    apply Rplus_le_compat_r.
    apply Rle_trans with ((snd (Xn n))).
    rewrite H ; apply Rlt_le, Rlt_Rminus ; ring_simplify ;
    apply Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
    by apply H0, lt_le_weak.
    rewrite H ; ring.
    rewrite -(Rminus_eq0 (fst (Xn m))) ; apply Rplus_le_compat_r.
    by apply H0, lt_le_weak.
    
    case: (min_spec n m) ; case => H3 H4.
    rewrite H4 ; by apply H2.
    rewrite H4 ; by apply H2.
    
    move: (H1 _ _ H2) => {H1} H1.
    move: (Lim_seq (fun n : nat => fst (Xn n))) H1 H2 => l H1 H2.
    apply is_lim_seq_unique in H1.
    rewrite -H1 ; split.
    apply is_lim_seq_unique => eps.
    have : exists N, 2/2^N + /4^N < eps.
    case: (fun H => pow_lt_1_zero (/4) H (eps/2) (is_pos_div_2 eps)) => [ | N0 H3].
    rewrite Rabs_pos_eq.
    apply Rlt_Rminus ; field_simplify ; rewrite -Rdiv_1 ;
    apply Rdiv_lt_0_compat ;
    [apply Rplus_lt_0_compat | apply Rmult_lt_0_compat ] ; by intuition.
    apply Rlt_le, Rinv_0_lt_compat ; apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    case: (fun H => pow_lt_1_zero (/2) H (eps/2) (is_pos_div_2 eps)) => [ | N1 H4].
    rewrite Rabs_pos_eq.
    apply Rlt_Rminus ; field_simplify ; rewrite -Rdiv_1 /Rdiv Rmult_1_l ; by intuition.
    by intuition.
    
    set N := (N0+S N1)%nat ; exists N ;
    replace (/4^N) with (Rabs ((/4)^N)) ;
    try replace (2/2^N) with (Rabs (2*(/2)^N)).
    rewrite (double_var eps).
    apply Rplus_lt_compat.
    rewrite /N -plus_n_Sm /= ; (field_simplify (2 * (/ 2 * (/ 2) ^ (N0 + N1)))) ;
    rewrite -Rdiv_1.
    by apply H4, le_plus_r.
    by apply H3, le_plus_l.
    rewrite -Rinv_pow.
    apply Rabs_pos_eq.
    apply Rlt_le, Rdiv_lt_0_compat.
    apply Rlt_R0_R2.
    apply pow_lt, Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt, Rlt_R0_R2.
    rewrite Rinv_pow.
    apply Rabs_pos_eq.
    apply Rlt_le, pow_lt, Rinv_0_lt_compat, Rmult_lt_0_compat ; by apply Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt, Rmult_lt_0_compat ; by apply Rlt_R0_R2.
    rewrite -Rinv_pow.
    apply Rabs_pos_eq.
    apply Rlt_le, Rdiv_lt_0_compat.
    apply Rlt_R0_R2.
    apply pow_lt, Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt, Rlt_R0_R2.
    
    case => N H3.
    exists N => n Hn.
    apply Rle_lt_trans with (2 := H3).
    rewrite -Ropp_minus_distr' Rabs_Ropp.
    apply Rabs_le_between'.
    split.
    apply Rle_trans with (fst (Xn n) ^ 2).
    apply Rlt_le, Rlt_Rminus ; ring_simplify.
    rewrite /Rdiv ?Rinv_pow.
    apply Rplus_lt_0_compat.
    apply Rmult_lt_0_compat.
    by apply Rlt_R0_R2.
    apply pow_lt, Rinv_0_lt_compat ; apply Rlt_R0_R2.
    apply pow_lt, Rinv_0_lt_compat, Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt, Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply Rgt_not_eq, Rlt_gt ; apply Rlt_R0_R2.
    
    elim: (n) => [ | m IH] /= ; rewrite -?/(pow _ 2).
    simpl ; rewrite Rmult_0_l ; by apply Rlt_le.
    case: Rlt_dec => /= ; by intuition.
    apply Rle_trans with ((snd (Xn n))^2).
    elim: (n) => [ | m IH] /= ; rewrite -?/(pow _ 2).
    simpl ; rewrite ?Rmult_1_l ; by apply Rlt_le.
    case: Rlt_dec => H4 /= ; rewrite -/(pow _ 2).
    by [].
    by apply Rnot_lt_le.
    rewrite H.
    replace ((fst (Xn n) + / 2 ^ n) ^ 2) with 
      (fst (Xn n) ^ 2 + (2 * fst (Xn n) / 2 ^ n + / 4 ^ n)).
      apply Rplus_le_compat_l.
      apply Rplus_le_compat.
      apply Rmult_le_compat.
      apply Rmult_le_pos.
      apply Rlt_le, Rlt_R0_R2.
      replace 0 with (fst (Xn O)) by auto.
      apply H0, le_O_n.
      apply Rlt_le, Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
      rewrite -{2}(Rmult_1_r 2) ; apply Rmult_le_compat_l.
      apply Rlt_le, Rlt_R0_R2.
      replace 1 with (snd (Xn O)) by auto.
      apply Rle_trans with (snd (Xn n)).
      rewrite H ; apply Rlt_le, Rlt_Rminus ; ring_simplify ;
      apply Rinv_0_lt_compat, pow_lt, Rlt_R0_R2.
      apply H0, le_O_n.
      apply Rle_Rinv.
      apply pow_lt, Rlt_R0_R2.
      apply pow_lt, Rlt_R0_R2.
      apply Rle_pow ; by intuition.
      apply Rle_Rinv.
      apply pow_lt, Rmult_lt_0_compat ; apply Rlt_R0_R2.
      apply pow_lt, Rmult_lt_0_compat ; apply Rlt_R0_R2.
      apply Rle_pow ; try by intuition.
      rewrite -{1}(Rmult_1_l 1) ; apply Rmult_le_compat ; by intuition.
      apply Rminus_diag_uniq ; simpl ; ring_simplify.
      rewrite /Rdiv ; ring_simplify ; rewrite Rplus_comm.
      apply Rminus_diag_eq.
      rewrite ?Rinv_pow.
      elim: (n) => /= [ | m ->] ; field.
      apply Rgt_not_eq, Rlt_gt, Rlt_R0_R2.
      apply Rgt_not_eq, Rlt_gt, Rmult_lt_0_compat ; apply Rlt_R0_R2.
      apply is_lim_seq_le with (2 := is_lim_seq_const 0) (3 := H2).
      move => n ; replace 0 with (fst (Xn O)) by auto.
      apply H0, le_O_n.
Qed.
Definition sqrt (x : R) := projT1 (ex_sqrt x).

Lemma sqrt_pos (x : R) : 0 <= sqrt x.
Proof.
  rewrite /sqrt ; case: ex_sqrt => l ;
  case => Hl /=.
  by apply Hl.
  rewrite (proj2 Hl) ; by apply Rle_refl.
Qed.
Lemma sqrt_pos_lt (x : R) : (0 < x) -> 0 < sqrt x.
Proof.
  rewrite /sqrt ; case: ex_sqrt => l ;
  case => Hl /= Hx.
  case: Hl => Hl ; case => H.
  by apply H.
  apply Rlt_not_eq in Hx ; contradict Hx.
  rewrite -Hl -H ; simpl ; ring.
  apply Rlt_le, Rle_not_lt in Hx ; by intuition.
Qed.

Lemma sqrt_sqrt (x : R) : (0 <= x) -> sqrt x * sqrt x = x.
Proof.
  rewrite /sqrt ; case: ex_sqrt => l ;
  case ; case => Hl H /= Hx.
  rewrite -Hl /= ; ring.
  by apply Rle_not_lt in Hx.
Qed.

(** * Sequence of functions *)

(** ** Definitions *)

Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) :=
  forall x : R, D x -> ex_lim_seq (fun n => fn n x).

Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) :=
  forall eps : posreal, exists N : nat, 
  forall (n : nat) (x : R), D x -> (N <= n)%nat
    -> Rabs (fn n x - (Lim_seq (fun n => fn n x))) < eps.
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) :=
  forall eps : posreal, exists N : nat, 
  forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat
    -> Rabs (fn n x - fn m x) < eps.

(** equivalences with standard library *)

Lemma CVU_dom_equiv (fn : nat -> R -> R) (f : R -> R) (x : R) (r : posreal) :
  (forall y, (Boule x r y) -> f y = Lim_seq (fun n => fn n y)) ->
  (CVU fn f x r <-> CVU_dom fn (Boule x r)).
Proof.
  split ; move => Hcvu.
  have Hf : forall y, Boule x r y -> is_lim_seq (fun n => fn n y) (f y).
    move => y Hy [e He] /=.
    case: (Hcvu e He) => {Hcvu} N Hcvu.
    exists N => n Hn.
    rewrite -Ropp_minus_distr' Rabs_Ropp.
    by apply Hcvu.
  move => [e He] /=.
  case: (Hcvu e He) => {Hcvu} N Hcvu.
  exists N => n y Hy Hn.
  rewrite (is_lim_seq_unique (fun n0 : nat => fn n0 y) _ (Hf y Hy)).
  rewrite -Ropp_minus_distr' Rabs_Ropp.
  by apply Hcvu.
  
  move => e He ; set eps := mkposreal e He.
  case: (Hcvu eps) => {Hcvu} N Hcvu.
  exists N => n y Hn Hy.
  rewrite -Ropp_minus_distr' Rabs_Ropp (H y Hy).
  by apply Hcvu.
Qed.

(** Various inclusions and equivalence between definitions *)

Lemma CVU_CVS_dom (fn : nat -> R -> R) (D : R -> Prop) :
  CVU_dom fn D -> CVS_dom fn D.
Proof.
  move => Hcvu x Hx.
  exists (Lim_seq (fun n => fn n x)) => eps.
  case: (Hcvu eps) => {Hcvu} N Hcvu.
  exists N => n Hn.
  by apply Hcvu.
Qed.
Lemma CVU_dom_cauchy (fn : nat -> R -> R) (D : R -> Prop) :
  CVU_dom fn D <-> CVU_cauchy fn D.
Proof.
  split => H eps.
(* CVU_dom -> CVU_cauchy *)
  case: (H (pos_div_2 eps)) => {H} N /= H.
  exists N => n m x Hx Hn Hm.
  rewrite (double_var eps).
  replace (fn n x - fn m x) 
    with ((fn n x - Lim_seq (fun n0 : nat => fn n0 x))
      - (fn m x - Lim_seq (fun n0 : nat => fn n0 x)))
    by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _) ; rewrite Rabs_Ropp.
  apply Rplus_lt_compat ; by apply H.
(* CVU_cauchy -> CVU_dom *)
  rewrite /Lim_seq.
  case: (H (pos_div_2 eps)) => {H} N /= H.
  exists N => n x Hx Hn.
  rewrite /LimSup_seq ; case: ex_LimSup_seq ; case => [ls | | ] /= Hls.
  rewrite /LimInf_seq ; case: ex_LimInf_seq ; case => [li | | ] /= Hli.
  replace (fn n x - (ls + li) / 2)
    with (((fn n x - ls) + (fn n x - li))/2)
    by field.
  rewrite Rabs_div ; [ | by apply Rgt_not_eq, Rlt_R0_R2].
  rewrite (Rabs_pos_eq 2) ; [ | by apply Rlt_le, Rlt_R0_R2].
  rewrite Rlt_div ; [ | by apply Rlt_R0_R2].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  replace (eps * 2) with (eps + eps) by ring.
  apply Rplus_lt_compat ; apply Rabs_lt_between'.
  case: (Hls (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
  case: (H0 N) => {H0} m [Hm H0].
  apply Rlt_trans with (fn m x - eps/2).
  replace (ls - eps) 
    with ((ls - eps / 2) - eps/2)
    by field.
  by apply Rplus_lt_compat_r.
  replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
  replace (fn m x - eps / 2) with ((fn m x - fn n x) + (fn n x - eps/2)) by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  apply Rlt_trans with (fn (n+N0)%nat x + eps/2).
  replace (fn n x) with (fn (n + N0)%nat x + (fn n x - fn (n+N0)%nat x)) by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  replace (ls + eps) with ((ls + eps/2) + eps/2) by field.
  apply Rplus_lt_compat_r.
  apply H1 ; by intuition.
  case: (Hli (pos_div_2 eps)) => {Hls Hli} /= H0 [N0 H1] ; split.
  apply Rlt_trans with (fn (n+N0)%nat x - eps/2).
  replace (li - eps) with ((li - eps/2) - eps/2) by field.
  apply Rplus_lt_compat_r.
  apply H1 ; by intuition.
  replace (fn n x) with (eps/2 + (fn n x - eps/2)) by ring.
  replace (fn (n + N0)%nat x - eps / 2) 
    with ((fn (n + N0)%nat x - fn n x) + (fn n x - eps/2))
    by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  case: (H0 N) => {H0} m [Hm H0].
  apply Rlt_trans with (fn m x + eps/2).
  replace (fn n x) with (fn m x + (fn n x - fn m x)) by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  replace (li + eps) 
    with ((li + eps / 2) + eps/2)
    by field.
  by apply Rplus_lt_compat_r.
  case: (Hli (fn n x + eps / 2)) => {Hls Hli} N0 H0.
  move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn (N + N0)%nat x)
    with (fn n x + (fn (N + N0)%nat x - fn n x))
    by ring.
  apply Rplus_lt_compat_l.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
  case: (Hli (fn n x - eps / 2) N) => {Hls Hli} m [Hm H0].
  contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn m x) with (eps/2 + (fn m x - eps/2)) by ring.
  replace (fn n x - eps / 2) 
    with ((fn n x - fn m x) + (fn m x - eps/2)) by ring.
  apply Rplus_lt_compat_r, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  case: (Hls (fn n x + eps / 2) N) => {Hls} m [Hm H0].
  contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn m x) with (fn n x + (fn m x - fn n x)) by ring.
  apply Rplus_lt_compat_l, Rle_lt_trans with (1 := Rle_abs _) ; by apply H.
  case: (Hls (fn n x - eps / 2)) => {Hls} N0 H0.
  move: (H0 _ (le_plus_r N N0)) => {H0} H0 ; contradict H0.
  apply Rle_not_lt, Rlt_le.
  replace (fn (N + N0)%nat x)
    with (eps/2 + (fn (N + N0)%nat x - eps/2))
    by ring.
  replace (fn n x - eps / 2) 
    with ((fn n x - fn (N+N0)%nat x) + (fn (N+N0)%nat x - eps/2)) by ring.
  apply Rplus_lt_compat_r.
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply H ; by intuition.
Qed.

Lemma CVU_dom_include (fn : nat -> R -> R) (D1 D2 : R -> Prop) :
  (forall y, D2 y -> D1 y) -> CVU_dom fn D1 -> CVU_dom fn D2.
Admitted. (** Admitted. *)

(** ** Limits, integrals and differentiability *)

Lemma CVU_limits (fn : nat -> R -> R) (D : R -> Prop) (x : R) :
  CVU_dom fn D
  -> (forall n, ex_lim (fn n) x)
  -> ex_lim_seq (fun n => Lim (fn n) x) 
    /\ ex_lim (fun y => Lim_seq (fun n => fn n y)) x
    /\ Lim_seq (fun n => Lim (fn n) x) = Lim (fun y => Lim_seq (fun n => fn n y)) x.
Admitted. (** Admitted *)
Lemma CVU_cont (fn : nat -> R -> R) (f : R -> R) (D : R -> Prop) :
  CVU_dom fn D -> (forall x, D x -> is_lim_seq (fun n => fn n x) (f x))
  -> (forall n, forall x, D x -> continuity_pt (fn n) x)
  -> forall x, D x -> continuity_pt f x.
Proof.
  move => Hfn Hl Hc x Hx.
  suff H : is_lim f x (f x).
    move => e He ; case: (H (mkposreal e He)) => /= {H} delta H.
    exists delta ; split.
    by apply delta.
    rewrite /R_dist /= => y [_ Hy].
    case: (Req_dec y x) => [-> | Hxy].
    by rewrite Rminus_eq0 Rabs_R0.
    by apply H.
    case: (CVU_limits _ _ x Hfn).
    
Admitted. (** Admitted *)
Lemma CVU_Nint (fn Fn : nat -> R -> R) (F : R -> R) (a b : R) (Hab : a < b) :
  CVU_dom fn (fun x => a <= x <= b)
  -> (forall n, forall x, a <= x <= b -> continuity_pt (fn n) x)
  -> (forall n x, a <= x <= b -> is_derive (Fn n) x (fn n x)) -> (forall n, Fn n a = 0)
  -> (forall x, a <= x <= b -> is_derive F x (Lim_seq (fun n => fn n x))) -> (F a = 0)
  -> CVU_dom Fn (fun x => a <= x <= b) 
    /\ (forall x, a <= x <= b -> Lim_seq (fun n => Fn n x) = F x).
Admitted. (** Admitted *)
Lemma CVU_Rint (fn : nat -> R -> R) (a b : R) (Hab : a < b) :
  CVU_dom fn (fun x => a <= x <= b)
  -> (forall n, forall x, a <= x <= b -> continuity_pt (fn n) x)
  -> CVU_dom (fun n x => RInt (fn n) a x) (fun x => a <= x <= b) 
    /\ (forall x, a <= x <= b -> Lim_seq (fun n => RInt (fn n) a x) = RInt (fun y => Lim_seq (fun n => fn n y)) a x).
Admitted. (** Admitted *)
Lemma CVU_Derive (fn : nat -> R -> R) (a b : R) (Hab : a < b) :
  (forall n x, a <= x <= b -> ex_derive (fn n) x)
  -> (forall n x, a <= x <= b -> continuity_pt (Derive (fn n)) x)
  -> (exists x0, a <= x0 <= b /\ ex_lim_seq (fun n => fn n x0))
  -> CVU_dom (fun n x => Derive (fn n) x) (fun x => a <= x <= b)
  -> (CVU_dom fn (fun x => a <= x <= b))
    /\ (forall x, a <= x <= b -> ex_derive (fun y => Lim_seq (fun n => fn n y)) x)
    /\ (forall x, a <= x <= b -> continuity_pt (Derive (fun y => Lim_seq (fun n => fn n y))) x)
    /\ (forall x, a <= x <= b -> Derive (fun y => Lim_seq (fun n => fn n y)) x = Lim_seq (fun n => Derive (fn n) x)).
Proof.
  move => HexDf HcDf [x0 [Hx0 Hexf]] HcvuDf.
  have H : CVU_cauchy fn (fun x => a <= x <= b).
    move => eps /=.
    apply ex_lim_seq_cauchy_corr in Hexf.
    case: (Hexf (pos_div_2 eps)) => /= {Hexf} Nf Hexf.
    have He : 0 < eps / (2 * (b-a)) ; [ | set e := mkposreal _ He].
      apply Rdiv_lt_0_compat.
      by apply eps.
      apply Rmult_lt_0_compat.
      by apply Rlt_R0_R2.
      by rewrite -Rlt_Rminus.
    apply CVU_dom_cauchy in HcvuDf.
    case: (HcvuDf e) => {HcvuDf} Ndf HcvuDf.
    exists (Nf + Ndf)%nat => n m x Hx Hn Hm.
    replace (fn n x - fn m x) 
      with ((fn n x0 - fn m x0) + ((fn n x - fn m x) - (fn n x0 - fn m x0)))
      by ring.
    rewrite (double_var eps).
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
    apply Hexf ; apply le_trans with (Nf + Ndf)%nat ; by intuition.
    case: (MVT (fun y => fn n y - fn m y) x0 x).
    move => y Hy ; apply ex_derive_minus ; apply HexDf ; split ; apply Rlt_le.
    apply Rle_lt_trans with (2 := proj1 Hy) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rlt_le_trans with (1 := proj2 Hy) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    apply Rle_lt_trans with (2 := proj1 Hy) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rlt_le_trans with (1 := proj2 Hy) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    move => y Hy ; apply derivable_continuous_pt ;
    exists (Derive (fun y => fn n y - fn m y) y) ;
    apply Derive_correct, ex_derive_minus ; apply HexDf ; split.
    apply Rle_trans with (2 := proj1 Hy) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rle_trans with (1 := proj2 Hy) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    apply Rle_trans with (2 := proj1 Hy) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rle_trans with (1 := proj2 Hy) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    move => cn [Hcn ->].
    rewrite Rabs_mult.
    case: (Req_dec x x0) => Hxx0.
    rewrite Hxx0 Rminus_eq0 Rabs_R0 Rmult_0_r ; by apply is_pos_div_2.
    apply Rlt_le_trans with (e * Rabs (x - x0)).
    apply Rmult_lt_compat_r.
    apply Rabs_pos_lt.
    by apply Rminus_eq_contra.
    rewrite Derive_minus.
    apply HcvuDf.
    split.
    apply Rle_trans with (2 := proj1 Hcn) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rle_trans with (1 := proj2 Hcn) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    apply le_trans with (Nf + Ndf)%nat ; by intuition.
    apply le_trans with (Nf + Ndf)%nat ; by intuition.
    apply HexDf ; split.
    apply Rle_trans with (2 := proj1 Hcn) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rle_trans with (1 := proj2 Hcn) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    apply HexDf ; split.
    apply Rle_trans with (2 := proj1 Hcn) ;
    apply Rmin_case ; [by apply Hx0 | by apply Hx].
    apply Rle_trans with (1 := proj2 Hcn) ;
    apply Rmax_case ; [by apply Hx0 | by apply Hx].
    rewrite /e /=.
    rewrite Rdiv_le_1 ; field_simplify ; rewrite -?Rdiv_1.
    rewrite -Rdiv_le_1.
    rewrite /Rabs ; case: Rcase_abs => H.
    rewrite Ropp_minus_distr' ; apply Rplus_le_compat.
    by apply Hx0.
    by apply Ropp_le_contravar, Hx.
    apply Rplus_le_compat.
    by apply Hx.
    by apply Ropp_le_contravar, Hx0.
    by rewrite -Rlt_Rminus.
    split ; apply Rgt_not_eq, Rlt_gt.
    by rewrite -Rlt_Rminus.
    by apply eps.
    by apply is_pos_div_2.

  split.
  by apply CVU_dom_cauchy.
  set f := (fun y : R => Lim_seq (fun n : nat => fn n y)).
  set rn := fun x1 n x => match (Req_EM_T x1 x) with
    | left _ => (Derive (fn n) x1)
    | right _ => (fn n x - fn n x1)/(x - x1)
  end.
  set r := fun x1 x => match (Req_EM_T x1 x) with
    | left _ => Lim_seq (fun n => Derive (fn n) x1)
    | right _ => (f x - f x1)/(x - x1)
  end.
  
  have Crn : forall x1 n, a <= x1 <= b ->
    continuity_pt (rn x1 n) x1.
    move => x1 n Hx1 e He.
    move: (HexDf n x1 Hx1) => {HexDf} Hdf.
    apply Derive_correct in Hdf.
    case: (Hdf e He) ; case => {Hdf} /= [d Hd] Hdf.
    exists d ; rewrite /D_x /R_dist /no_cond /rn /= ; split.
    exact: Hd.
    move => y [[_ Hy] Hy0].
    case: Req_EM_T => // H1 ;
    case: Req_EM_T => // H0.
    set h := (y - x1).
    replace y with (x1 + h) by (rewrite /h ; ring).
    apply Hdf.
    by apply Rminus_eq_contra, sym_not_eq.
    exact: Hy0.
  have Hcs : forall x1 x, a <= x1 <= b -> a <= x <= b 
    -> is_lim_seq (fun n => rn x1 n x) (r x1 x).
    move => x1 x Hx1 Hx.
    rewrite /rn /r.
    case: Req_EM_T => Hxx1.
    apply Lim_seq_correct.
    apply (CVU_CVS_dom (fun n x1 => Derive (fn n) x1) (fun x => a <= x <= b)).
    exact: HcvuDf.
    exact: Hx1.
    apply is_lim_seq_div.
    by apply Rminus_eq_contra, sym_not_eq.
    apply is_lim_seq_minus.
    apply Lim_seq_correct.
    apply (CVU_CVS_dom fn (fun x => a <= x <= b)).
    by apply CVU_dom_cauchy.
    exact: Hx.
    apply Lim_seq_correct.
    apply (CVU_CVS_dom fn (fun x => a <= x <= b)).
    by apply CVU_dom_cauchy.
    exact: Hx1.
    apply is_lim_seq_const.
  
  suff Cr : forall x1, a <= x1 <= b -> continuity_pt (r x1) x1.

have Hrw : forall x : R,
  a <= x <= b -> Derive f x = Lim_seq (fun n : nat => Derive (fn n) x).
  move => x1 Hx1.
  apply is_derive_unique => e He.
  case: (Cr x1 Hx1 e He) => {Cr} d [Hd Cr].
  exists (mkposreal d Hd) => /= h Hh Hhd.
  set y := (x1 + h).
  replace h with (y - x1) by (rewrite /y ; ring).
  have Hy : x1 <> y.
    rewrite /y ;
      apply Rminus_not_eq_right ; by (ring_simplify (x1+h-x1)).
  have Hyd : Rabs (y - x1) < d.
      rewrite /y ; by (ring_simplify (x1+h-x1)).
  move: (Cr y (conj (conj I Hy) Hyd)).
  rewrite /dist /= /R_dist /r.
  case: Req_EM_T => // _.
  by case: Req_EM_T (refl_equal x1) => //.

    split.
    move => x1 Hx1.
    exists (r x1 x1) => e He.
    case: (Cr x1 Hx1 e He) => {Cr} d [Hd Cr].
    exists (mkposreal d Hd) => /= h Hh Hhd.
    set y := (x1 + h).
    replace h with (y - x1) by (rewrite /y ; ring).
    have Hy : x1 <> y.
      rewrite /y ;
      apply Rminus_not_eq_right ; by (ring_simplify (x1+h-x1)).
    have Hyd : Rabs (y - x1) < d.
      rewrite /y ; by (ring_simplify (x1+h-x1)).
    move: (Cr y (conj (conj I Hy) Hyd)).
    rewrite /dist /= /R_dist /r.
    by case: Req_EM_T.
  split.

  apply CVU_cont with (fun n x => Derive (fn n) x).
  exact: HcvuDf.
  move => x1 Hx1.
  rewrite (Hrw x1 Hx1).
  apply Lim_seq_correct.
  apply (CVU_CVS_dom (fun n x => Derive (fn n) x) (fun x => a <= x <= b) HcvuDf x1 Hx1).
  by apply HcDf.
  
  exact: Hrw.
  
  move => x1 Hx1.
  apply (CVU_cont (fun n x => rn x1 n x) _ (fun x => a <= x <= b)).
  
Focus 2.
  move => x Hx ; by apply Hcs.
Focus 2.
  move => n x Hx.
  case: (Req_EM_T x1 x) => H0.
  rewrite H0 => {x1 Hx1 H0}.
  by apply Crn.
  move: x Hx H0.
  have H0 : forall x, a <= x <= b -> x1 <> x -> 
    continuity_pt (fun x2 : R => (fn n x2 - fn n x1) / (x2 - x1)) x.
    move => x Hx Hx2.
    apply continuity_pt_div.
    apply continuity_pt_minus.
    apply derivable_continuous_pt ; exists (Derive (fn n) x) ;
    by apply Derive_correct, HexDf.
    by apply continuity_pt_const.
    apply continuity_pt_minus.
    apply derivable_continuous_pt, derivable_pt_id.
    by apply continuity_pt_const.
    by apply Rminus_eq_contra, sym_not_eq.
  move => x Hx Hx2 e He.
  case: (H0 x Hx Hx2 e He) => {H0} d [Hd H0].
  exists (Rmin d (Rabs (x-x1))) ; split.
  apply Rmin_case.
  by apply Hd.
  apply Rabs_pos_lt ; by apply Rminus_eq_contra, sym_not_eq.
  move => y [[_ Hy] Hyd].
  rewrite /rn.
  case: Req_EM_T => // H1.
  rewrite H1 in Hyd ; contradict Hyd.
  apply Rle_not_lt ; rewrite /= /R_dist.
  rewrite -Ropp_minus_distr' Rabs_Ropp.
  apply Rmin_r.
  case: Req_EM_T => // _.
  apply H0 ; split => //.
  apply Rlt_le_trans with (1 := Hyd).
  apply Rmin_l.
Focus 2.
  by apply Hx1.
  
  apply CVU_dom_cauchy in HcvuDf.
  apply CVU_dom_cauchy => eps.
  case: (HcvuDf eps) => {HcvuDf} /= N Hcvu.
  exists N => n m x Hx Hn Hm.
  rewrite /rn.
  case: Req_EM_T => H0.
  rewrite H0.
  by apply Hcvu.
  replace ((fn n x - fn n x1) / (x - x1) - (fn m x - fn m x1) / (x - x1))
    with ( ((fn n x - fn m x) - (fn n x1 - fn m x1))/(x - x1))
    by (field ; by apply Rminus_eq_contra, sym_not_eq).
  case: (MVT (fun x => fn n x - fn m x) x1 x).
  move => y Hy.
  apply ex_derive_minus ; apply HexDf.
  split ; apply Rlt_le.
  apply Rle_lt_trans with (2 := proj1 Hy) ; apply Rmin_case ; by intuition.
  apply Rlt_le_trans with (1 := proj2 Hy) ; apply Rmax_case ; by intuition.
  split ; apply Rlt_le.
  apply Rle_lt_trans with (2 := proj1 Hy) ; apply Rmin_case ; by intuition.
  apply Rlt_le_trans with (1 := proj2 Hy) ; apply Rmax_case ; by intuition.
  move => y Hy.
  apply continuity_pt_minus ; apply derivable_continuous_pt.
  exists (Derive (fn n) y) ; apply Derive_correct, HexDf.
  split.
  apply Rle_trans with (2 := proj1 Hy) ; apply Rmin_case ; by intuition.
  apply Rle_trans with (1 := proj2 Hy) ; apply Rmax_case ; by intuition.
  exists (Derive (fn m) y) ; apply Derive_correct, HexDf.
  split.
  apply Rle_trans with (2 := proj1 Hy) ; apply Rmin_case ; by intuition.
  apply Rle_trans with (1 := proj2 Hy) ; apply Rmax_case ; by intuition.
  move => c [Hc ->].
  field_simplify (Derive (fun x2 : R => fn n x2 - fn m x2) c * (x - x1) / (x - x1)).
  rewrite -Rdiv_1.
  rewrite Derive_minus.
  apply Hcvu => //.
  split.
  apply Rle_trans with (2 := proj1 Hc) ; apply Rmin_case ; by intuition.
  apply Rle_trans with (1 := proj2 Hc) ; apply Rmax_case ; by intuition.
  apply HexDf.
  split.
  apply Rle_trans with (2 := proj1 Hc) ; apply Rmin_case ; by intuition.
  apply Rle_trans with (1 := proj2 Hc) ; apply Rmax_case ; by intuition.
  apply HexDf.
  split.
  apply Rle_trans with (2 := proj1 Hc) ; apply Rmin_case ; by intuition.
  apply Rle_trans with (1 := proj2 Hc) ; apply Rmax_case ; by intuition.
  by apply Rminus_eq_contra, sym_not_eq.
Qed.

(** * Series *)
(** todo: move to Series.v *)
(** ** Definitions *)

Definition is_series (a : nat -> R) (l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k)) l.
Definition ex_series (a : nat -> R) :=
  ex_lim_seq (sum_f_R0 (fun k => a k)).
Definition Series (a : nat -> R) : R :=
  Lim_seq (sum_f_R0 (fun k => a k)).

Lemma ex_series_dec (a : nat -> R) :
  {ex_series a} + {~ex_series a}.
Proof.
  by apply ex_lim_seq_dec.
Qed.

Lemma is_series_equiv (a : nat -> R) (l : R) :
  is_series a l <-> infinite_sum a l.
Proof.
  split => H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 a n) with (sum_f_R0 (fun k : nat => a k) n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a k) n) with (sum_f_R0 a n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.
Lemma ex_series_equiv_0 (a : nat -> R) :
  ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
  move => H ;
  exists (Series a) ;
  apply Lim_seq_correct in H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 a n) with (sum_f_R0 (fun k : nat => a k) n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.
Lemma ex_series_equiv_1 (a : nat -> R) :
  { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l } -> ex_series a.
Proof.
  case => l H.
  exists l.
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a k) n) with (sum_f_R0 a n)
    by (elim: (n) => //= k -> //).
  by apply (H n Hn).
Qed.

(** ** Operations *)

(** Extentionality *)

Lemma is_series_ext (a b : nat -> R) (l : R) :
  (forall n, a n = b n) -> (is_series a l) 
    -> is_series b l.
Proof.
  move => Heq Ha.
  apply is_lim_seq_ext with (2 := Ha).
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.
Lemma ex_series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> ex_series a
    -> ex_series b.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_series_ext with a.
Qed.
Lemma Series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> Series a = Series b.
Proof.
  move => Heq.
  apply Lim_seq_ext.
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.

(** Multiplication by a scalar *)

Lemma is_series_scal (c : R) (a : nat -> R) (l : R) :
  is_series a l -> is_series (fun n => c * a n) (c * l).
Proof.
  move => Ha.
  apply is_lim_seq_ext with (fun n => c * (sum_f_R0 (fun k => a k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  by apply is_lim_seq_scal.
Qed.
Lemma ex_series_scal (c : R) (a : nat -> R) :
  ex_series a -> ex_series (fun n => c * a n).
Proof.
  move => [l Ha].
  exists (c * l).
  by apply is_series_scal.
Qed.
Lemma Series_scal (c : R) (a : nat -> R) :
  Series (fun n => c * a n) = c * Series a.
Proof.
  rewrite -Lim_seq_scal.
  apply Lim_seq_ext.
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite IH ; ring.
Qed.

(** Addition of two power series *)

Lemma is_series_plus (a b : nat -> R) (la lb : R) :
  is_series a la -> is_series b lb
    -> is_series (fun n => a n + b n) (la + lb).
Proof.
  move => Ha Hb.
  apply is_lim_seq_ext 
    with (fun n => (sum_f_R0 (fun k => a k) n) + (sum_f_R0 (fun k => b k) n)).
  elim => [ | n IH].
  simpl ; ring.
  simpl ; rewrite -IH ; ring.
  by apply is_lim_seq_plus with la lb.
Qed.
Lemma ex_series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> ex_series (fun n => a n + b n).
Proof.
  move => [la Ha] [lb Hb].
  exists (la + lb).
  by apply is_series_plus.
Qed.
Lemma Series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n + b n) = Series a + Series b.
Proof.
  intros Ha Hb.
  apply is_lim_seq_unique, is_series_plus ;
  by apply Lim_seq_correct.
Qed.

(** Comming soon:
  - addition
  - multiplication *)

(** Index offset *)

Lemma is_series_incr_1 (a : nat -> R) (l : R) :
  is_series a (l + a O)
    -> is_series (fun k => a (S k)%nat) l.
Proof.
  move => Ha eps.
  case: (Ha eps) => {Ha} N Ha.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => a (S k)) n - l)
    with (a O + sum_f_R0 (fun k : nat => a (S k)) (pred (S n)) - (l + a O))
    by (simpl ; ring).
  rewrite -(decomp_sum (fun k => a k)).
  apply (Ha (S n)).
  by intuition.
  by apply lt_O_Sn.
Qed.
Lemma is_series_incr_n (a : nat -> R) (n : nat) (l : R) :
  (0 < n)%nat -> is_series a (l + sum_f_R0 a (pred n))
    -> is_series (fun k => a (n + k)%nat) l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n l Ha => [ | n IH] l Ha.
  by apply is_series_incr_1.
  apply is_series_ext with (fun k : nat => a (S (n + S k))).
    move => k ; apply f_equal ; ring.
  apply is_series_incr_1 with (a := fun k : nat => a (S (n + k))).
  rewrite plus_0_r.
  apply IH.
  by rewrite Rplus_assoc (Rplus_comm (a (S n))).
Qed.

Lemma is_series_decr_1 (a : nat -> R) (l : R) :
  is_series (fun k => a (S k)%nat) (l - a O) -> is_series a l.
Proof.
  move => Ha eps.
  case: (Ha eps) => {Ha} N Ha.
  exists (S N) ; elim => [ | n IH] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  rewrite decomp_sum /=.
  replace (a 0%nat + sum_f_R0 (fun i : nat => a (S i)) n - l) 
    with(sum_f_R0 (fun k : nat => a (S k)) n - (l - a 0%nat)) by ring.
  by apply Ha.
  by apply lt_0_Sn.
Qed.
Lemma is_series_decr_n (a : nat -> R) (n : nat) (l : R) :
  (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (l - sum_f_R0 a (pred n))
    -> is_series a l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n a l Ha => [ | n IH] a l Ha.
  by apply is_series_decr_1.
  apply is_series_decr_1.
  apply IH.
  replace (l - a 0%nat - sum_f_R0 (fun k : nat => a (S k)) n)
    with (l - sum_f_R0 a (S n)).
  by apply Ha.
  rewrite decomp_sum /=.
  ring.
  by apply lt_O_Sn.
Qed.

Lemma ex_series_decal_1 (a : nat -> R) :
  ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
  split ; move => [la Ha].
  exists (la - a O).
  apply is_series_incr_1.
  by ring_simplify (la - a 0%nat + a 0%nat).
  exists (la + a O).
  apply is_series_decr_1.
  by ring_simplify (la + a 0%nat - a 0%nat).
Qed.
Lemma ex_series_decal_n (a : nat -> R) (n : nat) :
  ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
  case: n => [ | n].
  split ; apply ex_series_ext ; by intuition.
  split ; move => [la Ha].
  exists (la - sum_f_R0 a (pred (S n))).
  apply is_series_incr_n.
  by apply lt_O_Sn.
  by ring_simplify (la - sum_f_R0 a (pred (S n)) + sum_f_R0 a (pred (S n))).
  exists (la + sum_f_R0 a (pred (S n))).
  apply is_series_decr_n with (S n).
  by apply lt_O_Sn.
  by ring_simplify (la + sum_f_R0 a (pred (S n)) - sum_f_R0 a (pred (S n))).
Qed.

Lemma Series_decal_1 (a : nat -> R) :
  ex_series a -> Series a = a O + Series (fun k => a (S k)).
Proof.
  move => Ha.
  apply is_lim_seq_unique.
  rewrite Rplus_comm.
  apply is_series_decr_1 ;
  ring_simplify (Series (fun k : nat => a (S k)) + a 0%nat - a 0%nat).
  by apply Lim_seq_correct, (ex_series_decal_1 a).
Qed.
Lemma Series_decal_n (a : nat -> R) (n : nat) :
  (0 < n)%nat -> ex_series a 
    -> Series a = sum_f_R0 a (pred n)  + Series (fun k => a (n + k)%nat).
Proof.
  move => Hn Ha.
  apply is_lim_seq_unique.
  rewrite Rplus_comm.
  apply is_series_decr_n with n.
  by [].
  ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) -
   sum_f_R0 a (pred n)).
  by apply Lim_seq_correct, (ex_series_decal_n a).
Qed.

Lemma Series_decal_1_aux (a : nat -> R) :
  a O = 0 -> Series a = Series (fun k => a (S k)).
Proof.
  move => Ha.
  rewrite /Series.
  rewrite -Lim_seq_incr.
  apply Lim_seq_ext => n.
  rewrite decomp_sum /=.
  rewrite Ha ; by apply Rplus_0_l.
  by apply lt_O_Sn.
Qed.
Lemma Series_decal_n_aux (a : nat -> R) (n : nat) :
   (forall k, (k < n)%nat -> a k = 0) 
     -> Series a = Series (fun k => a (n + k)%nat).
Proof.
  elim: n => [ | n IH] Ha.
  by apply Series_ext => k.
  rewrite IH.
  rewrite Series_decal_1_aux.
  apply Series_ext => k.
  apply f_equal ; ring.
  intuition.
  move => k Hk ; intuition.
Qed.

(** ** Convergence theorems *)

(** Cauchy Criterion : A redemontrer sans Rcomplete.R_complete *)

Lemma Cauchy_ex_series (a : nat -> R) :
  ex_series a <-> (Cauchy_crit_series a).
Proof.
  split => Hcv.
  by apply cv_cauchy_1, ex_series_equiv_0.
  apply ex_series_equiv_1.
  apply R_complete.
  by apply Hcv.
Qed.
(** %$\sum a_n$ is convergent $\Rightarrow \lim_{n\to + \infty} a_n = 0$%
#if a is summable, then its limit is 0# *)

Lemma ex_series_lim_0 (a : nat -> R) :
  ex_series a -> is_lim_seq a 0.
Proof.
  move => Hs eps.
  apply Cauchy_ex_series in Hs.
  case: (Hs eps (cond_pos eps)) => {Hs} N Hs.
  exists (S N) ; case => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  replace (a (S n) - 0)
    with (sum_f_R0 a (S n) - sum_f_R0 a n)
    by (simpl ; ring).
  apply Hs ; by intuition.
Qed.

(** #Absolute convergence imply convergence#
%$\sum | a_n |$ converge $\Rightarrow \sum a_n$ is convergent% *)

Lemma Abs_ex_series (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) -> ex_series a.
Proof.
  move => H.
  apply Cauchy_ex_series.
  apply cauchy_abs.
  by apply Cauchy_ex_series.
Qed.
(** Comparison *)

Lemma Comp_ex_series (a b : nat -> R) :
   (forall n : nat, 0 <= a n <= b n) ->
   ex_series b -> ex_series a.
Proof.
  move => H Hb.
  apply Cauchy_ex_series.
  apply Cauchy_ex_series in Hb.
  move => e He.
  case (Hb e He) => {Hb} N Hb.
  exists N => n m Hn Hm.
  wlog: n m Hn Hm /(n > m)%nat => [Hw | Hnm].
  case: (le_lt_dec n m) => Hnm.
  apply le_lt_eq_dec in Hnm ; case: Hnm => Hnm.
  rewrite /R_dist -Ropp_minus_distr' Rabs_Ropp ; by apply Hw.
  by rewrite Hnm /R_dist Rminus_eq0 Rabs_R0.
  by apply Hw.
  move: (Hb n m Hn Hm).
  rewrite /R_dist (tech2 a m n Hnm) (tech2 b m n Hnm) ; 
    ring_simplify (sum_f_R0 a m 
    + sum_f_R0 (fun i : nat => a (S m + i)%nat) (n - S m) 
    - sum_f_R0 a m) ; 
    ring_simplify (sum_f_R0 b m 
    + sum_f_R0 (fun i : nat => b (S m + i)%nat) (n - S m) 
    - sum_f_R0 b m).
  apply Rle_lt_trans.
  apply Rle_trans with (2 := Rle_abs _).
  rewrite Rabs_pos_eq.
  elim: (n - S m)%nat => /= [ | k IH].
  by apply H.
  apply Rplus_le_compat.
  exact: IH.
  by apply H.
  elim: (n - S m)%nat => /= [ | k IH].
  by apply H.
  apply Rplus_le_le_0_compat.
  exact: IH.
  by apply H.
Qed.

(** D'Alembert criterium *)

Lemma DAlembert_ex_series (a : nat -> R) (k : R) :
  k < 1 -> (forall n, a n <> 0) 
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) k
      -> ex_series (fun n => Rabs (a n)).
Proof.
  move => Hk Ha H.
  have : exists N, forall n, (N <= n)%nat -> Rabs (a (S n) / a n) <= (k+1)/2.
    case: (fun He => H (mkposreal ((1-k)/2) He)).
      move: (fun He => is_pos_div_2 (mkposreal (1-k) He)) => /= He ;
      apply: He.
      by apply -> Rlt_Rminus.
    move => {H} /= Hk1 N H.
    exists N => n Hn.
    move: (H n Hn) => {H} H.
    apply Rabs_lt_between' in H ; case: H => _ H ; 
    field_simplify in H ; rewrite -Rdiv_1 in H ; by apply Rlt_le.
  case => {H} N H.
  apply ex_series_decal_n with N.
  apply Comp_ex_series with (fun n => Rabs (a N) * ((k+1)/2)^n).
  move => n ; split.
  by apply Rabs_pos.
  rewrite Rmult_comm ; apply Rle_div.
  by apply Rabs_pos_lt.
  rewrite -Rabs_div.
  elim: n => [ | n IH].
  rewrite plus_0_r /Rdiv Rinv_r.
  rewrite Rabs_R1 ; by apply Rle_refl.
  by apply Ha.
  replace (Rabs (a (N + S n)%nat / a N)) 
    with (Rabs (a (S (N + n))/a (N+n)%nat) * Rabs (a (N + n)%nat / a N)).
  simpl ; apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  apply H, le_plus_l.
  by apply IH.
  rewrite -Rabs_mult ; apply f_equal.
  rewrite plus_n_Sm ; field ; split ; by apply Ha.
  by apply Ha.
  apply ex_series_scal.
  set k0 := ((k + 1) / 2).
  apply ex_lim_seq_ext with (fun N => / (1 - k0) * (1 - k0 ^ S N)).
  move => n ; rewrite tech3.
  by apply Rmult_comm.
  apply Rlt_not_eq.
  replace 1 with ((1+1)/2) by field ; rewrite /k0.
  apply Rmult_lt_compat_r ; by intuition.
  apply ex_lim_seq_scal.
  exists (1-0).
  apply is_lim_seq_minus.
  by apply is_lim_seq_const.
  simpl ; rewrite -(Rmult_0_r k0) ; apply is_lim_seq_scal.
  apply (is_lim_seq_geom k0).
  rewrite Rabs_pos_eq.
  replace 1 with ((1+1)/2) by field ; rewrite /k0.
  apply Rmult_lt_compat_r ; by intuition.
  apply Rle_trans with (2 := H N (le_refl _)) ; by apply Rabs_pos.
Qed.

Lemma DAlembert_not_ex_series (a : nat -> R) (l : R) :
  l > 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) l
      -> ~ is_lim_seq a 0.
Proof.
  move => Hl Ha Hda Ha0.
  set k := (l+1)/2.
  have Hk1 : 1 < k.
    apply Rminus_lt ; unfold k ; field_simplify ; rewrite -Rdiv_1.
    rewrite -(Rmult_0_l (/2)) ; apply Rmult_lt_compat_r ; try by intuition.
    rewrite Rplus_comm ; by apply Rlt_minus.
  have : exists N, forall n, (N <= n)%nat -> k <= Rabs (a (S n) / a n).
    case: (fun H => Hda (mkposreal ((l-1)/2) H)) => [ | /= {Hda} H N Hda].
    apply Rdiv_lt_0_compat.
    by apply -> Rlt_Rminus.
    by apply Rlt_R0_R2.
    exists N => n Hn.
    move: (Hda n Hn) => {Hda} Hda.
    apply Rabs_lt_between' in Hda.
    replace (k) with (l - (l - 1) / 2) by (unfold k ; field).
    by apply Rlt_le, Hda.
  case => N H.
  apply is_lim_seq_abs_0, (is_lim_seq_incr_n _ N) in Ha0.
  have : forall n, Rabs (a N) * k ^ n <= Rabs (a (n + N)%nat).
    elim => /= [ | n IH].
    rewrite Rmult_1_r ; by apply Rle_refl.
    replace (Rabs (a (S (n + N)))) 
      with (Rabs (a (S (n+N)) / a (n+N)%nat) * Rabs (a (n+N)%nat))
      by (rewrite -Rabs_mult ; apply f_equal ; by field).
    replace (Rabs (a N) * (k * k ^ n)) with (k * (Rabs (a N) * k ^ n)) by ring.
    apply Rmult_le_compat.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H, le_plus_r.
    by apply IH.
  move => {H} H.
  have : Finite 0 = p_infty.
    rewrite -(Rbar_lim_seq_geom_p k Hk1).
    apply sym_equal.
    apply Rbar_is_lim_correct, is_lim_seq_correct.
    apply is_lim_seq_ext with (fun n => / Rabs (a N) * (Rabs (a N) * k ^ n)).
    move => n ; field ; by apply Rabs_no_R0.
    rewrite -(Rmult_0_r (/Rabs (a N))).
    apply is_lim_seq_scal.
    apply is_lim_seq_le_le with (fun _ => 0) (fun n => Rabs (a (n + N)%nat)).
    move => n ; split.
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H.
    by apply is_lim_seq_const.
    by apply Ha0.
  by [].
Qed.

(** Comming soon : alternated series *)

(** ** Series of functions *)

Lemma CVN_CVU_r (fn : nat -> R -> R) (r : posreal) :
  CVN_r fn r -> forall x, (Rabs x < r) -> exists e : posreal, 
    CVU (fun n => SP fn n) (fun x => Series (fun n => fn n x)) x e.
Proof.
  case => An [l [H H0]] x Hx.
  have H1 : ex_series An.
    apply ex_series_equiv_1.
    exists l => e He.
    case: (H e He) => {H} N H.
    exists N => n Hn.
    replace (sum_f_R0 An n) with (sum_f_R0 (fun k : nat => Rabs (An k)) n).
    by apply H.
    elim: n {Hn} => /= [ | n IH].
    apply Rabs_pos_eq.
    apply Rle_trans with (Rabs (fn O 0)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
    rewrite IH Rabs_pos_eq.
    by [].
    apply Rle_trans with (Rabs (fn (S n) 0)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.

  have H2 : is_lim_seq (fun n => Series (fun k => An (n + k)%nat)) 0.
    apply is_lim_seq_incr.
    apply is_lim_seq_ext with (fun n => Series An - sum_f_R0 An n).
    move => n ; rewrite (Series_decal_n An (S n)) /=.
    ring.
    by apply lt_O_Sn.
    by apply H1.
    apply is_lim_seq_plus with (Series An) (-Series An).
    by apply is_lim_seq_const.
    apply is_lim_seq_opp.
    rewrite /Series ;
    apply (is_lim_seq_ext (sum_f_R0 (fun k => An k))).
    elim => /= [ | n IH].
    by [].
    by rewrite IH.
    apply Lim_seq_correct, H1.
    ring.

  apply Rlt_Rminus in Hx.
  set r0 := mkposreal _ Hx.
  exists r0 => e He ; set eps := mkposreal e He.
  case: (H2 eps) => {H2} N H2.
  exists N => n y Hn Hy.
  apply Rle_lt_trans with (2 := H2 (S n) (le_trans _ _ _ (le_n_Sn _) (le_n_S _ _ Hn))).
  rewrite Rminus_0_r /SP.
  rewrite (Series_decal_n (fun k : nat => fn k y) (S n)) /=.
  ring_simplify (sum_f_R0 (fun k : nat => fn k y) n +
    Series (fun k : nat => fn (S (n + k)) y) -
    sum_f_R0 (fun k : nat => fn k y) n).

  apply Rle_trans with (2 := Rle_abs _).
  apply Rle_trans with (Series (fun k : nat => Rabs (fn (S (n + k)) y))).
  apply Rabs_le_between ; rewrite -Lim_seq_opp /Series ; split.

  apply is_lim_seq_le with 
    (fun n0 : nat => - sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y)) n0)
    (sum_f_R0 (fun k : nat => fn (S (n + k)) y)).
  elim => /= [ | k IH].
  apply Ropp_le_cancel ; rewrite Ropp_involutive.
  by apply Rabs_maj2.
  rewrite Ropp_plus_distr ; apply Rplus_le_compat.
  by apply IH.
  apply Ropp_le_cancel ; rewrite Ropp_involutive.
  by apply Rabs_maj2.
  apply Lim_seq_correct, ex_lim_seq_opp.
  apply Comp_ex_series with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  apply Lim_seq_correct.
  apply Abs_ex_series.
  apply Comp_ex_series with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  
  apply is_lim_seq_le with 
    (sum_f_R0 (fun k : nat => fn (S (n + k)) y))
    (sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y))).
  elim => /= [ | k IH].
  by apply Rle_abs.
  apply Rplus_le_compat.
  by apply IH.
  apply Rle_abs.
  apply Lim_seq_correct.
  apply Abs_ex_series.
  apply Comp_ex_series with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  apply (is_lim_seq_ext (sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y)))).
  by [].
  apply Lim_seq_correct.
  apply (Comp_ex_series) with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  
  apply is_lim_seq_le with 
    (sum_f_R0 (fun k : nat => Rabs (fn (S (n + k)) y)))
    (sum_f_R0 (fun k : nat => An (S (n + k)))).
  elim => /= [ | k IH].
  apply H0.
  rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  apply Rplus_le_compat.
  by apply IH.
  apply H0.
  rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  
  apply Lim_seq_correct.
  apply (Comp_ex_series) with (fun k => An (S (n + k))).
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply (ex_series_decal_n An (S n)).
  
  apply Lim_seq_correct.
  by apply (ex_series_decal_n An (S n)).
  by apply lt_O_Sn.
  
  apply Abs_ex_series.
  apply (Comp_ex_series) with An.
  move => k ; split.
  by apply Rabs_pos.
  apply H0 ; rewrite /Boule ?Rminus_0_r /r0 /= in Hy |- *.
  apply Rabs_lt_between.
  apply Rabs_lt_between' in Hy.
  split.
  apply Rle_lt_trans with (2 := proj1 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm -{2}(Ropp_involutive x).
  apply -> Rminus_le_0.
  apply Rabs_maj2.
  apply Rlt_le_trans with (1 := proj2 Hy).
  apply Rminus_le_0 ; ring_simplify.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rle_abs.
  by apply H1.
Qed.

(** * Power series *)
(** A new definition using our limits *)

Definition is_pseries (a : nat -> R) (x l : R) :=
  is_lim_seq (sum_f_R0 (fun k => a k * x ^ k)) l.
Definition ex_pseries (a : nat -> R) (x : R) :=
  ex_lim_seq (sum_f_R0 (fun k => a k * x ^ k)).
Definition PSeries (a : nat -> R) (x : R) : R :=
  Lim_seq (sum_f_R0 (fun k => a k * x ^ k)).

Lemma ex_pseries_dec (a : nat -> R) (x : R) :
  {ex_pseries a x} + {~ ex_pseries a x}.
Proof.
  by apply ex_lim_seq_dec.
Qed.

(** This new formalisation is equivalent with standard library *)

Lemma is_pseries_equiv (a : nat -> R) (x l : R) :
  is_pseries a x l <-> Pser a x l.
Proof.
  split => H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => {H} N H.
  exists N => n Hn.
  by apply H.
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  by apply H.
Qed.

(** ** Domain of definition *)
(** A power series is always defined at 0 *)
Lemma is_pseries_0 (a : nat -> R) :
  is_pseries a 0 (a O).
Proof.
  apply is_lim_seq_ext with (fun _ => a O).
  elim => [ | n IH] /=.
  ring.
  rewrite -IH ; ring.
  by apply is_lim_seq_const.
Qed.
Lemma ex_pseries_0 (a : nat -> R) :
  ex_pseries a 0.
Proof.
  exists (a O) ; by apply is_pseries_0.
Qed.
Lemma PSeries_0 (a : nat -> R) :
  PSeries a 0 = a O.
Proof.
  by apply is_lim_seq_unique, is_pseries_0.
Qed.

(** Extentionality *)

Lemma is_pseries_ext (a b : nat -> R) (x l : R) :
  (forall n, a n = b n) -> (is_pseries a x l) 
    -> is_pseries b x l.
Proof.
  move => Heq Ha.
  apply is_lim_seq_ext with (2 := Ha).
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.
Lemma ex_pseries_ext (a b : nat -> R) (x : R) :
  (forall n, a n = b n) -> ex_pseries a x
    -> ex_pseries b x.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_pseries_ext with a.
Qed.
Lemma PSeries_ext (a b : nat -> R) (x : R) :
  (forall n, a n = b n) -> PSeries a x = PSeries b x.
Proof.
  move => Heq.
  apply Lim_seq_ext.
  elim => /= [ | n IH] .
  by rewrite Heq.
  by rewrite IH Heq.
Qed.


(** Convergence circle *)

Definition CV_circle_set (a : nat -> R) (r : R) :=
  ex_series (fun n => Rabs (a n * r^n)).

Lemma CV_circle_pty1 (a : nat -> R) (r1 r2 : R) :
  Rabs r1 <= Rabs r2 -> CV_circle_set a r2 -> CV_circle_set a r1.
Proof.
  move => H.
  apply Comp_ex_series => n ; split.
  rewrite Rabs_mult ; apply Rmult_le_pos ; by apply Rabs_pos.
  rewrite ?Rabs_mult ; apply Rmult_le_compat_l.
  by apply Rabs_pos.
  rewrite -?RPow_abs ; apply pow_incr ; split.
  by apply Rabs_pos.
  by apply H.
Qed.
Lemma CV_circle_pty2 (a : nat -> R) (x : R) :
  CV_circle_set a x -> ex_pseries a x.
Proof.
  by apply Abs_ex_series.
Qed.

Lemma CV_circle_0 (a : nat -> R) :
  CV_circle_set a 0.
Proof.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
  elim => /= [ | n IH].
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
  by apply ex_lim_seq_const.  
Qed.

Lemma CV_circle_ne (a : nat -> R) :
  exists x, (CV_circle_set a) x.
Proof.
  exists 0.
  by apply CV_circle_0.
Qed.
Definition CV_circle (a : nat -> R) : Rbar :=
  Lub_Rbar_ne (CV_circle_set a) (CV_circle_ne a).

Lemma CV_circle_le_0 (a : nat -> R) :
  Rbar_le (Finite 0) (CV_circle a).
Proof.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => /= l Hl.
  apply Hl, CV_circle_0.
Qed.

Lemma CV_circle_bounded (a : nat -> R) :
  is_lub_Rbar (fun r => exists M, forall n, Rabs (a n * r ^ n) <= M) (CV_circle a).
Proof.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => cv /= [ub lub].
  split.
  
  move => r /= [M Hr].
  
  have : forall y, Rabs y < Rabs r -> (CV_circle_set a) y.
    move => y Hy ; rewrite /CV_circle_set /=.
  set l := (Rabs (y / r)).
  have : ex_series (fun n => M * l ^ n).
  apply ex_series_scal.
  apply ex_lim_seq_ext with (fun n => (1 - l ^ S n) / (1 - l)).
  move => n ; rewrite tech3.
  by [].
  move => H.
  have H0 : Rabs y = Rabs r.
  rewrite -(Rmult_1_l (Rabs r)) ; rewrite -H.
  rewrite /l Rabs_div ; try field.
  apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hy), Rabs_pos.
  have Hr0 : Rabs r <> 0.
    apply Rgt_not_eq ; apply Rle_lt_trans with (2 := Hy), Rabs_pos.
  contradict Hr0 ; rewrite Hr0 Rabs_R0 //.
  rewrite H0 in Hy ; by apply Rlt_irrefl in Hy.
  case: (Req_dec l 0) => Hl0.
  rewrite Hl0 ; exists 1.
  apply is_lim_seq_ext with (2 := is_lim_seq_const 1).
  move => n ; rewrite /Rdiv ?Rmult_0_l pow_i.
  field.
  by apply lt_0_Sn.
  exists (/ (1 - l)) => eps.
  have Hl1 : Rabs l < 1.
    rewrite /l Rabs_Rabsolu Rabs_div.
    apply (Rdiv_lt_1 (Rabs _)).
    apply Rle_lt_trans with (2 := Hy), Rabs_pos.
    by apply Hy.
    have Hr0 : Rabs r <> 0.
      apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
    contradict Hr0 ; by rewrite Hr0 Rabs_R0.
  have Hl2 : 1 - l <> 0.
    apply Rminus_eq_contra.
    contradict Hl1 ; rewrite -Hl1.
    apply Rle_not_lt ; rewrite Rabs_R1 ; by apply Rle_refl.

  case: (pow_lt_1_zero l _ (eps * Rabs (1-l)/ Rabs l)) => //.
  repeat apply Rmult_lt_0_compat.
  apply eps.
  by apply Rabs_pos_lt.
  by apply Rinv_0_lt_compat, Rabs_pos_lt.

  move => N H.
  exists N => n Hn /=.
    
  field_simplify ((1 - l * l ^ n) / (1 - l) - / (1 - l)) ;
  try by intuition.
  rewrite  ?Rabs_mult Rabs_Ropp Rabs_Rinv ; try by intuition.
  replace (pos eps) with (Rabs l * (eps * Rabs (1 - l) / Rabs l) * / Rabs (- l + 1)).
  apply Rmult_lt_compat_r => //.
    apply Rinv_0_lt_compat, Rabs_pos_lt ; by rewrite Rplus_comm.
  apply Rmult_lt_compat_l.
  by apply Rabs_pos_lt.
  by apply H.
  rewrite Rplus_comm /Rminus.
  field ; try by (split ; apply Rabs_no_R0).
  by rewrite Rplus_comm.

  apply Comp_ex_series => n.
  split.
  by apply Rabs_pos.
  replace (Rabs (a n * y ^ n)) with (Rabs (a n * r ^ n) * l^n).
  apply Rmult_le_compat_r.
  apply pow_le ; by apply Rabs_pos.
  by apply Hr.
  rewrite ?Rabs_mult Rmult_assoc ; apply Rmult_eq_compat_l.

  rewrite /l RPow_abs -Rabs_mult.
  apply f_equal.
  elim: n  => /= [ | n IH].
  ring.
  rewrite -IH ; field.
  have Hr0 : Rabs r <> 0.
    apply Rgt_not_eq, Rle_lt_trans with (2 := Hy), Rabs_pos.
  contradict Hr0 ; by rewrite Hr0 Rabs_R0.
  
  move => H.
  
  have : forall y, Rabs y < Rabs r -> Rbar_le (Finite (y)) cv.
  move => y Hy.
  apply ub.
  by apply (H y Hy).

  have Hc0 : Rbar_le (Finite 0) cv.
  apply ub, CV_circle_0.
  case: (cv) Hc0 => [c | | ] Hc0 Hcv.
  apply Rbar_finite_le.

  case: (Rle_lt_dec r 0) => Hr0.
  by apply Rle_trans with (1 := Hr0), Rbar_finite_le.

  have H0 : forall e, 0 < e <= r -> r - e <= c.
    intros.
    apply Rbar_finite_le, Hcv.
    apply Rlt_le_trans with (2 := Rle_abs _).
    rewrite Rabs_pos_eq.
    rewrite -(Rplus_0_r (r - e)).
    pattern r at 2 ; replace r with ((r-e)+e) by ring.
    apply Rplus_lt_compat_l, H0.
    rewrite -Rminus_le_0 ; by apply H0.

  apply Rnot_lt_le => H1.
  apply Rbar_finite_le in Hc0.
  have H2: (c < ((c+r)/2) < r).
    pattern r at 3 ; replace r with ((r+r)/2) by field.
    pattern c at 1 ; replace c with ((c+c)/2) by field.
    split ; apply Rmult_lt_compat_r ; by intuition.
  have H3 : 0 < ((r-c)/2) <= r.
  split.
  apply Rdiv_lt_0_compat.
  by apply -> Rlt_Rminus.
  by apply Rlt_R0_R2.
  pattern r at 2 ; replace r with ((r+r)/2) by field.
  apply Rmult_le_compat_r ; intuition.
  apply Rplus_le_compat_l.
  apply Rle_trans with 0.
  rewrite -(Rminus_eq0 c).
  rewrite -(Rplus_0_l (-c)).
  by apply Rplus_le_compat_r.
  by apply Rlt_le.
  move: (H0 _ H3).
  apply Rlt_not_le.
  rewrite {1}(Rdiv_1 r).
  rewrite Rdiv_minus ; try by [intuition | apply Rgt_not_eq ; intuition].
  ring_simplify (r * 2 - (r - c) * 1) ; rewrite Rmult_1_l.
  rewrite Rplus_comm ; by apply H2.

  by left.
  by case: Hc0.

(* lub *)
  move => b Hb.
  apply lub => x Hx.
  apply Hb.
  apply ex_series_lim_0 in Hx.
  case: (Hx (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.
  
  set M := fix f N := match N with 
    | O => Rabs (a O * x ^ O) 
    | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
  exists (Rmax (M N) 1) => n.
  case: (le_lt_dec N n) => Hn.
  apply Rle_trans with (2 := Rmax_r _ _).
  move: (Hx n Hn).
  rewrite Rminus_0_r Rabs_Rabsolu.
  by apply Rlt_le.
  apply Rle_trans with (2 := Rmax_l _ _).
  elim: N n Hn {Hx} => [ | N IH] /= n Hn.
  by apply lt_n_O in Hn.
  apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
  apply Rle_trans with (2 := Rmax_l _ _).
  by apply IH.
  rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
Qed.

(** The power series is absolutly convergent inside the convergence circle *)
Lemma CV_circle_carac (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a)
    -> ex_series (fun n => Rabs (a n * x ^ n)).
Proof.
  move => Ha.
  have H : ~ ~ ex_series (fun n => Rabs (a n * x ^ n)).
    contradict Ha.
    apply Rbar_le_not_lt.
    rewrite /CV_circle /Lub_Rbar_ne ;
    case: ex_lub_Rbar_ne => l /= [ub lub].
    apply: lub => r Hr.
    apply Rbar_finite_le.
    apply Rnot_lt_le ; contradict Ha.
    move: Hr.
    apply CV_circle_pty1.
    by apply Rlt_le, Rlt_le_trans with (2 := Rle_abs _).
  by case: (ex_series_dec (fun n => Rabs (a n * x ^ n))).
Qed.

(** The power series is strongly divergent outside the convergence circle *)
Lemma CV_circle_carac_not (a : nat -> R) (x : R) :
  Rbar_lt (CV_circle a) (Finite (Rabs x))
    -> ~ is_lim_seq (fun n => a n * x ^ n) 0.
Proof.
  case: (CV_circle_bounded a) => ub lub.
  move => Hx.
  have H : ~ (fun r : R => exists M : R, forall n : nat, Rabs (a n * r ^ n) <= M) x.
    contradict Hx ; apply Rbar_le_not_lt.
    apply ub.
    case: Hx => M Hx.
    exists M => n.
    by rewrite Rabs_mult RPow_abs Rabs_Rabsolu -Rabs_mult.
  contradict H.

  case: (H (mkposreal _ Rlt_0_1)) => /= {Hx} N Hx.
  
  set M := fix f N := match N with 
    | O => Rabs (a O * x ^ O) 
    | S n => Rmax (f n) (Rabs (a (n) * x ^ (n))) end.
  exists (Rmax (M N) 1) => n.
  case: (le_lt_dec N n) => Hn.
  apply Rle_trans with (2 := Rmax_r _ _).
  move: (Hx n Hn).
  rewrite Rminus_0_r.
  by apply Rlt_le.
  apply Rle_trans with (2 := Rmax_l _ _).
  elim: N n Hn {Hx} => [ | N IH] /= n Hn.
  by apply lt_n_O in Hn.
  apply lt_n_Sm_le, le_lt_eq_dec in Hn ; case: Hn => Hn.
  apply Rle_trans with (2 := Rmax_l _ _).
  by apply IH.
  rewrite Hn ; by apply Rle_trans with (2 := Rmax_r _ _), Rle_refl.
Qed.

(** ** Convergence criterion *)

(** D'Alembert Criterion for power series *)

Lemma DAlembert_ex_pseries_aux (a : nat -> R) (x k : R) : 
  x <> 0 -> (forall n, a n <> 0) ->
  (is_lim_seq (fun n => Rabs (a (S n) / a n)) k
    <-> is_lim_seq (fun n => Rabs ((a (S n) * x^(S n)) / (a n * x ^ n))) (Rabs x * k)).
Proof.
  move => Hx Ha ; split => H.
  apply (fun Heq => is_lim_seq_ext _ _ _ Heq (is_lim_seq_scal _ _ _ H)).
  move => n ; rewrite ?Rabs_div => //=.
  rewrite ?Rabs_mult.
  field.
  split ; apply Rabs_no_R0 => //.
  by apply pow_nonzero.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero.
  replace k with (/ (Rabs x) * ((Rabs x)*k)) by (field ; by apply Rabs_no_R0).
  apply (is_lim_seq_ext ((fun n : nat => / Rabs x * Rabs (a (S n) * x ^ S n / (a n * x ^ n)) ))).
  move => n ; rewrite ?Rabs_div => //=.
  rewrite ?Rabs_mult.
  field.
  repeat split ; apply Rabs_no_R0 => //.
  by apply pow_nonzero.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero.
  by apply is_lim_seq_scal.
Qed.

Lemma DAlembert_crit (a : nat -> R) (x:R) l :
  (forall n:nat, a n <> 0) ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  (l = 0 \/ (l <> 0 /\ Rabs x < / l)) 
    -> ex_series (fun n => Rabs (a n * x ^ n)).
Proof.
  move => Ha Hl H.
  case: (Req_dec x 0) => Hx.
  rewrite Hx.
  move: (ex_lim_seq_const (Rabs (a O))).
  apply ex_lim_seq_ext ; elim => /= [ | n IH].
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
  
  apply DAlembert_ex_series with (Rabs x * l).
  case: H => H.
  rewrite H Rmult_0_r ; by apply Rlt_0_1.
  replace 1 with (/ l * l) by (field ; apply H).
  apply Rmult_lt_compat_r.
  apply Rnot_le_lt ; case => H0.
  case: H => H.
  apply Rle_not_lt.
  apply Rlt_le, Rlt_le_trans with 0.
  by apply Rinv_lt_0_compat.
  by apply Rabs_pos.
  by case: H.
  by apply H.
  move => n ; apply Rmult_integral_contrapositive_currified.
  by apply Ha.
  by apply pow_nonzero.
  by apply DAlembert_ex_pseries_aux.
Qed.

Lemma DAlembert_CV_circle_neq_0 (a : nat -> R) (l : R) :
  (forall n:nat, a n <> 0) -> 0 < l ->
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) l ->
  CV_circle a = Finite (/l).
Proof.
  move => Ha Hl Hda.
  apply Rbar_le_antisym.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => /= cv [ub lub].
  apply lub => x Hax.
  apply Rbar_finite_le.
  case: (Rle_lt_dec x 0) => Hx.
  apply Rlt_le, Rle_lt_trans with 0.
  by apply Hx.
  by apply Rinv_0_lt_compat.
  rewrite -(Rabs_pos_eq x (Rlt_le _ _ Hx)).
  rewrite -(Rmult_1_l (/l)).
  replace (Rabs x) with ((Rabs x * l) /l) by (field ; apply Rgt_not_eq, Hl).
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rinv_0_lt_compat.
  apply Rnot_lt_le.
  contradict Hax.
  have : CV_circle_set a x -> is_lim_seq (fun n => a n * x ^ n) 0.
    move => H.
    apply ex_series_lim_0.
    by apply Abs_ex_series.
  move => H H0.
  move: (H H0) => {H H0}.
  apply (DAlembert_not_ex_series ) with (Rabs x * l) => //.
  move => n.
  apply Rmult_integral_contrapositive_currified => //.
  by apply pow_nonzero, Rgt_not_eq.
  apply DAlembert_ex_pseries_aux.
  by apply Rgt_not_eq.
  by apply Ha.
  by apply Hda.

  apply Rbar_not_lt_le.
  move : (CV_circle_carac_not a).
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ;
  case => [cv | | ] /= [ub lub] Hnot_ex H ; try by auto.
  suff H0 : cv < ((cv+/l)/2) < /l.
  absurd (ex_series (fun n => Rabs (a n * ((cv+/l)/2)^n))).
  
  suff H1 : cv < Rabs ((cv + / l) / 2).
  move: (Hnot_ex ((cv + / l) / 2) H1) => {Hnot_ex} Hnot_ex.
  contradict Hnot_ex ; by apply ex_series_lim_0, Abs_ex_series.
  apply Rlt_le_trans with (2 := Rle_abs _), H0.
  apply (DAlembert_crit) with l.
  by apply Ha.
  by apply Hda.
  right ; split.
  by apply Rgt_not_eq.
  rewrite Rabs_pos_eq.
  by apply H0.
  apply Rlt_le, Rle_lt_trans with (2 := proj1 H0).
  apply Rbar_finite_le, ub.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
    elim => [ | n IH] /=.
    by rewrite Rmult_1_r.
    by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
    by apply ex_lim_seq_const.
  pattern (/l) at 3 ;
  replace (/ l) with ((/l + / l) / 2) by (field ; by apply Rgt_not_eq).
  pattern (cv) at 1 ;
  replace (cv) with ((cv + cv) / 2) by field.
  split ; apply Rmult_lt_compat_r ; by intuition.
  case: (ub 0) => //.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
    elim => [ | n IH] /=.
    by rewrite Rmult_1_r.
    by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
    by apply ex_lim_seq_const.
Qed.

Lemma DAlembert_CV_circle_eq_0 (a : nat -> R) :
  (forall n:nat, a n <> 0) -> 
  is_lim_seq (fun n:nat => Rabs (a (S n) / a n)) 0 ->
  CV_circle a = p_infty.
Proof.
  move => Ha Hda.
  rewrite /CV_circle /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne ; case => [cv | | ] //= [ub lub] ;
  have : False => //.
  have H : CV_circle_set a (cv + 1).
    have H : 0 < cv + 1.
      apply Rlt_le_trans with (0+1).
      rewrite Rplus_0_l ; by apply Rlt_0_1.
      apply Rplus_le_compat_r.
      apply Rbar_finite_le, ub.
      apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
      elim => [ | k IH] /=.
      by rewrite Rmult_1_r.
      by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
      by apply ex_lim_seq_const.
      
    apply DAlembert_ex_series with 0.
    by apply Rlt_0_1.
    move => n ; apply Rmult_integral_contrapositive_currified.
    by[].
    by apply Rgt_not_eq, pow_lt.
  rewrite -(Rmult_0_r (Rabs (cv + 1))).
  apply (DAlembert_ex_pseries_aux a (cv + 1)).
  by apply Rgt_not_eq.
  by [].
  by [].
  move: (ub (cv+1) H).
  by apply Rbar_lt_not_le, Rlt_n_Sn.
  case: (ub 0) => //.
  apply ex_lim_seq_ext with (fun _ => Rabs (a O)).
  elim => [ | k IH] /=.
  by rewrite Rmult_1_r.
  by rewrite Rmult_0_l Rmult_0_r Rabs_R0 Rplus_0_r.
  by apply ex_lim_seq_const.
Qed.

(** Convergence normale *)

Lemma CV_circle_CVN (a : nat -> R) (r : posreal) :
  Rbar_lt (Finite r) (CV_circle a) -> CVN_r (fun n x => a n * x ^ n) r.
Proof.
  move => Hr.
  rewrite /CVN_r /Boule.
  have H := CV_circle_bounded a.
  exists (fun n => Rabs (a n * r ^ n)).
  exists (Series (fun n => Rabs (a n * r ^ n))) ; split.
  rewrite -(Rabs_pos_eq r (Rlt_le _ _ (cond_pos r))) in Hr.
  apply CV_circle_carac in Hr.
  apply Lim_seq_correct in Hr ; 
  rewrite -/(Series (fun n : nat => Rabs (a n * r ^ n))) in Hr.
  move => e He.
  case: (Hr (mkposreal e He)) => /= {Hr} N Hr.
  exists N => n Hn.
  replace (sum_f_R0 (fun k : nat => Rabs (Rabs (a k * r ^ k))) n)
    with (sum_f_R0 (fun k : nat => (Rabs (a k * r ^ k))) n).
  by apply Hr.
  elim: n {Hn} => /= [ | n IH] ; rewrite Rabs_Rabsolu.
  by [].
  by rewrite IH.
  move => n x Hx.
  rewrite ?Rabs_mult -?RPow_abs.
  apply Rmult_le_compat_l.
  by apply Rabs_pos.
  apply pow_incr ; split.
  by apply Rabs_pos.
  rewrite (Rabs_pos_eq r).
  rewrite Rminus_0_r in Hx.
  by apply Rlt_le.
  by apply Rlt_le, r.
Qed.

Lemma CV_circle_CVN_bis (a : nat -> R) (r : posreal) :
  CVN_r (fun n x => a n * x ^ n) r -> Rbar_le (Finite r) (CV_circle a).
Proof.
  case => An [l [H H0]].
  have H1 : is_lub_Rbar (CV_circle_set a) (CV_circle a).
    rewrite /CV_circle /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  have H2 : forall (y : R), 0 < y < r -> (CV_circle_set a y).
    move => y Hy.
    apply Comp_ex_series with An.
    move => n ; split.
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rabs_pos_eq Rminus_0_r.
    by apply Hy.
    by apply Rlt_le, Hy.
    exists l => eps.
    case: (H eps (cond_pos eps)) => N {H} H.
    exists N => n Hn.
    replace (sum_f_R0 (fun k : nat => An k) n)
      with (sum_f_R0 (fun k : nat => Rabs (An k)) n).
    by apply H.
    elim: n {Hn} => /= [ | n IH].
    apply Rabs_pos_eq.
    apply Rle_trans with (Rabs (a O * 0 ^ O)).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
    rewrite IH Rabs_pos_eq.
    by [].
    apply Rle_trans with (Rabs (a (S n) * 0 ^ (S n))).
    by apply Rabs_pos.
    apply H0 ; rewrite /Boule Rminus_0_r Rabs_R0 ; by apply r.
  have H3  : forall y, 0 < y < r -> Rbar_le (Finite (y)) (CV_circle a).
    move => y Hy.
    by apply H1, H2.
    have H4 := CV_circle_le_0 a.
    case: (CV_circle a) H3 H4 => /= [cv | | ] H3 H4.
    apply Rbar_not_lt_le => /= H5.
    apply Rbar_finite_le in H4.
    have H6 : 0 < (cv+r)/2 < r.
      split.
      apply Rdiv_lt_0_compat.
      apply Rplus_le_lt_0_compat.
      by apply H4.
      by apply Rle_lt_trans with cv.
      by apply Rlt_R0_R2.
      pattern (pos r) at 2 ; replace (pos r) with ((r+r)/2) by field.
      apply Rmult_lt_compat_r ; by intuition.
    move: (H3 _ H6).
    apply Rbar_lt_not_le => /=.
    pattern cv at 1 ; replace cv with ((cv+cv)/2) by field.
    apply Rmult_lt_compat_r ; by intuition.
    by left.
    by case: H4.
Qed.


Lemma CV_circle_CVU (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a) 
  -> exists r : posreal, CVU (fun n x => sum_f_R0 (fun k => a k * x ^ k) n) (PSeries a) x r.
Proof.
  move => Hx.
  have H : exists r : posreal, Rabs x < r /\ Rbar_lt (Finite r) (CV_circle a).
    case: (CV_circle a) Hx => /= [cv | | ] Hx.
    have H : 0 < (Rabs x + cv)/2.
    apply Rdiv_lt_0_compat.
    apply Rplus_le_lt_0_compat.
    by apply Rabs_pos.
    by apply Rle_lt_trans with (2 := Hx), Rabs_pos.
    by apply Rlt_R0_R2.
    exists (mkposreal _ H) => /=.
    pattern cv at 3 ; replace cv with ((cv+cv)/2) by field.
    pattern (Rabs x) at 1 ; replace (Rabs x) with ((Rabs x + Rabs x)/2) by field.
    split ; apply Rmult_lt_compat_r ; by intuition.
    have H : 0 < Rabs x + 1.
      apply Rle_lt_0_plus_1, Rabs_pos.
    exists (mkposreal _ H) => /=.
    split.
    by apply Rlt_plus_1.
    by [].
    by [].
  case: H => r H.
  apply CVN_CVU_r with r.
  by apply CV_circle_CVN, H.
  by apply H.
Qed.

(** * Operations *)

(** Addition of two power series *)

Definition PS_plus (a b : nat -> R) (n : nat) : R :=
  a n + b n.
Lemma is_pseries_plus (a b : nat -> R) (x la lb : R) :
  is_pseries a x la -> is_pseries b x lb
    -> is_pseries (PS_plus a b) x (la + lb).
Proof.
  move => Ha Hb.
  apply is_lim_seq_ext 
    with (fun n => (sum_f_R0 (fun k => a k * x ^ k) n) + (sum_f_R0 (fun k => b k * x ^ k) n)).
  elim => [ | n IH].
  simpl ; rewrite /PS_plus ; ring.
  simpl ; rewrite -IH /PS_plus ; ring.
  by apply is_lim_seq_plus with la lb.
Qed.
Lemma ex_pseries_plus (a b : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries b x
    -> ex_pseries (PS_plus a b) x.
Proof.
  move => [la Ha] [lb Hb].
  exists (la + lb).
  by apply is_pseries_plus.
Qed.
Lemma PSeries_plus (a b : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries b x
    -> PSeries (PS_plus a b) x = PSeries a x + PSeries b x.
Proof.
  intros Ha Hb.
  apply is_lim_seq_unique, is_pseries_plus ;
  by apply Lim_seq_correct.
Qed.

Lemma CV_circle_set_plus (a b : nat -> R) (x : R) :
  (CV_circle_set a x) -> (CV_circle_set b x) 
  -> (CV_circle_set (PS_plus a b) x).
Proof.
  move => Ha Hb.
  move: (ex_series_plus _ _ Ha Hb).
  apply Comp_ex_series => n ; split.
  by apply Rabs_pos.
  rewrite Rmult_plus_distr_r.
  by apply Rabs_triang.
Qed.
Lemma CV_circle_plus (a b : nat -> R) :
  Rbar_le (Rbar_min (CV_circle a) (CV_circle b)) (CV_circle (PS_plus a b)).
Proof.
  have Ha0 := CV_circle_le_0 a.
  have Hb0 := CV_circle_le_0 b.
  have Hab0 := CV_circle_le_0 (PS_plus a b).
  have Hmin_0 : Rbar_le (Finite 0) (Rbar_min (CV_circle a) (CV_circle b)).
    rewrite /Rbar_min ; by case: Rbar_le_dec => H.
  apply is_lub_Rbar_subset 
    with (CV_circle_set (PS_plus a b)) 
    (fun x => (CV_circle_set a x) /\ (CV_circle_set b x)).
  move => x [Ha Hb] ; by apply CV_circle_set_plus.
  rewrite /CV_circle /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  rewrite /Rbar_min ; case: Rbar_le_dec => Hle ; [case: Hle => Hle | ].

  apply is_lub_Rbar_eqset with (CV_circle_set a).
  move => x ; split => Hx.
  by apply Hx.
  split.
  by apply Hx.
  apply CV_circle_carac.
  apply Rbar_le_lt_trans with (2 := Hle).
  apply Rbar_not_lt_le => H1.
  apply (CV_circle_carac_not _ _ H1).
  by apply ex_series_lim_0, Abs_ex_series.
  rewrite /CV_circle /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.

  have Ha : is_lub_Rbar (fun x : R => CV_circle_set a x) (CV_circle a).
    rewrite /CV_circle /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  have Hb : is_lub_Rbar (fun x : R => CV_circle_set b x) (CV_circle b).
    rewrite /CV_circle /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
  rewrite -Hle in Hb.
  split => [x Hx | l Hl].
  case: Hx => Hx0 Hx1.
  by apply Ha.
  move: (proj2 Ha l) => {Ha} Ha.
  move: (proj2 Hb l) => {Hb} Hb.
  have H1 : Rbar_le (Finite 0) l.
    apply Hl ; split ; by apply CV_circle_0.
  case: l Hl Ha Hb H1 => [l | | ] Hl Ha Hb H1.
  apply Rbar_finite_le in H1.
  apply Rbar_not_lt_le => H0.
  case: {1 2 3 5 6}(CV_circle a) H0 Hl Ha Hb (eq_refl (CV_circle a)) Ha0 => /= [c | | ] H0 Hl Ha Hb Heq Ha0.
  case: (Hl ((l+c)/2)).
  split ; apply CV_circle_carac ; rewrite -?Hle ?Heq /=.
  have H : 0 <= ((l + c) / 2).
    apply Rmult_le_pos ; intuition.
    apply Rbar_finite_le in Ha0.
    by apply Rplus_le_le_0_compat.
  rewrite (Rabs_pos_eq _ H).
  pattern c at 2 ; replace c with ((c+c)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  have H : 0 <= ((l + c) / 2).
    apply Rmult_le_pos ; intuition.
    apply Rbar_finite_le in Ha0.
    by apply Rplus_le_le_0_compat.
  rewrite (Rabs_pos_eq _ H).
  pattern c at 2 ; replace c with ((c+c)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  apply Rle_not_lt, Rlt_le.
  pattern l at 1 ; replace l with ((l+l)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  rewrite Rbar_finite_eq ; apply Rgt_not_eq.
  pattern l at 2 ; replace l with ((l+l)/2) by field.
  apply Rmult_lt_compat_r ; by intuition.
  case: (Hl (l+1)).
  split ; apply CV_circle_carac ; by rewrite -?Hle ?Heq.
  apply Rle_not_lt, Rlt_le, Rlt_plus_1.
  rewrite Rbar_finite_eq ; apply Rgt_not_eq, Rlt_plus_1.
  by case: Ha0.
  by apply Rbar_not_lt_le => /=.
  by case: H1.

  apply Rbar_not_le_lt in Hle.
  apply is_lub_Rbar_eqset with (CV_circle_set b).
  move => x ; split => Hx.
  by apply Hx.
  split.
  apply CV_circle_carac.
  apply Rbar_le_lt_trans with (2 := Hle).
  apply Rbar_not_lt_le => H1.
  apply (CV_circle_carac_not _ _ H1).
  by apply ex_series_lim_0, Abs_ex_series.
  by apply Hx.
  rewrite /CV_circle /Lub_Rbar_ne ; by case: ex_lub_Rbar_ne.
Qed.

(** Scalar multiplication *)

Definition PS_scal (c : R) (a : nat -> R) (n : nat) : R :=
  c * a n.
Lemma is_pseries_scal (c : R) (a : nat -> R) (x l : R) :
  is_pseries a x l -> is_pseries (PS_scal c a) x (c * l).
Proof.
  move => Ha.
  apply is_lim_seq_ext with (fun n => c * (sum_f_R0 (fun k => a k * x ^ k) n)).
  elim => [ | n IH].
  simpl ; rewrite /PS_scal ; ring.
  simpl ; rewrite -IH /PS_scal ; ring.
  by apply is_lim_seq_scal.
Qed.
Lemma ex_pseries_scal (c : R) (a : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries (PS_scal c a) x.
Proof.
  move => [l Ha].
  exists (c * l).
  by apply is_pseries_scal.
Qed.
Lemma PSeries_scal (c : R) (a : nat -> R) (x : R) :
  PSeries (PS_scal c a) x = c * PSeries a x.
Proof.
  rewrite -Lim_seq_scal.
  apply Lim_seq_ext.
  elim => [ | n IH].
  simpl ; rewrite /PS_scal ; ring.
  simpl ; rewrite IH /PS_scal ; ring.
Qed.

(** Multiplication and division by a variable *)

Definition PS_incr_1 (a : nat -> R) (n : nat) : R :=
  match n with
    | 0 => 0
    | S n => a n
  end.
Lemma is_pseries_incr_1 (a : nat -> R) (x l : R) :
  is_pseries a x l -> is_pseries (PS_incr_1 a) x (x * l).
Proof.
  move => Ha.
  move: (is_lim_seq_scal _ x l Ha) => {Ha} Ha.
  apply is_lim_seq_incr.
  apply is_lim_seq_ext with (2 := Ha).
  case.
  simpl ; ring.
  elim => /= [ | n IH].
  ring.
  rewrite -IH ; ring.
Qed.
Lemma ex_pseries_incr_1 (a : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries (PS_incr_1 a) x.
Proof.
  move => [l Ha] ; exists (x * l) ; by apply is_pseries_incr_1.
Qed.
Lemma PSeries_incr_1 a x :
  PSeries (PS_incr_1 a) x = x * PSeries a x.
Proof.
  rewrite -Lim_seq_scal.
  unfold PSeries.
  rewrite -(Lim_seq_incr (sum_f_R0 (fun k : nat => PS_incr_1 a k * x ^ k))) /=.
  apply Lim_seq_ext.
  case.
  simpl ; ring.
  elim => /= [ | n IH].
  ring.
  rewrite IH ; ring.
Qed.

Fixpoint PS_incr_n (a : nat -> R) (n k : nat) : R :=
  match n with
    | O => a k
    | S n => PS_incr_1 (PS_incr_n a n) k
  end.
Lemma PS_incr_n_simplify (a : nat -> R) (n k : nat) :
  PS_incr_n a n k = 
  match (le_lt_dec n k) with
    | left _ => a (k-n)%nat
    | right _ => 0
  end.
Proof.
  case: le_lt_dec => H.
  elim: n k H => [ | n IH] k H.
  rewrite /PS_incr_n ; by case: k H.
  case: k H => [ | k] H.
  by apply le_Sn_0 in H.
  rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
  rewrite IH.
  apply f_equal.
  by elim: n k H {IH} => /= [ | n IH] k H.
  by apply le_S_n.
  elim: n k H => [ | n IH] k H.
  by apply lt_n_O in H.
  rewrite /PS_incr_n -/PS_incr_n /PS_incr_1.
  case: k H => [ | k] H.
  by [].
  by apply IH, lt_S_n.
Qed.
Lemma is_pseries_incr_n (a : nat -> R) (n : nat) (x l : R) :
  is_pseries a x l -> is_pseries (PS_incr_n a n) x (x^n * l).
Proof.
  move => Ha.
  elim: n => /= [ | n IH].
  by rewrite Rmult_1_l.
  rewrite Rmult_assoc.
  by apply is_pseries_incr_1.
Qed.
Lemma ex_pseries_incr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x -> ex_pseries (PS_incr_n a n) x.
Proof.
  move => [l Ha].
  exists (x^n*l) ; by apply is_pseries_incr_n.
Qed.
Lemma PSeries_incr_n (a : nat -> R) (n : nat) (x : R) :
  PSeries (PS_incr_n a n) x = x^n * PSeries a x.
Proof.
  elim: n => /= [ | n IH].
  by rewrite Rmult_1_l.
  rewrite Rmult_assoc.
  by rewrite PSeries_incr_1 IH.
Qed.

Definition PS_decr_1 (a : nat -> R) (n : nat) : R :=
  a (S n).
Lemma is_pseries_decr_1 (a : nat -> R) (x l : R) :
  x <> 0 -> is_pseries a x l 
    -> is_pseries (PS_decr_1 a) x ((l - a O) / x).
Proof.
  move => Hx Ha eps.
  have He : 0 < eps * Rabs x.
    apply Rmult_lt_0_compat.
    by apply eps.
    by apply Rabs_pos_lt.
  case: (Ha (mkposreal _ He)) => /= {Ha} N Ha.
  exists N => n Hn.
  rewrite /PS_decr_1.
  replace (sum_f_R0 (fun k : nat => a (S k) * x ^ k) n - (l - a 0%nat) / x)
    with ((sum_f_R0 (fun k : nat => a k * x ^ k) (S n) - l)/x).
  Focus 2.
    elim: n {Hn} => /= [ | n IH].
    by field.
    rewrite /Rminus (Rplus_assoc (sum_f_R0 (fun k : nat => a (S k) * x ^ k) n)).
    rewrite (Rplus_comm (a (S (S n)) * (x * x ^ n))).
    rewrite -(Rplus_assoc (sum_f_R0 (fun k : nat => a (S k) * x ^ k) n)).
    rewrite /Rminus in IH ; rewrite -IH.
    by field.
  rewrite Rabs_div.
  apply Rlt_div.
  by apply Rabs_pos_lt.
  apply Ha ; by intuition.
  by [].
Qed.
Lemma ex_pseries_decr_1 (a : nat -> R) (x : R) :
  ex_pseries a x -> ex_pseries (PS_decr_1 a) x.
Proof.
  move => [l Ha].
  case: (Req_dec x 0) => Hx.
  rewrite Hx ; by apply ex_pseries_0.
  exists ((l-a O)/x) ; by apply is_pseries_decr_1.
Qed.
Lemma PSeries_decr_1 (a : nat -> R) (x : R) :
  ex_pseries a x 
    -> PSeries a x = a O + x * PSeries (PS_decr_1 a) x.
Proof.
  move => Ha.
  case: (Req_dec x 0) => Hx.
  rewrite Hx PSeries_0 ; ring.
  move: (is_pseries_decr_1 a x (PSeries a x) Hx (Lim_seq_correct _ Ha)) => Hb.
  rewrite {2}/PSeries (is_lim_seq_unique _ _ Hb).
  by field.
Qed.
Lemma PSeries_decr_1_aux (a : nat -> R) (x : R) :
  a O = 0 -> (PSeries a x) = x * PSeries (PS_decr_1 a) x.
Proof.
  intros Ha0.
  rewrite -PSeries_incr_1.
  rewrite /PS_incr_1 /PS_decr_1 /=.
  apply Lim_seq_ext.
  elim => [ | n IH] /=.
  by rewrite Ha0.
  by rewrite IH.
Qed.

Definition PS_decr_n (a : nat -> R) (n k : nat) : R :=
  a (n + k)%nat.
Lemma is_pseries_decr_n (a : nat -> R) (n : nat) (x l : R) :
  x <> 0 -> (0 < n)%nat -> is_pseries a x l 
    -> is_pseries (PS_decr_n a n) x ((l - sum_f_R0 (fun k => a k * x^k) (n-1)%nat)/x^n).
Proof.
  move => Hx Hn Ha.
  case: n Hn => [ | n] Hn.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl ; rewrite -minus_n_O /PS_decr_n /=.
  elim: n => /= [ | n IH].
  rewrite ?Rmult_1_r.
  by apply is_pseries_decr_1.
  set ln := ((l - sum_f_R0 (fun k : nat => a k * x ^ k) n) / (x * x ^ n)) ;
  rewrite -/ln in IH.
  replace ((l - (sum_f_R0 (fun k : nat => a k * x ^ k) n + a (S n) * (x * x ^ n))) /
    (x * (x * x ^ n))) with ((ln - a (S (n + 0)))/x).
  move: (is_pseries_decr_1 (fun k : nat => a (S (n + k))) x ln Hx IH).
  rewrite /PS_decr_1 /=.
  apply is_pseries_ext => k.
  apply f_equal ; ring.
  rewrite /ln plus_0_r ; field ; split.
  by apply pow_nonzero.
  by [].
Qed.
Lemma ex_pseries_decr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x -> ex_pseries (PS_decr_n a n) x.
Proof.
  move => Ha.
  elim: n => [ | n IH].
  move: Ha ; apply ex_pseries_ext => n ; by rewrite /PS_decr_n.
  move: (ex_pseries_decr_1 _ _ IH).
  apply ex_pseries_ext => k.
  rewrite /PS_decr_1 /PS_decr_n.
  apply f_equal ; ring.
Qed.
Lemma PSeries_decr_n (a : nat -> R) (n : nat) (x : R) :
  ex_pseries a x
    -> PSeries a x = sum_f_R0 (fun k => a k * x^k) n + x^(S n) * PSeries (PS_decr_n a (S n)) x.
Proof.
  move => Ha.
  case: (Req_dec x 0) => Hx.
  rewrite Hx PSeries_0 ; simpl ; ring_simplify.
  elim: n => /= [ | n IH].
  ring.
  rewrite -IH ; ring.
  move: (is_pseries_decr_n a (S n) x (PSeries a x) Hx (lt_0_Sn _) (Lim_seq_correct _ Ha)) => Hb.
  rewrite {2}/PSeries (is_lim_seq_unique _ _ Hb).
  simpl ; rewrite -minus_n_O ; field.
  split.
  by apply pow_nonzero.
  by [].
Qed.
Lemma PSeries_decr_n_aux (a : nat -> R) (n : nat) (x : R) :
  (forall k : nat, (k < n)%nat -> a k = 0) 
    -> PSeries a x = x^n * PSeries (PS_decr_n a n) x.
Proof.
  elim: n => /= [ | n IH] Ha.
  rewrite Rmult_1_l.
  apply PSeries_ext => n ; by intuition.
  rewrite IH.
  rewrite PSeries_decr_1_aux.
  rewrite (Rmult_comm _ (x^n)) Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  apply PSeries_ext => k ; rewrite /PS_decr_1 /PS_decr_n ; by intuition.
  apply Ha ; by intuition.
  move => k Hk.
  apply Ha ; by intuition.
Qed.

(** Sums on even and odd *)

Lemma is_pseries_odd_even (a : nat -> R) (x l1 l2 : R) :
  is_pseries (fun n => a (2*n)%nat) (x^2) l1 -> is_pseries (fun n => a (2*n+1)%nat) (x^2) l2
    -> is_pseries a x (l1 + x * l2).
Proof.
rewrite /is_pseries.
  move => H1 H2.
  apply is_lim_seq_ext with (fun n => 
    (sum_f_R0 (fun k : nat => a (2 * k)%nat * (x ^ 2) ^ k) (div2 n)) +
    x * match n with | O => 0 
    | S n => (sum_f_R0 (fun k : nat => a (2 * k + 1)%nat * (x ^ 2) ^ k) (div2 n)) end).
  case => [ | n].
  simpl ; ring.
  case: (even_odd_dec n) => Hn.
(* even n *)
  rewrite -(even_div2 _ Hn) {3}(even_double _ Hn).
  elim: (div2 n) => {n Hn} [ | n] ;
  rewrite ?double_S /sum_f_R0 -/sum_f_R0.
  rewrite /double /= ; ring.
  rewrite -pow_mult.
  replace (2 * S n)%nat with (S (S (double n))) 
    by (rewrite -double_S /double ; ring).
  replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
  move => <- ; simpl ; ring.
(* odd n *)
  rewrite -(odd_div2 _ Hn) {3}(odd_double _ Hn).
  elim: (div2 n) => {n Hn} [ | n] ;
  rewrite ?double_S /sum_f_R0 -/sum_f_R0.
  rewrite /double /= ; ring.
  rewrite -?pow_mult.
  replace (2 * S n)%nat with (S (S (double n))) 
    by (rewrite -double_S /double ; ring).
  replace (2 * S (S n))%nat with (S (S (S (S (double n))))) 
    by (rewrite -double_S /double ; ring).
  replace (S (S (double n)) + 1)%nat with (S (S (S (double n)))) by ring.
  move => <- ; simpl ; ring.
  apply is_lim_seq_plus with l1 (x*l2).
(* a(2k)x^(2k) *)
  move => eps ; case: (H1 eps) => {H1} N H1.
  exists (double N) => n Hn.
  apply H1.
  case: (even_odd_dec n) => Hn'.
  rewrite (even_double _ Hn') in Hn.
  elim: (div2 n) N Hn {H1 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
  rewrite (odd_double _ Hn') in Hn.
  elim: (div2 n) N Hn {H1 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_S_n, le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
(* a(2k+1)x^(2k+1) *)
  apply is_lim_seq_scal.
  move => eps ; case: (H2 eps) => {H1 H2} N H2.
  exists (S (double N)) => n Hn.
  case: n Hn => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  apply H2.
  case: (even_odd_dec n) => Hn'.
  rewrite (even_double _ Hn') in Hn.
  elim: (div2 n) N Hn { H2 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_S_n, le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
  rewrite (odd_double _ Hn') in Hn.
  elim: (div2 n) N Hn {H2 Hn'} => {n} /= [ | n IH] ;
  case => [ | N] Hn.
  by [].
  rewrite double_S in Hn ; by apply le_S_n, le_S_n, le_Sn_0 in Hn.
  apply le_0_n.
  rewrite ?double_S in Hn ; apply le_n_S, IH.
  by apply le_S_n, le_S_n.
  by [].
Qed.
Lemma ex_pseries_odd_even (a : nat -> R) (x : R) :
  ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2)
    -> ex_pseries a x.
Proof.
  move => [l1 H1] [l2 H2].
  exists (l1 + x * l2).
  by apply is_pseries_odd_even.
Qed.
Lemma PSeries_odd_even (a : nat -> R) (x : R) :
  ex_pseries (fun n => a (2*n)%nat) (x^2) -> ex_pseries (fun n => a (2*n+1)%nat) (x^2)
    -> PSeries a x = PSeries (fun n => a (2*n)%nat) (x^2) + x * PSeries (fun n => a (2*n+1)%nat) (x^2).
Proof.
  move => H1 H2 ;
  apply is_lim_seq_unique.
  apply is_pseries_odd_even ; by apply Lim_seq_correct.
Qed.

(** Coming soon: (* bonus *)
  - multiplication
  - composition
  - inverse *)

(** * Analysis *)

(** Continuity *)

Lemma PSeries_continuity (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a) 
    -> continuity_pt (PSeries a) x.
Proof.
  move => H.
  case: (CV_circle_CVU a x H) => r H0.
  apply (CVU_continuity 
    (fun (n : nat) (x : R) => sum_f_R0 (fun k : nat => a k * x ^ k) n)
    (PSeries a) x r H0).
  move => n y Hy.
  apply continuity_pt_finite_SF.
  move => k Hk.
  apply continuity_pt_scal.
  elim: k {Hk} => /= [ | k IH].
  by apply continuity_pt_const => d f.
  apply continuity_pt_mult.
  apply derivable_continuous_pt, derivable_pt_id.
  by apply IH.
  rewrite /Boule Rminus_eq0 Rabs_R0 ; by apply r.
Qed.

Definition PS_derive (a : nat -> R) (n : nat) :=
  INR (S n) * a (S n).
Lemma PS_derive_circle (a : nat -> R) :
  CV_circle (PS_derive a) = CV_circle a.
Proof.
  have H := (CV_circle_bounded a).
  have H0 := (CV_circle_bounded (PS_derive a)).

  apply Rbar_le_antisym.
  apply is_lub_Rbar_subset with (2 := H) (3 := H0) => x [M Ha].
  exists (Rmax (Rabs (a O)) (Rabs x * M)) ; case => /= [ | n].
  rewrite Rmult_1_r ; by apply Rmax_l.
  apply Rle_trans with (2 := Rmax_r _ _).
  replace (a (S n) * (x * x ^ n)) 
    with (x  * ((PS_derive a n * x ^ n) / INR (S n)))
    by (rewrite /PS_derive ; field ; apply not_0_INR, sym_not_eq, O_S).
  rewrite Rabs_mult ; apply Rmult_le_compat_l.
  by apply Rabs_pos.
  rewrite Rabs_div ; [ | by apply not_0_INR, sym_not_eq, O_S].
  apply Rle_div.
  by apply Rabs_pos_lt, not_0_INR, sym_not_eq, O_S.
  apply Rle_trans with (1 := Ha n).
  rewrite -{1}(Rmult_1_r M).
  apply Rmult_le_compat_l.
  by apply Rle_trans with (2 := Ha O), Rabs_pos.
  by apply Rle_trans with (2 := Rle_abs _), (le_INR 1), le_n_S, le_O_n.
  
  apply H => x [M Hx].
  
  have H1 : Rbar_le (Finite 0) (CV_circle (PS_derive a)).
    apply H0 ; exists (Rabs (PS_derive a O)) ; case => /= [ | n].
    rewrite Rmult_1_r ; by apply Rle_refl.
    rewrite Rmult_0_l Rmult_0_r Rabs_R0 ; by apply Rabs_pos.
  wlog: x Hx / (0 < x) => [Hw |  Hx0].
    case: (Rle_lt_dec x 0) => Hx0.
    apply Rbar_le_trans with (Finite 0).
    by apply Rbar_finite_le.
    by apply H1.
    by apply Hw.
  
  suff : forall y, 0 < y < x -> Rbar_le (Finite y) (CV_circle (PS_derive a)).
    case: (CV_circle (PS_derive a)) H1 => [l | | ] /= H1 H2.
    apply Rbar_not_lt_le => /= H3.
    have H4 : (0 < (x+l)/2 < x).
      apply Rbar_finite_le in H1.
      split.
      apply Rdiv_lt_0_compat.
      by apply Rplus_lt_le_0_compat.
      by apply Rlt_R0_R2.
      apply Rminus_lt, Ropp_lt_cancel ; field_simplify.
      rewrite -Rdiv_1 ; apply Rdiv_lt_0_compat.
      by apply -> Rlt_Rminus.
      by apply Rlt_R0_R2.
    move: (H2 _ H4).
    apply Rbar_lt_not_le => /=.
    apply Rminus_lt, Ropp_lt_cancel ; field_simplify.
    rewrite -Rdiv_1 ; apply Rdiv_lt_0_compat.
    rewrite Rplus_comm ; by apply -> Rlt_Rminus.
    by apply Rlt_R0_R2.
    by left.
    by case: H1.
  move => y Hy.
  apply H0 ; rewrite /PS_derive.
  have H2 : is_lim_seq (fun n => INR (S n) / x * (y/x) ^ n) 0.
    apply ex_series_lim_0.
    apply Abs_ex_series.
    apply DAlembert_crit with 1.
    move => n.
    apply Rgt_not_eq, Rdiv_lt_0_compat.
    by apply lt_0_INR, lt_O_Sn.
    apply Rlt_trans with y ; by apply Hy.
    move => eps.
    case: (nfloor_ex (/eps)) => [ | N HN].
    by apply Rlt_le, Rinv_0_lt_compat, eps.
    exists (S N) => n Hn.
    apply Rabs_lt_between'.
    replace (INR (S (S n)) / x / (INR (S n) / x))
      with (INR (S (S n)) / (INR (S n)))
      by (field ; split ; [apply Rgt_not_eq, Rlt_trans with y ; by apply Hy | 
       by apply Rgt_not_eq, lt_0_INR, lt_O_Sn]).
    rewrite Rabs_pos_eq.
    split.
    apply Rdiv_lt.
    by apply lt_0_INR, lt_O_Sn.
    rewrite ?S_INR Rlt_Rminus ; ring_simplify.
    rewrite Rplus_assoc.
    apply Rplus_le_lt_0_compat.
    apply Rmult_le_pos.
    by apply (le_INR O), le_O_n.
    by apply Rlt_le, eps.
    by apply Rle_lt_0_plus_1, Rlt_le, eps.
    apply Rlt_div.
    by apply lt_0_INR, lt_O_Sn.
    rewrite ?S_INR Rlt_Rminus ; ring_simplify.
    rewrite /Rminus Rplus_assoc -/(Rminus eps 1).
    rewrite -(Ropp_involutive (eps-1)) -Rlt_Rminus Ropp_minus_distr'.
    apply Rlt_trans with 1.
    apply Rlt_Rminus ; ring_simplify ; by apply eps.
    replace 1 with (eps*/eps) by (field ; apply Rgt_not_eq, eps).
    apply Rmult_lt_compat_l.
    by apply eps.
    apply Rlt_le_trans with (1 := proj2 HN).
    rewrite -S_INR ; by apply le_INR.
    apply Rlt_le, Rdiv_lt_0_compat ; by apply lt_0_INR, lt_O_Sn.
    right ; split.
    by apply Rgt_not_eq, Rlt_0_1.
    rewrite Rinv_1 Rabs_pos_eq.
    apply -> Rdiv_lt_1.
    by apply Hy.
    apply Rlt_trans with y ; by apply Hy.
    apply Rlt_le, Rdiv_lt_0_compat.
    by apply Hy.
    apply Rlt_trans with y ; by apply Hy.
    case: (H2 (mkposreal _ (Rlt_0_1))) ;
    simpl pos => {H2} N HN.
    set My := fix f n := match n with
      | O => 1
      | S n => Rmax (Rabs (INR (S n) / x * (y / x) ^ n)) (f n)
    end.
    exists (M * My N) => n.
    replace (INR (S n) * a (S n) * y ^ n)
      with ((a (S n) * x ^ (S n)) * (INR (S n) /x * (y / x) ^ n))
      by (rewrite /pow -/pow ; apply Rminus_diag_uniq ; field_simplify ;
      [rewrite -?Rdiv_1 | apply Rgt_not_eq, Rlt_trans with y ; by apply Hy ] ;
      rewrite ?Rmult_assoc -(Rmult_minus_distr_l (a (S n))) ;
      apply Rmult_eq_0_compat_l ;
      rewrite Rmult_comm Rmult_assoc -(Rmult_minus_distr_l (INR (S n))) ;
      apply Rmult_eq_0_compat_l, Rminus_diag_eq ; 
      elim: n => /= [ | n IH] ; [ring 
      | rewrite -IH ; field ; apply Rgt_not_eq, Rlt_trans with y ; by apply Hy]).
    rewrite Rabs_mult ; apply Rmult_le_compat.
    by apply Rabs_pos.
    by apply Rabs_pos.
    by apply Hx.
    case: (le_lt_dec N n) => Hn.
    apply Rle_trans with 1.
    move: (HN n Hn) ; rewrite Rminus_0_r ; by apply Rlt_le.
    move: (HN n Hn) => {HN Hn} ;
    elim: N => [ | N IH] H2. 
    simpl ; by apply Rle_refl.
    apply Rle_trans with (1 := IH H2) ;
    rewrite /My -/My ; by apply Rmax_r.
    elim: N n Hn {HN} => [ | N IH] n Hn.
    by apply lt_n_O in Hn.
    apply le_S_n in Hn ; case: (le_lt_eq_dec _ _ Hn) => {Hn} Hn.
    apply Rle_trans with (2 := Rmax_r _ (My N)) ; by apply IH.
    rewrite Hn ; by apply (Rmax_l _ (My N)).
Qed.

Lemma is_derive_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a)
    -> is_derive (PSeries a) x (PSeries (PS_derive a) x).
Proof.
  move => Hx.

  case: (CV_circle_CVU _ _ Hx) => r0 Hr0 ;
  rewrite -PS_derive_circle in Hx ;
  case: (CV_circle_CVU _ _ Hx) => r1 Hr1 ;
  rewrite PS_derive_circle in Hx.
  apply CVU_dom_equiv in Hr0 ;
  apply CVU_dom_equiv in Hr1.
  have Hr : 0 < Rmin r0 r1.
    apply Rmin_case.
    by apply r0.
    by apply r1.
  set r := mkposreal _ Hr.
  set b := x - r/2.
  set c := x + r/2.
  
  have H := CVU_Derive (fun n x => sum_f_R0 (fun k => a k * x ^ k) n) b c.
  have H0 : b < c.
    rewrite /b /c Rlt_Rminus.
    replace (x + r / 2 - (x - r / 2)) with (pos r) by field.
    by apply r.
  move: (H H0) => {H} H.
  have H1 : forall x,
    is_derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) O) x 0.
    move => y /= ; by apply derivable_pt_lim_const.
  have H2 : (forall (n : nat) (x : R),
    is_derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) (S n)) x
      (sum_f_R0 (fun k => PS_derive a k * x ^ k) n)).
    elim => [ | n IH] y.
    rewrite /PS_derive /= Rmult_1_l -(Rplus_0_l (a 1%nat*1)).
    apply is_derive_ext with (fun x => a O + a 1%nat * x).
    move => t ; ring.
    apply derivable_pt_lim_plus.
    by apply derivable_pt_lim_const.
    by apply (derivable_pt_lim_scal id), derivable_pt_lim_id.
    apply derivable_pt_lim_plus with (1 := IH y).
    rewrite /PS_derive (Rmult_comm _ (a _)) Rmult_assoc.
    apply derivable_pt_lim_scal.
    apply derivable_pt_lim_pow.
  have H3 : (forall (n : nat) (x : R),
    b <= x <= c ->
    ex_derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) n) x).
    case => [ | n] y _.
    by exists 0.
    by exists (sum_f_R0 (fun k : nat => PS_derive a k * y ^ k) n).
  
  move: (H H3) => {H} H.
  have H4 : (forall (n : nat) (x : R),
    b <= x <= c -> continuity_pt
      (Derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) n)) x).
    case => [ | n] y _.
    have H4 : continuity_pt (fun _ => 0) y.
      by apply continuity_pt_const.
    move => e He ; case: (H4 e He) => {H4} d [Hd H4].
    exists d ; split.
    by apply Hd.
    move => z [Hz0 Hz].
    rewrite (is_derive_unique _ _ _ (H1 y)).
    rewrite (is_derive_unique _ _ _ (H1 z)).
    apply (H4 z) ; by split.
    have H4 : continuity_pt (fun x => sum_f_R0 (fun k : nat => PS_derive a k * x ^ k) n) y.
      apply continuity_pt_finite_SF => N HN.
      apply continuity_pt_scal.
      elim: N {HN} => [ | N IH].
      by apply continuity_pt_const.
      apply continuity_pt_mult.
      apply derivable_continuous, derivable_id.
      by apply IH.
    move => e He ; case: (H4 e He) => {H4} d [Hd H4].
    exists d ; split.
    by apply Hd.
    move => z [Hz0 Hz].
    rewrite (is_derive_unique _ _ _ (H2 n y)).
    rewrite (is_derive_unique _ _ _ (H2 n z)).
    apply (H4 z) ; by split.
  
  move: (H H4) => {H} H.
  have H5 : b <= x <= c.
    rewrite /c /b ; split ; apply Rminus_le ; ring_simplify ;
    by apply Rlt_le, Ropp_lt_gt_0_contravar, is_pos_div_2.
  have H6 : (exists y : R,
    b <= y <= c /\
    ex_lim_seq (fun n : nat => sum_f_R0 (fun k : nat => a k * y ^ k) n)).
    exists x ; split.
    by apply H5.
    apply (Abs_ex_series (fun k => a k * x ^ k)).
    by apply CV_circle_carac.
  
  move: (H H6) => {H} H.
  have H7 : CVU_dom
    (fun (n : nat) (x : R) =>
    Derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) n) x)
    (fun x : R => b <= x <= c).
    have H7 : CVU_dom
      (fun (n : nat) (x0 : R) =>
      Derive (fun x1 : R => sum_f_R0 (fun k : nat => a k * x1 ^ k) n) x0)
      (Boule x r).
      move => eps.
      case: (Hr1 eps) => {Hr1} N Hr1 ;
      exists (S N) => n y Hy Hn.
      case: n Hn => [ | n] Hn.
      by apply le_Sn_O in Hn.
      apply le_S_n in Hn.
      have Hy1 : Boule x r1 y.
        apply Rlt_le_trans with (1 := Hy).
        rewrite /r /= ; apply Rmin_r.
      move: (Hr1 n y Hy1 Hn) => {Hr1}.
      rewrite (is_derive_unique _ _ _ (H2 n y)).
      rewrite -(Lim_seq_incr (fun n0 : nat =>
      Derive (fun x1 : R => sum_f_R0 (fun k : nat => a k * x1 ^ k) n0) y)).
      rewrite (Lim_seq_ext (fun n0 : nat =>
        Derive (fun x1 : R => sum_f_R0 (fun k : nat => a k * x1 ^ k) (S n0)) y)
        (fun n0 : nat => sum_f_R0 (fun k : nat => PS_derive a k * y ^ k) (n0))).
      by [].
      move => m.
      by rewrite (is_derive_unique _ _ _ (H2 m y)).
    move => eps.
    case: (H7 eps) => {H7} N H7.
    exists N => n y Hy Hn.
    apply H7.
    rewrite /Boule Rabs_lt_between' ; split.
    apply Rlt_le_trans with (2 := proj1 Hy).
    rewrite /b Rlt_Rminus ; field_simplify ; rewrite -Rdiv_1 ; by apply is_pos_div_2.
    apply Rle_lt_trans with (1 := proj2 Hy).
    rewrite /c Rlt_Rminus ; field_simplify ; rewrite -Rdiv_1 ; by apply is_pos_div_2.
    by apply Hn.
  
  move: (H H7) => {H} [H9 [H10 [H11 H]]].
  rewrite /PSeries.
  rewrite (Lim_seq_ext (sum_f_R0 (fun k : nat => PS_derive a k * x ^ k))
    (fun n : nat =>
    Derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) (S n)) x)).
  rewrite (Lim_seq_incr (fun n : nat =>
    Derive (fun x0 : R => sum_f_R0 (fun k : nat => a k * x0 ^ k) (n)) x)).
  rewrite -H.
  apply is_derive_ext with (fun y : R =>
    Lim_seq (fun n : nat => sum_f_R0 (fun k : nat => a k * y ^ k) n)).
    move => t ; by apply Lim_seq_ext.
  apply Derive_correct.
  by apply H10.
  by [].
  move => n ; apply sym_eq.
  by apply is_derive_unique.
  move => y Hy /= ; by apply Lim_seq_ext.
  move => y Hy /= ; by apply Lim_seq_ext.
  move => y Hy /= ; by apply Lim_seq_ext.
Qed.
Lemma ex_derive_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a)
    -> ex_derive (PSeries a) x.
Proof.
  move => Hx ; exists (PSeries (PS_derive a) x).
  by apply is_derive_PSeries.
Qed.
Lemma Derive_PSeries (a : nat -> R) (x : R) :
  Rbar_lt (Finite (Rabs x)) (CV_circle a)
    -> Derive (PSeries a) x = PSeries (PS_derive a) x.
Proof.
  move => H.
  apply is_derive_unique.
  by apply is_derive_PSeries.
Qed.

(** Coming soon *) (* bonus *)

(** * Bessel functions *)

Definition Bessel1_seq (n k : nat) :=
  (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).

Lemma ex_Bessel1 (n : nat) (x : R) :
  ex_pseries (Bessel1_seq n) x.
Proof.
  have H : forall k, Bessel1_seq n k <> 0.
    move => k.
    rewrite /Bessel1_seq.
    apply Rmult_integral_contrapositive_currified.
    apply pow_nonzero, Ropp_neq_0_compat, R1_neq_R0.
    apply Rinv_neq_0_compat, Rmult_integral_contrapositive_currified ;
    apply INR_fact_neq_0.
  apply Abs_ex_series.
  apply DAlembert_crit with 0.
  by apply H.
  move => eps.
  have H0 : 0 <= /(sqrt eps).
    apply Rlt_le, Rinv_0_lt_compat, sqrt_pos_lt, eps.
  set N := nfloor (/(sqrt eps)) H0.
  exists N => k Hk.
  rewrite Rminus_0_r Rabs_Rabsolu Rabs_div.
  rewrite 2?Rabs_div ?Rabs_mult -?RPow_abs ?Rabs_Ropp ?Rabs_R1 
    ?pow1 ?(Rabs_pos_eq _ (pos_INR _)) ?H2.
  rewrite /Rdiv ?Rmult_1_l.
  rewrite Rinv_involutive.
  rewrite -plus_n_Sm.
  rewrite /fact -/fact ?mult_INR.
  field_simplify ; rewrite -?Rdiv_1 /Rdiv ?Rmult_1_l.
  rewrite Rinv_mult_distr.
  rewrite -(sqrt_sqrt eps (Rlt_le _ _ (cond_pos eps))).
  apply Rmult_gt_0_lt_compat ; try by intuition.
  apply sqrt_pos_lt, eps.
  rewrite -(Rinv_involutive (sqrt eps)).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; try by intuition.
  apply Rinv_0_lt_compat, sqrt_pos_lt, eps.
  apply Rlt_le_trans with (INR (S N)).
  rewrite /N /nfloor in Hk |- * ;
  case: nfloor_ex Hk => {N} /= N HN Hk ; rewrite -/(INR (S N)) S_INR.
  by apply HN.
  by apply le_INR, le_n_S.
  apply Rgt_not_eq, sqrt_pos_lt, eps.
  rewrite -(Rinv_involutive (sqrt eps)).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat ; try by intuition.
  apply Rinv_0_lt_compat, sqrt_pos_lt, eps.
  apply Rlt_le_trans with (INR (S N)).
  rewrite /N /nfloor in Hk |- * ;
  case: nfloor_ex Hk => {N} /= N HN Hk ; rewrite -/(INR (S N)) S_INR.
  by apply HN.
  apply le_INR, le_n_S ; by intuition.
  apply Rgt_not_eq, sqrt_pos_lt, eps.
  apply Rgt_not_eq ; by intuition.
  apply Rgt_not_eq ; by intuition.
  repeat split.
  apply INR_fact_neq_0.
  apply Rgt_not_eq ; by intuition.
  apply INR_fact_neq_0.
  apply Rgt_not_eq ; by intuition.
  apply Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
  apply Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
  apply Rmult_integral_contrapositive_currified ; apply INR_fact_neq_0.
  by apply H.
  by left.
Qed.

Lemma CV_Bessel1 (n : nat) :
  CV_circle (Bessel1_seq n) = p_infty.
Proof.
  have : forall x : R, Rbar_le (Finite x) (CV_circle (Bessel1_seq n)).
  move => x ; apply Rbar_le_trans with (Finite (Rabs x)).
    by apply Rbar_finite_le, Rle_abs.
  apply Rbar_not_lt_le => Hx.
  apply CV_circle_carac_not in Hx.
  apply: Hx.
  by apply ex_series_lim_0, (ex_Bessel1 n x).
  
  rewrite /CV_circle /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ;
  case => /= [c | | ] Hc Hx.
  have: False => // ; move: (Hx (c+1)).
  apply Rbar_lt_not_le => /=.
  by apply Rlt_plus_1.
  by [].
  by case: (Hx 0).
Qed.

Definition Bessel1 (n : nat) (x : R) :=
  (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_equality_1 (n : nat) (x : R) : (0 < n)%nat -> x<>0
  -> Bessel1 (n+1)%nat x + Bessel1 (n-1)%nat x = (2*INR n)/x * Bessel1 n x.
Proof.
  case: n => [ | n] Hn Hx.
  by apply lt_irrefl in Hn.
  clear Hn.
  replace (S n - 1)%nat with n by (case: n => //=).
  replace (S n + 1)%nat with (S (S n)) by ring.
  rewrite /Bessel1.
  rewrite -Rmult_assoc.
  replace (2 * INR (S n) / x * (x / 2) ^ S n) with (INR (S n) * (x/2)^n)
    by (rewrite /pow -/pow ; field ; apply Hx).
  replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2)^2) +
    (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2)^2))
    with ((x / 2) ^ n * ((x / 2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2)^2) +
      PSeries (Bessel1_seq n) ((x / 2)^2)))
    by (rewrite /pow ; field).
  rewrite (Rmult_comm (INR _)) Rmult_assoc.
  apply f_equal.
  rewrite -PSeries_incr_1.
  rewrite -PSeries_scal.
  rewrite -PSeries_plus.
  apply PSeries_ext => k.
Focus 2. (* ex_pseries (PS_incr_1 (Bessel1_seq (S (S n))) (S (S n))) (x / 2) *)
  apply ex_pseries_incr_1, ex_Bessel1.
Focus 2. (* ex_pseries (PS_incr_n (Bessel1_seq n) n) (x / 2) *)
  apply ex_Bessel1.
(* egalité *)
  rewrite /PS_plus /PS_scal /PS_incr_1.
  case: k => [ | k].
  rewrite /Bessel1_seq .
  rewrite /pow -/pow ?plus_0_r /fact -/fact ; simpl plus.
  rewrite ?mult_INR -/fact ?S_INR ?plus_INR.
  field.
  rewrite -?S_INR ; repeat split ; 
    try by [apply not_0_INR, sym_not_eq, O_S | apply INR_fact_neq_0].
  rewrite /Bessel1_seq.
  simpl pow.
  rewrite -?plus_n_Sm ?plus_0_r /plus -/plus /fact -/fact.
  rewrite 3?mult_INR ?S_INR plus_INR ; field.
  rewrite  -plus_INR -?S_INR ; repeat split ;
  try by [apply INR_fact_neq_0 | apply not_0_INR, sym_not_eq, O_S].
Qed.
Lemma Bessel1_equality_2 (n : nat) (x : R) : x <> 0
  -> Bessel1 (n+1)%nat x = INR n * Bessel1 n x / x - Derive (Bessel1 n) x.
Proof.
  move => Hx.
(* Supprimer les dérivées *)
  rewrite /Bessel1 Derive_mult.
  Focus 2.
    by apply ex_derive_pow, (ex_derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))),
    ex_derive_scal, ex_derive_id.
  Focus 2.
    apply ex_derive_comp.
    apply ex_derive_PSeries ; by rewrite CV_Bessel1.
    by apply ex_derive_pow, (ex_derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))),
    ex_derive_scal, ex_derive_id.
  rewrite Derive_pow.
  Focus 2.
    by apply (ex_derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))),
    ex_derive_scal, ex_derive_id.
  rewrite -(Derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))) Derive_scal Derive_id.
  rewrite Derive_comp.
  Focus 2.
    apply ex_derive_PSeries ; by rewrite CV_Bessel1.
  Focus 2.
    by apply ex_derive_pow, (ex_derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))),
    ex_derive_scal, ex_derive_id.
  rewrite Derive_PSeries.
  Focus 2.
    by rewrite CV_Bessel1.
  rewrite Derive_pow.
  Focus 2.
    by apply (ex_derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))),
    ex_derive_scal, ex_derive_id.
  rewrite -(Derive_ext (fun x => /2 * x) _ _ (Rmult_comm (/2))) Derive_scal Derive_id.
(* Supprimer les PSeries *)
  case: n => [ | n].
(* * cas n = 0 *)
  simpl ; field_simplify => // ; rewrite -/(pow _ 2).
  replace (x * PSeries (Bessel1_seq 1) ((x / 2) ^ 2) / 2)
    with ((x/2) * PSeries (Bessel1_seq 1) ((x / 2) ^ 2))
    by (field => //).
  replace (- x ^ 2 * PSeries (PS_derive (Bessel1_seq 0)) ((x / 2) ^ 2) / (2 * x))
    with ((x/2) * ((-1) * PSeries (PS_derive (Bessel1_seq 0)) ((x / 2) ^ 2)))
    by (rewrite /pow ; field => //).
  apply f_equal.
  rewrite -PSeries_scal.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal /PS_derive plus_0_l.
  replace (1+k)%nat with (S k) by ring.
  rewrite /fact -/fact mult_INR /pow -/pow.
  field ; split.
  exact: INR_fact_neq_0.
  by apply not_0_INR, not_eq_sym, O_S.
(* * cas S n *)
  replace (S n + 1)%nat with (S(S n)) by ring.
  simpl ; field_simplify => // ; rewrite -/(pow _ 2).
  replace (x ^ 2 * (x / 2) ^ n * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) / 4)
    with ((x / 2) ^ n * ( (x/2)^2 *  PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2)))
    by (field => //).
  replace (-4 * x ^ 2 * (x / 2) ^ n * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2) / 16)
    with ((x / 2) ^ n * ( (x/2)^2 * ((-1)* PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2))))
    by (field => //).
  repeat apply f_equal.
  rewrite -PSeries_scal.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal /PS_derive -?plus_n_Sm ?plus_Sn_m.
  rewrite /pow -/pow /fact -/fact ?mult_INR ?S_INR plus_INR.
  field.
  rewrite -plus_INR -?S_INR.
  repeat split ;
  try by [exact: INR_fact_neq_0 | apply not_0_INR, not_eq_sym, O_S].
Qed.
Print Assumptions Bessel1_equality_2.

(* Fonctions de Bessel du premier ordre (cf: wikipédia)
  - résoudre égalités avec dérivées *)

(*
(** * Power series for equivalent computation *)

Record PSeries_equiv := mk_pse {ind : Z ; seq : nat -> R}.
Definition PSE_fun (A : PSeries_equiv) (x : R) : R :=
  (seq A 0) * Zpow x (ind A) * (1 + PSeries (seq A) 1 x).

(** ** PSeries_equiv is a field *)

Definition PSE_zero := mk_pse 0 (fun _ => 0).
Lemma PSE_zero_carac (A : PSeries_equiv) :
  seq A 0 = 0 -> forall x, PSE_fun A x = 0.
Proof.
  move => H x.
  by rewrite /PSE_fun H !Rmult_0_l.
Qed.

Definition PSE_one := mk_pse 0 (fun n => match n with | 0 => 1 | _ => 0 end).
Lemma PSE_one_carac :
  forall x, PSE_fun PSE_one x = 1.
Proof.
  move => x.
  rewrite /PSE_fun.
  replace (PSeries (seq PSE_one) 1 x) with 0.
  simpl ; ring.
  apply sym_equal.
  rewrite -(Lim_seq_const 0).
  apply Lim_seq_ext => n.
  rewrite /sum_f.
  case: n => [ | n].
  simpl ; ring.
  rewrite -pred_of_minus ; simpl pred.
  elim: n => [ | n IH] /=.
  ring.
  rewrite IH ; ring.
Qed.

Definition PSE_opp (A : PSeries_equiv) := mk_pse (ind A) (fun n => - seq A n).
Lemma PSE_opp_carac (A : PSeries_equiv) :
  forall x, PSeries *)