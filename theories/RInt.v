Require Import Reals Div2 ConstructiveEpsilon.
Require Import ssreflect ssrbool eqtype seq.
Require Import Markov Rcomplements Floor Total_sup Sup_seq Lim_seq Derive SF_seq.


(** * Build sequences *)

(** ** sequence ly : partition of [a,b] *)

Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1%nat
    | S n => (2 * pow2 n)%nat
  end.

Lemma pow2_INR (n : nat) : INR (pow2 n) = 2^n.
Proof.
  elim: n => //= n IH ;
  rewrite ?plus_INR ?IH /= ; field.
Qed.

Lemma pow2_pos (n : nat) : (0 < pow2 n)%nat.
Proof.
  apply INR_lt ; rewrite pow2_INR ; intuition.
Qed.

Definition RInt_part (a b : R) (n : nat) : seq R := 
  mkseq (fun i => a + (INR i) * (b - a) / (INR n + 1)) (S (S n)).

Lemma RInt_part_bound (a b : R) (n : nat) : 
  RInt_part a b n = rev (RInt_part b a n).
Proof.
  apply (@eq_from_nth R 0) ; rewrite ?size_rev ?size_mkseq => // ;
  move => i Hi ; apply SSR_leq in Hi.
  rewrite nth_rev ?SSR_leq ?SSR_minus ?size_mkseq => //.
  rewrite ?nth_mkseq ?SSR_leq => //.
  rewrite minus_INR ?S_INR => // ; field.
  apply Rgt_not_eq, INRp1_pos.
  apply INR_le ; rewrite ?S_INR minus_INR ?S_INR => //.
  apply Rminus_le_0 ; ring_simplify.
  apply pos_INR.
Qed.

Lemma RInt_part_sort (a b : R) (n : nat) : a <= b -> sorted Rle (RInt_part a b n).
Proof.
  move => Hab ; apply sorted_nth => i Hi x0 ; 
  rewrite ?size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ;
  [ |apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
  apply Rminus_le_0 ; field_simplify ; 
  [| apply Rgt_not_eq ; intuition] ; rewrite -?Rdiv_1 ;
  apply Rdiv_le_0_compat ; intuition.
  rewrite Rplus_comm ; by apply (proj1 (Rminus_le_0 _ _)).
Qed.

Lemma RInt_part_nat (a b : R) (n : nat) (x : R) : (a <= x <= b) -> 
  {i : nat |
  nth 0 (RInt_part a b n) i <= x < nth 0 (RInt_part a b n) (S i) /\
  (S (S i) < size (RInt_part a b n))%nat} +
  {nth 0 (RInt_part a b n) (n) <= x <=
   nth 0 (RInt_part a b n) (S n)}.
Proof.
  move: (sorted_dec (RInt_part a b n) 0 x) => Hdec Hx.
  have Hs : sorted Rle (RInt_part a b n) ;
    [ apply RInt_part_sort, Rle_trans with (r2 := x) ; intuition 
    | move: (Hdec Hs) => {Hdec Hs} Hdec].
  have Hx' : (head 0 (RInt_part a b n) <= x <= last 0 (RInt_part a b n)).
    rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= /Rdiv.
    ring_simplify (a + 0 * (b - a) * / (INR n + 1)).
    field_simplify (a + (INR n + 1) * (b - a) * / (INR n + 1)).
    by rewrite -Rdiv_1.
    apply Rgt_not_eq, INRp1_pos.
  case: (Hdec Hx') => {Hdec Hx'} [[i Hi]|Hi].
  left ; by exists i.
  right ; rewrite size_mkseq /= in Hi ; intuition.
  by rewrite -minus_n_O in H1.
Qed.

(** ** sequences lx *)

(** *** Values *)

Definition SF_val_ly (f : R -> R) (a b : R) (n : nat) : seq R :=
  behead (pairmap (fun x y => f ((x+y)/2)) 0 (RInt_part a b n)).
Definition SF_val_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (fun x y => f ((x+y)/2)) (RInt_part a b n) 0.
Definition SF_val_fun (f : R -> R) (a b : R) (n : nat) (x : R) : R :=
  SF_fun_f2 (fun x y => f ((x+y)/2)) (RInt_part a b n) (0,0) x.

Lemma SF_val_ly_bound (f : R -> R) (a b : R) (n : nat) :
  SF_val_ly f a b n = rev (SF_val_ly f b a n).
Proof.
  rewrite /SF_val_ly (RInt_part_bound b a).
  case: (RInt_part a b n) => [| h s] // ; elim: s h => [| h0 s IH] h //=.
  rewrite ?rev_cons.
  replace (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rcons (rev s) h0) h))
    with (rcons (pairmap (fun x y : R => f ((x + y) / 2)) 0 (rcons (rev s) h0)) (f ((h0+h)/2))).
  rewrite behead_rcons.
  rewrite rev_rcons Rplus_comm -rev_cons -IH //.
  rewrite size_pairmap size_rcons ; apply lt_O_Sn.
  move: (0) h h0 {IH} ; apply rcons_ind with (s := s) => {s} [| s h1 IH] x0 h h0 //.
  rewrite ?rev_rcons /= IH //.
Qed.

Lemma ad_SF_val_fun (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (SF_val_fun f a b n) a b 
      (seq2Rlist (RInt_part a b n)) (seq2Rlist (SF_val_ly f a b n)))
  /\ (~(a <= b) -> adapted_couple (SF_val_fun f b a n) a b 
      (seq2Rlist (RInt_part b a n)) (seq2Rlist (SF_val_ly f b a n))).
Proof.
  wlog : a b / (a <= b) => Hw.
    split ; case: (Rle_dec a b) => // Hab _.
    by apply Hw.
    apply StepFun_P2 ; apply Hw ; by apply Rlt_le, Rnot_le_lt.
  split ; case: (Rle_dec a b) => // {Hw} Hab _.
  
  have : (a = head 0 (SF_lx (SF_val_seq f a b n))) ; 
  [rewrite SF_lx_f2 /= ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  pattern b at 3 ; replace b with (last 0 (SF_lx (SF_val_seq f a b n))).
  replace (RInt_part a b n) 
    with (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) by intuition ;
  rewrite -(SF_lx_f2 (fun x y => f ((x+y)/2))).
  rewrite /SF_val_ly -SF_ly_f2.
  apply (ad_SF_compat (SF_val_seq f a b n)).
  by apply SF_sorted_f2, RInt_part_sort.
  rewrite SF_lx_f2 ;
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) 
    with (RInt_part a b n) by auto.
    rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ;
    field ; apply Rgt_not_eq, INRp1_pos.
Qed.

Definition sf_SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  case : (Rle_dec a b) => Hab.
  exists (SF_val_fun f a b n) ;
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
  exists (SF_val_fun f b a n) ;
  exists (seq2Rlist (RInt_part b a n)) ;
  exists (seq2Rlist (SF_val_ly f b a n)) ; by apply ad_SF_val_fun.
Defined.
Lemma SF_val_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (sf_SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /sf_SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_val_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (sf_SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (SF_val_ly f a b n)
    | right _ => seq2Rlist (SF_val_ly f b a n)
  end.
Proof.
  rewrite /sf_SF_val_fun ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_val_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_val_fun f a b n x = 
    match (RInt_part_nat a b n x Hx) with
      | inleft H => f (a + (INR (projT1 H) + /2) * (b-a) / (INR n + 1))
      | inright _ => f (a + (INR n + /2) * (b-a) / (INR n + 1))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  case: RInt_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] /=.
(* i < 2^n - 1 *)
  rewrite /SF_val_fun /SF_fun_f2.
  replace (a + (INR i + /2) * (b - a) / (INR n+1)) 
    with ((nth 0 (RInt_part a b n) i + nth 0 (RInt_part a b n) (S i)) / 2) ;
    [ | rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ; 
    [field ; apply Rgt_not_eq | apply SSR_leq | apply SSR_leq ] ; intuition].
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = 2^n - 1 *)
  replace (a + (INR n + /2) * (b - a) / (INR n + 1)) 
    with ((nth 0 (RInt_part a b n) (n) + nth 0 (RInt_part a b n) (S n)) / 2) ;
    [ | rewrite ?nth_mkseq ?minus_INR ?S_INR /= ; 
    [field ; apply Rgt_not_eq | 
    apply SSR_leq | apply SSR_leq ] ; intuition].
  suff : (1 < size (RInt_part a b n))%nat.
  move: x Hx ; have: (n = size (RInt_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | ].
    move => {2 4 8 10}->.
  rewrite /SF_val_fun /SF_fun_f2.
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) => {a b Hab n} [| h s Hs x Hx /= Hi] .
  intros _ x Hx Hi.
  by apply lt_n_O in Hi.
  case: s h Hs Hi x Hx => [| h0 s] h Hs /= Hi.
  by apply lt_irrefl in Hi.
  elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -minus_n_O in IH.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx ).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
  rewrite size_mkseq ; by apply lt_n_S, lt_O_Sn.
Qed.

Definition RInt_val (f : R -> R) (a b : R) (n : nat) :=
  ((b-a)/(INR n+1)) * foldr Rplus 0 (SF_val_ly f a b n).

Lemma RInt_val_swap (f : R -> R) (a b : R) (n : nat) :
  RInt_val f a b n = - RInt_val f b a n.
Proof.
  rewrite /RInt_val.
  replace (foldr Rplus 0 (SF_val_ly f b a n))
    with (foldr Rplus 0 (SF_val_ly f a b n)).
  field ; apply Rgt_not_eq ; by intuition.
  rewrite (SF_val_ly_bound _ b a).
  rewrite -(Rplus_0_l (foldr Rplus 0 (SF_val_ly f a b n))).
  elim: (SF_val_ly f a b n) {1 3}(0) => /= [ | x1 s IH] x0.
  ring.
  rewrite rev_cons foldr_rcons -Rplus_assoc (Rplus_comm x0 x1).
  exact: IH.
Qed.

Lemma RInt_val_correct (f : R -> R) (a b : R) (n : nat) :
  RInt_val f a b n = RiemannInt_SF (sf_SF_val_fun f a b n).
Proof.
have H : (forall a b i, (S i < size (RInt_part a b n))%nat -> 
  nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/(INR n + 1)).
  move => {a b} a b i Hi ; rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR.
  field ; apply Rgt_not_eq ; intuition.
  apply SSR_leq ; intuition.
  apply SSR_leq ; intuition.
rewrite /RInt_val /RiemannInt_SF SF_val_subdiv SF_val_subdiv_val ;
case: Rle_dec => Hab.
(* a <= b *)
  rewrite /SF_val_ly ; case: (RInt_part a b n) (H a b) => [| h s] /=.
  move => _ ; field ; apply Rgt_not_eq ; intuition.
  elim: s h => [|h0 s IH] h Hs /=.
  field ; apply Rgt_not_eq ; intuition.
  rewrite Rmult_plus_distr_l (IH) ; move: (Hs O (lt_n_S _ _ (lt_O_Sn _))) => /= Hs'.
  rewrite Hs' ; field ; apply Rgt_not_eq ; intuition.
  move => i Hi ; apply (Hs (S i)), lt_n_S, Hi.
(* ~ a <= b *)
  rewrite (SF_val_ly_bound f a b n) /SF_val_ly.
  case: (RInt_part b a n) (H b a) => [| h s] /=.
  move => _ ; field ; apply Rgt_not_eq ; intuition.
  rewrite -Rminus_0_l -{4}(Rmult_0_l ((b-a)/(INR n + 1))) ;
  elim: s {3 4}(0) h => [|h0 s IH] x0 h Hs /=.
  field ; apply Rgt_not_eq ; intuition.
  rewrite rev_cons foldr_rcons (IH) ; move: (Hs O (lt_n_S _ _ (lt_O_Sn _))) => /= Hs'.
  rewrite Hs' ; field ; apply Rgt_not_eq ; intuition.
  move => i Hi ; apply (Hs (S i)), lt_n_S, Hi.
Qed.

(** *** Local sup and inf *)

Lemma ex_Im_fct (f : R -> R) (a b : R) : a <> b ->
  exists x, (fun y => exists x, y = f x /\ Rmin a b < x < Rmax a b) x.
Proof.
  wlog : a b /(a < b) => [Hw Hab | Hab _].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => Hab'.
    by apply Hw.
    by [].
    rewrite Rmin_comm Rmax_comm ;
    apply sym_not_eq in Hab ;
    by apply Hw.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  exists (f ((a+b)/2)) ; exists ((a+b)/2) ; split.
  by [].
  pattern b at 3 ; replace b with ((b + b)/2) by field ;
  pattern a at 1 ; replace a with ((a + a)/2) by field.
  split ; apply Rmult_lt_compat_r ; by intuition.
Qed.

Definition Sup_fct (f : R -> R) (a b : R) : Rbar :=
  match Req_EM_T a b with
    | right Hab => Lub_Rbar_ne _ (ex_Im_fct f a b Hab)
    | left _ => Finite 0
  end.
Definition Inf_fct (f : R -> R) (a b : R) : Rbar :=
  match Req_EM_T a b with
    | right Hab => Glb_Rbar_ne _ (ex_Im_fct f a b Hab)
    | left _ => Finite 0
  end.

Lemma Sup_fct_bound (f : R -> R) (a b : R) :
  Sup_fct f a b = Sup_fct f b a.
Proof.
  rewrite /Sup_fct /= ; 
  case: Req_EM_T => Hab ; 
  case: Req_EM_T => Hba.
  by [].
  by apply sym_equal in Hab.
  by apply sym_equal in Hba.
  apply Lub_Rbar_ne_eqset => x ; 
  by rewrite Rmin_comm Rmax_comm.
Qed.
Lemma Inf_fct_bound (f : R -> R) (a b : R) :
  Inf_fct f a b = Inf_fct f b a.
Proof.
  rewrite /Inf_fct /= ; 
  case: Req_EM_T => Hab ; 
  case: Req_EM_T => Hba.
  by [].
  by apply sym_equal in Hab.
  by apply sym_equal in Hba.
  apply Glb_Rbar_ne_eqset => x ; 
  by rewrite Rmin_comm Rmax_comm.
Qed.

Lemma Sup_fct_le (f : R -> R) (a b : R) (x : R) : 
  (Rmin a b < x < Rmax a b) ->
    Rbar_le (Finite (f x)) (Sup_fct f a b).
Proof.
  move => Hx ; rewrite /Sup_fct.
  case: Req_EM_T => Hab.
  move: (Rlt_trans _ _ _ (proj1 Hx) (proj2 Hx)) => {Hx} ; 
  rewrite /Rmin /Rmax ; 
  case: Rle_dec (Req_le _ _ Hab) => //= _ _ Hx.
  contradict Hx ; by apply Rle_not_lt, Req_le.
  rewrite /Lub_Rbar_ne ;
  case: ex_lub_Rbar_ne => l lub ; 
  apply lub ; exists x ; split ; by [].
Qed.
Lemma Inf_fct_le (f : R -> R) (a b : R) (x : R) : (Rmin a b < x < Rmax a b) ->
  Rbar_le (Inf_fct f a b) (Finite (f x)).
Proof.
  move => Hx ; rewrite /Inf_fct.
  case: Req_EM_T => Hab.
  move: (Rlt_trans _ _ _ (proj1 Hx) (proj2 Hx)) => {Hx} ; 
  rewrite /Rmin /Rmax ; 
  case: Rle_dec (Req_le _ _ Hab) => //= _ _ Hx.
  contradict Hx ; by apply Rle_not_lt, Req_le.
  rewrite /Glb_Rbar_ne ;
  case: ex_glb_Rbar_ne => l lub ; 
  apply lub ; exists x ; split ; by [].
Qed.

Lemma Sup_fct_maj (f : R -> R) (a b : R) (M : R) : 
  (forall x, Rmin a b < x < Rmax a b -> f x <= M) ->
  is_finite (Sup_fct f a b).
Proof.
  rewrite /Sup_fct ; case: Req_EM_T => Hab Hf.
  by [].
  rewrite /Lub_Rbar_ne ; 
  case: ex_lub_Rbar_ne ; case => [l | | ] [lub ub] /=.
  by [].
  case: (ub (Finite M)) => //.
  move => _ [x [-> Hx]].
  by apply Rbar_finite_le, Hf.
  case: (lub (f((a+b)/2))) => //.
  exists ((a + b) / 2) ; split.
  by [].
  move => {Hf lub ub} ;
  wlog : a b Hab /(a < b) => [ Hw | {Hab} Hab ].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => Hab'.
    by apply Hw.
    by [].
    rewrite Rmin_comm Rmax_comm Rplus_comm ;
    apply sym_not_eq in Hab ;
    by apply Hw.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  pattern b at 3 ; replace b with ((b + b)/2) by field ;
  pattern a at 1 ; replace a with ((a + a)/2) by field.
  split ; apply Rmult_lt_compat_r ; by intuition.
Qed.
Lemma Inf_fct_min (f : R -> R) (a b : R) (m : R) : 
  (forall x, Rmin a b < x < Rmax a b -> m <= f x) ->
  is_finite (Inf_fct f a b).
Proof.
  rewrite /Inf_fct ; case: Req_EM_T => Hab Hf.
  by [].
  rewrite /Glb_Rbar_ne ; 
  case: ex_glb_Rbar_ne ; case => [l | | ] [lub ub] /=.
  by [].
  case: (lub (f((a+b)/2))) => //.
  exists ((a + b) / 2) ; split.
  by [].
  move => {Hf lub ub} ;
  wlog : a b Hab /(a < b) => [ Hw | {Hab} Hab ].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => Hab'.
    by apply Hw.
    by [].
    rewrite Rmin_comm Rmax_comm Rplus_comm ;
    apply sym_not_eq in Hab ;
    by apply Hw.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  pattern b at 3 ; replace b with ((b + b)/2) by field ;
  pattern a at 1 ; replace a with ((a + a)/2) by field.
  split ; apply Rmult_lt_compat_r ; by intuition.
  case: (ub (Finite m)) => //.
  move => _ [x [-> Hx]].
  by apply Rbar_finite_le, Hf.
Qed.

(** *** SF_sup and SF_inf *)

Definition SF_sup_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Sup_fct f) (RInt_part a b n) 0.
Lemma SF_sup_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_sup_seq f a b n) = RInt_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_sup_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_sup_seq f a b n) = behead (pairmap (Sup_fct f) 0 (RInt_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Definition SF_inf_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Inf_fct f) (RInt_part a b n) 0.
Lemma SF_inf_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_inf_seq f a b n) = RInt_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_inf_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_inf_seq f a b n) = behead (pairmap (Inf_fct f) 0 (RInt_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_sup_seq f a b n) = SF_sup_seq f b a n.
Proof.
  rewrite /SF_sup_seq RInt_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Sup_fct_bound.
Qed.
Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) : 
  SF_rev (SF_inf_seq f a b n) = SF_inf_seq f b a n.
Proof.
  rewrite /SF_inf_seq RInt_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Inf_fct_bound.
Qed.


Definition SF_sup_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_sup_seq f a b n) (Finite 0) x
    | right _ => SF_fun (SF_sup_seq f b a n) (Finite 0) x
  end.
Definition SF_inf_fun (f : R -> R) (a b : R) (n : nat) (x : R) : Rbar :=
  match (Rle_dec a b) with
    | left _ => SF_fun (SF_inf_seq f a b n) (Finite 0) x
    | right _ => SF_fun (SF_inf_seq f b a n) (Finite 0) x
  end.

Lemma SF_sup_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) :
  SF_sup_fun f a b n x = SF_sup_fun f b a n x.
Proof.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
  by rewrite (Rle_antisym _ _ Hab Hba).
  by contradict Hba ; apply Rlt_le, Rnot_le_lt.
Qed.
Lemma SF_inf_fun_bound (f : R -> R) (a b : R) (n : nat) (x : R) :
  SF_inf_fun f a b n x = SF_inf_fun f b a n x.
Proof.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => Hab ; case : (Rle_dec b a) => Hba //.
  by rewrite (Rle_antisym _ _ Hab Hba).
  by contradict Hba ; apply Rlt_le, Rnot_le_lt.
Qed.

Lemma SF_sup_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_sup_fun f a b n x = 
    match (RInt_part_nat a b n x Hx) with
      | inleft H => Sup_fct f (nth 0 (RInt_part a b n) (projT1 H)) 
          (nth 0 (RInt_part a b n) (S (projT1 H)))
      | inright _ => Sup_fct f (nth 0 (RInt_part a b n) (n)) 
          (nth 0 (RInt_part a b n) (S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_sup_fun /SF_sup_seq ; case: Rle_dec => // _.
  case: RInt_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl projT1.
(* i < n *)
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = n *)
  move: x Hx.
  suff : (1 < size (RInt_part a b n))%nat.
  have: (n = size (RInt_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | move => {3 5 8 10}->].
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_irrefl in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
  rewrite size_mkseq ; by apply lt_n_S, lt_O_Sn.
Qed.

Lemma SF_inf_fun_rw (f : R -> R) (a b : R) (n : nat) (x : R) (Hx : a <= x <= b) :
  SF_inf_fun f a b n x = 
    match (RInt_part_nat a b n x Hx) with
      | inleft H => Inf_fct f (nth 0 (RInt_part a b n) (projT1 H)) 
          (nth 0 (RInt_part a b n) (S (projT1 H)))
      | inright _ => Inf_fct f (nth 0 (RInt_part a b n) (n)) 
          (nth 0 (RInt_part a b n) (S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_inf_fun /SF_inf_seq ; case: Rle_dec => // _.
  case: RInt_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl projT1.
(* i < n *)
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  case: (s) Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [| h0 s] Hs /= i Hi.
    by apply lt_n_O in Hi.
  elim: (s) h h0 Hs (i) (lt_S_n _ _ Hi) => {s i Hi} [|h1 s IH] h h0 Hs /= i Hi x Hx.
    by apply lt_n_O in Hi.
  case: i Hx Hi => [|i]/= Hx Hi.
  rewrite /SF_fun /=.
  case: Rlt_dec => [Hx0 | _ ].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rlt_dec => // Hx0 ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) i (lt_S_n _ _ Hi) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
(* i = n *)
  move: x Hx.
  suff : (1 < size (RInt_part a b n))%nat.
  have: (n = size (RInt_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | move => {3 5 8 10}->].
  case: (RInt_part a b n) (RInt_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
  by apply lt_n_O in Hi.
  case: s h Hs Hi => [| h0 s] h Hs /= Hi.
  by apply lt_irrefl in Hi.
  rewrite -minus_n_O ; elim: s h h0 Hs {Hi} => [| h1 s IH] h h0 Hs /= x Hx.
  rewrite /SF_fun /= ; case: Rlt_dec => [Hx0 | _].
  contradict Hx0 ; apply Rle_not_lt, Hx.
  case: Rle_dec => [| Hx0] // ; contradict Hx0 ; apply Hx.
  rewrite -(IH h0 h1 (proj2 Hs) x Hx).
  rewrite /SF_fun /= ; case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (1 := proj1 Hs), 
  Rle_trans with (2 := proj1 Hx), (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ;
  simpl; intuition.
  case: Rlt_dec => [ Hx0 | _ ] //.
  contradict Hx0 ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hx), 
  (sorted_head [:: h0, h1 & s] _ (proj2 Hs)) ; simpl; intuition.
  rewrite size_mkseq ; by apply lt_n_S, lt_O_Sn.
Qed.

(** ** SF_sup_real is a StepFun *)

Lemma ad_SF_sup_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b 
      (seq2Rlist (RInt_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b 
      (seq2Rlist (RInt_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part b a n))))).
Proof.
  wlog : a b / (a <= b) => [Hw|Hab].
  case: (Rle_dec a b) => // Hab ; split => // _.
    by apply (Hw a b).
    apply Rnot_le_lt, Rlt_le in Hab ;
    case : (Hw b a Hab) => {Hw} Hw _ ;
    move: (Hw Hab) => {Hw} Hw ; 
    rewrite /adapted_couple in Hw |-* ; rewrite Rmin_comm Rmax_comm ; 
    intuition => x Hx ; rewrite SF_sup_fun_bound ; by apply H4.
  split ; case: (Rle_dec a b)=> // _ _.
  rewrite /SF_sup_fun ; case: (Rle_dec a b) => // _.
  have Hs : (SF_sorted Rle (SF_map real (SF_sup_seq f a b n))).
    rewrite /SF_sorted SF_map_lx SF_lx_f2.
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) 
    with (RInt_part a b n) by intuition.
    by apply RInt_part_sort.
  have: a = head 0 (RInt_part a b n) ; 
  [ simpl ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have: b = last 0 (RInt_part a b n) ; 
  [ rewrite -nth_last size_mkseq nth_mkseq ?S_INR//= ; 
  field ; apply Rgt_not_eq ; intuition | move => {3}->].
  replace (behead
    (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (RInt_part a b n)))
    with (SF_ly (SF_map real (SF_sup_seq f a b n))).
  replace (RInt_part a b n) 
  with (SF_lx (SF_map real (SF_sup_seq f a b n))).
  move: (ad_SF_compat (SF_map real (SF_sup_seq f a b n)) Hs) ;
  rewrite /adapted_couple => Had ; intuition.
  move: (H4 i H3) => {H4 H3} H3 x H4.
  move: (H3 x H4) => {H3 H4} <-.
  by rewrite -(SF_fun_map real).
  by rewrite SF_map_lx SF_lx_f2.
  rewrite SF_map_ly SF_ly_f2.
  by rewrite -behead_map map_pairmap.
Qed.

Definition SF_sup_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => real (SF_sup_fun f a b n x)) ;
  case : (Rle_dec a b) => Hab.
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part a b n)))) ;
  by apply ad_SF_sup_r.
  exists (seq2Rlist ((RInt_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part b a n)))) ;
  by apply ad_SF_sup_r.
Defined.
Lemma SF_sup_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_sup_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_sup_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_sup_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (RInt_part b a n))))
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_sup_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_sup_r f a b n x = SF_sup_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_sup_fun_bound.
Qed.

(** ** SF_inf_real is a StepFun *)

Lemma ad_SF_inf_r (f : R -> R) (a b : R) (n : nat) :
  ((a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b 
      (seq2Rlist (RInt_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b 
      (seq2Rlist (RInt_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part b a n))))).
Proof.
  wlog : a b / (a <= b) => [Hw|Hab].
  case: (Rle_dec a b) => // Hab ; split => // _.
    by apply (Hw a b).
    apply Rnot_le_lt, Rlt_le in Hab ;
    case : (Hw b a Hab) => {Hw} Hw _ ;
    move: (Hw Hab) => {Hw} Hw ; 
    rewrite /adapted_couple in Hw |-* ; rewrite Rmin_comm Rmax_comm ; 
    intuition => x Hx ; rewrite SF_inf_fun_bound ; by apply H4.
  split ; case: (Rle_dec a b)=> // _ _.
  rewrite /SF_inf_fun ; case: (Rle_dec a b) => // _.
  have Hs : (SF_sorted Rle (SF_map real (SF_inf_seq f a b n))).
    rewrite /SF_sorted SF_map_lx SF_lx_f2.
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) 
    with (RInt_part a b n) by intuition.
    by apply RInt_part_sort.
  have: a = head 0 (RInt_part a b n) ; 
  [ simpl ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have: b = last 0 (RInt_part a b n) ; 
  [ rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ; 
  field ; apply Rgt_not_eq ; intuition | move => {3}->].
  replace (behead
    (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (RInt_part a b n)))
    with (SF_ly (SF_map real (SF_inf_seq f a b n))).
  replace (RInt_part a b n) 
  with (SF_lx (SF_map real (SF_inf_seq f a b n))).
  move: (ad_SF_compat (SF_map real (SF_inf_seq f a b n)) Hs) ;
  rewrite /adapted_couple => Had ; intuition.
  move: (H4 i H3) => {H4 H3} H3 x H4.
  move: (H3 x H4) => {H3 H4} <-.
  by rewrite -(SF_fun_map real).
  by rewrite SF_map_lx SF_lx_f2.
  rewrite SF_map_ly SF_ly_f2.
  by rewrite -behead_map map_pairmap.
Qed.

Definition SF_inf_r (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  exists (fun x => real (SF_inf_fun f a b n x)) ;
  case : (Rle_dec a b) => Hab.
  exists (seq2Rlist (RInt_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part a b n)))) ;
  by apply ad_SF_inf_r.
  exists (seq2Rlist ((RInt_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part b a n)))) ;
  by apply ad_SF_inf_r.
Defined.
Lemma SF_inf_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (RInt_part a b n)
    | right _ => seq2Rlist (RInt_part b a n)
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_inf_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (RInt_part b a n))))
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_inf_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_inf_r f a b n x = SF_inf_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_inf_fun_bound.
Qed.

(** * A new Riemann_integrable in Prop *)

Definition pointed_subdiv (ptd : @SF_seq R) :=
  forall i : nat, (i < SF_size ptd)%nat -> 
    nth 0 (SF_lx ptd) i <= nth 0 (SF_ly ptd) i <= nth 0 (SF_lx ptd) (S i).

Lemma ptd_cons h s : pointed_subdiv (SF_cons h s) -> pointed_subdiv s.
Proof.
  move => H i Hi ; apply (H (S i)) ; rewrite SF_size_cons ; intuition.
Qed.
Lemma ptd_sort ptd : 
  pointed_subdiv ptd -> SF_sorted Rle ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ;
  [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] => 
  Hptd ; try split => //=.
  apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
  apply Rle_trans with y0 ; apply (Hptd O) ; rewrite SF_size_cons ; apply lt_O_Sn.
  apply IH, (ptd_cons (x0,y0)) => //.
Qed.
Lemma ptd_sort' ptd : 
  pointed_subdiv ptd -> sorted Rle (SF_ly ptd).
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd] ;
  [ | apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd] IH] => 
  Hptd ; try split.
  apply Rle_trans with x1 ; [apply (Hptd O) | apply (Hptd 1%nat)] ; 
  rewrite ?SF_size_cons ; repeat apply lt_n_S ; apply lt_O_Sn.
  apply IH, (ptd_cons (x0,y0)) => //.
Qed.

Definition signe (x : R) :=
  match Rle_dec 0 x with
    | left H => match Rle_lt_or_eq_dec _ _ H with
        | left _ => 1
        | right _ => 0
      end
    | right _ => -1
  end.
Lemma Ropp_signe (x : R) : signe (-x) = - signe x.
Proof.
  rewrite /signe ; 
  case: Rle_dec => H ; case: Rle_dec => H0.
  have: ~ (0 < - x).
    apply Rle_not_lt, Ropp_le_cancel ; intuition.
  have: ~ (0 < x).
    apply Rle_not_lt, Ropp_le_cancel ; rewrite Ropp_0 ; intuition.
  case: Rle_lt_or_eq_dec => // ; case: Rle_lt_or_eq_dec => // ; intuition.
  have: ~ (0 = - x).
    contradict H0 ; apply Ropp_le_cancel ; rewrite -H0 ; intuition.
  case: Rle_lt_or_eq_dec => // ; intuition.
  have: ~ (0 = x).
    contradict H ; rewrite -H ; intuition.
  case: Rle_lt_or_eq_dec => // ; intuition.
  contradict H0 ; apply Ropp_le_cancel, Rlt_le, Rnot_le_lt ; intuition.
Qed.

Definition seq_step (s : seq R) := 
  foldr Rmax 0 (pairmap (fun x y => Rabs (Rminus y x)) (head 0 s) (behead s)).

Definition Riemann_sum (f : R -> R) (ptd : SF_seq) :=
  RInt_seq (SF_map f ptd) Rplus Rmult 0.

Lemma Riemann_sum_cons (f : R -> R) h0 ptd :
  Riemann_sum f (SF_cons h0 ptd) =
    f (snd h0) * (SF_h ptd - fst h0) + Riemann_sum f ptd.
Proof.
  rewrite /Riemann_sum /RInt_seq /=.
  case: h0 => x0 y0 ;
  apply SF_cons_dec with (s := ptd) => {ptd} [ x1 | [x1 y1] ptd ] //=.
Qed. 

Lemma pointed_pty2 f ptd : SF_sorted Rle ptd ->
  SF_h ptd = last (SF_h ptd) (SF_lx ptd) -> Riemann_sum f ptd = 0.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd IH] //= Hs Hhl.
  rewrite Riemann_sum_cons IH /= => {IH}.
  replace x0 with (SF_h ptd) ; try ring.
  apply Rle_antisym.
  rewrite Hhl => {Hhl} /=.
  apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
  replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
  apply Hs.
  apply SF_cons_ind with (s := ptd) => {ptd Hs} [x1 | [x1 y1] ptd IH] //=.
  apply lt_O_Sn.
  apply Hs.
  apply Hs.
  apply Rle_antisym.
  apply (sorted_last (SF_h ptd :: @map (R*R) R (@fst R R) (SF_t ptd)) O) with (x0 := 0).
  replace ((SF_h ptd) :: map _ _) with (SF_lx ptd).
  apply Hs.
  apply SF_cons_ind with (s := ptd) => {ptd Hs Hhl} [x1 | [x1 y1] ptd IH] //=.
  apply lt_O_Sn.
  move: Hhl ; rewrite -?(last_map (@fst R R)) /= => <- ; apply Hs.
Qed.

Lemma Riemann_sum_plus (f g : R -> R) ptd :
  Riemann_sum (fun x => f x + g x) ptd =
    Riemann_sum f ptd + Riemann_sum g ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
  rewrite /Riemann_sum /RInt_seq /= ; ring.
  rewrite !Riemann_sum_cons /= ; rewrite IH ; ring.
Qed.
Lemma Riemann_sum_minus (f g : R -> R) ptd :
  Riemann_sum (fun x => f x - g x) ptd =
    Riemann_sum f ptd - Riemann_sum g ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH].
  rewrite /Riemann_sum /RInt_seq /= ; ring.
  rewrite !Riemann_sum_cons /= ; rewrite IH ; ring.
Qed.

Lemma Riemann_sum_abs (f g : R -> R) ptd : pointed_subdiv ptd ->
  (forall t, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t) <= g t)
  -> Rabs (Riemann_sum f ptd) <= Riemann_sum g ptd.
Proof.
  apply SF_cons_ind with (s := ptd) => {ptd} /= [x0 | [x0 y0] s IH] /= Hs H.
  rewrite Rabs_R0 ; exact: Rle_refl.
  rewrite !Riemann_sum_cons /=.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_compat.
  rewrite Rabs_mult (Rabs_right (_-_)).
  apply Rmult_le_compat_r.
  apply -> Rminus_le_0 ; apply Rle_trans with y0 ;
  apply (Hs O) ; rewrite SF_size_cons ; exact: lt_O_Sn.
  apply H ; split.
  apply (Hs O) ; rewrite SF_size_cons ; exact: lt_O_Sn.
  apply Rle_trans with (SF_h s).
  apply (Hs O) ; rewrite SF_size_cons ; exact: lt_O_Sn.
  apply (sorted_last (SF_lx s) O) with (x0 := 0).
  by apply (ptd_sort _ Hs).
  exact: lt_O_Sn.
  apply Rle_ge ; apply -> Rminus_le_0 ; apply Rle_trans with y0 ;
  apply (Hs O) ; rewrite SF_size_cons ; exact: lt_O_Sn.
  apply IH.
  by apply ptd_cons with (h := (x0,y0)).
  move => t Ht ; apply H ; split.
  by apply Rle_trans with (2 := proj1 Ht), (ptd_sort _ Hs).
  by apply Ht.
Qed.

Definition SF_last {T : Type} x0 (s : SF_seq) : (R*T) :=
  last (SF_h s,x0) (SF_t s).
Definition SF_belast {T : Type} (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (belast (SF_t s) : seq (R*T)).


Definition SF_head {T : Type} (x0 : T) (s : @SF_seq T) := (SF_h s, head x0 (SF_ly s)).
Definition SF_behead {T : Type} (s : @SF_seq T) :=
  mkSF_seq (head (SF_h s) (unzip1 (SF_t s))) (behead (SF_t s)).

Definition is_RInt (f : R -> R) (a b If : R) :=
  forall eps : posreal, exists alpha : posreal, 
    forall (ptd : SF_seq) (H : pointed_subdiv ptd), 
    seq_step (SF_lx ptd) < alpha -> 
    SF_h ptd = Rmin a b -> last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
    Rabs (If - signe (b-a) * Riemann_sum f ptd) < eps.
Definition ex_RInt (f : R -> R) (a b : R) :=
  exists If : R, is_RInt f a b If.

Lemma is_RInt_swap :
  forall f a b If,
  is_RInt f b a (-If) -> is_RInt f a b If.
Proof.
  move => f a b If HIf eps.
  case: (HIf eps) => {HIf} alpha HIf.
  exists alpha => ptd Hptd Hstep Ha Hb.
  rewrite -(Ropp_minus_distr' b a) Ropp_signe.
  replace (If - - signe (a - b) * Riemann_sum f ptd) with
    (-(- If - signe (a - b) * Riemann_sum f ptd)) by ring.
  rewrite Rabs_Ropp.
  apply HIf.
  exact: Hptd.
  exact: Hstep.
  by rewrite Rmin_comm.
  by rewrite Rmax_comm.
Qed.
Lemma ex_RInt_swap :
  forall f a b,
  ex_RInt f a b -> ex_RInt f b a.
Proof.
  intros f a b.
  case => If HIf.
  exists (-If).
  apply is_RInt_swap.
  by rewrite Ropp_involutive.
Qed.

Lemma ex_RInt_bounded f a b :
  ex_RInt f a b -> exists m, exists M : R, forall t : R,
    Rmin a b <= t <= Rmax a b -> m <= f t <= M.
Proof.
  wlog: a b / (a < b) => [ Hw | Hab ] Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite /Rmin /Rmax ; case: Rle_dec (Req_le _ _ Hab) => // _ _ ;
    rewrite -Hab.
    exists (f a) ; exists (f a) => t Ht ; replace t with a.
    split ; exact: Rle_refl.
    apply Rle_antisym ; by case: Ht.
    rewrite Rmin_comm Rmax_comm ; 
    apply ex_RInt_swap in Hex ; by apply Hw.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  
  case: Hex => If Hex.
  case: (Hex (mkposreal _ Rlt_0_1)) => {Hex} alpha Hex.
  have Hn : 0 <= ((b-a)/alpha).
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Rlt_le, Hab.
    by apply alpha.
  set n := (nfloor _ Hn).
  set ptd := fun (g : R -> R -> R) =>
    SF_seq_f2 g (RInt_part a b n) 0.
  
  have : forall g, pointed_subdiv (ptd g) ->
    Rabs (If - Riemann_sum f (ptd g)) < 1.
    move => g Hg ; replace (If - Riemann_sum f (ptd g))
      with (If - signe (b - a) * Riemann_sum f (ptd g)).
  apply Hex.
  exact: Hg.
  apply Rle_lt_trans with ((b-a)/(INR n + 1)).
  clearbody n ; rewrite SF_lx_f2.
  replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n))
    with (RInt_part a b n) by auto.
  suff : forall i, (S i < size (RInt_part a b n))%nat ->
    nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/(INR n + 1).
  elim: (RInt_part a b n) => [ /= _ | x0].
  apply Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  case => /= [ | x1 s] IH Hnth.
  apply Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  replace (seq_step _)
    with (Rmax (Rabs (x1 - x0)) (seq_step (x1 :: s))) by auto.
  apply Rmax_case_strong => _.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))) Rabs_right.
  exact: Rle_refl.
  apply Rle_ge, Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  apply IH => i Hi ; exact: (Hnth (S i) (lt_n_S _ _ Hi)).
  rewrite size_mkseq => i Hi ;
  rewrite ?nth_mkseq ?SSR_leq ?S_INR.
  field ; apply Rgt_not_eq ; by intuition.
  exact: lt_le_weak.
  exact: Hi.
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm ; apply Rlt_div_l.
  by apply alpha.
  rewrite /n /nfloor ; case: nfloor_ex => /= n' Hn'.
  by apply Hn'.
  clearbody n ; rewrite /Rmin ;
  case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ; field ; apply Rgt_not_eq ;
  by intuition.
  clearbody n ; rewrite /Rmax -nth_last SF_lx_f2.
  replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n))
    with (RInt_part a b n) by auto.
  rewrite size_mkseq nth_mkseq ?S_INR // ;
  case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ; field ; apply Rgt_not_eq ;
  by intuition.
  apply f_equal.
  rewrite /signe.
  case: Rle_dec (Rlt_le _ _ (Rgt_minus _ _ Hab)) => // Hab' _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rgt_minus _ _ Hab)) => // {Hab'} _ _.
  ring.
  move => {Hex} Hex.
  
  have : exists m, exists M, forall g : R -> R -> R,
    pointed_subdiv (ptd g) -> m <= Riemann_sum f (ptd g) <= M.
    exists (If - 1) ; exists (If + 1) ; move => g Hg.
    apply Rabs_le_between', Rlt_le.
    rewrite -Ropp_minus_distr' Rabs_Ropp.
    by apply Hex.
  clearbody n ; move => {Hex} Hex.
  have: forall i, (S i < size (RInt_part a b n))%nat -> 
    exists m, exists M, forall t, 
      nth 0 (RInt_part a b n) i <= t <= nth 0 (RInt_part a b n) (S i)
      -> m <= f t <= M.
    move => i ; revert ptd Hex.
    have : sorted Rlt (RInt_part a b n).
      apply sorted_nth => j Hj x0.
      rewrite size_mkseq /= in Hj ;
      rewrite ?nth_mkseq ?S_INR ?SSR_leq /=.
      apply Rminus_gt ; field_simplify.
      rewrite Rplus_comm -Rdiv_1 ; apply Rdiv_lt_0_compat.
      exact: Rgt_minus.
      by intuition.
      apply Rgt_not_eq ; by intuition.
      by intuition.
      by intuition.
    elim: (RInt_part a b n) i => [ /= i _ _ Hi | x0].
    by apply lt_n_O in Hi.
    case => [ /= _ i _ _ Hi | x1 s IH].
    by apply lt_S_n, lt_n_O in Hi.
    case => [ | i] Hlt /= Hex Hi.
    have : exists m, exists M, forall t g, x0 <= t <= x1 -> 
      pointed_subdiv (SF_seq_f2 g [:: x1 & s] 0) ->
      m <= f t * (x1 - x0) + Riemann_sum f (SF_seq_f2 g [:: x1 & s] 0) <= M.
    case: (Hex) => m [M Hex'].
    exists m ; exists M ;
    move => t g Ht Hg.
    set g0 := fun x y =>
      match Req_EM_T x x0 with
        | left _ =>  t
        | right _ => g x y
      end.
    replace (_+_)
      with (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s] 0)).
    apply: Hex'.
    case => [ | j] Hj ; rewrite SF_size_f2 /= in Hj ;
    rewrite SF_lx_f2 SF_ly_f2 /=.
    rewrite /g0.
    by case: Req_EM_T (refl_equal x0).
    rewrite (nth_pairmap 0).
    rewrite /g0.
    suff : (nth 0 (x1 :: s) j) <> x0.
    case: Req_EM_T => // _ _.
    move: (Hg j).
    rewrite SF_size_f2 ; rewrite SF_lx_f2 SF_ly_f2 /= (nth_pairmap 0).
    move => Hg' ; by apply Hg', lt_S_n.
    apply SSR_leq ; by intuition.
    apply Rgt_not_eq.
    apply lt_S_n in Hj.
    elim: j Hj => {IH} [ | j IH] Hj.
    by apply Hlt.
    apply Rlt_trans with (nth 0 (x1 :: s) j).
    apply IH ; by intuition.
    apply (sorted_nth Rlt).
    by apply Hlt.
    by intuition.
    apply SSR_leq ; by intuition.
    rewrite SF_cons_f2 /=.
    rewrite Riemann_sum_cons /=.
    apply f_equal2.
    apply (f_equal (fun x => Rmult x _)).
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (refl_equal x0).
    case: s Hlt {IH Hex Hex' Hi Hg} => [ | x2 s] Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x1) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    apply (f_equal (fun x => x * _)) , f_equal.
    rewrite /g0.
    by case: Req_EM_T (Rgt_not_eq _ _ (proj1 Hlt)).
    elim: s x2 Hlt => [ | x3 s IH] x2 Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x2) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    apply (f_equal (fun x => x * _)) , f_equal.
    rewrite /g0.
    by case: Req_EM_T (Rgt_not_eq _ _ (Rlt_trans _ _ _ (proj1 Hlt) (proj1 (proj2 Hlt)))).
    apply IH.
    split.
    by apply Hlt.
    split.
    apply Rlt_trans with x2 ; by apply Hlt.
    by apply Hlt.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
  move => {Hex} Hex.
  case: (Hex) => m [M Hex'].
  exists ((m - Riemann_sum f (SF_seq_f2 (fun x y => x) (x1 :: s) 0)) / (x1 - x0)).
  exists ((M - Riemann_sum f (SF_seq_f2 (fun x y => x) (x1 :: s) 0)) / (x1 - x0)).
  move => t Ht.
  have Hg : pointed_subdiv (SF_seq_f2 (fun x y : R => x) (x1 :: s) 0).
    move => j ; rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 /= => Hj.
    rewrite (nth_pairmap 0).
    split.
    apply Rle_refl.
    apply Rlt_le, (sorted_nth Rlt (x1::s)).
    by apply Hlt.
    by [].
    apply SSR_leq ; by intuition.
  move: (Hex' _ _ Ht Hg) ; split.
  apply Rle_div_l.
  by apply Rgt_minus, Hlt.
  by apply Rle_minus_l, Hex'0.
  apply Rle_div_r.
  by apply Rgt_minus, Hlt.
  apply Rle_minus_l ; rewrite /Rminus Ropp_involutive ; by apply Hex'0.
  apply IH.
  by apply Hlt.
  case: Hex => m [M Hex].
  exists ((m - f x0 * (x1 - x0))) ; exists ((M - f x0 * (x1 - x0))) => g Hg.
  set g0 := fun x y =>
      match Req_EM_T x x0 with
        | left _ => x0
        | right _ => g x y
      end.
  have Hg0 : pointed_subdiv (SF_seq_f2 g0 (x0::x1 :: s) 0).
    move => j ; rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 => Hj.
    rewrite nth_behead (nth_pairmap 0) /=.
    case: j Hj => /= [ | j ] Hj.
    rewrite /g0.
    case: Req_EM_T (refl_equal x0) => // _ _.
    split.
    exact: Rle_refl.
    by apply Rlt_le, Hlt.
    suff : (nth 0 (x1 :: s) j) <> x0.
    rewrite /g0 ; case: Req_EM_T => // _ _.
    move: (Hg j).
    rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 /= => {Hg} Hg.
    move: (Hg (lt_S_n _ _ Hj)) ; rewrite (nth_pairmap 0).
    by [].
    apply SSR_leq ; by intuition.
    apply Rgt_not_eq.
    elim: j Hj => {IH} /= [ | j IH] Hj.
    by apply Hlt.
    apply Rlt_trans with (nth 0 (x1 :: s) j).
    apply IH ; by intuition.
    apply (sorted_nth Rlt (x1::s)).
    by apply Hlt.
    by intuition.
    apply SSR_leq ; by intuition.
    replace (Riemann_sum _ _) 
      with (Riemann_sum f (SF_seq_f2 g0 (x0::x1::s) 0) - f x0 * (x1-x0)).
    split ; apply Rplus_le_compat_r, (Hex _ Hg0).
    rewrite SF_cons_f2 /=.
    rewrite Riemann_sum_cons /=.
    replace (Riemann_sum f (SF_seq_f2 g0 (x1 :: s) x0)) with
      (Riemann_sum f (SF_seq_f2 g (x1 :: s) 0)).
    rewrite /g0 ; case: Req_EM_T (refl_equal x0) => // _ _ ; ring.
    elim: s x1 Hlt {IH Hex Hg Hg0 Hi} => [ | x2 s IH] x1 Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x1) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    rewrite /g0 ; by case: Req_EM_T (Rgt_not_eq _ _ (proj1 Hlt)).
    apply IH.
    split.
    apply Rlt_trans with x1 ; by apply Hlt.
    by apply Hlt.
    exact: lt_O_Sn.
    exact: lt_O_Sn.
    exact: lt_O_Sn.
    exact: lt_S_n.
  move => {Hex} Hex.
  replace b with (last 0 (RInt_part a b n)).
  pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
  elim: (RInt_part a b n) Hex => /= [ | x0].
  exists (f 0) ; exists (f 0) => t Ht ;
  rewrite (Rle_antisym t 0) ; by intuition.
  case => /= [ | x1 s] IH Hex.
  exists (f x0) ; exists (f x0) => t Ht ;
  rewrite (Rle_antisym t x0) ; by intuition.
  case: (Hex _ (lt_n_S _ _ (lt_O_Sn _))) => /= m0 [M0 H0].
  case: IH => [ | m [M IH]].
  move => i Hi ; case: (Hex _ (lt_n_S _ _ Hi)) => {Hex} /= m [M Hex].
  exists m ; by exists M.
  exists (Rmin m0 m) ; exists (Rmax M0 M) => t Ht ;
  case: (Rlt_le_dec t x1) => Ht0.
  split ; 
  [apply Rle_trans with (1 := Rmin_l _ _) 
  | apply Rle_trans with (2 := RmaxLess1 _ _)] ;
  apply H0 ; by intuition.
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by intuition.
  simpl ; field ; apply Rgt_not_eq ; by intuition.
  rewrite -nth_last size_mkseq nth_mkseq ?S_INR /=.
  field ; apply Rgt_not_eq, INRp1_pos.
  by [].
Qed.

Lemma ex_RInt_ub f a b :
  ex_RInt f a b -> exists M : R, forall t : R,
    Rmin a b <= t <= Rmax a b -> f t <= M.
Proof.
  move => Hex ; case: (ex_RInt_bounded _ _ _ Hex) => m [M H].
  exists M => t Ht ; by apply H.
Qed.
Lemma ex_RInt_lb f a b :
  ex_RInt f a b -> exists m : R, forall t : R,
    Rmin a b <= t <= Rmax a b -> m <= f t.
Proof.
  move => Hex ; case: (ex_RInt_bounded _ _ _ Hex) => m [M H].
  exists m => t Ht ; by apply H.
Qed.

Lemma ex_RInt_correct_aux_1 (f : R -> R) (a b : R) :
  forall pr : Riemann_integrable f a b,
    is_RInt f a b (RiemannInt pr).
Proof.
  wlog: a b / (a < b) => [Hw | Hab].
    case: (total_order_T a b) => [[Hab | <-] | Hab] pr eps.
    by apply Hw.
    exists (mkposreal 1 Rlt_0_1) => ptd H _ (*_*) H0 H1.
    replace (Riemann_sum _ _) with 0.
    rewrite RiemannInt_P9 Rmult_0_r Rminus_0_r Rabs_R0 ; apply eps.
    apply sym_equal, pointed_pty2 ; [by apply ptd_sort | rewrite {1}H0].
    move: H1 (Rle_refl a) ; rewrite /Rmin /Rmax ; 
    case: Rle_dec => //= _ <- _.
    move: (RiemannInt_P1 pr) => pr'.
    case: (Hw _ _ Hab pr' eps) ; rewrite Rmin_comm Rmax_comm => {Hw} alpha Hw ; 
    exists alpha ; intros.
    rewrite (RiemannInt_P8 pr pr').
    rewrite -(Ropp_minus_distr' b a) Ropp_signe 
    {1}/Rminus -(Ropp_plus_distr _ (_*_)) Rabs_Ropp
    Ropp_mult_distr_l_reverse.
    apply Hw => //.
  rewrite /is_RInt.
  suff : forall (pr : Riemann_integrable f a b) (eps : posreal),
    exists alpha : posreal,
      forall ptd : SF_seq,
      pointed_subdiv ptd ->
      seq_step (SF_lx ptd) < alpha ->
      SF_h ptd = Rmin a b ->
      last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
      Rabs (RiemannInt pr - signe (b - a) * Riemann_sum f ptd) <= eps.
    move => Hle pr eps ; set eps2 := pos_div_2 eps.
    case: (Hle pr eps2) => {Hle} alpha Hle.
    exists alpha => ptd Hptd Hstep Ha Hb.
    apply Rle_lt_trans with (1 := Hle ptd Hptd Hstep Ha Hb).
    replace (eps : R) with (eps/1) by field.
    simpl ; apply (Rmult_lt_compat_l eps).
    apply eps.
    apply Rinv_lt_contravar.
    rewrite Rmult_1_l ; exact: Rlt_R0_R2.
    rewrite -{1}(Rplus_0_l 1).
    apply Rplus_lt_compat_r.
    apply Rlt_0_1.

  rewrite /Rmin /Rmax ; move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  rewrite /signe ;
  move: (Rlt_Rminus _ _ Hab) => Hab' ; 
  move: (Rlt_le _ _ Hab') (Rlt_not_eq _ _ Hab') ;
  case: Rle_dec => // H _ ; case: Rle_lt_or_eq_dec => // _ _ {H Hab'}.

  suff H : forall (phi : StepFun a b) (eps : posreal),
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (unzip1 (SF_t ptd)) = b ->
    Rabs (RiemannInt_SF phi - 1 * Riemann_sum phi ptd) <= eps.
    
  rewrite /RiemannInt /= => pr eps ; case: RiemannInt_exists => If HIf.
  set eps2 := pos_div_2 eps.
  set eps4 := pos_div_2 eps2.
(* RInt (f-phi) < eps/4 *)
  case: (HIf _ (cond_pos eps4)) => {HIf} N HIf.
  case: (nfloor_ex (/eps4) (Rlt_le _ _ (Rinv_0_lt_compat _ (cond_pos eps4)))) => n Hn.
  move: (HIf (N+n)%nat (le_plus_l _ _)) => {HIf}.
  rewrite /phi_sequence /R_dist ; case: pr => phi [psi pr] ; 
  simpl RiemannInt_SF => HIf.
(* RInt psi < eps/4*)
  have H0 : Rabs (RiemannInt_SF psi) < eps4.
    apply Rlt_le_trans with (1 := proj2 pr).
    rewrite -(Rinv_involutive eps4 (Rgt_not_eq _ _ (cond_pos eps4))) /=.
    apply Rle_Rinv.
    apply Rinv_0_lt_compat, eps4.
    intuition.
    apply Rlt_le, Rlt_le_trans with (1 := proj2 Hn).
    apply Rplus_le_compat_r.
    apply le_INR, le_plus_r.
(* Rsum phi < eps/4 and Rsum psi < eps/4 *)
  case: (H phi eps4) => alpha0 Hphi.
  case: (H psi eps4) => {H} alpha1 Hpsi.
  have Halpha : (0 < Rmin alpha0 alpha1).
    apply Rmin_case_strong => _ ; [apply alpha0 | apply alpha1].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd H Hstep (*Hsort*) Ha Hb.
  rewrite (double_var eps) 1?(double_var (eps/2)) ?Rplus_assoc.
  replace (_-_) with (-(RiemannInt_SF phi - If) 
    + (RiemannInt_SF phi - Riemann_sum f ptd)) ; 
    [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  rewrite Rabs_Ropp ; apply Rlt_le, HIf.
  clear HIf ;
  replace (_-_) with ((RiemannInt_SF phi - 1* Riemann_sum phi ptd) 
    + (Riemann_sum phi ptd - Riemann_sum f ptd)) ;
    [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Hphi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_l.
  rewrite -Ropp_minus_distr' Rabs_Ropp -Riemann_sum_minus.
  have H1 : (forall t : R, 
    SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t - phi t) <= psi t).
    move => t Ht.
    apply pr ; move: (Rlt_le _ _ Hab) ; rewrite /Rmin /Rmax ; 
    case: Rle_dec => // _ _ ; rewrite -Ha -Hb //.
  apply Rle_trans with (1 := Riemann_sum_abs _ _ _ H H1).
  apply Rle_trans with (1 := Rle_abs _).
  replace (Riemann_sum _ _) with 
    (-(RiemannInt_SF psi - 1* Riemann_sum psi ptd) 
    + RiemannInt_SF psi) ; [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  rewrite Rabs_Ropp ; apply Hpsi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_r.
  apply Rlt_le, H0.
  
(* forall StepFun *)

  case => phi [lx [ly Hphi]] eps /= ;
  rewrite /RiemannInt_SF /subdivision /subdivision_val ;
  move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  move: (Rlt_le _ _ Hab) Hphi => {Hab} ;
  elim: lx ly eps a b => [ | lx0 lx IH] ly eps a b Hab.
(* lx = [::] *)
  case ; intuition ; by [].
  case: lx IH ly => [ | lx1 lx] IH ;
  case => [ {IH} | ly0 ly] Had ; try by (case: Had ; intuition ; by []).
(* lx = [:: lx0] *)
  exists eps => ptd Hptd Hstep (*Hsort*) Ha Hb /=.
  rewrite pointed_pty2.
  rewrite Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
  by apply ptd_sort.
  rewrite /SF_lx /= Hb Ha ; case: Had => {Ha Hb} _ [Ha [Hb _]] ; move: Ha Hb ;
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ <- <- //.
(* lx = [:: lx0, lx1 & lx] *)
  set eps2 := pos_div_2 eps ; set eps4 := pos_div_2 eps2.
(* * alpha1 from IH *)
  case: (IH ly eps4 lx1 b) => {IH}.
  
  replace b with (last 0 (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx)))).
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1%nat)
  with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; apply lt_n_S, lt_O_Sn.
  case: Had => /= _ [_ [Hb _]] ; move: Hb ; rewrite /Rmax ; 
  case: Rle_dec => //= _ ;
  elim: (lx) lx1  => //= h s IH _ ; apply IH.
  apply (StepFun_P7 Hab Had).
  
  move => /= alpha1 IH.
(* * alpha2 from H *)  
  suff H : forall eps : posreal,
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (SF_lx ptd) = lx1 ->
    Rabs (ly0 * (lx1 - lx0) - Riemann_sum phi ptd) <= eps.

  case: (H eps4) => {H} alpha2 H.
(* * alpha3 from (fmax - fmin) *)
  set fmin1 := foldr Rmin 0 (ly0::Rlist2seq ly).
  set fmin2 := foldr Rmin 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmin := Rmin fmin1 fmin2.
  set fmax1 := foldr Rmax 0 (ly0::Rlist2seq ly).
  set fmax2 := foldr Rmax 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmax := Rmax fmax1 fmax2.
  
  have Ha3 : (0 < eps4 / (Rmax (fmax - fmin) 1)).
    apply Rdiv_lt_0_compat ; [ apply eps4 | ].
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha3 := mkposreal _ Ha3.  
(* * alpha = Rmin (Rmin alpha1 alpha2) alpha3 *)  
  have Halpha : (0 < Rmin (Rmin alpha1 alpha2) alpha3).
    apply Rmin_case_strong => _ ; [ | apply alpha3].
    apply Rmin_case_strong => _ ; [ apply alpha1 | apply alpha2].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd Hptd Hstep Ha Hb.

  suff Hff : forall x, a <= x <= b -> fmin <= phi x <= fmax.
  suff Hab1 : forall i, (i <= SF_size ptd)%nat -> a <= nth 0 (SF_lx ptd) i <= b.
  suff Hab0 : a <= lx1 <= b.

  rewrite /Riemann_sum (SF_Chasles (phi (SF_h ptd)) _ lx1) /=.
  replace (_-_) with 
    ((ly0 * (lx1 - lx0) - 1* RInt_seq (SF_cut_down (phi (SF_h ptd)) (SF_map phi ptd) lx1) Rplus Rmult 0)
    + (Int_SF ly (RList.cons lx1 lx) - 1* RInt_seq (SF_cut_up (phi (SF_h ptd)) (SF_map phi ptd) lx1) Rplus Rmult 0))
    ; [ | by ring_simplify].
  
  rewrite (double_var eps) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* partie [lx0;lx1] *)

  replace (SF_cut_down _ _ _: @SF_seq R) with 
  (SF_map phi (SF_cut_down (SF_h ptd) ptd lx1) : @SF_seq R).

  set ptd_r_last := (SF_last a (SF_cut_down a ptd lx1)).
  set ptd_r_belast := (SF_belast (SF_cut_down a ptd lx1)).
  set ptd_r := SF_rcons ptd_r_belast (lx1, (fst (SF_last a ptd_r_belast) + lx1)/2).

  move: (H ptd_r) => {H} H.

  replace (_-_) with ((ly0 * (lx1 - lx0) - Riemann_sum phi ptd_r) +
    (phi ((fst (SF_last 0 ptd_r_belast) + lx1)/2) - phi (snd ptd_r_last)) 
      * (lx1 - fst (SF_last 0 ptd_r_belast))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* * appliquer H *)
  apply: H => {IH}.
  
  Focus 3.
    rewrite -Ha /ptd_r /ptd_r_belast.
    move: (proj1 Hab0) ; rewrite -Ha.
    apply SF_cons_dec with (s := ptd) => [x0 | [x0 y0] s] //= Hx0 ;
    by case: Rle_dec.
  Focus 3.
    revert ptd_r_belast ptd_r ; move: (proj1 Hab0) ;
    rewrite -Ha ;
    apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] 
    //= Hx0 ; case: Rle_dec => //= _.
    by rewrite unzip1_rcons /= last_rcons.

(* ** ptd_r est une subdivision pointée *)

  revert ptd_r_belast ptd_r Hptd ;
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH ] Hptd.
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.

  case => /= [ _ | i Hi] .  
  case: Rle_dec => //= Hx0.
  pattern lx1 at 3 ; replace lx1 with ((lx1 + lx1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  split ; apply Req_le ; by field.
  contradict Hi ; apply le_not_lt.
  case: Rle_dec => //= Hx0 ; rewrite /SF_size /= ;
  apply le_n_S, le_O_n.
  
  move: (IH (ptd_cons _ _ Hptd)) => {IH} IH.
  case => [ _ | i Hi].
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: Rle_dec => //= Hx0.
  case: Rle_dec => //= Hx1.
  move: Hptd Hx1 ; apply SF_cons_dec with (s := s) 
    => {s IH} /= [x1 | [x1 y1] s] //= Hptd Hx1.
  by apply (Hptd O (lt_O_Sn _)).
  case: Rle_dec => //= Hx2.
  by apply (Hptd O (lt_O_Sn _)).
  by apply (Hptd O (lt_O_Sn _)).
  pattern lx1 at 3 ; replace lx1 with ((lx1 + lx1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  split ; apply Req_le ; by field.
  move: Hi (IH i) => {IH}.
  rewrite ?SF_size_rcons -?SF_size_lx ?SF_lx_rcons ?SF_ly_rcons.
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -?unzip1_fst.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: (Rle_dec x0 lx1) => //= Hx0.
  case: (Rle_dec (SF_h s) lx1) => //= Hx1.
  rewrite size_belast size_belast'.
  move: Hx1 ;
  apply SF_cons_dec with (s := s) => {s Hptd} /= [ x1 | [x1 y1] s] //= Hx1.
  move => Hi IH ; apply IH ; by apply lt_S_n.
  case: Rle_dec => //= Hx2.
  
  move => Hi IH ; apply IH ; by apply lt_S_n.
  
  move => Hi IH ; apply IH ; by apply lt_S_n.
  
  move => Hi ; by apply lt_S_n, lt_n_O in Hi.
  move => Hi ; by apply lt_S_n, lt_n_O in Hi.
  
  apply Rlt_le_trans with (2 := Rmin_r alpha1 alpha2) ;
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep) => {Hstep}.
  move: Hab0 ; rewrite -Ha -Hb ;
  revert ptd_r_belast ptd_r => {Hab1} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //= Hab0.
  rewrite /SF_lx /SF_rcons /SF_belast /SF_last /SF_cut_down /=.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) /seq_step /=.
  rewrite Rminus_eq0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  move: Hab0 (fun Hx1 => IH (conj Hx1 (proj2 Hab0))) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hab0 IH.
  rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: Rle_dec => //= Hx1.
  rewrite /seq_step /=.
  apply Rle_max_compat_l.
  rewrite (Rle_antisym _ _ Hx1 (proj2 Hab0)) Rminus_eq0 Rabs_R0.
  apply Rmax_case_strong ; by intuition.
  rewrite /seq_step /=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  apply Rplus_le_compat_r.
  by apply Rlt_le, Rnot_le_lt.
  apply Rle_ge ; rewrite -Rminus_le_0 ; by apply Hab0.
  move: IH ; rewrite /SF_cut_down /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: (Rle_dec x1 lx1) => //= Hx1 IH.
  move: (IH Hx1) => {IH}.
  case: (Rle_dec (SF_h s) lx1) => //= Hx2.
  rewrite /seq_step -?(last_map (@fst R R)) /= => IH ; 
  apply Rle_max_compat_l, IH.
  rewrite /seq_step /= ; apply Rle_max_compat_l.
  rewrite /seq_step /= ; apply Rmax_le_compat.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
  apply Rle_ge ; rewrite -Rminus_le_0 ; apply Hab0.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  apply SF_cons_ind with (s := s) => {s IH Hab0} /= [x2 | [x2 y2] s IH] //=.
  exact: Rle_refl.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  exact: IH.
(* ** transition 1 *) 
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (fst (SF_last 0 ptd_r_belast) + lx1) / 2 <= b.
  suff H1 : a <= snd ptd_r_last <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_r_last Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  replace a with ((a+a)/2) by field.
  replace b with ((b+b)/2) by field.
  split ; apply Rmult_le_compat_r, Rplus_le_compat ; try by intuition.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  
  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite Rabs_right.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_r_belast ptd_r Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /SF_cut_down /SF_belast /SF_last /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) ; apply Req_le ; by ring.
  move => Hptd Hab0 ; 
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  rewrite /SF_cut_down /SF_belast /SF_last /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx3.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
  
  apply Rle_ge ; rewrite -Rminus_le_0.
  revert ptd_r_belast ptd_r ; rewrite -Ha in Hab0 ; move: (proj1 Hab0) ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down /SF_belast /SF_last /=.
  by case: Rle_dec.
  move: IH ; rewrite /SF_cut_down /SF_belast /SF_last /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= Hx1 IH.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //=.
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] //= Hx2.
  case: (Rle_dec (SF_h s) _) => //=.
  
  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.
  
  clear H IH.
  rewrite Rplus_assoc -Ropp_minus_distr Rmult_1_l.
  apply (f_equal (Rminus (ly0 * (lx1 - lx0)))).
  revert ptd_r_last ptd_r_belast ptd_r ; move: (proj1 Hab0) ; 
  rewrite -Ha => {Hab0} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down /=.
  case: (Rle_dec x0 lx1) => //= _.
  rewrite /Riemann_sum /RInt_seq /=.
  by ring.
  case: (Rle_dec (SF_h s) lx1) => //= => Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} [x1 | [x1 y1] s] /= Hx1.
  rewrite /SF_cut_down /= ; 
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _.
  rewrite /Riemann_sum /RInt_seq /= => _.
  ring.
  rewrite /SF_cut_down /= ; 
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _ ;
  case: (Rle_dec (SF_h s) _) => //= Hx2.
  rewrite (SF_map_cons _ (x0,y0) (mkSF_seq x1 ([:: (SF_h s, y1) & seq_cut_down (SF_t s) lx1 y1])))
    RInt_seq_cons /=.
  move => <-.
  rewrite /SF_belast /SF_last /SF_rcons /=.
  rewrite /Riemann_sum.
  rewrite (SF_map_cons _ (x0,y0) (mkSF_seq x1 (rcons _ _))) RInt_seq_cons /=.
  rewrite -!(last_map (@fst R R)) -!unzip1_fst /=.
  ring.
  rewrite /Riemann_sum /RInt_seq /= => _ ; ring.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= _ ; case: Rle_dec => //= _.
  rewrite /Riemann_sum /RInt_seq /= ; ring.
  
  apply SF_cons_ind with (s := ptd) => {IH} /= [x0 | [x0 y0] s IH] /=.
  rewrite /SF_cut_down /= ; by case: Rle_dec.
  move: IH.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] /=.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= _ ; case: Rle_dec => //=.
  rewrite /SF_cut_down /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec x1 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= _.
  rewrite (SF_map_cons _ (x0,y0) (mkSF_seq x1 ((SF_h s, y1) :: seq_cut_down (SF_t s) lx1 y1))) /=.
  by move => -> /=.
(* partie [lx1 ; b] *)
  replace (SF_cut_up _ _ _: @SF_seq R) with 
  (SF_map phi (SF_cut_up (SF_h ptd) ptd lx1) : @SF_seq R).

  set ptd_l_head := (SF_head a (SF_cut_up a ptd lx1)).
  set ptd_l_behead := (SF_behead (SF_cut_up a ptd lx1)).
  set ptd_l := SF_cons (lx1, (lx1 + fst (SF_head a ptd_l_behead))/2) ptd_l_behead.

  move: (IH ptd_l) => {IH} IH.

  replace (_-_) with ((Int_SF ly (RList.cons lx1 lx) - 1 * Riemann_sum phi ptd_l) -
    (phi ((lx1 + fst (SF_head 0 ptd_l_behead))/2) - phi (snd ptd_l_head)) 
      * (lx1 - fst (SF_head 0 ptd_l_behead))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
(* * hypothèse d'induction *)
  apply: IH.
(* ** ptd_l est une subdivision pointée *)
  case.
  move => _ ; move: (proj1 Hab0) ; rewrite -Ha => /= Hx0 ;
  case: Rle_dec => //= _.
  rewrite seq_cut_up_head.
  move: Hx0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  split ; apply Req_le ; field.
  case: Rle_dec => //= Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: Rle_dec => //= Hx2.
  pattern (SF_h s) at 3 ; replace (SF_h s) with ((SF_h s+SF_h s)/2) by field.
  pattern lx1 at 1 ; replace lx1 with ((lx1+lx1)/2) by field.
  apply Rnot_le_lt, Rlt_le in Hx1 ; split ;
  apply Rmult_le_compat_r ; by intuition.
  rewrite /ptd_l SF_lx_cons SF_ly_cons SF_size_cons => i Hi ;
  move: i {Hi} (lt_S_n _ _ Hi).
  revert ptd_l_behead ptd_l Hptd ;
  apply SF_cons_ind with (s := ptd) 
    => /= [x0 | [x0 y0] s IH] /= Hptd.
  rewrite /SF_cut_up /=.
  case: Rle_dec => //=.
  rewrite /SF_size /SF_behead /= => _ i Hi ; by apply lt_n_O in Hi.
  move: (IH (ptd_cons _ _ Hptd)) => {IH}.
  rewrite /SF_cut_up /=.
  case: (Rle_dec x0 _) => //= Hx0.
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  rewrite !seq_cut_up_head.
  move: Hx1 ; apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //= Hx2.
(* * seq_step (SF_lx ptd_l) < alpha1 *)
  apply Rlt_le_trans with (2 := Rmin_l alpha1 alpha2).
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep).
  revert ptd_l_behead ptd_l ; move :(proj1 Hab0) ;
  rewrite -Ha ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] /= s IH] Hx0.
  rewrite /SF_cut_up /= ; case: (Rle_dec x0 _) => //= _.
  rewrite /seq_step /= Rminus_eq0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  rewrite /SF_cut_up /= ; case: (Rle_dec x0 _) => //= _.
  move: IH ; rewrite /SF_cut_up /= ; case: (Rle_dec (SF_h s) _) => //= Hx1 ;
  rewrite ?seq_cut_up_head => IH.
  move: Hx1 (IH Hx1) => {IH} ; 
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx1 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; 
  exact: RmaxLess2.
  move: IH ; case: (Rle_dec (SF_h s) _) => //= Hx2 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; 
  exact: RmaxLess2.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; 
  exact: RmaxLess2.
  clear IH ; rewrite /seq_step/=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_l, Ropp_le_contravar.
  by apply Rle_ge, (Rminus_le_0 lx1 _), Rlt_le, Rnot_le_lt.
  by rewrite /ptd_l /=.
  rewrite -Hb.
  move: (proj1 Hab0) ; rewrite -Ha /=;
  case: (Rle_dec (SF_h ptd) lx1) => //= _ _.
  rewrite seq_cut_up_head.
  move: Hab0 ; rewrite -Ha -Hb ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= [Hx0 Hlx1].
  by apply Rle_antisym.
  move: (fun Hx1 => IH (conj Hx1 Hlx1)) => {IH} ;
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  move => IH ; rewrite -(IH Hx1) => {IH}.
  move: Hx1 Hlx1 ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s ] Hx1 Hlx1.
  by [].
  case: (Rle_dec (SF_h s) _) => /= Hx2 ;
  by [].
(* ** transition 2 *) 
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_Ropp Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (lx1 + fst (SF_head 0 ptd_l_behead)) / 2 <= b.
  suff H1 : a <= snd ptd_l_head <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_l_head Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_up /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_up /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  replace a with ((a+a)/2) by field.
  replace b with ((b+b)/2) by field.
  split ; apply Rmult_le_compat_r, Rplus_le_compat ; try by intuition.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down /= ; case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up /SF_head /= -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite ?seq_cut_up_head.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite !seq_cut_up_head.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  
  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite -Rabs_Ropp Rabs_right ?Ropp_minus_distr'.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_l_behead ptd_l Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  apply Req_le ; by ring.
  move => Hptd Hab0 ; 
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  rewrite !seq_cut_up_head in IH |-*.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar, Hab0.

  apply Rle_ge, (Rminus_le_0 lx1).
  revert ptd_l_behead ptd_l ; rewrite -Ha -Hb in Hab0 ; move: Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  case: Rle_dec => /= _.
  exact: Rle_refl.
  exact: (proj2 Hx0).
  move: (proj1 Hx0) ; case: Rle_dec => //= _ _.
  move: (fun Hx1 => IH (conj Hx1 (proj2 Hx0))) => {IH}.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  rewrite !seq_cut_up_head in IH |-* ; move: (IH Hx1) => {IH}.
  move: Hx0 Hx1 ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx0 Hx1 IH.
  exact: Rle_refl.
  move: IH ; case: (Rle_dec (SF_h s)) => /= Hx2.
  by [].
  by [].
  by apply Rlt_le, Rnot_le_lt, Hx1.
  
  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.
  
  clear H IH.
  rewrite !Rmult_1_l {1 2}/Rminus Rplus_assoc -Ropp_plus_distr.
  apply (f_equal (Rminus _)) => /=.
  rewrite /ptd_l /ptd_l_behead /ptd_l_head /= /SF_cut_up /= ; 
  move: Hab0 ; rewrite -Ha -Hb /= ; 
  case => [Hx0 Hlx1].
  case: (Rle_dec (SF_h ptd)) => //= _.
  rewrite ?seq_cut_up_head /SF_ly /= /Riemann_sum SF_map_cons RInt_seq_cons /=.
  move: Hx0 Hlx1 ; apply SF_cons_ind with (s := ptd) 
    => [x0 | [x0 y0] s /= IH] /= Hx0 Hlx1.
  rewrite /RInt_seq /= ; ring.
  case: (Rle_dec (SF_h s)) => //= Hx1.
  move: (IH Hx1 Hlx1) => /= {IH}.
  move: Hx1 Hlx1 ; apply SF_cons_dec with (s := s) 
    => {s} [x1 | [x1 y1] s /=] /= Hx1 Hlx1 IH.
  rewrite /RInt_seq /= ; ring.
  move: IH ; case: (Rle_dec (SF_h s)) => //= Hx2.
  move => <- ; apply Rminus_diag_uniq ; ring_simplify.
  move: Hx2 Hlx1 y1 ; apply SF_cons_ind with (s := s) 
    => {s} [x2 | [x2 y2] s /= IH] /= Hx2 Hlx1 y1.
  ring.
  case: (Rle_dec (SF_h s)) => //= Hx3.
  by apply IH.
  ring.
  ring_simplify.
  rewrite (SF_map_cons _ (lx1,y0) s) RInt_seq_cons /=.
  rewrite /SF_behead /= ; ring_simplify ; by case: (s).
  
  apply SF_cons_ind with (s := ptd) => {IH} /= [x0 | [x0 y0] s IH] /=.
  rewrite /SF_cut_up /= ; by case: Rle_dec.
  move: IH.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] /=.
  rewrite /SF_cut_up /= ; case: Rle_dec => //= _ ; case: Rle_dec => //=.
  rewrite /SF_cut_up /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec x1 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= _.
  by rewrite ?seq_cut_up_head.
  rewrite -Ha -Hb in Hab0 ; move: Hab0.
  rewrite -(last_map (@fst R R)) -unzip1_fst /=.
  replace (unzip1 (map (fun x : R * R => (fst x, phi (snd x))) (SF_t ptd)))
    with (unzip1 (SF_t ptd)).
  by [].
  elim: (SF_t ptd) => {IH} [ | [x0 y0] s IH] //=.
  by rewrite IH.
  
  replace lx1 with (pos_Rl (RList.cons lx0 (RList.cons lx1 lx)) 1) by reflexivity.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ; 
  case: Rle_dec => // _ <- <-.
  rewrite -(seq2Rlist_bij (RList.cons lx0 _)) !nth_compat size_compat.
  split.
  rewrite nth0.
  apply (sorted_head (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.
  simpl ; rewrite -last_nth.
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1) with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.
  
  rewrite -Ha -Hb /SF_lx /= => i Hi.
  apply le_lt_n_Sm in Hi ; rewrite -SF_size_lx /SF_lx in Hi.
  split.
  exact: (sorted_head (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).
  exact: (sorted_last (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).

  clear H IH.
  move => x Hx ; case: (sorted_dec ([:: lx0, lx1 & Rlist2seq lx]) 0 x).
  apply sorted_compat ; rewrite /= seq2Rlist_bij ; apply Had.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ; 
  case: Rle_dec => // _.
  rewrite -nth0 -nth_last /= => -> Hb'.
  split.
  by apply Hx.
  elim: (lx) (lx1) Hb' => /= [ | h1 s IH] h0 Hb'.
  rewrite Hb' ; by apply Hx.
  by apply IH.
  case => i ; case ; case ; case => {Hx} Hx Hx' Hi.
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (S i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ; 
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  have : (((size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat) < 
    size [:: lx0, lx1 & Rlist2seq lx])%nat.
    by [].
  replace (size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat with 
    (S (size [:: lx0, lx1 & Rlist2seq lx] - 2)) by (simpl ; intuition).
  move: (size [:: lx0, lx1 & Rlist2seq lx] - 2)%nat => i Hi.
  case ; case => {Hx} Hx ; [ case => Hx' | move => _ ].
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ; 
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite Hx'.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] (S i)) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: s IH Hi => /= [ | h1 s] IH Hi.
  by apply lt_S_n, lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; 
  [ apply Rle_trans with (1 := Rmin_r _ _) ; exact: Rmin_l 
  | apply Rle_trans with (2 := RmaxLess2 _ _) ; exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ; 
  [apply Rle_trans with (1 := Rmin_r _ _) 
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.

(* preuve de H *)  
  clear eps eps2 IH eps4 alpha1.
  move: (proj1 (proj2 Had)) => /= ; rewrite /Rmin ; 
    case: Rle_dec => //= _ <-.
  move: (proj1 Had O (lt_O_Sn _)) => /= Hl0l1.
  move: (proj2 (proj2 (proj2 (proj2 Had))) O (lt_O_Sn _)) => /= Hval.
  clear a b Hab Had lx ly.
  rename lx0 into a ; rename lx1 into b ; 
  rename ly0 into c ; rename Hl0l1 into Hab.
  
  set fmin := Rmin (Rmin (phi a) (phi b)) c.
  set fmax := Rmax (Rmax (phi a) (phi b)) c.
  
  move => eps ; set eps2 := pos_div_2 eps.
  have Halpha : 0 < eps2 / (Rmax (fmax - fmin) 1).
    apply Rdiv_lt_0_compat.
    apply eps2.
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd.
  apply SF_cons_ind with (s := ptd) 
    => {ptd} [x0 | [x0 y0] ptd IH] Hptd Hstep Ha Hb ; simpl in Ha, Hb.
  rewrite -Ha -Hb /Riemann_sum /RInt_seq /= ;
  rewrite Rminus_eq0 Rmult_0_r Rminus_0_r Rabs_R0.
  by apply Rlt_le, eps.
  move: (fun Ha => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep) Ha Hb)
    => {IH} IH.
  move: (proj1 (ptd_sort _ Hptd)) ; 
  rewrite Ha in Hptd, Hstep |- * => {x0 Ha} ; 
  case => /= Ha.
  rewrite /Riemann_sum SF_map_cons RInt_seq_cons /= => {IH}.
  replace (_-_) with ((c-phi y0) * (SF_h ptd - a) 
    + (c * (b - SF_h ptd) - RInt_seq (SF_map phi ptd) Rplus Rmult 0)) ;
    [ | by ring_simplify].
  rewrite (double_var eps) ; 
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ; 
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  rewrite -Hb ; 
  apply (sorted_last (SF_lx ptd) 0 (proj2 (ptd_sort _ Hptd)) (lt_O_Sn _)) 
    with (x0 := 0).
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ; 
  rewrite /seq_step /= ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.
  
  move: (ptd_cons _ _ Hptd) 
  (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep : seq_step (SF_lx ptd) < alpha) 
  Ha Hb => {Hptd Hstep y0} Hptd Hstep Ha Hb.
  suff : SF_h ptd <= b.
  case => Hx0.
  move: Hptd Hstep Ha Hb Hx0.
  apply SF_cons_ind with (s := ptd) => {ptd} 
    [x0 | [x0 y0] ptd IH] Hptd Hstep /= Ha Hb Hx0.
  contradict Hb ; apply Rlt_not_eq, Hx0.
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep)
    (Rlt_le_trans _ _ _ Ha (proj1 (ptd_sort _ Hptd))) Hb Hx1) => {IH} IH.
  rewrite SF_map_cons RInt_seq_cons /=.
  have : SF_h ptd <= b.
    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
    apply lt_O_Sn.
  case => Hx1.
  rewrite Hval.
  replace (_-_) with (c * (b - SF_h ptd) - RInt_seq (SF_map phi ptd) Rplus Rmult 0)
  by (ring_simplify ; auto).
  by apply IH.
  split.
  apply Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_lt_trans with (2 := Hx1), (Hptd O (lt_O_Sn _)).
  rewrite Hx1 -/(Riemann_sum phi ptd) pointed_pty2.
  replace (c * (b - x0) - (phi y0 * (b - x0) + 0))
    with ((c - phi y0) * (b - x0)) by ring.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ; 
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply Rlt_le, Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  by apply Req_le.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ; 
  rewrite /seq_step /= -Hx1 ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite -Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.
  apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
  by rewrite /SF_lx /= Hb.
  rewrite Hx0 -/(Riemann_sum phi ptd) pointed_pty2.
  replace (c * (b - b) - 0) with 0 by ring.
  rewrite Rabs_R0 ; apply Rlt_le, eps2.
  apply ptd_sort, Hptd.
  by rewrite /SF_lx /= Hb.
  
    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, Hptd.
    apply lt_O_Sn.
  rewrite Riemann_sum_cons /= -Ha.
  rewrite Rminus_eq0 Rmult_0_r Rplus_0_l.
  by apply IH.
Qed.

Lemma ex_RInt_correct_1 (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> ex_RInt f a b.
Proof.
  move => pr ; exists (RiemannInt pr).
  exact: ex_RInt_correct_aux_1.
Qed.

Lemma ex_RInt_correct_aux_2 (f : R -> R) (a b : R) :
  forall If : R, is_RInt f a b If -> is_lim_seq (RInt_val f a b) If.
Proof.
  wlog: a b /(a < b) => [Hw | Hab] If Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    
    Focus 2.
    suff H : is_lim_seq (RInt_val f b a) (-If).
      move => eps ; case: (H eps) => {H} N H ; exists N => n Hn.
      rewrite RInt_val_swap.
      replace (- RInt_val f b a n - If) with (- (RInt_val f b a n - - If)) by ring.
      rewrite Rabs_Ropp ; by apply H.
    apply Hw.
    exact: Hab.
    
    move => eps ; case: (Hex eps) => {Hex} alpha Hex ; 
    exists alpha => ptd Hptd Hstep Ha Hb.
    rewrite -(Ropp_minus_distr' a b) Ropp_signe.
    replace (- If - - signe (b - a) * Riemann_sum f ptd) with
      (- (If - signe (b - a) * Riemann_sum f ptd)) by ring.
    rewrite Rabs_Ropp ; apply Hex.
    exact: Hptd.
    exact: Hstep.
    by rewrite Rmin_comm.
    by rewrite Rmax_comm.
    
    have H : forall n, RInt_val f a a n = 0.
      move => n ; rewrite /RInt_val ; field ; apply Rgt_not_eq ; by intuition.
    rewrite -Hab in Hex |- * => {Hab b}.
    replace If with 0.
    move => eps ; exists O => n _.
    rewrite H.
    rewrite Rminus_0_r Rabs_R0 ; apply eps.
    suff H0 : forall eps : posreal, Rabs If < eps.
    apply Rle_antisym ; apply le_epsilon => e He ;
    set eps := mkposreal e He ; apply Rlt_le.
    rewrite -(Rminus_eq0 If) ; 
    apply Rplus_lt_compat_l, Rle_lt_trans with (Rabs If).
    exact: Rabs_maj2.
    by apply (H0 eps).
    rewrite Rplus_0_l ;
    apply Rle_lt_trans with (Rabs If).
    exact: Rle_abs.
    by apply (H0 eps).
    move => eps ; move: (Hex eps) => {Hex}.
    rewrite Rminus_eq0 /signe.
    move: (Rle_refl 0) (Rle_not_lt _ _ (Rle_refl 0)).
    case: Rle_dec => // H0 _ ; case: Rle_lt_or_eq_dec => // _ _ {H0}.
    case => alpha Halpha.
    set ptd := @SF_nil R a.
    replace If with (If - 0 * Riemann_sum f ptd) by ring.
    apply Halpha.
    move => i /= Hi.
    by apply lt_n_O in Hi.
    by apply alpha.
    rewrite /Rmin ; by case: Rle_dec (Rle_refl a).
    rewrite /Rmax ; by case: Rle_dec (Rle_refl a).
(* * Preuve dans la cas a < b *)
  move => eps.
  case: (Hex eps) => {Hex} alpha Hex.
(* ** Trouver N *)
  have HN : 0 <= (b-a)/alpha.
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Rlt_le, Hab.
    by apply alpha.
  set N := (nfloor _ HN).
  exists N => n Hn.
  rewrite -Rabs_Ropp.
  set ptd := SF_seq_f2 (fun x y => (x+y)/2) (RInt_part a b n) 0.
(* ** Appliquer Hex *)
  replace (- (RInt_val f a b n - If)) 
    with (If - signe (b - a) * Riemann_sum f ptd).
  apply: Hex.
  move => i.
  rewrite SF_size_f2 size_mkseq => Hi ; simpl in Hi.
  rewrite SF_lx_f2 SF_ly_f2.
  replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n)) with
    (RInt_part a b n) by auto.
  rewrite nth_behead (nth_pairmap 0).
  replace (nth 0 (0 :: RInt_part a b n) (S i)) with
    (nth 0 (RInt_part a b n) i) by auto.
  have : nth 0 (RInt_part a b n) i <= nth 0 (RInt_part a b n) (S i).
    apply (sorted_nth Rle).
    by apply RInt_part_sort, Rlt_le.
    by rewrite size_mkseq.
  move : (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i)) => x y Hxy.
  pattern y at 3 ; replace y with ((y+y)/2) by field.
  pattern x at 1 ; replace x with ((x+x)/2) by field.
  split ; apply Rmult_le_compat_r ; by intuition.
  apply SSR_leq ; rewrite size_mkseq ; by intuition.
  apply Rle_lt_trans with ((b-a)/(INR n + 1)).
  suff : forall i, (S i < size (SF_lx ptd))%nat ->
    nth 0 (SF_lx ptd) (S i) - nth 0 (SF_lx ptd) i = (b-a)/(INR n + 1).
  elim: (SF_lx ptd) => /= [ | x0].
  move => _ ; apply Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  case => /=[ | x1 s] IH Hs.
  apply Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  replace (seq_step _) with (Rmax (Rabs (x1 - x0)) (seq_step (x1::s))) by auto.
  rewrite (Hs _ (lt_n_S _ _ (lt_O_Sn _))) Rabs_right.
  apply Rmax_lub.
  by apply Rle_refl.
  apply IH => i Hi.
  by apply (Hs _ (lt_n_S _ _ Hi)).
  apply Rle_ge, Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  rewrite SF_lx_f2.
  replace (head 0%R (RInt_part a b n) :: behead (RInt_part a b n))
    with (RInt_part a b n) by auto.
  rewrite size_mkseq => i Hi ; rewrite !nth_mkseq ?S_INR.
  field ; apply Rgt_not_eq, INRp1_pos.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
  apply Rle_lt_trans with ((b-a)/(INR N + 1)).
  apply Rmult_le_compat_l.
  by apply Rlt_le, Rgt_minus.
  apply Rinv_le_contravar.
  by apply INRp1_pos.
  by apply Rplus_le_compat_r, le_INR.
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm ; apply Rlt_div_l.
  by apply alpha.
  rewrite /N /nfloor ; case: nfloor_ex => N' HN' /=.
  by apply HN'.
  rewrite /Rmin /= ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  field ; apply Rgt_not_eq, INRp1_pos.
  rewrite SF_lx_f2 -nth_last.
  replace (head 0 _ :: behead _) with (RInt_part a b n) by auto.
  rewrite size_mkseq nth_mkseq ?S_INR /=.
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  field ; apply Rgt_not_eq, INRp1_pos.
  by [].
  rewrite Ropp_minus_distr'.
  apply f_equal.
  rewrite /signe.
  case: Rle_dec (Rlt_le _ _ (Rgt_minus _ _ Hab)) => // Hab' _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rgt_minus _ _ Hab)) => // _ _.
  rewrite Rmult_1_l.
  rewrite /Riemann_sum /RInt_val /RInt_seq /ptd /SF_val_ly.
  rewrite SF_map_f2.
  suff : forall i, (S i < size (RInt_part a b n))%nat -> 
    nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/(INR n + 1).
  elim : (RInt_part a b n) {5}(0) => /= [ | x1].
  move => _ Hnth ; ring.
  case => /= [ | x2 s] IH x0 Hnth.
  ring.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))) IH.
  ring.
  move => i Hi ; exact: (Hnth (S i) (lt_n_S _ _ Hi)).
  rewrite size_mkseq => i Hi ; rewrite !nth_mkseq ?S_INR.
  field ; apply Rgt_not_eq, INRp1_pos.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
Qed.

Lemma ex_RInt_correct_2 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
  wlog: a b /(a < b) => [Hw | Hab ] Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: (Rle_lt_or_eq_dec _ _ Hab) => {Hab} Hab.
    by apply Hw.
    rewrite -Hab.
    by apply RiemannInt_P7.
    apply ex_RInt_swap in Hex ;
    apply RiemannInt_P1 ;
    by apply Hw.
  have : {If : R | is_RInt f a b If}.
    exists (real (Lim_seq (RInt_val f a b))).
    case: Hex => If Hex.
    replace (real (Lim_seq (RInt_val f a b))) with If.
    exact: Hex.
    replace If with (real (Finite If)) by auto.
    apply f_equal, sym_equal, is_lim_seq_unique.
    by apply ex_RInt_correct_aux_2.
  case => If HIf.
  set E := fun eps : posreal => 
    (fun alpha => 0 < alpha <= b-a + 1 /\
      forall ptd : SF_seq,
        pointed_subdiv ptd ->
        seq_step (SF_lx ptd) < alpha ->
        SF_h ptd = Rmin a b ->
        last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
        Rabs (If - signe (b - a) * Riemann_sum f ptd) < eps).
  have E_bnd : forall eps : posreal, bound (E eps).
    move => eps ; exists (b-a+1) => x [Hx _] ; by apply Hx.
  have E_ex : forall eps : posreal, exists x, (E eps x).
    move => eps ; case: (HIf eps) => {HIf} alpha HIf.
    exists (Rmin alpha (b-a + 1)) ; split.
    apply Rmin_case_strong => H.
    split.
    by apply alpha.
    exact: H.
    split.
    apply Rplus_le_lt_0_compat.
    by apply (Rminus_le_0 a b), Rlt_le.
    exact: Rlt_0_1.
    exact: Rle_refl.
    intros.
    apply: HIf.
    exact: H.
    move: H0 ; apply Rmin_case_strong.
    by [].
    move => Halp Hstep ; by apply Rlt_le_trans with (b-a+1).
    exact: H1.
    exact: H2.
  set alpha := fun eps : posreal => projT1 (completeness (E eps) (E_bnd eps) (E_ex eps)).
  have Ealpha : forall eps : posreal, (E eps (alpha eps)).
    revert alpha ; move => /= eps.
    case: (E_ex eps) => alp H.
    case: completeness => alpha [ub lub] /= ; split.
    split.
    apply Rlt_le_trans with alp.
    by apply H.
    by apply ub.
    apply: lub => x [Hx _] ; by apply Hx.
    intros.
    apply Rnot_le_lt ; contradict H1.
    apply Rle_not_lt.
    apply: lub => x [Hx1 Hx2].
    apply Rnot_lt_le ; contradict H1.
    by apply Rlt_not_le, Hx2.
  have Hn : forall eps : posreal, {n : nat | (b-a)/(INR n + 1) < alpha eps}.
    move => eps.
    have Hn : 0 <= (b-a)/(alpha eps).
      apply Rdiv_le_0_compat.
      by apply Rlt_le, Rgt_minus.
      by apply Ealpha.
    set n := (nfloor _ Hn).
    exists n.
    apply Rlt_div_l.
    by apply INRp1_pos.
    rewrite Rmult_comm ; apply Rlt_div_l.
    by apply Ealpha.
    rewrite /n /nfloor ; case: nfloor_ex => /= n' Hn'.
    by apply Hn'.
  
  rewrite /Riemann_integrable.
  suff H : forall eps : posreal,
    {phi : StepFun a b &
    {psi : StepFun a b |
    (forall t : R, Rmin a b <= t <= Rmax a b -> Rabs (f t - phi t) <= psi t) /\
    Rabs (RiemannInt_SF psi) <= eps}}.
  move => eps ; set eps2 := pos_div_2 eps.
  case: (H eps2) => {H} phi [psi [H H0]].
  exists phi ; exists psi ; split.
  exact: H.
  apply Rle_lt_trans with (1 := H0).
  apply Rminus_gt ; simpl ; field_simplify ; rewrite -Rdiv_1 ; by apply eps2.

  move => eps ; set eps2 := pos_div_2 eps.
  case: (Hn eps2) => {Hn} n Hn.
  case: (Ealpha eps2) => {HIf} Halpha HIf.
  
(* Construire phi *)
  set phi := sf_SF_val_fun f a b n.
  exists phi.
(* Construire psi *)
  set psi1 := SF_sup_r (fun t => Rabs (f t - phi t)) a b n.
  have Haux : forall x, 
    {i : nat | x = nth 0 (RInt_part a b n) i /\ (i < size (RInt_part a b n))%nat}
    + {(forall i, (i < size (RInt_part a b n))%nat -> x <> nth 0 (RInt_part a b n) i)}.
    move => x.
    have : {n0 : nat | x = nth 0 (RInt_part a b n) n0 
      /\ (n0 < size (RInt_part a b n))%nat} +
      {(forall n0 : nat,
      ~ (x = nth 0 (RInt_part a b n) n0 
      /\ (n0 < size (RInt_part a b n))%nat))}.
    apply (Markov (fun i => x = nth 0 (RInt_part a b n) i 
      /\ (i < size (RInt_part a b n))%nat)).
    move => i.
    case: (Req_EM_T x (nth 0 (RInt_part a b n) i)) => Hx.
    case: (lt_dec i (size (RInt_part a b n))) => Hi.
    left ; split ; by [].
    right ; contradict Hi ; by apply Hi.
    right ; contradict Hx ; by apply Hx.
    case => [[i Hi] | Hx].
    left ; by exists i.
    right => i Hi ; 
    move: (Hx i) => {Hx} Hx ; 
    contradict Hx ; by split.
  set psi2_aux := fun x => match Haux x with
    | inleft Hi => Rabs (f x - phi x) - psi1 x
    | inright _ => 0
  end.
  set psi2_ly := seq2Rlist (SF_ly (SF_seq_f1 (fun _ => 0) (RInt_part a b n) 0)).
  have psi2_ad : adapted_couple psi2_aux a b (seq2Rlist (RInt_part a b n)) psi2_ly.
    split.
    by apply sorted_compat, RInt_part_sort, Rlt_le.
    split.
    rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
    field ; apply Rgt_not_eq ; by intuition.
    split.
    rewrite size_compat size_mkseq nth_compat nth_mkseq ?S_INR /=.
    rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ ;
    field ; apply Rgt_not_eq ; by intuition.
    by [].
    split.
    by rewrite !size_compat SF_ly_f1 size_belast' size_map.
    rewrite size_compat => i Hi ;
    rewrite !nth_compat SF_ly_f1 => x Hx.
    rewrite /psi2_aux => {psi2_aux} ; 
    case: Haux => [ [j [Hx' Hj]] | Hx' ].
    rewrite Hx' in Hx |- * ; case: Hx => Hxi Hxj.
    case: (lt_dec i j) => Hij.
    contradict Hxj ; apply Rle_not_lt.
    apply sorted_incr.
    by apply RInt_part_sort, Rlt_le.
    by [].
    by [].
    contradict Hxi ; apply Rle_not_lt.
    apply sorted_incr.
    by apply RInt_part_sort, Rlt_le.
    by apply not_lt.
    by intuition.
    move: i Hi {Hx} ; 
    elim: (RInt_part a b n) => /= [ i Hi | x0].
    by apply lt_n_O in Hi.
    case => /= [ | x1 s] IH i Hi.
    by apply lt_n_O in Hi.
    case: i Hi => /= [ | i] Hi.
    by [].
    by apply IH, lt_S_n.
  have psi2_is : IsStepFun psi2_aux a b.
    exists (seq2Rlist (RInt_part a b n)).
    exists psi2_ly.
    by [].
  set psi2 := mkStepFun psi2_is.
  set psi := mkStepFun (StepFun_P28 1 psi1 psi2).
    
  exists psi.

have Hfin : forall i, (S i < size (RInt_part a b n))%nat ->
  is_finite (Sup_fct (fun t0 : R => Rabs (f t0 - phi t0)) 
    (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i))).
  case: (ex_RInt_ub f a b Hex) => M HM.
  case: (ex_RInt_lb f a b Hex) => m Hm.
  case: (StepFun_bound phi) => M' HM'.
  have : exists m, forall x : R, Rmin a b <= x <= Rmax a b -> m <= phi x.
    case: (StepFun_bound (mkStepFun (StepFun_P28 (-1) (mkStepFun (StepFun_P4 a b 0)) phi)))
    => /= m' Hm'.
    exists (-m') => x Hx.
    replace (phi x) with (- (fct_cte 0 x + -1 * phi x)) 
      by (rewrite /fct_cte /= ; ring).
    by apply Ropp_le_contravar, Hm'.
  case => m' Hm' i ;
  rewrite size_mkseq => Hi ;
  rewrite !nth_mkseq.
  rewrite /Sup_fct.
  have H : (a + INR i * (b - a) / (INR n + 1)) <
    (a + (INR (S i)) * (b - a) / (INR n + 1)).
    rewrite S_INR ; apply Rminus_gt ; field_simplify.
    rewrite -Rdiv_1 Rplus_comm ; apply Rdiv_lt_0_compat. 
    by apply Rgt_minus.
    by apply INRp1_pos.
    by apply Rgt_not_eq, INRp1_pos.
  move: (Rlt_not_eq _ _ H) ; case: Req_EM_T => // H0 _.
  move: (ex_Im_fct _ _ _ _) ;
  rewrite /Rmin /Rmax ; 
  case: Rle_dec (Rlt_le _ _ H) => // _ _ H1.
  rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; case => [l | | ] [ub lub] /=.
  by [].
  case: (lub (Finite (Rmax (M - m') (-(m - M'))))) => //.
  move => _ [x [-> Hx]].
  apply Rbar_finite_le, Rabs_le_between_Rmax.
  suff H2 : Rmin a b <= x <= Rmax a b.
  split ; apply Rplus_le_compat, Ropp_le_contravar.
  by apply Hm.
  by apply HM'.
  by apply HM.
  by apply Hm'.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ ; split ;
  apply Rlt_le.
  replace a with (a + INR O * (b - a) / (INR n + 1)) 
    by (simpl ; field ; apply Rgt_not_eq, INRp1_pos).
  apply Rle_lt_trans with (2 := proj1 Hx).
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat ; by intuition.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rgt_minus.
  apply le_INR ; by intuition.
  replace b with (a + INR (S n) * (b - a) / (INR n + 1)) 
    by (rewrite S_INR ; field ; apply Rgt_not_eq, INRp1_pos).
  apply Rlt_le_trans with (1 := proj2 Hx).
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat ; by intuition.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rgt_minus.
  apply le_INR ; by intuition.
  case : H1 => y Hy.
  by case: (ub y Hy).
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.

have Hfin' : forall t, is_finite (SF_sup_fun (fun t : R => Rabs (f t - phi t)) a b n t).
  rewrite /SF_sup_fun ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite /SF_fun /SF_sup_seq.
  case: (RInt_part a b n) Hfin => [ | x0 sx] /=.
  move => _ t ; by case: Rle_dec.
  case: sx => [ | x1 sx] /=.
  move => _ t ; by case: Rle_dec.
  move => H t.
  case: Rlt_dec => Hx0.
  by [].
  elim: sx x0 x1 H Hx0 => [ | x2 sx IH] x0 x1 /= H Hx0.
  case: Rle_dec => Hx1.
  apply (H O) ; by intuition.
  by [].
  case: Rlt_dec => Hx1.
  apply (H O) ; by intuition.
  apply IH.
  move => i Hi ; apply (H (S i) (lt_n_S _ _ Hi)).
  exact: Hx1.

  split.
(* Partie 1 *)
  move => t Ht_ab.
  move: Ht_ab ; rewrite /Rmin /Rmax ; 
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Ht_ab.
  rewrite /= /psi2_aux /= ; case: (Haux t) => [ [i Hi] | Hi ] ;
  ring_simplify.
  exact: Rle_refl.
  apply Rbar_finite_le ; rewrite Hfin'.
  rewrite /SF_sup_fun ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite /SF_fun /SF_sup_seq.
  move: (RInt_part_sort a b n (Rlt_le _ _ Hab)).
  move: Ht_ab.
  pattern b at 1 ; replace b with (last 0 (RInt_part a b n)).
  pattern a at 1 ; replace a with (head 0 (RInt_part a b n)).
  have : (0 < size (RInt_part a b n))%nat.
    rewrite size_mkseq ; exact: lt_O_Sn.
  case: (RInt_part a b n) Hi => [ | x0 sx] Hi Hsx Ht_ab Hsort /=.
  by apply lt_irrefl in Hsx.
  clear Hsx.
  case: sx Hsort Hi Ht_ab => [ | x1 sx] Hsort /= Hi [Ht_a Ht_b].
  move: (Rle_antisym _ _ Ht_b Ht_a) => Ht.
  contradict Ht ; apply (Hi O (lt_n_Sn _)).
  apply Rle_not_lt in Ht_a.
  case: Rlt_dec => // _.
  elim: sx x0 x1 Hsort Ht_a Ht_b Hi => [ | x2 sx IH] x0 x1 Hsort /= Ht_a Ht_b Hi.
  case: Rle_dec => // _.
  rewrite /Sup_fct /Lub_Rbar_ne.
  have H : x0 < x1.
    apply Rlt_trans with t.
    apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
    by [].
    contradict Ht_a ; apply sym_not_eq, (Hi O).
    by apply lt_O_Sn.
    case: Ht_b => Ht_b.
    by [].
    contradict Ht_b ; apply (Hi 1%nat).
    by apply lt_n_Sn.
  move: (Rlt_not_eq _ _ H) ;
  case: Req_EM_T => // H0 _.
  case: ex_lub_Rbar_ne => l lub /=.
  apply lub ; exists t ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _ ;
  split.
  apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
  by [].
  contradict Ht_a ; apply sym_not_eq, (Hi O).
  by apply lt_O_Sn.
  case: Ht_b => Ht_b.
  by [].
  contradict Ht_b ; apply (Hi 1%nat).
  by apply lt_n_Sn.
  case: Rlt_dec => Hx1.
   rewrite /Sup_fct /Lub_Rbar_ne.
  have H : x0 < x1.
    apply Rlt_trans with t.
    apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
    by [].
    contradict Ht_a ; apply sym_not_eq, (Hi O).
    by apply lt_O_Sn.
    by apply Hx1.
  move: (Rlt_not_eq _ _ H) ;
  case: Req_EM_T => // H0 _.
  case: ex_lub_Rbar_ne => l lub /=.
  apply lub ; exists t ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _ ;
  split.
  apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
  by [].
  contradict Ht_a ; apply sym_not_eq, (Hi O).
  by apply lt_O_Sn.
  by [].
  apply IH.
  exact: (proj2 Hsort).
  exact: Hx1.
  exact: Ht_b.
  move => j Hj ; apply (Hi (S j) (lt_n_S _ _ Hj)).
  simpl ; field ; apply Rgt_not_eq ; by intuition.
  rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ;
  field ; apply Rgt_not_eq, INRp1_pos.

(* Partie 2 *)
(* * SF_lx ptd = RInt_part a b n *)
  have : forall g : R -> R -> R,
    let ptd := SF_seq_f2 g (RInt_part a b n) 0 in
    pointed_subdiv ptd ->
    Rabs (If - signe (b-a) * Riemann_sum f ptd) < eps2.
  move => g ptd Hptd.
  apply HIf.
  exact: Hptd.
  rewrite SF_lx_f2.
  suff : forall i, (S i < size (RInt_part a b n))%nat ->
    nth 0 (RInt_part a b n) (S i) - nth 0 (RInt_part a b n) i = (b-a)/(INR n + 1).
  elim: (RInt_part a b n) => /= [ | h0 t IH].
  move => _ ; by apply Ealpha.
  case: t IH => /= [ | h1 t] IH Hnth.
  by apply Ealpha.
  replace (seq_step _) with (Rmax (Rabs (h1 - h0)) (seq_step (h1::t))) by auto.
  apply (Rmax_case_strong (Rabs (h1 - h0))) => /= _.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))).
  rewrite Rabs_right.
  exact: Hn.
  apply Rle_ge, Rdiv_le_0_compat.
  by apply Rlt_le, Rgt_minus.
  by intuition.
  apply IH => i Hi.
  by apply (Hnth (S i)), lt_n_S.
  move => i ; rewrite size_mkseq => Hi ; rewrite !nth_mkseq.
  rewrite S_INR ; field ; apply Rgt_not_eq ; by intuition.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
  simpl ; rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
  field ; apply Rgt_not_eq ; by intuition.
  rewrite -nth_last SF_lx_f2.
  replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n))
    with (RInt_part a b n) by auto.
  rewrite size_mkseq nth_mkseq.
  simpl ssrnat.predn ; rewrite S_INR /Rmax ;
  case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
  field ; apply Rgt_not_eq ; by intuition.
  simpl ; apply SSR_leq, le_refl.
  move => {HIf} HIf.
  have : forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (RInt_part a b n) 0 in
    let ptd2 := SF_seq_f2 g2 (RInt_part a b n) 0 in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
    Rabs (Riemann_sum f ptd1 - Riemann_sum f ptd2) < eps.
  move => g1 g2 ptd1 ptd2 H1 H2.
  replace (Riemann_sum f ptd1 - Riemann_sum f ptd2) with
    ((If - signe (b - a) * Riemann_sum f ptd2) -
      (If - signe (b - a) * Riemann_sum f ptd1)).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps) ; apply Rplus_lt_compat ;
  by apply HIf.
  rewrite /signe /=.
  move: (proj1 (Rminus_le_0 _ _) (Rlt_le _ _ Hab)) ; case: Rle_dec => //= H0 _.
  case: Rle_lt_or_eq_dec => //= {H0} H0.
  ring.
  contradict H0.
  by apply Rlt_not_eq, Rgt_minus.
  move => {HIf} HIf.
  rewrite /Riemann_sum in HIf.
(* * oublier If *)
  have : forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (RInt_part a b n) 0 in
    let ptd2 := SF_seq_f2 g2 (RInt_part a b n) 0 in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
      Rabs
        (RInt_seq (SF_seq_f2 (fun x y => f (g1 x y) - f(g2 x y)) 
          (RInt_part a b n) 0) Rplus Rmult 0) < eps.
  move => g1 g2 ptd1 pdt2 H1 H2.
  replace (RInt_seq _ _ _ _ : R) with 
    (RInt_seq (SF_map f (SF_seq_f2 g1 (RInt_part a b n) 0)) Rplus Rmult 0 -
    RInt_seq (SF_map f (SF_seq_f2 g2 (RInt_part a b n) 0)) Rplus Rmult 0).
  apply HIf.
  exact: H1.
  exact: H2.
  rewrite !SF_map_f2.
  elim: (RInt_part a b n) {1 3 5}(0) => /= [ x0 | h0].
  rewrite /RInt_seq /= ; ring.
  case => /= [ | h1 t] IH x0.
  rewrite /RInt_seq /= ; ring.
  rewrite !(SF_cons_f2 _ h0) /= ; try by intuition.
  rewrite !RInt_seq_cons /= -IH ; ring.
  move => {HIf} HIf.
(* * faire rentrer Rabs dans l'intégrale *)
  have : forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (RInt_part a b n) 0 in
    let ptd2 := SF_seq_f2 g2 (RInt_part a b n) 0 in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
      RInt_seq
      (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
      (RInt_part a b n) 0) Rplus Rmult 0 < eps.
  move => g1 g2 ptd1 ptd2 H1 H2.
  set h1 := fun x y => match Rle_dec (f (g1 x y)) (f (g2 x y)) with
    | left _ => g2 x y | right _ => g1 x y end.
  set h2 := fun x y => match Rle_dec (f (g1 x y)) (f (g2 x y)) with
    | left _ => g1 x y | right _ => g2 x y end.
  replace (RInt_seq
    (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
    (RInt_part a b n) 0) Rplus Rmult 0) with
    (RInt_seq (SF_seq_f2 (fun x y : R => (f (h1 x y) - f (h2 x y)))
    (RInt_part a b n) 0) Rplus Rmult 0).
  rewrite -(Rabs_pos_eq (RInt_seq
    (SF_seq_f2 (fun x y : R => f (h1 x y) - f (h2 x y)) (RInt_part a b n) 0)
    Rplus Rmult 0)).
  apply HIf.
    revert ptd1 ptd2 H1 H2.
    elim: (RInt_part a b n) (0) => [z /= _ _ | x0].
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    case => [ | x1 t] /= IH z H1 H2.
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    move: H1 H2 ; rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    move => H1 H2 ; case => [ | i] /= Hi.
    rewrite /h1 ; case: Rle_dec => //= _.
    apply (H2 O (lt_O_Sn _)).
    apply (H1 O (lt_O_Sn _)).
    apply (IH x0 (ptd_cons _ _ H1) (ptd_cons _ _ H2)).
    apply lt_S_n, Hi.
    revert ptd1 ptd2 H1 H2.
    elim: (RInt_part a b n) (0) => [z /= _ _ | x0].
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    case => [ | x1 t] /= IH z H1 H2.
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    move: H1 H2 ; rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    move => H1 H2 ; case => [ | i] /= Hi.
    rewrite /h2 ; case: Rle_dec => //= _.
    apply (H1 O (lt_O_Sn _)).
    apply (H2 O (lt_O_Sn _)).
    apply (IH x0 (ptd_cons _ _ H1) (ptd_cons _ _ H2)).
    apply lt_S_n, Hi.
  elim: (RInt_part a b n) (RInt_part_sort a b n (Rlt_le _ _ Hab))
    {2}(0) => [Hsort x0 | x0].
  rewrite /RInt_seq /= ; exact: Rle_refl.
  case => [ | x1 t] IH Hsort z.
  rewrite /RInt_seq /= ; exact: Rle_refl.
  rewrite SF_cons_f2 /= ; try by intuition.
  rewrite RInt_seq_cons /= ; apply Rplus_le_le_0_compat.
  apply Rmult_le_pos ; rewrite -Rminus_le_0.
  rewrite /h1 /h2 ; case: Rle_dec => H0.
  by apply H0.
  by apply Rlt_le, Rnot_le_lt.
  by apply Hsort.
  apply IH.
  by apply Hsort.
  elim: (RInt_part a b n) {1 3}(0) => [x0 | x0].
  by rewrite /RInt_seq /= .
  case => [ | x1 t] IH z.
  by rewrite /RInt_seq /= .
  rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
  rewrite !RInt_seq_cons /=.
  apply f_equal2.
  rewrite /h1 /h2 ; case: Rle_dec => H0.
  rewrite Rabs_left1.
  ring.
  by apply Rle_minus.
  rewrite Rabs_right.
  ring.
  by apply Rgt_ge, Rgt_minus, Rnot_le_lt.
  by apply IH.
  move => {HIf} HIf.
(* * phi (g x y) = f (h x y) *)
  have : forall g : R -> R -> R,
    (forall i j, (S i < size (RInt_part a b n))%nat -> 
      (j < size (RInt_part a b n))%nat ->
      g (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i)) 
      <> nth 0 (RInt_part a b n) j) ->
    let ptd := SF_seq_f2 g (RInt_part a b n) 0 in
    pointed_subdiv ptd ->
    RInt_seq
    (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y)))
    (RInt_part a b n) 0) Rplus Rmult 0 < eps.
  move => g1 Hg1 ptd1 H1.
  rewrite /phi /sf_SF_val_fun ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _.
  move: (RInt_part_nat a b n) => Hp.
  set h := fun t => match Rle_dec a t with
    | right _ => t
    | left Ha => match Rle_dec t b with
      | right _ => t
      | left Hb => match Hp t (conj Ha Hb) with
        | inleft H => (a + (INR (projT1 H) + /2) * (b - a) / (INR n + 1))
        | inright _ => (a + (INR n + /2) * (b - a) / (INR n + 1))
      end
    end
  end.
  set g2 := fun x y => h (g1 x y).
  set ptd2 := SF_seq_f2 g2 (RInt_part a b n) 0.
  have H2 : pointed_subdiv ptd2.
    move => i ; move: (H1 i) => {H1}.
    rewrite !SF_lx_f2 !SF_ly_f2 !SF_size_f2 size_mkseq.
    replace (head 0 (RInt_part a b n) :: behead (RInt_part a b n))
      with (RInt_part a b n) by auto.
    move => H1 Hi ; move: (H1 Hi) => {H1}.
    simpl in Hi.
    rewrite !nth_behead !(nth_pairmap 0).
    replace (nth 0 (0 :: RInt_part a b n) (S i)) with
      (nth 0 (RInt_part a b n) i) by auto.
    rewrite /g2 /h => {h g2 ptd2 ptd1} H1.
    case: Rle_dec => Ha.
    case: Rle_dec => Hb.
    case: Hp => [ [j [Ht Hj]] | Ht] ; simpl projT1.
    suff Hij : j = i.
    rewrite Hij in Ht, Hj |- * => {j Hij}.
    rewrite !nth_mkseq.
    rewrite S_INR.
    split ; simpl ; apply Rminus_le_0 ; field_simplify.
    rewrite -Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by field.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    rewrite -Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by field.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; rewrite size_mkseq in Hi, Hj ; by intuition.
    apply SSR_leq ; rewrite size_mkseq in Hi, Hj ; by intuition.
    apply le_antisym ; apply not_lt.
    have Hij : nth 0 (RInt_part a b n) j < nth 0 (RInt_part a b n) (S i).
      apply Rle_lt_trans with 
        (g1 (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i))).
      by apply Ht.
      case: (proj2 H1) => {H1} H1.
      exact: H1.
      contradict H1 ; apply (Hg1 i (S i)).
      rewrite size_mkseq ; by apply lt_n_S.
      rewrite size_mkseq ; by apply lt_n_S.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply RInt_part_sort, Rlt_le, Hab.
    by [].
    by intuition.
    move: (Rle_lt_trans _ _ _ (proj1 H1) (proj2 Ht)) => Hij.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply RInt_part_sort, Rlt_le, Hab.
    by [].
    rewrite size_mkseq ; by intuition.
    suff : i = n.
    move => ->.
    rewrite !nth_mkseq ?S_INR.
    split ; simpl ; apply Rminus_le_0 ; field_simplify.
    rewrite -Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by ring.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    rewrite -Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    replace (2 * INR n + 2) with (2 * (INR n + 1)) by ring.
    apply Rmult_lt_0_compat ; by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; by intuition.
    apply SSR_leq ; by intuition.
    apply le_antisym ; apply not_lt.
    have Hij : nth 0 (RInt_part a b n) i < nth 0 (RInt_part a b n) (S n).
      apply Rle_lt_trans with 
        (g1 (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i))).
      by apply H1.
      case: (proj2 Ht) => {Ht} Ht.
      exact: Ht.
      contradict Ht ; apply Hg1.
      rewrite size_mkseq ; by apply lt_n_S.
      rewrite size_mkseq ; by apply lt_n_Sn.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply RInt_part_sort, Rlt_le , Hab.
    by intuition.
    rewrite size_mkseq ; by intuition.
    have Hij : nth 0 (RInt_part a b n) (n) < nth 0 (RInt_part a b n) (S i).
      apply Rle_lt_trans with 
        (g1 (nth 0 (RInt_part a b n) i) (nth 0 (RInt_part a b n) (S i))).
      by apply Ht.
      case: (proj2 H1) => {H1} H1.
      exact: H1.
      contradict H1 ; apply Hg1.
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq ; by intuition.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply RInt_part_sort, Rlt_le, Hab.
    by [].
    rewrite size_mkseq ; by intuition.
    exact: H1.
    exact: H1.
    apply SSR_leq ; rewrite size_mkseq ; by intuition.
    apply SSR_leq ; rewrite size_mkseq ; by intuition.
    move: (HIf g1 g2 H1 H2).
    replace (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - SF_val_fun f a b n (g1 x y)))
     (RInt_part a b n) 0) with
     (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
     (RInt_part a b n) 0).
    by [].
    have H0 : forall t, a <= t <= b -> SF_val_fun f a b n t = f (h t).
      move => t Ht.
      rewrite /h SF_val_fun_rw.
      case: Ht => Ha Hb.
      case: Rle_dec => // Ha'.
      case: Rle_dec => // Hb'.
      case: RInt_part_nat => [ [i [Ht Hi]] | Ht] ; 
      case: Hp {h g2 ptd2 H2} => [ [j [Ht' Hj]] | Ht'] ; simpl projT1.
      apply (f_equal (fun i => f (a + (INR i + /2) * (b - a) / (INR n + 1)))).
      apply le_antisym ; apply not_lt.
      move: (Rle_lt_trans _ _ _ (proj1 Ht) (proj2 Ht')) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      apply RInt_part_sort, Rlt_le, Hab.
      by [].
      by intuition.
      move: (Rle_lt_trans _ _ _ (proj1 Ht') (proj2 Ht)) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply RInt_part_sort, Rlt_le.
      by [].
      by intuition.
      absurd (i < n)%nat.
      move: (Rle_lt_trans _ _ _ (proj1 Ht') (proj2 Ht)) => Hij ; 
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply RInt_part_sort, Rlt_le.
      by [].
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq in Hi ; by intuition.
      absurd (j < n)%nat.
      move: (Rle_lt_trans _ _ _ (proj1 Ht) (proj2 Ht')) => Hij ; 
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply RInt_part_sort, Rlt_le.
      by [].
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq in Hj ; by intuition.
      by [].
    rewrite /g2.
  have : forall i, (i < size (RInt_part a b n))%nat ->
    a <= nth 0 (RInt_part a b n) i <= b.
    move => i ; rewrite size_mkseq => Hi ; rewrite nth_mkseq.
    pattern b at 3 ; replace b with (a + (INR n + 1) * (b - a) / (INR n + 1)) by 
      (field ; apply Rgt_not_eq ; intuition).
    pattern a at 1 ; replace a with (a + 0 * (b - a) / (INR n + 1)) by 
      (field ; apply Rgt_not_eq ; intuition).
    apply Rgt_minus in Hab.
    split ; apply Rplus_le_compat_l ; repeat apply Rmult_le_compat_r ;
    try by intuition.
    rewrite -S_INR ; apply le_INR ; by intuition.
    by apply SSR_leq.
    revert ptd1 H1 ;
    elim: (RInt_part a b n) {4 5}(0) => [ z ptd1 H1 Hnth | x0 ].
    by [].
    case => [ | x1 s] IH z ptd1 H1 Hnth.
    by [].
    revert ptd1 H1 ;
    rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    intro ;
    apply (f_equal2 (fun x y => SF_cons (x0, Rabs (f (g1 x0 x1) - x)) y)).
    apply sym_equal, H0.
    move: (H1 O (lt_O_Sn _)) 
      (Hnth O (lt_O_Sn _)) (Hnth 1%nat (lt_n_S _ _ (lt_O_Sn _))) => /= ; intuition.
    by apply Rle_trans with x0.
    by apply Rle_trans with x1.
    apply (IH x0 (ptd_cons _ _ H1)).
    move => i Hi ; apply (Hnth (S i)) ; simpl in Hi |- * ; by apply lt_n_S.

  move => {HIf} HIf.
  rewrite Rabs_right.
  
(* * dernière étape :-) *)
  replace (RiemannInt_SF psi) with 
    (RInt_seq (SF_seq_f2 (fun x y : R => real (Sup_fct (fun t => Rabs (f t - phi t)) x y))
    (RInt_part a b n) 0) Rplus Rmult 0).
  set F := fun z s val => exists g : R -> R -> R, 
    (forall (i j : nat),
    (S i < size s)%nat -> (j < size s)%nat 
      -> g (nth 0 s i) (nth 0 s (S i)) <> nth 0 s j) /\
    (let ptd := SF_seq_f2 g s z in pointed_subdiv ptd) /\
    RInt_seq (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y)))
      s z) Rplus Rmult 0 = val.
  suff Hlub : is_lub (F 0 (RInt_part a b n)) (RInt_seq (SF_seq_f2
    (fun x y : R => real (Sup_fct (fun t : R => Rabs (f t - phi t)) x y))
    (RInt_part a b n) 0) Rplus Rmult 0).

  apply Hlub => val [g [Hnth [H0 Hval]]].
  apply Rlt_le ; rewrite -Hval.
  apply HIf.
  exact: Hnth.
  exact: H0.

  Focus 2.
  rewrite StepFun_P30.
  replace (RiemannInt_SF psi2) with 0.
  rewrite Rmult_0_r Rplus_0_r /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ; 
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  elim: (RInt_part a b n) (RInt_part_sort a b n (Rlt_le _ _ Hab)) {1}(0) 
  => [ Hsort z | x0 ].
  by [].
  case => [ | x1 s] IH Hsort z.
  by [].
  rewrite SF_cons_f2 /=.
  rewrite RInt_seq_cons /=.
  by apply f_equal, IH, Hsort.
  exact: lt_O_Sn.
  rewrite /RiemannInt_SF ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (StepFun_P17 (StepFun_P1 psi2) psi2_ad).
  clear psi2_ad.
  revert psi2_ly ; elim: (RInt_part a b n) => /= [ | x0].
  by [].
  case => /= [ | x1 s] IH.
  by [].
  rewrite -IH ; ring.
    
  Focus 2.
  rewrite StepFun_P30.
  replace (RiemannInt_SF psi2) with 0.
  rewrite Rmult_0_r Rplus_0_r ;
  rewrite /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ; 
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  elim: (RInt_part a b n) (RInt_part_sort a b n (Rlt_le _ _ Hab))
    => [ Hsort /= | x0].
  by apply Rge_refl.
  case => [ | x1 s] IH Hsort /=.
  by apply Rge_refl.
  apply Rle_ge, Rplus_le_le_0_compat.
  apply Rmult_le_pos.
  rewrite /Sup_fct /Lub_Rbar_ne.
  case: Req_EM_T => Hx0.
  by apply Rle_refl.
  case: ex_lub_Rbar_ne ; 
  case => [l | | ] [ub lub] /=.
  apply Rle_trans with (Rabs (f ((x0+x1)/2) - phi ((x0+x1)/2))).
  apply Rabs_pos.
  apply Rbar_finite_le, ub.
  exists ((x0+x1)/2) ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _.
  pattern x1 at 3 ; replace x1 with ((x1 + x1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_lt_compat_r.
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
  apply Rplus_lt_compat_l ; by case: (proj1 Hsort).
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
  apply Rplus_lt_compat_r ; by case: (proj1 Hsort).
  apply Rle_refl.
  apply Rle_refl.
  apply -> Rminus_le_0 ; apply Hsort.
  apply Rge_le, IH, Hsort.
  rewrite /RiemannInt_SF ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (StepFun_P17 (StepFun_P1 psi2) psi2_ad).
  clear psi2_ad.
  revert psi2_ly ; elim: (RInt_part a b n) => /= [ | x0].
  by [].
  case => /= [ | x1 s] IH.
  by [].
  rewrite -IH ; ring.

(* ** c'est la bonne borne sup *)
  
  move: Hfin.
  have : sorted Rlt (RInt_part a b n).
    apply sorted_nth => i.
    rewrite size_mkseq => Hi x0 ; rewrite !nth_mkseq.
    apply Rminus_gt ; rewrite S_INR ; field_simplify.
    rewrite -Rdiv_1.
    apply Rdiv_lt_0_compat.
    rewrite Rplus_comm ; by apply Rgt_minus.
    by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; by intuition.
    apply SSR_leq ; by intuition.
  elim: (RInt_part a b n) {3 4}(0) (RInt_part_sort a b n (Rlt_le _ _ Hab))
    => [ x0 Hle Hlt Hfin | x1].
  split ; rewrite /RInt_seq /=.
  move => val [g [Hnth [Hptd Hval]]].
  rewrite -Hval ; by apply Rle_refl.
  move => ub Hub ; apply: Hub.
  exists (fun _ _ => 0).
  split.
  move => i j Hi Hj ; by apply lt_n_O in Hi.
  split.
  move => ptd i Hi ; by apply lt_n_O in Hi.
  split.
  case => [ | x2 s] IH x0 Hle Hlt Hfin.
  split ; rewrite /RInt_seq /=.
  move => val [g [Hnth [Hptd Hval]]].
  rewrite -Hval ; by apply Rle_refl.
  move => ub Hub ; apply: Hub.
  exists (fun _ _ => 0).
  split.
  move => i j Hi Hj.
  simpl in Hi ; by apply lt_S_n, lt_n_O in Hi.
  split.
  move => ptd i Hi ; by apply lt_n_O in Hi.
  split.
  rewrite SF_cons_f2 /= ; last by apply lt_O_Sn.
  rewrite RInt_seq_cons /=.
  set F0 := fun x => 
    exists t, x1 < t < x2 /\ x = Rabs (f t - phi t) * (x2 - x1).
  set set_plus := fun (F : R -> Prop) (G : R -> Prop) (x : R) =>
    exists y, exists z, x = y + z /\ F y /\ G z.
  suff H0 : forall (x : R), F x0 [:: x1, x2 & s] x 
    <-> (set_plus (F0) (F x1 (x2::s))) x.
  suff H1 : is_lub (set_plus (F0) (F x1 (x2::s)))
    (real (Sup_fct (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1) +
    RInt_seq
    (SF_seq_f2
    (fun x y : R => real (Sup_fct (fun t : R => Rabs (f t - phi t)) x y))
    (x2 :: s) x1) Rplus Rmult 0).
  split.
  move => x Hx ; by apply H1, H0.
  move => ub Hub ; apply H1 => x Hx ; by apply Hub, H0.
  suff H_F0 : is_lub (F0) (real (Sup_fct 
    (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1)).
  have Hfin0 : (forall i : nat,
    (S i < size (x2 :: s))%nat ->
    is_finite
    (Sup_fct (fun t0 : R => Rabs (f t0 - phi t0)) (nth 0 (x2 :: s) i)
       (nth 0 (x2 :: s) (S i)))).
    move => i /= Hi ; move: (Hfin (S i) (lt_n_S _ _ Hi)) => /= {Hfin}.
    by [].
  
  move: H_F0 (IH x1 (proj2 Hle) (proj2 Hlt) Hfin0).
  
  move: (F0 (pos_div_2 eps)) (F x1 (x2::s) (pos_div_2 eps)) 
    (real (Sup_fct (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1))
    (RInt_seq (SF_seq_f2 (fun x4 y : R =>
      real (Sup_fct (fun t : R => Rabs (f t - phi t)) x4 y)) (x2 :: s) x1)
      Rplus Rmult 0).
  move => F1 F2 l1 l2 Hl1 Hl2.
    split.
    move => _ [y [z [-> Hx]]].
    apply Rplus_le_compat.
    by apply Hl1, Hx.
    by apply Hl2, Hx.
    move => ub Hub.
    replace ub with ((ub-l2) + l2) by ring.
    apply Rplus_le_compat_r.
    apply Hl1 => y Hy.
    replace y with (l2 + (y - l2)) by ring.
    replace (ub-l2) with ((ub - y) + (y - l2)) by ring.
    apply Rplus_le_compat_r.
    apply Hl2 => z Hz.
    replace z with ((y+z) - y) by ring.
    apply Rplus_le_compat_r.
    apply Hub.
    exists y ; exists z ; by intuition.
  move: (Hfin O (lt_n_S _ _ (lt_O_Sn _))).
  rewrite /Sup_fct /=.
  move: (Rlt_not_eq _ _ (proj1 Hlt)).
  case: Req_EM_T => // Hx1 _.
  rewrite /Lub_Rbar_ne ; case: ex_lub_Rbar_ne ; 
    case => [l | | ] [ub lub] ; simpl.
    split.
    move => _ [t [Ht ->]].
    apply Rmult_le_compat_r.
    apply -> Rminus_le_0 ; apply Hle.
    apply Rbar_finite_le, ub ; exists t ; split.
    by [].
    rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hle) => // _ _ ;
    by intuition.
    move => b0 Hb0.
    move: (Rgt_minus _ _ (proj1 Hlt)) => H1.
    replace b0 with ((b0 / (x2 - x1)) * (x2 - x1)) by 
      (field ; by apply Rgt_not_eq).
    apply Rmult_le_compat_r.
    by apply Rlt_le.
    apply Rbar_finite_le, lub => _ [t [-> Ht]].
    apply Rbar_finite_le.
    replace (Rabs (f t - phi t)) with ((Rabs (f t - phi t) * (x2 - x1)) / (x2 - x1))
      by (field ; by apply Rgt_not_eq).
    apply Rmult_le_compat_r.
    by apply Rlt_le, Rinv_0_lt_compat.
    apply Hb0 ; exists t.
    split.
    move: Ht ; rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hle) => //.
    by [].
    
  
  by [].
  by [].

    move => val ; split => Hval.
    case: Hval => g [Hnth [Hptd <-]] {val}.
    rewrite SF_cons_f2 /=.
    rewrite RInt_seq_cons /=.
    exists (Rabs (f (g x1 x2) - phi (g x1 x2)) * (x2 - x1)).
    exists (RInt_seq
      (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y))) (x2 :: s) x1)
      Rplus Rmult 0).
    split.
    by [].
    split.
    exists (g x1 x2) ; split.
    case: (Hptd O) => /=.
    rewrite SF_size_f2 /= ; exact: lt_O_Sn.
    case => Hx1.
    case => Hx2.
    by split.
    contradict Hx2 ; apply (Hnth O 1%nat).
    simpl ; by intuition.
    simpl ; by intuition.
    contradict Hx1 ; apply sym_not_eq, (Hnth O O).
    simpl ; by intuition.
    simpl ; by intuition.

    by [].
    exists g.
    split.
    move => i j Hi Hj.
    apply (Hnth (S i) (S j)).
    simpl ; apply lt_n_S, Hi.
    simpl ; apply lt_n_S, Hj.
    split.
    move: Hptd => /=.
    rewrite SF_cons_f2 /=.
    apply ptd_cons.
    apply lt_O_Sn.
    split.
    exact: lt_O_Sn.

    case: Hval => /= y Hy.
    case: Hy => /= z [-> [F0y Fz]].
    case: F0y => t [Ht ->].
    case: Fz => g [Hnth [Hpdt <-]].
    set g0 := fun x y => match Req_EM_T x x1 with
      | left _ => match Req_EM_T y x2 with
        | left _ => t
        | right _ => g x y
      end
      | right _ => g x y
    end.
    exists g0.
    split.
    move => {val y z} i j Hi Hj.
    rewrite /g0.
    case: Req_EM_T => Hx1'.
    case: Req_EM_T => Hx2'.
    case: j Hj => /= [ | j] Hj.
    by apply Rgt_not_eq, Ht.
    apply lt_S_n in Hj ; case: j Hj => /= [ | j] Hj.
    by apply Rlt_not_eq, Ht.
    move: (proj2 Hle : sorted Rle (x2 :: s)).
    apply lt_S_n in Hj ; move: (proj2 Ht) ;
    elim: j x2 s Hj {IH Hle Hlt Hfin Hnth Hpdt F0 Ht g0 Hx2' x0 Hx1' i Hi}
      => [ | i IH] x0 ; case => {x1} [ | x1 s] Hi Ht Hle ; simpl.
    by apply lt_irrefl in Hi.
    apply Rlt_not_eq, Rlt_le_trans with (1 := Ht).
    by apply Hle.
    by apply lt_n_O in Hi.
    apply (IH x1).
    by apply lt_S_n, Hi.
    apply Rlt_le_trans with (1 := Ht).
    by apply Hle.
    by apply Hle.
    case: i j Hi Hj Hx1' Hx2' => /= [ | i] j Hi Hj Hx1' Hx2'.
    by [].
    case: j Hj => /= [ | j] Hj.
    apply Rgt_not_eq, Rlt_le_trans with x2.
    apply Rlt_trans with t ; by intuition.
    apply Rle_trans with (nth 0 (x2 :: s) i).
    apply (sorted_incr (x2 :: s) O i).
    move: (ptd_sort _ Hpdt).
    by rewrite /SF_sorted SF_lx_f2.
    by intuition.
    simpl ; by intuition.
    move: (Hpdt i).
    rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 (nth_pairmap 0) /=.
    move => H ; apply H.
    by intuition.
    apply SSR_leq ; by intuition.
    apply Hnth.
    by intuition.
    by intuition.
    simpl in Hi ; apply lt_S_n in Hi ;
    case: i Hi Hx1' => /= [ | i] Hi Hx1'.
    by [].
    case: j Hj => /= [ | j] Hj.
    apply Rgt_not_eq, Rlt_le_trans with x2.
    apply Rlt_trans with t ; by intuition.
    apply Rle_trans with (nth 0 (x2 :: s) i).
    apply (sorted_incr (x2 :: s) O i).
    move: (ptd_sort _ Hpdt).
    by rewrite /SF_sorted SF_lx_f2.
    by intuition.
    simpl ; by intuition.
    move: (Hpdt i).
    rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 (nth_pairmap 0) /=.
    move => H ; apply H.
    by intuition.
    apply SSR_leq ; by intuition.
    apply Hnth.
    by intuition.
    by intuition.
  split.
  move => ptd i Hi.
  rewrite SF_size_f2 /= in Hi.
  rewrite SF_lx_f2 SF_ly_f2 nth_behead (nth_pairmap 0) /=.
  case: i Hi => /= [ | i] Hi ; rewrite /g0.
  move: (refl_equal x1) ; case: Req_EM_T => // _ _.
  move: (refl_equal x2) ; case: Req_EM_T => // _ _.
  split ; apply Rlt_le ; by intuition.
  suff : (nth 0 (x2 :: s) i) <> x1.
  case: Req_EM_T => // _ _.
  move: (Hpdt i).
  rewrite SF_size_f2 SF_lx_f2 SF_ly_f2 nth_behead (nth_pairmap 0) /=.
  move => H ; apply H ; by intuition.
  apply SSR_leq ; by intuition.
  apply Rgt_not_eq, Rlt_le_trans with x2.
  apply Rlt_trans with t ; by intuition.
  apply (sorted_incr (x2 :: s) O i).
  move: (ptd_sort _ Hpdt).
  by rewrite /SF_sorted SF_lx_f2.
  by intuition.
  simpl ; by intuition.
  apply SSR_leq ; by intuition.
  rewrite SF_cons_f2 /=.
  rewrite RInt_seq_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (refl_equal x1) ; case: Req_EM_T => // _ _.
  move: (refl_equal x2) ; case: Req_EM_T => // _ _.
  case: s Hlt {Hpdt IH Hle Hfin F0 Ht Hnth}
    => [ | x3 s] Hlt /=.
  apply refl_equal.
  rewrite !(SF_cons_f2 _ _ (x3 :: _)) /=.
  rewrite !RInt_seq_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (Rgt_not_eq _ _ (proj1 Hlt)) ;
  by case: Req_EM_T.
  elim: s (x2) x3 Hlt => [ | x4 s IH] x2' x3 Hlt.
  exact: refl_equal.
  rewrite !(SF_cons_f2 _ _ (x4 :: _)) /=.
  rewrite !RInt_seq_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (Rgt_not_eq _ _ (Rlt_trans _ _ _ (proj1 Hlt) (proj1 (proj2 Hlt)))) ;
  by case: Req_EM_T.
  apply IH.
  split.
  apply Rlt_trans with x2' ; apply Hlt.
  apply Hlt.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
Qed.

(** * The RInt function *)

Lemma ex_RInt_cv (f : R -> R) (a b : R) : 
  ex_RInt f a b -> ex_lim_seq (RInt_val f a b).
Proof.
  case => If Hex.
  exists If ; by apply ex_RInt_correct_aux_2.
Qed.

Definition RInt (f : R -> R) (a b : R) := 
  match Rle_dec a b with
    | left _ => real (Lim_seq (RInt_val f a b))
    | right _ => - real (Lim_seq (RInt_val f b a))
  end.

Lemma RInt_correct (f : R -> R) (a b : R) :
  forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
  wlog: a b /(a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    move => pr ; set pr' := (RiemannInt_P1 pr).
    rewrite (RiemannInt_P8 _ pr').
    move: (Hw _ _ (Rlt_le _ _ Hab) pr').
    rewrite /RInt ; case: Rle_dec ;
    case: Rle_dec (Rlt_le _ _ Hab) (Rlt_not_le _ _ Hab) => // _ _ _ _.
    by move => ->.
  move => pr ; rewrite /RInt ; case: Rle_dec => // _.
  replace (RiemannInt pr) with (real (Finite (RiemannInt pr))) by auto.
  apply f_equal, is_lim_seq_unique.
  apply ex_RInt_correct_aux_2.
  exact: ex_RInt_correct_aux_1.
Qed.
