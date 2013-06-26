Require Import Reals.
Require Import ssreflect seq.
Require Import ssrbool.

Open Scope R_scope.

(** * more in sdtlib and ssreflect *)
(** Notations *)
Lemma SSR_leq (n m : nat) : is_true (ssrnat.leq n m) <-> (n <= m)%nat.
Proof.
  set H := (@ssrnat.leP n m) ; case: H => H //=.
Qed.
Lemma SSR_minus (n m : nat) : ssrnat.subn n m = (n - m)%nat.
Proof.
  elim: m n => //.
Qed.
(** rcons *)
Lemma rcons_ind {T : Type} (P : seq T -> Type) :
  P [::] -> (forall (s : seq T) (t : T), P s -> P (rcons s t)) -> forall s, P s.
Proof.
  move => H0 Hr s ; move: (refl_equal (size s)).
  move: {1}(size s) => n ; elim: n s => // [| n IH] s Hn ;
  case: s Hn => [| h s] Hn //.
  have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ;
    [| case => s0 [t0 H]].
    elim: (s) (h) => {s h Hn IH} [| h s IH] h0.
      exists [::] ; by exists h0.
    case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ; 
    by rewrite rcons_cons -H.
  rewrite H ; apply Hr, IH, eq_add_S ; by rewrite -(size_rcons s0 t0) -H.
Qed.
Lemma rcons_dec {T : Type} (P : seq T -> Type) :
  (P [::]) -> (forall s t, P (rcons s t)) -> forall s, P s.
Proof.
  move => H0 Hr ; case => [| h s] //.
  have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ;
    [| case => s0 [t0 H]].
    elim: s h => [| h s IH] h0.
      exists [::] ; by exists h0.
    case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ; 
    by rewrite rcons_cons -H.
  by rewrite H.
Qed.
Lemma size_rcons_pos {T : Type} (s : seq T) (t : T) : (0 < size (rcons s t))%nat.
Proof.
  rewrite size_rcons /= ; apply lt_O_Sn.
Qed.

Lemma foldr_rcons {T T0 : Type} : forall (f : T0 -> T -> T) x0 s t, 
  foldr f x0 (rcons s t) = foldr f (f t x0) s.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0 t0 ;
  by rewrite IH.
Qed.
Lemma foldl_rcons {T T0 : Type} : forall (f : T -> T0 -> T) x0 s t, 
  foldl f x0 (rcons s t) = f (foldl f x0 s) t.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0 t0 ;
  by rewrite IH.
Qed.

(** sorted *)
Fixpoint sorted {T : Type} (Ord : T -> T -> Prop) (s : seq T) :=
  match s with
    | [::] | [:: _] => True
    | h0 :: (h1 :: t1) as t0 => Ord h0 h1 /\ sorted Ord t0
  end.
Lemma sorted_nth {T : Type} (Ord : T -> T -> Prop) (s : seq T) :
  sorted Ord s <-> (forall i : nat,
    (i < Peano.pred (size s))%nat -> forall x0 : T, Ord (nth x0 s i) (nth x0 s (S i))).
Proof.
  case: s.
  split => // _ i Hi ; contradict Hi ; apply lt_n_O.
  move => t s ; elim: s t => [ t | t s IHs t0] ; split => // H.
  move => i Hi ; contradict Hi ; apply lt_n_O.
  case => [| i] Hi x0 ; simpl in Hi.
  apply H.
  case: (IHs t) => {IHs} IHs _ ;
  apply (IHs (proj2 H) i (lt_S_n _ _ Hi) x0).
  split.
  apply (H O (lt_0_Sn _) t).
  case: (IHs t) => {IHs} _ IHs.
  apply: IHs => i Hi x0 ; apply: (H (S i)) ; simpl ; apply lt_n_S, Hi.
Qed.
Lemma sorted_cat  {T : Type} (Ord : T -> T -> Prop) (s1 s2 : seq T) x0 :
  sorted Ord s1 -> sorted Ord s2 -> Ord (last x0 s1)  (head x0 s2)
  -> sorted Ord (s1 ++ s2).
Proof.
  move/sorted_nth => H1.
  move/sorted_nth => H2 H0.
  apply sorted_nth => i Hi => x1.
  rewrite ?nth_cat.
  rewrite ?SSR_minus.
  case: (le_dec (S i) (size s1)) => Hi0.
  move: (proj2 (SSR_leq _ _) Hi0) ;
  case: (ssrnat.leq (S i) (size s1)) => // _.
  case: (le_dec (S (S i)) (size s1)) => Hi1.
  move: (proj2 (SSR_leq _ _) Hi1) ;
  case: (ssrnat.leq (S (S i)) (size s1)) => // _.
  apply H1 ; intuition.
  have : ~ (ssrnat.leq (S (S i)) (size s1)).
  contradict Hi1 ; by apply SSR_leq.
  case: (ssrnat.leq (S (S i)) (size s1)) => // _.
  suff Hi' : i = Peano.pred (size s1).
  rewrite Hi' nth_last.
  replace (S (Peano.pred (size s1)) - size s1)%nat with O.
  rewrite nth0.
  apply not_le in Hi1.
  case: (s1) H0 Hi Hi' Hi0 Hi1 => [ | x2 s1'] //= H0 Hi Hi' Hi0 Hi1.
  by apply le_Sn_O in Hi0.
  case: (s2) H0 Hi0 Hi => [ | x3 s2'] //= H0 Hi0 Hi.
  rewrite cats0 /= in Hi.
  rewrite Hi' in Hi.
  by apply lt_irrefl in Hi.
  case: (s1) Hi0 => //= [ | x2 s0] Hi0.
  by apply le_Sn_O in Hi0.
  by rewrite minus_diag.
  apply sym_eq, le_antisym.
  apply NPeano.Nat.le_pred_le_succ.
  apply not_le in Hi1.
  by apply lt_n_Sm_le.
  replace i with (Peano.pred (S i)) by auto.
  by apply le_pred.
  have : ~ (ssrnat.leq (S i) (size s1)).
  contradict Hi0 ; by apply SSR_leq.
  case: (ssrnat.leq (S i) (size s1)) => // _.
  have : ~ssrnat.leq (S (S i)) (size s1).
  contradict Hi0.
  apply SSR_leq in Hi0.
  intuition.
  case: (ssrnat.leq (S (S i)) (size s1)) => // _.
  replace (S i - size s1)%nat with (S (i - size s1)).
  apply H2.
  rewrite size_cat in Hi.
  apply not_le in Hi0.
  elim: (size s1) i Hi Hi0 => [ | n IH] /= i Hi Hi0.
  rewrite -minus_n_O.
  unfold ssrnat.addn, ssrnat.addn_rec in Hi.
  by rewrite plus_0_l in Hi.
  case: i Hi Hi0 => [ | i] /= Hi Hi0.
  by apply lt_S_n, lt_n_O in Hi0.
  apply IH ; by intuition.
  apply not_le in Hi0.
  rewrite minus_Sn_m ; by intuition.
Qed.
(* head, last, behead and belast *)
Lemma head_rcons {T : Type} (x0 : T) (s : seq T) (t : T) : head x0 (rcons s t) = head t s.
Proof.
  case: s x0 t => //.
Qed.
Lemma behead_rcons {T : Type} (s : seq T) (t : T) : 
  (0 < size s)%nat ->  behead (rcons s t) = rcons (behead s) t.
Proof.
  case: s t => // t Hi ; contradict Hi ; apply lt_n_O.
Qed.
Definition belast {T : Type} (s : seq T) :=
  match s with
    | [::] => [::]
    | h :: s => belast h s
  end.
Lemma behead_rev {T : Type} (s : seq T) : behead (rev s) = rev (belast s).
Proof.
  case: s => // t s ; elim: s t => // t s IHs t0.
  rewrite rev_cons behead_rcons ?IHs ?size_rev -?rev_cons //= ; by apply lt_0_Sn.
Qed.

Lemma pairmap_rcons {T T0 : Type} (f : T -> T -> T0) (s : seq T) h0 h x0 :
  pairmap f x0 (rcons (rcons s h0) h) = rcons (pairmap f x0 (rcons s h0)) (f h0 h).
Proof.
  elim: s x0 h h0 => [| h1 s IH] x0 h h0 //= ; by rewrite IH.
Qed.
Lemma map_pairmap {T T0 T1 : Type} (f : T0 -> T1) (g : T -> T -> T0) (s : seq T) (x0 : T) :
  map f (pairmap g x0 s) = pairmap (fun x y => f (g x y)) x0 s.
Proof.
  elim: s x0 => [| h s IH] x0 //=.
  by rewrite IH.
Qed.
Lemma pairmap_map {T T0 T1 : Type} (f : T0 -> T0 -> T1) (g : T -> T0) (s : seq T) (x0 : T) :
  pairmap f (g x0) (map g s) = pairmap (fun x y => f (g x) (g y)) x0 s.
Proof.
  elim: s x0 => [| h s IH] x0 //=.
  by rewrite IH.
Qed.
(** zip and unzip *)
Lemma size_unzip1 {T T0 : Type} (s : seq (T * T0)) : size (unzip1 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
Lemma size_unzip2 {T T0 : Type} (s : seq (T * T0)) : size (unzip2 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
Lemma zip_cons {S T : Type} hs ht (s : seq S) (t : seq T) :
  zip (hs :: s) (ht :: t) = (hs,ht) :: zip s t.
Proof.
  by [].
Qed.
Lemma zip_rcons {S T : Type} (s : seq S) (t : seq T) hs ht : size s = size t ->
  zip (rcons s hs) (rcons t ht) = rcons (zip s t) (hs,ht).
Proof.
  elim: s t hs ht => [| hs s IHs] ; case => //= ht t hs' ht' Hs.
  rewrite IHs => // ; by apply eq_add_S.
Qed.
Lemma unzip1_rcons {S T : Type} (s : seq (S*T)) (h : S*T) :
  unzip1 (rcons s h) = rcons (unzip1 s) (fst h).
Proof.
  elim: s => [ | h0 s IH] //= ; by rewrite IH.
Qed.
Lemma unzip2_rcons {S T : Type} (s : seq (S*T)) (h : S*T) :
  unzip2 (rcons s h) = rcons (unzip2 s) (snd h).
Proof.
  elim: s => [ | h0 s IH] //= ; by rewrite IH.
Qed.
Lemma unzip1_belast {S T : Type} (s : seq (S*T)) :
  unzip1 (belast s) = belast (unzip1 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip2_belast {S T : Type} (s : seq (S*T)) :
  unzip2 (belast s) = belast (unzip2 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip1_behead {S T : Type} (s : seq (S*T)) :
  unzip1 (behead s) = behead (unzip1 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip2_behead {S T : Type} (s : seq (S*T)) :
  unzip2 (behead s) = behead (unzip2 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip1_fst {S T : Type} (s : seq (S*T)) :
  unzip1 s = map (@fst S T) s.
Proof.
  by elim: s.
Qed.
Lemma unzip2_snd {S T : Type} (s : seq (S*T)) :
  unzip2 s = map (@snd S T) s.
Proof.
  by elim: s.
Qed.
Lemma size_belast' {T : Type} (s : seq T) :
  size (belast s) = Peano.pred (size s).
Proof.
  case: s => /= [ | x0 s] //.
  by rewrite size_belast.
Qed.
Lemma head_map {T1 T2 : Type} (f : T1 -> T2) (s : seq T1) (x : T1) :
  head (f x) (map f s) = f (head x s).
Proof.
  by case: s.
Qed.

(** * Definitions of SF_seq *)

Record SF_seq {T : Type} := mkSF_seq {SF_h : R ; SF_t : seq (R * T)}.
Implicit Arguments SF_h [T].
Implicit Arguments SF_t [T].
Implicit Arguments mkSF_seq [T].
Definition SF_lx {T : Type} (s : @SF_seq T) : seq R := (SF_h s)::(unzip1 (SF_t s)).
Definition SF_ly {T : Type} (s : SF_seq) : seq T := unzip2 (SF_t s).
Definition SF_make {T : Type} (lx : seq R) (ly : seq T) (Hs : size lx = S (size ly)) : SF_seq :=
  mkSF_seq (head 0 lx) (zip (behead lx) ly).

Lemma SF_size_lx_ly {T : Type} (s : @SF_seq T) : size (SF_lx s) = S (size (SF_ly s)).
Proof.
  case: s => sh st ;
  rewrite /SF_lx /SF_ly /= ;
  elim: st => //= t s -> //.
Qed.
Lemma SF_seq_bij {T : Type} (s : @SF_seq T) :
  SF_make (SF_lx s) (SF_ly s) (SF_size_lx_ly s) = s.
Proof.
  case: s => sh st ; by rewrite /SF_make (zip_unzip st).
Qed.
Lemma SF_seq_bij_lx {T : Type} (lx : seq R) (ly : seq T)
  (Hs : size lx = S (size ly)) : SF_lx (SF_make lx ly Hs) = lx.
Proof.
  case: lx Hs => // x lx Hs ;
  rewrite /SF_make / SF_lx unzip1_zip //= ;
  apply SSR_leq, le_S_n ; rewrite -Hs => //.
Qed.
Lemma SF_seq_bij_ly {T : Type} (lx : seq R) (ly : seq T)
  (Hs : size lx = S (size ly)) : SF_ly (SF_make lx ly Hs) = ly.
Proof.
  case: lx Hs => // x lx Hs ;
  rewrite /SF_make / SF_ly unzip2_zip //= ;
  apply SSR_leq, le_S_n ; rewrite -Hs => //.
Qed.

(** ** Constructors *)

Definition SF_nil {T : Type} (x0 : R) : @SF_seq T := mkSF_seq x0 [::].
Definition SF_cons {T : Type} (h : R*T) (s : SF_seq) :=
  mkSF_seq (fst h) ((SF_h s,snd h)::(SF_t s)).
Definition SF_rcons {T : Type} (s : @SF_seq T) (t : R*T) :=
  mkSF_seq (SF_h s) (rcons (SF_t s) t).

Lemma SF_cons_dec {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P (SF_cons h s)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; case: st => [| h sf].
  apply Hnil.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf)) => {Hcons} ; 
  rewrite /SF_cons -surjective_pairing //=.
Qed.
Lemma SF_cons_ind {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall h s, P s -> P (SF_cons h s)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hcons [sh st] ; elim: st sh => [sh |h sf IHst sh].
  apply Hnil.
  move: (IHst (fst h)) => {IHst} IHst.
  move: (Hcons (sh,snd h) (mkSF_seq (fst h) sf) IHst) => {Hcons} ; 
  rewrite /SF_cons -surjective_pairing //=.
Qed.

Lemma SF_rcons_dec {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P (SF_rcons s t)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st ; apply rcons_dec => [| st t].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t).
Qed.
Lemma SF_rcons_ind {T : Type} (P : @SF_seq T -> Type) :
  (forall x0 : R, P (SF_nil x0)) -> (forall s t, P s -> P (SF_rcons s t)) 
    -> (forall s, P s).
Proof.
  move => Hnil Hrcons [sh st] ; move: st sh ;
  apply (rcons_ind (fun st => forall sh, P {| SF_h := sh; SF_t := st |})) => [sh | st t IHst sh].
  apply Hnil.
  apply (Hrcons (mkSF_seq sh st) t) => //.
Qed.

Lemma SF_cons_rcons {T : Type} (h : R*T) (s : @SF_seq T) (l : R*T) :
  SF_cons h (SF_rcons s l) = SF_rcons (SF_cons h s) l.
Proof.
  case: h => hx hy ;
  case: l => lx ly ;
  case: s => sh st //.
Qed.

Lemma SF_lx_nil {T : Type} (x0 : R) :
  SF_lx (@SF_nil T x0) = [:: x0].
Proof.
  by [].
Qed.
Lemma SF_ly_nil {T : Type} (x0 : R) :
  SF_ly (@SF_nil T x0) = [::].
Proof.
  by [].
Qed.

Lemma SF_lx_cons {T : Type} (h : R*T) (s : @SF_seq T) :
  SF_lx (SF_cons h s) = (fst h) :: (SF_lx s).
Proof.
  by [].
Qed.
Lemma SF_ly_cons {T : Type} (h : R*T) (s : @SF_seq T) :
  SF_ly (SF_cons h s) = (snd h) :: (SF_ly s).
Proof.
  by [].
Qed.
Lemma SF_lx_rcons {T : Type} (s : @SF_seq T) (h : R*T) :
  SF_lx (SF_rcons s h) = rcons (SF_lx s) (fst h).
Proof.
  case: s => sh st ; rewrite /SF_lx /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.
Lemma SF_ly_rcons {T : Type} (s : @SF_seq T) (h : R*T) :
  SF_ly (SF_rcons s h) = rcons (SF_ly s) (snd h).
Proof.
  case: s => sh st ; rewrite /SF_ly /SF_rcons /= ; elim: st sh => // [[x y] st] IHst sh /= ;
  by rewrite (IHst x).
Qed.

Lemma SF_lx_surj {T : Type} (s s0 : @SF_seq T) :
  s = s0 -> SF_lx s = SF_lx s0.
Proof.
  by move => ->.
Qed.
Lemma SF_ly_surj {T : Type} (s s0 : @SF_seq T) :
  s = s0 -> SF_ly s = SF_ly s0.
Proof.
  by move => ->.
Qed.
Lemma SF_lx_ly_inj {T : Type} (s s0 : @SF_seq T) :
  SF_lx s = SF_lx s0 -> SF_ly s = SF_ly s0 -> s = s0.
Proof.
  move: s0 ; apply SF_cons_ind with (s := s) => {s} [x | h s IH] s0 ;
    apply SF_cons_dec with (s := s0) => {s0} [x0 | h0 s0] Hx Hy //.
(* s = SF_nil _ *)
  rewrite !SF_lx_nil in Hx.
  replace x with (head 0 ([::x])) by intuition ;
  by rewrite Hx.
(* s = SF_cons _ _*)
  rewrite !SF_lx_cons in Hx ; rewrite !SF_ly_cons in Hy.
  replace h with (head (fst h) (fst h :: SF_lx s),head (snd h) (snd h :: SF_ly s)) ;
    [ rewrite Hx Hy (IH s0) //= | move => /= ; by apply injective_projections].
  replace (SF_lx s) with (behead (fst h :: SF_lx s)) by intuition ; by rewrite Hx.
  replace (SF_ly s) with (behead (snd h :: SF_ly s)) by intuition ; by rewrite Hy.
Qed.

(** ** SF_size *)

Definition SF_size {T : Type} (s : @SF_seq T) := size (SF_t s).

Lemma SF_size_cons {T : Type} (h : R*T) (s : @SF_seq T) : SF_size (SF_cons h s) = S (SF_size s).
Proof.
  rewrite /SF_cons /SF_size //=.
Qed.

Lemma SF_size_rcons {T : Type} (s : @SF_seq T) (t : R*T) : SF_size (SF_rcons s t) = S (SF_size s).
Proof.
  rewrite /SF_rcons /SF_size size_rcons //=.
Qed.

Lemma SF_size_lx {T : Type} (s : @SF_seq T) : size (SF_lx s) = S (SF_size s).
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.
Lemma SF_size_ly {T : Type} (s : @SF_seq T) : size (SF_ly s) = SF_size s.
Proof.
  case: s => sh st ; rewrite /SF_size /= ; elim: st => //= _ st -> //.
Qed.

(** ** SF_rev *)
Lemma SF_rev_0 {T : Type} (s : @SF_seq T) :
  size (rev (SF_lx s)) = S (size (rev (SF_ly s))).
Proof.
  by rewrite ?size_rev SF_size_lx SF_size_ly.
Qed.
Definition SF_rev {T : Type} (s : @SF_seq T) : SF_seq :=
  SF_make (rev (SF_lx s)) (rev (SF_ly s)) (SF_rev_0 s).

Lemma SF_rev_cons {T : Type} (h : R*T) (s : @SF_seq T) :
  SF_rev (SF_cons h s) = SF_rcons (SF_rev s) h.
Proof.
  apply SF_lx_ly_inj. 
  by rewrite SF_lx_rcons !SF_seq_bij_lx SF_lx_cons rev_cons.
  by rewrite SF_ly_rcons !SF_seq_bij_ly SF_ly_cons rev_cons.
Qed.
Lemma SF_rev_rcons {T : Type} (s : @SF_seq T) (t : R*T) :
  SF_rev (SF_rcons s t) = SF_cons t (SF_rev s).
Proof.
  apply SF_lx_ly_inj. 
  by rewrite SF_lx_cons !SF_seq_bij_lx SF_lx_rcons rev_rcons.
  by rewrite SF_ly_cons !SF_seq_bij_ly SF_ly_rcons rev_rcons.
Qed.

Lemma SF_rev_invol {T : Type} (s : @SF_seq T) :
  SF_rev (SF_rev s) = s.
Proof.
  apply SF_lx_ly_inj.
  by rewrite /SF_rev ?SF_seq_bij_lx revK.
  by rewrite /SF_rev ?SF_seq_bij_ly revK.
Qed.

Lemma SF_lx_rev {T : Type} (s : @SF_seq T) : SF_lx (SF_rev s) = rev (SF_lx s).
Proof.
  by rewrite /SF_rev ?SF_seq_bij_lx.
Qed.
Lemma SF_ly_rev {T : Type} (s : @SF_seq T) : SF_ly (SF_rev s) = rev (SF_ly s).
Proof.
  by rewrite /SF_rev ?SF_seq_bij_ly.
Qed.

Lemma SF_size_rev {T : Type} (s : @SF_seq T) : SF_size (SF_rev s) = SF_size s.
Proof.
  by rewrite -?SF_size_ly SF_ly_rev size_rev.
Qed.

Lemma SF_rev_surj {T : Type} (s s0 : @SF_seq T) :
  s = s0 -> SF_rev s = SF_rev s0.
Proof.
  by move => ->.
Qed.
Lemma SF_rev_inj {T : Type} (s s0 : @SF_seq T) :
  SF_rev s = SF_rev s0 -> s = s0.
Proof.
  move => H ; by rewrite -(SF_rev_invol s) -(SF_rev_invol s0) H.
Qed.

(** ** SF_sorted *)

Definition SF_sorted {T : Type} (Ord : R -> R -> Prop) (s : @SF_seq T) :=
  sorted Ord (SF_lx s).

Lemma sorted_dec (s : seq R) x0 (x : R) : 
  sorted Rle s -> head x0 s <= x <= last x0 s ->
    {i : nat | nth x0 s i <= x < nth x0 s (S i) /\ (S (S i) < size s)%nat}
    + {nth x0 s (size s - 2)%nat <= x <= nth x0 s (size s - 1)%nat}.
Proof.
  case: s => [/= _ Hx| h s] ; simpl minus ; rewrite -?minus_n_O.
    by right.
  case: s => [/= _ Hx| h0 s] ; simpl minus ; rewrite -?minus_n_O.
    by right.
  elim: s h h0 => [/= | h1 s IH] h h0 Hs Hx.
    by right.
  case: (Rlt_le_dec x h0) => Hx'.
    left ; exists O => /= ; intuition.
  case: (IH h0 h1) => [ | |[i Hi]|Hi].
  apply Hs.
  split ; [apply Hx'|apply Hx].
  left ; exists (S i) => /= ; intuition.
  right => /= ; intuition.
Qed.

(** * SF_map *)

Definition SF_map {T T0 : Type} (f : T -> T0) (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (map (fun x => (fst x,f (snd x))) (SF_t s)).

Lemma SF_map_cons {T T0 : Type} (f : T -> T0) (h : R*T) (s : SF_seq) : 
  SF_map f (SF_cons h s) = SF_cons (fst h, f (snd h)) (SF_map f s).
Proof.
  case: s => sh ; elim => // h st ; rewrite /SF_map => //.
Qed.

Lemma SF_map_rcons {T T0 : Type} (f : T -> T0) (s : SF_seq) (h : R*T) : 
  SF_map f (SF_rcons s h) = SF_rcons (SF_map f s) (fst h, f (snd h)).
Proof.
  move: h ; apply SF_cons_ind with (s := s) => {s} [x0 | h0 s IH] //= h.
  rewrite SF_map_cons.
  replace (SF_rcons (SF_cons h0 s) h) with
    (SF_cons h0 (SF_rcons s h)) by auto.
  rewrite SF_map_cons.
  rewrite IH.
  auto.
Qed.

Lemma SF_map_lx {T T0 : Type} (f : T -> T0) (s : SF_seq) : 
  SF_lx (SF_map f s) = SF_lx s.
Proof.
  apply SF_cons_ind with (s := s) => {s} //= h s IH ;
  by rewrite SF_map_cons ?SF_lx_cons IH.
Qed.

Lemma SF_map_ly {T T0 : Type} (f : T -> T0) (s : SF_seq) : 
  SF_ly (SF_map f s) = map f (SF_ly s).
Proof.
  apply SF_cons_ind with (s := s) => {s} //= h s IH ;
  by rewrite SF_map_cons ?SF_ly_cons IH.
Qed.

Lemma SF_map_rev {T T0 : Type} (f : T -> T0) s :
  SF_rev (SF_map f s) = SF_map f (SF_rev s).
Proof.
  apply SF_lx_ly_inj.
  by rewrite SF_lx_rev ?SF_map_lx ?SF_lx_rev.
  by rewrite SF_ly_rev ?SF_map_ly ?SF_ly_rev map_rev.
Qed.

(** * Definition of SF_fun *)

Fixpoint SF_fun_aux {T : Type} (h : R*T) (s : seq (R*T)) (x0 : T) (x : R) :=
  match s with
    | [::] => match Rle_dec x (fst h) with
        | left _ => snd h
        | right _ => x0
      end
    | h0 :: s0 => match Rlt_dec x (fst h) with
        | left _ => snd h
        | right _ => SF_fun_aux h0 s0 x0 x
      end
  end.
Definition SF_fun {T : Type} (s : SF_seq) (x0 : T) (x : R) :=
  SF_fun_aux (SF_h s,x0) (SF_t s) x0 x.

Lemma SF_fun_incr {T : Type} (s : SF_seq) (x0 : T) (x : R) Hs Hx :
  SF_fun s x0 x = 
  match (sorted_dec (SF_lx s) 0 x Hs Hx) with
    | inleft H => nth x0 (SF_ly s) (projT1 H) 
    | inright _ =>  nth x0 (SF_ly s) (SF_size s -1)%nat
  end.
Proof.
  rewrite /SF_fun /=.
(* s = SF_nil _ *)
  move: Hs Hx ; apply SF_cons_dec with (s := s) => {s} [/= x1 | h s] Hs /= Hx.
    case: sorted_dec => /= [[i Hi]|Hi] ; rewrite /SF_ly ; case: Rle_dec => //= ; 
    case: i Hi => //.
(* s = SF_cons _ (SF_nil _) *)
  case: Rlt_dec => [Hx' | _].
  contradict Hx' ; apply Rle_not_lt, Hx.
  move: h Hs Hx ; apply SF_cons_ind with (s := s) => {s} [x1 | h0 s IH] h Hs /= Hx.
    case: sorted_dec => [/= [i [Hi' Hi]] /= |Hi].
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
  case: Hx => Hx Hx' ; apply Rle_not_lt in Hx ; case: Rle_dec => //.
(* s = SF_cons _ (SF_cons _ _) *)
  case: Rlt_dec => Hx'.
  case: sorted_dec => /= [[i Hi]|Hi]/=.
  case: i Hi => //= i Hi ; contradict Hx' ; 
  apply Rle_not_lt, Rle_trans with (2 := proj1 (proj1 Hi)).
  simpl in Hs ; elim: (unzip1 (SF_t s)) (fst h0) (SF_h s) (i) (proj2 Hs) (proj2 Hi)
    => {s IH Hs Hx Hi h h0} [| h1 s IH] h h0 n Hs Hn.
    repeat apply lt_S_n in Hn ; by apply lt_n_O in Hn.
    case: n Hn => [| n] Hn.
    apply Rle_refl.
  apply Rle_trans with (1 := proj1 Hs) => //= ; intuition.
  contradict Hx' ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hi).
  simpl in Hs ; elim: (unzip1 (SF_t s)) (fst h0) (SF_h s) (proj2 Hs)
    => {s IH Hs Hx Hi h h0} [| h1 s IH] h h0 Hs.
    apply Rle_refl.
    apply Rle_trans with (1 := proj1 Hs) => //= ; intuition.
  have : fst h0 <= x <= last (SF_h s) (unzip1 (SF_t s)) => [ | {Hx'} Hx'].
    split ; [by apply Rnot_lt_le | by apply Hx].
  rewrite (IH h0 (proj2 Hs) Hx') => {IH} ; 
  case: sorted_dec => [[i [Hxi Hi]]|Hi] ; case: sorted_dec => [[j [Hxj Hj]]|Hj] ;
  rewrite -?minus_n_O //=.
(* i,j < size s - 2 *)
  move : h h0 i j Hs {Hx Hx'} Hxi Hi Hxj Hj ; apply SF_cons_ind with (s := s) 
    => {s} [x1 | h1 s IH] h h0 i j Hs //= Hxi Hi Hxj Hj.
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
  case: j Hxj Hj => [/= | j] Hxj Hj.
  case: Hxj => _ Hxj ; contradict Hxj ; apply Rle_not_lt, Rle_trans with (2 := proj1 Hxi).
  elim: (i) Hi => {i Hxi IH} //= [| i IH] Hi.
  apply Rle_refl.
  apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hi)), (sorted_nth Rle) ;
  [apply Hs | simpl ; intuition].
  case: i Hxi Hi => [/= | i] Hxi Hi.
  case: j Hxj Hj => [//= | j] Hxj Hj.
  case: Hxi => _ Hxi ; contradict Hxi ; 
  apply Rle_not_lt, Rle_trans with (2 := proj1 Hxj) ;
  elim: (j) Hj => {j Hxj IH} //= [| j IH] Hj.
  apply Rle_refl.
  apply Rle_trans with (1 := IH (lt_trans _ _ _ (lt_n_Sn _) Hj)), (sorted_nth Rle) ;
  [apply Hs | simpl ; intuition].
  apply (IH h0 h1 i j) => //.
  apply Hs.
  apply lt_S_n, Hi.
  apply lt_S_n, Hj.
(* i < j = size s - 2 *)
  simpl in Hxi, Hj ; case: Hxi => _ Hxi ; contradict Hxi ; 
  apply Rle_not_lt, Rle_trans with (2 := proj1 Hj).
  move: Hi Hs ; rewrite ?SF_lx_cons /SF_lx.
  elim: i (fst h) (fst h0) (SF_h s) (unzip1 (SF_t s)) 
    => {s Hx Hx' Hj h x0 h0} [| i IH] h h0 h1 s Hi Hs.
    case: s Hi Hs => [| h2 s] Hi Hs /=.
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
    elim: s h h0 h1 h2 {Hi} Hs => [| h3 s IH] h h0 h1 h2 Hs /=.
    apply Rle_refl.
    apply Rle_trans with (r2 := h2).
    apply Hs.
    apply (IH h0 h1).
    apply (proj2 Hs).
  case: s Hi Hs => [| h2 s] Hi Hs.
    by apply lt_S_n, lt_S_n, lt_n_O in Hi.
  apply (IH h0 h1 h2 s).
  apply lt_S_n, Hi.
  apply Hs.
(* j < i = size s - 2 *)
  simpl in Hxj, Hi ; case: Hxj => _ Hxj ; contradict Hxj ; 
  apply Rle_not_lt, Rle_trans with (2 := proj1 Hi).
  move: Hj Hs ; rewrite ?SF_lx_cons /SF_lx.
  rewrite -minus_n_O ;
  elim: j (fst h) (fst h0) (SF_h s) (unzip1 (SF_t s)) 
    => {s Hx Hx' Hi h x0 h0} [ | j IH] h h0 h1 s Hj Hs /=.
    elim: s h h0 h1 {Hj} Hs => [| h2 s IH] h h0 h1 Hs /=.
    apply Rle_refl.
    apply Rle_trans with (r2 := h1).
    apply Hs.
    apply (IH h0 h1 h2).
    apply (proj2 Hs).
  case: s Hj Hs => [| h2 s] Hj Hs.
    by apply lt_S_n, lt_S_n, lt_S_n, lt_n_O in Hj.
  apply (IH h0 h1 h2 s).
  apply lt_S_n, Hj.
  apply Hs.
Qed.

Lemma SF_fun_map {T T0 : Type} (f : T -> T0) (s : SF_seq) x0 :
  forall x, SF_fun (SF_map f s) (f x0) x = f (SF_fun s x0 x).
Proof.
  case: s => sh st ; rewrite /SF_fun /SF_map /= ; case: st => [| h st] x /=.
  by case: Rle_dec.
  case: Rlt_dec => //.
  elim: st sh h x0 x => [| h0 st IH] sh h x0 x Hx //=.
  by case: Rle_dec.
  case: Rlt_dec => // {Hx} Hx.
  by apply: (IH (fst h)).
Qed.

(** * Definition of RInt_seq *)

Definition RInt_seq {T : Type} (s : SF_seq) (Tplus : T -> T -> T) 
  (Tmult : T -> R -> T) x0 :=
  foldr Tplus x0 (pairmap (fun x y => (Tmult (snd y) (fst y - fst x))) (SF_h s,x0) (SF_t s)).

Lemma RInt_seq_cons {T : Type} h (s : SF_seq) (Tplus : T -> T -> T) 
  (Tmult : T -> R -> T) x0 : 
  RInt_seq (SF_cons h s) Tplus Tmult x0 = Tplus 
    (Tmult (snd h) (SF_h s - fst h)) (RInt_seq s Tplus Tmult x0).
Proof.
  rewrite /RInt_seq //=.
  apply SF_cons_dec with (s := s) => {s} [x1 | h0 s] //=.
Qed.

(** * SF_seq form seq R *)

(** ** SF_seq *)

Definition SF_seq_f1 {T : Type} (f1 : R -> T) (P : seq R) (x0 : R) : SF_seq :=
  mkSF_seq (head x0 P) (pairmap (fun x y => (y, f1 x)) (head x0 P) (behead P)).
Definition SF_seq_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) (x0 : R) : SF_seq :=
  mkSF_seq (head x0 P) (pairmap (fun x y => (y, f2 x y)) (head x0 P) (behead P)).

Lemma SF_cons_f1 {T : Type} (f1 : R -> T) (h : R) (P : seq R) (x0 : R) : 
  (0 < size P)%nat -> SF_seq_f1 f1 (h::P) x0 = SF_cons (h,f1 h) (SF_seq_f1 f1 P x0).
Proof.
  case: P => [ H | h0 P _] //.
  by apply lt_n_O in H.
Qed.
Lemma SF_cons_f2 {T : Type} (f2 : R -> R -> T) (h : R) (P : seq R) (x0 : R) : 
  (0 < size P)%nat -> 
    SF_seq_f2 f2 (h::P) x0 = SF_cons (h,f2 h (head x0 P)) (SF_seq_f2 f2 P h).
Proof.
  case: P => [ H | h0 P _] //.
  by apply lt_n_O in H.
Qed.

Lemma SF_size_f1 {T : Type} (f1 : R -> T) P x0 :
  SF_size (SF_seq_f1 f1 P x0) = Peano.pred (size P).
Proof.
  case: P => [| h P] //= ; by rewrite /SF_size /= size_pairmap.
Qed.
Lemma SF_size_f2 {T : Type} (f2 : R -> R -> T) P x0 :
  SF_size (SF_seq_f2 f2 P x0) = Peano.pred (size P).
Proof.
  case: P => [| h P] //= ; by rewrite /SF_size /= size_pairmap.
Qed.

Lemma SF_lx_f1 {T : Type} (f1 : R -> T) P x0 :
  SF_lx (SF_seq_f1 f1 P x0) = (head x0 P) :: (behead P).
Proof.
  case: P => [| h P] // ; elim: P h =>  //= h P IH h0 ;
  by rewrite -{2}(IH h).
Qed.
Lemma SF_lx_f2 {T : Type} (f2 : R -> R -> T) P x0 :
  SF_lx (SF_seq_f2 f2 P x0) = (head x0 P) :: (behead P).
Proof.
  case: P => [| h P] // ; elim: P h =>  //= h P IH h0 ;
  by rewrite -{2}(IH h).
Qed.

Lemma SF_ly_f1 {T : Type} (f1 : R -> T) P x0 :
  SF_ly (SF_seq_f1 f1 P x0) = belast (map f1 P).
Proof.
  case: P => [| h P] // ; elim: P h =>  //= h P IH h0 ;
  by rewrite -(IH h).
Qed.
Lemma SF_ly_f2 {T : Type} (f2 : R -> R -> T) P x0 :
  SF_ly (SF_seq_f2 f2 P x0) = behead (pairmap f2 x0 P).
Proof.
  case: P => [| h P] // ; elim: P h =>  //= h P IH h0 ;
  by rewrite -(IH h).
Qed.

Lemma SF_sorted_f1 {T : Type} (f1 : R -> T) P x0 Ord :
  (sorted Ord P) <-> (SF_sorted Ord (SF_seq_f1 f1 P x0)).
Proof.
  rewrite /SF_sorted SF_lx_f1 ; case: P ; by split.
Qed.
Lemma SF_sorted_f2 {T : Type} (f2 : R -> R -> T) P x0 Ord :
  (sorted Ord P) <-> (SF_sorted Ord (SF_seq_f2 f2 P x0)).
Proof.
  rewrite /SF_sorted SF_lx_f2 ; case: P ; by split.
Qed.

Lemma SF_rev_f2 {T : Type} (f2 : R -> R -> T) P x0 : (forall x y, f2 x y = f2 y x) ->
  SF_rev (SF_seq_f2 f2 P x0) = SF_seq_f2 f2 (rev P) x0.
Proof.
  move => Hf2 ; apply SF_lx_ly_inj ;
  case: P => [ | h P] //.
  by rewrite SF_lx_rev !SF_lx_f2 ?rev_cons /= headI.
  rewrite SF_ly_rev !SF_ly_f2 /= ?rev_cons.
  elim: P x0 h => [ | h0 P IH] x0 h //=.
  rewrite ?rev_cons pairmap_rcons behead_rcons ?(IH x0 h0) ?(Hf2 h h0) //.
  rewrite size_pairmap size_rcons ; apply lt_O_Sn.
Qed.

Lemma SF_map_f1 {T T0 : Type} (f : T -> T0) (f1 : R -> T) P x0 :
  SF_map f (SF_seq_f1 f1 P x0) = SF_seq_f1 (fun x => f (f1 x)) P x0.
Proof.
  case: P => [| h P] // ; elim: P h => [| h0 P IH] h //.
  rewrite ?(SF_cons_f1 _ _ (h0::P)) /= ; try intuition.
  rewrite SF_map_cons IH ; intuition.
Qed.
Lemma SF_map_f2 {T T0 : Type} (f : T -> T0) (f2 : R -> R -> T) P x0 :
  SF_map f (SF_seq_f2 f2 P x0) = SF_seq_f2 (fun x y => f (f2 x y)) P x0.
Proof.
  case: P => [| h P] // ; elim: P h => [| h0 P IH] h //.
  rewrite ?(SF_cons_f2 _ _ (h0::P)) /= ; try intuition.
  rewrite SF_map_cons IH ; intuition.
Qed.

(** ** SF_fun *)

Definition SF_fun_f1 {T : Type} (f1 : R -> T) (P : seq R) (x0 : R*T) x :=
  SF_fun (SF_seq_f1 f1 P (fst x0)) (snd x0) x.
Definition SF_fun_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) (x0 : R*T) x :=
  SF_fun (SF_seq_f2 f2 P (fst x0)) (snd x0) x.

(** ** RInt_seq *)

Definition RInt_f1 {T : Type} Tplus Tmult (f1 : R -> T) (P : seq R) x0 :=
  RInt_seq (SF_seq_f1 f1 P (fst x0)) Tplus Tmult (snd x0).
Definition RInt_f2 {T : Type} Tplus Tmult (f2 : R -> R -> T) (P : seq R) x0 :=
  RInt_seq (SF_seq_f2 f2 P (fst x0)) Tplus Tmult (snd x0).

(** * SF_seq in R *)
(** seq R and Rlist *)
Fixpoint seq2Rlist (s : seq R) :=
  match s with
    | [::] => RList.nil
    | h::t => RList.cons h (seq2Rlist t)
  end.
Fixpoint Rlist2seq (s : Rlist) : seq R :=
  match s with
    | RList.nil => [::]
    | RList.cons h t => h::(Rlist2seq t)
  end.

Lemma seq2Rlist_bij (s : Rlist) :
  seq2Rlist (Rlist2seq s) = s.
Proof.
  by elim: s => //= h s ->.
Qed.
Lemma Rlist2seq_bij (s : seq R) :
  Rlist2seq (seq2Rlist s) = s.
Proof.
  by elim: s => //= h s ->.
Qed.

Lemma size_compat (s : seq R) :
  Rlength (seq2Rlist s) = size s.
Proof.
  elim: s => // t s IHs /= ; by rewrite IHs.
Qed.

Lemma nth_compat (s : seq R) (n : nat) :
  pos_Rl (seq2Rlist s) n = nth 0 s n.
Proof.
  elim: s n => [n|t s IHs n] /= ;
  case: n => //=.
Qed.

Lemma sorted_compat (s : seq R) :
  sorted Rle s <-> ordered_Rlist (seq2Rlist s).
Proof.
  case: s => [| h s].
(* s = [::] *)
  split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
  elim: s h => [h | h s IHs h'].
(* s = [::_] *)
  split => // H i /= Hi ; contradict Hi ; apply lt_n_O.
(* s = _::(_::_) *)
  split => H.
  case => [ /= | i] ; rewrite size_compat => Hi ; simpl in Hi.
  apply H.
  apply (proj1 (IHs h) (proj2 H) i) ; rewrite size_compat /= ; apply lt_S_n => //.
  split.
  apply (H O) ; rewrite size_compat /= ; apply lt_O_Sn.
  apply IHs => i ; rewrite size_compat /= => Hi ; apply (H (S i)) ; 
  rewrite size_compat /= ; apply lt_n_S, Hi.
Qed.

Lemma sorted_head (s : seq R) i : 
  sorted Rle s -> (i < size s)%nat -> forall x0, head x0 s <= nth x0 s i.
Proof.
  case: s => [| h s].
   move => _ Hi ; by apply lt_n_O in Hi.
  elim: s h i => [| h0 s IH] h i Hs Hi x0.
    apply lt_n_Sm_le, le_n_O_eq in Hi ; rewrite -Hi ; apply Rle_refl.
  case: i Hi => [| i] Hi.
  apply Rle_refl.
  apply Rle_trans with (r2 := head x0 (h0::s)).
  apply Hs.
  apply IH.
  apply Hs.
  apply lt_S_n, Hi.
Qed.

Lemma sorted_incr (s : seq R) i j : sorted Rle s -> (i <= j)%nat -> (j < size s)%nat
  -> forall x0, nth x0 s i <= nth x0 s j.
Proof.
  elim: i j s => [| i IH] j s Hs Hij Hj x0.
  rewrite nth0 ; by apply sorted_head.
  case: j Hij Hj => [| j] Hij Hj.
  by apply le_Sn_O in Hij.
  case: s Hs Hj => [| h s] Hs Hj.
  by apply lt_n_O in Hj.
  apply (IH j s) with (x0 := x0) => //.
  case: (s) Hs => {s Hj} [| h0 s] Hs ; apply Hs.
  apply le_S_n, Hij.
  apply le_S_n, Hj.
Qed.

Lemma sorted_last (s : seq R) i : 
  sorted Rle s -> (i < size s)%nat -> forall x0, nth x0 s i <= last x0 s.
Proof.
  move => Hs Hi x0 ; rewrite -nth_last.
  case: s Hi Hs => [| h s] Hi Hs //.
  by apply lt_n_O in Hi.
  apply sorted_incr => //.
  intuition.
Qed.

(** ** from SF_seq to StepFun *)

Lemma ad_SF_compat (s : SF_seq) (pr : SF_sorted Rle s) : 
  adapted_couple (SF_fun s 0) (head 0 (SF_lx s)) (last 0 (SF_lx s))
    (seq2Rlist (SF_lx s)) (seq2Rlist (SF_ly s)).
Proof.
(* head and last *)
  have H : ((head 0 (SF_lx s)) <= (last 0 (SF_lx s))).
    move: pr ; rewrite /SF_sorted.
    case: (SF_lx s) => {s} [| h s] Hs.
    apply Rle_refl.
    rewrite -nth0 ; apply sorted_last => // ; apply lt_O_Sn.
  rewrite /adapted_couple ?nth_compat ?size_compat ?nth0 ?nth_last 
  /Rmin /Rmax ?SF_size_lx ?SF_size_ly ;
  case: (Rle_dec (head 0 (SF_lx s)) (last 0 (SF_lx s))) => // {H} _ ; intuition.
(* sorted *)
  apply sorted_compat => //.
(* adapted *)
  move: i pr H ; apply SF_cons_dec with (s := s) 
    => {s} [x0 | h s] i Hs Hi x [Hx0 Hx1].
    by apply lt_n_O in Hi.
  rewrite /SF_fun ?SF_size_cons ?nth_compat -?SF_size_lx ?SF_lx_cons in Hi, Hx0, Hx1 |- *.
  move: h i x {3}(0) Hs Hi Hx0 Hx1 ; apply SF_cons_ind with (s := s) 
    => {s} [x1 | h0 s IH] h ; case => [| i ] x x0 Hs Hi Hx0 Hx1 //= ; case: Rlt_dec => Hx' //.
  contradict Hx' ; apply Rle_not_lt, Rlt_le, Hx0.
  case: Rle_dec => Hx'' // ; contradict Hx'' ; apply Rlt_le, Hx1.
  rewrite /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
  rewrite /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
  contradict Hx' ; apply Rle_not_lt, Rlt_le, Hx0.
  case: Rlt_dec => Hx'' //.
  contradict Hx' ; apply Rle_not_lt, Rlt_le, Rle_lt_trans with (2 := Hx0) ;
  have Hi' : (S i < size (SF_lx (SF_cons h (SF_cons h0 s))))%nat ; 
  [ rewrite ?SF_lx_cons /= in Hi |-* ; apply lt_trans with (1 := Hi), lt_n_Sn | ] ;
  apply (sorted_head (SF_lx (SF_cons h (SF_cons h0 s))) (S i) Hs Hi' 0).
  apply (IH h0 i x (snd h)) => //.
  apply Hs.
  rewrite ?SF_lx_cons /= in Hi |-* ; apply lt_S_n, Hi.
Qed.

Definition SF_compat_le (s : @SF_seq R) (pr : SF_sorted Rle s) : 
  StepFun (head 0 (SF_lx s)) (last 0 (SF_lx s)).
Proof.
  exists (SF_fun s 0) ; exists (seq2Rlist (SF_lx s)) ; exists (seq2Rlist (SF_ly s)).
  by apply ad_SF_compat.
Defined.

Lemma RInt_compat (s : SF_seq) (pr : SF_sorted Rle s) :
  RInt_seq s Rplus Rmult 0 = RiemannInt_SF (SF_compat_le s pr).
Proof.
  rewrite /RiemannInt_SF ; case: Rle_dec => // [_ | H].
  move: pr ; apply SF_cons_ind with (s := s) => {s} [x0 | h s IH] pr //=.
  rewrite /= -IH /RInt_seq /= => {IH}.
  by apply SF_cons_dec with (s := s).
  apply pr.
  contradict H ; rewrite -nth_last -nth0 ; move: (le_refl (ssrnat.predn (size (SF_lx s)))) ;
  elim: {1 3}(ssrnat.predn (size (SF_lx s))) => /= [| i IH] Hi.
  apply Rle_refl.
  apply Rle_trans with (1 := IH (le_trans _ _ _ (le_n_Sn i) Hi)), (sorted_nth Rle) ;
  intuition.
Qed.

(** Chasles Theorem *)

Fixpoint seq_cut_down {T : Type} (s : seq (R*T)) (x : R) (x0 : T) : seq (R*T) :=
  match s with
    | [::] => [:: (x,x0)]
    | h :: t => 
        match Rle_dec (fst h) x with
          | right _ => [:: (x,snd h)]
          | left _ => h :: (seq_cut_down t x (snd h))
        end
  end.
Fixpoint seq_cut_up {T : Type} (s : seq (R*T)) (x : R) (x0 : T) : seq (R*T) :=
  match s with
    | [::] => [:: (x,x0)]
    | h :: t => 
        match Rle_dec (fst h) x with
          | right _ => (x,x0)::h::t
          | left _ => seq_cut_up t x (snd h)
        end
  end.

Lemma seq_cut_correct {T : Type} (s : seq (R*T)) (x : R) (x0 : T) :
  belast (seq_cut_down s x x0) ++ behead (seq_cut_up s x x0) = s.
Proof.
  case: s => [ | h0 s] //= ; case: Rle_dec => H0 //=.
  elim: s h0 H0 => [ | h1 s IH] h0 H0 //= ; case: Rle_dec => H1 //=.
  by rewrite (IH h1).
Qed.

Lemma seq_cut_up_head {T : Type} (s : seq (R*T)) x x0 z :
  fst (head z (seq_cut_up s x x0)) = x.
Proof.
    elim: s x x0 ; simpl ; intuition.
    case: Rle_dec => //= H.
Qed.
Lemma seq_cut_up_behead {T : Type} (s : seq (R*T)) x x0 x1 : 
  behead (seq_cut_up s x x0) = behead (seq_cut_up s x x1).
Proof.
  elim: s x x0 x1 ; simpl ; intuition.
  case: Rle_dec => //= H.
Qed.
  

Definition SF_cut_down {T : Type} (x0 : T) (sf : @SF_seq T) (x : R) :=
  let s := seq_cut_down ((SF_h sf,x0) :: (SF_t sf)) x x0 in
  mkSF_seq (fst (head (SF_h sf,x0) s)) (behead s).
Definition SF_cut_up {T : Type} (x0 : T) (sf : @SF_seq T) (x : R) :=
  let s := seq_cut_up ((SF_h sf,x0) :: (SF_t sf)) x x0 in
  mkSF_seq (fst (head (SF_h sf,x0) s)) (behead s).

Lemma SF_cut_up_head {T : Type} (x0 : T) (sf : @SF_seq T) (x : R) :
  SF_h (SF_cut_up x0 sf x) = x.
Proof.
  rewrite /SF_cut_up ; case: sf => h0 sf /=.
  case: Rle_dec => //=.
  elim: sf h0 x0 (h0, x0) => [ | h1 sf IH] h0' h0 x0 H0 //=.
  case: Rle_dec => //= H1 ;
  by apply IH with (p := x0) (x0 := snd h1) (h0 := fst h1).
Qed.

Lemma SF_Chasles x0 (s : SF_seq) x :
  (SF_h s <= x <= fst (last (SF_h s,x0) (SF_t s))) ->
  RInt_seq s Rplus Rmult 0 = 
  (RInt_seq (SF_cut_down x0 s x) Rplus Rmult 0) 
  + (RInt_seq (SF_cut_up x0 s x) Rplus Rmult 0).
Proof.
  rename x0 into z0.
  apply SF_cons_ind with (s := s) => {s} /= [ x0 | [x0 y0] s IH] /= Hx.
  rewrite (Rle_antisym _ _ (proj1 Hx) (proj2 Hx)).
  move: (Rle_refl x).
  rewrite /SF_cut_down /SF_cut_up /= ; case: Rle_dec => //= _ _.
  rewrite /RInt_seq /= ; ring.
  rewrite -!(last_map (@fst R R)) /= -!unzip1_fst in IH, Hx.
  move: (fun Hx1 => IH (conj Hx1 (proj2 Hx))) => {IH}.
  rewrite /SF_cut_down /SF_cut_up /= ; 
  case: (Rle_dec x0 _) (proj1 Hx) => //= Hx0 _.
  case: (Rle_dec (SF_h s) x) => //= Hx1 IH.
  move: (IH Hx1) => {IH} IH.
  rewrite (RInt_seq_cons (x0,y0)) 
    (RInt_seq_cons (x0,y0) (mkSF_seq (SF_h s) (seq_cut_down (SF_t s) x y0))) 
    IH /= => {IH}.
  rewrite Rplus_assoc ; apply f_equal.
  rewrite ?seq_cut_up_head.
  move: (proj2 Hx) Hx1 => {Hx} ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx Hx1.
  rewrite /RInt_seq /= ; rewrite (Rle_antisym _ _ Hx Hx1) ; ring.
  by case: Rle_dec.
  clear IH.
  rewrite RInt_seq_cons (RInt_seq_cons (x,y0) s) {2}/RInt_seq /=.
  ring.
Qed.

(** * SF_seq and StepFun *)

Lemma StepFun_bound {a b : R} (f : StepFun a b) :
  exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
  case: f => /= f [lx [ly [Hsort [Hhead [Hlast [Hsize Hval]]]]]];
  rename a into a0 ; rename b into b0 ; set a := Rmin a0 b0 ; set b := Rmax a0 b0 ;
  set Rl_max := fun x0 => fix f l := match l with 
    | RList.nil => x0 
    | RList.cons h t => Rmax h (f t)
  end ;
  set f_lx := (fix app l := match l with
    | RList.nil => RList.nil
    | RList.cons h t => RList.cons (f h) (app t)
  end) lx ;
  set M_f_lx := Rl_max (f 0) f_lx ;
  set M_ly := Rl_max 0 ly.
  exists (Rmax M_f_lx M_ly) => x [Hx Hx'].
  rewrite /M_f_lx /f_lx ;
  case: lx Hsort Hhead Hlast Hsize Hval {f_lx M_f_lx}.
(* lx = [::] *)
  move => _ _ _ H ; contradict H ; apply O_S.
  move => h l ; case: l h.
(* lx = [:: h] *)
  move => h _ Ha Hb _ _ ; simpl in Ha, Hb.
  rewrite /a -Ha in Hx ; rewrite /b -Hb in Hx'.
  rewrite (Rle_antisym _ _ Hx Hx') /= ; apply Rle_trans with (2 := RmaxLess1 _ _) ; 
  apply RmaxLess1.
(* lx = [:: h,h'::l] *)
  move => h l h' Hsort Hhead Hlast Hsize Hval.
  apply Rle_lt_or_eq_dec in Hx' ; case: Hx' => Hx'.
  have H : exists i : nat, (i < S (Rlength l))%nat /\
    (pos_Rl (RList.cons h' (RList.cons h l)) i) <= x 
    < (pos_Rl (RList.cons h' (RList.cons h l)) (S i)).
    rewrite /a -Hhead in Hx ; rewrite /b -Hlast in Hx'.
    elim: l h' h Hx Hx' Hsort {Hhead Hlast Hsize Hval} => [| h'' l IH] h' h Hx Hx' Hsort ; simpl in Hx, Hsort.
    case: (Rlt_le_dec x h) => H.
    exists O ; intuition.
    exists O => /= ; intuition.
    case: (Rlt_le_dec x h) => H.
    exists O => /= ; intuition.
    have H0 : ordered_Rlist (RList.cons h (RList.cons h'' l)).
    move => i Hi ; apply (Hsort (S i)) => /= ; apply lt_n_S, Hi.
    case: (IH _ _ H Hx' H0) => {IH} i Hi.
    exists (S i) ; split.
    simpl ; apply lt_n_S, Hi => /=.
    apply Hi.
  case: H => i [Hi [Ht Ht']].
  apply Rle_lt_or_eq_dec in Ht ; case: Ht => Ht.
  rewrite (Hval i Hi x).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  rewrite /M_ly ; case: (ly).
  apply Rle_refl.
  move => y ly' ; elim: ly' (i) y.
  move => i0 y ; case: i0 => //=.
  apply RmaxLess1.
  move => _; apply RmaxLess2.
  move => y ly' IH i0 y' ; case: i0.
  apply RmaxLess1.
  move => n ; apply Rle_trans with (1 := IH n y) ; apply RmaxLess2.
  split => //.
  rewrite -Ht ; apply Rle_trans with (2 := RmaxLess1 _ _).
  case: (i).
  apply RmaxLess1.
  move => n ; elim: n (h) (h') (l).
  move => h0 h'0 l0 ; apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
  move => n IH h0 h'0 l0.
  case: l0.
  apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess2.
  move => h''0 l0 ; apply Rle_trans with (1 := IH h''0 h0 l0), RmaxLess2.
  rewrite Hx' /b -Hlast.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  elim: (l) (h') (h) => [| h''0 l0 IH] h'0 h0.
  apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
  apply Rle_trans with (1 := IH h0 h''0), RmaxLess2.
Qed.

Lemma Riemann_integrable_bound (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
  move => pr ;
  case (pr (mkposreal _ Rlt_0_1)) => {pr} phi [psi [pr _]] ;
  case: (StepFun_bound phi) => M_phi H_phi ;
  case: (StepFun_bound psi) => M_psi H_psi ;
  exists (M_psi + M_phi) => x Hx.
  apply Rle_trans with (2 := Rplus_le_compat _ _ _ _ (H_psi _ Hx) (H_phi _ Hx)).
  have: (f x = (f x - phi x) + phi x) ; first by ring.
  move => -> ; apply Rplus_le_compat_r, Rle_trans with (1 := Rle_abs _), pr, Hx.
Qed.

