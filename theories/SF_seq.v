Require Import Reals.
Require Import ssreflect seq.

Open Scope R_scope.

(** * more in sdtlib and ssreflect *)
(** Notations *)
Lemma SSR_leq (n m : nat) : ssrbool.is_true (ssrnat.leq n m) <-> (n <= m)%nat.
Proof.
  set H := (@ssrnat.leP n m) ; case: H => H //=.
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
(** zip and unzip *)
Lemma size_unzip1 {T T0 : Type} (s : seq (T * T0)) : size (unzip1 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
Lemma size_unzip2 {T T0 : Type} (s : seq (T * T0)) : size (unzip2 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
(** belast *)
Definition belast {T : Type} (s : seq T) :=
  match s with
    | [::] => [::]
    | h :: s => belast h s
  end.
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

(** ** SF_sorted *)

Definition SF_sorted {T : Type} (Ord : R -> R -> Prop) (s : @SF_seq T) :=
  sorted Ord (SF_lx s).

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

Lemma SF_fun_incr {T : Type} (s : SF_seq) (x0 : T) (x : R) (i : nat) :
  SF_sorted Rle s -> ((S i < SF_size s)%nat -> 
  nth 0 (SF_lx s) i <= x < nth 0 (SF_lx s) (S i) -> SF_fun s x0 x = nth x0 (SF_ly s) i) 
  /\ (S i = SF_size s -> nth 0 (SF_lx s) i <= x <= nth 0 (SF_lx s) (S i) -> 
      SF_fun s x0 x = nth x0 (SF_ly s) i).
Proof.
  move: i ; apply SF_cons_dec with (s := s) => {s} [x1 | h s].
(* s = SF_nil _ *)
  split => // Hi ; by apply lt_n_O in Hi.
  move: h ; apply SF_cons_ind with (s := s) => {s} [x1 | h s IH] h0 ; 
  case => [| i] Hs ; split => Hi [Hax Hxb].
(* s = SF_cons _ (SF_nil _) *)
(* * i = 0 *)
  rewrite /SF_size /= in Hi ; by apply lt_irrefl in Hi.
  simpl in Hax,Hxb ; rewrite /SF_fun /=.
  case: Rlt_dec => [H|_].
    contradict H ; by apply Rle_not_lt.
  case: Rle_dec => //.
(* * i = S _ *)
  rewrite /SF_size /= in Hi ; by apply lt_S_n, lt_n_O in Hi.
  rewrite /SF_size /= in Hi ; by apply eq_add_S in Hi.
(* s = SF_cons _ (SF_cons _ _) *)
(* * i = 0 *)
  simpl in Hax,Hxb ; rewrite /SF_fun /=.
  case: Rlt_dec => [H|_].
    contradict H ; by apply Rle_not_lt.
  case: Rlt_dec => //.
(* * i = S _ *)
  rewrite /SF_size /= in Hi ; by apply eq_add_S in Hi.
  rewrite /= -(proj1 (IH h i (proj2 Hs))) => //.
  have H : ~(x < fst h).
    apply Rle_not_lt, Rle_trans with (2 := Hax).
    elim: (i) Hi => {i Hax Hxb IH} => [|i IH] Hi.
    apply Rle_refl.
    have Hi' : (S (S i) < SF_size (SF_cons h0 (SF_cons h s)))%nat ;
      [intuition | ] ;
    apply Rle_trans with (1 := IH Hi') ; apply (proj1 (sorted_nth _ _)) => //.
    rewrite /SF_size ?SF_lx_cons /= size_unzip1 in Hi, Hi' |- * ; intuition.
  rewrite /SF_fun /= ;
  case: Rlt_dec => [H0| _].
  contradict H0 ; apply Rle_not_lt, Rle_trans with (2 := Rnot_lt_le _ _ H), Hs.
  case: Rlt_dec => //.
  rewrite SF_size_cons in Hi ; intuition.
  rewrite /= -(proj2 (IH h i (proj2 Hs))) => //.
  have H : ~(x < fst h).
    apply Rle_not_lt, Rle_trans with (2 := Hax).
    have : (S (S i) <= SF_size (SF_cons h0 (SF_cons h s)))%nat ; 
      [rewrite Hi ; apply le_refl| move => {Hi} Hi].
    elim: (i) Hi => {i Hax Hxb IH} => [|i IH] Hi.
    apply Rle_refl.
    have Hi' : (S (S i) <= SF_size (SF_cons h0 (SF_cons h s)))%nat ;
      [intuition | ] ;
    apply Rle_trans with (1 := IH Hi') ; apply (proj1 (sorted_nth _ _)) => //.
    rewrite /SF_size ?SF_lx_cons /= size_unzip1 in Hi, Hi' |- * ; intuition.
  rewrite /SF_fun /= ;
  case: Rlt_dec => [H0| _].
  contradict H0 ; apply Rle_not_lt, Rle_trans with (2 := Rnot_lt_le _ _ H), Hs.
  case: Rlt_dec => //.
  rewrite SF_size_cons in Hi ; intuition.
Qed.

(** * Build SF_seq and SF_fun *)

(** ** SF_seq *)

Definition SF_seq_f1 {T : Type} (f1 : R -> T) (P : seq R) (x0 : R) : SF_seq :=
  mkSF_seq (head x0 P) (behead (pairmap (fun x y => (y, f1 x)) x0 P)).
Definition SF_seq_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) (x0 : R) : SF_seq :=
  mkSF_seq (head x0 P) (behead (pairmap (fun x y => (y, f2 x y)) x0 P)).

Lemma SF_size_f1 {T : Type} (f1 : R -> T) P x0 :
  SF_size (SF_seq_f1 f1 P x0) = pred (size P).
Proof.
  case: P => [| h P] //= ; by rewrite /SF_size /= size_pairmap.
Qed.
Lemma SF_size_f2 {T : Type} (f2 : R -> R -> T) P x0 :
  SF_size (SF_seq_f2 f2 P x0) = pred (size P).
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

(** ** SF_fun *)

Definition SF_fun_f1 {T : Type} (f1 : R -> T) (P : seq R) (x0 : R*T) x :=
  SF_fun (SF_seq_f1 f1 P (fst x0)) (snd x0) x.
Definition SF_fun_f2 {T : Type} (f2 : R -> R -> T) (P : seq R) (x0 : R*T) x :=
  SF_fun (SF_seq_f2 f2 P (fst x0)) (snd x0) x.
