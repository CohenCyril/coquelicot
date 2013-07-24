Require Import Reals.
Require Import Rcomplements Rbar Lub.
Require Import ssreflect seq ssrbool.

Open Scope R_scope.

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

Definition SF_last {T : Type} x0 (s : SF_seq) : (R*T) :=
  last (SF_h s,x0) (SF_t s).
Definition SF_belast {T : Type} (s : SF_seq) : SF_seq :=
  mkSF_seq (SF_h s) (Rcomplements.belast (SF_t s) : seq (R*T)).


Definition SF_head {T : Type} (x0 : T) (s : @SF_seq T) := (SF_h s, head x0 (SF_ly s)).
Definition SF_behead {T : Type} (s : @SF_seq T) :=
  mkSF_seq (head (SF_h s) (unzip1 (SF_t s))) (behead (SF_t s)).

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
  SF_ly (SF_seq_f1 f1 P x0) = Rcomplements.belast (map f1 P).
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
  Rcomplements.belast (seq_cut_down s x x0) ++ behead (seq_cut_up s x x0) = s.
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

(** * Uniform partition *)

Definition unif_part (a b : R) (n : nat) : seq R := 
  mkseq (fun i => a + (INR i) * (b - a) / (INR n + 1)) (S (S n)).

Lemma unif_part_bound (a b : R) (n : nat) : 
  unif_part a b n = rev (unif_part b a n).
Proof.
  apply (@eq_from_nth R 0) ; rewrite ?size_rev ?size_mkseq => // ;
  move => i Hi ; apply SSR_leq in Hi.
  rewrite nth_rev ?SSR_minus ?size_mkseq.
  2: now apply SSR_leq.
  rewrite ?nth_mkseq.
  3: now apply SSR_leq.
  rewrite minus_INR ?S_INR => // ; field.
  apply Rgt_not_eq, INRp1_pos.
  apply SSR_leq, INR_le ; rewrite ?S_INR minus_INR ?S_INR => //.
  apply Rminus_le_0 ; ring_simplify.
  apply pos_INR.
Qed.

Lemma unif_part_sort (a b : R) (n : nat) : a <= b -> sorted Rle (unif_part a b n).
Proof.
  move => Hab ; apply sorted_nth => i Hi x0 ; 
  rewrite ?size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ;
  [ |apply SSR_leq ; intuition | apply SSR_leq ; intuition ].
  apply Rminus_le_0 ; field_simplify ; 
  [| apply Rgt_not_eq ; intuition] ; rewrite ?Rdiv_1 ;
  apply Rdiv_le_0_compat ; intuition.
  rewrite Rplus_comm ; by apply (proj1 (Rminus_le_0 _ _)).
Qed.

Lemma unif_part_nat (a b : R) (n : nat) (x : R) : (a <= x <= b) -> 
  {i : nat |
  nth 0 (unif_part a b n) i <= x < nth 0 (unif_part a b n) (S i) /\
  (S (S i) < size (unif_part a b n))%nat} +
  {nth 0 (unif_part a b n) (n) <= x <=
   nth 0 (unif_part a b n) (S n)}.
Proof.
  move: (sorted_dec (unif_part a b n) 0 x) => Hdec Hx.
  have Hs : sorted Rle (unif_part a b n) ;
    [ apply unif_part_sort, Rle_trans with (r2 := x) ; intuition 
    | move: (Hdec Hs) => {Hdec Hs} Hdec].
  have Hx' : (head 0 (unif_part a b n) <= x <= last 0 (unif_part a b n)).
    rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= /Rdiv.
    ring_simplify (a + 0 * (b - a) * / (INR n + 1)).
    field_simplify (a + (INR n + 1) * (b - a) * / (INR n + 1)).
    by rewrite Rdiv_1.
    apply Rgt_not_eq, INRp1_pos.
  case: (Hdec Hx') => {Hdec Hx'} [[i Hi]|Hi].
  left ; by exists i.
  right ; rewrite size_mkseq /= in Hi ; intuition.
  by rewrite -minus_n_O in H1.
Qed.

(** * Particluar step functions using unif_part *)

Definition SF_val_ly (f : R -> R) (a b : R) (n : nat) : seq R :=
  behead (pairmap (fun x y => f ((x+y)/2)) 0 (unif_part a b n)).
Definition SF_val_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (fun x y => f ((x+y)/2)) (unif_part a b n) 0.
Definition SF_val_fun (f : R -> R) (a b : R) (n : nat) (x : R) : R :=
  SF_fun_f2 (fun x y => f ((x+y)/2)) (unif_part a b n) (0,0) x.

Lemma SF_val_ly_bound (f : R -> R) (a b : R) (n : nat) :
  SF_val_ly f a b n = rev (SF_val_ly f b a n).
Proof.
  rewrite /SF_val_ly (unif_part_bound b a).
  case: (unif_part a b n) => [| h s] // ; elim: s h => [| h0 s IH] h //=.
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
      (seq2Rlist (unif_part a b n)) (seq2Rlist (SF_val_ly f a b n)))
  /\ (~(a <= b) -> adapted_couple (SF_val_fun f b a n) a b 
      (seq2Rlist (unif_part b a n)) (seq2Rlist (SF_val_ly f b a n))).
Proof.
  wlog : a b / (a <= b) => Hw.
    split ; case: (Rle_dec a b) => // Hab _.
    by apply Hw.
    apply StepFun_P2 ; apply Hw ; by apply Rlt_le, Rnot_le_lt.
  split ; case: (Rle_dec a b) => // {Hw} Hab _.
  
  have : (a = head 0 (SF_lx (SF_val_seq f a b n))) ; 
  [rewrite SF_lx_f2 /= ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  pattern b at 3 ; replace b with (last 0 (SF_lx (SF_val_seq f a b n))).
  replace (unif_part a b n) 
    with (head 0 (unif_part a b n) :: behead (unif_part a b n)) by intuition ;
  rewrite -(SF_lx_f2 (fun x y => f ((x+y)/2))).
  rewrite /SF_val_ly -SF_ly_f2.
  apply (ad_SF_compat (SF_val_seq f a b n)).
  by apply SF_sorted_f2, unif_part_sort.
  rewrite SF_lx_f2 ;
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n)) 
    with (unif_part a b n) by auto.
    rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ;
    field ; apply Rgt_not_eq, INRp1_pos.
Qed.

Definition sf_SF_val_fun (f : R -> R) (a b : R) (n : nat) : StepFun a b.
Proof.
  case : (Rle_dec a b) => Hab.
  exists (SF_val_fun f a b n) ;
  exists (seq2Rlist (unif_part a b n)) ;
  exists (seq2Rlist (SF_val_ly f a b n)) ; by apply ad_SF_val_fun.
  exists (SF_val_fun f b a n) ;
  exists (seq2Rlist (unif_part b a n)) ;
  exists (seq2Rlist (SF_val_ly f b a n)) ; by apply ad_SF_val_fun.
Defined.
Lemma SF_val_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (sf_SF_val_fun f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (unif_part a b n)
    | right _ => seq2Rlist (unif_part b a n)
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
    match (unif_part_nat a b n x Hx) with
      | inleft H => f (a + (INR (projT1 H) + /2) * (b-a) / (INR n + 1))
      | inright _ => f (a + (INR n + /2) * (b-a) / (INR n + 1))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] /=.
(* i < 2^n - 1 *)
  rewrite /SF_val_fun /SF_fun_f2.
  replace (a + (INR i + /2) * (b - a) / (INR n+1)) 
    with ((nth 0 (unif_part a b n) i + nth 0 (unif_part a b n) (S i)) / 2) ;
    [ | rewrite size_mkseq in Hi ; rewrite ?nth_mkseq ?S_INR ; 
    [field ; apply Rgt_not_eq | apply SSR_leq | apply SSR_leq ] ; intuition].
  case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
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
    with ((nth 0 (unif_part a b n) (n) + nth 0 (unif_part a b n) (S n)) / 2) ;
    [ | rewrite ?nth_mkseq ?minus_INR ?S_INR /= ; 
    [field ; apply Rgt_not_eq | 
    apply SSR_leq | apply SSR_leq ] ; intuition].
  suff : (1 < size (unif_part a b n))%nat.
  move: x Hx ; have: (n = size (unif_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | ].
    move => {2 4 8 10}->.
  rewrite /SF_val_fun /SF_fun_f2.
  case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s Hs x Hx /= Hi] .
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

(** * pointed subdivision *)

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

Definition seq_step (s : seq R) := 
  foldr Rmax 0 (pairmap (fun x y => Rabs (Rminus y x)) (head 0 s) (behead s)).

(** * Upper and lower step functions *)

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

(** SF_sup and SF_inf *)

Definition SF_sup_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Sup_fct f) (unif_part a b n) 0.
Lemma SF_sup_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_sup_seq f a b n) = unif_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_sup_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_sup_seq f a b n) = behead (pairmap (Sup_fct f) 0 (unif_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Definition SF_inf_seq (f : R -> R) (a b : R) (n : nat) : SF_seq :=
  SF_seq_f2 (Inf_fct f) (unif_part a b n) 0.
Lemma SF_inf_lx (f : R -> R) (a b : R) (n : nat) :
  SF_lx (SF_inf_seq f a b n) = unif_part a b n.
Proof.
  by apply SF_lx_f2.
Qed.
Lemma SF_inf_ly (f : R -> R) (a b : R) (n : nat) :
  SF_ly (SF_inf_seq f a b n) = behead (pairmap (Inf_fct f) 0 (unif_part a b n)).
Proof.
  by apply SF_ly_f2.
Qed.

Lemma SF_sup_bound (f : R -> R) (a b : R) (n : nat) :
  SF_rev (SF_sup_seq f a b n) = SF_sup_seq f b a n.
Proof.
  rewrite /SF_sup_seq unif_part_bound => //.
  rewrite SF_rev_f2 ?revK //.
  move => x y ; apply Sup_fct_bound.
Qed.
Lemma SF_inf_bound (f : R -> R) (a b : R) (n : nat) : 
  SF_rev (SF_inf_seq f a b n) = SF_inf_seq f b a n.
Proof.
  rewrite /SF_inf_seq unif_part_bound => //.
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
    match (unif_part_nat a b n x Hx) with
      | inleft H => Sup_fct f (nth 0 (unif_part a b n) (projT1 H)) 
          (nth 0 (unif_part a b n) (S (projT1 H)))
      | inright _ => Sup_fct f (nth 0 (unif_part a b n) (n)) 
          (nth 0 (unif_part a b n) (S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_sup_fun /SF_sup_seq ; case: Rle_dec => // _.
  case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl projT1.
(* i < n *)
  case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
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
  suff : (1 < size (unif_part a b n))%nat.
  have: (n = size (unif_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | move => {3 5 8 10}->].
  case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
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
    match (unif_part_nat a b n x Hx) with
      | inleft H => Inf_fct f (nth 0 (unif_part a b n) (projT1 H)) 
          (nth 0 (unif_part a b n) (S (projT1 H)))
      | inright _ => Inf_fct f (nth 0 (unif_part a b n) (n)) 
          (nth 0 (unif_part a b n) (S n))
    end.
Proof.
  have Hab : (a <= b) ; [by apply Rle_trans with (1 := proj1 Hx), Hx | ].
  rewrite /SF_inf_fun /SF_inf_seq ; case: Rle_dec => // _.
  case: unif_part_nat => {Hx} [ [ i [Hx Hi] ] | Hx] ; simpl projT1.
(* i < n *)
  case: (unif_part a b n) (unif_part_sort a b n Hab) i Hi x Hx => {a b Hab n} [| h s] Hs /= i Hi.
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
  suff : (1 < size (unif_part a b n))%nat.
  have: (n = size (unif_part a b n) - 2)%nat ;
    [ rewrite size_mkseq ; intuition | move => {3 5 8 10}->].
  case: (unif_part a b n) (unif_part_sort a b n Hab) => {a b Hab n} [| h s] Hs /= Hi.
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
      (seq2Rlist (unif_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_sup_fun f a b n x)) a b 
      (seq2Rlist (unif_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n))))).
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
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n)) 
    with (unif_part a b n) by intuition.
    by apply unif_part_sort.
  have: a = head 0 (unif_part a b n) ; 
  [ simpl ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have: b = last 0 (unif_part a b n) ; 
  [ rewrite -nth_last size_mkseq nth_mkseq ?S_INR//= ; 
  field ; apply Rgt_not_eq ; intuition | move => {3}->].
  replace (behead
    (pairmap (fun x y : R => real (Sup_fct f x y)) 0 (unif_part a b n)))
    with (SF_ly (SF_map real (SF_sup_seq f a b n))).
  replace (unif_part a b n) 
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
  exists (seq2Rlist (unif_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n)))) ;
  by apply ad_SF_sup_r.
  exists (seq2Rlist ((unif_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n)))) ;
  by apply ad_SF_sup_r.
Defined.
Lemma SF_sup_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_sup_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (unif_part a b n)
    | right _ => seq2Rlist (unif_part b a n)
  end.
Proof.
  rewrite /SF_sup_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_sup_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_sup_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Sup_fct f x y)) 0 (unif_part b a n))))
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
      (seq2Rlist (unif_part a b n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n)))))
  /\ (~(a <= b) -> adapted_couple (fun x => real (SF_inf_fun f a b n x)) a b 
      (seq2Rlist (unif_part b a n)) 
      (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n))))).
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
    replace (head 0 (unif_part a b n) :: behead (unif_part a b n)) 
    with (unif_part a b n) by intuition.
    by apply unif_part_sort.
  have: a = head 0 (unif_part a b n) ; 
  [ simpl ; field ; apply Rgt_not_eq ; intuition | move => {2}->].
  have: b = last 0 (unif_part a b n) ; 
  [ rewrite -nth_last size_mkseq nth_mkseq ?S_INR //= ; 
  field ; apply Rgt_not_eq ; intuition | move => {3}->].
  replace (behead
    (pairmap (fun x y : R => real (Inf_fct f x y)) 0 (unif_part a b n)))
    with (SF_ly (SF_map real (SF_inf_seq f a b n))).
  replace (unif_part a b n) 
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
  exists (seq2Rlist (unif_part a b n)) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n)))) ;
  by apply ad_SF_inf_r.
  exists (seq2Rlist ((unif_part b a n))) ;
  exists (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n)))) ;
  by apply ad_SF_inf_r.
Defined.
Lemma SF_inf_subdiv (f : R -> R) (a b : R) (n : nat) :
  subdivision (SF_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => seq2Rlist (unif_part a b n)
    | right _ => seq2Rlist (unif_part b a n)
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.
Lemma SF_inf_subdiv_val (f : R -> R) (a b : R) (n : nat) :
  subdivision_val (SF_inf_r f a b n) = 
  match (Rle_dec a b) with 
    | left _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part a b n))))
    | right _ => (seq2Rlist (behead (pairmap (fun x y => real (Inf_fct f x y)) 0 (unif_part b a n))))
  end.
Proof.
  rewrite /SF_inf_r ; case: (Rle_dec a b) => Hab //.
Qed.

Lemma SF_inf_r_bound (f : R -> R) (a b : R) (n : nat) :
  forall x, SF_inf_r f a b n x = SF_inf_r f b a n x.
Proof.
  move => x /= ; by rewrite SF_inf_fun_bound.
Qed.

