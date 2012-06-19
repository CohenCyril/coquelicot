Require Import Reals.
Require Import ssreflect ssrbool seq.
Require Import Rcomplements Locally Derive RInt Differential Integral Continuity.

Fixpoint Rn n T :=
  match n with
  | O => T
  | S n => R -> Rn n T
  end.

Inductive bop :=
  | Eplus
  | Emult.

Inductive uop :=
  | Eopp.

Inductive expr :=
  | Var : nat -> expr
  | AppExt : forall k, Rn k R -> seq expr -> expr
  | App : expr -> expr -> expr
  | Subst : expr -> expr -> expr
  | Cst : R -> expr
  | Binary : bop -> expr -> expr -> expr
  | Unary : uop -> expr -> expr
  | Int : expr -> expr -> expr -> expr.

Section ExprInduction.

Hypothesis P : expr -> Prop.
Hypothesis P_Var : forall n, P (Var n).
Hypothesis P_AppExt : forall k f le, foldr (fun e acc  => P e /\ acc) True le -> P (AppExt k f le).
Hypothesis P_App : forall e1 e2, P e1 -> P e2 -> P (App e1 e2).
Hypothesis P_Subst : forall e1 e2, P e1 -> P e2 -> P (Subst e1 e2).
Hypothesis P_Cst : forall r, P (Cst r).
Hypothesis P_Binary : forall o e1 e2, P e1 -> P e2 -> P (Binary o e1 e2).
Hypothesis P_Unary : forall o e, P e -> P (Unary o e).
Hypothesis P_Int : forall f e1 e2, P f -> P e1 -> P e2 -> P (Int f e1 e2).

Fixpoint expr_ind' (e : expr) : P e :=
  match e return P e with
  | Var n => P_Var n
  | AppExt k f le => P_AppExt k f le
    ((fix expr_ind'' (le : seq expr) : foldr (fun e acc => P e /\ acc) True le :=
       match le return foldr (fun e acc => P e /\ acc) True le with
       | nil => I
       | cons h q => conj (expr_ind' h) (expr_ind'' q)
       end) le)
  | App e1 e2 => P_App e1 e2 (expr_ind' e1) (expr_ind' e2)
  | Subst e1 e2 => P_Subst e1 e2 (expr_ind' e1) (expr_ind' e2)
  | Cst r => P_Cst r
  | Binary o e1 e2 => P_Binary o e1 e2 (expr_ind' e1) (expr_ind' e2)
  | Unary o e => P_Unary o e (expr_ind' e)
  | Int f e1 e2 => P_Int f e1 e2 (expr_ind' f) (expr_ind' e1) (expr_ind' e2)
  end.

End ExprInduction.

Fixpoint apply {T} p : Rn p T -> (nat -> R) -> T :=
  match p return Rn p T -> _ -> T with
  | O => fun (x : T) _ => x
  | S p => fun (f : Rn (S p) T) g => apply p (f (g p)) g
  end.

Lemma apply_ext :
  forall T k (f : Rn k T) g1 g2,
  (forall n, (n < k)%nat -> g1 n = g2 n) ->
  apply k f g1 = apply k f g2.
Proof.
intros T k f g1 g2 Hg.
revert f.
induction k.
easy.
simpl.
intros f.
rewrite Hg.
apply IHk.
intros n Hn.
apply Hg.
now apply lt_S.
apply lt_n_Sn.
Qed.

Fixpoint interp (l : seq R) (e : expr) : R :=
  match e with
  | Var n => nth R0 l n
  | AppExt k f le => apply k f (nth 0 (map (interp l) le))
  | App e1 e2 => interp ((interp l e2) :: l) e1
  | Subst e1 e2 => interp (set_nth R0 l 0 (interp l e2)) e1
  | Cst c => c
  | Binary o e1 e2 => match o with Eplus => Rplus | Emult => Rmult end (interp l e1) (interp l e2)
  | Unary o e => match o with Eopp => Ropp end (interp l e)
  | Int e1 e2 e3 => RInt (fun x => interp (x :: l) e1) (interp l e2) (interp l e3)
  end.

Inductive domain :=
  | Never : domain
  | Always : domain
  | Derivable : nat -> forall k, Rn k R -> seq expr -> domain
  | Continuous : nat -> expr -> domain
  | Continuous2 : nat -> nat -> expr -> domain
  | Integrable : expr -> expr -> expr -> domain
  | And : seq domain -> domain
  | Forall : expr -> expr -> domain -> domain
  | Forone : expr -> domain -> domain
  | Locally : nat -> domain -> domain
  | Locally2 : nat -> nat -> domain -> domain
  | ForallWide : nat -> expr -> expr -> domain -> domain.

Section DomainInduction.

Hypothesis P : domain -> Prop.
Hypothesis P_Never : P Never.
Hypothesis P_Always : P Always.
Hypothesis P_Derivable : forall n k f le, P (Derivable n k f le).
Hypothesis P_Continuous : forall n e, P (Continuous n e).
Hypothesis P_Continuous2 : forall m n e, P (Continuous2 m n e).
Hypothesis P_Integrable : forall f e1 e2, P (Integrable f e1 e2).
Hypothesis P_And : forall ld, foldr (fun d acc  => P d /\ acc) True ld -> P (And ld).
Hypothesis P_Forall : forall e1 e2 d, P d -> P (Forall e1 e2 d).
Hypothesis P_Forone : forall e d, P d -> P (Forone e d).
Hypothesis P_Locally : forall n d, P d -> P (Locally n d).
Hypothesis P_Locally2 : forall m n d, P d -> P (Locally2 m n d).
Hypothesis P_ForallWide : forall n e1 e2 d, P d -> P (ForallWide n e1 e2 d).

Fixpoint domain_ind' (d : domain) : P d :=
  match d return P d with
  | Never => P_Never
  | Always => P_Always
  | Derivable n k f le => P_Derivable n k f le
  | Continuous n e => P_Continuous n e
  | Continuous2 m n e => P_Continuous2 m n e
  | Integrable f e1 e2 => P_Integrable f e1 e2
  | And ld => P_And ld
    ((fix domain_ind'' (ld : seq domain) : foldr (fun d acc => P d /\ acc) True ld :=
       match ld return foldr (fun d acc => P d /\ acc) True ld with
       | nil => I
       | cons h q => conj (domain_ind' h) (domain_ind'' q)
       end) ld)
  | Forall e1 e2 d => P_Forall e1 e2 d (domain_ind' d)
  | Forone e d => P_Forone e d (domain_ind' d)
  | Locally n d => P_Locally n d (domain_ind' d)
  | Locally2 m n d => P_Locally2 m n d (domain_ind' d)
  | ForallWide n e1 e2 d => P_ForallWide n e1 e2 d (domain_ind' d)
  end.

End DomainInduction.

Fixpoint Derive_Rn_aux n (f : Rn (S n) R) x : Rn n R :=
  match n return Rn (S n) R -> Rn n R with
  | O => fun f => Derive (fun x => f x) x
  | S n => fun f y => Derive_Rn_aux n (fun x => f x y) x
  end f.

Fixpoint Derive_Rn n (f : Rn n R) i : Rn n R :=
  match n return Rn n R -> Rn n R with
  | O => fun _ => R0
  | S n => fun f x => if ssrnat.eqn n i then Derive_Rn_aux n f x else Derive_Rn n (f x) i
  end f.

Fixpoint ex_derive_Rn_aux n (f : Rn (S n) R) x : Rn n Prop :=
  match n return Rn (S n) R -> Rn n Prop with
  | O => fun f => ex_derive (fun x => f x) x
  | S n => fun f y => ex_derive_Rn_aux n (fun x => f x y) x
  end f.

Fixpoint ex_derive_Rn n (f : Rn n R) i : Rn n Prop :=
  match n return Rn n R -> Rn n Prop with
  | O => fun _ => True
  | S n => fun f x => if ssrnat.eqn n i then ex_derive_Rn_aux n f x else ex_derive_Rn n (f x) i
  end f.

Lemma Derive_Rn_correct :
  forall k f g v,
  apply k (ex_derive_Rn k f v) g ->
  is_derive (fun x => apply k f (fun i => if ssrnat.eqn i v then x else g i)) (g v) (apply k (Derive_Rn k f v) g).
Proof.
intros k f g.
induction k.
intros v _.
exact: derivable_pt_lim_const.
intros v.
simpl.
case E: (ssrnat.eqn k v).
2: apply IHk.
rewrite -(ssrnat.eqnP E).
intros Df.
apply (is_derive_ext (fun x => apply k (f x) g)).
intros t.
apply apply_ext.
intros n Hn.
case E': (ssrnat.eqn n k).
elim (lt_irrefl n).
now rewrite -(ssrnat.eqnP E') in Hn.
easy.
revert Df.
clear.
generalize (g k).
induction k.
simpl.
apply Derive_correct.
simpl.
intros Df.
apply IHk.
Qed.

Fixpoint interp_domain (l : seq R) (d : domain) : Prop :=
  match d with
  | Never => False
  | Always => True
  | Derivable n k f le => apply k (ex_derive_Rn k f n) (nth 0 (map (interp l) le))
  | Continuous n f => continuity_pt (fun x => interp (set_nth R0 l n x) f) (nth R0 l n)
  | Continuous2 m n f => continuity_2d_pt (fun x y => interp (set_nth R0 (set_nth R0 l n y) m x) f) (nth R0 l m) (nth R0 l n)
  | Integrable f e1 e2 => ex_RInt (fun x => interp (x :: l) f) (interp l e1) (interp l e2)
  | And ld => foldr (fun d acc => interp_domain l d /\ acc) True ld
  | Forall e1 e2 s =>
    let a1 := interp l e1 in let a2 := interp l e2 in
    forall t, Rmin a1 a2 <= t <= Rmax a1 a2 ->
    interp_domain (t :: l) s
  | Forone e s => interp_domain (interp l e :: l) s
  | Locally n s =>
    locally (fun x => interp_domain (set_nth R0 l n x) s) (nth R0 l n)
  | Locally2 m n s =>
    locally_2d (fun x y => interp_domain (set_nth R0 (set_nth R0 l n y) m x) s) (nth R0 l m) (nth R0 l n)
  | ForallWide n e1 e2 s =>
    let a1 := interp l e1 in let a2 := interp l e2 in
    exists d : posreal,
    forall t u, Rmin a1 a2 - d < t < Rmax a1 a2 + d -> Rabs (u - nth R0 l n) < d ->
    interp_domain (t :: set_nth R0 l n u) s
  end.

Fixpoint is_const (e : expr) n : bool :=
  match e with
  | Var v => negb (ssrnat.eqn v n)
  | AppExt k f le => foldr (fun v acc => andb (is_const v n) acc) true le
  | App f e => andb (is_const f (S n)) (is_const e n)
  | Subst f e => andb (orb (ssrnat.eqn n 0) (is_const f n)) (is_const e n)
  | Cst _ => true
  | Binary b e1 e2 => andb (is_const e1 n) (is_const e2 n)
  | Unary u e => is_const e n
  | Int f e1 e2 => andb (is_const f (S n)) (andb (is_const e1 n) (is_const e2 n))
  end.

Lemma is_const_correct :
  forall e n, is_const e n = true ->
  forall l x1 x2,
  interp (set_nth 0 l n x1) e = interp (set_nth 0 l n x2) e.
Proof.
induction e using expr_ind'.
(* *)
simpl => k Hk l x1 x2.
rewrite 2!nth_set_nth /=.
now rewrite -ssrnat.eqnE (ssrbool.negbTE Hk).
(* *)
simpl => n Hc l x1 x2.
apply apply_ext.
intros m _.
revert m.
induction le.
intros m.
now rewrite nth_nil.
apply andb_prop in Hc.
intros [|m].
simpl.
now apply H.
simpl.
apply IHle.
apply H.
apply Hc.
(* *)
simpl => n.
move /ssrbool.andP => [H1 H2] l x1 x2.
rewrite (IHe2 n H2 l x1 x2).
now apply: (IHe1 (S n) _ (interp (set_nth 0 l n x2) e2 :: l)).
(* *)
intros n.
simpl is_const.
move /ssrbool.andP => [H1 H2] l x1 x2.
change (interp (set_nth 0 (set_nth 0 l n x1) 0 (interp (set_nth 0 l n x1) e2)) e1 =
  interp (set_nth 0 (set_nth 0 l n x2) 0 (interp (set_nth 0 l n x2) e2)) e1).
move: H1.
replace (orb (ssrnat.eqn n 0) (is_const e1 n)) with
  (orb (ssrnat.eqn n 0) (andb (negb (ssrnat.eqn n 0)) (is_const e1 n))).
move /ssrbool.orP => [H1|].
rewrite 2!set_set_nth.
rewrite -ssrnat.eqnE H1.
now rewrite (IHe2 n H2 l x1 x2).
move /ssrbool.andP => [H1 H3].
rewrite 2!set_set_nth.
rewrite -ssrnat.eqnE (ssrbool.negbTE H1).
rewrite (IHe2 n H2 l x1 x2).
now apply IHe1.
now case (ssrnat.eqn n 0).
(* *)
easy.
(* *)
simpl => n.
move /ssrbool.andP => [H1 H2] l x1 x2.
now rewrite (IHe1 n H1 l x1 x2) (IHe2 n H2 l x1 x2).
(* *)
simpl => n H l x1 x2.
now rewrite (IHe n H l x1 x2).
(* *)
simpl => n.
move /ssrbool.andP => [H1].
move /ssrbool.andP => [H2 H3] l x1 x2.
rewrite (IHe2 n H2 l x1 x2) (IHe3 n H3 l x1 x2).
apply RInt_ext => x _.
apply (IHe1 _ H1 (x :: l)).
Qed.

Lemma interp_ext :
  forall l1 l2 e,
  (forall k, nth 0 l1 k = nth 0 l2 k) ->
  interp l1 e = interp l2 e.
Proof.
intros l1 l2 e Hl.
revert l1 l2 Hl.
induction e using expr_ind'.
(* *)
now simpl => l1 l2 Hl.
(* *)
simpl => l1 l2 Hl.
apply apply_ext.
intros n _.
revert n.
induction le.
easy.
simpl in H |- *.
destruct H as (Ha,Hb).
intros [|n].
simpl.
now apply Ha.
now apply IHle.
(* *)
simpl => l1 l2 Hl.
apply IHe1.
intros [|k].
now apply IHe2.
apply Hl.
(* *)
intros l1 l2 Hl.
rewrite /interp -/interp.
apply IHe1 => k.
rewrite 2!nth_set_nth /=.
case eqtype.eq_op.
now apply IHe2.
apply Hl.
(* *)
easy.
(* *)
simpl => l1 l2 Hl.
apply f_equal2.
now apply IHe1.
now apply IHe2.
(* *)
simpl => l1 l2 Hl.
apply f_equal.
now apply IHe.
(* *)
simpl => l1 l2 Hl.
rewrite (IHe2 l1 l2 Hl) (IHe3 l1 l2 Hl).
apply RInt_ext => x _.
apply IHe1.
intros [|k].
easy.
apply Hl.
Qed.

Lemma interp_set_nth :
  forall n l e,
  interp (set_nth 0 l n (nth 0 l n)) e = interp l e.
Proof.
intros n l e.
apply interp_ext.
intros k.
rewrite nth_set_nth /=.
case ssrnat.eqnP.
intros H.
now apply f_equal.
easy.
Qed.

Lemma interp_domain_ext :
  forall l1 l2 b,
  (forall k, nth 0 l1 k = nth 0 l2 k) ->
  interp_domain l1 b -> interp_domain l2 b.
Proof.
intros l1 l2 b Hl.
revert l1 l2 Hl.
induction b using domain_ind' ; try easy.
(* *)
simpl => l1 l2 Hl Hb.
now rewrite -(eq_map (fun e => interp_ext _ _ e Hl)).
(* *)
simpl => l1 l2 Hl.
rewrite Hl.
apply continuity_pt_ext => x.
apply interp_ext => k.
rewrite 2!nth_set_nth /=.
now case eqtype.eq_op.
(* *)
simpl => l1 l2 Hl.
rewrite 2!Hl.
apply continuity_2d_pt_ext => x y.
apply interp_ext => k.
rewrite 2!nth_set_nth /=.
case eqtype.eq_op => //.
rewrite 2!nth_set_nth /=.
now case eqtype.eq_op.
(* *)
simpl => l1 l2 Hl.
rewrite 2!(interp_ext _ _ _ Hl).
apply ex_RInt_ext.
intros x _.
apply interp_ext.
intros [|k].
easy.
apply Hl.
(* *)
simpl => l1 l2 Hl.
induction ld.
easy.
simpl in H |- *.
intros (H1,H2).
split.
apply (proj1 H _ _ Hl H1).
now apply IHld.
(* *)
simpl => l1 l2 Hl.
rewrite 2!(interp_ext _ _ _ Hl).
intros H t Ht.
apply (IHb (t :: l1)).
intros [|k].
easy.
apply Hl.
now apply H.
(* *)
simpl => l1 l2 Hl.
apply IHb.
intros [|k].
now apply interp_ext.
apply Hl.
(* *)
simpl => l1 l2 Hl.
rewrite Hl.
apply locally_impl.
apply locally_forall => y.
apply IHb => k.
now rewrite 2!nth_set_nth /= Hl.
(* *)
simpl => l1 l2 Hl.
rewrite 2!Hl.
apply locally_2d_impl.
apply locally_2d_forall => x y.
apply IHb => k.
now rewrite 2!nth_set_nth /= 2!nth_set_nth /= Hl.
(* *)
simpl => l1 l2 Hl.
rewrite Hl 2!(interp_ext _ _ _ Hl).
intros (d,Hd).
exists d => t u Ht Hu.
apply: IHb (Hd t u Ht Hu).
intros [|k].
easy.
now rewrite /= 2!nth_set_nth /= Hl.
Qed.

Lemma interp_domain_set_nth :
  forall n l b,
  interp_domain (set_nth 0 l n (nth 0 l n)) b <-> interp_domain l b.
Proof.
intros n l b.
split ;
  apply interp_domain_ext => k.
rewrite nth_set_nth /=.
case ssrnat.eqnP.
intros H.
now apply f_equal.
easy.
rewrite nth_set_nth /=.
case ssrnat.eqnP.
intros H.
now apply f_equal.
easy.
Qed.

Definition foldr_not_const l n :=
  fst (foldr (fun v acc =>
    let '(acc1,acc2) := acc in
    if is_const v n then (acc1, S acc2)
    else (acc2::acc1, S acc2)
  ) (nil, O) l).

Lemma foldr_not_const_correct :
  forall n l (k : nat),
  not (mem_seq (T:=ssrnat.nat_eqType) (foldr_not_const l n) k) ->
  is_const (nth (Cst 0) l k) n = true.
Proof.
admit.
Qed.

Lemma interp_AppExt_set_nth_not_const :
  forall k f le l n x,
  interp (set_nth 0 l n x) (AppExt k f le) =
  apply k f (foldr (fun v acc i => if ssrnat.eqn i v then interp (set_nth 0 l n x) (nth (Cst 0) le v) else acc i)
    (nth 0 (map (interp l) le)) (foldr_not_const le n)).
Proof.
intros k f le l n x.
simpl.
apply apply_ext => m _.
generalize (foldr_not_const_correct n le m).
induction (foldr_not_const le n).
simpl => Hp.
case (ssrnat.leqP (size le) m) => Hs.
rewrite 2?nth_default ?size_map //.
rewrite 2?(nth_map (Cst 0)) //.
rewrite (is_const_correct _ n _ l x (nth 0 l n)).
apply interp_set_nth.
now apply Hp.
rewrite /= -ssrnat.eqnE.
case E: (ssrnat.eqn m t).
intros _.
rewrite (ssrnat.eqnP E).
case (ssrnat.leqP (size le) t) => Hs.
now rewrite 2?nth_default ?size_map.
now rewrite (nth_map (Cst 0)).
simpl.
apply IHs.
Qed.

Fixpoint D (e : expr) n {struct e} : expr * domain :=
  match e with
  | Var v => (if ssrnat.eqn v n then Cst 1 else Cst 0, Always)
  | Cst _ => (Cst 0, Always)
  | AppExt k f le =>
(*
    if orb (ssrnat.leq 3 k) (negb (ssrnat.eqn (size le) k)) then (Cst 0, Never) else (* TODO: prove in the general case *)
    let '(d1,d2,_,_) :=
      foldr (fun v acc =>
        let '(acc1,acc2,acc3,acc4) := acc in
        if is_const v n then (acc1,acc2,S acc3,acc4)
        else
          let '(d1,d2) := D v n in
          (Binary Eplus (Binary Emult d1 (AppExt k (Derive_Rn k f acc3) le)) acc1,
           match acc4 with
           | nil => Derivable acc3 k f le :: d2 :: acc2
           | y :: nil =>
           | _ => Never
           end, S acc3,acc3::acc4)
      ) (Cst 0, nil, O, nil) le in
    (d1, And d2)
*)
    let lnc := foldr_not_const le n in
    let ld := map (fun e => D e n) le in
    match lnc with
    | nil => (Cst 0, Always)
    | v :: nil =>
      let '(d1,d2) := nth (Cst 0,Never) ld v in
      (Binary Emult d1 (AppExt k (Derive_Rn k f v) le),
       And (Derivable v k f le :: d2 :: nil))
    | v1 :: v2 :: nil =>
      let '(d1,d2) := nth (Cst 0,Never) ld v1 in
      let '(d3,d4) := nth (Cst 0,Never) ld v2 in
      (Binary Eplus (Binary Emult d1 (AppExt k (Derive_Rn k f v1) le)) (Binary Emult d3 (AppExt k (Derive_Rn k f v2) le)),
       And (Derivable v1 k f le :: d2 :: Derivable v2 k f le :: d4 :: nil))
    | _ => (Cst 0, Never)
    end
  | App f e => (Cst 0, Never)
  | Subst f e => (Cst 0, Never)
  | Binary b e1 e2 =>
    let '(a1,b1) := D e1 n in
    let '(a2,b2) := D e2 n in
    match b, is_const e1 n, is_const e2 n with
    | Eplus, true, _ => (a2, b2)
    | Eplus, _, true => (a1, b1)
    | Eplus, _, _ => (Binary Eplus a1 a2, And (b1::b2::nil))
    | Emult, true, _ => (Binary Emult e1 a2, b2)
    | Emult, _, true => (Binary Emult a1 e2, b1)
    | Emult, _, _ => (Binary Eplus (Binary Emult a1 e2) (Binary Emult e1 a2), And (b1::b2::nil))
    end
  | Unary u e =>
    let '(a,b) := D e n in
    match u with
    | Eopp => (Unary Eopp a, b)
    end
  | Int f e1 e2 =>
    let '(a1,b1) := D e1 n in
    let '(a2,b2) := D e2 n in
    let '(a3,b3) := D f (S n) in
    match is_const f (S n), is_const e1 n, is_const e2 n with
    | true, true, _ =>
      (Binary Emult a2 (App f e2), And (b2::(Integrable f e1 e2)::(Forone e2 (Locally 0 (Continuous 0 f)))::nil))
    | true, false, true =>
      (Unary Eopp (Binary Emult a1 (App f e1)), And (b1::(Integrable f e1 e2)::(Forone e1 (Locally 0 (Continuous 0 f)))::nil))
    | true, false, false =>
      (Binary Eplus (Binary Emult a2 (App f e2)) (Unary Eopp (Binary Emult a1 (App f e1))),
       And (b1::b2::(Integrable f e1 e2)::(Forone e1 (Locally 0 (Continuous 0 f)))::(Forone e2 (Locally 0 (Continuous 0 f)))::nil))
    | false, true, true =>
      (Int a3 e1 e2,
       And ((Integrable a3 e1 e2)::(ForallWide n e1 e2 b3)::
            (Locally n (Integrable f e1 e2))::(Forall e1 e2 (Continuous2 (S n) 0 a3))::nil))
    | _, _, _ => (Cst 0, Never)
(*
    | _, _, _ =>
      (Binary Eplus
        (Binary Eplus
          (Binary Emult a2 (App f e2))
          (Unary Eopp (Binary Emult a1 (App f e1))))
        (Int a3 e1 e2), And (b1::b2::(Forall e1 e2 b3)::(Integrable f e1 e2)::nil))
*)
    end
  end.

Lemma D_correct :
  forall (e : expr) l n,
  let '(a,b) := D e n in
  interp_domain l b ->
  is_derive (fun x => interp (set_nth R0 l n x) e) (nth R0 l n) (interp l a).
Proof.
induction e using expr_ind'.

(* Var *)
simpl => l k _.
apply (is_derive_ext (fun x => if ssrnat.eqn n k then x else nth 0 l n)).
intros t.
now rewrite nth_set_nth.
case ssrnat.eqnP => [H|H].
apply derivable_pt_lim_id.
apply derivable_pt_lim_const.

(* AppExt *)
simpl D => l n.
assert (Dle: forall v n l,
  let '(a,b) := D (nth (Cst 0) le v) n in
  interp_domain l b -> is_derive (fun x => interp (set_nth 0 l n x) (nth (Cst 0) le v)) (nth 0 l n) (interp l a)).
clear n l.
induction le => v n l.
rewrite nth_nil /= => _.
apply derivable_pt_lim_const.
simpl in H |- *.
destruct v as [|v].
apply H.
simpl.
now apply IHle.
move: (interp_AppExt_set_nth_not_const k f le l n).
case (foldr_not_const le n) => [|v1 [|v2 [|v3 q]]] /= Hc.
(* . *)
intros _.
apply (is_derive_ext (fun x => apply k f (nth 0 (map (interp l) le)))).
intros t.
apply sym_eq.
apply Hc.
apply derivable_pt_lim_const.
(* . *)
case (ssrnat.leqP (size le) v1) => Hv1.
rewrite nth_default ?size_map //.
now intros (_&F&_).
rewrite (nth_map (Cst 0)) //.
move: (Dle v1 n l).
case (D (nth (Cst 0) le v1)) => /= [d1 d2] {Dle} Dle [H1 [H2 _]].
rewrite Rmult_comm.
specialize (Dle H2).
apply (is_derive_ext (fun x => apply k f (fun i => if ssrnat.eqn i v1 then interp (set_nth 0 l n x) (nth (Cst 0) le v1) else nth 0 (map (interp l) le) i))).
intros t.
now apply sym_eq.
apply derivable_pt_lim_comp with (f2 := fun x => apply k f (fun i => if ssrnat.eqn i v1 then x else nth 0 (map (interp l) le) i)) (1 := Dle).
rewrite interp_set_nth.
rewrite -(nth_map (Cst 0) 0) //.
now apply Derive_Rn_correct.
(* . *)
case (ssrnat.leqP (size le) v1) => Hv1.
rewrite nth_default ?size_map //.
case (nth (Cst 0, Never) (map (fun e => D e n) le) v2) => [d3 d4].
now intros (_&F&_).
rewrite (nth_map (Cst 0)) //.
move: (Dle v1 n l).
case (D (nth (Cst 0) le v1)) => /= [d1 d2] Dle1.
case (ssrnat.leqP (size le) v2) => Hv2.
rewrite nth_default ?size_map //.
now intros (_&_&_&F).
rewrite (nth_map (Cst 0)) //.
move: (Dle v2 n l).
case (D (nth (Cst 0) le v2)) => /= [d3 d4] Dle2 {Dle} [H1 [H2 [H3 [H4 _]]]].
rewrite Rmult_comm (Rmult_comm (interp l d3) _).
specialize (Dle1 H2).
specialize (Dle2 H4).
set (g u v := apply k f (fun i =>
  if ssrnat.eqn i v1 then u else if ssrnat.eqn i v2 then v else nth 0 (map (interp l) le) i)).
apply (is_derive_ext (fun x => g (interp (set_nth 0 l n x) (nth (Cst 0) le v1)) (interp (set_nth 0 l n x) (nth (Cst 0) le v2)))).
intros t.
unfold g.
now apply sym_eq.
apply derivable_pt_lim_comp_2d with (f1 := g).
rewrite 2!interp_set_nth.
rewrite -(is_derive_unique _ _ _ (Derive_Rn_correct _ _ _ _ H1)).
rewrite -(nth_map (Cst 0) 0 (interp l) Hv1).
rewrite -(nth_map (Cst 0) 0 (interp l) Hv2).
rewrite -(Derive_ext (fun x => g x (nth 0 (map (interp l) le) v2))).
apply derivable_differentiable_pt_lim.
admit. (* local differentiability *)
apply: is_derive_ext (Derive_Rn_correct _ _ _ _ H3).
intros t.
apply apply_ext.
intros p Hp.
case E: (ssrnat.eqn p v1) => //.
case E': (ssrnat.eqn p v2).
admit. (* p1 <> P2 *)
now rewrite (ssrnat.eqnP E).
admit. (* continuity 2D *)
intros t.
apply apply_ext.
intros p Hp.
case (ssrnat.eqn p v1) => //.
case E: (ssrnat.eqn p v2) => //.
now rewrite (ssrnat.eqnP E).
apply Dle1.
apply Dle2.
(* . *)
easy.

(* App *)
simpl => l n [].

(* Subst *)
simpl => l n [].

(* Cst *)
simpl => l n _.
apply derivable_pt_lim_const.

(* Binary *)
simpl => l n.
specialize (IHe1 l n).
specialize (IHe2 l n).
destruct (D e1 n) as (a1,b1).
destruct (D e2 n) as (a2,b2).
case C1: (is_const e1 n).
(* . *)
assert (H1 := is_const_correct e1 n C1 l).
case o ; intros H2.
rewrite -(Rplus_0_l (interp l a2)).
apply derivable_pt_lim_plus.
apply (is_derive_ext (fun x => interp (set_nth 0 l n 0) e1)).
apply H1.
apply derivable_pt_lim_const.
now apply IHe2.
simpl.
replace (interp l e1 * interp l a2) with (0 * interp (set_nth 0 l n (nth 0 l n)) e2 + interp l e1 * interp l a2) by ring.
rewrite -(interp_set_nth n _ e1).
apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).
apply (is_derive_ext (fun x => interp (set_nth 0 l n 0) e1)).
apply H1.
apply derivable_pt_lim_const.
now apply IHe2.
case C2: (is_const e2 n) => {C1}.
(* . *)
assert (H2 := is_const_correct e2 n C2 l).
case o ; intros H1.
rewrite -(Rplus_0_r (interp l a1)).
apply derivable_pt_lim_plus.
now apply IHe1.
apply (is_derive_ext (fun x => interp (set_nth 0 l n 0) e2)).
apply H2.
apply derivable_pt_lim_const.
simpl.
replace (interp l a1 * interp l e2) with (interp l a1 * interp l e2 + interp (set_nth 0 l n (nth 0 l n)) e1 * 0) by ring.
rewrite -(interp_set_nth n _ e2).
apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).
now apply IHe1.
apply (is_derive_ext (fun x => interp (set_nth 0 l n 0) e2)).
apply H2.
apply derivable_pt_lim_const.
(* . *)
clear C2.
case o ; simpl ;
  intros (H1&H2&_) ;
  specialize (IHe1 H1) ;
  specialize (IHe2 H2).
now apply derivable_pt_lim_plus.
rewrite -(interp_set_nth n _ e1) -(interp_set_nth n _ e2).
now apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).

(* Unary *)
simpl => l n.
specialize (IHe l n).
destruct (D e n) as (a,b).
case o.
simpl.
intros H.
apply derivable_pt_lim_opp.
now apply IHe.

(* Int *)
simpl => l n.
specialize (IHe2 l n).
specialize (IHe3 l n).
move: (fun l => IHe1 l (S n)) => {IHe1} IHe1.
destruct (D e1 (S n)) as (a1,b1).
destruct (D e2 n) as (a2,b2).
destruct (D e3 n) as (a3,b3).
(* . *)
assert (HexI: forall f x, locally (fun x => continuity_pt f x) x -> exists eps : posreal, ex_RInt f (x - eps) (x + eps)).
clear => f x [eps H].
exists (pos_div_2 eps).
apply ex_RInt_correct_3.
apply RiemannInt_P6.
apply Rplus_lt_compat_l.
apply Rle_lt_trans with (2 := cond_pos _).
rewrite -Ropp_0.
apply Ropp_le_contravar.
apply Rlt_le.
apply cond_pos.
intros u Hu.
apply H.
apply Rle_lt_trans with (pos_div_2 eps).
now apply Rabs_le_between'.
rewrite (double_var eps).
rewrite -(Rplus_0_r (pos_div_2 eps)).
apply Rplus_lt_compat_l.
apply (cond_pos (pos_div_2 eps)).
case C1: (is_const e1 (S n)).
clear IHe1.
case C2: (is_const e2 n).
(* . *)
simpl.
intros (H3&Hi&H1&_).
rewrite Rmult_comm.
apply (is_derive_ext (comp (fun x => RInt (fun t => interp (t :: l) e1) (interp (set_nth 0 l n (nth 0 l n)) e2) x) (fun x => interp (set_nth 0 l n x) e3))).
intros t.
unfold comp.
rewrite -(is_const_correct e2 n C2 l (nth 0 l n)).
apply RInt_ext.
intros z _.
rewrite -(interp_set_nth (S n)).
apply (is_const_correct e1 (S n) C1 (z :: l)).
apply derivable_pt_lim_comp.
now apply IHe3.
rewrite 2!interp_set_nth.
apply derivable_pt_lim_RInt with (1 := Hi).
now apply HexI.
now apply locally_singleton.
clear C2.
case C3: (is_const e3 n).
(* . *)
simpl.
intros (H2&Hi&H1&_).
rewrite Rmult_comm -Ropp_mult_distr_l_reverse.
apply (is_derive_ext (fun x => comp (fun x => RInt (fun t => interp (t :: l) e1) x (interp (set_nth 0 l n (nth 0 l n)) e3)) (fun x => interp (set_nth 0 l n x) e2) x)).
intros t.
unfold comp.
rewrite -(is_const_correct e3 n C3 l (nth 0 l n)).
apply RInt_ext.
intros z _.
rewrite -(interp_set_nth (S n)).
apply (is_const_correct e1 (S n) C1 (z :: l)).
apply (derivable_pt_lim_comp (fun x0 : R => interp (set_nth 0 l n x0) e2)
  (fun x0 : R => RInt (fun t : R => interp (t :: l) e1) x0 (interp (set_nth 0 l n (nth 0 l n)) e3))).
now apply IHe2.
rewrite 2!interp_set_nth.
apply derivable_pt_lim_RInt' with (1 := Hi).
now apply HexI.
now apply locally_singleton.
(* . *)
clear C3.
simpl.
intros (H2&H3&Hi&H12&H13&_).
apply (is_derive_ext (fun x => RInt (fun t => interp (t :: l) e1) (interp (set_nth 0 l n x) e2) (interp (set_nth 0 l n x) e3))).
intros t.
apply RInt_ext.
intros z _.
rewrite -(interp_set_nth (S n)).
apply (is_const_correct e1 (S n) C1 (z :: l)).
rewrite -(interp_set_nth n l e2) -(interp_set_nth n l e3).
apply derivable_pt_lim_RInt_bound_comp.
now rewrite 2!interp_set_nth.
rewrite interp_set_nth.
now apply HexI.
rewrite interp_set_nth.
now apply HexI.
rewrite interp_set_nth.
now apply locally_singleton.
rewrite interp_set_nth.
now apply locally_singleton.
now apply IHe2.
now apply IHe3.
case C2: (is_const e2 n).
clear IHe2.
case C3: (is_const e3 n).
clear IHe3.
(* . *)
clear C1.
simpl.
intros (H1&H3&H2&H4&_).
apply (is_derive_ext (fun x => RInt (fun t => interp (t :: set_nth 0 l n x) e1) (interp (set_nth 0 l n (nth 0 l n)) e2) (interp (set_nth 0 l n (nth 0 l n)) e3))).
intros t.
apply f_equal2.
now apply is_const_correct.
now apply is_const_correct.
rewrite 2!interp_set_nth.
destruct H3 as (d,H3).
assert (H3': locally (fun x => forall t, Rmin (interp l e2) (interp l e3) <= t <= Rmax (interp l e2) (interp l e3) ->
  interp_domain (set_nth 0 (t :: l) (S n) x) b1) (nth 0 l n)).
exists d => y Hy t Ht.
apply H3.
split.
apply Rlt_le_trans with (2 := proj1 Ht).
rewrite -{2}[Rmin _ _]Rplus_0_r -Ropp_0.
apply Rplus_lt_compat_l.
apply Ropp_lt_contravar.
apply cond_pos.
apply Rle_lt_trans with (1 := proj2 Ht).
rewrite -{1}[Rmax _ _]Rplus_0_r.
apply Rplus_lt_compat_l.
apply cond_pos.
exact Hy.
rewrite (RInt_ext (fun x => interp (x :: l) a1) (fun x => Derive (fun t => interp (set_nth 0 (x :: l) (S n) t) e1) (nth 0 (x :: l) (S n)))).
apply derivable_pt_lim_param.
apply: locally_impl H3'.
apply locally_forall => y H3' t Ht.
specialize (IHe1 _ (H3' t Ht)).
rewrite nth_set_nth /= eqtype.eq_refl in IHe1.
exists (interp (set_nth 0 (t :: l) (S n) y) a1).
apply is_derive_ext with (f := fun x => interp (set_nth 0 (set_nth 0 (t :: l) (S n) y) (S n) x) e1) (2 := IHe1).
intros t'.
now rewrite set_set_nth eqtype.eq_refl.
intros t Ht.
apply continuity_2d_pt_ext_loc with (f := fun x y => interp (set_nth 0 (y :: l) (S n) x) a1).
exists d => u v Hu Hv.
apply sym_eq.
apply is_derive_unique.
apply is_derive_ext with (f := fun z => interp (set_nth 0 (set_nth 0 (v :: l) (S n) u) (S n) z) e1).
intros z.
now rewrite set_set_nth eqtype.eq_refl.
pattern u at 2; replace u with (nth 0 (set_nth 0 (v :: l) (S n) u) (S n)).
apply IHe1.
apply H3.
apply Rabs_lt_between' in Hv.
split.
apply Rle_lt_trans with (2 := proj1 Hv).
now apply Rplus_le_compat_r.
apply Rlt_le_trans with (1 := proj2 Hv).
now apply Rplus_le_compat_r.
exact Hu.
now rewrite nth_set_nth /= eqtype.eq_refl.
now apply H4.
apply: locally_impl H2.
apply locally_forall => y.
rewrite (is_const_correct e2 n C2 l y (nth 0 l n)).
rewrite (is_const_correct e3 n C3 l y (nth 0 l n)).
now rewrite 2!interp_set_nth.
apply ex_RInt_ext with (2 := H1).
intros t Ht.
apply sym_eq.
apply is_derive_unique.
apply locally_singleton in H3'.
apply (IHe1 (t :: l)).
generalize (H3' t Ht).
apply (interp_domain_set_nth (S n) (t :: l)).
intros t Ht.
apply sym_eq.
apply is_derive_unique.
apply locally_singleton in H3'.
apply (IHe1 (t :: l)).
generalize (H3' t Ht).
apply (interp_domain_set_nth (S n) (t :: l)).
(* . *)
easy.
easy.
Qed.

Fixpoint simplify_domain (d : domain) : domain :=
  match d with
  | And ld =>
    let l := foldr (fun d acc =>
      let d' := simplify_domain d in
      match d' with
      | Always => acc
      | And l => cat l acc
      | Never => Never :: nil
      | _ => d' :: acc
      end) nil ld in
    match l with
    | nil => Always
    | d :: nil => d
    | _ => And l
    end
  | Forall e1 e2 d =>
    let d' := simplify_domain d in
    match d' with
    | Always => Always
    | _ => Forall e1 e2 d'
    end
  | Locally e d =>
    let d' := simplify_domain d in
    match d' with
    | Always => Always
    | Never => Never
    | _ => Locally e d'
    end
  | _ => d
  end.

Lemma simplify_domain_correct :
  forall d l,
  interp_domain l (simplify_domain d) -> interp_domain l d.
Proof.
intros d.
induction d using domain_ind' => l ; try easy ; simpl.
(* And *)
set (f := fun (d : domain) (acc : seq domain) =>
  match simplify_domain d with
  | Never => Never :: nil
  | Always => acc
  | And l0 => l0 ++ acc
  | _ => simplify_domain d :: acc
  end).
intros H'.
have: (foldr (fun d acc => interp_domain l d /\ acc) True (foldr f nil ld)).
by move: (foldr f nil ld) H' => [|h [|s]].
clear H'.
revert H.
induction ld => H.
easy.
simpl in H |- *.
destruct H as (Ha,Hb).
revert Ha.
rewrite /f -/f.
case (simplify_domain t) ; simpl.
(* . *)
now intros _ (H,_).
(* . *)
exact (fun H1 H2 => conj (H1 l I) (IHld Hb H2)).
(* . *)
intros n k f' le H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros n e H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros m n e H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros e0 e1 e2 H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros ls H1 H2.
rewrite foldr_cat in H2.
refine ((fun H => conj (H1 l (proj1 H)) (IHld Hb (proj2 H))) _).
revert H2.
generalize (foldr f nil ld).
clear.
induction ls.
done.
simpl.
split.
split.
apply H2.
eapply (fun s H => proj1 (IHls s H)).
apply H2.
now apply IHls.
(* . *)
intros e1 e2 d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros e d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros n d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros m n d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
intros n e1 e2 d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* Forall *)
revert IHd.
assert (HH: forall d', (forall l, interp_domain l d' -> interp_domain l d) ->
  interp_domain l (Forall e1 e2 d') -> interp_domain l (Forall e1 e2 d)).
simpl.
intros d' H1 H2 t Ht.
apply H1.
now apply H2.
destruct (simplify_domain d) ; try (apply HH ; fail).
simpl.
intros H _ t Ht.
now apply H.
(* Locally *)
revert IHd.
assert (HH: forall d', (forall l, interp_domain l d' -> interp_domain l d) ->
  interp_domain l (Locally n d') -> interp_domain l (Locally n d)).
simpl.
intros d' H1 (eps,H2).
exists eps => t Ht.
apply H1.
now apply H2.
destruct (simplify_domain d) ; try (apply HH ; fail).
easy.
simpl.
intros H _.
exists (mkposreal _ Rlt_0_1) => t Ht.
now apply H.
Qed.

Definition var : nat -> R.
exact (fun _ => R0).
Qed.

Ltac reify_helper a b z d :=
  match a with
  | Cst _ =>
    match b with
    | Cst _ => constr:(Cst d)
    | _ => z
    end
  | _ => z
  end.

Ltac reify fct nb :=
  let rec reify_aux fct l i :=
    match fct with
    | ?f ?a => let e := reify a nb in reify_aux f (e :: l) (S i)
    | _ => constr:(fct, rev l, i)
    end in
  match fct with
  | var ?i =>
    eval vm_compute in (Var (nb - i))
  | Rplus ?a ?b =>
    let a' := reify a nb in
    let b' := reify b nb in
    reify_helper a' b' (Binary Eplus a' b') fct
  | Ropp ?a =>
    let a' := reify a nb in
    match a' with
    | Cst _ => constr:(Cst fct)
    | _ => constr:(Unary Eopp a')
    end
  | Rminus ?a ?b =>
    let a' := reify a nb in
    let b' := reify b nb in
    reify_helper a' b' (Binary Eplus a' (Unary Eopp b')) fct
  | Rmult ?a ?b =>
    let a' := reify a nb in
    let b' := reify b nb in
    reify_helper a' b' (Binary Emult a' b') fct
  | RInt ?f ?a ?b =>
    let f := eval cbv beta in (f (var (S nb))) in
    let f' := reify f (S nb) in
    let a' := reify a nb in
    let b' := reify b nb in
    constr:(Int f' a' b')
  | appcontext [var ?i] =>
    match reify_aux fct (Nil expr) O with
    | (?f,?le,?k) => constr:(AppExt k f le)
    end
  | _ => constr:(Cst fct)
  end.

Lemma auto_derive_helper :
  forall (e : expr) l n,
  let '(a,b) := D e n in
  interp_domain l (simplify_domain b) ->
  is_derive (fun x => interp (set_nth R0 l n x) e) (nth R0 l n) (interp l a).
Proof.
intros e l n.
generalize (D_correct e l n).
destruct (D e n) as (d1,d2).
intros H1 H2.
apply H1.
now apply simplify_domain_correct.
Qed.

Ltac auto_derive_fun f :=
  let f := eval cbv beta in (f (var O)) in
  let e := reify f O in
  let H := fresh "H" in
  assert (H := fun x => auto_derive_helper e (x :: nil) 0) ;
  simpl in H ;
  revert H.

Ltac auto_derive :=
  match goal with
  | |- derivable_pt_lim ?f ?v ?l =>
    auto_derive_fun f ;
    let H := fresh "H" in
    intro H ;
    specialize (H v) ;
    refine (eq_ind _ (derivable_pt_lim _ _) (H _) _ _) ;
    clear H
  end.

Goal forall f x, derivable_pt_lim (fun y => f (2 * x) + RInt (fun z => z) 0 y + 2 * y) x 0.
intros f x.
auto_derive.
2: ring_simplify.
Abort.
