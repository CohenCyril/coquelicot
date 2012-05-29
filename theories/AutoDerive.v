Require Import Reals.
Require Import ssreflect seq.
Require Import Arithmetique Locally Deriv_fct RInt Differential.

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

Fixpoint apply {T} p : Rn p T -> seq R -> T :=
  match p return Rn p T -> seq R -> T with
  | O => fun (x : T) l => x
  | S p => fun (f : Rn (S p) T) l => match l with h::q => apply p (f h) q | nil => apply p (f R0) l end
  end.

Fixpoint interp (l : seq R) (e : expr) : R :=
  match e with
  | Var n => nth R0 l n
  | AppExt k f le => apply k f (map (interp l) le)
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
  | Derivable : forall k, Rn k R -> seq expr -> nat -> domain
  | Continuous : expr -> domain
  | Integrable : expr -> expr -> expr -> domain
  | And : seq domain -> domain
  | Forall : expr -> expr -> domain -> domain
  | Locally : expr -> domain -> domain.

Fixpoint Deriv_Rn_aux n (f : Rn (S n) R) x : Rn n R :=
  match n return Rn (S n) R -> Rn n R with
  | O => fun f => Deriv (fun x => f x) x
  | S n => fun f y => Deriv_Rn_aux n (fun x => f x y) x
  end f.

Fixpoint Deriv_Rn n (f : Rn n R) i : Rn n R :=
  match n return Rn n R -> Rn n R with
  | O => fun _ => R0
  | S n => fun f => if ssrnat.eqn n i then fun x => Deriv_Rn_aux n f x else fun x => Deriv_Rn n (f x) i
  end f.

Fixpoint ex_deriv_Rn_aux n (f : Rn (S n) R) x : Rn n Prop :=
  match n return Rn (S n) R -> Rn n Prop with
  | O => fun f => ex_deriv (fun x => f x) x
  | S n => fun f y => ex_deriv_Rn_aux n (fun x => f x y) x
  end f.

Fixpoint ex_deriv_Rn n (f : Rn n R) i : Rn n Prop :=
  match n return Rn n R -> Rn n Prop with
  | O => fun _ => False
  | S n => fun f => if ssrnat.eqn n i then fun x => ex_deriv_Rn_aux n f x else fun x => ex_deriv_Rn n (f x) i
  end f.

Fixpoint interp_domain (l : seq R) (d : domain) : Prop :=
  match d with
  | Never => False
  | Always => True
  | Derivable k f le n => apply k (ex_deriv_Rn k f n) (map (interp l) le)
  | Continuous f => continuity_pt (fun x => interp (set_nth R0 l 0 x) f) (nth R0 l 0)
  | Integrable f e1 e2 => ex_RInt (fun x => interp (x :: l) f) (interp l e1) (interp l e2)
  | And ld => foldr (fun d acc => interp_domain l d /\ acc) True ld
  | Forall e1 e2 s =>
    let a1 := interp l e1 in let a2 := interp l e2 in
    exists eps : posreal, forall t, -eps < t < 1 + eps ->
    interp_domain (a1 + t * (a2 - a1) :: l) s
  | Locally e s =>
    locally (fun x => interp_domain (x :: l) s) (interp l e)
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
  forall e n, is_const e n ->
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
revert k f.
induction le => k f.
easy.
simpl in Hc, H |- *.
apply andb_prop in Hc.
destruct H as (H1,H2).
destruct Hc as (H3,H4).
specialize (IHle H2 H4).
destruct k as [|k].
easy.
simpl.
now rewrite (H1 _ H3 l x1 x2).
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
apply RInt_rw => x _.
apply (IHe1 _ H1 (x :: l)).
Qed.

Fixpoint D (e : expr) n : expr * domain :=
  match e with
  | Var v => (if ssrnat.eqn v n then Cst 1 else Cst 0, Always)
  | Cst _ => (Cst 0, Always)
  | AppExt k f le =>
    if orb (ssrnat.leq 3 k) (negb (ssrnat.eqn (size le) k)) then (Cst 0, Never) else (* TODO: prove in the general case *)
    let '(d1,d2,_) :=
      foldr (fun v acc =>
        let '(acc1,acc2,acc3) := acc in
        if is_const v n then (acc1,acc2,S acc3)
        else
          let '(d1,d2) := D v n in
          (Binary Eplus (Binary Emult d1 (AppExt k (Deriv_Rn k f acc3) le)) acc1,
           Derivable k f le acc3 :: d2 :: acc2, S acc3)
      ) (Cst 0, nil, O) le in
    (d1, And d2)
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
      (Binary Emult a2 (App f e2), And (b2::(Integrable f e1 e2)::(Locally e2 (Continuous f))::nil))
    | true, false, true =>
      (Unary Eopp (Binary Emult a1 (App f e1)), And (b1::(Integrable f e1 e2)::(Locally e1 (Continuous f))::nil))
    | true, false, false =>
      (Binary Eplus (Binary Emult a2 (App f e2)) (Unary Eopp (Binary Emult a1 (App f e1))),
       And (b1::b2::(Integrable f e1 e2)::(Locally e1 (Continuous f))::(Locally e2 (Continuous f))::nil))
    | _, _, _ =>
      (Binary Eplus
        (Binary Eplus
          (Binary Emult a2 (App f e2))
          (Unary Eopp (Binary Emult a1 (App f e1))))
        (Int a3 e1 e2), And (b1::b2::(Forall e1 e2 b3)::(Integrable f e1 e2)::nil))
    end
  end.

Lemma is_deriv_eq :
  forall f g x l,
  (forall t, f t = g t) ->
  is_deriv f x l -> is_deriv g x l.
Proof.
intros f g x l Heq Hf eps Heps.
move: (Hf eps Heps) => {Hf} [delta Hf].
exists delta => h Zh Hh.
rewrite -2!Heq.
now apply Hf.
Qed.

Lemma interp_subst :
  forall n l e,
  interp (set_nth 0 l n (nth 0 l n)) e = interp l e.
Proof.
intros n l e.
revert n l.
induction e using expr_ind'.
(* *)
simpl => k l.
rewrite nth_set_nth /= /eqtype.eq_op /=.
case ssrnat.eqnP.
move => -> //.
easy.
(* *)
simpl => n l.
apply f_equal.
induction le.
easy.
simpl in H |- *.
destruct H as (Ha,Hb).
rewrite Ha.
specialize (IHle Hb).
now apply f_equal.
(* *)
simpl => n l.
rewrite IHe2.
change (interp l e2 :: set_nth 0 l n (nth 0 l n)) with
  (set_nth 0 (interp l e2 :: l) (S n) (nth 0 (interp l e2 :: l) (S n))).
apply IHe1.
(* *)
intros n l.
rewrite /interp -/interp.
rewrite IHe2.
rewrite set_set_nth.
case ssrnat.eqnP => H.
easy.
replace (nth 0 l n) with (nth 0 (set_nth 0 l 0 (interp l e2)) n).
apply IHe1.
rewrite nth_set_nth /=.
case ssrnat.eqnP => H'.
now contradict H.
easy.
(* *)
easy.
(* *)
simpl => n l.
now rewrite IHe1 IHe2.
(* *)
simpl => n l.
now rewrite IHe.
(* *)
simpl => n l.
rewrite IHe2 IHe3.
apply RInt_rw => x _.
apply (IHe1 (S n) (x :: l)).
Qed.

Axiom derivable_pt_lim_RInt :
  forall f a x,
  ex_RInt f a x -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x ->
  derivable_pt_lim (fun x => RInt f a x) x (f x).

Axiom RInt_swap :
  forall f a b,
  -(RInt f a b) = RInt f b a.

Lemma derivable_pt_lim_RInt' :
  forall f a x,
  ex_RInt f x a -> (exists eps : posreal, ex_RInt f (x - eps) (x + eps)) ->
  continuity_pt f x ->
  derivable_pt_lim (fun x => RInt f x a) x (- f x).
Proof.
intros f a x Hi Ix Cx.
apply (is_deriv_eq (fun u => - RInt f a u)).
intros t.
apply RInt_swap.
apply derivable_pt_lim_opp.
apply derivable_pt_lim_RInt ; try easy.
apply ex_RInt_correct_2.
apply RiemannInt_P1.
now apply ex_RInt_correct_1.
Qed.

Lemma derivable_pt_lim_RInt_bound_comp :
  forall f a b da db x,
  ex_RInt f (a x) (b x) ->
  (exists eps : posreal, ex_RInt f (a x - eps) (a x + eps)) ->
  (exists eps : posreal, ex_RInt f (b x - eps) (b x + eps)) ->
  continuity_pt f (a x) ->
  continuity_pt f (b x) ->
  derivable_pt_lim a x da ->
  derivable_pt_lim b x db ->
  derivable_pt_lim (fun x => RInt f (a x) (b x)) x (db * f (b x) - da * f (a x)).
Proof.
intros f a b da db x Hi Ia Ib Ca Cb Da Db.
replace (db * f (b x) - da * f (a x)) with (- f(a x) * da + f (b x) * db) by ring.
apply derivable_pt_lim_comp_2d ; try easy.
replace (- f (a x)) with (Deriv (fun u => RInt f u (b x)) (a x)).
replace (f (b x)) with (Deriv (fun u => RInt f (a x) u) (b x)).
apply derivable_differentiable_pt_lim.
admit.
admit.
admit.
admit.
apply Deriv_correct.
now apply derivable_pt_lim_RInt.
apply Deriv_correct.
now apply derivable_pt_lim_RInt'.
Qed.

Lemma D_correct :
  forall (e : expr) l n,
  let '(a,b) := D e n in
  interp_domain l b ->
  is_deriv (fun x => interp (set_nth R0 l n x) e) (nth R0 l n) (interp l a).
Proof.
induction e using expr_ind'.
(* Var *)
simpl => l k _.
apply is_deriv_eq with (fun x => if ssrnat.eqn n k then x else nth 0 l n).
intros t.
now rewrite nth_set_nth.
case ssrnat.eqnP => [H|H].
apply derivable_pt_lim_id.
apply derivable_pt_lim_const.
(* AppExt *)
simpl => l n.
match goal with
|- appcontext [foldr ?f] => set (g := f)
end.
case Ek: (orb (ssrnat.leq 3 k) (negb (ssrnat.eqn (size le) k))).
easy.
cut (let '(d1, d2, _) := foldr g (Cst 0, nil, O) le in interp_domain l (And d2) ->
  is_deriv (fun x : R => apply k f (map (interp (set_nth 0 l n x)) le)) (nth 0 l n) (interp l d1)).
by case: foldr => [[a b] _].
destruct k as [|k].
destruct le as [|t le].
simpl => _.
apply derivable_pt_lim_const.
easy.
destruct k as [|k].
destruct le as [|t [|t' le]] ; try easy.
simpl in H |- *.
case C: (is_const t n).
simpl => _.
assert (H1 := is_const_correct t n C).
apply (is_deriv_eq (fun x => f (interp (set_nth 0 l n 0) t))).
intros t'.
now apply f_equal.
apply derivable_pt_lim_const.
destruct H as (H,_).
specialize (H l n).
destruct (D t n) as (d1,d2).
simpl.
intros (H1&H2&_).
specialize (H H2).
rewrite Rplus_0_r Rmult_comm.
apply derivable_pt_lim_comp with (f2 := fun x => f x) (1 := H).
rewrite (interp_subst n _ t).
now apply Deriv_prop.
destruct k as [|k] ; try easy.
destruct le as [|t1 [|t2 [|t' le]]] ; try easy.
simpl in H |- *.
destruct H as (H3&H4&_).
specialize (H3 l n).
specialize (H4 l n).
case C2: (is_const t2 n).
assert (H2 := is_const_correct t2 n C2).
simpl.
case C1: (is_const t1 n).
assert (H1 := is_const_correct t1 n C1).
simpl => _.
apply (is_deriv_eq (fun x => f (interp (set_nth 0 l n 0) t1) (interp (set_nth 0 l n 0) t2))).
intros t'.
now apply f_equal2.
apply derivable_pt_lim_const.
destruct (D t1 n) as (d1,d2).
simpl.
intros (H5&H6&_).
specialize (H3 H6).
apply (is_deriv_eq (fun x => f (interp (set_nth 0 l n x) t1) (interp (set_nth 0 l n (nth 0 l n)) t2))).
intros t'.
now apply f_equal.
rewrite Rplus_0_r Rmult_comm.
apply derivable_pt_lim_comp with (f2 := fun x => f x (interp (set_nth 0 l n (nth 0 l n)) t2)) (1 := H3).
rewrite (interp_subst n _ t1) (interp_subst n l t2).
now apply Deriv_prop.
destruct (D t2 n) as (d3,d4).
simpl.
case C1: (is_const t1 n).
assert (H1 := is_const_correct t1 n C1).
simpl.
intros (H5&H6&_).
specialize (H4 H6).
apply (is_deriv_eq (fun x => f (interp (set_nth 0 l n (nth 0 l n)) t1) (interp (set_nth 0 l n x) t2))).
intros t'.
now apply f_equal2.
rewrite Rplus_0_r Rmult_comm.
apply derivable_pt_lim_comp with (f2 := fun x => f (interp (set_nth 0 l n (nth 0 l n)) t1) x) (1 := H4).
rewrite (interp_subst n _ t1) (interp_subst n l t2).
now apply Deriv_prop.
destruct (D t1 n) as (d1,d2).
simpl.
intros (H5&H6&H7&H8&_).
rewrite Rplus_0_r.
admit. (* manque la continuité des dérivées ou la différentiabilité *)
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
apply (is_deriv_eq (fun x => interp (set_nth 0 l n 0) e1)).
apply H1.
apply derivable_pt_lim_const.
now apply IHe2.
simpl.
replace (interp l e1 * interp l a2) with (0 * interp (set_nth 0 l n (nth 0 l n)) e2 + interp l e1 * interp l a2) by ring.
rewrite -(interp_subst n _ e1).
apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).
apply (is_deriv_eq (fun x => interp (set_nth 0 l n 0) e1)).
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
apply (is_deriv_eq (fun x => interp (set_nth 0 l n 0) e2)).
apply H2.
apply derivable_pt_lim_const.
simpl.
replace (interp l a1 * interp l e2) with (interp l a1 * interp l e2 + interp (set_nth 0 l n (nth 0 l n)) e1 * 0) by ring.
rewrite -(interp_subst n _ e2).
apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).
now apply IHe1.
apply (is_deriv_eq (fun x => interp (set_nth 0 l n 0) e2)).
apply H2.
apply derivable_pt_lim_const.
(* . *)
clear C2.
case o ; simpl ;
  intros (H1&H2&_) ;
  specialize (IHe1 H1) ;
  specialize (IHe2 H2).
now apply derivable_pt_lim_plus.
rewrite -(interp_subst n _ e1) -(interp_subst n _ e2).
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
apply ex_RInt_correct_2.
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
now apply Rabs_le_encadre_cor.
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
apply (is_deriv_eq (comp (fun x => RInt (fun t => interp (t :: l) e1) (interp (set_nth 0 l n (nth 0 l n)) e2) x) (fun x => interp (set_nth 0 l n x) e3))).
intros t.
unfold comp.
rewrite -(is_const_correct e2 n C2 l (nth 0 l n)).
apply RInt_rw.
intros z _.
rewrite -(interp_subst (S n)).
apply (is_const_correct e1 (S n) C1 (z :: l)).
apply derivable_pt_lim_comp.
now apply IHe3.
rewrite 2!interp_subst.
apply derivable_pt_lim_RInt with (1 := Hi).
now apply HexI.
now apply locally_singleton.
clear C2.
case C3: (is_const e3 n).
(* . *)
simpl.
intros (H2&Hi&H1&_).
rewrite Rmult_comm -Ropp_mult_distr_l_reverse.
apply (is_deriv_eq (fun x => comp (fun x => RInt (fun t => interp (t :: l) e1) x (interp (set_nth 0 l n (nth 0 l n)) e3)) (fun x => interp (set_nth 0 l n x) e2) x)).
intros t.
unfold comp.
rewrite -(is_const_correct e3 n C3 l (nth 0 l n)).
apply RInt_rw.
intros z _.
rewrite -(interp_subst (S n)).
apply (is_const_correct e1 (S n) C1 (z :: l)).
apply (derivable_pt_lim_comp (fun x0 : R => interp (set_nth 0 l n x0) e2)
  (fun x0 : R => RInt (fun t : R => interp (t :: l) e1) x0 (interp (set_nth 0 l n (nth 0 l n)) e3))).
now apply IHe2.
rewrite 2!interp_subst.
apply derivable_pt_lim_RInt' with (1 := Hi).
now apply HexI.
now apply locally_singleton.
(* . *)
clear C3.
simpl.
intros (H2&H3&Hi&H12&H13&_).
apply (is_deriv_eq (fun x => RInt (fun t => interp (t :: l) e1) (interp (set_nth 0 l n x) e2) (interp (set_nth 0 l n x) e3))).
intros t.
apply RInt_rw.
intros z _.
rewrite -(interp_subst (S n)).
apply (is_const_correct e1 (S n) C1 (z :: l)).
rewrite -(interp_subst n l e2) -(interp_subst n l e3).
apply derivable_pt_lim_RInt_bound_comp.
now rewrite 2!interp_subst.
rewrite interp_subst.
now apply HexI.
rewrite interp_subst.
now apply HexI.
rewrite interp_subst.
now apply locally_singleton.
rewrite interp_subst.
now apply locally_singleton.
now apply IHe2.
now apply IHe3.
(* . *)
admit.
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

Section DomainInduction.

Hypothesis P : domain -> Prop.
Hypothesis P_Never : P Never.
Hypothesis P_Always : P Always.
Hypothesis P_Derivable : forall k f le n, P (Derivable k f le n).
Hypothesis P_Continuous : forall e, P (Continuous e).
Hypothesis P_Integrable : forall f e1 e2, P (Integrable f e1 e2).
Hypothesis P_And : forall ld, foldr (fun d acc  => P d /\ acc) True ld -> P (And ld).
Hypothesis P_Forall : forall e1 e2 d, P d -> P (Forall e1 e2 d).
Hypothesis P_Locally : forall e d, P d -> P (Locally e d).

Fixpoint domain_ind' (d : domain) : P d :=
  match d return P d with
  | Never => P_Never
  | Always => P_Always
  | Derivable k f le n => P_Derivable k f le n
  | Continuous e => P_Continuous e
  | Integrable f e1 e2 => P_Integrable f e1 e2
  | And ld => P_And ld
    ((fix domain_ind'' (ld : seq domain) : foldr (fun d acc => P d /\ acc) True ld :=
       match ld return foldr (fun d acc => P d /\ acc) True ld with
       | nil => I
       | cons h q => conj (domain_ind' h) (domain_ind'' q)
       end) ld)
  | Forall e1 e2 d => P_Forall e1 e2 d (domain_ind' d)
  | Locally e d => P_Locally e d (domain_ind' d)
  end.

End DomainInduction.

Lemma simplify_domain_correct :
  forall d l,
  interp_domain l (simplify_domain d) -> interp_domain l d.
Proof.
intros d.
induction d using domain_ind' => l ; try easy.
(* And *)
simpl.
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
case (simplify_domain t).
(* . *)
now intros _ (H,_).
(* . *)
exact (fun H1 H2 => conj (H1 l I) (IHld Hb H2)).
(* . *)
simpl.
intros k f' le n H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
simpl.
intros e H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
simpl.
intros e0 e1 e2 H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
simpl.
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
simpl.
intros e1 e2 d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* . *)
simpl.
intros e d H1 (H2,H3).
exact (conj (H1 l H2) (IHld Hb H3)).
(* Forall *)
simpl.
revert IHd.
assert (HH: forall d', (forall l, interp_domain l d' -> interp_domain l d) ->
  interp_domain l (Forall e1 e2 d') -> interp_domain l (Forall e1 e2 d)).
simpl.
intros d' H1 (eps,H2).
exists eps => t Ht.
apply H1.
now apply H2.
destruct (simplify_domain d) ; try (apply HH ; fail).
simpl.
intros H _.
exists (mkposreal _ Rlt_0_1) => t Ht.
now apply H.
(* Locally *)
simpl.
revert IHd.
assert (HH: forall d', (forall l, interp_domain l d' -> interp_domain l d) ->
  interp_domain l (Locally e d') -> interp_domain l (Locally e d)).
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
    | _ => constr:(fct, l, i)
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
  is_deriv (fun x => interp (set_nth R0 l n x) e) (nth R0 l n) (interp l a).
Proof.
intros e l n.
generalize (D_correct e l n).
destruct (D e n) as (d1,d2).
intros H1 H2.
apply H1.
now apply simplify_domain_correct.
Qed.

Ltac auto_derive_expr f v :=
  let f := eval cbv beta in (f (var O)) in
  let e := reify f O in
  let H := fresh "H" in
  assert (H := auto_derive_helper e (v :: nil) 0) ;
  simpl in H ;
  try specialize (H I) ;
  revert H.

Ltac auto_derive :=
  match goal with
  | |- derivable_pt_lim ?f ?v ?l =>
    auto_derive_expr f v ;
    let H := fresh "H" in
    intro H ;
    refine (eq_ind _ (derivable_pt_lim _ _) (H _) _ _) || refine (eq_ind _ (derivable_pt_lim _ _) H _ _) ;
    clear H
  end.

Goal forall f x, derivable_pt_lim (fun y => f (2 * x) + RInt (fun z => z) 0 y + 2 * y) x 0.
intros f x.
auto_derive.
2: ring_simplify.
Abort.