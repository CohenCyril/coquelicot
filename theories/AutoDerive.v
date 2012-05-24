Require Import Reals.
Require Import ssreflect seq.
Require Import Arithmetique Locally Deriv_fct RInt.

Fixpoint Rn n :=
  match n with
  | O => R
  | S n => R -> Rn n
  end.

Inductive bop :=
  | Eplus
  | Emult.

Inductive uop :=
  | Eopp.

Inductive expr :=
  | Var : nat -> expr
  (*| AppExt : forall k, Rn k -> seq expr -> expr*)
  | App : expr -> expr -> expr
  | Subst : expr -> expr -> expr
  | Cst : R -> expr
  | Binary : bop -> expr -> expr -> expr
  | Unary : uop -> expr -> expr
  | Int : expr -> expr -> expr -> expr.

Fixpoint apply p : Rn p -> seq R -> R :=
  match p return Rn p -> seq R -> R with
  | O => fun (x : R) l => x
  | S p => fun (f : Rn (S p)) l => match l with h::q => apply p (f h) q | nil => apply p (f R0) l end
  end.

Fixpoint interp (l : seq R) (e : expr) : R :=
  match e with
  | Var n => nth R0 l n
  (*| AppExt k f le => apply k f (map (interp l) le)*)
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
  | Derivable : expr -> nat -> domain
  | Integrable : expr -> expr -> expr -> domain
  | And : seq domain -> domain
  | Forall : expr -> expr -> domain -> domain.

Fixpoint interp_domain (l : seq R) (d : domain) : Prop :=
  match d with
  | Never => False
  | Always => True
  | Derivable e n => ex_deriv (fun x => interp (set_nth R0 l n x) e) (nth R0 l n)
  | Integrable f e1 e2 => ex_RInt (fun x => interp (x :: l) f) (interp l e1) (interp l e2)
  | And ld => foldr (fun d acc => interp_domain l d /\ acc) True ld
  | Forall e1 e2 s =>
    let a1 := interp l e1 in let a2 := interp l e2 in
    exists eps : posreal, forall t, -eps < t < 1 + eps ->
    interp_domain (a1 + t * (a2 - a1) :: l) s
  end.

Fixpoint is_const (e : expr) n : bool :=
  match e with
  | Var v => negb (ssrnat.eqn v n)
  | Cst _ => true
  | App f e => andb (is_const f (S n)) (is_const e n)
  | Subst f e => andb (orb (ssrnat.eqn n 0) (is_const f n)) (is_const e n)
  | Binary b e1 e2 => andb (is_const e1 n) (is_const e2 n)
  | Unary u e => is_const e n
  | Int f e1 e2 => andb (is_const f (S n)) (andb (is_const e1 n) (is_const e2 n))
  end.

Lemma is_const_correct :
  forall e n, is_const e n ->
  forall l x1 x2,
  interp (set_nth 0 l n x1) e = interp (set_nth 0 l n x2) e.
Proof.
induction e.
(* *)
simpl => k Hk l x1 x2.
rewrite 2!nth_set_nth /=.
now rewrite -ssrnat.eqnE (ssrbool.negbTE Hk).
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
    (Binary Eplus
      (Binary Eplus
        (Binary Emult a2 (App f e2))
        (Unary Eopp (Binary Emult a1 (App f e1))))
      (Int a3 e1 e2), And (b1::b2::(Forall e1 e2 b3)::(Integrable f e1 e2)::nil))
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
induction e.
(* *)
simpl => k l.
rewrite nth_set_nth /= /eqtype.eq_op /=.
case ssrnat.eqnP.
move => -> //.
easy.
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

Lemma D_correct :
  forall (e : expr) l n,
  let '(a,b) := D e n in
  interp_domain l b ->
  is_deriv (fun x => interp (set_nth R0 l n x) e) (nth R0 l n) (interp l a).
Proof.
induction e.
(* *)
simpl => l k _.
apply is_deriv_eq with (fun x => if ssrnat.eqn n k then x else nth 0 l n).
intros t.
now rewrite nth_set_nth.
case ssrnat.eqnP => [H|H].
apply derivable_pt_lim_id.
apply derivable_pt_lim_const.
(* *)
simpl => l n [].
(* *)
simpl => l n [].
(* *)
simpl => l n _.
apply derivable_pt_lim_const.
(* *)
simpl => l n.
specialize (IHe1 l n).
specialize (IHe2 l n).
destruct (D e1 n) as (a1,b1).
destruct (D e2 n) as (a2,b2).
case C1: (is_const e1 n).
(* . *)
assert (H1 := is_const_correct e1 n C1 l).
case b ; intros H2.
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
case b ; intros H1.
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
case b ; simpl ;
  intros (H1&H2&_) ;
  specialize (IHe1 H1) ;
  specialize (IHe2 H2).
now apply derivable_pt_lim_plus.
rewrite -(interp_subst n _ e1) -(interp_subst n _ e2).
now apply (derivable_pt_lim_mult (fun x => interp (set_nth 0 l n x) e1) (fun x => interp (set_nth 0 l n x) e2)).
(* *)
simpl => l n.
specialize (IHe l n).
destruct (D e n) as (a,b).
case u.
simpl.
intros H.
apply derivable_pt_lim_opp.
now apply IHe.
(* *)
simpl => l n.
specialize (IHe2 l n).
specialize (IHe3 l n).
move: (fun l => IHe1 l (S n)) => {IHe1} IHe1.
destruct (D e1 (S n)) as (a1,b1).
destruct (D e2 n) as (a2,b2).
destruct (D e3 n) as (a3,b3).
simpl.
intros (H2&H3&(eps,H1)&_).
specialize (IHe2 H2).
specialize (IHe3 H3).
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
  | _ => d
  end.

Section DomainInduction.
Hypothesis P : domain -> Prop.
Hypothesis P_Never : P Never.
Hypothesis P_Always : P Always.
Hypothesis P_Derivable : forall e n, P (Derivable e n).
Hypothesis P_Integrable : forall f e1 e2, P (Integrable f e1 e2).
Hypothesis P_And : forall ld, foldr (fun d acc  => P d /\ acc) True ld -> P (And ld).
Hypothesis P_Forall : forall e1 e2 d, P d -> P (Forall e1 e2 d).

Fixpoint domain_ind' (d : domain) : P d :=
  match d return P d with
  | Never => P_Never
  | Always => P_Always
  | Derivable e n => P_Derivable e n
  | Integrable f e1 e2 => P_Integrable f e1 e2
  | And ld => P_And ld
    ((fix domain_ind'' (ld : seq domain) : foldr (fun d acc => P d /\ acc) True ld :=
       match ld return foldr (fun d acc => P d /\ acc) True ld with
       | nil => I
       | cons h q => conj (domain_ind' h) (domain_ind'' q)
       end) ld)
  | Forall e1 e2 d => P_Forall e1 e2 d (domain_ind' d)
  end.

End DomainInduction.

Lemma simplify_domain_correct :
  forall d l,
  interp_domain l (simplify_domain d) -> interp_domain l d.
Proof.
intros d.
induction d using domain_ind' => l ; try easy.
(* *)
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
intros e n H1 (H2,H3).
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
(* *)
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

Goal forall x, derivable_pt_lim (fun y => RInt (fun z => y + z) 0 y + 2 * y) x (3 * x + 2).
intros x.
auto_derive.
ring_simplify.
