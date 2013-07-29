(**
This library provides vernacular files containing a formalization of real
analysis for Coq. It is a conservative extension of the standard library Reals
with a focus on usability. It has been developed by Sylvie Boldo, Catherine
Lelay, and Guillaume Melquiond.

The goal of Coquelicot is to ease the writing of formulas and
theorem statements for real analysis. This is achieved by using total functions in place of
dependent types for limits, derivatives, integrals, power series, and so on.
To help with the proof process, the library comes with a comprehensive set
of theorems that cover not only these notions, but also some extensions such
as parametric integrals, two-dimensional differentiability, asymptotic
behaviors. It also offers some automations for performing differentiability
proofs. Since Coquelicot is a conservative extension of Coq's standard
library, we provide correspondence theorems between the two libraries.

Total functions:
- [Lim_seq : (nat -> R) -> Rbar]
- [Lim : (R -> R) -> Rbar -> Rbar]
- [Derive : (R -> R) -> R -> R]
- [RInt : (R -> R) -> R -> R -> R]
- [Series : (nat -> R) -> R]
- [PSeries : (nat -> R) -> R -> R]
- [CV_radius : (nat -> R) -> Rbar]


The corresponding predicates are:
- [is_lim_seq : (nat -> R) -> Rbar -> Prop]
- [is_lim : (R -> R) -> Rbar -> Rbar -> Prop]
- and so on, except for [CV_radius].


There are also predicates in case the actual limit does not matter:
- [ex_lim_seq : (nat -> R) -> Prop]
- and so on.


Naming conventions:
- Correspondence theorems with the standard library contain [_Reals] in their name.
- Extensionality theorems contain [_ext] in their name.
  If the equality only needs to be local, they also contain [_loc].
- Uniqueness theorems contain [_unique] in their name.
- Theorems about asymptotic behaviors are suffixed by [_p] or [_m]
  if they are at infinite points.
*)

Require Export AutoDerive Compactness Continuity Derive.
Require Export Derive_2d Equiv ElemFct Limit.
Require Export Locally Lub Markov PSeries Rbar Rcomplements.
Require Export RInt Seq_fct Series SF_seq.