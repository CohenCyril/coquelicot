Require Import Reals ssreflect.
Add LoadPath "~/Documents/coquelicot/coquelicot/theories".
Require Import Rcomplements RInt.
Require Import Lim_fct Rbar_theory.

Ltac pos_rat :=
  repeat ( apply Rdiv_lt_0_compat
         || apply Rplus_lt_0_compat 
         || apply Rmult_lt_0_compat) ;
  try by apply Rlt_0_1.






