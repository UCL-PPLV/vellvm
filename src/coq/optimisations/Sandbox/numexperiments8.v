Require Import Equivalence EquivDec.
Require Import Coqlib.
Require Import Vellvm.CFG.
Require Import Vellvm.DecidableEquality.
Require Import Vellvm.DecidableProp.
Require Import Vellvm.optimisations.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
  Require Import ZArith List String Omega.

Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.


Require Import compcert.lib.Maps.



Set Implicit Arguments.



Print N.eq_dec.


Print TREE.
Print peq.




Module NTree <: TREE.

  Definition elt := nat.
  Definition elt_eq := N.eq_dec.
  Print elt_eq.
  Print TREE.
End NTree.