Require Import compcert.lib.Maps.

Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.

Require Import Equalities.
Module pc_list.

  Definition elt := instr_id.
  Definition elt_eq := forall (x y : instr_id), {x = y} + {x <> y}.

  Definition t (A : Type) : Type := list (instr_id * A).


  Definition set (A: Type) (p:instr_id) (x: A) (m: t A) := (p, x) :: m.

  Fixpoint get (A: Type) (p:instr_id) (m: t A) : option A :=
    match m with
    | nil => None
    | (x, i) :: tl => if decide (x = p) then Some i else (get A p tl)
   end.                                                     

   Fixpoint remove (A: Type) (p:instr_id) (m: t A) : t A :=
    match m with
    | nil => nil
    | (x, i) :: tl => if decide (x = p) then tl else (remove A p tl)
   end.           
    End pc_list.