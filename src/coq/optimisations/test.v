From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
From Heaps
Require Import idynamic ordtype finmap pcm unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Combine.

Parameters (V : eqType).
Parameter K : ordType.
Parameter f : V -> V -> V.

Fixpoint _combine_helper (ks : seq K) (m1 m2 acc : union_map K V) :=
  if ks is k :: ks'
  then
    match (find k m1, find k m2) with
    | (Some v1, Some v2) => k \\-> (f v1 v2) \+ acc
    | (Some v1, None) => k \\-> v1 \+ acc
    | (None, Some v2) => k \\-> v2 \+ acc
    | _ => acc
    end
  else acc.

Definition combine m1 m2 :=
  _combine_helper (undup (keys_of m1 ++ keys_of m2)) m1 m2 Unit.

Theorem combine_valid m1 m2 :
  valid m1 -> valid m2 -> valid (combine m1 m2).
Proof.
(* 

Induction on the keys of the maps, also check
the induction lemmas um_indf and um_indb.

 *)


End Combine.