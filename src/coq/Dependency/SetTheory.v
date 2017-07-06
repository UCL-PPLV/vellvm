From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun 
  ssrnat seq.

Require Import Vellvm.Dependency.DEPIMP.


(** Some set theory functions needed before declaring the data dependency theorem **)
(** Union **)

Fixpoint findId (a: DEPIMP.id) (b: seq DEPIMP.id)  :=
  match b with
  | nil => false
  | t::ts => beq_id a t || findId a ts
end.

Fixpoint compareSeqId (a b: seq DEPIMP.id) :=
  match a with
  | nil => b
  | t::ts => if findId t b then (compareSeqId ts b) else (compareSeqId ts (t::b))
end.

Fixpoint union (a b: seq DEPIMP.id) := compareSeqId (compareSeqId a nil) (compareSeqId b nil).

Fixpoint intersection (a b: seq DEPIMP.id) :=
  match a with
  | nil => nil
  | t::ts => if findId t b then (t :: intersection ts b) else (intersection ts b)
end.



Notation "x 'U' a" :=
  (union x a) (at level 60).


Notation "x 'N' a" :=
  (intersection x a) (at level 60).

