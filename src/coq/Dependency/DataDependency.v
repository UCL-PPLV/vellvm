Require Import List.
Require Import Nat.
Require Import Bool.

Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.

From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.





(*Util + Maps*)
Inductive id : Type :=
  | Id : nat -> id.

Definition total_map (A:Type) := id -> A.

Definition state := total_map nat.



Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.


Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.


Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.


Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).


Definition empty_state : state :=
  t_empty 0.






Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.



(*IMP*)



Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Inductive com : Type :=
  | CAss : id -> aexp -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.




Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.


Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).


Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).



Inductive ceval : com -> state -> state -> Prop :=
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').


(*********************************************************************************)


(*Get all the previous instructions*)

Inductive instruction :=
  | ins (v:com) (a:nat).



Variable (l: seq instruction).



Definition equalInstruction (b:instruction) (a:instruction) :=
  match b,a with
  | (ins _ c), (ins _ d) => (beq_nat c d)
end.




Check find.

(* Get a list of all the previous instructions *)
Definition getInstructionList (b:instruction) := 
  let i := find (equalInstruction b) l in
  match i with
  | 0 => None
  | a.+1 => Some (drop a l)
end.


(*
Fixpoint checkAssignment (c:com) (i:id) :=
  match c with
  | CIf a b c => checkAssignment c i
  | CWhile a b => checkAssignment b i
  | CAss a b => if beq_nat a i then 1 else 0
end.
*)







Fixpoint checkRead (a:aexp) (i:id) :=
  match a with
  | ANum _ => 0
  | AId b => if b = i then 1 else 0
  | APlus c b => checkRead c i + checkRead b i
  | AMinus c b => checkRead c i + checkRead b i
  | AMult c b => checkRead c i + checkRead b i
end.


































(*********************************************************************)
(*SCRAP IDEAS*)
(*********************************************************************)

Inductive variable :=
  | A
  | B
  | C
  | const (cs:nat).


Inductive dependency :=
  | Dep (v:variable) (a:nat) (b:nat).


Inductive state :=
  | st (v:variable) (a:nat).


Variable (l: seq dependency).
Variable (s: list state).



Definition equalVar (a b: variable) :=
  match a, b with
  | A, A => true
  | B, B => true
  | C, C => true
  | _, _ => false
end.



Definition equalDep (b:variable) (a : dependency) :=
  match a with
  | (Dep c _ _) => equalVar b c
end.


Definition equalState (b:variable) (a:state) :=
  match a with
  | (st a _) => equalVar a b
end.


Definition findDep (b:variable) := find (equalDep b) l.

Definition findVarState (b:variable) := find (equalState b) s.


Fixpoint getItem (A:Type) (l:list A) (n:nat) :=
  match l, n with
  | nil,_  => None
  | (a::s), 0 => Some a
  | (a::s), b.+1 => getItem A s b
end.


Print find.





Definition retrieveVar (b:variable) :=
  let vr := findVarState b in
  match vr with
  | 0 => None
  | a.+1 => let x := getItem state s a in
            match x with
            | None => None
            | Some (st d e) => Some e
            end
end.



Definition setVariable (b:variable) (n:nat) := 0.











Inductive instruction :=
  | Add (pc:nat) (v1:variable) (v2:variable) (v3:variable)
.


Check foldr.



Variable (V: nat)(E: Type)(r: seq instruction).
Definition sum := foldr countAinV1 0 r.
(*c