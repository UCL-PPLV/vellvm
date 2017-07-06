Require Import Coq.Strings.String.

(*Util + Maps*)
Inductive id : Type :=
  | Id : string -> id.

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



Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
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



(* AST *)


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
  | CIf : bexp ->  com ->  com -> com
  | CWhile : bexp ->  com -> com
  | CSeq : com -> com -> com
  | CFor : id -> nat -> nat -> com -> com
  | CFrom : nat -> nat -> com -> com
  | CSkip : com.


Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'FOR' i 'FROM' e 'TO' j 'DO' k 'OD'" :=
  (CFor i e j k)  (at level 80, right associativity).

Notation "'FROM' e 'TO' j 'DO' k 'OD'" :=
  (CFrom e j k)  (at level 80, right associativity).

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).


Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
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



Print t_update.


Fixpoint while_eval (st:state) (b:bexp) (c:com) : state :=
  let val := beval st b in
  match val with
  | true => st
  | false => st
end.
(*
Fixpoint ceval_fix (st:state) (c:com) : state :=
  match c with
  | CAss a b => (t_update st a (aeval st b))
  | CIf a b c => if (beval st a) then (ceval_fix st b) else (ceval_fix st c)
  | CSkip => st
  | 
end.
*)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
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


  (*For loop*)
  | E_ForEnd : forall st  a2 n x k,
      (x ::= (ANum n)) / st \\ (t_update st x n) -> 
      beq_nat n a2 = true -> 
      (FOR x FROM n TO a2 DO k OD) / st \\ st


  | E_ForLoop : forall st st' st'' a2 n x k,
      (x ::= (ANum n)) / st \\ (t_update st x n) -> 
      beq_nat n a2 = false -> k / st \\ st' -> 
      (FOR x FROM (n + 1) TO a2 DO k OD) / st' \\ st''-> 
      (FOR x FROM n TO a2 DO k OD) / st \\ st''




  (*From Loop*)
  | E_FromEnd : forall st a2 n k,
      beq_nat n a2 = true -> 
      (FROM n TO a2 DO k OD) / st \\ st
  | E_FromLoop : forall st st' st'' a2 n k,
      beq_nat n a2 = false -> k / st \\ st' -> 
      (FROM (n + 1) TO a2 DO k OD) / st' \\ st''-> 
      (FROM n TO a2 DO k OD) / st \\ st''



  where "c1 '/' st '\\' st'" := (ceval c1 st st').




(*Sample Variables*)


Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".




(*********************************************************************************)


