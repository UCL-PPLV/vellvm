Require Import EqNat.

(* Consider the following structure: *)

Definition iid := nat.
Definition data := nat.

Definition bid := nat.
Definition fid := nat.

Definition listA := list (bid * data).


Fixpoint find (b:bid) (l:listA) : option data :=
match l with
  | nil => None
  | ((fst, snd) :: tl)%list => if beq_nat fst b then Some snd else find b tl
end.



Definition two_fold (b:bid) (l l1:listA) : option data :=
match (find b l) with
  | None => match (find b l1) with
           | None => None
           | Some a => Some a
            end
  | Some a => Some a
end.



Lemma two_consecutive_eq 