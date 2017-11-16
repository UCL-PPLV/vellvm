(* Consider the following structure: *)

Definition iid := nat.
Definition data := nat.

Definition bid := nat.
Definition fid := nat.

Definition listA := list (bid * data).
Definition listB := list (fid * listA).


Fixpoint searchListA (b:bid) (l:listA) : option (bid * data) :=
match l with
  | nil => None
  | (_::_)%list => None
end.
