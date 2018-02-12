From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat finset fintype.
(*

Definition eqinstr_id (a b:instr_id) : bool :=
match a, b with
  | (IId h1), (IId h2) => eqraw_id h1 h2
  | (IVoid h1), (IVoid h2) => Z.eqb h1 h2
  | _, _ => false
end
.

Lemma eqinstr_idP : Equality.axiom eqinstr_id.
Proof. move => n m. induction n, m; simpl; try constructor; auto.
  +simpl. admit.
  +admit.
Admitted.


Canonical instr_id_eqMixin := EqMixin (T:= instr_id) (op:=eqinstr_id) (@eqinstr_idP).
Canonical instr_id_eqType := Eval hnf in EqType instr_id instr_id_eqMixin.

Print instr.
Print value.
Print Expr.
Print ident.

Definition eqident (a b: ident) :=
match a, b with
  | ID_Global c, ID_Global d => eqraw_id c d
  | ID_Local c, ID_Local d => eqraw_id c d
  | _, _ => false
end.



*)


Require Import Coq.Arith.EqNat.

Definition nat_tuple : Set := (nat * nat).
Definition eq_nat_tuple (a b: nat_tuple) := beq_nat (fst a) (fst b) && beq_nat (snd a) (snd b).
Print eq_nat_tuple.

Lemma eq_nat_idP : Equality.axiom eq_nat_tuple.
Proof. move => n m. induction n, m. simpl in *. induction a, b; simpl in *; unfold eq_nat_tuple; simpl in *; induction n, n0; simpl in *; eauto; try constructor; simpl in *; eauto. Admitted.

Canonical nat_tuple_eqMixin := EqMixin (T:= nat_tuple) (op:=eq_nat_tuple) (@eq_nat_idP ).
Canonical instr_id_eqType := Eval hnf in EqType nat_tuple nat_tuple_eqMixin.
Canonical rinstr_id_eqType := Eval hnf in FinType nat_tuple  instr_id_eqType.
