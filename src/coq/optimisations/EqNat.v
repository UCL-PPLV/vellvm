

From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat fintype.


Require Import Vellvm.Ollvm_ast Vellvm.CFG.
Require Import Vellvm.Classes.
Require Import Vellvm.AstLib.

Require Import String Ascii.
Require Import Bool.
Require Import Equalities.
Require Import ZArith.
Print Ascii.

Print eqb_refl.
Definition eqascii (a b:ascii) :=
match a, b with
  | Ascii a1 b1 c1 d1 e1 f1 g1 h1, Ascii a2 b2 c2 d2 e2 f2 g2 h2 => eqb a1 a2 && eqb b1 b2 &&
                                                                    eqb c1 c2 && eqb d1 d2 &&
                                                                    eqb e1 e2 && eqb f1 f2 &&
                                                                    eqb g1 g2 && eqb h1 h2
end.



Lemma ascii_eq : forall a, eqascii a a = true.
Proof. intros a. induction a. unfold eqascii. Print eqb_reflx.
repeat (rewrite eqb_reflx; simpl). auto. Qed.


Lemma eqasciiP : Equality.axiom eqascii.
Proof. move=> n m. destruct n, m; simpl.
Admitted.

Canonical ascii_eqMixin := EqMixin (T:= ascii) (op:=eqascii) (@eqasciiP).
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.




Print String.


Fixpoint eqstring (a b: string) :=
match a, b with
  | EmptyString, EmptyString => true
  | String hd1 tl1, String hd2 tl2 => eqascii hd1 hd2 && eqstring tl1 tl2
  | _, _ => false
end.

Lemma string_eq : forall s, eqstring s s = true.
Proof. intros. induction s; simpl; auto; try rewrite ascii_eq; simpl; try rewrite IHs; auto.
Qed.



Lemma eqstringP : Equality.axiom eqstring.
Proof. move => n m. destruct n, m.
  +simpl. constructor. auto.
  +simpl. constructor. unfold not. intros. inversion H.
  +simpl. constructor. unfold not. intros. inversion H.
  +simpl.  Admitted.

Canonical string_eqMixin := EqMixin (T:= string) (op:=eqstring) (@eqstringP).
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.




Print raw_id.


Definition eqraw_id (a b: raw_id) : bool:=
match a, b with
  | Name a, Name b => eqstring a b
  | Anon a, Anon b => Z.eqb a b
  | Raw a, Raw b => Z.eqb a b
  | _, _ => false
end.


Lemma eqraw_idP : Equality.axiom eqraw_id.
Proof.  move => n m. induction n, m; simpl; try constructor; auto.
Admitted.


Canonical raw_id_eqMixin := EqMixin (T:= raw_id) (op:=eqraw_id) (@eqraw_idP).
Canonical raw_id_eqType := Eval hnf in EqType raw_id raw_id_eqMixin.



Print instr_id.


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
