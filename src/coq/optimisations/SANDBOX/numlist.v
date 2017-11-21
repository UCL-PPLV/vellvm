
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat fintype.


Definition larger_than (n m:nat) := if n < m then m else n.

Definition list := seq nat.

Definition maximum n := foldr larger_than 0 n.


Definition test : seq nat := cons 1 (cons 2 (cons 3 nil)).


Lemma test1: forall n, n + 1 != n.
Proof. move =>// n; induction n=>//. Qed.

Require Import Omega.
Lemma max_plus_one_not_in_single_list : forall n, (maximum [::n]) + 1 \notin [::n].
Proof. move => //n. induction n =>//. Qed.
Print in_mem.

Lemma testtest : forall a, (a + 1 == a) = false.
Proof. move =>//a. induction a => //. Qed.

Lemma testtest1: forall a n, (maximum (a :: n) + 1 \notin a :: n) = ((maximum (a::n) + 1 \notin [::a]) || (maximum (a::n) + 1 \notin n)).
Proof. move =>//a n. induction n => //. simpl. unfold negb. rewrite /larger_than/= => //. rewrite /in_mem/=. simpl.
induction a =>//.
rewrite /maximum/=. simpl. rewrite /negb/= => //.


Lemma max_plus_one_not_in_list : forall n, (maximum n) + 1 \notin n.
Proof. move => //n.
induction n => //.












 rewrite /nilp/= in H. rewrite /negb/= in H.
induction n => //. rewrite /maximum/=.  rewrite /negb/=.
rewrite /in_mem/=. simpl. simpl. induction n. simpl in *. rewrite testtest. simpl. auto.
simpl. rewrite /larger_than/= in IHn0.
rewrite /larger_than/=. simpl in *.
Admitted.


