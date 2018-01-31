

Require Import Coq.Arith.EqNat.
Require Import List.




Definition pair1 : Set := (nat * option nat).




Fixpoint get1 (n:nat) (l:list pair1) :=
  match l with
  | nil => None
  | hd :: tl => if beq_nat (fst hd) n then Some (snd hd) else get1 n tl
  end.
Definition beq_pair1 (p p1:pair1) : bool :=
  match p, p1 with
  | (k, None), (k1, None) => (beq_nat k k1)
  | (k, Some a), (k1, Some b) => (beq_nat k k1) &&  (beq_nat a b)
  | (k, None), (k1, Some b) => (beq_nat k k1)
  | _, _ => false
  end.



Fixpoint list_eq2 (l l1: list pair1) : bool :=
  match l, l1 with
  | nil, nil => true
  | l1, nil => false
  | nil, l1 => true
  | hd::tl, hd1::tl1 => (beq_pair1 hd hd1) && (list_eq2 tl tl1)
  end.






Lemma test12: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> In (n, Some a) l1 -> In (n, Some a) l2.

Proof. induction l2. intros.  destruct l1. simpl in *. inversion H0.
 simpl in *. inversion H.
       intros. simpl in *. induction l1. simpl in *. inversion H0. 
simpl in *. remember (beq_pair1 a1 a). destruct b. simpl in *.
 inversion H0. left. unfold beq_pair1 in *. simpl in *. destruct a1.
 simpl in *. destruct a. simpl in *. destruct o. destruct o0. simpl in *.
       remember (PeanoNat.Nat.eqb n0 n1). destruct b.
apply beq_nat_eq in Heqb0. subst. 
remember (PeanoNat.Nat.eqb n2 n3). destruct b. 
apply beq_nat_eq in Heqb0. subst. auto. simpl in *. 
inversion Heqb. simpl in *. inversion Heqb.
 inversion Heqb. destruct o0. simpl in *. 
inversion H1. inversion H1.
right.

eapply IHl2 in H; eauto. simpl in *. inversion H. Qed.



    Lemma In_conv : forall l e1 i1, Some e1 = get1 i1 l -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb n i1). destruct b. inversion H. subst. left. apply beq_nat_eq in Heqb. subst. auto. right. apply IHl. apply H. Qed.




(*IN CONV TEST12*)

Lemma test12313: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> Some (Some a) = get1 n l1 ->  In (n, Some a) l2.
Proof. intros. eapply In_conv in H0. eapply test12; eauto. Qed.




(*test12313*)


Lemma tes3t12313: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> Some (Some a) = get1 n l1 -> Some (Some a) = get1 n l2.
Proof. induction l2. simpl in *. intros. simpl in *. destruct l1. simpl in *. inversion H0. simpl in *. inversion H.


       intros. generalize H; intros. eapply test12313 in H; eauto. 
simpl in *. destruct a. simpl in *. inversion H. inversion H1. (*here 2*)
induction l1. simpl in *. inversion H0. simpl in *. destruct a. 
simpl in *. destruct o0, o; simpl in *. remember (PeanoNat.Nat.eqb n1 n0).
       destruct b. apply beq_nat_eq in Heqb. subst. simpl in *.
 remember (PeanoNat.Nat.eqb n2 n3). destruct b. simpl in *. 
eapply beq_nat_eq in Heqb. subst. simpl in *.
 remember (PeanoNat.Nat.eqb n0 n). destruct b. 
apply beq_nat_eq in Heqb. subst. auto. simpl in *.
 eapply IHl2.
       apply H1. auto. simpl in *. inversion H1. 
simpl in *. inversion H1. simpl in *. inversion H4.
 simpl in *.
       remember ( PeanoNat.Nat.eqb n1 n). destruct b.
 inversion H0. simpl in *. remember  (PeanoNat.Nat.eqb n1 n0).
 destruct b. simpl in *. apply beq_nat_eq in Heqb0. subst.
 simpl in *. remember ( PeanoNat.Nat.eqb n0 n). destruct b.
 simpl in *. inversion Heqb. simpl in *. eapply IHl2.
       apply H1. apply H0. simpl in *. inversion H1. 
simpl in *.
remember ( PeanoNat.Nat.eqb n1 n). destruct b. inversion H0.
 remember (PeanoNat.Nat.eqb n1 n0). destruct b. apply beq_nat_eq in Heqb0.
 subst. simpl in *.
 remember ( PeanoNat.Nat.eqb n0 n). destruct b. inversion Heqb.
 simpl in *. eapply IHl2; eauto.
simpl in *. inversion H1.
       (*HERE 1*) 
       induction l1. simpl in *. inversion H0. simpl in *. 
destruct a. simpl in *. destruct o0, o. simpl in *.
       remember (PeanoNat.Nat.eqb n1 n0). 
remember ( PeanoNat.Nat.eqb n2 n3). destruct b, b0.
 eapply beq_nat_eq in Heqb; eapply beq_nat_eq in Heqb0. 
subst. simpl in *.
(*7*)
remember (PeanoNat.Nat.eqb n0 n). destruct b. simpl in *.
 auto. simpl in *. eapply IHl2; eauto.
(*6*)
       simpl in *. inversion H1. simpl in *. inversion H1.
 simpl in *. inversion H1. simpl in *. inversion H1. simpl in *.
       remember (PeanoNat.Nat.eqb n1 n0). destruct b. 
apply beq_nat_eq in Heqb. subst. remember ( PeanoNat.Nat.eqb n0 n). destruct b. simpl in *. inversion H0. simpl in *. eapply IHl2. apply H1. apply H0. simpl in *. inversion H1. simpl in *.
       remember (PeanoNat.Nat.eqb n0 n). destruct b. 
apply beq_nat_eq in Heqb. subst. remember ( PeanoNat.Nat.eqb n1 n). destruct b. eapply beq_nat_eq in Heqb. inversion H0. simpl in *. inversion H1. simpl in *. remember ( PeanoNat.Nat.eqb n1 n). destruct b. inversion H0. simpl in *.
       remember (PeanoNat.Nat.eqb n1 n0). destruct b.
 simpl in *. eapply beq_nat_eq in Heqb1. subst. 
eapply IHl2; eauto. simpl in *. inversion H1. Qed.