Require Import List.
Require Import Coq.Arith.EqNat.
Definition pair : Set := (nat * option nat).

Definition pair_list := list pair.




Fixpoint combine (f:option nat -> option nat -> option nat) (p:pair_list) :=
  match p with
  | nil => nil
  | (key, val) :: tl => (key, f val val) :: combine f tl                                                
  end.


Fixpoint get (p:pair_list) (k:nat) :=
         match p with
         | nil => None
         | (key, val) :: tl => if beq_nat key k then val else get tl k
         end.
Lemma transitivity : forall p f i, f None None = None -> get (combine f p) i = f (get p i) (get p i).
  induction p; simpl in *.
  +intros. symmetry. eauto.
  +simpl in *. destruct a. intros. simpl. destruct ( PeanoNat.Nat.eqb n i) eqn:?. eauto. eapply IHp. eauto. Qed.




Fixpoint combine_r (f:option nat -> option nat -> option nat) (p1: pair_list) :=
  match p1 with
  | nil => nil
  | (key, val) :: tl => (key, f None val) :: combine_r f tl
  end.


Fixpoint combine1 (f:option nat -> option nat -> option nat) (p:pair_list) (p1:pair_list) :=
  match p with
  | nil => combine_r f p1
  | (key, val) :: tl => (key, f val (get p1 key)) :: (combine1 f tl p1)                       
  end.



Lemma transitivity1 : forall p p1 f i, f None None = None -> get (combine1 f p p1) i = f (get p i) (get p1 i).
Proof. induction p.
       +intros. simpl in *. induction p1. simpl in *. symmetry. eauto.
        simpl in *. destruct a. simpl in *. destruct ( PeanoNat.Nat.eqb n i) eqn:?. eauto. eauto.
       +simpl in *. intros. destruct a. simpl in *. destruct ( PeanoNat.Nat.eqb n i) eqn:?. symmetry in Heqb. eapply beq_nat_eq in Heqb. subst. eauto. eapply IHp. eauto. Qed.