Require Import Coq.Arith.EqNat.
Require Import List.
Definition pair : Type := (nat * option nat).


Definition list_pair := list pair.


Definition first := cons (1, Some 1) (cons (2, Some 2) (cons (3, Some 3) (cons (4, Some 4) nil))).
Definition second := cons (2, Some 2) (cons (1, Some 1) (cons (3, Some 3) (cons (4, Some 4) nil))).
(*get first from list 1*)



Fixpoint get (l:list pair) (n:nat) :=
  match l with
  | nil => None
  | (a, b) :: tl => if beq_nat a n then b else get tl n
  end.


Fixpoint set (l:list pair) (k n:nat) :=
  match l with
  | nil => cons (k, Some n) nil
  | (a, b) :: tl => if beq_nat a k then (a, Some n) :: tl else (a, b) :: set tl k n
  end.


Fixpoint remove (l:list pair) (n:nat) :=
  match l with
  | nil => nil
  | (a, b) :: tl => if beq_nat a n then remove tl n else (a, b) :: remove tl n
  end.

Variable f: option nat -> option nat -> option nat.
  Hypothesis f_none_none: f None None = None.


Fixpoint combine_l (l:list pair)  (k:nat) (v:option nat) :=
  match l with
  | nil => (k, f v None)
  | (a, b) :: tl => if beq_nat k a then (a, f v b) else combine_l tl k v
  end.


                
  
Fixpoint combine_l_none (l:list pair) :=
  match l with
  | nil => nil
  | (a, b) :: tl => (a, (f b None)) :: combine_l_none tl
  end.

  Lemma xgcombine_l :
          forall m i,
          get (combine_l_none m) i = f (get m i) None.
Proof.
  induction m; intros; simpl. symmetry. apply f_none_none.
destruct a. simpl in *. destruct ( PeanoNat.Nat.eqb n i) eqn:?. eauto. simpl in *. apply IHm. Qed.
  
Hint Resolve xgcombine_l.


Fixpoint combine_r_none (l:list pair) :=
  match l with
  | nil => nil
  | (a, b) :: tl => (a, f None b) :: combine_r_none tl
  end.




  Lemma xgcombine_r :
          forall m i,
          get (combine_r_none m) i = f None (get m i).
Proof.
  induction m; simpl in *; intros. symmetry. apply f_none_none.
  destruct a; simpl in *. destruct ( PeanoNat.Nat.eqb n i) eqn:?; eauto. Qed.

Fixpoint combine_r (l:list pair)  (k:nat) (v:option nat) :=
  match l with
  | nil => (k, f v None)
  | (a, b) :: tl => if beq_nat k a then (a, f b v) else combine_r tl k v
  end.


Fixpoint combine (l1 l2: list pair) :=
  match l1 with
  | nil => combine_r_none l2
  | (a, b) :: tl => match get l2 a with
                       | None => (a, f b None) :: combine tl (remove l2 a)
                       | Some res => (a, f b (Some res)) :: combine tl (remove l2 a)
                       end
                         
                       
  end.



Theorem gcombine:
      forall m1 m2 i,
      get (combine m1 m2) i = f (get m1 i) (get m2 i).
Proof. induction m1. simpl in *. eauto.
 Admitted.


