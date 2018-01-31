From Paco
Require Import paco.

Require Import Ascii String.
Require Import Coq.Strings.String.
Require Import List.
Require Import Coq.Arith.EqNat.

Definition tuple : Set := (nat * nat).
Definition listtuple := list tuple.


Definition fallthrough (l:listtuple) :=
  match l with
  | nil => None
  | hd::tl => Some (hd)
  end.


Fixpoint list_to_tuple (l:listtuple) (t:nat)  :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (fst hd) t) then Some (snd hd, fallthrough tl) else list_to_tuple tl t
  end.
Print list_to_tuple.


Fixpoint calculate_previous (l:listtuple) (i:nat) :=
  match l with
  | nil => nil
  | cons hd tl => if beq_nat (fst hd) i then nil else cons hd  (calculate_previous tl i)
  end.

Definition find_tuple (l:listtuple) (i:nat) :=
  match list_to_tuple l i with
  | Some (t, _) => Some t
  | _ => None
  end.


Definition increase_tuple (l:listtuple) (i:nat) :=
  match list_to_tuple l i with
  | Some (_, Some a) => Some a
  | _ => None
  end.




Definition calculate_current_previous (l:listtuple) (t:tuple) := (fst t, calculate_previous l (fst t)).

Definition calculate_previous_lists (l:listtuple) : list (nat * listtuple) := map (calculate_current_previous l) l.





Lemma test : forall l i i1, find_tuple l i = Some i1 ->
                            exists tl, l = (calculate_previous l i) ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple in *. simpl in *. induction l; simpl in *.
       +inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb n i). simpl in *. destruct b. simpl in *. inversion H. subst. apply beq_nat_eq in Heqb. subst. eauto. simpl in *. apply IHl in H. inversion H. exists x. rewrite <- H0. eauto.
Qed.

Lemma test2 : forall l i i1 t1, find_tuple l i = Some i1 -> increase_tuple l i = Some t1 -> list_to_tuple l i = Some (i1, Some t1).
Proof. intros. unfold find_tuple in *. unfold increase_tuple in *. destruct ( list_to_tuple l i). simpl in *. destruct p. simpl in *. inversion H. subst. destruct o. simpl in *. inversion H0. eauto. inversion H0. inversion H0. Qed.




       Lemma test5 : forall n1 (A:listtuple) n2 x0, In n1 (map fst (A ++ (n1, n2) :: x0)).
       Proof. intros. induction A. simpl in *. left. eauto. simpl. right. eauto. Qed.
              



Lemma test6 : forall t1 A x0, NoDup (map fst (A ++ (cons t1 nil) ++ x0)) -> calculate_previous (A ++ (cons t1 nil) ++ x0) (fst t1) = A.
Proof. intros. induction A. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto. simpl in *. destruct a, t1. simpl in *. remember  (PeanoNat.Nat.eqb n n1). destruct b. simpl in *. apply beq_nat_eq in Heqb. subst. inversion H. subst. contradiction H2. apply test5. 
(assert ((calculate_previous (A ++ (n1, n2) :: x0) n1 = A)  -> ((n, n0)
  :: calculate_previous (A ++ (n1, n2) :: x0) n1 =
  (n, n0) :: A ))). intros. rewrite H0. eauto. apply H0; apply IHA. inversion H; subst; eauto. Qed.





Lemma test9: forall x l i i1 t1, NoDup (map fst l) -> list_to_tuple l i = Some (i1,Some t1) -> l = calculate_previous l i ++ (i, i1) :: x -> exists tl, x = cons t1 tl.
Proof. intros. induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb n i). destruct b. simpl in *. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H1. subst. inversion H0. subst. destruct x. simpl in *. inversion H3. simpl in *. inversion H3. subst. eauto. apply IHl; eauto. inversion H. subst. eauto. 
       


       
assert ((n, n0) :: l = ((n, n0) :: calculate_previous l i) ++ (i, i1) :: x -> l = ( calculate_previous l i) ++ (cons (i, i1) x)). intros. inversion H2. rewrite <- H4. eauto. apply H2 in H1. eauto.  Qed.



Lemma test10: forall l0 i i1 t1 (x0:listtuple), l0 ++ (i, i1) :: t1 :: x0 = (l0 ++ (i, i1) :: nil) ++ (t1 :: nil) ++ x0. Proof. intros. simpl. SearchAbout app. rewrite <- app_assoc. simpl in *. eauto. Qed.
 


Lemma test11: forall l i i1 t1 head, NoDup (map fst l) -> find_tuple l i = Some i1 -> increase_tuple l i = Some t1 ->
                                     list_to_tuple l i = Some (i1, Some t1) ->
                                     calculate_previous l i = head  ->
                                     calculate_previous l (fst t1) = calculate_previous l i ++ (cons (i, i1) nil).
Proof. intros. generalize H0. intro. apply test in H0. rewrite H3. simpl in *. inversion H0. eapply test9 in H2; eauto. inversion H2. subst. remember ( calculate_previous l i). simpl in *. rewrite H5. simpl in *.
       assert ((l0 ++ (i, i1) :: t1 :: x0) = ((l0 ++ (i, i1) :: nil) ++ (cons t1 nil) ++ x0)).


     


apply test10. rewrite H3. 
remember ((l0 ++ (i, i1) :: nil)). simpl. apply test6. simpl. subst. simpl in *. rewrite H3 in H5. rewrite H5 in H.

simpl in *. eauto. Qed. 






Lemma test12: forall l i i1 t1 head, NoDup (map fst l) -> find_tuple l i = Some i1 -> increase_tuple l i = Some t1 -> calculate_previous l i = head  -> calculate_previous l (fst t1) = calculate_previous l i ++ (cons (i, i1) nil).
Proof. intros. eapply test11 in H; eauto. eapply test2; eauto. Qed.




(***********************)





Definition fallthrough1 (l:listtuple) :=
  match l with
  | nil => None
  | hd::tl => Some (fst hd)
  end.


Fixpoint list_to_tuple1 (l:listtuple) (t:nat)  :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (fst hd) t) then Some (snd hd, fallthrough1 tl) else list_to_tuple1 tl t
  end.
Print list_to_tuple.


Fixpoint calculate_previous1 (l:listtuple) (i:nat) :=
  match l with
  | nil => nil
  | cons hd tl => if beq_nat (fst hd) i then nil else cons hd  (calculate_previous1 tl i)
  end.

Definition find_tuple1 (l:listtuple) (i:nat) :=
  match list_to_tuple1 l i with
  | Some (t, _) => Some t
  | _ => None
  end.


Definition increase_tuple1 (l:listtuple) (i:nat) :=
  match list_to_tuple1 l i with
  | Some (_, Some a) => Some a
  | _ => None
  end.




Definition calculate_current_previous1 (l:listtuple) (t:tuple) := (fst t, calculate_previous1 l (fst t)).

Definition calculate_previous_lists1 (l:listtuple) : list (nat * listtuple) := map (calculate_current_previous1 l) l.
Print increase_tuple1.


Lemma test21 : forall l i i1 t1, find_tuple1 l i = Some i1 -> increase_tuple1 l i = Some t1 -> list_to_tuple1 l i = Some (i1, Some t1).
Proof. intros. unfold find_tuple1 in *. unfold increase_tuple1 in *. destruct ( list_to_tuple1 l i). simpl in *. destruct p. simpl in *. inversion H. subst. destruct o. simpl in *. inversion H0. eauto. inversion H0. inversion H0. Qed.



Lemma test_second : forall l i i1, find_tuple1 l i = Some i1 ->
                            exists tl, l = (calculate_previous1 l i) ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple1 in *. simpl in *. induction l; simpl in *.
       +inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb n i). simpl in *. destruct b. simpl in *.  inversion H. subst. apply beq_nat_eq in Heqb. subst. eauto. simpl in *. apply IHl in H. inversion H. exists x. rewrite <- H0. eauto.
Qed.




       Lemma test51 : forall n1 (A:listtuple) n2 x0, In n1 (map fst (A ++ (n1, n2) :: x0)).
       Proof. intros. induction A. simpl in *. left. eauto. simpl. right. eauto. Qed.
              



Lemma test61: forall t1 A x0, NoDup (map fst (A ++ (cons t1 nil) ++ x0)) -> 

calculate_previous1 (A ++ (cons t1 nil) ++ x0) (fst t1) = A.
Proof. intros. induction A. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto. simpl in *. destruct a, t1. simpl in *. remember  (PeanoNat.Nat.eqb n n1). destruct b. simpl in *. apply beq_nat_eq in Heqb. subst. inversion H. subst. contradiction H2. apply test5. 
(assert ((calculate_previous (A ++ (n1, n2) :: x0) n1 = A)  -> ((n, n0)
  :: calculate_previous (A ++ (n1, n2) :: x0) n1 =
  (n, n0) :: A ))). intros. rewrite H0. eauto. apply H0; apply IHA. inversion H; subst; eauto. Qed.




Lemma test91: forall x l i i1 t1, NoDup (map fst l) -> list_to_tuple1 l i = Some (i1,Some t1) ->

                                  l = calculate_previous1 l i ++ (i, i1) :: x ->
                                  exists tl r, x = cons (t1, r) tl.
Proof. intros.  induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. 



remember ( PeanoNat.Nat.eqb n i). destruct b. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H1. subst. inversion H0. subst. destruct x. simpl in *. inversion H3. simpl in *. inversion H3. subst. destruct p. simpl in *. exists x. exists n0. eauto. eapply IHl.
       +inversion H. subst. eauto.
       +simpl in *. inversion H1. simpl in *. rewrite <- H3. eauto.
       +inversion H1. rewrite <- H3. eauto. Qed. 




Lemma test111: forall l i i1 t1 head, NoDup (map fst l) -> find_tuple1 l i = Some i1 -> increase_tuple1 l i = Some t1 ->

 list_to_tuple1 l i = Some (i1, Some t1) -> calculate_previous1 l i = head  -> 


calculate_previous1 l (t1) = calculate_previous1 l i ++ (cons (i, i1) nil).

Proof. intros. generalize H. intro. apply test_second in H0. rewrite H3. simpl in *. inversion H0.

eapply test91 in H; eauto. rewrite H5.  inversion H. inversion H6. rewrite H7. simpl in *. rewrite H3.
rewrite H7 in H5. rewrite H5 in H4. simpl in *. 



       assert ((head++ (i, i1) :: (t1, x1) :: x0) = ((head ++ (i, i1) :: nil) ++ (cons (t1,x1) nil) ++ x0)).
simpl in *. rewrite <- app_assoc. simpl in *. eauto. rewrite H8. simpl in *. remember ((head ++ (i, i1) :: nil)). eapply test61.
subst. simpl in *. eauto. rewrite <- app_assoc. simpl in *. eauto. Qed.






Lemma test121: forall l i i1 t1 head, NoDup (map fst l) -> find_tuple1 l i = Some i1 -> increase_tuple1 l i = Some t1 -> calculate_previous1 l i = head  -> calculate_previous1 l (t1) = calculate_previous1 l i ++ (cons (i, i1) nil).
Proof. intros. eapply test111 in H; eauto. eapply test21; eauto. Qed.

