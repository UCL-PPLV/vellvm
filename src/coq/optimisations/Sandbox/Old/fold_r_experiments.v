Require Import List.
Require Import Vellvm.Classes.

(*> foldr f z []     = z
> foldr f z (x:xs) = x `f` foldr f z xs
 
 *)

Fixpoint foldr A B (f:B -> A -> A) (z:A) (l:list B) :=
  match l with
  | nil => z
  | cons hd tl => f hd (foldr A B f z tl)               
  end.


(*LET B = LIST OF NATS*)
(*F = add int b to A*)
(*A = LIST OF NAT*)
Print fold_right.

Definition f (b:nat) (a:list nat) := (b + 1) :: a.



Print fold_right_app.

Print fold_right.
(*fold_right = 
fun (A B : Type) (f : B -> A -> A) (a0 : A) =>
fix fold_right (l : list B) : A := match l with
                                   | nil => a0
                                   | b :: t => f b (fold_right t)
                                   end
     : forall A B : Type, (B -> A -> A) -> A -> list B -> A
 *)



(*  fold_right f i (l ++ l') = fold_right f (fold_right f i l') l*)



Definition test a b := fold_right f a b.

Lemma foldr_lists : forall a b, exists e, test a b = e ++ a.
Proof. unfold test. induction b. simpl in *. exists nil. eauto.


       +simpl in *. destruct IHb. rewrite H. unfold f. simpl in *. exists (a0+1::x). simpl in *. eauto. Qed.




(**************)
Print mret.

