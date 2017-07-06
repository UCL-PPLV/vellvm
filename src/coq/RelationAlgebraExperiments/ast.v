Section s.
Require Import RelationAlgebra.kat RelationAlgebra.prop RelationAlgebra.rel RelationAlgebra.comparisons RelationAlgebra.kat_tac.


(** identifiers for memory locations  *)
Variable loc: Set.
(** abstract state (or memory) *)
Variable state: Set.
(** updating the state *)
Variable update: loc -> nat -> state -> state.

(** * Definition of the languague *)

(** programs *)

Inductive prog :=
| skp
| aff (x: loc) (e: state -> nat)
| seq (p q: prog)
| ite (t: dset state) (p q: prog)
| whl (t: dset state) (p: prog).

(** notations *)
Bind Scope imp_scope with prog.
Delimit Scope imp_scope with imp.
Notation "x  <- y" := (aff x y) (at level 90): imp_scope.
Notation "p  ;; q" := (seq p%imp q%imp) (left associativity, at level 101): imp_scope.
Arguments ite _%ra _%imp _%imp.
Arguments whl _%ra _%imp.


(** * Big step semantics *)

(** corresponding functional relation *)
Notation upd x e := (frel (fun s => update x (e s) s)).


(** ** using KAT expressions in the model of relations

   the semantics can then be given by induction on the program, using
   a simple fixpoint *)










Fixpoint bstep (p: prog): rel state state :=
  match p with
    | skp => 1
    | aff x e => upd x e
    | seq p q => bstep p * bstep q
    | ite b p q => [b] * bstep p + [!b] * bstep q
    | whl b p => ([b] * bstep p)^*  *  [!b]
  end.

(** ** using an inductive predicate, as in standard textbooks *)

Inductive bstep': prog -> rel state state :=
| s_skp: forall s, bstep' skp s s
| s_aff: forall x e s, bstep' (x <- e) s (update x (e s) s)
| s_seq: forall p q s s' s'', bstep' p s s' -> bstep' q s' s'' -> bstep' (p ;; q) s s''
| s_ite_ff: forall (b: dset state) p q s s', b s = false -> bstep' q s s' -> bstep' (ite b p q) s s'
| s_ite_tt: forall (b: dset state) p q s s', b s = true -> bstep' p s s' -> bstep' (ite b p q) s s'
| s_whl_ff: forall (b: dset state) p s, b s = false -> bstep' (whl b p) s s
| s_whl_tt: forall (b: dset state) p s s', b s = true -> bstep' (p ;; whl b p) s s' -> bstep' (whl b p) s s'.

(** ** equivalence between the two definitions *)

Lemma bstep_eq p: bstep' p == bstep p.
Proof.
  apply antisym. 
  - intros s s'. induction 1. 
     reflexivity. 
     reflexivity. 
     eexists; eassumption. 
     right. eexists. split. reflexivity. simpl; now rewrite H. assumption.
     left. eexists. split. reflexivity. assumption. assumption. 
     exists s. apply (str_refl ([b] * bstep p)). reflexivity.
      simpl. unfold rel_inj. simpl. now rewrite H.
     destruct IHbstep' as [t ? [t' ? ?]]. exists t'. 2: assumption. 
     apply (str_cons ([b] * bstep p)). exists t. 2: assumption.
     eexists; eauto. now split. 
  - induction p; unfold bstep; fold bstep.
     intros ? ? <-. constructor. 
     intros ? ? ->. constructor. 
     intros ? ? [? H1 H2]. econstructor. apply IHp1, H1. apply IHp2, H2.
     intros ? ? [[? [<- H] H']|[? [<- H] H']]. 
      apply s_ite_tt. assumption. apply IHp1, H'. 
      apply s_ite_ff. now apply Bool.negb_true_iff. apply IHp2, H'. 
     apply str_ind_l'.
      intros ? ? [<- H]. apply s_whl_ff. now apply Bool.negb_true_iff.
      rewrite <-dotA. intros s s'' [? [<- H] [s' H' H'']]. apply s_whl_tt. assumption.
      econstructor. apply IHp, H'. assumption.
Qed. 


From mathcomp.ssreflect
Require Import seq.

Fixpoint change (p:prog) : list prog :=
  match p with
  | skp => [:: skp]
  | aff a b => [::aff a b]
  | (t ;; q)%imp => change t ++ change q
  | ite a b c =>[:: ite a b c]
  | whl b p => [::whl b p]

end.


Require Import Nat.



Require Import Vellvm.Ollvm_ast.








Definition code := seq instr.


Fixpoint codeexec (c: code) :=
match c with
  | [::a] => 0%nat
  | a::b => 1%nat
  | nil => 2%nat
end.











(*

Fixpoint testy (p:list prog): rel state state  := 
  match p with
  | nil => 1
  |(a :: b)%list => (bstep a) * (testy b)
end.


Lemma bstep_eq1 p: testy (change p) == bstep p.
apply antisym.
  induction p. intros s s'. induction 1. 
    +simpl. inversion H0. inversion H. rewrite H1. reflexivity.
    +simpl. intros. inversion H. symmetry in H1. rewrite H1. apply H0.
    +induction p1, p2; unfold bstep; fold bstep.
      *simpl. intros. inversion H. subst. apply H1.
      *simpl. intros. eexists. auto. inversion H. subst. inversion H1. subst. apply H0.
      *simpl. intros. eexists. auto. inversion H. subst. simpl in *. inversion H. subst. apply IHp2. apply H2. 
      *simpl. intros. eexists. auto. inversion H. subst. simpl in *. inversion H. subst. apply IHp2. apply H2.
      *simpl. intros. eexists. auto. inversion H. subst. simpl in *. inversion H. subst. apply IHp2. apply H2.
      *simpl. intros. eexists. unfold upd. simpl. auto. inversion H. unfold upd in H0. symmetry. inversion H1. symmetry in H3. rewrite H3. symmetry in H2. rewrite H2. apply H0.
      *simpl. intros. eexists. auto. inversion H. subst. inversion H. unfold upd. unfold upd in H0. simpl. auto. inversion H. inversion H1. inversion H0. subst. apply H2.
      *simpl. intros ? ? [? H1 H2]. eexists. apply H1. simpl in *. apply IHp2. auto.
      *simpl. intros ? ? [? H1 H2]. eexists. apply H1. simpl in *. apply IHp2. apply H2.
      *simpl. intros ? ? [? H1 H2]. eexists. apply H1. simpl in *. apply IHp2. apply H2.
      *simpl. intros ? ? ?.

*)