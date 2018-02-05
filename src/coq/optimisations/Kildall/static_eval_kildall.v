Print nat.

Require Import Vellvm.optimisations.Kildall.lattice.
Require Import Vellvm.optimisations.maps.


Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.

Require Import Vellvm.DecidableEquality.
Require Import Vellvm.DecidableProp.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
(*ABSTRACT VALUES*)
Inductive aval : Type :=
  | vbot (* bottom (empty set of values) *)
  | val (n: dvalue) (* exactly Vint n *)
  | vtop
. 



Print eqType.
Locate eqType.
Print SEMILATTICE_WITH_TOP.
Module AVal <: SEMILATTICE_WITH_TOP.

  Definition t := aval.
  Definition eq_val (a b:aval) :=
    match a, b with
    | vbot, vbot => True
    | val n, val n1 =>  (n = n1)
    | vtop, vtop => True
    | _, _ => False                          
    end.

  Definition eq := eq_val.
  Lemma eq_refl: forall x, eq x x.
    Proof. intros. destruct x; simpl in *; eauto. Qed.
Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof. intros. unfold eq in *. destruct x, y; simpl in *; eauto. Qed.


Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof. intros. destruct x, y, z; simpl in *; eauto. inversion H. subst; eauto.  inversion H. Qed.



    Definition beq (a b:aval) :=
      match a, b with
    | vtop, vtop => true
    | vbot, vbot => true
    | val n, val n1 =>  decide (n = n1)
    | _, _ => false                          
    end.

    Lemma beq_correct: forall x y, beq x y = true -> eq x y.
    Proof. intros. destruct x, y; simpl in *; eauto. destruct (decide (n = n0)); simpl in *; eauto. inversion H. Qed.

(*a is greater or equal to b*)
    Definition ge (a b: aval) : Prop :=
      match a, b with
      | vbot, vbot => True
      | vbot, val _ => False
      | vbot, vtop => False
      | val _, vtop => False
      | val _, vbot => True
      | val v1, val v2 => decide (v1 = v2)
      | vtop, vbot => True
      | vtop, val_  => True               
      end.


    Lemma ge_refl: forall x y, eq x y -> ge x y.
    Proof. intros. destruct x, y; simpl in *; eauto.
           +subst. unfold decide. destruct ( eq_dvalue n0 n0); simpl in *; eauto. Qed.
        
    Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
    Proof. intros. destruct x, y, z; simpl in *; eauto. unfold decide in *. destruct (eq_dvalue n n0); simpl in *; subst; eauto. Qed.

    Definition top := vtop.
    Definition bot := vbot.

    Lemma ge_bot: forall x, ge x bot.
    Proof. intros. destruct x; simpl in *; eauto. Qed.
    

Print aval.
    Definition lub (a b: aval) :=
      match a, b with
      | vbot, _ => b
      | _, vbot => a
      | val v1, val v2 => if (decide (v1 = v2)) then val v1 else vtop
      | val _, vtop => vtop
      | vtop, val _ => vtop
      | vtop, vtop => vtop
      end.
    
    Lemma ge_lub_left: forall x y, ge (lub x y) x.
    Proof. destruct x, y; simpl in *; eauto.
           +unfold decide. destruct (  eq_dvalue n n); simpl in *; eauto.
           +unfold is_left. unfold decide. simpl in *. destruct ( eq_dvalue n n0); simpl in *; eauto. unfold decide. destruct ( eq_dvalue n n); simpl in *; eauto. Qed.



    
    Lemma ge_lub_right: forall x y, ge (lub x y) y.
    Proof. destruct x, y; simpl in *; eauto.
           unfold decide. destruct ( eq_dvalue n n); simpl in *; eauto. unfold is_left. 
unfold decide. destruct (eq_dvalue n n0); simpl in *; subst; eauto. unfold decide.
 destruct ( eq_dvalue n0 n0); simpl in *; eauto. Qed.


 Lemma ge_top: forall x, ge top x.
Proof. destruct x; simpl in *; eauto. Qed.
       
End AVal.

(**)
(*LPMap1*)
