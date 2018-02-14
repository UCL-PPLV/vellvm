Require Import Vellvm.optimisations.Kildall.lattice.
Require Import Vellvm.optimisations.maps.


Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.vellvm_tactics.

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
  | avalue (n: dvalue) (* exactly Vint n *)
  | vtop
. 



Print SEMILATTICE_WITH_TOP.
Module AVal <: SEMILATTICE_WITH_TOP.

  Definition t := aval.
  Definition eq_val (a b:aval) :=
    match a, b with
    | vbot, vbot => True
    | avalue n, avalue n1 =>  (n = n1)
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

  Lemma eq_val_correct : forall a b, eq_val a b  <-> a = b.
  Proof. intros. destruct a, b; simpl in *; split; intros; eauto; inversion H; eauto. Qed.
    Definition beq (a b:aval) :=
      match a, b with
    | vtop, vtop => true
    | vbot, vbot => true
    | avalue n, avalue n1 =>  decide (n = n1)
    | _, _ => false                          
    end.

    Lemma beq_correct: forall x y, beq x y = true -> eq x y.
    Proof. intros. destruct x, y; simpl in *; eauto. destruct (decide (n = n0)); simpl in *; eauto. inversion H. Qed.

    Lemma beq_eq : forall x y, beq x y = true <-> x = y.
    Proof. destruct x, y; simpl in *; intros; split; intros; eauto; inversion H. unfold decide in *. destruct (eq_dvalue n n0). subst. eauto. simpl in *. inversion H. subst. unfold decide. destruct ( eq_dvalue n0 n0); simpl in *. eauto. contradiction n; eauto. Qed.


    
(*a is greater or equal to b*)
    Definition ge (a b: aval) : Prop :=
      match a, b with
      | vbot, vbot => True
      | vbot, avalue _ => False
      | vbot, vtop => False
      | avalue _, vtop => False
      | avalue _, vbot => True
      | avalue v1, avalue v2 => decide (v1 = v2)
      | vtop, vbot => True
      | vtop, vtop => True
                        
      | vtop, avalue _  => True               
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
    

    Definition lub (a b: aval) :=
      match a, b with
      | vbot, _ => b
      | _, vbot => a
      | avalue v1, avalue v2 => if (decide (v1 = v2)) then avalue v1 else vtop
      | avalue _, vtop => vtop
      | vtop, avalue _ => vtop
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

Module AE := lidPMap(AVal).

Definition aenv := AE.t.


Module VA <: SEMILATTICE.

  Inductive t' := Bot | State (ae: aenv).
  Definition t := t'.

  Definition eq (x y: t) :=
    match x, y with
    | Bot, Bot => True
    | State ae1, State ae2 => AE.eq ae1 ae2
    | _, _ => False
    end.

  Lemma eq_refl: forall x, eq x x.
Proof.
  intros.
destruct x. simpl in *. eauto. simpl in *. apply AE.eq_refl. Qed.

  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof. intros.  destruct x, y; simpl in *; eauto. apply AE.eq_sym in H. auto. Qed.

  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
    destruct x, y, z; simpl; try tauto. 
    eapply AE.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => true
    | State ae1, State ae2 => AE.beq ae1 ae2
    | _, _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof. 
    destruct x, y; simpl; intros.
    auto.
    congruence.
    congruence.
    apply AE.beq_correct; auto.
Qed.
    
  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    | State ae1, State ae2 => AE.ge ae1 ae2
    end.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
        destruct x, y; simpl; try tauto. intros.
    apply AE.ge_refl; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
    destruct x, y, z; simpl; try tauto. eapply AE.ge_trans.
Qed.

  Definition bot : t := Bot.
  Lemma ge_bot: forall x, ge x bot.
Proof.
destruct x; simpl in *; eauto. Qed.

Definition lub (x y: t) : t :=
    match x, y with
    | Bot, _ => y
    | _, Bot => x
    | State ae1, State ae2 => State (AE.lub ae1 ae2)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    apply ge_refl; apply eq_refl.
    simpl.  apply AE.ge_lub_left. Qed.


Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.

      destruct x, y.
    apply ge_refl; apply eq_refl.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    simpl. apply AE.ge_lub_right. 
  Qed.

End VA.





Definition lookup_env_aenv (e:env) (id:raw_id) : aval :=
  match lookup_env e id with
  | None => vtop
  | Some a => avalue a
  end.



(*env - aenv*)
Inductive vmatch : aval -> aval -> Prop :=
| vtop_match : forall dval, vmatch dval vtop
| vval_match : forall dval dval1, dval = dval1 -> vmatch (avalue dval1) (avalue dval).




Definition ematch (e:env) (a:aenv) := forall p, vmatch (lookup_env_aenv e p) (AE.get p a).

Inductive vge: aval -> aval -> Prop :=
| vge_bot : forall v, vge v vbot
| vge_val : forall v v1, v = v1 -> vge (avalue v) (avalue v1)
| vge_top : forall v, vge vtop v.





Lemma vmatch_ge:
  forall v x y, vge x y -> vmatch v y -> vmatch v x.
Proof.
  induction 1; intros V. inversion V. subst. eauto. constructor. Qed.



Lemma ematch_ge:
  forall  e ae1 ae2,
  ematch e ae1 -> AE.ge ae2 ae1 -> ematch e ae2.
Proof. intros. unfold ematch in *. intros. unfold AE.ge in *. specialize (H p).
       specialize (H0 p). unfold AVal.ge in *. simpl in *.
       destruct ((lookup_env_aenv e p)); eauto. eapply vmatch_ge; eauto.
       destruct ( AE.get p ae2); simpl in *; eauto.
       destruct ( AE.get p ae1); eauto. apply vge_bot.
       inversion H0. inversion H0. destruct (AE.get p ae1).
       constructor. constructor. destruct (decide (n = n0)).
       subst; eauto. simpl in *. inversion H0. inversion H0.
       destruct (AE.get p ae1). constructor. constructor. constructor.
       destruct (AE.get p ae1), ( AE.get p ae2); eauto; inversion H; inversion H0; subst.
       constructor. destruct (decide (n1 = n)). subst. eauto.
       simpl in *. inversion H5. constructor.
       destruct ( AE.get p ae2), (AE.get p ae1); try constructor; eauto; try inversion H0; inversion H. Qed.



Lemma vmatch_false : forall e p, vmatch (lookup_env_aenv e p) AVal.bot -> False.
Proof. intros. inversion H. Qed.


Lemma ematch_update:
  forall e ae v av r,
  ematch e ae -> vmatch (avalue v) av -> ematch (add_env r v e) (AE.set r av ae).
Proof.
  intros. red. intros. remember ( (lookup_env_aenv (add_env r v e) p)).
 assert  (ae <> AE.Bot -> ~ (AVal.beq av AVal.bot) = true ->
vmatch a ((if loc_id_eq p r then av else AE.get p ae)) -> vmatch a (AE.get p (AE.set r av ae))).
 intros. unfold is_left in. simpl in *. unfold AE.get, AE.set in *. unfold is_left in *. simpl in *. destruct ae. congruence. destruct ( AVal.beq av AVal.bot). contradiction H2; eauto.
 destruct (AVal.beq av AVal.top) eqn:?. simpl in *.
 rewrite lidTree.grspec. unfold lidTree.elt_eq. 
destruct ( loc_id_eq p r). constructor. eauto.
rewrite lidTree.gsspec. unfold lidTree.elt_eq. simpl in *.
destruct ( loc_id_eq p r). eauto. eauto.
apply H1. unfold not. intros. subst. unfold ematch in *.
simpl in *. specialize (H r). inversion H. simpl in *.
unfold not. intros.  apply AVal.beq_eq in H2.
subst. simpl in *. inversion H0.
unfold is_left. simpl in *. subst.
unfold lookup_env_aenv, add_env, lookup_env in *; simpl in *.
destruct (AstLib.RawID.eq_dec p r), (loc_id_eq p r); subst; eauto; try contradiction n; eauto.
Qed.




Lemma ematch_update_top : forall r v e ae, ematch e ae -> ematch (add_env r v e) (AE.set r vtop ae).
Proof. intros. eapply ematch_update; eauto. constructor. Qed.

