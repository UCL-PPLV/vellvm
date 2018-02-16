Require Import ZArith.ZArith List.
Require Import String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Vellvm.optimisations.vellvm_tactics.
Require Import Vellvm.optimisations.local_cfg.
Require Import Vellvm.optimisations.map_spec.

Require Import Equalities.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import Compare_dec.
Require Import Bool.
Require Import Coq.MSets.MSetGenTree.
Import ListNotations.
Set Implicit Arguments.


Instance eq_dec_int : eq_dec int := Z_eq_dec.
Require Import Ascii.



Module AsciiOrd <: OrderedType.
  Definition t := ascii.
  Definition eq := @eq t.
    Scheme Equality for ascii.
  Definition lt (a b:ascii) := N.lt (N_of_ascii a) (N_of_ascii b).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
 

  Ltac destr_simpl x y := destruct x eqn:?; simpl in *; inv y.

    Lemma eq_correct : forall a b, eq a b <-> ascii_beq a b = true.
  Proof. split; intros. 
         unfold eq in *. subst. destruct b; simpl in *. assert (forall a, bool_beq a a = true). intros. destruct a; simpl in *; eauto. repeat rewrite H. simpl. eauto.

destruct a, b. simpl in *. 
destr_simpl (bool_beq b0 b) H; destr_simpl (bool_beq b1 b8) H; destr_simpl (bool_beq b2 b9) H; destr_simpl (bool_beq b3 b10) H; destr_simpl (bool_beq b4 b11) H; destr_simpl (bool_beq b5 b12) H; destr_simpl (bool_beq b6 b13) H.

assert (forall a c, bool_beq a c = true -> a = c).  intros. destruct a, c; eauto.
eapply H0 in Heqb15; eapply H0 in Heqb0; eapply H0 in Heqb1; eapply H0 in Heqb2; eapply H0 in Heqb3; eapply H0 in Heqb4; eapply H0 in Heqb5; eapply H0 in H; subst; eapply eq_refl. Qed.

Lemma beq_refl : forall a, ascii_beq a a = true.
  Proof. intros. eapply eq_correct. eapply eq_refl. Qed.


  
  Lemma lt_trans : forall a b c:t, lt a b -> lt b c -> lt a c.
  Proof.
    intros a b c.
    unfold lt.
    apply N.lt_trans.
  Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    intros a b H.
    unfold eq. unfold not. intros He. rewrite He in H.
    eapply N.lt_neq. unfold lt in H. apply H. reflexivity.
  Qed.
  

    Lemma N_of_ascii_inj : forall x y, N_of_ascii x = N_of_ascii y -> x = y.
  Proof.
    intros x y H.
    rewrite <- ascii_N_embedding.
    rewrite <- (@ascii_N_embedding x).
    rewrite H. reflexivity.
  Defined.

    Program Definition compare (x y: t) : Compare lt eq x y :=
    match N_as_OT.compare (N_of_ascii x) (N_of_ascii y) with
    | LT p => _
    | EQ p => _
    | GT p => _
    end.
  Next Obligation.
    apply LT. unfold lt. auto.
  Defined.
  Next Obligation.
    apply EQ. unfold eq. apply N_of_ascii_inj. auto.
  Defined.
  Next Obligation.
    apply GT. unfold lt. auto.
  Defined.
  Definition eq_dec := ascii_dec.

End AsciiOrd.
Module AsciiOrdFacts := OrderedTypeFacts(AsciiOrd).

Module StringOrd <: OrderedType.
  Definition t := string.
    Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
    Fixpoint lt (s1 s2:string) : Prop :=
    match s1, s2 with
    | EmptyString, EmptyString => False
    | EmptyString, String _ _ => True
    | String a s1', String b s2' =>
      match AsciiOrd.compare a b with
      | LT _ => True
      | EQ _ => lt s1' s2'
      | GT _ => False
      end
    | String _ _, EmptyString => False
    end.

  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    induction a.
    - destruct b; destruct c; simpl; intros; try tauto.
    - destruct b; destruct c; simpl; intros; try tauto.
      destruct (AsciiOrd.compare a a1); try tauto.
      + destruct (AsciiOrd.compare a1 a2); try tauto.
        * AsciiOrdFacts.elim_comp; auto.
        * AsciiOrdFacts.elim_comp; auto.
      + destruct (AsciiOrd.compare a1 a2); try tauto.
        * AsciiOrdFacts.elim_comp; auto.
        * AsciiOrdFacts.elim_comp; auto.
          eapply IHa; eauto.
  Qed.          
      
  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    induction a; intros b H He; unfold eq in He; subst.
    - unfold lt in H. destruct H.
    - simpl in H.
      destruct (AsciiOrd.compare a a); auto.
      apply AsciiOrd.lt_not_eq in l. apply l. AsciiOrdFacts.order.
      apply IHa in H. apply H. unfold eq. reflexivity.
  Qed.


    Program Fixpoint compare (s1 s2 : t) : Compare lt eq s1 s2 :=
    match s1, s2 with
    | EmptyString, EmptyString => _
    | EmptyString, String b s2' => _
    | String a s1', String b s2' =>
      match AsciiOrd.compare a b with
      | LT _ => _
      | EQ _ => match compare s1' s2' with
               | LT _ => _
               | EQ _ => _
               | GT _ => _
               end
      | GT _ => _ 
      end
    | String a s1', EmptyString => _
    end.
  Next Obligation.
    apply EQ. unfold eq. reflexivity.
  Defined.
  Next Obligation.
    apply LT. simpl. auto.
  Defined.
  Next Obligation.
    apply LT. simpl. rewrite <- Heq_anonymous. auto.
  Defined.
  Next Obligation.
    apply LT. simpl. rewrite <- Heq_anonymous0. auto.
  Defined.
  Next Obligation.
    apply EQ. simpl. unfold AsciiOrd.eq in wildcard'0. subst. unfold eq in e. subst. reflexivity.
  Defined.
  Next Obligation.
    apply GT. simpl. unfold AsciiOrd.eq in wildcard'0. subst.
    rewrite <- Heq_anonymous0. auto.
  Defined.
  Next Obligation.
    apply GT. simpl. AsciiOrdFacts.elim_comp_lt b a. auto.
  Defined.
  Next Obligation.
    apply GT. simpl. auto.
  Defined.

  Definition eq_dec := string_dec.

  Fixpoint string_beq (a b: string) :=
    match a, b with
    | EmptyString, EmptyString => true
    | String s1 t1, String s2 t2 => AsciiOrd.ascii_beq s1 s2 && string_beq t1 t2
    | _, _ => false
    end.


    Lemma beq_refl : forall a, string_beq a a = true.
    Proof. induction a; eauto. simpl in *. rewrite AsciiOrd.beq_refl. simpl in *. eauto. Qed.

    
    Lemma beq_correct : forall a b, string_beq a b = true <-> a = b.
  Proof. induction a, b; split; intros; eauto.
         +inversion H.
         +inversion H.
         +inversion H.
         +inversion H.
         +inversion H. simpl in *.
          destruct ( AsciiOrd.ascii_beq) eqn:?.
         -simpl in *. eapply IHa in H. subst. eapply AsciiOrd.eq_correct in Heqb0. inversion Heqb0. subst. eauto.
         -simpl in *. inversion H.
         +rewrite H.  simpl. rewrite AsciiOrd.beq_refl. simpl in *. rewrite beq_refl. eauto. Qed.


  
End StringOrd.
Module StringOrdFacts := OrderedTypeFacts(StringOrd).







Module RawIDOrd <: OrderedType.
  Definition t := raw_id.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  
  (* Anon < Name < Raw *)
  Definition lt (x:t) (y:t) : Prop :=
    match x,y with
    | Anon n1, Anon n2 => (n1 < n2)%Z
    | Name s1, Name s2 => StringOrd.lt s1 s2
    | Raw n1, Raw n2 => (n1 < n2)%Z
    | Anon _, _ => True
    | Name _, Raw _ => True
    | _, _ => False 
    end.

  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    destruct a; destruct b; destruct c; simpl; intros H1 H2; intuition.
    - eapply StringOrd.lt_trans; eauto.
  Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    destruct a; destruct b; simpl; intros H He; inversion He; subst.
    - apply StringOrd.lt_not_eq in H. apply H. unfold StringOrd.eq. reflexivity.
    - apply Z_as_OT.lt_not_eq in H. tauto.
    - apply Z_as_OT.lt_not_eq in H. tauto.
  Qed.


         
  Program Definition compare (x:t) (y:t) : Compare lt eq x y :=
    match x,y with
    | Anon n1, Anon n2 =>
      match Z_as_OT.compare n1 n2 with
      | LT _ => LT _
      | EQ _ => EQ _
      | GT _ => GT _
      end
    | Anon _, Name _ => LT _
    | Anon _, Raw _ => LT _
    | Name _, Anon _ => GT _
    | Name s1, Name s2 =>
      match StringOrd.compare s1 s2 with
      | LT _ => LT _
      | EQ _ => EQ _
      | GT _ => GT _
      end
    | Name _, Raw _ => LT _
    | Raw _, Anon _ => GT _
    | Raw _, Name _ => GT _
    | Raw n1, Raw n2 =>
      match Z_as_OT.compare n1 n2 with
      | LT _ => LT _
      | EQ _ => EQ _
      | GT _ => GT _
      end
    end.
  Next Obligation.
    unfold Z_as_OT.eq in wildcard'. subst. unfold eq. reflexivity.
  Defined.
  Next Obligation.
    unfold StringOrd.eq in wildcard'. subst. unfold eq. reflexivity.
  Defined.
  Next Obligation.
    unfold Z_as_OT.eq in wildcard'. subst. unfold eq. reflexivity.
  Defined.


  Definition beq (t1 t2: raw_id) :=
    match t1, t2 with
    | Anon n1, Anon n2 => Z.eqb n1 n2
    | Name s1, Name s2 => StringOrd.string_beq s1 s2
    | Raw n1, Raw n2 => Z.eqb n1 n2
    | _, _ => false
    end.

  Lemma beq_refl : forall a, beq a a = true.
  Proof. unfold beq; destruct a. eapply StringOrd.beq_correct. eauto.
apply Z.eqb_refl. apply Z.eqb_refl. Qed.
Hint Resolve beq_refl.
         
  Lemma beq_correct : forall a b, beq a b = true <-> eq a b.
  Proof. induction a, b; split; intros; try inv H.
         +eapply StringOrd.beq_correct in H1. subst. apply eq_refl.
         +eapply Z.eqb_eq in H1. subst. eapply eq_refl.
         +eapply Z.eqb_eq in H1. subst. eapply eq_refl. Qed.

  Lemma lt_false :  forall lbk1 lbk0, lt lbk1 lbk0 ->  lt lbk0 lbk1 -> False.
  Proof. intros. destruct lbk1, lbk0; simpl in *; try inv H; try inv H0.
         +eapply StringOrd.lt_trans in H; eauto. eapply StringOrd.lt_not_eq in H. contradiction H. unfold StringOrd.eq. eauto.
         +eapply Z.lt_asymm in H. tauto.
         +eapply Z.lt_asymm in H. tauto. Qed.


  Definition eq_dec : forall (x y : t), {x = y} + {x <> y}.
    decide equality.
    - apply string_dec.
    - apply eq_dec_int.
    - apply eq_dec_int.
  Defined.

End RawIDOrd.  

Instance eq_dec_raw_id : eq_dec raw_id := RawIDOrd.eq_dec.




Module InstrIDOrd <: OrderedType.
  Definition t := instr_id.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  
  Definition beq (t1 t2:t) :=
    match t1, t2 with
    | IId i1, IId i2 => RawIDOrd.beq i1 i2
    | IVoid i1, IVoid i2 => Z.eqb i1 i2
    | _, _ => false
    end.


  Lemma beq_refl : forall t1, beq t1 t1 = true.
  Proof. destruct t1; simpl in *. eapply RawIDOrd.beq_refl. eapply Z.eqb_refl. Qed.
  Hint Resolve beq_refl.
  
  Lemma beq_correct : forall t1 t2,  beq t1 t2 = true <-> eq t1 t2.
  Proof. destruct t1, t2; split; intros; try inv H; eauto.
         + eapply  RawIDOrd.beq_correct in H1. unfold RawIDOrd.eq in *. subst. eapply eq_refl.
         + eapply Z.eqb_eq in H1. subst. unfold eq. eauto. Qed.
  
(*IVoid < IId*)  
  Definition lt (x:t) (y:t) : Prop :=
    match x,y with
    | IVoid n1, IVoid n2 => (n1 < n2)%Z
    | IId s1, IId s2 => RawIDOrd.lt s1 s2
    | IVoid _, IId _ => False
    | IId _, IVoid _ => True
    end.
  
    Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    destruct a; destruct b; destruct c; simpl; intros H1 H2; intuition.
    eapply RawIDOrd.lt_trans; eauto.
  Qed.
  
  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    destruct a; destruct b; simpl; intros H He; inversion He; subst.
    - apply RawIDOrd.lt_not_eq in H. unfold not in H. unfold RawIDOrd.eq in *. unfold eq in He. eapply H. eauto.
    - apply Z_as_OT.lt_not_eq in H. tauto.
  Qed.

  Program Definition compare (x:t) (y:t) : Compare lt eq x y :=
    match x, y with
    | IId n1, IId n2 => match RawIDOrd.compare n1 n2 with
                        | LT _ => LT _
                        | EQ _ => EQ _
                        | GT _ => GT _                        
                        end
                          
    | IId _, IVoid _ => LT _
    | IVoid n1, IVoid n2 => match Z_as_OT.compare n1 n2 with
                             | LT _ => LT _
                             | EQ _ => EQ _
                             | GT _ => GT _
                             end
    | IVoid _, IId _ => GT _
    end.
  Next Obligation. unfold RawIDOrd.eq in *. subst. unfold eq. eauto. Defined.
  Next Obligation. unfold Z_as_OT.eq in *. subst. unfold eq. eauto. Defined.



  Definition eq_dec : forall (x y : t), {x = y} + {x <> y}.
    decide equality.
    -eapply  eq_dec_raw_id.
    -eapply eq_dec_int.
     Defined.


  
End InstrIDOrd.
Instance eq_dec_instr_id : eq_dec instr_id := InstrIDOrd.eq_dec.






Module Local_PCOrd <: OrderedType.
    Definition t := local_pc.
  
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition beq (t1 t2: local_pc) : bool := RawIDOrd.beq (lbk t1) (lbk t2) && InstrIDOrd.beq (lpt t1) (lpt t2).

  Lemma beq_refl : forall t1, beq t1 t1 = true.
  Proof. unfold beq; destruct t1; simpl in *. rewrite RawIDOrd.beq_refl. simpl. rewrite InstrIDOrd.beq_refl. auto. Qed.


  Lemma beq_correct : forall t1 t2, beq t1 t2 = true <-> eq t1 t2.
  Proof. induction t1, t2; unfold beq; simpl in *; split; intros; unfold eq.
         +destruct ( RawIDOrd.beq lbk lbk0) eqn:?; destruct (InstrIDOrd.beq lpt lpt0) eqn:?; simpl in *.
          *eapply RawIDOrd.beq_correct in Heqb. unfold RawIDOrd.eq in *. subst. eapply InstrIDOrd.beq_correct in Heqb0. unfold InstrIDOrd.eq in *. subst. eauto.
          *inversion H.
          *inversion H.
          *inversion H.
         +unfold eq in *. inversion H. subst. rewrite RawIDOrd.beq_refl. rewrite InstrIDOrd.beq_refl. simpl in *. eauto. Qed.


    Definition lt (x:t) (y:t) : Prop :=
      match RawIDOrd.beq (lbk x) (lbk y) with
      | true => InstrIDOrd.lt (lpt x) (lpt y)
      | false => RawIDOrd.lt (lbk x) (lbk y)
      end.



  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    destruct a; destruct b; destruct c. simpl in *. unfold lt. simpl in *. intros.
    destruct (RawIDOrd.beq lbk lbk0) eqn:?, (RawIDOrd.beq lbk0 lbk1) eqn:?, (RawIDOrd.beq lbk lbk1) eqn:?.
    +simpl in *. eapply RawIDOrd.beq_correct in Heqb. unfold RawIDOrd.eq in *. subst. eapply RawIDOrd.beq_correct in Heqb0. unfold RawIDOrd.eq in *. subst. eapply InstrIDOrd.lt_trans; eauto.
    +eapply RawIDOrd.beq_correct in Heqb. eapply RawIDOrd.beq_correct in Heqb0. unfold RawIDOrd.eq in *. subst. rewrite RawIDOrd.beq_refl in Heqb1. inversion Heqb1.
    +eapply RawIDOrd.beq_correct in Heqb. eapply RawIDOrd.beq_correct in Heqb1. unfold RawIDOrd.eq in *. subst. rewrite RawIDOrd.beq_refl in Heqb0. inversion Heqb0.
    +eapply RawIDOrd.beq_correct in Heqb. unfold RawIDOrd.eq in *. subst. eauto.
    +eapply RawIDOrd.beq_correct in Heqb0. eapply RawIDOrd.beq_correct in Heqb1. unfold RawIDOrd.eq in *. subst. rewrite RawIDOrd.beq_refl in Heqb. inversion Heqb.
    +eapply RawIDOrd.beq_correct in Heqb0. unfold RawIDOrd.eq in *. subst. eauto.
    +eapply RawIDOrd.beq_correct in Heqb1. unfold RawIDOrd.eq in *. subst. unfold  InstrIDOrd.lt. simpl in *.
     eapply RawIDOrd.lt_false in H; eauto. inversion H.
    +eapply RawIDOrd.lt_trans; eauto. Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof. intros. destruct a, b. simpl in *. unfold lt in *. simpl in *. unfold eq. simpl in *. unfold not. intros. inversion H0. subst. rewrite RawIDOrd.beq_refl in H. eapply InstrIDOrd.lt_not_eq in H. unfold InstrIDOrd.eq in *. tauto. Qed.



    Program Definition compare (x:t) (y:t) : Compare lt eq x y :=
      match RawIDOrd.compare (lbk x) (lbk y) with
      | LT _ => LT _
      | EQ _ => match InstrIDOrd.compare (lpt x) (lpt y) with
                | LT _ => LT _
                | EQ _ => EQ _
                | GT _ => GT _           
                end
      | GT _ => GT _
      end.
    Next Obligation.
destruct x, y. simpl in *. simpl. unfold lt. simpl in *.
destruct (RawIDOrd.beq lbk lbk0) eqn:?; eauto. generalize wildcard'. intros. eapply RawIDOrd.lt_not_eq in wildcard'0.  unfold not in wildcard'0.  eapply RawIDOrd.beq_correct in Heqb. tauto.
    Defined.
    Next Obligation.
      destruct x, y. simpl in *. unfold lt. simpl in *. destruct (RawIDOrd.beq lbk lbk0) eqn:?. eapply RawIDOrd.beq_correct in Heqb. unfold RawIDOrd.eq in *. eauto. eauto. assert (RawIDOrd.beq lbk lbk0 = true). eapply RawIDOrd.beq_correct. eauto. rewrite H in Heqb. inversion Heqb.
      Defined.
      Next Obligation.
        destruct x, y. simpl in *. unfold eq. unfold RawIDOrd.eq in *. unfold InstrIDOrd.eq in *. subst. eauto.
      Defined.
      Next Obligation.
        destruct x, y. simpl in *. unfold lt.  simpl in *. destruct (RawIDOrd.beq lbk0 lbk) eqn:?. eapply RawIDOrd.beq_correct in Heqb. unfold RawIDOrd.eq in *. subst. eauto. unfold RawIDOrd.eq in *. subst.
        assert (RawIDOrd.beq lbk0 lbk0 = true). rewrite RawIDOrd.beq_refl. eauto. rewrite H in Heqb. inversion Heqb.
      Defined.
      Next Obligation.
        destruct y, x. simpl in *. unfold lt. simpl in *. destruct (RawIDOrd.beq lbk lbk0) eqn:?; eauto. eapply RawIDOrd.beq_correct in Heqb. unfold RawIDOrd.eq in *. subst. generalize wildcard'; intros.


        eapply RawIDOrd.lt_not_eq in wildcard'0. unfold not in *. unfold RawIDOrd.eq in *. tauto.
      Defined.


  Definition eq_dec : forall (x y : t), {x = y} + {x <> y}.
    decide equality.
    -eapply  eq_dec_instr_id.
    -eapply eq_dec_raw_id.
     Defined.


      
End Local_PCOrd.



Instance eq_dec_local_pc : eq_dec local_pc := Local_PCOrd.eq_dec.


