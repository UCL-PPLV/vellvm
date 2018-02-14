Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.local_cfg.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coqlib.
Require Import Vellvm.optimisations.map_spec.
Require Import Vellvm.optimisations.eq_dec.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
Require Import Ascii.
Require Import Equalities.
Require Coq.MSets.MSetAVL.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

Module PCTree1 (v:BooleanDecidableType) <: TREE1.
    Definition elt := local_pc.
  Definition elt_eq := local_pcDec.eq_dec.


  Definition elt_eq_refl := @eq_refl elt.
  Definition elt_eq_sym := @eq_sym elt.
  Definition elt_eq_trans := @eq_trans elt.
  Definition elt_eqb := Local_PCOrd.beq.


  Lemma elt_eqb_eq : forall a b, elt_eqb a b = true <-> eq a b.
  Proof. intros. eapply Local_PCOrd.beq_correct. Qed.


  Definition val := v.t. Print BooleanDecidableType.
  Definition val_eq := v.eq.
  Definition val_eqb := v.eqb.
  
  Lemma val_eqb_eq : forall a b, val_eqb a b = true <-> v.eq a b.
  Proof. eapply v.eqb_eq.  Qed.

  Definition tree  := list (elt * val).
  Definition t := tree.

  Definition empty : list (elt * val) := nil.

    Fixpoint get (i:local_pc) (m: t) : option val :=
    match m with
    | nil => None
    | (key, item) :: tl => if (elt_eq key i) then Some item else get i tl
    end.


    Fixpoint set (i: local_pc) (v:val ) (m : t) : t :=
    match m with
    | nil => cons (i, v) nil
    | (key, item) :: tl => if (elt_eq key i) then (key, v) :: tl  else (key, item) :: set i v tl
    end.


    Fixpoint remove (i : local_pc) (m : t) : t :=
    match m with
    | nil => nil
    | (key, item) :: tl => if (elt_eq key i) then remove i tl else (key, item) :: remove i tl
    end.

  Theorem gempty :
    forall  (i : local_pc), get i (empty) = None.
  Proof. intros. simpl in *. eauto. Qed.
  Hint Resolve gempty.

  Theorem gss : forall (i : local_pc) (x : val) (m: t), get i (set i x m) = Some x.
  Proof. induction m; simpl in *; eauto. destruct (elt_eq i i). eauto. contradiction n; eauto.
         destruct a; simpl in *. destruct ( elt_eq e i). simpl in *. subst.
         destruct (elt_eq i i). eauto. tauto. simpl in *. destruct ( elt_eq e i); subst; tauto.
  Qed.



  
  Lemma gleaf : forall  (i : local_pc), get i (nil : t A) = None.
  Proof. intros. simpl in *. eauto. Qed. Hint Resolve gleaf.


  Theorem gso : forall (A : Type) (i j : local_pc) (x: A) (m : t A), i <> j -> get i (set j x m) = get i m.
  Proof. intros. induction m; simpl in *. destruct (elt_eq j i). subst. contradiction H; eauto.
eauto. destruct a.  simpl in * . destruct (elt_eq e j), (elt_eq e i); subst. contradiction H; eauto. simpl in *. destruct (elt_eq j i). subst. contradiction H; eauto. eauto. simpl in *.
destruct (elt_eq i i). eauto. contradiction n0; eauto. simpl in *. destruct ( elt_eq e i). subst. contradiction n0; eauto. eauto.
  Qed.
Hint Resolve gso.
  
  Theorem gsspec : forall (A : Type) (i j: local_pc) (x : A) (m: t A), get i (set j x m) = if (elt_eq i j) then Some x else get i m.
  Proof. intros. induction m; simpl in *; eauto.
         destruct (elt_eq j i), (elt_eq i j); subst; auto; try contradiction n; eauto.
         destruct a. destruct (elt_eq e j), ( elt_eq i j); subst; simpl in *. destruct ( elt_eq j j). eauto.
         contradiction n; eauto. destruct ( elt_eq j i). subst. contradiction n; eauto. eauto.
         destruct ( elt_eq e j); subst. contradiction n; eauto. eauto. rewrite IHm. eauto.
          Qed.
 Hint Resolve gsspec.


  Theorem gsident: forall (A: Type) (i: local_pc) (m: t A) (v: A), get i m = Some v -> set i v m = m.
  Proof. intros. induction m; simpl in *.
         +inversion H.
         +simpl in *. destruct a. destruct (elt_eq e i); subst; eauto. eapply IHm in H. rewrite H. auto.



  Qed. Hint Resolve gsident.

End PCTree1.
Module PCTree <: TREE.
  Definition elt := local_pc.
         
  Definition elt_eq := local_pcDec.eq_dec.

  Definition tree A := list (elt * option A).
  Definition t := tree.


  Definition empty (A : Type) := (nil : t A).

  
  Fixpoint get (A:Type) (i:local_pc) (m: t A) : option A :=
    match m with
    | nil => None
    | (key, item) :: tl => if (elt_eq key i) then item else get i tl
    end.

  Fixpoint set (A: Type) (i: local_pc) (v:A) (m : t A) : t A :=
    match m with
    | nil => cons (i, Some v) nil
    | (key, item) :: tl => if (elt_eq key i) then (key, Some v) :: tl  else (key, item) :: set i v tl
    end.

  Fixpoint remove (A : Type) (i : local_pc) (m : t A) : t A :=
    match m with
    | nil => nil
    | (key, item) :: tl => if (elt_eq key i) then remove i tl else (key, item) :: remove i tl
    end.


  Theorem gempty :
    forall (A : Type) (i : local_pc), get i (empty A) = None.
  Proof. intros. simpl in *. eauto. Qed.
  Hint Resolve gempty.



  Theorem gss : forall (A : Type) (i : local_pc) (x : A) (m: t A), get i (set i x m) = Some x.
  Proof. induction m; simpl in *; eauto. destruct (elt_eq i i). eauto. contradiction n; eauto.
         destruct a; simpl in *. destruct ( elt_eq e i). simpl in *. subst.
         destruct (elt_eq i i). eauto. contradiction n; eauto. simpl in *. destruct ( elt_eq e i); subst. contradiction n; eauto. eauto.
  Qed.


  Lemma gleaf : forall (A : Type) (i : local_pc), get i (nil : t A) = None.
  Proof. intros. simpl in *. eauto. Qed. Hint Resolve gleaf.


  Theorem gso : forall (A : Type) (i j : local_pc) (x: A) (m : t A), i <> j -> get i (set j x m) = get i m.
  Proof. intros. induction m; simpl in *. destruct (elt_eq j i). subst. contradiction H; eauto.
eauto. destruct a.  simpl in * . destruct (elt_eq e j), (elt_eq e i); subst. contradiction H; eauto. simpl in *. destruct (elt_eq j i). subst. contradiction H; eauto. eauto. simpl in *.
destruct (elt_eq i i). eauto. contradiction n0; eauto. simpl in *. destruct ( elt_eq e i). subst. contradiction n0; eauto. eauto.
  Qed.
Hint Resolve gso.
  
  Theorem gsspec : forall (A : Type) (i j: local_pc) (x : A) (m: t A), get i (set j x m) = if (elt_eq i j) then Some x else get i m.
  Proof. intros. induction m; simpl in *; eauto.
         destruct (elt_eq j i), (elt_eq i j); subst; auto; try contradiction n; eauto.
         destruct a. destruct (elt_eq e j), ( elt_eq i j); subst; simpl in *. destruct ( elt_eq j j). eauto.
         contradiction n; eauto. destruct ( elt_eq j i). subst. contradiction n; eauto. eauto.
         destruct ( elt_eq e j); subst. contradiction n; eauto. eauto. rewrite IHm. eauto.
          Qed.
 Hint Resolve gsspec.


  Theorem gsident: forall (A: Type) (i: local_pc) (m: t A) (v: A), get i m = Some v -> set i v m = m.
  Proof. intros. induction m; simpl in *.
         +inversion H.
         +simpl in *. destruct a. destruct (elt_eq e i); subst; eauto. eapply IHm in H. rewrite H. auto.



  Qed. Hint Resolve gsident.


  Theorem grs:
    forall (A: Type) (i: local_pc) (m: t A), get i (remove i m) = None.
  Proof. intros. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *. destruct (elt_eq e i). subst. eauto. simpl in *. destruct ( elt_eq e i). subst. contradiction n; eauto. eauto.  Qed.
Hint Resolve grs.


  Theorem gro:
    forall (A: Type) (i j: local_pc) (m: t A),
      i <> j -> get i (remove j m) = get i m.
  Proof. intros. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *.
destruct ( elt_eq e j), (elt_eq e i); subst. contradiction H; eauto. eauto. simpl in *.
destruct (elt_eq i i); eauto. contradiction n0; eauto. simpl in *. destruct (elt_eq e i). subst. contradiction n0; eauto. eauto.
  Qed. Hint Resolve gro.


  Theorem grspec: forall (A: Type) (i j: elt) (m: t A), get i (remove j m) = if elt_eq i j then None else get i m.
  Proof. intros. induction m. simpl in *. destruct ( elt_eq i j). eauto. eauto. simpl in *. destruct a.
    destruct ( elt_eq e j),  ( elt_eq i j); subst; simpl in *; eauto. destruct ( elt_eq j i); subst. contradiction n; eauto. eauto. destruct ( elt_eq e j). subst. contradiction n; eauto. eauto. rewrite IHm. eauto.

  Qed.

  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.

(*
    Definition bsingle_empty A (a: (elt * option A)) :=
      match a with
      | (key, _) => false
      | _ => true
               
      end.
 *)
    (*
    Fixpoint bempty (m: t A) : bool :=
      match m with
      | nil => true
      | hd :: tl => bsingle_empty hd && bempty tl
      end.
*)
    Definition beq_single (a b :(elt * option A)) : bool :=
      match a, b with
      | (key, None), (key1, None) => (elt_eq key key1)
      | (key, Some a), (key1, Some a1) => (elt_eq key key1) && (beqA a a1)
      | _, _ => false
      end.
    



    
    Fixpoint beq (m1 m2: t A) : bool :=
      match m1, m2 with
      | nil, nil => true
      | _, nil => false
      | nil, _ => false
      | hd::tl, hd1::tl1 =>  beq_single hd hd1 && beq tl tl1                 
      end.


    Lemma correct_eq : forall a b, beq a b = true <-> a = b.
    Proof. intros; split; intros. induction a, b; simpl in *; eauto. inversion H. inversion H. simpl in *.
           destruct a, p. simpl in *. destruct o, o0. simpl in *.
           assert (beqA a a1 = true). destruct ( beqA a a1). eauto.  Admitted.
    (*
        Lemma bempty_correct:
      forall m, bempty m = true <-> (forall x, get x m = None).
Proof.
      induction m; simpl.
      split; intros; eauto.

      split; intros. destruct a. simpl in *. destruct o. simpl in *. inversion H. simpl in *. destruct (elt_eq e x). subst. eauto. eapply IHm. eauto.




      eapply andb_true_intro; split.  admit.





      destruct a. eapply IHm. destruct o. simpl in *. intros. specialize (

 

      destruct ; split; intros.
      congruence.
      generalize (H xH); simpl; congruence.
      destruct (andb_prop _ _ H). rewrite IHm1 in H0. rewrite IHm2 in H1.
      destruct x; simpl; auto.
      apply andb_true_intro; split.
      apply IHm1. intros; apply (H (xO x)).
      apply IHm2. intros; apply (H (xI x)).
    Qed.*)





           
    
    Lemma beq_correct: forall m1 m2, beq m1 m2 = true <-> (forall (x: elt),
                                                              match get x m1, get x m2 with
                                                                           | None, None => True
                                                                           | Some y1, Some y2 => beqA y1 y2 = true
                                                                           | _, _ => False
                                                                                       end).
    Proof. induction m1; intros.
           +simpl. split; intros.
           -induction m2. simpl in *. eauto.
           -simpl in *. destruct a. simpl in *. destruct o. simpl in *. inversion H. simpl in *.
*


(*
      induction m1. intros.
           -simpl in *. rewrite bempty_correct.



      induction m1; intros.
    - simpl. rewrite bempty_correct. split; intros.
      rewrite gleaf. rewrite H. auto.
      generalize (H x). rewrite gleaf. destruct (get x m2); tauto.
    - destruct m2.
      + unfold beq. rewrite bempty_correct. split; intros.
        rewrite H. rewrite gleaf. auto.
        generalize (H x). rewrite gleaf. destruct (get x (Node m1_1 o m1_2)); tauto.
      + simpl. split; intros.
        * destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0).
          rewrite IHm1_1 in H3. rewrite IHm1_2 in H1.
          destruct x; simpl. apply H1. apply H3.
          destruct o; destruct o0; auto || congruence.
        * apply andb_true_intro. split. apply andb_true_intro. split.
          generalize (H xH); simpl. destruct o; destruct o0; tauto.
          apply IHm1_1. intros; apply (H (xO x)).
          apply IHm1_2. intros; apply (H (xI x)).
    Qed.



    Admitted.*) Admitted.
  End BOOLEAN_EQUALITY.



Print t.

  Fixpoint map (A B: Type) (f: local_pc -> A -> B) m : t B :=
    match m with
    | nil => nil
    | (key, Some item) :: tl => (key, Some (f key item)) :: map f tl
    | (key, None) :: tl => (key, None) :: map f tl
    end.
 

  Fixpoint map1 (A B: Type) (f: A -> B) (m: t A) : t B :=
    match m with
    | nil => nil
    | (key, None) :: tl => (key, None) :: map1 f tl
    | (key, Some a) :: tl => (key, Some (f a)) :: map1 f tl
    end.
  
      

  Theorem gmap: forall (A B: Type) (f: local_pc -> A -> B) (i: local_pc) (m: t A),
      get i (map f m) = option_map (f i) (get i m).
  Proof. intros. induction m; simpl in *; eauto. destruct a. simpl in *.
         destruct (elt_eq e i). subst. simpl in *. destruct o. simpl in *. destruct (elt_eq i i). subst. eauto. contradiction n; eauto. simpl in *. destruct ( elt_eq i i). eauto. contradiction n; eauto. destruct o. simpl in *.
         destruct (elt_eq e i); subst. contradiction n; eauto. eauto. simpl in *.
         destruct ( elt_eq e i). subst. contradiction n; eauto. eauto. Qed.

  Theorem gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
      get i (map1 f m) = option_map f (get i m).
  Proof. induction m; simpl in *; eauto. destruct a; simpl in *. destruct (elt_eq e i). subst.
         destruct o; simpl in *. destruct ( elt_eq i i); eauto. contradiction n; eauto.
         destruct (elt_eq i i); eauto. contradiction n; eauto. destruct o; simpl in *.
         destruct (elt_eq e i). subst. contradiction n; eauto. eauto. destruct (elt_eq e i). subst. contradiction n; eauto.
         eauto. Qed.




  Section COMBINE.

    Variables A B C: Type.
    Variable f: option A -> option B -> option C.
    Hypothesis f_none_none: f None None = None.

    Fixpoint combine_r (l : t B) :=
      match l with
      | nil => nil
      | (key, val) :: tl => (key, f None val) :: combine_r tl
      end.
    

Fixpoint combine (p: t A) (p1: t B) :=
  match p with
  | nil => combine_r p1
  | (key, val) :: tl => (key, f val (get key p1)) :: combine tl p1
  end.



Theorem gcombine:
      forall p p1 i,
      get i (combine p p1) = f (get i p) (get i p1).
Proof. induction p; intros; simpl in *.
       +induction p1; simpl in *. symmetry; eauto. destruct a; simpl in *. destruct ( elt_eq e i); subst; eauto.
        destruct a; simpl in *. destruct ( elt_eq e i); subst; eauto. Qed.


End COMBINE.
End PCTree.

  
Module PCMap <: MAP.
  Definition elt := local_pc.
  Definition pc_eq (a b:local_pc) := local_pcDec.eq_dec.
  Definition elt_eq := local_pcDec.eq_dec.

  Definition t (A : Type) : Type := (A * PCTree.t A)%type.

  Definition init (A : Type) (x: A) :=
    (x, PCTree.empty A).

  Definition get (A: Type) (i: local_pc) (m: t A) :=
    match PCTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.


  Definition set (A: Type) (i : local_pc) (x : A) (m : t A) :=
    (fst m, PCTree.set i x (snd m)).


  Theorem gi: forall (A: Type) (i: local_pc) (x: A), get i (init x) = x.
  Proof. intros. unfold init. unfold get. rewrite PCTree.gempty. simpl in *. auto. Qed.


  Theorem gss:
    forall (A: Type) (i: local_pc) (x: A) (m: t A), get i (set i x m) = x.
  Proof. intros. unfold get. unfold set. simpl in *. rewrite PCTree.gss. auto. Qed.


  Theorem gso:
    forall (A: Type) (i j: local_pc) (x: A) (m: t A),
      i <> j -> get i (set j x m) = get i m.
  Proof. intros. unfold get. unfold set. simpl in *. rewrite PCTree.gso; eauto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: local_pc) (x: A) (m: t A),
      get i (set j x m) = if elt_eq i j then x else get i m.
  Proof. intros.  destruct (elt_eq i j); subst; eauto. eapply gss. unfold get, set; simpl in *.
         rewrite PCTree.gso. eauto. eauto. Qed.



  Theorem gsident:
    forall (A: Type) (i j: local_pc) (m: t A),
      get j (set i (get i m) m) = get j m.
  Proof. intros. destruct ( elt_eq i j). simpl in *. subst. rewrite gss. auto. rewrite gso; eauto. Qed.


  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := (f (fst m), PCTree.map1 f (snd m)).





  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: local_pc) (m: t A),
      get i (map f m) = f (get i m).
  Proof. intros. unfold map. unfold get. simpl in *. rewrite PCTree.gmap1. unfold option_map.
         destruct (PCTree.get i (snd m)); eauto. Qed.


  Theorem set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
      set i y (set i x m) = set i y m.
  Proof. induction m; simpl in *. unfold set. simpl in *. induction b. simpl in *. destruct (PCTree.elt_eq i i). eauto. contradiction n; eauto.
         simpl in *. destruct a0. simpl in *. destruct ( PCTree.elt_eq e i). subst. simpl in *. destruct ( PCTree.elt_eq i i ). eauto. contradiction n. eauto.
         simpl in *. destruct (PCTree.elt_eq e i). subst. contradiction n; eauto. inversion IHb. rewrite H0. eauto. Qed.
End PCMap.
  



Notation "a ! b" := (PCTree.get b a) (at level 1).
Notation "a !! b" := (PCMap.get b a) (at level 1).





(*********)



Definition loc_id_eq (a b:local_id) := decide (a = b).
















Module lidTree <: TREE.
  Definition elt := local_id.
  Definition elt_eq := loc_id_eq.
  Definition tree A := list (elt * option A).
  Definition t := tree.


  Definition empty (A : Type) := (nil : t A).
Print elt_eq.
  
  Fixpoint get (A:Type) (i:local_id) (m: t A) : option A :=
    match m with
    | nil => None
    | (key, item) :: tl => if (elt_eq key i) then item else get i tl
    end.

  Fixpoint set (A: Type) (i: local_id) (v:A) (m : t A) : t A :=
    match m with
    | nil => cons (i, Some v) nil
    | (key, item) :: tl => if (elt_eq key i) then (key, Some v) :: tl  else (key, item) :: set i v tl
    end.

  Fixpoint remove (A : Type) (i : local_id) (m : t A) : t A :=
    match m with
    | nil => nil
    | (key, item) :: tl => if (elt_eq key i) then remove i tl else (key, item) :: remove i tl
    end.


  Theorem gempty :
    forall (A : Type) (i : local_id), get i (empty A) = None.
  Proof. intros. simpl in *. eauto. Qed.
  Hint Resolve gempty.



  Theorem gss : forall (A : Type) (i : local_id) (x : A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros. induction m; simpl in *. destruct ( elt_eq i i). eauto. contradiction n; eauto. destruct a. simpl in *.
    destruct ( elt_eq e i). subst. simpl in *. destruct (elt_eq i i). eauto. contradiction n; eauto. simpl in *.
    destruct ( elt_eq e i). subst. contradiction n ; eauto. eauto.
  Qed.


  Lemma gleaf : forall (A : Type) (i : local_id), get i (nil : t A) = None.
  Proof. intros. simpl in *. eauto. Qed. Hint Resolve gleaf.


  Theorem gso : forall (A : Type) (i j : local_id) (x: A) (m : t A), i <> j -> get i (set j x m) = get i m.
  Proof. intros. induction m; simpl in *. destruct ( elt_eq j i). subst. contradiction H; eauto. eauto.

         destruct a. simpl in *. destruct ( elt_eq e j). simpl in *. subst. destruct ( elt_eq j i); subst. contradiction H; eauto. eauto. simpl in *. destruct (elt_eq e i). eauto. eauto. Qed.
Hint Resolve gso.
  
  Theorem gsspec : forall (A : Type) (i j: local_id) (x : A) (m: t A), get i (set j x m) = if (elt_eq i j) then Some x else get i m.
  Proof. intros. induction m; simpl in *; eauto. destruct (elt_eq j i). destruct (elt_eq i j); subst; eauto. contradiction n; eauto. destruct (elt_eq i j); subst; eauto. contradiction n; eauto.


         destruct a. destruct (elt_eq e j). simpl in *. subst. destruct ( elt_eq j i). subst. destruct (elt_eq i i); eauto. contradiction n; eauto. simpl in *. eauto. simpl in *. destruct ( elt_eq i j); subst. contradiction n; eauto. eauto. simpl in *. destruct ( elt_eq e i); subst. destruct (elt_eq i j). subst. contradiction n; eauto. eauto. eauto. Qed. Hint Resolve gsspec.


  Theorem gsident: forall (A: Type) (i: local_id) (m: t A) (v: A), get i m = Some v -> set i v m = m.
  Proof. intros. induction m; simpl in *.
         +inversion H.
         +simpl in *. destruct a. simpl in *. destruct (elt_eq e i). subst. simpl in *. eauto. apply IHm in H. rewrite H. auto. Qed. Hint Resolve gsident.


  Theorem grs:
    forall (A: Type) (i: local_id) (m: t A), get i (remove i m) = None.
  Proof. intros. induction m. simpl in *. auto. simpl in *.
         destruct a. simpl in *. destruct ( elt_eq e i).
         subst. auto. simpl in *. destruct (elt_eq e i).
         subst. contradiction n. auto. auto. Qed.
Hint Resolve grs.


  Theorem gro:
    forall (A: Type) (i j: local_id) (m: t A),
      i <> j -> get i (remove j m) = get i m.
  Proof. intros. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *.
         destruct ( elt_eq e j). subst. destruct ( elt_eq j i). subst.
         contradiction H; eauto.  eauto. simpl in *.
         destruct (elt_eq e i). auto. eauto.
  Qed. Hint Resolve gro.


  Theorem grspec: forall (A: Type) (i j: elt) (m: t A), get i (remove j m) = if elt_eq i j then None else get i m.
  Proof. intros. induction m. simpl in *. destruct (elt_eq i j). eauto.
         eauto. simpl in *. destruct a. simpl in *.
         destruct ( elt_eq e j), (elt_eq i j); subst; eauto.
         destruct ( elt_eq j i); subst. contradiction n; eauto.
         eauto. simpl in *. destruct ( elt_eq e j); subst; eauto. contradiction n; eauto.
         simpl in *. destruct ( elt_eq e i); eauto.
         Qed.

  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.


    Definition bsingle_empty A (a: (elt * option A)) :=
      match a with
      | (key, Some item) => true
      | _ => false
               
      end.
    
    Fixpoint bempty (m: t A) : bool :=
      match m with
      | nil => true
      | hd :: tl => bsingle_empty hd && bempty tl
      end.


    Definition beq_single (a b :(elt * option A)) : bool :=
      match a, b with
      | (key, None), (key1, None) => elt_eq key key1
      | (key, Some a), (key1, Some a1) => (elt_eq key key1) && (beqA a a1)
      | _, _ => false
      end.
    
                

    Fixpoint beq (m1 m2: t A) : bool :=
      match m1, m2 with
      | nil, nil => true
      | _, nil => bempty m1
      | nil, _ => bempty m2
      | hd::tl, hd1::tl1 =>  beq_single hd hd1 && beq tl tl1                 
      end.
    
    
    Lemma bempty_correct:
      forall m, bempty m = true <-> (forall x, get x m = None).
    Proof. Admitted.


    Lemma beq_correct: forall m1 m2, beq m1 m2 = true <-> (forall (x: elt),
                                                              match get x m1, get x m2 with
                                                                           | None, None => True
                                                                           | Some y1, Some y2 => beqA y1 y2 = true
                                                                           | _, _ => False
                                                                                       end).
Proof. Admitted.
  End BOOLEAN_EQUALITY.



Print t.

  Fixpoint map (A B: Type) (f: local_id -> A -> B) m : t B :=
    match m with
    | nil => nil
    | (key, Some item) :: tl => (key, Some (f key item)) :: map f tl
    | (key, None) :: tl => (key, None) :: map f tl
    end.
 

  Fixpoint map1 (A B: Type) (f: A -> B) (m: t A) : t B :=
    match m with
    | nil => nil
    | (key, None) :: tl => (key, None) :: map1 f tl
    | (key, Some a) :: tl => (key, Some (f a)) :: map1 f tl
    end.
  
      

  Theorem gmap: forall (A B: Type) (f: local_id -> A -> B) (i: local_id) (m: t A),
      get i (map f m) = option_map (f i) (get i m).
  Proof. intros. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *. destruct o. simpl in *. destruct (elt_eq e i). subst. eauto. simpl in *. eauto. simpl in *. destruct ( elt_eq e i). subst. simpl in *. eauto. eauto. Qed.




  Theorem gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
      get i (map1 f m) = option_map f (get i m).
  Proof. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *. destruct o. simpl in *. destruct (elt_eq e i). subst. simpl in *. auto. eauto. simpl in *.  destruct ( elt_eq e i). subst. simpl in *. eauto. eauto. Qed.





  Section COMBINE.

    Variables A B C: Type.
    Variable f: option A -> option B -> option C.
    Hypothesis f_none_none: f None None = None.






    Fixpoint combine_r (l : t B) :=
      match l with
      | nil => nil
      | (key, val) :: tl => (key, f None val) :: combine_r tl
      end.
    

Fixpoint combine (p: t A) (p1: t B) :=
  match p with
  | nil => combine_r p1
  | (key, val) :: tl => (key, f val (get key p1)) :: combine tl p1
  end.



Theorem gcombine:
      forall p p1 i,
      get i (combine p p1) = f (get i p) (get i p1).
Proof. induction p; intros; simpl in *.
       +induction p1; simpl in *. symmetry; eauto. destruct a. simpl in *. destruct ( elt_eq e i); simpl in *; eauto.
       +destruct a. simpl in *. destruct (elt_eq e i); subst; eauto. Qed.



End COMBINE.
End lidTree.

  
Module lidMap <: MAP.
  Definition elt := local_id.
  Definition elt_eq := loc_id_eq.

  Definition t (A : Type) : Type := (A * lidTree.t A)%type.

  Definition init (A : Type) (x: A) :=
    (x, lidTree.empty A).

  Definition get (A: Type) (i: local_id) (m: t A) :=
    match lidTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.


  Definition set (A: Type) (i : local_id) (x : A) (m : t A) :=
    (fst m, lidTree.set i x (snd m)).


  Theorem gi: forall (A: Type) (i: local_id) (x: A), get i (init x) = x.
  Proof. intros. unfold init. unfold get. rewrite lidTree.gempty. simpl in *. auto. Qed.


  Theorem gss:
    forall (A: Type) (i: local_id) (x: A) (m: t A), get i (set i x m) = x.
  Proof. intros. unfold get. unfold set. simpl in *. rewrite lidTree.gss. auto. Qed.


  Theorem gso:
    forall (A: Type) (i j: local_id) (x: A) (m: t A),
      i <> j -> get i (set j x m) = get i m.
  Proof. intros. unfold get. unfold set. simpl in *. rewrite lidTree.gso; eauto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: local_id) (x: A) (m: t A),
      get i (set j x m) = if elt_eq i j then x else get i m.
  Proof. intros.  destruct (elt_eq i j). subst. apply gss. rewrite gso. auto. auto. Qed.



  Theorem gsident:
    forall (A: Type) (i j: local_id) (m: t A),
      get j (set i (get i m) m) = get j m.
  Proof. intros. destruct ( elt_eq i j). simpl in *. subst. rewrite gss. auto. rewrite gso; eauto. Qed.


  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := (f (fst m), lidTree.map1 f (snd m)).





  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: local_id) (m: t A),
      get i (map f m) = f (get i m).
  Proof. intros. unfold map. unfold get. simpl in *. rewrite lidTree.gmap1. unfold option_map.
         destruct (lidTree.get i (snd m)); eauto. Qed.


  Theorem set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
      set i y (set i x m) = set i y m.
  Proof. induction m; simpl in *. unfold set. simpl in *. induction b. simpl in *. destruct (lidTree.elt_eq i i). eauto. contradiction n; eauto.
         simpl in *. destruct a0. simpl in *. destruct (lidTree.elt_eq e i). subst. simpl in *. destruct ( lidTree.elt_eq i i ). eauto. contradiction n. eauto.
         simpl in *. destruct (lidTree.elt_eq e i). subst. contradiction n; eauto. inversion IHb. rewrite H0. eauto. Qed.
End lidMap.
  



Notation "a # b" := (lidTree.get b a) (at level 1).
Notation "a ## b" := (lidMap.get b a) (at level 1).





(*********)


