Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coqlib.
Require Import Vellvm.optimisations.map_spec.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.






Print test.

Module PCTree <: TREE.
  Definition elt := pc.
  Definition pc_eq (a b: pc):= decide (a = b).
  Definition elt_eq := pc_eq.
  Definition tree A := list (elt * option A).
  Definition t := tree.


  Definition empty (A : Type) := (nil : t A).

  
  Fixpoint get (A:Type) (i:pc) (m: t A) : option A :=
    match m with
    | nil => None
    | (key, item) :: tl => if (elt_eq key i) then item else get i tl
    end.

  Fixpoint set (A: Type) (i: pc) (v:A) (m : t A) : t A :=
    match m with
    | nil => cons (i, Some v) nil
    | (key, item) :: tl => if (elt_eq key i) then (key, Some v) :: tl  else (key, item) :: set i v tl
    end.

  Fixpoint remove (A : Type) (i : pc) (m : t A) : t A :=
    match m with
    | nil => nil
    | (key, item) :: tl => if (elt_eq key i) then remove i tl else (key, item) :: remove i tl
    end.


  Theorem gempty :
    forall (A : Type) (i : pc), get i (empty A) = None.
  Proof. intros. simpl in *. eauto. Qed.
  Hint Resolve gempty.



  Theorem gss : forall (A : Type) (i : pc) (x : A) (m: t A), get i (set i x m) = Some x.
  Proof. induction m; simpl in *; eauto. destruct (elt_eq i i); eauto. contradiction n; eauto. destruct a; simpl in *. destruct ( elt_eq e i); subst; eauto. simpl in *.
         destruct ( elt_eq i i ); eauto. contradiction n; eauto. simpl in *. destruct (elt_eq e i); subst. contradiction n; eauto. eauto. 
  Qed.


  Lemma gleaf : forall (A : Type) (i : pc), get i (nil : t A) = None.
  Proof. intros. simpl in *. eauto. Qed. Hint Resolve gleaf.


  Theorem gso : forall (A : Type) (i j : pc) (x: A) (m : t A), i <> j -> get i (set j x m) = get i m.
  Proof. intros. induction m; simpl in *. destruct ( elt_eq j i). subst. contradiction H; eauto. eauto.

         destruct a. simpl in *. destruct ( elt_eq e j). simpl in *. subst. destruct ( elt_eq j i); subst. contradiction H; eauto. eauto. simpl in *. destruct (elt_eq e i). eauto. eauto. Qed.
Hint Resolve gso.
  
  Theorem gsspec : forall (A : Type) (i j: pc) (x : A) (m: t A), get i (set j x m) = if (elt_eq i j) then Some x else get i m.
  Proof. intros. induction m; simpl in *; eauto. destruct (elt_eq j i). destruct (elt_eq i j); subst; eauto. contradiction n; eauto. destruct (elt_eq i j); subst; eauto. contradiction n; eauto.


         destruct a. destruct (elt_eq e j). simpl in *. subst. destruct ( elt_eq j i). subst. destruct (elt_eq i i); eauto. contradiction n; eauto. simpl in *. eauto. simpl in *. destruct ( elt_eq i j); subst. contradiction n; eauto. eauto. simpl in *. destruct ( elt_eq e i); subst. destruct (elt_eq i j). subst. contradiction n; eauto. eauto. eauto. Qed. Hint Resolve gsspec.


  Theorem gsident: forall (A: Type) (i: pc) (m: t A) (v: A), get i m = Some v -> set i v m = m.
  Proof. intros. induction m; simpl in *.
         +inversion H.
         +simpl in *. destruct a. simpl in *. destruct (elt_eq e i). subst. simpl in *. eauto. apply IHm in H. rewrite H. auto. Qed. Hint Resolve gsident.


  Theorem grs:
    forall (A: Type) (i: pc) (m: t A), get i (remove i m) = None.
  Proof. intros. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *. destruct ( elt_eq e i). subst. auto. simpl in *. destruct (elt_eq e i). subst. contradiction n. auto. auto. Qed.
Hint Resolve grs.


  Theorem gro:
    forall (A: Type) (i j: pc) (m: t A),
      i <> j -> get i (remove j m) = get i m.
  Proof. intros. induction m. simpl in *. auto. simpl in *. destruct a. simpl in *.
         destruct ( elt_eq e j). subst. destruct ( elt_eq j i). subst. contradiction H; eauto.  eauto. simpl in *. destruct (elt_eq e i). auto. eauto. Qed. Hint Resolve gro.


  Theorem grspec: forall (A: Type) (i j: elt) (m: t A), get i (remove j m) = if elt_eq i j then None else get i m.
  Proof. intros. induction m. simpl in *. destruct (elt_eq i j). eauto. eauto. simpl in *. destruct a. simpl in *. destruct ( elt_eq e j), (elt_eq i j); subst; eauto. destruct ( elt_eq j i); subst. contradiction n; eauto.
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
      | (key, None), (key1, None) => (elt_eq key key1)
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
    
    

    Lemma beq_correct: forall m1 m2, beq m1 m2 = true <-> (forall (x: elt),
                                                              match get x m1, get x m2 with
                                                                           | None, None => True
                                                                           | Some y1, Some y2 => beqA y1 y2 = true
                                                                           | _, _ => False
                                                                                       end).
Proof. Admitted.
  End BOOLEAN_EQUALITY.



Print t.

  Fixpoint map (A B: Type) (f: pc -> A -> B) m : t B :=
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
  
      

  Theorem gmap: forall (A B: Type) (f: pc -> A -> B) (i: pc) (m: t A),
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

Print t.

Print tree.

  Fixpoint xcombine_l (m : t A) {struct m} : t C :=
    match m with
    | nil => nil
               | (key, val) :: tl => (key, (f val None)) :: xcombine_l tl
    (*  | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)*)
      end.


  Lemma xgcombine_l :
          forall m i,
          get i (xcombine_l m) = f (get i m) None.
Proof.
      induction m; intros; simpl; symmetry; eauto. destruct a. simpl in *. remember ( elt_eq e i). destruct s. simpl in *. eauto. symmetry. eauto. Qed.

  Fixpoint xcombine_r (m : t B) {struct m} : t C :=
    match m with
    | nil => nil
    | (key, val) :: tl => (key, (f None val)) :: xcombine_r tl
      end.


  Lemma xgcombine_r :
          forall m i,
          get i (xcombine_r m) = f None (get i m).
Proof.
      induction m; intros; simpl; symmetry; eauto. destruct a. simpl in *. remember ( elt_eq e i). destruct s. simpl in *. eauto. symmetry. eauto. Qed.



Fixpoint combine (l1: t A) (l2: t B) :=
  match l1 with
  | nil => xcombine_r l2
  | (a, b) :: tl => match get a l2 with
                       | None => (a, f b None) :: combine tl (remove a l2)
                       | Some res => (a, f b (Some res)) :: combine tl (remove a l2)
                       end
                         
                       
  end.



Theorem gcombine:
      forall m1 m2 i,
      get i (combine m1 m2) = f (get i m1) (get i m2).
Proof. 
 Admitted.



End COMBINE.
     

  Fixpoint elements A (m : t A) : (list (pc * A)) :=
    match m with
    | nil => nil
    | (key, Some item) :: tl => (key, item) :: elements tl
    | _ :: tl => elements tl
    end.
  
                                                    
  Theorem elements_correct: forall (A: Type) (m: t A) (i: pc) (v: A),
      get i m = Some v -> In (i, v) (elements m).
  Proof. induction m. simpl in *. intros. inversion H.
         simpl in *. destruct a. simpl in *. intros. destruct (elt_eq e i). subst. simpl in *. left. auto. simpl in *. destruct o. simpl in *. subst. right. apply IHm. auto. apply IHm. apply H. Qed.
  

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: pc) (v: A),
      In (i, v) (elements m) -> get i m = Some v.
  Proof. induction m. intros. simpl in *. inversion H. intros. simpl in *.   destruct a.
destruct ( elt_eq e i).



  Admitted.



  Definition xkeys (A: Type) (m: t A) (i: pc) :=
    List.map fst m.

Print list_norepet.
  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: pc),
      list_norepet (xkeys m i).
Proof. intros. induction m. simpl in *. constructor. simpl in *. destruct a. simpl in *. constructor. simpl in *. Admitted.


Theorem elements_keys_norepet:
  forall (A: Type) (m: t A),
    list_norepet (List.map fst (elements m)). Proof. Admitted.



Theorem elements_extensional:
  forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
Proof. Admitted.

Theorem elements_remove:
  forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i, v) :: l2 /\ elements (remove i m) = l1 ++ l2.
Proof. intros. Admitted.


Fixpoint fold1 (A B: Type) (f: B -> A -> B) (m: t A) (v: B) : B :=
  match m with
  | nil => v
  | (key, Some item) :: tl => fold1 f tl (f v item)
  | (key, None) :: tl => fold1 f tl v
  end.

Fixpoint fold (A B: Type) (f: B -> pc -> A -> B) (m: t A) (v: B) : B :=
  match m with
  | nil => v
  | (key, Some item) :: tl => fold f tl (f v key item)
  | (key, None) :: tl => fold f tl v
  end.


Theorem fold_spec:
  forall (A B: Type) (f: B -> pc -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
Proof. induction m. simpl in *. auto.
       simpl in *. destruct a. simpl in *. destruct o. simpl in *. eauto. Admitted.

Theorem fold1_spec:
  forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof. Admitted. 
End PCTree.

  
Module PCMap <: MAP.
  Definition elt := pc.
  Definition pc_eq (a b:pc) := decide (a = b).
  Definition elt_eq := pc_eq.

  Definition t (A : Type) : Type := (A * PCTree.t A)%type.

  Definition init (A : Type) (x: A) :=
    (x, PCTree.empty A).

  Definition get (A: Type) (i: pc) (m: t A) :=
    match PCTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.


  Definition set (A: Type) (i : pc) (x : A) (m : t A) :=
    (fst m, PCTree.set i x (snd m)).


  Theorem gi: forall (A: Type) (i: pc) (x: A), get i (init x) = x.
  Proof. intros. unfold init. unfold get. rewrite PCTree.gempty. simpl in *. auto. Qed.


  Theorem gss:
    forall (A: Type) (i: pc) (x: A) (m: t A), get i (set i x m) = x.
  Proof. intros. unfold get. unfold set. simpl in *. rewrite PCTree.gss. auto. Qed.


  Theorem gso:
    forall (A: Type) (i j: pc) (x: A) (m: t A),
      i <> j -> get i (set j x m) = get i m.
  Proof. intros. unfold get. unfold set. simpl in *. rewrite PCTree.gso; eauto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: pc) (x: A) (m: t A),
      get i (set j x m) = if pc_eq i j then x else get i m.
  Proof. intros.  destruct (elt_eq i j). subst. simpl in *. unfold get, set. simpl in *. destruct ( pc_eq j j). simpl in *. rewrite PCTree.gss. eauto. contradiction n; eauto.
 unfold get, set. simpl in *. destruct ( pc_eq i j). subst. contradiction n. auto. eapply PCTree.gso in n. rewrite n. eauto. Qed.


  Theorem gsident:
    forall (A: Type) (i j: pc) (m: t A),
      get j (set i (get i m) m) = get j m.
  Proof. intros. destruct ( elt_eq i j). simpl in *. subst. rewrite gss. auto. rewrite gso; eauto. Qed.


  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := (f (fst m), PCTree.map1 f (snd m)).





  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: pc) (m: t A),
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

Print t.

Print tree.

  Fixpoint xcombine_l (m : t A) {struct m} : t C :=
    match m with
    | nil => nil
               | (key, val) :: tl => (key, (f val None)) :: xcombine_l tl
    (*  | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)*)
      end.


  Lemma xgcombine_l :
          forall m i,
          get i (xcombine_l m) = f (get i m) None.
Proof.
      induction m; intros; simpl; symmetry; eauto. destruct a. simpl in *. remember ( elt_eq e i). destruct s. simpl in *. eauto. symmetry. eauto. Qed.

  Fixpoint xcombine_r (m : t B) {struct m} : t C :=
    match m with
    | nil => nil
    | (key, val) :: tl => (key, (f None val)) :: xcombine_r tl
      end.


  Lemma xgcombine_r :
          forall m i,
          get i (xcombine_r m) = f None (get i m).
Proof.
      induction m; intros; simpl; symmetry; eauto. destruct a. simpl in *. remember ( elt_eq e i). destruct s. simpl in *. eauto. symmetry. eauto. Qed.



Fixpoint combine (l1: t A) (l2: t B) :=
  match l1 with
  | nil => xcombine_r l2
  | (a, b) :: tl => match get a l2 with
                       | None => (a, f b None) :: combine tl (remove a l2)
                       | Some res => (a, f b (Some res)) :: combine tl (remove a l2)
                       end
                         
                       
  end.



Theorem gcombine:
      forall m1 m2 i,
      get i (combine m1 m2) = f (get i m1) (get i m2).
Proof. 
 Admitted.



End COMBINE.
     

  Fixpoint elements A (m : t A) : (list (local_id * A)) :=
    match m with
    | nil => nil
    | (key, Some item) :: tl => (key, item) :: elements tl
    | _ :: tl => elements tl
    end.
  
                                                    
  Theorem elements_correct: forall (A: Type) (m: t A) (i: local_id) (v: A),
      get i m = Some v -> In (i, v) (elements m).
  Proof. induction m. simpl in *. intros. inversion H.
         simpl in *. destruct a. simpl in *. intros. destruct (elt_eq e i). subst. simpl in *. left. auto. simpl in *. destruct o. simpl in *. subst. right. apply IHm. auto. apply IHm. apply H. Qed.
  

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: local_id) (v: A),
      In (i, v) (elements m) -> get i m = Some v.
  Proof. induction m. intros. simpl in *. inversion H. intros. simpl in *.   destruct a.
destruct ( elt_eq e i).



  Admitted.



  Definition xkeys (A: Type) (m: t A) (i: local_id) :=
    List.map fst m.

Print list_norepet.
  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: local_id),
      list_norepet (xkeys m i).
Proof. intros. induction m. simpl in *. constructor. simpl in *. destruct a. simpl in *. constructor. simpl in *. Admitted.


Theorem elements_keys_norepet:
  forall (A: Type) (m: t A),
    list_norepet (List.map fst (elements m)). Proof. Admitted.



Theorem elements_extensional:
  forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
Proof. Admitted.

Theorem elements_remove:
  forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i, v) :: l2 /\ elements (remove i m) = l1 ++ l2.
Proof. intros. Admitted.


Fixpoint fold1 (A B: Type) (f: B -> A -> B) (m: t A) (v: B) : B :=
  match m with
  | nil => v
  | (key, Some item) :: tl => fold1 f tl (f v item)
  | (key, None) :: tl => fold1 f tl v
  end.

Fixpoint fold (A B: Type) (f: B -> local_id -> A -> B) (m: t A) (v: B) : B :=
  match m with
  | nil => v
  | (key, Some item) :: tl => fold f tl (f v key item)
  | (key, None) :: tl => fold f tl v
  end.


Theorem fold_spec:
  forall (A B: Type) (f: B -> local_id -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
Proof. induction m. simpl in *. auto.
       simpl in *. destruct a. simpl in *. destruct o. simpl in *. eauto. Admitted.

Theorem fold1_spec:
  forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof. Admitted.
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
  Proof.
    intros. unfold set. simpl in *. decEq. Admitted.
End lidMap.
  



Notation "a # b" := (lidTree.get b a) (at level 1).
Notation "a ## b" := (lidMap.get b a) (at level 1).





(*********)


