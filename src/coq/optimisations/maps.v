Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coqlib.

Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.


Require Import compcert.lib.Maps.

Definition test (a b:pc):= decide (a = b).


Module PCTree <: TREE.
  Definition elt := pc.
  Definition elt_eq := test.
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
  Proof. Admitted.

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


    Fixpoint xcombine_l (m1 : t A) : t C :=
      match m1 with
      | nil => nil
      | (key, item) :: tl => (key, f item None) :: xcombine_l tl
      end.

    Lemma xgcombine_l :
      forall (m: t A) (i : pc),
        get i (xcombine_l m) = f (get i m) None.
    Proof.
      induction m; intros; simpl in *. eauto. simpl in *. destruct a. simpl in *. destruct ( elt_eq e i). eauto. simpl in *. eauto. Qed.

    Fixpoint xcombine_r (m : t B) : t C :=
      match m with
      | nil => nil
      | (key, item) :: tl => (key, f None item) :: xcombine_r tl
      end.

    Lemma xgcombine_r :
      forall (m: t B) (i: pc),
        get i (xcombine_r m) = f None (get i m).
    Proof. intros. induction m; simpl in *; eauto.
           destruct a. simpl in *. destruct (elt_eq e i). eauto. eauto. Qed.


    Fixpoint combine (m1: t A) (m2: t B) : t C :=
      match m1, m2 with
      | nil, nil => nil
      | nil, list => xcombine_r list
      | list, nil => xcombine_l list
      | (key, item)::tl, (key1, item1)::tl1 => (key, (f item item1)) :: combine tl tl1
      end.


    Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: pc),
        get i (combine m1 m2) = f (get i m1) (get i m2).
      Proof. induction m1. simpl in *. induction m2. simpl in *. auto. simpl in *. 
             intros. destruct a. simpl in *. destruct ( elt_eq e i); simpl in *; eauto. induction m2. simpl in *; eauto. simpl in *. destruct a. simpl in *. specialize (IHm2 i). auto.
             simpl in *. destruct a. simpl in *. induction m2. simpl in *. intros. destruct (elt_eq e i). eauto. induction m1. simpl in *. auto. simpl in *. destruct a. simpl in *.





             destruct (elt_eq e0 i). eauto. apply IHm0. simpl in *. Admitted.

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
  Proof. induction m. intros. simpl in *. inversion H. intros. simpl in *.  Admitted.



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
  Definition elt_eq := test.

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
      get i (set j x m) = if elt_eq i j then x else get i m.
  Proof. intros.  destruct (elt_eq i j). subst. apply gss. rewrite gso. auto. auto. Qed.



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
  Proof.
    intros. unfold set. simpl in *. decEq. Admitted.
End PCMap.
  


Notation "a ! b" := (PCTree.get b a) (at level 1).
Notation "a !! b" := (PCMap.get b a) (at level 1).

(*
  
  Definition elt := pc.
  Definition pc_comp (A B:pc) : bool := decide (A = B).
  Print pc_comp.
  Definition elt_eq := pc_comp.



  Definition t A := seq (pc * option A).

  Definition empty (A : Type) := (nil : t A).
  Print elt_eq.
  
  Fixpoint get (A : Type) (p : pc) (m : t A) : option A :=
    match m with
    | nil => None
    | hd :: tl => if (elt_eq (fst hd) p) then (snd hd) else get  p tl
    end.


  Fixpoint get (A : Type) (i : pc) (v : A) (m : t A) : t A :=
    match m with
    | nil => cons (i, Some v) nil
    | hd :: tl  => if (elt_eq (fst hd) i) then (i, Some v) :: tl else hd :: (set i v tl)
    end.


  Fixpoint remove (A : Type) (p : pc) (m : t A) : t A :=
    match m with
    | nil => nil
    | hd :: tl => if (elt_eq (fst hd) p) then remove p tl else hd :: (remove p tl)
    end.



  Lemma eq_refl : forall i, elt_eq i i = true.
  Proof. intros. unfold elt_eq. unfold pc_comp. destruct ( decide (i = i)). simpl in *. eauto. contradiction n. eauto. Qed.
Hint Rewrite eq_refl.
  
      Theorem gempty:
    forall (A: Type) (i: pc), get i (empty A) = None.
Proof. move => //. Qed.

  Theorem gss:
    forall (A: Type) (i: pc) (x: A) (m:t A), get i (set i x m) = Some x.
  Proof. intros. induction m; simpl in *. rewrite eq_refl. eauto. simpl in *. destruct a. simpl in *. unfold elt_eq. unfold pc_comp. unfold is_left. simpl in *. destruct ( decide (p = i)); simpl in *; eauto. rewrite eq_refl. eauto. simpl in *. unfold elt_eq. simpl in *. unfold pc_comp. simpl in *. unfold is_left. destruct (decide (p = i)); subst. contradiction n; eauto. eauto. Qed.

Hint Resolve gss.

         
    Lemma gleaf : forall (A : Type) (i : pc), get i (nil : t A) = None.
    Proof. intros. simpl in *. auto. Qed.
Hint Resolve gleaf.
    
  Theorem gso:
    forall (A: Type) (i j: pc) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof. intros. induction m. simpl in *.
         +unfold elt_eq. simpl in *. unfold pc_comp. unfold is_left. destruct ( decide (j = i)). subst. contradiction H; eauto. eauto.
         +simpl in *. unfold elt_eq. simpl in *. unfold pc_comp. simpl in *. unfold is_left. simpl in *. destruct a. simpl in *.
          destruct ( decide (p = j)). simpl in *; subst. unfold elt_eq. unfold pc_comp. unfold is_left. simpl in *. destruct ( decide (j = i)); subst. contradiction H. eauto. eauto.
         +simpl in *. unfold elt_eq. simpl in *. unfold pc_comp. simpl in *. unfold is_left. simpl in *. destruct ( decide (p = i)); subst. eauto. simpl in *. eauto. Qed.
Hint Resolve gso.
         
  Theorem gsspec:
    forall (A: Type) (i j: pc) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
Proof.
  intros. unfold elt_eq. unfold pc_comp. unfold is_left. simpl in *. destruct ( decide (i = j)). subst. auto. auto. Qed.
Hint Resolve gsspec.


  
  Theorem gsident:
    forall (A: Type) (i: pc) (m: t A) (v: A),
      get i m = Some v -> set i v m = m.
  Proof. intros. induction m; simpl in *; eauto.
         +inversion H.
         +destruct a. unfold elt_eq in *. unfold pc_comp in *. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (p = i)); subst; eauto. simpl in *. apply IHm in H. rewrite H; eauto. Qed.
Hint Resolve gsident.



  Theorem set2:
    forall (A: Type) (i: elt) (m: t A) (v1 v2: A),
    set i v2 (set i v1 m) = set i v2 m.
  Proof. intros. induction m. simpl in *. rewrite  eq_refl; eauto. simpl in *. destruct a. simpl in *. unfold elt_eq. simpl in *. unfold pc_comp. simpl in *. unfold is_left. simpl in *. destruct ( decide (p = i)). simpl in *. rewrite eq_refl.
eauto. simpl in *. unfold elt_eq. simpl in *. unfold pc_comp. unfold is_left.  destruct ( decide (p = i)); subst. contradiction n; eauto. rewrite IHm. eauto. Qed. Hint Rewrite set2.

    
  Lemma rleaf : forall (A : Type) (i : pc), remove i (nil : t A) = nil.
Proof. intros. simpl in *. eauto. Qed. Hint Rewrite rleaf.  Hint Resolve rleaf.

  Theorem grs:
    forall (A: Type) (i: pc) (m: t A), get i (remove i m) = None.
Proof.
  intros. simpl in *. induction m.
  +simpl in *. eauto.
  +simpl in *. destruct a. simpl in *. unfold elt_eq. unfold pc_comp. unfold is_left. destruct (decide (p = i)). eauto.  simpl in *. unfold elt_eq. unfold pc_comp. unfold is_left. destruct (decide (p = i)); subst. contradiction n. eauto. eauto. Qed.
  Hint Resolve grs.
  Theorem gro:
    forall (A: Type) (i j: pc) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof. 
    intros.  induction m; simpl in *; eauto. destruct a. unfold elt_eq. unfold pc_comp. unfold is_left. simpl in *. destruct (decide (p = j)); subst. destruct ( decide (j = i)); subst. contradiction H; eauto. eauto. simpl in *. unfold elt_eq. unfold pc_comp. unfold is_left. destruct ( decide (p = i) ); eauto. Qed.
  Hint Resolve gro.
  
  
  Theorem grspec:
    forall (A: Type) i j (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof. induction m. simpl in *. unfold elt_eq. simpl in *. unfold pc_comp. unfold is_left. simpl in *. 
destruct ( decide (i = j)); eauto. unfold elt_eq in *. unfold pc_comp in *. unfold is_left in *. simpl in *. destruct a. simpl in *. unfold elt_eq. unfold pc_comp in *. unfold is_left in *. destruct (decide (p = j)); simpl in *; subst; eauto.
destruct ( decide (i = j)); subst; eauto. destruct ( decide (j = i) ); subst; eauto. contradiction n; eauto. unfold elt_eq. unfold pc_comp in *. unfold is_left in *. destruct ( decide (p = i)); subst; eauto. destruct ( decide (i = j)); simpl in *; subst; eauto. contradiction n. eauto. Qed. Hint Resolve grspec.




  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.
    Print t.

    Definition single_empty (a : (pc * option A)) :=
      match a with
      | (_, Some _) => false
      | _ => true
      end.

    
    Fixpoint bempty (m: t A) : bool :=
      match m with
      | nil => true
      | hd :: tl => single_empty hd && bempty tl
      end.

      Definition single_eq (a b : (pc * option A)) :=
      match a, b with
      | (pc1, Some op1), (pc2, Some op2) => elt_eq pc1 pc2 && beqA op1 op2
      | (pc1, None), (pc2, None) => elt_eq pc1 pc2
      | _, _ => false
      end.

        
    Fixpoint beq (m1 m2: t A) {struct m1} : bool :=
      match m1, m2 with
      | nil, nil => true
      | hd1::tl1, hd2::tl2  => single_eq hd1 hd2 && beq tl1 tl2
      | _, _ => false
                  
      end.

    Lemma bempty_correct:
      forall m, bempty m = true <-> (forall x, get x m = None).
    Proof. intros; split; intros.
           +induction m. simpl in *. auto. simpl in *. destruct a. simpl in *. unfold elt_eq.  
            unfold pc_comp in *. unfold is_left. destruct ( decide (p = x)). subst. destruct o. simpl in *. inversion H. eauto. simpl in *. destruct o. simpl in *. inversion H. simpl in *. apply IHm in H. eauto.

            +induction m. simpl in *. auto. simpl in *. destruct a. simpl in *. specialize (H p). rewrite eq_refl in H. destruct o. simpl in *. inversion H. simpl in *. apply IHm. simpl in *. intros. Admitted.
  
    Lemma beq_correct:
      forall m1 m2,
      beq m1 m2 = true <->
      (forall (x: elt),
       match get x m1, get x m2 with
       | None, None => True
       | Some y1, Some y2 => beqA y1 y2 = true
       | _, _ => False
       end).
    Proof. Admitted.







           
  End BOOLEAN_EQUALITY.
(*
  Fixpoint prev_append (i j: pc) {struct i} : positive :=
    match i with
      | xH => j
      | xI i' => prev_append i' (xI j)
      | xO i' => prev_append i' (xO j)
    end.

  Definition prev (i: positive) : positive :=
    prev_append i xH.

  Lemma prev_append_prev i j:
    prev (prev_append i j) = prev_append j i.
Proof.

  Lemma prev_involutive i :
    prev (prev i) = i.
  Proof (prev_append_prev i xH).

  Lemma prev_append_inj i j j' :
    prev_append i j = prev_append i j' -> j = j'.
Proof.
 *)
  (*
    Fixpoint xmap (A B : Type) (f : pc -> A -> B) (m : t A) (i : positive)
             {struct m} : t B :=
      match m with
      | nil => nil
      | cons hd tl => cons (f (fst hd) (snd hd)) xmap f tl end.


      l o r => Node (xmap f l (xO i))
                           (match o with None => None | Some x => Some (f (prev i) x) end)
                           (xmap f r (xI i))
      end.

  Definition map (A B : Type) (f : positive -> A -> B) m := xmap f m xH.

    Lemma xgmap:
      forall (A B: Type) (f: positive -> A -> B) (i j : positive) (m: t A),
      get i (xmap f m j) = option_map (f (prev (prev_append i j))) (get i m).
Proof.

  Theorem gmap:
    forall (A B: Type) (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
Proof.
   *)

  Print t.

  Print option_map.


  Print t.

  
  Definition map1_single A B (f : A -> B) (item:(pc * option A)) : (pc*option B):=
    match item with
      | (first, second) => (first, option_map f second)
    end. Print t.
  Fixpoint map1 (A B: Type) (f: A -> B) (m: t A) {struct m} : t B :=
    match m with
    | nil => nil
    | hd :: tl => (map1_single f hd) :: (map1 f tl)
    end.
(*
  Theorem gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
Proof.

  Definition Node' (A: Type) (l: t A) (x: option A) (r: t A): t A :=
    match l, x, r with
    | Leaf, None, Leaf => Leaf
    | _, _, _ => Node l x r
    end.

  Lemma gnode':
    forall (A: Type) (l r: t A) (x: option A) (i: positive),
    get i (Node' l x r) = get i (Node l x r).
Proof.

  Fixpoint filter1 (A: Type) (pred: A -> bool) (m: t A) {struct m} : t A :=
    match m with
    | Leaf => Leaf
    | Node l o r =>
        let o' := match o with None => None | Some x => if pred x then o else None end in
        Node' (filter1 pred l) o' (filter1 pred r)
    end.

  Theorem gfilter1:
    forall (A: Type) (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
Proof.
   *)
  (*
  Section COMBINE.

  Variables A B C: Type.
  Variable f: option A -> option B -> option C.
  Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : t A) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)
      end.

  Lemma xgcombine_l :
          forall (m: t A) (i : positive),
          get i (xcombine_l m) = f (get i m) None.
Proof.

  Fixpoint xcombine_r (m : t B) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: t B) (i : positive),
          get i (xcombine_r m) = f None (get i m).
Proof.

  Fixpoint combine (m1: t A) (m2: t B) {struct m1} : t C :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
        end
    end.

  Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
Proof.

  End COMBINE.

  Lemma xcombine_lr :
    forall (A B: Type) (f g : option A -> option A -> option B) (m : t A),
    (forall (i j : option A), f i j = g j i) ->
    xcombine_l f m = xcombine_r g m.
Proof.

  Theorem combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
Proof.

    Fixpoint xelements (A : Type) (m : t A) (i : positive)
                       (k: list (positive * A)) {struct m}
                       : list (positive * A) :=
      match m with
      | Leaf => k
      | Node l None r =>
          xelements l (xO i) (xelements r (xI i) k)
      | Node l (Some x) r =>
          xelements l (xO i)
            ((prev i, x) :: xelements r (xI i) k)
      end.

  Definition elements (A: Type) (m : t A) := xelements m xH nil.

  Remark xelements_append:
    forall A (m: t A) i k1 k2,
    xelements m i (k1 ++ k2) = xelements m i k1 ++ k2.
Proof.

  Remark xelements_leaf:
    forall A i, xelements (@Leaf A) i nil = nil.
Proof.

  Remark xelements_node:
    forall A (m1: t A) o (m2: t A) i,
    xelements (Node m1 o m2) i nil =
       xelements m1 (xO i) nil
    ++ match o with None => nil | Some v => (prev i, v) :: nil end
    ++ xelements m2 (xI i) nil.
Proof.

    Lemma xelements_incl:
      forall (A: Type) (m: t A) (i : positive) k x,
      In x k -> In x (xelements m i k).
Proof.

    Lemma xelements_correct:
      forall (A: Type) (m: t A) (i j : positive) (v: A) k,
      get i m = Some v -> In (prev (prev_append i j), v) (xelements m j k).
Proof.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
Proof.

  Lemma in_xelements:
    forall (A: Type) (m: t A) (i k: positive) (v: A) ,
    In (k, v) (xelements m i nil) ->
    exists j, k = prev (prev_append j i) /\ get j m = Some v.
Proof.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
Proof.

  Definition xkeys (A: Type) (m: t A) (i: positive) :=
    List.map (@fst positive A) (xelements m i nil).

  Remark xkeys_leaf:
    forall A i, xkeys (@Leaf A) i = nil.
Proof.

  Remark xkeys_node:
    forall A (m1: t A) o (m2: t A) i,
    xkeys (Node m1 o m2) i =
       xkeys m1 (xO i)
    ++ match o with None => nil | Some v => prev i :: nil end
    ++ xkeys m2 (xI i).
Proof.

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k: positive),
    In k (xkeys m i) ->
    (exists j, k = prev (prev_append j i)).
Proof.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: positive),
    list_norepet (xkeys m i).
Proof.

  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
Proof.

  Remark xelements_empty:
    forall (A: Type) (m: t A) i, (forall i, get i m = None) -> xelements m i nil = nil.
Proof.

  Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i, option_rel R (get i m) (get i n)) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
Proof.

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
Proof.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
Proof.

  Lemma xelements_remove:
    forall (A: Type) v (m: t A) i j,
    get i m = Some v ->
    exists l1 l2,
    xelements m j nil = l1 ++ (prev (prev_append i j), v) :: l2
    /\ xelements (remove i m) j nil = l1 ++ l2.
Proof.

  Theorem elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.
Proof.

  Fixpoint xfold (A B: Type) (f: B -> positive -> A -> B)
                 (i: positive) (m: t A) (v: B) {struct m} : B :=
    match m with
    | Leaf => v
    | Node l None r =>
        let v1 := xfold f (xO i) l v in
        xfold f (xI i) r v1
    | Node l (Some x) r =>
        let v1 := xfold f (xO i) l v in
        let v2 := f v1 (prev i) x in
        xfold f (xI i) r v2
    end.

  Definition fold (A B : Type) (f: B -> positive -> A -> B) (m: t A) (v: B) :=
    xfold f xH m v.

  Lemma xfold_xelements:
    forall (A B: Type) (f: B -> positive -> A -> B) m i v l,
    List.fold_left (fun a p => f a (fst p) (snd p)) l (xfold f i m v) =
    List.fold_left (fun a p => f a (fst p) (snd p)) (xelements m i l) v.
Proof.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
Proof.

  Fixpoint fold1 (A B: Type) (f: B -> A -> B) (m: t A) (v: B) {struct m} : B :=
    match m with
    | Leaf => v
    | Node l None r =>
        let v1 := fold1 f l v in
        fold1 f r v1
    | Node l (Some x) r =>
        let v1 := fold1 f l v in
        let v2 := f v1 x in
        fold1 f r v2
    end.

  Lemma fold1_xelements:
    forall (A B: Type) (f: B -> A -> B) m i v l,
    List.fold_left (fun a p => f a (snd p)) l (fold1 f m v) =
    List.fold_left (fun a p => f a (snd p)) (xelements m i l) v.
Proof.

  Theorem fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
Proof.
*)
End PList.


Module PMap.
  Definition elt := pc.
  Definition pc_comp (A B:pc) : bool := decide (A = B).

  Definition elt_eq := pc_comp.

  Definition t (A : Type) : Type := (A * PList.t A)%type.

  Definition init (A : Type) (x : A) :=
    (x, PList.empty A).

  Definition get (A : Type) (i : pc) (m : t A) :=
    match PList.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : pc) (x : A) (m : t A) :=
    (fst m, PList.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: pc) (x: A), get A i (init A x) = x.
Proof.
  intros. unfold init. simpl in *. unfold get. simpl in *. eauto. Qed.
Hint Resolve gi.
  Theorem gss:
    forall (A: Type) (i: pc) (x: A) (m: t A), get A i (set A i x m) = x.
Proof.
  intros. induction m. simpl in *. unfold set. simpl in *. unfold get. simpl in *. SearchAbout PList.get.
rewrite PList.gss. eauto. Qed.


            
  Theorem gso:
    forall (A: Type) (i j: pc) (x: A) (m: t A),
    i <> j -> get A i (set A j x m) = get A i m.
Proof. intros. induction m. simpl in *. simpl in *. unfold set. simpl in *. unfold get. simpl in *. remember ( PList.get i (PList.set j x b) ). eapply PList.gso in H. rewrite <- Heqo in H. clear Heqo. rewrite H. auto. Qed.
  
  Theorem gsspec:
    forall (A: Type) (i j: pc) (x: A) (m: t A),
    get A i (set A j x m) = if elt_eq i j then x else get A i m.
Proof.
intros. unfold get, set. simpl in *. Admitted.



  
  Theorem gsident:
    forall (A: Type) (i j: pc) (m: t A),
    get A j (set A i (get A i m) m) = get A j m.
Proof.
  Proof. intros.
  Admitted.

  
  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m),PList.map1 f (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: pc) (m: t A),
    get B i (map A B f m) = f(get A i m).
Proof.
  intros. induction m; simpl in *. unfold map. simpl in *. unfold get. simpl in *. Admitted.


Print elt.

  
  Theorem set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set A i y (set A i x m) = set A i y m.
Proof.
Admitted.
End PMap.




Notation "a ! b" := (PList.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).



Module Type SEMILATTICE.

  Parameter t: Type.
  Parameter eq: t -> t -> Prop.
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Parameter beq: t -> t -> bool.
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.
  Parameter ge: t -> t -> Prop.
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Parameter bot: t.
  Axiom ge_bot: forall x, ge x bot.
  Parameter lub: t -> t -> t.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End SEMILATTICE.


Module Type DATAFLOW_SOLVER.

  Declare Module L: SEMILATTICE.

  Parameter fixpoint:
    forall {A: Type} (code: PList.t A) (successors: A -> list pc)
           (transf: pc -> L.t -> L.t)
           (ep: pc) (ev: L.t),
    option (PMap.t L.t).
Print PList.get.
Print SEMILATTICE.


Print state.


Module Type NODE_SET.

  Parameter t: Type.
  Parameter empty: t.
  Parameter add: pc -> t -> t.
  Parameter pick: t -> option (pc * t).
  Parameter all_nodes: forall {A: Type}, PList.t A -> t.

  Parameter In: pc -> t -> Prop.
  Axiom empty_spec:
    forall n, ~In n empty.
  Axiom add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Axiom pick_none:
    forall s n, pick s = None -> ~In n s.
  Axiom pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Axiom all_nodes_spec:
    forall A (code: PList.t A) n instr,
    code!n = Some instr -> In n (all_nodes code).

End NODE_SET.




Module Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET)  := LAT.


Section Kildall.

Context {A: Type}.
Variable code: PList.t A.
Variable successors: A -> list pc.
Variable transf: pc -> L.t -> L.t.



Record state : Type :=
  mkstate { aval: PList.t L.t; worklist: list A; visited: positive -> Prop }.

Definition abstr_value (n: pc) (s: state) : L.t :=
  match s.(aval)!n with
  | None => L.bot
  | Some v => v
  end.

(*
Definition propagate_succ (s: state) (out: L.t) (n: positive) :=
  match s.(aval)!n with
  | None =>
      {| aval := PTree.set n out s.(aval);
         worklist := NS.add n s.(worklist);
         visited := fun p => p = n \/ s.(visited) p |}
  | Some oldl =>
      let newl := L.lub oldl out in
      if L.beq oldl newl
      then s
      else {| aval := PTree.set n newl s.(aval);
              worklist := NS.add n s.(worklist);
              visited := fun p => p = n \/ s.(visited) p |}
  end.

propagate_succ_list corresponds, in the pseudocode, to the for loop iterating over all successors.

Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list positive)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

step corresponds to the body of the outer while loop in the pseudocode.

Definition step (s: state) : PMap.t L.t + state :=
  match NS.pick s.(worklist) with
  | None =>
      inl _ (L.bot, s.(aval))
  | Some(n, rem) =>
      match code!n with
      | None =>
          inr _ {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
      | Some instr =>
          inr _ (propagate_succ_list
                  {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
                  (transf n (abstr_value n s))
                  (successors instr))
      end
  end.

The whole fixpoint computation is the iteration of step from an initial state.

Definition fixpoint_from (start: state) : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start.
 *)



(*Definition start_state (enode: positive) (eval: L.t) :=
  {| aval := PTree.set enode eval (PTree.empty L.t);
     worklist := NS.add enode NS.empty;
     visited := fun n => n = enode |}.

Definition fixpoint (enode: positive) (eval: L.t) :=
  fixpoint_from (start_state enode eval).
 *)



(*Record good_state (st: state) : Prop := {
  gs_stable: forall n,
    st.(visited) n ->
    NS.In n st.(worklist) \/
    (forall i s,
     code!n = Some i -> In s (successors i) ->
     optge st.(aval)!s (Some (transf n (abstr_value n st))));
  gs_defined: forall n v,
    st.(aval)!n = Some v -> st.(visited) n
}.

 *)
(*

Lemma step_state_good:
  forall st pc rem instr,
  NS.pick st.(worklist) = Some (pc, rem) ->
  code!pc = Some instr ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(aval) rem st.(visited))
                                  (transf pc (abstr_value pc st))
                                  (successors instr)).
Proof.
 *)


(*Lemma step_state_good_2:
  forall st pc rem,
  good_state st ->
  NS.pick (worklist st) = Some (pc, rem) ->
  code!pc = None ->
  good_state (mkstate st.(aval) rem st.(visited)).
Proof.

Lemma steps_state_good:
  forall st1 st2, steps st1 st2 -> good_state st1 -> good_state st2.
Proof.
 *)

(*Lemma start_state_good:
  forall enode eval, good_state (start_state enode eval).
Proof.
  intros. unfold start_state; constructor; simpl; intros.
- subst n. rewrite NS.add_spec; auto.
- rewrite PTree.gsspec in H. rewrite PTree.gempty in H.
  destruct (peq n enode). auto. discriminate.
Qed.

Lemma start_state_nodeset_good:
  forall enodes, good_state (start_state_nodeset enodes).
Proof.
  intros. unfold start_state_nodeset; constructor; simpl; intros.
- left. auto.
- rewrite PTree.gempty in H. congruence.
Qed.

Lemma start_state_allnodes_good:
  good_state start_state_allnodes.
Proof.
  unfold start_state_allnodes; constructor; simpl; intros.
- destruct H as [instr CODE]. left. eapply NS.all_nodes_spec; eauto.
- rewrite PTree.gempty in H. congruence.
Qed.
*)*)