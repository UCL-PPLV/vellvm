From Paco
Require Import paco.

Require Import Ascii String Bool.
Require Import Coq.Strings.String.
Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
(*Defining an instruction id as a nat*)





Definition instr_id := nat.
Definition block_id := nat.

Inductive exp : Type :=
| AIdent : instr_id -> exp
| ANum : nat -> exp
| APlus : exp -> exp -> exp
| ANone : exp
.


Inductive terminator : Type :=
| br_2 (i:instr_id) (b1 b2:block_id)
| br (b:block_id)
| term (i:instr_id)
.



Definition pc : Set := (block_id * instr_id).
Definition blk_id_of (p:pc) := fst p.
Definition instr_id_of (p:pc) := snd p.

Definition env := list (instr_id * exp).


Record state := mkState {e : env; p : pc}.



Record block := mkBlock {blk_id : block_id;  blk_code : list (instr_id*exp); blk_term : (instr_id*terminator)}.



Record cfg := mkCFG {init: block_id; blk_instrs : list block}.



Fixpoint get_env (s:env) (i:instr_id) : option exp :=
  match s with
  | nil => None
  | (iis, ins)::tl => if beq_nat iis i then Some ins else get_env tl i
  end.

Definition add_env (s:env) (i:instr_id) (v:exp) := (i, v) :: s.


Inductive cmd :=
| Term (i:terminator)
| Step_cmd (e:exp)
.



Definition blk_term_id (b:block) := fst (blk_term b).
Definition blk_term_instr (b:block) := snd (blk_term b).
Definition get_blk_id (b:block) :=  (blk_id b).


Fixpoint get_block (l:list block) (i:block_id) : option block :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (get_blk_id hd) i) then Some hd else get_block tl i
  end.


Definition fallthrough (cd:list (instr_id*exp)) (t:instr_id) :=
  match cd with
  | nil => t
  | hd :: _ => fst hd
  end.


Definition block_entry (b:block) := fallthrough (blk_code b) (blk_term_id b).

                                      
Fixpoint find_instr (l:list (instr_id * exp)) (i t:nat)  :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (fst hd) i) then Some (Step_cmd (snd hd), Some (fallthrough tl t)) else find_instr tl i t
  end.


Definition block_to_cmd (b:block) (i:instr_id) : option (cmd * option instr_id) :=
  if beq_nat (blk_term_id b) i then Some (Term (blk_term_instr b), None) else find_instr (blk_code b) i (blk_term_id b).


Print pc.
Definition fetch (l:cfg) (p:pc) :=
  match get_block (blk_instrs l) (blk_id_of p) with
  | None => None
  | Some b => match block_to_cmd b (instr_id_of p) with
              | None => None
              | Some (a, _) => Some a
              end
  end.



Definition incr_pc (l:cfg) (p:pc) : option pc :=
  match get_block (blk_instrs l) (blk_id_of p) with
  | None => None
  | Some b => match block_to_cmd b (instr_id_of p) with
              | Some (_, Some a) => Some (get_blk_id b, a)
              | _ => None
              end
  end.
Print incr_pc.





Definition get_block_entry_pc (c:cfg) (bid:block_id) : option pc :=
  match get_block (blk_instrs c) bid with
  | None => None
  | Some b => Some (bid, block_entry b)
  end.


(******** OPERATIONAL SEMANTICS ********)



Inductive Event :=
| Fin : exp -> Event
| Err : Event
.


Inductive transition X :=
| Step (s:X)
| Obs (m:Event)
.

Fixpoint eval_exp (i:exp) (s:env) : option exp :=
  match i with
  | ANone => Some ANone
  | AIdent a =>  (get_env s a) 
  | ANum a =>  Some (ANum a)
  | APlus a b => match (eval_exp a s), (eval_exp b s) with
                 | (Some (ANum a1)), (Some (ANum b1)) => Some (ANum (a1 + b1))
                 | _, _ => None
                 end
  end
.

Print pc.
Print env. Print state. Print get_block_entry_pc.
Print eval_exp.
Definition eval_term (c:cfg) (t:terminator) (s:env) :=
  match t with
  | br_2 id br1 br2 => match (eval_exp (AIdent id) s) with
                             | Some (ANum 1) =>  match get_block_entry_pc c br1 with
                                          | None => Obs state Err
                                          | Some a => Step state (mkState s a)
                                                 end
                             | Some _ =>  match get_block_entry_pc c br2 with
                                          | None => Obs state Err
                                          | Some a => Step state (mkState s a)
                                          end
                             | None => Obs state Err
                                         
                       end
                         
  | br id => match get_block_entry_pc c id with
             | None => Obs state Err
             | Some a => Step state (mkState s a)
             end
  | term a => match get_env s a with
              | None => Obs state Err
              | Some a => Obs state (Fin a)
              end
  end.
Print fetch.
Print cmd.
Print state. Print add_env. Print pc.
Definition StepD (c:cfg) (s:state) : transition state :=
  let (e, pc) := s in
  match fetch c pc with
  | Some (Step_cmd ins) => match incr_pc c pc with
                           | None => Obs state Err
                           | Some next_pc => match (eval_exp ins e) with
                                             | Some a => Step state (mkState (add_env e (snd pc) a) next_pc)
                                             | None => Obs state Err
                                             end
                           end
                             
                             
  | Some (Term a) => eval_term c a e
  | _ => Obs state Err
  end.


CoInductive Trace X :=
| Vis (v : Event)
| Tau (s:X) (k : Trace X)
.



CoFixpoint sem (c:cfg) (s:state) : Trace state :=
  match StepD c s with
  | Step _ s' => Tau state s (sem c s')
  | Obs _ Err => Vis state Err
  | Obs _ (Fin s) => Vis state (Fin s)                
  end.


  Inductive related_event_step : Event -> Event -> Prop :=
  | related_event_fin :
      forall v1 v2
        (Hv: v1 = v2),
        related_event_step (Fin v1) (Fin v2)
  | related_event_err :
      related_event_step (Err) (Err).


  Section OBSERVATIONAL_EQUIVALENCE. 
  Variable X : Type.
  Variable R : Trace X -> Trace X -> Prop.

  Inductive trace_equiv_step : Trace X -> Trace X -> Prop :=
  | trace_equiv_step_vis :
      forall e1 e2
        (HRe : related_event_step e1 e2),
        trace_equiv_step (Vis X e1) (Vis X e2)
  | trace_equiv_step_tau :
      forall x1 x2 k1 k2
        (HRk : R k1 k2),
        trace_equiv_step (Tau X x1 k1) (Tau X x2 k2)
  | trace_equiv_step_lft :
      forall x1 k1 k2
        (IH : trace_equiv_step k1 k2),
        trace_equiv_step (Tau X x1 k1) k2
  | trace_equiv_step_rgt :
      forall x2 k1 k2
        (IH : trace_equiv_step k1 k2),
        trace_equiv_step k1 (Tau X x2 k2)
  .

  Hint Constructors trace_equiv_step.

  End OBSERVATIONAL_EQUIVALENCE.

  Lemma related_event_step_monotone : forall X (R1 R2:X -> X -> Prop)
                                        (HR: forall d1 d2, R1 d1 d2 -> R2 d1 d2) m1 m2
                                        (HM:related_event_step m1 m2),
    related_event_step m1 m2.
Proof. auto. Qed.
Hint Resolve related_event_step_monotone : paco.  


  Lemma trace_equiv_step_monotone : forall {X}, monotone2 (@trace_equiv_step X).
  Proof. intros. unfold monotone2. intros.  induction IN. constructor. apply HRe.
         constructor. apply LE. apply HRk.  constructor.  eauto.  constructor.  auto. Qed.
  Hint Resolve related_event_step_monotone : paco.


  Definition trace_equiv {X} (p q: Trace X) := paco2 (@trace_equiv_step X) bot2 p q.
  Hint Unfold trace_equiv.







(*static analysis*)


Definition areg : Set := (instr_id * exp).
Definition aenv : Set := list areg.

Print cfg.
Print cmd.
Definition map_exp_to_cmd (e:instr_id * exp) : (instr_id * cmd) := (fst e, Step_cmd (snd e)).
Print map_exp_to_cmd.

Print terminator.
Print exp.

Definition map_term_to_cmd (t: (instr_id*terminator)) : list (instr_id * cmd) := cons (fst t, Term (snd t)) nil.









  
Print block.
Definition prep_block (b:block) := map map_exp_to_cmd (blk_code b) ++ map_term_to_cmd (blk_term b).


Definition aenv_fallthrough (l:aenv) :=
  match l with
  | nil => None
  | hd::tl => Some (fst hd)
  end.


Fixpoint list_to_tuple (l: aenv) (t:nat)  :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (fst hd) t) then Some (snd hd, aenv_fallthrough tl) else list_to_tuple tl t
  end.




Definition find_tuple (l:aenv) (i:nat) :=
  match list_to_tuple l i with
  | Some (t, _) => Some t
  | _ => None
  end.


Definition increase_tuple (l:aenv) (i:nat) :=
  match list_to_tuple l i with
  | Some (_, Some a) => Some a
  | _ => None
  end.


Fixpoint get_from_aenv (l:aenv)  (i:nat) :=
  match l with
  | nil => None
  | (iis, ins) :: tl => if beq_nat iis i then Some (ins) else get_from_aenv tl i
  end.

Print eval_exp.


Definition transfer (a:aenv) (i:instr_id * cmd) : aenv :=
  match snd i with
  | Term t =>  a
  | Step_cmd (ANum t) => (fst i, (ANum t)) :: a
  | Step_cmd (APlus t t1) => match eval_exp (APlus t t1) a with
                             | Some (ANum res) => (fst i, (ANum res)) :: a
                             | _ =>  a
                             end
                               

  | Step_cmd (AIdent t) => match (get_from_aenv a t) with
                             
                           | Some b  => (fst i, b) :: a
                           | None => a
                           end
  | Step_cmd ANone => (fst i, ANone) :: a
  end.




Fixpoint value_analysis_fix (acc:aenv) l (i:nat)  :=
  match l with
  | nil => nil
  | hd :: tl => if beq_nat (fst hd) i then acc else (value_analysis_fix (transfer acc hd) tl i)
  end.

Print value_analysis_fix.



Definition value_analysis l (i:nat) := value_analysis_fix nil l i.


Print value_analysis.
Print pc.
Print get_block.
Print cfg.

Print prep_block.
Print aenv.
Print value_analysis.
Print value_analysis_fix.
Definition prep_selected_block (c:cfg) (p:pc) :=
  match get_block (blk_instrs c) (fst p) with
  | None => None
  | Some a => Some (prep_block a)
  end.


Print prep_selected_block.

Print value_analysis.


Definition value_analysis_specific (c:cfg) (p:pc) :=
  match prep_selected_block c p with
  | None => None
  | Some a => Some (value_analysis a (snd p))
  end.



Lemma find_tuple_implies : forall l i i1,  NoDup (map fst l) -> find_tuple l i = Some i1 ->
                            exists head tl, l = head ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple in *. induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. inversion H0. subst. exists nil; eauto. exists l. eauto.
inversion H. subst. eapply IHl in H4; eauto. simpl in *. inversion H4. subst. inversion H1. subst. simpl in *. exists ( (i0, e0) :: x ). exists x0. eauto. 
 Qed.       
Print increase_tuple.


      
Lemma incr_pc_implies : forall l i i1 t,  NoDup (map fst  l) -> list_to_tuple l i = Some (i1, Some t) ->
                            exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof. intros. unfold increase_tuple in *. simpl in *. simpl in *. induction l. simpl in *. inversion H0.
       simpl in *. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. subst. destruct l. simpl in *. inversion H3. simpl in *. inversion H3. destruct p0. simpl in *. subst. exists nil. simpl. exists l. simpl. eauto. simpl in *. inversion H. subst. eapply IHl in H4; eauto. inversion H4. subst. inversion H1. subst. inversion H2. simpl in *. subst. simpl in *. inversion H2. subst. exists ((i0, e0) :: x). simpl. exists x0. exists x1. eauto. Qed.




Definition newlist := list (instr_id * cmd).

Print fallthrough.
Definition opt_fallthrough (n:newlist) : option instr_id :=
  match n with
  | nil => None
  | hd :: _ => Some (fst hd)
  end.












  Fixpoint find_in_newlist(n:newlist)  (i:instr_id) :=
  match n with
  | nil => None
  | hd :: tl => if beq_nat (fst hd) i then Some (snd hd, opt_fallthrough tl) else find_in_newlist tl i
  end.

  Print value_analysis.

  Lemma incr_pc_implies2 : forall prog i i1 t,  NoDup (map fst (prep_block prog)) ->  block_to_cmd prog i =  Some (i1, Some t) ->  find_in_newlist (prep_block prog) i = Some (i1, Some t).

  Proof. intros. unfold block_to_cmd in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *.
         destruct blk_term0. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. eapply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. simpl in *. induction blk_code0. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i2 i). destruct b. eapply beq_nat_eq in Heqb0. subst. simpl in *. inversion H0. subst. simpl in *. destruct blk_code0.  simpl in *.

 eauto. simpl in *. eauto.
 eapply IHblk_code0; eauto. inversion H; subst; eauto. Qed.







Lemma map_prog : forall prog_code0, ((map fst (map map_exp_to_cmd prog_code0)) = (map fst prog_code0)).
Proof. induction prog_code0; simpl in *; eauto.
       inversion IHprog_code0. auto. Qed.

Print block.
                                                                                                                    
Lemma get_prog_id : forall prog, NoDup ((map fst (blk_code prog)) ++  (blk_term_id prog ) :: nil) ->
                                 NoDup (map fst (prep_block prog)).
Proof. intros. unfold prep_block. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *.
       induction blk_code0. simpl in *. auto. simpl in *. destruct a. simpl in *. inversion H. simpl in *. subst.  eapply IHblk_code0 in H3. subst. unfold not in H2. simpl in *. contradiction H2. simpl. Admitted.




Lemma incr_pc_implies1 : forall l i i1 t,  NoDup (map fst l) ->
                                           find_in_newlist l i = Some (i1, Some t) ->
                                          exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof. simpl in *. intros. induction l; simpl in *.
       +inversion H0.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. simpl in *. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. subst.
        *exists nil. simpl. destruct l. simpl in *. inversion H3. simpl in *. inversion H3. subst. destruct p0. simpl in *. exists l. exists c. eauto.
        *inversion H. subst. eapply IHl in H4; eauto. inversion H4. inversion H1. subst. inversion H2. subst. simpl in *. exists ( (i0, c)
    :: x). simpl in *. exists x0. exists x1. eauto. Qed.



Lemma testtest : forall l hd i i1 t r tl a,  NoDup (map fst l) -> l = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl ->   value_analysis_fix a l t =
  transfer (value_analysis_fix a l i) (i, i1).
Proof. intros. simpl in *. generalize a. simpl in *. rewrite H0. rewrite H0 in H. clear H0. induction hd. simpl in *. remember (PeanoNat.Nat.eqb i t). destruct b. apply beq_nat_eq in Heqb. subst.
inversion H. subst. contradiction H2.  simpl; eauto.
       simpl in *. rewrite PeanoNat.Nat.eqb_refl. simpl in *. rewrite PeanoNat.Nat.eqb_refl.  eauto. simpl in *. destruct a0.  simpl in *. remember ( PeanoNat.Nat.eqb n t). destruct b. apply  beq_nat_eq in Heqb. subst. clear IHhd. inversion H. subst.  clear H3. clear H. assert (In t (map fst (hd ++ (i, i1) :: (t, r) :: tl))).
       simpl in *. induction hd. simpl in *. right; left; eauto. simpl in *. right. apply IHhd. unfold not. intros. apply H2. right. auto. apply H2 in H. inversion H.


       +simpl in *. remember ( PeanoNat.Nat.eqb n i). destruct b. apply beq_nat_eq in Heqb0. subst.
        *inversion H. subst. clear IHhd. clear H3. clear H. assert (In i (map fst (hd ++ (i, i1) :: (t, r) :: tl))). induction hd. simpl in *. left. auto. simpl. right. apply IHhd. simpl in *. unfold not. intros. unfold not in H2. apply H2. right. auto. apply H2 in H. inversion H.  
        *assert ( NoDup (map fst (hd ++ (i, i1) :: (t, r) :: tl))). inversion H; subst. apply H3. intros. remember ((transfer a0 (n, c))). eapply IHhd. inversion H; subst. eapply H4. Qed.


 Lemma testtest1 : forall prog hd i i1 t r tl, NoDup (map fst  (prep_block prog)) ->  (prep_block prog) = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl  -> value_analysis  (prep_block prog) t = transfer (value_analysis  (prep_block prog) i) (i, i1).

 Proof. intros. unfold value_analysis. simpl in *. eapply testtest in H; simpl in *; eauto. Qed.


 Print block.
 
 Lemma testtest2 : forall prog i i1 t, NoDup ((map fst (blk_code prog)) ++ ( blk_term_id prog ) :: nil) -> block_to_cmd prog i =  Some (i1, Some t)  ->  value_analysis  (prep_block prog) t = transfer (value_analysis  (prep_block prog) i) (i, i1).
 Proof. intros. assert (H' := H). eapply get_prog_id in H.   assert (H'' := H).   assert (H''' := H). 
        eapply  incr_pc_implies2 in H; eauto. eapply incr_pc_implies1 in H''; eauto.
inversion H''. inversion H1. inversion H2. subst. eapply testtest in H'''; eauto. Qed.

 
Lemma test5 : forall prog i i1 t head,  NoDup ((map fst (blk_code prog)) ++ (blk_term_id prog :: nil)) ->
                                        block_to_cmd prog i = Some (t, Some i1) ->
                                        value_analysis (prep_block prog) i = head  ->
                                        value_analysis (prep_block prog) (i1) = transfer head (i, t).
Proof. intros. eapply testtest2 in H; eauto. rewrite <- H1; eauto. Qed.




(*

  Definition Subset s s' := forall a : (instr_id * exp), In a s -> In a s'.
  Print Subset.
*)
Print get_env. Print get_from_aenv. 
  Definition Subset1 (s s':aenv) := forall a b, get_from_aenv s a = Some b -> get_env s' a = Some b.

  Lemma opposite_subset : forall s' s a, Subset1 s s' -> get_env s' a = None -> get_from_aenv s a = None.
Proof. intros. Admitted.

    Lemma in_aenv_in_env : forall s' s a b, Subset1 s s' -> get_from_aenv s a = Some b -> get_env s' a = Some b.
    
  Proof. Admitted.
     Print prep_selected_block.

    Print aenv.
    Print env.
    Print areg.
Print value_analysis. Print prep_selected_block.
    Definition sound_aenv (c:cfg) (p:pc) (e:env) := forall prep, prep_selected_block c p = Some prep -> Subset1 (value_analysis prep (snd p)) e.
    Print state.
    
                               
Inductive sound_state : cfg -> state  -> Prop :=
| sound_state_intro:
    forall st c
           (env: sound_aenv c (p st) (e st)), sound_state c st.
                             
Print get_from_aenv.
Lemma get_aenv_env_equiv : get_from_aenv = get_env.
Proof. repeat (apply functional_extensionality; intros). induction x; simpl; eauto. Qed.

Print block.
Lemma testtesttest : forall b0 blk_instrs0 b, Some b0 = get_block blk_instrs0 b -> b = blk_id b0.                          
Proof.
  intros. induction blk_instrs0. simpl in *. inversion H. simpl in *. unfold get_blk_id in H. simpl in *. destruct a. simpl in *.
remember ( PeanoNat.Nat.eqb blk_id0 b). destruct b1; eauto.  eapply beq_nat_eq in Heqb1. symmetry. destruct b0. simpl in *. inversion H. subst. auto. Qed. 


Lemma value_analysis_at_entry_is_nil : forall b4,

  (value_analysis_fix nil
       (map map_exp_to_cmd (blk_code b4) ++
            map_term_to_cmd (blk_term b4)) (block_entry b4)) = nil.

Proof. intros. unfold block_entry. simpl in *. destruct b4. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term0. simpl in *. destruct blk_code0. simpl in *. rewrite PeanoNat.Nat.eqb_refl. auto. simpl in *. destruct p0. simpl in *. rewrite PeanoNat.Nat.eqb_refl. auto.
Qed.



Print get_env.
Lemma empty_list_always_subset : forall (l1:aenv), Subset1 nil l1.
Proof. unfold Subset1. simpl in *. intros. inversion H. Qed.




Lemma value_analysis_entry_nil : forall e0 b3,  Subset1 (value_analysis (prep_block b3) (block_entry b3)) e0.
Proof. intros. unfold value_analysis. unfold prep_block. simpl in *. rewrite value_analysis_at_entry_is_nil.  apply empty_list_always_subset. Qed. Hint Resolve value_analysis_entry_nil.
(*
Lemma eval_in_aenv_same : forall   Subset1 (value_analysis prep i) e0*) (* eval_exp e1_1 (value_analysis (prep_block b0) i)*)(* eval_exp e1_1 e0*)


Lemma equal_eval_aenv_env : forall i a e1_1 e0 b0, Subset1 (value_analysis (prep_block b0) i) e0 ->  eval_exp e1_1 (value_analysis (prep_block b0) i) = Some a -> eval_exp e1_1 e0 = Some a.
Proof. intros. unfold Subset1 in *. generalize dependent a.  induction e1_1. simpl in *. SearchAbout get_env.
       +intros.  rewrite <- get_aenv_env_equiv in H0. remember (get_from_aenv (value_analysis (prep_block b0) i) i0). destruct o. symmetry in Heqo. apply H in Heqo. rewrite Heqo. auto. inversion H0.
       +simpl in *. auto.
       +simpl in *. intros. remember ( eval_exp e1_1_1 (value_analysis (prep_block b0) i)).
rewrite Heqo in IHe1_1_1. destruct o. symmetry in Heqo. generalize Heqo; intros.  apply IHe1_1_1 in Heqo.
rewrite Heqo. remember ( eval_exp e1_1_2 (value_analysis (prep_block b0) i) ). rewrite Heqo1 in IHe1_1_2. destruct o. symmetry in Heqo1. apply IHe1_1_2 in Heqo1. rewrite Heqo1. auto. destruct e1. inversion H0. inversion H0. inversion H0. inversion H0. inversion H0.
       +intros. simpl in *. auto. Qed.
         


       

Lemma testtes123123 : forall e0 i e2 a b, ( get_env ((i, e2) :: e0) a = Some b) -> get_env ((i, e2) :: nil) a = Some b \/ get_env e0 a = Some b.

Proof. intro. induction e0.
       +simpl in *. intros. remember ( PeanoNat.Nat.eqb i a). destruct b0. apply beq_nat_eq in Heqb0. subst. left. auto. left. auto.

       +simpl in *. intros. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i a0). destruct b0. eapply beq_nat_eq in Heqb0. subst. inversion H. left. auto. simpl in *. right. auto. Qed.

       

Lemma step_preserves_soundness : forall p st st1,
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state p st -> StepD p st = Step state st1 -> sound_state p st1.
Proof. intros. inversion H0. subst. constructor. unfold StepD in H1. simpl in *. destruct st. simpl in *. unfold fetch in H1. unfold incr_pc in H1. simpl in *. unfold instr_id_of in *. simpl in *. unfold blk_id_of in H1. destruct p1. simpl in *.  remember ( get_block (blk_instrs p0) b). destruct o. 
                                                                                                                                                                                                                                                                                                              simpl in *. remember (block_to_cmd b0 i). destruct o. destruct p1. simpl in *. destruct c. simpl in *.
       +destruct i0.






        (*TERM BR2*)
       -simpl in *. remember (get_env e0 i0). destruct o0. simpl in *. destruct e1.
        *simpl in *. unfold get_block_entry_pc in *. simpl in *.
         remember ( get_block (blk_instrs p0) b2). destruct o0. simpl in *.
         destruct st1. simpl in *. inversion H1. subst. generalize Heqo2. intros. apply testtesttest in Heqo2. subst. simpl in *. unfold sound_aenv in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo3. simpl in *. intros. inversion H2. eauto. inversion H1.



         






         
        *simpl in *. destruct n. simpl in *.



         unfold get_block_entry_pc in *.  simpl in *. remember (get_block (blk_instrs p0) b2). destruct o0. simpl in *. generalize Heqo2. intros. apply testtesttest in Heqo3. subst. simpl in *. destruct st1. simpl in *. inversion H1. subst. simpl in *. unfold sound_aenv. simpl in *. intros. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo2 in H2. inversion H2. subst. simpl in *. auto. inversion H1.



         destruct n.


         unfold get_block_entry_pc in *. simpl in *. remember (get_block (blk_instrs p0) b1). destruct o0. simpl in *. generalize Heqo2. intros. apply testtesttest in Heqo3. subst. simpl in *. destruct st1. simpl in *. inversion H1. subst. unfold sound_aenv. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo2. intros. inversion H2. auto. inversion H1.



         unfold get_block_entry_pc in *. simpl in *. remember (get_block (blk_instrs p0) b2).
         destruct o0; inversion H1. generalize Heqo2. intros. apply testtesttest in Heqo3. subst. simpl in *. unfold sound_aenv in *. simpl in *. unfold prep_selected_block in *. simpl in *.
         rewrite <- Heqo2. intros. inversion H2. subst. auto.
        *simpl in *. unfold get_block_entry_pc in *. simpl in *.
         remember ( get_block (blk_instrs p0) b2). simpl in *.
         destruct o0. simpl in *. destruct st1. simpl in *.
         inversion H1. subst. generalize Heqo2. intros.
         apply testtesttest in Heqo3. subst. simpl in *.
         unfold sound_aenv in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo2. intros. inversion H2.  auto. inversion H1.
        *simpl in *. unfold get_block_entry_pc in *. simpl in *.
         remember ( get_block (blk_instrs p0) b2). simpl in *.
         destruct o0. simpl in *. destruct st1. simpl in *.
         inversion H1. subst. generalize (Heqo2); intros.
         apply testtesttest in Heqo2. subst. simpl in *.
         unfold sound_aenv in *. simpl in *. unfold prep_selected_block in *.
         simpl in *. intros. rewrite <- Heqo3 in H2. inversion H2. simpl in *.  auto. inversion H1.
        *inversion H1.



         
       -(*TERM BR1*)
         simpl in *. unfold get_block_entry_pc in *. simpl in *.
        remember ( get_block (blk_instrs p0) b1). simpl in *.
        destruct o0. simpl in *. destruct st1. simpl in *.
        inversion H1. subst. generalize Heqo1; intros.
        apply testtesttest in Heqo2. subst. simpl in *.
        unfold sound_aenv. simpl in *. unfold prep_selected_block in *.
        simpl in *. intros. rewrite <- Heqo1 in H2. inversion H2.
        subst. unfold prep_block. simpl in *. unfold value_analysis.
        simpl in *. rewrite  value_analysis_at_entry_is_nil. auto.
        apply  empty_list_always_subset. inversion H1.

       -(*RET*)
         simpl in *. destruct (get_env e0 i0); inversion H1.

         
       +destruct o. destruct st1. simpl in *. remember ( eval_exp e1 e0). destruct o. simpl in *. inversion H1. subst. unfold get_blk_id in *. simpl in *. destruct b0. simpl in *. unfold sound_aenv in env0. simpl in *. 
 unfold sound_aenv. simpl in *.  symmetry in Heqo0. eapply test5 in Heqo0; eauto. intros. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in env0.  unfold prep_block in *. simpl in *.  

generalize Heqo; intros. apply testtesttest in Heqo2. simpl in *. subst. rewrite <- Heqo in H2.
simpl in *. inversion H2. subst. rewrite Heqo0. simpl in *. unfold transfer. simpl in *.

destruct e1.
-simpl in *. unfold add_env. unfold Subset1. simpl in *. intros. simpl in *. remember (           get_from_aenv
             (value_analysis (map map_exp_to_cmd blk_code0 ++ map_term_to_cmd blk_term0) i) i1
                                                                                      ). simpl in *.  destruct o.  remember (PeanoNat.Nat.eqb i a). destruct b0. rewrite Heqo1. symmetry in Heqo2. simpl in *. rewrite  <- Heqb0 in H3. inversion H3. subst. specialize (env0 (map map_exp_to_cmd blk_code0 ++ map_term_to_cmd blk_term0)). apply env0 in H2. apply H2 in Heqo2. auto.
 symmetry in Heqo2.




(*


simpl in *. rewrite PeanoNat.Nat.eqb_refl in H3. auto. simpl in *.



admit. simpl in *. admit. simpl in *. admit. simpl in *. rewrite PeanoNat.Nat.eqb_refl in H3. auto. simpl in *. destruct e1. simpl in *. remember (           get_from_aenv
             (value_analysis (prep_block b0) i) i1
). destruct o. simpl in *. rewrite <- Heqb1 in H3. simpl in *. eapply H1 in H3. eauto. simpl in *. eapply H1 in H3. eauto. simpl in *. rewrite <- Heqb1 in H3. eapply H1 in H3. eauto. simpl in *.





































         rewrite H. simpl in *. unfold transfer. simpl in *. destruct e1; simpl in *; eauto.




       -rewri

         unfold add_env. simpl in *. unfold Subset1. simpl in *. intros.

         
 rewrite <- Heqo1 in Heqo2. inversion Heqo2. unfold Subset1. intros. subst. simpl in *. remember (PeanoNat.Nat.eqb i a). destruct b1. auto. apply H1. auto. unfold Subset1. simpl in *. intros. remember ( PeanoNat.Nat.eqb i a).
 destruct b1.



 admit. unfold add_env. simpl in *. unfold Subset1. simpl 


        
      -(*ANUM*)
simpl in *. unfold Subset1. simpl in *. intros. remember ( PeanoNat.Nat.eqb i a). destruct b1. simpl in *. eapply beq_nat_eq in Heqb1. subst. inversion H3. subst. clear H2. inversion Heqo1. subst. auto. apply H1. auto.
      -(*APLUS*)



        remember (      eval_exp e1_1
          (value_analysis (prep_block b0) i)). symmetry in Heqo2. destruct o. eapply equal_eval_aenv_env in Heqo2; eauto. rewrite Heqo2 in Heqo1. destruct e1. inversion Heqo1. remember (        eval_exp e1_2
          (value_analysis (prep_block b0) i)
                                                                                                                                                                                         ). destruct o.  symmetry in Heqo3; eapply equal_eval_aenv_env in Heqo3; eauto. rewrite Heqo3 in Heqo1. destruct e1. inversion Heqo1. inversion Heqo1. subst. admit. inversion Heqo1. inversion Heqo1. remember (eval_exp e1_2 e0). destruct o. destruct e1. inversion Heqo1. inversion Heqo1. subst. unfold Subset1. simpl in *. admit. inversion Heqo1. inversion Heqo1. inversion Heqo1. inversion Heqo1. inversion Heqo1. simpl in *. admit.



      -(*ANONE*)
        inversion Heqo1. admit.
       *inversion H1.
       +inversion H1.
       +inversion H1.


        Admitted.*)



Lemma step_preserves_soundness1 : forall p st st1,
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state p st -> StepD p st = Step state st1 -> sound_state p st1.
Proof. intros. destruct p0. simpl in *. 
(*
       unfold StepD in H1. destruct st, st1. simpl in *. unfold fetch in *. unfold incr_pc in *. simpl in *. unfold blk_id_of in *. destruct p0. simpl in *. remember ( get_block blk_instrs0 b). destruct o. simpl in *. inversion H0. subst. unfold sound_aenv in *. simpl in *. unfold prep_selected_block in *. simpl in *. generalize Heqo. intros. apply testtesttest in Heqo0. subst. simpl in *. constructor. unfold sound_aenv. simpl in *. unfold prep_selected_block. simpl in *. destruct p1. simpl in *. remember ( block_to_cmd b0 i). destruct o. simpl in *. destruct p0. simpl in *. destruct c. simpl in *. admit. simpl in *. destruct o. simpl in *. intros. remember ( eval_exp e2 e0). destruct o. inversion H1. subst. unfold get_blk_id in *. rewrite <- Heqo in H2. inversion H2. subst. unfold Subset1. eapply test5 in H; eauto. simpl in *. intros. remember (PeanoNat.Nat.eqb i a). destruct b1. rewrite Heqo1. eapply equal_eval_aenv_env. rewrite <- Heqo in env0. apply env0 in H2. auto. rewrite <- Heqo in env0.
       destruct e2.
       (*9*)
       -simpl in *. rewrite H in H3. simpl in *. unfold transfer in *. simpl in *. remember (get_from_aenv (value_analysis (prep_block b0) i) i1). destruct o. simpl in *. rewrite <- Heqb1 in H3. eauto. simpl in *. inversion H3. subst. symmetry. rewrite <- get_aenv_env_equiv. auto.


        
        rewrite <- H3. remember ( get_env (value_analysis (prep_block b0) i) i1). destruct o. rewrite <- get_aenv_env_equiv in Heqo3. rewrite <- Heqo2 in Heqo3. inversion Heqo3. symmetry in H3.
        apply env0 in H2. symmetry in H3. generalize H3. intros.  rewrite H4. rewrite Heqo2.

        SearchAbout 


        admit.
       -admit.
       -admit.
       -admit.



(*5*)
 -




       
rewrite <- Heqo in env0. apply env0 in H2. apply H2. rewrite H in H3. unfold transfer in H3. simpl in *. 
destruct e2. simpl in *. remember ( get_from_aenv (value_analysis (prep_block b0) i) i1). destruct o. simpl in *. rewrite <- Heqb1 in H3. eauto. simpl in *. eauto. simpl in *. rewrite <- Heqb1 in H3. auto. simpl in *. admit. simpl in *. rewrite <- Heqb1 in H3.


auto.


-inversion H1.
-inversion H1.
-inversion H1.
-inversion H1. Admitted.








       





       admit. admit. inversion H1. inversion H1. inversion H1. inversion H1.






       r*)




Admitted.





Print sound_state.

Print sound_aenv.


  Definition Subset s s' := forall a : (instr_id * exp), In a s -> In a s'.
  Print Subset.


 Definition sound_aenv1 (c:cfg) (p:pc) (e:env) := forall prep, prep_selected_block c p = Some prep -> Subset (value_analysis prep (snd p)) e.
    Print state.
    

    Lemma In_conv : forall l e1 i1, Some e1 = get_from_aenv l i1 -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i i1). destruct b. inversion H. subst. left. apply beq_nat_eq in Heqb. subst. auto. right. apply IHl. apply H. Qed.


Lemma test123 : forall (e0:aenv) i2,    (In i2 (map fst e0) -> exists e1, In (i2, e1) e0).
Proof. intro.  induction e0. simpl in *.
       +intros. inversion H.
       +simpl in *. intros. destruct a. simpl in *. inversion H; subst. esplit. left. auto.
specialize (IHe0 i2). apply IHe0 in H0. inversion H0. subst. exists x. right. auto. Qed. 




Lemma test1234: forall (e0:aenv) i2 e2 , In (i2, e2) e0 -> In i2 (map fst e0).
Proof. intro. induction e0.
       +simpl in *. intros. inversion H.
       +simpl in *. intros. inversion H. subst. simpl in *. left. auto. right. eapply IHe0.
apply H0. Qed.



        
Lemma In_conv1 : forall e0 i2 e2, NoDup (map fst e0)  -> In (i2, e2) e0
                                   ->  Some e2 = get_env e0 i2.
Proof.  intro. induction e0. simpl in *. intros. inversion H0.
        simpl in *. intros. destruct a. simpl in *. inversion H0. inversion H1. rewrite PeanoNat.Nat.eqb_refl. eauto. inversion H. subst. eapply IHe0 in H5; eauto. remember ( PeanoNat.Nat.eqb i i2). destruct b; eauto. rewrite H5. symmetry. apply IHe0. inversion H0. inversion H. auto. inversion H. auto. apply beq_nat_eq in Heqb. subst. unfold not in H4. simpl in *.

        assert     (In i2 (map fst e0) -> In (i2, e1) e0).
intros. simpl in *. induction e0. simpl in *. auto. 
apply H4 in H2. inversion H2. simpl in *. apply test1234 in H1. apply H4 in H1. inversion H1. Qed.

Lemma convert_aenv_env : forall b1 i0 i2 e0 e2,
NoDup (map fst e0) -> 
 Subset (value_analysis (prep_block b1) i0) e0  ->
 Some e2 = get_from_aenv (value_analysis (prep_block b1) i0) i2 ->
 Some e2 = get_env e0 i2.
Proof. intros. unfold Subset in H0. simpl in *. apply In_conv1; eauto.
 apply In_conv in H1. apply H0. auto. Qed.





Print equal_eval_aenv_env.



Lemma equal_eval_aenv_env1 : forall i a e1_1 e0 b0, Subset (value_analysis (prep_block b0) i) e0 ->  eval_exp e1_1 (value_analysis (prep_block b0) i) = Some a -> eval_exp e1_1 e0 = Some a.
Proof. intros. unfold Subset in *. generalize dependent e0. generalize dependent a. generalize dependent b0.
       induction e1_1; simpl in *; intros; eauto. Admitted.




       
    
 Inductive sound_state1 : cfg -> state -> Prop :=
    sound_state_intro1 : forall (st : state) (c : cfg) (saenv: sound_aenv1 c (p st) (e st)) (uid: NoDup (map fst (e st))), sound_state1 c st.

 Print In.


Lemma step_preserves_soundness2 : forall prog st st1,
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state1 prog st  -> StepD prog st = Step state st1 -> sound_state1 prog st1.
Proof. intros.  destruct st, st1. constructor.  inversion H0. subst. unfold sound_aenv1 in *. simpl in *. unfold prep_selected_block. simpl in *. destruct p1. simpl in *. unfold fetch in *. unfold incr_pc in *. simpl in *. unfold blk_id_of in *. simpl in *. destruct p0. simpl in *. remember ( get_block (blk_instrs prog) b0). destruct o. simpl in *. remember (block_to_cmd b1 i0). destruct o. simpl in *. destruct p0. simpl in *. destruct c. simpl in *.

       (*TERM*)
       +destruct i1.
        *(*BR2*) admit.
        *(*BR*) simpl in *. unfold get_block_entry_pc in *. destruct ( get_block (blk_instrs prog) b2).
       -simpl in *. inversion H1. admit.
       -inversion H1.
        *(*TERM*) simpl in *. destruct ( get_env e0 i1); inversion H1.
       +destruct o.
        (*STEP*)
       -destruct e2; simpl in *.
        *(*AIDENT*) remember ( get_env e0 i2). destruct o. inversion H1. subst. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in saenv. intros. generalize Heqo; intros. apply testtesttest in Heqo2. subst. unfold get_blk_id in *. simpl in *. rewrite <- Heqo in H2. inversion H2. subst. unfold add_env. simpl in *. eapply test5 in H; eauto. rewrite H. unfold transfer. simpl in *. simpl in *. remember ( get_from_aenv (value_analysis (prep_block b1) i0) i2). destruct o. specialize (saenv (prep_block b1)). assert (
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Some (prep_block b1) = Some (prep_block b1)) by auto. apply saenv in H3.  eapply convert_aenv_env in H3; eauto. rewrite <- H3 in Heqo1.  inversion Heqo1. subst. unfold Subset. simpl in . intros. simpl in *. inversion H4; subst; eauto. right.  apply saenv in H2. apply H2. auto. simpl in *. apply saenv in H2. generalize H2; intros. generalize H2; intros. 
         unfold Subset. simpl in *. intros. right. apply H3. auto. simpl in *. inversion H1. 
        *(*ANUM*) inversion H1. subst. unfold add_env. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in
             saenv. unfold get_blk_id in *. simpl in *. generalize Heqo; intros. apply testtesttest in Heqo1. subst. rewrite <- Heqo in H2. inversion H2. subst. apply saenv in H2; eauto. unfold Subset in *. simpl in *. simpl in *. intros. specialize (H2 a). simpl in *. eapply test5 in H; eauto. simpl in *. rewrite H in H3. simpl in *. clear H. inversion H3. subst. left. auto. right. apply H2. eauto.
        *(*APLUS*) remember (eval_exp e2_1 e0). remember (eval_exp e2_2 e0). 
         {

           +destruct o.
           -unfold prep_selected_block in *. simpl in *. destruct e2. inversion H1. destruct o0. destruct e2. inversion H1. inversion H1. subst. unfold get_blk_id in *. simpl in *. generalize Heqo. intros. apply testtesttest in Heqo3. subst. simpl in *. rewrite <- Heqo in H2. inversion H2. subst. rewrite <- Heqo in saenv. eapply test5 in H; eauto. rewrite H. unfold transfer. simpl in *. unfold Subset. simpl in *. intros. apply saenv in H2. remember (             eval_exp e2_1
               (value_analysis (prep_block b1) i0)). destruct o. symmetry in Heqo3. generalize H2; intros.  eapply equal_eval_aenv_env1 in H2; eauto. rewrite H2 in Heqo1. inversion Heqo1. rewrite <- H6 in H3. remember (             eval_exp e2_2
               (value_analysis (prep_block b1) i0)
                                                                                                                                                                                                                          ). destruct o. symmetry in Heqo4. generalize H4; intros. eapply equal_eval_aenv_env1 in H4; eauto. rewrite H4 in Heqo2. inversion Heqo2. subst. simpl in *. inversion H3. subst. left. auto. right. apply H5. auto. right. apply H4. auto. simpl in *. right. apply H2. auto.
            inversion H1. inversion H1. inversion H1. inversion H1. inversion H1.
           -inversion H1.
          
          }
           


          
        *(*ANONE*) inversion H1. subst. unfold add_env. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in saenv. unfold get_blk_id in *. simpl in *. generalize Heqo. intros. apply testtesttest in Heqo1. subst. rewrite <- Heqo in H2.
inversion H2. subst. apply saenv in H2; eauto. unfold Subset in *. simpl in *.  intros. specialize (H2 a). simpl in *. eapply test5 in H; eauto.
 rewrite H in H3. simpl in *. clear H. inversion H3. subst. left. auto. right. apply H2. auto.
       -inversion H1.
        +inversion H1.
        +inversion H1.
+admit.
Admitted.

Print cfg. Print value_analysis.
