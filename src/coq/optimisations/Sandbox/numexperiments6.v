From Paco
Require Import paco.

Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.FunctionalExtensionality.

Definition ident := nat.
Definition instr_id := nat.

Inductive value :=
| Num (n:nat)
| Skip
| Ident (n:ident)
| Plus (a b:value)
.



Inductive instr :=
| OP_Instrs (v:value)
| OP_Call (i:ident)
.


Inductive term :=
| ret (i:ident)
.

Inductive cmd :=
| step_ins (i:instr)
| term_ins (t:term)
.


Record block := mkBlock {blk_id : ident;  blk_code : list (instr_id*instr); blk_term : (instr_id*term)}.


Record program := mkProgram   { prog_blocks : list block}.


Definition pc : Set := (ident * instr_id).
Definition env : Set := list (instr_id * value).

Inductive frame :=
| KRet (i:ident) (p:pc) (e:env)
.

Definition stack := list frame.


Definition state := (pc * env * stack)%type.
  Definition pc_of (s:state) :=
    let '(p, e, k) := s in p.

  Definition env_of (s:state) :=
    let '(p, e, k) := s in e.

  Definition stack_of (s:state) :=
    let '(p, e, k) := s in k.

  Definition instr_id_of (s:state) :=
    snd (pc_of s).

  
Fixpoint get_env (e:env) (i:instr_id) : option value :=
  match e with
  | nil => None
  | hd :: tl => if beq_nat (fst hd) i then Some (snd hd) else get_env tl i
  end.



Fixpoint eval_value (v:value) (e:env) :=
  match v with
  | Skip => Some Skip
  | Num a => Some (Num a)
  | Ident a => get_env e a
  | Plus a b => match (eval_value a e), (eval_value b e) with
                 | Some (Num c), Some (Num d) => Some (Num (c + d))
                 | _, _ => None
                 end
                   
  end.


Fixpoint find_block (l:list block) (b:ident) :=
  match l with
  | nil => None
  | hd :: tl => if beq_nat (blk_id hd) b then Some hd else find_block tl b
  end.



Definition fallthrough (l:list (instr_id*instr)) (t:instr_id) :=
  match l with
  | nil => t
  | hd :: tl => fst hd
  end.
Print block.


Definition blk_term_id (b:block) : instr_id := fst (blk_term b).
Definition blk_term_ins (b:block) : term := snd (blk_term b).



Definition block_entry (b:block) := fallthrough (blk_code b) (blk_term_id b).
Print program. 
Definition get_block_entry (p:program) (i:ident) : option pc :=
  match find_block (prog_blocks p) i with
  | Some b => Some (i, (block_entry b))
  | None => None
  end.
Print get_block_entry.
  


                                      
Fixpoint find_instr (l:list (instr_id * instr)) (i t:instr_id) :=
  match l with
  | nil => None
  | hd :: tl => if beq_nat (fst hd) i then Some (step_ins (snd hd), Some (fallthrough tl t)) else find_instr tl i t
  end.




Print cmd.
Definition block_to_cmd (b:block) (i:instr_id) :=
  if beq_nat (blk_term_id b) i then Some (term_ins (blk_term_ins b), None) else find_instr (blk_code b) i (blk_term_id b).



Print pc.


Definition fetch (p:pc) (prog:program) : option cmd :=
  match find_block (prog_blocks prog) (fst p)  with
  | None => None
  | Some b => match block_to_cmd b (snd p) with
              | None => None
              | Some (ins, _) => Some ins
              end
                
  end.

Print pc.

Print block.
Definition incr_pc (p:pc) (prog:program) : option pc :=
  match find_block (prog_blocks prog) (fst p)  with
  | None => None
  | Some b => match block_to_cmd b (snd p) with
              | Some (_, Some ins_id) => Some (blk_id b, ins_id)
              | _ => None
              end
                
  end.




(*events*)

Inductive Event :=
| Fin : value -> Event
| Err : Event
.

(*transition*)

Inductive transition X :=
| Step (s:X)
| Obs (m:Event)
.


(*exec instr*)


Print cmd.

Print get_env. Print pc. Print frame.
Definition eval_term (t:term) (prog:program) (s:state) :=
  match t with
  | ret a =>  match get_env (env_of s) a with
              | None => Obs state Err
              | Some res => match (stack_of s) with
                            | nil => Obs state (Fin res)
                            | (KRet id p e) :: tl => Step state (p, (id,res) :: e, tl)
                            end
              end
  end.
Print frame.

(*frame
 *) Print frame.

(*ident pc env*)

Definition new_frame (s:state) (new_pc:pc) :=
  (KRet (snd (pc_of s)) new_pc (env_of s)):: (stack_of s).


Definition eval_instrs (i1: instr_id) (i:instr) (prog:program) (s:state) :=
  match incr_pc (pc_of s) prog with
  | None => Obs state Err
  | Some ins_id => match i with
                   | OP_Instrs ins => match eval_value ins (env_of s) with
                                      | Some res => Step state (ins_id, (i1, res) :: (env_of s), stack_of s)
                                      | None => Obs state Err
                                      end
                   | OP_Call new_block => match  get_block_entry prog new_block with
                                          | None => Obs state Err
                                          | Some new_pc =>  Step state (new_pc, nil, new_frame s ins_id)
                                          end
                                            
                   end
  end.
Print cmd.

Definition stepD (prog:program) (s:state) :=
  match fetch (pc_of s) prog with
  | None => Obs state Err
  | Some (step_ins ins) => eval_instrs (fst (pc_of s)) ins prog s
  | Some (term_ins ter) => eval_term ter prog s
  end.




CoInductive Trace X :=
| Vis (v : Event)
| Tau (s:X) (k : Trace X)
.



CoFixpoint sem (p:program) (s:state) : Trace state :=
  match stepD p s with
  | Step _ s' => Tau state s (sem p s')
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


  
Definition areg : Set := (instr_id * value).
Definition aenv : Set := list areg.

Print step_ins.
Print instr.
Print value.
 
Definition transfer (a:aenv) (i:instr_id * cmd) : aenv :=
    match snd i with
    | step_ins (OP_Instrs (Num n)) => (fst i, (Num n)) :: a
                                                      
    | _ => a
    end.

  
Fixpoint value_analysis_fix (acc:aenv) l (i:nat)  :=
  match l with
  | nil => nil
  | hd :: tl => if beq_nat (fst hd) i then acc else (value_analysis_fix (transfer acc hd) tl i)
  end.


Definition value_analysis l (i:nat) := value_analysis_fix nil l i.

Definition map_exp_to_cmd (e:instr_id * instr) : (instr_id * cmd) := (fst e, step_ins (snd e)).
Definition map_term_to_cmd (t: (instr_id*term)) : list (instr_id * cmd) := cons (fst t, term_ins (snd t)) nil.



Definition prep_block (b:block) := map map_exp_to_cmd (blk_code b) ++ map_term_to_cmd (blk_term b).

Definition prep_selected_block (prog:program) (p:pc) :=
  match find_block (prog_blocks prog) (fst p) with
  | None => None
  | Some a => Some (prep_block a)
  end.



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


Definition newlist := list (instr_id * cmd).


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


Lemma find_tuple_implies : forall l i i1,  NoDup (map fst l) -> find_tuple l i = Some i1 ->
                            exists head tl, l = head ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple in *. induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. inversion H0. subst. exists nil; eauto. exists l. eauto.
inversion H. subst. eapply IHl in H4; eauto. simpl in *. inversion H4. subst. inversion H1. subst. simpl in *. eauto. exists ( (i0, v) :: x ). exists x0. eauto. 
Qed.



      
Lemma incr_pc_implies : forall l i i1 t,  NoDup (map fst  l) -> list_to_tuple l i = Some (i1, Some t) ->
                            exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof. (*intros. unfold increase_tuple in *. simpl in *. simpl in *. induction l. simpl in *. inversion H0.
       simpl in *. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. subst. destruct l. simpl in *. inversion H3. simpl in *. inversion H3. destruct p0. simpl in *. subst. exists nil. simpl. exists l. simpl. eauto. simpl in *. inversion H. subst. eapply IHl in H4; eauto. inversion H4. subst. inversion H1. subst. inversion H2. simpl in *. subst. simpl in *. inversion H2. subst. exists ((i0, e0) :: x). simpl. exists x0. exists x1. eauto. Qed.
        *) Admitted.







  Lemma incr_pc_implies2 : forall prog i i1 t,  NoDup (map fst (prep_block prog)) ->  block_to_cmd prog i =  Some (i1, Some t) ->  find_in_newlist (prep_block prog) i = Some (i1, Some t).

  Proof. intros. unfold block_to_cmd in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *.
         destruct blk_term0. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. eapply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. simpl in *. induction blk_code0. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i2 i). destruct b. eapply beq_nat_eq in Heqb0. subst. simpl in *. inversion H0. subst. simpl in *. destruct blk_code0.  simpl in *.

 eauto. simpl in *. eauto.
 eapply IHblk_code0; eauto. inversion H; subst; eauto. Qed.

  

                                                                                                                    
Lemma get_prog_id : forall prog, NoDup ((map fst (blk_code prog)) ++  (blk_term_id prog ) :: nil) ->
                                 NoDup (map fst (prep_block prog)).
Proof. intros. unfold prep_block. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *.
       induction blk_code0. simpl in *. auto. simpl in *. destruct a. simpl in *. inversion H. simpl in *. subst.  eapply IHblk_code0 in H3. subst. unfold not in H2. simpl in *. contradiction H2. simpl.
Admitted.



Lemma incr_pc_implies1 : forall l i i1 t,  NoDup (map fst l) ->
                                           find_in_newlist l i = Some (i1, Some t) ->
                                          exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof. simpl in *. intros. induction l; simpl in *.
       +inversion H0.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. simpl in *. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. subst.
        *exists nil. simpl. destruct l. simpl in *. inversion H3. simpl in *. inversion H3. subst. (* destruct p0. simpl in *. exists l. exists c. eauto.
        *inversion H. subst. eapply IHl in H4; eauto. inversion H4. inversion H1. subst. inversion H2. subst. simpl in *. exists ( (i0, c)
    :: x). simpl in *. exists x0. exists x1. eauto.*) Admitted.




Lemma testtest : forall l hd i i1 t r tl a,  NoDup (map fst l) -> l = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl ->   value_analysis_fix a l t =
  transfer (value_analysis_fix a l i) (i, i1).
Proof. intros. simpl in *. generalize a. simpl in *. rewrite H0. rewrite H0 in H. clear H0. induction hd. simpl in *. remember (PeanoNat.Nat.eqb i t). destruct b. apply beq_nat_eq in Heqb. subst.
inversion H. subst. contradiction H2.  simpl; eauto.
       simpl in *. rewrite PeanoNat.Nat.eqb_refl. simpl in *. rewrite PeanoNat.Nat.eqb_refl.  eauto. simpl in *. destruct a0.  simpl in *. remember ( PeanoNat.Nat.eqb n t). destruct b. apply  beq_nat_eq in Heqb. subst. clear IHhd. inversion H. subst.  clear H3. clear H. assert (In t (map fst (hd ++ (i, i1) :: (t, r) :: tl))).
       simpl in *. induction hd. simpl in *. right; left; eauto. simpl in *. right. apply IHhd. unfold not. intros. apply H2. right. auto. apply H2 in H. inversion H.


       +simpl in *. remember ( PeanoNat.Nat.eqb n i). destruct b. apply beq_nat_eq in Heqb0. subst.
        *inversion H. subst. clear IHhd. clear H3. clear H. assert (In i (map fst (hd ++ (i, i1) :: (t, r) :: tl))). induction hd. simpl in *. left. auto. simpl. right. apply IHhd. simpl in *. unfold not. intros. unfold not in H2. apply H2. right. auto. apply H2 in H. inversion H.  
        *assert ( NoDup (map fst (hd ++ (i, i1) :: (t, r) :: tl))). inversion H; subst. apply H3. intros. remember ((transfer a0 (n, c))). eapply IHhd. inversion H; subst. eapply H4. Qed.

 Lemma testtest2 : forall prog i i1 t, NoDup ((map fst (blk_code prog)) ++ ( blk_term_id prog ) :: nil) -> block_to_cmd prog i =  Some (i1, Some t)  ->  value_analysis  (prep_block prog) t = transfer (value_analysis  (prep_block prog) i) (i, i1).
 Proof. intros. assert (H' := H). eapply get_prog_id in H.   assert (H'' := H).   assert (H''' := H). 
        eapply  incr_pc_implies2 in H; eauto. eapply incr_pc_implies1 in H''; eauto.
inversion H''. inversion H1. inversion H2. subst. eapply testtest in H'''; eauto. Qed.

 
Lemma test5 : forall prog i i1 t head,  NoDup ((map fst (blk_code prog)) ++ (blk_term_id prog :: nil)) ->
                                        block_to_cmd prog i = Some (t, Some i1) ->
                                        value_analysis (prep_block prog) i = head  ->
                                        value_analysis (prep_block prog) (i1) = transfer head (i, t).
Proof. intros. eapply testtest2 in H; eauto. rewrite <- H1; eauto. Qed.


Print cmd.
Print instr.

Print fetch.

Definition instr_is_call (prog:program) (s:state) := forall i, fetch (pc_of s) prog = Some (step_ins (OP_Call i)).
Definition instr_is_op (prog:program) (s:state) := forall i, fetch (pc_of s) prog = Some (step_ins (OP_Instrs i)).
Definition instr_is_term (prog:program) (s:state) := forall i, fetch (pc_of s) prog = Some (term_ins i).


Definition Subset s s' := forall a : (instr_id * value), In a s -> In a s'.
Print Subset.


Print prep_selected_block.
Definition sound_env (prog:program) (p:pc) (e:env) :=
  forall prep, prep_selected_block prog p = Some prep -> Subset (value_analysis prep (snd p)) e.





    Inductive sound_stack : program -> stack -> Prop :=
    | sound_stack_nil : forall prog, sound_stack prog nil
    | sound_stack_call : forall prog id p e k (SENV: sound_env prog p e)
                                  (STK: sound_stack prog k), sound_stack prog ((KRet id p e)::k).

Inductive sound_state : program -> state -> Prop :=
| opstate : forall p s (STK:sound_stack p (stack_of s)) (senv: sound_env p (pc_of s) (env_of s)), sound_state p s
.
                                           
                                                                 
Lemma get_aenv_env_equiv : get_from_aenv = get_env.
Proof. repeat (apply functional_extensionality; intros). induction x; simpl; eauto. destruct a.  simpl in *. destruct ( PeanoNat.Nat.eqb i x0); simpl in *; eauto. Qed.

Print fetch.


Lemma testtesttest : forall b0 blk_instrs0 b, Some b0 = find_block blk_instrs0 b -> b = blk_id b0.                          
Proof. Admitted.

Lemma aenv_nil : forall b0, (value_analysis (prep_block b0) (fallthrough (blk_code b0) (blk_term_id b0))) = nil.
Proof. intros. destruct b0. simpl in *. unfold value_analysis, prep_block, fallthrough, blk_term_id.  destruct blk_code0; simpl in *; rewrite PeanoNat.Nat.eqb_refl; eauto.
Qed.

Lemma aenv_nil_subset : forall b0, Subset (value_analysis (prep_block b0) (fallthrough (blk_code b0) (blk_term_id b0))) nil.
Proof. intros. rewrite aenv_nil. unfold Subset. intros; eauto. Qed.
       Hint Resolve aenv_nil_subset.

Ltac duplicate X := generalize X; intro. 

Lemma step_preserves_soundness2 : forall prog st st1,
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state prog st  -> stepD prog st = Step state st1 -> sound_state prog st1.
Proof. intros. unfold stepD in *. simpl in *. unfold fetch in *. simpl in *. unfold pc_of in *. simpl in *. destruct st, st1. simpl in *. destruct p, p0. simpl in *. destruct p, p0. simpl in *. remember (find_block (prog_blocks prog) i ). destruct o. simpl in *. remember ( block_to_cmd b i0). destruct o. simpl in *. destruct p. unfold eval_instrs, eval_term in *. simpl in *. unfold incr_pc in *. simpl in *. rewrite <- Heqo in H1. rewrite <- Heqo0 in H1. simpl in *.


       destruct c. destruct o. destruct i3. simpl in *. destruct v. simpl in *.

       +inversion H1; subst. simpl in *. inversion H0. subst. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. simpl in *. specialize (senv (prep_block b)). simpl in *. assert (Some (prep_block b) = Some (prep_block b)) by auto. apply senv in H2.
        constructor. simpl in *. auto. simpl in *. unfold sound_env. simpl in *. intros. simpl in *. unfold prep_selected_block in *. simpl in *. duplicate Heqo. apply testtesttest in Heqo1. simpl in *. subst. rewrite <- Heqo in H3. inversion H3. subst. remember (value_analysis (prep_block b) i0). symmetry in Heql. eapply test5 in H; eauto. unfold transfer in *. simpl in *.



















       

       -unfold sound_env in *; simpl in *; unfold prep_selected_block in *; simpl in *; rewrite <- Heqo in senv;
          simpl in *; duplicate Heqo; apply testtesttest in Heqo; subst; rewrite <- Heqo1; intros; inversion H2; subst; rewrite H; specialize (senv (prep_block b)); apply senv in H2; unfold transfer; simpl in *; unfold Subset in *; simpl in *; intros; right; eauto.
       -remember ( get_env e n). destruct o. inversion H1; subst; eauto. inversion H1.
       -remember ( get_env e n). destruct o; inversion H1; subst. simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. duplicate Heqo. apply testtesttest in Heqo2; subst. rewrite <- Heqo. intros. inversion H2. subst. specialize (senv (prep_block b)). apply senv in H2. unfold Subset in *. simpl in *. rewrite H.  unfold transfer; simpl in *. intros; right; eauto.
       -unfold sound_env in *. remember (eval_value v1 e); remember (eval_value v2 e). destruct o. destruct v.   destruct o0. destruct v. 
        *inversion H3. subst. eauto.
        *inversion H1.
        *inversion H1.
        *inversion H1.
        *inversion H1.
        *inversion H1.
        *inversion H1.
        *inversion H1.
        *inversion H1.
       -remember (eval_value v1 e). destruct o. destruct v. remember (eval_value v2 e). destruct o. inversion H1.  destruct v. inversion H1. inversion H3. subst.
        *unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. duplicate Heqo. apply testtesttest in Heqo3; subst. rewrite <- Heqo. intros. inversion H2. subst. apply senv in H2. rewrite H. unfold transfer. simpl in *. unfold Subset in *. simpl in *. right. auto.
        *inversion H3.
        *inversion H3.
        *inversion H3.
        *inversion H3.
        *inversion H1.
        *inversion H1.
        *inversion H1.
        *inversion H1.
       -unfold eval_instrs in *. simpl in *. unfold incr_pc in *. simpl in *. rewrite <- Heqo in H1. rewrite <- Heqo0 in H1. inversion H1.
        +unfold eval_instrs in *. simpl in *. unfold incr_pc in *. simpl in *. rewrite <- Heqo in H1. rewrite <- Heqo0 in H1. destruct o. simpl in *. remember (get_block_entry prog i3). destruct o. inversion H1; eauto; subst. constructor.
         *simpl in *. constructor; simpl in *; eauto. eapply test5 in H; eauto. unfold sound_env. simpl in *. unfold sound_env in *. simpl in *. intros. unfold prep_selected_block in *. simpl in *. duplicate Heqo. apply testtesttest in Heqo2. subst. rewrite <- Heqo in H2. inversion H2. rewrite H. simpl in *. unfold transfer. simpl in *.  subst. rewrite <- Heqo in senv. apply senv in H2. auto.   
         *simpl in *. unfold get_block_entry in *. simpl in *. unfold sound_env. simpl in *. remember (find_block (prog_blocks prog) i3). destruct o. unfold block_entry in *. simpl in *. inversion Heqo1. subst. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo2. intros. inversion H2; eauto. inversion Heqo1.
         *inversion H1.
         *inversion H1.
        +destruct t. simpl in *. remember ( get_env e i3). destruct o0. destruct s. simpl in *. inversion H1. destruct f. simpl in *. inversion H1. subst. constructor. simpl in *. inversion STK; subst; eauto. simpl in *. inversion STK; subst. unfold sound_env in SENV. simpl in *. unfold sound_env. simpl in *. intros. unfold prep_selected_block in *. simpl in *. destruct (find_block (prog_blocks prog) i1). inversion H2. subst. apply SENV in H2. unfold Subset in *. simpl in *. intros. right; eauto. inversion H2. inversion H1.
       +inversion H1.
       +inversion H1.
        Qed.