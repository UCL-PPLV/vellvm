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
Definition function_id := nat.


Inductive exp : Type :=
| AIdent : instr_id -> exp
| ANum : nat -> exp
| APlus : exp -> exp -> exp
| ANone : exp
.



(*| INSTR_Alloca (t:typ) (nb: option tvalue) (align:option int) 
| INSTR_Load  (volatile:bool) (t:typ) (ptr:tvalue) (align:option int)       
| INSTR_Store (volatile:bool) (val:tvalue) (ptr:tvalue) (align:option int)
 *)




Inductive instr :=
| INSTR_Op (e:exp)
| INSTR_Call (i:instr_id)
.



Inductive terminator : Type :=
| br_2 (i:instr_id) (b1 b2:block_id)
| br (b:block_id)
| term (i:instr_id)
.



Definition pc : Set := (function_id * block_id * instr_id).
Definition example : pc := (1, 2, 3).

Definition fn_id_of (p:pc) := fst (fst p).
Definition blk_id_of (p:pc) := snd (fst p).
Definition instr_id_of (p:pc) := snd  p.


Definition env := list (instr_id * exp).


Inductive frame :=
| KRet (e:env) (i:instr_id) (p:pc)
.

Definition stack := list frame.


Record state := mkState {e : env; p : pc; s : stack}.



Record block := mkBlock {blk_id : block_id;  blk_code : list (instr_id*instr); blk_term : (instr_id*terminator)}.



Record cfg := mkCFG {cfg_id: function_id; init: block_id; blk_instrs : list block}.

Record program := mkProgram {list_cfg : list cfg}.


Fixpoint get_env (s:env) (i:instr_id) : option exp :=
  match s with
  | nil => None
  | (iis, ins)::tl => if beq_nat iis i then Some ins else get_env tl i
  end.

Definition add_env (s:env) (i:instr_id) (v:exp) := (i, v) :: s.


Inductive cmd :=
| Term (i:terminator)
| Step_cmd (e:instr)
.



Definition blk_term_id (b:block) := fst (blk_term b).
Definition blk_term_instr (b:block) := snd (blk_term b).
Definition get_blk_id (b:block) :=  (blk_id b).
Definition get_cfg_id (c:cfg) := cfg_id c.

Fixpoint get_cfg (l:list cfg) (f:function_id) :=
  match l with
  | nil => None
  | hd :: tl => if beq_nat (get_cfg_id hd) f then Some hd else get_cfg tl f
  end.

                                                                 
  


Fixpoint get_block (l:list block) (i:block_id) : option block :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (get_blk_id hd) i) then Some hd else get_block tl i
  end.


Definition fallthrough (cd:list (instr_id*instr)) (t:instr_id) :=
  match cd with
  | nil => t
  | hd :: _ => fst hd
  end.


Definition block_entry (b:block) := fallthrough (blk_code b) (blk_term_id b).

                                      
Fixpoint find_instr (l:list (instr_id * instr)) (i t:nat)  :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (fst hd) i) then Some (Step_cmd (snd hd), Some (fallthrough tl t)) else find_instr tl i t
  end.


Definition block_to_cmd (b:block) (i:instr_id) : option (cmd * option instr_id) :=
  if beq_nat (blk_term_id b) i then Some (Term (blk_term_instr b), None) else find_instr (blk_code b) i (blk_term_id b).


Print pc. Print program.


Definition fetch (prog:program) (p:pc) :=
  match get_cfg (list_cfg prog) (fn_id_of p) with
  | None => None
  | Some l => match get_block (blk_instrs l) (blk_id_of p) with
              | None => None
              | Some b => match block_to_cmd b (instr_id_of p) with
                          | None => None         
                          | Some (a, _) => Some a
                          end
              end
  end.


                
  

Print pc.
Definition incr_pc (prog:program) (p:pc) : option pc :=
  match get_cfg (list_cfg prog) (fn_id_of p) with
  | None => None
  | Some l => match get_block (blk_instrs l) (blk_id_of p) with
              | None => None
              | Some b => match block_to_cmd b (instr_id_of p) with
                          | Some (_,Some a) => Some (fn_id_of p, blk_id_of p, a)
                          | _ => None
                          end
              end
  end.

Print block_entry.
Definition get_block_entry_pc (prog:program) (fid:function_id) (bid:block_id) : option pc :=
  match get_cfg (list_cfg prog) fid with
  | None => None
  | Some l => match get_block (blk_instrs l) bid with
              | None => None
              | Some b => Some (fid, bid, block_entry b)
              end
  end.


Print cfg.
Definition get_function_entry (prog:program) (fid:function_id) : option pc :=
  match get_cfg (list_cfg prog) fid with
  | None => None
  | Some l => match get_block (blk_instrs l) (init l) with
              | None => None
              | Some b => Some (fid, (init l), block_entry b)
              end
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
Print eval_exp. Print state.
Print frame.
Definition eval_term (prog:program) (fid:function_id) (t:terminator) (e:env) (s:stack):=
  match t with
  | br_2 id br1 br2 => match (eval_exp (AIdent id) e) with
                             | Some (ANum 1) =>  match get_block_entry_pc prog fid br1 with
                                          | None => Obs state Err
                                          | Some a => Step state (mkState e a s)
                                                 end
                             | Some _ =>  match get_block_entry_pc prog fid br2 with
                                          | None => Obs state Err
                                          | Some a => Step state (mkState e a s)
                                          end
                             | None => Obs state Err
                                         
                       end
                         
  | br id => match get_block_entry_pc prog fid id with
             | None => Obs state Err
             | Some a => Step state (mkState e a s)
             end
  | term a => match get_env e a with
              | None => Obs state Err
              | Some a => match s with
                          | nil => Obs state (Fin a)
                          | (KRet e id p) :: tl => Step state (mkState ((id, a) :: e) p tl)
                          end
                            
              end
  end.

Print state.

Print add_env.
Print frame.
Print eval_exp. Print pc. Print instr. Print get_function_entry.
Definition eval_ins prog (next_pc:pc) (ins:instr) k cur_iid (e:env) :=
  match ins with
  | INSTR_Op op =>  match (eval_exp op e) with
                    | Some a => Step state (mkState (add_env e cur_iid a) next_pc k)
                    | None => Obs state Err
                    end
  | INSTR_Call a => match get_function_entry prog a with
                    | None => Obs state Err
                    | Some new_pc => Step state (mkState (nil) new_pc ((KRet e cur_iid next_pc)::k ))
                    end
                      
  end.










Print instr_id_of.

Definition StepD (prog:program) (s:state) : transition state :=
  let (e, pc, k) := s in
  match fetch prog pc with
  | Some (Step_cmd ins) => match incr_pc prog pc with
                           | None => Obs state Err
                           | Some next_pc => eval_ins prog next_pc ins k (instr_id_of pc) e
                           end
                             
                             
  | Some (Term a) => eval_term prog (fn_id_of (p s)) a e k
  | _ => Obs state Err
  end.


CoInductive Trace X :=
| Vis (v : Event)
| Tau (s:X) (k : Trace X)
.



CoFixpoint sem (prog:program) (s:state) : Trace state :=
  match StepD prog s with
  | Step _ s' => Tau state s (sem prog s')
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


Definition areg : Set := (instr_id * option exp).
Definition aenv : Set := list areg.

Print cfg.
Print cmd.
Definition map_exp_to_cmd (e:instr_id * instr) : (instr_id * cmd) := (fst e, Step_cmd (snd e)).
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
(*NEW*)

Print cmd.
Print instr.

Definition transfer (a:aenv) (i:instr_id * cmd) : aenv :=
  match snd i with
  | Step_cmd (INSTR_Op (ANum t)) => (fst i, Some (ANum t)) :: a
  | Step_cmd (INSTR_Op (AIdent t)) => (fst i, None) :: a

  | _ => (fst i, None) :: a
  end.




Fixpoint value_analysis_fix (acc:aenv) l (i:nat)  :=
  match l with
  | nil => nil
  | hd :: tl => if beq_nat (fst hd) i then acc else (value_analysis_fix (transfer acc hd) tl i)
  end.

Print value_analysis_fix.



Definition value_analysis l (i:nat) := value_analysis_fix nil l i.



Definition prep_selected_block (prog:program) (p:pc) :=
  match get_cfg (list_cfg prog) (fn_id_of p) with
  | None => None
  | Some l => match get_block (blk_instrs l) (blk_id_of p) with
              | None => None
              | Some a => Some (prep_block a)
              end
  end.


Definition value_analysis_specific (prog:program) (p:pc) :=
  match prep_selected_block prog p with
  | None => None
  | Some a => Some (value_analysis a (snd p))
  end.



Lemma find_tuple_implies : forall l i i1,  NoDup (map fst l) -> find_tuple l i = Some i1 ->
                            exists head tl, l = head ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple in *. induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. inversion H0. subst. exists nil; eauto. exists l. eauto.
inversion H. subst. eapply IHl in H4; eauto. simpl in *. inversion H4. subst. inversion H1. subst. simpl in *. exists ( (i0, o) :: x ). exists x0. eauto. 
 Qed.       
Print increase_tuple.


      
Lemma incr_pc_implies : forall l i i1 t,  NoDup (map fst  l) -> list_to_tuple l i = Some (i1, Some t) ->
                            exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof. intros. unfold increase_tuple in *. simpl in *. simpl in *. induction l. simpl in *. inversion H0.
       simpl in *. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. subst. destruct l. simpl in *. inversion H3. simpl in *. inversion H3. destruct p0. simpl in *. subst. exists nil. simpl. exists l. simpl. eauto. simpl in *. inversion H. subst. eapply IHl in H4; eauto. inversion H4. subst. inversion H1. subst. inversion H2. simpl in *. subst. simpl in *. inversion H2. subst. exists ((i0, o) :: x). simpl. exists x0. exists x1. eauto. Qed.




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
Print prep_block. Print blk_term_id.
Lemma prog_id_eq : forall prog, (map fst (blk_code prog)) ++ (cons (blk_term_id prog ) nil) =  (map fst (prep_block prog)).
Proof. intros. simpl in *. unfold prep_block. simpl in *. unfold map_term_to_cmd in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *. induction blk_code0. simpl in *. eauto.
       simpl in *. destruct a. simpl in *. rewrite IHblk_code0. eauto. Qed.
       

  
Lemma get_prog_id : forall prog, NoDup ((map fst (blk_code prog)) ++  (blk_term_id prog ) :: nil) ->
                                 NoDup (map fst (prep_block prog)).
Proof. intros. rewrite <- prog_id_eq. eauto. Qed.


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



Print block.
Lemma testtesttest : forall b0 blk_instrs0 b, Some b0 = get_block blk_instrs0 b -> b = blk_id b0.                          
Proof.
  intros. induction blk_instrs0. simpl in *. inversion H. simpl in *. unfold get_blk_id in H. simpl in *. destruct a. simpl in *.
remember ( PeanoNat.Nat.eqb blk_id0 b). destruct b1; eauto.  eapply beq_nat_eq in Heqb1. symmetry. destruct b0. simpl in *. inversion H. subst. auto. Qed. 

Print cfg.

Lemma testtesttest1 : forall b0 cfg b, Some b0 = get_cfg (list_cfg cfg) b -> b = cfg_id b0.                          
Proof. intros. destruct b0. simpl in *. destruct cfg0. simpl in *. induction list_cfg0.
       +simpl in *. inversion H.
       +simpl in *. unfold get_cfg_id in *. simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb cfg_id1 b). destruct b0. eapply  beq_nat_eq in Heqb0. subst. inversion H. subst. auto. inversion H. apply IHlist_cfg0. eauto. Qed.


Lemma value_analysis_at_entry_is_nil : forall b4,

  (value_analysis_fix nil
       (map map_exp_to_cmd (blk_code b4) ++
            map_term_to_cmd (blk_term b4)) (block_entry b4)) = nil.

Proof. intros. unfold block_entry. simpl in *. destruct b4. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term0. simpl in *. destruct blk_code0. simpl in *. rewrite PeanoNat.Nat.eqb_refl. auto. simpl in *. destruct p0. simpl in *. rewrite PeanoNat.Nat.eqb_refl. auto.
Qed.



Print get_env.


Print env.
Print areg.
Print exp.
SearchAbout exp.
Fixpoint beq_exp (a b: exp) :=
  match a, b with
  | AIdent a1, AIdent a2 => beq_nat a1 a2
  | ANum a1, ANum a2 => beq_nat a1 a2
  | ANone, ANone => true
  | APlus a b, APlus c d => beq_exp a c && beq_exp b d
  | _, _ => false                                  
  end.


Definition beq_pair1 (p: instr_id * option exp) (p1: instr_id * exp) : bool :=
  match p, p1 with
  | (k, None), (k1, a) => (beq_nat k k1)
  | (k, Some a1), (k1, a) => (beq_nat k k1) &&  (beq_exp a a1)
  end.


Fixpoint list_eq2 (l:aenv) (l1:env) : bool :=
  match l, l1 with
  | nil, nil => true
  | l1, nil => false
  | nil, l1 => true
  | hd::tl, hd1::tl1 => (beq_pair1 hd hd1) && (list_eq2 tl tl1)
  end.
Fixpoint get1 (n:nat) (l:areg) :=
  match l with
  | nil => None
  | hd :: tl => if beq_nat (fst hd) n then Some (snd hd) else get1 n tl
  end.*)

(*
Lemma test12: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> In (n, Some a) l1 -> In (n, a) l2.
Proof. induction l2. intros.  destruct l1. simpl in *. inversion H0. simpl in *. inversion H.
       intros. simpl in *. induction l1. simpl in *. inversion H0. simpl in *.
       remember (beq_pair1 a1 a). destruct b. simpl in *. inversion H0. left.
   (*    unfold beq_pair1 in *. simpl in *. destruct a1. simpl in *. destruct a.
       simpl in *. destruct o. destruct o0. simpl in *.
       remember (PeanoNat.Nat.eqb n0 n1). destruct b. apply beq_nat_eq in Heqb0.
       subst. remember (PeanoNat.Nat.eqb n2 n3). destruct b.
       apply beq_nat_eq in Heqb0. subst. auto. simpl in *. inversion Heqb.
       simpl in *. inversion Heqb. inversion Heqb. destruct o0. simpl in *. inversion H1. inversion H1.
right.

eapply IHl2 in H; eauto. simpl in *. inversion H.*) Admitted.

    Lemma In_conv : forall l e1 i1, Some e1 = get1 i1 l -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb n i1). destruct b. inversion H. subst. left. apply beq_nat_eq in Heqb. subst. auto. right. apply IHl. apply H. Qed.


Lemma tes3t12313: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> Some (Some a) = get1 n l1 -> Some (Some a) = get1 n l2.


*)






  Definition Subset s s' := list_eq2 s s' = true.
  Print Subset.


 Definition sound_env (prog:program) (p:pc) (e:env) := forall prep, prep_selected_block prog p = Some prep -> Subset (value_analysis prep (snd p)) e.
    Print state.

Print pc. SearchAbout pc. Print cmd. Print Step_cmd. Print instr. Print Step_cmd.
    Inductive sound_stack : program -> stack -> Prop :=
    | nil_stack : forall p,  sound_stack p nil
    | step_stack : forall id prog p e k (sstack_env: sound_env prog ((fn_id_of p), (blk_id_of p), id) e) (stk:sound_stack prog k), incr_pc prog ((fn_id_of p), (blk_id_of p), id) = Some p ->
                                                                                                   (exists i1, fetch prog ((fn_id_of p), (blk_id_of p), id) = Some (Step_cmd (INSTR_Call i1)))  ->sound_stack prog ((KRet e id p)::k).
Print state.




Print incr_pc.

Print state. Print fetch. Print cmd.
Print state.
Print fetch.
Print cmd.
Print instr.

Print stack. Print state.
Print frame. Print state. Print add_env.
 Inductive sound_state : program -> state -> Prop :=
   | sound_state_intro :
     forall prog k  pc_next  e
            (sstack: sound_stack prog k)
            (senv: sound_env prog pc_next e),  
                                                 sound_state prog (mkState e pc_next k)

 .

 Inductive sound_state1 : program -> state -> cmd -> Prop :=
   | sound_state_intro1 :
     forall prog k  pc_next e i1
            (sstack: sound_stack prog k)
            (senv: sound_env prog pc_next e), fetch prog pc_next = Some (Step_cmd i1) ->
                      sound_state1 prog (mkState e pc_next k) (Step_cmd i1)
   | sound_state_intro2 :
     forall prog k  pc_next i1 e
            (sstack: sound_stack prog k), fetch prog pc_next = Some (Term i1) ->
                     sound_state1 prog (mkState e pc_next k) (Term i1)

 . Print sound_env.



 Print test5.
 Print fetch.

 Print block_to_cmd.
 Print incr_pc.

 Definition prog_to_cmd prog p :=
  match get_cfg (list_cfg prog) (fn_id_of p) with
  | None => None
  | Some l => match get_block (blk_instrs l) (blk_id_of p) with
              | None => None
              | Some b => block_to_cmd b (instr_id_of p) 
              end
  end.
        Print fetch. Print prog_to_cmd.

Lemma fetch_incr_block_to_cmd1 : forall prog p ins next_pc, fetch prog p = Some ins -> incr_pc prog p = Some next_pc -> prog_to_cmd prog p = Some (ins, Some (instr_id_of next_pc)).
Proof. intros.
       +unfold fetch, incr_pc, prog_to_cmd in *. unfold fn_id_of, blk_id_of, instr_id_of in *. destruct p0. destruct p0. simpl in *. destruct (get_cfg (list_cfg prog) f). destruct (get_block (blk_instrs c) b). destruct (block_to_cmd b0 i). destruct p0. simpl in *. inversion H. destruct o. inversion H0; simpl in *. auto. inversion H0. inversion H0. inversion H0. inversion H0.
Qed.


Lemma subset_none : forall b2 i2 e2 e3, Subset (value_analysis (prep_block b2) i2) e3  ->
                                     Subset ((i2, None) :: value_analysis (prep_block b2) i2) ((i2, e2) :: e3).
Proof. intros. unfold Subset in *. simpl in *. rewrite PeanoNat.Nat.eqb_refl. simpl in *. eauto. Qed.
Hint Resolve subset_none.


Lemma subset_start : forall b3 e0, Subset (value_analysis (prep_block b3) (block_entry b3)) e0.
Proof. intros. destruct b3; simpl in *. unfold prep_block. unfold block_entry. simpl in *. unfold blk_term_id in *. unfold fallthrough. simpl in *. unfold value_analysis in *. simpl in *. destruct blk_code0; simpl in *; rewrite PeanoNat.Nat.eqb_refl; unfold Subset; destruct e0; simpl in *; eauto. Qed.

Hint Resolve subset_start.
  Lemma step_preserves_env: forall prog st st1 ,   (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state prog st  -> StepD prog st = Step state st1 -> sound_env prog (p st1) (e st1).
Proof.  intros. destruct st1, st; simpl in *; eauto.
        unfold fetch, incr_pc in *. unfold fn_id_of, blk_id_of, instr_id_of in *. destruct p1, p0. destruct p1, p0. simpl in *. remember (get_cfg (list_cfg prog) f). destruct o. remember ( get_block (blk_instrs c) b). destruct o. remember ( block_to_cmd b1 i). destruct o. destruct p0. simpl in *. 
        destruct c0.
        +destruct i1.
         *simpl in *. remember (get_env e1 i1). destruct o0. destruct e2. (* *) unfold get_block_entry_pc in *. rewrite <- Heqo in H1. remember ( get_block (blk_instrs c) b3). destruct o0. inversion H1. subst. inversion H0; subst. unfold sound_env in *. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo3. intros. inversion H2. subst. eauto. inversion H1. destruct n. unfold get_block_entry_pc in *. rewrite <- Heqo in H1. remember ( get_block (blk_instrs c) b3). destruct o0. inversion H1; subst. unfold sound_env in *. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo3. intros. inversion H2. subst. eauto. inversion H1. destruct n. unfold get_block_entry_pc in *. rewrite <- Heqo in H1. remember ( get_block (blk_instrs c) b2). destruct o0. inversion H1; subst. unfold sound_env. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo3. intros. inversion H2. subst. eauto. inversion H1. unfold get_block_entry_pc in *. unfold sound_env. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo in H1. remember (get_block (blk_instrs c) b3). destruct o0. inversion H1. subst. rewrite <- Heqo. rewrite <- Heqo3. intros. inversion H2. subst. eauto. inversion H1. unfold get_block_entry_pc in *. rewrite <- Heqo in H1. remember ( get_block (blk_instrs c) b3). destruct o0. inversion H1; subst. unfold sound_env. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo3. intros. inversion H2. subst. eauto. inversion H1. unfold get_block_entry_pc in *. rewrite <- Heqo in H1. remember (get_block (blk_instrs c) b3). destruct o0. inversion H1. subst. unfold sound_env. unfold prep_selected_block. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo3. intros. inversion H2. subst; eauto. inversion H1. inversion H1.





          
         *simpl in *. unfold get_block_entry_pc in *.  rewrite <- Heqo in H1. remember ( get_block (blk_instrs c) b2). destruct o0. inversion H1. subst. inversion H0; subst. unfold sound_env in *. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo2. intros. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. inversion H2.
eauto. inversion H1.          
         *simpl in *.




          remember ( get_env e1 i1). destruct o0. destruct s1. inversion H1. destruct f1. inversion H0; subst. inversion sstack; subst. inversion H1; subst. unfold blk_id_of in *. simpl in *. unfold fn_id_of in *. simpl in *.  inversion H8; subst.  clear H8.

          eapply fetch_incr_block_to_cmd1 in H2; eauto. unfold prog_to_cmd in *. unfold incr_pc in *. unfold blk_id_of in *. unfold instr_id_of in *. simpl in *. unfold fn_id_of in *. simpl in *. remember ( get_cfg (list_cfg prog) f0). destruct o0. remember (get_block (blk_instrs c0) b0).
destruct o0.

eapply test5 in H2; eauto. clear H5. clear H1. clear senv. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. unfold fn_id_of in *. unfold blk_id_of in *. simpl in *. rewrite <- Heqo3. rewrite <- Heqo4. rewrite <- Heqo3 in sstack_env. rewrite <- Heqo4 in sstack_env. intros. inversion H1; subst. apply sstack_env in H1. rewrite H2. clear H2. unfold transfer. simpl in *. eauto. inversion H2. inversion H2. inversion H1.
        +destruct o. simpl in *. unfold eval_ins in *. simpl in *. destruct e2. simpl in *. destruct e2.
        -simpl in *. remember ( get_env e1 i2). destruct o. inversion H1; subst. inversion H0; subst. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. unfold fn_id_of in *. unfold blk_id_of in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo. rewrite <- Heqo0 in senv. rewrite <- Heqo0. intros. inversion H2; subst. apply senv in H2. eapply test5 in H; eauto. rewrite H. unfold transfer. simpl in *. clear H. unfold add_env. eauto. inversion H1.
        -simpl in *. inversion H1.  subst. inversion H0; subst. eapply test5 in H; eauto.  unfold sound_env in *. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo0 in senv. intros. inversion H2. subst. apply senv in H2. rewrite H. unfold transfer. simpl in *. unfold add_env. unfold Subset in *. simpl in *. repeat rewrite PeanoNat.Nat.eqb_refl. simpl in *. eauto.
        -simpl in *. destruct (eval_exp e2_1 e1). destruct e2. inversion H1. remember ( eval_exp e2_2 e1). destruct o. destruct e2. inversion H1. inversion H1. subst. simpl in *. eapply test5 in H; eauto. inversion H0; subst; eauto. unfold sound_env in *. unfold prep_selected_block in *. unfold blk_id_of, fn_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. intros. inversion H2; subst. apply senv in H2. rewrite H. unfold transfer; simpl in *. unfold add_env. simpl in *. eauto. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1.
        -simpl in *. inversion H1; subst. inversion H0; subst. unfold sound_env in *. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. intros. inversion H2. subst. apply senv in H2. unfold add_env. eapply test5 in H; eauto. rewrite H. unfold transfer. simpl in *. eauto.
        -unfold get_function_entry in *. remember ( get_cfg (list_cfg prog) i2). destruct o. remember ( get_block (blk_instrs c0) (init c0)). destruct o. inversion H1; subst. clear H1. inversion H0; subst. unfold sound_env in *. unfold prep_selected_block in *. unfold fn_id_of, blk_id_of in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. rewrite <- Heqo2. rewrite <- Heqo3. intros. inversion H1. subst. unfold Subset. simpl in *. unfold value_analysis. simpl in *. unfold prep_block. destruct b2. simpl in *. destruct blk_code0. simpl in *. unfold block_entry. simpl in *. unfold blk_term_id in *. simpl in *. rewrite PeanoNat.Nat.eqb_refl. simpl in *. eauto. simpl in *. unfold block_entry in *. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto. inversion H1. inversion H1.
        -inversion H1.
         +inversion H1.
         +inversion H1.
         +inversion H1.
Qed.

    
  Lemma step_preserves_stack : forall prog st st1 ,   (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state prog st  -> StepD prog st = Step state st1 -> sound_stack prog (s st1).
Proof. intros. destruct st1, st; simpl in *; eauto.
       unfold fetch, incr_pc in *. unfold fn_id_of, blk_id_of, instr_id_of in *. destruct p1, p0. destruct p1, p0. simpl in *. remember (get_cfg (list_cfg prog) f). destruct o. remember ( get_block (blk_instrs c) b). destruct o. remember ( block_to_cmd b1 i). destruct o. destruct p0. simpl in *.
       destruct c0.
       +destruct i1.
        *simpl in *. unfold get_block_entry_pc in *. rewrite <- Heqo in H1. destruct (get_env e1 i1). destruct e2. destruct (get_block (blk_instrs c) b3). inversion H1; subst. inversion H0; subst; eauto. inversion H1. destruct n; simpl in *. remember (get_block (blk_instrs c) b3). destruct o0. inversion H1; subst; eauto. inversion H0; subst; eauto. inversion H1. destruct n. destruct (get_block (blk_instrs c) b2). inversion H1; subst. inversion H0; subst; eauto. inversion H1. destruct ( get_block (blk_instrs c) b3). inversion H1; subst. inversion H0; eauto. inversion H1. destruct ( get_block (blk_instrs c) b3). inversion H1; subst. inversion H0; subst; eauto. inversion H1. 
destruct ( get_block (blk_instrs c) b3). inversion H1; subst. inversion H0; subst; eauto. inversion H1. inversion H1.




        *simpl in *. unfold get_block_entry_pc in *. rewrite <- Heqo in H1. remember ( get_block (blk_instrs c) b2). destruct o0. inversion H1. subst. inversion H0; subst; eauto. inversion H1.
        *simpl in *. remember ( get_env e1 i1). destruct o0. destruct s1. inversion H1. destruct f1. inversion H1; subst. inversion H0; subst. inversion sstack; subst. eauto. inversion H1.
       +destruct e2. destruct o. simpl in *.
       -simpl in *.  remember ( eval_exp e2 e1). destruct o. inversion H1; subst. inversion H0. subst. eauto. inversion H1.
       -inversion H1.
       -simpl in *. destruct o. simpl in *. unfold get_function_entry in *. remember (get_cfg (list_cfg prog) i1). destruct o. remember ( get_block (blk_instrs c0) (init c0)). destruct o. inversion H1; subst; simpl in *; eauto. inversion H0; subst; simpl in *; eauto. constructor. unfold blk_id_of in *. simpl in *. unfold fn_id_of in *. simpl in *. eauto. eauto. unfold fn_id_of, blk_id_of in *. simpl in *. unfold incr_pc. unfold fn_id_of, blk_id_of, instr_id_of in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo1. eauto. exists f0. unfold fn_id_of, blk_id_of; simpl in *; eauto. unfold fetch. unfold fn_id_of, blk_id_of, instr_id_of; simpl in *; eauto. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo1. eauto. inversion H1. inversion H1. inversion H1.
        +inversion H1.
        +inversion H1.
        +inversion H1.
Qed.



Lemma step_preserves_state : forall prog st st1 ,   (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state prog st  -> StepD prog st = Step state st1 -> sound_state prog st1.
  Proof. intros. destruct st1. constructor. eapply step_preserves_stack in H; eauto; simpl in *; eauto. eapply step_preserves_env in H; eauto; simpl in *; eauto. Qed.
Print get_from_aenv.




Definition constant_prop_exp (prog:program) (fid: function_id) (bid: block_id) (iid: instr_id) (i:instr) : instr :=
  match (prep_selected_block prog (fid, bid, iid)) with
  | None => i
  | Some a => match i with
              | INSTR_Op (AIdent ident) => let abc := (value_analysis a iid) in
                                match (get_from_aenv abc ident) with
                                | Some (Some (ANum n)) => ( INSTR_Op (ANum n))
                                | _ => i
                                end
              | _ => i
              end
                
  end.

Print block.


Definition opt_instr (prog:program) (fid:function_id) (bid:block_id) (i:instr_id*instr) := (fst i, constant_prop_exp prog fid bid (fst i) (snd i)).


Definition map_code  (l:list (instr_id * instr)) (prog:program) (fid: function_id) (bid: block_id) := map (opt_instr prog fid bid) l.



Definition block_op (fid:function_id) (prog:program) (b:block) :=
  mkBlock (blk_id b) (map_code (blk_code b) prog fid (blk_id b)) (blk_term b).



Print cfg.



Definition map_blocks (fid:function_id) (prog:program) (l:list block) :=
  map (block_op fid prog) l.


Print cfg.

Definition cfg_opt (prog:program) (c:cfg) :=
  mkCFG (cfg_id c) (init c) (map_blocks (cfg_id c) prog (blk_instrs c)).


Print program.

Definition cfg_list_opt (prog:program) := map (cfg_opt prog) (list_cfg prog).



Definition prog_opt (prog:program) := mkProgram (cfg_list_opt prog).

Print StepD.

Definition startfunc p0 f := get_cfg (list_cfg p0) f.
Print startfunc.

Definition targetfunc p0 f := get_cfg (cfg_list_opt p0) f.
Print targetfunc.


Definition endfunc p0 f :=
  match get_cfg (list_cfg p0) f with
  | None => None
  | Some a => Some (cfg_opt p0 a)
  end.
Lemma firstfunc : forall p0 f,  get_cfg (cfg_list_opt p0) f = endfunc p0 f.
Proof. intro. destruct p0. unfold endfunc. simpl in *. unfold cfg_list_opt. simpl in *. simpl in *. induction list_cfg0.
       +simpl in *. auto.
       +simpl in *.  intros. unfold get_cfg_id in *.  remember ( PeanoNat.Nat.eqb (cfg_id a) f).
        destruct b. auto. simpl in *. remember ( a :: list_cfg0). generalize l.  clear IHlist_cfg0. clear Heql. clear l. intros. induction list_cfg0. simpl in *. auto. simpl in *. unfold get_cfg_id in *. simpl in *. remember ( PeanoNat.Nat.eqb (cfg_id a0) f). destruct b. auto. auto. Qed.


Print block_op.
Definition startfunc1 c b :=  get_block (blk_instrs c) b.
Definition  targetfunc1 c p0 b :=  get_block (map_blocks (cfg_id c) p0 (blk_instrs c)) b.
Definition endfunc1 c p0 b :=
  match get_block (blk_instrs c) b with
  | None => None
  | Some a => Some (block_op (cfg_id c) p0 a)
  end.

Lemma firstfunc1 : forall c b p0,  get_block (map_blocks (cfg_id c) p0 (blk_instrs c)) b = endfunc1 c p0 b.
Proof. intros. unfold endfunc1. simpl in *. destruct c. simpl in *. induction blk_instrs0.
       +simpl in *. auto.
       +simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb blk_id0 b). destruct b0. apply beq_nat_eq in Heqb0. subst. auto. auto. Qed.



Definition startfunc2 blk_code0 i i0 := find_instr blk_code0 i i0.


Definition targetfunc2 blk_code0 p0 c blk_id0 i i0 := find_instr (map_code blk_code0 p0 (cfg_id c) blk_id0) i i0.

Definition endfunc2 p0 c blk_id0 blk_code0 i i0 :=
  match find_instr blk_code0 i i0 with
  | Some (Step_cmd a, b) => Some (Step_cmd (constant_prop_exp p0 (cfg_id c) blk_id0 i a), b)
  | rest => rest
              
  end.
Print endfunc2.

Lemma fallthrough_equiv : forall blk_code0 p0 c blk_id0 i0, (fallthrough (map_code blk_code0 p0 (cfg_id c) blk_id0) i0) =  (fallthrough blk_code0 i0).
  Proof. intros. destruct blk_code0. simpl in *. auto. simpl in *. auto. Qed.
Lemma firstfunc2 : forall blk_code0 c blk_id0 i i0 p0, find_instr (map_code blk_code0 p0 (cfg_id c) blk_id0) i i0 = endfunc2 p0 c blk_id0 blk_code0 i i0. Proof.
                                                                                                                                                            intros. simpl in *. unfold endfunc2. simpl in *. induction blk_code0. simpl in *. auto.
                                                                                                                                                            simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb i1 i). destruct b.
rewrite fallthrough_equiv. auto. apply beq_nat_eq in Heqb. subst. auto. auto. Qed.


Lemma block_entry_pc_equiv : forall p0 f b2, get_block_entry_pc p0 f b2  = get_block_entry_pc (prog_opt p0) f b2.
Proof. intros. unfold get_block_entry_pc. simpl in *. rewrite firstfunc. unfold endfunc. simpl in *. destruct ( get_cfg (list_cfg p0) f).
       destruct c. simpl in *. induction blk_instrs0. simpl in *. auto. simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb blk_id0 b2). destruct b. simpl in *. unfold block_entry. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_code0. simpl in *. eauto. simpl in *. eauto. auto. auto. Qed.




Lemma func_entry_pc_equiv : forall p0 i2, get_function_entry p0 i2 =  get_function_entry (prog_opt p0) i2.
Proof. intros. unfold get_function_entry. simpl in *. rewrite firstfunc. unfold endfunc. simpl in *.
destruct (get_cfg (list_cfg p0) i2). simpl in *. rewrite firstfunc1. simpl in *. unfold endfunc1. simpl in *. auto. destruct ( get_block (blk_instrs c) (init c)). unfold block_op. simpl in *. unfold block_entry. simpl in *. unfold blk_term_id in *. simpl in *. destruct b. simpl in *. destruct blk_term0. simpl in *. destruct blk_code0. simpl in *. auto. simpl in *. auto. auto. auto.  Qed.


Lemma term_equiv : forall  t e0 f p0 s0 ,
  eval_term p0 f t e0 s0 =
  eval_term (prog_opt p0) f t e0 s0.
Proof. intros. destruct t.
       +simpl in *. destruct (get_env e0 i). destruct e1. rewrite block_entry_pc_equiv. auto. destruct n. rewrite block_entry_pc_equiv. eauto. destruct n. rewrite block_entry_pc_equiv. eauto.  rewrite block_entry_pc_equiv. eauto.  rewrite block_entry_pc_equiv. eauto.  rewrite block_entry_pc_equiv. eauto.  auto.
       +simpl in *.  rewrite block_entry_pc_equiv. eauto.
       +simpl in *. auto.
Qed.
Hint Resolve term_equiv. Print In.
        
Lemma env_in : forall l  e1 i2, get_env l i2 = Some e1 -> In (i2, e1) l.
Proof. intro. induction l. intros. simpl in *. inversion H.
       +intros. simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb i i2). destruct b. apply beq_nat_eq in Heqb. subst. inversion H. subst. left.   auto. right.
apply IHl. auto. Qed.

Print Subset.

       
       Lemma get_cfg_implies :forall p0 c f,  Some c = get_cfg (list_cfg p0) f -> f = cfg_id c.
Proof. intro. destruct p0. simpl in *. induction list_cfg0.
       +simpl in *. intros. inversion H.
       +intros. simpl in *. destruct a. unfold get_cfg_id in *. simpl in *. remember (PeanoNat.Nat.eqb cfg_id0 f).    



destruct b. inversion H. destruct c. inversion H1. subst. apply beq_nat_eq in Heqb. subst. simpl in *. auto.




        apply IHlist_cfg0. auto.  Qed.



Lemma get_block_implies : forall blk_id0 blk_code0 i0 t c b,  Some {| blk_id := blk_id0; blk_code := blk_code0; blk_term := (i0, t) |} =
          get_block (blk_instrs c) b -> blk_id0 = b.
Proof. intros. destruct c. simpl in *. induction blk_instrs0.
       +simpl in *. inversion H.
       +simpl in *. unfold get_blk_id in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb blk_id1 b). destruct b0. apply beq_nat_eq in Heqb0. subst. inversion H. subst. auto. apply IHblk_instrs0. auto. Qed.



(*
Lemma tes3t12313: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> Some (Some a) = get1 n l1 -> Some (Some a) = get1 n l2.

*)
Print list_eq2.

Lemma beq_exp_eq : forall e0 e1, true = beq_exp e0 e1 -> e0 = e1.
Proof. intros. Admitted.




       
Lemma test12: forall l2 l1 n a ,  list_eq2 l1 l2 = true -> In (n, Some a) l1 -> In (n, a) l2.
Proof.

  induction l2. intros.
  +simpl in *. destruct l1. simpl in *. inversion H0. simpl in *. inversion H.
  +simpl in *. intros. induction l1. simpl in *. inversion H0. simpl in *. remember ( beq_pair1 a1 a). destruct b. simpl in *. inversion H0. left. unfold beq_pair1 in *. simpl in *. destruct a1. simpl in *. destruct a. simpl in *. destruct o. simpl in *. remember (PeanoNat.Nat.eqb i i0). destruct b. apply beq_nat_eq in Heqb0. subst. remember (beq_exp e0 e1).  destruct b. simpl in *. apply beq_exp_eq in Heqb0; subst. simpl in *. inversion H1. subst. eauto. simpl in *. inversion Heqb. simpl in *. inversion Heqb. simpl in *. inversion H1. simpl in *. eapply IHl2 in H; eauto. simpl in *. inversion H. Qed.



  

Print get_env.
    Lemma In_conv : forall l e1 i1, Some e1 = get_env l i1 -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i i1). destruct b. inversion H. subst. left. apply beq_nat_eq in Heqb. subst. auto. right. apply IHl. apply H. Qed.

    Lemma In_conv1 : forall l e1 i1, Some e1 = get_from_aenv l i1 -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i i1). destruct b. inversion H. subst. left. apply beq_nat_eq in Heqb. subst. auto. right. apply IHl. apply H. Qed.



Print list_eq2.
Print get_from_aenv.

Lemma test12313: forall l2 l1 n a ,  list_eq2 l1 l2 = true ->  (Some (Some a)) = get_from_aenv l1 n ->  In (n,  a) l2.
Proof. intros. eapply In_conv1 in H0. eapply test12; eauto. Qed.





Lemma list_in : forall l2 l1 a n,   list_eq2 l1 l2 = true ->  get_from_aenv l1 n = Some (Some a) ->  get_env l2 n = Some a.
Proof. induction l2.
       +simpl in *. intros. simpl in *. destruct l1. simpl in *. inversion H0. simpl in *. inversion H.
       +intros. generalize H; intros. eapply test12313 in H1; eauto. simpl in *. destruct a. simpl in *.
        inversion H1. inversion H2. rewrite PeanoNat.Nat.eqb_refl. eauto. simpl in *.




induction l1. simpl in *. inversion H0. simpl in *. unfold beq_pair1 in H. simpl in *. destruct a. simpl in *.  destruct o. simpl in *.
remember (PeanoNat.Nat.eqb i0 i). destruct b. simpl in *. remember ( beq_exp e0 e1). destruct b. simpl in *. remember ( PeanoNat.Nat.eqb i0 n). destruct b. simpl in *.




remember ( PeanoNat.Nat.eqb i n ). destruct b. eapply beq_nat_eq in Heqb1. subst. inversion H0. subst. apply  beq_exp_eq in Heqb0. subst. auto. inversion H0. subst.
eapply beq_nat_eq in Heqb. subst. eapply beq_exp_eq in Heqb0. subst. eapply beq_nat_eq in Heqb1. subst. 
rewrite PeanoNat.Nat.eqb_refl in Heqb2. inversion Heqb2.


eapply beq_nat_eq in Heqb. apply beq_exp_eq in Heqb0. subst. simpl in *.
remember (PeanoNat.Nat.eqb i n). destruct b. inversion Heqb1. eapply IHl2; eauto. simpl in *. inversion H. simpl in *. inversion H. simpl in *.


remember ( PeanoNat.Nat.eqb i0 i ). destruct b. simpl in *. eapply beq_nat_eq in Heqb. subst. 
remember ( PeanoNat.Nat.eqb i n). destruct b. inversion H0. eapply IHl2; eauto. simpl in *. inversion H. Qed.






        
Lemma stepD_equiv : forall p s, sound_state p s -> StepD p s = StepD (prog_opt p) s.
Proof. intros. unfold StepD. destruct s0. destruct p1. destruct p1. simpl in *. unfold fetch. unfold incr_pc.  simpl in *. unfold fn_id_of in *. simpl in *.
       rewrite firstfunc. unfold endfunc. simpl in *.  remember ( get_cfg (list_cfg p0) f). destruct o; simpl in *; eauto. unfold blk_id_of in *; simpl in *.
    rewrite firstfunc1. unfold endfunc1. simpl in *. remember ( get_block (blk_instrs c) b). destruct o; simpl in *; eauto. simpl in *. unfold block_to_cmd in *. unfold blk_term_id in *.  simpl in *. destruct b0. simpl in *. unfold blk_term_instr in *. simpl in *. destruct blk_term0. simpl in *.
    remember ( PeanoNat.Nat.eqb i0 i).  destruct b0; simpl in *; eauto.



    rewrite firstfunc2. unfold endfunc2. simpl in *. destruct ( find_instr blk_code0 i i0); eauto. destruct p1. simpl in *. destruct c0.  eauto. destruct o.



    unfold eval_ins. simpl in *. destruct e1.
       +destruct e1.
       -simpl in *. unfold constant_prop_exp. simpl in *. inversion H; subst. unfold sound_env in senv. simpl in *.

generalize Heqo; intros. apply get_cfg_implies in Heqo1. subst.
generalize Heqo0; intros. apply get_block_implies in Heqo1. subst.
remember (prep_selected_block p0 (cfg_id c, b, i)). destruct o.
specialize (senv l). assert (Some l = Some l) by auto. apply senv in H0. Print In. remember ( get_from_aenv (value_analysis l i) i2). destruct o. symmetry in Heqo2.




unfold Subset in H0. destruct o. eapply list_in in H0; eauto. rewrite H0. simpl in *. destruct e1; simpl in *; try rewrite H0; eauto. simpl in *.  eauto. simpl in *. eauto. simpl in *. eauto.


       -simpl in *. unfold constant_prop_exp. unfold prep_selected_block. simpl in *. destruct p0. unfold fn_id_of in *. simpl in *.
        destruct (get_cfg list_cfg0 (cfg_id c)). unfold blk_id_of in *. simpl in *. destruct (get_block (blk_instrs c0) blk_id0). simpl in *. auto. simpl in *. eauto. simpl in *. auto.
       -simpl in *. unfold constant_prop_exp. simpl in *. unfold prep_selected_block. simpl in *. unfold fn_id_of in *. simpl in *. destruct ( get_cfg (list_cfg p0) (cfg_id c)). unfold blk_id_of in *. simpl in *. destruct ( get_block (blk_instrs c0) blk_id0). simpl in *. eauto. simpl in *. eauto. simpl in *. eauto.
       -unfold constant_prop_exp. simpl in *. unfold prep_selected_block. simpl in *. unfold fn_id_of in *. simpl in *. destruct ( get_cfg (list_cfg p0) (cfg_id c)). unfold blk_id_of in *. simpl in *. destruct (get_block (blk_instrs c0) blk_id0 ). simpl in *. auto. simpl in *. auto. simpl in *. auto.
        +simpl in *. unfold constant_prop_exp. simpl in *. unfold prep_selected_block. simpl in *. unfold blk_id_of in *. simpl in *. unfold fn_id_of in *. simpl in *. destruct (get_cfg (list_cfg p0) (cfg_id c)). destruct ( get_block (blk_instrs c0) blk_id0).

         rewrite <- func_entry_pc_equiv. eauto. rewrite <- func_entry_pc_equiv. eauto. rewrite <- func_entry_pc_equiv. auto.
        +auto. Qed.







Definition unroll (t:Trace state) :=
  match t with
  | Vis _ b => Vis state b
  | Tau _ b c => Tau state b c
                     
  end.
    

Lemma trace_equiv_opt : forall st p,   (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state p st -> trace_equiv (sem p st) (sem (prog_opt p) st).
Proof. pcofix CIH. intros. pfold.


       assert (    (sem p0 st) = unroll     (sem p0 st)). destruct     (sem p0 st); eauto. rewrite H; clear H.
       assert ( (sem (prog_opt p0) st) = unroll  (sem (prog_opt p0) st)). destruct  (sem (prog_opt p0) st); eauto. rewrite H; clear H. simpl in *. generalize H1; intros. eapply stepD_equiv in H1. rewrite <- H1. remember (StepD p0 st). destruct t.
       
 eapply step_preserves_state  in H2; eauto. constructor. right. generalize H2. apply CIH.  eauto. destruct m; constructor; constructor; eauto. Qed.                                                                                                