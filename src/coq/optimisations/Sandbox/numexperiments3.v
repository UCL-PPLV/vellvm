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

(*Defining an expression as an identifier (AIdent), a number (Anum) or APlus*)
Inductive exp : Type :=
  | AIdent : instr_id -> exp
  | ANum : nat -> exp
  | APlus : exp -> exp -> exp
.

(*A program counter simply points to the current instruction*)
Definition pc := instr_id.

(*Maps an instr_id to an expression*)
Definition env := list (instr_id * exp).


(*State comprising of env and a pc*)
Record state := mkState {e : env; p : pc}.

(*Programs consist of a sequence of instructions followed by a return terminator value*)
Record program := mkProgram {prog_code : list (instr_id*exp); term : (instr_id*instr_id)}.

(*Helper function which retrieves an expression from the env*)
Fixpoint get_env (s:env) (i:instr_id) :  exp :=
  match s with
  | nil =>  (AIdent i)
  | (iis, ins)::tl => if beq_nat iis i then  ins else get_env tl i
  end.

(*Helper function: adds a variable binding*)
Definition add_env (s:env) (i:instr_id) (v:exp) := (i, v) :: s.


(*A command is either a terminator or an expression*)
Inductive cmd :=
| Term (i:instr_id)
| Step_cmd (e:exp)
.


Definition get_program_term_id (p:program) := fst (term p).


Definition fallthrough (cd:list (instr_id*exp)) (t:instr_id) :=
  match cd with
  | nil => t
  | hd :: _ => fst hd
  end.


Print cmd.


Fixpoint find_instr (l:list (instr_id * exp)) (i t:nat)  :=
  match l with
  | nil => None
  | hd :: tl => if (beq_nat (fst hd) i) then Some (Step_cmd (snd hd), Some (fallthrough tl t)) else find_instr tl i t
  end.



Definition program_to_cmd (p:program) (i:instr_id) : option (cmd * option instr_id) :=
  if beq_nat (get_program_term_id p) i then Some (Term (snd (term p)), None) else find_instr (prog_code p) i (get_program_term_id p).


Definition fetch (l:program) (i:nat) :=
  match program_to_cmd l i with
  | Some (t, _) => Some t
  | _ => None
  end.


Definition incr_pc (l:program) (i:nat) :=
  match program_to_cmd l i  with
  | Some (_, a) =>  a
  | _ => None
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



(*Evaluates an expression*)
Fixpoint eval_exp (i:exp) (s:env) :  exp :=
  match i with
  | AIdent a =>  (get_env s a)
  | ANum a =>  (ANum a)
  | APlus a b => match (eval_exp a s), (eval_exp b s) with
                 | ( (ANum a1)), ( (ANum b1)) =>  (ANum (a1 + b1))
                 |  c,  d =>  (APlus c d)
                 end
  end
.

(*Evaluates an instruction*)
Definition StepD (p:program) (s:state) : transition state :=
  let (e, pc) := s in
  match program_to_cmd p pc with
  | Some (Step_cmd ins, Some next_pc) => Step state (mkState ((pc, ( eval_exp ins e)) :: e) next_pc)
  | Some (Term a,None) => Obs state (Fin (get_env e a))
  | _ => Obs state Err
  end.



CoInductive Trace X :=
| Vis (v : Event)
| Tau (s:X) (k : Trace X)
.



CoFixpoint sem (p:program) (s:state) : Trace state :=
  match StepD p s with
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



Definition areg : Set := (instr_id * exp).
Definition aenv : Set := list areg.



Definition map_exp_to_cmd (e:instr_id * exp)  := (fst e, Step_cmd (snd e)).
Definition map_term_to_cmd (t: (instr_id*instr_id)) := cons (fst t, Term (snd t)) nil.
Definition prep_prog (p:program) :=  map map_exp_to_cmd (prog_code p) ++ map_term_to_cmd (term p).


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

Print aenv.

Print get_env.

(*STATIC EVAL*)

Fixpoint get_from_aenv (l:aenv)  (i:nat) :=
  match l with
  | nil =>  (AIdent i)
  | (iis, ins) :: tl => if beq_nat iis i then  (ins) else get_from_aenv tl i
  end.
Print areg.
Print cmd.
Print exp.
Print cmd. Print aenv. Print areg. Print eval_exp.
Definition transfer (a:aenv) (i:instr_id * cmd) : aenv :=
  match snd i with
  | Term t =>  a
  | Step_cmd (ANum t) => (fst i, (ANum t)) :: a
  | Step_cmd (APlus t t1) => (fst i, eval_exp (APlus t t1) a):: a
  | Step_cmd (AIdent t) => (fst i, get_from_aenv a t) :: a
  end.


Print transfer.


Print aenv.




Fixpoint value_analysis_fix (acc:aenv) l (i:nat)  :=
  match l with
  | nil => nil
  | hd :: tl => if beq_nat (fst hd) i then acc else (value_analysis_fix (transfer acc hd) tl i)
  end.



Definition value_analysis l (i:nat) := value_analysis_fix nil l i.


Print prep_prog.


Print areg.

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




Print prep_prog.


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

  Lemma incr_pc_implies2 : forall prog i i1 t,  NoDup (map fst (prep_prog prog)) ->  program_to_cmd prog i =  Some (i1, Some t) ->  find_in_newlist (prep_prog prog) i = Some (i1, Some t).

  Proof. intros. unfold program_to_cmd in *. simpl in *. unfold get_program_term_id in *. simpl in *. destruct prog. simpl in *.
         destruct term0. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. eapply beq_nat_eq in Heqb. subst. simpl in *. inversion H0. simpl in *. induction prog_code0. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i3 i). destruct b. eapply beq_nat_eq in Heqb0. subst. simpl in *. inversion H0. subst. simpl in *. destruct prog_code0.  simpl in *.

 eauto. simpl in *. eauto.
 eapply IHprog_code0; eauto. inversion H; subst; eauto. Qed.







Lemma map_prog : forall prog_code0, ((map fst (map map_exp_to_cmd prog_code0)) = (map fst prog_code0)).
Proof. induction prog_code0; simpl in *; eauto.
       inversion IHprog_code0. auto. Qed.

                                                                                                                                              
Lemma get_prog_id : forall prog, NoDup ((map fst (prog_code prog)) ++ (get_program_term_id prog ) :: nil) ->
                                 NoDup (map fst (prep_prog prog)).
Proof. intros. unfold prep_prog. unfold get_program_term_id in *. simpl in *. destruct prog. simpl in *.
       induction prog_code0. simpl in *. auto. simpl in *. inversion H. simpl in *. subst. eapply IHprog_code0 in H3. simpl in *. unfold not in H2. constructor; eauto. unfold not. simpl in *. destruct a. simpl in *.
intros.
assert (fst term0 :: nil =  map fst (map_term_to_cmd term0)).
destruct term0. simpl in *. auto. rewrite map_app in H3. rewrite map_app in H0. rewrite map_app in IHprog_code0. rewrite <- H1 in H0. rewrite <- H1 in H3.  rewrite <- H1 in IHprog_code0. rewrite map_prog in IHprog_code0.
rewrite map_prog in H3. rewrite map_prog in H0. clear H1. eauto. Qed.

       


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
Print testtest.

Print cmd.


Print value_analysis.
 Lemma testtest1 : forall prog hd i i1 t r tl, NoDup (map fst  (prep_prog prog)) ->  (prep_prog prog) = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl  -> value_analysis  (prep_prog prog) t = transfer (value_analysis  (prep_prog prog) i) (i, i1).

 Proof. intros. unfold value_analysis. simpl in *. eapply testtest in H; simpl in *; eauto. Qed.

 Lemma testtest2 : forall prog i i1 t, NoDup ((map fst (prog_code prog)) ++ (get_program_term_id prog ) :: nil) -> program_to_cmd prog i =  Some (i1, Some t)  ->  value_analysis  (prep_prog prog) t = transfer (value_analysis  (prep_prog prog) i) (i, i1).
 Proof. intros. assert (H' := H). eapply get_prog_id in H.   assert (H'' := H).   assert (H''' := H). 
        eapply  incr_pc_implies2 in H; eauto. eapply incr_pc_implies1 in H''; eauto.
inversion H''. inversion H1. inversion H2. subst. eapply testtest in H'''; eauto. Qed.


   
Lemma test5 : forall prog i i1 t head,  NoDup ((map fst (prog_code prog)) ++ (get_program_term_id prog :: nil)) ->
                                        program_to_cmd prog i = Some (t, Some i1) ->
                                        value_analysis (prep_prog prog) i = head  ->
                                        value_analysis (prep_prog prog) (i1) = transfer head (i, t).
Proof. intros. eapply testtest2 in H; eauto. rewrite <- H1; eauto.
Qed.


Print value_analysis.
Print value_analysis_fix.
Print transfer.

Print env.
Print areg.


Fixpoint compare_lists (a b: list nat) :=
  match a, b with
  | nil, nil => true
  | hd::tl, hd1::tl1 => beq_nat hd hd1 && compare_lists tl tl1
  | _, _ => false
  end.

                                                        
(*

Lemma match_sym : forall e1 e2, value_match e2 e1 = true <->  value_match e1 e2 = true.

Proof.
  intros. destruct e1, e2; simpl in *; split; intros; inversion H; try rewrite PeanoNat.Nat.eqb_sym; eauto.
  Qed.

Print value_match_eq.

Fixpoint eq_list (l1 l2: list nat) :=
  match l1, l2 with
  | nil, nil => true
  | hd :: tl, hd1 :: tl1 => beq_nat hd hd1 && eq_list tl tl1
  | _, _ => false
  end.
*)



                               
Inductive sound_state : program -> state  -> Prop :=
| sound_state_intro:
    forall st prog
           (env:  (value_analysis (prep_prog prog) (p st)) = (e st)), sound_state prog st.
                             
Print get_from_aenv.
Lemma get_aenv_env_equiv : get_from_aenv = get_env.
  Proof. repeat (apply functional_extensionality; intros). induction x; simpl; eauto. Qed.


                                                         
       
Lemma step_preserves_soundness : forall p st st1,
     NoDup ((map fst (prog_code p)) ++ (get_program_term_id p ) :: nil)  -> sound_state p st -> StepD p st = Step state st1 -> sound_state p st1.
Proof. intros. constructor. inversion H0; subst. remember  (value_analysis (prep_prog p0) (p st)) . unfold StepD in H1. destruct st, st1. remember ( program_to_cmd p0 p1). generalize Heqo; intro. symmetry in Heqo. destruct o. destruct p3. simpl in *. destruct o. eapply test5 in Heqo; eauto; subst.
       +destruct c. inversion H1. simpl in *. simpl in *.






        remember ( eval_exp e0 (value_analysis (prep_prog p0) p1)). inversion H1. subst. rewrite Heqo. simpl in *. unfold transfer. simpl in *. destruct e0. simpl in *. eauto. simpl in *. eauto. simpl. eauto.
       +destruct c; inversion Heqo.
        inversion H1. inversion H1.
        +inversion H1. Qed.


Print get_from_aenv.
Print exp.
Definition constant_prop_exp (prog:program) (i:instr_id*exp) :=
  let a :=  (value_analysis (prep_prog prog) (fst i)) in
  match snd i with
  | AIdent ident => match (get_from_aenv a ident) with
                    | ANum a =>(fst i, ANum a)
                    | _ => i
                             
                      end

  | APlus a b => i
  | ANum a => i    
  end.

    
                  


Print constant_prop_exp. Print program.
Definition map_program (prog:program) (opt : instr_id*exp -> instr_id*exp) := mkProgram (map opt (prog_code prog)) (term prog).


Definition unroll (t:Trace state) :=
  match t with
  | Vis _ b => Vis state b
  | Tau _ b c => Tau state b c
  end.

Lemma trace_equiv_refl: forall st prog,   NoDup
    (map fst (prog_code prog) ++
     get_program_term_id prog :: nil) -> sound_state prog st -> trace_equiv (sem prog st) (sem prog st).
Proof. pcofix CIH. simpl in *. intros. pfold. assert ( (sem prog st) = unroll  (sem prog st)). destruct (sem prog st); eauto. rewrite H; clear H. simpl in *. remember (StepD prog st). destruct t. generalize H0; intro.  eapply step_preserves_soundness in H0; eauto. constructor. right. apply CIH; eauto. simpl in *. destruct m. constructor. constructor. auto. constructor. constructor. Qed.

Ltac duplicate X := generalize X; intro.




Definition second p0 prog := (find_instr (prog_code prog) p0 (fst (term prog))).


Definition test p0 prog :=
  match second p0 prog with
  | None => None
  | Some (Step_cmd a, rest) => Some (Step_cmd (snd (constant_prop_exp prog (p0, a))), rest)
  | a => a

           
           
  end.



Lemma test123 : forall p0 prog, find_instr
           (map (constant_prop_exp prog) (prog_code prog)) p0
           (fst (term prog)) = test p0 prog.
  intros. unfold test. simpl in *. unfold second. simpl in *. unfold constant_prop_exp. simpl in *. generalize ( (prep_prog prog)). intros. induction prog. simpl in *. induction prog_code0. simpl in *. auto. simpl in *. destruct a. simpl in *. destruct e0. simpl in *. remember (get_from_aenv (value_analysis l i) i0).
  +simpl in *. remember (PeanoNat.Nat.eqb i p0). destruct b. apply beq_nat_eq in Heqb. subst. simpl in *. destruct prog_code0; simpl in *; eauto. remember ( get_from_aenv (value_analysis l p0) i0). destruct e0. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto.  simpl. rewrite PeanoNat.Nat.eqb_refl. eauto. destruct ( get_from_aenv (value_analysis l p0) i0); simpl in *; eauto.
  rewrite PeanoNat.Nat.eqb_refl. destruct p1. simpl in *. destruct e0. simpl in *. destruct ( get_from_aenv (value_analysis l i1) i2); simpl in *; eauto. simpl in *; eauto.  simpl in *; eauto. 

 rewrite PeanoNat.Nat.eqb_refl.  destruct p1. simpl in *.  destruct e0. simpl in *.
destruct ( get_from_aenv (value_analysis l i) i1); simpl in *; eauto. simpl in *. eauto. simpl in *. eauto. 

rewrite PeanoNat.Nat.eqb_refl.  destruct p1; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct ( get_from_aenv (value_analysis l i) i1); simpl in *; eauto. destruct e0; simpl in *; eauto. remember ( PeanoNat.Nat.eqb i p0). destruct b. inversion Heqb. eauto. simpl in *. rewrite <- Heqb. eauto. rewrite <- Heqb. eauto.
+simpl in *. remember (PeanoNat.Nat.eqb i p0). destruct b. eapply beq_nat_eq in Heqb. subst. simpl in *. destruct prog_code0. simpl in *. eauto. simpl in *. destruct p1; simpl in *; eauto. destruct e0; simpl in *; eauto.
 destruct ( get_from_aenv (value_analysis l i) i0); simpl in *; eauto. eauto.
 +simpl in *. remember (PeanoNat.Nat.eqb i p0). destruct b. eapply beq_nat_eq in Heqb. subst. simpl in *. destruct prog_code0. simpl in *. eauto. simpl in *. destruct p1; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct ( get_from_aenv (value_analysis l i) i0); simpl in *; eauto. eauto. Qed.
   

Lemma testhelp :  forall a prog_code0 term0,     (fst
         (constant_prop_exp
            {| prog_code := a :: prog_code0; term := term0 |} a)) = fst a.
Proof. intros. destruct a. simpl in *. unfold constant_prop_exp. simpl in *. destruct e0; simpl in * ; eauto.
simpl in *. destruct (      get_from_aenv
        (value_analysis
           (prep_prog
              {| prog_code := (i, AIdent i0) :: prog_code0; term := term0 |}) i)
        i0); simpl in *; eauto.         
Qed.
Lemma stepD_equiv : forall a b prog st,

        sound_state prog st ->  NoDup
         (map fst (prog_code prog) ++
              get_program_term_id prog :: nil) ->  StepD (map_program prog (constant_prop_exp prog)) st = a ->  StepD prog st = b -> a = b.
  Proof. intros. unfold StepD in *. simpl in *. unfold program_to_cmd in *. simpl in *. unfold get_program_term_id in *.
         simpl in *. destruct st. simpl in *. destruct (PeanoNat.Nat.eqb (fst (term prog)) p0). destruct ( get_env e0 (snd (term prog))).
         subst. auto. subst. auto. simpl in *. subst. auto. simpl in *.
         rewrite test123 in H1. unfold test in *. unfold second in *. simpl in *. destruct ( find_instr (prog_code prog) p0 (fst (term prog))); subst; simpl in *; eauto. simpl in *. destruct p1. simpl in *. destruct c; simpl in *; subst; eauto; destruct 0; simpl in *; eauto.
         *unfold constant_prop_exp; simpl in *; eauto. inversion H. subst. simpl in *. destruct e1. simpl in *. rewrite env0. rewrite  get_aenv_env_equiv. remember (get_env e0 i0). destruct e1. simpl in *. rewrite Heqe1. auto. simpl in *. eauto. simpl in *. rewrite Heqe1. simpl in *. eauto. simpl in *. eauto. simpl in *. eauto.
          Qed.

                              
Lemma trace_equiv_constprop : forall st prog,   NoDup
    (map fst (prog_code prog) ++
     get_program_term_id prog :: nil) -> sound_state prog st -> trace_equiv (sem (map_program prog (constant_prop_exp prog)) st) (sem prog st).
Proof. pcofix CIH. simpl in *. intros. pfold. simpl in *.  simpl in *.
       assert (  (sem (map_program prog (constant_prop_exp prog)) st) = unroll   (sem (map_program prog (constant_prop_exp prog)) st)). destruct   (sem (map_program prog (constant_prop_exp prog)) st); eauto. rewrite H; clear H. simpl in *.



       duplicate H1.  duplicate H0.

       assert ((sem prog st) = unroll (sem prog st)). destruct (sem prog st); eauto. rewrite H; clear H. simpl in *.

       remember ( StepD prog st). remember (StepD (map_program prog (constant_prop_exp prog)) st). duplicate Heqt. duplicate Heqt0. simpl in *. eapply stepD_equiv in H1; eauto. rewrite Heqt0. rewrite Heqt1. rewrite H1. destruct t. simpl in *. eapply step_preserves_soundness in H0; eauto. subst. rewrite <- Heqt. constructor. right. generalize H0.  generalize H3. apply CIH. rewrite <- Heqt1. destruct m; constructor; constructor; eauto. Qed.






Definition print_out_prog (prog:program) := (map_program prog (constant_prop_exp prog)).

Print program.


Definition first_line : (instr_id * exp) := (1, ANum 0).
Definition second_line : (instr_id * exp) := (2, AIdent 1).
Definition third_line : (instr_id * exp) := (3, APlus (ANum 10) (ANum 10)).
Definition fourth_line : (instr_id * exp) := (4, AIdent 2).
Definition fifth_line : (instr_id * exp) := (5, AIdent 3).

Definition term_line : (instr_id * instr_id) := (6, 2).

Definition code := cons first_line (cons second_line (cons third_line (cons fourth_line (cons fifth_line nil)))).
Definition prog := mkProgram code term_line.


Eval compute in print_out_prog prog.
Print beq_nat.




Fixpoint eq_list (a b: list nat) :=
  match a, b with
  | nil, nil => true
  | hd :: tl, hd1 :: tl1 => beq_nat hd hd1 && eq_list tl tl1
  | _, _ => false
  end.



Lemma test123123 : forall a b, eq_list a b = true -> a = b.
Proof. intros. generalize dependent b. induction a; intros; induction b; simpl in *; eauto; inversion H.
       +remember (PeanoNat.Nat.eqb a a1). destruct b0. apply beq_nat_eq in Heqb0. simpl in *. auto.  subst. 
        assert (a0 = b ->  a1 :: a0 = a1 :: b). intros. rewrite H0. auto. apply H0. apply IHa. auto.
        simpl in *. inversion H.
Qed.



Print In.

  Definition Subset s s' := forall a : nat, In a s -> In a s'.
  Print Subset.




  Lemma test1231323 : forall l1 l2 a,  Subset l1 l2 -> In a l1 -> In a l2.
    Proof. intros. unfold Subset in H. simpl in *. apply H in H0. auto. Qed.