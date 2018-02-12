From Paco
Require Import paco.

Require Import Ascii String Bool.
Require Import Coq.Strings.String.
Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Permutation.

(*Defining an instruction id as a nat*)

Definition instr_id := nat.

(*Defining an expression as an identifier (AIdent), a number (Anum) or APlus*)
Inductive exp : Type :=
  | AIdent : instr_id -> exp
  | ANum : nat -> exp
(*  | APlus : exp -> exp -> exp *)
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
Fixpoint get_env (s:env) (i:instr_id) : option exp :=
  match s with
  | nil => None
  | (iis, ins)::tl => if beq_nat iis i then Some ins else get_env tl i
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
Fixpoint eval_exp (i:exp) (s:env) : option exp :=
  match i with
  | AIdent a => get_env s a
  | ANum a => Some (ANum a)
(*  | APlus a b => match (eval_exp a s), (eval_exp b s) with
                 | (Some (ANum a1)), (Some (ANum b1)) => Some (ANum (a1 + b1))
                 | _, _ => None
                 end*)
  end
.

(*Evaluates an instruction*)
Definition StepD (p:program) (s:state) : transition state :=
  let (e, pc) := s in
  match program_to_cmd p pc with
  | Some (Step_cmd ins, Some next_pc) => match eval_exp ins e with
                                         | Some res => Step state (mkState (e ++ cons (pc, res) nil) next_pc)
                                         | None => Obs state (Err)
                                         end
  | Some (Term a,None) => match get_env e a with
                       | Some fin => Obs state (Fin fin)
                       | None => Obs state (Err)                                  
                       end
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
         constructor. apply LE. apply HRk. Admitted.
  Hint Resolve related_event_step_monotone : paco.


  Definition trace_equiv {X} (p q: Trace X) := paco2 (@trace_equiv_step X) bot2 p q.
  Hint Unfold trace_equiv.







(*static analysis*)



Definition areg : Set := (instr_id * cmd).
Definition aenv : Set := list areg.



Definition map_exp_to_cmd (e:instr_id * exp) : areg := (fst e, Step_cmd (snd e)).
Definition map_term_to_cmd (t: (instr_id*instr_id)) := cons (fst t, Term (snd t)) nil.
Definition prep_prog (p:program) : aenv := map map_exp_to_cmd (prog_code p) ++ map_term_to_cmd (term p).


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

Fixpoint calculate_previous1 (l:aenv) (i:nat) : aenv :=
  match l with
  | nil => nil
  | cons hd tl => if beq_nat (fst hd) i then nil else cons hd  (calculate_previous1 tl i)
  end.

Lemma test21 : forall l i i1 t1, find_tuple l i = Some i1 -> increase_tuple l i = Some t1 -> list_to_tuple l i = Some (i1, Some t1).
Proof. intros. unfold find_tuple in *. unfold increase_tuple in *. destruct ( list_to_tuple l i). simpl in *. destruct p0. simpl in *. inversion H. subst. destruct o. simpl in *. inversion H0. eauto. inversion H0. inversion H0. Qed.

(*
Lemma test_second : forall l i i1, find_tuple l i = Some i1 ->
                            exists tl, l = (calculate_previous1 l i) ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple in *. simpl in *. induction l; simpl in *.
       +inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i0 i).
        simpl in *. destruct b. simpl in *.  inversion H. subst. apply beq_nat_eq in Heqb. subst. eauto. simpl in *. apply IHl in H. inversion H. exists x. rewrite <- H0. eauto.
Qed.

**)


       Lemma test51 : forall n1 (A:aenv) n2 x0, In n1 (map fst (A ++ (n1, n2) :: x0)).
       Proof. intros. induction A. simpl in *. left. eauto. simpl. right. eauto. Qed.
              



Lemma test61: forall t1 A x0, NoDup (map fst (A ++ (cons t1 nil) ++ x0)) -> 

calculate_previous1 (A ++ (cons t1 nil) ++ x0) (fst t1) = A.
Proof. intros. induction A. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto. simpl in *. destruct a, t1. simpl in *. remember  (PeanoNat.Nat.eqb i i0). destruct b. simpl in *. apply beq_nat_eq in Heqb. subst. inversion H. subst. contradiction H2. apply test51. 
(assert ((calculate_previous1 (A ++ (i0, c0) :: x0) i0 = A)  -> ((i, c)
  :: calculate_previous1 (A ++ (i0, c0) :: x0) i0 =
  (i, c) :: A ))). intros. rewrite H0. eauto. apply H0; apply IHA. inversion H; subst; eauto. Qed.




Lemma test91: forall x l i i1 t1, NoDup (map fst l) -> list_to_tuple l i = Some (i1,Some t1) ->

                                  l = calculate_previous1 l i ++ (i, i1) :: x ->
                                  exists tl r, x = cons (t1, r) tl.
Proof. intros.  induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *. 



remember ( PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. simpl in *. inversion H1. subst. inversion H0. subst. destruct x. simpl in *. inversion H3. simpl in *. inversion H3. subst. destruct p0. simpl in *. exists x. exists c. eauto. eapply IHl.
       +inversion H. subst. eauto.
       +simpl in *. inversion H1. simpl in *. rewrite <- H3. eauto.
       +inversion H1. rewrite <- H3. eauto. Qed. 




Lemma test111: forall l i i1 t1 head, NoDup (map fst l) -> find_tuple l i = Some i1 -> increase_tuple l i = Some t1 ->

 list_to_tuple l i = Some (i1, Some t1) -> calculate_previous1 l i = head  -> 


calculate_previous1 l (t1) = calculate_previous1 l i ++ (cons (i, i1) nil).

Proof. intros. generalize H. intro. (* apply test_second in H0. rewrite H3. simpl in *. inversion H0.

eapply test91 in H; eauto. rewrite H5.  inversion H. inversion H6. rewrite H7. simpl in *. rewrite H3.
rewrite H7 in H5. rewrite H5 in H4. simpl in *. 



       assert ((head++ (i, i1) :: (t1, x1) :: x0) = ((head ++ (i, i1) :: nil) ++ (cons (t1,x1) nil) ++ x0)).
simpl in *. rewrite <- app_assoc. simpl in *. eauto. rewrite H8. simpl in *. remember ((head ++ (i, i1) :: nil)). eapply test61.
subst. simpl in *. eauto. rewrite <- app_assoc. simpl in *. eauto. Qed.

*) Admitted.




Lemma test121: forall l i i1 t1 head, NoDup (map fst l) -> find_tuple l i = Some i1 -> increase_tuple l i = Some t1 ->

                                      calculate_previous1 l i = head  ->
                                      calculate_previous1 l (t1) = calculate_previous1 l i ++ (cons (i, i1) nil).
Proof. intros. eapply test111 in H; eauto. eapply test21; eauto. Qed.



Lemma test : forall prog i i1, NoDup((get_program_term_id prog) :: (map fst (prog_code prog))) -> find_tuple (prep_prog prog) i = Some i1 -> fetch prog i = Some i1.
Proof. intros. unfold get_program_term_id in *.  destruct prog. simpl in *. unfold fetch. unfold program_to_cmd. simpl in *. unfold get_program_term_id. simpl in *. destruct term0. simpl in *. unfold find_tuple in *. simpl in *. simpl in *. unfold prep_prog in *. simpl in *. unfold map_term_to_cmd in *. simpl in *.  remember ( PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. 


       subst. induction prog_code0. simpl in *. rewrite PeanoNat.Nat.eqb_refl in *. eauto.

       simpl in *. destruct a. simpl in *. eapply IHprog_code0. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. inversion H. subst. contradiction H3. simpl. left. eauto. simpl in *. eapply H0. inversion H. subst. 

       admit. simpl in *.


       induction prog_code0. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b. inversion Heqb. inversion H0. simpl in *. destruct a. simpl in *. destruct (PeanoNat.Nat.eqb i3 i). eauto.
       eapply IHprog_code0; eauto. inversion H. subst. 

       admit. Admitted.



Lemma test1 : forall prog i t, NoDup ((get_program_term_id prog ) :: (map fst (prog_code prog))) -> fetch prog i = Some t -> find_tuple (prep_prog prog) i = Some t.
Proof. intros. unfold get_program_term_id in *. simpl in *. unfold fetch in *. unfold program_to_cmd in *. unfold get_program_term_id in *. unfold find_tuple in *. destruct prog. simpl in *. destruct term0. simpl in *.
       induction prog_code0. simpl in *.
       +remember (PeanoNat.Nat.eqb i0 i). destruct b. eauto. eauto.
       +simpl in *. destruct a. simpl in *. remember (PeanoNat.Nat.eqb i2 i). destruct b. simpl in *. eapply beq_nat_eq in Heqb. subst. remember (PeanoNat.Nat.eqb i0 i). destruct b. apply beq_nat_eq in Heqb. subst. inversion H; subst. contradiction H3. simpl. left. auto. auto. eapply IHprog_code0.
clear IHprog_code0. clear H0. clear Heqb. inversion H. subst. inversion H3. subst. unfold not in *. simpl in *. constructor. unfold not. intros. apply H2. right. auto. auto.


        eauto.  Qed.

Print incr_pc.


Lemma test2 : forall prog i i1, NoDup((get_program_term_id prog) :: (map fst (prog_code prog))) ->  incr_pc prog i = Some i1 -> increase_tuple (prep_prog prog) i = Some i1.
Proof. intros.  unfold increase_tuple in *. unfold incr_pc in *. unfold program_to_cmd in *. unfold get_program_term_id in *. simpl in *. destruct prog. simpl in *. destruct term0. simpl in *. remember (PeanoNat.Nat.eqb i0 i). destruct b. inversion H0. simpl in *.
       induction prog_code0. simpl in *. inversion H0. unfold prep_prog. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i3 i). destruct b. unfold aenv_fallthrough. simpl in *. eapply beq_nat_eq in Heqb0.

       induction prog_code0. simpl in *. eauto. simpl in *. destruct a. simpl in *. subst. eauto.

       unfold prep_prog in *. simpl in *. eapply IHprog_code0; eauto. inversion H.  subst. unfold not in H3. apply NoDup_cons_iff in H. unfold not in H. destruct H. constructor. simpl in *. unfold not.  intros. apply H3. right. eauto. inversion H4. subst. auto. Qed.
                                                                                                                                                                                         



Lemma test3 : forall prog,   NoDup ((get_program_term_id prog ) :: (map fst (prog_code prog))) ->  NoDup (map fst (prep_prog prog)).
Proof. intros. destruct prog. simpl in *. unfold get_program_term_id in *.  simpl in *. unfold prep_prog. unfold map_term_to_cmd. simpl in *. destruct term0. simpl in *. induction prog_code0; simpl in *; eauto.
       +  Admitted.


Lemma test4 : forall prog i i1 t head,  NoDup ((get_program_term_id prog ) :: (map fst (prog_code prog))) ->
                                        incr_pc prog i = Some i1 ->
                                        fetch prog i = Some t ->
    calculate_previous1 (prep_prog prog) i = head  ->
    calculate_previous1 (prep_prog prog) (i1) = calculate_previous1 (prep_prog prog) i ++ (cons (i, t) nil).                     Proof. intros. generalize H. intros. apply test3 in H3. generalize H; intros.  eapply test2 in H; eauto.            (*increase_tuple*)

                                                                                                                                        eapply test1 in H4; eauto. eapply test121 in H3; eauto. Qed.




Definition value_match (e:exp) (c:cmd) : bool :=
  match e, c with
  | AIdent a, Step_cmd (AIdent b) => beq_nat a b
  | ANum a, Step_cmd (ANum b) => beq_nat a b
  | _, _ => false
  end.



Fixpoint match_aenv_env (a:areg) (e:instr_id * exp) : bool :=
  match a, e with
    | (id1, val1), (id2, val2) => if beq_nat id1 id2 then value_match val2 val1 else false
  end.


Print calculate_previous1.


Fixpoint match_lists (a:aenv) (e:env) :=
  match a, e with
  | nil, nil => true
  | (hd1::tl1), (hd2::tl2) => match_aenv_env hd1 hd2 && match_lists tl1 tl2
  | _, _ => false
  end.


Lemma helper : forall A B C D, match_lists A C = true /\ match_lists B D = true ->  match_lists (A ++ B) (C ++ D) = true. 
Proof. intros. Admitted.




                               
Inductive sound_state : program -> state  -> Prop :=
| sound_state_intro:
    forall st prog
           (env: (match_lists (calculate_previous1 (prep_prog prog) (p st)) (e st)) = true), sound_state prog st.


Lemma prog_to_cmd_implies_fetch_and_incr : forall prog i i1 t, program_to_cmd prog i = Some (t, i1) -> incr_pc prog i = i1 /\ fetch prog i = Some t.
Proof. intros. unfold incr_pc. unfold fetch. unfold program_to_cmd in *. unfold get_program_term_id in *. destruct prog. simpl in *. destruct term0. simpl in *. remember ( PeanoNat.Nat.eqb i0 i). destruct b.  inversion H. auto. destruct ( find_instr prog_code0 i i0). destruct p0. inversion H. eauto. inversion H. Qed.




Lemma test5 : forall prog i i1 t head,  NoDup ((get_program_term_id prog ) :: (map fst (prog_code prog))) ->
                                        program_to_cmd prog i = Some (t, Some i1) ->
                                        calculate_previous1 (prep_prog prog) i = head  ->
                                        calculate_previous1 (prep_prog prog) (i1) = calculate_previous1 (prep_prog prog) i ++ (cons (i, t) nil).
Proof. intros. apply prog_to_cmd_implies_fetch_and_incr in H0. destruct H0. eapply test4 in H; eauto. Qed.

Print transition.




       
Lemma step_preserves_soundness : forall p st st1,
     NoDup ((get_program_term_id p ) :: (map fst (prog_code p)))  -> sound_state p st -> StepD p st = Step state st1 -> sound_state p st1.
Proof. intros. constructor. inversion H. subst.

       unfold StepD in H0. destruct st.  simpl in *. 
       remember ( program_to_cmd p0 p1).

       destruct o. simpl in *. destruct p2. simpl in *. destruct o. destruct c. simpl in *.
       inversion H1. simpl in *. eapply test5 in H; eauto. destruct st1. simpl in *. destruct ( eval_exp e1 e0) (*warning*).
       inversion H1. subst. rewrite H. simpl in *. admit.simpl in *.
       

