From Paco
Require Import paco.

Require Import Ascii String.
Require Import Coq.Strings.String.
Require Import List.
Require Import Coq.Arith.EqNat.


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



Fixpoint calculate_previous (l:list (instr_id * exp)) (i:nat) :=
  match l with
  | nil => nil
  | cons hd tl => if beq_nat (fst hd) i then nil else cons hd  (calculate_previous tl i)
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



(* Fetches the current instruction and the following instruction, if any*)




(*Evaluates an expression*)
Fixpoint eval_exp (i:exp) (s:env) : option exp :=
  match i with
  | AIdent a => get_env s a
  | ANum a => Some (ANum a)
  | APlus a b => match (eval_exp a s), (eval_exp b s) with
                 | (Some (ANum a1)), (Some (ANum b1)) => Some (ANum (a1 + b1))
                 | _, _ => None
                 end
  end
.


Inductive Event :=
| Fin : exp -> Event
| Err : Event
.


Inductive transition X :=
| Step (s:X)
| Obs (m:Event)
.




(*Evaluates an instruction*)
Definition eval_instr (p:program) (s:state) : transition state :=
  let (e, pc) := s in
  match program_to_cmd p pc with
  | Some (Step_cmd ins, Some next_pc) => match eval_exp ins e with
                                         | Some res => Step state (mkState ((pc, res)::e) next_pc)
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
  match eval_instr p s with
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
         constructor. apply LE. apply HRk. constructor. eauto. constructor. eauto. Qed.
  Hint Resolve related_event_step_monotone : paco.


  Definition trace_equiv {X} (p q: Trace X) := paco2 (@trace_equiv_step X) bot2 p q.
  Hint Unfold trace_equiv.





  (************************************************)
  (*STATIC EVALUATION*)
  Print cmd.







  
Definition areg : Set := (instr_id * exp).
Definition aenv := list areg.


Definition fallthrough1 (l:aenv) :=
  match l with
  | nil => None
  | hd::tl => Some (fst hd)
  end.


Fixpoint calculate_aenv_code (l:list (instr_id * exp)) (i:nat) : aenv :=
  match l with
  | nil => nil
  | cons hd tl => if beq_nat (fst hd) i then nil else cons hd  (calculate_aenv_code tl i)
  end.

(*
Definition program_to_cmd (p:program) (i:instr_id) : option (cmd * option instr_id) :=
  if beq_nat (get_program_term_id p) i then Some (Term (snd (term p)), None) else find_instr (prog_code p) i (get_program_term_id p).
*)

Definition calculate_aenv (p:program) (i:nat) :=
  if beq_nat (get_program_term_id p) i then calculate_aenv_code (prog_code p) i else calculate_aenv_code (prog_code p) i.
  

Print fetch.



(*USEFUL LEMMAS*)

(*First lemma relates the position of an instruction with the previous instructions *)

Print fetch.

Lemma find_tuple_relates_previous : forall p i i1, fetch p i = Some (Step_cmd i1) ->
                            exists tl, (prog_code p) = (calculate_aenv p i) ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold fetch in *. simpl in *. destruct p0.
       unfold program_to_cmd in *. unfold get_program_term_id in *. simpl in *. destruct term0. simpl in *. unfold calculate_aenv. simpl in *. unfold get_program_term_id. simpl in *. destruct (PeanoNat.Nat.eqb i0 i). inversion H. 
       induction prog_code0; simpl in *.
       +inversion H.
       +simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i3 i). simpl in *. destruct b. simpl in *. inversion H. subst. apply beq_nat_eq in Heqb. subst.  eauto.  eauto. simpl in *. apply IHprog_code0 in H. inversion H. exists x. rewrite <- H0. eauto.
Qed.


(*Relates a fetch and an incr_pc with the program_to_cmd which is easier to reason with*)
Lemma fetch_and_increase_implies_cmd_pair : forall l i i1 t1, fetch l i = Some i1 -> incr_pc l i = Some t1 -> program_to_cmd l i = Some (i1, Some t1).
Proof. intros. unfold fetch in *. unfold incr_pc in *. destruct (program_to_cmd l i). destruct p0. simpl in *. inversion H. subst. eauto. inversion H. Qed.



(*Small helper function for lists*)
Lemma n1_in_list : forall n1 (A:aenv) n2 x0, In n1 (map fst (A ++ (n1, n2) :: x0)).
Proof. intros. induction A. simpl in *. left. eauto. simpl. right. eauto. Qed.
              




(*Relates calculate_aenv with the instructions used*) Print calculate_aenv.
Lemma calculate_aenv_from_lists : forall t1 A x0, NoDup (map fst (A ++ (cons t1 nil) ++ x0)) -> calculate_aenv_code (A ++ (cons t1 nil) ++ x0) (fst t1) = A.
Proof. intros. induction A. simpl in *. rewrite PeanoNat.Nat.eqb_refl. eauto. simpl in *. destruct a, t1. simpl in *.
       remember  (PeanoNat.Nat.eqb i i0). destruct b. simpl in *. apply beq_nat_eq in Heqb.
       subst. inversion H. subst. contradiction H2. apply n1_in_list. 
(assert ((calculate_previous (A ++ (i0, e1) :: x0) i0 = A)  -> ((i, e0)
  :: calculate_previous (A ++ (i0, e1) :: x0) i0 =
  (i, e0) :: A ))). intros. rewrite H0. eauto. apply H0; apply IHA. inversion H; subst; eauto. Qed.



Print program.

Print program_to_cmd.
Print program_to_cmd.
Print program_to_cmd.
(*Links a pair*)






























  Definition aenv := list (instr_id *  exp).
  Definition prog_aenv := (list (instr_id * (aenv))).
Print program_to_cmd.
Print cmd.


  Definition transfer  (a:aenv) (i:instr_id*exp) : aenv :=  a ++ (cons i nil).
      
  
  Fixpoint aeval_code  (c:list (instr_id*exp)) (a:aenv) : prog_aenv :=
    match c with
    | hd :: tl => (fst hd, a) :: aeval_code tl (transfer a (hd))
    | nil => nil
    end.
 Print aeval_code.

 Print program.

  Definition aeval_prog (prog:program) := aeval_code (prog_code prog) nil.


Print aeval_prog.
  Fixpoint get_aenv (i:instr_id) (p:prog_aenv) :=
    match p with
    | nil => None
    | hd :: tl => if beq_nat (fst hd) i then Some (snd hd) else get_aenv i tl
    end.
  

  Fixpoint get_instr_from_aenv (i:instr_id) (a:aenv) :=
    match a with
    | nil => None
    | hd :: tl => if beq_nat (fst hd) i then Some (snd hd) else get_instr_from_aenv i tl
    end.

  
  
(*Small experiment*)
Definition first_instr := (1, ANum 2).
Definition second_instr := (2, AIdent 1).
Definition third_instr := (3, AIdent 1).

Definition term_instr := (4, 2).
Definition test_prog := mkProgram (cons first_instr (cons second_instr (cons third_instr nil))) term_instr.


Eval compute in aeval_prog test_prog.




(************************************************)

Print  cmd.

Print get_instr_from_aenv.


  Fixpoint const_prop_aexp (a:aenv) (e:exp) : exp :=
  match e with
  | AIdent ident => match get_instr_from_aenv ident a with
                    | Some a => a
                    | None => AIdent ident
                                     
                    end
  | ANum num => ANum num
  | APlus v1 v2 => APlus (const_prop_aexp a v1) (const_prop_aexp a v2)          
  end.

  

  Definition const_prop_instr (a:prog_aenv) (i:instr_id * exp) :=
    match get_aenv (fst i) a with
    | None => i
    | Some a => (fst i, const_prop_aexp a (snd i))
    end.
  


Definition const_prop_code (a:prog_aenv) (p:list (instr_id * exp)) := map (const_prop_instr a) p. 
Print aeval_prog.

Print const_prop_code.


Definition const_prop_prog (p:program) := mkProgram (const_prop_code (aeval_prog p ) (prog_code p)) (term p).

Eval compute in test_prog.
Eval compute in const_prop_prog test_prog.



Inductive value_match : exp -> exp -> Prop :=
| match_ident : forall a, value_match ( (AIdent a)) ( (AIdent a))
| match_num : forall a,  value_match ( (ANum a)) ( (ANum a))
| match_plus : forall a b c d, value_match ( a) ( c) -> value_match ( b) ( d) -> value_match ( (APlus a b)) ( (APlus c d)).


Print aenv.
Definition second (o:option exp) (i:exp) :=
  match o with
  | None => True
  | Some a => value_match a i
                          end.


                                          
Fixpoint match_aenv_env (a:aenv) (e:env) :=
  match a, e with
  | nil, nil => True
  | hd::tl, hd1::tl1 => if (beq_nat (fst hd) (fst hd1)) then match_aenv_env tl tl1 else False
  | _, _ => False
  end.
    

Inductive match_list : env -> aenv -> Prop :=
  | match_list_intro : forall a e, match_aenv_env a e -> match_list e a.


Print state.

Inductive sound_state : program -> state  -> Prop :=
| sound_state_intro:
    forall st prog aenv (AN: get_aenv (p st) (aeval_prog prog) = Some aenv)
           (env: match_list (e st) aenv), sound_state prog st.
                    






Definition get_initial_state (p:program) := mkState nil (fallthrough (prog_code p) (fst (term p))).



Lemma initial_state_is_sound : forall p s, get_initial_state p = s -> sound_state p s.
Proof. intros. Admitted.


Print transfer.


(*Print  eval_instr p s*)
Print program_to_cmd.
Print program.

Print cmd.

Lemma testtest : forall prog st st1 instr,  program_to_cmd prog (p st) = Some (Step_cmd instr, Some (p st1)) -> exists head tail, (prog_code prog) = head ++ (cons ((p st),instr) nil) ++ tail.

Proof. intros. destruct st. destruct prog. unfold program_to_cmd in *. simpl in *. destruct term0. simpl in *.
       remember ( PeanoNat.Nat.eqb i p0). destruct b. simpl in *. inversion H.


       destruct st1. simpl in *.
       induction prog_code0. simpl in *. inversion H. simpl in *. destruct a. simpl in *. remember ( PeanoNat.Nat.eqb i1 p0). destruct b. simpl in *. SearchAbout PeanoNat.Nat.eqb. apply beq_nat_eq in Heqb0.  subst. inversion H. subst. exists nil. simpl in *. exists prog_code0. eauto.
       simpl in *. apply IHprog_code0 in H. inversion H. subst. destruct H0. rewrite H0. simpl. exists ((i1, e2) :: x). exists x0. eauto. Qed.


