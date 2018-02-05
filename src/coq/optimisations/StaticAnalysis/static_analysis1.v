Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.



Print memory.
(*Definition of an abstract register*)
Definition areg : Set := (local_id * option value).


(*Definition of the abstract set of registers*)
Definition aenv : Set := list areg.



(*Instructions useful to manipulate the abstract registers*)
Definition aenv_fallthrough (l:aenv) :=
  match l with
  | nil => None
  | hd::tl => Some (fst hd)
  end.


Fixpoint list_to_tuple (l: aenv) (t: local_id)  :=
  match l with
  | nil => None
  | hd :: tl => if (decide ((fst hd) = t)) then Some (snd hd, aenv_fallthrough tl) else list_to_tuple tl t
  end.


Definition find_areg (l: aenv) (i: local_id) :=
  match list_to_tuple l i with
  | Some (t, _) => Some t
  | _ => None
  end.

Definition next_areg (l: aenv) (i: local_id) :=
  match list_to_tuple l i with
  | Some (_, Some a) => Some a
  | _ => None
  end.


Fixpoint get_from_aenv (l: aenv)  (i: local_id) :=
  match l with
  | nil => None
  | (iis, ins) :: tl => if decide (iis = i) then Some (ins) else get_from_aenv tl i
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
  | hd :: tl => if decide ((fst hd) = i) then Some (snd hd, opt_fallthrough tl) else find_in_newlist tl i
  end.


(*Maps a block into a list of commands*)
Definition map_exp_to_cmd (e:instr_id * instr) : (instr_id * cmd) := (fst e, CFG.Step (snd e)).
Definition map_term_to_cmd (t: (instr_id*terminator)) : list (instr_id * cmd) := cons (fst t, Term (snd t)) nil.
Definition prep_block (b:block) := map map_exp_to_cmd (blk_code b) ++ map_term_to_cmd (blk_term b).



(*Fetches and maps the block in the specified pc, into a list of commands *)
Definition prep_selected_block (m:mcfg) (p:pc) :=
  match find_function m (fn p) with
  | None => None
  | Some func => match find_block (blks (df_instrs func)) (bk p) with
                 | None => None
                 | Some a => Some (prep_block a)
                 end
                   
  end.




(*The transfer function which adds values to the abstract registers *)
Definition transfer (a: aenv) (i: instr_id * cmd) : aenv :=
  match (fst i), (snd i) with
  | (IId loc), CFG.Step ins => match ins with
                    | INSTR_Op val => match val with
                                      | SV s_value => match s_value with
                                                      | VALUE_Integer n => (loc, Some (DV (VALUE_Integer n))) :: a
                                                      | _ => (loc, None) :: a
                                                        end
                                      end
                    | _ => (loc, None) :: a
                             
                    end
                      
  | _, _ => a
  end.



(*Recursive iteration of the transfer function over a list of instructions*)
Fixpoint value_analysis_fix (acc: aenv) (l: (seq (instr_id * cmd))) (i: instr_id) : aenv :=
  match l with
  | nil => nil
  | hd :: tl => if (decide ((fst hd) = i)) then acc else (value_analysis_fix (transfer acc hd) tl i)
  end.



Definition value_analysis (l: seq (instr_id * cmd)) (i: instr_id) := value_analysis_fix nil l i.




(***************************************)
(*Relating env to aenv*)



(*Useful function*)
Definition beq_value (a b: value) : bool := decide (a = b).
Definition beq_local_id (a b: local_id) : bool := decide (a = b).



(*An abstract register matches a register if they have matching variable names. 
If the abstract register holds a value, then the register will match it.*)

Definition aenv_env_pair (a:areg) (e: local_id * value) : bool :=
  match a, e with
  | (k, None), (k1, a) => beq_local_id k k1
  | (k, Some a1), (k1, e1) => beq_local_id k k1 && beq_value a1 e1
  end.


Fixpoint substring (a:aenv) (e:env) : bool :=
  match a, e with
  | nil, nil => true
  | l1, nil => false
  | nil, l1 => true
  | hd :: tl, hd1 :: tl1 => aenv_env_pair hd hd1 && substring tl tl1
  end.




(*Defining the correctness of various elements of the memory*)

Definition sound_env (m:mcfg) (p:pc) (e:env) :=
  forall prep, prep_selected_block m p = Some prep ->
               substring (value_analysis prep (pt p)) e.



(*A stack is well formed if each of its elements are well formed*)
(*Each function pointer is well formed, if its env is well-formed*)
(*Additionally, information about the previous instruction is recorded for purposes later on*)

Inductive sound_stack : mcfg -> stack -> Prop :=
| nil_stack : forall p,  sound_stack p nil



                                     
| kret_stack : forall id m p e k (sstack_env: sound_env m  (mk_pc (fn p) (bk p) (IId id)) e) (stk:sound_stack m k),
    (exists tptr tval, fetch m (mk_pc (fn p) (bk p) (IId id)) = Some (CFG.Step (INSTR_Call tptr tval)) /\
                          incr_pc m (mk_pc (fn p) (bk p) (IId id)) = Some p)
    -> sound_stack m ((KRet e id p)::k)





                   
| kret_void_stack : forall m p e k (stk:sound_stack m k),
    (exists tptr tval id, sound_env m (mk_pc (fn p) (bk p) (IVoid id)) e /\ fetch m (mk_pc (fn p) (bk p) (IVoid id)) = Some (CFG.Step (INSTR_Call tptr tval)) /\
                          incr_pc m (mk_pc (fn p) (bk p) (IVoid id)) = Some p)
 -> sound_stack m ((KRet_void e p)::k).


(*A state is well formed if both its stack and registers are well formed*)
Inductive sound_state : mcfg -> state -> Prop :=
| sound_state_intro :
    forall m st
           (sstack: sound_stack m (stack_of st))
           (senv: sound_env m (pc_of st) (env_of st)),
      sound_state m st.

