Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.optimisation_stepsem.
Require Import Vellvm.DecidableEquality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.

Set Implicit Arguments.

Print mcfg.
Print Trace.
Inductive finish_item X :=
  | tauitem : memory -> X -> finish_item X
  | visitem : memory -> Event (Trace X) -> finish_item X.

Print Trace.

Print Event.


Print Event.

Print mem_step.
Definition head_of_trace (m:memory) (t:Trace state) : finish_item state :=
match t with
  | Vis x => visitem m x
  | Tau a _ => tauitem m a
end.


Definition CFG_step insn CFG s := 
  let '(pc, e, k) := s in
    do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op =>
        do dv <- eval_op e None op;     
          Step (pc_next, add_env id dv e, k)

      | IId id, INSTR_Alloca t _ _ =>
        Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k))))
                
      | IId id, INSTR_Load _ t (u,ptr) _ =>
        do dv <- eval_op e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end

      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args =>
        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end        
                
      | _, INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"

      | _, INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable" 

        (* Currently unhandled LLVM instructions *)
      | _, INSTR_Fence 
      | _, INSTR_AtomicCmpXchg 
      | _, INSTR_AtomicRMW
      | _, INSTR_VAArg 
      | _, INSTR_LandingPad => t_raise "Unsupported LLVM intsruction" 

      (* Error states *)                                     
      | _, _ => t_raise "ID / Instr mismatch void/non-void"
      end.



Print code.

Print CFG_step.
Print Obs. 



Inductive mini_trace :=
| fin (f:finish_item state)
| tau (f:finish_item state) (d:mini_trace).

Fixpoint exec_code (m:mcfg) (c:code) (f:finish_item ( state)) : mini_trace :=
match c with
  | [::] => match f with
            | visitem mem (Eff s') => fin ((visitem mem (Eff s')))
            | sec => fin (sec)
            end
  | h :: t => match f with
              | tauitem mem s => match (CFG_step (snd h) m s) with
                             | Step s' => tau ((tauitem mem s)) (exec_code m t (tauitem mem s'))
                             | Jump s' => tau ((tauitem mem s)) (exec_code m t (tauitem mem s'))
                             | Obs (Eff s') => match mem_step s' mem with
                                               | inr (m', v, k) => tau ((tauitem mem s)) (exec_code m t (tauitem m' (k v)))
                                               | inl _ => fin ((tauitem mem s))
                                               end
                             | Obs (Fin s') => tau ((tauitem mem s)) (exec_code m t ((visitem mem (Fin s'))))
                             | Obs (Err s') => tau ((tauitem mem s)) (exec_code m t ((visitem mem (Err s'))))
                             end
              | item => fin item
              end
end.



Inductive compare_trace : mini_trace -> mini_trace -> Prop  :=
| trace_refl : forall a, compare_trace a a
| trace_right : forall a h t, compare_trace a t -> compare_trace a (tau h t)
| trace_left : forall a h t, compare_trace t a -> compare_trace (tau h t) a.



Lemma compare_trace_fin : forall A B (H1: compare_trace (fin A) (fin B)), compare_trace (fin B) (fin A).
Proof. intros. inversion H1. subst. auto. Qed.

Hint Resolve compare_trace_fin.





       



       
Definition compare_exec m m1 c c1 mem s := compare_trace (exec_code m c (tauitem mem s)) (exec_code m1 c1 (tauitem mem s)).



Lemma mini_trace_implies_double : forall A B C D, compare_trace (tau A (fin B)) (tau C (fin D)) -> B = D.
Proof. intros. inversion H; subst; auto. inversion H2; subst; auto. inversion H4; subst; auto.
       inversion H3; subst; auto. inversion H2; subst; auto. Qed.


Lemma mini_trace_2r_implies_1l : forall A B C, compare_trace (tau A (fin B)) (fin C) -> B = C.
Proof. intros. inversion H; subst. inversion H3; subst. auto. Qed.



Print incr_pc.

(*s l -> option pc*)

Print state.
Print pc.
Print block.
Definition incr_pc_v1 (s:state) (t:instr_id) (c:code) : option pc :=
    let '(pc, e, k) := s in
    match c with
    | nil =>  Some (mk_pc (fn pc) (bk pc) t)
    | cons _ nil  =>  Some (mk_pc (fn pc) (bk pc) t)
    | cons _ (cons (iis, ins) _) => Some (mk_pc (fn pc) (bk pc) iis)
    end
.



Definition CFG_step_v1 insn CFG s t (c:code) := 
  let '(pc, e, k) := s in
    do pc_next <- trywith "no fallthrough intsruction" (incr_pc_v1 s t c);
      match (pt pc), insn  with
      | IId id, INSTR_Op op =>
        do dv <- eval_op e None op;     
          Step (pc_next, add_env id dv e, k)

      | IId id, INSTR_Alloca t _ _ =>
        Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k))))
                
      | IId id, INSTR_Load _ t (u,ptr) _ =>
        do dv <- eval_op e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end

      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args =>
        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end        
                
      | _, INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"

      | _, INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable" 

        (* Currently unhandled LLVM instructions *)
      | _, INSTR_Fence 
      | _, INSTR_AtomicCmpXchg 
      | _, INSTR_AtomicRMW
      | _, INSTR_VAArg 
      | _, INSTR_LandingPad => t_raise "Unsupported LLVM intsruction" 

      (* Error states *)                                     
      | _, _ => t_raise "ID / Instr mismatch void/non-void"
      end.

Fixpoint exec_code1 (m:mcfg) (c:code) (term_id:instr_id) (f:finish_item ( state)) : mini_trace :=
match c with
  | [::] => match f with
            | visitem mem (Eff s') => fin ((visitem mem (Eff s')))
            | sec => fin (sec)
            end
  | h :: t => match f with
              | tauitem mem s => match (CFG_step_v1 (snd h) m s term_id c) with
                             | Step s' => tau ((tauitem mem s)) (exec_code1 m t term_id (tauitem mem s'))
                             | Jump s' => tau ((tauitem mem s)) (exec_code1 m t term_id (tauitem mem s'))
                             | Obs (Eff s') => match mem_step s' mem with
                                               | inr (m', v, k) => tau ((tauitem mem s)) (exec_code1 m t term_id (tauitem m' (k v)))
                                               | inl _ => fin ((tauitem mem s))
                                               end
                             | Obs (Fin s') => tau ((tauitem mem s)) (exec_code1 m t term_id ((visitem mem (Fin s'))))
                             | Obs (Err s') => tau ((tauitem mem s)) (exec_code1 m t term_id ((visitem mem (Err s'))))
                             end
              | item => fin item
              end
end.


Definition compare_exec1 m m1 c c1 mem s t := compare_trace (exec_code1 m c t (tauitem mem s)) (exec_code1 m1 c1 t (tauitem mem s)).





(*USEFUL LEMMAS*)

Print mem.


Lemma false_mem : forall (mem:memory) A, (mem ++ [:: A])%list = mem -> False.
Proof. intros. induction mem; simpl in *.
       +inversion H.
       +apply IHmem. inversion H; subst. rewrite H1. apply H1. Qed.


Lemma false_stack : forall (s:seq frame) A,  A :: s = s -> False.
Proof. intros. induction s.
       +inversion H.
       +apply IHs. inversion H. subst. rewrite H2; auto. Qed.


Lemma false_env : forall id v e,  add_env id v e = e -> False.
Proof. intros. unfold add_env in *. induction e; simpl in *.
       +inversion H.
       +apply IHe. inversion H; subst. rewrite H2. rewrite H2. auto. Qed.
         