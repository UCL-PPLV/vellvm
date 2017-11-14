Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast Vellvm.ReasoningFramework.Test2.
Import ListNotations.

From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Require Export Permutation.
Require Import Vellvm.Effects.



Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.





Definition part_term_ret(t:typ) (op:Ollvm_ast.value) (e:env) (k:stack) (pc:pc) := 
    do dv <- eval_op e (Some t) op;
      match k with
      | [] => Obs (Fin dv)
      | (KRet e' id p') :: k' => Jump (p', add_env id dv e', k')
      | _ => t_raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end
.


Definition part_term_ret_void (k:stack) (pc:pc) :=
    match k with
    | [] => Obs (Fin (DV (VALUE_Bool true)))
    | (KRet_void e' p')::k' => Jump (p', e', k')
    | _ => t_raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end
.
Print jump.

Definition part_term_br (CFG:mcfg) (br1 br2:block_id) (t:typ) (op:Ollvm_ast.value) (e:env) (k:stack) (pc:pc) :=
    do dv <- eval_op e (Some t) op; (* TO SEE *)
      do br <- match dv with 
              (* CHKoh: | DV (VALUE_Bool true) => mret br1
                 | DV (VALUE_Bool false) => mret br2 *)
              | DVALUE_I1 comparison_bit =>
                if Int1.eq comparison_bit Int1.one then
                  mret br1
                else
                  mret br2
              | _ => failwith "Br got non-bool value"
              end;
      do st <- jump CFG (fn pc) (bk pc) br e k;
      Jump st
.

Definition part_term_br_l (CFG:mcfg) (pc:pc) (k:stack) (br:block_id) (e:env) := do st <- jump CFG (fn pc) (bk pc) br e k; Jump st.

Print cmd.

Print Step.
Print Alloca.
Print state.

Definition part_INSTR_Op (id:local_id) (pc_next:pc) (op:Ollvm_ast.value) (e:env) (k:stack) := 
do dv <- eval_op e None op; Step (pc_next, add_env id dv e, k).

Print part_INSTR_Op.
Definition part_INSTR_Alloca (id:local_id) (pc_next:pc) (e:env) (t:typ) (k:stack) := Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k)))).


Definition part_INSTR_Load (id:local_id) (pc_next:pc) (u:typ) (ptr:Ollvm_ast.value) (pc:pc) (e:env) (k:stack) :=
        do dv <- eval_op e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end.


Definition part_INSTR_Store (pc_next:pc) (u t:typ) (val ptr:Ollvm_ast.value) (e:env) (k:stack) := 
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end.

Print find_function_entry.
Print env.

Definition part_INSTR_Call (pt:instr_id) (pc_next:pc) (ret_ty:typ) (args:seq tvalue) (CFG:mcfg) (fid: function_id) (e:env) (k:stack) := 

        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end.


Print IId.
Print pc.
Print state.

Function part_CFG_Step (insn:instr) (CFG:mcfg) (pc:pc) (k:stack) (e:env) : transition state :=
 do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op => part_INSTR_Op id pc_next op e k
      | IId id, INSTR_Alloca t _ _ => part_INSTR_Alloca id pc_next e t k
      | IId id, INSTR_Load _ t (u,ptr) _ => part_INSTR_Load id pc_next u ptr pc e k
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => part_INSTR_Store pc_next u t val ptr e k
      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args => part_INSTR_Call pt pc_next ret_ty args CFG fid e k
                
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


Function Reason_stepD (CFG:mcfg) (s:state) : transition state :=
  let '(pc, e, k) := s in
  do cmd <- trywith ("CFG has no instruction at " ++ string_of pc) (fetch CFG pc);
  match cmd with
  | Term (TERM_Ret (t, op)) => part_term_ret t op e k pc
  | Term TERM_Ret_void => part_term_ret_void k pc
  | Term (TERM_Br (t,op) br1 br2) => part_term_br CFG br1 br2 t op e k pc
  | Term (TERM_Br_1 br) => part_term_br_l CFG pc k br e
             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator" 
  | CFG.Step insn =>  (* instruction *) part_CFG_Step insn CFG pc k e
end.







CoInductive result (X: Type) : Type :=
  | Complete : Event X -> result X
  | JumpFinish : X -> result X
  | Continue : X -> result X. 

Print transition.

Print transition.
Print transition.
Print Trace.

CoFixpoint exec_block (CFG:mcfg) (s:state) : result state :=
match (Reason_stepD CFG s) with
  | Step s' => Continue s'
  | Jump s' => JumpFinish s'
  | Obs (Err s) => Complete (Err s)
  | Obs (Fin s) => Complete (Fin s)
  | Obs (Eff m) => Complete (Eff m)
end.
Print exec_block.

Function testytest (CFG:mcfg) (st: state) : transition state :=
match (exec_block CFG st) with
  | Complete (Err s) => Obs (Err s)
  | Complete (Fin s) => Obs (Fin s)
  | Complete (Eff m) => Obs (Eff m)
  | JumpFinish s' => Jump s'
  | Continue s' => Step s'
end
.



CoFixpoint exec_block1 (CFG:mcfg) (s:state) :=
match (Reason_stepD CFG s) with
  | Step s' => Continue s'
  | Jump s' => JumpFinish s'
  | Obs (Err s) => Complete (Err s)
  | Obs (Fin s) => Complete (Fin s)
  | Obs (Eff m) => Complete (Eff m)
end.


Function testytest1 (t:result state) : transition state :=
match t with
  | Complete (Err s) => Obs (Err s)
  | Complete (Fin s) => Obs (Fin s)
  | Complete (Eff m) => Obs (Eff m)
  | JumpFinish s' => Jump s'
  | Continue s' => Step s'
end
.


Theorem exec_block_equiv : forall CFG s, testytest1(exec_block1 CFG s) = Reason_stepD CFG s.

Proof. intros. unfold testytest1, exec_block1. induction (Reason_stepD CFG s); eauto.
induction m; eauto. Qed. 




Print testytest.



Function stepD_finish (CFG:mcfg) (s:state) :=
match (Reason_stepD CFG s) with
  | Step s' => Step s'
  | Jump s' => Jump s'
  | Obs (Err s) => Obs (Err s)
  | Obs (Fin s) => Obs (Fin s)
  | Obs (Eff m) => Obs (Eff m)
end.

Theorem Reason_StepD_equiv : forall CFG s, stepD CFG s = Reason_stepD CFG s.
Proof. intros. auto. Qed.

Theorem Reason_StepD_equiv1 : forall CFG s, testytest CFG s = stepD_finish CFG s.
Proof. intros. unfold testytest, stepD_finish. unfold exec_block. 
induction (Reason_stepD CFG s); eauto.
induction m; eauto. Qed.


Theorem stepD_finish_equiv : forall CFG s, stepD_finish CFG s = Reason_stepD CFG s.
Proof. intros. unfold stepD_finish. induction (Reason_stepD CFG s); eauto.
induction m; eauto. Qed.


Theorem stepD_equiv : forall CFG s, testytest CFG s = Reason_stepD CFG s.
Proof. intros. unfold testytest. unfold exec_block. induction (Reason_stepD CFG s); eauto.
induction m; eauto. Qed.


CoFixpoint new_step_sem (CFG:mcfg) (s:state) : Trace state :=
  match (testytest CFG s) with
  | Step s' => Tau s (new_step_sem CFG s')
  | Jump s' => Tau s (new_step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (new_step_sem CFG) m))
  end.




CoFixpoint Reason_step_sem (CFG:mcfg) (s:state) : Trace state :=
  match (Reason_stepD CFG s) with
  | Step s' => Tau s (step_sem CFG s')
  | Jump s' => Tau s (step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (step_sem CFG) m))
  end.



Theorem step_em_equiv : forall CFG s, Reason_step_sem CFG s = step_sem CFG s.
Proof. intros. auto. induction CFG. simpl. eauto. Admitted.


Set Printing All.




Theorem new_step_sem_equal_silly : forall CFG s, step_sem CFG s = new_step_sem CFG s.
Proof. intros. unfold step_sem, new_step_sem. Admitted.

Print testytest.

CoFixpoint new_step_sem_new (f:(mcfg -> state -> transition state)) (CFG:mcfg) (s:state) : Trace state :=
  match (f CFG s) with
  | Step s' => Tau s (new_step_sem CFG s')
  | Jump s' => Tau s (new_step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (new_step_sem CFG) m))
  end.



Theorem step_sem_neq_step_sem_equiv : forall CFG s, step_sem CFG s = new_step_sem_new Reason_stepD CFG s.
Proof. intros. unfold step_sem, new_step_sem_new. eauto. induction (Reason_stepD CFG s); eauto.

Admitted.