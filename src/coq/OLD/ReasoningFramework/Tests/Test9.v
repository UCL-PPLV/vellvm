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

Print IId.
Print pc.
Print state.
Print incr_pc.
Print IId.
Print pc.
Print instr_id.
Definition testytest (insn:instr) (CFG:mcfg) (pc_next pc:pc) (k:stack) (e:env) : transition state :=
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

Print ident.



Print pc.



Definition part_CFG_Step_test (insn:instr) (CFG:mcfg) (pc:pc)  (k:stack) (e:env) : transition state :=
 do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      testytest insn CFG pc_next pc k e.


Definition part_CFG_Step (insn:instr) (CFG:mcfg) (pc:pc) (k:stack) (e:env) : transition state :=
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



Print state.


Definition part_CFG_Step_one (insn:instr) (s:state) (CFG:mcfg) : transition state :=
  let '(pc, e, k) := s in
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








Definition lift_err_d {A} (m:err A) (f: A -> transition state) : transition state :=
  match m with
    | inl s => Obs (Err s)
    | inr b => f b
  end.

Notation "'do' x <- m ; f" := (lift_err_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).


Print part_INSTR_Op.





Theorem testtest : forall insn CFG pc k e, part_CFG_Step_test insn CFG pc k e = part_CFG_Step insn CFG pc k e.
Proof. intros. auto. Qed.

Definition Reason_stepD (CFG:mcfg) (s:state) : transition state :=
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


CoFixpoint Reason_step_sem (CFG:mcfg) (s:state) : Trace state :=
  match (Reason_stepD CFG s) with
  | Step s' => Tau s (Reason_step_sem CFG s')
  | Jump s' => Tau s (Reason_step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (Reason_step_sem CFG) m))
  end.

Theorem equality_stepD : forall CFG s, stepD CFG s = Reason_stepD CFG s.
Proof. intros. destruct s. induction s, p, e; simpl; eauto. Qed.



Theorem equality_step_sen : forall CFG s, Reason_step_sem CFG s = step_sem CFG s.
Proof. auto. Qed.



