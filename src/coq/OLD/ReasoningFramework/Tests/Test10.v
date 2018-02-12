Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
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






Module SS := StepSemantics.StepSemantics(A).
Export SS.
Print state.

Definition part_term_ret(t:typ) (op:Ollvm_ast.value) (s:state) := 
  let '(pc, e, k) := s in
    do dv <- eval_op e (Some t) op;
      match k with
      | [] => Obs (Fin dv)
      | (KRet e' id p') :: k' => Jump (p', add_env id dv e', k')
      | _ => t_raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end
.


Definition part_term_ret_void (s:state) :=
  let '(pc, e, k) := s in
    match k with
    | [] => Obs (Fin (DV (VALUE_Bool true)))
    | (KRet_void e' p')::k' => Jump (p', e', k')
    | _ => t_raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end
.
Print jump.

Definition part_term_br (CFG:mcfg) (br1 br2:block_id) (t:typ) (op:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
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

Definition part_term_br_l (CFG:mcfg) (br:block_id) (s:state) :=
  let '(pc, e, k) := s in
do st <- jump CFG (fn pc) (bk pc) br e k; Jump st.

Print cmd.

Print Step.
Print Alloca.
Print state.

Definition part_INSTR_Op (id:local_id) (pc_next:pc) (op:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
do dv <- eval_op e None op; Step (pc_next, add_env id dv e, k).

Print part_INSTR_Op.
Definition part_INSTR_Alloca (id:local_id) (pc_next:pc) (t:typ) (s:state) :=
  let '(pc, e, k) := s in
 Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k)))).


Definition part_INSTR_Load (id:local_id) (pc_next:pc) (u:typ) (ptr:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
        do dv <- eval_op e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end.


Definition part_INSTR_Store (pc_next:pc) (u t:typ) (val ptr:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end.

Print find_function_entry.
Print env.

Definition part_INSTR_Call (pt:instr_id) (pc_next:pc) (ret_ty:typ) (args:seq tvalue) (CFG:mcfg) (fid: function_id) (s:state) := 
  let '(pc, e, k) := s in
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
Print pc.
Print pt.

Definition part_CFG_Step (insn:instr) (CFG:mcfg) (s:state) : transition state :=
  let '(pc, e, k) := s in
 do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op => part_INSTR_Op id pc_next op s
      | IId id, INSTR_Alloca t _ _ => part_INSTR_Alloca id pc_next t s
      | IId id, INSTR_Load _ t (u,ptr) _ => part_INSTR_Load id pc_next u ptr s
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => part_INSTR_Store pc_next u t val ptr s
      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args => part_INSTR_Call pt pc_next ret_ty args CFG fid s
                
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


Definition Reason_stepD (CFG:mcfg) (s:state) : transition state :=
  let '(pc, e, k) := s in
  do cmd <- trywith ("CFG has no instruction at " ++ string_of pc) (fetch CFG pc);
  match cmd with
  | Term (TERM_Ret (t, op)) => part_term_ret t op s
  | Term TERM_Ret_void => part_term_ret_void s
  | Term (TERM_Br (t,op) br1 br2) => part_term_br CFG br1 br2 t op s
  | Term (TERM_Br_1 br) => part_term_br_l CFG br s
             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator" 
  | CFG.Step insn =>  (* instruction *) part_CFG_Step insn CFG s
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
Proof. intros. unfold Reason_step_sem, step_sem.
Admitted.



