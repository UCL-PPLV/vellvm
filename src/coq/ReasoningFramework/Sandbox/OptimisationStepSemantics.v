(*Step Semantics*)


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




Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.



Module SS := StepSemantics.StepSemantics(A).
Export SS.



Definition term_ret(t:typ) (op:Ollvm_ast.value) (s:state) := 
  let '(pc, e, k) := s in
    do dv <- eval_op e (Some t) op;
      match k with
      | [] => Obs (Fin dv)
      | (KRet e' id p') :: k' => Jump (p', add_env id dv e', k')
      | _ => t_raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end
.


Definition term_ret_void (s:state) :=
  let '(pc, e, k) := s in
    match k with
    | [] => Obs (Fin (DV (VALUE_Bool true)))
    | (KRet_void e' p')::k' => Jump (p', e', k')
    | _ => t_raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end
.
Print jump.

Definition term_br (CFG:mcfg) (br1 br2:block_id) (t:typ) (op:Ollvm_ast.value) (s:state) :=
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

Definition term_br_l (CFG:mcfg) (br:block_id) (s:state) :=
  let '(pc, e, k) := s in
do st <- jump CFG (fn pc) (bk pc) br e k; Jump st.



Definition INSTR_Op_part (op:Ollvm_ast.value) (s:state) := 
  let '(pc, e, k) := s in
  (eval_op e None op).


Definition INSTR_Op_single (id:local_id) (pc_next:pc) (op:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
do dv <- INSTR_Op_part op s; Step (pc_next, add_env id dv e, k).

Print INSTR_Op_single.
Print transition.
Definition INSTR_Alloca_single (id:local_id) (pc_next:pc) (t:typ) (s:state) :=
  let '(pc, e, k) := s in
 Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k)))).


Definition INSTR_Load_single (id:local_id) (pc_next:pc) (u:typ) (ptr:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
        do dv <- eval_op e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end.


Definition INSTR_Store_single (pc_next:pc) (u t:typ) (val ptr:Ollvm_ast.value) (s:state) :=
  let '(pc, e, k) := s in
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end.


Definition INSTR_Call_single (pt:instr_id) (pc_next:pc) (ret_ty:typ) (args:seq tvalue) (CFG:mcfg) (fid: function_id) (s:state) := 
  let '(pc, e, k) := s in
        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end.




Definition CFG_Step (insn:instr) (CFG:mcfg) (s:state) : transition state :=
  let '(pc, e, k) := s in
 do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op => INSTR_Op_single id pc_next op s
      | IId id, INSTR_Alloca t _ _ => INSTR_Alloca_single id pc_next t s
      | IId id, INSTR_Load _ t (u,ptr) _ => INSTR_Load_single id pc_next u ptr s
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => INSTR_Store_single pc_next u t val ptr s
      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args => INSTR_Call_single pt pc_next ret_ty args CFG fid s
                
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
  | Term (TERM_Ret (t, op)) => term_ret t op s
  | Term TERM_Ret_void => term_ret_void s
  | Term (TERM_Br (t,op) br1 br2) => term_br CFG br1 br2 t op s
  | Term (TERM_Br_1 br) => term_br_l CFG br s
             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator" 
  | CFG.Step insn =>  (* instruction *) CFG_Step insn CFG s
end.



Theorem equiv_stepD : forall CFG s, Reason_stepD CFG s = stepD CFG s.
Proof. intros. induction s. induction a, b; eauto. Qed.





CoFixpoint Reason_step_sem (CFG:mcfg) (s:state) : Trace state :=
  match (Reason_stepD CFG s) with
  | Step s' => Tau s (Reason_step_sem CFG s')
  | Jump s' => Tau s (Reason_step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (Reason_step_sem CFG) m))
  end.


Theorem equiv_step_sem : forall CFG s, Reason_step_sem CFG s = step_sem CFG s.
Proof. intros. induction s. induction a, b; eauto. induction a, b0; eauto. Admitted.



Definition Reason_sem (CFG:mcfg) (s:state) : Trace () := hide_taus (Reason_step_sem CFG s).


