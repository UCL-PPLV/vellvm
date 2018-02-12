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


(*

Print state.

Inductive result x :=
  | Success (s:x)
  | Error (s:x)
.



Definition result_block_lift_err_d {A} (m:err A) (f: A ->  (result (transition state))) :  (result (transition state)) :=
  match m with
    | inl s =>  (Success (Obs (Err s)))
    | inr b => f b
  end.


Notation "'do' x <- m ; f" := (result_block_lift_err_d m (fun x => f)) 
   (at level 200, x ident, m at level 100, f at level 200).

Definition result_block_t_raise s : finish (result (transition state)) :=
 Finished (Error (Obs (Err s))). 

Definition result_block_t_raise_p (p:pc) s := result_block_t_raise (s ++ ": " ++ (string_of p)).





Definition block_part_term_ret(t:typ) (op:Ollvm_ast.value) (e:env) (k:stack) (pc:pc) :  finish (result (transition state)) := 
    do dv <- eval_op e (Some t) op;
      match k with
      | [] =>  Finished (Success (Obs (Fin dv)))
      | (KRet e' id p') :: k' =>  Finished (Success (Jump (p', add_env id dv e', k')))
      | _ => result_block_t_raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end
.


Definition block_part_term_ret_void (k:stack) (pc:pc) :   (result (transition state)) :=
    match k with
    | [] => Finished (Success (Obs (Fin (DV (VALUE_Bool true)))))
    | (KRet_void e' p')::k' => Finished (Success (Jump (p', e', k')))
    | _ => result_block_t_raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end
.
Print jump.

Definition block_part_term_br (CFG:mcfg) (br1 br2:block_id) (t:typ) (op:Ollvm_ast.value) (e:env) (k:stack) (pc:pc) :  (result (transition state)) :=
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
      Finished (Success (Jump st))
.

Definition block_part_term_br_l (CFG:mcfg) (pc:pc) (k:stack) (br:block_id) (e:env) :  (result (transition state)) := 
do st <- jump CFG (fn pc) (bk pc) br e k; Finished (Success (Jump st)).

Print cmd.

Print Step.
Print Alloca.
Print state.

Definition block_part_INSTR_Op (id:local_id) (pc_next:pc) (op:Ollvm_ast.value) (e:env) (k:stack) : finish (result (transition state)) := 
do dv <- eval_op e None op; NotFinished (Success (Step (pc_next, add_env id dv e, k))).


Definition block_part_INSTR_Alloca (id:local_id) (pc_next:pc) (e:env) (t:typ) (k:stack) : finish (result (transition state)) := 
NotFinished (Success (Obs (Eff (Alloca t (fun (a:value) => (pc_next, add_env id a e, k)))))).


Definition block_part_INSTR_Load (id:local_id) (pc_next:pc) (u:typ) (ptr:Ollvm_ast.value) (pc:pc) (e:env) (k:stack) : finish (result (transition state)) :=
        do dv <- eval_op e (Some u) ptr;
          match dv with
          | DVALUE_Addr a => NotFinished (Success (Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))))
          | _ => result_block_t_raise "ERROR: Load got non-pointer value" 
          end.


Definition block_part_INSTR_Store (pc_next:pc) (u t:typ) (val ptr:Ollvm_ast.value) (e:env) (k:stack) : finish (result (transition state)) := 
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => NotFinished (Success (Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))))
          |  _ => result_block_t_raise "ERROR: Store got non-pointer value"
          end.

Print find_function_entry.
Print env.

Definition block_part_INSTR_Call (pt:instr_id) (pc_next:pc) (ret_ty:typ) (args:seq tvalue) (CFG:mcfg) (fid: function_id) (e:env) (k:stack) : finish (result (transition state)) := 

        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => NotFinished (Error (Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))))
              | IId id, _ =>          NotFinished (Error (Step (pc_f, combine ids dvs, (KRet e id pc_next::k))))
              | _, _ => result_block_t_raise "Call mismatch void/non-void"
          end.


Print IId.
Print pc.
Print state.


Definition block_part_CFG_Step (insn:instr) (CFG:mcfg) (pc:pc) (k:stack) (e:env) :  (result (transition state)):=
 do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op => block_part_INSTR_Op id pc_next op e k
      | IId id, INSTR_Alloca t _ _ => block_part_INSTR_Alloca id pc_next e t k
      | IId id, INSTR_Load _ t (u,ptr) _ => block_part_INSTR_Load id pc_next u ptr pc e k
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => block_part_INSTR_Store pc_next u t val ptr e k
      | _, INSTR_Store _ _ _ _ => result_block_t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args => block_part_INSTR_Call pt pc_next ret_ty args CFG fid e k
                
      | _, INSTR_Call (_, ID_Local _) _ => result_block_t_raise "INSTR_Call to local"

      | _, INSTR_Unreachable => result_block_t_raise "IMPOSSIBLE: unreachable" 

        (* Currently unhandled LLVM instructions *)
      | _, INSTR_Fence 
      | _, INSTR_AtomicCmpXchg 
      | _, INSTR_AtomicRMW
      | _, INSTR_VAArg 
      | _, INSTR_LandingPad => result_block_t_raise "Unsupported LLVM intsruction" 

      (* Error states *)                                     
      | _, _ => result_block_t_raise "ID / Instr mismatch void/non-void"
      end.









Definition block_reason_stepD (CFG:mcfg) (s:state) : (result (transition state)) :=
  let '(pc, e, k) := s in
  do cmd <- trywith ("CFG has no instruction at " ++ string_of pc) (fetch CFG pc);
  match cmd with
  | Term (TERM_Ret (t, op)) => block_part_term_ret t op e k pc
  | Term TERM_Ret_void => block_part_term_ret_void k pc
  | Term (TERM_Br (t,op) br1 br2) => block_part_term_br CFG br1 br2 t op e k pc
  | Term (TERM_Br_1 br) => block_part_term_br_l CFG pc k br e
             
  (* Currently unhandled LLVM terminators *)                                  
  | Term (TERM_Switch _ _ _)
  | Term (TERM_IndirectBr _ _)
  | Term (TERM_Resume _)
  | Term (TERM_Invoke _ _ _ _) => result_block_t_raise "Unsupport LLVM terminator" 
  | CFG.Step insn =>  (* instruction *) block_part_CFG_Step insn CFG pc k e
end.



CoFixpoint block_reason_step_sem (CFG:mcfg) (s:state) : result (Trace state) :=
  match (block_reason_stepD CFG s) with
  | Success (Step s') => Tau s (Success (block_reason_step_sem CFG s'))
  | Success (Jump s') =>  (Tau s (block_reason_step_sem CFG s'))
  | Success (Obs (Err s)) =>  (Vis (Err s))
  | Success (Obs (Fin s)) =>  (Vis (Fin s))
  | Success (Obs (Eff m)) =>  (Vis (Eff (effects_map (block_reason_step_sem CFG) m)))
  | Error (Step s') => Tau s (block_reason_step_sem CFG s')
  | Error (Jump s') =>  (Tau s (block_reason_step_sem CFG s'))
  | Error (Obs (Err s)) =>  (Vis (Err s))
  | Error (Obs (Fin s)) =>  (Vis (Fin s))
  | Error (Obs (Eff m)) =>  (Vis (Eff (effects_map (block_reason_step_sem CFG) m)))
  end.


Theorem reason_step_sem_equiv : forall CFG s a, block_reason_step_sem CFG s = a -> Reason_step_sem CFG s = a.
Proof. Admitted.
*)
