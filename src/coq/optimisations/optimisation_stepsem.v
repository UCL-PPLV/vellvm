Require Import Vellvm.StepSemantics.
Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util Vellvm.Memory.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG Vellvm.Effects.
Require Import paco.
Import ListNotations.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.


Definition term_ret_val op t e k pc :=
    do dv <- eval_op e (Some t) op;
      match k with
      | [] => Obs (Fin dv)
      | (KRet e' id p') :: k' => Jump (p', add_env id dv e', k')
      | _ => t_raise_p pc "IMPOSSIBLE: Ret op in non-return configuration" 
      end.


Definition term_ret_void k pc :=
    match k with
    | [] => Obs (Fin (DV (VALUE_Bool true)))
    | (KRet_void e' p')::k' => Jump (p', e', k')
    | _ => t_raise_p pc "IMPOSSIBLE: Ret void in non-return configuration"
    end.


Definition term_ret_br_two CFG op t e br1 br2 k pc:=
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


Definition term_ret_br CFG br pc k e:=
    do st <- jump CFG (fn pc) (bk pc) br e k;
    Jump st.


Definition term_ret_eval (CFG:mcfg) (t:terminator) s :=
  let '(pc, e, k) := s in
match t with
  |  (TERM_Ret (t, op)) => term_ret_val op t e k pc
  |  TERM_Ret_void => term_ret_void k pc
  |  (TERM_Br (t,op) br1 br2) => term_ret_br_two CFG op t e br1 br2 k pc
  |  (TERM_Br_1 br) => term_ret_br CFG br pc k e
             
  (* Currently unhandled LLVM terminators *)                                  
  |  (TERM_Switch _ _ _)
  |  (TERM_IndirectBr _ _)
  |  (TERM_Resume _)
  |  (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator" 
end.

Print cmd.


Definition step_eval_op op id e pc_next k:=
do dv <- eval_op e None op;
Step (pc_next, add_env id dv e, k).


Definition step_alloca t id pc_next e k : transition state := 
Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k)))).

Definition step_load e k u ptr pc_next id :=
do dv <- eval_op e (Some u) ptr;     
match dv with
| DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
| _ => t_raise "ERROR: Load got non-pointer value" 
end.

Definition step_store val t e ptr u pc_next k :=
do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
(* CHKoh: do dv <- eval_op e val; *)
do v <- eval_op e (Some u) ptr;
match v with 
| DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
|  _ => t_raise "ERROR: Store got non-pointer value" 
end.
Print pt.

Definition step_call CFG pt ret_ty pc_next fid args e k : transition state :=
do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end.

Definition CFG_step insn CFG s := 
let '(pc, e, k) := s in
do pc_next <- trywith "no fallthrough intsruction" (incr_pc CFG pc);
      match (pt pc), insn  with
      | IId id, INSTR_Op op => step_eval_op op id e pc_next k
      | IId id, INSTR_Alloca t _ _ => step_alloca t id pc_next e k 
      | IId id, INSTR_Load _ t (u,ptr) _ => step_load e k u ptr pc_next id
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => step_store val t e ptr u pc_next k
      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args => step_call CFG pt ret_ty pc_next fid args e k
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


Definition optimisedstepD (CFG:mcfg) (s:state) : transition state :=
  let '(pc, e, k) := s in
  do cmd <- trywith ("CFG has no instruction at " ++ string_of pc) (fetch CFG pc);
  match cmd with
  | Term (t) => term_ret_eval CFG t s
  | CFG.Step insn => CFG_step insn CFG s
  end.


CoFixpoint optimised_step_sem (CFG:mcfg) (s:state) : Trace state :=
  match (optimisedstepD CFG s) with
  | Step s' => Tau s (optimised_step_sem CFG s')
  | Jump s' => Tau s (optimised_step_sem CFG s')
  | Obs (Err s) => Vis (Err s)
  | Obs (Fin s) => Vis (Fin s)
  | Obs (Eff m) => Vis (Eff (effects_map (optimised_step_sem CFG) m))
  end.

Definition optimised_sem (CFG:mcfg) (s:state) : Trace () := hide_taus (optimised_step_sem CFG s).



Definition unroll_trace_state (t:Trace state) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.

Definition unroll_trace (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.

Definition unroll_effects A (e:effects A) :=
match e with
  | Alloca a b => Alloca a b
  | Load a b => Load a b

end.




Lemma stepD_equiv : forall CFG s, optimisedstepD CFG s = stepD CFG s.
Proof.
intros. unfold stepD. unfold optimisedstepD. destruct s. destruct p.
destruct (fetch CFG p); simpl; auto.
Qed.


Lemma step_sem_equiv : forall CFG s, trace_equiv (optimised_step_sem CFG s) (step_sem CFG s).
Proof.
pcofix CIH. intros. pfold.

(*unfold left*)
assert ((optimised_step_sem CFG s) = unroll_trace_state (optimised_step_sem CFG s)).
destruct (optimised_step_sem CFG s); eauto.
rewrite H. simpl. clear H.

(*unfold right*)
assert ((step_sem CFG s) = unroll_trace_state (step_sem CFG s)).
destruct ((step_sem CFG s)); eauto. rewrite H; simpl.
rewrite stepD_equiv.
destruct (stepD CFG s).
  +constructor. right. auto.
  +constructor. right. auto.
  +destruct m.
    *constructor. constructor. auto.
    *constructor. constructor.
    *constructor. constructor. simpl.


Admitted.

