Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.



Print mcfg.


Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.



Print cfg.
Print block.

(*If all the functions are equal, then the execution is the same*)


Print find_function.

Definition function_equal :=
forall m1 m2 fid, find_function m1 fid = find_function m2 fid.



Definition jump_equal_trace_equiv := forall m1 m2 fn bk br2 e s, jump m1 fn bk br2 e s = jump m2 fn bk br2 e s.


Lemma jump_equal : function_equal -> jump_equal_trace_equiv.
Proof. unfold function_equal, jump_equal_trace_equiv.
intros.
unfold jump. simpl. unfold find_block_entry.
simpl.
generalize (H m1 m2 fn). intros. rewrite H0. simpl. destruct (find_function m2 fn); eauto. Qed.





Lemma function_equal_trace_equiv : (function_equal) -> forall mem m1 m2 s, (trace_equiv (memD mem (sem m1 s)) (memD mem (sem m2 s))).
Proof. intro func_equal. pcofix CIH. intros. pfold.


assert (memD mem (sem m1 s) = unroll (memD mem (sem m1 s))).
destruct (memD mem (sem m1 s)); simpl; eauto.
rewrite H. clear H.


assert ((memD mem (sem m2 s)) = unroll (memD mem (sem m2 s))). destruct (memD mem (sem m2 s)); eauto. rewrite H; clear H.
unfold function_equal in func_equal. destruct s. destruct p. destruct p.
simpl. unfold find_function_entry. simpl.



generalize (func_equal m1 m2 fn). intros. 
remember (find_function m1 fn) as A.
remember (find_function m2 fn) as B.
destruct A, B; simpl; inversion H; simpl; eauto. subst.
destruct ( find_block (blks (df_instrs d0)) bk); simpl; eauto.
destruct (block_to_cmd b pt); simpl; eauto.
destruct p; simpl; eauto.
destruct c; simpl; eauto.
destruct o; simpl; eauto.
destruct pt; simpl; eauto.
destruct i; simpl; eauto.
destruct (eval_op e None op); simpl; eauto.
destruct fn0; simpl; eauto.
destruct i; simpl; eauto.
generalize (func_equal m1 m2 id0); intros; simpl; eauto. inversion H0.
destruct (find_function m1 id0); simpl; eauto.
simpl. destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl; eauto.
destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl; eauto.
destruct ptr; simpl; eauto. destruct (eval_op e (Some t0) v); simpl; eauto.
destruct v0; simpl; eauto.
destruct i; simpl; eauto.
destruct fn0; simpl; eauto.
destruct i; simpl; eauto.
generalize (func_equal m1 m2 id); intros; simpl; eauto. inversion H0.
destruct (find_function m1 id ); simpl; eauto.
destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl; eauto.
destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl; eauto.
destruct t; simpl; eauto.
destruct val; simpl; eauto.
destruct ptr; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct (eval_op e (Some t0) v0); simpl; eauto.
destruct v2; simpl; eauto.
destruct t; simpl; eauto.
destruct v; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct s; simpl; eauto.
destruct f; simpl; eauto.
destruct s; simpl; eauto.
destruct f; simpl; eauto.
destruct v; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct v0; simpl; eauto.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl; eauto.
apply jump_equal in func_equal. unfold jump_equal_trace_equiv in func_equal.
specialize (func_equal m1 m2 fn bk br1 e s). rewrite func_equal.
destruct (jump m2 fn bk br1 e s); simpl; eauto.
apply jump_equal in func_equal. unfold jump_equal_trace_equiv in func_equal.
specialize (func_equal m1 m2 fn bk br2 e s). rewrite func_equal.
destruct (jump m2 fn bk br2 e s); simpl; eauto.
apply jump_equal in func_equal. unfold jump_equal_trace_equiv in func_equal.
specialize (func_equal m1 m2 fn bk br e s). rewrite func_equal.
destruct (jump m2 fn bk br e s); simpl; eauto.
Qed.




Print fetch.



Print find_block.
Print block.

Definition get_block (fid:function_id) (bid:block_id) (m:mcfg) : option block :=
match find_function m fid with
  | None => None
  | Some fn => find_block (blks (df_instrs fn)) bid
end.


(*With the same fid, bid, m1 and m2 yield some result.
The result, block_id are the same.
block_phis are the same
the stepD of the head of both are the same
the tl of the code is the same
the blk_term is also the same*)
Print block.





Definition block_same_phis (b1 b2:block) :=
if (decide (b1.(blk_phis) = b2.(blk_phis))) then true else false.


Definition block_same_id (b1 b2:block) :=
if (decide (b1.(blk_id) = b2.(blk_id))) then true else false.



Definition block_same_term (b1 b2: block) :=
if (decide (b1.(blk_term) = b2.(blk_term))) then true else false.

Print code.




Definition tl (c:code) :=
match c with
  | [::] => [::]
  | _ :: t => t
end.




Definition block_same_tl_code (b1 b2: block) := if decide (tl (b1.(blk_code)) = tl (b2.(blk_code))) then true else false.


Print block.

Print find_block_entry.
Print block_entry.

Print find_block_entry.
Print block_entry.
Print find_function.


(*Either the first instruction of a block is the first of the list, if the list is empty then the terminator*)
Definition hdb (b:block) :=
match b.(blk_code) with
  | [::] => None
  | h :: _ => Some h
end.

Print sem.
Definition hd_block_equal m1 m2 fnid bkid b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => forall e s mem, step_trace_exec 0 (sem m1 ((mk_pc fnid bkid h1, e, s))) mem = step_trace_exec 0 (sem m2 ((mk_pc fnid bkid h2, e, s))) mem
  | _, _ => False
end.
Print hdb.

Definition hd_fst_block_equal b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => h1 = h2
  | _, _ => False
end.




Definition tl_block_equal b1 b2 :=
tl (b1.(blk_code)) = tl (b2.(blk_code)).
Print fst.
Print hd.

Definition list_equal (b:block) :=
match hdb b with
  | None => [::]
  | Some h => (h :: tl b.(blk_code))
end.


Definition head (b:block) :=
match b.(blk_code) with
  | [::] => [::]
  | h :: t => [::h]
end.
Print find_function.
Print definition.
Print cfg.

(*(if (decide (fn1.(df_prototype) = fn2.(df_prototype))) then True else False) /\*)


Definition fulldefinition (m1 m2: mcfg) :=
forall fnid fn1 fn2, 
(*Fetching a function_id (fnid) always returns some result*)
(find_function m1 fnid = Some fn1) /\ (find_function m2 fnid = Some fn2) /\

(*These bits of definition are all equal*)

(*ADD DF_PROTOTYPE*)
(if (decide (fn1.(df_args) = fn2.(df_args))) then True else False) /\


(*Convert definition to CFG*)
forall cfg cfg1, (df_instrs fn1) = cfg /\ (df_instrs fn2) = cfg1 /\
(if (decide ((init cfg) = (init cfg1))) then True else False) /\
(*These bits of the CFG are all equal*)

forall bkid bk1 bk2,
(*Fetching a block_id (bkid) always returns some result*)
(find_block (blks (df_instrs fn1)) bkid = Some bk1) /\ (find_block (blks (df_instrs fn2)) bkid = Some bk2) /\


(*The blk_id, blk_phis and the blk_term are all equal*)
(if (decide (bk1.(blk_id) = bk2.(blk_id))) then True else False) /\
(if (decide (bk1.(blk_phis) = bk2.(blk_phis))) then True else False) /\
(if (decide (bk1.(blk_term) = bk2.(blk_term))) then True else False) /\
hd_fst_block_equal bk1 bk2 /\


(*The execution of the head of both blocks are equal*)
hd_block_equal m1 m2 fnid bkid bk1 bk2 /\


(*The body of both blocks are equal *)
tl_block_equal bk1 bk2 /\

bk1.(blk_code) = head bk1 ++ tl bk1.(blk_code) /\
bk2.(blk_code) = head bk2 ++ tl bk2.(blk_code)

.

Lemma test123 : forall prog prog1, fulldefinition prog prog1 -> forall st mem, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog1 st)).
Proof. intros prog prog1 H. pcofix CIH.
intros. pfold.


assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))).
destruct (memD mem (sem prog st)); eauto. rewrite H0. clear H0.

assert ((memD mem (sem prog1 st)) = unroll (memD mem (sem prog1 st))).
destruct (memD mem (sem prog1 st)); eauto. rewrite H0. clear H0.


destruct st. destruct p. destruct p.
generalize H. intros. unfold fulldefinition in H0.
specialize (H0 fn). simpl.

remember (find_function prog fn) as find_func_fn.
remember (find_function prog1 fn) as find_func_fn1.

destruct find_func_fn, find_func_fn1; simpl in *; eauto.
+specialize (H0 d d0). destruct H0. clear H0. destruct H1. clear H0.
unfold is_left in *. destruct (decide (df_args d = df_args d0)).
destruct H1. 
clear H0.
remember (find_block (blks (df_instrs d)) bk) as find_block_fn.
remember (find_block (blks (df_instrs d0)) bk) as find_block_fn1.
destruct find_block_fn, find_block_fn1. unfold block_to_cmd.
specialize (H1 (df_instrs d) (df_instrs d0)). destruct H1. clear H0. destruct H1. clear H0.
destruct d. simpl in *. destruct (decide (init df_instrs = init (Ollvm_ast.df_instrs d0))).
simpl in *. destruct H1. clear H0. specialize (H1 bk). unfold blk_term_id in *.
unfold blk_term in *. simpl in *. specialize (H1 b b0). destruct H1. clear H0. destruct H1. clear H0.
destruct b, b0. simpl in *.
unfold hd_fst_block_equal in *. unfold tl_block_equal in *. simpl in *.
destruct (decide (blk_id = blk_id0)), (decide (blk_phis = blk_phis0)), 
(decide (blk_term = blk_term0)).

destruct H1. clear H0. destruct H1. clear H0. destruct H1.
clear H0.
destruct H1. destruct H1. destruct H2.
destruct H3. subst. unfold hd_block_equal in H1.
unfold hdb in *. simpl in *. destruct blk_code, blk_code0; simpl in *; eauto; try inversion H1.
destruct p. inversion H0. destruct p, p0. subst.
destruct blk_term0. simpl in *. specialize (H1 e s mem).
destruct (decide (i = pt)), (decide (pt = i1)); simpl in *; eauto.
admit. admit. rewrite <- Heqfind_func_fn in H1. destruct df_instrs. simpl in *.
rewrite <- Heqfind_block_fn in H1. unfold block_to_cmd in H1. unfold blk_term_id in H1.
simpl in *.

rewrite <- Heqfind_func_fn1 in H1. unfold block_to_cmd in H1. unfold blk_term_id in H1.
rewrite <- Heqfind_block_fn1 in H1. unfold blk_term in H1. simpl in H1.
destruct (decide (i = i1)), (decide (i1 = i1)); simpl in *; subst; simpl in *.
admit. admit.





remember (match i1 with
           | IId id =>
               match i2 with
               | INSTR_Op op =>
                   do dv <- eval_op e None op;
                   Step
                     ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
                     add_env id dv e, s)
               | INSTR_Call (_, ID_Global fid) args =>
                   do fnentry <-
                   trywith ("stepD: no function " ++ string_of fid)
                     (find_function_entry prog1 fid);
                   let
                   'FunctionEntry ids pc_f := fnentry in
                    do dvs <-
                    map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                    Step
                      (pc_f, combine ids dvs,
                      KRet e id
                        {| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}
                      :: s)
               | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
               | INSTR_Alloca t _ _ =>
                   Obs
                     (Eff
                        (Alloca t
                           (fun a : value =>
                            ({|
                             fn := fn;
                             bk := bk;
                             pt := fallthrough blk_code0 i |}, 
                            add_env id a e, s))))
               | INSTR_Load _ _ (u, ptr) _ =>
                   do dv <- eval_op e (Some u) ptr;
                   match dv with
                   | DV _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_CodePointer _ =>
                       t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_Addr a =>
                       Obs
                         (Eff
                            (Load a
                               (fun dv0 : value =>
                                ({|
                                 fn := fn;
                                 bk := bk;
                                 pt := fallthrough blk_code0 i |},
                                add_env id dv0 e, s))))
                   | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
                   end
               | INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID"
               | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
               | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
               | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
               | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
               end
           | IVoid _ =>
               match i2 with
               | INSTR_Op _ => t_raise "ID / Instr mismatch void/non-void"
               | INSTR_Call (ret_ty, ID_Global fid) args =>
                   do fnentry <-
                   trywith ("stepD: no function " ++ string_of fid)
                     (find_function_entry prog1 fid);
                   let
                   'FunctionEntry ids pc_f := fnentry in
                    do dvs <-
                    map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                    match ret_ty with
                    | TYPE_I _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Void =>
                        Step
                          (pc_f, combine ids dvs,
                          KRet_void e
                            {| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}
                          :: s)
                    | TYPE_Half => t_raise "Call mismatch void/non-void"
                    | TYPE_Float => t_raise "Call mismatch void/non-void"
                    | TYPE_Double => t_raise "Call mismatch void/non-void"
                    | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                    | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                    | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                    | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                    | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                    | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                    | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                    end
               | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
               | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
               | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
               | INSTR_Store _ (t, val) (u, ptr) _ =>
                   do dv <- eval_op e (Some t) val;
                   do v <- eval_op e (Some u) ptr;
                   match v with
                   | DV _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_CodePointer _ =>
                       t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_Addr a =>
                       Obs
                         (Eff
                            (Store a dv
                               (fun _ : value =>
                                ({|
                                 fn := fn;
                                 bk := bk;
                                 pt := fallthrough blk_code0 i |}, e, s))))
                   | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
                   end
               | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
               | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
               | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
               | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
               end
           end) as TEST.


remember (           match i1 with
           | IId id =>
               match i0 with
               | INSTR_Op op =>
                   do dv <- eval_op e None op;
                   Step
                     ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
                     add_env id dv e, s)
               | INSTR_Call (_, ID_Global fid) args =>
                   do fnentry <-
                   trywith ("stepD: no function " ++ string_of fid)
                     (find_function_entry prog fid);
                   let
                   'FunctionEntry ids pc_f := fnentry in
                    do dvs <-
                    map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                    Step
                      (pc_f, combine ids dvs,
                      KRet e id
                        {| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}
                      :: s)
               | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
               | INSTR_Alloca t _ _ =>
                   Obs
                     (Eff
                        (Alloca t
                           (fun a : value =>
                            ({|
                             fn := fn;
                             bk := bk;
                             pt := fallthrough blk_code0 i |}, 
                            add_env id a e, s))))
               | INSTR_Load _ _ (u, ptr) _ =>
                   do dv <- eval_op e (Some u) ptr;
                   match dv with
                   | DV _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_CodePointer _ =>
                       t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_Addr a =>
                       Obs
                         (Eff
                            (Load a
                               (fun dv0 : value =>
                                ({|
                                 fn := fn;
                                 bk := bk;
                                 pt := fallthrough blk_code0 i |},
                                add_env id dv0 e, s))))
                   | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
                   | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
                   end
               | INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID"
               | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
               | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
               | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
               | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
               end
           | IVoid _ =>
               match i0 with
               | INSTR_Op _ => t_raise "ID / Instr mismatch void/non-void"
               | INSTR_Call (ret_ty, ID_Global fid) args =>
                   do fnentry <-
                   trywith ("stepD: no function " ++ string_of fid)
                     (find_function_entry prog fid);
                   let
                   'FunctionEntry ids pc_f := fnentry in
                    do dvs <-
                    map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                    match ret_ty with
                    | TYPE_I _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Void =>
                        Step
                          (pc_f, combine ids dvs,
                          KRet_void e
                            {| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}
                          :: s)
                    | TYPE_Half => t_raise "Call mismatch void/non-void"
                    | TYPE_Float => t_raise "Call mismatch void/non-void"
                    | TYPE_Double => t_raise "Call mismatch void/non-void"
                    | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                    | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                    | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                    | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                    | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                    | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                    | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                    | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                    end
               | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
               | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
               | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
               | INSTR_Store _ (t, val) (u, ptr) _ =>
                   do dv <- eval_op e (Some t) val;
                   do v <- eval_op e (Some u) ptr;
                   match v with
                   | DV _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_CodePointer _ =>
                       t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_Addr a =>
                       Obs
                         (Eff
                            (Store a dv
                               (fun _ : value =>
                                ({|
                                 fn := fn;
                                 bk := bk;
                                 pt := fallthrough blk_code0 i |}, e, s))))
                   | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                   | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
                   end
               | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
               | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
               | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
               | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
               | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
               end
           end) as TEST1.



















destruct i0, i2. inversion H1.
destruct (eval_op e None op), (eval_op e None op0); simpl in *; eauto.
inversion H1. admit. constructor. left.
assert ((memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog1
           ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
           add_env id v0 e, s)))) = unroll (memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog1
           ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
           add_env id v0 e, s))))).
destruct (memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog1
           ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
           add_env id v0 e, s)))); eauto. rewrite H0. clear H0.

assert   ((memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
           add_env id v e, s)))) = unroll   (memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
           add_env id v e, s))))).
destruct   (memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |},
           add_env id v e, s)))); eauto.
rewrite H0. clear H0. simpl. rewrite <- Heqfind_func_fn. destruct df_instrs. simpl in *.

induction i1, i0, i2; simpl in *; eauto. 
destruct (eval_op e None op),(eval_op e None op0); simpl in *; eauto.
simpl in *. eauto.
rewrite <- Heqfind_func_fn1 in H1.

destruct df_instrs. simpl in *. 
rewrite <- Heqfind_block_fn1 in H1. unfold block_to_cmd in H1. unfold blk_term_id in *. unfold blk_term in H1. simpl in *. subst.
destruct (decide (i = fallthrough blk_code0 i)), (decide (fallthrough blk_code0 i = IId id)). subst; simpl in *; eauto. rewrite <- e0 in e1. admit.
simpl in *.

+specialize (H0 d d). destruct H0. destruct H1. inversion H1.
+specialize (H0 d d). destruct H0. inversion H0.
Admitted.