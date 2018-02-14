Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Require Import Vellvm.optimisations.SSA_semantics.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.optimisations.StaticAnalysis.static_analysis.
Require Import Vellvm.optimisations.StaticAnalysis.static_analysis_proof.
Require Import Vellvm.optimisations.StaticAnalysis.congruence_definition.
Require Import Vellvm.optimisations.StaticAnalysis.congruence_proof.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.



(* LLVM IR is 3 address code. VELLVM IR permits infinite address code, but we only implement constant folding for 3 address code*)
Print  StepSemantics.Int1.int.
Definition get_value (a:aenv) (i:ident) :=
  match i with
  | ID_Global _ => SV (VALUE_Ident i)
  | ID_Local id => match get_from_aenv a id with
                   | Some (Some (DV (VALUE_Integer i))) => SV ((VALUE_Integer i))
                   | _ => SV (VALUE_Ident i)
                   end
                     
  end.


Definition substitute_value (a:aenv) (o:Ollvm_ast.value) :=
  match o with
  | SV (VALUE_Ident (ID_Local ident)) =>match get_from_aenv a ident with
                                        | Some (Some (DV (VALUE_Integer i))) => SV ((VALUE_Integer i))
                                        | _ => SV (VALUE_Ident (ID_Local ident))
                                        end
  | _ => o
  end.


Print modul_opt.


Definition optimise_val (o:Ollvm_ast.value) (b:seq (instr_id * cmd)) (r:raw_id) :=
  let abc := (value_analysis b (IId r)) in
  match o with
  | SV (VALUE_Ident (ID_Local ident)) =>  (get_value abc (ID_Local ident))
  | SV (OP_IBinop ibinop (TYPE_I 32)  (SV (VALUE_Ident (ID_Local ident)))  (SV (VALUE_Ident (ID_Local ident1)))) =>
  (SV (OP_IBinop ibinop (TYPE_I 32)  (substitute_value abc ( (SV (VALUE_Ident (ID_Local ident))))) (substitute_value abc ( (SV (VALUE_Ident (ID_Local ident1)))))))
  | rest => rest 
  end.


Lemma val_correct : forall id b e ins,  substring (value_analysis (prep_block b) (IId id)) e = true -> eval_op e None ins = eval_op e None (optimise_val ins (prep_block b) id).
Proof. intros.
       induction ins. induction e0; simpl in *; eauto.
destruct id0; simpl in *; eauto.
       

destruct (      get_from_aenv
                  (value_analysis (prep_block b) (IId id)) id0) eqn:?; simpl in *; eauto. destruct o; simpl in *; eauto.
eapply substring_get_in_l1_get_in_l2 in H; eauto. destruct v; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; rewrite H; eauto.

destruct t; simpl in *; eauto. destruct sz; simpl in *; eauto. destruct p; simpl in *; eauto. destruct p; simpl in *; eauto. destruct p; simpl in *; eauto. destruct p; simpl in *; eauto. destruct p; simpl in *; eauto. destruct p; simpl in *; eauto. destruct v1; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct id0; simpl in *; eauto. destruct v2; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct id1; simpl in *; eauto.
generalize H; intros.

destruct (get_from_aenv (value_analysis (prep_block b) (IId id)) id0) eqn:?; simpl in *; eauto.  destruct o; simpl in *; eauto. eapply substring_get_in_l1_get_in_l2 in H; eauto. destruct v; simpl in *; eauto.


destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 

 eapply substring_get_in_l1_get_in_l2 in H0; eauto.
 destruct e0; simpl in *; try destruct v; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; rewrite H0; simpl in *; eauto.



 destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; eauto.

 destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; eauto.

 


destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
eapply substring_get_in_l1_get_in_l2 in H0; eauto.

destruct v; simpl in *; try destruct v0; simpl in *; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; rewrite H0; simpl in *; eauto.

eauto. eauto.



destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
eapply substring_get_in_l1_get_in_l2 in H0; eauto.
unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; rewrite H0; simpl in *; destruct v; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; rewrite H0; simpl in *; eauto. eauto. eauto.


destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
eapply substring_get_in_l1_get_in_l2 in H0; eauto.

simpl in *. unfold eval_expr in *; simpl in *; unfold eval_expr; simpl in *; rewrite H.
rewrite H0. simpl in *. destruct v; simpl in *; eauto; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; rewrite H0; simpl in *; eauto. eauto. eauto.



destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
eapply substring_get_in_l1_get_in_l2 in H0; eauto.
unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; simpl in *; rewrite H0; simpl in *; destruct v; simpl in *; eauto; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; rewrite H0; simpl in *; eauto. auto. auto.




destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
eapply substring_get_in_l1_get_in_l2 in H0; eauto.
unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; simpl in *; rewrite H0; simpl in *; destruct v; simpl in *; eauto; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; rewrite H0; simpl in *; eauto. auto. auto.



       destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
eapply substring_get_in_l1_get_in_l2 in H0; eauto.
unfold eval_expr; simpl in *; unfold eval_expr; simpl in *; rewrite H; simpl in *; rewrite H0; simpl in *; destruct v; simpl in *; eauto; try destruct e0; simpl in *; eauto; unfold eval_expr; simpl in *; rewrite H0; simpl in *; eauto. auto. auto.

       destruct ( get_from_aenv
           (value_analysis (prep_block b) (IId id)) id1) eqn:?.  destruct o. 
       eapply substring_get_in_l1_get_in_l2 in H0; eauto.
       unfold eval_expr in *; simpl in *; unfold eval_expr; simpl in *; rewrite H0.        destruct ( lookup_env e id0); simpl in *; eauto.
       destruct v; simpl in *; eauto; try destruct e0; simpl in *; eauto; unfold eval_expr in *; simpl in *; eauto; rewrite H0; simpl in *; eauto. eauto. eauto. unfold eval_expr in *; simpl in *; eauto. unfold eval_expr in *.  simpl in *. destruct (lookup_env e id0) eqn:?; simpl in *; eauto. destruct (        get_from_aenv
                                                                                                                                                                                                                                                                                                                         (value_analysis (prep_block b) (IId id)) id1) eqn:?; simpl in *; eauto. destruct o; simpl in *; eauto.

       
       eapply substring_get_in_l1_get_in_l2 in H0; eauto. rewrite H0. simpl in *. destruct v0; simpl in *; eauto; try destruct e0; simpl in *; eauto; unfold eval_expr in *; simpl in *; rewrite H0; eauto. Qed.

Print opt.

(*pc -> mcfg -> instr_id * instr -> instr*)

Definition optimise_instr1 (p:pc) (m:mcfg) (i:instr_id * instr) :=
  match prep_selected_block m p with
  | None => snd i
  | Some a => match fst i, snd i with
                  | (IId id), INSTR_Op ins =>  INSTR_Op (optimise_val ins a id)
                  | _,_ => snd i
              end
  end.





Definition optimise_instr (p:pc) (m:mcfg) (i:instr_id * instr) :=
   match fst i, snd i with
   | (IId id), INSTR_Op ins => match prep_selected_block m p with
                               | None => snd i
                               | Some a => INSTR_Op (optimise_val ins a id)
                               end           
   | _,_ => snd i
   end.

Print opt.

  
Lemma const_prop  : forall m st mem (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt optimise_instr m) st)).
Proof. intros.  apply congruence_correct1; eauto.

       
       unfold correct_instr1; intros; eauto. unfold exec_code1. simpl in *. unfold individual_step.
unfold  lift_err_d; simpl in *.
simpl in *. inversion sstate0; subst; simpl in *.
destruct id; simpl in *; eauto. destruct instr; simpl in *; eauto.
unfold optimise_instr. simpl in *. unfold sound_env in senv. simpl in *. unfold prep_selected_block in *; simpl in *. destruct ( find_function m fn) eqn:?. destruct (find_block (blks (df_instrs d)) bk) eqn:?. assert ( Some (prep_block b) = Some (prep_block b)) by auto.
apply senv in H. eapply  val_correct in H; eauto.
rewrite <- H. try_resolve. try_resolve. try_resolve.
try_resolve. try_resolve. try_resolve. 



try_resolve. try_resolve. try_resolve. try_resolve. try_resolve. try_resolve.   try_resolve. unfold optimise_instr. simpl in *. try_resolve. Qed.