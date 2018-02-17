Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.Kildall.general_congruence.
Require Import Vellvm.optimisations.Kildall.static_eval.
Require Import Vellvm.optimisations.vellvm_tactics.
Require Import Vellvm.CFG.

Require Import Vellvm.optimisations.maps.


Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.


Lemma find_function_entry_unaffected_V1: forall m o,
    find_function_entry (modul_opt o m) = find_function_entry m.
Proof. intros. apply functional_extensionality.
       intros. rewrite find_function_entry_unaffected; auto. Qed.


Lemma jump_unaffected_v1 : forall o m, jump (modul_opt o m) = jump m.
Proof. intros. apply functional_extensionality. intros.
       apply functional_extensionality. intros.
       apply functional_extensionality. intros.
       apply functional_extensionality. intros.
       apply functional_extensionality. intros.
       apply jump_unaffected. Qed.


Lemma stack_false_l : forall t (s:stack),  t :: s = s -> False.
Proof. intros. induction s. simpl in *.
       inversion H. apply IHs. inversion H.
       subst. rewrite H2. eauto. Qed.
Hint Resolve stack_false_l : tauto.

Lemma stack_false_r : forall  t (s:stack),  s = t :: s -> False.
Proof. intros. induction s. simpl in *.
       inversion H. apply IHs. inversion H.
       subst. rewrite <- H2. eauto. Qed.
Hint Resolve stack_false_r : tauto.

Lemma mem_false_r : forall (mem:seq dvalue) undef, mem = (mem ++ [:: undef])%list -> False.
Proof. intros. induction mem. simpl in *.
       inversion H. simpl in *. apply IHmem.
       inversion H. subst. rewrite <- H1. auto. Qed.
Hint Resolve mem_false_r : tauto.

Lemma mem_false_l : forall (mem:seq dvalue) undef,  (mem ++ [:: undef])%list = mem -> False.
Proof. intros. induction mem. simpl in *.
       inversion H. apply IHmem. simpl in *.
       inversion H. subst. rewrite H1. auto. Qed.

Hint Resolve mem_false_l : tauto.

Ltac break_congruence :=  break_inner_match_goal; simpl in *; eauto; try eapply trace_equiv_err; try eapply trace_equiv_fin.
Ltac try_break_congruence := try (repeat break_congruence); simpl in *; eauto; try eapply trace_equiv_err; try eapply trace_equiv_fin.





Ltac break_inner_match' t :=
  match t with
  (* | context[find_function_entry _ _] => unfold find_function_entry in *; break_inner_match' t*)
   | context[match ?X with _ => _ end] => break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

Ltac break_inner_match_goal :=
  match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

Ltac break_goal := unfold find_function_entry in *; break_inner_match_goal; simpl in *; eauto.
  

Ltac try_resolve := try (repeat break_goal); try constructor.

Print correct_instr.
Print exec_code1.
Print finish_item.



Lemma congruence_correct1 : forall P o m st mem
                                   (cor_instr: correct_instr P o m)
                                   (wf_prog: wf_program m) (sstate: P m st)

                                   (sstate_preserve: forall mem st st' mem1,
                                       P m st ->  exec_code1 mem m st = tauitem mem1 st'
                                                                                -> P m st'),
    trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof.
  
  intros. generalize dependent st. generalize dependent mem. pcofix CIH. intros. pfold.


  assert (memD mem (sem m st) = unroll(memD mem (sem m st))).
  destruct (memD mem (sem m st)); eauto. rewrite H. clear H.
  assert ( (memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))).
  destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H. clear H.

  dupl cor_instr.
  simpl in *.

  unfold correct_instr in *. simpl in *.
  dupl sstate. eapply cor_instr with (mem := mem) in sstate. unfold exec_code1.
  unfold exec_code1 in sstate.

  specialize (sstate_preserve mem st).

  
destruct st. destruct p. simpl in *. rewrite fetch_helper_equiv. rewrite <- incr_pc_unaffected.
rewrite fetch_helper_equiv in sstate. rewrite <- incr_pc_unaffected in sstate.
unfold fetch_helper in *. unfold fetch, incr_pc in *; simpl in *. destruct p. simpl in *.
destr_eq ( find_function m fn).
destr_eq (find_block (blks (df_instrs d)) bk).
destr_eq (block_to_cmd b pt). destruct p; simpl in *.
destruct c. destruct o0. rewrite  find_function_entry_unaffected_V1.
rewrite  find_function_entry_unaffected_V1 in sstate.


unfold exec_code1 in sstate_preserve. simpl in sstate_preserve. rewrite Heqo0 in sstate_preserve.
rewrite Heqo1 in sstate_preserve. rewrite Heqo2 in sstate_preserve.


destruct pt; simpl in *.












destruct ( o {| fn := fn; bk := bk; pt := IId id |} m (IId id, i)), i; simpl in *; eauto; unfold  lift_err_d; repeat (break_goal); try inv sstate; try constructor; try right; try eapply CIH; intros; eauto.




eapply stack_false_l in H6; inversion H6.
eapply mem_false_l in H; inversion H.
eapply stack_false_r in H6; inversion H6.



eapply stack_false_r in H7; inversion H7.
eapply stack_false_r in H6; inversion H6.
eapply mem_false_r in H; inversion H; eauto.
eapply mem_false_r in H; inversion H; eauto.
eapply mem_false_r in H; inversion H; eauto.
eapply stack_false_l in H6; inversion H6.
eapply mem_false_l in H; inversion H; eauto.






destruct (o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)), i; simpl in *; eauto; unfold  lift_err_d; repeat (break_goal); try inv sstate; try constructor; try right; try eapply CIH; intros; eauto.




eapply stack_false_r in H7; inversion H7.
eapply stack_false_l in H7; inversion H7.






simpl in *. eauto.

simpl in *.

unfold exec_code1 in sstate_preserve.
simpl in sstate_preserve.
rewrite Heqo0 in sstate_preserve.
rewrite Heqo1 in sstate_preserve.
rewrite  Heqo2 in sstate_preserve. simpl in *.

destruct t; simpl in *; eauto; unfold lift_err_d; simpl in *; repeat (break_goal); try inv sstate; try constructor; try right; try eapply CIH; intros; eauto.
Qed.



Require Import Vellvm.optimisations.Kildall.const_prop.
Require Import Vellvm.optimisations.Kildall.valueanalysis.
Require Import Vellvm.optimisations.Kildall.valuedomain.


Lemma eq_result_refl : forall a, eq_result a a.
Proof.  intros. destruct a; try constructor. destruct e; try constructor. Qed.
Hint Resolve eq_result_refl. SearchAbout find_function_entry.

Lemma  const_prop_equiv_instr : forall m, correct_instr sound_state (optimise_instr (analyse_program m)) m.
Proof. intros. unfold correct_instr.

       
 intros. inv sstate. destruct s. simpl in *. destruct p. simpl in *. unfold exec_code1. simpl in *. rewrite fetch_helper_equiv. unfold fetch_helper. rewrite <- incr_pc_unaffected. unfold fetch, incr_pc; simpl in *. destruct p. destr_eq (find_function m fn). destr_eq (find_block (blks (df_instrs d)) bk).
       
       destr_eq ( block_to_cmd b pt). destr p. destr o. unfold optimise_instr; simpl in *.
       destr c. destr pt.
         rewrite find_function_entry_unaffected_V1.
         unfold optimise_instr. simpl in *. rewrite AN. destr i0. rewrite <- val_correct; eauto. rewrite AN.
         rewrite find_function_entry_unaffected_V1. destr i0. rewrite jump_unaffected_v1. destr t. destr c. destr t. destr v. destr (eval_op e (Some t) v). destr v0. destr (StepSemantics.Int1.eq x StepSemantics.Int1.one). rewrite jump_unaffected_v1; eauto. rewrite jump_unaffected_v1; eauto. rewrite jump_unaffected_v1; eauto. Qed.

Hint Resolve const_prop_equiv_instr.




Lemma sound_state_pres : forall mem0 mem1 m st0 st' (wfprog:  wf_program m),  sound_state m st0 ->
  exec_code1 mem0 m st0 = tauitem mem1 st' -> sound_state m st'.


Proof. intros. inv H; simpl in *. destruct st0. destruct p. simpl in *. unfold exec_code1 in *. simpl in *. unfold fetch, incr_pc in *; simpl in *. destruct p; simpl in *. destr_eq (find_function m fn). destr_eq (find_block (blks (df_instrs d)) bk). destr_eq (block_to_cmd b pt). destr p; simpl in *. destr c. destr o. destr pt; destr i; simpl in *; inv H0; clear H0. destr_eq ( eval_op e None op); simpl in *; inv H2; clear H2.

       destruct op.
eapply sound_succ_state; simpl in *; eauto; unfold successor_pc, fetch, transfer',  local_cfg.fetch, local_cfg.cfg_to_cmd; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; simpl; eauto; eapply ematch_update; eauto.

(******)


destruct fn0. simpl in *. destruct i. simpl in *. unfold find_function_entry in *. simpl in *.

destr_eq (find_function m id0).

destr_eq ( find_block (blks (df_instrs d0)) (init (df_instrs d0))). simpl in *.
destr_eq (map_monad (fun '(t, op) => eval_op e (Some t) op) args). simpl in *. inversion H2. simpl in *. inversion H2. subst.

inversion wfprog. unfold wf_call_instr in wf_call. simpl in *.
specialize (wf_call (mk_pc fn bk (IId id))). simpl in *. rewrite Heqo in wf_call. rewrite Heqo0 in wf_call. rewrite Heqo1 in wf_call. specialize (wf_call id0 d0). specialize (wf_call args (t, ID_Global id0)). assert ((Some (CFG.Step (INSTR_Call (t, ID_Global id0) args)) =
 Some (CFG.Step (INSTR_Call (t, ID_Global id0) args)))) by auto. eapply wf_call in H0; eauto. eapply map_moad_preserves_length in Heqe0.
dupl Heqo2.
eapply analyse_entrypoint in Heqo2; eauto.
 simpl in *. destruct Heqo2. destruct H1. simpl in *.
econstructor; simpl in *. econstructor; simpl in *.  eauto. eauto. eauto. rewrite Heqo. rewrite Heqo0. rewrite Heqo1. eauto. eauto. eauto. eapply compare_length_trans; eauto. simpl in *. inv H2. simpl in *. inv H2. simpl in *. inv H2.

(*****)

eapply sound_succ_state; eauto;  unfold successor_pc, fetch, transfer',  local_cfg.fetch, local_cfg.cfg_to_cmd; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; simpl in *; eauto; eapply ematch_update; try constructor; eauto.




destruct ptr. destr_eq (eval_op e (Some t0) v); simpl in *; inv H2; clear H2. destr v0; simpl in *; inv H1; clear H1. eapply sound_succ_state; eauto;  unfold successor_pc, fetch, transfer',  local_cfg.fetch, local_cfg.cfg_to_cmd; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; simpl in *; eauto; eapply ematch_update; try constructor; eauto.
(*******)

destruct fn0. destruct i. unfold find_function_entry in *; simpl in *.
destr_eq (find_function m id); simpl in *.
destr_eq ( find_block (blks (df_instrs d0)) (init (df_instrs d0))). simpl in *. 
destr_eq (map_monad (fun '(t, op) => eval_op e (Some t) op) args). simpl in *.
inv H2. simpl in *. destruct t; inv H2; clear H2.



eapply map_moad_preserves_length in Heqe0.  inv wfprog. unfold wf_call_instr in *. simpl in *.
specialize (wf_call (mk_pc fn bk (IVoid n)) id d0 args  (TYPE_Void, ID_Global id)).
unfold fetch in *. simpl in *. rewrite Heqo in wf_call. rewrite Heqo0 in wf_call. rewrite Heqo1 in wf_call.

dupl Heqo2. eapply analyse_entrypoint in Heqo4; eauto. destruct Heqo4. destruct H0.


econstructor; simpl in *. econstructor; simpl in *; eauto. rewrite Heqo. rewrite Heqo0. exists  (TYPE_Void, ID_Global id).  exists (args). exists n.  rewrite Heqo1. split; eauto. eauto. eauto. eapply compare_length_trans; eauto. simpl in *. inv H2. inv H2. simpl in *. inv H2. 







(*******)
destr val. destr ptr. destr_eq ( eval_op e (Some t) v); destr_eq (eval_op e (Some t0) v0); simpl in *; inv H2; clear H2. destr v2; simpl in *; inv H1; clear H1.
eapply sound_succ_state; eauto;  unfold successor_pc, fetch, transfer',  local_cfg.fetch, local_cfg.cfg_to_cmd; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; simpl in *; eauto; eapply ematch_update; try constructor; eauto.


simpl in *. inversion H0.




destr t. destr v. destr ( eval_op e (Some t) v); simpl in *; inv H0; clear H0. destr s; inv H2; clear H2. destr f; inv H1; clear H1.
inv sstack. simpl in *. destruct q. simpl in *. destr_eq (find_function m fn0). destr_eq (find_block (blks (df_instrs d0)) bk0). destr_eq (block_to_cmd b0 (IId id)). simpl in *. destr p. destruct H2. destruct H0. destruct H0. inversion H0. subst. clear H0. destruct o0. simpl in *. inversion H1. subst. clear H1.  






eapply sound_succ_state; eauto; unfold transfer',  local_cfg.fetch,  local_cfg.cfg_to_cmd, successor_pc, fetch; simpl in *; try rewrite Heqo2; try rewrite Heqo3; try rewrite Heqo4; eauto; simpl in *; eauto; eapply ematch_update. eauto. constructor. inv H1. destruct H2. destruct H0. destruct H0. inversion H0.  destruct H2. destruct H0. destruct H0. inversion H0.   destruct H2. destruct H0. destruct H0. inversion H0. 





destr s; simpl in *; inv H0. destruct f; simpl in *; inv H0.



inv sstack; simpl in *. destruct H4. destruct H1. destruct H1. destruct H1. destruct H3. destruct H4. destruct p. simpl in *. destr_eq ( find_function m fn0). destr_eq (find_block (blks (df_instrs d0)) bk0). destr_eq (block_to_cmd b0 (IVoid x1)). destruct p. inversion H4. subst. clear H4. destr_eq o0. simpl in *. subst. inversion H5. subst. clear H5. eapply sound_succ_state; eauto;
                                                                                                                                                                                                                                                                                                                                                                  unfold transfer', fetch, successor_pc, local_cfg.fetch, local_cfg.cfg_to_cmd; simpl in *; try rewrite Heqo2; try rewrite Heqo3; try rewrite Heqo4; simpl; eauto. inv H5. inv H5. inv H5. inv H5.



destruct v. destr_eq ( eval_op e (Some t) v); simpl in *; inv H0; clear H0. destruct v0; simpl in *; inv H2; clear H2. destr_eq (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *.


unfold jump in *. unfold find_block_entry in *. simpl in *. rewrite Heqo in H1.
destr_eq ( find_block (blks (df_instrs d)) br1); simpl in *. unfold monad_fold_right in *. 

remember ( (fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end)). rewrite <- Heqp in H1. destruct p. simpl in *. inversion H1. simpl in *. inversion H1. subst. eapply sound_succ_state; eauto; unfold transfer', local_cfg.fetch, local_cfg.cfg_to_cmd,  successor_pc, fetch, find_block_pc, find_block_entry; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto. unfold ematch. intros. simpl. constructor. inv H1.



unfold jump in *. unfold find_block_entry in *. simpl in *. rewrite Heqo in H1. destr_eq (find_block (blks (df_instrs d)) br2). simpl in *. unfold monad_fold_right in *. remember ( (fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end)). rewrite <- Heqp in H1. clear Heqp. destruct p. simpl in *. inversion H1. simpl in *. inversion H1. subst. eapply sound_succ_state; eauto; unfold fetch, successor_pc, find_block_pc, find_block_entry, transfer',  local_cfg.fetch, local_cfg.cfg_to_cmd; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto. destr_eq ( find_block (blks (df_instrs d)) br1). unfold ematch. simpl in *. constructor. simpl in *. inv H1.



remember (jump m fn bk br e s). symmetry in Heqe0. destruct e0; simpl in *. inversion H0.

dupl Heqe0. dupl Heqe0. unfold jump in Heqe1. simpl in *. unfold find_block_entry in *. simpl in *.
rewrite Heqo in Heqe1. destr_eq (find_block (blks (df_instrs d)) br). clear Heqe1. SearchAbout jump.





eapply jump_phis_preserved in Heqe0; unfold get_block; simpl in *; try rewrite Heqo; try rewrite Heqo2; eauto.

destruct Heqe0. simpl in *.  destruct H1.




rewrite H1 in Heqe2. inv Heqe2. clear Heqe2. dupl Heqo2. symmetry in Heqo3. eapply find_block_equiv in Heqo3. subst. inv H0. subst. clear H0.

eapply sound_succ_state; eauto; unfold  local_cfg.fetch, transfer', successor_pc,fetch,  local_cfg.fetch,  local_cfg.cfg_to_cmd, find_block_pc, find_block_entry; simpl in *; try rewrite Heqo; try rewrite Heqo0; try rewrite Heqo1; eauto; simpl in *; try rewrite Heqo2; simpl in *; unfold blk_entry_pc; unfold blk_entry_id; eauto.
destruct b0. simpl in *. unfold blk_term_id. simpl in *. destruct blk_term. simpl in *. destruct blk_code. simpl in *. eauto. simpl in *. eauto. unfold combine_phis. simpl in *. 



eapply add_multiple_correct; eauto.
simpl in *. inversion Heqe1. simpl in *. inversion H0. simpl in *. inversion H0. simpl in *. inversion H0. simpl in *. inversion H0. simpl in *. inversion H0. simpl in *. inversion H0. simpl in *. inversion H0. Qed.

Hint Resolve sound_state_pres.



  




Lemma const_prop_equiv : forall mem m st (sstate:sound_state m st) (wf_prog: wf_program m), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt (optimise_instr (analyse_program m)) m) st)).
  Proof. intros. eapply congruence_correct1; eauto. Qed.