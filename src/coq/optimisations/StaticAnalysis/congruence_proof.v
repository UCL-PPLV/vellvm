Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.StaticAnalysis.congruence_definition.
Require Import Vellvm.optimisations.StaticAnalysis.static_analysis.
Require Import Vellvm.optimisations.StaticAnalysis.static_analysis_proof.

Require Import Vellvm.optimisations.SSA_semantics.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.





  Lemma beq_local_eq : forall id, beq_local_id id id = true.
  Proof. intros. unfold beq_local_id. unfold decide. destruct (eq_dec_local_id id id); simpl in *; eauto. Qed.

Lemma beq_value_eq :forall x, beq_value x x = true.
Proof.
  intros. unfold beq_value. unfold decide. destruct (eq_dvalue x x); simpl in *; eauto.
Qed.







Lemma find_function_entry_unaffected_V1: forall m o,
    find_function_entry (modul_opt o m) = find_function_entry m.
Proof. intros. apply functional_extensionality. intros. rewrite find_function_entry_unaffected; auto. Qed.









Lemma jump_unaffected_v1 : forall o m, jump (modul_opt o m) = jump m.
Proof. intros. apply functional_extensionality. intros.  apply functional_extensionality.
       intros.  apply functional_extensionality. intros.  apply functional_extensionality. intros.  apply functional_extensionality. intros.  apply jump_unaffected. Qed.
Print correct_instr1.


Lemma stack_false_l : forall t (s:stack),  t :: s = s -> False.
Proof. intros. induction s. simpl in *. inversion H. apply IHs. inversion H. subst. rewrite H2. eauto. Qed.

Lemma stack_false_r : forall  t (s:stack),  s = t :: s -> False.
Proof. intros. induction s. simpl in *. inversion H. apply IHs. inversion H. subst. rewrite <- H2. eauto. Qed.

Print memory.
Lemma mem_false_r : forall (mem:seq dvalue) undef, mem = (mem ++ [:: undef])%list -> False.
Proof. intros. induction mem. simpl in *. inversion H. simpl in *. apply IHmem. inversion H. subst. rewrite <- H1. auto. Qed.

Lemma mem_false_l : forall (mem:seq dvalue) undef,  (mem ++ [:: undef])%list = mem -> False.
Proof. intros. induction mem. simpl in *. inversion H. apply IHmem. simpl in *. inversion H. subst. rewrite H1. auto. Qed.



Lemma congruence_correct1 : forall o m st mem (correct_instr: correct_instr1 o m) (wfprogram: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof. 
  pcofix CIH. intros.
  assert (memD mem (sem m st) = unroll(memD mem (sem m st))).
  destruct (memD mem (sem m st)); eauto. rewrite H. clear H.
  assert ( (memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))). 
  destruct  (memD mem (sem (modul_opt o m) st)); eauto.
  rewrite H. clear H.

simpl in *. unfold stepD. destruct st. destruct p. destruct p. 

rewrite fetch_helper_equiv.
rewrite <- incr_pc_unaffected.
unfold fetch_helper.
unfold correct_instr1 in *.
unfold fetch, incr_pc in *.
simpl in *.


destruct ( find_function m fn) eqn:?; simpl in *; eauto.
destruct ( find_block (blks (df_instrs d)) bk) eqn:?; simpl in *; eauto.
destruct (block_to_cmd b pt) eqn:?; simpl in *; eauto.
destruct p; simpl in *; eauto.
simpl in *. destruct c; simpl in *; eauto.
destruct o0; simpl in *; eauto.
dupl correct_instr.


specialize (correct_instr mem fn bk pt i e s i0).
dupl wfprogram.
apply correct_instr in wfprogram0; eauto.
unfold exec_code1 in wfprogram0; simpl in *.
unfold individual_step in wfprogram0. simpl in *.
destruct pt.

rewrite  find_function_entry_unaffected_V1.
inv sstate. destruct ( o {| fn := fn; bk := bk; pt := IId id |} m (IId id, i)), i;
simpl in *; eauto; unfold  lift_err_d in *; try (repeat break_goal); inv wfprogram0; pfold; try constructor; try right; try eapply CIH; eauto; try constructor; simpl in *; eauto.

(*instr_op*)
induction wfprogram; simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *. rewrite Heqo0. rewrite Heqo1. intros. inversion H. subst. rewrite Heqo0 in senv. rewrite Heqo1 in senv. eapply senv in H. unfold block_uid in *. simpl in *. unfold get_block in *; simpl in *. specialize (buid fn bk b). rewrite Heqo0 in buid. rewrite Heqo1 in buid. assert (Some b = Some b) by auto. eapply buid in H0. eapply value_analysis_equals_previous_val_analysis in H0; eauto. rewrite H0. simpl in *. unfold transfer; simpl. destruct op0. destruct e0; simpl; try rewrite beq_local_eq; simpl; unfold eval_op in Heqe0; unfold eval_expr in Heqe0; simpl in Heqe0; inversion Heqe0; simpl; try rewrite beq_value_eq; simpl; eauto.




apply stack_false_l in H4; inversion H4.
apply mem_false_l in H; inversion H.


induction wfprogram; simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *. rewrite Heqo0. rewrite Heqo1. intros.  inversion H. subst. rewrite Heqo0 in senv. rewrite Heqo1 in senv. eapply senv in H. unfold block_uid in *. simpl in *. unfold get_block in *; simpl in *. specialize (buid fn bk b). rewrite Heqo0 in buid. rewrite Heqo1 in buid. assert (Some b = Some b) by auto. eapply buid in H0. eapply value_analysis_equals_previous_val_analysis in H0; eauto. rewrite H0. simpl in *. rewrite beq_local_eq. eauto.


apply stack_false_r in H4. inversion H4.



(*call*)

 constructor; eauto. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto.


 unfold sound_env. simpl in *. destruct p0. simpl in *. unfold find_function_entry in *. simpl in *. unfold prep_selected_block. simpl in *. destruct (find_function m id0) eqn:?. destruct ( find_block (blks (df_instrs d0)) (init (df_instrs d0))) eqn:?. simpl in *. inv Heqe0. rewrite Heqo3. rewrite Heqo4. intros. inversion H. subst. eauto.


simpl in *. inversion Heqe0. inversion Heqe0.

eapply stack_false_r in H5; inversion H5.
eapply stack_false_r in H4; inversion H4.
eapply mem_false_r in H; inversion H.
eapply mem_false_r in H; inversion H.






induction wfprogram; simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *. rewrite Heqo0. rewrite Heqo1. intros.  inversion H. subst. rewrite Heqo0 in senv. rewrite Heqo1 in senv. eapply senv in H. unfold block_uid in *. simpl in *. unfold get_block in *; simpl in *. specialize (buid fn bk b). rewrite Heqo0 in buid. rewrite Heqo1 in buid. assert (Some b = Some b) by auto. eapply buid in H0. eapply value_analysis_equals_previous_val_analysis in H0; eauto. rewrite H0. unfold transfer; simpl. rewrite beq_local_eq; eauto.



eapply mem_false_r in H; inversion H.






induction wfprogram; simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *. rewrite Heqo0. rewrite Heqo1. intros.  inversion H. subst. rewrite Heqo0 in senv. rewrite Heqo1 in senv. eapply senv in H. unfold block_uid in *. simpl in *. unfold get_block in *; simpl in *. specialize (buid fn bk b). rewrite Heqo0 in buid. rewrite Heqo1 in buid. assert (Some b = Some b) by auto. eapply buid in H0. eapply value_analysis_equals_previous_val_analysis in H0; eauto. rewrite H0. unfold transfer; simpl. destruct op. destruct e0; simpl; try rewrite beq_local_eq; simpl; unfold eval_op in Heqe0; unfold eval_expr in Heqe0; simpl in Heqe0; inversion Heqe0; simpl; try rewrite beq_value_eq; simpl; eauto.




eapply stack_false_l in H4; inversion H4.
eapply mem_false_l in H; inversion H.




induction wfprogram; simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *. rewrite Heqo0. rewrite Heqo1. intros.  inversion H0. subst. rewrite Heqo0 in senv. rewrite Heqo1 in senv. eapply senv in H0. unfold block_uid in *. simpl in *. unfold get_block in *; simpl in *. specialize (buid fn bk b). rewrite Heqo0 in buid. rewrite Heqo1 in buid. assert (Some b = Some b) by auto. eapply buid in H1. eapply value_analysis_equals_previous_val_analysis in H1; eauto. rewrite H1. unfold transfer; simpl. rewrite beq_local_eq. eauto.





rewrite  find_function_entry_unaffected_V1.
inv sstate.
destruct ( o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)), i; simpl in *; eauto; unfold lift_err_d in *; try (repeat break_goal); try inv wfprogram0; eauto; pfold; try constructor; try right; try eapply CIH; intros; eauto; try constructor; simpl in *; eauto.



constructor; eauto. simpl in *. rewrite Heqo0. rewrite Heqo1. exists  (TYPE_Void, ID_Global id). exists args0. exists n. rewrite Heqo2. eauto. unfold find_function_entry in *; simpl in *.
destruct ( find_function m id0) eqn:?. destruct ( find_block (blks (df_instrs d0)) (init (df_instrs d0))) eqn:?. simpl in *. inversion Heqe2. subst. unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. rewrite Heqo3. rewrite Heqo4. intros. inversion H. subst. eauto. 
simpl in *; inversion Heqe2. simpl in *; inversion Heqe2.




eapply stack_false_r in H5; inversion H5.
eapply stack_false_l in H5; inversion H5.


induction wfprogram; simpl in *.
unfold sound_env in *; simpl in *. unfold prep_selected_block in *; simpl in *. rewrite Heqo0. rewrite Heqo1. intros. inversion H0. subst. rewrite Heqo0 in senv. rewrite Heqo1 in senv. eapply senv in H0. unfold block_uid in *. specialize (buid fn bk b). unfold get_block in *; simpl in *. rewrite Heqo0 in buid. rewrite Heqo1 in buid. assert (Some b = Some b) by auto. apply buid in H1. eapply value_analysis_equals_previous_val_analysis in H1; eauto. rewrite H1. unfold transfer; simpl in *; eauto.



(*TERMINATORS*)





Admitted.