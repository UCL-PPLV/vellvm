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



Lemma stepD_equiv : forall o m st  (correct_instr: correct_instr o m) (wf_program: wf_program m) (sstate: sound_state m st), stepD (modul_opt o m) st = stepD m st. Proof. intros. destruct st. destruct p. simpl in *. rewrite fetch_helper_equiv. rewrite <- incr_pc_unaffected. unfold fetch_helper. destruct p. simpl in *.


remember (find_function m fn). destruct o0; eauto. 
remember (find_block (blks (df_instrs d)) bk). destruct o0; eauto.
remember ( block_to_cmd b pt). destruct o0; eauto.
destruct p; simpl in *. destruct c; simpl in *; auto.
destruct o0; simpl in *; eauto.



unfold congruence_definition.correct_instr in correct_instr.
specialize (correct_instr fn bk pt i e s i0). eapply correct_instr in wf_program; eauto. unfold individual_step in wf_program; simpl in *; eauto. rewrite <- wf_program.
clear wf_program.


destruct pt; simpl in *; eauto.
destruct (o {| fn := fn; bk := bk; pt := IId id |} m (IId id, i)); eauto.
destruct fn0; simpl in *; eauto.
destruct i1; simpl in *; eauto. rewrite find_function_entry_unaffected; eauto.
destruct ( o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)); eauto.
destruct fn0; eauto. destruct i1; simpl in *; eauto. rewrite find_function_entry_unaffected; eauto.

destruct t; simpl in *; eauto. destruct v. simpl in *. destruct (eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; rewrite jump_unaffected; eauto. rewrite jump_unaffected; eauto. Qed.




  Lemma beq_local_eq : forall id, beq_local_id id id = true.
  Proof. intros. unfold beq_local_id. unfold decide. destruct (eq_dec_local_id id id); simpl in *; eauto. Qed.

Lemma beq_value_eq :forall x, beq_value x x = true.
Proof.
  intros. unfold beq_value. unfold decide. destruct (eq_dvalue x x); simpl in *; eauto.
Qed.


(*eval_op e None op0*) Print find_function_entry.
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
Lemma congruence_correct : forall o m st mem (correct_instr: correct_instr o m) (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
  
Admitted.
Print correct_instr1.
Print find_function_entry.

Lemma find_function_entry_unaffected_V1: forall m o,
                                                                                                  find_function_entry (modul_opt o m) = find_function_entry m. Proof. intros. apply functional_extensionality. intros. rewrite find_function_entry_unaffected; auto. Qed.


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



Lemma op_mem_correct : forall op e mem b a id,
(eval_op e None op = inr (List.nth_default undef mem a)) -> 
(substring (value_analysis (prep_block b) (IId id)) e = true) ->   (substring
    (transfer (value_analysis (prep_block b) (IId id))
       (IId id, CFG.Step (INSTR_Op op)))
    (add_env id (List.nth_default undef mem a) e) = true).
Proof. intros. unfold transfer. simpl in *; destruct op; destruct e0; simpl in *; simpl in *; inversion H; repeat rewrite beq_local_eq; repeat rewrite beq_value_eq; simpl in *; eauto.
Qed.

Lemma op_correct : forall b id e op0 v0 op, eval_op e None op0 = inr v0 -> 
 eval_op e None op = inr v0 ->  substring (value_analysis (prep_block b) (IId id)) e = true ->
substring
    (transfer (value_analysis (prep_block b) (IId id))
       (IId id, CFG.Step (INSTR_Op op0))) (add_env id v0 e) = true.
Proof. intros. unfold transfer. simpl in *. destruct op0; simpl in *; eauto. destruct e0; simpl in *; repeat rewrite beq_local_eq; simpl in *; auto; simpl in *; inversion H; rewrite beq_value_eq; simpl in *; eauto. Qed.

Hint Resolve op_correct.
Hint Resolve op_mem_correct.

  
Lemma congruence_correct1 : forall o m st mem (correct_instr: correct_instr1 o m) (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof.
  pcofix CIH. intros. pfold.
  assert (memD mem (sem m st) = unroll(memD mem (sem m st))). destruct (memD mem (sem m st)); eauto. rewrite H. clear H.
       assert ( (memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))). destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H. clear H.

simpl in *. unfold stepD. destruct st. destruct p. destruct p. 

rewrite fetch_helper_equiv. rewrite <- incr_pc_unaffected.
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

specialize (correct_instr mem fn bk pt i e s i0). dupl wf_program.  apply correct_instr in wf_program0; eauto.

unfold exec_code1 in wf_program0; simpl in *. dupl wf_program0. unfold individual_step in wf_program0. simpl in *.

destruct pt.

rewrite  find_function_entry_unaffected_V1.
inv sstate.

destruct ( o {| fn := fn; bk := bk; pt := IId id |} m (IId id, i)), i; simpl in *; eauto; unfold  lift_err_d in *; try (repeat break_goal); try inv wf_program0; try constructor; try right; try apply CIH; intros; eauto; try constructor; simpl in *; eauto.

+unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn bk b). unfold get_block in wf_program; simpl in *. rewrite Heqo0 in wf_program; rewrite Heqo1 in wf_program.

 assert ( Some b = Some b) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. unfold sound_env in *. unfold prep_selected_block in *. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo0 in senv. rewrite Heqo1 in senv. intros. inversion H0; subst. apply senv in H0. rewrite H.


eauto.


 

 apply  stack_false_l in H6; inversion H6.
 apply mem_false_l in H; inversion H.








 

 clear wf_program1; clear wf_program0.


+unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn bk b). unfold get_block in wf_program; simpl in *. rewrite Heqo0 in wf_program; rewrite Heqo1 in wf_program.

 assert ( Some b = Some b) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. unfold sound_env in *. unfold prep_selected_block in *. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo0 in senv. rewrite Heqo1 in senv. intros. inversion H0. inversion H2; subst. apply senv in H0. clear H1. rewrite H. unfold transfer; simpl in *. rewrite  beq_local_eq; eauto.



 

apply  stack_false_r in H6; inversion H6.








 constructor; eauto. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. rewrite Heqo5. rewrite H3. rewrite Heqo6. intros. inversion H; subst; eauto. rewrite H5. rewrite H4. eauto.

apply  stack_false_r in H7; inversion H7.
apply  stack_false_r in H6; inversion H6.
apply  mem_false_r in H; inversion H.
apply stack_false_l in H7; inversion H7.





unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn bk b). unfold get_block in wf_program; simpl in *. rewrite Heqo0 in wf_program; rewrite Heqo1 in wf_program.

assert ( Some b = Some b) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. unfold sound_env in *. unfold prep_selected_block in *. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo0 in senv. rewrite Heqo1 in senv. intros. inversion H0. inversion H2; subst. apply senv in H0. clear H1. rewrite H.


unfold transfer; simpl in *. rewrite beq_local_eq; simpl in *; eauto.



apply  mem_false_r in H; inversion H.





 
unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn bk b). unfold get_block in wf_program; simpl in *. rewrite Heqo0 in wf_program; rewrite Heqo1 in wf_program.

assert ( Some b = Some b) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. unfold sound_env in *. unfold prep_selected_block in *. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo0 in senv. rewrite Heqo1 in senv. intros. inversion H0. inversion H2; subst. apply senv in H0. clear H1. rewrite H.

eauto.


apply stack_false_l in H6; inversion H6.
 


apply  mem_false_l in H; inversion H.


 unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn bk b).  
 clear wf_program1. clear wf_program0. clear correct_instr. clear H. unfold get_block in wf_program; simpl in *. rewrite Heqo0 in wf_program. rewrite Heqo1 in wf_program. assert ( Some b = Some b ) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. unfold sound_env in *. unfold prep_selected_block in *. simpl in *. rewrite Heqo0. rewrite Heqo0 in senv. rewrite Heqo1. rewrite Heqo1 in senv. intros. inversion H0. subst. apply senv in H0.


 rewrite H. unfold transfer; simpl in *; eauto; rewrite  beq_local_eq; simpl in *; eauto.





rewrite  find_function_entry_unaffected_V1.
inv sstate.
destruct ( o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)), i; simpl in *; eauto; unfold lift_err_d in *; try (repeat break_goal); try inv wf_program0; eauto; try constructor; try right; try apply CIH; intros; eauto; try constructor; simpl in *; eauto.


constructor; eauto. unfold sound_env. simpl. rewrite Heqo0. rewrite Heqo1. exists  (TYPE_Void, ID_Global id0). exists args0. exists n. rewrite Heqo2. eauto.


unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. rewrite Heqo5. intro. rewrite H3. rewrite Heqo6. intros. inversion H. subst. rewrite H4. rewrite H5. auto.

remember ( (combine (df_args d0) l)).
remember ( {| fn := id; bk := init (df_instrs d0); pt := blk_entry_id b0 |}). eapply stack_false_r in H7. inversion H7.

apply stack_false_l  in H7.
inversion H7.




unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo0 in senv. rewrite Heqo1 in senv. intros. inversion H0; subst. apply senv in H0.





 unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn bk b).  
 clear wf_program1. clear wf_program0. clear correct_instr. clear H. unfold get_block in wf_program; simpl in *. rewrite Heqo0 in wf_program. rewrite Heqo1 in wf_program. assert ( Some b = Some b ) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto.
rewrite H. unfold transfer; simpl in *; eauto.





rewrite jump_unaffected_v1.


inv sstate; simpl in *.
destruct t; simpl in *; eauto; unfold lift_err_d in *; try (repeat break_goal); eauto; constructor; right; apply CIH; intros; eauto; constructor; subst; simpl in *; eauto.


inversion sstack; subst; eauto.  
inversion sstack; subst; eauto.  simpl in *.


unfold sound_env in sstack_env. unfold sound_env. unfold prep_selected_block in *. simpl in *. destruct q. simpl in *. remember (find_function m fn0). destruct o1. simpl in *.
remember ( find_block (blks (df_instrs d0)) bk0). destruct o1. simpl in *. intros.  inversion H; subst. destruct H1. destruct H0. destruct H0. remember (block_to_cmd b0 (IId id)). destruct o1. destruct p. simpl in *. destruct o1. inversion H0; subst. inversion H1. subst.
clear correct_instr. unfold SSA_semantics.wf_program in *. unfold get_block in *. specialize (wf_program fn0 bk0 b0). simpl in *. rewrite <- Heqo3 in wf_program. rewrite <- Heqo4 in wf_program.
assert ( Some b0 = Some b0 ) by auto. apply wf_program in H2. eapply value_analysis_equals_previous_val_analysis in H2; eauto. rewrite H2. unfold transfer; simpl in *; eauto.
rewrite  beq_local_eq; simpl in *; eauto. inversion H1. inversion H1. intros. inversion H.
intros. inversion H.

inv sstack; subst; simpl in *; eauto.
inv sstack; subst; simpl in *; eauto.

unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. destruct p. simpl in *.



destruct H1. destruct H. destruct H. destruct H. destruct H0. unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn0 bk0). unfold get_block in *. simpl in *.
destruct ( find_function m fn0 ) eqn:?.
destruct (find_block (blks (df_instrs d0)) bk0) eqn:?.
destruct ( block_to_cmd b0 (IVoid x1)) eqn:?. destruct p. simpl in *. destruct o1. inversion H0. inversion H1. subst. specialize (wf_program b0).
assert ( Some b0 = Some b0) by auto. apply wf_program in H2. eapply value_analysis_equals_previous_val_analysis in H2; eauto. intros. inversion H3; subst. rewrite H2. unfold transfer; simpl in *; eauto. inversion H1. inversion H1. inversion H1. inversion H1.



unfold jump in *. destruct ( find_block_entry m fn br1). destruct b0. unfold monad_fold_right in *.              remember ((fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp0 in Heqe1. destruct p0; simpl in *. inversion Heqe1. inversion Heqe1. simpl in *; eauto.
inversion Heqe1.





unfold jump in *. unfold find_block_entry in *. simpl in *. rewrite Heqo0 in Heqe1.

destruct (find_block (blks (df_instrs d)) br1) eqn:?. unfold block_to_entry in *. simpl in *. unfold monad_fold_right in *. remember (fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end). rewrite <- Heqp in Heqe1. destruct p; simpl in *. inversion Heqe1. inversion Heqe1. unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. rewrite Heqo0. dupl Heqo3. symmetry in Heqo4. apply find_block_equiv in Heqo4. subst. rewrite Heqo3.  intros. inversion H. subst. eauto. inversion Heqe1.






unfold jump in *. destruct ( find_block_entry m fn br2). destruct b0. unfold monad_fold_right in *.              remember ((fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp0 in Heqe1. destruct p0; simpl in *. inversion Heqe1. inversion Heqe1. simpl in *; eauto.
inversion Heqe1.




unfold jump in *. unfold find_block_entry in *. simpl in *. rewrite Heqo0 in Heqe1.

destruct (find_block (blks (df_instrs d)) br2) eqn:?. unfold block_to_entry in *. simpl in *. unfold monad_fold_right in *. remember (fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end). rewrite <- Heqp in Heqe1. destruct p; simpl in *. inversion Heqe1. inversion Heqe1. unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. rewrite Heqo0. dupl Heqo3. symmetry in Heqo4. apply find_block_equiv in Heqo4. subst. rewrite Heqo3.  intros. inversion H. subst. eauto. inversion Heqe1.





unfold jump in *. destruct ( find_block_entry m fn br). destruct b0. unfold monad_fold_right in *.              remember ((fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp0 in Heqe0. destruct p0; simpl in *. inversion Heqe0. inversion Heqe0. simpl in *; eauto.
inversion Heqe0.





unfold jump in *. unfold find_block_entry in *. simpl in *. rewrite Heqo0 in Heqe0.

destruct (find_block (blks (df_instrs d)) br) eqn:?. unfold block_to_entry in *. simpl in *. unfold monad_fold_right in *. remember (fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end). rewrite <- Heqp in Heqe0. destruct p; simpl in *. inversion Heqe0. inversion Heqe0. unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. rewrite Heqo0. dupl Heqo3. symmetry in Heqo4. apply find_block_equiv in Heqo4. subst. rewrite Heqo3.  intros. inversion H. subst. eauto. inversion Heqe0.

Qed.






(*
  
Lemma congruence_correct : forall o m st mem (correct_instr: correct_instr o m) (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).

Proof. pcofix CIH. intros. pfold.
  assert (memD mem (sem m st) = unroll(memD mem (sem m st))). destruct (memD mem (sem m st)); eauto. rewrite H. clear H.
       assert ( (memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))). destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H. clear H.





       
simpl in *. generalize sstate; intros.
eapply stepD_equiv  in sstate; eauto. rewrite sstate.

clear sstate.
unfold stepD. destruct st. destruct p. simpl in *. destruct p. simpl in *.


remember (find_function m fn). destruct o0; simpl in *; eauto.
remember (find_block (blks (df_instrs d)) bk ). destruct o0; simpl in *; eauto.
remember ( block_to_cmd b pt). destruct o0; simpl in *; eauto.
destruct p; simpl in *. destruct c. destruct o0; simpl in *; eauto. destruct pt, i; simpl in *; eauto.
       +remember ( eval_op e None op). destruct e0; simpl in *; eauto.
        constructor. right. apply CIH; eauto. unfold SSA_semantics.wf_program in *. specialize (wf_program fn bk b). unfold get_block in *; simpl in *. rewrite <- Heqo0 in wf_program. rewrite <- Heqo1 in wf_program. assert (Some b = Some b) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. inversion sstate0; subst; simpl in *. constructor; eauto; simpl in *. unfold sound_env in *; simpl in *. unfold prep_selected_block in *; simpl in *. rewrite <- Heqo0. rewrite <- Heqo1. rewrite <- Heqo0 in senv. rewrite <- Heqo1 in senv. intros. inversion H0; subst. apply senv in H0. rewrite H. unfold transfer; simpl in *; destruct op.
        destruct e0; simpl in *; eauto; inversion Heqe0; try rewrite beq_local_eq; try rewrite beq_value_eq; simpl in *; eauto.
       
       
       +destruct fn0; simpl in *. destruct i; simpl in *; eauto. unfold find_function_entry in *; simpl in *; eauto. remember ( find_function m id0). destruct o0; simpl in *; eauto. remember (find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o0; simpl in *; eauto.
        destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto.
        constructor. right. apply CIH; eauto; simpl in *. inversion sstate0; subst; simpl in *; eauto.
        constructor; simpl in *; eauto. constructor; simpl in *; eauto. rewrite <- Heqo0. rewrite <- Heqo1. rewrite <- Heqo2. simpl in *. eauto. unfold sound_env. simpl in *. unfold prep_selected_block; simpl in *. rewrite <- Heqo3. rewrite <- Heqo4. intros. inversion H; subst. eauto. 

















        constructor. right. apply CIH; inversion sstate0; simpl in *; subst; eauto. constructor; simpl in *; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *; eauto. rewrite <- Heqo0. rewrite <- Heqo1. rewrite <- Heqo0 in senv. rewrite <- Heqo1 in senv. intros. inversion H; subst. apply senv in H. unfold SSA_semantics.wf_program,  get_block in *; simpl in *; eauto. specialize (wf_program fn bk b). rewrite <- Heqo0 in wf_program. rewrite <- Heqo1 in wf_program. assert (Some b = Some b) by auto. apply wf_program in H0. eapply value_analysis_equals_previous_val_analysis in H0; simpl in *; eauto. rewrite H0. unfold transfer; simpl in *; eauto. clear H0. unfold beq_local_id. unfold decide. destruct (  eq_dec_local_id id id); simpl in *; eauto.
        




       +destruct ptr. remember (eval_op e (Some t0) v). destruct e0; simpl in *; eauto. destruct v0; simpl in *; eauto. constructor. right. apply CIH; eauto. inversion sstate0; simpl in *; subst; eauto. constructor; simpl in *; eauto. unfold SSA_semantics.wf_program in *. unfold get_block in *. simpl in *. specialize (wf_program fn bk b). rewrite <- Heqo0 in wf_program. rewrite <- Heqo1 in wf_program. assert (Some b = Some b) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo0. rewrite <- Heqo1.  rewrite <- Heqo0 in senv. rewrite <- Heqo1 in senv. intros. inversion H0; subst. apply senv in H0. rewrite H. unfold transfer; simpl in *; eauto. rewrite  beq_local_eq.  simpl in *; eauto.






       +destruct fn0; simpl in *; eauto. destruct i; simpl in *; eauto. unfold find_function_entry in *; simpl in *. remember ( find_function m id). destruct o0; simpl in *; eauto. remember ( find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o0; simpl in *; eauto.
        destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. constructor. right. eapply CIH; eauto. inversion sstate0; subst; simpl in *; eauto. constructor; simpl in *; eauto. constructor; simpl in *; eauto. rewrite <- Heqo0. rewrite <- Heqo1. exists (TYPE_Void, ID_Global id). exists args. exists n. rewrite <- Heqo2. split. eauto. eauto. unfold sound_env; simpl in *. unfold prep_selected_block; simpl in *; eauto. rewrite <- Heqo3. rewrite <- Heqo4. intros. inversion H; subst; eauto. 


        


       +destruct val, ptr; simpl in *; eauto. remember (eval_op e (Some t) v). remember (eval_op e (Some t0) v0). destruct e0, e1; simpl in *; eauto. destruct  v2; simpl in *; eauto. constructor. right. apply CIH; eauto. inversion sstate0; subst; simpl in *; eauto. constructor; simpl in *; eauto. unfold sound_env in *; simpl in *. unfold prep_selected_block in *; simpl in *. rewrite <- Heqo0. rewrite <- Heqo1. rewrite <- Heqo0 in senv. rewrite <- Heqo1 in senv. intros. inversion H; subst; simpl in *; eauto. apply senv in H. unfold SSA_semantics.wf_program in *. specialize (wf_program fn bk b).  unfold get_block in *; simpl in *. rewrite <- Heqo0 in wf_program. rewrite <- Heqo1 in wf_program. assert (Some b = Some b) by auto. apply wf_program in H0. eapply value_analysis_equals_previous_val_analysis in H0; eauto. rewrite H0. unfold transfer; simpl in *; eauto.



        *destruct t; simpl in *; eauto.
       +destruct v. remember ( eval_op e (Some t) v). destruct e0; simpl in *; eauto. destruct s; simpl in *; eauto. destruct f; simpl in *; eauto. constructor; right. apply CIH; eauto. inversion sstate0; simpl in *; subst; eauto. constructor; simpl in *; eauto. inversion sstack; simpl in *; eauto. inversion sstack; simpl in *; subst; eauto. destruct q; simpl in *; eauto.

unfold sound_env; simpl in *. unfold prep_selected_block in *; simpl in *. remember (find_function m fn0). destruct o1; simpl in *; eauto. remember (find_block (blks (df_instrs d0)) bk0). destruct o1; simpl in *; eauto. destruct H1. destruct H. destruct H. simpl in *. remember ( block_to_cmd b0 (IId id)). destruct o1. destruct p. simpl in *. inversion H; subst. destruct o1. inversion H0; subst. symmetry in Heqo5. unfold sound_env in sstack_env. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo3 in sstack_env. rewrite <- Heqo4 in sstack_env. intros. inversion H1; subst. apply sstack_env in H1. clear H0. clear H.  unfold SSA_semantics.wf_program in wf_program. simpl in *. specialize (wf_program fn0 bk0 b0). unfold get_block in *; simpl in *. rewrite <- Heqo3 in wf_program. rewrite <- Heqo4 in wf_program. assert(Some b0 = Some b0) by auto. apply wf_program in H. eapply value_analysis_equals_previous_val_analysis in H; eauto. rewrite H. unfold transfer; simpl in *; eauto. rewrite beq_local_eq; simpl in *; eauto. inversion H0. inversion H0. intros. inversion H. intros. inversion H. 

        

        
       +destruct s; simpl in *; eauto. destruct f; simpl in *; eauto. constructor. right; apply CIH; eauto. inversion sstate0; simpl in *; subst; eauto. inversion sstack; simpl in *; subst; eauto. constructor; simpl in *; eauto. unfold sound_env. simpl in *. unfold prep_selected_block. simpl in *. destruct p. simpl in *. remember (find_function m fn0). destruct o1; simpl in *.
remember ( find_block (blks (df_instrs d0)) bk0). destruct o1; simpl in *; eauto. destruct H1. destruct H. destruct H. destruct H. destruct H0. remember ( block_to_cmd b0 (IVoid x1)). destruct o1. destruct p; simpl in *; eauto. destruct o1. inversion H0. inversion H1. subst.  unfold SSA_semantics.wf_program in wf_program. specialize (wf_program fn0 bk0 b0). unfold get_block in *; simpl in *. rewrite <- Heqo3 in wf_program. rewrite <- Heqo4 in wf_program. assert (Some b0 = Some b0) by auto. apply wf_program in H2.  eapply value_analysis_equals_previous_val_analysis in H2; eauto. 
intros. inversion H3; subst. rewrite H2. unfold transfer; simpl in *; eauto. unfold sound_env in H. unfold prep_selected_block in H; simpl in *. rewrite <- Heqo3 in H. rewrite <- Heqo4 in H. apply H in H3. eauto. inversion H1. inversion H1. intros. inversion H. intros. inversion H.



       +destruct v; simpl in *; eauto. remember (eval_op e (Some t) v). destruct e0; simpl in *; eauto. destruct v0; simpl in *; eauto. remember (StepSemantics.Int1.eq x StepSemantics.Int1.one). destruct b0; simpl in *; eauto.



        inversion sstate0; subst; simpl in *; eauto.



        
        unfold jump in *. unfold find_block_entry in *; simpl in *. rewrite <- Heqo0.

remember ( find_block (blks (df_instrs d)) br1). destruct o1; simpl in *; eauto. unfold monad_fold_right in *. remember (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x0 :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x0)
                  end). rewrite <- Heqp. destruct p; simpl in *; eauto. constructor. right. apply CIH; eauto. constructor; simpl in *; eauto. unfold sound_env. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo0. generalize Heqo3; intro. apply find_block_equiv in Heqo4. subst. rewrite <- Heqo3. intros. inversion H; subst. eauto.


        
        unfold jump in *. unfold find_block_entry in *; simpl in *. rewrite <- Heqo0.

remember ( find_block (blks (df_instrs d)) br2). destruct o1; simpl in *; eauto. unfold monad_fold_right in *. remember (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x0 :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x0)
                  end). rewrite <- Heqp. destruct p; simpl in *; eauto. constructor. right. apply CIH; eauto. inversion sstate0; simpl in *; subst; eauto. 


constructor; simpl in *; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo0. generalize Heqo3; intro. apply find_block_equiv in Heqo4. subst. rewrite <- Heqo3. intros. inversion H; subst. eauto.



        
        unfold jump in *. unfold find_block_entry in *; simpl in *. rewrite <- Heqo0.

remember ( find_block (blks (df_instrs d)) br). destruct o1; simpl in *; eauto. unfold monad_fold_right in *. remember (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x0 :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x0)
                  end). rewrite <- Heqp. destruct p; simpl in *; eauto. constructor. right. apply CIH; eauto. inversion sstate0; simpl in *; subst; eauto. constructor; simpl in *; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo0. generalize Heqo3; intro. apply find_block_equiv in Heqo4. subst. rewrite <- Heqo3. intros. inversion H; subst. eauto.
Qed.*)