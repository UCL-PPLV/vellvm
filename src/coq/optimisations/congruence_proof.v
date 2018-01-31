Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.congruence_definition.
Require Import Vellvm.optimisations.static_analysis.
Require Import Vellvm.optimisations.static_analysis_proof.

Require Import Vellvm.optimisations.SSA_semantics.

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
        constructor; simpl in *; eauto. constructor; simpl in *; eauto. rewrite <- Heqo0. rewrite <- Heqo1. rewrite <- Heqo2. simpl in *. eauto. unfold sound_env in *; simpl in *; eauto. unfold prep_selected_block in *; simpl in *; eauto. rewrite <- Heqo3. rewrite <- Heqo4. intros. inversion H; subst. eauto. constructor. right. apply CIH; inversion sstate0; simpl in *; subst; eauto. constructor; simpl in *; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *; simpl in *; eauto. rewrite <- Heqo0. rewrite <- Heqo1. rewrite <- Heqo0 in senv. rewrite <- Heqo1 in senv. intros. inversion H; subst. apply senv in H. unfold SSA_semantics.wf_program,  get_block in *; simpl in *; eauto. specialize (wf_program fn bk b). rewrite <- Heqo0 in wf_program. rewrite <- Heqo1 in wf_program. assert (Some b = Some b) by auto. apply wf_program in H0. eapply value_analysis_equals_previous_val_analysis in H0; simpl in *; eauto. rewrite H0. unfold transfer; simpl in *; eauto. clear H0. unfold beq_local_id. unfold decide. destruct (  eq_dec_local_id id id); simpl in *; eauto.
        




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
Qed.