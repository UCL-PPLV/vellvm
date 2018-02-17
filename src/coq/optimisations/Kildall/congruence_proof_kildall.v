Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.Kildall.congruence_definition_kildall.
Require Import Vellvm.optimisations.Kildall.valueanalysis.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.optimisations.Kildall.static_eval.
Require Import Vellvm.optimisations.vellvm_tactics.
Require Import Vellvm.optimisations.local_cfg.

Require Import Vellvm.optimisations.maps.


Require Import Vellvm.optimisations.SSA_semantics.
Require Import Vellvm.optimisations.vellvm_tactics.

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
Proof. intros. repeat (apply functional_extensionality; intros).
       apply jump_unaffected. Qed.


Lemma stack_false_l : forall t (s:stack),  t :: s = s -> False.
Proof. intros. induction s. simpl in *.
       inversion H. apply IHs. inversion H.
       subst. rewrite H2. eauto. Qed.

Lemma stack_false_r : forall  t (s:stack),  s = t :: s -> False.
Proof. intros. induction s. simpl in *.
       inversion H. apply IHs. inversion H.
       subst. rewrite <- H2. eauto. Qed.

Lemma mem_false_r : forall (mem:seq dvalue) undef, mem = (mem ++ [:: undef])%list -> False.
Proof. intros. induction mem. simpl in *.
       inversion H. simpl in *. apply IHmem.
       inversion H. subst. rewrite <- H1. auto. Qed.

Lemma mem_false_l : forall (mem:seq dvalue) undef,  (mem ++ [:: undef])%list = mem -> False.
Proof. intros. induction mem. simpl in *.
       inversion H. apply IHmem. simpl in *.
       inversion H. subst. rewrite H1. auto. Qed.






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
  


Lemma congruence_correct1 : forall o m st mem (correct_instr: correct_instr1 o m) (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof. 
  pcofix CIH. intros. pfold.
  assert (memD mem (sem m st) = unroll(memD mem (sem m st))).
  destruct (memD mem (sem m st)); eauto. rewrite H. clear H.
  assert ( (memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))).
  destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H. clear H.

  dupl correct_instr.
  unfold correct_instr1 in correct_instr. dupl wf_program. 



  destruct st. destruct p.
simpl.    rewrite fetch_helper_equiv. rewrite <- incr_pc_unaffected.
unfold fetch_helper in *. unfold fetch, incr_pc in *; simpl in *. destruct p. simpl in *.
destr_eq ( find_function m fn).
destr_eq (find_block (blks (df_instrs d)) bk).
destr_eq (block_to_cmd b pt). destruct p; simpl in *.
destruct c. destruct o0. rewrite  find_function_entry_unaffected_V1.

inv sstate; simpl in *.

specialize (correct_instr mem fn bk pt i e s i0). eapply correct_instr in wf_program0; eauto.
unfold exec_code1 in wf_program0. unfold individual_step in wf_program0. unfold lift_err_d in wf_program0. simpl in *.
destruct pt; simpl in *.



destruct ( o {| fn := fn; bk := bk; pt := IId id |} m (IId id, i)), i; unfold lift_err_d; simpl in *; repeat break_goal; inv wf_program0; try constructor; try right; try eapply CIH; eauto.


(*OP*)
destruct op0.
eapply sound_succ_state; eauto; unfold successor_pc; unfold transfer'; unfold CFG.fetch; unfold fetch; unfold cfg_to_cmd; unfold pc_to_local_pc; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto; eapply ematch_update; eauto.




eapply stack_false_l in H6; inversion H6.
eapply mem_false_l in H; inversion H.

























eapply sound_succ_state; eauto; unfold  transfer', successor_pc, CFG.fetch, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto; eapply ematch_update; eauto; constructor.




eapply stack_false_r in H6; inversion H6.


rewrite Heqo3 in Heqo5. inversion Heqo5. subst. clear Heqo5. rewrite Heqo4 in Heqo6. inversion Heqo6. subst. clear Heqo6. clear H3. clear H4. eapply map_moad_preserves_length in Heqe0. eapply map_moad_preserves_length in Heqe1. 
inv wf_program. unfold wf_call_instr in wf_call. specialize (wf_call (mk_pc fn bk (IId id))). simpl in *. rewrite Heqo0 in wf_call. rewrite Heqo1 in wf_call. rewrite Heqo2 in wf_call.
specialize (wf_call id1 d1 args0  (t, ID_Global id1)). assert ( Some (CFG.Step (INSTR_Call (t, ID_Global id1) args0)) =  Some (CFG.Step (INSTR_Call (t, ID_Global id1) args0))) by auto. eapply wf_call in H; simpl in *; eauto.
eapply analyse_entrypoint in Heqo3; simpl in *; eauto. destruct Heqo3. destruct H0. econstructor; simpl in *; try econstructor; simpl in *; eauto. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. eapply compare_length_trans; eauto.





eapply stack_false_r in H7; inversion H7.
eapply stack_false_r in H6; inversion H6.
eapply mem_false_r in H; inversion H; eauto.
eapply mem_false_r in H; inversion H; eauto.





eapply sound_succ_state; simpl in *; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto; eapply ematch_update; eauto; try constructor.






eapply mem_false_r in H; inversion H; eauto.



destruct op.



eapply sound_succ_state; simpl in *; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto; eapply ematch_update; eauto.





eapply stack_false_l in H6; inversion H6.
eapply mem_false_l in H; inversion H; eauto.


eapply sound_succ_state; simpl in *; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto; eapply ematch_update; eauto; try constructor.




(***************** IVOID*)




destruct (o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)), i; simpl in *; eauto; unfold  lift_err_d; repeat (break_goal); try inv wf_program0; try constructor; try right; try eapply CIH; intros; eauto.




rewrite Heqo3 in Heqo5. inversion Heqo5. subst. clear Heqo5. rewrite Heqo4 in Heqo6. inversion Heqo6. subst. clear Heqo6. clear H4. clear H3. eapply map_moad_preserves_length in Heqe0.
eapply map_moad_preserves_length in Heqe1. 


inversion wf_program. subst. unfold wf_call_instr in *.
specialize (wf_call {| fn := fn; bk := bk; pt := (IVoid n) |}). unfold CFG.fetch in *. simpl in *. rewrite Heqo0 in wf_call. rewrite Heqo1 in wf_call. rewrite Heqo2 in wf_call.
specialize (wf_call id0). specialize (wf_call d1). specialize (wf_call args0). specialize (wf_call  (TYPE_Void, ID_Global id0)). simpl in *. 

assert ( Some (CFG.Step (INSTR_Call (TYPE_Void, ID_Global id0) args0)) =
         Some (CFG.Step (INSTR_Call (TYPE_Void, ID_Global id0) args0))) by eauto. eapply wf_call in H; eauto.
eapply analyse_entrypoint in Heqo3; eauto.
destruct Heqo3. destruct H0.

econstructor; simpl in *; eauto. econstructor; eauto. simpl in *. rewrite Heqo0. rewrite Heqo1.
exists ( (TYPE_Void, ID_Global id0)). exists (args0). exists n.
rewrite Heqo2. split; eauto. eapply compare_length_trans; eauto.




eapply stack_false_r in H7; inversion H7.
eapply stack_false_l in H7; inversion H7.



eapply sound_succ_state; simpl in *; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; simpl in *; eauto; eapply ematch_update; eauto; try constructor.
simpl in *; eauto. simpl in *.


(*TERMINATOR INSTRUCTIONS*)


rewrite jump_unaffected_v1.
simpl in *.
inv sstate.
destruct t; simpl in *; eauto; unfold lift_err_d; repeat (break_goal); try inv wf_program; constructor; right; eapply CIH; intros; eauto.

inv sstack; simpl in *. destruct q. simpl in *. destruct H1. destruct H. destruct H.
destruct ( find_function m fn0) eqn:?. destruct (find_block (blks (df_instrs d0)) bk0) eqn:?.
destruct ( block_to_cmd b0 (IId id)) eqn:?. destruct p. inv H. destruct o1. inv H0.




eapply sound_succ_state; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo3; try rewrite Heqo4;try rewrite Heqo5; simpl in *; eauto; eapply ematch_update; eauto; try constructor. inversion H0. inversion H0. inversion H0. inversion H0.




inv sstack; simpl in *. destruct p. simpl in *. destruct H1. destruct H. destruct H. destruct H.
destruct H0. destruct H1.

destruct ( find_function m fn0) eqn:?. destruct (find_block (blks (df_instrs d0)) bk0) eqn:?.
destruct (  block_to_cmd b0 (IVoid x1)) eqn:?. destruct p.  destruct o1. inv H1. inv H2.




eapply sound_succ_state; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd; simpl in *; try rewrite Heqo3; try rewrite Heqo4; try rewrite Heqo5; simpl in *; eauto. inv H2. inv H2. inv H2. inv H2.




unfold jump in *. simpl in *. unfold CFG.find_block_entry in *. simpl in *. rewrite Heqo0 in Heqe1. destruct ( find_block (blks (df_instrs d)) br1) eqn:?. simpl in *. unfold monad_fold_right in *.

remember ((fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end)). rewrite <- Heqp in Heqe1. destruct p. simpl in *. inv Heqe1. inv Heqe1.

eapply sound_succ_state; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd, find_block_pc,  CFG.find_block_entry; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; try rewrite Heqo3; simpl in *; eauto; constructor. inv Heqe1.









unfold jump in *. simpl in *. unfold CFG.find_block_entry in *. simpl in *. rewrite Heqo0 in Heqe1. destruct ( find_block (blks (df_instrs d)) br2) eqn:?. simpl in *. unfold monad_fold_right in *.

remember  ((fix
             monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                              (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                              (a : A) {struct l} : M A :=
               match l with
               | [::] => mret a
               | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
               end)). rewrite <- Heqp in Heqe1. destruct p. simpl in *. inv Heqe1. inv Heqe1.

eapply sound_succ_state; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd, find_block_pc,  CFG.find_block_entry; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; eauto. rewrite Heqo3. destruct ( find_block (blks (df_instrs d)) br1). simpl in *. eauto. simpl in *; eauto. constructor. inv Heqe1.





rewrite <- jump_v1_equiv in Heqe0.
dupl Heqe0. 




unfold jump_v1 in  Heqe1. simpl in *. unfold CFG.find_block_entry in Heqe1. simpl in *. rewrite Heqo0 in Heqe1. destr_eq (find_block (blks (df_instrs d)) br ). simpl in *. destr_eq ( jump_monad e (blk_phis b0) bk). inv Heqe1. dupl Heqs1. eapply jump_monad3 in Heqs0. destruct Heqs0. destruct H. rewrite H in Heqs1. inversion Heqs1. subst. clear Heqs1. inversion Heqe1. subst. clear Heqe1.
eapply sound_succ_state; eauto; unfold transfer', CFG.fetch, successor_pc, fetch, cfg_to_cmd, find_block_pc,  CFG.find_block_entry; simpl in *; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; eauto. rewrite Heqo3.  simpl in *; eauto. rewrite Heqo3. eauto. eapply add_multiple_correct; eauto. inv Heqe1. Qed.


