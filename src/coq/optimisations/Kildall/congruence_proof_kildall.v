Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.Kildall.congruence_definition_kildall.
Require Import Vellvm.optimisations.Kildall.static_eval_valueanalysis.
Require Import Vellvm.optimisations.Kildall.static_eval_valuedomain.
Require Import Vellvm.optimisations.maps.

Print sound_state.

Require Import Vellvm.optimisations.SSA_semantics.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Print sound_stack.



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




Ltac inv t := inversion t; subst; clear t; eauto.
Ltac destr_eq t := destruct t eqn:?; simpl; eauto.
Ltac destr t := destruct t; simpl; eauto.
Ltac appl t y := generalize y; intro; apply t in y.






                                                                                                                                                                           
Lemma congruence_correct1 : forall o m st mem (correct_instr: correct_instr1 o m) (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof.
  pcofix CIH. intros. pfold.
  assert (memD mem (sem m st) = unroll(memD mem (sem m st))). destruct (memD mem (sem m st)); eauto. rewrite H. clear H.
  assert ( (memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))).



  destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H. clear H.



  dupl correct_instr.



  
simpl in *. unfold stepD. destruct st. destruct p. destruct p. 

rewrite fetch_helper_equiv. rewrite <- incr_pc_unaffected.
unfold fetch_helper.

unfold correct_instr1 in *.
unfold fetch, incr_pc in *.
simpl in *.


destr_eq (find_function m fn).
destr_eq ( find_block (blks (df_instrs d)) bk).
destr_eq (block_to_cmd b pt ).
destr p.
destr c.
destr o0.
specialize (correct_instr mem fn bk pt i e s i0).

appl correct_instr wf_program.
unfold exec_code1 in wf_program. simpl in *. 

rewrite  find_function_entry_unaffected_V1.
inv sstate.
unfold individual_step in *; simpl in *. destruct pt; simpl in *.
destruct ( o {| fn := fn; bk := bk; pt := IId id |} m (IId id, i)), i; simpl in *; eauto; unfold  lift_err_d in *; try (repeat break_goal); try inv wf_program. 
  +assert (fetch m (mk_pc fn bk (IId id)) = Some (CFG.Step (INSTR_Op op0))). unfold fetch. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto.

  +assert (incr_pc  m (mk_pc fn bk (IId id)) = Some (mk_pc fn bk i0)). unfold incr_pc; simpl. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto.


   
   constructor. right. eapply CIH; intros; eauto. destr_eq op0. simpl. destr_eq e0; eapply sound_succ_state; try apply AN; try rewrite H; simpl; unfold transfer'; try rewrite H; simpl; unfold get_successors; try rewrite H; try rewrite H0; simpl; eauto; try apply ematch_update; eauto; try constructor.
assert (eval_op e None (SV (VALUE_Integer x)) = inr (DV (VALUE_Integer x))). simpl in *. eauto. rewrite Heqe0 in H1. inversion H1. eauto.


   







  +eapply stack_false_l in H6. inversion H6.
  +apply false_mem in H; inversion H.
  +constructor; right; eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN; auto.
   unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eauto. unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eapply ematch_update; eauto; constructor; eauto. eauto.
  +SearchAbout stack. apply stack_false_r in H6. inversion H6.
  +constructor. right. eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN; eauto.
   unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2. unfold find_function_entry; simpl in *; rewrite Heqo3; rewrite Heqo4; simpl in *. eauto. unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. constructor. econstructor; eauto. simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto.
  +eapply stack_false_r in H7; inversion H7.
  +eapply stack_false_r in H6; inversion H6.
  +symmetry in H; eapply false_mem in H; inversion H.
  +eapply stack_false_l in H7; inversion H7.
  +constructor; right; eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN.
   unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eauto.  
   unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto.  eapply ematch_update; eauto; constructor; eauto. eauto.
  +symmetry in H; eapply false_mem in H; inversion H.
  +constructor; right; eapply CIH; intros; eauto. destruct op.




  +assert (fetch m (mk_pc fn bk (IId id)) = Some (CFG.Step (INSTR_Op (SV e0)))). unfold fetch. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto.

  +assert (incr_pc  m (mk_pc fn bk (IId id)) = Some (mk_pc fn bk i0)). unfold incr_pc; simpl. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto.

 destr_eq e0; eapply sound_succ_state; try apply AN; try rewrite H; simpl; unfold transfer'; try rewrite H; simpl; unfold get_successors; try rewrite H; try rewrite H0; simpl; eauto; try apply ematch_update; eauto; try constructor.
assert (eval_op e None (SV (VALUE_Integer x)) = inr (DV (VALUE_Integer x))). simpl in *. eauto. rewrite Heqe0 in H1. inversion H1. eauto.





  +eapply stack_false_l in H6; inversion H6.
  +eapply false_mem in H; inversion H.
  +constructor; right; eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN.
   unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eauto.
   unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto.  eapply ematch_update; eauto. constructor. eauto.



   destruct ( o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)), i; simpl in *; eauto; unfold lift_err_d in *; simpl in *; try (repeat break_goal); try inv wf_program.

  +constructor; right; eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN.
   unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; unfold find_function_entry; simpl in *; rewrite Heqo3; rewrite Heqo4; simpl in *; eauto. unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eauto. econstructor; eauto. exists (TYPE_Void, ID_Global id0). exists args0. exists n. simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl in *; eauto.
  +eapply stack_false_r in H7; inversion H7.
  +eapply stack_false_l in H7; inversion H7.
  +constructor; right; eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN. 
   unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eauto.
   unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto.  eauto. eauto. eauto.





 rewrite jump_unaffected_v1.
   destruct t; simpl in *; eauto.
  + 
    destruct v. destruct (eval_op e (Some t) v) eqn:?; simpl in *; eauto. destruct s; simpl in *; eauto. destruct f; simpl in *; eauto.





    inversion sstate; subst; eauto. simpl in *. inversion sstack; subst; eauto. simpl in *. destruct H1. destruct H. destruct H. destruct q. simpl in *. destr_eq ( find_function m fn0). destr_eq ( find_block (blks (df_instrs d0)) bk0). destr_eq ( block_to_cmd b0 (IId id)). destruct p. destruct o1. simpl in *. inversion H0; subst. inversion H. subst. clear H. clear H0. constructor. right. eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN0. unfold fetch; simpl in *; rewrite Heqo3; rewrite Heqo4; rewrite Heqo5; eauto. dupl Heqo3. eapply block_implies_successor in Heqo3; eauto. unfold transfer'; simpl in *; rewrite Heqo3; rewrite Heqo4; rewrite Heqo5; eauto. eauto. eauto. inversion H0. inversion H0. inversion H0. inversion H0.



  +destruct s; simpl in *; eauto. destruct f; simpl in *; eauto. constructor; right; eapply CIH; intros; eauto. inversion sstate; subst; simpl in *; eauto; clear sstate. inversion sstack; simpl in *; subst; clear sstack. destruct H1. destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct p. simpl in *. destr_eq (find_function m fn0). destr_eq (find_block (blks (df_instrs d0)) bk0). destr_eq ( block_to_cmd b0 (IVoid x1)). destruct p. destr o1. inversion H1; inversion H2; subst; clear H1; clear H2. eapply sound_succ_state. eapply H. unfold fetch; simpl in *; rewrite Heqo3; rewrite Heqo4; rewrite Heqo5; simpl in *; eauto. eauto. unfold transfer'; simpl in *; rewrite Heqo3; rewrite Heqo4; rewrite Heqo5; eauto. eauto. eauto. inversion H2. inversion H2. inversion H2. inversion H2.

  +destruct v. destr_eq (eval_op e (Some t) v). destr_eq v0. destr_eq (StepSemantics.Int1.eq x StepSemantics.Int1.one). unfold jump; simpl in *. unfold find_block_entry; simpl in *.
   destr_eq (find_function m fn). destr_eq ( find_block (blks (df_instrs d0)) br1). simpl in *.
unfold monad_fold_right. simpl in *. destr_eq ( (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x0 :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x0)
                  end)). constructor. right. eapply CIH; intros; eauto. simpl in *. unfold blk_entry_pc. simpl in *. clear Heqp. inversion sstate; subst; simpl in *; eauto. inversion Heqo0. subst. unfold blk_entry_id. simpl in *. eapply sound_succ_state. eapply AN. unfold fetch; simpl in *. rewrite Heqo3. rewrite Heqo1. rewrite Heqo2. eauto. unfold get_successors; simpl in *; rewrite Heqo3; rewrite Heqo1; rewrite Heqo2; unfold next_term. unfold block_entry_pc. simpl in *. unfold find_block_entry; simpl in *. rewrite Heqo3. rewrite Heqo4. unfold block_to_entry; simpl in *. destr_eq (find_block (blks (df_instrs d)) br2). unfold transfer'; simpl in *; rewrite Heqo3; rewrite Heqo1; rewrite Heqo2. eauto. eauto. eauto.



  +unfold jump; simpl in *; eauto. unfold find_block_entry; simpl in *.
rewrite Heqo0. destr_eq (find_block (blks (df_instrs d)) br2). unfold monad_fold_right. destr_eq ( (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x0 :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x0)
                  end)). constructor; right; eapply CIH; intros; eauto.  inversion sstate; subst; simpl in *. eapply sound_succ_state. eapply AN. unfold fetch; simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold blk_entry_pc. unfold blk_entry_id. simpl in *. unfold blk_term_id. simpl in *. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; unfold next_term. unfold block_entry_pc. unfold find_block_entry; simpl in *. rewrite Heqo0. rewrite Heqo3. destr_eq ( find_block (blks (df_instrs d)) br1). unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2. eauto. eauto. eauto.












  +unfold jump; simpl in *; eauto. unfold find_block_entry; simpl in *.
rewrite Heqo0. destr_eq (find_block (blks (df_instrs d)) br). unfold monad_fold_right. destr_eq ( (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x0 :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x0)
                  end)). constructor; right; eapply CIH; intros; eauto.  inversion sstate; subst; simpl in *. eapply sound_succ_state. eapply AN. unfold fetch; simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold blk_entry_pc. unfold blk_entry_id. simpl in *. unfold blk_term_id. simpl in *. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; unfold next_term. unfold block_entry_pc. unfold find_block_entry; simpl in *. rewrite Heqo0. rewrite Heqo3. unfold block_to_entry; simpl in *; eauto. unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eauto. eauto. Qed.

SearchAbout ematch.
Print AE.get.
Print aval. Print lookup_env.
Lemma ematch_get : forall e a id val, ematch e a -> AE.get id a = avalue val -> lookup_env e id = Some val.
  Proof. intros. unfold ematch in *. simpl in *. specialize (H id). rewrite H0 in H. simpl in *. inversion H; subst. unfold lookup_env_aenv in *. simpl in *. destr_eq (lookup_env e id). inversion H1. subst. eauto. inversion H1. Qed.