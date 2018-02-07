Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.Kildall.congruence_definition_kildall.
Require Import Vellvm.optimisations.Kildall.valueanalysis.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.optimisations.Kildall.static_eval.

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

Print Expr. Print typ. Print Ollvm_ast.typ.  Print instr.
   
                                                                                                                                                                           
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


   
   constructor. right. eapply CIH; intros; eauto; destr_eq op; destr_eq op0.
subst. eapply sound_succ_state. eapply AN. eapply H. unfold get_successors; simpl in *; rewrite H; rewrite H0; simpl in *; left; eauto. unfold transfer'; rewrite H.  eauto. 
apply ematch_update; eauto. 

destruct e1; simpl in *; eauto; try constructor; try inversion Heqe0; eauto; unfold eval_expr in *; unfold eval_aenv_expr; simpl in *; try destruct t; try destruct sz; try constructor; try destruct p; try constructor; try destruct p; try constructor. try destruct p; try constructor. try destruct p; try constructor. try destruct p; try constructor. try destruct p; try constructor. destruct p; try constructor. destruct v1; try constructor. destruct e1; try constructor. destruct v2; try constructor. destruct e1; try constructor.  simpl in *. inversion Heqe0. simpl. eauto. destruct v1; try constructor. destruct e1; try constructor. destruct v2; try constructor. destruct e1; try constructor; simpl in *; try inversion H2; try constructor. destruct v1; try constructor. destruct e1; try constructor. destruct v2; try constructor. destruct e1; try constructor; simpl in *. inversion H2; eauto. destruct p; try constructor.  destruct p; try constructor. destruct p; try constructor. destruct p; try constructor. destruct p; try constructor. destruct v1; try constructor. destruct e1; try constructor. destruct v2; try constructor. destruct e1; try constructor; simpl in *. inversion H2; eauto. destruct v1; try constructor. destruct e1; try constructor. destruct v2; try constructor. destruct e1; try constructor; simpl in *. inversion H2; eauto. destruct v1, v2; try constructor. destruct e1, e2; try constructor; simpl in *. inversion H2; eauto. eauto.














eapply stack_false_l in H6; inversion H6.
eapply mem_false_l in H; inversion H.






constructor. right. eapply CIH; intros; eauto. eapply sound_succ_state; try eapply AN.
unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; try rewrite Heqo2; eauto.
unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl in *; eauto.
unfold transfer'; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto.
eapply ematch_update; eauto; try constructor. eauto.




eapply stack_false_r in H6; inversion H6.
constructor. right. eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN. unfold fetch. rewrite Heqo0; simpl in *; rewrite Heqo1; rewrite Heqo2; eauto. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; unfold find_function_entry; simpl in *; rewrite Heqo5; simpl in ; rewrite Heqo6; simpl in *; inversion H4; inversion H3; subst; eauto. unfold transfer'; simpl in *; rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; eauto. eauto. econstructor; simpl in *; eauto. rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto.


eapply stack_false_r in H7; inversion H7.
eapply stack_false_r in H6; inversion H6.
symmetry in H; eapply mem_false_l in H; inversion H.
eapply stack_false_l in H7; inversion H7.


constructor. right. eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN. unfold fetch; simpl; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl in *; eauto. unfold transfer'; unfold fetch; simpl; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eapply ematch_add; eauto. eauto.


symmetry in H; eapply mem_false_l in H; inversion H.

destr_eq op.

constructor. right. eapply CIH; intros; eauto. eapply sound_succ_state. eapply AN. unfold fetch; simpl; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl in *; eauto. unfold transfer'; unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. unfold add_env. simpl in *. unfold eval_aenv_expr; simpl in *; destr_eq e0; simpl in *; try destr_eq t1; try inv Heqe0;

                                                                                                                                                                                                                                                                                                                                                                                             try destr_eq sz; try destr_eq p; try destr_eq p0; try destr_eq p1; try destr_eq p2; try destr_eq p3; try destr_eq p4; try destr_eq p5; try destr_eq v1; try destr_eq e0; try destr_eq v2; try destr_eq e1; try inv H0; try eapply ematch_update; eauto; constructor; eauto. eauto.



eapply stack_false_l in H6; inversion H6.
eapply mem_false_l in H; inversion H; eauto.


constructor; right; eapply CIH; intros; eauto.


eapply sound_succ_state. eapply AN. unfold fetch; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl in *; eauto. unfold get_successors; simpl in *; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl in *; eauto.


unfold transfer'; simpl in *; eauto; rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; eauto. eapply ematch_add; eauto. eauto.



destr_eq ( o {| fn := fn; bk := bk; pt := IVoid n |} m (IVoid n, i)); destr_eq i; simpl in *; eauto; unfold  lift_err_d in *; try (repeat break_goal); try inv wf_program; try eapply stack_false_r in H7; try inv H7; try eapply stack_false_l in H7; try inv H7; try constructor; try right; try eapply CIH; intros; eauto.





eapply sound_succ_state; try eapply AN; unfold fetch; unfold transfer'; unfold get_successors; simpl; try rewrite Heqo0; try rewrite Heqo1; try rewrite Heqo2; auto; unfold find_function_entry; simpl in *; try rewrite Heqo5; try rewrite Heqo6; simpl. rewrite H4. right. left. rewrite H3. eauto.





econstructor; eauto. simpl in *. rewrite Heqo0. rewrite Heqo1. exists (TYPE_Void, ID_Global id0), args0, n. rewrite Heqo2. eauto.






eapply stack_false_l in H0. inversion H0.









eapply sound_succ_state; try eapply AN. unfold fetch; simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold get_successors; simpl in *. rewrite Heqo0; rewrite Heqo1; rewrite Heqo2; simpl; eauto. unfold transfer'. simpl in *. rewrite Heqo0; rewrite Heqo1; rewrite Heqo2. eauto.
eauto. eauto.




















auto.




rewrite jump_unaffected_v1.

unfold jump. destruct t; unfold  lift_err_d in *; try (repeat break_goal); subst; try inv Heqt; constructor; right; eapply CIH; intros; eauto; inv sstate. simpl in EM; simpl in AN; simpl in sstack.

inv sstack. simpl in *. destruct q. simpl in *. destruct H1. destruct H. destruct H. destr_eq (find_function m fn0). destr_eq ( find_block (blks (df_instrs d0)) bk0). destr_eq (block_to_cmd b0 (IId id)). destr_eq p. simpl in *. destr_eq c. inv H. destr_eq o1. inv  H0. eapply sound_succ_state. eapply AN0. unfold fetch; simpl. rewrite Heqo3. rewrite Heqo4. rewrite Heqo5. eauto. unfold get_successors; simpl in *; rewrite Heqo3; rewrite Heqo4; rewrite Heqo5. simpl in *. destruct x. simpl in *. destruct i. simpl in *. unfold find_function_entry; simpl. destr_eq (find_function m id0).
destr_eq ( find_block (blks (df_instrs d1)) (init (df_instrs d1))). simpl in *. eauto. unfold transfer'; simpl in *. rewrite Heqo3. rewrite Heqo4. rewrite Heqo5. eauto. simpl in *. eauto. eauto.
inversion H0. inversion H. inversion H. inversion H. inversion H.



simpl in *. inv sstack. simpl in *. destr H1. destr H. destr H. destr H. destr H0. destr H1. destr p. simpl in *. destr_eq (find_function m fn0). destr_eq ( find_block (blks (df_instrs d0)) bk0). destr_eq (block_to_cmd b0 (IVoid x1)). destr p. destr o1. inv H1. inv H2. eapply sound_succ_state.
eapply H. unfold fetch; simpl. rewrite Heqo3. rewrite Heqo4. rewrite Heqo5. eauto. unfold get_successors; simpl in *. rewrite Heqo3. rewrite Heqo4. rewrite Heqo5. unfold find_function_entry. destr x. destr i. destr_eq (find_function m id). destr_eq ( find_block (blks (df_instrs d1)) (init (df_instrs d1))). unfold transfer'; simpl. rewrite Heqo3. rewrite Heqo4. rewrite Heqo5. simpl in *. eauto. eauto. eauto. inversion H1. inversion H2. inversion H1. inversion H1. inversion H1.





simpl in *. eapply sound_succ_state. eapply AN.  unfold get_successors. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold get_successors. simpl in *. unfold next_term. unfold block_entry_pc. simpl in *.  rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. rewrite Heqo3. simpl. eauto. unfold transfer'. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. eauto. eauto.




simpl in *. eapply sound_succ_state. eapply AN.  unfold get_successors. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold get_successors. simpl in *. unfold next_term. unfold block_entry_pc. simpl in *.  rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. rewrite Heqo3.
destr_eq ( find_block_entry m fn br1). destr b0.
unfold transfer'. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. eauto. eauto.






simpl in *.  eapply sound_succ_state. eapply AN.  unfold get_successors. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. unfold get_successors. simpl in *. unfold next_term. unfold block_entry_pc. simpl in *.  rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. rewrite Heqo3. simpl in *; eauto.
unfold transfer'. simpl in *. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. eauto. eauto. eauto.

Qed.