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