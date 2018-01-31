Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.optimisations.static_analysis.
Require Import Vellvm.optimisations.static_analysis_proof.
Require Import Vellvm.optimisations.congruence_definition.
Require Import Vellvm.optimisations.congruence_proof.


Definition constant_prop (p:pc) (m:mcfg) (i:instr_id * instr) :=

  match (prep_selected_block m p) with
  | None => snd i
  | Some a => match fst i, snd i with
              | IId id, INSTR_Op (SV (VALUE_Ident (ID_Local ident))) => let abc := (value_analysis a (IId id)) in
                                                                        match (get_from_aenv abc ident) with
                                                                        | Some (Some (DV (VALUE_Integer a))) => INSTR_Op (SV (VALUE_Integer a))
                                                                        | _ => snd i
                                                                        end
                                                                          
              | _, _ => snd i
              end
                
                          
    
  end.


Print opt.
SearchAbout substring.
Lemma const_prop  : forall m st mem (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt constant_prop m) st)).
Proof. intros.  apply congruence_correct; eauto. unfold correct_instr. simpl in *. intros. unfold individual_step. simpl in *. unfold constant_prop. simpl in *.
       remember (prep_selected_block m {| fn := fn; bk := bk; pt := id |}). destruct o; simpl in *; eauto. destruct id; simpl in *; eauto.
       destruct instr; simpl in *; eauto.  destruct op; simpl in *; eauto.  destruct e0; simpl in *; eauto.
       destruct id0; simpl in *; eauto. remember ( get_from_aenv (value_analysis l (IId id)) id0). destruct o; simpl in *; eauto. destruct o; simpl in *; eauto. destruct v; simpl in *; eauto. destruct e0; simpl in *; eauto. inversion sstate0; subst. unfold sound_env in senv; simpl in *. specialize (senv l). symmetry in Heqo. apply senv in Heqo. eapply substring_get_in_l1_get_in_l2 in Heqo; eauto.
unfold eval_expr. simpl in *. rewrite Heqo. simpl in *. eauto. Qed.

