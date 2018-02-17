Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
Require Import Vellvm.optimisations.SSA_semantics.
Require Import Vellvm.optimisations.maps.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.optimisations.Kildall.valueanalysis.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.



Definition get_value (a:aenv) (i:ident) :=
  match i with
  | ID_Global _ => SV (VALUE_Ident i)
  | ID_Local id => match AE.get id a with
                   | avalue (DV (VALUE_Integer i)) => SV ((VALUE_Integer i))
                   | _ => SV (VALUE_Ident i)
                   end
                     
  end.


Definition substitute_value (a:aenv) (o:Ollvm_ast.value) :=
  match o with
  | SV (VALUE_Ident (ID_Local ident)) => match AE.get ident a with
                                         |  (avalue (DV (VALUE_Integer i))) => SV ((VALUE_Integer i))                                                       
                                         |  (avalue (DV (VALUE_Float i))) => SV ((VALUE_Float i))
                                         |  (avalue (DV (VALUE_Bool i))) => SV ((VALUE_Bool i))
                                         |  (avalue (DV (VALUE_Null))) => SV ((VALUE_Null))
                                         |  (avalue (DV (VALUE_Zero_initializer))) => SV ((VALUE_Zero_initializer))
                                         |  (avalue (DV (VALUE_Cstring i))) => SV ((VALUE_Cstring i))
                                         |  (avalue (DV (VALUE_None))) => SV ((VALUE_None))
                                         |  (avalue (DV (VALUE_Undef))) => SV ((VALUE_Undef))

                                         | _ => SV (VALUE_Ident (ID_Local ident))

                                         end
  | _ => o
  end.


Definition optimise_val (ae:aenv) (o:Ollvm_ast.value)  (r:raw_id) :=
  match o with
  | SV (VALUE_Ident (ID_Local ident)) =>  substitute_value ae o
  | SV (OP_IBinop ibinop (TYPE_I 32)  a a1) => SV (OP_IBinop ibinop (TYPE_I 32)  (substitute_value ae a)  (substitute_value ae a1))
  | rest => rest 
  end.



Ltac clean := simpl in *; unfold eval_expr; simpl in *; eauto.




Lemma ematch_get : forall e a id val, ematch e a -> AE.get id a = avalue val -> lookup_env e id = Some val.
Proof. intros. unfold ematch in *. simpl in *. specialize (H id). rewrite H0 in H. simpl in *. inversion H; subst. unfold lookup_env_aenv in *. simpl in *. destr_eq (lookup_env e id). inversion H1. subst. eauto. inversion H1. Qed.












Lemma val_correct : forall id a e ins,  ematch e a ->
                                        eval_op e None ins = eval_op e None (optimise_val a ins id).
Proof. intros.
       destruct ins.



       destruct e0; simpl in *; try destruct id0; simpl in *; eauto. destruct ( AE.get id0 a) eqn:?; simpl in *; eauto. destruct n;try  destruct e0; dupl Heqt; eapply ematch_get in Heqt; clean; try rewrite Heqt; clean.
       destruct t; clean. destruct sz; clean. destruct p; clean. destruct p; clean. destruct p; clean. destruct p; clean. destruct p; clean .  destruct p; clean. clean. destruct v1.
       
       destruct e0; clean; try destruct id0; clean; try destruct (AE.get id0 a) eqn:?; try dupl Heqt; simpl in *; clean; try destruct v2; clean; try destruct e0; clean; try destruct id1; clean; try destruct ( AE.get id1 a) eqn:?; try dupl Heqt1;  clean  ; try eapply ematch_get in Heqt0; eauto; try rewrite Heqt0; try destruct n; clean; try destruct e0; clean; try eapply ematch_get in Heqt1; eauto; try rewrite Heqt1; clean; try rewrite Heqt0; clean; try destruct n0; clean; try rewrite Heqt1; clean; try destruct e0; clean; try rewrite Heqt1; clean; try destruct id0; clean; destruct ( AE.get id0 a) eqn:?; clean; try dupl Heqt; destruct n; try eapply ematch_get in Heqt; eauto; try rewrite Heqt; try destruct e0; clean; try rewrite Heqt; clean; try dupl Heqt0; try eapply ematch_get in Heqt0; eauto; rewrite Heqt0; clean. 
Qed.







Definition optimise_instr (ae: list (function_id * PCMap.t DS.L.t)) (p:pc) (m:mcfg) (i:instr_id * instr) : instr :=
  match fetch_analysis p ae with
  | Some (VA.State ae) => match fst i, snd i with
                   | (IId id), INSTR_Op ins => INSTR_Op (optimise_val ae ins id)
                   | _, _ => snd i
                              
                          end
  | _ => snd i
             
                     
  end.

(*


  Lemma const_prop  : forall m st mem (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt (optimise_instr (analyse_program m)) m) st)).
  Proof. intros.(* SearchAbout trace_equiv.

         apply congruence_correct; eauto.
       
       unfold correct_instr1; intros; eauto.
       unfold optimise_instr; simpl in *. inv sstate0; simpl in *.
       rewrite AN.  destruct id; clean. destruct instr; clean.
       unfold exec_code1; simpl in *. unfold individual_step. simpl in *. eapply val_correct in EM. rewrite EM. eauto. Qed.
*) Admitted.*)