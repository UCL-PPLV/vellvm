Require Export Vellvm.ReasoningFramework.OptimisationEffects.
Require Export Vellvm.ReasoningFramework.OptimisationStepSemantics.
Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.
Require Import paco.
From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.



Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.



Module SS := StepSemantics.StepSemantics(A).
Export SS.





Definition optimization := definition (list block) -> definition (list block).

Definition optimize (m:modul (list block)) (o:optimization) : modul (list block) :=
 {|
  m_name := (m_name m);
  m_target := (m_target m);
  m_datalayout := (m_datalayout m);
  m_globals := (m_globals m);
  m_declarations := (m_declarations m);
  m_definitions := map o (m_definitions m);
  |}.

Definition correct (P : modul (list block) -> Prop) (o:optimization) :=
  forall (m:modul (list block)) m_semantic m_opt_semantic,
    mcfg_of_modul m = Some m_semantic ->
    mcfg_of_modul (optimize m o) = Some m_opt_semantic ->forall s a b, (sem m_semantic s) = a -> (sem m_opt_semantic s) = b ->
 trace_equiv a b. 



Theorem remove_some : forall (a b : mcfg), a = b <-> Some a = Some b.
Proof. intros. split; intros; inversion H; auto. Qed.


Theorem trace_equiv_lemma: forall (a:Trace ()), trace_equiv a a.
Proof.   pcofix CIH. intro d.
  pfold. destruct d; eauto.
  - destruct v; eauto. destruct e; econstructor; eauto; constructor; apply related_effect_refl;
    apply upaco2_refl; auto.
Qed.

Hint Resolve trace_equiv_lemma.

Print sem.
Print Reason_sem.

Theorem trace_equiv_step_sem: forall a s, trace_equiv (sem a s) (sem a s).
Proof. intros. remember (sem a s) as b. auto. Qed.

Hint Resolve trace_equiv_step_sem.

Theorem trace_equiv_step_sem_equiv : forall s a b, a = b -> trace_equiv (sem a s) (sem b s).
Proof. intros. rewrite H; auto. Qed. 

