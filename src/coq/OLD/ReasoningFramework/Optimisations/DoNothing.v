
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.Effects Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast Vellvm.ReasoningFramework.OptimisationStepSemantics.

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


Require Export Vellvm.ReasoningFramework.OptimisationHints.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.


Definition donothing (d:definition (list block)) := d.


Theorem optimise_equiv : forall m, optimize m donothing = m.
Proof. intros. unfold optimize, donothing. simpl. induction m; simpl; eauto.
induction m_definitions; simpl; eauto. induction a; simpl; eauto. inversion IHm_definitions. rewrite H0. rewrite H0. simpl. eauto. Qed.

Theorem donothing_correct : forall p, correct p donothing.
Proof. intros. unfold correct. intros. rewrite optimise_equiv in H0. rewrite  H in H0. apply remove_some in H0. rewrite <- H0 in H2. rewrite <- H2. rewrite <- H1.
auto. Qed.