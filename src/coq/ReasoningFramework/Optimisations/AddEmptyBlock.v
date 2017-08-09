From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.
Require Import paco.

Require Export Vellvm.ReasoningFramework.OptimisationHints.

Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.





Print definition.

Definition emptyblock := [mk_block (Anon 1) nil nil (IVoid 0, TERM_Ret_void)].

Print emptyblock.

Print concat.
Definition add_empty_blocks (d:definition (list block)) := 
  {|
    df_prototype   := (df_prototype d);
    df_args        := (df_args d);
    df_instrs      := cat (df_instrs d) emptyblock;
  |}.



Print definition.


Print related_effect_refl.

Theorem correct_empty_blocks : forall p, correct p add_empty_blocks.
Proof. intros. unfold correct. intros. induction m. unfold add_empty_blocks in H1. 
induction m_definitions. simpl in *. 
unfold optimize in H0.  simpl in *.  rewrite H in H0. 
apply remove_some in H0.  rewrite H0 in H1.  rewrite <- H2. rewrite <- H1. auto.
rewrite <- H1; rewrite  <- H2. unfold sem.
unfold step_sem.