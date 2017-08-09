Require Export Vellvm.ReasoningFramework.OptimisationEffects.
Require Export Vellvm.ReasoningFramework.OptimisationHints.


Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast Vellvm.ReasoningFramework.OptimisationStepSemantics.
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
(*

Inductive Leaf :=
  | MyLeaf (b:block).

Inductive LoopTree :=
  | MyNode (leafs:list Leaf)
.



Definition LeafToSingleBlock (l:Leaf) :=
match l with
  | MyLeaf b => b
end.

Definition SingleBlockToLeaf (b:block) : Leaf := MyLeaf b.

Theorem LeafToLoopTree : forall b, b = LeafToSingleBlock(SingleBlockToLeaf b).
Proof. auto. Qed.

Definition BlockToListOfLeaves (b:list block) := MyNode (map SingleBlockToLeaf b).

Definition ListOfLeavesToBlock (l:LoopTree) : list block :=
match l with
  | MyNode a => map LeafToSingleBlock a
end.


Theorem BlockConversion : forall l, ListOfLeavesToBlock(BlockToListOfLeaves(l)) = l.
Proof. unfold ListOfLeavesToBlock, BlockToListOfLeaves. induction l.
  -simpl. auto.
  -simpl. rewrite IHl. auto. Qed.


Definition convertdeconvert b := ListOfLeavesToBlock (BlockToListOfLeaves b).



Theorem convertdeconvert_correct : forall b, convertdeconvert b = b.
Proof. unfold convertdeconvert. intros. apply BlockConversion. Qed.


Definition testy1234 (d:definition (list block)) := 
  {|
    df_prototype   := (df_prototype d);
    df_args        := (df_args d);
    df_instrs      := convertdeconvert (df_instrs d);
  |}.

Print testy1234.
Theorem correct_testy : forall d, testy1234 d = d.
Proof. intros. induction d. unfold testy1234. rewrite convertdeconvert_correct. simpl. eauto. Qed.



Theorem test123123 : forall m_definitions, [seq testy1234 i | i <- m_definitions] = m_definitions.
Proof. intros. induction m_definitions; simpl; eauto. rewrite IHm_definitions. rewrite correct_testy. auto. Qed.


Theorem optimize_convertdeconvert_equal : forall m_semantic, (optimise m_semantic testy1234) = m_semantic.
Proof. intros. unfold optimise. rewrite test123123. induction m_semantic; simpl; eauto. Qed.



Theorem correct_testy1234 : forall p, correct p testy1234.
Proof.  unfold correct. 
intros m m_semantic m_opt_semantic Happlies H0 H1 s Herr. rewrite optimize_convertdeconvert_equal in Herr. rewrite s in Herr. apply remove_some in Herr. rewrite Herr. auto. Qed.


*)