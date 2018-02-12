Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast Vellvm.ReasoningFramework.Test2.
Import ListNotations.

From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Require Export Permutation.
Require Import Vellvm.Effects.



Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.

Print code.

Definition instr_optimisation := (instr) -> (instr).

Definition no_optimisation (i:instr) := i.

Definition instr_optimisation_ins (i:instr_optimisation) (ins:instr) := i ins.

Definition instr_optimisation_id (i:instr_optimisation) (ins:instr_id*instr) :=
match ins with
  | (a, b) => (a, instr_optimisation_ins i b)
end.

Definition intrs_optimisation_list (i:instr_optimisation) (c:code) := map (instr_optimisation_id i) c.


Definition instr_optimisation_block (i:instr_optimisation) (b:block) := mk_block b.(blk_id) b.(blk_phis) (intrs_optimisation_list i b.(blk_code)) b.(blk_term).

Definition instr_optimisation_list_block (i:instr_optimisation) (sb: seq block) := map (instr_optimisation_block i) sb.

Print cfg.

Definition instr_optimisation_cfg (i:instr_optimisation) (c:cfg) := mkCFG c.(init) (instr_optimisation_list_block i c.(blks)) c.(glbl).

Definition instr_optimisation_definition_cfg (i:instr_optimisation) (dc: definition cfg) := mk_definition cfg dc.(df_prototype) dc.(df_args) (instr_optimisation_cfg i dc.(df_instrs)).

Definition instr_optimisation_definition_cfg_list (i:instr_optimisation) (dc: seq (definition cfg)) := map (instr_optimisation_definition_cfg i) dc.

Definition instr_optimisation_modul_cfg (i:instr_optimisation) (m: modul cfg) :=
mk_modul cfg m.(m_name) m.(m_target) m.(m_datalayout) m.(m_globals) m.(m_declarations) (instr_optimisation_definition_cfg_list i m.(m_definitions)).



Print state.



Theorem testy : forall f insn CFG pc k e, part_CFG_Step (instr_optimisation_ins f insn) CFG pc k e = part_CFG_Step insn CFG pc k e -> Reason_stepD (instr_optimisation_modul_cfg f CFG) (pc, e, k) = Reason_stepD CFG (pc, e, k).
Proof. intros.  unfold Reason_stepD. replace (part_CFG_Step insn (instr_optimisation_modul_cfg f CFG) pc k e) with (part_CFG_Step insn CFG pc k e).




Admitted.

Theorem smalltest1 : forall insn f CFG pc k e, part_CFG_Step (instr_optimisation_ins f insn) CFG pc k e = part_CFG_Step insn CFG pc k e  -> part_CFG_Step insn (instr_optimisation_modul_cfg f CFG) pc k e =  part_CFG_Step insn CFG pc k e.
Proof. intros. induction CFG. unfold instr_optimisation_modul_cfg. simpl. unfold instr_optimisation_definition_cfg_list. simpl. eauto.
induction m_definitions. simpl. eauto.
Admitted.


Print instr.


Print part_CFG_Step.






