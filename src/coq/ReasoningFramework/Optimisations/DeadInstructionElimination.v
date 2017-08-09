From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.
Require Import paco.


Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.



Require Export Vellvm.ReasoningFramework.OptimisationEffects.
Require Export Vellvm.ReasoningFramework.OptimisationHints.
Require Export Vellvm.ReasoningFramework.OptimisationStepSemantics.
Print definition.

(*

Class RemoveInstr X := remove_instr : instr_id -> X -> X.


Print block.


Definition remove_instr_block (id:instr_id) (b:block) : block :=
  {| blk_id := blk_id b;
     blk_phis := blk_phis b;
     blk_code := blk_code b;
     blk_term := blk_term b;
  |}.


Instance rem_instr_block : RemoveInstr block := remove_instr_block.


Definition remove_instr_defn (id:instr_id) (d:definition (list block)) : definition (list block) :=
  {|
    df_prototype   := (df_prototype d);
    df_args        := (df_args d);
    df_instrs      := List.map (remove_instr id) (df_instrs d);
  |}.


Instance rem_instr_defn : RemoveInstr (definition (list block)) := remove_instr_defn.


Definition dead (g:cfg) (inst:instr_id) : Prop :=
  match inst with
  | IVoid _ => False
  | IId id => False
  end.


Inductive remove_instr_applies (inst:instr_id) (d:definition (list block)) : Prop :=
| remove_instr_applies_intro:
    forall glbls g, cfg_of_definition glbls d = Some g ->
               dead g inst ->
               remove_instr_applies inst d.



Definition remove_instr_applies_module (instr:instr_id) (m:modul (list block)) : Prop :=
  Forall (remove_instr_applies instr) (m_definitions m).


Lemma remove_instr_correct:
  forall (instr:instr_id), correct (remove_instr_applies_module instr) (remove_instr_defn instr).
Proof.
  intros instr.
  unfold correct.
  intros m m_semantic m_opt_semantic Happlies H0 H1 s Herr. revert s Herr.
  pcofix CIH.
intros. Admitted.




*)









