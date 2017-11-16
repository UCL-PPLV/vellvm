
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.
Require Import Vellvm.StepSemantics.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.






Print modul.








Definition list_block_opt (o:list block -> list block) (m:CFG.cfg) := 
CFG.mkCFG m.(CFG.init) (o m.(CFG.blks)) m.(CFG.glbl).


Definition block_opt (o:code -> code) (m: block) : block :=
mk_block m.(blk_id) m.(blk_phis) m.(blk_code) m.(blk_term).


Definition alter_blocks (o:code -> code) (m:CFG.cfg) : CFG.cfg :=
CFG.mkCFG m.(CFG.init) (map (block_opt o) m.(CFG.blks)) m.(CFG.glbl).

Definition cfg_opt (o:code -> code) (m:definition CFG.cfg) :=
mk_definition CFG.cfg m.(df_prototype) m.(df_args) (alter_blocks o m.(df_instrs)).


Definition def_cfg_opt (o:code -> code) (m:modul CFG.cfg) := 
mk_modul CFG.cfg m.(m_name) m.(m_target) m.(m_datalayout) m.(m_globals) m.(m_declarations) (map (cfg_opt o) m.(m_definitions)).







(*Disabling certain instructions*)


Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.



Definition disable_instr (i:instr) : bool :=
match i with
  | INSTR_Op _ => true
  | INSTR_Call _ _ => false
  | INSTR_Alloca _ _ _ => false
  | INSTR_Load _ _ _ _ => false
  | INSTR_Store _ _ _ _ => false
  | INSTR_Fence => false
  | INSTR_AtomicCmpXchg => false
  | INSTR_AtomicRMW => false
  | INSTR_Unreachable => false
  | INSTR_VAArg => false
  | INSTR_LandingPad => false
end.


Inductive disable_state (m:CFG.mcfg) : state -> Prop :=
  | disable_state_intro : forall s p e i, disable_instr i = true -> CFG.fetch m p = Some (CFG.Step i) -> disable_state m (p, e, s).

