
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.

Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.


Print find_function.



(*Let's prove the find_function does not get impacted by both*)


Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.

(*Let's recap:
This optimisation adds a useless instruction to a block if the terminator is a return void


Informally reasoning, there are two possible cases:
  -The terminator instruction is a return void. This means that the state doesn't matter because it doesn't impact the terminator instruction.
  -The terminator is not a return void. The instruction does not get added meaning the execution doesn't get affected.



Essentially, we want to solve this by induction on the terminator instruction of a block.


*)



Print prog_optimise.
Print optimise.
Lemma do_nothing_correct : forall mem st prog, trace_equiv (memD mem (sem prog st)) (memD mem (sem (prog_optimise prog) st)).
Proof. pcofix CIH.
intros.
pfold.

(*unroll right*)
assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st)) ).
destruct (memD mem (sem prog st)) ; eauto.
rewrite H. clear H.

(*unroll left*)
assert ((memD mem (sem (prog_optimise prog) st)) = unroll (memD mem (sem (prog_optimise prog) st))
). destruct (memD mem (sem (prog_optimise prog) st)); eauto. rewrite H. clear H.

(*unroll*)
simpl.


(*unfold stepD*)
unfold stepD.
unfold CFG.fetch. destruct st. destruct p. destruct p.
unfold CFG.find_function.





destruct prog. simpl.
destruct m_definitions. simpl.
(*no instruction*)
  -constructor. constructor.
  -destruct d. simpl.
unfold find_defn. 
unfold cfg_opt. simpl.
destruct df_instrs. simpl in *.
unfold alter_blocks. simpl.
unfold optimise.
unfold map.
unfold AstLib.ident_of.
unfold AstLib.ident_of_definition.
simpl.
destruct (AstLib.ident_of df_prototype == ID_Global fn); simpl.
    +simpl. destruct blks.
{
simpl. constructor. constructor.
}
{
simpl.
unfold terminator_check. simpl. destruct b.
simpl. 



(*NOT SURE*)



destruct blk_term. simpl.
induction t.
    -simpl. admit.
    -simpl. admit.
    -simpl. admit.
    -simpl. admit.
    -simpl. admit.
    -simpl. admit.
    -simpl. admit.
    -simpl. admit.
}
  +unfold not in n.
unfold AstLib.ident_of.
unfold AstLib.ident_of_declaration.
unfold dc_name.
(*UNFOLD IN TWO*)
