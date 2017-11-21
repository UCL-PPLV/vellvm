
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.

Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.

(*
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

Print incr_pc.


Inductive pc_match : mcfg -> pc -> (mcfg -> mcfg) -> pc -> Prop :=
  | match_pc_intro : forall m p i j k l f, incr_pc m p = Some l -> incr_pc (f m) p = Some k -> fetch m p = Some i  -> fetch (f m) p = Some j -> pc_match m p f p.

Print state.
Inductive state_match : mcfg -> (mcfg -> mcfg) -> state -> state -> Prop :=
  | match_state_intro : forall m f p e s, pc_match m p f p -> state_match m f (p, e, s) (p, e, s).


Ltac try_finish X := simpl; try (simpl; constructor; constructor; auto); try ( constructor; right; apply X).

Print fetch.



Definition separate_fetch (o:mcfg -> mcfg) (m:mcfg) (p:pc) :=
match fetch m p with
  | Some a => Some a
  | None => None
end.

Print prog_optimise.
Print optimise.

Print prog_optimise.
Print def_cfg_opt.

Definition nothing o : block := o.


Definition prog_nothing := def_cfg_opt nothing.

Lemma add_instrproof : (forall st st1 prog, state_match prog prog_optimise st st1) -> forall st prog mem, trace_equiv (memD mem (sem ((def_cfg_opt nothing) prog) st)) (memD mem (sem (prog) st)).
Proof. intro. pcofix CIH. Admitted.
(*

intros. pfold. generalize (H st st prog). intros. 
inversion H0. simpl. subst. inversion H1. simpl. subst.

assert ((memD mem (sem (def_cfg_opt nothing prog) (p, e, s))) = unroll ((memD mem (sem (def_cfg_opt nothing prog) (p, e, s))))).
destruct ((memD mem (sem (def_cfg_opt nothing prog) (p, e, s)))); eauto.
rewrite H6.

assert ((memD mem (sem prog (p, e, s))) = unroll (memD mem (sem prog (p, e, s)))
). destruct (memD mem (sem prog (p, e, s))); eauto.

rewrite H6. rewrite H7. clear H6; clear H7. simpl.

destruct prog; simpl in *.
unfold def_cfg_opt. simpl.
induction m_definitions.
  +unfold fetch in *; simpl in *. destruct p. inversion H4.
  +unfold fetch in *. simpl in *. destruct p. simpl in *.
unfold find_function in *. simpl in *.
unfold find_defn in *.
unfold cfg_opt in *; simpl in *.
unfold AstLib.ident_of in *; simpl in *.
*)*)