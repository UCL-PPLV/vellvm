
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


Inductive pc_match : mcfg -> pc -> (mcfg -> mcfg) -> pc -> Prop :=
  | match_pc_intro : forall m p i f, fetch m p = Some i  -> fetch (f m) p = Some i -> pc_match m p f p.

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



(*

Lemma add_instrproof : (forall st st1 prog, state_match prog prog_optimise st st1) -> forall st prog mem, trace_equiv (memD mem (sem (prog_optimise prog) st)) (memD mem (sem (prog) st)).
Proof. intro. pcofix CIH.
intros. pfold. generalize (H st st prog). intros. inversion H0. subst. inversion H1.
subst. clear H7.



(*unroll right*)
assert ((memD mem (sem prog (p, e, s))) = unroll (memD mem (sem prog (p, e, s))) ).
destruct (memD mem (sem prog (p, e, s))) ; eauto.
rewrite H4. clear H4.

(*unroll left*)
assert ((memD mem (sem (prog_optimise prog) (p, e, s))) = unroll (memD mem (sem (prog_optimise prog) (p, e, s)))
). destruct (memD mem (sem (prog_optimise prog) (p, e, s))); eauto. rewrite H4. clear H4.

(*unroll*)
simpl. 

rewrite H2. rewrite H3.
simpl.
destruct i.
  +
unfold incr_pc. simpl. destruct p.

(*induction on *)


unfold incr_pc. simpl. destruct p. simpl. unfold prog_optimise.
unfold optimise. unfold def_cfg_opt. simpl in *.

 admit.
  +simpl. destruct t.
    *destruct v. simpl. destruct (eval_op e (Some t) v); simpl.
      -constructor. constructor.
      -destruct s. simpl. constructor. constructor. auto. simpl. destruct f. constructor. right. apply CIH. simpl. constructor. constructor.
    *destruct s. simpl. constructor. constructor. auto. destruct f. simpl. constructor. constructor. constructor. right. apply CIH.
    *destruct v. simpl. destruct (eval_op e (Some t) v). simpl. constructor. constructor. simpl. destruct v0. simpl. constructor. constructor. simpl. constructor. constructor. simpl. constructor. constructor. simpl.
simpl. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one). admit. admit. simpl. constructor. constructor. simpl. constructor. constructor. simpl. constructor. constructor.
    *admit.
    *simpl. constructor. constructor.
    *simpl. constructor. constructor.
    *simpl. constructor. constructor.
    *simpl. constructor. constructor.
Admitted.
(*

rewrite H2. simpl.
unfold fetch in H3. simpl in *. destruct p. simpl in *.
unfold find_function in H3. simpl in *.
unfold cfg_opt in H3. simpl. unfold find_map in H3. simpl in *.












destruct (fetch prog p); simpl in *; try_finish CIH.


unfold fetch in H3. simpl in *. destruct p. simpl in *.
unfold prog_optimise in H3. simpl in H3.
unfold find_block in H3. simpl in H3.













+destruct c; simpl.
  -simpl. induction prog. simpl in *.
simpl in *.

unfold incr_pc.
simpl in *. destruct p. simpl in *.



unfold prog_optimise. simpl.
unfold def_cfg_opt. simpl in *.
unfold find_function. simpl in *.

unfold prog_optimise in H3. simpl in H3.
unfold def_cfg_opt in H3.
simpl in *.
unfold map, cfg_opt, optimise in H3; simpl in H3.
unfold find_function in H3. simpl in *.
unfold find_defn in H3. simpl in *.
  -{destruct t; try_finish CIH.
    *destruct v. destruct (eval_op e (Some t) v); try_finish CIH. destruct s; try_finish CIH. destruct f. constructor. right. apply CIH. try_finish CIH. 
    *destruct s; try_finish CIH.
      +destruct f.
        -simpl. constructor. constructor.
        -constructor. right. apply CIH.
    *destruct v. destruct (eval_op e (Some t) v); simpl; try_finish CIH. destruct v0; simpl; try_finish CIH.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one). simpl.
{
unfold jump. unfold find_block_entry. simpl.
destruct prog. simpl. unfold prog_optimise.
unfold def_cfg_opt. simpl.
destruct p. simpl.
unfold cfg_opt. unfold alter_blocks.
unfold find_function. simpl. unfold find_defn. simpl.
unfold AstLib.ident_of. simpl.
unfold AstLib.ident_of_definition. simpl. admit.

}
}
*)



*)


