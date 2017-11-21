
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.optimisations.transform.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.

(*Do Nothing Problem*)


Print memD.

Print trace_equiv.

Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.




Definition unroll_event (t:Event (Trace())) :=
match t with
  | Fin n => Fin n
  | Err n => Err n
  | Eff n => Eff n
end.
Print trace_map.
Print Event.


Definition test prog v args k := (trace_map (fun _ : state => ()) <$>
   effects_map (step_sem prog) (Call v args k)).
Print test.
Definition unroll_effects (t:effects (Trace ())) :=
match t with
  | Alloca typ k => Alloca typ k
  | Load ad k => Load ad k
  | Store ad v k => Store ad v k
  | Call v lv k => Call v lv k
end.


Definition test1 prog v args k := unroll_effects ((trace_map (fun _ : state => ()) <$>
   effects_map (step_sem prog) (Call v args k))).




Lemma do_nothing_correct : forall mem st prog, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog st)).
Proof. Admitted.


(*
(*Initialise*)
pcofix CIH.
(*Normal proof.*)
intros. pfold.

(*Unroll left & right function once*)
assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))).
destruct (memD mem (sem prog st)); eauto. rewrite H. simpl. clear H.

unfold stepD. destruct st. destruct p. simpl.
destruct prog. simpl. induction m_definitions.
  +unfold CFG.fetch. simpl. destruct p. simpl. constructor. constructor.
  +unfold CFG.fetch in *. simpl in *. destruct p. unfold CFG.find_function in *; simpl in *.
unfold CFG.find_defn in *; simpl in *. destruct a. simpl in *.
destruct df_instrs. induction blks.
destruct (AstLib.ident_of
                     {|
                     df_prototype := df_prototype;
                     df_args := df_args;
                     df_instrs := {| CFG.init := init; CFG.blks := []; CFG.glbl := glbl |} |} ==
                   ID_Global fn).
simpl. constructor. constructor.

*)