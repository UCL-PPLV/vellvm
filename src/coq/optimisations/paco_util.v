Require Import paco.
Require Import Vellvm.Effects.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.


Set Implicit Arguments.
Set Contextual Implicit.

Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.

Ltac finish X :=
repeat match goal with
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Err _)) (Vis (trace_map (fun _ : state => ()) <$> Err _)) ] => constructor; constructor
  | [ |- related_event_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Err _)) (Vis (trace_map (fun _ : state => ()) <$> Err _)) ] => constructor
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Fin _)) (Vis (trace_map (fun _ : state => ()) <$> Fin _)) ] => constructor; constructor; auto
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Tau () (memD _ (trace_map (fun _ : state => ()) (step_sem _ _)))) (Tau () (memD _ (trace_map (fun _ : state => ()) (step_sem _ _))))] => constructor; right; apply X

end.

Ltac destr_simpl P X:= destruct P; simpl; finish X.
