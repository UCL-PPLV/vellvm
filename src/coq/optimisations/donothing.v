
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

Ltac test X :=
repeat match goal with
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Err _)) (Vis (trace_map (fun _ : state => ()) <$> Err _)) ] => constructor; constructor
  | [ |- related_event_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Err _)) (Vis (trace_map (fun _ : state => ()) <$> Err _)) ] => constructor
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Fin _)) (Vis (trace_map (fun _ : state => ()) <$> Fin _)) ] => constructor; constructor; auto
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Tau () (memD _ (trace_map (fun _ : state => ()) (step_sem _ _)))) (Tau () (memD _ (trace_map (fun _ : state => ()) (step_sem _ _))))] => constructor; right; apply X

end.

Ltac destr_simpl P X:= destruct P; simpl; test X.





Lemma do_nothing_correct : forall mem st prog, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog st)).
Proof. pcofix CIH.
intros. pfold.
assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))).
destruct (memD mem (sem prog st)); eauto. rewrite H. simpl. clear H.
unfold stepD.
destruct st.
destruct p.
destruct p.
simpl.
unfold CFG.fetch.




destr_simpl (CFG.find_function prog fn) CIH.
destr_simpl d CIH. 
destr_simpl df_instrs CIH.
destr_simpl (CFG.find_block blks bk) CIH.
destr_simpl (CFG.block_to_cmd b pt) CIH.
destr_simpl p CIH.
destr_simpl c CIH.
destr_simpl o CIH.
destr_simpl pt CIH.
destr_simpl i CIH.
destr_simpl (eval_op e None op) CIH.
destr_simpl fn0 CIH.
destr_simpl i CIH.
destr_simpl (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args) CIH.
destr_simpl ((CFG.find_function_entry prog id0)) CIH.
destr_simpl f CIH.
destr_simpl (CFG.find_function_entry prog id0) CIH.
destr_simpl f CIH.
destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t0) v) CIH.
destr_simpl v0 CIH.
destr_simpl i CIH.
destr_simpl fn0 CIH.
destr_simpl i CIH.
destr_simpl (CFG.find_function_entry prog id) CIH.
destr_simpl f CIH.
destr_simpl (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args) CIH.
destr_simpl t CIH.
destr_simpl val CIH.
destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v) CIH.
destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v2 CIH.
destr_simpl t CIH.
destr_simpl v CIH.
destr_simpl (eval_op e (Some t) v) CIH.
destr_simpl s CIH.
destr_simpl f CIH.
destr_simpl s CIH.
destr_simpl f CIH.
destr_simpl v CIH.
destr_simpl (eval_op e (Some t) v) CIH.
destr_simpl v0 CIH.
destr_simpl (StepSemantics.Int1.eq x StepSemantics.Int1.one) CIH.
destr_simpl (jump prog fn bk br1 e s) CIH.
destr_simpl (jump prog fn bk br2 e s) CIH.
destr_simpl (jump prog fn bk br e s) CIH.
Qed.



