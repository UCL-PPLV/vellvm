Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.DecidableEquality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.

Set Implicit Arguments.

Print mcfg.
Print Trace.
Inductive finish_item X :=
  | tauitem : X -> finish_item X
  | visitem : Event (Trace X) -> finish_item X.

Print Trace.

Print Event.


Fixpoint step_trace_exec (n:nat) (t:Trace ()) (m:memory) : option (finish_item ()) :=
match n with
  | 0 => match t with
       | Vis (Eff e) =>
                        match mem_step e m with
                         | inr (m', v, k) => Some (tauitem tt)
                         | inl _ => None
                        end
       | Vis a => Some (visitem (a))
       | Tau a _ => Some (tauitem a)
       end
  | b.+1 => match t with
       | Vis (Eff e) =>
                        match mem_step e m with
                         | inr (m', v, k) => step_trace_exec b (k v) m'
                         | inl _ => None
                        end
       | Vis a => Some (visitem (a))
       | Tau a d => step_trace_exec b d m
       end
end.


(*COMPARE STEP_TRACE*)


