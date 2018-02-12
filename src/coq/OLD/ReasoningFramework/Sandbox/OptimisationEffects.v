(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Program Classical.
Require Import paco.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type EffT.
  (* The effects interface is parameterized by the language's types and the 
   memory model's notion of addresses. *)
  Parameter typ : Set.
  Parameter addr : Set.
  Parameter value : Set.
  Parameter inj_addr: addr -> value.
  Parameter no_value : value.  (* Morally DV VALUE_None *)
End EffT.



Require Import  Vellvm.StepSemantics.




Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.



Module SS := StepSemantics.StepSemantics(A).
Export SS.


Module OptimisationEffects(ET:EffT).
Export ET.


(* TODO: Add other memory effects, such as synchronization operations *)
(* Notes: 
   - To allow the memory model to correctly model stack alloca deallocation,
     we would also have to expose the "Ret" instruction. 

   - What is the correct way to model global data? 
*)


Definition effects_map {A B} (f:A -> B) (m:effects A) : effects B :=
  match m with
  | Alloca t g => Alloca t (fun a => f (g a))
  | Load a g  => Load a (fun dv => f (g dv))
  | Store a dv d => Store a dv (fun dv => f (d dv))
  | Call v args d => Call v args (fun dv => f (d dv))
  end.

(* traceervational equivalence ------------------------------------------------ *)

Section RELATED_EFFECTS.
  Variable X : Type.
  Variable R : X -> X -> Prop.

  
  (*
  This relation doesn't allow any variation in the relations for the memory model.  
  A more parametric version would:
    - Replace the use of '=' in the definition of trace_equiv_effect_step with 
      a state relation on states: RA : A -> A -> Prop
    - have an address relation   RAddr : addr -> addr -> Prop  
    - have a value relation     RValue : value -> value -> Prop
  It builds in the "total" relation for error string traceervations:
     Err s1 ~~ Err s2   for any s1, s2     
     ( Could pass in E : string -> string -> Prop )

  In order for the theory to make sense, we probly would also want to have:
    RA a1 a2 <-> R (Ret a1) (Ret a2)
    RAddr a1 a2 <->  RValue (inj_addr a1) (inj_addr a2)
  *)
  
  Inductive related_effect_step  : effects X -> effects X -> Prop :=
  | related_effect_Alloca :
      forall t k1 k2
        (HRk : forall (a1 a2:addr), a1 = a2 -> R (k1 (inj_addr a1)) (k2 (inj_addr a2))),
        related_effect_step (Alloca t k1) (Alloca t k2)

  | related_effect_Load :
      forall a1 a2 k1 k2
        (HRa : a1 = a2)
        (HRk : (forall (v1 v2:value), v1 = v2 -> R (k1 v1) (k2 v2))),
        related_effect_step (Load a1 k1) (Load a2 k2)

  | related_effect_Store  :
      forall a1 a2 v1 v2 k1 k2
        (HRa : a1 = a2)
        (HRv : v1 = v2)
        (HRk : R (k1 no_value) (k2 no_value)),
        related_effect_step (Store a1 v1 k1) (Store a2 v2 k2)

  | related_effect_Call :
      forall v1 v2 vs1 vs2 k1 k2
        (HRv : v1 = v2)
        (HRvs : vs1 = vs2)
        (HRk : (forall (rv1 rv2:value), rv1 = rv2 -> R (k1 rv1) (k2 rv2))),
        related_effect_step (Call v1 vs1 k1) (Call v2 vs2 k2)
  .
  Hint Constructors related_effect_step.
  
  Lemma related_effect_refl : (reflexive _ R) -> reflexive _ related_effect_step.
  Proof.
    unfold reflexive.
    intros HR x.
    destruct x; eauto.
    - econstructor. intros a1 a2 H. subst. eauto.
    - econstructor; eauto. intros v1 v2 H. subst. eauto.
    - econstructor; intros; subst; eauto.
  Qed.      

  Lemma related_effect_symm : (symmetric _ R) -> symmetric _ related_effect_step.
  Proof.
    unfold symmetric.
    intros HR x y H.
    dependent destruction H; eauto.
  Qed.

  Lemma related_effect_trans : (transitive _ R) -> transitive _ related_effect_step.
  Proof.
    unfold transitive.
    intros HR x y z H1 H2.
    dependent destruction H1; dependent destruction H2; eauto.
  Qed.    
End RELATED_EFFECTS.    

Section RELATED_EVENTS.

  Variable X : Type.
  Variable R : X -> X -> Prop.
  
  Inductive related_event_step : Event X -> Event X -> Prop :=
  | related_event_fin :
      forall v1 v2
        (Hv: v1 = v2),
        related_event_step (Fin v1) (Fin v2)

  | related_event_err :
      forall s1 s2,
        related_event_step (Err s1) (Err s2)

  | related_event_eff :
      forall e1 e2
        (HRe : related_effect_step R e1 e2),
        related_event_step (Eff e1) (Eff e2)
  .
  Hint Constructors related_event_step.
  
  Lemma related_event_refl : (reflexive _ R) -> reflexive _ related_event_step.
  Proof.
    unfold reflexive.
    intros HR x.
    destruct x; eauto. 
    - constructor. apply related_effect_refl; auto.
  Qed.      

  Lemma related_event_symm : (symmetric _ R) -> symmetric _ related_event_step.
  Proof.
    unfold symmetric.
    intros HR x y H.
    dependent destruction H; subst; constructor; eauto.
    - apply related_effect_symm; auto.
  Qed.

  Lemma related_event_trans : (transitive _ R) -> transitive _ related_event_step.
  Proof.
    unfold transitive.
    intros HR x y z H1 H2.
    dependent destruction H1; dependent destruction H2; constructor; eauto.
    - eapply related_effect_trans; eauto.
  Qed.    
  
End RELATED_EVENTS.

Section OBSERVATIONAL_EQUIVALENCE. 
  Variable X : Type.
  Variable R : Trace X -> Trace X -> Prop.
  
  Inductive trace_equiv_step : Trace X -> Trace X -> Prop :=
  | trace_equiv_step_vis :
      forall e1 e2
        (HRe : related_event_step R e1 e2),
        trace_equiv_step (Vis e1) (Vis e2)

  | trace_equiv_step_tau :
      forall x1 x2 k1 k2
        (HRk : R k1 k2),
        trace_equiv_step (Tau x1 k1) (Tau x2 k2)

  | trace_equiv_step_lft :
      forall x1 k1 k2
        (IH : trace_equiv_step k1 k2),
        trace_equiv_step (Tau x1 k1) k2

  | trace_equiv_step_rgt :
      forall x2 k1 k2
        (IH : trace_equiv_step k1 k2),
        trace_equiv_step k1 (Tau x2 k2)
  .
  Hint Constructors trace_equiv_step.
  
End OBSERVATIONAL_EQUIVALENCE.

Hint Constructors related_effect_step related_event_step trace_equiv_step.

Lemma related_effect_step_monotone : forall X (R1 R2: X -> X -> Prop)
                                        (HR: forall d1 d2, R1 d1 d2 -> R2 d1 d2) e1 e2
                                        (HM:related_effect_step R1 e1 e2),
    related_effect_step R2 e1 e2.
Proof.
  intros X R1 R2 HR e1 e2 HM.
  dependent destruction HM; constructor; eauto.
Qed.  
Hint Resolve related_effect_step_monotone : paco.

Lemma related_event_step_monotone : forall X (R1 R2:X -> X -> Prop)
                                        (HR: forall d1 d2, R1 d1 d2 -> R2 d1 d2) m1 m2
                                        (HM:related_event_step R1 m1 m2),
    related_event_step R2 m1 m2.
Proof.
  intros X R1 R2 HR m1 m2 HM.
  dependent destruction HM; constructor; eauto using related_effect_step_monotone.
Qed.  
Hint Resolve related_event_step_monotone : paco.  

Lemma trace_equiv_step_monotone : forall {X}, monotone2 (@trace_equiv_step X).
Proof.
  unfold monotone2. intros. induction IN; eauto using related_event_step_monotone.
Qed.
Hint Resolve trace_equiv_step_monotone : paco.

Definition trace_equiv {X} (p q: Trace X) := paco2 (@trace_equiv_step X) bot2 p q.
Hint Unfold trace_equiv.

Lemma upaco2_refl : forall {X} F r, reflexive X r -> reflexive _ (upaco2 F r).
Proof.
  intros X F r H.
  unfold reflexive. intros. right. apply H.
Qed.


Print reflexive.
Print relation.
Print trace_equiv.
Print reflexive.




Definition TraceState := Trace state.


Print testytest.


Lemma trace_equiv_refl : reflexive TraceState trace_equiv.
Proof.
  pcofix CIH. intro d.
  pfold. destruct d; eauto.
  - destruct v; eauto. destruct e; econstructor; eauto; constructor; apply related_effect_refl;
    apply upaco2_refl; auto.
Qed.

Lemma trace_equiv_symm : symmetric TraceState trace_equiv.
Proof.
  pcofix CIH.
  intros d1 d2 H.
  punfold H. 
  induction H; pfold; econstructor; eauto.
  - dependent destruction HRe; subst; eauto.
    constructor. inversion HRe; constructor; eauto.
    + intros. specialize (HRk a2 a1 (sym_eq H1)). pclearbot. right. eauto.
    + intros. specialize (HRk v2 v1 (sym_eq H1)). pclearbot. right. eauto.
    + pclearbot. right.  eauto.
    + intros. specialize (HRk rv2 rv1 (sym_eq H1)). pclearbot. right. eauto.
  - pclearbot. right. eauto.
  - punfold IHtrace_equiv_step.
  - punfold IHtrace_equiv_step.
Qed.



