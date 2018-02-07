Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Require Import Vellvm.optimisations.SSA_semantics.
Require Import Vellvm.optimisations.maps.
Require Import Vellvm.optimisations.Kildall.valueanalysis.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.optimisations.Kildall.congruence_proof_kildall.
Require Import Vellvm.optimisations.Kildall.congruence_definition_kildall.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Print Expr.

Ltac inv t := inversion t; subst; clear t; eauto.
Ltac destr_eq t := destruct t eqn:?; simpl; unfold eval_expr; eauto.
Ltac destr t := destruct t; simpl; unfold eval_expr; eauto.
Ltac appl t y := generalize y; intro; eapply t in y.


Ltac break_inner_match' t :=
  match t with
   | context[match ?X with _ => _ end] => break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

Ltac break_inner_match_goal :=
  match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

Ltac break_goal :=  break_inner_match_goal; simpl in *; eauto; try constructor.
Ltac try_resolve := try (repeat break_goal); try constructor.


(* LLVM IR is 3 address code. VELLVM IR permits infinite address code, but we only implement constant folding for 3 address code*)


Print aenv.
Definition get_value (a:aenv) (i:ident) :=
  match i with
  | ID_Global _ => SV (VALUE_Ident i)
  | ID_Local id => match AE.get id a with
                   | avalue (DV (VALUE_Integer i)) => SV ((VALUE_Integer i))
                   | _ => SV (VALUE_Ident i)
                   end
                     
  end.


Definition substitute_value (a:aenv) (o:Ollvm_ast.value) :=
  match o with
  | SV (VALUE_Ident (ID_Local ident)) => match AE.get ident a with
                                        |  (avalue (DV (VALUE_Integer i))) => SV ((VALUE_Integer i))
                                        | _ => SV (VALUE_Ident (ID_Local ident))
                                        end
  | _ => o
  end.


Print modul_opt.
Print analyse.


Definition optimise_val (a:aenv) (o:Ollvm_ast.value)  (r:raw_id) :=
  match o with
  | SV (VALUE_Ident (ID_Local ident)) =>  (get_value a (ID_Local ident))
  | SV (OP_IBinop ibinop (TYPE_I 32)  (SV (VALUE_Ident (ID_Local ident)))  (SV (VALUE_Ident (ID_Local ident1)))) =>
  (SV (OP_IBinop ibinop (TYPE_I 32)  (substitute_value a ( (SV (VALUE_Ident (ID_Local ident))))) (substitute_value a ( (SV (VALUE_Ident (ID_Local ident1)))))))
  | rest => rest 
  end.


Print ematch.

Lemma ematch_get : forall e a id val, ematch e a -> AE.get id a = avalue val -> lookup_env e id = Some val.
Proof. intros. unfold ematch in *. simpl in *. specialize (H id). rewrite H0 in H. simpl in *. inversion H; subst. unfold lookup_env_aenv in *. simpl in *. destr_eq (lookup_env e id). inversion H1. subst. eauto. inversion H1. Qed.


Lemma val_correct : forall id a e ins,  ematch e a ->
                                        eval_op e None ins = eval_op e None (optimise_val a ins id).
Proof. intros.
       induction ins.  destr e0. destr id0. destr_eq (AE.get id0 a). eapply ematch_get in H; eauto. destr_eq n. destr_eq e0; rewrite H; eauto. destr t. destr sz. destr p. destr p. destr p. destr p. destr p. destr p. destr v1. destr e0. destr id0. destr v2. destr e0. destr id1.

       destr_eq (AE.get id0 a).
       +simpl. destr (lookup_env e id0). destr_eq (AE.get id1 a). eapply ematch_get in Heqt0; eauto. rewrite Heqt0. destr n; try destr e0; simpl in *; rewrite Heqt0; eauto. eapply ematch_get in Heqt; eauto. rewrite Heqt. simpl in *.

        destr_eq (AE.get id1 a). simpl in *. destr n; simpl in *. destr e0; simpl in *; rewrite Heqt; eauto. rewrite Heqt. simpl in *. eauto. rewrite Heqt. eauto. rewrite Heqt. eauto. rewrite Heqt. eauto. rewrite Heqt. eauto. rewrite Heqt. eauto. simpl in *. eapply ematch_get in Heqt0; eauto. rewrite Heqt0. simpl in *; destr n; destr n0; try destr e0; simpl in *; try rewrite Heqt0; try rewrite Heqt; try destr e1; simpl in *; try rewrite Heqt0; simpl in *; eauto. simpl in *. destr (lookup_env e id1). destr n; simpl in *; eauto; try destr e0; simpl in *; try rewrite Heqt; eauto. destr n; try destr e0; simpl in *; try rewrite Heqt; eauto. simpl in *. destr_eq (lookup_env e id0). destr_eq (AE.get id1 a). eapply ematch_get in Heqt0; eauto. rewrite Heqt0. destr n. destr e0; simpl in *; rewrite Heqt0; simpl in *; eauto. simpl in *; rewrite Heqt0; eauto.  simpl in *; rewrite Heqt0; eauto.  simpl in *; rewrite Heqt0; eauto.  simpl in *; rewrite Heqt0; eauto.  simpl in *; rewrite Heqt0; eauto.  simpl in *; rewrite Heqt0; eauto. Qed.



       


Definition get_point (m:mcfg) (p:pc) := PCMap.get p (analyse m).

Definition optimise_instr (p: PCMap.t DS.L.t) (p:pc) (m:mcfg) (i:instr_id * instr) : instr :=
  match get_point m p with
  | VA.Bot => snd i
  | VA.State ae => match fst i, snd i with
                   | (IId id), INSTR_Op ins => INSTR_Op (optimise_val ae ins id)
                   | _, _ => snd i
                              
                   end
                     
  end.

Lemma eq_result_refl : forall a, eq_result a a.
Proof. destr_eq a; try constructor. destr_eq e; try constructor. Qed.
Hint Resolve eq_result_refl.
  Lemma const_prop  : forall m st mem (wf_program: wf_program m) (sstate: sound_state m st), trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt (optimise_instr (analyse m)) m) st)).
Proof. intros.  apply congruence_correct1; eauto.


       
       unfold correct_instr1; intros; eauto.
       unfold optimise_instr; simpl in *. inv sstate0; simpl in *. unfold get_point. rewrite AN.
       destr_eq id. destr_eq instr; subst. eapply  val_correct in EM. unfold exec_code1; simpl in *; unfold individual_step; simpl in *. rewrite -> EM. eauto. Qed.