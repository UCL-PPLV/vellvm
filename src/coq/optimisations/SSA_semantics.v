Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat.
Set Implicit Arguments.


Definition get_block (CFG:mcfg) fid bid :=
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  mret blk
.

Fixpoint wf_phis (phis:seq (local_id * phi)) (bk:block_id) (e:env) :=
  match phis with
  | nil => true
  | (l, Phi typ l2) :: tl => match assoc AstLib.RawID.eq_dec bk l2 with
                             | Some op => match eval_op e (Some typ) op with
                                          | inr _ => wf_phis tl bk e
                                          | inl _ => false
                                          end
                                            
                             | None => false                        
                          end
                            
  end.



Definition branch_correct (m:mcfg) := forall p e br phis n_pc,
    fetch m p = Some (Term (TERM_Br_1 br)) -> find_block_entry m (fn p) br = Some (BlockEntry phis n_pc) ->
    wf_phis phis (bk p) e.



Definition block_uid m := forall fn bk b, get_block m fn bk = Some b -> ( NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil)).


Fixpoint compare_length A B (l1: seq A) (l2: seq B) : Prop :=
  match l1, l2 with
  | nil, nil => True
  | _ :: tl, _ :: tl1 => compare_length tl tl1
  | _, _ => False
  end.



Lemma compare_length_trans : forall A B C (l1: seq A) (l2: seq B) (l3: seq C),
    compare_length l1 l2 -> compare_length l2 l3 -> compare_length l1 l3.
Proof. induction l1, l2, l3; simpl in *; eauto. intros. inversion H. Qed.


Lemma compare_length_sym : forall A B (l1: seq A) (l2: seq B), compare_length l1 l2 = compare_length l2 l1.
  Proof. induction l1, l2; simpl in *; eauto. Qed. 

Lemma map_preserves_length : forall A B C (l1:seq A) (l2:seq B) (f:B -> C) (l3:seq C), compare_length l1 l2 ->
                                                                                       map f l2 = l3 -> compare_length l1 l3.
Proof. induction l1, l2, l3; simpl in *; eauto; intros.
       +induction l3. simpl in *. inversion H0. simpl in *. inversion H0. simpl in *. inversion H. simpl in *. inversion H0. simpl in *. inversion H0. subst. inversion H0. eapply IHl1 in H; eauto. Qed.

Lemma map_monad_partition : forall  t val l2 l3 e, 
    map_monad (fun '(t, op) => eval_op e (Some t) op) ((t, val)::l2) = inr l3 ->
    exists res1 res2,  eval_op e (Some t) val = inr res1 /\ map_monad  (fun '(t, op) => eval_op e (Some t) op) l2 = inr res2 /\ l3 = res1 :: res2.
Proof. intros. simpl in *. destruct (eval_op e (Some t) val). inversion H. 
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) l2). inversion H. inversion H. eauto. Qed.


Lemma map_moad_preserves_length : forall l2 l3 e,  map_monad (fun '(t, op) => eval_op e (Some t) op) l2 = inr l3 -> compare_length l2 l3.
Proof. induction l2. intros. simpl in *. destruct l3. eauto. inversion H.



       destruct a.

       intros. dupl H.  eapply map_monad_partition in H0.

       destruct H0. destruct H0. destruct H0. destruct H1. rewrite H2.
       simpl. eapply IHl2. eauto. Qed.


(*WF call instructions - Call instructions are wff if they have the same number of arguments as the prototype of the instruction being called*)




Definition wf_call_instr (m:mcfg) := forall p fn func args t,
  fetch m p = Some (CFG.Step (INSTR_Call t args)) -> snd t = ID_Global fn ->
  find_function m fn = Some func -> compare_length (df_args func) args.

Inductive wf_program (m:mcfg) : Prop :=
  | wf_program_intro : forall (wf_call: wf_call_instr m)(buid: block_uid m) (bcor: branch_correct m), wf_program m.