Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.





Definition convert (c:definition cfg) : seq.seq block := blks (df_instrs c).

Print instr.


Definition optimise_code (o:code -> code) (b:code) : code := o b.

Print block.

Definition optimise_block (o:code -> code) (b:block) : block := mk_block (blk_id b) (blk_phis b) (optimise_code o (blk_code b)) (blk_term b).


Definition optimise_list_block (o:code -> code) (b:list block) : list block :=
  map (optimise_block o) b.


Definition optimise_cfg (o:code ->  code) (c:cfg) : cfg :=
  mkCFG (init c) (optimise_list_block o (blks c)) (glbl c).
Print definition.


Definition optimise_definition (o:code -> code) (c:definition cfg) :=
  mk_definition cfg (df_prototype c) (df_args c) (optimise_cfg o (df_instrs c)).


Definition optimise_list_definition (o:code -> code) (c: list (definition cfg)) :=
  map (optimise_definition o) c.


Definition optimise_modul (o:code -> code) (c: modul cfg) :=
  mk_modul cfg (m_name c) (m_target c) (m_datalayout c) (m_globals c) (m_declarations c) (optimise_list_definition o (m_definitions c)).

Print block.
Definition testfunc (m:mcfg) (o:code -> code) :=
  (forall fnid, (find_function m fnid = None /\ find_function (optimise_modul o m) fnid = None) \/ (forall cfg1 cfg2, find_function m fnid = Some cfg1 /\ find_function (optimise_modul o m) fnid = Some cfg2 /\  ( forall bkid, (CFG.find_block (convert cfg1) bkid = None /\ CFG.find_block (convert cfg2) bkid = None) \/ (forall b1 b2, CFG.find_block (convert cfg1) bkid = Some b1 /\ CFG.find_block (convert cfg2) bkid = Some b2 /\ (b1.(blk_term) = b2.(blk_term))  /\ (b1.(blk_id) = b2.(blk_id))  /\ (b1.(blk_phis) = b2.(blk_phis)) /\ (forall pt ins ins1, find_instr (blk_code b1) pt (blk_term_id b1) = Some ins /\ find_instr (blk_code b2) pt (blk_term_id b2) = Some ins1)

















  )))) /\


  (forall b1 s mem, compare_seq (exec_code1 m b1 (tauitem mem s)) (exec_code1 (optimise_modul o m) (optimise_code o b1)  (tauitem mem s))).




Definition startfunc1 fnid A o := find_function (optimise_modul o A) fnid.

Definition endfunc1 fnid A := find_function A fnid.


Definition targetfunc1 fnid A o :=
  match endfunc1 fnid A with
  | Some a => Some (optimise_definition o a)
  | None => None
  end.


Lemma equiv_func1 : forall A o fnid, find_function (optimise_modul o A) fnid = targetfunc1 fnid A o.
Proof. Admitted.


Definition startfunc o df_instrs bk := find_block (optimise_list_block o (blks df_instrs)) bk.

Definition endfunc df_instrs bk := find_block (blks df_instrs) bk.



Definition targetfunc o df_instrs bkid :=
  match endfunc df_instrs bkid with
  | Some a => Some (optimise_block o a)
                             | None => None 
  end.


Lemma equiv_func : forall o df_instrs bk, find_block (optimise_list_block o (blks df_instrs)) bk = targetfunc o df_instrs bk.
Proof. Admitted.





Definition startfunc2 o blk_code pt i := find_instr (optimise_code o blk_code) pt i.


Definition endfunc2 blk_code pt i : option (cmd * option instr_id) := find_instr blk_code pt i.
Print find_instr.
Definition targetfunc2 o blk_code pt i : option (cmd * option instr_id) :=
  match endfunc2 blk_code pt i with
   	| Some (CFG.Step a, b) =>  Some (CFG.Step (o a), b)
	| Some (a, b) =>  Some (a, b)
	| None => None
  end.

 

Print find_instr.
Print targetfunc2.


    



Definition startfunc3 pt i blk_code := match find_instr blk_code pt i with
               | Some (c, _) => Some c
               | None => None
               end.


Fixpoint new_find_instr (blk_code:code) (p:instr_id) :=
  match blk_code with
  | nil => None
  | (x, i)::cd => if (decide (p = x)) then Some (CFG.Step i) else new_find_instr cd p
  end.
Print new_find_instr.
Definition test_cmd (o:option cmd) :=
  match o with
  | None => true
  | Some (CFG.Step _) => true
  | Some _ => false
    end.



Lemma new_find_always_true : forall pt i blk_code, test_cmd (startfunc3 pt i blk_code) = true.
  Proof. intros. unfold test_cmd. induction blk_code. simpl in *. auto. unfold startfunc3 in *. simpl in *. destruct a. 
         unfold is_left. destruct (decide (pt = i0)). auto. apply IHblk_code. Qed.

Lemma test : forall pt i blk_code result, startfunc3 pt i blk_code = result -> test_cmd result = true. Proof. intros. unfold startfunc3 in H. induction blk_code. simpl in *. rewrite <- H. simpl. auto. simpl in *. destruct a. destruct (decide (pt = i0)). subst. simpl in *. auto. apply IHblk_code. apply H. Qed.



Lemma test1 : forall A blk_code pt i, (match find_instr blk_code pt i with
         | Some (c, _) => Some c
         | None => None
         end = A) -> test_cmd A = true.
Proof. intros. induction blk_code; simpl in *; subst; simpl in *; eauto. destruct a; simpl in *; eauto. destruct (decide (pt = i0)); eauto. Qed.

Print find_instr.



Lemma test2 : forall A B C m blk_code, (compare_seq
         (A :: exec_code1 m blk_code B)
         C) -> False. Proof. Admitted.
Lemma Test123 : (forall cd p t ins, find_instr cd p t = Some ins) -> forall m o, testfunc m o -> forall st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (optimise_modul o m) st)).
Proof. intros instr m o test. pcofix CIH.  intros. pfold. assert ( (memD mem (sem (optimise_modul o m) st)) = unroll  (memD mem (sem (optimise_modul o m) st))). destruct  (memD mem (sem (optimise_modul o m) st)); eauto. rewrite H; clear H. assert ( (memD mem (sem m st)) = unroll  (memD mem (sem m st))). destruct  (memD mem (sem m st)); eauto. rewrite H; clear H.
       destruct test. generalize (H0); intro. destruct st. destruct p. destruct p. generalize (H fn). intro. rewrite equiv_func1 in H2. unfold targetfunc1 in H2. unfold endfunc1 in H2.
       remember (find_function m fn) as findfunc. destruct findfunc. destruct H2. destruct H2.
       inversion H2. specialize (H2 d (optimise_definition o d)). destruct H2. clear H2. destruct H3. clear H2. specialize (H3 bk). unfold convert in *. rewrite equiv_func in H3. unfold targetfunc in H3. unfold endfunc in H3. remember (find_block (blks (df_instrs d)) bk) as findblock. destruct findblock. destruct H3. destruct H2. inversion H2. specialize (H2 b (optimise_block o b)). destruct H2.
       clear H2. destruct H3. clear H2. destruct b. simpl in H3. unfold blk_term_id in H3. simpl in H3.


       simpl in *. rewrite <- Heqfindfunc. rewrite <- Heqfindblock. unfold block_to_cmd in *. unfold blk_term_id in *. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. rewrite <- Heqfindfunc. rewrite equiv_func. unfold targetfunc. unfold endfunc. rewrite <- Heqfindblock. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt)); simpl in *; eauto. subst.


       admit.

       destruct H3. clear H2. destruct H3. clear H2. destruct H3. clear H2. specialize (H3 pt).



       specialize (H1 blk_code). induction (optimise_code o blk_code), blk_code; simpl in *; eauto. destruct p.


       specialize (H1  ({| fn := fn; bk := bk; pt := pt |}, e, s) mem). simpl in *. rewrite <- Heqfindfunc in H1. rewrite <- Heqfindblock in H1. unfold block_to_cmd in H1. unfold blk_term_id in H1. simpl in *.
       destruct (decide (i = pt)); simpl in *; subst. admit.
       destruct ( decide (pt = i0)); subst; simpl in *; eauto.




       destruct i0, i1; simpl in *; eauto. destruct ( eval_op e None op); simpl in *; eauto. apply test2 in H1. inversion H1. destruct fn0. destruct i0; simpl in *; eauto. destruct  (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply test2 in H1. inversion H1.
       apply test2 in H1. inversion H1. destruct ptr; simpl in *. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply test2 in H1. inversion H1.
       destruct fn0; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. destruct t0; simpl in *; eauto.  apply test2 in H1. inversion H1.  destruct val, ptr; simpl in *; eauto. destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto. destruct  v2; simpl in *; eauto. apply test2 in H1. inversion H1. simpl in *. admit.







       admit. admit.


       admit. admit.







       Admitted.