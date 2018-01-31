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

Require Import Vellvm.optimisations.static_analysis.


(*An abstract register implies there is a list of  previous and succeeding registers*)

Lemma find_areg_implies_list: forall l i i1,  NoDup (map fst l) -> find_areg l i = Some i1 ->
                            exists head tl, l = head ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_areg in *. induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *.

       unfold is_left in *. simpl in *. destruct (decide (l0 = i)). inversion H0. subst. exists nil. eauto.
       inversion H; subst. apply IHl in H4; eauto. inversion H4. inversion H1. subst. eauto.
       exists ( (l0, o) :: x). exists x0. auto. Qed.
Print find_areg.
(*A tuple of program l at abstract register i consists of the value of register i, and the following register r*)
(*This implies register r succeeds register r*)
Lemma list_to_tuple_implies_succeession  : forall l i i1 r,  NoDup (map fst  l) -> list_to_tuple l i = Some (i1, Some r) ->
                            exists head tl v,  l = head ++ (cons (i, i1) (cons (r, v) nil)) ++ tl.
Proof.
  intros. unfold list_to_tuple in *. simpl in *.  induction l.  inversion H0.
  simpl in *. destruct a. simpl in *. unfold is_left in *. simpl in *.
  destruct ( decide (l0 = i)). subst.  inversion H0. subst.
  destruct l. simpl in *. inversion H3. simpl in *. inversion H3. destruct p.
  simpl in *.  subst. exists nil. simpl in *. exists l. exists o. eauto.  


  inversion H; subst. apply IHl in H4; eauto. inversion H4; subst. inversion H1. inversion H2. subst.
  exists ((l0, o) :: x). simpl in *. exists x0. exists x1. eauto. Qed.


(*NEED TO CHECK*)

Definition newlist := list (instr_id * cmd).
Definition opt_fallthrough (n:newlist) : option instr_id :=
  match n with
  | nil => None
  | hd :: _ => Some (fst hd)
  end.

  Fixpoint find_in_newlist(n:newlist)  (i:instr_id) :=
  match n with
  | nil => None
  | hd :: tl => if decide ((fst hd) = i) then Some (snd hd, opt_fallthrough tl) else find_in_newlist tl i
  end.

(*An instruction in block b maps to the same result in the corresponding prepared block*)
  
Lemma block_maps_prep_correct : forall i i1 t b,  NoDup (map fst (prep_block b)) ->
                                                block_to_cmd b i =  Some (i1, Some t) ->
                                                find_in_newlist (prep_block b) i = Some (i1, Some t).
  Proof. intros. unfold block_to_cmd in *. unfold blk_term_id in *. destruct b. simpl in *.
         destruct blk_term. simpl in *. destruct (decide (i0 = i)); subst. inversion H0.
         simpl in *. induction blk_code; simpl in *. inversion H0. unfold is_left in *. destruct a. simpl in *.
destruct ( decide (i2 = i)). subst. destruct ( decide (i = i)). unfold opt_fallthrough. destruct blk_code. simpl in *. eauto. simpl in *. destruct p. simpl in *. eauto. contradiction n0; eauto. unfold prep_block in *. simpl in *. apply IHblk_code. inversion H. subst. eauto. destruct (decide (i = i2)); subst. contradiction n0; auto. auto. Qed.



(*The prepared block code keeps the exact same instr_ids*)
Lemma map_block_code : forall block_code0, ((map fst (map map_exp_to_cmd block_code0)) = (map fst block_code0)).
Proof. induction block_code0; simpl in *; eauto. inversion IHblock_code0. eauto. Qed.


(*The prepared block  keeps the exact same instr_ids*)
Lemma map_block : forall block, (map fst (blk_code block)) ++ (cons (blk_term_id block ) nil) =  (map fst (prep_block block)).
Proof. intros. unfold prep_block. unfold map_term_to_cmd in *. unfold blk_term_id in *.  destruct block. simpl in *. induction blk_code. simpl in *. eauto.
       simpl in *. destruct a. simpl in *. rewrite IHblk_code. eauto. Qed.
       

(*NEED TO CHECK*)
Lemma incr_pc_implies1 : forall l i i1 t,
    NoDup (map fst l) -> find_in_newlist l i = Some (i1, Some t) ->
    exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof.  simpl in *. intros. induction l; simpl in *.
       +inversion H0.
       +simpl in *. destruct a. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (i0 = i)). subst. simpl in *. inversion H0. subst.
        *exists nil. simpl in *. destruct l. simpl in *. inversion H3. simpl in *. exists l. simpl in *. destruct p. simpl in *. inversion H3. subst. exists c. eauto.
        *inversion H. subst. apply IHl in H4; eauto. inversion H4. inversion H1. subst. inversion H2. subst. simpl in *. exists ((i0, c) :: x). simpl in *. exists x0. exists x1. eauto. Qed.







(*Given that registers t and i are successive, the value analysis at t is equal to the value analysis at i passed through the transfer function*)
Lemma value_analysis_equals_previous : forall l hd i i1 t r tl a,  NoDup (map fst l) ->
                                             l = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl ->
                                             value_analysis_fix a l t =
                                             transfer (value_analysis_fix a l i) (i, i1).
Proof. intros. simpl in *. generalize a. simpl in *. rewrite H0. rewrite H0 in H. clear H0. induction hd. simpl in *.

unfold is_left.
destruct ( decide (i = t)). subst.
inversion H. subst. contradiction H2.  simpl; eauto.
destruct ( decide (t = t)). destruct ( decide (i = i)). eauto. contradiction  n0; eauto. contradiction n0; eauto.
simpl in *. unfold is_left in *. destruct a0. simpl in *. destruct ( decide (i0 = t)). subst.
inversion H; subst. clear IHhd. clear H.  clear H3.
assert ( In t [seq fst i | i <- hd ++ [:: (i, i1), (t, r) & tl]]).  induction hd. simpl in *. right. left. auto.
simpl in *. right. apply IHhd. unfold not. intros. unfold not in H2. apply H2. right.  auto.
apply H2 in H. inversion H. destruct (decide (i0 = i)). subst. inversion H. subst.
clear IHhd. clear H. clear H3. assert ( In i [seq fst i | i <- hd ++ [:: (i, i1), (t, r) & tl]]).
induction hd. simpl in *. left. auto. simpl in *. right. apply IHhd. unfold not in *. intros. apply H2. right. auto. apply H2 in H. inversion H.
intros. remember ( (transfer a0 (i0, c))).
 apply IHhd. inversion H; subst; eauto. Qed.





(*Given a prepared block and two successive registers, the value analysis of the later is equal to the
application of the transfer function to the former*)
Lemma prep_block_value_analysis_equals_previous: forall block hd i i1 t r tl,
    NoDup (map fst  (prep_block block)) ->
    (prep_block block) = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl  ->
    value_analysis  (prep_block block) t = transfer (value_analysis  (prep_block block) i) (i, i1).
 Proof.  intros. unfold value_analysis. simpl in *. eapply value_analysis_equals_previous in H; simpl in *; eauto. Qed.


(*Given i maps to an instruction and register t succeeds it, the value analysis of t is equivalent to 
the value analysis of i passed through the transfer function*)
 
 Lemma block_to_cmd_value_analysis : forall prog i i1 t, NoDup ((map fst (blk_code prog)) ++ ( blk_term_id prog ) :: nil) -> 
block_to_cmd prog i =  Some (i1, Some t)  ->
value_analysis  (prep_block prog) t = transfer (value_analysis  (prep_block prog) i) (i, i1).
 Proof. intros. assert (H' := H). rewrite map_block in H.
  assert (H'' := H).   assert (H''' := H). 
        eapply  block_maps_prep_correct in H; eauto. eapply incr_pc_implies1 in H''; eauto.
inversion H''. inversion H1. inversion H2. eapply  value_analysis_equals_previous in H'''; eauto. Qed.


 (*Similar to previous*)
Lemma value_analysis_equals_previous_val_analysis : forall block i i1 t i_va,  NoDup ((map fst (blk_code block)) ++ (blk_term_id block :: nil)) ->
                                        block_to_cmd block i = Some (t, Some i1) ->
                                        value_analysis (prep_block block) i = i_va  ->
                                        value_analysis (prep_block block) (i1) = transfer i_va (i, t).
Proof. intros. eapply  block_to_cmd_value_analysis in H; eauto. rewrite <- H1; eauto. Qed.

Print  value_analysis_equals_previous_val_analysis.

(*Few more helper functions*)
               
Definition prog_to_cmd (CFG : mcfg) (p:pc) :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
   (block_to_cmd blk iid).
   
Lemma fetch_and_incr_implies_cmd : forall prog p ins next_pc, fetch prog p = Some ins ->
                                                              incr_pc prog p = Some next_pc ->
                                                              prog_to_cmd prog p = Some (ins, Some (pt next_pc)).
Proof. intros.
       +unfold fetch, incr_pc, prog_to_cmd in *; simpl in *.  destruct p.
        destruct ( find_function prog fn); inversion H.
        destruct (find_block (blks (df_instrs d)) bk); inversion H.
        destruct (block_to_cmd b pt); inversion H. destruct p. inversion H; subst.
        destruct o; inversion H0; simpl in *; eauto. Qed.







(*Lemmas about the substring relation *)

(*If is present in l1, then it is present in l2*)   
Lemma substring_in_l1_implies_in_l2: forall l2 l1 n a ,  substring l1 l2 = true -> In (n, Some a) l1 -> In (n, a) l2.
Proof.

  induction l2. intros.
  +simpl in *. destruct l1. simpl in *. inversion H0. simpl in *. inversion H.
  +simpl in *. intros. induction l1. simpl in *. inversion H0. simpl in *. remember (aenv_env_pair a1 a). destruct b. simpl in *. inversion H0. left. unfold aenv_env_pair in *. destruct a1. destruct a.  destruct o. unfold beq_local_id in *. unfold beq_value in *. simpl in *. destruct (decide (l = l0)). destruct ( decide (v0 = v)). simpl in *. subst. inversion H1. subst. auto. simpl in *. inversion Heqb. simpl in *. inversion Heqb. inversion H1. 

 eapply IHl2 in H; eauto. simpl in *. inversion H. Qed.



  
(*Get env implies it is in l*)
Print lookup_env.
Lemma lookup_env_convert : forall l e1 i1, Some e1 = lookup_env l i1 -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. unfold lookup_env in H. simpl in *. destruct ( AstLib.RawID.eq_dec i1 l0). inversion H. subst; eauto. right. apply IHl; eauto. Qed.

(*Get from aenv implies in l*)
Lemma get_from_aenv_convert : forall l e1 i1, Some e1 = get_from_aenv l i1 -> In (i1, e1) l.
Proof. intro. induction l; intros.
       +simpl in *. inversion H.
       +simpl in *. destruct a. unfold is_left in *. destruct ( decide (l0 = i1)); inversion H; subst; eauto. Qed.


(*alternate substring definition*)
Lemma substring_get_in_l1_implies_in_l2: forall l2 l1 n a ,  substring l1 l2 = true ->  (Some (Some a)) = get_from_aenv l1 n ->  In (n, a) l2.
Proof. intros. eapply get_from_aenv_convert in H0. eapply  substring_in_l1_implies_in_l2; eauto. Qed.





Lemma lookup_env_equal : forall l a0 l2,  lookup_env ((l, a0) :: l2) l = Some a0.
Proof. unfold lookup_env. simpl in *. intros. destruct (AstLib.RawID.eq_dec l l); eauto. contradiction n; eauto. Qed.
Hint Resolve lookup_env_equal.


(*Most useful substring property. If lookup in l1 returns some value, then l2 always returns the samse*)
Lemma substring_get_in_l1_get_in_l2 : forall l2 l1 a n,   substring l1 l2 = true ->  get_from_aenv l1 n = Some (Some a) ->  lookup_env l2 n = Some a.
Proof. induction l2.
       +simpl in *. intros. simpl in *. destruct l1. simpl in *. inversion H0. simpl in *. inversion H.
       +intros. generalize H; intros. eapply substring_get_in_l1_implies_in_l2 in H1; eauto. simpl in *. destruct a. simpl in *.
        inversion H1. inversion H2. subst. eauto.


        induction l1. simpl in *. inversion H0. simpl in *. unfold aenv_env_pair in H. destruct a. destruct o.
        unfold is_left in *.  destruct (decide (l0 = n)). subst. unfold beq_local_id, beq_value in *. destruct ( decide (n = l)), (decide (v0 = v)); simpl in *; subst. inversion H0; subst; eauto. inversion H. inversion H. inversion H.


        unfold beq_local_id, beq_value in *. destruct (decide (l0 = l)), (decide (v0 = v)); simpl in *; subst; eauto.

        unfold lookup_env. simpl in *. destruct ( AstLib.RawID.eq_dec n l). subst. contradiction n0; eauto. unfold lookup_env in IHl2. eapply IHl2; eauto.


        unfold is_left, beq_local_id in *. destruct (decide (l0 = l)), (decide (l0 = n)); simpl in *; subst. inversion H0.
        unfold lookup_env. simpl in *. destruct ( AstLib.RawID.eq_dec n l); subst. contradiction n0; eauto. eapply IHl2; eauto. inversion H. inversion H. Qed.





(*********************************************************************************)
(*Proving the preservation for the static analysis*)


Lemma substring_nil_add : forall id b v e,  substring (value_analysis (prep_block b) (IId id)) e ->
                                        substring ((id, None) :: value_analysis (prep_block b) (IId id)) (add_env id v e).
Proof. intros. simpl. unfold beq_local_id. unfold decide. simpl in *. destruct ( eq_dec_local_id id id ); simpl in *; eauto. Qed.
Hint Resolve substring_nil_add.

Lemma substring_add_item : forall id b e x, substring (value_analysis (prep_block b) (IId id)) e -> substring
    ((id, Some x)
     :: value_analysis (prep_block b) (IId id))
    (add_env id x e).
Proof. intros. simpl in *. unfold beq_local_id. unfold beq_value. unfold decide. destruct ( eq_dec_local_id id id), (eq_dvalue x x); simpl in *; eauto. Qed.
Hint Resolve substring_add_item.

Lemma substring_start_block : forall b0 l, substring (value_analysis (prep_block b0) (blk_entry_id b0)) l. Proof. intros. unfold prep_block. unfold blk_entry_id. unfold blk_term_id in *. unfold value_analysis. destruct b0. simpl in *. unfold fallthrough. simpl in *. destruct blk_code; simpl in *; eauto; unfold is_left. destruct ( decide (fst blk_term = fst blk_term)), l; simpl in *; eauto. destruct p; simpl in *. destruct ( decide (i = i)), l; simpl in *; eauto. Qed.
Hint Resolve substring_start_block.







(********************************************************************************************)
(*Preservation proofs*)

(*


       Lemma step_preserves_sound_env : forall m st st1, 
   wf_program m  -> sound_state m st  -> stepD m st = Step st1 -> sound_env m (pc_of st1) (env_of st1).
       Proof. intros. destruct st, st1. destruct p, p0. destruct p, p0. simpl.
              inversion H0; subst. simpl in senv. simpl in sstack. unfold sound_env in *. simpl.  simpl in senv.
              simpl in *. remember ( find_function m fn). destruct o. remember ( find_block (blks (df_instrs d)) bk). destruct o. remember ( block_to_cmd b pt). unfold wf_program in *. unfold get_block in H; simpl in H. specialize (H fn bk). rewrite <- Heqo in H. rewrite <- Heqo0 in H.
specialize (H b). assert (Some b = Some b) by auto. apply H in H2. clear H. rename H2 into H. 
              destruct o. destruct p; simpl in *. destruct c. destruct o; simpl in *; simpl in *.
              eapply value_analysis_equals_previous_val_analysis in H; eauto.
              +destruct pt, i; simpl in *; inversion H1.
               *remember ( eval_op e None op). destruct e1; simpl in *; inversion H1; subst. 
                unfold prep_selected_block in *; simpl in *. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. intros. inversion H2; subst. apply senv in H2. rewrite H. unfold transfer; simpl; destruct op, e0; eauto. simpl in Heqe1; inversion Heqe1; eauto.
               *destruct fn1.  destruct i.  unfold find_function_entry in *; simpl in *. remember ( find_function m id0). destruct o. remember ( find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o. simpl in *. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *. inversion H1. simpl in *. inversion H1; subst. unfold prep_selected_block; simpl in *. rewrite <- Heqo2. rewrite <- Heqo3. intros. inversion H2. subst. eauto. simpl in *. inversion H1. simpl in *. inversion H1. inversion H1.
               *destruct ptr. simpl in *. remember ( eval_op e (Some t0) v); simpl in *. destruct e1; simpl in *; eauto; inversion H1. destruct v0; inversion H1. clear H3. destruct fn1; destruct i. unfold find_function_entry in *; simpl in *. remember (find_function m id). destruct o. remember ( find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o; simpl in *. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *. inversion H1. destruct t; inversion H1; subst. unfold prep_selected_block in *; simpl in *. rewrite <- Heqo2. rewrite <- Heqo3. intros. inversion H2; subst; eauto. inversion H1. simpl in *; inversion H1. inversion H1.
               *destruct val, ptr; simpl in *. remember ( eval_op e (Some t) v). remember (eval_op e (Some t0) v0). clear H3. destruct e1, e2; simpl in *; inversion H1. clear H3. destruct v2; inversion H1. inversion H1.
              +destruct t; inversion H1; clear H3.
               *destruct v. destruct ( eval_op e (Some t) v); simpl in *; inversion H1. destruct s; inversion H1. destruct f; inversion H1.
               *destruct s; inversion H1. destruct f; inversion H1.
               *destruct v. destruct (eval_op e (Some t) v); simpl in *; inversion H1; clear H3. destruct v0; inversion H1. destruct ( StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; inversion H1. destruct (jump m fn bk br1 e s); simpl in *; inversion H1. destruct (jump m fn bk br2 e s); simpl in *; inversion H1.
               *destruct (jump m fn bk br e s); simpl in *; inversion H1.
              +simpl in *. inversion H1.
              +simpl in *. inversion H1.
              +simpl in *. inversion H1.
               Qed.
          

             Lemma step_preserves_sound_stack : forall m st st1, 
    wf_program m  -> sound_state m st  -> stepD m st = Step st1 -> sound_stack m (stack_of st1).
Proof.  intros. destruct st, st1. destruct p, p0. destruct p, p0. simpl.
 inversion H0; subst. simpl in senv. simpl in sstack. unfold sound_env in *. simpl.  simpl in senv.
 simpl in *. remember ( find_function m fn). destruct o. remember ( find_block (blks (df_instrs d)) bk). destruct o. specialize (H fn bk b). unfold get_block in *; simpl in *. rewrite <- Heqo in H; rewrite <- Heqo0 in H. assert (Some b = Some b) by auto. apply H in H2. clear H; rename H2 into H.



 remember ( block_to_cmd b pt). destruct o. destruct p; simpl in *. destruct c. destruct o; simpl in *; simpl in *.



 destruct pt, i; inversion H1.


        +remember ( eval_op e None op). destruct e1; simpl in *; inversion H1; subst. eauto.
        +destruct fn1. destruct i; simpl in *. unfold find_function_entry in *; simpl in *.
         remember (find_function m id0). destruct o. remember ( find_block (blks (df_instrs d0)) (init (df_instrs d0))); simpl in *; eauto. destruct o; simpl in *. remember ( map_monad (fun '(t, op) => eval_op e (Some t) op) args). destruct e1; simpl in *. inversion H1. simpl in *. inversion H1; subst. constructor; simpl in *; eauto. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo1. eauto. inversion H1. simpl in *; inversion H1. inversion H1.
        +destruct ptr. simpl in *. remember (eval_op e (Some t0) v). destruct e1; simpl in *; eauto. inversion H1.
        +destruct v0; simpl in *; inversion H1.
        +destruct fn1. destruct i; inversion H1. unfold find_function_entry in *. simpl in *. clear H3. clear H4. remember ( find_function m id). destruct o. remember (find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o; simpl in *. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1. clear H3. destruct t; simpl in *; inversion H1; subst. constructor; eauto. simpl in *. rewrite <- Heqo. rewrite <- Heqo0. exists (TYPE_Void, ID_Global fn0). exists args. exists n. split. eauto. split. rewrite <- Heqo1. eauto. rewrite <- Heqo1.
         eauto. inversion H1. simpl in *. inversion H1.
        +destruct val. destruct ptr. simpl in *. destruct ( eval_op e (Some t) v), (eval_op e (Some t0) v0); simpl in *; inversion H1. destruct v2; simpl in *; inversion H1. inversion H1.

         *destruct t; inversion H1.
        +destruct v. destruct ( eval_op e (Some t) v); simpl in *. inversion H1. destruct s; inversion H1. destruct f; simpl in *; inversion H1.
        +destruct s; inversion H1. destruct f; simpl in *; inversion H1.
        +destruct v; destruct ( eval_op e (Some t) v); simpl in *. inversion H3. destruct v0; simpl in *; inversion H1. destruct ( StepSemantics.Int1.eq x StepSemantics.Int1.one ); simpl in *. 
destruct ( jump m fn bk br1 e s); simpl in *. inversion H1. inversion H1. destruct (jump m fn bk br2 e s); simpl in *; inversion H1. destruct ( jump m fn bk br e s); simpl in *; inversion H1. simpl in *. inversion H1. simpl in *. inversion H1. simpl in *. inversion H1. Qed.




    
  Lemma step_preserves_sound_state: forall m st st1, 
        wf_program m -> sound_state m st  -> stepD m st = Step st1 -> sound_state m st1.
Proof. intros. constructor.  eapply  step_preserves_sound_stack in H; eauto. eapply step_preserves_sound_env; eauto. Qed.



    Lemma jump_preserves_sound_stack : forall m st st1, 
   wf_program m  -> sound_state m st  -> stepD m st = Jump st1 -> sound_stack m (stack_of st1). Proof.
intros. destruct st, st1. destruct p, p0. destruct p, p0. simpl.
              inversion H0; subst. simpl in senv. simpl in sstack. unfold sound_env in *. simpl.  simpl in senv.
              simpl in *. remember ( find_function m fn). destruct o. remember ( find_block (blks (df_instrs d)) bk). destruct o.
              specialize (H fn bk b). unfold get_block in *; simpl in *. rewrite <- Heqo in H; rewrite <- Heqo0 in H. assert (Some b = Some b) by auto. apply H in H2. clear H; rename H2 into H. 




              remember ( block_to_cmd b pt). destruct o. destruct p; simpl in *. destruct c. destruct o; simpl in *; simpl in *.
+destruct pt, i; simpl in *; inversion H1.
 *destruct ( eval_op e None op); simpl in *; inversion H1.
 *destruct fn1. destruct i; inversion H1. destruct  (find_function_entry m id0); simpl in *; inversion H1. destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1.
 *destruct ptr. destruct ( eval_op e (Some t0) v); simpl in *; inversion H1. destruct v0; simpl in *; inversion H1.
 *clear H3. destruct fn1. destruct i; inversion H1. clear H3. destruct  (find_function_entry m id); simpl in *; inversion H1.  clear H3. destruct f. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1. destruct t; inversion H1. destruct val, ptr. destruct ( eval_op e (Some t) v), ( eval_op e (Some t0) v0); simpl in *; inversion H1. destruct v2; simpl in *; inversion H1. inversion H1.


+destruct t; simpl in *; inversion H1.
 * destruct v; simpl in *. destruct s; simpl in *; inversion H1. destruct (eval_op e (Some t) v); simpl in *; inversion H1. destruct (eval_op e (Some t) v); inversion H1; simpl in *. destruct f; inversion H1; subst. inversion sstack; eauto. 
   +destruct s. inversion H1. destruct f; inversion H1; subst. inversion sstack; eauto.



+destruct v. destruct (eval_op e (Some t) v); simpl in *. inversion H3. destruct v0; inversion H1; clear H3. clear H4. remember ( StepSemantics.Int1.eq x StepSemantics.Int1.one). destruct b0; simpl in *.
 -unfold jump in *. destruct (find_block_entry m fn br1); simpl in *.  destruct b0. unfold monad_fold_right in *. remember (fix
           monad_fold_right (A B : Type) (M : Type -> Type) 
                            (H : Functor M) (H0 : Monad) 
                            (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs =>
                 monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end). rewrite <- Heqp0 in H1. destruct p0; simpl in *. inversion H1. inversion H1; subst; eauto. inversion H1. unfold jump in *. destruct (find_block_entry m fn br2 ). destruct b0. unfold monad_fold_right in *. remember  (fix
         monad_fold_right (A B : Type) (M : Type -> Type) 
                          (H : Functor M) (H0 : Monad) 
                          (f : A -> B -> M A) (l : seq B) 
                          (a : A) {struct l} : M A :=
           match l with
           | [::] => mret a
           | x :: xs =>
               monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
           end). rewrite <- Heqp0 in H1. destruct p0; simpl in *. inversion H1. inversion H1; subst; eauto. simpl in *. inversion H1.



   +unfold jump in *; simpl in *. destruct ( find_block_entry m fn br). destruct b0. unfold monad_fold_right in *. simpl in *. remember ( (fix
           monad_fold_right (A B : Type) (M : Type -> Type) 
                            (H : Functor M) (H0 : Monad) 
                            (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs =>
                 monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp0 in H3. destruct p0; simpl in *. inversion H3. inversion H3; subst; eauto.


   +inversion H3.
   +simpl in *. inversion H1.
   +simpl in *. inversion H1.
   +simpl in *. inversion H1.
                                                                                                                                                           Qed.


    

    Lemma block_id_eq : forall b0 d br, Some b0 = find_block (blks (df_instrs d)) br ->  br = blk_id b0. Proof. intros. destruct d. simpl in *. destruct df_instrs. simpl in *. induction blks. simpl in *. inversion H. simpl in *. destruct ( decide (blk_id a = br)). inversion H; subst. eauto. apply IHblks. clear IHblks. induction blks. simpl in *. eauto. simpl in *. destruct (decide (blk_id a0 = br)); eauto. Qed.




    Lemma jump_equiv : forall d m fn pt0 bk s0 br e s fn0 bk0 e0,  Some d = find_function m fn ->
                                       (do st <- jump m fn bk br e s; Jump st) =
       Jump ({| fn := fn0; bk := bk0; pt := pt0 |}, e0, s0) ->
  forall prep : seq (instr_id * cmd),
  prep_selected_block m {| fn := fn0; bk := bk0; pt := pt0 |} = Some prep ->
  substring (value_analysis prep pt0) e0.
Proof. intros. simpl in *. unfold prep_selected_block in *. unfold jump in *. simpl in *. unfold find_block_entry in *; simpl in *. rewrite <- H in H0. remember ( find_block (blks (df_instrs d)) br). destruct o; simpl in *. unfold monad_fold_right in *.
remember (  (fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp in H0. destruct p; simpl in *; inversion H0; subst. rewrite <- H in H1. generalize Heqo; intros. apply block_id_eq in Heqo0. subst. rewrite <- Heqo in H1. subst. inversion H1. subst. eauto. inversion H0. Qed.


Hint Resolve jump_equiv.

      
Lemma jump_preserves_sound_env : forall m st st1, 
    wf_program m  -> sound_state m st  -> stepD m st = Jump st1 -> sound_env m (pc_of st1) (env_of st1).
Proof.
intros. destruct st, st1. destruct p, p0. destruct p, p0. simpl.
inversion H0; subst. simpl in senv. simpl in sstack. unfold sound_env in *. simpl.  simpl in senv.
simpl in *.

remember ( find_function m fn). destruct o.

remember ( find_block (blks (df_instrs d)) bk). destruct o. 
remember ( block_to_cmd b pt). destruct o; simpl in *. destruct p; simpl in *. destruct c; simpl in *. destruct o; simpl in *.



+destruct pt, i; simpl in *; inversion H1.
 *destruct ( eval_op e None op); simpl in *; inversion H1.
 *destruct fn1. destruct i; inversion H1. destruct  (find_function_entry m id0); simpl in *; inversion H1. destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1.
 *destruct ptr. destruct ( eval_op e (Some t0) v); simpl in *; inversion H1. destruct v0; simpl in *; inversion H1.
 *clear H3. destruct fn1. destruct i; inversion H1. clear H3. destruct  (find_function_entry m id); simpl in *; inversion H1.  clear H3. destruct f. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1. destruct t; inversion H1. destruct val, ptr. destruct ( eval_op e (Some t) v), ( eval_op e (Some t0) v0); simpl in *; inversion H1. destruct v2; simpl in *; inversion H1. inversion H1.




  destruct t; inversion H1; clear H3; eauto.

  

  
+destruct v. destruct s; simpl in *; inversion H1.  destruct ( eval_op e (Some t) v); simpl in *; inversion H3.
remember ( eval_op e (Some t) v). destruct e1; simpl in *; inversion H1. clear H3; clear H4. destruct f; simpl in *; inversion H1; subst. inversion sstack; subst; eauto.
destruct H4. destruct H2. destruct H2.
 eapply fetch_and_incr_implies_cmd in H2; eauto. unfold prog_to_cmd in *. simpl in *.


 remember ( find_function m fn0). destruct o0. remember ( find_block (blks (df_instrs d0)) bk0). destruct o0. (*CLEAR*) specialize (H fn0 bk0 b0). unfold get_block in *; simpl in *. rewrite <- Heqo2 in H; rewrite <- Heqo3 in H. assert ( Some b0 = Some b0) by auto. apply H in H4. clear H; rename H4 into H.
 eapply value_analysis_equals_previous_val_analysis in H; eauto.




 simpl in *. unfold prep_selected_block in *; simpl in *. rewrite <- Heqo2. rewrite <- Heqo3. intros. inversion H4; subst. rewrite H. unfold sound_env in sstack_env.
 unfold prep_selected_block in sstack_env. simpl in sstack_env.


 rewrite <- Heqo2 in sstack_env. rewrite <- Heqo3 in sstack_env.

 apply sstack_env  in H4. unfold add_env. simpl in *. unfold beq_local_id.

 unfold decide. destruct ( eq_dec_local_id id id); simpl in *; eauto. inversion H2. inversion H2.






 +

 destruct s; simpl in *. inversion H1. destruct f; inversion H1; simpl in *; subst.



inversion sstack; subst. 








 destruct H4. destruct H2. destruct H2. destruct H2. destruct H3.
 eapply fetch_and_incr_implies_cmd in H3; eauto. unfold prog_to_cmd, incr_pc, prep_selected_block in *. simpl in *. remember ( find_function m fn0 ). destruct o0; inversion H3. remember (find_block (blks (df_instrs d0)) bk0). destruct o0; inversion H3. rewrite H3 in H4.

specialize (H fn0 bk0 b0). unfold get_block in *; simpl in *. rewrite <- Heqo2 in H. rewrite <- Heqo3 in H. assert (Some b0 = Some b0) by auto. apply H in H5. clear H; rename H5 into H.


 eapply value_analysis_equals_previous_val_analysis in H; eauto.





 intros. inversion H5; subst.



 rewrite H. unfold transfer; simpl.

 unfold sound_env in *. simpl in *. unfold prep_selected_block in *.
 simpl in *. rewrite <- Heqo2 in H2. rewrite <- Heqo3 in H2. apply H2 in H5.  eauto.





 (*ret br*)


 destruct v. simpl in *. destruct ( eval_op e (Some t) v); simpl in *. inversion H1. destruct v0; simpl in *; inversion H1. destruct ( StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; eauto. eauto. inversion H1. simpl in *; eauto; inversion H1. simpl in *; inversion H1. Qed.







  Lemma jump_preserves_sound_state: forall m st st1, 
       wf_program m  -> sound_state m st  -> stepD m st = Jump st1 -> sound_state m st1.
Proof. intros. constructor.  eapply  jump_preserves_sound_stack in H; eauto. eapply jump_preserves_sound_env; eauto. Qed.
*)