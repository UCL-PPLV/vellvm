Require Import Vellvm.optimisations.Kildall.lattice.
Require Import Vellvm.optimisations.maps.


Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG Vellvm.AstLib.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.vellvm_tactics.

Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.optimisations.Kildall.kildall.
Require Import Vellvm.optimisations.Kildall.static_eval.
Require Import Vellvm.optimisations.local_cfg.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Vellvm.DecidableProp.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat.

Set Implicit Arguments.

Module NodeSetForward <: NODE_SET.
  Definition t := list local_pc.
  Definition empty := nil : list local_pc.
  Definition add (n: local_pc) (s: t) : t := n :: s.


  
  
  Definition pick (s: t) :=
    match s with
    | nil => None
    | hd :: tl => Some (hd, tl)
    end.

  
  Definition code_to_pc  (bk:block_id) (i:instr_id*instr) : local_pc := mk_localpc bk (fst i).
  Definition map_code bk (c:code) : seq local_pc := map (code_to_pc bk) c.
  Definition block_to_pc (b:block) := map_code (blk_id b) (blk_code b) ++ (cons (mk_localpc (blk_id b) (blk_term_id b)) nil).
  Definition cfg_to_pc  (c:cfg) := flatten (map (block_to_pc) (blks c)).

  
Lemma all_node_block : forall code n instr,  block_to_cmd code n = Some instr -> In (mk_localpc (blk_id code) n) (block_to_pc code).
Proof. intros. destruct code. simpl in *. unfold block_to_pc. simpl in *. unfold block_to_cmd in *.
       simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *.
       destruct ( decide (i = n)). subst. induction blk_code.
       simpl in *. eauto. simpl in *. right. eauto. induction blk_code. simpl in *.
       inversion H. simpl in *. simpl in *. destruct a.
       destruct (decide (n = i0)). unfold code_to_pc. simpl in *. subst. left. eauto.
       right. eapply IHblk_code; eauto. Qed.




Definition all_nodes (code: cfg) : list local_pc := cfg_to_pc code.





  Definition In (p:local_pc) (l:t) := In p l.
  Lemma empty_spec:
    forall n, ~In n empty.
Proof.
intros. simpl in *. eauto. Qed.
  Lemma add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
Proof.
  intros. simpl in *.  split; intros. eauto. eauto. Qed.

  Lemma pick_none:
    forall s n, pick s = None -> ~In n s.
Proof.
  intros. unfold not. intros. induction s. simpl in *. eauto. simpl in *. inversion H. Qed.

  
  Lemma pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.  
Proof.
  intros until s'. induction s. simpl in *. intros. split. inversion H. inversion H. simpl in *. intros. inversion H. subst. split. intros. eauto. simpl in *. intros. eauto. Qed.

Lemma In_helper'' : forall A (B:seq local_pc) C, In A B ->  In A (B ++ C).
Proof. intros. induction B. simpl in *. inversion H. simpl in *. inversion H. subst; eauto.
       right. eauto. Qed.
Hint Resolve In_helper''.

Lemma In_helper' : forall A (B:seq local_pc) (C: seq local_pc), In A (B ++ C) <-> In A B \/ In A C.
Proof. intros; split; intros.
       +induction B. simpl in *. right. eauto. simpl in *. inversion H. subst. left. left. eauto.
       eapply IHB in H0. inversion H0. left. right. eauto. right. eauto.
       +inversion H. eapply In_helper''. eauto. induction B. simpl in *. eauto. simpl in *.  right. eapply IHB. right. eauto. Qed.
        
Lemma all_nodes_spec:
    forall code n instr,
    local_cfg.fetch code n = Some instr -> In n (all_nodes code).
Proof. intros. destruct code. simpl in *. unfold fetch in *. unfold cfg_to_cmd in *.
       simpl in *. destruct n. simpl in *. induction blks. simpl in *. inversion H.

(* block_to_cmd code n = Some instr -> In (mk_localpc (blk_id code) n) (block_to_pc code).*)
simpl in *. destruct (decide (blk_id a = lbk)). subst. simpl in *.
remember (block_to_cmd a lpt). symmetry in Heqo. destruct o.
eapply all_node_block in Heqo. simpl in *. unfold all_nodes. unfold cfg_to_pc. simpl in *.
eapply In_helper'. left. eauto. inversion H.



unfold all_nodes in *. unfold cfg_to_pc in *. simpl in *.
apply In_helper'. right. eapply IHblks. destruct blks; simpl in *; eauto. Qed.


End NodeSetForward.

Module DS := Dataflow_Solver(VA)(NodeSetForward).





Fixpoint add_multiple_aenv (a:aenv) (l:seq (local_id)) :=
  match l with
  | nil => a
  | hd :: tl => AE.set hd vtop (add_multiple_aenv a tl)
  end. 


       
Lemma add_multiple_correct : forall l a e r, compare_length l r -> ematch e a ->  ematch ((combine l r) ++ e) (add_multiple_aenv a l) .
Proof.  induction l. simpl in *. intros. eauto.
        intros. simpl in *. destruct r. inversion H. simpl in *.
eapply ematch_update; eauto. constructor. Qed.


Definition transfer' (m:cfg) (p:local_pc) (a:aenv) : VA.t :=
  match local_cfg.fetch m p with
  | Some (Term (TERM_Br _ _ _)) => VA.State (AE.Top_except nil)
  | Some (Term (TERM_Br_1 br)) => match find_block (blks m) br with
                                  | None => VA.State (AE.Top_except nil)
                                  | Some bl => (VA.State(add_multiple_aenv a (map fst (blk_phis bl))))
                                  end
                                    
  | Some (CFG.Step (INSTR_Op (SV o))) => match (lpt p) with
                                         | IId id => VA.State (AE.set id (eval_aenv_expr a o) a)
                                         | _ => VA.State a
                                         end
    | Some _ => match (lpt p) with
              | IId id => VA.State (AE.set id (vtop) a)

              | _ => VA.State a
              end
                
  | None => VA.State a
  end.

Definition transfer (m:cfg) (p:local_pc) (v:VA.t)  : VA.t :=
  match v with
  | VA.Bot => VA.Bot
  | VA.State ae => match transfer' m p ae with
                   | VA.Bot => VA.Bot
                   | VA.State ae' => VA.State ae'
                   end
                     
  end.



Definition analyse (d:definition cfg) :   PCMap.t DS.L.t :=
  let c := df_instrs d in
  match find_block (blks c) (init c) with
  | None =>  PCMap.init (VA.State (AE.top))
  | Some block => match (DS.fixpoint c local_cfg.fetch successor_local_pc transfer (mk_localpc (init c) (blk_entry_id block))
                                     (VA.State(add_multiple_aenv (AE.top) (df_args d)))) with
                     | Some res => res
                     | None => PCMap.init (VA.State (AE.top))
                  end
  end.

       
Definition analyse_cfg (d:definition cfg) := ((dc_name (df_prototype d)), (analyse d)).

Definition analyse_program (m:mcfg) := map analyse_cfg (m_definitions m).


Fixpoint fetch_analysis (p:pc) (s: seq (function_id * PCMap.t DS.L.t)) :=
  match s with
  | nil => None
  | (key, map) :: tl => if eq_dec_function_id (fn p) key then Some (map!!(mk_localpc (bk p) (pt p))) else fetch_analysis p tl
  end.


Inductive sound_stack : mcfg -> stack -> Prop :=
| nil_stack : forall p, sound_stack p nil
| kret_stack : forall id m p e k ae
                      (AN: fetch_analysis (mk_pc (fn p) (bk p) (IId id)) (analyse_program m) = Some (VA.State ae))
                      
(EM: ematch e ae)  (stk:sound_stack m k),
    (exists tptr tval, CFG.fetch m (mk_pc (fn p) (bk p) (IId id)) = Some (CFG.Step (INSTR_Call tptr tval)) /\
                       incr_pc m (mk_pc (fn p) (bk p) (IId id)) = Some p) -> sound_stack m ((KRet e id p)::k)

                                                                                           
| kret_void_stack : forall m p e k ae (stk:sound_stack m k),
    (exists tptr tval id,
        (fetch_analysis (mk_pc (fn p) (bk p) (IVoid id)) (analyse_program m) = Some (VA.State ae)) /\
        ematch e ae /\
        CFG.fetch m (mk_pc (fn p) (bk p) (IVoid id)) = Some (CFG.Step (INSTR_Call tptr tval)) /\
        incr_pc m (mk_pc (fn p) (bk p) (IVoid id)) = Some p)  -> sound_stack m ((KRet_void e p)::k).




Inductive sound_state : mcfg -> state -> Prop :=
| sound_state_base :
    forall m st ae
           (sstack: sound_stack m (stack_of st))
 (AN: fetch_analysis (pc_of st) (analyse_program m) = Some (VA.State ae))
(EM: ematch (env_of st) ae),  sound_state m st.


Lemma analyse_entrypoint : forall m fn0 d0 b0 l, compare_length (df_args d0) l ->
  find_function m fn0 = Some d0 -> find_block (blks (df_instrs d0)) (init (df_instrs d0)) = Some b0 ->
  exists ae', fetch_analysis {| fn := fn0; bk := init (df_instrs d0); pt := blk_entry_id b0 |} (analyse_program m) = Some (VA.State ae') /\ ematch  (combine (df_args d0) l) ae'.
Proof. intros. destruct m. unfold find_function in *. simpl in *. induction m_definitions.
       simpl in *. inversion H0. simpl in *. unfold is_left in *. simpl in *.
       unfold find_defn in *. unfold ident_of in *. unfold ident_of_definition in *.
       unfold ident_of in *. unfold ident_of_declaration in *. simpl in *. destruct a. simpl in *. 
       destruct (decide (ID_Global (dc_name df_prototype) = ID_Global fn0)). inversion e; subst.
       inversion H0; subst. simpl in *. destruct ( eq_dec_function_id (dc_name df_prototype) (dc_name df_prototype)).
       simpl in *. unfold analyse. simpl in *. rewrite H1. simpl.


destruct ( DS.fixpoint df_instrs fetch successor_local_pc transfer
          {| lbk := init df_instrs; lpt := blk_entry_id b0 |}
          (VA.State (add_multiple_aenv (AE.top) df_args))) eqn:?.
assert (A: VA.ge t!!({| lbk := init df_instrs; lpt := blk_entry_id b0 |})
                 (VA.State (add_multiple_aenv (AE.top) df_args))) by (eapply DS.fixpoint_entry; eauto). 

destruct ( t !! {| lbk := init df_instrs; lpt := blk_entry_id b0 |}); simpl in A. inversion A.
simpl. exists ae. split; eauto. eapply ematch_ge; try eapply A.

assert ((combine df_args l) = (combine df_args l) ++ nil). rewrite cats0. eauto. rewrite H2. eapply add_multiple_correct; eauto. simpl. unfold ematch. unfold lookup_env_aenv. simpl in *. intros. constructor.
exists (AE.top).  rewrite PCMap.gi. split. eauto. simpl in *. constructor.
contradiction n; eauto. 
destruct ( eq_dec_function_id fn0 (dc_name df_prototype)). subst. contradiction n; eauto. eauto. Qed.






Lemma analyse_successor:
  forall m n ae ae' s instr,
    (analyse m)!!n = VA.State ae ->
    fetch (df_instrs m) n = Some instr ->
    In s ( successor_local_pc (df_instrs m) n) ->
    transfer' (df_instrs m) n ae = ae' ->
    VA.ge (analyse m)!!s (transfer (df_instrs m) n (VA.State ae)).
Proof. unfold analyse; intros.
       destruct (find_block (blks (df_instrs m)) (init (df_instrs m))) eqn:?.
       remember (VA.State AE.Bot) as entry.
       
       destruct ( DS.fixpoint (df_instrs m) fetch successor_local_pc transfer
        {| lbk := init (df_instrs m); lpt := blk_entry_id b |}
        (VA.State (add_multiple_aenv AE.top (df_args m)))) eqn:?.
        assert (A: VA.ge t !! s (transfer (df_instrs m) n (t !!n))).
        eapply DS.fixpoint_solution; eauto with coqlib. intros. unfold transfer. simpl. eauto.
        rewrite H in A. unfold transfer in A. simpl in *. rewrite H2 in A. rewrite H2.
        eauto. simpl in *. destruct ( transfer' (df_instrs m) n ae). eauto. eapply AE.ge_top.
        unfold transfer. simpl in *. rewrite H2. simpl in *. destruct ae'. eauto. eapply AE.ge_top. Qed.

Lemma analyse_succ:
  forall e f n ae instr s ae',
  (analyse f)!!n = VA.State ae ->
  fetch (df_instrs f) n = Some instr ->
  In s ( successor_local_pc (df_instrs f) n) ->
  transfer' (df_instrs f) n ae = VA.State ae' ->
  ematch e ae' ->
  exists ae'',
     (analyse f)!!s = VA.State ae''
  /\ ematch e ae''.
Proof. intros. generalize H; intros. eapply analyse_successor in H4; eauto.
       unfold transfer in H4. simpl in *. rewrite H2 in H4.
       destruct ((analyse f) !! s); try tauto. exists ae0.
       split. auto. eapply ematch_ge; eauto. Qed. 




Definition find_block_pc (m:mcfg) (fn:function_id) (bk:block_id) :=
  match CFG.find_block_entry m fn bk with
  | None => nil
  | Some (BlockEntry _ pc) => cons pc nil
  end.

                                   
Definition successor_pc (m:mcfg) (p:pc) :=
  match CFG.fetch m p with
  | None => nil
  | Some (Term t) => match t with
                     | TERM_Br_1 br => find_block_pc m (fn p) br
                     | TERM_Br _ br1 br2 => (find_block_pc m (fn p) br1) ++ (find_block_pc m (fn p) br2)
                     | _ => nil
                     end
                         
  | Some (CFG.Step ins) => match incr_pc m p with
                                              | Some res => cons res nil
                                              | None => nil
                                              end
                     
  end.


Lemma find_block_pc_equiv : forall d bk b, find_block (blks (df_instrs d)) bk = Some b -> (blk_id b) = bk.
Proof. intros. destruct d. simpl in *. destruct df_instrs. simpl in *. induction blks. simpl in *. inversion H.
simpl in *.  destruct ( decide (blk_id a = bk)). inversion H. subst. simpl in *. eauto. simpl in *. eapply IHblks.
destruct blks. simpl in *. eauto. simpl in *. eapply H. Qed. 



       
Lemma successor_pc_to_local : forall pc pc' m d, In pc' (successor_pc m pc) -> find_function m (fn pc) = Some d -> In (pc_to_local_pc pc') (successor_local_pc (df_instrs d) (pc_to_local_pc pc)).
Proof. intros. unfold successor_pc in *. simpl in *. unfold successor_local_pc in *.
       unfold CFG.fetch in *. simpl in *. destruct pc, pc'. simpl in *.
       unfold pc_to_local_pc in *. simpl in *.
       unfold cfg_to_cmd. simpl in *. destruct (find_function m fn) eqn:?.
       inv H0. clear H0.
       destruct ( find_block (blks (df_instrs d)) bk) eqn:?.
       destruct ( block_to_cmd b pt) eqn:?. simpl in *. destruct p.
       simpl in *. destruct c. simpl in *. destruct o. simpl in *.
       inversion H. inversion H0; subst. left. eauto. inversion H0.
       simpl in *. inversion H. simpl in *. destruct t; simpl in *; try inv H.
       unfold find_block_entry in *. simpl in *. unfold find_block_pc in *.
       simpl in *. unfold CFG.find_block_entry in *. simpl in *.
       rewrite Heqo in H.
       destruct (find_block (blks (df_instrs d)) br1) eqn:?, (find_block (blks (df_instrs d)) br2) eqn:?; simpl in *; unfold blk_entry_pc in *; simpl in *; unfold blk_entry_id in *; simpl in *.
       inversion H. inversion H0; subst; clear H0. simpl. left.
       eapply find_block_pc_equiv in Heqo2. subst.  eauto. inversion H0.
       inversion H1; subst. eapply find_block_pc_equiv in Heqo3. subst.
       eauto. inversion H1. inversion H. inversion H0. subst. simpl in *.
       eapply find_block_pc_equiv in Heqo2. subst. eauto. inversion H0.
       inversion H. inversion H0. subst. eapply  find_block_pc_equiv in Heqo3.
       subst. eauto. inversion H0. inversion H.
       unfold find_block_pc in *. unfold find_block_entry. unfold CFG.find_block_entry in *.
       simpl in *. rewrite Heqo in H. destruct (find_block (blks (df_instrs d)) br) eqn:?.
       simpl in *. inversion H. inversion H0. subst. eapply find_block_pc_equiv in Heqo2.
       subst. eauto. inversion H0. simpl in *. eauto. simpl in *. eauto.
       simpl in *. eauto. simpl in *. inversion H. Qed.






Lemma fetch_local_analysis : forall p m ae d, fetch_analysis p (analyse_program m) = Some (VA.State ae) ->
                                              find_function m (fn p) = Some d ->
                                              ((analyse d) !!(mk_localpc (bk p) (pt p))) = VA.State ae.
Proof. intros. destruct m. simpl in *. unfold analyse_program in *. simpl in *. 
       destruct d. simpl in *. destruct p. simpl in *. destruct df_instrs. simpl in *.
       induction m_definitions. unfold find_function in *. simpl in *. inversion H0.
       simpl in *. unfold find_function in H0. simpl in *. unfold is_left in *. simpl in *. unfold find_defn in H0.
       simpl in *. unfold ident_of in *. simpl in *. unfold ident_of_definition in *. destruct a. simpl in *.
       destruct ( decide (ident_of df_prototype0 = ID_Global fn)). unfold ident_of in *.
       simpl in *. unfold ident_of_declaration in *. simpl in *. inversion e. subst.
       destruct ( eq_dec_function_id (dc_name df_prototype0) (dc_name df_prototype0)). simpl in *.
       inversion e; clear e. clear e0. inversion H; inversion H0; subst. clear H0.
       clear H. eauto. contradiction n; eauto. unfold ident_of in *. simpl in *.
       unfold ident_of_declaration in *. simpl in *. destruct ( eq_dec_function_id fn (dc_name df_prototype0)).
       inversion H; subst. contradiction n; eauto. eapply IHm_definitions in H.
       eapply H. clear  IHm_definitions. clear H. clear n. clear n0. destruct m_definitions.
       simpl in *. eauto. eauto. Qed.


Lemma fetch_to_local_fetch : forall m pc instr d, CFG.fetch m pc = Some instr -> find_function m (fn pc) = Some d -> fetch (df_instrs d) (pc_to_local_pc pc) = Some instr.
Proof. intros. unfold CFG.fetch in *. simpl in *.
       destruct pc. simpl in *. rewrite H0 in H.
       unfold fetch. unfold pc_to_local_pc. simpl in *.
       unfold cfg_to_cmd. simpl in *.
       destruct ( find_block (blks (df_instrs d)) bk) eqn:?; eauto. Qed.

Lemma pc_equiv : forall m pc' fn1 bk1 pt1,  In pc' (successor_pc m {| fn := fn1; bk := bk1; pt := pt1 |}) -> (fn pc') = fn1.
Proof. intros. destruct pc'.  simpl in *. unfold successor_pc in *. simpl in *.
       destruct (find_function m fn1) eqn:?; simpl in *.
       destruct (find_block (blks (df_instrs d)) bk1) eqn:?; simpl in *.
       destruct (block_to_cmd b pt1) eqn:?; simpl in *.
       destruct p. simpl in *. destruct c. simpl in *. destruct o. simpl in *. inversion H.
       inversion H0. subst; eauto. inversion H0. simpl in *. inversion H.
       destruct t; simpl in *; try inversion H. unfold find_block_pc in *.
       unfold CFG.find_block_entry in *. simpl in *. rewrite Heqo in H.
       destruct (find_block (blks (df_instrs d)) br1) eqn:?,
                (find_block (blks (df_instrs d)) br2) eqn:?; simpl in *;
         unfold blk_entry_pc in *; simpl in *; try inversion H; try inversion H0; subst; eauto.
       inversion H1; subst; eauto. inversion H1. unfold find_block_pc in *.
       unfold CFG.find_block_entry in *; simpl in *. rewrite Heqo in H.
       destruct (find_block (blks (df_instrs d)) br) eqn:?; simpl in *. inversion H; eauto.
       inversion H0; subst; eauto. inversion H0. inversion H. inversion H. inversion H. inversion H. Qed.






Lemma fetch_analysis_equiv : forall m fn d bk0 pt0 aef,
find_function m fn = Some d ->
 (analyse d) !! {| lbk := bk0; lpt := pt0 |} = VA.State aef ->
fetch_analysis {| fn := fn; bk := bk0; pt := pt0 |} (analyse_program m) = Some (VA.State aef).
Proof. intros. destruct m. simpl in *. unfold find_function in *.
       simpl in *. unfold find_defn in *. simpl in *. unfold ident_of in *.
       simpl in *. unfold ident_of_definition in *. simpl in *.
       induction m_definitions. simpl in *. inversion H.
       simpl in *. unfold is_left in *. unfold ident_of in *.
       unfold ident_of_declaration in *.
       destruct a. simpl in *. destruct (decide (ID_Global (dc_name df_prototype) = ID_Global fn)).
       simpl in *. inversion H. subst. clear H. inversion e. subst. simpl in *.
       destruct ( eq_dec_function_id (dc_name df_prototype) (dc_name df_prototype)). simpl in *.
       rewrite H0. eauto. contradiction n; eauto. destruct ( eq_dec_function_id fn (dc_name df_prototype)).
       subst. contradiction n; eauto. eapply IHm_definitions in H.
       destruct m_definitions. simpl in *. eauto. simpl in *. eauto. Qed.







       
Lemma sound_succ_state: forall m d pc ae instr s pc' e' ae',
fetch_analysis pc (analyse_program m) = Some (VA.State ae) ->
CFG.fetch m pc = Some instr -> 
In pc' (successor_pc m pc) ->
find_function m (fn pc) = Some d ->
transfer' (df_instrs d) (pc_to_local_pc pc) ae = VA.State ae' ->
ematch e' ae' -> sound_stack m s ->
sound_state m (pc', e', s)
.
Proof. intros. dupl H1. eapply successor_pc_to_local in H6; eauto. 
dupl H.
eapply fetch_local_analysis in H; eauto.
dupl H0. eapply fetch_to_local_fetch in H8; eauto.
unfold pc_to_local_pc in *. simpl in *. eapply analyse_succ in H; eauto.
generalize H. intros (aef & aes'). destruct aes'. simpl in *.
destruct pc. simpl in *. dupl H1. eapply pc_equiv in H11. destruct pc'. simpl in *. subst.
econstructor; simpl; eauto. eapply fetch_analysis_equiv; eauto. Qed.




(*Helper functions for proving preservation*)

Require Import Vellvm.optimisations.SSA_semantics.




Definition combine_phis (b:list (local_id * phi)) (e:env) (v:list value) := 
  combine (map fst b) v ++ e.



Definition jump_monad e phis b_entry :=  monad_fold_right
            (fun (e0 : env) '(iid, Phi t1 ls) =>
             match assoc RawID.eq_dec b_entry ls with
             | Some op =>
                 match eval_op e (Some t1) op with
                 | inl x => inl x
                 | inr a => inr (add_env iid a e0)
                 end
             | None =>
                 failwith
                   ("jump: block " ++ string_of b_entry ++ " not found in " ++ string_of iid)
             end) phis e.


Print jump_monad.



Lemma jump_monad3 : forall phis e b_entry l, jump_monad e phis b_entry = inr l -> exists r, jump_monad e phis b_entry = inr ((combine (map fst phis) r) ++ e) /\ compare_length (map fst phis) r.
Proof. induction phis; intros.
       +unfold jump_monad; simpl in *. exists nil. eauto.
       +unfold jump_monad; simpl in *; destruct a; destruct p; simpl in *.
        destr_eq (assoc RawID.eq_dec b_entry args). destr_eq ( eval_op e (Some t) v).
        *unfold jump_monad in H. simpl in *. rewrite Heqo in H. rewrite Heqe0 in H. unfold monad_fold_right in H. remember (  (fix
         monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                          (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                          (a : A) {struct l} : M A :=
           match l with
           | [::] => mret a
           | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
           end)). rewrite <- Heqp in H. clear Heqp. destruct p; inv H.
        *unfold jump_monad in H. simpl in *. remember ( monad_fold_right
          (fun (e0 : env) '(iid, Phi t1 ls) =>
           match assoc RawID.eq_dec b_entry ls with
           | Some op =>
               match eval_op e (Some t1) op with
               | inl x => inl x
               | inr a => inr (add_env iid a e0)
               end
           | None =>
               failwith
                 ("jump: block " ++
                  string_of b_entry ++ " not found in " ++ string_of iid)
           end) phis e). rewrite Heqs. destruct s. inv H. symmetry in Heqs. eapply IHphis in Heqs.
         inversion Heqs; clear Heqs. destruct H0. unfold jump_monad in H0. rewrite H0. unfold add_env. simpl in *. exists (v0 :: x). simpl in *. split; eauto.
        *unfold jump_monad in *. simpl in *. rewrite Heqo in H. unfold monad_fold_right in *. remember ((fix
         monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                          (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                          (a : A) {struct l} : M A :=
           match l with
           | [::] => mret a
           | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
           end)). rewrite <- Heqp in H. destr p; inv H. Qed.
  
Definition jump_v1 CFG fid bid_src bid_tgt e k : err state :=
  match CFG.find_block_entry CFG fid bid_tgt with
  | Some (BlockEntry phis pc_entry) => match jump_monad e phis bid_src with
                                       | inr a => inr (pc_entry, a, k)
                                       | inl b => failwith b
                                       end
  |  None => failwith ("jump: target block " ++ string_of bid_tgt ++ " not found")
  end.

Lemma jump_v1_equiv : jump_v1 = jump.
  Proof. repeat (apply functional_extensionality; intros). unfold jump_v1. unfold jump. simpl in *. 
         destr_eq (CFG.find_block_entry x x0 x2). Qed.
  

  Lemma jump_phis_preserved : forall m f b_entry b_exit block (e:env) s t,
      jump m f b_entry b_exit e s = inr t ->
      get_block m f b_exit = Some block ->
      exists t, jump m f b_entry b_exit e s =  inr ((mk_pc f b_exit (fallthrough (blk_code block) (blk_entry_id block))), combine_phis (blk_phis block) e t, s) /\
                compare_length (map fst (blk_phis block)) t.




   
   Proof. rewrite <- jump_v1_equiv. intros. unfold jump_v1 in *. simpl in *.
          unfold CFG.find_block_entry in *; simpl in *. destr_eq (find_function m f).
          
          destr_eq ( find_block (blks (df_instrs d)) b_exit). simpl in *. unfold get_block in *.
          simpl in *. rewrite Heqo in H0.  rewrite Heqo0 in H0. inversion H0. subst.
          eapply find_block_pc_equiv in Heqo0. subst. clear H0.
          remember ( jump_monad e (blk_phis block) b_entry). destruct s0. inv H. inversion H.
          subst. clear H. symmetry in Heqs0. dupl Heqs0. eapply  jump_monad3 in Heqs0.
          inversion Heqs0; clear Heqs0. destruct H. unfold combine_phis. rewrite H in Heqs1.
          inversion Heqs1. subst. clear Heqs1. unfold blk_entry_pc. simpl in *. exists x. split.
          unfold fallthrough. unfold blk_entry_id. simpl in *. destruct block. simpl in *.
          unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. destruct blk_code.
          simpl in *. eauto. simpl in *. eauto. eauto. inv H. inv H. Qed.

