Require Import Vellvm.optimisations.Kildall.lattice.
Require Import Vellvm.optimisations.maps.


Require Import ZArith List String Omega.
Require Import Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.optimisations.Kildall.kildall.
Require Import Vellvm.optimisations.Kildall.static_eval.

Require Import Vellvm.DecidableEquality.
Require Import Vellvm.DecidableProp.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat.



Print NODE_SET.
Module NodeSetForward <: NODE_SET.
  Definition t := list pc.
  Definition empty := nil : list pc.
  Definition add (n: pc) (s: t) : t := n :: s.


  
  
  Definition pick (s: t) :=
    match s with
    | nil => None
    | hd :: tl => Some (hd, tl)
    end.

  
  Definition code_to_pc (fn:function_id) (bk:block_id) (i:instr_id*instr) : pc := mk_pc fn bk (fst i).
  Definition map_code fn bk (c:code) : seq pc := map (code_to_pc fn bk) c.
  Definition block_to_pc fn (b:block) := map_code fn (blk_id b) (blk_code b) ++ (cons (mk_pc fn (blk_id b) (blk_term_id b)) nil).
Print block_to_cmd. Print block.

Lemma all_node_block : forall code fn n instr,  block_to_cmd code n = Some instr -> In (mk_pc fn (blk_id code) n) (block_to_pc fn code).
Proof. intros. destruct code. simpl in *. unfold block_to_pc. simpl in *. unfold block_to_cmd in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *.
       destruct ( decide (i = n)). simpl in *. simpl in *. subst. induction blk_code. simpl in *. eauto. simpl in *. right. eauto. induction blk_code. simpl in *. inversion H. simpl in *. simpl in *. destruct a. simpl in *. destruct (decide (n = i0)). simpl in *. unfold code_to_pc. simpl in *. subst. left. eauto. right. eapply IHblk_code; eauto. Qed.





Definition cfg_to_pc fn (c:cfg) := flatten (map (block_to_pc fn) (blks c)).
Definition def_cfg_to_pc (d:definition cfg) := cfg_to_pc (dc_name (df_prototype d)) (df_instrs d).






  Definition mcfg_to_pc (m:mcfg) := flatten (map def_cfg_to_pc (m_definitions m)).  


Definition all_nodes (code: mcfg) := mcfg_to_pc code.
  Definition In (p:pc) (l:t) := In p l.
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

Lemma all_nodes_spec:
    forall code n instr,
    fetch code n = Some instr -> In n (all_nodes code).
Proof.
  unfold fetch. unfold all_nodes. unfold mcfg_to_pc. simpl in *. unfold def_cfg_to_pc. simpl in *. unfold cfg_to_pc. simpl in *. unfold block_to_pc. simpl in *.
simpl in *. destruct code. induction m_definitions. simpl in *. intros. destruct n. inversion H. 


Admitted.




End NodeSetForward.

Module DS := Dataflow_Solver(VA)(NodeSetForward).


Definition block_entry_pc (m:mcfg) (f:function_id) (b:block_id) :=
  match find_block_entry m f b with
  | Some (BlockEntry a p) => cons p nil
                   | None => nil
  end.


Definition next_term (m:mcfg) (f:function_id) (t:terminator) :=
  match t with
  | TERM_Ret _ => nil
  | TERM_Ret_void => nil
  | TERM_Br _ br1 br2 => (block_entry_pc m f br1) ++ (block_entry_pc m f br2) 
  | TERM_Br_1 br1 => (block_entry_pc m f br1) 
  | _ => nil
  end.



Definition get_successors (m:mcfg) (p:pc) :=
  match fetch m p with
  | Some (Term a) => next_term m (fn p) a
  | Some (CFG.Step (INSTR_Call (_, ID_Global fid) args)) => match incr_pc m p, find_function_entry m fid  with
                         | None, None => nil
                         | Some a, Some (FunctionEntry _ b) => cons a (cons b nil)
                         | Some a, _ => cons a nil
                         | None, Some (FunctionEntry _ a) => cons a nil
                                                
                         end
  | Some (CFG.Step a) => match incr_pc m p with
                         | None => nil
                         | Some a => cons a nil
                         end
  | None => nil 
  end.




Print instr. Print Expr. Print aval.

Print eval_aenv_expr.


Definition transfer' (m:mcfg) (p:pc) (a:aenv) : VA.t :=
  match fetch m p with
  | Some (Term (TERM_Br _ _ _)) => VA.State (AE.Top_except nil)
  | Some (Term (TERM_Br_1 _)) => VA.State (AE.Top_except nil)
  | Some (CFG.Step (INSTR_Op (SV o))) => match (pt p) with
                                         | IId id => VA.State (AE.set id (eval_aenv_expr a o) a)
                                         | _ => VA.State a
                                         end
  





  | Some (CFG.Step (INSTR_Call _ _)) => VA.State (AE.Top_except nil)
  | Some _ => match (pt p) with
              | IId id => VA.State (AE.set id (vtop) a)

              | _ => VA.State a
              end
                
  | None => VA.State a
  end.

Definition transfer (m:mcfg) (p:pc) (v:VA.t)  : VA.t :=
  match v with
  | VA.Bot => VA.Bot
  | VA.State ae => match transfer' m p ae with
                   | VA.Bot => VA.Bot
                   | VA.State ae' => VA.State ae'
                   end
                     
  end.


Definition find_func (m:mcfg) :=
  match find_function_entry m (Name "main") with
   | Some (FunctionEntry _ p) => Some p
   | None => None                
  end.


Definition analyse (m:mcfg) :=
  match find_func m with
  | Some start_pc => match (DS.fixpoint m fetch get_successors transfer start_pc (VA.State (AE.Bot))) with
                     | Some res => res
                     | None => PCMap.init (VA.State (AE.top))
                     end
                       
  | None =>  PCMap.init (VA.State (AE.top))
  end.


(*
Definition lookup_env_aenv (e:env) (id:raw_id) : aval :=
  match lookup_env e id with
  | None => vbot
  | Some a => avalue a
  end.



(*env - aenv*)
Inductive vmatch : aval -> aval -> Prop :=
| vtop_match : forall dval, vmatch dval vtop
| vval_match : forall dval dval1, dval = dval1 -> vmatch (avalue dval1) (avalue dval).




Definition ematch (e:env) (a:aenv) := forall p, vmatch (lookup_env_aenv e p) (AE.get p a).

Inductive vge: aval -> aval -> Prop :=
| vge_bot : forall v, vge v vbot
| vge_val : forall v v1, v = v1 -> vge (avalue v) (avalue v1)
| vge_top : forall v, vge vtop v.





Lemma vmatch_ge:
  forall v x y, vge x y -> vmatch v y -> vmatch v x.
Proof.
  induction 1; intros V. inversion V. subst. eauto. constructor. Qed.



Lemma ematch_ge:
  forall  e ae1 ae2,
  ematch e ae1 -> AE.ge ae2 ae1 -> ematch e ae2.
Proof. intros. unfold ematch in *. intros. unfold AE.ge in *. specialize (H p).
       specialize (H0 p). unfold AVal.ge in *. simpl in *. destruct ((lookup_env_aenv e p)); eauto. eapply vmatch_ge; eauto. destruct ( AE.get p ae2); simpl in *; eauto. destruct ( AE.get p ae1); eauto. apply vge_bot. inversion H0. inversion H0. destruct (AE.get p ae1). constructor. constructor. destruct (decide (n = n0)). subst; eauto. simpl in *. inversion H0. inversion H0.
destruct (AE.get p ae1). constructor. constructor. constructor.
destruct (AE.get p ae1), ( AE.get p ae2); eauto; inversion H; inversion H0; subst. constructor.
destruct (decide (n1 = n)). subst. eauto. simpl in *. inversion H5. constructor. 
destruct ( AE.get p ae2), (AE.get p ae1); try constructor; eauto; try inversion H0; inversion H. Qed.



Lemma vmatch_false : forall e p, vmatch (lookup_env_aenv e p) AVal.bot -> False.
Proof. intros. inversion H. Qed.


Lemma ematch_update:
  forall e ae v av r,
  ematch e ae -> vmatch (avalue v) av -> ematch (add_env r v e) (AE.set r av ae).
Proof.
  intros. red. intros. remember ( (lookup_env_aenv (add_env r v e) p)).
 assert  (ae <> AE.Bot -> ~ (AVal.beq av AVal.bot) = true ->
vmatch a ((if loc_id_eq p r then av else AE.get p ae)) -> vmatch a (AE.get p (AE.set r av ae))).
 intros. unfold is_left in. simpl in *. unfold AE.get, AE.set in *. unfold is_left in *. simpl in *. destruct ae. congruence. destruct ( AVal.beq av AVal.bot). contradiction H2; eauto.
 destruct (AVal.beq av AVal.top) eqn:?. simpl in *.
 rewrite lidTree.grspec. unfold lidTree.elt_eq. 
destruct ( loc_id_eq p r). constructor. eauto.
rewrite lidTree.gsspec. unfold lidTree.elt_eq. simpl in *.
destruct ( loc_id_eq p r). eauto. eauto.
apply H1. unfold not. intros. subst. unfold ematch in *.
simpl in *. specialize (H r). inversion H. simpl in *.
unfold not. intros.  apply AVal.beq_eq in H2.
subst. simpl in *. inversion H0.
unfold is_left. simpl in *. subst.
unfold lookup_env_aenv, add_env, lookup_env in *; simpl in *.
destruct (AstLib.RawID.eq_dec p r), (loc_id_eq p r); subst; eauto; try contradiction n; eauto.
Qed.


*)
 
Inductive sound_stack : mcfg -> stack -> Prop :=
| nil_stack : forall p, sound_stack p nil
| kret_stack : forall id m p e k ae
(AN: (analyse m)!!(mk_pc (fn p) (bk p) (IId id)) = VA.State ae)
(EM: ematch e ae)  (stk:sound_stack m k),
    (exists tptr tval, fetch m (mk_pc (fn p) (bk p) (IId id)) = Some (CFG.Step (INSTR_Call tptr tval)) /\incr_pc m (mk_pc (fn p) (bk p) (IId id)) = Some p) -> sound_stack m ((KRet e id p)::k)
| kret_void_stack : forall m p e k ae (stk:sound_stack m k),
    (exists tptr tval id, (analyse m)!!(mk_pc (fn p) (bk p) (IVoid id)) = VA.State ae /\ ematch e ae /\ fetch m (mk_pc (fn p) (bk p) (IVoid id)) = Some (CFG.Step (INSTR_Call tptr tval)) /\
                          incr_pc m (mk_pc (fn p) (bk p) (IVoid id)) = Some p)  -> sound_stack m ((KRet_void e p)::k).


Inductive sound_state : mcfg -> state -> Prop :=
| sound_state_intro :
    forall m st  ae
           (sstack: sound_stack m (stack_of st))
(AN: (analyse m)!!(pc_of st) = VA.State ae)
(EM: ematch (env_of st) ae) ,
      sound_state m st.




Lemma analyse_successor:
  forall m n ae ae' s instr,
    (analyse m)!!n = VA.State ae ->
    fetch m n = Some instr ->
    In s (get_successors m n) ->
    transfer' m n ae = ae' ->
    VA.ge (analyse m)!!s (transfer m n (VA.State ae)).
Proof. unfold analyse; intros. unfold find_func in *. simpl in *.
       unfold find_function_entry in *. simpl in *.
       destruct ( find_function m (Name "main")) eqn:?.
       destruct ( find_block (blks (df_instrs d)) (init (df_instrs d))) eqn:?.
       remember ( (VA.State AE.Bot)) as entry.
       destruct ( DS.fixpoint m fetch get_successors transfer  {| fn := Name "main"; bk := init (df_instrs d); pt := blk_entry_id b |} entry) eqn:?.
       assert (A: VA.ge t !! s (transfer m n (t !!n))).
       eapply DS.fixpoint_solution; eauto with coqlib. intros.
       unfold transfer. apply DS.L.eq_refl. rewrite H in A.
       unfold transfer in A. unfold transfer in H2. rewrite H2 in A.
       rewrite H2. unfold transfer.  eauto. simpl in *.
       destruct (transfer' m n ae). eauto. apply AE.ge_top. rewrite H2.
       simpl in *. destruct ae'.  eauto. eapply AE.ge_top. simpl in *.
       rewrite H2. destruct ae'. simpl in *. eauto. eapply AE.ge_top. Qed.



Lemma analyse_succ:
  forall e f n ae instr s ae',
  (analyse f)!!n = VA.State ae ->
  fetch f n = Some instr ->
  In s (get_successors f n) ->
  transfer' f n ae = VA.State ae' ->
  ematch e ae' ->
  exists ae'',
     (analyse f)!!s = VA.State ae''
  /\ ematch e ae''.
Proof. intros. generalize H; intros. eapply analyse_successor in H4; eauto.
       unfold transfer in H4. simpl in *. rewrite H2 in H4.
       destruct ((analyse f) !! s); try tauto. exists ae0.
       split. auto. eapply ematch_ge; eauto. Qed. 


Lemma sound_succ_state:
  forall pc ae instr f s pc' e' ae',
    (analyse f)!!pc = VA.State ae  ->
    fetch f pc = Some instr -> In pc' (get_successors f pc) ->
    transfer' f pc ae = VA.State ae' ->
ematch e' ae' -> sound_stack f s ->
  sound_state f (pc', e', s).
Proof.
  intros. generalize H. intros. eapply analyse_succ in H5; eauto.
  generalize H5. intros (aea' & aef). destruct aef.
  simpl in *. inversion H5. destruct H8. simpl in *. econstructor; eauto. Qed.


Lemma unfold_fetch : forall m fn0 d bk0 b id  pt0 instr
  (Heqo : find_function m fn0 = Some d)
  (Heqo0 : find_block (blks (df_instrs d)) bk0 = Some b)
  (Heqo1 : block_to_cmd b id = Some (instr, pt0)),
  fetch m {| fn := fn0; bk := bk0; pt := id|} = Some instr.
Proof. intros. unfold fetch. simpl in *. rewrite Heqo. rewrite Heqo0. rewrite Heqo1. eauto.
Qed.


Hint Resolve unfold_fetch.



Lemma unfold_instr : forall m fn0 d b id instruction pt0 bk0 (Heqo : find_function m fn0 = Some d)
 ( Heqo0 : find_block (blks (df_instrs d)) bk0 = Some b)
  (Heqo1 : block_to_cmd b id = Some (CFG.Step instruction, Some pt0)),
  In {| fn := fn0; bk := bk0; pt := pt0 |}
    (get_successors m {| fn := fn0; bk := bk0; pt := id |}).
Proof. intros. unfold get_successors. simpl in *. rewrite Heqo. rewrite Heqo0.
       rewrite Heqo1. destruct instruction; simpl in *; eauto. destruct fn.
       destruct i. simpl in *. destruct ( find_function_entry m id0) eqn:?.
       destruct f. simpl in *. eauto. simpl in *. eauto. simpl in *.
       eauto. Qed.
Hint Resolve unfold_instr.


Lemma transfer_add :
forall m fn0 d bk0 b ae op pt0 id, 
find_function m fn0 = Some d ->
find_block (blks (df_instrs d)) bk0 = Some b ->
block_to_cmd b (IVoid id) = Some (CFG.Step (INSTR_Op op), Some pt0) ->
transfer' m {| fn := fn0; bk := bk0; pt := IVoid id |} ae = VA.State ae.
Proof. intros. unfold transfer'.
       simpl in *. rewrite H. rewrite H0.
       rewrite H1. destruct op; simpl in *. destruct e; eauto. Qed.
Hint Resolve transfer_add.





Lemma block_implies_successor : forall m fn0 d0 bk0 b0 id x x0 pt0,
find_function m fn0 = Some d0 -> find_block (blks (df_instrs d0)) bk0 = Some b0 -> 
block_to_cmd b0 id =
Some (CFG.Step (INSTR_Call x x0), Some pt0) -> In  (mk_pc fn0 bk0 pt0) (get_successors m (mk_pc fn0 bk0 id)).
Proof. intros. unfold get_successors. simpl in *.
       rewrite H. rewrite H0. rewrite H1. destruct x.
       destruct i. simpl in *. unfold find_function_entry in *.
       simpl in *. destruct (find_function m id0) eqn:?.
       destruct ( find_block (blks (df_instrs d)) (init (df_instrs d))) eqn:?.
       simpl in *. eauto. simpl in *. eauto. simpl in *. eauto.
       simpl in *. eauto.  Qed.
     Hint Resolve block_implies_successor.

               