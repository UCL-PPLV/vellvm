(*Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.static_analysis.

Require Import Vellvm.optimisations.EqNat.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.

Print pc.

Print lookup_env.
Print value.
Print dvalue.
Print env.
Print value_analysis.

Print sound_state.

Print sound_state.
Print aenv. Print areg.
Print instr_id.
Print dvalue.
Print local_id_of_ident.



Definition local_id_of_ident_op (i:ident) a :=
 match i with
| ID_Global _ => None
| ID_Local i0 => lookup_env a i0

 end.

Definition constant_prop_exp (m:mcfg) (fid: function_id) (bid: block_id) (iid: instr_id) (i:instr) : instr :=
  match (prep_selected_block m (mk_pc fid bid iid)) with
  | None => i
  | Some a => match  i with
              | INSTR_Op val => match val with
                                | SV s => match s with
                                          | VALUE_Ident iden => match local_id_of_ident_op iden (value_analysis a iid)  with
                                                              | Some (DV (VALUE_Integer ae)) => INSTR_Op (SV (VALUE_Integer ae))
                                                              | _ => i
                                                              end
                                                                
                                          | _ => i
                                                   
                                          end
                                            
                                end
              | _ => i
              end
                
  end.

Print block.


Definition opt_instr (m:mcfg) (fid:function_id) (bid:block_id) (i:instr_id*instr) := (fst i, constant_prop_exp m fid bid (fst i) (snd i)).


Definition map_code  (l:list (instr_id * instr)) (m:mcfg) (fid: function_id) (bid: block_id) := map (opt_instr m fid bid) l.
Print block.

       
Definition block_op (fid:function_id) (m:mcfg) (b:block) :=
  mk_block (blk_id b) (blk_phis b) (map_code (blk_code b) m fid (blk_id b)) (blk_term b).



Print cfg.



Definition map_blocks (fid:function_id) (m:mcfg) (l:list block) :=
  map (block_op fid m) l.


Print cfg.

Definition cfg_opt (fid:function_id) (m:mcfg) (c:cfg) :=
  mkCFG (init c) (map_blocks fid m (blks c)) (glbl c).


Print definition.

Print definition.
Print declaration.


Definition get_fn (d:definition cfg) : function_id := dc_name (df_prototype d).

Definition def_opt (m:mcfg) (d:definition cfg) := mk_definition cfg (df_prototype d) (df_args d) (cfg_opt (get_fn d) m (df_instrs d)).


Definition list_def_opt (m:mcfg) (l:list (definition cfg)) := map (def_opt m) l.
Print modul.
Definition mcfg_opt (m:mcfg) := mk_modul cfg (m_name m) (m_target m) (m_datalayout m) (m_globals m) (m_declarations m) (list_def_opt m (m_definitions m)).



        
Definition start_func p fid : option (definition cfg) := find_function p fid.
Definition target_func p fid : option (definition cfg) := find_function (mcfg_opt p) fid.

Definition end_func p fid :=
  match find_function p fid with
  | Some a => Some (def_opt p a)
  | None => None
  end.


Lemma first_func : forall p fid, find_function (mcfg_opt p) fid = end_func p fid.
Proof. intros. unfold find_function. simpl in *. destruct p. simpl in *. induction m_definitions.
       +simpl in *. unfold end_func. simpl in *. eauto.
       +simpl in *. unfold end_func. simpl in *. unfold find_function in *. simpl in *. unfold def_opt. simpl in *. unfold find_defn. simpl in *. simpl in *. unfold AstLib.ident_of.
        simpl in *. unfold cfg_opt in *. unfold AstLib.ident_of_definition. simpl in *.
        destruct ( decide (AstLib.ident_of (df_prototype a) = ID_Global fid)). simpl in *.
 Admitted.


Definition start_func1 d bk := find_block (blks (df_instrs d)) bk.
Definition target_func1 d p bk : option block :=  find_block (map_blocks (get_fn d) p (blks (df_instrs d))) bk.
Definition end_func1 bk d p :=
  match find_block (blks (df_instrs d)) bk with
      | Some a => Some (block_op (get_fn d) p a)
      | None => None
end.


Lemma second_func : forall bk d p,  find_block (map_blocks (get_fn d) p (blks (df_instrs d))) bk = end_func1 bk d p.
Proof. Admitted.
Print start_func1.



Definition start_func2 blk_code pt i := find_instr blk_code pt i.
Definition target_func2 blk_code p d blk_id pt i := find_instr (map_code blk_code p (get_fn d) blk_id) pt  i. Print find_instr.
Print cmd.
Definition end_func2 m blk_id blk_code pt i d :=
  match find_instr blk_code pt i with
  | Some (CFG.Step a, b) => Some (CFG.Step ( constant_prop_exp m (get_fn d) blk_id i a), b)
  | res => res
  end.

Lemma third_func : forall blk_code p d blk_id pt i,  find_instr (map_code blk_code p (get_fn d) blk_id) pt  i = end_func2 p blk_id blk_code pt i d.
Proof. Admitted.



Definition start_func3 b pt := block_to_cmd b pt.
Definition target_func3 d b pt p := block_to_cmd
         {|
         blk_id := blk_id b;
         blk_phis := blk_phis b;
         blk_code := map_code (blk_code b) p (get_fn d) (blk_id b);
         blk_term := blk_term b |} pt.


Definition end_func3 b pt p d :=
  match block_to_cmd b pt with
  | None => None
  | Some (Term t, res) => Some (Term t, res)
  | Some (CFG.Step s, res) => Some (CFG.Step (constant_prop_exp p (get_fn d) (blk_id b) pt s), res)       
  end.



Lemma fourth_func : forall b pt d p, block_to_cmd
         {|
         blk_id := blk_id b;
         blk_phis := blk_phis b;
         blk_code := map_code (blk_code b) p (get_fn d) (blk_id b);
         blk_term := blk_term b |} pt = end_func3 b pt p d.
Proof. intros. Admitted.

Lemma jump_equiv : forall p fn bk br1 e s,  (jump p fn bk br1 e s) =  (jump (mcfg_opt p) fn bk br1 e s).
Proof. intros. unfold jump. simpl in *. unfold find_block_entry. simpl in *. rewrite first_func. unfold end_func. simpl in *. destruct (find_function p fn); eauto. rewrite second_func. unfold end_func1. simpl in *. destruct ( find_block (blks (df_instrs d)) br1); eauto. unfold block_to_entry in *. simpl in *. unfold monad_fold_right. simpl in *. remember ( (fix
     monad_fold_right (A B : Type) (M : Type -> Type)
                      (H : Functor M) (H0 : Monad)
                      (f : A -> B -> M A) 
                      (l : seq B) (a : A) {struct l} :
       M A :=
       match l with
       | [::] => mret a
       | x :: xs =>
           monad_fold_right A B M H H0 f xs a
           ≫= (fun y : A => f y x)
       end)). rewrite <- Heqp0. destruct p0; simpl in *; eauto.
 unfold blk_entry_pc in *. simpl in *. unfold blk_entry_id in *. simpl in *. destruct b. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_code. simpl in *. eauto. simpl in *. destruct p1. simpl in *. eauto. Qed.


Lemma term_equiv : forall id bk fn p s e t0,  match t0 with
  | TERM_Ret (t1, op) =>
      do dv <- eval_op e (Some t1) op;
      match s with
      | [::] => Obs (Fin dv)
      | KRet e' id0 p' :: k' => Jump (p', add_env id0 dv e', k')
      | KRet_void _ _ :: _ =>
          t_raise_p {| fn := fn; bk := bk; pt := IId id |}
            "IMPOSSIBLE: Ret op in non-return configuration"
      end
  | TERM_Ret_void =>
      match s with
      | [::] => Obs (Fin (DV (VALUE_Bool true)))
      | KRet _ _ _ :: _ =>
          t_raise_p {| fn := fn; bk := bk; pt := IId id |}
            "IMPOSSIBLE: Ret void in non-return configuration"
      | KRet_void e' p' :: k' => Jump (p', e', k')
      end
  | TERM_Br (t1, op) br1 br2 =>
      do dv <- eval_op e (Some t1) op;
      do br <-
      match dv with
      | DV _ => failwith "Br got non-bool value"
      | DVALUE_CodePointer _ => failwith "Br got non-bool value"
      | DVALUE_Addr _ => failwith "Br got non-bool value"
      | DVALUE_I1 comparison_bit =>
          if StepSemantics.Int1.eq comparison_bit StepSemantics.Int1.one
          then inr br1
          else inr br2
      | DVALUE_I32 _ => failwith "Br got non-bool value"
      | DVALUE_I64 _ => failwith "Br got non-bool value"
      | DVALUE_Poison => failwith "Br got non-bool value"
      end; do st <- jump p fn bk br e s; Jump st
  | TERM_Br_1 br => do st <- jump p fn bk br e s; Jump st
  | TERM_Switch _ _ _ => t_raise "Unsupport LLVM terminator"
  | TERM_IndirectBr _ _ => t_raise "Unsupport LLVM terminator"
  | TERM_Resume _ => t_raise "Unsupport LLVM terminator"
  | TERM_Invoke _ _ _ _ => t_raise "Unsupport LLVM terminator"
  end =
  match t0 with
  | TERM_Ret (t1, op) =>
      do dv <- eval_op e (Some t1) op;
      match s with
      | [::] => Obs (Fin dv)
      | KRet e' id0 p' :: k' => Jump (p', add_env id0 dv e', k')
      | KRet_void _ _ :: _ =>
          t_raise_p {| fn := fn; bk := bk; pt := IId id |}
            "IMPOSSIBLE: Ret op in non-return configuration"
      end
  | TERM_Ret_void =>
      match s with
      | [::] => Obs (Fin (DV (VALUE_Bool true)))
      | KRet _ _ _ :: _ =>
          t_raise_p {| fn := fn; bk := bk; pt := IId id |}
            "IMPOSSIBLE: Ret void in non-return configuration"
      | KRet_void e' p' :: k' => Jump (p', e', k')
      end
  | TERM_Br (t1, op) br1 br2 =>
      do dv <- eval_op e (Some t1) op;
      do br <-
      match dv with
      | DV _ => failwith "Br got non-bool value"
      | DVALUE_CodePointer _ => failwith "Br got non-bool value"
      | DVALUE_Addr _ => failwith "Br got non-bool value"
      | DVALUE_I1 comparison_bit =>
          if StepSemantics.Int1.eq comparison_bit StepSemantics.Int1.one
          then inr br1
          else inr br2
      | DVALUE_I32 _ => failwith "Br got non-bool value"
      | DVALUE_I64 _ => failwith "Br got non-bool value"
      | DVALUE_Poison => failwith "Br got non-bool value"
      end; do st <- jump (mcfg_opt p) fn bk br e s; Jump st
  | TERM_Br_1 br => do st <- jump (mcfg_opt p) fn bk br e s; Jump st
  | TERM_Switch _ _ _ => t_raise "Unsupport LLVM terminator"
  | TERM_IndirectBr _ _ => t_raise "Unsupport LLVM terminator"
  | TERM_Resume _ => t_raise "Unsupport LLVM terminator"
  | TERM_Invoke _ _ _ _ => t_raise "Unsupport LLVM terminator"
  end. Proof. intros. destruct t0; eauto.
              +destruct v; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. eauto. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; rewrite  jump_equiv; eauto. rewrite <- jump_equiv. eauto. Qed.
 Hint Resolve term_equiv.


Lemma find_func_entry_equiv : forall p id0, (find_function_entry p id0) =  (find_function_entry (mcfg_opt p) id0).
Proof. intros. unfold find_function_entry. simpl in *. rewrite first_func. unfold end_func. simpl in *. destruct (find_function p id0); eauto. rewrite second_func. unfold end_func1. simpl in *. destruct ( find_block (blks (df_instrs d)) (init (df_instrs d))); eauto. simpl in *. unfold blk_entry_id in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct b. simpl in *. destruct blk_code; simpl in *; eauto. Qed.


Lemma find_func_equiv : forall d p fn,  Some d = find_function p fn -> (get_fn d) = fn.
Proof. Admitted.
Lemma subset_implies : forall b id e id0 res,  Subset (value_analysis (prep_block b) (IId id)) e  -> lookup_env (value_analysis (prep_block b) (IId id)) id0 = Some res -> lookup_env e id0 = Some res.
Proof. intros. unfold Subset in *. simpl in *.  induction e. simpl in *. Admitted.


Lemma find_block_equiv : forall b bk d, Some b = find_block (blks (df_instrs d)) bk -> (blk_id b) = bk. Proof. Admitted.
Lemma stepD_equiv : forall p s, sound_state p s -> stepD p s = stepD (mcfg_opt p) s.
Proof.
  intros. destruct s. simpl in *. destruct p0. simpl in *.
  unfold fetch in *. unfold incr_pc in *. destruct p0. rewrite first_func. simpl in *. unfold end_func. simpl in *. remember (find_function p fn). destruct o; simpl in *; eauto. rewrite second_func. unfold end_func1. simpl in *. remember (find_block (blks (df_instrs d)) bk). destruct o; eauto. unfold block_op. simpl in *. rewrite fourth_func. unfold end_func3. simpl in *. remember ( block_to_cmd b pt). destruct o; simpl in *. destruct p0. simpl in *. destruct c. destruct o; simpl in *; eauto.

  (*first*)



  destruct pt, i; simpl in *; eauto. unfold constant_prop_exp. simpl in *.
  (*CONST PROP*)



unfold constant_prop_exp; simpl in *. inversion H; subst; simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *.

generalize Heqo. intros. apply find_func_equiv in Heqo2. subst. rewrite <- Heqo. rewrite <- Heqo in senv.

generalize Heqo0. intros. apply find_block_equiv in Heqo2. subst. rewrite <- Heqo0.  rewrite <- Heqo0 in senv. destruct op. destruct e0; simpl in *; eauto. unfold  local_id_of_ident_op. unfold eval_expr. simpl in *. unfold local_id_of_ident. simpl in *.
destruct id0; simpl in *; eauto. generalize (senv (prep_block b)). assert (  Some (prep_block b) = Some (prep_block b)) by auto.
apply senv in H0.

remember ( lookup_env (value_analysis (prep_block b) (IId id)) id0). destruct o. simpl in *. destruct v; simpl in *; eauto.
destruct e0; simpl in *; eauto. simpl in *. eapply subset_implies in H0; eauto. rewrite H0. simpl in *. intros. eauto. simpl in *. unfold eval_expr. simpl in *. eauto.





  (*23*)






destruct fn0. unfold constant_prop_exp in *; eauto. destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto. destruct i; simpl in *; eauto.

rewrite <- find_func_entry_equiv. destruct (find_function_entry p id0); simpl in *; eauto. destruct i. rewrite <- find_func_entry_equiv. destruct (find_function_entry p id0); simpl in *; eauto; eauto. eauto. 




  unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

  unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

    unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

      unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

        unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

          unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

            unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.

              unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.


        unfold constant_prop_exp. destruct ( prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IId id |}); eauto.
        unfold constant_prop_exp. inversion H. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. subst.
generalize Heqo; intro. generalize Heqo0; intros. apply find_func_equiv in Heqo2. subst. rewrite <- Heqo. apply find_block_equiv in Heqo3. subst. rewrite <- Heqo0. destruct op. destruct e0; simpl in *; eauto.
unfold local_id_of_ident_op. simpl in *. destruct id; simpl in *; eauto. unfold lookup_env. simpl in *. destruct (      assoc AstLib.RawID.eq_dec id
        (value_analysis (prep_block b) (IVoid n))
). destruct v; simpl in *; eauto. destruct e0; simpl in *; eauto. eauto.
      

destruct fn0. destruct i. simpl in *. unfold constant_prop_exp in *. simpl in *. inversion H; subst; eauto. simpl in *. unfold sound_env in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. generalize Heqo. generalize Heqo0. intros. apply find_func_equiv in Heqo3. subst. rewrite <- Heqo. apply find_block_equiv in Heqo2. subst. rewrite <- Heqo0. rewrite <- find_func_entry_equiv. destruct (find_function_entry p id); simpl in *; eauto. 


 unfold constant_prop_exp. simpl in *.
destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.



unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.




unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.


unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.


unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.



unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.


unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.


unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.


unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.

unfold constant_prop_exp; destruct (prep_selected_block p {| fn := get_fn d; bk := blk_id b; pt := IVoid n |}); eauto.


destruct t; eauto. destruct v. simpl in *.  destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. destruct ( StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; eauto; rewrite jump_equiv; eauto. rewrite jump_equiv. eauto. eauto. 

Qed.





                   
   Definition unroll (t:Trace ()) :=
  match t with
  | Vis b => Vis b
  | Tau b c => Tau  b c
                     
  end.

    

   Lemma trace_equiv_opt : forall  (norep: forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil)) mem st p,  
                                           sound_state p st ->
                                           trace_equiv (memD mem (sem p st)) (memD mem (sem (mcfg_opt p) st)).
   Proof. intro. pcofix CIH. intros. pfold.
          assert ( (memD mem (sem p st)) = unroll (memD mem (sem p st))). destruct  (memD mem (sem p st)); eauto. rewrite H; clear H.

          assert ( (memD mem (sem (mcfg_opt p) st)) = unroll  (memD mem (sem (mcfg_opt p) st))). destruct  (memD mem (sem (mcfg_opt p) st)); eauto. rewrite H. clear H. simpl in *. generalize H0; intros. apply  stepD_equiv in H1. rewrite <- H1.
          remember (stepD p st). generalize Heqt. intros.
 symmetry in Heqt0.

 apply test_stepD_equiv in Heqt0. destruct t. eapply step_preserves_sound_state  in H0; eauto.

 eapply jump_preserves_sound_state in norep; eauto. destruct m. simpl in *; eauto. simpl in *. eauto.


 simpl in *.

 
 unfold stepD in Heqt. destruct st. destruct p0. unfold fetch, incr_pc in *.
 simpl in *. destruct p0. clear H1. 
 remember (find_function p fn). destruct o. remember (find_block (blks (df_instrs d)) bk). destruct o. remember ( block_to_cmd b pt). destruct o. destruct p0. destruct c. simpl in *. destruct o. simpl in *. destruct pt, i; inversion Heqt. clear H1. (* HERE*)
destruct ( eval_op e0 None op). simpl in *. inversion Heqt. simpl in *. inversion Heqt.
destruct fn0. simpl in *. destruct i. destruct  (find_function_entry p id0); simpl in *; inversion H1. destruct f. simpl in *.
 destruct ( map_monad (fun '(t, op) => eval_op e0 (Some t) op) args); simpl in *; inversion H1. inversion H1.

 subst. simpl in *. constructor. right. apply CIH. eapply test5 in norep; eauto.





inversion H0; subst; simpl in *. constructor; simpl in *; eauto. unfold add_env. simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo in senv. simpl in *. rewrite <- Heqo0. rewrite <- Heqo0 in senv.


intros. inversion H. subst. apply senv in H. unfold Subset in *. simpl in *. rewrite norep. unfold transfer. simpl in *. intros. right. apply H. auto.







destruct ptr. simpl in *.
simpl in *. destruct (eval_op e0 (Some t0) v); simpl in *. inversion H1. destruct v0; simpl in *; inversion H1. subst. simpl in *. constructor. right. apply CIH. clear Heqt. clear H1. clear Heqt0. inversion H0. subst. simpl in *. constructor; eauto. simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. simpl in *. intros. inversion H. subst. apply senv in H. unfold Subset in *. simpl in *. eapply test5 in norep; eauto. rewrite norep. unfold transfer; simpl. intros. right. auto. destruct fn0. simpl in *. destruct i. simpl in *. destruct  (find_function_entry p id); simpl in *. destruct f. simpl in *. destruct (map_monad (fun '(t, op) => eval_op e0 (Some t) op) args); simpl in *; inversion H1. destruct t; inversion H1. inversion H1. inversion H1. destruct val. destruct ptr. simpl in *. destruct (eval_op e0 (Some t) v), (eval_op e0 (Some t0) v0); simpl in *; inversion H1. destruct v2; inversion H1. subst. simpl in *. clear Heqt. clear Heqt0. clear H1. clear H2. constructor. right. apply CIH. inversion H0; simpl in *; subst. constructor; simpl in *; eauto. eapply test5 in norep; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. rewrite <- Heqo. rewrite <- Heqo0. intros. inversion H. subst. apply senv in H. rewrite norep. unfold transfer; simpl in *. unfold Subset in *. simpl in *. intros. auto. simpl in *. inversion Heqt. simpl in *. destruct t; inversion Heqt. destruct v. simpl in *.   destruct (eval_op e0 (Some t) v); simpl in *; inversion H1. destruct s; inversion H1. destruct f; inversion H1. destruct s; inversion H1. destruct f; inversion H1. destruct v. destruct ( eval_op e0 (Some t) v); simpl in *; inversion H1. destruct v0; inversion H1. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; inversion H1. destruct (jump p fn bk br1 e0 s); simpl in *; inversion H1. destruct (jump p fn bk br2 e0 s); inversion H1. destruct (jump p fn bk br e0 ); inversion H1. simpl in *. inversion Heqt. simpl in *. inversion Heqt. simpl in *. inversion Heqt. Qed.*)