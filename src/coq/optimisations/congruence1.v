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


(*An optimisation takes in a program counter, the overall program and an instruction and returns a fully formed line of code*)

Definition opt := pc -> mcfg -> instr -> (instr_id * instr).

Print pc.

Definition mkpc (fn:function_id) (bk:block_id) (pt:instr_id) : pc := mk_pc fn bk pt.

Definition code_opt (o:opt) (m:mcfg) (c:code) (bk:block_id) (fn:function_id) : code :=
  match c with
  | nil => nil
  | (iid, ins) :: tl => (o (mk_pc fn bk iid) m ins) :: tl
  end.

Definition block_opt (o:opt) (m:mcfg) (fn:function_id) (b:block) : block := mk_block (blk_id b) (blk_phis b) (code_opt o m (blk_code b) (blk_id b) fn) (blk_term b).


Definition list_block_opt (o:opt) (m:mcfg) (fn:function_id) (l:list block) : list block := map (block_opt o m fn) l.

Definition cfg_opt (o:opt) (m:mcfg) (fn:function_id) (c:cfg) : cfg := mkCFG (init c) (list_block_opt o m fn (blks c)) (glbl c).


Print definition.
Print declaration.

Definition function_id_of_dec (d:declaration) : function_id := (dc_name d).

Print definition.




Definition definition_cfg_opt (o:opt) (m:mcfg) (d:definition cfg) : definition cfg := mk_definition cfg (df_prototype d) (df_args d) (cfg_opt o m (function_id_of_dec (df_prototype d)) (df_instrs d)).


Definition list_def_cfg_opt (o:opt) (m:mcfg) (d:list (definition cfg)) : list (definition cfg) := map (definition_cfg_opt o m) d.

Print modul.

Definition modul_opt (o:opt) (m:mcfg) := mk_modul cfg (m_name m) (m_target m) (m_datalayout m) (m_globals m) (m_declarations m) (list_def_cfg_opt o m (m_definitions m)).


Print fetch.
Print find_block_entry.
Print block_entry.




Definition block_entry_pc m fid bid :=
  match find_block_entry m fid bid with
  | None => None
  | Some (BlockEntry _ a) => Some a
  end
.


Print  compare_exec.
Print state.
Definition mk_state (p:pc) (e:env) (s:stack) : state := (p, e, s).
Print pc.

Definition pt_of_pc (p:pc) : instr_id := pt p.

Print compare_exec.
Definition correct_instr m o  fid bid := forall mem s e i a, block_entry_pc m fid bid = Some a /\ compare_exec m (modul_opt o m) (cons ((pt_of_pc a), i) nil) (cons (o a m i) nil) mem (mk_state a e s) /\ fst (o a m i) = pt_of_pc a.




Print find_function.
Definition startfunc1 fnid A o := find_function (modul_opt o A) fnid.

Definition endfunc1 fnid A := find_function A fnid.


Definition targetfunc1 fnid A o :=
  match endfunc1 fnid A with
  | Some a => Some (definition_cfg_opt o A a)
  | None => None
  end.


Lemma equiv_func1 : forall A o fnid, find_function (modul_opt o A) fnid = targetfunc1 fnid A o.
Proof. Admitted.

Definition startfunc d m o bk :=                  find_block
                   (list_block_opt o m (function_id_of_dec (df_prototype d))
                      (blks (df_instrs d))) bk.

Definition endfunc d bk := find_block (blks (df_instrs d)) bk.


Definition targetfunc o m (d:definition cfg)  bkid :=
  match endfunc d bkid with
  | Some a => Some (block_opt o m (function_id_of_dec (df_prototype d)) a)
  | None => None 
  end.


Lemma equiv_func : forall o m d df_instrs bk,  find_block
                   (list_block_opt o m (function_id_of_dec (df_prototype d))
                      (blks (df_instrs d))) bk = targetfunc o m d bk.
Proof. Admitted.









Lemma correct_instr_trace : (forall o m fid bid, correct_instr m o fid bid) -> forall o m st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof. intro. pcofix CIH. intros. specialize (H o m). pfold.
       assert (  (memD mem (sem m st)) = unroll   (memD mem (sem m st))). destruct   (memD mem (sem m st)); eauto.
       rewrite H0; clear H0.

       assert ((memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))). destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H0; clear H0.

       destruct st. destruct p. destruct p. specialize (H fn bk). unfold correct_instr in H. specialize (H mem s e). unfold block_entry_pc in H. unfold find_block_entry in H. simpl in H. unfold block_to_entry in H. simpl in H.


       simpl in *. rewrite equiv_func1. unfold targetfunc1; unfold endfunc1.
       remember ( find_function m fn) as findfunc. destruct findfunc; simpl in *; eauto.  rewrite equiv_func. unfold targetfunc. unfold endfunc. remember ( find_block (blks (df_instrs d)) bk) as findblock. destruct findblock; simpl in *; eauto. unfold blk_entry_pc in H. unfold block_to_cmd. unfold blk_term_id in *. destruct b. simpl in *.
       destruct blk_term. simpl in *. unfold blk_entry_id in *. simpl in *. destruct ( decide (i = pt)); simpl in *. subst.


       admit.
       unfold code_opt. destruct blk_code; simpl in *; eauto. destruct p. specialize (H i1).
       specialize (H  {| fn := dc_name (df_prototype d); bk := bk; pt := pt |}). destruct H. inversion H; subst. unfold pt_of_pc in H0. unfold mk_state in H0. simpl in *. destruct ( decide (pt = pt)); simpl in *. unfold function_id_of_dec in *. simpl in *. destruct d. destruct H0. unfold compare_exec in H0. simpl in *. rewrite equiv_func1 in H0; unfold targetfunc1 in H0; unfold endfunc1 in H0; rewrite <- Heqfindfunc in H0; rewrite equiv_func in H0; unfold targetfunc in H0; unfold endfunc in H0; simpl in *; rewrite <- Heqfindblock in H0. unfold function_id_of_dec in H0. unfold block_to_cmd in H0. unfold blk_term_id in *; simpl in *.
       destruct ( decide (i = pt)); subst; simpl in *; eauto. apply n in e0. inversion e0. destruct (decide (pt = pt)). simpl in *. destruct  (o {| fn := dc_name df_prototype; bk := bk; pt := pt |}
                                                                                                                                                 m i1); simpl in *; subst. destruct (decide (pt = pt)); simpl in *.
       destruct pt, i1, i2; simpl in *; eauto. destruct ( eval_op e None op0), (eval_op e None op); simpl in *; eauto. admit. admit. admit. destruct ( eval_op e None op), fn, i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id0); simpl in *; eauto.  destruct ( map_monad
                (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto. destruct f; simpl in *; eauto. destruct f; simpl in *; eauto. admit. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto. admit. admit. admit. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. admit. admit. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto.  admit.  destruct ( eval_op e None op); simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. destruct fn, i0; simpl in *; eauto. destruct   (find_function_entry m id0); simpl in *; eauto; destruct f; simpl in *; eauto. destruct (             map_monad
               (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. admit. admit. admit. admit. destruct fn, i0; simpl in *; eauto. destruct  (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op)
               args0); simpl in *; eauto. admit. destruct fn0, i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op)
              args0); simpl in *; eauto. admit. admit. admit. admit. destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (  map_monad (fun '(t2, op) => eval_op e (Some t2) op)
               args0); simpl in *; eauto. admit. destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto; destruct (  map_monad (fun '(t2, op) => eval_op e (Some t2) op)
                args0); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f, (  map_monad (fun '(t, op) => eval_op e (Some t) op)
               args); simpl in *; eauto. admit. admit. admit. admit. destruct fn, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f, (map_monad (fun '(t, op) => eval_op e (Some t) op)
               args); simpl in *; eauto. destruct ptr; simpl. destruct ( eval_op e (Some t2) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ptr; simpl in *. destruct ( eval_op e (Some t2) v); simpl in *; eauto. admit. destruct v0; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct fn, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (  map_monad (fun '(t, op) => eval_op e (Some t) op)
              args); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op)
              args); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct     (find_function_entry m id0); simpl in *; eauto. destruct f, (             map_monad (fun '(t1, op) => eval_op e (Some t1) op)
               args); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct   (find_function_entry m id0); simpl in *; eauto. destruct f, ( map_monad (fun '(t1, op) => eval_op e (Some t1) op)
                args); simpl in *; eauto. admit. destruct fn; simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. admit. destruct fn, i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f, ( map_monad (fun '(t2, op) => eval_op e (Some t2) op)
                                                                                                                                                                                                                                                                                                                                       args); simpl in *; eauto. admit. admit. admit. admit. destruct ptr. destruct ( eval_op e (Some t2) v); simpl in *; eauto. admit. destruct v0; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct ptr, ( eval_op e None op); simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ( eval_op e (Some t1) v); simpl in *; eauto. admit. destruct v1; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct ptr, ptr0; simpl in *; eauto. destruct ( eval_op e (Some t2) v); simpl in *; eauto. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct  v1; simpl in *; eauto. admit. destruct v1; simpl in *; eauto. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct v1; simpl in *; eauto. admit. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct v1; simpl in *; eauto. admit. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. admit. destruct v1; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct v1; simpl in *; eauto. admit. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct v1; simpl in *; eauto. admit. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct v1; simpl in *; eauto. admit. destruct ( eval_op e (Some t3) v0); simpl in *; eauto. destruct v1; simpl in *; eauto. admit. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ptr; simpl in *; eauto.
destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ptr; simpl in *; eauto. destruct (eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ptr; simpl in *; eauto.  destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f, (
              map_monad (fun '(t1, op) => eval_op e (Some t1) op)
                args); simpl in *; eauto. admit. admit. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. destruct fn, i0; simpl in *; eauto. destruct    (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (  map_monad (fun '(t, op) => eval_op e (Some t) op)
              args); simpl in *; eauto. admit. admit. destruct ptr. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. admit. destruct ( eval_op e None op); simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct val, ptr; simpl in *; eauto.  destruct ( eval_op e (Some t0) v), ( eval_op e (Some t1) v0); simpl in *; eauto. destruct v2; simpl in *; eauto. admit. admit. admit. destruct val, ptr; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. apply n1 in e1. inversion e1. apply n1 in e0; inversion e0. assert (pt = pt) by auto.  apply n0 in H1. inversion H1. Admitted.