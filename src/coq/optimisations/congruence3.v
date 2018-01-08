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


Definition opt := pc -> mcfg -> instr -> seq instr.

Print raw_id.
Print instr_id.
Fixpoint get_max (c:code) (i:option int) :=
  match c, i with
  | nil, _ => i
  | ((IId (Raw a), ins) :: tl), None => get_max tl (Some a)
  | ((IId (Raw a), ins) :: tl), Some b => if Z.leb a b then (get_max tl (Some a)) else (get_max tl (Some b))
  | _ :: tl, _ => get_max tl i                                        
  end.



Definition get_next (c:code) :=
  match get_max c None with
  | None => Z.zero
  | Some a => Z.succ a
  end.


Definition int_to_ins (i:int) := IId (Raw i).

Fixpoint create_code_help (s:seq instr) (i:int) :=
  match s with
  | nil => nil
  | hd :: tl => ((int_to_ins i), hd) :: (create_code_help tl (Z.succ i))
  end.


Definition create_code (s:seq instr) (i:int) (iid:instr_id) :=
  match s with
  | nil => nil
  | hd :: tl => (iid, hd) :: create_code_help tl i
  end.

Print pc.


Definition build_opt (o:opt) (p:pc) (m:mcfg) (i:instr) (ins:int) := create_code (o p m i) ins (pt p).



Definition mkpc (fn:function_id) (bk:block_id) (pt:instr_id) : pc := mk_pc fn bk pt.




Definition code_opt (o:opt) (m:mcfg) (c:code) (bk:block_id) (fn:function_id) (i:int) : code :=
  match c with
  | nil => nil
  | (iid, ins) :: tl => (build_opt o (mkpc fn bk iid) m ins i) ++ tl
  end.


Definition block_opt (o:opt) (m:mcfg) (fn:function_id) (b:block) : block := mk_block (blk_id b) (blk_phis b) (code_opt o m (blk_code b) (blk_id b) fn (get_next b.(blk_code))) (blk_term b).


Definition list_block_opt (o:opt) (m:mcfg) (fn:function_id) (l:list block) : list block := map (block_opt o m fn) l.

Definition cfg_opt (o:opt) (m:mcfg) (fn:function_id) (c:cfg) : cfg := mkCFG (init c) (list_block_opt o m fn (blks c)) (glbl c).

Definition function_id_of_dec (d:declaration) : function_id := (dc_name d).







Definition definition_cfg_opt (o:opt) (m:mcfg) (d:definition cfg) : definition cfg := mk_definition cfg (df_prototype d) (df_args d) (cfg_opt o m (function_id_of_dec (df_prototype d)) (df_instrs d)).


Definition list_def_cfg_opt (o:opt) (m:mcfg) (d:list (definition cfg)) : list (definition cfg) := map (definition_cfg_opt o m) d.

Print modul.

Definition modul_opt (o:opt) (m:mcfg) := mk_modul cfg (m_name m) (m_target m) (m_datalayout m) (m_globals m) (m_declarations m) (list_def_cfg_opt o m (m_definitions m)).

Definition mk_state (p:pc) (e:env) (s:stack) : state := (p, e, s).


Definition correct_instr1 m o fid bid := forall mem s e iid i t int_ins, compare_exec1 m (modul_opt o m) (cons (iid, i) nil)

                                                                               (build_opt o (mk_pc fid bid iid) m i int_ins) mem (mk_state (mk_pc fid bid iid) e s) t.



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




Definition check_size (l:code) :=
  match l with
  | nil => True
  | cons _ nil => True
  | cons _ ( cons _ nil) => True
  | _ => False
  end.

Print build_opt.


 Lemma correct_instr_trace1 : (forall o fid bid iid m i int_ins, check_size (build_opt o (mk_pc fid bid iid) m i int_ins)) ->(forall o m fid bid, correct_instr1 m o fid bid) -> forall o m st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof. intro. intro. intro.  pcofix CIH. intros. pfold.

       assert ( (memD mem (sem m st)) = unroll  (memD mem (sem m st))). destruct  (memD mem (sem m st)); eauto. rewrite H1. clear H1.

       assert (  (memD mem (sem (modul_opt o m) st)) = unroll   (memD mem (sem (modul_opt o m) st))). destruct   (memD mem (sem (modul_opt o m) st)); eauto. rewrite H1. clear H1.


       simpl in *. destruct st. simpl in *. destruct p. destruct p. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1.



       specialize (H o). specialize (H0 o m). destruct ( find_function m fn); simpl in *; eauto.
       rewrite equiv_func. unfold targetfunc. unfold endfunc. simpl in *. destruct (find_block (blks (df_instrs d)) bk); simpl in *; eauto. unfold block_to_cmd. unfold blk_term_id. simpl in *. destruct b. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt) ); simpl in *; eauto. admit. unfold code_opt in *.


specialize (H0  (function_id_of_dec (df_prototype d)) blk_id).






unfold correct_instr1 in H0. specialize (H0 mem s e).
destruct blk_code. simpl in *; eauto.



simpl in *. destruct p.
Admitted.