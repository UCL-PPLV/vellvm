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



Print pc.


Print find_block_entry.

Print function_entry.
Definition get_block_pc (m:mcfg) (fid: function_id) (bid: block_id) :=
  match find_block_entry m fid bid  with
  | None => None
  | Some (BlockEntry _ a) => Some a
  end.

Print incr_pc.
Locate pc.
Print pc.
Definition new_state (old:pc) (i1:instr_id) :=
  let (fn, bk, pt) := old in
  mk_pc fn bk i1.

Inductive pc_correct : mcfg -> pc -> Prop :=
| pc_correct_start : forall m pc fpc, fpc = pc -> get_block_pc m (fn pc) (bk pc) = Some fpc -> pc_correct m pc
| pc_step : forall m pc i, pc_correct m (new_state pc i) -> incr_pc m (new_state pc i)  = Some pc -> pc_correct m pc.
Print pc.




Inductive match_state : state -> mcfg -> mcfg -> Prop :=
| match_pc : forall s1 m1 m2 (H:pc_correct m1 (pc_of s1)) (H1: pc_correct m2 (pc_of s1)), match_state s1 m1 m2.



Definition opt := (instr_id*instr -> instr_id*instr).





Inductive list1 :=
| single : finish_item state -> list1
| double : finish_item state -> list1 -> list1.
















Fixpoint exec_code2 (m:mcfg) (c:code) (f:finish_item ( state)) : list1 :=
match c with
  | [::] => match f with
            | visitem mem (Eff s') => single ( (visitem mem (Eff s'))) 
            | sec => single ( sec)
            end
  | h :: t => match f with
              | tauitem mem s => match (CFG_step (snd h) m s) with
                             | Step s' => double ( (tauitem mem s)) (exec_code2 m t (tauitem mem s'))
                             | Jump s' => double ( (tauitem mem s)) (exec_code2 m t (tauitem mem s'))
                             | Obs (Eff s') => match mem_step s' mem with
                                               | inr (m', v, k) => double ( (tauitem mem s)) (exec_code2 m t (tauitem m' (k v)))
                                               | inl _ => single ( (tauitem mem s))
                                               end
                             | Obs (Fin s') => double ( (tauitem mem s)) (exec_code2 m t ((visitem mem (Fin s'))))
                             | Obs (Err s') => double ( (tauitem mem s)) (exec_code2 m t ((visitem mem (Err s'))))
                             end
              | item => single ( item)
              end
end.

Inductive compare_list2 : list1 -> list1 -> Prop :=
| compare_list2_refl : forall a, compare_list2 a a
| compare_list2_right : forall h t1 t2, compare_list2 t1 t2 -> compare_list2 t1 (double h t2)
| compare_list2_left : forall h t1 t2, compare_list2 t1 t2 -> compare_list2 (double h t1) t2.



Definition optimise_code (o:instr_id*instr -> instr_id*instr) (b:code) : code :=
  match b with
  | nil => nil
  | hd :: tl => o hd :: tl
  end
.

Print block.

Definition optimise_block  (o:instr_id*instr -> instr_id*instr) (b:block) : block := mk_block (blk_id b) (blk_phis b) (optimise_code o (blk_code b)) (blk_term b).


Definition optimise_list_block (o:instr_id*instr -> instr_id*instr)  (b:list block) : list block :=
  map (optimise_block o) b.


Definition optimise_cfg (o:instr_id*instr -> instr_id*instr)  (c:cfg) : cfg :=
  mkCFG (init c) (optimise_list_block o (blks c)) (glbl c).
Print definition.


Definition optimise_definition (o:instr_id*instr -> instr_id*instr)  (c:definition cfg) :=
  mk_definition cfg (df_prototype c) (df_args c) (optimise_cfg o (df_instrs c)).


Definition optimise_list_definition (o:instr_id*instr -> instr_id*instr)  (c: list (definition cfg)) :=
  map (optimise_definition o) c.


Definition optimise_modul (o:instr_id*instr -> instr_id*instr) (c: modul cfg) :=
  mk_modul cfg (m_name c) (m_target c) (m_datalayout c) (m_globals c) (m_declarations c) (optimise_list_definition o (m_definitions c)).








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




Definition hd_equal (o:opt) := forall i,  fst i = fst (o i).




Definition correct_instr (o:opt) := (forall s b1 m mem, compare_list2 (exec_code2 m b1 (tauitem mem s)) (exec_code2 (optimise_modul o m) (optimise_code o b1)  (tauitem mem s))).


Lemma Test123 : forall o, correct_instr o /\ hd_equal o -> forall m st mem, match_state st m (optimise_modul o m) -> trace_equiv (memD mem (sem m st)) (memD mem (sem (optimise_modul o m) st)).
Proof. intros o instrcpr. pcofix CIH. intros. pfold. inversion H0; subst.

destruct instrcpr. unfold correct_instr, hd_equal in *. specialize (H2 st).




destruct st. destruct p. destruct p.



inversion H; subst; simpl in *.  unfold get_block_pc in *. unfold find_block_entry in H5. simpl in *.




       assert ( (memD mem (sem m ({| fn := fn; bk := bk; pt := pt |}, e, s))) = unroll  (memD mem (sem m ({| fn := fn; bk := bk; pt := pt |}, e, s)))). destruct  (memD mem (sem m ({| fn := fn; bk := bk; pt := pt |}, e, s))); eauto. rewrite H4; clear H4. 




       assert (  (memD mem (sem (optimise_modul o m) ({| fn := fn; bk := bk; pt := pt |}, e, s))) = unroll   (memD mem (sem (optimise_modul o m) ({| fn := fn; bk := bk; pt := pt |}, e, s)))). destruct   (memD mem (sem (optimise_modul o m) ({| fn := fn; bk := bk; pt := pt |}, e, s))); eauto. rewrite H4; clear H4.


       simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. remember ( find_function m fn) as findfunc. destruct findfunc; simpl in *; eauto.
       
 simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc. remember ( find_block (blks (df_instrs d)) bk) as findblock. destruct findblock; simpl in *; eauto. unfold blk_entry_pc in *. unfold blk_id in *.
 unfold block_to_cmd. unfold blk_entry_id in *. 
 destruct b. simpl in *. unfold  blk_term_id in *. simpl in *. inversion H5. subst.

 destruct blk_term; simpl in *.
 destruct blk_code.

       +simpl in *. destruct ( decide (i = i)); simpl in *; eauto. admit.
       +simpl in *. destruct p. simpl in *. destruct ( decide (i = i0)); simpl in *. admit. destruct (decide (i0 = i0)); simpl in *. specialize (H3  (i0, i1)). destruct ( o (i0, i1)); simpl in *. subst. destruct ( decide (i2 = i2)); simpl in *. admit. apply n0 in e0. inversion e0. assert (i0 = i0) by auto. apply n0 in H4. inversion H4.




        assert ( (memD mem (sem m ({| fn := fn; bk := bk; pt := pt |}, e, s))) = unroll  (memD mem (sem m ({| fn := fn; bk := bk; pt := pt |}, e, s)))). destruct  (memD mem (sem m ({| fn := fn; bk := bk; pt := pt |}, e, s))); eauto. rewrite H6; clear H6.

        assert (  (memD mem (sem (optimise_modul o m) ({| fn := fn; bk := bk; pt := pt |}, e, s))) = unroll   (memD mem (sem (optimise_modul o m) ({| fn := fn; bk := bk; pt := pt |}, e, s)))). destruct   (memD mem (sem (optimise_modul o m) ({| fn := fn; bk := bk; pt := pt |}, e, s))); eauto. rewrite H6; clear H6. simpl in *. unfold incr_pc in *. simpl in *. unfold block_to_cmd in *.





 rewrite equiv_func1. unfold targetfunc1. unfold endfunc1.

        
 remember ( find_function m fn) as findfunc. destruct findfunc; simpl in *.
 rewrite equiv_func. unfold targetfunc. unfold endfunc.
        remember ( find_block (blks (df_instrs d)) bk) as findblock. destruct findblock; simpl in *.
        unfold blk_term_id in *. simpl in *. destruct b. simpl in *. destruct blk_term. simpl in *. 

        destruct ( decide (i0 = pt)); simpl in *. admit. destruct ( decide (i0 = i)); simpl in *. inversion H5. unfold optimise_code in *. destruct blk_code in *. simpl in *. eauto. simpl in *. destruct blk_code. simpl in *. destruct p. destruct ( decide (i = i1)); simpl in *. inversion H5; subst.
        destruct ( decide (pt = i1)); simpl in *; subst; eauto. admit. specialize (H3 (i1, i2)). destruct ( o (i1, i2)); simpl in *. subst. destruct (decide (pt = i)); subst; simpl in *. admit. eauto. inversion H5. destruct p.



        admit. eauto. eauto. Admitted.









(**********************************************************************************)


Print instr_id.
Print raw_id.


Fixpoint max (cd:code) (n:option int) :=
  match cd with
  | nil => n
  | (IId (Raw iis), ins) :: tl => match n with
                        | None => max tl (Some iis)
                        | Some a => if Z.leb iis a then max tl (Some iis) else max tl n
                                  end
  | _ :: tl => max tl n
    end.


Fixpoint generate_code (l: list instr) (n:int) : code :=
  match l with
  | nil => nil
  | hd :: tl => ((IId (Raw n), hd) :: (generate_code tl (Z.succ n)))
    end.


Definition generate_opt_code (cd:code) (l:list instr) :=
  match max cd None with
  | None => generate_code l Z.zero
  | Some a => generate_code l (Z.succ a)
  end.



Definition opt1 (c:code) (i:instr_id*instr) (l:list instr) : code :=
  let (iid, ins) := i in
  match l with
  | nil => nil
  | hd :: tl => (iid, hd) :: generate_opt_code c tl
  end
.



Definition optimise_code1 (c:code) (l:list instr):=
  match c with
  | nil => nil
  | hd::tl => (opt1 c hd l) ++ tl
  end.


Definition optimise_block1  (l:list instr) (b:block) : block := mk_block (blk_id b) (blk_phis b) (optimise_code1 (blk_code b) l) (blk_term b).


Definition optimise_list_block1 (l:list instr)  (b:list block) : list block :=
  map (optimise_block1 l) b.


Definition optimise_cfg1 (l:list instr)  (c:cfg) : cfg :=
  mkCFG (init c) (optimise_list_block1 l (blks c)) (glbl c).
Print definition.


Definition optimise_definition1 (l:list instr)  (c:definition cfg) :=
  mk_definition cfg (df_prototype c) (df_args c) (optimise_cfg1 l (df_instrs c)).


Definition optimise_list_definition1 (l:list instr)  (c: list (definition cfg)) :=
  map (optimise_definition1 l) c.


Definition optimise_modul1 (l:list instr) (c: modul cfg) :=
  mk_modul cfg (m_name c) (m_target c) (m_datalayout c) (m_globals c) (m_declarations c) (optimise_list_definition1 l (m_definitions c)).


Definition correct_instr1 (c:code) (i:instr_id*instr) (l:list instr) := (forall s m mem, compare_list2 (exec_code2 m (cons i nil) (tauitem mem s)) (exec_code2 (optimise_modul1 l m)
 (opt1 c i l)  (tauitem mem s))).









Definition startfunc2 fnid A o := find_function (optimise_modul1 o A) fnid.

Definition endfunc2 fnid A := find_function A fnid.


Definition targetfunc2 fnid A o :=
  match endfunc2 fnid A with
  | Some a => Some (optimise_definition1 o a)
  | None => None
  end.


Lemma equiv_func2 : forall A o fnid, find_function (optimise_modul1 o A) fnid = targetfunc2 fnid A o.
Proof. Admitted.


Definition startfunc3 o df_instrs bk := find_block (optimise_list_block1 o (blks df_instrs)) bk.

Definition endfunc3 df_instrs bk := find_block (blks df_instrs) bk.



Definition targetfunc3 o df_instrs bkid :=
  match endfunc3 df_instrs bkid with
  | Some a => Some (optimise_block1 o a)
                             | None => None 
  end.


Lemma equiv_func3 : forall o df_instrs bk, find_block (optimise_list_block1 o (blks df_instrs)) bk = targetfunc3 o df_instrs bk.
Proof. Admitted.

