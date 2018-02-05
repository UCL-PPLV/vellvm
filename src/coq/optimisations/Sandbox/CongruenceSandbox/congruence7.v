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

(* take 1 instr and returns a list of instr *)

Print code.
Print state.
Print pc.
Definition instr_opt  := (mcfg) -> (function_id) -> (block_id) -> (instr_id * instr) ->  seq (instr_id * instr).


Definition apply_instr_opt (i:instr_opt) (m:mcfg) (fn:function_id) (bk:block_id) (ins:instr_id * instr) := i m fn bk ins.

Print instr_opt.


Print map.

Definition code_opt (m:mcfg) (fn:function_id) (bk:block_id) (o:instr_opt) (cd:code) : code :=
  match cd with
  | nil => nil
  | hd::tl => (o m fn bk hd) ++ tl
    end.




    
Print block.
Definition block_opt (m:mcfg) (o:instr_opt) (fn:function_id) (b:block) := mk_block (blk_id b) (blk_phis b) (code_opt m fn (blk_id b) o (blk_code b)) (blk_term b).


Print cfg.


Definition list_block_opt (m:mcfg) (o:instr_opt) (fn:function_id) (b:list block) := map (block_opt m o fn) b.

Definition cfg_opt (m:mcfg) (o:instr_opt) (fn:function_id) (c:cfg) := mkCFG (init c) (list_block_opt m o fn (blks c)) (glbl c).



Print definition.
Print declaration.

Definition fn_id (d:declaration) : function_id := (dc_name d).

Definition definition_opt (m:mcfg) (o:instr_opt) (d:definition cfg) := mk_definition cfg (df_prototype d) (df_args d) (cfg_opt m o (fn_id (df_prototype d)) (df_instrs d)).


Print mcfg.
Print modul.

Definition list_definition_opt (m:mcfg) (o:instr_opt) (d:list (definition cfg)) := map (definition_opt m o) d.

Definition mcfg_opt (o:instr_opt) (m:mcfg) := mk_modul cfg (m_name m) (m_target m) (m_datalayout m) (m_globals m) (m_declarations m) (list_definition_opt m o (m_definitions m)).



Print compare_seq.



Definition startfunc1 fnid A o := find_function (mcfg_opt o A) fnid.

Definition endfunc1 fnid A := find_function A fnid.


Definition targetfunc1 fnid A o :=
  match endfunc1 fnid A with
  | Some a => Some (definition_opt A o a)
  | None => None
  end.


Lemma equiv_func1 : forall A o fnid, find_function (mcfg_opt o A) fnid = targetfunc1 fnid A o.
Proof. Admitted.

Print find_block.
Definition startfunc m (o:instr_opt) d bk : option block := find_block
                   (list_block_opt m o (fn_id (df_prototype d)) (blks (df_instrs d)))
                   bk.

Definition endfunc d bk := find_block (blks (df_instrs d)) bk.


Print endfunc.
Definition targetfunc m o d bkid :=
  match endfunc d bkid with
  | Some a => Some (block_opt m o (fn_id (df_prototype d)) a)
                             | None => None 
  end.


Lemma equiv_func : forall m o d bk, find_block (list_block_opt m o (fn_id (df_prototype d)) (blks (df_instrs d))) bk = targetfunc m o d bk.
Proof. Admitted.




(*
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


    

*)




(*find in block*)
 Print find_instr.





(*first is the same*)
(* equality*)
Print code.
Definition donothing (fn:function_id) (bk:block_id)  (i:instr_id * instr) : code := cons i nil.
Print compare_seq1.




Inductive compare_seq2 : seq (option (finish_item state)) -> seq (option (finish_item state)) -> Prop :=
  | third1 : forall h1 h2 : option (finish_item state), h1 = h2 -> compare_seq2 [:: h1] [:: h2]
  | left1 : forall (h1 h2 : option (finish_item state)) (t1 t2 : seq (option (finish_item state))),
            compare_seq2 t1 (h2::t2) -> compare_seq2 (h1 :: t1) (h2 :: t2)
  | right1 : forall (h1 h2 : option (finish_item state))
               (t1 t2 : seq (option (finish_item state))),
             compare_seq2 (h1::t1) t2 -> compare_seq2 (h1::t1) (h2 :: t2)
.



Definition instr_correct (o:instr_opt) := forall i fn bk m mem s, compare_seq2 (exec_code1 m (cons i nil) (tauitem mem s)) (exec_code1 (mcfg_opt o m) (o m fn bk i) (tauitem mem s)).


Lemma compare_seq_eq : forall a, compare_seq a a.
Proof. intros. induction a; constructor; auto. Qed.
Hint Resolve compare_seq_eq.


Definition check_hd(i:instr_id) (cd:code) :=
  match cd with
  | nil => True
  | (id, _) :: _ => i = id
  end.

  
Definition instr_opt_check (i:instr_opt) := forall  (id:instr_id * instr) m fn bk, check_hd (fst id) (i m fn bk id).



Print instr.
Print find_instr.
Print cmd.

Definition instr_check (i:option cmd) :=
  match i with
  | None => true
  | (Some (CFG.Step _)) => true
  | (Some (Term _)) => false
  end.


Lemma test1: forall blk_code pt i ins, (match find_instr blk_code pt i with
               | Some (c, _) => Some c
               | None => None
               end) = ins-> instr_check ins = true.
Proof. intros. unfold instr_check. induction blk_code; simpl in *.
       +rewrite <- H. auto.
       +destruct a. simpl in *. destruct (decide (pt = i0)); simpl in *.
        *rewrite <- H. auto.
        *apply IHblk_code. apply H. Qed.
Print compare_seq1.


Lemma test2: forall A B C,  compare_seq2
        [:: A; B]
        [:: C] -> B = C.
Proof. intros. inversion H; subst; eauto. inversion H1; subst; eauto. inversion H2. inversion H2. inversion H1. Qed.
Hint Resolve test2.

Lemma jump_correct : forall (r:Trace () -> Trace () -> Prop) o prog br2 e s bk fn pt mem,
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match (do st <- jump prog fn bk br2 e s; Jump st) with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem prog s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem prog s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m) => Vis (Eff (effects_map (step_sem prog) m))
          end
        with
        | Vis v0 => Vis (trace_map (fun _ : state => ()) <$> v0)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x0) => Vis x0
      | Vis (Err _ as x0) => Vis x0
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v0, k) => Tau () (memD m' (k v0))
          end
      | Tau x0 d' => Tau x0 (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match (do st <- jump (mcfg_opt o prog) fn bk br2 e s; Jump st) with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem (mcfg_opt o prog) s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem (mcfg_opt o prog) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m) => Vis (Eff (effects_map (step_sem (mcfg_opt o prog)) m))
          end
        with
        | Vis v0 => Vis (trace_map (fun _ : state => ()) <$> v0)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x0) => Vis x0
      | Vis (Err _ as x0) => Vis x0
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v0, k) => Tau () (memD m' (k v0))
          end
      | Tau x0 d' => Tau x0 (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. Admitted. Hint Resolve jump_correct.






Lemma add_env_false : forall id v e, add_env id v e = e -> False.
Proof. intros. unfold add_env in *. induction e.
       +inversion H.
       +inversion H. subst. apply IHe. apply H2.
Qed.

Lemma stack_false : forall a (s:stack), a :: s = s -> False.
Proof. intros. induction s. inversion H. apply IHs. inversion H. subst. rewrite H2. apply H2. Qed.



Lemma test4 : forall A B C D, compare_seq2
        [:: A; B]
        [:: C; D] -> B = D.
Proof. intros. inversion H; subst. inversion H1; subst. inversion H2. inversion H2; subst; eauto. inversion H3. inversion H3. inversion H1; subst. inversion H2; subst; eauto. inversion H2. Qed.




Lemma test3 : forall (r:Trace() -> Trace() -> Prop) e s i0 v l prog o s0 i mem fn d t blk_phis blk_id op bk id blk_code (  CIH : forall (o : instr_opt) (st : state) (mem : memory) (prog : mcfg),
        r (memD mem (sem prog st)) (memD mem (sem (mcfg_opt o prog) st))) (  H : compare_seq2
        [:: Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s)); Some (visitem mem (Err s0))]
        (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
         :: exec_code1 (mcfg_opt o prog) l
         (tauitem mem ({| fn := fn; bk := bk; pt := i0 |}, add_env id v e, s))))



(n1 : i <> IId id)
(Heqfindfunc : Some d = find_function prog fn)
(Heqfindblock : Some
                   {|
                   blk_id := blk_id;
                   blk_phis := blk_phis;
                   blk_code := (IId id, INSTR_Op op) :: blk_code;
                   blk_term := (i, t) |} = find_block (blks (df_instrs d)) bk)










  ,   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r) (Vis (trace_map (fun _ : state => ()) <$> Err s0))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem (mcfg_opt o prog)
                ({| fn := fn; bk := bk; pt := fallthrough (l ++ blk_code) i |}, add_env id v e, s))))).  
Proof. intros. induction l. simpl in *. apply test4 in H. inversion H.

       +constructor. assert (  (memD mem
       (trace_map (fun _ : state => ())
          (step_sem (mcfg_opt o prog)
             ({| fn := fn; bk := bk; pt := fallthrough ((a :: l) ++ blk_code) i |}, add_env id v e, s))))
 = unroll   (memD mem
       (trace_map (fun _ : state => ())
          (step_sem (mcfg_opt o prog)
             ({| fn := fn; bk := bk; pt := fallthrough ((a :: l) ++ blk_code) i |}, add_env id v e, s))))). destruct   (memD mem
       (trace_map (fun _ : state => ())
          (step_sem (mcfg_opt o prog)
                    ({| fn := fn; bk := bk; pt := fallthrough ((a :: l) ++ blk_code) i |}, add_env id v e, s)))); eauto. rewrite H0; clear H0. simpl in *. rewrite equiv_func1. unfold targetfunc1; unfold endfunc1. rewrite equiv_func1 in H; unfold targetfunc1 in H; unfold endfunc1 in H.

        rewrite <- Heqfindfunc in H. rewrite <- Heqfindfunc. rewrite equiv_func in H. rewrite equiv_func.
        unfold targetfunc in *. unfold endfunc in *. rewrite <- Heqfindblock. rewrite <- Heqfindblock in H. unfold block_to_cmd in *. unfold blk_term_id in *. simpl in *. destruct (decide (i = i0)); simpl in *; eauto. destruct a.
Admitted.






Lemma congruence_correct : (forall ins,  instr_opt_check ins) ->  (forall i, instr_correct i) -> forall o st mem prog, trace_equiv (memD mem (sem prog st)) (memD mem (sem (mcfg_opt o prog) st)).

 Proof.  intros  insoptcheck inscorrect.
 pcofix CIH. intros. pfold.
       assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))). destruct (memD mem (sem prog st)); eauto. rewrite H. clear H. 
assert ( (memD mem (sem (mcfg_opt o prog) st)) = unroll  (memD mem (sem (mcfg_opt o prog) st))). destruct  (memD mem (sem (mcfg_opt o prog) st)); eauto. rewrite H. clear H.



simpl in *. destruct st; destruct p; destruct p; simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. remember (find_function prog fn) as findfunc. destruct findfunc; simpl in *; eauto. simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc.
remember ( find_block (blks (df_instrs d)) bk) as findblock.  destruct findblock; simpl in *; eauto.
unfold block_opt. simpl in *. unfold block_to_cmd. destruct b. simpl in *. unfold blk_term_id in *.
simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt)); simpl in *; eauto. admit.

unfold code_opt. destruct blk_code. simpl in *. eauto.

generalize e.
generalize s.
generalize mem.


generalize (inscorrect o).
intro.
generalize (insoptcheck o).
intro.
unfold instr_correct in H.
unfold instr_opt_check in H0.
specialize (H p (fn_id (df_prototype d)) blk_id prog). 
specialize (H0 p prog (fn_id (df_prototype d)) blk_id). unfold check_hd in H0.

induction (o prog (fn_id (df_prototype d)) blk_id p); simpl in *; eauto.


destruct p. simpl in *. intros.
specialize (H mem0  ({| fn := fn; bk := bk; pt := pt |}, e0, s0)).
simpl in *.
rewrite <- Heqfindfunc in H.
rewrite <- Heqfindblock in H.
unfold block_to_cmd in H. unfold blk_term_id in *.
simpl in *. destruct ( decide (i = pt)); simpl in *; eauto. admit.


destruct (decide (pt = i0)); simpl in *; eauto. destruct pt, i1; simpl in *; eauto; subst.
destruct ( eval_op e0 None op); simpl in *; eauto; try apply test2 in H; try inversion H; subst.

admit. admit. admit.
admit. admit. admit.
admit. admit. admit.
admit. admit. admit.
admit. admit. admit.
admit. admit. admit.
admit. admit. admit.
admit. admit.


destruct p, a. simpl in *. subst.
intros.
destruct ( decide (pt = i2)); simpl in *.

(*h*) admit.


intros. apply IHl. 