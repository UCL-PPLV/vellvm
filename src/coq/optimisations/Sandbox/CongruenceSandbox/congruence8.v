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


Definition optimise_instruction (o:instr -> instr) (i:instr_id * instr) :=
  match i with
    (iid, ins) => (iid, o ins)
    end.

Definition optimise_code (o:instr -> instr) (b:code) : code := map (optimise_instruction o) b.

Print block.

Definition optimise_block (o:instr -> instr) (b:block) : block := mk_block (blk_id b) (blk_phis b) (optimise_code o (blk_code b)) (blk_term b).


Definition optimise_list_block (o:instr -> instr) (b:list block) : list block :=
  map (optimise_block o) b.


Definition optimise_cfg (o:instr ->  instr) (c:cfg) : cfg :=
  mkCFG (init c) (optimise_list_block o (blks c)) (glbl c).
Print definition.


Definition optimise_definition (o:instr -> instr) (c:definition cfg) :=
  mk_definition cfg (df_prototype c) (df_args c) (optimise_cfg o (df_instrs c)).


Definition optimise_list_definition (o:instr -> instr) (c: list (definition cfg)) :=
  map (optimise_definition o) c.


Definition optimise_modul (o:instr -> instr) (c: modul cfg) :=
  mk_modul cfg (m_name c) (m_target c) (m_datalayout c) (m_globals c) (m_declarations c) (optimise_list_definition o (m_definitions c)).

Print block.
Definition testfunc (m:mcfg) (o:instr -> instr) :=
  (forall fnid, (find_function m fnid = None /\ find_function (optimise_modul o m) fnid = None) \/ (forall cfg1 cfg2, find_function m fnid = Some cfg1 /\ find_function (optimise_modul o m) fnid = Some cfg2 /\  ( forall bkid, (CFG.find_block (convert cfg1) bkid = None /\ CFG.find_block (convert cfg2) bkid = None) \/ (forall b1 b2, CFG.find_block (convert cfg1) bkid = Some b1 /\ CFG.find_block (convert cfg2) bkid = Some b2 /\ (b1.(blk_term) = b2.(blk_term))  /\ (b1.(blk_id) = b2.(blk_id))  /\ (b1.(blk_phis) = b2.(blk_phis))

















  )))) /\


  (forall s b1 mem, compare_seq (exec_code1 m b1 (tauitem mem s)) (exec_code1 (optimise_modul o m) (optimise_code o b1)  (tauitem mem s))).




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
Lemma equiv_func2 : forall o blk_code pt i, find_instr (optimise_code o blk_code) pt i = targetfunc2 o blk_code pt i.
Proof. intros. unfold targetfunc2. unfold endfunc2. induction blk_code.
       +simpl in *. auto.
       +simpl in *. destruct a. simpl in *. destruct ( decide (pt = i0)); subst; simpl in *; eauto. destruct blk_code. simpl in *. auto. simpl in *. destruct p. simpl in *. auto. Qed.










Lemma  list_implies_head : forall (h1 h2:option (finish_item state)) t1 t2,  (h1 :: t1) = (h2 :: t2) -> h1 = h2. intros. inversion H. eauto. Qed.


Hint Resolve list_implies_head.



Lemma  compare_seq_implies_starting_state : forall p p1 blk_code blk_code0 mem s0 s1, compare_seq (exec_code1 p blk_code (tauitem mem s0))
                                                                                                  (exec_code1 p1 blk_code0 (tauitem mem s1)) -> s0 = s1.
Proof. intros. destruct blk_code, blk_code0; simpl in *; inversion H; subst.
       +inversion H3; eauto.
       +subst. destruct p0. simpl in *. destruct ( CFG_step i0 p1 s1). inversion H. inversion H5; eauto. inversion H; inversion H5; eauto. destruct m; simpl in *; inversion H; eauto. inversion H5; eauto. inversion H5; eauto. subst. destruct e; simpl in *; eauto. inversion H; simpl in *; eauto. inversion H7; eauto. inversion H; inversion H7; eauto. inversion H; inversion H7; eauto. inversion H2; eauto. destruct p0. simpl in *; eauto. destruct (CFG_step i0 p s0); eauto. simpl in *; eauto. inversion H; inversion H5; eauto. inversion H; inversion H5; eauto. destruct m; simpl in *. inversion H. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct e; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto.  inversion H; eauto. inversion H5; eauto.
        destruct p0, p2; simpl in *; eauto. destruct (CFG_step i0 p s0), (CFG_step i2 p1 s1); simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct m; simpl in *; inversion H.  inversion H5; eauto. inversion H5; eauto. induction e; simpl in *; inversion H. inversion H10; eauto. inversion H10; eauto. inversion H10; eauto.
        inversion H10; eauto. inversion H; simpl in *; eauto. inversion H5; eauto. inversion H; simpl in *; eauto. inversion H5; eauto. destruct m; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H. inversion H5; eauto. destruct e; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct m; eauto. inversion H; eauto.  inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct e; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; subst. eauto. subst. inversion H. subst. inversion H5. auto. destruct m. inversion H. subst.
        inversion H5. eauto.
        inversion H. subst. inversion H5. eauto. destruct e; simpl in *.
        rewrite H1 in H2. apply list_implies_head in H2.  inversion H2. eauto. rewrite H1 in H2. apply list_implies_head in H2. inversion H2.
        eauto. rewrite H1 in H2. apply list_implies_head in H2. inversion H2.
        eauto. rewrite H1 in H2. inversion H2. eauto. destruct m, m0. rewrite H1 in H2. apply list_implies_head in H2. inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. destruct e; simpl in *; eauto. rewrite H1 in H2. apply list_implies_head in H2. inversion H2; eauto. rewrite H1 in H2. inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2. inversion H2. eauto. rewrite H1 in H2. inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. destruct e; simpl in *; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. destruct e; simpl in *; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; simpl in *; eauto. rewrite H1 in H2. destruct e; simpl in *; inversion H2; eauto. rewrite H1 in H2; destruct e, e0; simpl in *; inversion H2; eauto. destruct p0, p2. simpl in *; eauto.
        destruct (CFG_step i0 p s0), (CFG_step i2 p1 s1). apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         destruct m; simpl in *.  apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto. 
        apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
destruct e; simpl in *; eauto.  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto. apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
          apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct m; simpl in *; eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
destruct m; simpl in *; eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

destruct e; simpl in *; eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct m; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                 apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

        destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

        destruct m, m0; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

        destruct e; simpl in *.           apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
                  apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  destruct e; simpl in *; eauto.
                                    apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

destruct e, e0; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

         Qed.









Lemma firstcase : forall (r:Trace () -> Trace () -> Prop) o mem m s s0 s1 d1 blk_code (  H1 : compare_seq
         (Some (tauitem mem s)
          :: exec_code1 m blk_code
               (tauitem mem d1))
         (Some (tauitem mem s)
          :: exec_code1 (optimise_modul o m) (optimise_code o blk_code)
               (visitem mem (Err s0)))), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem m s1 )))) (Vis (trace_map (fun _ : state => ()) <$> Err s0))
.
  Proof. Admitted. Hint Resolve firstcase.


Lemma secondcase : forall (r:Trace () -> Trace () -> Prop) o mem m s0 blk_code e s i v fn bk id

(   H1 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 m blk_code (visitem mem (Err s0)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 (optimise_modul o m) (optimise_code o blk_code)
               (tauitem mem
                  ({| fn := fn; bk := bk; pt := fallthrough (optimise_code o blk_code) i |},
                  add_env id v e, s)))),
 trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err s0))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem (optimise_modul o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v e, s)))))
.

Proof. Admitted. Hint Resolve secondcase.




Lemma thirdcase : forall (r:Trace () -> Trace () -> Prop) o mem m blk_code e s i v v0 fn bk id

(    H1 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 m blk_code
               (tauitem mem
                  ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v0 e, s)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 (optimise_modul o m) (optimise_code o blk_code)
               (tauitem mem
                  ({| fn := fn; bk := bk; pt := fallthrough (optimise_code o blk_code) i |},
                  add_env id v e, s)))
),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v0 e, s)))))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem (optimise_modul o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v e, s)))))
.
Proof. Admitted. Hint Resolve thirdcase.


Lemma fourthcase : forall (r:Trace () -> Trace () -> Prop) o mem m p l args0 blk_code e s i v fn bk id

(   H1 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 m blk_code
               (tauitem mem
                  (p, combine args0 l,
                  KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 (optimise_modul o m) (optimise_code o blk_code)
               (tauitem mem
                  ({| fn := fn; bk := bk; pt := fallthrough (optimise_code o blk_code) i |},
                  add_env id v e, s)))
),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem m
                (p, combine args0 l,
                KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)))))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem (optimise_modul o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v e, s)))))
.
Proof. Admitted. Hint Resolve fourthcase.

Lemma fifthcase :  forall (r:Trace () -> Trace () -> Prop) o mem m s0 blk_code e s i fn bk id (    H1 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 m blk_code
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 (optimise_modul o m) (optimise_code o blk_code) (visitem mem (Err s0)))
                                                                                                       ),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    (Vis (trace_map (fun _ : state => ()) <$> Err s0))
.

Proof. Admitted. Hint Resolve fifthcase.



Lemma sixthcase :   forall (r:Trace () -> Trace () -> Prop) o mem m v blk_code e s i fn bk id
                           (  H1 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 m blk_code
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 (optimise_modul o m) (optimise_code o blk_code)
               (tauitem mem
                  ({| fn := fn; bk := bk; pt := fallthrough (optimise_code o blk_code) i |},
                  add_env id v e, s)))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem (optimise_modul o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v e, s)))))

.

Proof. Admitted. Hint Resolve sixthcase.












  

Lemma Test123 : forall m o, testfunc m o -> forall st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (optimise_modul o m) st)).
Proof. intros m o test. pcofix CIH. intros. pfold.
       assert ( (memD mem (sem (optimise_modul o m) st) = unroll  (memD mem (sem (optimise_modul o m) st)))). destruct  (memD mem (sem (optimise_modul o m) st)); eauto. rewrite H; clear H.
       assert ( (memD mem (sem m st)) = unroll  (memD mem (sem m st))). destruct  (memD mem (sem m st)); eauto.
       rewrite H; clear H. simpl in *. unfold stepD.


       destruct test. generalize (H0 st). intro.


       destruct st. destruct p. destruct p. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. simpl in *. remember (find_function m fn) as findfunc. destruct findfunc. rewrite equiv_func. unfold targetfunc. unfold endfunc. remember ( find_block (blks (df_instrs d)) bk) as findblock. simpl in *. destruct findblock. simpl in *.
       unfold block_to_cmd. destruct b. unfold blk_term_id. simpl in *. specialize (H1 blk_code mem).
       destruct blk_term. simpl in *. destruct (decide (i = pt)); subst; simpl in *; eauto.

       (*term*) admit.


       rewrite equiv_func2. unfold targetfunc2. unfold endfunc2. simpl in *.


       induction blk_code; simpl in *; eauto. rewrite equiv_func1 in H1. unfold targetfunc1 in *.
       unfold endfunc1 in *. rewrite <- Heqfindfunc in H1. rewrite equiv_func in H1. unfold targetfunc in *. unfold endfunc in *. rewrite <- Heqfindblock in H1. unfold block_to_cmd in *. unfold blk_term_id in *. simpl in *.
       destruct ( decide (i = pt)); subst; simpl in *. admit. destruct a. unfold optimise_instruction in *. simpl in *. destruct ( decide (pt = i0)); simpl in *; eauto. destruct pt, (o i1), i1; simpl in *; eauto.

       destruct (eval_op e None op), (eval_op e None op0); simpl in *; eauto.
       destruct fn0, (eval_op e None op); simpl in *; eauto.
       destruct i1; simpl in *; eauto.
       destruct  (find_function_entry m id0); simpl in *; eauto.
       destruct f; simpl in *; eauto.
       destruct (map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
       destruct i1; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto.
       destruct f; simpl in *; eauto.
       destruct ( map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
       destruct ( eval_op e None op); simpl in *; eauto. destruct ptr, (eval_op e None op); simpl in *; eauto. destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto.
       destruct ( eval_op e (Some t1) v); simpl in *; eauto. destruct v1; simpl in *; eauto.
       destruct ( eval_op e None op); simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto. destruct (eval_op e None op), fn0; simpl in *; eauto. destruct i1; simpl in *; eauto. destruct  (find_function_entry (optimise_modul o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto. admit. destruct i1; simpl in *; eauto. destruct (find_function_entry (optimise_modul o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto.
       destruct ( map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
       admit. destruct fn1, fn0; simpl in *; eauto. destruct i1, i2; simpl in *; eauto.
       destruct (find_function_entry m id0),  (find_function_entry (optimise_modul o m) id1); simpl in *; eauto. destruct f, f0; simpl in *; eauto.

       destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0), ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. admit. admit. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. admit. destruct (find_function_entry m id0); simpl in *; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto. destruct  (find_function_entry (optimise_modul o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. admit. destruct fn0; simpl in *; eauto. destruct i1; simpl in *; eauto. destruct (find_function_entry (optimise_modul o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. admit. destruct ptr, fn0; simpl in *; eauto. destruct ( eval_op e (Some t1) v), i1; simpl in *; eauto. destruct ( (find_function_entry (optimise_modul o m) id0)); simpl in *; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct v0, ( (find_function_entry (optimise_modul o m) id0)); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
       admit. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. admit. destruct v0; simpl in *; eauto. destruct fn0; simpl in *; eauto. destruct i1; simpl in *; eauto. destruct  (find_function_entry (optimise_modul o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. admit. destruct fn0; simpl in *; eauto.
       destruct i1; simpl in *; eauto. destruct  (find_function_entry (optimise_modul o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. admit. destruct fn0, i1; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct fn0, ptr; simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.  admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.  admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.  admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit.  admit. admit. admit. admit. admit. admit. admit. admit. admit.



       apply IHblk_code. generalize (H0  ({| fn := fn; bk := bk; pt := pt |}, e, s) blk_code mem). intro. auto. clear IHblk_code. clear H1. generalize (H fn). intro. rewrite <- Heqfindfunc in H1. inversion H1. destruct H2. inversion H2. specialize (H2 d d). destruct H2. rewrite equiv_func1 in H3. unfold targetfunc1 in H3. unfold endfunc1 in H3. rewrite <- Heqfindfunc in H3. clear H2. destruct H3. clear H2. specialize (H3 bk). inversion H3. unfold convert in *.  rewrite <- Heqfindblock in H2. simpl in *. inversion H2. inversion H4. specialize (H2   {| blk_id := blk_id; blk_phis := blk_phis; blk_code := blk_code; blk_term := (i, t) |}   {| blk_id := blk_id; blk_phis := blk_phis; blk_code := blk_code; blk_term := (i, t) |}). simpl in *. unfold convert in H2. destruct H2. auto. simpl in *. eauto.
       simpl in *. eauto. Admitted.