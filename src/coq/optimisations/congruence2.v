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

Fixpoint code_opt (o:opt) (m:mcfg) (c:code) (bk:block_id) (fn:function_id) : code :=
  match c with
  | nil => nil
  | (iid, ins) :: tl => (o (mk_pc fn bk iid) m ins) ::  (code_opt o m tl bk fn)
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
Print pc.
Definition mk_pc (fn:function_id) (bk:block_id) (pt:instr_id) := mk_pc fn bk pt.


Definition correct_instr m o fid bid := forall mem s e iid i, compare_exec m (modul_opt o m) (cons (iid, i) nil) (cons (o (mk_pc fid bid iid) m i) nil) mem (mk_state (mk_pc fid bid iid) e s).

Definition same_hd_instr (o:opt) (i:instr) (m:mcfg) fid iid bid := fst (o (mk_pc fid bid iid) m i) = iid.


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



Lemma test : forall d m fn, (Some d = find_function m fn) -> fn =  function_id_of_dec (df_prototype d).
Proof. intros. unfold function_id_of_dec. simpl in *. unfold find_function in H. destruct m. simpl in *. induction m_definitions; simpl in *. inversion H.



       +unfold find_defn in *. simpl in *. destruct ( decide (AstLib.ident_of a = ID_Global fn)). simpl in *. inversion e. inversion H. subst. auto. apply IHm_definitions. apply H. Qed.






Lemma test1 : forall b d bk, Some b = find_block (blks (df_instrs d)) bk -> (blk_id b) = bk.
Proof. intros. destruct d. simpl in *. destruct df_instrs. simpl in *. induction blks; simpl in *.
       +inversion H.
       +simpl in *. destruct ( decide (blk_id a = bk)); simpl in *.
       -inversion e. inversion H. subst. auto.
        -apply IHblks. destruct blks. simpl in *. auto. simpl in *. destruct ( decide (blk_id b0 = bk)); subst; simpl in *. auto. auto. Qed.

Print same_hd_instr.

Lemma jump_equiv : forall o m (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)  (r:Trace()->Trace()->Prop) mem pt bk  (d:definition cfg) br1 e s  (  CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st))),


    trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do st <- jump m (function_id_of_dec (df_prototype d)) bk br1 e s; Jump st)
          with
          | Step s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
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
          match
            (do st <- jump (modul_opt o m) (function_id_of_dec (df_prototype d)) bk br1 e s;
             Jump st)
          with
          | Step s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
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
Proof. intros. unfold jump. simpl in *. unfold find_block_entry. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct ( find_function m (function_id_of_dec (df_prototype d))); simpl in *; eauto. rewrite equiv_func. unfold targetfunc. unfold endfunc. 
destruct ( find_block (blks (df_instrs d0)) br1); simpl in *; eauto. unfold monad_fold_right. simpl in *. remember ( (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
                  end)) as A. rewrite <- HeqA. destruct A; simpl in *; eauto. unfold blk_entry_pc. simpl in *. unfold blk_entry_id. simpl in *. destruct blk_code; simpl in *; eauto. simpl in *. destruct p. unfold blk_term_id in *. simpl in *. unfold same_hd_instr in same_instr. unfold mk_pc in *.
destruct b. simpl in *.
specialize (same_instr i0 (function_id_of_dec (df_prototype d0)) blk_id i).
destruct (o {| fn := function_id_of_dec (df_prototype d0); bk := blk_id; pt := i |} m i0). simpl in *; subst. eauto. Qed.
Hint Resolve jump_equiv.






Lemma term_eq : forall  o m (same_hd: forall i fid bid iid, same_hd_instr o i m fid iid bid) (r:Trace()->Trace()->Prop) t e s (d:definition cfg) bk pt mem
 (  CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st))),  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            match t with
            | TERM_Ret (t0, op) =>
                do dv <- eval_op e (Some t0) op;
                match s with
                | [::] => Obs (Fin dv)
                | KRet e' id p' :: k' => Jump (p', add_env id dv e', k')
                | KRet_void _ _ :: _ =>
                    t_raise_p
                      {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret op in non-return configuration"
                end
            | TERM_Ret_void =>
                match s with
                | [::] => Obs (Fin (DV (VALUE_Bool true)))
                | KRet _ _ _ :: _ =>
                    t_raise_p
                      {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret void in non-return configuration"
                | KRet_void e' p' :: k' => Jump (p', e', k')
                end
            | TERM_Br (t0, op) br1 br2 =>
                do dv <- eval_op e (Some t0) op;
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
                end; do st <- jump m (function_id_of_dec (df_prototype d)) bk br e s; Jump st
            | TERM_Br_1 br =>
                do st <- jump m (function_id_of_dec (df_prototype d)) bk br e s; Jump st
            | TERM_Switch _ _ _ => t_raise "Unsupport LLVM terminator"
            | TERM_IndirectBr _ _ => t_raise "Unsupport LLVM terminator"
            | TERM_Resume _ => t_raise "Unsupport LLVM terminator"
            | TERM_Invoke _ _ _ _ => t_raise "Unsupport LLVM terminator"
            end
          with
          | Step s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            match t with
            | TERM_Ret (t0, op) =>
                do dv <- eval_op e (Some t0) op;
                match s with
                | [::] => Obs (Fin dv)
                | KRet e' id p' :: k' => Jump (p', add_env id dv e', k')
                | KRet_void _ _ :: _ =>
                    t_raise_p
                      {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret op in non-return configuration"
                end
            | TERM_Ret_void =>
                match s with
                | [::] => Obs (Fin (DV (VALUE_Bool true)))
                | KRet _ _ _ :: _ =>
                    t_raise_p
                      {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret void in non-return configuration"
                | KRet_void e' p' :: k' => Jump (p', e', k')
                end
            | TERM_Br (t0, op) br1 br2 =>
                do dv <- eval_op e (Some t0) op;
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
                end;
                do st <- jump (modul_opt o m) (function_id_of_dec (df_prototype d)) bk br e s;
                Jump st
            | TERM_Br_1 br =>
                do st <- jump (modul_opt o m) (function_id_of_dec (df_prototype d)) bk br e s;
                Jump st
            | TERM_Switch _ _ _ => t_raise "Unsupport LLVM terminator"
            | TERM_IndirectBr _ _ => t_raise "Unsupport LLVM terminator"
            | TERM_Resume _ => t_raise "Unsupport LLVM terminator"
            | TERM_Invoke _ _ _ _ => t_raise "Unsupport LLVM terminator"
            end
          with
          | Step s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := pt |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end

. Proof. intros. destruct t; simpl in *; eauto.
         +destruct v; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct s; simpl in *; eauto. destruct f; simpl in *; eauto.
         +destruct s; simpl in *; eauto. destruct f; simpl in *; eauto. destruct v; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto.
         +destruct v0; simpl in *; eauto. destruct ( StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; eauto. Qed.



Hint Resolve term_eq.




Lemma first_case : forall o (m:mcfg) (r:Trace()-> Trace()->Prop) A e op i (d:definition cfg) s (r:Trace()->Trace()->Prop) bk blk_code id mem (  CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
(  H1 : compare_trace
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin (visitem mem (Err A))))
), 
trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough blk_code i |}, add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem m s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e1) =>
          match mem_step e1 mem with
          | inl e2 => Vis (Eff e2)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    (Vis
       (trace_map (fun _ : state => ()) <$> Err A)).
Proof.  intros. destruct ( eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. Qed.
Hint Resolve first_case.

Lemma second_case : forall (r:Trace()->Trace()->Prop) (d:definition cfg) i e A args s id bk mem blk_code (fn: tident) o m
(  CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
    (H1 : compare_trace
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <-
                 map_monad (fun '(t, op) => eval_op e (Some t) op)
                   args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := i |} :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) 
               (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) 
               (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s))
               (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s))
               (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
                   (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IId id |} e s))
            (fin (visitem mem (Err A))))),


    trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
   match
     match
       match
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <-
                 map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := fallthrough blk_code i |} :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             Tau
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := IId id |}, e, s) (step_sem m s')
         | Jump s' =>
             Tau
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := IId id |}, e, s) (step_sem m s')
         | Obs (Fin s0) => Vis (Fin s0)
         | Obs (Err s0) => Vis (Err s0)
         | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
         end
       with
       | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
       | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
       end
     with
     | Vis (Fin _ as x) => Vis x
     | Vis (Err _ as x) => Vis x
     | Vis (Eff e1) =>
         match mem_step e1 mem with
         | inl e2 => Vis (Eff e2)
         | inr (m', v, k) => Tau () (memD m' (k v))
         end
     | Tau x d' => Tau x (memD mem d')
     end
   with
   | Vis a => Vis a
   | Tau a b => Tau a b
   end
   (Vis (trace_map (fun _ : state => ()) <$> Err A))
.
Proof. intros. destruct fn; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto.
       destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. Qed.
Hint Resolve second_case.

Print same_hd_instr.

Lemma third_case :  forall o m (same_hd : forall i fid bid iid, same_hd_instr o i m fid iid bid) (r:Trace()->Trace()->Prop) (d:definition cfg) i op0 e s op bk blk_code id mem  (  CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))

(   H1 : compare_trace
         match
           (do dv <- eval_op e None op0;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}, 
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                         s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                         s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}, 
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                         s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                         s)) (fin (tauitem m' (k v)))
             end
         end

)


    ,


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op0;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough blk_code i |}, add_env id dv e, s))
          with
          | Step s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough (code_opt o m blk_code bk (function_id_of_dec (df_prototype d)))
                        i |}, add_env id dv e, s))
          with
          | Step s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof.  intros. destruct ( eval_op e None op0), (eval_op e None op); simpl in *; eauto; try apply mini_trace_implies_double in H1. inversion H1. inversion H1. inversion H1.
destruct blk_code; simpl in *; eauto.  destruct p. 
specialize (same_hd i1 (function_id_of_dec (df_prototype d)) bk i0). unfold same_hd_instr in *. unfold mk_pc in *. destruct  (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto. Qed.
Hint Resolve third_case.

Lemma fourth_case : forall (r:Trace()->Trace()->Prop) e op (d:definition cfg) (fn:tident) id s i m o args bk blk_code mem
  (  CIH : forall  (st : state) (mem : memory),
      r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (H1 : compare_trace
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end)
  ,
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough blk_code i |}, add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough
                              (code_opt o m blk_code bk (function_id_of_dec (df_prototype d)))
                              i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct (eval_op e None op), fn; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct   (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto.
       -apply mini_trace_implies_double in H1. inversion H1.
       -destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. 
 apply mini_trace_implies_double in H1. inversion H1. symmetry in H3; apply false_stack in H3; inversion H3. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve fourth_case.

Lemma fifth_case : forall (r:Trace()->Trace()->Prop) id e s mem bk i A m blk_code (d:definition cfg)
  (  H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                  s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
         (step_trace.tau
            (tauitem mem
               (mk_state {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                  s)) (fin (visitem mem (Err A))))
),
   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
   (Tau ()
      (memD (mem ++ [:: undef])%list
         (trace_map (fun _ : state => ())
            (step_sem m
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough blk_code i |},
               add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
   (Vis
      (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. apply mini_trace_implies_double in H1; inversion H1. Qed.
Hint Resolve fifth_case.

Lemma sixth_case : forall A (r:Trace()->Trace()->Prop) e i (d:definition cfg) s o m (ptr0: tvalue) bk id blk_code mem
       (  CIH : forall  (st : state) (mem : memory),
      r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
                     
(  H1 : compare_trace
         match
           (let (u, ptr) := ptr0 in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := i |}, add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IId id |} e s))
            (fin (visitem mem (Err A)))))
  ,
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (u, ptr1) := ptr0 in
             do dv <- eval_op e (Some u) ptr1;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, 
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem m s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    (Vis (trace_map (fun _ : state => ()) <$> Err A))


.
Proof. intros. destruct ptr0. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.

Hint Resolve sixth_case.

Lemma eighth_case : forall (r:Trace()->Trace()->Prop) e op i (d:definition cfg) A m o s bk blk_code id mem
    (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IId id |} e s))
            (fin (visitem mem (Err A))))
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end)        (  CIH : forall (st : state) (mem : memory),
      r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
,
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough
                        (code_opt o m blk_code bk
                           (function_id_of_dec (df_prototype d))) i |},
               add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.

Proof. intros. destruct ( eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed. Hint Resolve eighth_case.


Lemma ninth_case : forall (ptr: tvalue) (r:Trace()->Trace()->Prop) A mem s id blk_code bk o m e (d:definition cfg) i (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IId id |} e s))
            (fin (visitem mem (Err A))))
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := i |}, add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end)  (  CIH : forall (st : state) (mem : memory),
      r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
,   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    match
      match
        match
          match
            (let (u, ptr1) := ptr in
             do dv <- eval_op e (Some u) ptr1;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros.  destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto.  destruct v0; simpl in *; eauto.  apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve ninth_case.


Lemma tenth_case : forall (r:Trace()->Trace()->Prop) A (ptr:tvalue) (val:tvalue) mem n0 blk_code bk e i (d:definition cfg) m s o (CIH : forall (st : state) (mem : memory),
                                                                                                                                       r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))

    (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IVoid n0 |} e s))
            (fin (visitem mem (Err A))))
         match
           (let (t, val) := val in
            let (u, ptr) := ptr in
            do dv <- eval_op e (Some t) val;
            do v <- eval_op e (Some u) ptr;
            match v with
            | DV _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Store a dv
                        (fun _ : value =>
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := i |}, e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end),



  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis
       (trace_map (fun _ : state => ()) <$>
        Err A))
    match
      match
        match
          match
            (let (t0, val0) := val in
             let (u, ptr0) := ptr in
             do dv <- eval_op e (Some t0) val0;
             do v <- eval_op e (Some u) ptr0;
             match v with
             | DV _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ =>
                 t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |},
                          e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. destruct val, ptr. destruct ( eval_op e (Some t) v), (eval_op e (Some t0) v0); simpl in *; eauto. destruct v2; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve tenth_case.




Lemma eleventh_case : forall A (r:Trace()->Trace()->Prop) o m args e i (d:definition cfg) s id bk mem blk_code (fn:tident)
 (  CIH : forall (st : state) (mem : memory),
                                                                                                                                       r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IId id |} e s))
            (fin (visitem mem (Err A))))
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := i |} :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IId id |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end)


  , trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
   (Vis
      (trace_map (fun _ : state => ()) <$> Err A))
   match
     match
       match
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <-
                 map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := fallthrough
                             (code_opt o m blk_code bk
                                (function_id_of_dec (df_prototype d))) i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             Tau
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
         | Jump s' =>
             Tau
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
         | Obs (Fin s0) => Vis (Fin s0)
         | Obs (Err s0) => Vis (Err s0)
         | Obs (Eff m1) =>
             Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
         end
       with
       | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
       | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
       end
     with
     | Vis (Fin _ as x) => Vis x
     | Vis (Err _ as x) => Vis x
     | Vis (Eff e1) =>
         match mem_step e1 mem with
         | inl e2 => Vis (Eff e2)
         | inr (m', v, k) => Tau () (memD m' (k v))
         end
     | Tau x d' => Tau x (memD mem d')
     end
   with
   | Vis a => Vis a
   | Tau a b => Tau a b
   end
.
Proof. intros. destruct fn; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve eleventh_case.


Lemma twelth_case : forall (r:Trace() -> Trace() -> Prop) A (fn:tident) args mem blk_code bk n0 o m e s (d:definition cfg) i
   ( H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IVoid n0 |} e s))
            (fin (visitem mem (Err A))))
         match
           (let (ret_ty, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 match ret_ty with
                 | TYPE_I _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Void =>
                     Step
                       (pc_f, combine ids dvs,
                       KRet_void e
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := i |} :: s)
                 | TYPE_Half => t_raise "Call mismatch void/non-void"
                 | TYPE_Float => t_raise "Call mismatch void/non-void"
                 | TYPE_Double => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                 | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                 | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                 | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                 end
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                    {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis
       (trace_map (fun _ : state => ()) <$>
        Err A))
    match
      match
        match
          match
            (let (ret_ty, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <-
                  map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e
                          {|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := fallthrough
                                  (code_opt o m blk_code bk
                                     (function_id_of_dec (df_prototype d))) i |}
                        :: s)
                  | TYPE_Half => t_raise "Call mismatch void/non-void"
                  | TYPE_Float => t_raise "Call mismatch void/non-void"
                  | TYPE_Double => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                  | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                  | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                  | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                  end
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct fn; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve twelth_case.


Lemma thirteenth_case : forall A m (r:Trace()->Trace()->Prop) args e i (d:definition cfg) mem blk_code bk (fn:tident)  n0 s   (H1 : compare_trace
         match
           (let (ret_ty, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 match ret_ty with
                 | TYPE_I _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Void =>
                     Step
                       (pc_f, combine ids dvs,
                       KRet_void e
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := i |} :: s)
                 | TYPE_Half => t_raise "Call mismatch void/non-void"
                 | TYPE_Float => t_raise "Call mismatch void/non-void"
                 | TYPE_Double => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                 | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                 | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                 | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                 end
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {|
                     fn := function_id_of_dec (df_prototype d);
                     bk := bk;
                     pt := IVoid n0 |} e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {|
                  fn := function_id_of_dec (df_prototype d);
                  bk := bk;
                  pt := IVoid n0 |} e s))
            (fin (visitem mem (Err A))))),

    
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (ret_ty, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <-
                  map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e
                          {|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := fallthrough blk_code i |} :: s)
                  | TYPE_Half => t_raise "Call mismatch void/non-void"
                  | TYPE_Float => t_raise "Call mismatch void/non-void"
                  | TYPE_Double => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                  | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                  | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                  | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                  end
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s) (step_sem m s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    (Vis
       (trace_map (fun _ : state => ()) <$>
        Err A))
.
Proof. intros. destruct fn; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct  (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct  (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve thirteenth_case.
(*HERE*)




Lemma fourteenth_case : forall (r:Trace()->Trace()->Prop) A (val:tvalue) (ptr:tvalue) mem blk_code bk e i (d:definition cfg) s m n0 (H1 : compare_trace
         match
           (let (t, val) := val in
            let (u, ptr) := ptr in
            do dv <- eval_op e (Some t) val;
            do v <- eval_op e (Some u) ptr;
            match v with
            | DV _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Store a dv
                        (fun _ : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |} e s))
            (fin (visitem mem (Err A))))),


   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (t0, val0) := val in
             let (u, ptr0) := ptr in
             do dv <- eval_op e (Some t0) val0;
             do v <- eval_op e (Some u) ptr0;
             match v with
             | DV _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end (Vis (trace_map (fun _ : state => ()) <$> Err A))
.

Proof. intros. destruct val, ptr; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct ( eval_op e (Some t0) v0); simpl in *; eauto. destruct v2; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.


Hint Resolve fourteenth_case.



Lemma fiftheenth_case : forall i A (d:definition cfg) m o e mem s bk id blk_code (r:Trace () -> Trace () -> Prop)   (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin (visitem mem (Err A))))
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                   add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),

    
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough
                         (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))

. Proof. intros. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve fiftheenth_case.



Lemma sixteenth_case : forall (r:Trace()->Trace()->Prop) (d:definition cfg) mem id blk_code bk op s o i m e   ( H1 : compare_trace
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))

  ,

      trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough blk_code i |}, add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough
                         (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))

.

Proof. intros. destruct ( eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. symmetry in H0. apply false_mem in H0. inversion H0. Qed.  Hint Resolve sixteenth_case.


Lemma seventeenth_case : forall (r:Trace () -> Trace () -> Prop) m o s op (ptr:tvalue) e i (d:definition cfg) bk blk_code id mem   (H1 : compare_trace
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end) (  CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))  (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough blk_code i |}, add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (u, ptr0) := ptr in
             do dv <- eval_op e (Some u) ptr0;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct ( eval_op e None op), ptr; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct ( eval_op e (Some t) v0); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1.

       destruct blk_code; simpl in *; eauto. destruct p. simpl in *. unfold same_hd_instr in same_instr. specialize (same_instr i1 (function_id_of_dec (df_prototype d)) bk i0). unfold mk_pc in *. destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve seventeenth_case.


Lemma eighteenth_case : forall op (r:Trace() -> Trace() -> Prop) m (fn:tident) e i mem blk_code bk id (d:definition cfg) o s args (  H1 : compare_trace
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough
                        (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
               add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
. Proof. intros. destruct fn. destruct i0, ( eval_op e None op); simpl in *; eauto.
         destruct (find_function_entry m id0); simpl in *; eauto.
         destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct  (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. apply false_stack in H3. inversion H3.  apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve eighteenth_case.





 Print same_hd_instr.


Lemma ninteenth_case : forall (r:Trace()->Trace()->Prop) blk_code o m op e i (d:definition cfg) s mem bk id (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough
                        (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
               add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
  Proof. intros. destruct ( eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply false_mem in H0. inversion H0. Qed.
  Hint Resolve ninteenth_case.



  Lemma twentieth_case : forall (r:Trace()->Trace()->Prop) (ptr:tvalue) blk_code m o mem id bk s e op i (d:definition cfg) (  CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)
(H1 : compare_trace
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (do dv <- eval_op e None op;
            Step
              ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
              add_env id dv e, s))
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (u, ptr0) := ptr in
             do dv <- eval_op e (Some u) ptr0;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step
               ({|
                fn := function_id_of_dec (df_prototype d);
                bk := bk;
                pt := fallthrough
                        (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
               add_env id dv e, s))
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct ptr. destruct ( eval_op e (Some t) v), ( eval_op e None op); simpl in *; eauto.
       +apply mini_trace_implies_double in H1. inversion H1.
       +destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1.
        destruct blk_code; simpl in *; eauto. destruct p. simpl in *. unfold same_hd_instr in *.
        unfold mk_pc in *. specialize (same_instr i1 ( function_id_of_dec (df_prototype d)) bk i0). destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. Qed.
Hint Resolve twentieth_case.



Lemma twenty_first_case : forall (r:Trace()->Trace()->Prop) blk_code m o args args0 e i (fn:tident) id bk mem (d:definition cfg) s (fn0:tident) (CIH : forall(st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)
 (H1 : compare_trace
         match
           (let (_, i0) := fn0 in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args0;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (_, i0) := fn0 in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough
                              (code_opt o m blk_code bk (function_id_of_dec (df_prototype d)))
                              i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
. Proof. intros. destruct fn0, fn. destruct i0, i1; simpl in *; eauto. destruct  (find_function_entry m id0); simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f, f0; simpl in *; eauto. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args0), (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
         +apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1.

destruct blk_code in *; eauto; simpl in *. destruct p1. simpl in *. unfold same_hd_instr in *. unfold mk_pc in *. specialize (same_instr i1 (function_id_of_dec (df_prototype d)) bk i0). 
destruct  (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto.
 destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args0); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args0); simpl in *; eauto. destruct  (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct    (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.
Hint Resolve twenty_first_case.




Lemma twenty_second_case : forall (r:Trace()->Trace()->Prop) (fn:tident) blk_code id bk mem s (d:definition cfg) i e args o m (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough
                              (code_opt o m blk_code bk (function_id_of_dec (df_prototype d)))
                              i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end. Proof. intros. destruct fn. destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. symmetry in H4. apply false_stack in H4. inversion H4. Qed.
Hint Resolve twenty_second_case.


Lemma twenty_third_case : forall (r:Trace()->Trace()->Prop) blk_code m o args e i (d:definition cfg) s (ptr:tvalue) (fn:tident) bk mem id (H1 : compare_trace
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (u, ptr0) := ptr in
             do dv <- eval_op e (Some u) ptr0;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough
                              (code_opt o m blk_code bk (function_id_of_dec (df_prototype d)))
                              i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct ptr, fn; simpl in *; eauto. destruct i0, ( eval_op e (Some t) v); simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v0, (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.  apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1.  symmetry in H3. apply false_stack in H3. inversion H3.  apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed.

Hint Resolve twenty_third_case.

Lemma twenty_fourth_case : forall (r:Trace()->Trace()->Prop) blk_code o bk (fn:tident) mem id args m s e i (d:definition cfg) (H1 : compare_trace
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                   add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),
    trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough
                         (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
                 add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))).
Proof. intros. destruct fn; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply false_stack in H4.  inversion H4. Qed.  Hint Resolve twenty_fourth_case.

Lemma twenty_fifth_case : forall (r:Trace()->Trace()->Prop) blk_code i o m (d:definition cfg) e id bk mem s (  CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
                                 (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)
 (H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                   add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough
                         (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
. Proof. intros. apply mini_trace_implies_double in H1. inversion H1.
destruct blk_code; simpl in *; eauto. destruct p; simpl in *. unfold same_hd_instr in *. unfold mk_pc in *. specialize (same_instr i1 (function_id_of_dec (df_prototype d)) bk i0). destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto. Qed.
Hint Resolve twenty_fifth_case.


Lemma twenty_sixth_case : forall (r:Trace()->Trace()->Prop) blk_code (ptr:tvalue) o m mem id bk s i (d:definition cfg) e (H1 : compare_trace
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                   add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (u, ptr0) := ptr in
             do dv <- eval_op e (Some u) ptr0;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough
                         (code_opt o m blk_code bk (function_id_of_dec (df_prototype d))) i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))

.
Proof. intros. destruct ptr. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. symmetry in H0. apply false_mem in H0.  inversion H0. Qed.
Hint Resolve twenty_sixth_case.

Lemma twenty_seventh_case : forall blk_code (r:Trace()->Trace()->Prop) o mem bk id (fn:tident) args m s (d:definition cfg) i e (ptr:tvalue) (H1 : compare_trace
         match
           (let (_, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 Step
                   (pc_f, combine ids dvs,
                   KRet e id {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                   :: s)
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (_, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id
                      {|
                      fn := function_id_of_dec (df_prototype d);
                      bk := bk;
                      pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (u, ptr0) := ptr in
             do dv <- eval_op e (Some u) ptr0;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct fn, ptr; simpl in *; eauto. destruct i0, ( eval_op e (Some t0) v); simpl in *; eauto. destruct  (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct v0; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1. apply false_stack in H3. inversion H3. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed. 


Hint Resolve twenty_seventh_case.


Lemma twenty_eighth_case: forall (r:Trace()->Trace()->Prop) (ptr:tvalue) e s id o m blk_code bk mem (d:definition cfg) i (  H1 : compare_trace
         (step_trace.tau
            (tauitem mem
               (mk_state
                  {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e s))
            (fin
               (tauitem (mem ++ [:: undef])%list
                  ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                  add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),
    trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({|
                 fn := function_id_of_dec (df_prototype d);
                 bk := bk;
                 pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    match
      match
        match
          match
            (let (u, ptr0) := ptr in
             do dv <- eval_op e (Some u) ptr0;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
  Proof. intros. destruct ptr. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply false_mem in H0. inversion H0. Qed.
Hint Resolve twenty_eighth_case.

Lemma twenty_ninth_case : forall (r:Trace()->Trace()->Prop) blk_code m s o (d:definition cfg) i e mem id bk (ptr0:tvalue) (ptr:tvalue) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)
 (H1 : compare_trace
         match
           (let (u, ptr) := ptr0 in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (u, ptr) := ptr in
            do dv <- eval_op e (Some u) ptr;
            match dv with
            | DV _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Load a
                        (fun dv0 : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         add_env id dv0 e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |} e
                     s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IId id |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (u, ptr1) := ptr0 in
             do dv <- eval_op e (Some u) ptr1;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (u, ptr1) := ptr in
             do dv <- eval_op e (Some u) ptr1;
             match dv with
             | DV _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Load a
                         (fun dv0 : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IId id |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. destruct ptr0, ptr. destruct ( eval_op e (Some t0) v0), ( eval_op e (Some t) v); simpl in *; eauto. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct v2; simpl in *; eauto. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1.
       destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1.
       apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. unfold same_hd_instr in *. unfold mk_pc in *.
destruct blk_code; simpl in *; eauto. destruct p. simpl in *. specialize (same_instr i1 (function_id_of_dec (df_prototype d)) bk i0). destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto.



apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. apply mini_trace_implies_double in H1; inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1.
Qed.

Hint Resolve twenty_ninth_case.


Lemma thirtieth_case : forall (r:Trace()->Trace()->Prop) (fn:tident) (fn0:tident) blk_code mem bk n0 s (d:definition cfg) e i m o args args0
                              (  CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)
(H1 : compare_trace
         match
           (let (ret_ty, i0) := fn0 in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args0;
                 match ret_ty with
                 | TYPE_I _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Void =>
                     Step
                       (pc_f, combine ids dvs,
                       KRet_void e
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                       :: s)
                 | TYPE_Half => t_raise "Call mismatch void/non-void"
                 | TYPE_Float => t_raise "Call mismatch void/non-void"
                 | TYPE_Double => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                 | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                 | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                 | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                 end
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (ret_ty, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 match ret_ty with
                 | TYPE_I _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Void =>
                     Step
                       (pc_f, combine ids dvs,
                       KRet_void e
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                       :: s)
                 | TYPE_Half => t_raise "Call mismatch void/non-void"
                 | TYPE_Float => t_raise "Call mismatch void/non-void"
                 | TYPE_Double => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                 | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                 | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                 | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                 end
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end), 
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (ret_ty, i0) := fn0 in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e
                          {|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := fallthrough blk_code i |} :: s)
                  | TYPE_Half => t_raise "Call mismatch void/non-void"
                  | TYPE_Float => t_raise "Call mismatch void/non-void"
                  | TYPE_Double => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                  | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                  | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                  | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                  end
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (ret_ty, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e
                          {|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := fallthrough
                                  (code_opt o m blk_code bk
                                     (function_id_of_dec (df_prototype d))) i |} :: s)
                  | TYPE_Half => t_raise "Call mismatch void/non-void"
                  | TYPE_Float => t_raise "Call mismatch void/non-void"
                  | TYPE_Double => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                  | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                  | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                  | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                  end
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. destruct fn0, fn; simpl in *; eauto. destruct i0, i1; simpl in *; eauto. destruct  (find_function_entry m id),  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f, f0; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), 
( map_monad (fun '(t, op) => eval_op e (Some t) op) args0); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct t0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct t, t0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.




destruct blk_code; simpl in *; eauto. destruct p1; simpl in *.
unfold same_hd_instr in *. unfold mk_pc in *.
specialize (same_instr i1 (function_id_of_dec (df_prototype d)) bk i0). 
destruct  (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
 apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args0); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1.
destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t0; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. destruct  (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto.

destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto.
destruct t; simpl in *; eauto.
apply mini_trace_implies_double in H1. inversion H1.
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto.
destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto.  destruct f; simpl in *; eauto. destruct t0; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. Qed. 

Hint Resolve thirtieth_case.


Lemma thirty_first_case : forall (r:Trace()->Trace()->Prop) blk_code (val:tvalue) (ptr:tvalue) (fn:tident) mem bk n0 s (d:definition cfg) i e args o m (H1 : compare_trace
         match
           (let (t, val) := val in
            let (u, ptr) := ptr in
            do dv <- eval_op e (Some t) val;
            do v <- eval_op e (Some u) ptr;
            match v with
            | DV _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Store a dv
                        (fun _ : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (ret_ty, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid)
                  (find_function_entry (modul_opt o m) fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 match ret_ty with
                 | TYPE_I _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Void =>
                     Step
                       (pc_f, combine ids dvs,
                       KRet_void e
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                       :: s)
                 | TYPE_Half => t_raise "Call mismatch void/non-void"
                 | TYPE_Float => t_raise "Call mismatch void/non-void"
                 | TYPE_Double => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                 | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                 | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                 | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                 end
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (t0, val0) := val in
             let (u, ptr0) := ptr in
             do dv <- eval_op e (Some t0) val0;
             do v <- eval_op e (Some u) ptr0;
             match v with
             | DV _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (ret_ty, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e
                          {|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := fallthrough
                                  (code_opt o m blk_code bk
                                     (function_id_of_dec (df_prototype d))) i |} :: s)
                  | TYPE_Half => t_raise "Call mismatch void/non-void"
                  | TYPE_Float => t_raise "Call mismatch void/non-void"
                  | TYPE_Double => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                  | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                  | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                  | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                  end
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.

Proof. intros. destruct val, ptr, fn; simpl in *; eauto. destruct ( eval_op e (Some t) v), i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct (eval_op e (Some t0) v0); simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto.
       destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
       destruct t1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       destruct v2,  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. apply mini_trace_implies_double in H1. inversion H1.
       apply mini_trace_implies_double in H1. inversion H1. symmetry in H4. apply false_stack in H4. inversion H4.
       apply mini_trace_implies_double in H1. inversion H1.
       apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.
apply mini_trace_implies_double in H1. inversion H1.

destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
destruct t1; simpl in *; eauto.
apply mini_trace_implies_double in H1. inversion H1.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
destruct t1; simpl in *; eauto.
apply mini_trace_implies_double in H1. inversion H1.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
destruct t1; simpl in *; eauto.
apply mini_trace_implies_double in H1. inversion H1.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
destruct t1; simpl in *; eauto.
apply mini_trace_implies_double in H1. inversion H1.
destruct ( eval_op e (Some t0) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
apply mini_trace_implies_double in H1. inversion H1.
Qed. Hint Resolve thirty_first_case.




Lemma thirty_second_case : forall (r:Trace()->Trace()->Prop) blk_code o (ptr:tvalue) (val:tvalue) mem bk (fn:tident) args m n0 s (d:definition cfg) i e (H1 : compare_trace
         match
           (let (ret_ty, i0) := fn in
            match i0 with
            | ID_Global fid =>
                do fnentry <-
                trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                let
                'FunctionEntry ids pc_f := fnentry in
                 do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                 match ret_ty with
                 | TYPE_I _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Void =>
                     Step
                       (pc_f, combine ids dvs,
                       KRet_void e
                         {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |}
                       :: s)
                 | TYPE_Half => t_raise "Call mismatch void/non-void"
                 | TYPE_Float => t_raise "Call mismatch void/non-void"
                 | TYPE_Double => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                 | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                 | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                 | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                 | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                 | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                 | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                 end
            | ID_Local _ => t_raise "INSTR_Call to local"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (t, val) := val in
            let (u, ptr) := ptr in
            do dv <- eval_op e (Some t) val;
            do v <- eval_op e (Some u) ptr;
            match v with
            | DV _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Store a dv
                        (fun _ : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (ret_ty, i0) := fn in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid) (find_function_entry m fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e
                          {|
                          fn := function_id_of_dec (df_prototype d);
                          bk := bk;
                          pt := fallthrough blk_code i |} :: s)
                  | TYPE_Half => t_raise "Call mismatch void/non-void"
                  | TYPE_Float => t_raise "Call mismatch void/non-void"
                  | TYPE_Double => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_fp80 => t_raise "Call mismatch void/non-void"
                  | TYPE_Fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Ppc_fp128 => t_raise "Call mismatch void/non-void"
                  | TYPE_Metadata => t_raise "Call mismatch void/non-void"
                  | TYPE_X86_mmx => t_raise "Call mismatch void/non-void"
                  | TYPE_Array _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Function _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Packed_struct _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                  | TYPE_Vector _ _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Identified _ => t_raise "Call mismatch void/non-void"
                  end
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (t0, val0) := val in
             let (u, ptr0) := ptr in
             do dv <- eval_op e (Some t0) val0;
             do v <- eval_op e (Some u) ptr0;
             match v with
             | DV _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({|
                           fn := function_id_of_dec (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m blk_code bk
                                      (function_id_of_dec (df_prototype d))) i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}, e,
                s) (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) => Vis (Eff (effects_map (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. destruct fn, val, ptr; simpl in *; eauto. destruct i0, ( eval_op e (Some t0) v), ( eval_op e (Some t1) v0); simpl in *; eauto. destruct  (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct  (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.  destruct (find_function_entry m id), v2; simpl in *; eauto. destruct f; simpl in *; eauto. 
destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.  apply mini_trace_implies_double in H1. inversion H1. 
destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1.
apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply false_stack in H4. inversion H4.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in H1; inversion H1.
 destruct f; simpl in *; eauto.
 destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
 destruct t; simpl in *; eauto.
 apply mini_trace_implies_double in H1; inversion H1.
 destruct f; simpl in *; eauto.
 destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
 destruct t; simpl in *; eauto.
 apply mini_trace_implies_double in H1; inversion H1.
 destruct f; simpl in *; eauto.
 destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto.
 destruct t; simpl in *; eauto.
 apply mini_trace_implies_double in H1; inversion H1.
 apply mini_trace_implies_double in H1; inversion H1.
 destruct v2; simpl in *; eauto.
 apply mini_trace_implies_double in H1; inversion H1.
Qed.  
 
Hint Resolve thirty_second_case.




Lemma thirty_third_case : forall (r:Trace()->Trace()->Prop) blk_code m o (ptr:tvalue) (ptr0:tvalue) (ptr:tvalue) (val0:tvalue) (  CIH : forall (st : state) (mem : memory),  r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (same_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid)
(val:tvalue) n0 s (d:definition cfg) i e bk mem (H1 : compare_trace
         match
           (let (t, val) := val0 in
            let (u, ptr) := ptr0 in
            do dv <- eval_op e (Some t) val;
            do v <- eval_op e (Some u) ptr;
            match v with
            | DV _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Store a dv
                        (fun _ : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end
         match
           (let (t, val) := val in
            let (u, ptr) := ptr in
            do dv <- eval_op e (Some t) val;
            do v <- eval_op e (Some u) ptr;
            match v with
            | DV _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Addr a =>
                Obs
                  (Eff
                     (Store a dv
                        (fun _ : value =>
                         ({| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i |},
                         e, s))))
            | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
            | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
            end)
         with
         | Step s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Jump s' =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (tauitem mem s'))
         | Obs (Fin s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Fin s')))
         | Obs (Err s') =>
             step_trace.tau
               (tauitem mem
                  (mk_state
                     {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := IVoid n0 |}
                     e s)) (fin (visitem mem (Err s')))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 fin
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s))
             | inr (m', v, k) =>
                 step_trace.tau
                   (tauitem mem
                      (mk_state
                         {|
                         fn := function_id_of_dec (df_prototype d);
                         bk := bk;
                         pt := IVoid n0 |} e s)) (fin (tauitem m' (k v)))
             end
         end),
    trace_equiv_step
    (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (t0, val1) := val0 in
             let (u, ptr1) := ptr0 in
             do dv <- eval_op e (Some t0) val1;
             do v <- eval_op e (Some u) ptr1;
             match v with
             | DV _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({|
                           fn := function_id_of_dec
                                   (df_prototype d);
                           bk := bk;
                           pt := fallthrough blk_code
                                   i |}, e, s))))
             | DVALUE_I1 _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_Poison =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec
                         (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec
                         (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) =>
              Vis (Eff (effects_map (step_sem m) m1))
          end
        with
        | Vis v =>
            Vis
              (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k =>
            Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match
            (let (t0, val1) := val in
             let (u, ptr1) := ptr in
             do dv <- eval_op e (Some t0) val1;
             do v <- eval_op e (Some u) ptr1;
             match v with
             | DV _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({|
                           fn := function_id_of_dec
                                   (df_prototype d);
                           bk := bk;
                           pt := fallthrough
                                   (code_opt o m
                                   blk_code bk
                                   (function_id_of_dec
                                   (df_prototype d)))
                                   i |}, e, s))))
             | DVALUE_I1 _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             | DVALUE_Poison =>
                 t_raise
                   "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau
                ({|
                 fn := function_id_of_dec
                         (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau
                ({|
                 fn := function_id_of_dec
                         (df_prototype d);
                 bk := bk;
                 pt := IVoid n0 |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) =>
              Vis
                (Eff
                   (effects_map
                      (step_sem (modul_opt o m)) m1))
          end
        with
        | Vis v =>
            Vis
              (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k =>
            Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e1 => Vis (Eff e1)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. destruct ptr0, ptr1, val0, val, ptr; simpl in *; eauto.
       destruct ( eval_op e (Some t1) v1), ( eval_op e (Some t) v), (eval_op e (Some t2) v2), ( eval_op e (Some t0) v0); simpl in *; eauto. destruct v4; simpl in *; eauto.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
               +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v6; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v6; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.
       +destruct v5, v7; simpl in *; eauto. apply mini_trace_implies_double in H1. inversion H1.

               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1. destruct blk_code; simpl in *; eauto. destruct p; simpl in *. unfold same_hd_instr in *. unfold mk_pc in *. specialize (same_instr i1 (function_id_of_dec (df_prototype d)) bk i0). destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1); simpl in *; subst; eauto.

               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.
               -apply mini_trace_implies_double in H1. inversion H1.

                Qed.

Hint Resolve thirty_third_case.
       
Definition correct_instr1 m o fid bid := forall mem s e iid i t, compare_exec1 m (modul_opt o m) (cons (iid, i) nil) (cons (o (mk_pc fid bid iid) m i) nil) mem (mk_state (mk_pc fid bid iid) e s) t.

(*
 Lemma correct_instr_trace1 : (forall o i m fid bid iid, same_hd_instr o i m fid iid bid) -> (forall o m fid bid, correct_instr1 m o fid bid) -> forall o m st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof. intro. intro. pcofix CIH. intros. generalize (H0 o m). intro. pfold.
       assert (  (memD mem (sem m st)) = unroll   (memD mem (sem m st))). destruct   (memD mem (sem m st)); eauto.
       rewrite H2; clear H2.

       assert ((memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))). destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H2; clear H2.

       destruct st. destruct p. destruct p. specialize (H1 fn bk). 



       unfold correct_instr1 in H1.
       specialize (H1 mem s e).  simpl in *. unfold compare_exec1 in H1. simpl in *.


      
       
       simpl in *. rewrite equiv_func1.  unfold targetfunc1 in *; unfold endfunc1 in *.
       remember ( find_function m fn) as findfunc. destruct findfunc; simpl in *; eauto.
       generalize (Heqfindfunc). intro. apply test in  Heqfindfunc0. subst. simpl in *.
     rewrite equiv_func. unfold targetfunc in *. unfold endfunc in *. remember ( find_block (blks (df_instrs d)) bk) as findblock. destruct findblock; simpl in *; eauto. generalize Heqfindblock. intros.  apply test1 in Heqfindblock0. unfold block_to_cmd in *. destruct b. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. subst. destruct (decide (i = pt)); simpl in *; subst. eauto.  

       

       

       
       clear Heqfindblock.
      induction blk_code; simpl in *; eauto. 


      destruct a. specialize (H1 i0 i1 i).




      generalize (H o i1 m (function_id_of_dec (df_prototype d)) bk i0).  intro. unfold same_hd_instr in H2.  unfold mk_pc in *. destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1). simpl in *. subst. destruct (decide (pt = i0)); subst; simpl in *.
      destruct i0, i3, i1; simpl in *; eauto. 

      apply IHblk_code. Qed.
*)


 Lemma correct_instr_trace2 : forall o m (same_hd_instr: forall i fid bid iid, same_hd_instr o i m fid iid bid) (correct_instr: forall fid bid, correct_instr1 m o fid bid) st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
 Proof. intros o m same_hd correct_instr. pcofix CIH. intros. pfold.
         assert (  (memD mem (sem m st)) = unroll   (memD mem (sem m st))). destruct   (memD mem (sem m st)); eauto.
       rewrite H; clear H.

       assert ((memD mem (sem (modul_opt o m) st)) = unroll  (memD mem (sem (modul_opt o m) st))). destruct  (memD mem (sem (modul_opt o m) st)); eauto. rewrite H; clear H.

       destruct st. destruct p. destruct p. specialize (correct_instr fn bk). 

(**)

       unfold correct_instr1 in correct_instr.
       specialize (correct_instr mem s e).  simpl in *. unfold compare_exec1 in *. simpl in *.


      
       
       simpl in *. rewrite equiv_func1.  unfold targetfunc1 in *; unfold endfunc1 in *.
       remember ( find_function m fn) as findfunc. destruct findfunc; simpl in *; eauto.
       generalize (Heqfindfunc). intro. apply test in  Heqfindfunc0. subst. simpl in *.
     rewrite equiv_func. unfold targetfunc in *. unfold endfunc in *. remember ( find_block (blks (df_instrs d)) bk) as findblock. destruct findblock; simpl in *; eauto. generalize Heqfindblock. intros.  apply test1 in Heqfindblock0. unfold block_to_cmd in *. destruct b. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. subst. destruct (decide (i = pt)); simpl in *; subst. eauto.  

       

       

       
       clear Heqfindblock.
      induction blk_code; simpl in *; eauto. 


      destruct a. specialize (correct_instr i0 i1 i).




      generalize (same_hd i1 (function_id_of_dec (df_prototype d)) bk i0). intro. unfold same_hd_instr in *.  unfold mk_pc in *. destruct (o {| fn := function_id_of_dec (df_prototype d); bk := bk; pt := i0 |} m i1). simpl in *. subst. destruct (decide (pt = i0)); subst; simpl in *.
      destruct i0, i1, i3; simpl in *; eauto. apply IHblk_code. Qed.
