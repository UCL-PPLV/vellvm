Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.congruence3_definition.
Require Import Vellvm.optimisations.congruence3_util.

Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat.

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

Print find_block_entry.
Print block_entry.

Print pc.


Print incr_pc.

Lemma jump_equiv : forall
  (mem : memory)
  (pt : instr_id)
  (bk : block_id)
  (fn : function_id)
  (o : opt)
  (m : mcfg)
  (br1 : block_id)
  (e : env)
  (s : seq frame)
  (r : Trace () -> Trace () -> Prop)
  (correct_instr : forall (fid : function_id) (bid : block_id) (mem : memory) 
                    (s : stack) (e : env) (iid : instr_id) (i : instr) 
                    (t : instr_id) (int_ins : int),
                  compare_exec1 m (modul_opt o m) [:: (iid, i)]
                    (build_opt o {| fn := fid; bk := bid; pt := iid |} m i int_ins) mem
                    (mk_state {| fn := fid; bk := bid; pt := iid |} e s) t)
  (check : forall (fid : function_id) (bid : block_id) (iid : instr_id) 
            (i : instr) (int_ins : int),
          check_size (build_opt o {| fn := fid; bk := bid; pt := iid |} m i int_ins))
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match (do st <- jump m fn bk br1 e s; Jump st) with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem m s')
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
      | Vis (Eff e1) =>
          match mem_step e1 mem with
          | inl e2 => Vis (Eff e2)
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
          match (do st <- jump (modul_opt o m) fn bk br1 e s; Jump st) with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem (modul_opt o m) s')
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
      | Vis (Eff e1) =>
          match mem_step e1 mem with
          | inl e2 => Vis (Eff e2)
          | inr (m', v0, k) => Tau () (memD m' (k v0))
          end
      | Tau x0 d' => Tau x0 (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. unfold jump. unfold find_block_entry. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct ( find_function m fn); simpl in *; eauto. rewrite equiv_func. unfold targetfunc. unfold endfunc. destruct (find_block (blks (df_instrs d)) br1); simpl in *; eauto.  unfold monad_fold_right. remember ((fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                                 (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
                  end)) as A. rewrite <- HeqA. destruct A; simpl in *; eauto. unfold blk_entry_pc. simpl in *. unfold blk_entry_id in *. simpl in *. destruct b. simpl in *. unfold blk_term_id in *. simpl in *. unfold function_id_of_dec. simpl in *.  unfold code_opt. simpl in *. destruct blk_code. simpl in *. eauto. simpl in *. destruct p. unfold build_opt in *. simpl in *.
unfold create_code in *. simpl in *. unfold mkpc in *. unfold compare_exec1 in correct_instr.
specialize (correct_instr ( dc_name (df_prototype d)) blk_id mem s e i). clear HeqA. clear A.
specialize (check (dc_name (df_prototype d)) blk_id i i0). unfold check_size in check. specialize (correct_instr i0 i Z.zero). destruct (o {| fn := dc_name (df_prototype d); bk := blk_id; pt := i |} m i0).  simpl in *. destruct i, i0; simpl in *; eauto; try apply mini_trace_2r_implies_1l in correct_instr; try inversion correct_instr.
destruct (eval_op e None op); simpl in *; eauto. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. destruct l; simpl in *; eauto.
Admitted.



Hint Resolve jump_equiv.












        
  
Lemma term_correct : forall mem pt bk fn o m t e s (r:Trace()->Trace()->Prop)   (correct_instr : forall (fid : function_id) (bid : block_id) (mem : memory) 
                    (s : stack) (e : env) (iid : instr_id) (i : instr) 
                    (t : instr_id) (int_ins : int),
                  compare_exec1 m (modul_opt o m) [:: (iid, i)]
                    (build_opt o {| fn := fid; bk := bid; pt := iid |} m i int_ins) mem
                    (mk_state {| fn := fid; bk := bid; pt := iid |} e s) t)
  (check : forall (fid : function_id) (bid : block_id) (iid : instr_id) 
            (i : instr) (int_ins : int),
          check_size (build_opt o {| fn := fid; bk := bid; pt := iid |} m i int_ins))
 (  CIH : forall st : state, forall mem : memory,
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st))), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            match t with
            | TERM_Ret (t0, op) =>
                do dv <- eval_op e (Some t0) op;
                match s with
                | [::] => Obs (Fin dv)
                | KRet e' id p' :: k' =>
                    Jump (p', add_env id dv e', k')
                | KRet_void _ _ :: _ =>
                    t_raise_p {| fn := fn; bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret op in non-return configuration"
                end
            | TERM_Ret_void =>
                match s with
                | [::] => Obs (Fin (DV (VALUE_Bool true)))
                | KRet _ _ _ :: _ =>
                    t_raise_p {| fn := fn; bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret void in non-return configuration"
                | KRet_void e' p' :: k' => Jump (p', e', k')
                end
            | TERM_Br (t0, op) br1 br2 =>
                do dv <- eval_op e (Some t0) op;
                do br <-
                match dv with
                | DV _ => failwith "Br got non-bool value"
                | DVALUE_CodePointer _ =>
                    failwith "Br got non-bool value"
                | DVALUE_Addr _ =>
                    failwith "Br got non-bool value"
                | DVALUE_I1 comparison_bit =>
                    if
                     StepSemantics.Int1.eq comparison_bit
                       StepSemantics.Int1.one
                    then inr br1
                    else inr br2
                | DVALUE_I32 _ =>
                    failwith "Br got non-bool value"
                | DVALUE_I64 _ =>
                    failwith "Br got non-bool value"
                | DVALUE_Poison =>
                    failwith "Br got non-bool value"
                end; do st <- jump m fn bk br e s; Jump st
            | TERM_Br_1 br =>
                do st <- jump m fn bk br e s; Jump st
            | TERM_Switch _ _ _ =>
                t_raise "Unsupport LLVM terminator"
            | TERM_IndirectBr _ _ =>
                t_raise "Unsupport LLVM terminator"
            | TERM_Resume _ =>
                t_raise "Unsupport LLVM terminator"
            | TERM_Invoke _ _ _ _ =>
                t_raise "Unsupport LLVM terminator"
            end
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
                (step_sem m s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
                (step_sem m s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) =>
              Vis (Eff (effects_map (step_sem m) m1))
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
    match
      match
        match
          match
            match t with
            | TERM_Ret (t0, op) =>
                do dv <- eval_op e (Some t0) op;
                match s with
                | [::] => Obs (Fin dv)
                | KRet e' id p' :: k' =>
                    Jump (p', add_env id dv e', k')
                | KRet_void _ _ :: _ =>
                    t_raise_p {| fn := fn; bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret op in non-return configuration"
                end
            | TERM_Ret_void =>
                match s with
                | [::] => Obs (Fin (DV (VALUE_Bool true)))
                | KRet _ _ _ :: _ =>
                    t_raise_p {| fn := fn; bk := bk; pt := pt |}
                      "IMPOSSIBLE: Ret void in non-return configuration"
                | KRet_void e' p' :: k' => Jump (p', e', k')
                end
            | TERM_Br (t0, op) br1 br2 =>
                do dv <- eval_op e (Some t0) op;
                do br <-
                match dv with
                | DV _ => failwith "Br got non-bool value"
                | DVALUE_CodePointer _ =>
                    failwith "Br got non-bool value"
                | DVALUE_Addr _ =>
                    failwith "Br got non-bool value"
                | DVALUE_I1 comparison_bit =>
                    if
                     StepSemantics.Int1.eq comparison_bit
                       StepSemantics.Int1.one
                    then inr br1
                    else inr br2
                | DVALUE_I32 _ =>
                    failwith "Br got non-bool value"
                | DVALUE_I64 _ =>
                    failwith "Br got non-bool value"
                | DVALUE_Poison =>
                    failwith "Br got non-bool value"
                end;
                do st <- jump (modul_opt o m) fn bk br e s;
                Jump st
            | TERM_Br_1 br =>
                do st <- jump (modul_opt o m) fn bk br e s;
                Jump st
            | TERM_Switch _ _ _ =>
                t_raise "Unsupport LLVM terminator"
            | TERM_IndirectBr _ _ =>
                t_raise "Unsupport LLVM terminator"
            | TERM_Resume _ =>
                t_raise "Unsupport LLVM terminator"
            | TERM_Invoke _ _ _ _ =>
                t_raise "Unsupport LLVM terminator"
            end
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
                (step_sem (modul_opt o m) s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m1) =>
              Vis
                (Eff (effects_map (step_sem (modul_opt o m)) m1))
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
    end.
Proof.  intros. destruct t; simpl in *; eauto.
        +destruct v. destruct (eval_op e (Some t) v); simpl in *; eauto. destruct s; simpl in *; eauto. destruct f; simpl in *; eauto.
        +destruct s; simpl in *; eauto. destruct f; simpl in *; eauto.
        +destruct v. destruct (eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; eauto. Qed.
Hint Resolve term_correct.



Lemma find_func_equiv : forall (r:Trace()->Trace()->Prop) mem bk fn id s i3 e args id0 o m, trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do fnentry <-
             trywith ("stepD: no function " ++ string_of id0) (find_function_entry m id0);
             let
             'FunctionEntry ids pc_f := fnentry in
              do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
              Step (pc_f, combine ids dvs, KRet e id {| fn := fn; bk := bk; pt := i3 |} :: s))
          with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s) (step_sem m s')
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
            (do fnentry <-
             trywith ("stepD: no function " ++ string_of id0)
               (find_function_entry (modul_opt o m) id0);
             let
             'FunctionEntry ids pc_f := fnentry in
              do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
              Step (pc_f, combine ids dvs, KRet e id {| fn := fn; bk := bk; pt := i3 |} :: s))
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. unfold find_function_entry. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct (find_function m id0); simpl in *; eauto. rewrite equiv_func. unfold targetfunc. unfold endfunc. simpl in *. destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. unfold blk_entry_id. simpl in *. admit. Admitted.
Hint Resolve find_func_equiv.


Lemma find_func_equiv1 : forall (r:Trace()->Trace()->Prop) m o args e t0 i3 s n1 bk fn id mem,  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do fnentry <-
             trywith ("stepD: no function " ++ string_of id) (find_function_entry m id);
             let
             'FunctionEntry ids pc_f := fnentry in
              do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
              match t0 with
              | TYPE_I _ => t_raise "Call mismatch void/non-void"
              | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
              | TYPE_Void =>
                  Step
                    (pc_f, combine ids dvs,
                    KRet_void e {| fn := fn; bk := bk; pt := i3 |} :: s)
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
              end)
          with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IVoid n1 |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IVoid n1 |}, e, s) (step_sem m s')
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
            (do fnentry <-
             trywith ("stepD: no function " ++ string_of id)
               (find_function_entry (modul_opt o m) id);
             let
             'FunctionEntry ids pc_f := fnentry in
              do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
              match t0 with
              | TYPE_I _ => t_raise "Call mismatch void/non-void"
              | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
              | TYPE_Void =>
                  Step
                    (pc_f, combine ids dvs,
                    KRet_void e {| fn := fn; bk := bk; pt := i3 |} :: s)
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
              end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n1 |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n1 |}, e, s)
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
Proof. intros. unfold find_function_entry. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct ( find_function m id); simpl in *; eauto. rewrite equiv_func. unfold targetfunc. unfold endfunc. destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. destruct t0; simpl in *; eauto.  Admitted.
 Hint Resolve find_func_equiv1.



Lemma find_instr_same_equiv : forall (r:Trace()->Trace()->Prop) mem blk_code pt bk fn m o s e i   (correct_instr : forall (fid : function_id) (bid : block_id) (mem : memory) 
                    (s : stack) (e : env) (iid : instr_id) (i : instr) 
                    (t : instr_id) (int_ins : int),
                  compare_exec1 m (modul_opt o m) [:: (iid, i)]
                    (build_opt o {| fn := fid; bk := bid; pt := iid |} m i int_ins) mem
                    (mk_state {| fn := fid; bk := bid; pt := iid |} e s) t)
  (check : forall (fid : function_id) (bid : block_id) (iid : instr_id) 
            (i : instr) (int_ins : int),
          check_size (build_opt o {| fn := fid; bk := bid; pt := iid |} m i int_ins))
(  CIH : forall st : state, forall mem : memory,
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st))), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do cmd <-
             trywith
               ("CFG has no instruction at " ++ string_of {| fn := fn; bk := bk; pt := pt |})
               match find_instr blk_code pt i with
               | Some (c, _) => Some c
               | None => None
               end;
             match cmd with
             | CFG.Step insn =>
                 do pc_next <-
                 trywith "no fallthrough intsruction"
                   match find_instr blk_code pt i with
                   | Some (_, Some a0) => Some {| fn := fn; bk := bk; pt := a0 |}
                   | Some (_, None) => None
                   | None => None
                   end;
                 match pt with
                 | IId id =>
                     match insn with
                     | INSTR_Op op =>
                         do dv <- eval_op e None op; Step (pc_next, add_env id dv e, s)
                     | INSTR_Call (_, ID_Global fid) args =>
                         do fnentry <-
                         trywith ("stepD: no function " ++ string_of fid)
                           (find_function_entry m fid);
                         let
                         'FunctionEntry ids pc_f := fnentry in
                          do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                          Step (pc_f, combine ids dvs, KRet e id pc_next :: s)
                     | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
                     | INSTR_Alloca t0 _ _ =>
                         Obs (Eff (Alloca t0 (fun a : value => (pc_next, add_env id a e, s))))
                     | INSTR_Load _ _ (u, ptr) _ =>
                         do dv <- eval_op e (Some u) ptr;
                         match dv with
                         | DV _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_Addr a =>
                             Obs
                               (Eff
                                  (Load a (fun dv0 : value => (pc_next, add_env id dv0 e, s))))
                         | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
                         end
                     | INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID"
                     | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
                     | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
                     | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
                     end
                 | IVoid _ =>
                     match insn with
                     | INSTR_Op _ => t_raise "ID / Instr mismatch void/non-void"
                     | INSTR_Call (ret_ty, ID_Global fid) args =>
                         do fnentry <-
                         trywith ("stepD: no function " ++ string_of fid)
                           (find_function_entry m fid);
                         let
                         'FunctionEntry ids pc_f := fnentry in
                          do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                          match ret_ty with
                          | TYPE_I _ => t_raise "Call mismatch void/non-void"
                          | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                          | TYPE_Void =>
                              Step (pc_f, combine ids dvs, KRet_void e pc_next :: s)
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
                     | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
                     | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                     | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                     | INSTR_Store _ (t0, val) (u, ptr) _ =>
                         do dv <- eval_op e (Some t0) val;
                         do v <- eval_op e (Some u) ptr;
                         match v with
                         | DV _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_CodePointer _ =>
                             t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_Addr a =>
                             Obs (Eff (Store a dv (fun _ : value => (pc_next, e, s))))
                         | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
                         end
                     | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
                     | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
                     | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
                     end
                 end
             | Term (TERM_Ret (t1, op)) =>
                 do dv <- eval_op e (Some t1) op;
                 match s with
                 | [::] => Obs (Fin dv)
                 | KRet e' id p' :: k' => Jump (p', add_env id dv e', k')
                 | KRet_void _ _ :: _ =>
                     t_raise_p {| fn := fn; bk := bk; pt := pt |}
                       "IMPOSSIBLE: Ret op in non-return configuration"
                 end
             | Term TERM_Ret_void =>
                 match s with
                 | [::] => Obs (Fin (DV (VALUE_Bool true)))
                 | KRet _ _ _ :: _ =>
                     t_raise_p {| fn := fn; bk := bk; pt := pt |}
                       "IMPOSSIBLE: Ret void in non-return configuration"
                 | KRet_void e' p' :: k' => Jump (p', e', k')
                 end
             | Term (TERM_Br (t1, op) br1 br2) =>
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
                 end; do st <- jump m fn bk br e s; Jump st
             | Term (TERM_Br_1 br) => do st <- jump m fn bk br e s; Jump st
             | Term (TERM_Switch _ _ _) => t_raise "Unsupport LLVM terminator"
             | Term (TERM_IndirectBr _ _) => t_raise "Unsupport LLVM terminator"
             | Term (TERM_Resume _) => t_raise "Unsupport LLVM terminator"
             | Term (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator"
             end)
          with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem m s')
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
            (do cmd <-
             trywith
               ("CFG has no instruction at " ++ string_of {| fn := fn; bk := bk; pt := pt |})
               match find_instr blk_code pt i with
               | Some (c, _) => Some c
               | None => None
               end;
             match cmd with
             | CFG.Step insn =>
                 do pc_next <-
                 trywith "no fallthrough intsruction"
                   match find_instr blk_code pt i with
                   | Some (_, Some a0) => Some {| fn := fn; bk := bk; pt := a0 |}
                   | Some (_, None) => None
                   | None => None
                   end;
                 match pt with
                 | IId id =>
                     match insn with
                     | INSTR_Op op =>
                         do dv <- eval_op e None op; Step (pc_next, add_env id dv e, s)
                     | INSTR_Call (_, ID_Global fid) args =>
                         do fnentry <-
                         trywith ("stepD: no function " ++ string_of fid)
                           (find_function_entry (modul_opt o m) fid);
                         let
                         'FunctionEntry ids pc_f := fnentry in
                          do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                          Step (pc_f, combine ids dvs, KRet e id pc_next :: s)
                     | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
                     | INSTR_Alloca t0 _ _ =>
                         Obs (Eff (Alloca t0 (fun a : value => (pc_next, add_env id a e, s))))
                     | INSTR_Load _ _ (u, ptr) _ =>
                         do dv <- eval_op e (Some u) ptr;
                         match dv with
                         | DV _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_Addr a =>
                             Obs
                               (Eff
                                  (Load a (fun dv0 : value => (pc_next, add_env id dv0 e, s))))
                         | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
                         | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
                         end
                     | INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID"
                     | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
                     | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
                     | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
                     end
                 | IVoid _ =>
                     match insn with
                     | INSTR_Op _ => t_raise "ID / Instr mismatch void/non-void"
                     | INSTR_Call (ret_ty, ID_Global fid) args =>
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
                              Step (pc_f, combine ids dvs, KRet_void e pc_next :: s)
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
                     | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
                     | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                     | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                     | INSTR_Store _ (t0, val) (u, ptr) _ =>
                         do dv <- eval_op e (Some t0) val;
                         do v <- eval_op e (Some u) ptr;
                         match v with
                         | DV _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_CodePointer _ =>
                             t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_Addr a =>
                             Obs (Eff (Store a dv (fun _ : value => (pc_next, e, s))))
                         | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                         | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
                         end
                     | INSTR_Fence => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicCmpXchg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_AtomicRMW => t_raise "Unsupported LLVM intsruction"
                     | INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable"
                     | INSTR_VAArg => t_raise "Unsupported LLVM intsruction"
                     | INSTR_LandingPad => t_raise "Unsupported LLVM intsruction"
                     end
                 end
             | Term (TERM_Ret (t1, op)) =>
                 do dv <- eval_op e (Some t1) op;
                 match s with
                 | [::] => Obs (Fin dv)
                 | KRet e' id p' :: k' => Jump (p', add_env id dv e', k')
                 | KRet_void _ _ :: _ =>
                     t_raise_p {| fn := fn; bk := bk; pt := pt |}
                       "IMPOSSIBLE: Ret op in non-return configuration"
                 end
             | Term TERM_Ret_void =>
                 match s with
                 | [::] => Obs (Fin (DV (VALUE_Bool true)))
                 | KRet _ _ _ :: _ =>
                     t_raise_p {| fn := fn; bk := bk; pt := pt |}
                       "IMPOSSIBLE: Ret void in non-return configuration"
                 | KRet_void e' p' :: k' => Jump (p', e', k')
                 end
             | Term (TERM_Br (t1, op) br1 br2) =>
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
                 end; do st <- jump (modul_opt o m) fn bk br e s; Jump st
             | Term (TERM_Br_1 br) => do st <- jump (modul_opt o m) fn bk br e s; Jump st
             | Term (TERM_Switch _ _ _) => t_raise "Unsupport LLVM terminator"
             | Term (TERM_IndirectBr _ _) => t_raise "Unsupport LLVM terminator"
             | Term (TERM_Resume _) => t_raise "Unsupport LLVM terminator"
             | Term (TERM_Invoke _ _ _ _) => t_raise "Unsupport LLVM terminator"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. destruct (find_instr blk_code pt i); simpl in *; eauto. destruct p; simpl in *; eauto. destruct c; simpl in *; eauto. destruct o0; simpl in *; eauto. destruct pt, i0; simpl in *; eauto. destruct ( eval_op e None op); simpl in *; eauto. destruct fn0; simpl in *; eauto.
       destruct i0; simpl in *; eauto. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t0) v); simpl in *; eauto. destruct v0; simpl in *; eauto. destruct fn0; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct val, ptr; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct ( eval_op e (Some t0) v0); simpl in *; eauto. destruct v2; simpl in *; eauto. Qed.
Hint Resolve find_instr_same_equiv.




Lemma correct_instr_trace1 : forall o m (check: forall fid bid iid  i int_ins, check_size (build_opt o (mk_pc fid bid iid) m i int_ins)) (correct_instr: forall fid bid, correct_instr1 m o fid bid) st mem, trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)).
Proof. intros o m check correct_instr.
                                                 


       pcofix CIH. intros. pfold.

       assert ( (memD mem (sem m st)) = unroll  (memD mem (sem m st))). destruct  (memD mem (sem m st)); eauto. rewrite H. clear H.

       assert (  (memD mem (sem (modul_opt o m) st)) = unroll   (memD mem (sem (modul_opt o m) st))). destruct   (memD mem (sem (modul_opt o m) st)); eauto. rewrite H. clear H.


       simpl in *. destruct st. simpl in *. destruct p. destruct p. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1.



       destruct ( find_function m fn); simpl in *; eauto.
       rewrite equiv_func. unfold targetfunc. unfold endfunc. simpl in *. destruct (find_block (blks (df_instrs d)) bk); simpl in *; eauto. unfold block_to_cmd. unfold blk_term_id. simpl in *. destruct b. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt) ); simpl in *; eauto.

       unfold code_opt. destruct blk_code; simpl in *; eauto.


       destruct p.
unfold mkpc in *.

       
       generalize (check (function_id_of_dec (df_prototype d)) blk_id i0 i1  (get_next ((i0, i1) :: blk_code))). intro check1. unfold check_size in check1. unfold build_opt in check1. unfold create_code in check1.
        unfold correct_instr1 in *. 
        generalize (correct_instr (function_id_of_dec (df_prototype d)) blk_id mem s e i0 i1 i  (get_next ((i0, i1) :: blk_code))). intro correct_instr1. unfold build_opt in correct_instr1. unfold create_code in *. unfold compare_exec1 in correct_instr1.
        

       +simpl in *. destruct ( o {| fn := function_id_of_dec (df_prototype d); bk := blk_id; pt := i0 |} m i1); simpl in *. destruct (decide (pt = i0)); subst; simpl in *; eauto.



        (*No instr on L*)

       -destruct i0, i1; simpl in *.
        *destruct (eval_op e None op); simpl in *; eauto; apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply false_env in H1.  inversion H1.
        *destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_2r_implies_1l in correct_instr1. inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1. inversion correct_instr1. apply false_stack in H2. inversion H2.  apply mini_trace_2r_implies_1l in correct_instr1. inversion correct_instr1.  apply mini_trace_2r_implies_1l in correct_instr1. inversion correct_instr1.  apply mini_trace_2r_implies_1l in correct_instr1. inversion correct_instr1. apply false_mem in H0. inversion H0. destruct ptr. destruct (eval_op e (Some t1) v); simpl in *; eauto.  apply mini_trace_2r_implies_1l in correct_instr1. inversion correct_instr1. destruct v0; simpl in *; eauto;  apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply false_env in H1. inversion H1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.   apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. destruct fn0, i0; simpl in *. destruct (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. destruct t0; apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply false_stack in H2. inversion H2. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. destruct val, ptr. destruct ( eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.  apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.  destruct v2; simpl in *; eauto; apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. subst. assert (IVoid n0 = IVoid n0) by auto.  apply n in H. inversion H.
         apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.  apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.  apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.  apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1. apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.  apply mini_trace_2r_implies_1l in correct_instr1; inversion correct_instr1.
      admit. destruct l; simpl in *; eauto. admit. inversion check1. Admitted.