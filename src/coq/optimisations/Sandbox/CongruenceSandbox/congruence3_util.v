Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.congruence3_definition.

Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat.




Lemma first_case_both_sides : forall (r:Trace()->Trace()->Prop) fn bk blk_code m o mem op op0 blk_id i id e s (d:definition cfg) (CIH : forall st : state,
        congruence3_definition.wf_pc (modul_opt o m) (pc_of_state st) ->
        congruence3_definition.wf_pc m (pc_of_state st) ->
        forall mem : memory, r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (wf_pc : congruence3_definition.wf_pc m {| fn := fn; bk := bk; pt := IId id |})
  (wf_pc_op : congruence3_definition.wf_pc (modul_opt o m)
               {| fn := fn; bk := bk; pt := IId id |}) (correct_instr : compare_trace
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (do dv <- eval_op e None op0;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
            (do dv <- eval_op e None op0;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
Proof. intros. destruct (eval_op e None op), ( eval_op e None op0); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. constructor. right. apply CIH. unfold pc_of_state in *. simpl in *. destruct blk_code. simpl in *. Admitted.
Hint Resolve first_case_both_sides.


Lemma second_case_both_sides : forall fn bk blk_code (r:Trace()->Trace()->Prop) m o blk_id i id e s (fn0:tident) args (d:definition cfg) mem op (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (let (_, i0) := fn0 in
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
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
            (let (_, i0) := fn0 in
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
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
Proof. intros. destruct ( eval_op e None op), fn0, i0; simpl in *; eauto.
       destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto.
       destruct f; simpl in *; eauto.
       destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto.
       apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       destruct (find_function_entry (modul_opt o m) id0); simpl in *; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr. symmetry in H2; apply false_stack in H2. inversion H2. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.

Hint Resolve second_case_both_sides.






Lemma third_case_both_sides : forall (r:Trace()->Trace()->Prop) (d:definition cfg) blk_code fn bk mem op o m e i id s blk_id (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))), 
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
.
Proof. intros. destruct ( eval_op e None op); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr. symmetry in H0. apply false_mem in H0.
       inversion H0. Qed.


Hint Resolve third_case_both_sides.

Lemma fourth_case_both_sides : forall (r:Trace()->Trace()->Prop) m o e fn blk_code bk id s blk_id (ptr:tvalue) i (d:definition cfg) op mem (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 ( correct_instr : compare_trace
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
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
                                    ({|
                                     fn := function_id_of_dec (df_prototype d);
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
    end
.
Proof. intros. destruct (eval_op e None op), ptr; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct (eval_op e (Some t) v0); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct v1; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto.
       Qed. Hint Resolve fourth_case_both_sides.



Lemma fifth_case_both_sides : forall (r:Trace()->Trace()->Prop) blk_code bk fn mem i op s A o m e (d:definition cfg) blk_id id ( CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))),   trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
    end (Vis (trace_map (fun _ : state => ()) <$> Err A))
.
Proof. intros. destruct (eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.

Hint Resolve fifth_case_both_sides.


Lemma sixth_case_both_sides : forall (r:Trace()->Trace()->Prop) (fn0: tident) m o op mem blk_code bk fn id args s i e (d:definition cfg) blk_id (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (_, i0) := fn0 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry m fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                            Step
                              (pc_f, combine ids dvs,
                              KRet e id
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                  do dvs <- map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
Proof. intros. destruct fn0, (eval_op e None op), i0; simpl in *; eauto; destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr.  apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply false_stack in H2; inversion H2.  apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr.   apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.

Hint Resolve sixth_case_both_sides.

Lemma seventh_case_both_sides : forall (r:Trace()->Trace()->Prop) s (d:definition cfg) i o m (fn0:tident) (fn1:tident) e mem blk_id id args args0 fn bk blk_code (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (_, i0) := fn0 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry m fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                            Step
                              (pc_f, combine ids dvs,
                              KRet e id
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (let (_, i0) := fn1 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry (modul_opt o m) fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <-
                            map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0;
                            Step
                              (pc_f, combine ids dvs,
                              KRet e id
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
            (let (_, i0) := fn1 in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
Proof. intros. destruct fn0, fn1; simpl in *; eauto. destruct i0, i1; simpl in *; eauto. auto.
       destruct (find_function_entry m id0),  (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f, f0; simpl in *; eauto. destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args), (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct  (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr.  destruct  (find_function_entry m id0); simpl in *; eauto. destruct   (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f0; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct  (find_function_entry (modul_opt o m) id1); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.
Hint Resolve seventh_case_both_sides.

Lemma eighth_case_both_sides : forall (r:Trace()->Trace()->Prop) (fn0:tident) blk_code fn bk mem blk_id id args s e (d:definition cfg) m i o (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (_, i0) := fn0 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry m fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                            Step
                              (pc_f, combine ids dvs,
                              KRet e id
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                  do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))).
Proof. intros. destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply false_stack in H3. inversion H3.  apply mini_trace_implies_double in correct_instr; inversion correct_instr.  apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.
Hint Resolve eighth_case_both_sides.


Lemma ninth_case_both_sides : forall (r:Trace()->Trace()->Prop) (d:definition cfg) fn bk blk_code mem blk_id id args s i e m o (ptr:tvalue) (fn0:tident) (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (_, i0) := fn0 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry m fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                            Step
                              (pc_f, combine ids dvs,
                              KRet e id
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
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
                                    ({|
                                     fn := function_id_of_dec (df_prototype d);
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                  do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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

Proof. intros. destruct ptr, fn0; simpl in *; eauto. destruct (eval_op e (Some t) v), i0; simpl in *; eauto. destruct ( (find_function_entry m id0)); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct v0, (find_function_entry m id0); simpl in *; eauto; try destruct f.

destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
apply false_stack in H2. inversion H2.
apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
destruct v0; simpl in *; eauto.
apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.
Hint Resolve ninth_case_both_sides.


Lemma tenth_case_both_sides : forall A (r:Trace()->Trace()->Prop) (fn0:tident) blk_code bk fn mem blk_id id i args (d:definition cfg) s m o e (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (_, i0) := fn0 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry m fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                            Step
                              (pc_f, combine ids dvs,
                              KRet e id
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  Step
                    (pc_f, combine ids dvs,
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
    end (Vis (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.
Hint Resolve tenth_case_both_sides.



Lemma eleventh_case_both_sides : forall (r:Trace()->Trace()->Prop) m o op e i (d:definition cfg)
s mem blk_id id fn bk blk_code                         
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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

Proof. intros. destruct ( eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply false_mem in H0. inversion H0. Qed.
Hint Resolve eleventh_case_both_sides.


Lemma twelth_case_both_sides : forall blk_code fn bk id blk_id mem s (d:definition cfg) i e (fn0:tident) args m o (r:Trace()->Trace()->Prop) ( CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
                    match
                      (let (_, i0) := fn0 in
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
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    match
      match
        match
          match
            (let (_, i0) := fn0 in
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
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
    end. Proof. intros. destruct fn0, i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr.  apply mini_trace_implies_double in correct_instr. inversion correct_instr. symmetry in H3; apply false_stack in H3. inversion H3. apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.
Hint Resolve twelth_case_both_sides.


Lemma thirteenth_case_both_sides : forall (r:Trace()->Trace()->Prop) (d:definition cfg) blk_code fn bk mem i (ptr:tvalue) m o blk_id id e s  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
Proof. intros. destruct ptr, ( eval_op e (Some t) v); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply false_mem in H0. inversion H0. apply mini_trace_implies_double in correct_instr. inversion correct_instr.  apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.
Hint Resolve thirteenth_case_both_sides.



Lemma fourteenth_case_both_sides : forall (r:Trace()->Trace()->Prop) blk_code bk fn id blk_id mem i (d:definition cfg) e s A o m ( CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem m
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))))
    (Vis (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.
Hint Resolve fourteenth_case_both_sides.


Lemma fiftheenth_case_both_sides : forall (r:Trace()->Trace()->Prop) blk_code bk fn mem id blk_id (ptr:tvalue) s (d:definition cfg) o m op e i (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end), 
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
Proof. intros. destruct ptr, ( eval_op e None op); simpl in *; eauto.
       destruct (eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct (eval_op e (Some t) v); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct v1; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. Qed. Hint Resolve fiftheenth_case_both_sides.


Lemma sixteenth_case_both_sides : forall (r:Trace()->Trace()->Prop) blk_code bk fn mem id  blk_id (ptr:tvalue) s (d:definition cfg) i e args (fn0:tident) m o (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (let (_, i0) := fn0 in
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
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end), 
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
            (let (_, i0) := fn0 in
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
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
Proof. intros. destruct fn0, ptr; simpl in *; eauto. destruct i0, ( eval_op e (Some t0) v); simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       destruct v0, (find_function_entry (modul_opt o m) id0); simpl in *; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct f. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct f. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto.  apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. symmetry in H2. apply false_stack in H2. inversion H2.  apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto.
       destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed. Hint Resolve sixteenth_case_both_sides.




Lemma seventeenth_case_both_sides : forall (ptr:tvalue) fn bk blk_code mem id blk_id s m e o i (d:definition cfg) (r:Trace()->Trace()->Prop)  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 ( correct_instr : compare_trace
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                 add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))).
Proof. intros. destruct ptr; simpl in *; eauto. destruct (eval_op e (Some t) v); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct v0; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr. symmetry in H0. apply false_mem in H0. inversion H0. Qed.

Hint Resolve seventeenth_case_both_sides.


Lemma eighteenth_case_both_sides : forall blk_code A mem bk fn id blk_id i (ptr:tvalue) (d:definition cfg) e s o m (r:Trace()->Trace()->Prop)  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
    end (Vis (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. destruct ptr; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.

Hint Resolve  eighteenth_case_both_sides.



Lemma nineteenth_case_both_sides : forall A fn bk blk_code m o op s id blk_id mem (d:definition cfg) i e (r:Trace()->Trace()->Prop) (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 ( correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))
                    match
                      (do dv <- eval_op e None op;
                       Step
                         ({|
                          fn := function_id_of_dec (df_prototype d);
                          bk := blk_id;
                          pt := i |}, add_env id dv e, s))
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    match
      match
        match
          match
            (do dv <- eval_op e None op;
             Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id dv e, s))
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
Proof. intros. destruct (eval_op e None op); simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.

Hint Resolve nineteenth_case_both_sides.

Lemma twentieth_case_both_sides : forall (r:Trace()->Trace()->Prop) (ptr0:tvalue) (d:definition cfg) (ptr:tvalue) blk_code bk fn mem id blk_id s i e o m (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
Proof. intros. destruct ptr, ptr0; simpl in *; eauto. destruct ( eval_op e (Some t0) v0), ( eval_op e (Some t) v); simpl in *; eauto. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr.  inversion correct_instr. destruct v1, v2; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. Qed.
Hint Resolve twentieth_case_both_sides.


Lemma twenty_first_case_both_sides : forall A (fn0:tident) blk_code fn bk id blk_id mem s (d:definition cfg) i e args  m o (r:Trace()->Trace()->Prop) ( CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
 (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))
                    match
                      (let (_, i0) := fn0 in
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
                                bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    match
      match
        match
          match
            (let (_, i0) := fn0 in
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
                    KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
             | ID_Local _ => t_raise "INSTR_Call to local"
             end)
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
    end. Proof. intros. destruct fn0, i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto.  apply mini_trace_implies_double in correct_instr. inversion correct_instr.  Qed.

Hint Resolve twenty_first_case_both_sides.



Lemma twenty_second_case_both_sides : forall A blk_code (r:Trace()->Trace()->Prop) o m bk fn id blk_id mem s e (d:definition cfg) i (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin
                          (tauitem (mem ++ [:: undef])%list
                             ({|
                              fn := function_id_of_dec (df_prototype d);
                              bk := blk_id;
                              pt := i |}, add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    (Tau ()
       (memD (mem ++ [:: undef])%list
          (trace_map (fun _ : state => ())
             (step_sem (modul_opt o m)
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                 add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))).
Proof. intros. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.
Hint Resolve twenty_second_case_both_sides.



Lemma twenty_third_case_both_sides : forall (r:Trace()->Trace()->Prop) blk_code fn bk id blk_id mem A s o m (ptr0:tvalue) (d:definition cfg) i e (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IId id |} e s))
                       (fin (visitem mem (Err A))))
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IId id |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IId id |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                          add_env id dv0 e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Load got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Load got non-pointer value"
             end)
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
Proof. intros. destruct ptr0; simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.

Hint Resolve twenty_third_case_both_sides.

Lemma twenty_fourth_case_both_sides : forall (r:Trace()->Trace()->Prop) blk_code bk fn s blk_id mem A n (d:definition cfg) i e args (fn0:tident) o m (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IVoid n |} e s))
                       (fin (visitem mem (Err A))))
                    match
                      (let (ret_ty, i0) := fn0 in
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
                                    bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
                  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
    match
      match
        match
          match
            (let (ret_ty, i0) := fn0 in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. destruct fn0, i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.


Hint Resolve twenty_fourth_case_both_sides.


Lemma twenty_fifth_case_both_sides : forall A (n : int)
  (op : Ollvm_ast.value)
  (volatile : bool)
  (val : tvalue) (ptr : tvalue)
  (align : option int)
  (e : env)
  (i : instr_id)
  (s : stack)
  (m : mcfg)
  (o : opt)
  (fn : function_id)
  (bk : block_id)
  (blk_code : code)
  (mem : memory)
  (d : definition cfg)
  (blk_id : block_id)
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IVoid n |} e s))
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
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
    end. Proof. intros. destruct val, ptr; simpl in *; eauto.
                destruct ( eval_op e (Some t) v), (eval_op e (Some t0) v0); simpl in *; eauto.
                destruct v2; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed. Hint Resolve twenty_fifth_case_both_sides.



Lemma twenty_sixth_case_both_sides : forall A (n : int)
  (fn0 : tident)
  (args : seq tvalue)
  (op : Ollvm_ast.value)
  (e : env)
  (i : instr_id)
  (s : stack)
  (m : mcfg)
  (o : opt)
  (fn : function_id)
  (bk : block_id)
  (blk_code : code)
  (mem : memory)
  (d : definition cfg)
  (blk_id : block_id)
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (ret_ty, i0) := fn0 in
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
                                    bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IVoid n |} e s))
                       (fin (visitem mem (Err A))))), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
                  do dvs <- map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
    end (Vis (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. destruct fn0, i0; simpl in *; eauto. destruct (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t0, op0) => eval_op e (Some t0) op0) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.

Hint Resolve twenty_sixth_case_both_sides.



Lemma twenty_seventh_case_both_sides : forall 
  (n : int)
  (fn0 : tident)
  (args : seq tvalue)
  (fn1 : tident)
  (args0 : seq tvalue)
  (e : env)
  (i : instr_id)
  (s : stack)
  (m : mcfg)
  (o : opt)
  (fn : function_id)
  (bk : block_id)
  (blk_code : code)
  (mem : memory)
  (d : definition cfg)
  (blk_id : block_id)
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (ret_ty, i0) := fn0 in
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
                                    bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (let (ret_ty, i0) := fn1 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry (modul_opt o m) fid);
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
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
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
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
            (let (ret_ty, i0) := fn1 in
             match i0 with
             | ID_Global fid =>
                 do fnentry <-
                 trywith ("stepD: no function " ++ string_of fid)
                   (find_function_entry (modul_opt o m) fid);
                 let
                 'FunctionEntry ids pc_f := fnentry in
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. destruct fn1, fn0; simpl in *; eauto. destruct i0, i1; simpl in *; eauto.
       destruct  (find_function_entry m id0),  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f, f0; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0), ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
       destruct t0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct t; simpl in *; eauto.  apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct t, t0; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. destruct f; simpl in *; eauto.
       destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
       destruct t0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct f. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct (find_function_entry m id0); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. destruct t0; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.

Hint Resolve twenty_seventh_case_both_sides.


Lemma twenty_eighth_case_both_sides : forall m o A s e n (d:definition cfg) (fn0:tident) args i blk_id mem fn bk blk_code
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (ret_ty, i0) := fn0 in
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
                                    bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IVoid n |} e s))
                       (fin (visitem mem (Err A))))),
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
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
    end (Vis (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. destruct fn0; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto. destruct t; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.

Hint Resolve twenty_eighth_case_both_sides.



Lemma twenty_ninth_case_both_sides : forall (val:tvalue) blk_code bk fn mem blk_id args n s (d:definition cfg) e i (ptr:tvalue) (fn0:tident) (r:Trace()->Trace()->Prop) o m
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (ret_ty, i0) := fn0 in
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
                                    bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
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
                                    ({|
                                     fn := function_id_of_dec (df_prototype d);
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
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
                  do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                  match ret_ty with
                  | TYPE_I _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                  | TYPE_Void =>
                      Step
                        (pc_f, combine ids dvs,
                        KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. destruct val, ptr, fn0, i0; simpl in *; eauto. destruct (eval_op e (Some t) v), ( eval_op e (Some t0) v0), (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct f, v2; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct t1; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr. apply false_stack in H3. inversion H3. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto.  apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args), t1; simpl in *; eauto.  apply mini_trace_implies_double in correct_instr; inversion correct_instr. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr.
       destruct v2; simpl in *; eauto.  apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct ( eval_op e (Some t) v), ( eval_op e (Some t0) v0); simpl in *; eauto. destruct v2; simpl in *; eauto.  apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed. Hint Resolve twenty_ninth_case_both_sides.




Lemma thirtieth_case_both_sides : forall A  
  (n : int)
  (volatile : bool)
  (ptr : tvalue) (val : tvalue)
  (e : env)
  (i : instr_id)
  (s : stack)
  (m : mcfg)
  (o : opt)
  (fn : function_id)
  (bk : block_id)
  (blk_code : code)
  (mem : memory)
  (d : definition cfg)
  (blk_id : block_id)
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IVoid n |} e s))
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err A))
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. destruct val. destruct ptr. destruct ( eval_op e (Some t0) v), ( eval_op e (Some t0) v0); simpl in *; eauto. destruct (eval_op e (Some t) v); simpl in *; eauto. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct v1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct ( eval_op e (Some t) v); simpl in *; eauto. destruct (eval_op e (Some t) v); simpl in *; eauto. destruct v2; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Qed.

Hint Resolve thirtieth_case_both_sides.

Lemma thirty_first_case_both_sides : forall A m o (val:tvalue) (ptr:tvalue) blk_code fn bk mem blk_id i (d:definition cfg) n s e (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
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
                                     bk := blk_id;
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    (step_trace.tau
                       (tauitem mem
                          (mk_state
                             {|
                             fn := function_id_of_dec (df_prototype d);
                             bk := blk_id;
                             pt := IVoid n |} e s))
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e, s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
    end (Vis (trace_map (fun _ : state => ()) <$> Err A)).
Proof. intros. destruct val, ptr; simpl in *; eauto. destruct (eval_op e (Some t) v), ( eval_op e (Some t0) v0); simpl in *; eauto. destruct v2; simpl in *; eauto. apply mini_trace_implies_double in correct_instr; inversion correct_instr. Qed.
Hint Resolve thirty_first_case_both_sides.


Lemma thirty_second_case_both_sides : forall blk_code bk m o s e (val:tvalue) (ptr:tvalue) fn n blk_id (fn0:tident) args i (d:definition cfg) mem
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (t, val) := val in
                       let (u, ptr) := ptr in
                       do dv <- eval_op e (Some t) val;
                       do v <- eval_op e (Some u) ptr;
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
                                     bk := blk_id;
                                     pt := i |}, e, s))))
                       | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_Poison =>
                           t_raise "ERROR: Store got non-pointer value"
                       end)
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) 
                              (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (let (ret_ty, i0) := fn0 in
                       match i0 with
                       | ID_Global fid =>
                           do fnentry <-
                           trywith ("stepD: no function " ++ string_of fid)
                             (find_function_entry (modul_opt o m) fid);
                           let
                           'FunctionEntry ids pc_f := fnentry in
                            do dvs <-
                            map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                            match ret_ty with
                            | TYPE_I _ => t_raise "Call mismatch void/non-void"
                            | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                            | TYPE_Void =>
                                Step
                                  (pc_f, combine ids dvs,
                                  KRet_void e
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
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
                            | TYPE_Function _ _ =>
                                t_raise "Call mismatch void/non-void"
                            | TYPE_Struct _ => t_raise "Call mismatch void/non-void"
                            | TYPE_Packed_struct _ =>
                                t_raise "Call mismatch void/non-void"
                            | TYPE_Opaque => t_raise "Call mismatch void/non-void"
                            | TYPE_Vector _ _ =>
                                t_raise "Call mismatch void/non-void"
                            | TYPE_Identified _ =>
                                t_raise "Call mismatch void/non-void"
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
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) 
                              (fin (tauitem m' (k v)))
                        end
                    end),
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
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e,
                          s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
            (let (ret_ty, i0) := fn0 in
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
                          {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
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
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s)
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
Proof. intros. destruct val, ptr, fn0; simpl in *; eauto. destruct ( eval_op e (Some t) v), (eval_op e (Some t0) v0); simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (  map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto.  apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct i0; simpl in *; eauto. destruct   (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (  map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct v2; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr.  destruct i0; simpl in *; eauto.  destruct    (find_function_entry (modul_opt o m) id); simpl in *; eauto.
       destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct f; simpl in *; eauto. destruct f; simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct t1; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. symmetry in H3. apply false_stack in H3. inversion H3. apply mini_trace_implies_double in correct_instr. inversion correct_instr. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct i0; simpl in *;  try apply mini_trace_implies_double in correct_instr.
       destruct (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct f; simpl in *; eauto. destruct f; simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. eauto. destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. admit. destruct i0; simpl in *; eauto. destruct (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. destruct i0; simpl in *; eauto. destruct  (find_function_entry (modul_opt o m) id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto. destruct t1; simpl in *; eauto. apply mini_trace_implies_double in correct_instr. inversion correct_instr. Admitted.


Hint Resolve thirty_second_case_both_sides.




Lemma thirty_third_case_both_sides : forall
  (n : int)
  (volatile : bool)
  (val : tvalue) (ptr : tvalue)
  (align : option int)
  (volatile0 : bool)
  (val0 : tvalue) ( ptr0 : tvalue)
  (align0 : option int)
  (e : env)
  (i : instr_id)
  (s : stack)
  (m : mcfg)
  (o : opt)
  (fn : function_id)
  (bk : block_id)
  (blk_code : code)
  (mem : memory)
  (d : definition cfg)
  (blk_id : block_id)
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (mem : memory),
        r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (correct_instr : compare_trace
                    match
                      (let (t, val) := val in
                       let (u, ptr) := ptr in
                       do dv <- eval_op e (Some t) val;
                       do v <- eval_op e (Some u) ptr;
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
                                     bk := blk_id;
                                     pt := i |}, e, s))))
                       | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_Poison =>
                           t_raise "ERROR: Store got non-pointer value"
                       end)
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) 
                              (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      (let (t, val) := val0 in
                       let (u, ptr) := ptr0 in
                       do dv <- eval_op e (Some t) val;
                       do v <- eval_op e (Some u) ptr;
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
                                     bk := blk_id;
                                     pt := i |}, e, s))))
                       | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
                       | DVALUE_Poison =>
                           t_raise "ERROR: Store got non-pointer value"
                       end)
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := IVoid n |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := IVoid n |} e s)) 
                              (fin (tauitem m' (k v)))
                        end
                    end),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            (let (t0, val1) := val in
             let (u, ptr1) := ptr in
             do dv <- eval_op e (Some t0) val1;
             do v <- eval_op e (Some u) ptr1;
             match v with
             | DV _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e,
                          s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s) (step_sem m s')
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
            (let (t0, val1) := val0 in
             let (u, ptr1) := ptr0 in
             do dv <- eval_op e (Some t0) val1;
             do v <- eval_op e (Some u) ptr1;
             match v with
             | DV _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Addr a =>
                 Obs
                   (Eff
                      (Store a dv
                         (fun _ : value =>
                          ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e,
                          s))))
             | DVALUE_I1 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I32 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_I64 _ => t_raise "ERROR: Store got non-pointer value"
             | DVALUE_Poison => t_raise "ERROR: Store got non-pointer value"
             end)
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s)
                (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := IVoid n |}, e, s)
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
Proof. intros. destruct val0, ptr0, val, ptr; simpl in *; eauto. destruct (eval_op e (Some t1) v1), (eval_op e (Some t2) v2), (eval_op e (Some t) v), (eval_op e (Some t0) v0); simpl in *; eauto.
       +destruct v4; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       +destruct v5; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       +destruct v5; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       +destruct v4; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       +destruct v4; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       +destruct v4; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr.
       +destruct v4, v6; simpl in *; eauto; apply mini_trace_implies_double in correct_instr; inversion correct_instr; eauto. Qed.
Hint Resolve thirty_third_case_both_sides.









Lemma one_instr_both_sides : forall
  (o : opt)
  (m : mcfg)
  (d : definition cfg)
  (blk_id : block_id)
  (i0 : instr_id)
  (i1 : instr)
  (blk_code : seq (instr_id * instr))
  (i2 : instr)
  (check : True)
  (e : env)
  (s : stack)
  (mem : memory)
  (i : instr_id)
  (correct_instr : compare_trace
                    match
                      match i0 with
                      | IId id =>
                          match i1 with
                          | INSTR_Op op =>
                              do dv <- eval_op e None op;
                              Step
                                ({|
                                 fn := function_id_of_dec (df_prototype d);
                                 bk := blk_id;
                                 pt := i |}, add_env id dv e, s)
                          | INSTR_Call (_, ID_Global fid) args =>
                              do fnentry <-
                              trywith ("stepD: no function " ++ string_of fid)
                                (find_function_entry m fid);
                              let
                              'FunctionEntry ids pc_f := fnentry in
                               do dvs <-
                               map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                               Step
                                 (pc_f, combine ids dvs,
                                 KRet e id
                                   {|
                                   fn := function_id_of_dec (df_prototype d);
                                   bk := blk_id;
                                   pt := i |} :: s)
                          | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
                          | INSTR_Alloca t _ _ =>
                              Obs
                                (Eff
                                   (Alloca t
                                      (fun a : value =>
                                       ({|
                                        fn := function_id_of_dec (df_prototype d);
                                        bk := blk_id;
                                        pt := i |}, add_env id a e, s))))
                          | INSTR_Load _ _ (u, ptr) _ =>
                              do dv <- eval_op e (Some u) ptr;
                              match dv with
                              | DV _ => t_raise "ERROR: Load got non-pointer value"
                              | DVALUE_CodePointer _ =>
                                  t_raise "ERROR: Load got non-pointer value"
                              | DVALUE_Addr a =>
                                  Obs
                                    (Eff
                                       (Load a
                                          (fun dv0 : value =>
                                           ({|
                                            fn := function_id_of_dec (df_prototype d);
                                            bk := blk_id;
                                            pt := i |}, add_env id dv0 e, s))))
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
                          match i1 with
                          | INSTR_Op _ => t_raise "ID / Instr mismatch void/non-void"
                          | INSTR_Call (ret_ty, ID_Global fid) args =>
                              do fnentry <-
                              trywith ("stepD: no function " ++ string_of fid)
                                (find_function_entry m fid);
                              let
                              'FunctionEntry ids pc_f := fnentry in
                               do dvs <-
                               map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                               match ret_ty with
                               | TYPE_I _ => t_raise "Call mismatch void/non-void"
                               | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                               | TYPE_Void =>
                                   Step
                                     (pc_f, combine ids dvs,
                                     KRet_void e
                                       {|
                                       fn := function_id_of_dec (df_prototype d);
                                       bk := blk_id;
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
                          | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
                          | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                          | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                          | INSTR_Store _ (t, val) (u, ptr) _ =>
                              do dv <- eval_op e (Some t) val;
                              do v <- eval_op e (Some u) ptr;
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
                                            bk := blk_id;
                                            pt := i |}, e, s))))
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
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := i0 |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := i0 |} e s)) (fin (tauitem m' (k v)))
                        end
                    end
                    match
                      match i0 with
                      | IId id =>
                          match i2 with
                          | INSTR_Op op =>
                              do dv <- eval_op e None op;
                              Step
                                ({|
                                 fn := function_id_of_dec (df_prototype d);
                                 bk := blk_id;
                                 pt := i |}, add_env id dv e, s)
                          | INSTR_Call (_, ID_Global fid) args =>
                              do fnentry <-
                              trywith ("stepD: no function " ++ string_of fid)
                                (find_function_entry (modul_opt o m) fid);
                              let
                              'FunctionEntry ids pc_f := fnentry in
                               do dvs <-
                               map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                               Step
                                 (pc_f, combine ids dvs,
                                 KRet e id
                                   {|
                                   fn := function_id_of_dec (df_prototype d);
                                   bk := blk_id;
                                   pt := i |} :: s)
                          | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
                          | INSTR_Alloca t _ _ =>
                              Obs
                                (Eff
                                   (Alloca t
                                      (fun a : value =>
                                       ({|
                                        fn := function_id_of_dec (df_prototype d);
                                        bk := blk_id;
                                        pt := i |}, add_env id a e, s))))
                          | INSTR_Load _ _ (u, ptr) _ =>
                              do dv <- eval_op e (Some u) ptr;
                              match dv with
                              | DV _ => t_raise "ERROR: Load got non-pointer value"
                              | DVALUE_CodePointer _ =>
                                  t_raise "ERROR: Load got non-pointer value"
                              | DVALUE_Addr a =>
                                  Obs
                                    (Eff
                                       (Load a
                                          (fun dv0 : value =>
                                           ({|
                                            fn := function_id_of_dec (df_prototype d);
                                            bk := blk_id;
                                            pt := i |}, add_env id dv0 e, s))))
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
                          match i2 with
                          | INSTR_Op _ => t_raise "ID / Instr mismatch void/non-void"
                          | INSTR_Call (ret_ty, ID_Global fid) args =>
                              do fnentry <-
                              trywith ("stepD: no function " ++ string_of fid)
                                (find_function_entry (modul_opt o m) fid);
                              let
                              'FunctionEntry ids pc_f := fnentry in
                               do dvs <-
                               map_monad (fun '(t, op) => eval_op e (Some t) op) args;
                               match ret_ty with
                               | TYPE_I _ => t_raise "Call mismatch void/non-void"
                               | TYPE_Pointer _ => t_raise "Call mismatch void/non-void"
                               | TYPE_Void =>
                                   Step
                                     (pc_f, combine ids dvs,
                                     KRet_void e
                                       {|
                                       fn := function_id_of_dec (df_prototype d);
                                       bk := blk_id;
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
                          | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
                          | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                          | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                          | INSTR_Store _ (t, val) (u, ptr) _ =>
                              do dv <- eval_op e (Some t) val;
                              do v <- eval_op e (Some u) ptr;
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
                                            bk := blk_id;
                                            pt := i |}, e, s))))
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
                    with
                    | Step s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (tauitem mem s'))
                    | Jump s' =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (tauitem mem s'))
                    | Obs (Fin s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (visitem mem (Fin s')))
                    | Obs (Err s') =>
                        step_trace.tau
                          (tauitem mem
                             (mk_state
                                {|
                                fn := function_id_of_dec (df_prototype d);
                                bk := blk_id;
                                pt := i0 |} e s)) (fin (visitem mem (Err s')))
                    | Obs (Eff s') =>
                        match mem_step s' mem with
                        | inl _ =>
                            fin
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := i0 |} e s))
                        | inr (m', v, k) =>
                            step_trace.tau
                              (tauitem mem
                                 (mk_state
                                    {|
                                    fn := function_id_of_dec (df_prototype d);
                                    bk := blk_id;
                                    pt := i0 |} e s)) (fin (tauitem m' (k v)))
                        end
                    end)
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall st : state,
        congruence3_definition.wf_pc (modul_opt o m) (pc_of_state st) ->
        congruence3_definition.wf_pc m (pc_of_state st) ->
        forall mem : memory, r (memD mem (sem m st)) (memD mem (sem (modul_opt o m) st)))
  (fn : function_id)
  (bk : block_id)
  (wf_pc : congruence3_definition.wf_pc m {| fn := fn; bk := bk; pt := i0 |})
  (wf_pc_op : congruence3_definition.wf_pc (modul_opt o m) {| fn := fn; bk := bk; pt := i0 |})
  (blk_phis : seq (local_id * phi))
  (t : terminator)
  (n : i <> i0),
  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match
            match i0 with
            | IId id =>
                match i1 with
                | INSTR_Op op =>
                    do dv <- eval_op e None op;
                    Step
                      ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, 
                      add_env id dv e, s)
                | INSTR_Call (_, ID_Global fid) args =>
                    do fnentry <-
                    trywith ("stepD: no function " ++ string_of fid)
                      (find_function_entry m fid);
                    let
                    'FunctionEntry ids pc_f := fnentry in
                     do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                     Step
                       (pc_f, combine ids dvs,
                       KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
                | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
                | INSTR_Alloca t0 _ _ =>
                    Obs
                      (Eff
                         (Alloca t0
                            (fun a : value =>
                             ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                             add_env id a e, s))))
                | INSTR_Load _ _ (u, ptr) _ =>
                    do dv <- eval_op e (Some u) ptr;
                    match dv with
                    | DV _ => t_raise "ERROR: Load got non-pointer value"
                    | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
                    | DVALUE_Addr a =>
                        Obs
                          (Eff
                             (Load a
                                (fun dv0 : value =>
                                 ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                                 add_env id dv0 e, s))))
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
                match i1 with
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
                         Step
                           (pc_f, combine ids dvs,
                           KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |}
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
                | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
                | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                | INSTR_Store _ (t0, val) (u, ptr) _ =>
                    do dv <- eval_op e (Some t0) val;
                    do v <- eval_op e (Some u) ptr;
                    match v with
                    | DV _ => t_raise "ERROR: Store got non-pointer value"
                    | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
                    | DVALUE_Addr a =>
                        Obs
                          (Eff
                             (Store a dv
                                (fun _ : value =>
                                 ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e, s))))
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
          with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := i0 |}, e, s) (step_sem m s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := i0 |}, e, s) (step_sem m s')
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
            match i0 with
            | IId id =>
                match i2 with
                | INSTR_Op op =>
                    do dv <- eval_op e None op;
                    Step
                      ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, 
                      add_env id dv e, s)
                | INSTR_Call (_, ID_Global fid) args =>
                    do fnentry <-
                    trywith ("stepD: no function " ++ string_of fid)
                      (find_function_entry (modul_opt o m) fid);
                    let
                    'FunctionEntry ids pc_f := fnentry in
                     do dvs <- map_monad (fun '(t0, op) => eval_op e (Some t0) op) args;
                     Step
                       (pc_f, combine ids dvs,
                       KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code i |} :: s)
                | INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"
                | INSTR_Alloca t0 _ _ =>
                    Obs
                      (Eff
                         (Alloca t0
                            (fun a : value =>
                             ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                             add_env id a e, s))))
                | INSTR_Load _ _ (u, ptr) _ =>
                    do dv <- eval_op e (Some u) ptr;
                    match dv with
                    | DV _ => t_raise "ERROR: Load got non-pointer value"
                    | DVALUE_CodePointer _ => t_raise "ERROR: Load got non-pointer value"
                    | DVALUE_Addr a =>
                        Obs
                          (Eff
                             (Load a
                                (fun dv0 : value =>
                                 ({| fn := fn; bk := bk; pt := fallthrough blk_code i |},
                                 add_env id dv0 e, s))))
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
                match i2 with
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
                         Step
                           (pc_f, combine ids dvs,
                           KRet_void e {| fn := fn; bk := bk; pt := fallthrough blk_code i |}
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
                | INSTR_Call (ret_ty, ID_Local _) _ => t_raise "INSTR_Call to local"
                | INSTR_Alloca _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                | INSTR_Load _ _ _ _ => t_raise "ID / Instr mismatch void/non-void"
                | INSTR_Store _ (t0, val) (u, ptr) _ =>
                    do dv <- eval_op e (Some t0) val;
                    do v <- eval_op e (Some u) ptr;
                    match v with
                    | DV _ => t_raise "ERROR: Store got non-pointer value"
                    | DVALUE_CodePointer _ => t_raise "ERROR: Store got non-pointer value"
                    | DVALUE_Addr a =>
                        Obs
                          (Eff
                             (Store a dv
                                (fun _ : value =>
                                 ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, e, s))))
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
          with
          | Step s' =>
              Tau ({| fn := fn; bk := bk; pt := i0 |}, e, s) (step_sem (modul_opt o m) s')
          | Jump s' =>
              Tau ({| fn := fn; bk := bk; pt := i0 |}, e, s) (step_sem (modul_opt o m) s')
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
Proof. intros. destruct i0, i1, i2; simpl in *; eauto. Admitted.
       
Hint Resolve one_instr_both_sides.

