Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.DecidableEquality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.



Print mcfg.


Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.



Print cfg.
Print block.

(*If all the functions are equal, then the execution is the same*)


Print find_function.

Definition function_equal :=
forall m1 m2 fid, find_function m1 fid = find_function m2 fid.



Definition jump_equal_trace_equiv := forall m1 m2 fn bk br2 e s, jump m1 fn bk br2 e s = jump m2 fn bk br2 e s.


Lemma jump_equal : function_equal -> jump_equal_trace_equiv.
Proof. unfold function_equal, jump_equal_trace_equiv.
intros.
unfold jump. simpl. unfold find_block_entry.
simpl.
generalize (H m1 m2 fn). intros. rewrite H0. simpl. destruct (find_function m2 fn); eauto. Qed.





Lemma function_equal_trace_equiv : (function_equal) -> forall mem m1 m2 s, (trace_equiv (memD mem (sem m1 s)) (memD mem (sem m2 s))).
Proof. intro func_equal. pcofix CIH. intros. pfold.


assert (memD mem (sem m1 s) = unroll (memD mem (sem m1 s))).
destruct (memD mem (sem m1 s)); simpl; eauto.
rewrite H. clear H.


assert ((memD mem (sem m2 s)) = unroll (memD mem (sem m2 s))). destruct (memD mem (sem m2 s)); eauto. rewrite H; clear H.
unfold function_equal in func_equal. destruct s. destruct p. destruct p.
simpl. unfold find_function_entry. simpl.



generalize (func_equal m1 m2 fn). intros. 
remember (find_function m1 fn) as A.
remember (find_function m2 fn) as B.
destruct A, B; simpl; inversion H; simpl; eauto. subst.
destruct ( find_block (blks (df_instrs d0)) bk); simpl; eauto.
destruct (block_to_cmd b pt); simpl; eauto.
destruct p; simpl; eauto.
destruct c; simpl; eauto.
destruct o; simpl; eauto.
destruct pt; simpl; eauto.
destruct i; simpl; eauto.
destruct (eval_op e None op); simpl; eauto.
destruct fn0; simpl; eauto.
destruct i; simpl; eauto.
generalize (func_equal m1 m2 id0); intros; simpl; eauto. inversion H0.
destruct (find_function m1 id0); simpl; eauto.
simpl. destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl; eauto.
destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl; eauto.
destruct ptr; simpl; eauto. destruct (eval_op e (Some t0) v); simpl; eauto.
destruct v0; simpl; eauto.
destruct i; simpl; eauto.
destruct fn0; simpl; eauto.
destruct i; simpl; eauto.
generalize (func_equal m1 m2 id); intros; simpl; eauto. inversion H0.
destruct (find_function m1 id ); simpl; eauto.
destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl; eauto.
destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl; eauto.
destruct t; simpl; eauto.
destruct val; simpl; eauto.
destruct ptr; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct (eval_op e (Some t0) v0); simpl; eauto.
destruct v2; simpl; eauto.
destruct t; simpl; eauto.
destruct v; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct s; simpl; eauto.
destruct f; simpl; eauto.
destruct s; simpl; eauto.
destruct f; simpl; eauto.
destruct v; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct v0; simpl; eauto.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl; eauto.
apply jump_equal in func_equal. unfold jump_equal_trace_equiv in func_equal.
specialize (func_equal m1 m2 fn bk br1 e s). rewrite func_equal.
destruct (jump m2 fn bk br1 e s); simpl; eauto.
apply jump_equal in func_equal. unfold jump_equal_trace_equiv in func_equal.
specialize (func_equal m1 m2 fn bk br2 e s). rewrite func_equal.
destruct (jump m2 fn bk br2 e s); simpl; eauto.
apply jump_equal in func_equal. unfold jump_equal_trace_equiv in func_equal.
specialize (func_equal m1 m2 fn bk br e s). rewrite func_equal.
destruct (jump m2 fn bk br e s); simpl; eauto.
Qed.




Print fetch.



Print find_block.
Print block.

Definition get_block (fid:function_id) (bid:block_id) (m:mcfg) : option block :=
match find_function m fid with
  | None => None
  | Some fn => find_block (blks (df_instrs fn)) bid
end.


(*With the same fid, bid, m1 and m2 yield some result.
The result, block_id are the same.
block_phis are the same
the stepD of the head of both are the same
the tl of the code is the same
the blk_term is also the same*)
Print block.





Definition block_same_phis (b1 b2:block) :=
if (decide (b1.(blk_phis) = b2.(blk_phis))) then true else false.


Definition block_same_id (b1 b2:block) :=
if (decide (b1.(blk_id) = b2.(blk_id))) then true else false.



Definition block_same_term (b1 b2: block) :=
if (decide (b1.(blk_term) = b2.(blk_term))) then true else false.

Print code.




Definition tl (c:code) :=
match c with
  | [::] => [::]
  | _ :: t => t
end.




Definition block_same_tl_code (b1 b2: block) := if decide (tl (b1.(blk_code)) = tl (b2.(blk_code))) then true else false.


Print block.

Print find_block_entry.
Print block_entry.

Print find_block_entry.
Print block_entry.
Print find_function.


(*Either the first instruction of a block is the first of the list, if the list is empty then the terminator*)
Definition hdb (b:block) :=
match b.(blk_code) with
  | [::] => None
  | h :: _ => Some h
end.


Definition hd_block_equal m1 m2 fnid bkid b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => forall e s, stepD m1 ((mk_pc fnid bkid h1, e, s)) = stepD m2 ((mk_pc fnid bkid h2, e, s))
  | _, _ => False
end.
Print hdb.

Definition hd_fst_block_equal b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => h1 = h2
  | _, _ => False
end.




Definition tl_block_equal b1 b2 :=
tl (b1.(blk_code)) = tl (b2.(blk_code)).
Print fst.
Print hd.

Definition list_equal (b:block) :=
match hdb b with
  | None => [::]
  | Some h => (h :: tl b.(blk_code))
end.


Definition head (b:block) :=
match b.(blk_code) with
  | [::] => [::]
  | h :: t => [::h]
end.
Print find_function.
Print definition.
Print cfg.

(*(if (decide (fn1.(df_prototype) = fn2.(df_prototype))) then True else False) /\*)


Definition fulldefinition (m1 m2: mcfg) :=
forall fnid fn1 fn2, 
(*Fetching a function_id (fnid) always returns some result*)
(find_function m1 fnid = Some fn1) /\ (find_function m2 fnid = Some fn2) /\

(*These bits of definition are all equal*)

(*ADD DF_PROTOTYPE*)
(if (decide (fn1.(df_args) = fn2.(df_args))) then True else False) /\


(*Convert definition to CFG*)
forall cfg cfg1, (df_instrs fn1) = cfg /\ (df_instrs fn2) = cfg1 /\
(if (decide ((init cfg) = (init cfg1))) then True else False) /\
(*These bits of the CFG are all equal*)

forall bkid bk1 bk2,
(*Fetching a block_id (bkid) always returns some result*)
(find_block (blks (df_instrs fn1)) bkid = Some bk1) /\ (find_block (blks (df_instrs fn2)) bkid = Some bk2) /\


(*The blk_id, blk_phis and the blk_term are all equal*)
(if (decide (bk1.(blk_id) = bk2.(blk_id))) then True else False) /\
(if (decide (bk1.(blk_phis) = bk2.(blk_phis))) then True else False) /\
(if (decide (bk1.(blk_term) = bk2.(blk_term))) then True else False) /\
hd_fst_block_equal bk1 bk2 /\


(*The execution of the head of both blocks are equal*)
hd_block_equal m1 m2 fnid bkid bk1 bk2 /\


(*The body of both blocks are equal *)
tl_block_equal bk1 bk2 /\

bk1.(blk_code) = head bk1 ++ tl bk1.(blk_code) /\
bk2.(blk_code) = head bk2 ++ tl bk2.(blk_code)

(*bk1.(blk_code) = (*hd + tl*)
  bk2.(blk_code) = (*hd + tl*)
*)
.

Lemma terminate_equiv : forall (r:Trace()->Trace()->Prop) prog prog1 mem t e s fn bk pt,
trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
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
              | DVALUE_CodePointer _ => failwith "Br got non-bool value"
              | DVALUE_Addr _ => failwith "Br got non-bool value"
              | DVALUE_I1 comparison_bit =>
                  if
                   StepSemantics.Int1.eq comparison_bit
                     StepSemantics.Int1.one
                  then inr br1
                  else inr br2
              | DVALUE_I32 _ => failwith "Br got non-bool value"
              | DVALUE_I64 _ => failwith "Br got non-bool value"
              | DVALUE_Poison => failwith "Br got non-bool value"
              end; do st <- jump prog fn bk br e s; Jump st
          | TERM_Br_1 br => do st <- jump prog fn bk br e s; Jump st
          | TERM_Switch _ _ _ => t_raise "Unsupport LLVM terminator"
          | TERM_IndirectBr _ _ => t_raise "Unsupport LLVM terminator"
          | TERM_Resume _ => t_raise "Unsupport LLVM terminator"
          | TERM_Invoke _ _ _ _ => t_raise "Unsupport LLVM terminator"
          end
        with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog s')
        | Obs (Fin s0) => Vis (Fin s0)
        | Obs (Err s0) => Vis (Err s0)
        | Obs (Eff m) => Vis (Eff (effects_map (step_sem prog) m))
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
        | inl e3 => Vis (Eff e3)
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
              | DVALUE_CodePointer _ => failwith "Br got non-bool value"
              | DVALUE_Addr _ => failwith "Br got non-bool value"
              | DVALUE_I1 comparison_bit =>
                  if
                   StepSemantics.Int1.eq comparison_bit
                     StepSemantics.Int1.one
                  then inr br1
                  else inr br2
              | DVALUE_I32 _ => failwith "Br got non-bool value"
              | DVALUE_I64 _ => failwith "Br got non-bool value"
              | DVALUE_Poison => failwith "Br got non-bool value"
              end; do st <- jump prog1 fn bk br e s; Jump st
          | TERM_Br_1 br => do st <- jump prog1 fn bk br e s; Jump st
          | TERM_Switch _ _ _ => t_raise "Unsupport LLVM terminator"
          | TERM_IndirectBr _ _ => t_raise "Unsupport LLVM terminator"
          | TERM_Resume _ => t_raise "Unsupport LLVM terminator"
          | TERM_Invoke _ _ _ _ => t_raise "Unsupport LLVM terminator"
          end
        with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog1 s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog1 s')
        | Obs (Fin s0) => Vis (Fin s0)
        | Obs (Err s0) => Vis (Err s0)
        | Obs (Eff m) => Vis (Eff (effects_map (step_sem prog1) m))
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
        | inl e3 => Vis (Eff e3)
        | inr (m', v, k) => Tau () (memD m' (k v))
        end
    | Tau x d' => Tau x (memD mem d')
    end
  with
  | Vis a => Vis a
  | Tau a b => Tau a b
  end.
Proof. Admitted.
Hint Resolve terminate_equiv.


Lemma jump_equiv : forall (r:Trace()->Trace()->Prop) prog prog1 mem fn pt bk br1 e s,
trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
  match
    match
      match
        match (do st <- jump prog fn bk br1 e s; Jump st) with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog s')
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
    | Vis (Eff e2) =>
        match mem_step e2 mem with
        | inl e3 => Vis (Eff e3)
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
        match (do st <- jump prog1 fn bk br1 e s; Jump st) with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog1 s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := pt |}, e, s)
              (step_sem prog1 s')
        | Obs (Fin s0) => Vis (Fin s0)
        | Obs (Err s0) => Vis (Err s0)
        | Obs (Eff m) =>
            Vis (Eff (effects_map (step_sem prog1) m))
        end
      with
      | Vis v0 => Vis (trace_map (fun _ : state => ()) <$> v0)
      | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
      end
    with
    | Vis (Fin _ as x0) => Vis x0
    | Vis (Err _ as x0) => Vis x0
    | Vis (Eff e2) =>
        match mem_step e2 mem with
        | inl e3 => Vis (Eff e3)
        | inr (m', v0, k) => Tau () (memD m' (k v0))
        end
    | Tau x0 d' => Tau x0 (memD mem d')
    end
  with
  | Vis a => Vis a
  | Tau a b => Tau a b
  end.




Proof. Admitted.
Hint Resolve jump_equiv.

(*a link from blk1 to the head and the tl*)

Lemma test123 : forall prog prog1, fulldefinition prog prog1 -> forall st mem, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog1 st)).
Proof. intros prog prog1 H. pcofix CIH. (*
intros. pfold.


assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))).
destruct (memD mem (sem prog st)); eauto. rewrite H0. clear H0.

assert ((memD mem (sem prog1 st)) = unroll (memD mem (sem prog1 st))).
destruct (memD mem (sem prog1 st)); eauto. rewrite H0. clear H0.


destruct st. destruct p. destruct p.
generalize H. intros. unfold fulldefinition in H0.
specialize (H0 fn). simpl.

remember (find_function prog fn) as find_func_fn.
remember (find_function prog1 fn) as find_func_fn1.


destruct find_func_fn, find_func_fn1.
  +specialize (H0 d d0). destruct H0. clear H0. destruct H1. clear H0.
destruct H1. destruct d, d0. specialize (H1 df_instrs df_instrs0).
simpl in *. destruct H1. clear H1. destruct H2. clear H1.
destruct H2. unfold is_left in *. destruct (decide (df_args = df_args0)). clear H0.
destruct (decide (init df_instrs = init df_instrs0)). clear H1. subst.



remember (find_block (blks df_instrs) bk) as find_block_fn.
remember (find_block (blks df_instrs0) bk) as find_block_fn1.
destruct find_block_fn, find_block_fn1.


 specialize (H2 bk b b0). 
destruct H2. destruct H1.
destruct H2. destruct H3. destruct H4. destruct H5. destruct H6.
destruct H7. destruct H8.


destruct b, b0.
simpl in *. unfold hd_fst_block_equal in H6. unfold hd_block_equal in H6.  unfold hdb in H6.
unfold tl_block_equal in H7.
destruct blk_code, blk_code0. simpl in *.
inversion H6.
unfold hd_fst_block_equal in H5.  unfold hdb in H5. simpl in H5. inversion H5.
unfold hd_fst_block_equal in H5. unfold hdb in H5. simpl in H5. destruct p. inversion H5.
simpl in *.
destruct (decide (blk_id = blk_id0)), (decide (blk_phis = blk_phis0)),
(decide (blk_term = blk_term0)), p, p0.
unfold hd_fst_block_equal in H5. unfold hdb in H5. simpl in H5.
unfold block_to_cmd in *. simpl in *.
unfold blk_term_id in *.
specialize (H6 e s). rewrite <- Heqfind_func_fn in H6.
rewrite <- Heqfind_func_fn1 in H6. simpl in *.
rewrite <- Heqfind_block_fn in H6.
rewrite <- Heqfind_block_fn1 in H6. simpl in *.


unfold blk_term_id in *. subst.
destruct blk_term0. simpl in *.




destruct (decide (i = i1)), (decide (i1 = i1)), (decide (i = pt)), (decide (pt = i1)); simpl in *; subst; simpl in *; eauto.


(*END CASE1*)
destruct t; simpl; auto.
destruct v; simpl; auto.
destruct (eval_op e (Some t) v); simpl; auto.
destruct s; simpl; auto.
destruct f; simpl; eauto.
destruct s; simpl; auto.
destruct f; simpl; eauto.
destruct v; simpl; auto.
destruct (eval_op e (Some t) v); simpl; auto.
destruct v0; simpl; auto. simpl in *.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; auto.

rewrite H6.

(*END CASE1*)
assert (pt = pt) by auto. apply n in H5. inversion H5.
apply n in e2; inversion e2.


(*BODY TAIL CASE*)


destruct (find_instr blk_code0 pt i1); simpl in *; eauto.
destruct p; simpl in *; eauto.
destruct c; simpl in *; eauto.
destruct o; simpl in *; eauto.
destruct pt; simpl in *; eauto.
destruct i; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl; eauto.
destruct i; simpl; eauto.

unfold find_function_entry. simpl.
(*GENERALIZE AGAIN*)


generalize H. intro funcentry.
specialize (funcentry id0).


remember (find_function prog id0) as findfuncentry.
remember (find_function prog1 id0) as findfuncentry1.


destruct findfuncentry, findfuncentry1. specialize (funcentry d d0). destruct d, d0.
simpl in *. destruct funcentry. clear H5. destruct H7. clear H5.
unfold is_left in *; simpl in *. destruct (decide (df_args = df_args1)); simpl in *.
destruct H7. clear H5. specialize (H7 df_instrs1 df_instrs2).
destruct H7. clear H5. destruct H7. clear H5. subst.
destruct (decide (init df_instrs1 = init df_instrs2)); simpl in *; eauto.
subst. rewrite e0. destruct H7. clear H5.
specialize (H7 (init df_instrs2)).
remember (find_block (blks df_instrs1) (init df_instrs2)) as funcfindblock.
remember (find_block (blks df_instrs2) (init df_instrs2)) as funcfindblock1.
destruct funcfindblock, funcfindblock1.
unfold blk_entry_id.  specialize (H7 b b0).
destruct H7. clear H5. destruct H7. clear H5.
destruct H7. destruct H7. destruct H10. destruct H11.
destruct H12. destruct H13. destruct H14.
destruct b, b0. destruct blk_code, blk_code1.
    +unfold hd_block_equal in H12. unfold hdb in H12. simpl in H12. inversion H12.
    +unfold hd_block_equal in H12. unfold hdb in H12. simpl in H12. inversion H12.
    +unfold hd_block_equal in H12. unfold hdb in H12. simpl in H12. destruct p. inversion H12.
    +simpl in *. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct p, p0. unfold hd_fst_block_equal in H11. unfold hdb in H11. simpl in H11.
subst. eauto.
    +specialize (H7 b b). destruct H7. destruct H7. inversion H7.
    +specialize (H7 b b). destruct H7. inversion H5.
    +specialize (H7 {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i0) :: blk_code0;
       blk_term := (i1, t) |} {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i0) :: blk_code0;
       blk_term := (i1, t) |}). destruct H7. inversion H5.
    +destruct H7. inversion H5.
    +destruct H7. inversion H5.
    +specialize (funcentry d d). destruct funcentry. destruct H7. inversion H7.
    +specialize (funcentry d d). destruct funcentry. inversion H5.
    +specialize (funcentry {|
                     df_prototype := df_prototype0;
                     df_args := df_args0;
                     df_instrs := df_instrs0 |}{|
                     df_prototype := df_prototype0;
                     df_args := df_args0;
                     df_instrs := df_instrs0 |}). destruct funcentry. inversion H5.

(*function_entry *) 









(*FINISH*)

destruct ptr; simpl; eauto.
destruct (eval_op e (Some t1) v); simpl; eauto.
destruct v0; simpl; eauto.
destruct i; simpl; eauto.
destruct fn0; simpl; eauto.
destruct i; simpl; eauto.
(*function_entry*) 


unfold find_function_entry. simpl.
(*GENERALIZE AGAIN*)


generalize H. intro funcentry.
specialize (funcentry id).


remember (find_function prog id) as findfuncentry.
remember (find_function prog1 id) as findfuncentry1.


destruct findfuncentry, findfuncentry1. specialize (funcentry d d0). destruct d, d0.
simpl in *. destruct funcentry. clear H5. destruct H7. clear H5.
unfold is_left in *; simpl in *. destruct (decide (df_args = df_args1)); simpl in *.
destruct H7. clear H5. specialize (H7 df_instrs1 df_instrs2).
destruct H7. clear H5. destruct H7. clear H5. subst.
destruct (decide (init df_instrs1 = init df_instrs2)); simpl in *; eauto.
subst. rewrite e0. destruct H7. clear H5.
specialize (H7 (init df_instrs2)).
remember (find_block (blks df_instrs1) (init df_instrs2)) as funcfindblock.
remember (find_block (blks df_instrs2) (init df_instrs2)) as funcfindblock1.
destruct funcfindblock, funcfindblock1.
unfold blk_entry_id. specialize (H7 b b0).
destruct H7. clear H5. destruct H7. clear H5.
destruct H7. destruct H7. destruct H10. destruct H11.
destruct H12. destruct H13. destruct H14. 
destruct b, b0. destruct blk_code, blk_code1; unfold hd_fst_block_equal in H11; simpl in H11; try destruct p; try destruct p0; try inversion H11.
    +simpl in *. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct t0; simpl; eauto. subst; eauto.
    +specialize (H7 b b). destruct H7. destruct H7. inversion H7.
    +specialize (H7 b b). destruct H7. inversion H5.
    +specialize (H7 {|
                     blk_id := blk_id0;
                     blk_phis := blk_phis0;
                     blk_code := (i1, i0) :: blk_code0;
                     blk_term := (i1, t) |}  {|
                     blk_id := blk_id0;
                     blk_phis := blk_phis0;
                     blk_code := (i1, i0) :: blk_code0;
                     blk_term := (i1, t) |} ). destruct H7. inversion H5.
    +destruct H7. inversion H5.
    +destruct H7. inversion H5.
    +specialize (funcentry d d). destruct funcentry. destruct H7. inversion H7.
    +specialize (funcentry d d). destruct funcentry. inversion H5.
    +specialize (funcentry {|
                    df_prototype := df_prototype;
                    df_args := df_args0;
                    df_instrs := df_instrs |}{|
                    df_prototype := df_prototype;
                    df_args := df_args0;
                    df_instrs := df_instrs |}). destruct funcentry. inversion H5.





(*function_entry*)
destruct val, ptr; simpl; eauto.

destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl; eauto.
destruct  v2; simpl; eauto. eapply terminate_equiv.
assert (pt = pt) by auto. apply n0 in H5. inversion H5.
assert (i1 = i1) by auto. apply n0 in H5. inversion H5.
assert (i1 = i1) by auto. apply n in H5. inversion H5.

 eapply terminate_equiv.
 eapply terminate_equiv.
(*JUMP*)




rewrite H6. destruct i1. destruct i2; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i1; simpl in *; eauto.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct ((find_function_entry prog1 id0)); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ((find_function_entry prog1 id0)); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct i2; simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i1; simpl in *; eauto.
destruct ((find_function_entry prog1 id)); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct t0; simpl in *; eauto.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
(*SPECIAL CASE*)



(*equal*)
destruct (find_instr blk_code0 pt i); simpl in *; eauto.
destruct p; simpl; eauto.
destruct c; simpl; eauto.
destruct o; simpl; eauto.
destruct pt; simpl; eauto.
destruct i3; simpl; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i3; simpl in *; eauto.
(*function_entry*) 



unfold find_function_entry. simpl.
(*GENERALIZE AGAIN*)


generalize H. intro funcentry.
specialize (funcentry id0).


remember (find_function prog id0) as findfuncentry.
remember (find_function prog1 id0) as findfuncentry1.

(* CHECK*)
destruct findfuncentry, findfuncentry1. specialize (funcentry d d0). destruct d, d0.
simpl in *. destruct funcentry. clear H5. destruct H7. clear H5.
unfold is_left in *; simpl in *. destruct (decide (df_args = df_args1)); simpl in *.
destruct H7. clear H5. specialize (H7 df_instrs1 df_instrs2).
destruct H7. clear H5. destruct H7. clear H5. subst.
destruct (decide (init df_instrs1 = init df_instrs2)); simpl in *; eauto.
rewrite e2.
subst.  destruct H7. clear H5.
specialize (H7 (init df_instrs2)).
remember (find_block (blks df_instrs1) (init df_instrs2)) as funcfindblock.
remember (find_block (blks df_instrs2) (init df_instrs2)) as funcfindblock1.
destruct funcfindblock, funcfindblock1.
unfold blk_entry_id. specialize (H7 b b0).
destruct H7. clear H5. destruct H7. clear H5.
destruct H7. destruct H7. destruct H10. destruct H11.
destruct H12. destruct H13. destruct H14. 
destruct b, b0; simpl in *. destruct blk_code, blk_code1; unfold hd_fst_block_equal in H11; simpl in H11; try destruct p; try destruct p0; try inversion H11.
    +simpl in *. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
    +specialize (H7 b b). destruct H7. destruct H7. inversion H7.
    +specialize (H7 b b). destruct H7. inversion H5.
    +specialize (H7 {|
                      blk_id := blk_id0;
                      blk_phis := blk_phis0;
                      blk_code := (i1, i2) :: blk_code0;
                      blk_term := (i, t) |} {|
                      blk_id := blk_id0;
                      blk_phis := blk_phis0;
                      blk_code := (i1, i2) :: blk_code0;
                      blk_term := (i, t) |} ). destruct H7. inversion H5.
    +destruct H7. inversion H5.
    +destruct H7. inversion H5.
    +specialize (funcentry d d). destruct funcentry. destruct H7. inversion H7.
    +specialize (funcentry d d). destruct funcentry. inversion H5.
    +specialize (funcentry {|
                    df_prototype := df_prototype;
                    df_args := df_args0;
                    df_instrs := df_instrs |}{|
                    df_prototype := df_prototype;
                    df_args := df_args0;
                    df_instrs := df_instrs |}). destruct funcentry. inversion H5.

(*function_entry*)
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl; eauto.
destruct i3; simpl; eauto.
destruct fn0; simpl in *; eauto.
destruct i3; simpl in *; eauto.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.


(*FUNCTION ENTRY 2*)
(*function_entry*) 


unfold find_function_entry. simpl.
(*GENERALIZE AGAIN*)


generalize H. intro funcentry.
specialize (funcentry id).


remember (find_function prog id) as findfuncentry.
remember (find_function prog1 id) as findfuncentry1.


destruct findfuncentry, findfuncentry1. specialize (funcentry d d0). destruct d, d0.
simpl in *. destruct funcentry. clear H5. destruct H7. clear H5.
unfold is_left in *; simpl in *. destruct (decide (df_args = df_args1)); simpl in *.
destruct H7. clear H5. specialize (H7 df_instrs1 df_instrs2).
destruct H7. clear H5. destruct H7. clear H5. subst.
destruct (decide (init df_instrs1 = init df_instrs2)); simpl in *; eauto.
subst. rewrite e2. destruct H7. clear H5.
specialize (H7 (init df_instrs2)).
remember (find_block (blks df_instrs1) (init df_instrs2)) as funcfindblock.
remember (find_block (blks df_instrs2) (init df_instrs2)) as funcfindblock1.
destruct funcfindblock, funcfindblock1.
unfold blk_entry_id. specialize (H7 b b0).
destruct H7. clear H5. destruct H7. clear H5.
destruct H7. destruct H7. destruct H10. destruct H11.
destruct H12. destruct H13. destruct H14. 
destruct b, b0. destruct blk_code, blk_code1; unfold hd_fst_block_equal in H11; simpl in H11; try destruct p; try destruct p0; try inversion H11.
    +simpl in *. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct t0; simpl; eauto. subst; eauto.
destruct t0; simpl; eauto.
-specialize (H7 {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i2) :: blk_code0;
       blk_term := (i, t) |} {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i2) :: blk_code0;
       blk_term := (i, t) |}). destruct H7. destruct H7. inversion H7. 
- destruct H7. inversion H5.
-
destruct H7. inversion H5.
-specialize (funcentry d d). destruct funcentry. destruct H7. inversion H7.
-specialize (funcentry d d). destruct funcentry. inversion H5.
-specialize (funcentry {|
                    df_prototype := df_prototype;
                    df_args := df_args0;
                    df_instrs := df_instrs |}{|
                    df_prototype := df_prototype;
                    df_args := df_args0;
                    df_instrs := df_instrs |}).
destruct funcentry. inversion H5.



(*function_entry*)


(*function_entry*) 


unfold find_function_entry. simpl.
(*GENERALIZE AGAIN*)


generalize H. intro funcentry.
specialize (funcentry id).


remember (find_function prog id) as findfuncentry.
remember (find_function prog1 id) as findfuncentry1.


destruct findfuncentry, findfuncentry1. specialize (funcentry d d0). destruct d, d0.
simpl in *. destruct funcentry. clear H5. destruct H7. clear H5.
unfold is_left in *; simpl in *. destruct (decide (df_args = df_args1)); simpl in *.
destruct H7. clear H5. specialize (H7 df_instrs1 df_instrs2).
destruct H7. clear H5. destruct H7. clear H5. subst.
destruct (decide (init df_instrs1 = init df_instrs2)); simpl in *; eauto.
subst. rewrite e2. destruct H7. clear H5.
specialize (H7 (init df_instrs2)).
remember (find_block (blks df_instrs1) (init df_instrs2)) as funcfindblock.
remember (find_block (blks df_instrs2) (init df_instrs2)) as funcfindblock1.
destruct funcfindblock, funcfindblock1.
unfold blk_entry_id. specialize (H7 b b0).
destruct H7. clear H5. destruct H7. clear H5.
destruct H7. destruct H7. destruct H10. destruct H11.
destruct H12. destruct H13. destruct H14. 
destruct b, b0. destruct blk_code, blk_code1; unfold hd_fst_block_equal in H11; simpl in H11; try destruct p; try destruct p0; try inversion H11.
    +simpl in *. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct t0; simpl; eauto. subst; eauto.
destruct t0; simpl; eauto.
-specialize (H7 {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i2) :: blk_code0;
       blk_term := (i, t) |} {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i2) :: blk_code0;
       blk_term := (i, t) |}). destruct H7. destruct H7. inversion H7. 
- specialize (H7 {|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i0) :: blk_code0;
       blk_term := (i, t) |}{|
       blk_id := blk_id0;
       blk_phis := blk_phis0;
       blk_code := (i1, i0) :: blk_code0;
       blk_term := (i, t) |}). destruct H7. inversion H5. simpl; eauto. destruct H7. inversion H5.
destruct H7. inversion H5.
-specialize (funcentry d d). destruct funcentry. destruct H7. inversion H7.
-specialize (funcentry d d). destruct funcentry. inversion H5.
simpl; eauto.

destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.


eapply terminate_equiv.
eapply terminate_equiv.
assert (i1 = i1) by auto. apply n0 in H5. inversion H5.
assert (i1 = i1) by auto. apply n0 in H5. inversion H5.

inversion H4.
inversion H3.
inversion H3.
inversion H2.
inversion H2.
inversion H2.
inversion H2.
simpl in *. specialize (H2 bk b b). destruct H2. destruct H1.
rewrite H1 in Heqfind_block_fn1. inversion Heqfind_block_fn1.
specialize (H2 bk b b). destruct H2. 
rewrite H0 in Heqfind_block_fn. inversion Heqfind_block_fn.


specialize (H2 bk).  simpl; eauto.
inversion H1.
inversion H0. specialize (H0 d d). destruct H0.
destruct H1. inversion H1.
specialize (H0 d d); destruct H0. inversion H0.
simpl; eauto.

Qed.
*) Admitted.