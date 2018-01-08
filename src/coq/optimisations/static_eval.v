(*Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.congruence2.
Require Import Vellvm.DecidableEquality.
Require Import Vellvm.StepSemantics.*)

Require Import ZArith List String Omega.
Require Import Vellvm.optimisations.congruence2.
Require Import Vellvm.optimisations.step_trace.

Require Import Vellvm.StepSemantics.
Require Import Vellvm.Ollvm_ast  Vellvm.Classes Vellvm.CFG.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.

Print trace_equiv.
SearchAbout trace_equiv.

Require Import compcert.lib.Integers.




Definition get_int_from_int1 (i:int1) : Ollvm_ast.int := Int1.unsigned i.

Definition get_int_from_int32 (i:int32) : Ollvm_ast.int :=
      Int32.unsigned i.

Definition get_int_from_int64 (i:int64) : Ollvm_ast.int := Int64.unsigned i.

Print Ollvm_ast.value.
Definition eval_iop_decast (o:Ollvm_ast.typ) (iop:ibinop) (d1 d2: dvalue)  :=
  match (eval_iop o iop d1 d2) with
  | inl _ => None
  | inr s => match s with
             | DVALUE_I32 a =>  Some (SV (OP_IBinop (Add false false) (TYPE_I (32%Z))  (SV (VALUE_Integer (get_int_from_int32 a)))  (SV (VALUE_Integer 0%Z))))
             | _ => None
               end
    end.
Print Ollvm_ast.typ.
Print OP_IBinop.
Print ibinop.
Definition get_expr (s:  Ollvm_ast.value) (top:option typ) : err dvalue :=
  match s with
  | SV a => match a with
            | VALUE_Integer x => match top with
                                 | None => mret (DV (VALUE_Integer x))
                                 | Some (TYPE_I (32%Z)) => (coerce_integer_to_int (32%Z) x)
                                 | _ => failwith "wrongint"
                                 end
            | _ => failwith "none"
            end
  end.
Print ibinop.
Print OP_IBinop.
Print ibinop.


Definition optimise_expr_op (o:Ollvm_ast.value) : option (Ollvm_ast.value) :=
  match o with
  | SV a => match a with
                                            
            | OP_IBinop (And) _ _ _ => None                                            
            | OP_IBinop (Shl _ _) _ _ _ => None                                            

                                            
                                            
            | OP_IBinop iop t op1 op2 => match (get_expr op1 (Some t)), (get_expr op2 (Some t)) with
                                         | (inr b), (inr c)  => eval_iop_decast t iop b c
                                         | (_), (_) => None
                                           end
            | _ => None
              end
  end.


Definition optimise_expr (o:Ollvm_ast.value) : Ollvm_ast.value :=
  match (optimise_expr_op o) with
  | None => o
  | Some a => a
  end.




(*opt pc -> mcfg -> instr -> instr_id * instr*)

Print instr.


Definition optimise_instr (i:instr) : instr :=
  match i with
  | INSTR_Op a => INSTR_Op (optimise_expr a)
  | rest => rest
  end.


Definition optimisation (p:pc) (m:mcfg) (i:instr) : instr_id * instr := (pt p, optimise_instr i).



Lemma step_trace_refl : forall A, compare_trace A A.
Proof. intros. constructor. Qed.
Hint Resolve step_trace_refl.



Lemma step_trace_one_right : forall A B, compare_trace (fin A) (step_trace.tau B (fin A)).
Proof. intros. constructor. constructor. Qed.
Hint Resolve step_trace_one_right.


Lemma find_function_equiv : forall m id mem0 s fid bid t e args id0, compare_trace
    match
      (do fnentry <-
       trywith ("stepD: no function " ++ string_of id0) (find_function_entry m id0);
       let
       'FunctionEntry ids pc_f := fnentry in
        do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
        Step (pc_f, combine ids dvs, KRet e id {| fn := fid; bk := bid; pt := t |} :: s))
    with
    | Step s' =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (tauitem mem0 s'))
    | Jump s' =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (tauitem mem0 s'))
    | Obs (Fin s') =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (visitem mem0 (Fin s')))
    | Obs (Err s') =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (visitem mem0 (Err s')))
    | Obs (Eff s') =>
        match mem_step s' mem0 with
        | inl _ => fin (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
        | inr (m', v, k) =>
            step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
              (fin (tauitem m' (k v)))
        end
    end
    match
      (do fnentry <-
       trywith ("stepD: no function " ++ string_of id0)
         (find_function_entry (modul_opt optimisation m) id0);
       let
       'FunctionEntry ids pc_f := fnentry in
        do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args;
        Step (pc_f, combine ids dvs, KRet e id {| fn := fid; bk := bid; pt := t |} :: s))
    with
    | Step s' =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (tauitem mem0 s'))
    | Jump s' =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (tauitem mem0 s'))
    | Obs (Fin s') =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (visitem mem0 (Fin s')))
    | Obs (Err s') =>
        step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
          (fin (visitem mem0 (Err s')))
    | Obs (Eff s') =>
        match mem_step s' mem0 with
        | inl _ => fin (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
        | inr (m', v, k) =>
            step_trace.tau (tauitem mem0 (mk_state (congruence2.mk_pc fid bid (IId id)) e s))
              (fin (tauitem m' (k v)))
        end
    end.
Proof. intros. unfold find_function_entry. simpl in *. rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct (find_function m id0). simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc. destruct (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl in *; eauto. destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. unfold optimisation. unfold block_opt. unfold blk_entry_id. simpl in *. unfold code_opt. simpl in *. destruct blk_code. simpl in *. auto. simpl in *. destruct p. simpl in *. auto. simpl in *. auto. Qed.
Hint Resolve find_function_equiv.


Lemma add_i32_correct : forall nuw nsw x x0 e, eval_op e None
    match
      match
        (if
          nuw && Int32.eq (Int32.add_carry (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
          || nsw &&
             Int32.eq (Int32.add_overflow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
         then DVALUE_Poison
         else DVALUE_I32 (Int32.add (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV (OP_IBinop (Add nuw nsw) (TYPE_I 32) (SV (VALUE_Integer x)) (SV (VALUE_Integer x0)))
    end =
  inr
    (if
      nuw && Int32.eq (Int32.add_carry (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
      || nsw &&
         Int32.eq (Int32.add_overflow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
     then DVALUE_Poison
     else DVALUE_I32 (Int32.add (Int32.repr x) (Int32.repr x0))).
Proof. intros. remember ( nuw && Int32.eq (Int32.add_carry (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one) as A. remember ( Int32.eq (Int32.add_overflow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one) as B. destruct A, B, nuw, nsw; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqA; try rewrite <- HeqB; simpl in *; eauto; try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; simpl in *; eauto; try inversion HeqA. Qed.
Hint Resolve add_i32_correct.


Lemma sub_i32_correct : forall e nuw nsw x x0, eval_op e None
    match
      match
        (if
          nuw &&
          Int32.eq (Int32.sub_borrow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
          || nsw &&
             Int32.eq (Int32.sub_overflow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
         then DVALUE_Poison
         else DVALUE_I32 (Int32.sub (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV
          (OP_IBinop (Ollvm_ast.Sub nuw nsw) (TYPE_I 32) (SV (VALUE_Integer x))
             (SV (VALUE_Integer x0)))
    end =
  inr
    (if
      nuw && Int32.eq (Int32.sub_borrow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
      || nsw &&
         Int32.eq (Int32.sub_overflow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one
     then DVALUE_Poison
     else DVALUE_I32 (Int32.sub (Int32.repr x) (Int32.repr x0))).
Proof. intros. remember (Int32.eq (Int32.sub_borrow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one) as A. remember (Int32.eq (Int32.sub_overflow (Int32.repr x) (Int32.repr x0) Int32.zero) Int32.one) as B. destruct nuw, nsw, A, B; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqA; try rewrite <- HeqB; simpl in *; eauto; try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto. Qed.
Hint Resolve sub_i32_correct.

Lemma mult_i32_correct : forall e nuw nsw x x0, 
  eval_op e None
    match
      match
        (if
          nuw &&
          (Int32.unsigned (Int32.repr x) * Int32.unsigned (Int32.repr x0) >?
           Int32.unsigned (Int32.mul (Int32.repr x) (Int32.repr x0)))
          || nsw &&
             ((Int32.min_signed >? Int32.signed (Int32.repr x) * Int32.signed (Int32.repr x0))
              || (Int32.signed (Int32.repr x) * Int32.signed (Int32.repr x0) >?
                  Int32.max_signed))
         then DVALUE_Poison
         else DVALUE_I32 (Int32.mul (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV (OP_IBinop (Mul nuw nsw) (TYPE_I 32) (SV (VALUE_Integer x)) (SV (VALUE_Integer x0)))
    end =
  inr
    (if
      nuw &&
      (Int32.unsigned (Int32.repr x) * Int32.unsigned (Int32.repr x0) >?
       Int32.unsigned (Int32.mul (Int32.repr x) (Int32.repr x0)))
      || nsw &&
         ((Int32.min_signed >? Int32.signed (Int32.repr x) * Int32.signed (Int32.repr x0))
          || (Int32.signed (Int32.repr x) * Int32.signed (Int32.repr x0) >? Int32.max_signed))
     then DVALUE_Poison
     else DVALUE_I32 (Int32.mul (Int32.repr x) (Int32.repr x0))).
Proof. intros. remember (Int32.unsigned (Int32.repr x) * Int32.unsigned (Int32.repr x0) >?
           Int32.unsigned (Int32.mul (Int32.repr x) (Int32.repr x0))) as A. remember ((Int32.min_signed >? Int32.signed (Int32.repr x) * Int32.signed (Int32.repr x0))
              || (Int32.signed (Int32.repr x) * Int32.signed (Int32.repr x0) >?
Int32.max_signed)) as B.                                     destruct nuw, nsw, A, B; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqA; try rewrite <- HeqB; simpl in *; eauto;  try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto. Qed.
Hint Resolve mult_i32_correct.

Lemma div_i32_unsigned_correct : forall e exact x0 x, eval_op e None
    match
      match
        (if exact && ~~ (Int32.unsigned (Int32.repr x) mod Int32.unsigned (Int32.repr x0) =? 0)
         then DVALUE_Poison
         else DVALUE_I32 (Int32.divu (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV (OP_IBinop (UDiv exact) (TYPE_I 32) (SV (VALUE_Integer x)) (SV (VALUE_Integer x0)))
    end =
  inr
    (if exact && ~~ (Int32.unsigned (Int32.repr x) mod Int32.unsigned (Int32.repr x0) =? 0)
     then DVALUE_Poison
     else DVALUE_I32 (Int32.divu (Int32.repr x) (Int32.repr x0)))
.
Proof. intros. remember ( ~~ (Int32.unsigned (Int32.repr x) mod Int32.unsigned (Int32.repr x0) =? 0)) as A. destruct exact, A; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqA; simpl in *; eauto;  try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto. Qed.
Hint Resolve div_i32_unsigned_correct.


Lemma shru_i32_correct : forall e exact x x0, eval_op e None
    match
      match
        (if Int32.unsigned (Int32.repr x0) >=? 32
         then DV VALUE_Undef
         else
          if
           exact &&
           ~~ (Int32.unsigned (Int32.repr x) mod 2 ^ Int32.unsigned (Int32.repr x0) =? 0)
          then DVALUE_Poison
          else DVALUE_I32 (Int32.shru (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV (OP_IBinop (LShr exact) (TYPE_I 32) (SV (VALUE_Integer x)) (SV (VALUE_Integer x0)))
    end =
  inr
    (if Int32.unsigned (Int32.repr x0) >=? 32
     then DV VALUE_Undef
     else
      if
       exact && ~~ (Int32.unsigned (Int32.repr x) mod 2 ^ Int32.unsigned (Int32.repr x0) =? 0)
      then DVALUE_Poison
      else DVALUE_I32 (Int32.shru (Int32.repr x) (Int32.repr x0))).
Proof. intros. remember (  ~~ (Int32.unsigned (Int32.repr x) mod 2 ^ Int32.unsigned (Int32.repr x0) =? 0)) as A. remember ( Int32.unsigned (Int32.repr x0) >=? 32) as B. destruct exact, A, B; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqA; try rewrite <- HeqB; simpl in *; eauto;  try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto. Qed.
Hint Resolve shru_i32_correct.

Lemma div_i32_signed_correct : forall exact e x x0, eval_op e None
    match
      match
        (if exact && ~~ (Int32.signed (Int32.repr x) mod Int32.signed (Int32.repr x0) =? 0)
         then DVALUE_Poison
         else DVALUE_I32 (Int32.divs (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV (OP_IBinop (SDiv exact) (TYPE_I 32) (SV (VALUE_Integer x)) (SV (VALUE_Integer x0)))
    end =
  inr
    (if exact && ~~ (Int32.signed (Int32.repr x) mod Int32.signed (Int32.repr x0) =? 0)
     then DVALUE_Poison
     else DVALUE_I32 (Int32.divs (Int32.repr x) (Int32.repr x0))).
Proof. intros. remember ( ~~ (Int32.signed (Int32.repr x) mod Int32.signed (Int32.repr x0) =? 0)) as A. destruct exact, A; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqA; simpl in *; eauto;  try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto. Qed.
Hint Resolve div_i32_signed_correct.

Lemma shr_correct : forall e exact x x0, eval_op e None
    match
      match
        (if Int32.unsigned (Int32.repr x0) >=? 32
         then DV VALUE_Undef
         else
          if
           exact &&
           ~~ (Int32.unsigned (Int32.repr x) mod 2 ^ Int32.unsigned (Int32.repr x0) =? 0)
          then DVALUE_Poison
          else DVALUE_I32 (Int32.shr (Int32.repr x) (Int32.repr x0)))
      with
      | DV _ => None
      | DVALUE_CodePointer _ => None
      | DVALUE_Addr _ => None
      | DVALUE_I1 _ => None
      | DVALUE_I32 a =>
          Some
            (SV
               (OP_IBinop (Add false false) (TYPE_I 32)
                  (SV (VALUE_Integer (get_int_from_int32 a))) (SV (VALUE_Integer 0))))
      | DVALUE_I64 _ => None
      | DVALUE_Poison => None
      end
    with
    | Some a => a
    | None =>
        SV (OP_IBinop (AShr exact) (TYPE_I 32) (SV (VALUE_Integer x)) (SV (VALUE_Integer x0)))
    end =
  inr
    (if Int32.unsigned (Int32.repr x0) >=? 32
     then DV VALUE_Undef
     else
      if
       exact && ~~ (Int32.unsigned (Int32.repr x) mod 2 ^ Int32.unsigned (Int32.repr x0) =? 0)
      then DVALUE_Poison
      else DVALUE_I32 (Int32.shr (Int32.repr x) (Int32.repr x0))).
Proof. intros. remember (Int32.unsigned (Int32.repr x0) >=? 32) as A. remember (  ~~ (Int32.unsigned (Int32.repr x) mod 2 ^ Int32.unsigned (Int32.repr x0) =? 0)) as B. destruct exact, A, B; simpl in *; eauto; unfold eval_i32_op; try rewrite <- HeqB; try rewrite <- HeqA; simpl in *; eauto;  try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto. Qed.
Hint Resolve shr_correct.

                              
Lemma instr_correct : forall e op, eval_op e None (optimise_expr op) =  eval_op e None op.
Proof. intros. destruct op. unfold optimise_expr. unfold optimise_expr_op. destruct e0; simpl in *; eauto. destruct v1, v2; simpl in *; eauto. destruct iop; destruct e0, e1; simpl in *; eauto; destruct t; simpl in *; eauto; destruct sz; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto;  unfold eval_iop_decast; simpl in *; unfold eval_i32_op; auto.  rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto.
        rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto.
        rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto.
        rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; eauto.
Qed.












Lemma optimisation_correct : forall st m mem,  trace_equiv (memD mem (sem m st)) (memD mem (sem (modul_opt optimisation m) st)).
Proof. intros. apply correct_instr_trace2; intros.
       -unfold optimisation. unfold same_hd_instr. simpl in *. auto.
       -unfold correct_instr1. intros. unfold step_trace.compare_exec1. simpl in *.
       -destruct iid, i; simpl in *; eauto.
        +rewrite <- instr_correct. auto. destruct fn, i; simpl in *; eauto. destruct fn, i; simpl in *; eauto.
 unfold find_function_entry. simpl in *.  rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct (find_function m id); simpl in *; eauto. simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc. destruct  (find_block (blks (df_instrs d)) (init (df_instrs d))); simpl in *; eauto. destruct t0; simpl in *; eauto. simpl in *. simpl in *. destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto. unfold blk_entry_id. simpl in *. unfold optimisation. simpl in *. unfold code_opt. simpl in *. unfold blk_term_id. simpl in *. destruct b. simpl in *. destruct blk_code. auto. simpl in *. destruct p. simpl in *. auto.
Qed.


