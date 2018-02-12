

From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Require Import Vellvm.optimisations.step_trace.



Require Import Vellvm.StepSemantics.
Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util Vellvm.Memory.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG Vellvm.Effects.
Require Import Vellvm.DecidableEquality.

Require Import paco.
Import ListNotations.
 
Require Import compcert.lib.Integers.





Definition get_int_from_int1 (i:int1) : Ollvm_ast.int := Int1.unsigned i.

Definition get_int_from_int32 (i:int32) : Ollvm_ast.int :=
      Int32.unsigned i.

Definition get_int_from_int64 (i:int64) : Ollvm_ast.int := Int64.unsigned i.

Print eval_iop.
Print value.
Print dvalue.
Print Ollvm_ast.value.


Print eval_op.


Definition eval_iop_decast (o:Ollvm_ast.typ) (iop:ibinop) (d1 d2: dvalue)  :=
  match (eval_iop o iop d1 d2) with
  | inl _ => None
  | inr s => match s with
             | DVALUE_I32 a =>  Some (SV (OP_IBinop (Add false false) (TYPE_I (32%Z))  (SV (VALUE_Integer (get_int_from_int32 a)))  (SV (VALUE_Integer 0%Z))))
             | _ => None
               end
    end.


Print eval_iop_decast.
Print eval_op.
Print INSTR_Op.

Print Expr.
Print coerce_integer_to_int.
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

Definition optimise_expr (o:Ollvm_ast.value) : option (Ollvm_ast.value) :=
  match o with
  | SV a => match a with
            | OP_IBinop iop t op1 op2 => match (get_expr op1 (Some t)), (get_expr op2 (Some t)) with
                                         | (inr b), (inr c)  => eval_iop_decast t iop b c
                                         | (_), (_) => None
                                           end
            | _ => None
              end
  end.





Definition final_optimise (o:Ollvm_ast.value) : (Ollvm_ast.value) :=
  match (optimise_expr o) with
  | None => o
  | Some a => a
    end.


Print typ.
Print Ollvm_ast.typ.

Print Ollvm_ast.value.
Print Expr.
Print ibinop.
Definition test12 : Ollvm_ast.value := SV (OP_IBinop (Add false false) (TYPE_I (32%Z)) (SV (VALUE_Integer 1%Z)) (SV (VALUE_Integer 1%Z))).


Lemma test : eval_op nil None test12 = eval_op nil None (final_optimise test12).
Proof.
  simpl in *. simpl in *. Print Int32. rewrite  Int32.add_unsigned.
  simpl in *. unfold Int32.unsigned.
  remember  (Int32.repr (Int32.intval (Int32.repr 1) + Int32.intval (Int32.repr 1))) as A.
  unfold get_int_from_int32. simpl in *. unfold Int32.unsigned. simpl in *. rewrite Int32.add_zero.
  rewrite HeqA. simpl in *. rewrite <- HeqA. rewrite Int32.repr_unsigned. auto.  Qed.

   


Lemma newtest : forall a, eval_op nil None a = eval_op nil None (final_optimise a).
Proof. intros. induction a. induction e; simpl in *; eauto. unfold eval_expr. simpl in *.
       destruct v1, v2; simpl in *; eauto. destruct e, e0; simpl in *; eauto; unfold coerce_integer_to_int; unfold final_optimise; unfold optimise_expr; simpl in *; destruct t; simpl in *; eauto; destruct sz; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto; destruct p; simpl in *; eauto. unfold eval_iop_decast. simpl in *. unfold eval_i32_op. 
destruct iop; simpl in *; eauto; try destruct nuw; try destruct nsw; simpl in *; try rewrite Int32.repr_unsigned; try rewrite Int32.add_zero; simpl in *; eauto.
       
       +remember (Int32.eq (Int32.add_carry (Int32.repr x) (Int32.repr x0) Int32.zero)
         Int32.one) as A; remember  ((Int32.eq (Int32.add_overflow (Int32.repr x) (Int32.repr x0) Int32.zero)
            Int32.one)%bool) as B; destruct A, B; simpl in *; unfold eval_i32_op; try rewrite <- HeqA; try rewrite <- HeqB; try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; simpl in *; eauto.
       +remember (Int32.eq (Int32.add_carry (Int32.repr x) (Int32.repr x0) Int32.zero)
                           Int32.one) as A; destruct A; simpl in *; unfold eval_i32_op; try rewrite <- HeqA; try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; simpl in *; eauto.
        +remember (      Int32.eq (Int32.add_overflow (Int32.repr x) (Int32.repr x0) Int32.zero)
                                  Int32.one) as A; destruct A; try rewrite <- HeqA; simpl in *; unfold eval_i32_op; try rewrite <- HeqA; try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; simpl in *; eauto.
         +remember  (Int32.eq (Int32.sub_borrow (Int32.repr x) (Int32.repr x0) Int32.zero)
         Int32.one) as A; remember  ((Int32.eq (Int32.sub_overflow (Int32.repr x) (Int32.repr x0) Int32.zero)
                                               Int32.one)%bool) as B; destruct A, B; simpl in *; eauto; unfold eval_i32_op; simpl in *; eauto; try rewrite <- HeqA; try rewrite <- HeqB; try rewrite Int32.add_zero; try rewrite Int32.repr_unsigned; simpl in *; eauto.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
         +admit.
Admitted.





(*fulldefinition = 
fun m1 m2 : mcfg =>
forall (fnid : function_id) (fn1 fn2 : definition cfg),
(find_function m1 fnid = Some fn1 /\ find_function m2 fnid = Some fn2 \/
 find_function m1 fnid = None /\ find_function m2 fnid = None) /\
(if ssrbool.is_left (df_args fn1 == df_args fn2) then True else False) /\
(forall cfg0 cfg1 : cfg,
 df_instrs fn1 = cfg0 /\
 df_instrs fn2 = cfg1 /\
 (if ssrbool.is_left (init cfg0 == init cfg1) then True else False) /\
 (forall (bkid : block_id) (bk1 bk2 : block),
  (find_block (blks (df_instrs fn1)) bkid = Some bk1 /\
   find_block (blks (df_instrs fn2)) bkid = Some bk2 \/
   find_block (blks (df_instrs fn1)) bkid = None /\
   find_block (blks (df_instrs fn2)) bkid = None) /\
  (if ssrbool.is_left (blk_id bk1 == blk_id bk2) then True else False) /\
  (if ssrbool.is_left (blk_phis bk1 == blk_phis bk2) then True else False) /\
  (if ssrbool.is_left (blk_term bk1 == blk_term bk2) then True else False) /\
  hd_fst_block_equal bk1 bk2 /\ hd_block_equal m1 m2 fnid bkid bk1 bk2))
     : mcfg -> mcfg -> Prop
 *)

Print block.

Definition hdb (b:block) :=
match b.(blk_code) with
  | [::] => None
  | h :: _ => Some h
end.



Definition hd_fst_block_equal b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => True
  | Some (h1, t1), Some (h2, t2) => h1 = h2
  | _, _ => False
end.


Definition hd_block_equal m1 m2 fnid bkid b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => True
  | Some (h1, t1), Some (h2, t2) => forall mem e s, compare_seq (exec_code1 m1 b1.(blk_code) (tauitem mem (mk_pc fnid bkid h1, e, s))) (exec_code1 m2 b2.(blk_code)
                                                                                                                              (tauitem mem (mk_pc fnid bkid h2, e, s)))
  | _, _ => False
end.











Definition block_match (m m1:mcfg) (fnid:function_id) (bk1 bk2:block) : Prop :=
(if (decide (bk1.(blk_id) = bk2.(blk_id))) then True else False) /\
(if (decide (bk1.(blk_phis) = bk2.(blk_phis))) then True else False) /\
(if (decide (bk1.(blk_term) = bk2.(blk_term))) then True else False) /\
hd_fst_block_equal bk1 bk2 /\
hd_block_equal m m1 fnid (bk1.(blk_id)) bk1 bk2
.
Print definition.


Definition find_block_match m m1 fn1 fn2 fnid bkid :=
  match (find_block (blks (df_instrs fn1)) bkid), (find_block (blks (df_instrs fn2)) bkid) with
  | None, None => True
  | Some bk1, Some bk2 => block_match m m1 fnid bk1 bk2
  | _, _ => False
  end.


Definition find_block (m m1: mcfg) (fn1 fn2: definition cfg) (fnid:function_id) (bkid: block_id) :=
  (if (decide (fn1.(df_args) = fn2.(df_args))) then True else False) /\
  (if (decide ((init (df_instrs fn1)) = (init (df_instrs fn2)))) then True else False) /\ find_block_match m m1 fn1 fn2 fnid bkid.



Definition find_function_match m m1:= forall fnid bkid,
  match (find_function m fnid), (find_function m1 fnid) with
  | None, None => True
  | Some f1, Some f2 => find_block m m1 f1 f2 fnid bkid
  | _, _ => False
    end.





Definition instr_value_optimise (i:instr) (o:value -> value) :=
  match i with
  | INSTR_Op op => INSTR_Op (o op)
  | _ => i
  end.




Definition optimise_instruction (o:value -> value) (i:instr_id * instr) :=
  match i with
    (iid, ins) => (iid, instr_value_optimise ins o)
    end.

Definition optimise_code (o:value -> value) (b:code) : code := map (optimise_instruction o) b.


Print block.
Definition optimise_block (o:value -> value) (b:block) : block :=
  mk_block (blk_id b) (blk_phis b) (optimise_code o (b.(blk_code))) (blk_term b).






Definition optimise_list_block (o:block -> block) (b:list block) : list block :=
  map o b.

Print cfg.

Definition optimise_cfg (o:block -> block) (c:cfg) : cfg :=
  mkCFG (init c) (optimise_list_block o (blks c)) (glbl c).
Print definition.


Definition optimise_definition (o:block -> block) (c:definition cfg) :=
  mk_definition cfg (df_prototype c) (df_args c) (optimise_cfg o (df_instrs c)).

Print modul.

Definition optimise_list_definition (o:block -> block) (c: list (definition cfg)) :=
  map (optimise_definition o) c.

Print modul.

Definition optimise_modul (o:block -> block) (c: modul cfg) :=
  mk_modul cfg (m_name c) (m_target c) (m_datalayout c) (m_globals c) (m_declarations c) (optimise_list_definition o (m_definitions c)).


Definition correct_instr_value_optimise (o:value -> value) := forall e v, eval_op e None v = eval_op e None (o v).

(* m (optimise_modul o m)*)




(*first*) Definition startfunc o df_instrs bkid:= CFG.find_block (optimise_list_block o (blks df_instrs)) bkid.


Definition endfunc df_instrs bkid:=  CFG.find_block (blks df_instrs) bkid.

Definition targetfunc o df_instrs bkid :=
  match endfunc df_instrs bkid with
  | Some a => Some (optimise_block o a)
                             | None => None 
  end.




Lemma equiv_func : forall o df_instrs bk, CFG.find_block (optimise_list_block (optimise_block o) (blks df_instrs)) bk = targetfunc o df_instrs bk.
  Proof. Admitted.






Definition startfunc1 fnid A o := find_function (optimise_modul o A) fnid.

Definition endfunc1 fnid A := find_function A fnid.


Definition targetfunc1 fnid A o :=
  match endfunc1 fnid A with
  | Some a => Some (optimise_definition o a)
  | None => None
  end.


Lemma equiv_func1 : forall A o fnid, find_function (optimise_modul o A) fnid = targetfunc1 fnid A o.
Proof. Admitted.





Definition startfunc2 o a fnid :=  find_defn fnid (optimise_definition o a).

Print startfunc2.
Definition endfunc2 fnid a : option (definition cfg) :=  find_defn fnid a.

Definition targetfunc2 o a fnid :=
  match endfunc2 fnid a  with
  | None => None
  | Some a => Some (optimise_definition o a)
    end.



Lemma equiv_func2 : forall a o fnid,  find_defn fnid (optimise_definition o a) = targetfunc2 o a fnid.
Proof. Admitted.




Locate find_instr.




Definition startfunc3 (fnid:function_id) o m_definitions :=  find_map (find_defn fnid) (optimise_list_definition o m_definitions).
Print startfunc3.
Definition endfunc3 (fnid:function_id) (m_definitions: seq.seq (definition cfg)) := find_map (find_defn fnid) m_definitions.

Print endfunc3.


Lemma silly3 : forall fnid m_definitions o, startfunc3 fnid o m_definitions = endfunc3 fnid m_definitions.
Proof. Admitted.

Definition targetfunc3 o fnid m_definitions :=
  match endfunc3 fnid m_definitions with
  | Some t => Some (optimise_definition o t)
  | None => None
    end.

 Print targetfunc3.

 
Print startfunc3.
Print endfunc3.
Print targetfunc3.

Lemma equiv_func3 : forall (fnid:function_id) (m_definitions: seq.seq (definition cfg)) o,
  find_map (find_defn fnid) (optimise_list_definition o m_definitions) = targetfunc3 o fnid m_definitions   
   . Proof. Admitted.



Lemma equiv_func4 : forall o blk_code0 i i1, find_instr blk_code0 i i1 =  find_instr (optimise_code o blk_code0) i i1.
Proof. Admitted. 

Print find_function.

Print block.

Print find_block.


Definition one m1 m2 fnid cfg1 cfg2 := (find_function m1 fnid = Some cfg1 /\ find_function m2 fnid = Some cfg2).

Print find_block.
Print fetch.
Print CFG.find_block.


Print definition.
Print cfg.

Definition convert (c:definition cfg) : seq.seq block := blks (df_instrs c).

Definition two (cfg1 cfg2: definition cfg) (bkid:block_id) (b1 b2:block) := CFG.find_block (convert cfg1) bkid = Some b1 /\ CFG.find_block (convert cfg1) bkid = Some b2.

Print hdb.


Definition hdfstb b :=
match blk_code b with
| [] => None
| (h :: _)%SEQ => Some (fst h)
end.

Definition three (b1 b2:block) i1 i2 := hdfstb b1 = Some i1 /\ hdfstb b2 = Some i2.

Print three.


Definition compare_equiv m1  o:= forall
 (correct: correct_instr_value_optimise o) b1 s mem, compare_seq (exec_code1 m1 b1 (tauitem mem s)) (exec_code1 (optimise_modul (optimise_block o)  m1) (optimise_code o b1)  (tauitem mem s)).



Lemma testequiv : forall m1 o, compare_equiv m1 o.
Proof.

  intros. unfold compare_equiv. simpl in *. intros correct code.


  induction code.





  +intros. simpl in *. constructor. auto. constructor.




   +intros. simpl in *. assert (( CFG_step (snd a) m1 s) = (      CFG_step
        (snd (optimise_instruction o a))
        (optimise_modul
           (optimise_block o) m1) s)).









    unfold CFG_step.  destruct s.  destruct p. destruct p. simpl in *.
rewrite equiv_func1. unfold targetfunc1. unfold endfunc1.
    remember ( find_function m1 fn) as A. destruct A. destruct d. simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc. remember (CFG.find_block (blks df_instrs) bk) as B. destruct B. simpl in *. unfold block_to_cmd. unfold blk_term_id. simpl in *. destruct blk_term. simpl in *.  
    destruct (i == pt); simpl in *; eauto. rewrite <- equiv_func4. simpl in *. destruct b. simpl in *.
    destruct ( find_instr blk_code pt i). destruct p. destruct o0. destruct pt. destruct a. simpl in *.
    unfold instr_value_optimise. destruct i2. unfold correct_instr_value_optimise in correct. specialize (correct e op).
    rewrite correct. destruct (eval_op e None (o op)); simpl in *; eauto.
    destruct fn0. destruct i2. unfold find_function_entry. simpl in *.



    rewrite equiv_func1. unfold targetfunc1. unfold endfunc1. destruct (find_function m1 id0); simpl in *; eauto.

    destruct d. simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc. simpl in *.

    destruct ( CFG.find_block (blks df_instrs0) (init df_instrs0)); simpl in *; eauto.
    

    destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
    unfold optimise_block. simpl in *. unfold blk_entry_id. simpl in *. unfold optimise_code. simpl in *.


    unfold blk_term_id. simpl in *.  destruct b. simpl in *. induction blk_code0. simpl in *. auto. simpl in *.  destruct a. simpl in *. auto.
    simpl in *. auto. simpl in *. auto. simpl in *. destruct ptr. simpl in *.



    destruct ( eval_op e (Some t1) v); simpl in *; eauto.
    auto. auto. auto. auto. auto. auto. auto. simpl in *. destruct a. simpl in *. destruct i2. simpl in *. auto. destruct fn0. destruct i2; simpl in *; eauto.
    unfold find_function_entry. simpl in *.

    rewrite equiv_func1. unfold targetfunc1. unfold endfunc1.


    destruct ( find_function m1 id); simpl in *; eauto.


    destruct d.
    simpl in *. rewrite equiv_func. unfold targetfunc. unfold endfunc. simpl in *.


    destruct ( CFG.find_block (blks df_instrs0) (init df_instrs0)); simpl in *; eauto.
    destruct t0; simpl in *; eauto.
    destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl in *; eauto.
    unfold optimise_block. simpl in *. unfold blk_entry_id. simpl in *. unfold blk_term_id.
    simpl in *. unfold optimise_code. unfold optimise_instruction. simpl in *. destruct b.
    simpl in *. induction blk_code0. simpl in *. auto. simpl in *. destruct a. simpl in *. auto.

    simpl in *. auto. simpl in *. auto. simpl in *; eauto. simpl in *; auto. simpl in *; auto.
    simpl in *; eauto. simpl in *; eauto. simpl in *; eauto. simpl in *; eauto. simpl in *; eauto.
    simpl in *. auto. simpl in *. auto. simpl in *. auto. rewrite <- H. simpl in *.
    destruct a. simpl in *. destruct ( CFG_step i0 m1 s); simpl in *; eauto.
    constructor. auto. apply IHcode. constructor. auto. apply IHcode. destruct m. simpl in *. constructor. auto. destruct code. simpl in *. constructor. auto. constructor. simpl in *.
    constructor. auto. constructor. constructor. auto. destruct code. simpl in *. constructor. auto. constructor. simpl in *. constructor. auto. constructor. destruct e; simpl in *; eauto.
    constructor. auto. apply IHcode. constructor. auto. apply IHcode. constructor. auto. apply IHcode. constructor. auto. constructor. Qed.


Print convert.


Definition testfunc (m:mcfg) (o:mcfg -> mcfg) :=
  (forall fnid, (find_function m fnid = None /\ find_function (o m) fnid = None) \/ (forall cfg1 cfg2, find_function m fnid = Some cfg1 /\ find_function (o m) fnid = Some cfg2 /\
                                                                                   ((forall bkid b1 b2, CFG.find_block (convert cfg1) bkid = Some b1 /\ CFG.find_block (convert cfg2) bkid = Some b2 )))) .

