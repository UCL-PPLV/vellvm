Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG.
Import ListNotations.
Require Import Vellvm.Memory.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.Classes.
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.optimisations.vellvm_tactics.


Require Import compcert.lib.Integers.
Open Scope Z_scope.
Open Scope string_scope.


(* Set up for i1, i32, and i64 *) 
Module Int64 := Integers.Int64.
Module Int32 := Integers.Int.
Module Int1 := Ollvm_ast.Int1.

Definition int1 := Int1.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.
Locate ET.
Print Expr.





Print eval_iop_integer_h.


Print ident.
Print eval_i1_op.

Print VALUE_Integer. Print OP_IBinop.
Definition convert_ibinop_i1 (i1 i2:Ollvm_ast.int) (op:ibinop) := avalue (eval_i1_op op (Int1.repr i1) (Int1.repr i2)).
Definition convert_ibinop_i32 (i1 i2:Ollvm_ast.int) (op:ibinop) := avalue (eval_i32_op op (Int32.repr i1) (Int32.repr i2)).
Definition convert_ibinop_i64 (i1 i2:Ollvm_ast.int) (op:ibinop) := avalue (eval_i64_op op (Int64.repr i1) (Int64.repr i2)).
Print Expr.

Definition convert_icmp_i1 (i1 i2:Ollvm_ast.int) (op:icmp) := avalue (eval_i1_icmp  op (Int1.repr i1) (Int1.repr i2)).
Definition convert_icmp_i32 (i1 i2:Ollvm_ast.int) (op:icmp) := avalue (eval_i32_icmp  op (Int32.repr i1) (Int32.repr i2)).
Definition convert_icmp_i64 (i1 i2:Ollvm_ast.int) (op:icmp) := avalue (eval_i64_icmp  op (Int64.repr i1) (Int64.repr i2)).
Print typ. Print VALUE_Float.


Definition eval_aenv_expr (e:aenv) (o:Expr value)  :=
 match o with
              | VALUE_Ident _ => vtop
              | VALUE_Integer i =>  ( (avalue (DV (VALUE_Integer i))))
              | VALUE_Float i => ( (avalue (DV (VALUE_Float i))))
              | VALUE_Bool i =>  ( (avalue (DV (VALUE_Bool i))))
              | VALUE_Null => ( (avalue (DV (VALUE_Null))))
              | VALUE_Zero_initializer => ((avalue (DV (VALUE_Zero_initializer))))
              | VALUE_Cstring a =>  ((avalue (DV (VALUE_Cstring a))))
              | VALUE_None => ((avalue (DV (VALUE_None))))
              | VALUE_Undef => ((avalue (DV (VALUE_Undef))))




              | OP_IBinop iop (TYPE_I 1) (SV(VALUE_Integer i1))  (SV(VALUE_Integer i2)) => ((convert_ibinop_i1 i1 i2 iop))
              | OP_IBinop iop (TYPE_I 32) (SV(VALUE_Integer i1))  (SV(VALUE_Integer i2)) => ((convert_ibinop_i32 i1 i2 iop))
              | OP_IBinop iop (TYPE_I 64) (SV(VALUE_Integer i1))  (SV(VALUE_Integer i2)) => ((convert_ibinop_i64 i1 i2 iop))




              | OP_ICmp iop (TYPE_I 1) (SV(VALUE_Integer i1))  (SV(VALUE_Integer i2)) => ((convert_icmp_i1 i1 i2 iop))
              | OP_ICmp iop (TYPE_I 32) (SV(VALUE_Integer i1))  (SV(VALUE_Integer i2)) => ((convert_icmp_i32 i1 i2 iop))
              | OP_ICmp iop (TYPE_I 64) (SV(VALUE_Integer i1))  (SV(VALUE_Integer i2)) => ((convert_icmp_i64 i1 i2 iop))                                       
              | _ =>  vtop
              
  end.

  



Lemma correct_static_eval : forall e ae e0 v0,
 eval_expr eval_op e None e0 = inr v0 ->      
 vmatch (avalue v0) (eval_aenv_expr ae e0).
Proof. intros.
       destruct e0; simpl in *; eauto; try constructor; inversion H; eauto; try destruct t; simpl in *; try constructor; destruct sz; try constructor; try destruct p; try destruct p; try destruct p; try destruct p; try destruct p; try destruct p; try destruct p; try constructor; try destruct v1; try destruct e0; try destruct v0; try destruct v2; try destruct e1; try constructor; simpl in *; try destruct e0; try inversion H; eauto; try constructor; eauto.
Qed.


Hint Resolve correct_static_eval.


