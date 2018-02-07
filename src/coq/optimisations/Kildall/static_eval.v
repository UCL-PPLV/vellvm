Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG.
Import ListNotations.
Require Import Vellvm.Memory.
Require Import Vellvm.optimisations.Kildall.valuedomain.
Require Import Vellvm.Classes.
Require Import Vellvm.Ollvm_ast.

Print dvalue. Print value. Print eval_expr.  Print ET. Locate ET.
Print eval_expr.

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

  








(*


Definition get_value (o:Ollvm_ast.value) (e:aenv) (top:option typ) :=
  match o with
  | SV (VALUE_Integer x) =>
    match top with
    | None =>  mret (DV (VALUE_Integer x))
    | Some (TYPE_I bits) => coerce_integer_to_int bits x
    | _ => failwith "bad type for constant int"
    end
  | SV (VALUE_Float x)   => mret (DV (VALUE_Float x))
  | SV (VALUE_Bool b)    => mret (DV (VALUE_Bool b)) 
  | SV (VALUE_Null)      => mret (DV (VALUE_Null))
  | SV (VALUE_Zero_initializer) => mret (DV (VALUE_Zero_initializer))
  | SV (VALUE_Cstring s) => mret (DV (VALUE_Cstring s))
  | SV (VALUE_None)      => mret (DV (VALUE_None))
  | SV (VALUE_Undef)     => mret (DV (VALUE_Undef))
  | _ => failwith "wrong val"
  end.
Print eval_conv.
Definition eval_aenv_expr (e:aenv) (top:option typ) (o:Expr value) : err ET.value :=
  match o with
  | VALUE_Integer x =>    match top with
                          | None =>  mret (DV (VALUE_Integer x))
                          | Some (TYPE_I bits) => coerce_integer_to_int bits x
                          | _ => failwith "bad type for constant int"
    end

  | VALUE_Float x   => mret (DV (VALUE_Float x))
  | VALUE_Bool b    => mret (DV (VALUE_Bool b)) 
  | VALUE_Null      => mret (DV (VALUE_Null))
  | VALUE_Zero_initializer => mret (DV (VALUE_Zero_initializer))
  | VALUE_Cstring s => mret (DV (VALUE_Cstring s))
  | VALUE_None      => mret (DV (VALUE_None))
  | VALUE_Undef     => mret (DV (VALUE_Undef))
  | OP_IBinop iop t op1 op2 =>
    'v1 <- get_value op1 e (Some t);
    'v2 <- get_value op2 e (Some t);
    (eval_iop t iop) v1 v2

  | OP_ICmp cmp t op1 op2 => 
    'v1 <- get_value op1 e (Some t);
    'v2 <- get_value op2 e (Some t);
    (eval_icmp t cmp) v1 v2

  | OP_FBinop fop fm t op1 op2 =>
    'v1 <- get_value op1 e (Some t);
    'v2 <- get_value op2 e (Some t);
    (eval_fop t fop) v1 v2

  | OP_FCmp fcmp t op1 op2 => 
    'v1 <- get_value op1 e (Some t);
    'v2 <- get_value op2 e (Some t);
    (eval_fcmp fcmp) v1 v2
  | OP_Conversion conv t1 op t2 =>
        'v <- get_value op e (Some t1);
    (eval_conv conv) t1 v t2

  | _ => failwith "badtype"
                  
  end
    
 .



Arguments eval_aenv_expr  _ _ _ : simpl nomatch.

Definition aeval_op (e:aenv)  (o:Ollvm_ast.value) : err ET.value :=
  match o with
  | SV o' => eval_aenv_expr e None o'
  end.
Arguments aeval_op _ _ : simpl nomatch.







Print ematch.


Ltac break_inner_match' t :=
  match t with
  (* | context[find_function_entry _ _] => unfold find_function_entry in *; break_inner_match' t*)
   | context[match ?X with _ => _ end] => break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

Ltac break_inner_match_goal :=
  match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

Ltac break_goal := unfold find_function_entry in *; break_inner_match_goal; simpl in *; eauto.
  

Ltac try_resolve := try (repeat break_goal); try constructor.

Lemma ematch_update : forall id a e res,  ematch e a -> AE.get id a = avalue res -> lookup_env e id = Some res.
Proof. unfold ematch in *. intros. specialize (H id). inversion H; subst. rewrite H0 in H3. inversion H3. unfold lookup_env_aenv in *; simpl in *. destruct (lookup_env e id) eqn:?. rewrite <- H2 in H0. rewrite H0 in H1. inversion H1. eauto. inversion H1. Qed.





Lemma test1 : forall e a t v1 iop v2 res, ematch e a ->  match get_value v1 a (Some t) with
       | inl x => inl x
       | inr a0 =>
           match get_value v2 a (Some t) with
           | inl x => inl x
           | inr a => eval_iop t iop a0 a
           end
       end = inr res -> 
         match eval_op e (Some t) v1 with
  | inl x => inl x
  | inr a0 =>
      match eval_op e (Some t) v2 with
      | inl x => inl x
      | inr a1 => eval_iop t iop a0 a1
      end
  end =
  match get_value v1 a (Some t) with
  | inl x => inl x
  | inr a0 =>
      match get_value v2 a (Some t) with
      | inl x => inl x
      | inr a1 => eval_iop t iop a0 a1
      end
  end.
Proof. intros. rewrite H0. unfold get_value in *; simpl in *. destruct v1; try destruct e0; simpl in *; unfold eval_expr; try inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); eauto; try destruct v2; simpl in *; unfold eval_expr; simpl in *; try destruct e0; simpl in *; try inversion H0; eauto. Qed.
Hint Resolve test1.



Lemma test2 : forall e a v1 v2 t cmp res, ematch e a ->
       match get_value v1 a (Some t) with
       | inl x => inl x
       | inr a0 =>
           match get_value v2 a (Some t) with
           | inl x => inl x
           | inr a => eval_icmp t cmp a0 a
           end
       end = inr res ->  match eval_op e (Some t) v1 with
  | inl x => inl x
  | inr a0 =>
      match eval_op e (Some t) v2 with
      | inl x => inl x
      | inr a1 => eval_icmp t cmp a0 a1
      end
  end =
  match get_value v1 a (Some t) with
  | inl x => inl x
  | inr a0 =>
      match get_value v2 a (Some t) with
      | inl x => inl x
      | inr a1 => eval_icmp t cmp a0 a1
      end
  end.
Proof. intros.  unfold get_value in *. destruct v1; simpl in *; try destruct e0; simpl in *; try inversion H0. destruct t; simpl in *; try destruct ( coerce_integer_to_int sz x); eauto; try destruct v2; try destruct e0; simpl in *; try inversion H0; try destruct (coerce_integer_to_int sz x0); simpl in *; eauto; try destruct d; simpl in *. try destruct v2; try destruct t; try destruct e0; simpl in *; try inversion H0; try destruct (coerce_integer_to_int sz x); simpl in *; inversion H0; try destruct d; try destruct e0; simpl in *; eauto.
       destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; simpl in *; eauto.
       destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; simpl in *; eauto.
       destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; simpl in *; eauto.
       destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; simpl in *; eauto.
       destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; simpl in *; eauto.
       destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; simpl in *; eauto.
Qed.       
       


       
Hint Resolve test2.
       


Lemma test3: forall e a v1 v2 t fop res,  ematch e a ->
  match get_value v1 a (Some t) with
       | inl x => inl x
       | inr a0 =>
           match get_value v2 a (Some t) with
           | inl x => inl x
           | inr a => eval_fop t fop a0 a
           end
       end = inr res ->
  match eval_op e (Some t) v1 with
  | inl x => inl x
  | inr a0 =>
      match eval_op e (Some t) v2 with
      | inl x => inl x
      | inr a1 => eval_fop t fop a0 a1
      end
  end =
  match get_value v1 a (Some t) with
  | inl x => inl x
  | inr a0 =>
      match get_value v2 a (Some t) with
      | inl x => inl x
      | inr a1 => eval_fop t fop a0 a1
      end
  end.
Proof. intros. rewrite H0. unfold get_value in *. simpl in *. destruct v1; try destruct e0; simpl in *; try inversion H0.
       destruct t; try destruct (coerce_integer_to_int sz x); try inversion H0; try destruct v2; try destruct e0; simpl in *; inversion H0;try destruct ( coerce_integer_to_int sz x0); simpl in *; try inversion H0. destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.

 destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.
 destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.
 destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.
 destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.
 destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.
 destruct v2; try destruct e0; simpl in *; inversion H0; try destruct t; try destruct ( coerce_integer_to_int sz x); inversion H0.
Qed.



Hint Resolve test3.



Lemma test4 : forall e a v1 v2 t cmp res, ematch e a ->
       match get_value v1 a (Some t) with
       | inl x => inl x
       | inr a0 =>
           match get_value v2 a (Some t) with
           | inl x => inl x
           | inr a => eval_fcmp cmp a0 a
           end
       end = inr res ->
  match eval_op e (Some t) v1 with
  | inl x => inl x
  | inr a0 =>
      match eval_op e (Some t) v2 with
      | inl x => inl x
      | inr a1 => eval_fcmp cmp a0 a1
      end
  end =
  match get_value v1 a (Some t) with
  | inl x => inl x
  | inr a0 =>
      match get_value v2 a (Some t) with
      | inl x => inl x
      | inr a1 => eval_fcmp cmp a0 a1
      end
  end.
Proof. intros. rewrite H0. destruct v1, v2; simpl in *. unfold eval_expr; destruct e0, e1; simpl in *; eauto; inversion H0; destruct t; try destruct e0; try destruct (coerce_integer_to_int sz x); inversion H0.
Qed. Hint Resolve test4.

Lemma test5 : forall e a t_to t_from v res conv, ematch e a ->  match get_value v a (Some t_from) with
       | inl x => inl x
       | inr a => eval_conv conv t_from a t_to
       end = inr res ->  match eval_op e (Some t_from) v with
  | inl x => inl x
  | inr a0 => eval_conv conv t_from a0 t_to
  end =
  match get_value v a (Some t_from) with
  | inl x => inl x
  | inr a0 => eval_conv conv t_from a0 t_to
  end.

Proof. intros. rewrite H0. unfold get_value in *; simpl in *. destruct v; try destruct e0; simpl in *; inversion H0; try destruct t_from; unfold eval_expr; simpl in *; eauto. Qed.
Hint Resolve test5.


Lemma test : forall a e o res, ematch e a -> aeval_op a  o = inr res -> eval_op e None o = inr res.
Proof. intros. induction o. simpl in *. unfold eval_expr. unfold eval_aenv_expr in *. induction e0; simpl in *; eauto; inversion H0; try destruct id; simpl in *; eauto; try destruct (AE.get id a) eqn:?; inversion H0; subst; try eapply ematch_update in Heqt; eauto; try rewrite Heqt; eauto.
Qed.*)