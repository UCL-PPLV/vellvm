Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFG Vellvm.StepSemantics.
Import ListNotations.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Effects.



(*
Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  


Module SS := StepSemantics.StepSemantics(A).
Export SS.


Print value.


Definition nat := int.
Print ibinop.*)
(*
Fixpoint fold_value (d : Ollvm_ast.value) : Ollvm_ast.value :=
  match d with
      | SV s =>
      match s with
        | VALUE_Ident a => SV (VALUE_Ident a)
        | VALUE_Integer a => SV (VALUE_Integer a)
        | VALUE_Float a => SV (VALUE_Float a)
        | VALUE_Bool a => SV (VALUE_Bool a)
        | VALUE_Null => SV (VALUE_Null)
        | VALUE_Zero_initializer => SV (VALUE_Zero_initializer)
        | VALUE_Cstring a => SV (VALUE_Cstring a)
        | VALUE_None => SV (VALUE_None)
        | VALUE_Undef => SV (VALUE_Undef)
        | VALUE_Struct a => SV (VALUE_Struct a)
        | VALUE_Packed_struct a => SV (VALUE_Packed_struct a)
        | VALUE_Array a => SV (VALUE_Array a)
        | VALUE_Vector a => SV (VALUE_Vector a)
        | OP_IBinop iop b v1 v2 => let cv1 := fold_value v1 in
                                 let cv2 := fold_value v2 in
                                 match cv1, cv2 with
                                   | SV (Ollvm_ast.VALUE_Integer x), SV (Ollvm_ast.VALUE_Integer y) =>
                                      match iop with
                                        | Ollvm_ast.Add _ _ =>  SV (Ollvm_ast.VALUE_Integer (x+y)%Z)
                                        | Ollvm_ast.Sub _ _ =>  SV (Ollvm_ast.VALUE_Integer (x-y)%Z)
                                        | Ollvm_ast.Mul _ _ =>  SV (Ollvm_ast.VALUE_Integer (x*y)%Z)
                                        | _ =>  SV (OP_IBinop iop b cv1 cv2)
                                      end
                                    | _ , _ => SV (OP_IBinop iop b cv1 cv2)
                                end
        | OP_ICmp a b v1 v2 =>  let cv1 := fold_value v1 in
                                let cv2 := fold_value v2 in
                              SV (OP_ICmp a b cv1 cv2)
        | OP_FCmp a b v1 v2  =>  let cv1 := fold_value v1 in
                                let cv2 := fold_value v2 in
                              SV (OP_FCmp a b cv1 cv2)
        | OP_FBinop a b c v1 v2 => let cv1 := fold_value v1 in
                                let cv2 := fold_value v2 in
                              SV (OP_FBinop a b c cv1 cv2)
        | OP_Conversion a b v1 d => let cv1 := fold_value v1 in
                                 SV (OP_Conversion a b v1 d)
        | OP_GetElementPtr a b c  => SV (OP_GetElementPtr a b c)
        | OP_ExtractElement a b  => SV (OP_ExtractElement a b)
        | OP_InsertElement a b c  => SV (OP_InsertElement a b c)
        | OP_ShuffleVector a b c  => SV (OP_ShuffleVector a b c)
        | OP_ExtractValue a b  => SV (OP_ExtractValue a b)
        | OP_InsertValue a b c => SV (OP_InsertValue a b c)
        | OP_Select a b c => SV (OP_Select a b c)
      end
  end.


*)
(*
Definition eval_expr {A:Set} (f:env -> option typ -> A -> err value) (e:env) (top:option typ) (o:Expr A) : err value :=
  match o with
    | VALUE_Ident id => 
    'i <- local_id_of_ident id;
      match lookup_env e i with
      | None => failwith ("lookup_env: id = " ++ (string_of i) ++ " NOT IN env = " ++ (string_of e))
      | Some v => mret v
      end
    | VALUE_Integer x => mret (DV (VALUE_Integer x))
    | VALUE_Float x   => mret (DV (VALUE_Float x))
    | VALUE_Bool b    => mret (DV (VALUE_Bool b)) 
    | VALUE_Null      => mret (DV (VALUE_Null))
    | VALUE_Zero_initializer => mret (DV (VALUE_Zero_initializer))
    | VALUE_Cstring s => mret (DV (VALUE_Cstring s))
    | VALUE_None      => mret (DV (VALUE_None))
    | VALUE_Undef     => mret (DV (VALUE_Undef))


    | VALUE_Struct es =>
    'vs <- map_monad (monad_app_snd (f e top)) es;
     mret (DV (VALUE_Struct vs))
    | VALUE_Packed_struct es =>
    'vs <- map_monad (monad_app_snd (f e top)) es;
     mret (DV (VALUE_Packed_struct vs))

    | VALUE_Array es =>
    'vs <- map_monad (monad_app_snd (f e top)) es;
     mret (DV (VALUE_Array vs))

    | VALUE_Vector es =>
    'vs <- map_monad (monad_app_snd (f e top)) es;
     mret (DV (VALUE_Vector vs))
    | OP_IBinop iop t op1 op2 =>
    'v1 <- f e (Some t) op1;
    'v2 <- f e (Some t) op2;
    (eval_iop t iop) v1 v2

    | OP_ICmp cmp t op1 op2 => 
    'v1 <- f e (Some t) op1;                   
    'v2 <- f e (Some t) op2;
    (eval_icmp t cmp) v1 v2

    | OP_FBinop fop fm t op1 op2 =>
    'v1 <- f e (Some t) op1;
    'v2 <- f e (Some t) op2;
    (eval_fop t fop) v1 v2

    | OP_FCmp fcmp t op1 op2 => 
    'v1 <- f e (Some t) op1;
    'v2 <- f e (Some t) op2;
    (eval_fcmp fcmp) v1 v2
              
    | OP_Conversion conv t1 op t2 =>
    'v <- f e (Some t1) op;
    (eval_conv conv) t1 v t2
                       
    | OP_GetElementPtr t ptrval idxs =>
    'vptr <- monad_app_snd (f e (Some t) ) ptrval;
    'vs <- map_monad (monad_app_snd (f e (Some (TYPE_I 32)))) idxs;
    failwith "getelementptr not implemented"  (* TODO: Getelementptr *)  
    
    | OP_ExtractElement vecop idx =>
(*    'vec <- monad_app_snd (f e) vecop;
    'vidx <- monad_app_snd (f e) idx;  *)
    failwith "extractelement not implemented" (* TODO: Extract Element *) 
      
    | OP_InsertElement vecop eltop idx =>
(*    'vec <- monad_app_snd (f e) vecop;
    'v <- monad_app_snd (f e) eltop;
    'vidx <- monad_app_snd (f e) idx; *)
    failwith "insertelement not implemented" (* TODO *)
    
    | OP_ShuffleVector vecop1 vecop2 idxmask =>
(*    'vec1 <- monad_app_snd (f e) vecop1;
    'vec2 <- monad_app_snd (f e) vecop2;      
    'vidx <- monad_app_snd (f e) idxmask; *)
    failwith "shufflevector not implemented" (* TODO *)

    | OP_ExtractValue strop idxs =>
    let '(t, str) := strop in
    'str <- f e (Some t) str;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => mret str
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          loop v tl
        end in
    loop str idxs
        
    | OP_InsertValue strop eltop idxs =>
    (*
    '(t1, str) <- monad_app_snd (f e) strop;
    '(t2, v) <- monad_app_snd (f e) eltop;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => failwith "invalid indices"
        | [i] =>
          insert_into_str str v i
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          'v <- loop v tl;
          insert_into_str str v i
        end in
    loop str idxs*)
    failwith "TODO"

    | OP_Select cndop op1 op2 => (* Do this *)
    (*
    '(t, cnd) <- monad_app_snd (f e) cndop;
    '(t1, v1) <- monad_app_snd (f e) op1;
    '(t2, v2) <- monad_app_snd (f e) op2;
    eval_select t cnd t1 v1 v2
     *)
    failwith "TODO"
end.
*)