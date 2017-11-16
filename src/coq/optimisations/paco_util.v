Require Import paco.
Require Import Vellvm.Effects.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.Ollvm_ast.


Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.


    Module ET : Vellvm.Effects.EffT
        with Definition addr := A.addr
        with Definition typ := Ollvm_ast.typ
        with Definition value := dvalue.

      Definition addr := A.addr.
      Definition typ := Ollvm_ast.typ.
      Definition value := dvalue.
      Definition inj_addr := DVALUE_Addr.
      Definition no_value := DV (VALUE_None).
    End ET.    
  Module E := Vellvm.Effects.Effects(ET).
  Export E.






