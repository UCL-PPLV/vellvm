From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.



Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Effects.




Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  


Module SS := StepSemantics.StepSemantics(A).
Export SS.


Print value.


Definition nat := int.
Print ibinop.




Record block : Set :=
  mk_block
    {
      blk_id    : block_id;
      blk_phis  : list (local_id * phi);
      blk_code  : code;
      blk_term  : instr_id * terminator;
    }.


Record block1 : Set :=
  mk_block1
    {
      blk_id1    : block_id;
      blk_phis1  : list (local_id * phi);
      blk_code1  : code;
      blk_term1  : instr_id * terminator;
    }.





Definition comparestr (s1 s2: string) := if string_dec s1 s2 then true else false.

Definition compare_blockID (a b: block_id) :=
match a, b with
  | Name c, Name d => comparestr c d
  | Anon c, Anon d => c == d
  | Raw c, Raw d => c == d
  | _, _ => false
end.



Definition loopfind (b:block) :=
let cd := b.(blk_id) in
match b.(blk_term) with
  | (_,c) => match c with
            | TERM_Br _ a d => (compare_blockID a cd) || (compare_blockID cd d)
            | _ => false
            end
end.



Record exm : Set :=
  mk_ex
    {
      exnat    : Datatypes.nat;
    
    }.


Definition testBlock := mk_ex 1%nat.


Print testBlock.







