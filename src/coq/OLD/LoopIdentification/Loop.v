Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.

From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.
Require Export Permutation.
Require Import Vellvm.Effects.

Print modul.

Print CFG.



Module A : Vellvm.StepSemantics.ADDR with Definition addr := nat.
  Definition addr := nat.
End A.  


Module SS := StepSemantics.StepSemantics(A).
Export SS.


(* Beq*) 



Module NoLoop.

Inductive Leaf :=
  | MyLeaf (b:block).

Inductive LoopTree :=
  | MyNode (leafs:list Leaf)
.


Definition LeafToSingleBlock (l:Leaf) :=
match l with
  | MyLeaf b => b
end.

Definition SingleBlockToLeaf (b:block) : Leaf := MyLeaf b.


Theorem LeafConversion : forall b, LeafToSingleBlock(SingleBlockToLeaf(b)) = b.
Proof.
intros. auto. Qed.



Definition BlockToListOfLeaves (b:list block) := MyNode (map SingleBlockToLeaf b).


Definition ListOfLeavesToBlock (l:LoopTree) : list block :=
match l with
  | MyNode a => map LeafToSingleBlock a
end.


Theorem BlockConversion : forall l, ListOfLeavesToBlock(BlockToListOfLeaves(l)) = l.
Proof. unfold ListOfLeavesToBlock, BlockToListOfLeaves. induction l.
  -simpl. auto.
  -simpl. rewrite IHl. auto. Qed.


Record LoopTreeBlock : Set := mkLTB
  { inits : block_id;  blkss : LoopTree;  glbls : list ident }.


Definition convertCFGtoLoopTreeBlock (c:cfg) := mkLTB c.(init) (BlockToListOfLeaves c.(blks)) c.(glbl).

Definition convertLoopTreeBlocktoCFG (c:LoopTreeBlock) := mkCFG c.(inits) (ListOfLeavesToBlock c.(blkss)) c.(glbls).

Theorem CFGConversion :
  forall c, convertLoopTreeBlocktoCFG(convertCFGtoLoopTreeBlock(c)) = c.
Proof.
intros. unfold convertCFGtoLoopTreeBlock, convertLoopTreeBlocktoCFG.
induction c.
simpl.
induction blks; simpl; eauto.
induction a.
simpl. symmetry.
inversion IHblks.
rewrite H0 H0.
auto.
Qed.


Definition DefLTBtoDefCFG (t:definition LoopTreeBlock) :=
  (mk_definition cfg t.(df_prototype) t.(df_args) (convertLoopTreeBlocktoCFG t.(df_instrs))).

Definition DefCFGtoDefLTB (t:definition cfg) :=
  (mk_definition LoopTreeBlock t.(df_prototype) t.(df_args) (convertCFGtoLoopTreeBlock t.(df_instrs))).


Theorem DefCFGConversion : forall c, DefLTBtoDefCFG(DefCFGtoDefLTB(c)) = c.
Proof.
intros.
unfold DefLTBtoDefCFG, DefCFGtoDefLTB.
induction c; simpl.
induction df_instrs; simpl; eauto.
rewrite CFGConversion; eauto; simpl.
Qed.



Definition ListDefLTBtoListDefCFG (t:list (definition LoopTreeBlock)) := map DefLTBtoDefCFG t.
Definition ListDefCFGtoListDefLTB (t:list (definition cfg)) := map DefCFGtoDefLTB t.


Theorem ListDefConversion : forall c, ListDefLTBtoListDefCFG(ListDefCFGtoListDefLTB(c)) = c.
Proof.
intros.
unfold ListDefLTBtoListDefCFG, ListDefCFGtoListDefLTB.
simpl; induction c; simpl; eauto.
rewrite DefCFGConversion; simpl; eauto.
rewrite IHc; eauto.
Qed.


Definition MLTBtoMCFG (t:modul LoopTreeBlock) : mcfg :=
  mk_modul cfg t.(m_name)
           t.(m_target) t.(m_datalayout)
           t.(m_globals)
           t.(m_declarations) (ListDefLTBtoListDefCFG t.(m_definitions)).

Definition MCFGtoMLTB (t:modul cfg) :=
  mk_modul LoopTreeBlock t.(m_name) t.(m_target)
           t.(m_datalayout) t.(m_globals) t.(m_declarations)
           (ListDefCFGtoListDefLTB t.(m_definitions)).

(*
Theorem MCFGConversion : forall c, MLTBtoMCFG(MCFGtoMLTB(c)) = c.
Proof. intros. unfold MLTBtoMCFG, MCFGtoMLTB; simpl; eauto. rewrite ListDefConversion. simpl. induction c; simpl; eauto; simpl. Qed.
*)

Definition parse_unparse (t: modul cfg) : modul cfg := MLTBtoMCFG (MCFGtoMLTB t).
(* Print stepD. *)

Theorem parse_unparse_eq c : parse_unparse c = c.
Proof.
Admitted.



Theorem parse_unparse_correct : forall c s, stepD (parse_unparse c) s = stepD c s.
Proof.
move=>c[[p e]]s.
by rewrite parse_unparse_eq.
Qed.

case: c; intros.
rewrite /parse_unparse/MLTBtoMCFG/MCFGtoMLTB. 
rewrite ![Ollvm_ast.m_name _]/= ![Ollvm_ast.m_definitions _]/=
        ![Ollvm_ast.m_declarations _]/= ![Ollvm_ast.m_target _]/=
        ![Ollvm_ast.m_datalayout _]/= ![Ollvm_ast.m_globals _]/=.
elim: m_definitions p e s=>//[cfg rest Hi]p0 e0 s0.
rewrite [ListDefLTBtoListDefCFG _] /=.
case: p0=>fn0 bk0 pt0.
rewrite /stepD.
rewrite /trywith/fetch.


set F := (find_function _ fn0).



case (find_function _ fn0)/ last first.
- rewrite [do _ <- _ ; _]/=.

(* unfold MLTBtoMCFG, MCFGtoMLTB. *)
(* simpl. *)
(* unfold ListDefLTBtoListDefCFG, ListDefCFGtoListDefLTB. *)
(* simpl.  *)
(* unfold DefLTBtoDefCFG, DefCFGtoDefLTB. simpl. *)
(* unfold convertLoopTreeBlocktoCFG, convertCFGtoLoopTreeBlock. *)
(* unfold ListOfLeavesToBlock, BlockToListOfLeaves. *)
(* simpl. eauto. *)
(* induction blks. simpl. *)
(* eauto. *)

Admitted.

End NoLoop.





Section MiniLoop.

Inductive Leaf :=
  | MyLeaf (b:block).

Inductive LoopTree :=
  | MyNode (leafs:list Leaf) (loops: list Leaf)
.

(* SingleLeaf to Block *)

Definition LeafToBlock (b:Leaf) := match b with MyLeaf b => b end.

(* MultipleLeaves to Block *)

Definition ListLeafToBlock (b: list Leaf) := map LeafToBlock b.

Definition BlockToLeaf (b:block) := MyLeaf b.

Print  block.

(* LoopTest *)

Definition comparestr (s1 s2: string) := if string_dec s1 s2 then true else false.

Definition compare_blockID (a b: block_id) :=
match a, b with
  | Name c, Name d => comparestr c d
  | _, _ => false
end.


Definition LoopTesting (b:block) := 
match (snd b.(blk_term)) with
  | TERM_Ret _ => false
  | TERM_Ret_void => false
  | TERM_Br _ d e => compare_blockID d b.(blk_id) || compare_blockID e b.(blk_id)
  | TERM_Br_1 _ => false
  | TERM_Switch _ _ _ => false
  | TERM_IndirectBr _ _ => false
  | TERM_Resume _ => false 
  | TERM_Invoke _ _ _ _ => false
end.

Theorem SingleBlockConversion : forall c, BlockToLeaf (LeafToBlock c) = c.
Proof. intros. unfold BlockToLeaf, LeafToBlock. auto. induction c. auto. Qed.


Fixpoint ListOfBlocksToLoopHelper (b:list block) (l:list Leaf) (loops: list Leaf) :=
match b with
  | nil => MyNode l loops
  | head::tail => if LoopTesting head
                  then ListOfBlocksToLoopHelper tail ([BlockToLeaf head] ++ l) loops
                  else ListOfBlocksToLoopHelper tail l ([BlockToLeaf head] ++ loops)
end.




Definition ListOfBlocksToLoop (b:list block) : LoopTree := ListOfBlocksToLoopHelper b nil nil.


Definition LoopToListOfBlocks (l:LoopTree) : list block := match l with MyNode a b => (ListLeafToBlock a) ++ (ListLeafToBlock b) end.


Theorem SingleListConversion : forall c, LoopToListOfBlocks(ListOfBlocksToLoop [::c] ) = [::c].
Proof. intros. induction c. unfold LoopToListOfBlocks, ListOfBlocksToLoop, ListOfBlocksToLoopHelper. simpl.
unfold LoopTesting. destruct blk_term. induction t; simpl; eauto. Qed.

Theorem DoubleListConversion : forall c d, Permutation (LoopToListOfBlocks(ListOfBlocksToLoop ([c] ++ [d]))) ([c]++[d]).
Proof. intros. induction c, d. induction blk_term, blk_term0. Admitted.






Record LoopTreeBlock : Set := mkLTB
  { inits : block_id;  blkss : LoopTree;  glbls : list ident }.


Definition convertCFGtoLoopTreeBlock (c:cfg) := mkLTB c.(init) (ListOfBlocksToLoop c.(blks)) c.(glbl).

Definition convertLoopTreeBlocktoCFG (c:LoopTreeBlock) := mkCFG c.(inits) (LoopToListOfBlocks c.(blkss)) c.(glbls).



Definition DefLTBtoDefCFG (t:definition LoopTreeBlock) := (mk_definition cfg t.(df_prototype) t.(df_args) (convertLoopTreeBlocktoCFG t.(df_instrs))).

Definition DefCFGtoDefLTB (t:definition cfg) := (mk_definition LoopTreeBlock t.(df_prototype) t.(df_args) (convertCFGtoLoopTreeBlock t.(df_instrs))).


Definition ListDefLTBtoListDefCFG (t:list (definition LoopTreeBlock)) := map DefLTBtoDefCFG t.
Definition ListDefCFGtoListDefLTB (t:list (definition cfg)) := map DefCFGtoDefLTB t.


Definition MLTBtoMCFG (t:modul LoopTreeBlock) : mcfg := mk_modul cfg t.(m_name) t.(m_target) t.(m_datalayout) t.(m_globals) t.(m_declarations) (ListDefLTBtoListDefCFG t.(m_definitions)).
Definition MCFGtoMLTB (t:modul cfg) := mk_modul LoopTreeBlock t.(m_name) t.(m_target) t.(m_datalayout) t.(m_globals) t.(m_declarations) (ListDefCFGtoListDefLTB t.(m_definitions)).

Print mcfg. Print modul. Print definition. Print cfg.

Definition parse x := MLTBtoMCFG (MCFGtoMLTB x).



Theorem MCFGJump : forall CFG state, stepD (parse CFG) state = stepD (CFG) state.
Proof. intros. destruct state0. destruct p. destruct CFG. simpl.
unfold parse. unfold MLTBtoMCFG. simpl. 

Admitted.





(*

Theorem MCFGJump : forall CFG fid bid_src bid_tgt env stack, jump CFG fid bid_src bid_tgt env stack = jump CFG fid bid_src bid_tgt env stack.
Proof. intros. reflexivity. Qed.


Theorem MCFGJump1 : forall CFG fid bid_src bid_tgt env stack, jump (MLTBtoMCFG(MCFGtoMLTB CFG)) fid bid_src bid_tgt env stack = jump CFG fid bid_src bid_tgt env stack.
Proof. intros. generalize dependent env0. induction CFG.

unfold MLTBtoMCFG, MCFGtoMLTB. simpl. unfold ListDefLTBtoListDefCFG, ListDefCFGtoListDefLTB. simpl. unfold  DefLTBtoDefCFG. unfold convertLoopTreeBlocktoCFG, convertCFGtoLoopTreeBlock. unfold LoopToListOfBlocks, DefCFGtoDefLTB. unfold convertCFGtoLoopTreeBlock. simpl. eauto.

induction m_definitions. simpl. auto.

destruct m_definitions. simpl. eauto.
unfold jump.
*)

Print block.



Print Trace.

(* List Block to LoopTree *)


End MiniLoop.

