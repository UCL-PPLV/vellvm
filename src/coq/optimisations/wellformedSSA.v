Require Import Vellvm.Ollvm_ast Vellvm.CFG.
Require Import Vellvm.optimisations.EqNat.


Set Implicit Arguments.
Set Contextual Implicit.



From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Print block.
Print code.

(*
Well-formed block
1. All instr_id in code (seq (instr_id * instr)) + blk_term should be unique
*)



Definition unique_instr_id (s:seq (instr_id * instr)) (b:(instr_id * terminator)) := uniq ((map fst s) ++ [::fst b]).


Inductive well_form_block (b:block) :=
 | wfb : unique_instr_id b.(blk_code) b.(blk_term) = true -> well_form_block b
.


(*A program is wellformed if all blocks within are well formed*)
Print pc.
Print find_function.

(* A program is well formed, if given its mcfg and a pc:
  -(function_find): There is always a function associated with its function_id
  -(block_find): There is always a block associated with its block_id
  -(some_block_to_cmd): There is always a command associated with its instruction_id
  -(block_wf): If each block is wellformed
*)


Inductive well_formed_program (m:mcfg) (p:pc):=
  | well_formed : forall i iid b bid cfg ins
(block_wf: well_form_block b)
(some_block_to_cmd: block_to_cmd b iid = Some ins)
(block_find: find_block (blks (df_instrs cfg)) bid = Some b)
(function_find: find_function m i = Some cfg), 
p = mk_pc i bid iid ->
well_formed_program m p.












(*********Essential: Dominator analysis*********)




(*
Basic definitions:
Given a graph G with entry E.

A block L is reachable if there is a path from the entry pf G to L.
A block L1 dominates L2, if for every path p from e to L2, L1 is a member of P.
A block L1 strictly dominates L2, if path P from e to L2, L1 != L2 /\ L2 is a member of P.
*)


(*
Basic lemmas:
Lemma 1: If L1 strictly dominates L2, then L1 dominates L2
Lemma 2: If L1 dominates L2 and L2 dominates L3, L1 dominates L3
Lemma 3: If L1 strictly dominates L2 and L2 strictly dominates L3, L1 strictly dominates L3
Lemma 4: Strict dominance is acyclic
Lemma 5: If L3 is reachable,L1 != L2, L1 strictly dominates L3, either L1 strictly dominates L2 OR L2 strictly dominates L1
*)






(*********Well-formed SSA Programs**********)




(*Well-scoped instructions*)
(*Every variable is only declared once*)
(*All uses of a variable must be dominated by their definition*)
(*The use of a variable at point p is well-scoped if it its definition strictly dominates its use*)




(*Well-formed phi nodes*)
(*
Consider [ %x = phi [lbl1:v1, ...,lbln:vn] ].
This is well formed when every predecessor block with terminator program point p' 
has a label associated with value v.  Moreover, if v uses an id then the definition of the uid strictly dominates p'.
*)



(*
Well Formed CFG:
  -It has an start pt
  -If all program points map to an instruction are well scopped 
  -All phi nodes are well formed
*)





(*Well Formed CFGs*)
(*A function is in valid SSA form if its CFG is well formed*)





(*Well formed programs*)
(*A Program is in valid SSA form if all of its functions are in valid SSA*)


(**********Lemmas deriving from SSA definitions*********)



  (*  wf_cfg g -> pt_exists g p1 -> edge_pt g p1 p2 -> pt_exists g p2.*)

(**********Useful lemmas for SSA optimisations*********)




(*Definition of a Dominator Tree*)
(*Lemma dom_tree_exists: Given a well-formed SSA program there exists a dominator tree*)






(*EQUATIONAL LEMMA*)

(*
Because every assignment creates a new value name it cannot kill (i.e. invalidate)
expressions previously computed from other values. In particular, if two expressions
are textually the same, they are sure to evaluate the same result.
*)





