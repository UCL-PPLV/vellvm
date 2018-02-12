(*
Require Import Vellvm.Ollvm_ast Vellvm.CFG.
Require Import Vellvm.optimisations.EqNat.
Require Import Vellvm.optimisations.dom.

Require Import Vellvm.Classes.
Require Import Vellvm.Util.


Set Implicit Arguments.
Set Contextual Implicit.



From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
Print block.
Print code.





(*A program consists of several functions. Each function has its own CFG*)




Print cfg.


Print find_block.

Print pc.



Record local_pc : Set := mk_local_pc { bk : block_id;  pt : instr_id }.

(*retrieve cfg from function*)
Definition get_cfg (d:definition cfg) : cfg := df_instrs d.

(*retrieve cfg entry from cfg*)
Definition get_cfg_entry (c:cfg) := find_block (blks c) (init c).
Print get_cfg_entry.
Print incr_pc.
Print find_function.

Inductive valid_cfg : mcfg -> cfg -> Prop :=
| test : forall m c d, (exists fn, find_function m fn = Some d -> get_cfg d = c) -> valid_cfg m c.


Print cmd.
Print cfg.
Print find_block.

Definition fetch_local (c:cfg) (p:local_pc) : option cmd :=
  let 'mk_local_pc bid iid := p in 
  'blk <- find_block (blks c) bid;
  '(c, _) <- block_to_cmd blk iid;
  mret c.
Print block_to_cmd.

Definition incr_pc_local (c:cfg) (p:local_pc) : option local_pc :=
  let 'mk_local_pc bid iid := p in 
  'blk <- find_block (blks c) bid;
  '(c, n) <- block_to_cmd blk iid;
  'iid_next <- n;
  mret (mk_local_pc bid iid_next).

Print find_block_entry.
Print block_entry.

Print blk_entry_id.

Definition get_block_entry_pc (c:cfg) (bid:block_id) : option local_pc :=
  match find_block (blks c) bid with
  | None => None
  | Some block => Some (mk_local_pc bid (blk_entry_id block))
  end.




Inductive incr_pc_rel : cfg -> local_pc -> local_pc -> Prop :=
  | incr_pc_intro : forall c p p1, incr_pc_local c p = Some p1 -> incr_pc_rel c p p1.


Definition lbls (t:terminator) : seq block_id :=
  match t with
  | TERM_Ret _        
  | TERM_Ret_void   => []
  | TERM_Br _ l1 l2 => [l1; l2] 
  | TERM_Br_1 l => [l] 
  | TERM_Switch _ l brs => l::(List.map (fun x => snd x) brs)
  | TERM_IndirectBr _ brs => brs
  | TERM_Resume _    => []
  | TERM_Invoke  _ _ l1 l2 => [l1; l2] 
  end.


Inductive succ_pc : cfg -> local_pc -> local_pc -> Prop :=
| succ_pc_s : forall c p p1, incr_pc_rel c p p1 -> succ_pc c p p1
(*1. Current instruction at p is a terminator
  2. There exists a block_id which is used by the terminator
  3. There exists a block b with the id block_id
  4. The initial pc of block b is equal to p1*)
| succ_pc_j : forall c p p1 t1 blk_id, fetch_local c p = Some (Term t1) ->
                                  blk_id \in lbls t1 -> get_block_entry_pc c blk_id = Some p1 -> succ_pc c p p1.

Print cfg.

Definition get_entry (c:cfg)  :=
  match get_cfg_entry c with
  | None => None
  | Some a =>  Some (mk_local_pc (init c) (blk_entry_id a))
  end
.

Module PtGraph <: GRAPH.
  Definition t := cfg.
  Definition V := local_pc.
  Definition entry g := get_entry g.
  Definition edge := succ_pc.
End PtGraph.


















(*
Well-formed block
1. All instr_id in code (seq (instr_id * instr)) + blk_term should be unique
*)




Print definition.
(*A program is wellformed if all blocks within are well formed*)
Print pc.
Print find_function.

(* A program is well formed, if given its mcfg and a pc:
  -(function_find): There is always a function associated with its function_id
  -(block_find): There is always a block associated with its block_id
  -(some_block_to_cmd): There is always a command associated with its instruction_id
  -(block_wf): If each block is wellformed
*)










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


*)

