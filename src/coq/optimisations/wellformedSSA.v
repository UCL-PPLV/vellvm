Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.

Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.



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





