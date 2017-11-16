(*
   - the initial pt denotes a command  
   - fallthrough closure: each fallthrough pt maps to a command 
   - jump closure: each label used in a terminator leads to a
     block within the same function body.
   - every use of an identifier is dominated by the id's definition
   - no identifier is defined multiple times
*)


Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util.

Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.



(*

(*Fetches an instruction given a MCFG + PC*)
Print fetch.

(*An instruction exists in a CFG at p*)
Definition pt_exists (CFG : mcfg) (p:pc) : Prop :=
  exists cmd, fetch CFG p = Some cmd.


Print cmd.
Print incr_pc.
Print cmd.


Inductive edge_pt (g:mcfg) : pc -> pc -> Prop :=
(*There exists a step instruction at point p, incrementing p generates another q implies there exists an edge relation between p and q.*)
| edge_pt_S : forall p q i,
    fetch g p = Some (Step i) -> incr_pc g p = Some q -> edge_pt g p q
| edge_pt_J : forall p q i,
    fetch g p = Some (Term i) -> incr_pc g p = Some q -> edge_pt g p q.
Print incr_pc.

Print phi.
 





(*Well-formed code*)
*)
(*
Well-formed block
  -No identifier is defined multiple times
  -Every use of an identifier is dominated by the id's definition
  -Every use of fallthrough maps a command
*)


(*Well-formed CFG*)




(*Well-formed MCFG*)




(*Given a PC that doesn't point to a terminator, the next instruction is always within the same *)