Require Import Vellvm.CFG.
Require Import Vellvm.Ollvm_ast.
Require Import Equalities.
Require Import List.


Record local_pc : Set := mk_localpc { lbk : block_id;  lpt : instr_id }.

Definition cfg_to_cmd (c:cfg) (p:local_pc) : option (cmd * option instr_id) :=
  match find_block (blks c) (lbk p) with
  | Some b => block_to_cmd b (lpt p) 
  | None => None
  end.


Definition incr_local_pc (c:cfg) (p:local_pc) :=
  match cfg_to_cmd c p with
  | Some (_, Some i) => Some (mk_localpc (lbk p) i)
  | _ => None
  end.


Definition fetch (c:cfg) (p:local_pc) : option cmd :=
  match cfg_to_cmd c p with
  | Some (instr, _) => Some instr
  | _ => None
  end.



Definition find_block_entry (c:cfg) (b:block_id) :=
  match find_block (blks c) b with
  | Some block => cons (mk_localpc b (blk_entry_id block)) nil
  | None => nil
  end.

Definition term_successor (c:cfg) (t:terminator) : list local_pc :=
  match t with
  | TERM_Br_1 br => find_block_entry c br
  | TERM_Br _ br1 br2 => find_block_entry c br1 ++ find_block_entry c br2
                                  
| _ => nil
end.


Definition successor_local_pc (c:cfg) (p:local_pc) :=
  match cfg_to_cmd c p with
  | Some (CFG.Step ins, Some i) => cons (mk_localpc (lbk p) i) nil
  | Some (Term t, _ ) => term_successor c t
  | _ => nil
  end.



Definition predecessor_local_pc (c:cfg) (p:local_pc) : list local_pc := nil.



Lemma make_predecessors_correct_2:
  forall n code instr s,
  fetch code n = Some instr -> In s (successor_local_pc code n) ->
  exists l, predecessor_local_pc code s = l /\ In n l.
Proof. Admitted.

Module local_pcDec <: MiniDecidableType.
  Definition t := local_pc.
  Lemma eq_dec : forall (x y : local_pc), {x = y} + {x <> y}.
  Proof.
    decide equality. SearchAbout instr_id.
    - eapply AstLib.InstrID.eq_dec.
    -eapply AstLib.RawID.eq_dec.
  Qed.
  
End  local_pcDec.



Definition pc_to_local_pc (p:pc) : local_pc := mk_localpc (bk p) (pt p).
Definition local_pc_to_pc (fn:function_id) (p:local_pc) := mk_pc fn (lbk p) (lpt p).