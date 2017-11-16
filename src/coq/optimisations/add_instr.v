
Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import ZArith.Int.
Require Import Vellvm.CFG.
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.optimisations.transform.

Print instr_id.
Print raw_id.


(*Instr_id is of type raw_id*)

(*raw_id is an inductive object with three cases:
  -Name: used for string identifiers
  -Anon: used for anonymous identifiers
  -Raw: used for code generation


get_max function calculates the 
*)


Fixpoint get_maximum (n:int) (c:code) :=
match c with
  | nil => n (*No more items*)
  | (IId (Raw iid),_)::tl =>if (Z.leb iid n) then get_maximum n tl else get_maximum iid tl (*When the item on the list is a raw iid*)
  | hd::tl => get_maximum n tl (*When the item on the list is not a raw id*)
end.


(*Fetches the last generated instruction and adds 1 to it*)
Definition get_first_unused (c:code) := IId (Raw (Z.add (get_maximum Z0 c) 1)).

(*Useless instruction*)
Definition no_instr : instr := INSTR_Op (SV (VALUE_Null)).

(*Useless iid*)
Definition useless_instr (c:code) : list (instr_id * instr) := cons (get_first_unused c, no_instr) nil.

(*optimise *)
Definition optimise (c:code) := c ++ useless_instr c.


Definition prog_optimise (p:modul CFG.cfg) := def_cfg_opt optimise p.