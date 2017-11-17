
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


get_max function calculates the first unused UIS
*)


Fixpoint get_maximum (n:int) (c:code) :=
match c with
  | nil => n (*No more items*)
  | (IId (Raw iid),_)::tl =>if (Z.leb iid n) then get_maximum n tl else get_maximum iid tl (*When the item on the list is a raw iid*)
  | hd::tl => get_maximum n tl (*When the item on the list is not a raw id*)
end.


(*So that an instruction with a unique UID can be added, we need to find to find an unused value*)
Print block.
Print instr_id.
Definition get_terminator_iid (b:block) : Z :=
match b.(blk_term) with
  | (IId (Raw n), _) => n
  | (_, _) => Z0
end.

(*Find the largest instruction (which is either the terminator ID or an instruction from within the code) and adds 1 to it*)
Definition get_first_unused (b:block) : instr_id := IId (Raw (Z.add (get_maximum (get_terminator_iid b) (b.(blk_code))) 1)).

(*Useless instruction*)
Definition no_instr : instr := INSTR_Op (SV (VALUE_Null)).



(*The code in a block gets executed sequentially.
This optimisation adds an instruction to the end of that code therefore the impact this might have is on the block terminator instruction.
There are currently 4 implemented terminator instructions:
  | TERM_Ret :  tvalue -> terminator
  | TERM_Ret_void : terminator
  | TERM_Br :  tvalue -> block_id -> block_id ->  terminator
  | TERM_Br_1 : block_id ->  terminator


Explanation:
TERM_Ret - return a typed value
TERM_Ret_void - return void
TERM_Br - branch to either block id depending on the evaluation of a typed value
TERM_Br_1 - branch directly to block_id



Let's add an instruction to a block if and only if its terminating instruction is TERM_Ret.
*)



(*Simple function that returns true if the terminating instruction is a return void*)
Definition terminator_check (b:block) : bool :=
match b.(blk_term) with
  | (_, TERM_Ret_void) => true
  | _ => false
end.

Print block.
Print block.
Print fetch.


Definition add_instr_block (b:block) (i:(instr_id * instr)) (b1:(instr_id * terminator)%type) := 
mk_block b.(blk_id) b.(blk_phis) (b.(blk_code) ++ (cons i nil)) b1.
Print blk_term.

Definition get_blk_id (b:block) : instr_id :=
let term := b.(blk_term) in
match term with 
  | (term_id, term_instr) => term_id
end.

Definition get_blk_term (b:block)  :=
let term := b.(blk_term) in
match term with 
  | (term_id, term_instr) => term_instr
end.



(*
The added instruction has the instruction id of the terminator instruction
Definition optimise (b:block) := if terminator_check b then (add_instr_block b (get_blk_id b, no_instr) (get_first_unused b,get_blk_term b)) else b.


Definition prog_optimise (p:modul CFG.cfg) := def_cfg_opt optimise p.