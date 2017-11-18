
Require Import ZArith.
Require Import List.

Require Import Bool.
Require Import ZArith.Int.
Require Import Vellvm.CFG.
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.optimisations.transform.
Require Import ZArith List String Omega.
Require Import Vellvm.AstLib Vellvm.Ollvm_ast.

Import ListNotations.
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
Locate fetch.
Print block_to_cmd.
Print block.


Definition fetch_two_block (b1: block) (c:code) (i:instr_id) : option (cmd * option instr_id) :=
match block_to_cmd b1 i with
  | None => match block_to_cmd (mk_block b1.(blk_id) b1.(blk_phis) c b1.(blk_term)) i with
            | None => None
            | Some t => Some t
            end
(*If terminator => test*)
(*If new => test*)
  | Some a => Some a
end.




(*
Definition fetch (CFG : mcfg) (p:pc) : option cmd :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- block_to_cmd blk iid;
  mret c.*)


(*

We want something like
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- dual_block_to_cmd blk i;
  mret c.*)

Print block.
Print blk_code.

Definition add_instr_block (b:block) (i:(instr_id * instr)) (b1:(instr_id * terminator)%type) := 
mk_block b.(blk_id) b.(blk_phis) (blk_code b ++ (cons i nil)) b1.
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

(*V1*)
Print block_to_cmd.
(*The added instruction has the instruction id of the terminator instruction*)
Definition optimisev1 (b:block) := if terminator_check b then (add_instr_block b (get_blk_id b, no_instr) (b.(blk_term))) else b.

Definition prog_optimisev1 (p:modul CFG.cfg) := def_cfg_opt optimisev1 p.


(*In the proof, there will always be the case:
  fetch prog pc = ...
  fetch (optimise prog) pc = ...

As seen in the pacoproof.v, it is useful to write (fetch (optimise prog) pc) as a new function of fetch prog pc.
This allows us to 
*)
(*V2*)



(**************************************************************************)
Definition dual_block_to_cmd (b:block) (i:instr_id) := if terminator_check b then fetch_two_block b (cons (get_blk_id b, no_instr) nil) i else block_to_cmd b i .


Require Import Vellvm.Classes.
Definition dual_fetch (CFG: mcfg) (p:pc) :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- dual_block_to_cmd blk iid;
  mret c.



Lemma test1 : forall b i, dual_block_to_cmd b i = block_to_cmd (optimisev1 b) i.
Proof. intros. unfold dual_block_to_cmd. unfold optimisev1.
unfold terminator_check. destruct b. simpl in *. destruct blk_term.
destruct t; auto. 
  +unfold fetch_two_block. simpl in *.
unfold add_instr_block. simpl in *.
remember ([(get_blk_id
                        {|
                        blk_id := blk_id;
                        blk_phis := blk_phis;
                        blk_code := blk_code;
                        blk_term := (i0, TERM_Ret_void) |}, no_instr)]) as A.


unfold block_to_cmd. simpl. unfold blk_term_id. simpl.
simpl.
induction (i0 == i). auto. subst. simpl. unfold get_blk_id. simpl.
induction blk_code. simpl. unfold not in b. simpl in *.
destruct (i == i0). symmetry in e. apply b in e. inversion e. auto.
simpl. destruct a.
destruct (i == i1). simpl.
-unfold fallthrough. simpl. destruct blk_code. simpl. auto. simpl. auto.
-auto.
Qed.



Print fetch.


Definition fetch1 (CFG : mcfg) (p:pc) : option cmd :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- dual_block_to_cmd blk iid;
  mret c.





Lemma equal_fetch : forall m p, fetch (prog_optimisev1 m) p = fetch1 m p.
Proof. intros.
destruct m. simpl.
induction m_definitions.
  +unfold prog_optimisev1 in *. unfold optimisev1. simpl. unfold def_cfg_opt. simpl. unfold fetch, fetch1. simpl. auto.
  +simpl in *. unfold fetch, fetch1 in *. simpl. destruct p. simpl in *. destruct a. simpl in *.
unfold find_function in *. simpl in *. unfold find_defn in *. simpl in *.
unfold cfg_opt in *. simpl in *. auto. unfold ident_of in *. simpl in *. 
unfold ident_of_definition in *. unfold ident_of in *. simpl in *.

destruct (ident_of_declaration df_prototype == ID_Global fn).
    *simpl in *. destruct df_instrs. simpl in *. induction blks; simpl in *; auto.
      -destruct a. simpl. unfold optimisev1. simpl. unfold terminator_check. simpl.
{destruct blk_term. simpl. destruct t; simpl; destruct (blk_id == bk); try (rewrite test1; unfold optimisev1; simpl; auto);
try (induction blks; simpl; auto).
}
    *auto.
Qed.



Print find_block.

(******************SECOND*************************)



Definition incr_pc1 (CFG : mcfg) (p:pc) : option pc :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, n) <- dual_block_to_cmd blk iid;
  'iid_next <- n;
  mret (mk_pc fid bid iid_next).

Lemma equal_incr_pc : forall m p, incr_pc (prog_optimisev1 m) p = incr_pc1 m p.
Proof. intros. destruct m. simpl.
destruct m_definitions; simpl in *.
  +unfold prog_optimisev1 in *. unfold optimisev1. simpl. unfold def_cfg_opt. simpl. unfold incr_pc, incr_pc1. simpl. auto.
  +simpl in *. unfold incr_pc, incr_pc1 in *. simpl. destruct p. simpl in *. destruct d. simpl in *.
unfold find_function in *. simpl in *. unfold find_defn in *. simpl in *.
unfold cfg_opt in *. simpl in *. auto. unfold ident_of in *. simpl in *. 
unfold ident_of_definition in *. unfold ident_of in *. simpl in *.

destruct (ident_of_declaration df_prototype == ID_Global fn).
    *simpl in *. destruct df_instrs. simpl in *. induction blks.
      -simpl in *. auto.
      -destruct a. simpl. unfold optimisev1. simpl. unfold terminator_check. simpl.
{destruct blk_term. simpl. destruct t; simpl; destruct (blk_id ==bk); try (rewrite test1; unfold optimisev1; simpl; eauto); try (induction blks; simpl; eauto).
}
    *induction m_definitions.
      -simpl. auto.
      -simpl.
{destruct (ident_of_declaration (Ollvm_ast.df_prototype a) == ID_Global fn).
        +simpl. destruct a. simpl in *. induction df_instrs0. 
          -simpl in *. induction blks.
            *simpl. auto.
            *simpl. unfold optimisev1. unfold terminator_check. simpl. destruct a. simpl in *. destruct blk_term. clear IHm_definitions. simpl in *.
{destruct t; simpl; destruct (blk_id == bk);
try (simpl; unfold dual_block_to_cmd, block_to_cmd, blk_term_id; simpl; auto);
try (induction blks; simpl; auto; auto).
unfold fetch_two_block. simpl.
unfold block_to_cmd; simpl in *.
unfold blk_term_id; simpl in *.
  *destruct (i == pt); auto. induction blk_code.
    -simpl. unfold get_blk_id. simpl. induction (pt == i); auto.
    -simpl. destruct a. destruct (pt == i0). simpl.
unfold get_blk_id; simpl in *.
unfold fallthrough. simpl. induction blk_code. simpl.
auto.
auto.
auto.
  *clear IHblks. clear IHblks0. 
unfold fetch_two_block. simpl. unfold block_to_cmd. simpl.
unfold get_blk_id. simpl. unfold blk_term_id. simpl.
subst.
destruct (i == pt); auto.
induction blk_code; auto.
  +simpl. destruct (pt == i); auto.
  +simpl. destruct a0. destruct (pt == i0); auto. unfold fallthrough. 
simpl. destruct blk_code; simpl; auto.
}
  +auto.
}
Qed.



(**************************************************************************)