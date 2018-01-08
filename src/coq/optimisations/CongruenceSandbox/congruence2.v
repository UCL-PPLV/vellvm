Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.
(*


Print mcfg.


Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.



Print cfg.
Print block.

(*If all the functions are equal, then the execution is the same*)


Print find_function.

Definition function_equal :=
forall m1 m2 fid, find_function m1 fid = find_function m2 fid.



Definition jump_equal_trace_equiv := forall m1 m2 fn bk br2 e s, jump m1 fn bk br2 e s = jump m2 fn bk br2 e s.



Print fetch.



Print find_block.
Print block.

Definition get_block (fid:function_id) (bid:block_id) (m:mcfg) : option block :=
match find_function m fid with
  | None => None
  | Some fn => find_block (blks (df_instrs fn)) bid
end.


(*With the same fid, bid, m1 and m2 yield some result.
The result, block_id are the same.
block_phis are the same
the stepD of the head of both are the same
the tl of the code is the same
the blk_term is also the same*)
Print block.





Definition block_same_phis (b1 b2:block) :=
if (decide (b1.(blk_phis) = b2.(blk_phis))) then true else false.


Definition block_same_id (b1 b2:block) :=
if (decide (b1.(blk_id) = b2.(blk_id))) then true else false.



Definition block_same_term (b1 b2: block) :=
if (decide (b1.(blk_term) = b2.(blk_term))) then true else false.

Print code.




Definition tl (c:code) :=
match c with
  | [::] => [::]
  | _ :: t => t
end.




Definition block_same_tl_code (b1 b2: block) := if decide (tl (b1.(blk_code)) = tl (b2.(blk_code))) then true else false.


Print block.

Print find_block_entry.
Print block_entry.

Print find_block_entry.
Print block_entry.
Print find_function.


(*Either the first instruction of a block is the first of the list, if the list is empty then the terminator*)
Definition hdb (b:block) :=
match b.(blk_code) with
  | [::] => None
  | h :: _ => Some h
end.

Print sem.
Print exec_code.
Definition hd_block_equal m1 m2 fnid bkid b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => forall mem e s, exec_code m1 mem b1.(blk_code) (tauitem (mk_pc fnid bkid h1, e, s)) = exec_code m2 mem b2.(blk_code) (tauitem (mk_pc fnid bkid h2, e, s))
  | _, _ => False
end.
Print hdb.

Definition hd_fst_block_equal b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => h1 = h2
  | _, _ => False
end.




Definition tl_block_equal b1 b2 :=
tl (b1.(blk_code)) = tl (b2.(blk_code)).
Print fst.
Print hd.

Definition list_equal (b:block) :=
match hdb b with
  | None => [::]
  | Some h => (h :: tl b.(blk_code))
end.


Definition head (b:block) :=
match b.(blk_code) with
  | [::] => [::]
  | h :: t => [::h]
end.
Print find_function.
Print definition.
Print cfg.

(*(if (decide (fn1.(df_prototype) = fn2.(df_prototype))) then True else False) /\*)


Definition fulldefinition (m1 m2: mcfg) :=
forall fnid fn1 fn2, 
(*Fetching a function_id (fnid) always returns some result*)
(find_function m1 fnid = Some fn1) /\ (find_function m2 fnid = Some fn2) /\

(*These bits of definition are all equal*)

(*ADD DF_PROTOTYPE*)
(if (decide (fn1.(df_args) = fn2.(df_args))) then True else False) /\


(*Convert definition to CFG*)
forall cfg cfg1, (df_instrs fn1) = cfg /\ (df_instrs fn2) = cfg1 /\
(if (decide ((init cfg) = (init cfg1))) then True else False) /\
(*These bits of the CFG are all equal*)

forall bkid bk1 bk2,
(*Fetching a block_id (bkid) always returns some result*)
(find_block (blks (df_instrs fn1)) bkid = Some bk1) /\ (find_block (blks (df_instrs fn2)) bkid = Some bk2) /\


(*The blk_id, blk_phis and the blk_term are all equal*)
(if (decide (bk1.(blk_id) = bk2.(blk_id))) then True else False) /\
(if (decide (bk1.(blk_phis) = bk2.(blk_phis))) then True else False) /\
(if (decide (bk1.(blk_term) = bk2.(blk_term))) then True else False) /\
hd_fst_block_equal bk1 bk2 /\


(*The execution of the head of both blocks are equal*)
hd_block_equal m1 m2 fnid bkid bk1 bk2 /\


(*The body of both blocks are equal *)
tl_block_equal bk1 bk2 /\

bk1.(blk_code) = head bk1 ++ tl bk1.(blk_code) /\
bk2.(blk_code) = head bk2 ++ tl bk2.(blk_code)

.

Lemma test123 : forall prog prog1, fulldefinition prog prog1 -> forall st mem, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog1 st)).
Proof. 
intros prog prog1 H. pcofix CIH.
intros. pfold.

(*
assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))).
destruct (memD mem (sem prog st)); eauto. rewrite H0. clear H0.

assert ((memD mem (sem prog1 st)) = unroll (memD mem (sem prog1 st))).
destruct (memD mem (sem prog1 st)); eauto. rewrite H0. clear H0.


destruct st. destruct p. destruct p.
generalize H. intros. unfold fulldefinition in H0.
specialize (H0 fn). simpl.

remember (find_function prog fn) as find_func_fn.
remember (find_function prog1 fn) as find_func_fn1.


destruct find_func_fn, find_func_fn1.
  +specialize (H0 d d0). destruct H0. clear H0. destruct H1. clear H0.
destruct H1. destruct d, d0. specialize (H1 df_instrs df_instrs0).
simpl in *. destruct H1. clear H1. destruct H2. clear H1.
destruct H2. unfold is_left in *. destruct (decide (df_args = df_args0)). clear H0.
destruct (decide (init df_instrs = init df_instrs0)). clear H1. subst.



remember (find_block (blks df_instrs) bk) as find_block_fn.
remember (find_block (blks df_instrs0) bk) as find_block_fn1.
destruct find_block_fn, find_block_fn1.


 specialize (H2 bk b b0). 
destruct H2. destruct H1.
destruct H2. destruct H3. destruct H4. destruct H5. destruct H6.
destruct H7. destruct H8.
unfold block_to_cmd. unfold blk_term_id in *.

destruct (decide (blk_id b = blk_id b0)), (decide (blk_phis b = blk_phis b0)), (decide (blk_term b = blk_term b0)).
subst. unfold tl_block_equal in H7. destruct b, b0. simpl in *.
subst. destruct blk_term0. unfold hd_fst_block_equal in H5. unfold hdb in H5.
destruct blk_code, blk_code0. simpl in *. inversion H5. unfold hd_block_equal in H6.
 unfold hdb in H6. simpl in H6. inversion H6.
unfold hd_block_equal in H6. destruct p. simpl in H6. inversion H6.
simpl in H7. subst. unfold head in *. simpl in *.
unfold hd_block_equal in H6. unfold hdb in H6. destruct p, p0. subst.
simpl in H6. rewrite <- Heqfind_func_fn in H6; rewrite <- Heqfind_func_fn1 in H6.
destruct df_instrs. simpl in *. destruct df_instrs0; simpl in *.
rewrite H0 in H6. rewrite H1 in H6. unfold block_to_cmd in H6. unfold blk_term_id in H6.
simpl in H6. destruct ( decide (i = i2)), (decide (i2 = i2)), (decide (i = pt)), (decide (pt = i2)); subst; simpl in *.



admit. admit. admit. admit. admit. admit. admit. admit. admit. admit. *) Admitted.

*)














