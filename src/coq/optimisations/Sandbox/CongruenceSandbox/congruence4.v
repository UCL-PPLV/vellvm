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

Print code.


(*

Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.



Print cfg.
Print block.

(*If all the functions are equal, then the execution is the same*)


Print find_function.


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

(*Fixpoint exec_code (m:mcfg) (mem:memory) (c:code) (f:finish_item ( state)) :=*)
Definition hd_block_equal m1 m2 fnid bkid b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => False
  | Some (h1, t1), Some (h2, t2) => forall mem e s, true_test (exec_code1 m1 b1.(blk_code) (tauitem mem (mk_pc fnid bkid h1, e, s))) (exec_code1 m2 b2.(blk_code)
                                                                                                                              (tauitem mem (mk_pc fnid bkid h2, e, s)))
  | _, _ => False
end.
Print hdb.

Definition hd_fst_block_equal b1 b2 := 
match hdb b1, hdb b2 with
  | None, None => True
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
(((find_function m1 fnid = Some fn1) /\ (find_function m2 fnid = Some fn2)) 
\/((find_function m1 fnid = None) /\ (find_function m2 fnid = None)))
/\

(*These bits of definition are all equal*)

(*ADD DF_PROTOTYPE*)
(if (decide (fn1.(df_args) = fn2.(df_args))) then True else False) /\


(*Convert definition to CFG*)
forall cfg cfg1, (df_instrs fn1) = cfg /\ (df_instrs fn2) = cfg1 /\
(if (decide ((init cfg) = (init cfg1))) then True else False) /\
(*These bits of the CFG are all equal*)

forall bkid bk1 bk2,
(*Fetching a block_id (bkid) always returns some result*)
(((find_block (blks (df_instrs fn1)) bkid = Some bk1) /\ (find_block (blks (df_instrs fn2)) bkid = Some bk2))
\/

((find_block (blks (df_instrs fn1)) bkid = None) /\ (find_block (blks (df_instrs fn2)) bkid = None))



) /\


(*The blk_id, blk_phis and the blk_term are all equal*)
(if (decide (bk1.(blk_id) = bk2.(blk_id))) then True else False) /\
(if (decide (bk1.(blk_phis) = bk2.(blk_phis))) then True else False) /\
(if (decide (bk1.(blk_term) = bk2.(blk_term))) then True else False) /\
hd_fst_block_equal bk1 bk2 /\


(*The execution of the head of both blocks are equal*)
hd_block_equal m1 m2 fnid bkid bk1 bk2 


(*bk1.(blk_code) = (*hd + tl*)
  bk2.(blk_code) = (*hd + tl*)
*)
.




Lemma Test123 : forall prog prog1, fulldefinition prog prog1 -> forall st mem, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog1 st)).
 intros p p1 fulldef. pcofix CIH. intros. pfold.
  
assert ((memD mem (sem p st)) = unroll (memD mem (sem p st))).
destruct (memD mem (sem p st)); eauto. rewrite H. clear H.

assert ((memD mem (sem p1 st)) = unroll (memD mem (sem p1 st))).
destruct (memD mem (sem p1 st)); eauto. rewrite H. clear H.


destruct st. destruct p0. destruct p0.
generalize fulldef. intros fulldef1. unfold fulldefinition in fulldef1.
specialize (fulldef1 fn). simpl.

remember (find_function p fn) as find_func_fn.
remember (find_function p1 fn) as find_func_fn1.


destruct find_func_fn, find_func_fn1.
  +specialize (fulldef1 d d0). destruct fulldef1. 
destruct H0. specialize (H1 (df_instrs d) (df_instrs d0)). destruct H1.
destruct H2. destruct H3. destruct d, d0; simpl in *. destruct df_instrs, df_instrs0.
simpl in *.


remember (find_block blks bk ) as findblock.
remember (find_block blks0 bk) as findblock1.

destruct findblock, findblock1.


specialize (H4 bk b b0).
destruct H4.
destruct H5.
destruct H6.
destruct H7.
destruct H8.

unfold block_to_cmd.
unfold blk_term_id in *.

unfold is_left in *. simpl in *.

unfold hd_block_equal in H9.
destruct b, b0.
unfold hdb in H9.
simpl in *.

unfold hd_fst_block_equal in *. unfold hdb in H8.
destruct (decide (df_args = df_args0)), (decide (blk_id = blk_id0)),
(decide (blk_phis = blk_phis0)), (decide (blk_term = blk_term0)); subst; simpl in *.




destruct blk_term0. simpl in *. induction blk_code, blk_code0; simpl in *; eauto.
inversion H9. inversion H9. destruct a; inversion H9.
destruct a, p0.



rewrite <- Heqfind_func_fn in H9; rewrite <- Heqfind_func_fn1 in H9. 
simpl in *.
rewrite <- Heqfindblock in H9; rewrite <- Heqfindblock1 in H9.
simpl in *. unfold block_to_cmd in H9. subst. unfold blk_term_id in H9. simpl in *.

destruct (decide (i = i2)); subst. simpl in *.
(*23*)


destruct (decide (i2 = pt)), (decide (pt = i2)); subst; simpl in *; eauto.


destruct t; simpl in *; eauto.
destruct v; simpl in *; eauto.
destruct ( eval_op e (Some t) v); simpl in *; eauto.
destruct s; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct s; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct v; simpl in *; eauto.
destruct ( eval_op e (Some t) v); simpl in *; eauto.


destruct v0; simpl in *; eauto.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *; eauto.

admit. admit. admit.

assert (pt = pt) by auto.
apply n in H8. inversion H8.
assert (i2 = i2) by auto.
apply n in H8. inversion H8.

apply   IHblk_code.




(*first*)
clear H; clear IHblk_code. clear H4.

generalize fulldef. intro.
unfold fulldefinition in fulldef0.


(*first*)
generalize fulldef. intro.
unfold fulldefinition in fulldef0.
specialize (fulldef0 fn  {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}).
simpl in *.
destruct fulldef0. destruct H4. simpl in *.
specialize (H8 {| init := init; blks := blks; glbl := glbl |}   {| init := init0; blks := blks0; glbl := glbl0 |}).  destruct H8. destruct H10. destruct H11.
specialize (H12 bk  {|
         blk_id := blk_id0;
         blk_phis := blk_phis0;
         blk_code := blk_code;
         blk_term := (i2, t)  |}
          {|blk_id := blk_id0;
         blk_phis := blk_phis0;
         blk_code :=((i2, i3) :: blk_code0);
         blk_term := (i2, t)  |}).
simpl in *. destruct H12. destruct H13.
destruct H14. destruct H15. destruct H16.

inversion H12. destruct (find_block blks bk), (find_block blks0 bk). auto. auto. auto. auto.
 destruct (find_block blks bk), (find_block blks0 bk). auto. auto. auto. auto.



(*second*)


clear H; clear IHblk_code.
generalize fulldef. intro.
unfold fulldefinition in fulldef0.
specialize (fulldef0 fn  {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}).
simpl in *.
destruct fulldef0. destruct H8. simpl in *.
specialize (H10 {| init := init; blks := blks; glbl := glbl |}   {| init := init0; blks := blks0; glbl := glbl0 |}).  destruct H10. destruct H11. destruct H12.
specialize (H13 bk  {|
         blk_id := blk_id0;
         blk_phis := blk_phis0;
         blk_code := blk_code;
         blk_term := (i2, t)  |}
          {|blk_id := blk_id0;
         blk_phis := blk_phis0;
         blk_code :=((i2, i3) :: blk_code0);
         blk_term := (i2, t)  |}).
simpl in *. destruct H13. destruct H14.
destruct H15. destruct H16. destruct H17. unfold hd_fst_block_equal in H17.
unfold hdb in H17. simpl in *. auto.












(*second*)



(*third*)
admit.

(*third*)


(*fourth*)




clear IHblk_code. clear H.


generalize fulldef. intro.
unfold fulldefinition in fulldef0.
specialize (fulldef0 fn {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |}  |}).
simpl in *.
destruct fulldef0.
destruct H8.
specialize (H10    {| init := init; blks := blks; glbl := glbl |}    {| init := init0; blks := blks0; glbl := glbl0 |} ).
destruct H10. destruct H11.
destruct H12. specialize (H13 bk   {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (i2, t)  |}   {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (i2, t)  |}). simpl in *. destruct H13.
destruct (find_block blks bk). inversion H13. destruct H15. symmetry; apply H15. destruct H15.
inversion H15.
inversion Heqfindblock.


(*fourth*)



destruct (decide (i = pt)), (decide (pt = i2)). subst.




assert (i2 = i2) by auto. apply n in H8. inversion H8. subst.

apply IHblk_code.
left. clear H9. clear IHblk_code.
admit. admit. admit. admit.


subst. simpl in *.

 
clear IHblk_code.  
clear H1; clear H2.

specialize (H9 mem e s).


destruct (decide (i2 = i2)); subst; eauto.
simpl in *.


simpl in *.(*
destruct i2, i1, i3; simpl in *; eauto.

destruct ( eval_op e None op), ( eval_op e None op0); simpl in *; eauto.

induction blk_code. simpl in *. inversion H9. subst. inversion H1.
simpl in *. induction blk_code0. simpl in *.
inversion H8. simpl in *. rewrite <- Heqfind_func_fn1 in  H8. simpl in *. 
rewrite <- Heqfindblock1 in H8.




unfold block_to_cmd in H8. unfold blk_term_id in H8.
destruct a. simpl in *.
destruct ( decide (i = i0)), ( decide (i0 = IId id)), ( decide (i0 = i0));subst; simpl in *; eauto.
admit. admit. inversion H8. inversion H8.
admit. admit.



admit. admit.


subst. inversion H9. subst. simpl in *. inversion H8.  simpl in *. destruct blk_code0.
simpl in *. inversion H8. simpl in *. rewrite <- Heqfind_func_fn1 in H11.
simpl in *. rewrite <- Heqfindblock1 in H11. unfold block_to_cmd in H11.
unfold blk_term_id in H11. simpl in *. destruct p0. destruct ( decide (i = i0)), ( decide (i0 = IId id)), ( decide (i0 = i0)); subst; simpl in *. admit. admit.  inversion H11. admit.
induction i1; simpl in *; eauto. destruct ( eval_op (add_env id v e) None op1); simpl in *; eauto.
inversion H11. inversion H11. admit. inversion H11. admit.  inversion H11. inversion H11.
inversion H11. inversion H11. inversion H11. inversion H11. inversion H11. admit.
destruct i0, i1; subst; simpl in *; eauto. admit. admit.
inversion H11. admit. inversion H11. admit. inversion H11. admit. inversion H11.
admit. inversion H11. inversion H11. admit. inversion H11. inversion H11.
admit. inversion H11. inversion H11. inversion H11. inversion H11. inversion H11.
inversion H11. admit. subst. simpl in *.


(*test*)



clear H2. clear H10. induction blk_code0. simpl in *. inversion H8. inversion H2.
subst. simpl in *. inversion H10. subst. inversion H12. subst. simpl in *. inversion H12.

simpl in *. destruct a.
rewrite <- Heqfind_func_fn1 in H8. simpl in *. rewrite <- Heqfindblock1 in H8.
unfold block_to_cmd in H8. unfold blk_term_id in H8.
simpl in *.
destruct ( decide (i = i0)), ( decide (i0 = IId id)), ( decide (i0 = i0)); subst; simpl in *.
admit. admit.  inversion H8. inversion H2. simpl in *. inversion H2. subst.
destruct  blk_code0; simpl in H13. inversion H13. inversion H13. simpl in *. subst.
(*inversion h2?*) admit. admit.  (*dunno*) admit.

admit.
(*final*)
destruct i0, i1; simpl in *; eauto.
admit.
admit.
inversion H8. subst. inversion H2.
subst. simpl in *. (*in H2=*) admit.
admit.* 


(*final*)

admit.





(*test*)



apply IHblk_code. admit. admit. admit. 










admit.



admit.
















*)







(*22*)



destruct (decide (i = pt)), (decide (pt = i2)). subst.




assert (i2 = i2) by auto. apply n in H8. inversion H8. subst.


(*24*)



apply IHblk_code.
left. clear H9. clear IHblk_code.

generalize fulldef. intro. unfold fulldefinition in fulldef0.
specialize (fulldef0 fn {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}). simpl in *. destruct fulldef0. destruct H9. simpl in *.
specialize (H10  {| init := init; blks := blks; glbl := glbl |}   {| init := init0; blks := blks0; glbl := glbl0 |}). destruct H10. clear H10. destruct H11.
clear H10. destruct H11. specialize (H11 bk {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (pt, t) |}  {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := (i2, i3) :: blk_code0; blk_term := (pt, t) |}).
destruct H11. clear H12.

destruct (find_block blks bk), (  find_block blks0 bk). inversion H11. auto.
destruct H12. inversion H12. inversion Heqfindblock1. split. inversion H11.
destruct H12. auto. destruct H12. inversion H13. inversion Heqfindblock.
inversion Heqfindblock.






clear IHblk_code. clear H9.

clear H. clear H4.

generalize fulldef; intro.

unfold fulldefinition in fulldef0.
specialize (fulldef0 fn {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}). destruct fulldef0. destruct H4.
simpl in *. specialize (H8  {| init := init; blks := blks; glbl := glbl |}    {| init := init0; blks := blks0; glbl := glbl0 |}). destruct H8.
destruct H9. destruct H10. specialize (H11 bk
  {|
                   blk_id := blk_id0;
                   blk_phis := blk_phis0;
                   blk_code :=  blk_code;
                   blk_term := (pt, t) |}  {|
                    blk_id := blk_id0;
                    blk_phis := blk_phis0;
                    blk_code := (i2, i3) :: blk_code0;
                    blk_term := (pt, t) |} ). simpl in *.
destruct H11. destruct H12. destruct H13. destruct H14. destruct H15.
unfold hd_fst_block_equal in H15. unfold hdb in H15. simpl in *. apply H15.


clear H9. clear IHblk_code.



generalize fulldef; intro. unfold fulldefinition in fulldef0.
specialize (fulldef0 fn {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}). simpl in *. destruct fulldef0.  destruct H9.
specialize (H10  {| init := init; blks := blks; glbl := glbl |}  {| init := init0; blks := blks0; glbl := glbl0 |}). destruct H10. destruct H11. 
destruct H12. specialize (H13 bk
  {|
                   blk_id := blk_id0;
                   blk_phis := blk_phis0;
                   blk_code :=  blk_code;
                   blk_term := (pt, t) |}  {|
                    blk_id := blk_id0;
                    blk_phis := blk_phis0;
                    blk_code := (i2, i3) :: blk_code0;
                    blk_term := (pt, t) |} ).  simpl in *.
destruct H13. destruct H14. destruct H15. destruct H16.
destruct H17.
unfold hd_block_equal in H18. unfold hdb in H18. simpl in *. auto.



clear IHblk_code. clear H9.


generalize fulldef; intro. unfold fulldefinition in fulldef0.
specialize (fulldef0 fn  {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |} {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}). simpl in *. destruct fulldef0. destruct H9. specialize (H10  {| init := init; blks := blks; glbl := glbl |}   {| init := init0; blks := blks0; glbl := glbl0 |}). destruct H10. destruct H11. destruct H12. specialize (H13 bk  {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (pt, t) |} {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (pt, t) |}). simpl in *. destruct H13. inversion H13. 

destruct (find_block blks bk). destruct H15. symmetry. apply H15. destruct H15.
inversion H15. destruct (find_block blks bk). destruct H15. inversion H15.
inversion Heqfindblock.





(*23*)

subst. simpl in *.

 
clear IHblk_code.  
clear H1; clear H2.

specialize (H9 mem e s).


destruct (decide (i2 = i2)); subst; eauto.
simpl in *.
 

induction i2, i1, i3; simpl; eauto.

destruct (eval_op e None op), (eval_op e None op0); simpl in *; eauto.
destruct (eval_op e None op), fn0; destruct i0; simpl in *; eauto.
destruct ((find_function_entry p1 id0)); simpl in *; eauto.
destruct f; simpl in *; eauto.

destruct (map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.

inversion H9. subst. apply exec_code_implies in H12; inversion H12.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct ( map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
inversion H9; subst. apply exec_code_implies in H12. inversion H12.
inversion H9; subst; eauto. apply exec_code_implies in H12; inversion H12.
subst. rewrite <- H2. rewrite <- H2. eauto.
destruct (eval_op e None op), ptr; simpl in *; eauto.
destruct ( eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v1; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct (eval_op e None op), fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct  ( map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
inversion H9; simpl in *; subst; eauto. apply exec_code_implies in H12; inversion H12; eauto.
destruct i0; simpl in *; eauto.
destruct ((find_function_entry p id0)); simpl in *; eauto.
destruct ( map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct fn0, fn1; simpl in *; eauto.
destruct i0, i1; simpl in *; eauto.
destruct (find_function_entry p id0), (find_function_entry p1 id1); simpl in *; eauto.
destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args), ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
destruct f, f0; simpl in *; eauto.
destruct f, f0; simpl in *; eauto.
inversion H9; simpl in *; subst; eauto.

simpl_finish H12.
destruct f, f0; simpl in *; eauto.
inversion H9; simpl in *; subst. simpl_finish H12.
destruct f, f0; simpl in *; eauto.
destruct f; simpl in *; eauto.

destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto.
inversion H9. subst. simpl_finish H12.
destruct f; subst; simpl in *.
destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
inversion H9; subst.
simpl_finish H12.
destruct (find_function_entry p id0); subst; simpl in *; eauto.
destruct f; subst; simpl in *; eauto.
destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct ((find_function_entry p1 id1)); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
inversion H9; subst; simpl in *; simpl_finish H12. rewrite <- H2. rewrite <- H2. rewrite H13.
rewrite H13. eauto.
inversion H9. subst. simpl in *; simpl_finish H12.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct fn0, ptr; simpl in *; subst.
destruct i0, (eval_op e (Some t2) v); simpl in *; subst; eauto.
destruct (find_function_entry p id0); simpl in *; subst; eauto.
destruct f; simpl in *; subst; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; subst; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct ((find_function_entry p id0)), v0; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; subst; simpl in *; simpl_finish H12.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto.
subst. simpl_finish H12.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto.
simpl_finish H12.
destruct v0; simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.

destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.
destruct fn0; simpl in *; eauto; destruct i0; simpl in *; eauto.
destruct  (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.
destruct fn0; simpl in *; eauto; destruct i0; simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.
destruct fn0; simpl in *; eauto; destruct i0; simpl in *; eauto.

destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.


inversion H9; simpl in *; eauto; subst; simpl_finish H12.
destruct fn0; simpl in *; eauto; destruct i0; simpl in *; eauto.

destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.

destruct (find_function_entry p id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.

destruct ( eval_op e None op); simpl in *; eauto.
inversion H9; simpl in *; eauto; subst; simpl_finish H12.
inversion H9; subst; apply exec_code_implies in H12. inversion H12.
repeat rewrite H2. eauto.




destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.

destruct  (find_function_entry p1 id0); simpl in *; eauto.
destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto.
destruct f; simpl in *; eauto.
inversion H9; simpl in *; eauto. subst.
apply exec_code_implies in H12. inversion H12.
destruct f; simpl in *; eauto.



inversion H9; simpl in *. subst.
apply exec_code_implies in H12. inversion H12.
repeat rewrite H2. repeat rewrite <- H13. eauto.
inversion H9; simpl in *; subst.

apply exec_code_implies in H12. inversion H12.
inversion H9; simpl in *;  subst; apply exec_code_implies in H12. inversion H12.
simpl in *. inversion H9; simpl in *; subst. apply exec_code_implies in H12.
inversion H12. subst. eauto.

destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t2) v); simpl in *; eauto.
inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12.
destruct v0; simpl in *; eauto.
inversion H9; simpl in *; eauto.
subst. apply exec_code_implies in H12. inversion H12.
inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12.

inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12.
repeat rewrite H2.
eauto.

inversion H9; simpl in *; subst.


apply exec_code_implies in H12.
inversion H12.


inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 


inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

simpl in H9; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

simpl in *; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 



simpl in *; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

simpl in *; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

simpl in *; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

simpl in *; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 

simpl in *; inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12. 




destruct ptr, (eval_op e None op); simpl in *; eauto.
destruct ( eval_op e (Some t1) v); simpl in *; eauto.


destruct v0; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v1; simpl in *; eauto.
destruct ptr, fn0; simpl in *; eauto.
destruct ( eval_op e (Some t1) v), i0; simpl in *; eauto.
destruct ((find_function_entry p1 id0)); simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.

inversion H9. subst. apply exec_code_implies in H12.
inversion H12.


destruct v0, (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto. 
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.

inversion H9; simpl in *; subst.
apply exec_code_implies in H12.
inversion H12.

simpl in *.
destruct f; simpl in *; eauto.
simpl in *.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.

inversion H9; simpl in *; eauto.
subst.  apply exec_code_implies in H12.
inversion H12.



destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9.
subst.
apply exec_code_implies in H12.
 inversion H12.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9; subst; apply exec_code_implies in H12.
inversion H12.


destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.
inversion H9. subst. apply exec_code_implies in H12. inversion H12.
destruct f; simpl in *; eauto. destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto.

inversion H9.  subst. apply exec_code_implies in H12. inversion H12.

destruct v0; simpl in *; eauto.
destruct ptr; simpl in *; eauto. destruct (eval_op e (Some t2) v); simpl in *; eauto.




inversion H9; simpl in *; eauto. subst. apply exec_code_implies in H12. inversion H12.
destruct v0; simpl in *; eauto. inversion H9; simpl in *; eauto. subst.
apply exec_code_implies in H12. inversion H12. inversion H9. apply exec_code_implies in H12. inversion H12. inversion H9. subst. apply exec_code_implies in H12. inversion H12.
rewrite <- H2. rewrite <- H2. eauto.

inversion H9. apply exec_code_implies in H12. inversion H12.
inversion H9. apply exec_code_implies in H12. inversion H12.
inversion H9. apply exec_code_implies in H12. inversion H12.
inversion H9. apply exec_code_implies in H12. inversion H12.


destruct ptr0, ptr; simpl in *; eauto.





destruct (eval_op e (Some t3) v0), (eval_op e (Some t2) v); simpl in *; eauto.
destruct v1; simpl in *; eauto. destruct v1; simpl in *; eauto. destruct v1, v2; simpl in *; eauto. destruct ptr; simpl in *; eauto. destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto. destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto. destruct v0; simpl in *; eauto. destruct ptr; simpl in *; eauto. destruct (eval_op e (Some t1) v); simpl in *; auto. destruct v0; simpl in *; eauto. destruct ptr; simpl in *; eauto. destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto. destruct ptr; simpl in *; eauto.  


destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto. destruct ptr; simpl in *; eauto.

destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct  (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9; simpl in *; eauto.
apply exec_code_implies in H12. inversion H12.

simpl in *. inversion H9. apply exec_code_implies in H12. inversion H12.
destruct ptr0; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9. apply exec_code_implies in H12. inversion H12. simpl in *.
inversion H9. apply exec_code_implies in H12. inversion H12.
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args ); simpl in *; eauto.
inversion H9. apply exec_code_implies in H12. inversion H12. simpl in *. inversion H9.
apply exec_code_implies in H12. inversion H12.

destruct (ptr); simpl in *; eauto.

destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.

destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.

inversion H9; simpl in *; eauto.
subst. apply exec_code_implies in H12; inversion H12.
simpl in *; eauto. inversion H9; subst.
apply exec_code_implies in H12; inversion H12.
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto. destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto. 
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9. apply exec_code_implies in H12; inversion H12.

simpl in *; eauto. inversion H9; apply exec_code_implies in H12; inversion H12.
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct (eval_op e None op); simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct  (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto. 

inversion H9; simpl in *; eauto.
apply exec_code_implies in H12; inversion H12.





simpl in *. inversion H9. apply exec_code_implies in H12. inversion H12.
destruct ptr. destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.

simpl in *.
destruct (eval_op e None op); simpl in *; eauto.

destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
inversion H9. apply exec_code_implies in H12. inversion H12.
simpl in *. inversion H9; apply exec_code_implies in H12; inversion H12.
destruct ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v); simpl in *; eauto.
destruct v0; simpl in *; eauto.
destruct fn0; simpl in *; eauto.
destruct i0; simpl in *; eauto.
destruct (find_function_entry p1 id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
destruct t0; simpl in *; eauto.
inversion H9. apply exec_code_implies in H12. inversion H12.
destruct ptr, val; simpl in *; eauto.

destruct (eval_op e (Some t1) v0), (eval_op e (Some t0) v); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12. inversion H12.
destruct fn0; simpl in *; eauto; destruct i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t1, op0) => eval_op e (Some t1) op0) args); simpl in *; eauto.
destruct t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0; destruct i0; simpl in *; eauto.

destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args); simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct fn1; simpl in *; destruct i0; simpl in *; eauto.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
destruct t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct fn1, i0; simpl in *; eauto.

destruct (find_function_entry p1 id0); simpl in *; eauto.

destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f, t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn1, i0; simpl in *; eauto.
destruct (find_function_entry p id),  (find_function_entry p1 id0); simpl in *; eauto.
destruct f, f0; simpl in *; eauto.
destruct t0, ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0); simpl in *; eauto.
destruct t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.

destruct t1; simpl in *; inversion H9; apply exec_code_implies in H12; inversion H12.


simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct t1; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, t0; simpl in *; eauto; inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, t1; simpl in *; eauto.


destruct ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct (find_function_entry p id), t0; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct f; simpl in *; eauto.

destruct fn1, i0; simpl in *; eauto.
destruct (find_function_entry p1 id0); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args0), t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct ( map_monad (fun '(t2, op) => eval_op e (Some t2) op) args), t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct  (find_function_entry p id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args); simpl in *; eauto.
destruct t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, val, ptr; simpl in *; eauto.
destruct i0, (eval_op e (Some t1) v), ( eval_op e (Some t2) v0); simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct  (find_function_entry p id); simpl in *; eauto.
destruct f; simpl in *; eauto.
destruct (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args); simpl in *; eauto. destruct t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct (find_function_entry p id), v2; simpl in *; eauto.
destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
subst. rewrite <- H14. rewrite <- H14. rewrite H17. rewrite H17. eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.


inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, ( map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f, ( map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct fn0, i0; simpl in *; eauto.

destruct (find_function_entry p id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.

destruct (find_function_entry p1 id); simpl in *; eauto.
destruct f, (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args), t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v), (eval_op e (Some t2) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p1 id); simpl in *; eauto.
destruct f, (map_monad (fun '(t2, op) => eval_op e (Some t2) op) args), t1; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr0; simpl in *; eauto.
destruct ( eval_op e (Some t1) v), (eval_op e (Some t2) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr; simpl in *; eauto.

destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr, fn0, i0; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0), (find_function_entry p1 id);
  simpl in *; eauto.
destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.

destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v2; simpl in *; eauto.
destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.



inversion H9; apply exec_code_implies in H12; inversion H12.


destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
rewrite H14. rewrite H14. rewrite <- H17. rewrite <- H17.
eauto.


inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct f, (map_monad (fun '(t3, op) => eval_op e (Some t3) op) args), t2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v), (eval_op e (Some t2) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t1) v), (eval_op e (Some t2) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr, val0, ptr0; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0), (eval_op e (Some t2) v1), 
( eval_op e (Some t3) v2); simpl in *; eauto.
destruct v4; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v5; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v5; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v4; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v4; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v4; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct v4, v6; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p1 id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.

destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p1 id); simpl in *; eauto.
destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.



destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p1 id); simpl in *; eauto.

destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.
destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.
destruct fn0, i0; simpl in *; eauto.
destruct (find_function_entry p1 id); simpl in *; eauto.

destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.

destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct fn0, i0; simpl in *; eauto.

destruct (find_function_entry p1 id); simpl in *; eauto.

destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.

inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.

destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.


destruct fn0, i0; simpl in *; eauto.

destruct (find_function_entry p1 id); simpl in *; eauto.

destruct f, (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args), t0; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.
destruct val, ptr; simpl in *; eauto.

destruct (eval_op e (Some t0) v), (eval_op e (Some t1) v0); simpl in *; eauto.
destruct v2; simpl in *; eauto.
inversion H9; apply exec_code_implies in H12; inversion H12.



assert (i2 = i2) by auto. apply n1 in H1. inversion H1.





 




(********************)








apply IHblk_code.

clear H9; clear IHblk_code. clear H.







generalize fulldef; intro. unfold fulldefinition in fulldef0. specialize (fulldef0 fn 
 {|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |}|}

 {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}).
destruct fulldef0. destruct H8.
simpl in H9.
specialize (H9 ( {| init := init; blks := blks; glbl := glbl |}) ({| init := init0; blks := blks0; glbl := glbl0 |})). destruct H9. clear H9. destruct H10. clear H9. destruct H10.
specialize (H10 bk {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (i, t) |}  {|
    blk_id := blk_id0;
    blk_phis := blk_phis0;
    blk_code := (i2, i3) :: blk_code0;
    blk_term := (i, t) |}).
destruct H10; eauto.

clear IHblk_code; clear H9. clear H.

generalize fulldef; intro. unfold fulldefinition in fulldef0.
specialize (fulldef0 fn 
{|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}
 {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}).
destruct fulldef0.
destruct H8.
simpl in *.
specialize (H9  {| init := init; blks := blks; glbl := glbl |}
                {| init := init0; blks := blks0; glbl := glbl0 |}).
destruct H9. clear H9. destruct H10. clear H9.
destruct H10. specialize (H10 bk).
specialize (H10
 {|
                    blk_id := blk_id0;
                    blk_phis := blk_phis0;
                    blk_code := blk_code;
                    blk_term := (i, t)  |}
            {|
                    blk_id := blk_id0;
                    blk_phis := blk_phis0;
                    blk_code := (i2, i1) :: blk_code;
                    blk_term := (i, t)  |}).
destruct H10. clear H10. destruct H11. clear H10.
destruct H11. clear H10. destruct H11. clear H10.
unfold hd_fst_block_equal in H11. unfold hdb in H11. simpl in *.
destruct H11. apply H10.


clear H.
clear IHblk_code. clear H9.



(*SPECIALIZE*)

generalize fulldef; intro. unfold fulldefinition in fulldef0.
specialize (fulldef0 fn 
{|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}
 {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}).
destruct fulldef0. clear H.
destruct H8.


simpl in *.

specialize (H8  {| init := init; blks := blks; glbl := glbl |}
                {| init := init0; blks := blks0; glbl := glbl0 |}).
destruct H8. clear H8. destruct H9.
clear H8. destruct H9.

unfold hd_block_equal in H9. unfold hdb in H9.

rewrite <- Heqfind_func_fn1. simpl in *.
rewrite <- Heqfindblock1. unfold block_to_cmd. unfold blk_term_id. simpl in *.

specialize (H9 bk  {|
         blk_id := blk_id0;
         blk_phis := blk_phis0;
         blk_code := blk_code;
         blk_term := (i, t)  |}). simpl in *.
destruct (decide (i2 = i2)).

specialize (H9  {|
         blk_id := blk_id0;
         blk_phis := blk_phis0;
         blk_code :=((i2, i3) :: blk_code0);
         blk_term := (i, t)  |}).
simpl in *. destruct H9. destruct H10. destruct H11. destruct H12. destruct H13.

rewrite <- Heqfind_func_fn1 in H14. simpl in *.
rewrite <- Heqfindblock1 in H14.
unfold block_to_cmd in H14. simpl in *. unfold blk_term_id in H14. simpl in *.
destruct (decide (i2 = i2)). apply H14.
assert (i2 = i2) by auto. apply n2 in e0. inversion e0.
assert (i2 = i2) by auto. apply n2 in H10. inversion H10.


clear H9. clear IHblk_code. clear H.


generalize fulldef; intro.
unfold fulldefinition in fulldef0.
specialize (fulldef0 fn
{|
                      df_prototype := df_prototype;
                      df_args := df_args0;
                      df_instrs := {| init := init; blks := blks; glbl := glbl |} |}
  {|
                       df_prototype := df_prototype0;
                       df_args := df_args0;
                       df_instrs := {| init := init0; blks := blks0; glbl := glbl0 |} |}).
destruct fulldef0. clear H. destruct H8. clear H.
simpl in *.
specialize (H8 {| init := init; blks := blks; glbl := glbl |}
               {| init := init0; blks := blks0; glbl := glbl0 |}).

destruct H8. destruct H8. destruct H9. 

specialize (H10 bk  {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (i, t) |} {| blk_id := blk_id0; blk_phis := blk_phis0; blk_code := blk_code; blk_term := (i, t) |}). destruct H10. inversion H10.
destruct (find_block blks bk). symmetry. destruct H12. apply H12.
inversion  Heqfindblock.

destruct (  find_block blks bk). destruct H12. inversion H12. inversion Heqfindblock.














 inversion H7.
inversion H6. inversion H7. inversion H5. inversion H5. inversion H5. inversion H5.
inversion H0. inversion H0. inversion H6. inversion H0. inversion H0. inversion H5.
inversion H5. inversion H0.



specialize (H4 bk b b). destruct H4. rewrite <- Heqfindblock in H4; rewrite <- Heqfindblock1 in H4. inversion H4; destruct H6. inversion H7. inversion H6.

specialize (H4 bk b b). destruct H4. rewrite <- Heqfindblock in H4; rewrite <- Heqfindblock1 in H4. inversion H4; destruct H6. inversion H6. inversion H7.
simpl; eauto.


specialize (fulldef1 d d). destruct fulldef1; inversion H; destruct H1. inversion H2. inversion H1.


specialize (fulldef1 d d). destruct fulldef1; inversion H; destruct H1. inversion H1. inversion H2.


simpl; eauto.

*)
