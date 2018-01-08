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
  | Some (h1, t1), Some (h2, t2) => forall mem e s, compare_seq (exec_code1 m1 b1.(blk_code) (tauitem mem (mk_pc fnid bkid h1, e, s))) (exec_code1 m2 b2.(blk_code)
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


Lemma  list_implies_head : forall (h1 h2:option (finish_item state)) t1 t2,  (h1 :: t1) = (h2 :: t2) -> h1 = h2. intros. inversion H. eauto. Qed.


Lemma  compare_seq_implies_starting_state : forall p p1 blk_code blk_code0 mem s0 s1, compare_seq (exec_code1 p blk_code (tauitem mem s0))
                                                                                                  (exec_code1 p1 blk_code0 (tauitem mem s1)) -> s0 = s1.
Proof. intros. destruct blk_code, blk_code0; simpl in *; inversion H; subst.
       +inversion H3; eauto.
       +subst. destruct p0. simpl in *. destruct ( CFG_step i0 p1 s1). inversion H. inversion H5; eauto. inversion H; inversion H5; eauto. destruct m; simpl in *; inversion H; eauto. inversion H5; eauto. inversion H5; eauto. subst. destruct e; simpl in *; eauto. inversion H; simpl in *; eauto. inversion H7; eauto. inversion H; inversion H7; eauto. inversion H; inversion H7; eauto. inversion H2; eauto. destruct p0. simpl in *; eauto. destruct (CFG_step i0 p s0); eauto. simpl in *; eauto. inversion H; inversion H5; eauto. inversion H; inversion H5; eauto. destruct m; simpl in *. inversion H. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct e; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto.  inversion H; eauto. inversion H5; eauto.
        destruct p0, p2; simpl in *; eauto. destruct (CFG_step i0 p s0), (CFG_step i2 p1 s1); simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct m; simpl in *; inversion H.  inversion H5; eauto. inversion H5; eauto. induction e; simpl in *; inversion H. inversion H10; eauto. inversion H10; eauto. inversion H10; eauto.
        inversion H10; eauto. inversion H; simpl in *; eauto. inversion H5; eauto. inversion H; simpl in *; eauto. inversion H5; eauto. destruct m; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H. inversion H5; eauto. destruct e; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct m; eauto. inversion H; eauto.  inversion H5; eauto. inversion H; eauto. inversion H5; eauto. destruct e; simpl in *; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; eauto. inversion H; eauto. inversion H5; subst. eauto. subst. inversion H. subst. inversion H5. auto. destruct m. inversion H. subst.
        inversion H5. eauto.
        inversion H. subst. inversion H5. eauto. destruct e; simpl in *.
        rewrite H1 in H2. apply list_implies_head in H2.  inversion H2. eauto. rewrite H1 in H2. apply list_implies_head in H2. inversion H2.
        eauto. rewrite H1 in H2. apply list_implies_head in H2. inversion H2.
        eauto. rewrite H1 in H2. inversion H2. eauto. destruct m, m0. rewrite H1 in H2. apply list_implies_head in H2. inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. destruct e; simpl in *; eauto. rewrite H1 in H2. apply list_implies_head in H2. inversion H2; eauto. rewrite H1 in H2. inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2. inversion H2. eauto. rewrite H1 in H2. inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. destruct e; simpl in *; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. destruct e; simpl in *; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; eauto. rewrite H1 in H2; inversion H2; simpl in *; eauto. rewrite H1 in H2. destruct e; simpl in *; inversion H2; eauto. rewrite H1 in H2; destruct e, e0; simpl in *; inversion H2; eauto. destruct p0, p2. simpl in *; eauto.
        destruct (CFG_step i0 p s0), (CFG_step i2 p1 s1). apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         destruct m; simpl in *.  apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto. 
        apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
destruct e; simpl in *; eauto.  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto. apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
         apply list_implies_head in H0.
         apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
          apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct m; simpl in *; eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
destruct m; simpl in *; eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

destruct e; simpl in *; eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct m; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                 apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

        destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

        destruct m, m0; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

        destruct e; simpl in *.           apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
        destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

destruct e; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
                  apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  destruct e; simpl in *; eauto.
                                    apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

destruct e, e0; simpl in *; eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.
                  apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

                          apply list_implies_head in H0.
        apply  list_implies_head in H1. rewrite H0 in H1. inversion H1. eauto.

         Qed.



Lemma  compare_seq_implies_starting_state_vis : forall p p1 blk_code blk_code0 mem s0 s1, compare_seq (exec_code1 p blk_code (visitem mem s0))
                                                                                                      (exec_code1 p1 blk_code0 (visitem mem s1)) -> s0 = s1.

Proof. intros.
       induction blk_code, blk_code0; simpl in *; eauto. destruct s1, s0; simpl in *; eauto; inversion H; subst.
       inversion H3; eauto. inversion H3; eauto. inversion H3; eauto. inversion H3; eauto.
       inversion H3; eauto. inversion H3; eauto.  inversion H3; eauto. inversion H3; eauto. inversion H3; eauto.


       destruct s0; simpl in *; eauto; inversion H; subst. inversion H3; eauto. inversion H3; eauto. inversion H3; eauto.


       simpl in *; eauto. destruct s1; simpl in *; eauto. simpl in *; eauto. inversion H; eauto. subst. inversion H3; eauto.
       simpl in *; eauto. inversion H; eauto. subst. inversion H3; eauto. simpl in *; eauto. inversion H; eauto. subst. inversion H3; eauto. simpl in *; eauto. inversion H; eauto. inversion H3; eauto. Qed.      

       
 Lemma exec_code_implies : forall p p1 a b blk_code blk_code0, compare_seq (exec_code1 p blk_code a)
                                                                           (exec_code1 p1 blk_code0 b) -> a = b.

 Proof.  intros. induction blk_code, blk_code0.
         +simpl in *. inversion H. destruct a, b; inversion H1; inversion H2. destruct e, e0; inversion H1; inversion h2.    inversion H3. subst. rewrite H0 in H1.
          destruct a, b. inversion H1; eauto. destruct e; simpl in *. inversion H1. inversion H1. inversion H1. destruct e. inversion H1.
          inversion H1. inversion H1. destruct e, e0. inversion H1. subst. eauto. inversion H1. inversion H1. inversion H1. inversion H1; eauto.
          inversion H1; eauto. inversion H1. inversion H1; eauto. inversion H1; eauto.
          simpl in *. destruct a, b. inversion H0; inversion H1. subst. inversion H11. eauto. destruct e. inversion H0; inversion H1. subst. inversion H11. inversion H1; inversion H0. subst. inversion H11. inversion H0; inversion H1. subst. inversion H11. destruct e. inversion H0; inversion H1. subst. inversion H11. subst. inversion H1; inversion H0. inversion H0; inversion H1. subst. inversion H11. destruct e, e0.
          inversion H1; inversion H0; subst. inversion H11. auto. inversion H1; inversion H0; subst. inversion H11.
          inversion H1; inversion H0; subst. inversion H11. inversion H1; inversion H0; eauto. subst. inversion H11. inversion H0; inversion H1.
          subst. inversion H11. auto. inversion H0; inversion H1. subst. inversion H11. subst. inversion H1; inversion H0. subst. inversion H0; inversion H1. subst. inversion H0; inversion H1. simpl in *.

          destruct a, b.   destruct (CFG_step (snd p0) p1 s0); simpl in *; inversion H; subst; auto; try inversion H3; eauto. destruct m1.
          inversion H2. auto. inversion H2. auto. destruct e; simpl in *. inversion H2. auto. inversion H2. auto. inversion H2. auto.
          inversion H2. auto. inversion H. subst. inversion H3. destruct e, ( CFG_step (snd p0) p1 s); inversion H; subst; auto; try inversion H3. 
          destruct m1; inversion H2; destruct e; simpl in *. inversion H1. inversion H1. inversion H1. inversion H1. destruct m1; simpl in *; inversion H2. destruct e; simpl in *. inversion H1. inversion H1. inversion H1. inversion H1. destruct m1; simpl in *; inversion H2.
          destruct e0; simpl in *; inversion H1. destruct e; simpl in *; inversion H; subst; inversion H3; auto.

          (*2*)


          destruct a, b. simpl in *. destruct (CFG_step (snd a0) p s). inversion H. inversion H3.
          auto. inversion H. inversion H3. auto. destruct m1; simpl in *; eauto. inversion H. inversion H3.
        auto. inversion H. subst. inversion H3; eauto. destruct e; simpl in *; eauto. inversion H. inversion H3; eauto. inversion H. subst. inversion H3. auto. inversion H. inversion H3. auto. inversion H. inversion H3. auto. simpl in *. destruct e, ( CFG_step (snd a0) p ). inversion H. inversion H3. inversion H. inversion H3. destruct m1; simpl in *. inversion H. inversion H3. inversion H. inversion H3. destruct e; simpl in *; eauto. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. destruct m1; simpl in *; eauto. inversion H. inversion H3. inversion H. inversion H3. destruct e; simpl in *; eauto. inversion H. subst. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. destruct m1; simpl in *.  inversion H. inversion H3. inversion H. inversion H3. destruct e0; simpl in *; eauto. simpl in *. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. inversion H3. inversion H. subst. destruct e0. inversion H2. auto. inversion H2. auto. inversion H2. auto.
        

          (*1*)
          destruct a, b. simpl in *. inversion H. rewrite H1 in H2. destruct (CFG_step (snd a0) p s), (CFG_step (snd p0) p1 s). inversion H1. inversion H1. inversion H1. inversion H1. inversion H1.
          inversion H1. destruct m1. inversion H1. inversion H1. destruct e; simpl in *. inversion H1. inversion H1. inversion H1. inversion H1. destruct m1; simpl in *. inversion H1. inversion H1. destruct e; simpl in *; eauto. inversion H1. inversion H1. inversion H1. inversion H1. destruct m1; simpl in *. inversion H1. inversion H1. destruct e; simpl in *; eauto. inversion H1. inversion H1. inversion H1. inversion H1.


          destruct a0, p0. simpl in *. destruct (CFG_step i0 p s), (CFG_step i2 p1 s0).
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct m1.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct m1; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct m1; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
destruct e; simpl in *; eauto.          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
destruct m1; simpl in *; eauto.          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct m1, m2; simpl in *; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
 destruct e; simpl in *; eauto. 

          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          destruct e, e0; simpl in *; eauto.
                    inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
          inversion H0; inversion H1; subst. inversion H7; eauto.
simpl in *.    destruct a0. simpl in *.

destruct (CFG_step i0 p s). inversion H. subst. inversion H3. inversion H. subst. inversion H3. destruct m1; simpl in *; eauto. inversion H. subst. inversion H3. inversion H. subst. inversion H3.
destruct e0; simpl in *; eauto. inversion H. subst. inversion H3.
inversion H. subst. inversion H3. inversion H. subst. inversion H3. inversion H. subst. inversion H3. inversion H. subst. destruct (CFG_step (snd p0) p1 s). inversion H2. inversion H2. destruct m1. inversion H2. inversion H2. destruct e0; simpl in *; eauto. inversion H2. inversion H2. inversion H2. inversion H2. inversion H. subst. inversion H3. subst. eauto.  Qed.
















 






          

Lemma compare_seq_two_fin : forall p p1 v v0 blk_code blk_code0 mem (r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st))) (H12 : compare_seq
          (exec_code1 p blk_code (visitem mem (Fin v)))
          (exec_code1 p1 blk_code0 (visitem mem (Fin v0)))), trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Fin v))
    (Vis (trace_map (fun _ : state => ()) <$> Fin v0)).
Proof. intros. apply exec_code_implies in H12. inversion H12. eauto. Qed.
Hint Resolve compare_seq_two_fin.




Lemma compare_seq_two_tau : forall p p1 i2 e s s1 s0 fn bk blk_code blk_code0 mem (r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st)))

(  H9 : compare_seq
         (Some
            (tauitem mem
               ({| fn := fn; bk := bk; pt := i2 |}, e, s))
          :: exec_code1 p blk_code (tauitem mem s0))
         (Some
            (tauitem mem
               ({| fn := fn; bk := bk; pt := i2 |}, e, s))
          :: exec_code1 p1 blk_code0 (tauitem mem s1))),


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ()) (step_sem p s0))))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem p1 s1))))
.
Proof. intros. inversion H9. subst. apply exec_code_implies in H4. inversion H4. eauto. Qed.

Hint Resolve compare_seq_two_tau.

Ltac simpl_finish x := apply exec_code_implies in x; inversion x; eauto.

Lemma compare_seq_err_tau : forall p1 p e s i blk_code blk_code0 v s0 mem fn bk id(r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st)))

( H9 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 p blk_code (visitem mem (Err s0)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 p1 blk_code0
               (tauitem mem
                        ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}, add_env id v e, s)))
  ),


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err s0))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem p1
                ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}, add_env id v e, s)))))
.
Proof. intros. inversion H9. subst. apply exec_code_implies in H4. inversion H4. Qed.

Hint Resolve compare_seq_err_tau.



Lemma compare_seq_err_tau_v2 : forall p1 p p0 l args0 e s i blk_code blk_code0 v s0 mem fn bk id(r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st)))

( H9 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 p blk_code (visitem mem (Err s0)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 p1 blk_code0
               (tauitem mem
                  (p0, combine args0 l,
                  KRet e id {| fn := fn; bk := bk; pt := fallthrough blk_code0 i |} :: s)))
  ),


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err s0))
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem p1
                ({| fn := fn; bk := bk; pt := fallthrough blk_code0 i |}, add_env id v e, s)))))
.
Proof. intros. inversion H9. subst. apply exec_code_implies in H4. inversion H4. Qed.

Hint Resolve compare_seq_err_tau_v2.










Lemma compare_seq_tau_err : forall p1 p e s i blk_code blk_code0 v s0 mem fn bk id(r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st)))

(H9 : compare_seq
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 p blk_code
               (tauitem mem
                  ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v e, s)))
         (Some (tauitem mem ({| fn := fn; bk := bk; pt := IId id |}, e, s))
          :: exec_code1 p1 blk_code0 (visitem mem (Err s0)))

  ),


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Tau ()
       (memD mem
          (trace_map (fun _ : state => ())
             (step_sem p
                ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id v e, s)))))
    (Vis (trace_map (fun _ : state => ()) <$> Err s0))
.
Proof. intros. inversion H9. subst. apply exec_code_implies in H4. inversion H4. Qed.

Hint Resolve compare_seq_tau_err.





Lemma compare_seq_case_1 : forall p1 p e blk_code blk_code0  mem   args0 A S1 B (r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st)))

(  H9 : compare_seq
         (Some (tauitem mem S1)
          :: exec_code1 p blk_code (visitem mem (Err (B))))
         (match
           (do _ <- map_monad (fun '(t, op) => eval_op e (Some t) op) args0;
            t_raise A)
         with
         | Step s' =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (tauitem mem s')
         | Jump s' =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (tauitem mem s')
         | Obs (Fin s') =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (visitem mem (Fin s'))
         | Obs (Err s') =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (visitem mem (Err s'))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ =>
                 [:: Some (tauitem mem (S1))]
             | inr (m', v, k) =>
                 Some (tauitem mem S1)
                 :: exec_code1 p1 blk_code0 (tauitem m' (k v))
             end
         end)


  ),


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err (B)))
    match
      match
        match
          match
            (do _ <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0;
             t_raise A)
          with
          | Step s' => Tau S1 (step_sem p1 s')
          | Jump s' => Tau S1 (step_sem p1 s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m) => Vis (Eff (effects_map (step_sem p1) m))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e1) =>
          match mem_step e1 mem with
          | inl e2 => Vis (Eff e2)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros. inversion H9.
       destruct ( map_monad (fun '(t0, op) => eval_op e (Some t0) op) args0); simpl in *; eauto. Qed.

Hint Resolve  compare_seq_case_1.





Lemma jump_equiv : forall (r: Trace() -> Trace () -> Prop) s e br1 p p1 fn bk pt mem
  (CIH : forall (st : state) (mem : memory), r (memD mem (sem p st)) (memD mem (sem p1 st)))
(  fulldef : fulldefinition p p1)

  ,

  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match (do st <- jump p fn bk br1 e s; Jump st) with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem p s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem p s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m) => Vis (Eff (effects_map (step_sem p) m))
          end
        with
        | Vis v0 => Vis (trace_map (fun _ : state => ()) <$> v0)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x0) => Vis x0
      | Vis (Err _ as x0) => Vis x0
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e2 => Vis (Eff e2)
          | inr (m', v0, k) => Tau () (memD m' (k v0))
          end
      | Tau x0 d' => Tau x0 (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match (do st <- jump p1 fn bk br1 e s; Jump st) with
          | Step s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem p1 s')
          | Jump s' => Tau ({| fn := fn; bk := bk; pt := pt |}, e, s) (step_sem p1 s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m) => Vis (Eff (effects_map (step_sem p1) m))
          end
        with
        | Vis v0 => Vis (trace_map (fun _ : state => ()) <$> v0)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x0) => Vis x0
      | Vis (Err _ as x0) => Vis x0
      | Vis (Eff e0) =>
          match mem_step e0 mem with
          | inl e2 => Vis (Eff e2)
          | inr (m', v0, k) => Tau () (memD m' (k v0))
          end
      | Tau x0 d' => Tau x0 (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.
Proof. intros. unfold jump. unfold find_block_entry. simpl in *.
       generalize fulldef. intro. unfold fulldefinition in fulldef.
       specialize (fulldef fn).
       remember (find_function p fn) as findfunc.
       remember (find_function p1 fn) as findfunc1.
       destruct findfunc, findfunc1; simpl in *; eauto.

       specialize (fulldef d d0). destruct fulldef. clear H. destruct H0. unfold is_left in H0.
       simpl in *. destruct d, d0; simpl in *. specialize (H0 df_instrs df_instrs0).
       destruct H0. clear H0. destruct H1. clear H0. destruct H1. destruct df_instrs, df_instrs0. simpl in *.
       remember (find_block blks br1) as findblock.
       remember (find_block blks0 br1) as findblock1.
       destruct findblock, findblock1; simpl in *; eauto. simpl in *.
       specialize (H1 br1 b b0). destruct H1. destruct H2. destruct H3. destruct H4.
       unfold is_left in *. destruct b, b0; simpl in *. destruct (decide (blk_id = blk_id0)),
                                                        (decide (blk_phis = blk_phis0)), ( decide (blk_term = blk_term0)); simpl in *; subst. unfold monad_fold_right. simpl in *.
remember ( (fix
                monad_fold_right (A B : Type) (M : Type -> Type) (H6 : Functor M) 
                                 (H7 : Monad) (f : A -> B -> M A) (l : seq B) 
                                 (a : A) {struct l} : M A :=
                  match l with
                  | [::] => mret a
                  | x :: xs => monad_fold_right A B M H6 H7 f xs a ≫= (fun y : A => f y x)
                  end)) as A.
rewrite <- HeqA. destruct A; simpl in *; eauto.
unfold blk_entry_pc. simpl in *. unfold blk_entry_id. simpl in *. unfold blk_term_id.
destruct blk_term. simpl in *. eauto.

destruct blk_code, blk_code0; simpl in *; eauto.
destruct H5. unfold hd_fst_block_equal in H5. unfold hdb in H5. simpl in H5. inversion H5.
unfold hd_fst_block_equal in H5. unfold hdb in H5. simpl in H5. destruct p0.
destruct H5. inversion H5. destruct p0, p2. unfold hd_fst_block_equal in H5.
unfold hdb in H5. simpl in H5. destruct H5. subst. eauto. inversion H4. inversion H3.
inversion H3. inversion H2. inversion H2. inversion H3. inversion H2.
specialize (H1 br1 b b). destruct H1. rewrite <- Heqfindblock in H1. rewrite <- Heqfindblock1 in H1. inversion H1. destruct H3. inversion H4. destruct H3. inversion H3.

specialize (H1 br1 b b). destruct H1. rewrite <- Heqfindblock in H1. rewrite <- Heqfindblock1 in H1. inversion H1. destruct H3. inversion H3. destruct H3. inversion H4.


specialize (fulldef d d). destruct fulldef. inversion H. destruct H1. inversion H2. destruct H1.
inversion H1.

specialize (fulldef d d). destruct fulldef. inversion H. destruct H1. inversion H1. destruct H1. inversion H2. Qed.











Lemma compare_seq_case_2 : forall p1 p S2 e blk_code blk_code0  mem   args0 A S1  (r:Trace () -> Trace () -> Prop) (CIH : forall (st : state) (mem : memory),  r (memD mem (sem p st)) (memD mem (sem p1 st)))

(   H9 : compare_seq
         (Some (tauitem mem S1)
          :: exec_code1 p blk_code (visitem mem (Err (A))))
         match
           (do dvs <- map_monad (fun '(t, op) => eval_op e (Some t) op) args0;
            Step
              (
             S2))
         with
         | Step s' =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (tauitem mem s')
         | Jump s' =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (tauitem mem s')
         | Obs (Fin s') =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (visitem mem (Fin s'))
         | Obs (Err s') =>
             Some (tauitem mem S1)
             :: exec_code1 p1 blk_code0 (visitem mem (Err s'))
         | Obs (Eff s') =>
             match mem_step s' mem with
             | inl _ => [:: Some (tauitem mem S1)]
             | inr (m', v, k) =>
                 Some (tauitem mem S1)
                 :: exec_code1 p1 blk_code0 (tauitem m' (k v))
             end
         end


  ),


  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    (Vis (trace_map (fun _ : state => ()) <$> Err (A)))
    match
      match
        match
          match
            (do dvs <- map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0;
             Step
               (
               S2))
          with
          | Step s' => Tau S1 (step_sem p1 s')
          | Jump s' => Tau S1 (step_sem p1 s')
          | Obs (Fin s0) => Vis (Fin s0)
          | Obs (Err s0) => Vis (Err s0)
          | Obs (Eff m) => Vis (Eff (effects_map (step_sem p1) m))
          end
        with
        | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
        | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
        end
      with
      | Vis (Fin _ as x) => Vis x
      | Vis (Err _ as x) => Vis x
      | Vis (Eff e1) =>
          match mem_step e1 mem with
          | inl e2 => Vis (Eff e2)
          | inr (m', v, k) => Tau () (memD m' (k v))
          end
      | Tau x d' => Tau x (memD mem d')
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
.
Proof. intros.
destruct (map_monad (fun '(t1, op) => eval_op e (Some t1) op) args0); simpl in *; eauto. inversion H9. subst. apply exec_code_implies in H4. inversion H4.
 Qed.

Hint Resolve  compare_seq_case_2.





















Lemma Test123 : forall prog prog1, fulldefinition prog prog1 -> forall st mem, trace_equiv (memD mem (sem prog st)) (memD mem (sem prog1 st)).
Proof. intros p p1 fulldef. pcofix CIH. intros. pfold.


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

eapply jump_equiv; eauto.
eapply jump_equiv; eauto.
eapply jump_equiv; eauto.

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
specialize (H10 {| init := init; blks := blks; glbl := glbl |}   {| init := init0; blks := blks0; glbl := glbl0 |}). destruct H10. destruct H11. destruct H12.
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
destruct H15. destruct H16. destruct H17.
unfold hd_block_equal in H18. unfold hdb in H18. simpl in *. auto.


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



Qed.