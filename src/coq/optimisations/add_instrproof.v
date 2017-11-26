
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.

Print find_function.



(*Let's prove the find_function does not get impacted by both*)


Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.

(*Let's recap:
This optimisation adds a useless instruction to a block if the terminator is a return void


Informally reasoning, there are two possible cases:
  -The terminator instruction is a return void. This means that the state doesn't matter because it doesn't impact the terminator instruction.
  -The terminator is not a return void. The instruction does not get added meaning the execution doesn't get affected.



Essentially, we want to solve this by induction on the terminator instruction of a block.


*)

Print incr_pc.

Print state.

Ltac try_finish := simpl; try (simpl; constructor; constructor; auto).

Print fetch.



Definition separate_fetch (o:mcfg -> mcfg) (m:mcfg) (p:pc) :=
match fetch m p with
  | Some a => Some a
  | None => None
end.


Definition nothing o : block := o.
Print find_instr.

Definition prog_nothing := def_cfg_opt nothing.


Ltac finish X :=
repeat match goal with
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Err _)) (Vis (trace_map (fun _ : state => ()) <$> Err _)) ] => constructor; constructor
  | [ |- related_event_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Err _)) (Vis (trace_map (fun _ : state => ()) <$> Err _)) ] => constructor
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Vis (trace_map (fun _ : state => ()) <$> Fin _)) (Vis (trace_map (fun _ : state => ()) <$> Fin _)) ] => constructor; constructor; auto
  | [ |- trace_equiv_step (upaco2 (trace_equiv_step (X:=())) _) (Tau () (memD _ (trace_map (fun _ : state => ()) (step_sem _ _)))) (Tau () (memD _ (trace_map (fun _ : state => ()) (step_sem _ _))))] => constructor; right; apply X

end.

Ltac destr_simpl P X:= destruct P; simpl in *; finish X.

Print terminator.

Print pc.





Lemma add_instrproof : (forall m fn bk pt, well_formed_program m optimise_program fn bk pt) -> (forall (t:terminator), t = TERM_Ret_void) -> forall st prog mem, trace_equiv (memD mem (sem (optimise_program prog) st)) (memD mem (sem (prog) st)).
Proof. intros PROGRAM CHECK. pcofix CIH. intros. pfold.
destruct st.
destruct p.





assert (memD mem (sem prog (p, e, s)) = unroll (memD mem (sem prog (p, e, s)))).
destruct (memD mem (sem prog (p, e, s))); simpl; auto. rewrite H. clear H.

assert ((memD mem (sem (optimise_program prog) (p, e, s))) = unroll ((memD mem (sem (optimise_program prog) (p, e, s))))).
destruct ((memD mem (sem (optimise_program prog) (p, e, s)))); simpl; auto. rewrite H. clear H.

simpl.


rewrite double_fetch_eq.
rewrite double_incr_pc_eq.

destruct p.
unfold double_fetch. simpl. unfold double_block_to_cmd_check. unfold double_block_to_cmd.
simpl. unfold find_instr_double. simpl.
unfold block_to_cmd.





remember (find_function prog fn) as A.
destr_simpl A CIH.
destr_simpl d CIH.
destr_simpl df_instrs CIH. simpl in *.
remember (find_block blks bk) as B.
destr_simpl B CIH.

unfold term_check.
destr_simpl b CIH. simpl in *.
destr_simpl blk_term CIH.


generalize (CHECK t). intros.
unfold blk_term_id. simpl.
destr_simpl t CIH; try inversion H.
unfold is_left. simpl in *.
destr_simpl (decide (i = pt)) CIH; subst.
destr_simpl s CIH.
destr_simpl f CIH.

remember (find_instr blk_code pt i) as C.
destr_simpl C CIH.
destr_simpl p CIH.
destr_simpl c CIH.
destr_simpl o CIH.
destr_simpl (decide (i1 = i)) CIH; subst.
destr_simpl pt CIH.
destr_simpl i0 CIH.


destr_simpl (eval_op e None op) CIH. simpl.





(*FIRST SIMULATION*)

constructor. left.
remember (({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |}, 
           add_env id v e, s)) as NEW_STATE.

assert ((memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := i |}, add_env id v e, s)))) = unroll (memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := i |}, add_env id v e, s))))).
destruct (memD mem
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := i |}, add_env id v e, s)))); auto.
rewrite H0. clear H0.

assert ((memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEW_STATE))) = unroll (memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEW_STATE)))).
destruct (memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEW_STATE))); auto.
rewrite H0. clear H0. pfold.
simpl.


(*term in old*)
rewrite <- HeqA. simpl.
rewrite <- HeqB. simpl.
unfold block_to_cmd. unfold blk_term_id. simpl.
unfold stepD.
subst.


rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch. simpl.
rewrite <- HeqA. simpl.
rewrite <- HeqB. simpl.
unfold double_block_to_cmd_check.

unfold term_check. unfold  blk_term. simpl.
unfold double_block_to_cmd. simpl.
unfold blk_term_id. simpl.
unfold is_left.
unfold find_instr_double.


simpl.


destr_simpl (decide
                      (i =
                       get_first_unused
                         {|
                         blk_id := blk_id;
                         blk_phis := blk_phis;
                         blk_code := blk_code;
                         blk_term := (i, TERM_Ret_void) |})) CIH.


(*wrong, i = (i + 1)*) admit.

unfold not in n0.

remember (find_instr blk_code
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) i) as D.

destr_simpl D CIH. (*wrong?*) admit.


simpl.


destruct (decide
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |} =
                    get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |})).

+simpl.


constructor. 

remember ((step_sem (optimise_program prog)
           ({| fn := fn; bk := bk; pt := i |},
           add_env
             (Raw
                (get_maximum
                   (get_terminator_iid
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) blk_code + 1)%Z)
             (DV VALUE_Null) (add_env id v e), s))) as NEWSTATE.

assert ((memD mem (trace_map (fun _ : state => ()) NEWSTATE)) = unroll (memD mem (trace_map (fun _ : state => ()) NEWSTATE))).
destruct (memD mem (trace_map (fun _ : state => ()) NEWSTATE)); auto. rewrite H0. simpl. subst. clear H0.
unfold step_sem. unfold stepD.
rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide (i = i)); simpl.



destr_simpl s CIH.
destr_simpl f CIH.
constructor. right. apply CIH.




unfold not in n1.
assert (i = i) by auto.
apply n1 in H0. inversion H0.


simpl. (* no instruction on left*) admit.


(*****************)


destr_simpl fn0 CIH.
destr_simpl i0 CIH.


admit.


(*SECOND SIMULATION*)


constructor. left.


remember ({| fn := fn; bk := bk; pt := i |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s) as NEWSTATE.


assert   ((memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ()) (step_sem prog NEWSTATE))) = unroll
  (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ()) (step_sem prog NEWSTATE)))).
destruct   (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ()) (step_sem prog NEWSTATE))); auto.
rewrite H0. simpl. clear H0. subst. unfold stepD.
unfold fetch. unfold incr_pc.
unfold block_to_cmd. simpl. rewrite <- HeqA; simpl.

rewrite <- HeqB; simpl. unfold blk_term_id. unfold blk_term.
simpl.



(*LEFT DONE*)





remember ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s) as NEWSTATE.


assert ((memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))) = unroll (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))).
destruct (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))); auto.
rewrite H0. simpl. subst.
clear H0.
unfold stepD.

rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide
                    (i =
                     get_first_unused
                       {|
                       blk_id := blk_id;
                       blk_phis := blk_phis;
                       blk_code := blk_code;
                       blk_term := (i, TERM_Ret_void) |})); simpl.

(*i != i + 1*) admit.

unfold find_instr_double. simpl.

destruct (find_instr blk_code
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) i).

(*find_instr blk_code of get_first_unused should give None*) admit.
destruct (                 decide
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |} =
                    get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |})). simpl.
pfold. 
constructor.





remember ({| fn := fn; bk := bk; pt := i |},
           add_env
             (Raw
                (get_maximum
                   (get_terminator_iid
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) blk_code + 1)%Z)
             (DV VALUE_Null)
             (add_env id (DVALUE_Addr (Datatypes.length mem)) e), s) as NEWSTATE.


assert (  (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))) = unroll   (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))).
destruct (  (memD (mem ++ [:: undef])%list
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))); auto.
rewrite H0. simpl. clear H0.
subst.

unfold stepD.


rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide (i = i)).
simpl. destr_simpl s CIH.
destr_simpl f CIH.
unfold not in n1. assert ( i = i) by auto.
apply n1 in H0. inversion H0.
simpl. (*no instruction on the right*) admit.


(*****************)



destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t0) v) CIH.
destr_simpl v0 CIH.







(*THIRD SIMULATION*)



constructor. left.


remember ({| fn := fn; bk := bk; pt := i |},
           add_env id ((List.nth_default undef mem a)) e, s) as NEWSTATE.


assert   ( (memD mem (trace_map (fun _ : state => ()) (step_sem prog NEWSTATE))) = unroll
  ( (memD mem (trace_map (fun _ : state => ()) (step_sem prog NEWSTATE))))).








destruct   ( (memD mem (trace_map (fun _ : state => ()) (step_sem prog NEWSTATE)))); auto.
rewrite H0. simpl. clear H0. subst. unfold stepD.
unfold fetch. unfold incr_pc.
unfold block_to_cmd. simpl. rewrite <- HeqA; simpl.

rewrite <- HeqB; simpl. unfold blk_term_id. unfold blk_term.
simpl.








(*LEFT DONE*)





remember (({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |},
           add_env id (List.nth_default undef mem a) e, s)) as NEWSTATE.


assert ((memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))) = unroll (memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))).
destruct (memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))); auto.
rewrite H0. simpl. subst.
clear H0.
unfold stepD.

rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide
                    (i =
                     get_first_unused
                       {|
                       blk_id := blk_id;
                       blk_phis := blk_phis;
                       blk_code := blk_code;
                       blk_term := (i, TERM_Ret_void) |})); simpl.


(*i != i + 1*) admit.

unfold find_instr_double. simpl.

destruct (find_instr blk_code
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) i).

(*find_instr blk_code of get_first_unused should give None*) admit.
destruct (                 decide
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |} =
                    get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |})). simpl.
pfold. 
constructor.





remember ({| fn := fn; bk := bk; pt := i |},
           add_env
             (Raw
                (get_maximum
                   (get_terminator_iid
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) blk_code + 1)%Z)
             (DV VALUE_Null) (add_env id (List.nth_default undef mem a) e),
           s) as NEWSTATE.


assert (  (memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))) = unroll (memD mem
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))).
destruct (memD mem
  (trace_map (fun _ : state => ())
     (step_sem (optimise_program prog) NEWSTATE))); auto.
rewrite H0. simpl. clear H0.
subst.

unfold stepD.


rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide (i = i)).
simpl. destr_simpl s CIH.
destr_simpl f CIH.
unfold not in n1. assert ( i = i) by auto.
apply n1 in H0. inversion H0.
simpl. (*no instruction on the right*) admit.



(*****************)



destr_simpl i0 CIH.
destr_simpl fn0 CIH.
destr_simpl i0 CIH.


(*JUMP*) admit.


destr_simpl val CIH.
destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v) CIH;
destr_simpl (eval_op e (Some t0) v0) CIH.

destr_simpl v2 CIH.



(*FOURTH SIMULATION*)




constructor. left.


remember ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |}, e, s) as NEWSTATE.


assert   ( ((memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem prog ({| fn := fn; bk := bk; pt := i |}, e, s))))) = unroll
  ( (memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem prog ({| fn := fn; bk := bk; pt := i |}, e, s)))))).








destruct   ( (memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem prog ({| fn := fn; bk := bk; pt := i |}, e, s))))); auto.


rewrite H0. simpl. clear H0. subst. unfold stepD.
unfold fetch. unfold incr_pc.
unfold block_to_cmd. simpl. rewrite <- HeqA; simpl.

rewrite <- HeqB; simpl. unfold blk_term_id. unfold blk_term.
simpl.








(*LEFT DONE*)





remember (({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |}, e, s)) as NEWSTATE.


assert ((memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))) = unroll (memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))).
destruct (memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))); auto.
rewrite H0. simpl. subst.
clear H0.
unfold stepD.

rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide
                    (i =
                     get_first_unused
                       {|
                       blk_id := blk_id;
                       blk_phis := blk_phis;
                       blk_code := blk_code;
                       blk_term := (i, TERM_Ret_void) |})); simpl.


(*i != i + 1*) admit.

unfold find_instr_double. simpl.

destruct (find_instr blk_code
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) i).

(*find_instr blk_code of get_first_unused should give None*) admit.
destruct (                 decide
                   (get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |} =
                    get_first_unused
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |})). simpl.
pfold. 
constructor.





remember ({| fn := fn; bk := bk; pt := i |},
           add_env
             (Raw
                (get_maximum
                   (get_terminator_iid
                      {|
                      blk_id := blk_id;
                      blk_phis := blk_phis;
                      blk_code := blk_code;
                      blk_term := (i, TERM_Ret_void) |}) blk_code + 1)%Z)
             (DV VALUE_Null) e, s) as NEWSTATE.


assert (  (memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE))) = unroll (memD (replace mem a v1)
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog) NEWSTATE)))).
destruct (memD (replace mem a v1)
  (trace_map (fun _ : state => ())
     (step_sem (optimise_program prog) NEWSTATE))); auto.
rewrite H0. simpl. clear H0.
subst.

unfold stepD.


rewrite double_incr_pc_eq.
rewrite double_fetch_eq.
unfold double_fetch.
unfold double_incr_pc.
simpl. rewrite <- HeqA. simpl. rewrite <- HeqB.
unfold double_block_to_cmd_check.
unfold term_check. simpl.
unfold double_block_to_cmd.
unfold blk_term_id. unfold blk_term. simpl.
unfold is_left.


destruct (decide (i = i)).
simpl. destr_simpl s CIH.
destr_simpl f CIH.
unfold not in n1. assert ( i = i) by auto.
apply n2 in H0. inversion H0.
simpl. (*no instruction on the right*) admit.



(*****************)

destr_simpl pt CIH.
destr_simpl i0 CIH.

destr_simpl (eval_op e None op) CIH.
destr_simpl fn0 CIH.

destr_simpl i0 CIH.


(*JUMP*) admit.

destr_simpl ptr CIH.


destr_simpl (eval_op e (Some t0) v) CIH.
destr_simpl v0 CIH.
destr_simpl i0 CIH.
destr_simpl fn0 CIH.
destr_simpl i0 CIH.




(*JUMP*) admit.


destr_simpl val CIH.
destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v) CIH;
destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v2 CIH.

(*No instruction on right*?*)
admit.

(*No instruction on the left? *)
admit.


Admitted.





(*Below was past experiments*)






(*


 destr_simpl b0 CIH.
destr_simpl blk_term CIH.
generalize (CHECK t). intros.
destr_simpl t CIH; try inversion H0.
  +unfold block_to_cmd. unfold blk_term_id. simpl in *. destr_simpl (decide (i = pt)) CIH; subst.
destr_simpl s CIH.
destr_simpl f CIH.





























destr_simpl s CIH. destr_simpl f CIH.
destr_simpl (find_instr blk_code pt i) CIH. destr_simpl p CIH.
destr_simpl c CIH. destr_simpl o CIH. destr_simpl (decide (i1 = i)) CIH; subst.
destr_simpl pt CIH. destr_simpl i0 CIH.
destr_simpl (eval_op e None op) CIH.

(*




 destr_simpl (find_instr blk_code pt i) CIH.
destr_simpl p CIH. destr_simpl c CIH. destr_simpl o CIH.
destr_simpl (i1 == i) CIH; subst. destr_simpl pt CIH.
destr_simpl i0 CIH. destr_simpl (eval_op e None op) CIH.
        -(*SIMULATION*) admit.
    *destr_simpl fn0 CIH. destr_simpl i0 CIH.
        -(*JUMP*) admit.
        -(*SIMULATION*) admit.
    *destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v) CIH.
destr_simpl v0 CIH.
        -(*SIMULATION*) admit.
    *destr_simpl i0 CIH. destr_simpl fn0 CIH. destr_simpl i0 CIH.
        -(*JUMP*) admit.
    *destr_simpl val CIH; destr_simpl ptr CIH. destr_simpl (eval_op e (Some t) v) CIH; destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v2 CIH.
        -(*SIMULATION*) admit.
    *destr_simpl pt CIH. destr_simpl i0 CIH. destr_simpl (eval_op e None op) CIH.
destr_simpl fn0 CIH. destr_simpl i0 CIH.
        -(*JUMP*) admit.
    *destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v) CIH.
destr_simpl v0 CIH. destr_simpl i0 CIH. destr_simpl fn0 CIH.
destr_simpl i0 CIH.
        -(*JUMP*) admit.
    *destr_simpl val CIH; destr_simpl ptr CIH. destr_simpl (eval_op e (Some t) v) CIH; destr_simpl (eval_op e (Some t0) v0) CIH.
destruct v2; simpl. constructor; constructor. constructor; constructor. constructor; right; apply CIH. constructor; constructor.
constructor; constructor. constructor; constructor. constructor; constructor.
generalize (CHECK t); intros. induction t; try inversion H0.
Admitted. 
(*
(*TERM_RET*)
  +unfold block_to_cmd. unfold blk_term_id. simpl. destr_simpl (i == pt) CIH. destr_simpl v CIH.
destr_simpl (eval_op e (Some t) v) CIH. destr_simpl s CIH.
destr_simpl f CIH. destr_simpl (find_instr blk_code pt i) CIH.
destr_simpl p CIH. destr_simpl c CIH. destr_simpl o CIH.
destr_simpl pt CIH. destr_simpl i0 CIH. destr_simpl (eval_op e None op) CIH.
destr_simpl fn0 CIH. destr_simpl i0 CIH. admit.
destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v1 CIH. destr_simpl i0 CIH. destr_simpl fn0 CIH.
destr_simpl i0 CIH. admit.

destr_simpl val CIH; destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v0) CIH;
destr_simpl (eval_op e (Some t0) v1) CIH.
destr_simpl v3 CIH.
destr_simpl t CIH.
destr_simpl v0 CIH.
destr_simpl (eval_op e (Some t) v0) CIH.
destr_simpl s CIH.
destr_simpl f CIH.
destr_simpl s CIH.
destr_simpl f CIH.
destr_simpl v0 CIH.
destr_simpl (eval_op e (Some t) v0) CIH.
destr_simpl v1 CIH.
destr_simpl (StepSemantics.Int1.eq x StepSemantics.Int1.one) CIH.
admit.
admit.
admit.







  +unfold block_to_cmd. unfold blk_term_id. simpl.
destr_simpl (i == pt ) CIH.
destr_simpl s CIH.
destr_simpl f CIH.
destr_simpl (find_instr blk_code pt i) CIH.
destr_simpl p CIH.
destr_simpl c CIH.
destr_simpl o CIH.
destr_simpl (i1 == i) CIH; subst.
  *destr_simpl pt CIH. destr_simpl i0 CIH. destr_simpl (eval_op e None op) CIH.
    -remember ((memD mem (trace_map (fun _ : state => ()) (step_sem prog ({| fn := fn; bk := bk; pt := i |}, add_env id v e, s))))) as A.
remember ((memD mem (trace_map (fun _ : state => ()) (step_sem (optimise_program prog) ({|  fn := fn;  bk := bk; pt := get_first_unused
{| blk_id := blk_id;  blk_phis := blk_phis;  blk_code := blk_code; blk_term := (i,  TERM_Ret_void) |} |}, add_env id v e, s))))) as B.
constructor. left. pfold.
assert (A = unroll A). destruct A; auto.
rewrite H. clear H.
assert (B = unroll B). destruct B; auto. rewrite H. clear H.
subst. simpl.

remember (             match find_function (optimise_program prog) fn with
             | Some a =>
                 match find_block (CFG.blks (df_instrs a)) bk with
                 | Some a0 =>
                     match
                       block_to_cmd a0
                         (get_first_unused
                            {|
                            blk_id := blk_id;
                            blk_phis := blk_phis;
                            blk_code := blk_code;
                            blk_term := (i, TERM_Ret_void) |})
                     with
                     | Some (c, _) => Some c
                     | None => None
                     end
                 | None => None
                 end
             | None => None
             end) as A.
assert (A = double_fetch prog (mk_pc fn bk i)). admit.
rewrite H. clear HeqA. subst.

remember (                 match find_function (optimise_program prog) fn with
                 | Some a =>
                     match find_block (CFG.blks (df_instrs a)) bk with
                     | Some a0 =>
                         match
                           block_to_cmd a0
                             (get_first_unused
                                {|
                                blk_id := blk_id;
                                blk_phis := blk_phis;
                                blk_code := blk_code;
                                blk_term := (i, TERM_Ret_void) |})
                         with
                         | Some (_, Some a2) => Some {| fn := fn; bk := bk; pt := a2 |}
                         | Some (_, None) => None
                         | None => None
                         end
                     | None => None
                     end
                 | None => None
                 end) as B.
assert (B = double_incr_pc prog (mk_pc fn bk i)). admit.
clear HeqB. subst.
unfold double_fetch, double_incr_pc. simpl.
unfold double_block_to_cmd_check.












    -destr_simpl fn0 CIH. destr_simpl i0 CIH. admit. (*simulation 2*) admit.
destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v) CIH. destr_simpl v0 CIH.
(*simulation 3*) admit. destr_simpl i0 CIH. destr_simpl fn0 CIH.
destr_simpl i0 CIH. admit. destr_simpl val CIH; destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v) CIH;
destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v2 CIH.
(*simulation 4*) admit.
*destr_simpl pt CIH.
destr_simpl i0 CIH.
destr_simpl (eval_op e None op) CIH.
destr_simpl fn0 CIH.
destr_simpl i0 CIH.
admit.
destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v) CIH.
destr_simpl v0 CIH.
destr_simpl i0 CIH.
destr_simpl fn0 CIH.
destr_simpl i0 CIH.
admit.
destr_simpl val CIH; destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v) CIH;
destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v2 CIH.
admit.
admit.


+admit.
+admit.
+admit.
+admit.
+admit.
+admit.
(*










    *(*First simulation*) admit.















    *destr_simpl fn0 (CIH). destr_simpl i0 CIH. admit.

    *destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v0) CIH.
    *destr_simpl v1 CIH. admit.
    *destr_simpl i0 CIH. destr_simpl fn0 CIH. destr_simpl i0 CIH. admit. 
destr_simpl val CIH. destr_simpl ptr CIH. destr_simpl (eval_op e (Some t) v0) CIH.
destr_simpl (eval_op e (Some t0) v1) CIH. destr_simpl v3 CIH. admit.
destr_simpl pt CIH. destr_simpl i0 CIH. destr_simpl (eval_op e None op) CIH.
destr_simpl fn0 CIH. destr_simpl i0 CIH. admit.
destr_simpl ptr CIH. destr_simpl (eval_op e (Some t0) v0) CIH.
destr_simpl v1 CIH. destr_simpl i0 CIH. destr_simpl fn0 CIH.
destr_simpl i0 CIH. admit. destr_simpl val CIH; destr_simpl ptr CIH.
destr_simpl (eval_op e (Some t) v0) CIH; destr_simpl (eval_op e (Some t0) v1) CIH.
destr_simpl v3 CIH. destr_simpl t CIH.
destr_simpl v0 CIH. destr_simpl (eval_op e (Some t) v0) CIH.
destr_simpl s CIH. destr_simpl f CIH. destr_simpl s CIH. destr_simpl f CIH.
destr_simpl v0 CIH. destr_simpl (eval_op e (Some t) v0) CIH.
destr_simpl v1 CIH. destr_simpl (StepSemantics.Int1.eq x StepSemantics.Int1.one) CIH.
admit. admit. admit.




Admitted.
(*




rewrite double_fetch_eq. 
rewrite double_incr_pc_eq.

destruct p.


inversion wff_prog. subst.
inversion wff_optimised_prog. subst.
inversion block_wf.
inversion block_wf0.


unfold double_fetch. simpl.
unfold double_block_to_cmd_check.
unfold double_block_to_cmd. simpl.


rewrite function_find0.



destruct p.
unfold double_fetch. unfold double_incr_pc.
simpl.
unfold fetch. 
unfold incr_pc.

unfold double_block_to_cmd_check. unfold double_block_to_cmd.
unfold find_instr_double. simpl.
unfold block_to_cmd. simpl. unfold find_function. simpl.
destruct (find_map (find_defn fn) m_definitions). simpl. destruct d.
simpl. destruct df_instrs. simpl. destruct (find_block blks bk).
simpl. destruct b. 
simpl. unfold term_check. simpl. 
unfold blk_term_id. simpl. destruct blk_term. simpl.
destruct t.
  +admit.
  +unfold ssrbool.is_left. destruct (i == pt). simpl. destruct s. constructor; constructor; auto.
    -destruct f. simpl. constructor. constructor. constructor. right. apply CIH.
destruct (find_instr blk_code pt i). destruct p. simpl. destruct c. destruct o.
destruct (i1 == i). simpl. destruct pt. destruct i0.
simpl. destruct (eval_op e None op). simpl. constructor. constructor.
simpl. constructor. left. pfold.






assert (  (memD mem
     (trace_map (fun _ : state => ())
        (step_sem
           {|
           m_name := m_name;
           m_target := m_target;
           m_datalayout := m_datalayout;
           m_globals := m_globals;
           m_declarations := m_declarations;
           m_definitions := m_definitions |}
           ({| fn := fn; bk := bk; pt := i1 |}, add_env id v e, s))))
= unroll   (memD mem
     (trace_map (fun _ : state => ())
        (step_sem
           {|
           m_name := m_name;
           m_target := m_target;
           m_datalayout := m_datalayout;
           m_globals := m_globals;
           m_declarations := m_declarations;
           m_definitions := m_definitions |}
           ({| fn := fn; bk := bk; pt := i1 |}, add_env id v e, s))))).
destruct ( (memD mem
     (trace_map (fun _ : state => ())
        (step_sem
           {|
           m_name := m_name;
           m_target := m_target;
           m_datalayout := m_datalayout;
           m_globals := m_globals;
           m_declarations := m_declarations;
           m_definitions := m_definitions |}
           ({| fn := fn; bk := bk; pt := i1 |}, add_env id v e, s))))); auto.
rewrite H. clear H.


assert (  (memD mem
     (trace_map (fun _ : state => ())
        (step_sem
           (optimise_program
              {|
              m_name := m_name;
              m_target := m_target;
              m_datalayout := m_datalayout;
              m_globals := m_globals;
              m_declarations := m_declarations;
              m_definitions := m_definitions |})
           ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |},
           add_env id v e, s))))
= unroll   (memD mem
     (trace_map (fun _ : state => ())
        (step_sem
           (optimise_program
              {|
              m_name := m_name;
              m_target := m_target;
              m_datalayout := m_datalayout;
              m_globals := m_globals;
              m_declarations := m_declarations;
              m_definitions := m_definitions |})
           ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |},
           add_env id v e, s))))).

destruct   (memD mem
     (trace_map (fun _ : state => ())
        (step_sem
           (optimise_program
              {|
              m_name := m_name;
              m_target := m_target;
              m_datalayout := m_datalayout;
              m_globals := m_globals;
              m_declarations := m_declarations;
              m_definitions := m_definitions |})
           ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i, TERM_Ret_void) |} |},
           add_env id v e, s)))); auto.
rewrite H. clear H. subst. unfold get_first_unused. simpl.














*)










Admitted.

(*
(*TERM_RET*)

  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl.
destruct (i == pt); try_finish. destruct v; simpl.
destruct (eval_op e (Some t) v); try_finish.
destruct s; try_finish.
destruct f. constructor. right. apply CIH. try_finish. 
destruct (find_instr blk_code pt i); try_finish.
destruct p; simpl. destruct c.
    *admit. (*match o*)
    *destruct t; try_finish.
      +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct s; try_finish. destruct f. constructor; right; apply CIH. try_finish.
      +destruct s; try_finish. destruct f. try_finish. constructor. right. apply CIH.
      +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct v1; try_finish. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one).
(*Jump*) admit. (*jump*) admit.
      +(*Jump*) admit.

(*TERM_RET_VOID*)
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl. unfold ssrbool.is_left. destruct (i == pt); try_finish.
    *destruct s; try_finish. destruct f. try_finish. constructor. right. apply CIH.
    *destruct (find_instr blk_code pt i); try_finish. destruct p; try_finish. destruct c.
      -simpl. (*match o*) admit.
      -simpl. (*one side no instruction*) admit.
      -simpl. (*one side no instruction *) admit.




(*TERM_BR*)
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl. destruct (i == pt). 
    *simpl. destruct v. simpl. destruct (eval_op e (Some t) v); try_finish. destruct v0; try_finish.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one).
      -simpl. (*jump*) admit.
      -simpl. (*jump*) admit.
    *simpl. destruct (find_instr blk_code pt i).
      -destruct p. simpl. destruct c.
        *simpl. (*match o*) admit.
        *destruct t; try_finish.
           +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct s; try_finish. destruct f. constructor. right. apply CIH. try_finish.
           +destruct s; try_finish. destruct f. try_finish. constructor; right; apply CIH.
           +destruct v0. destruct (eval_op e (Some t) v0); try_finish. destruct v1; try_finish.
destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one).
                -simpl. simpl. (*jump*) admit.
                -simpl. (*jump*) admit.
        *simpl. (*jump*) admit.
        *try_finish.


(*TERM_BR_1*)
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl.
destruct (i == pt).
    *simpl. (*jump*) admit.
    *simpl. destruct (find_instr blk_code pt i); try_finish. destruct p. simpl. destruct c.
      -simpl. (*match o*) admit.
      -destruct t; try_finish.
        +destruct v. simpl. destruct (eval_op e (Some t) v); try_finish. destruct s; try_finish. destruct f. constructor; right; apply CIH. try_finish.
destruct s; try_finish. destruct f. try_finish. constructor; right; apply CIH.
        +destruct v. simpl. destruct (eval_op e (Some t) v); try_finish. destruct v0; try_finish. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one).
          *simpl. (*jump*) admit.
          *simpl. (*jump*) admit.

        +(*jump*) admit.


(*TERM_SWITCH*)
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl. destruct (i == pt); try_finish. destruct (find_instr blk_code pt i).
    *simpl. destruct p. simpl. destruct c.
      -simpl. (*match o*) admit.
      -destruct t; try_finish.
        +destruct v0. destruct (eval_op e (Some t) v0); try_finish. destruct s; try_finish. destruct f. constructor; right; apply CIH. try_finish.
destruct s; try_finish. destruct f. try_finish. constructor; right; apply CIH.
        +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct v1; try_finish. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one).
simpl. (*jump*) admit. simpl. (*jump*) admit. (*jump*) admit. try_finish.

(*TERM_INDIRECTBR*)

  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl.
destruct (i == pt); try_finish. simpl. destruct (find_instr blk_code pt i); try_finish.
destruct p; simpl. destruct c.
    *(*match 0*) admit.
    *destruct t; try_finish.
      +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct s; try_finish. destruct f. constructor. right. apply CIH. try_finish.
      +destruct s; try_finish. destruct f. try_finish. constructor. right. apply CIH.
      +destruct v0. destruct (eval_op e (Some t) v0); try_finish. destruct v1; try_finish. (*jump*) admit.
      +(*jump *)admit.


(*TERM_RESUME*)
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl.
destruct (i == pt); try_finish. simpl. destruct (find_instr blk_code pt i); try_finish.
destruct p; simpl. destruct c.
    *(*match o*)admit.
    *destruct t; try_finish.
      +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct s; try_finish. destruct f. constructor. right. apply CIH. try_finish.
      +destruct s; try_finish. destruct f. try_finish. constructor. right. apply CIH.
      +destruct v0. simpl. destruct (eval_op e (Some t) v0); try_finish. destruct v1; try_finish. (*jump*) admit.
      +(*jump*) admit.



(*TERM_INVOKE*)
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl.
destruct (i == pt); try_finish.
    -simpl. destruct (find_instr blk_code pt i); try_finish. destruct p.
simpl. destruct c.
      *simpl. destruct o. unfold ssrbool.is_left. simpl. destruct (i1 == i). simpl. induction pt.
         +induction i0.
            -destruct (eval_op e None op). simpl. try_finish.
                *simpl. admit.















































                *destruct fn0. destruct i0. simpl. admit.
                *try_finish.
                *simpl. 
constructor. left.
assert ( (memD (mem ++ [undef])
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := i1 |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))) = 
unroll  (memD (mem ++ [undef])
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := i1 |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))).
destruct  (memD (mem ++ [undef])
     (trace_map (fun _ : state => ())
        (step_sem prog
           ({| fn := fn; bk := bk; pt := i1 |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))); auto. rewrite H.
clear H. 
assert (  (memD (mem ++ [undef])
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog)
           ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i,
                                TERM_Invoke fnptrval args to_label
                                  unwind_label) |} |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s)))) =
unroll  (memD (mem ++ [undef])
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog)
           ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i,
                                TERM_Invoke fnptrval args to_label
                                  unwind_label) |} |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))).
destruct (  (memD (mem ++ [undef])
     (trace_map (fun _ : state => ())
        (step_sem (optimise_program prog)
           ({|
            fn := fn;
            bk := bk;
            pt := get_first_unused
                    {|
                    blk_id := blk_id;
                    blk_phis := blk_phis;
                    blk_code := blk_code;
                    blk_term := (i,
                                TERM_Invoke fnptrval args to_label
                                  unwind_label) |} |},
           add_env id (DVALUE_Addr (Datatypes.length mem)) e, s))))); auto.
rewrite H.  clear H.
















(*simulation*) admit.
                *destruct ptr. destruct (eval_op e (Some t0) v); simpl.
                *try_finish.
                *destruct v0. try_finish. try_finish. 
                *simpl. (*simulation*) admit.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *try_finish.
                *destruct i0.
                *try_finish.
                *destruct fn0. destruct i0. simpl. admit. try_finish. try_finish.  try_finish.
                *destruct val, ptr. destruct (eval_op e (Some t) v); simpl. try_finish. destruct (eval_op e (Some t0) v0).
simpl. try_finish. simpl. destruct v2. try_finish. try_finish. (*simulation*) admit. try_finish. try_finish.
try_finish. try_finish. try_finish. try_finish. try_finish. try_finish. try_finish. try_finish. simpl.
destruct pt. destruct i0. destruct (eval_op e None op). simpl. try_finish. simpl. constructor. right. apply CIH.
destruct fn0.  destruct i0. simpl. admit. try_finish. simpl. constructor. right. apply CIH. simpl.
destruct ptr. destruct (eval_op e (Some t0) v). simpl. try_finish. try_finish. destruct v0.
try_finish. try_finish. simpl. constructor. right. apply CIH. try_finish. try_finish. try_finish.
try_finish. try_finish. try_finish. try_finish. try_finish. try_finish. try_finish. try_finish.
destruct i0. try_finish. destruct fn0. destruct i0. admit. try_finish. try_finish. try_finish.
destruct val, ptr. simpl. destruct (eval_op e (Some t) v). try_finish. simpl. destruct (eval_op e (Some t0) v0).
try_finish. try_finish. destruct v2. try_finish. try_finish. admit. try_finish. try_finish. try_finish. try_finish. try_finish.
try_finish. try_finish. try_finish. try_finish. try_finish. try_finish.
      *destruct t; try_finish.
        +destruct v. simpl. destruct (eval_op e (Some t) v); try_finish. destruct s; try_finish. destruct f. constructor. right. apply CIH. try_finish.
        +destruct s; try_finish. destruct f. simpl. try_finish. constructor. right. apply CIH.
        +destruct v. simpl. destruct (eval_op e (Some t) v); try_finish. destruct v0; try_finish. admit. (*jump*)
        +admit.
 Admitted.*)
*) Admitted. *) *)*) Admitted.