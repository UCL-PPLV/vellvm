Require Import Vellvm.CFG.
Require Import Vellvm.Ollvm_ast.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Vellvm.optimisations.Kildall.kildall.
Require Import Vellvm.optimisations.Kildall.lattice.
Require Import Vellvm.optimisations.maps.
Require Import Vellvm.optimisations.local_cfg.

Set Implicit Arguments.




Module Type BACKWARD_DATAFLOW_SOLVER.

  Declare Module L: SEMILATTICE.

    Variable code: cfg. (*MCFG*)
    Variable fetch : cfg -> local_pc -> option cmd. (*MCFG -> PC -> INSTR*)

  
  Parameter fixpoint:
    forall (code: cfg) (successors: local_pc -> list local_pc)
           (transf: local_pc -> L.t -> L.t),
    option (PCMap.t L.t).
Print fetch.
    Axiom fixpoint_solution:
    forall (code: cfg) successors transf res n instr s,
    fixpoint code successors transf = Some res ->
    fetch code n = Some instr -> In s (successors n) ->
    (forall n a, fetch code n = None -> L.eq (transf n a) L.bot) ->
    L.ge res!!n (transf s res!!s).


      Parameter fixpoint_allnodes:
    forall (code: cfg) (successors: local_pc -> list local_pc)
           (transf: local_pc -> L.t -> L.t),
    option (PCMap.t L.t).

     Print fixpoint_allnodes. 
  Axiom fixpoint_allnodes_solution:
    forall (code: cfg) successors transf res n instr s,
    fixpoint_allnodes code successors transf = Some res ->
    fetch code n = Some instr -> In s (successors n) ->
    L.ge res!!n (transf s res!!s).

End BACKWARD_DATAFLOW_SOLVER.

(*
Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET):
                   BACKWARD_DATAFLOW_SOLVER with Module L := LAT.


  Definition fixpoint_from (start: state) : option (PCMap.t L.t) :=
  PrimIter.iterate _ _ step start.



Definition fixpoint_nodeset (enodes: NS.t) :=
  fixpoint_from (start_state_nodeset enodes).


Definition fixpoint :=
  DS.fixpoint_nodeset
    (make_predecessors code successors) (fun l => l)
    transf exit_points.

(*Lemma make_predecessors_correct_1:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) ->
  In n make_predecessors!!!s.
Proof.
  intros until s.
  set (P := fun m p => m!n = Some instr -> In s (successors instr) ->
                       In n p!!!s).
  unfold make_predecessors.
  apply PTree_Properties.fold_rec with (P := P); unfold P; intros.
 extensionality   apply H0; auto. rewrite H; auto.
 base case   rewrite PTree.gempty in H; congruence.
 inductive case  apply add_successors_correct.
  rewrite PTree.gsspec in H2. destruct (peq n k).
  inv H2. auto.
  auto.
Qed.

Lemma make_predecessors_correct_2:
  forall n instr s,
  code!n = Some instr -> In s (successors instr) ->
  exists l, make_predecessors!s = Some l /\ In n l.
Proof.
  intros. exploit make_predecessors_correct_1; eauto.
  unfold successors_list. destruct (make_predecessors!s); simpl; intros.
  exists l; auto.
  contradiction.
Qed.
*)

(*Definition fixpoint_allnodes :=
  DS.fixpoint_allnodes
    (make_predecessors code successors) (fun l => l)
    transf.

Theorem fixpoint_allnodes_solution:
  forall res n instr s,
  fixpoint_allnodes = Some res ->
  code!n = Some instr -> In s (successors instr) ->
  L.ge res!!n (transf s res!!s).
Proof.
  intros.
  exploit (make_predecessors_correct_2 code); eauto. intros [l [P Q]].
  unfold fixpoint_allnodes in H.
  eapply DS.fixpoint_allnodes_solution; eauto.
Qed.
 *)*)


