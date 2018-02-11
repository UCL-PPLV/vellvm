Require Import Vellvm.optimisations.maps.
Require Import Vellvm.optimisations.Kildall.lattice.
Require Import Coqlib.
Require Import Vellvm.CFG Vellvm.CFGProp Vellvm.Effects Vellvm.Memory.
Require Import compcert.lib.Iteration.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.local_cfg.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Print mcfg.
Print stack.
Module Type NODE_SET.

  Parameter t: Type.
  Parameter empty: t.
  Parameter add: local_pc -> t -> t.
  Parameter pick: t -> option (local_pc * t).
  Parameter all_nodes: cfg -> t.

  Parameter In: local_pc -> t -> Prop.
  Axiom empty_spec:
    forall n, ~In n empty.
  Axiom add_spec:
    forall n n' s, In n' (add n s) <-> n = n' \/ In n' s.
  Axiom pick_none:
    forall s n, pick s = None -> ~In n s.
  Axiom pick_some:
    forall s n s', pick s = Some(n, s') ->
    forall n', In n' s <-> n = n' \/ In n' s'.
  Axiom all_nodes_spec:
    forall code n instr,
    fetch code n = Some instr -> In n (all_nodes code).

End NODE_SET.

Print cmd.
Section REACHABLE.
Context (fetch: cfg -> local_pc -> option cmd) (code: cfg) (successors:  cfg -> local_pc -> list local_pc).

Inductive reachable: local_pc -> local_pc -> Prop :=
  | reachable_refl: forall n, reachable n n
  | reachable_left: forall n1 n2 n3 i,
      fetch code n1 = Some i -> In n2 (successors code n1) -> reachable n2 n3 ->
      reachable n1 n3.

Scheme reachable_ind := Induction for reachable Sort Prop.

Lemma reachable_trans:
  forall n1 n2, reachable n1 n2 -> forall n3, reachable n2 n3 -> reachable n1 n3.
Proof.
  induction 1; intros.
- auto.
- econstructor; eauto.
Qed.

Lemma reachable_right:
  forall  n1 n2 n3 i,
  reachable n1 n2 -> fetch code n2 = Some i -> In n3 (successors code n2) ->
  reachable n1 n3.
Proof.
  intros. apply reachable_trans with n2; auto. econstructor; eauto. constructor.
Qed.


End REACHABLE.

Module Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET).

  Module L := LAT.

  Section Kildall.


    Context {A: Type} (*LATTICE*)  {B: Type}. (*CODE*)
    Variable code: cfg. (*MCFG*)
    Variable fetch : cfg -> local_pc -> option cmd. (*MCFG -> PC -> INSTR*)
    Variable successors:  cfg -> local_pc -> list local_pc.
Variable transf: cfg -> local_pc -> L.t -> L.t.


Record state : Type :=
  mkstate { aval: PCTree.t L.t; worklist: NS.t; visited: local_pc -> Prop }.

Definition abstr_value (n: local_pc) (s: state) : L.t :=
  match PCTree.get n (s.(aval)) with
  | None => L.bot
  | Some v => v
  end.


Definition propagate_succ (s: state) (out: L.t) (n: local_pc) :=
  match PCTree.get n (s.(aval)) with
  | None =>
      {| aval := PCTree.set n out s.(aval);
         worklist := NS.add n s.(worklist);
         visited := fun p => p = n \/ s.(visited) p |}
  | Some oldl =>
      let newl := L.lub oldl out in
      if L.beq oldl newl
      then s
      else {| aval := PCTree.set n newl s.(aval);
              worklist := NS.add n s.(worklist);
              visited := fun p => p = n \/ s.(visited) p |}
  end.


Fixpoint propagate_succ_list (s: state) (out: L.t) (succs: list local_pc)
                             {struct succs} : state :=
  match succs with
  | nil => s
  | n :: rem => propagate_succ_list (propagate_succ s out n) out rem
  end.

Print fetch.


Definition step (s: state) : PCMap.t L.t + state :=
  match NS.pick s.(worklist) with
  | None =>
      inl _ (L.bot, s.(aval))
  | Some(n, rem) =>
      match fetch code n with
      | None =>
          inr _ {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
      | Some instr =>
          inr _ (propagate_succ_list
                  {| aval := s.(aval); worklist := rem; visited := s.(visited) |}
                  (transf code n (abstr_value n s))
                  (successors code n))
      end
  end.



Definition fixpoint_from (start: state) : option (PCMap.t L.t) :=
  PrimIter.iterate _ _ step start.




(**)

Definition start_state (enode: local_pc) (eval: L.t) :=
  {| aval := PCTree.set enode eval (PCTree.empty L.t);
     worklist := NS.add enode NS.empty;
     visited := fun n => n = enode |}.

Definition start_state_nodeset (enodes: NS.t) :=
  {| aval := PCTree.empty L.t; worklist := enodes; visited := fun n => NS.In n enodes |}.


Definition fixpoint_nodeset (enodes: NS.t) :=
  fixpoint_from (start_state_nodeset enodes).

(*
Definition start_state_allnodes :=
  {| aval := PCTree.empty L.t; worklist := NS.all_nodes code; visited := fun n => exists instr, PCTree.get n code = Some instr|}.
*)

Definition fixpoint (enode: local_pc) (eval: L.t) :=
  fixpoint_from (start_state enode eval).
(*
Definition fixpoint_allnodes := fixpoint_from start_state_allnodes.
*)

Inductive optge: option L.t -> option L.t -> Prop :=
| optge_some: forall l l', L.ge l l' -> optge (Some l) (Some l')
| optge_none: forall ol, optge ol None.

Remark optge_refl: forall ol, optge ol ol.
Proof. destruct ol; constructor. apply L.ge_refl; apply L.eq_refl. Qed.

Remark optge_trans: forall ol1 ol2 ol3, optge ol1 ol2 -> optge ol2 ol3 -> optge ol1 ol3.
Proof.
  intros. inv H0. inv H. constructor. eapply L.ge_trans; eauto. constructor. Qed.

Remark optge_abstr_value:
  forall st st' n,
  optge (PCTree.get n (st.(aval)))  (PCTree.get n (st'.(aval))) ->
  L.ge (abstr_value n st) (abstr_value n st').
Proof.
  intros. unfold abstr_value. inv H. auto. apply L.ge_bot.
Qed.

Lemma propagate_succ_charact:
  forall st out n,
  let st' := propagate_succ st out n in
     optge st'.(aval)!n (Some out)
  /\ (forall s, n <> s -> st'.(aval)!s = st.(aval)!s)
  /\ (forall s, optge st'.(aval)!s st.(aval)!s)
  /\ (NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
  /\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
  /\ (forall n', NS.In n' st'.(worklist) -> n' = n \/ NS.In n' st.(worklist))
  /\ (forall n', st.(visited) n' -> st'.(visited) n')
  /\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
  /\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
  Proof.
  unfold propagate_succ; intros; simpl.
  destruct st.(aval)!n as [v|] eqn:E;
  [predSpec L.beq L.beq_correct v (L.lub v out) | idtac].
- (* already there, unchanged *)
  repeat split; intros.
  + rewrite E. constructor. eapply L.ge_trans. apply L.ge_refl. apply H; auto. apply L.ge_lub_right.
  + apply optge_refl.
  + right; auto.
  + auto.
  + auto.
  + auto.
  + auto.
  + congruence.
- (* already there, updated *)
  simpl; repeat split; intros.
  + rewrite PCTree.gss. constructor. apply L.ge_lub_right.
  + rewrite PCTree.gso by auto. auto.
  + rewrite PCTree.gsspec. destruct (PCTree.elt_eq s n).
    subst s. rewrite E. constructor. apply L.ge_lub_left.
    apply optge_refl.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec in H0. intuition.
  + auto.
  + destruct H0; auto. subst n'. rewrite NS.add_spec; auto.
  + rewrite PCTree.gsspec in H1. destruct (PCTree.elt_eq  n' n). auto. congruence.
- (* not previously there, updated *)
  simpl; repeat split; intros.
  + rewrite PCTree.gss. apply optge_refl.
  + rewrite PCTree.gso by auto. auto.
  + rewrite PCTree.gsspec. destruct (PCTree.elt_eq s n).
    subst s. rewrite E. constructor.
    apply optge_refl.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec. auto.
  + rewrite NS.add_spec in H. intuition.
  + auto.
  + destruct H; auto. subst n'. rewrite NS.add_spec. auto.
  + rewrite PCTree.gsspec in H0. destruct (PCTree.elt_eq n' n). auto. congruence.
Qed.


Lemma propagate_succ_list_charact:
  forall out l st,
  let st' := propagate_succ_list st out l in
     (forall n, In n l -> optge st'.(aval)!n (Some out))
  /\ (forall n, ~In n l -> st'.(aval)!n = st.(aval)!n)
  /\ (forall n, optge st'.(aval)!n st.(aval)!n)
  /\ (forall n, NS.In n st'.(worklist) \/ st'.(aval)!n = st.(aval)!n)
  /\ (forall n', NS.In n' st.(worklist) -> NS.In n' st'.(worklist))
  /\ (forall n', NS.In n' st'.(worklist) -> In n' l \/ NS.In n' st.(worklist))
  /\ (forall n', st.(visited) n' -> st'.(visited) n')
  /\ (forall n', st'.(visited) n' -> NS.In n' st'.(worklist) \/ st.(visited) n')
  /\ (forall n', st.(aval)!n' = None -> st'.(aval)!n' <> None -> st'.(visited) n').
Proof.
  induction l; simpl; intros.
- repeat split; intros.
  + contradiction.
  + apply optge_refl.
  + auto.
  + auto.
  + auto.
  + auto.
  + auto.
  + congruence.
- generalize (propagate_succ_charact st out a).
  set (st1 := propagate_succ st out a).
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  generalize (IHl st1).
  set (st2 := propagate_succ_list st1 out l).
  intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). clear IHl.
  repeat split; intros.
  + destruct H.
    * subst n. eapply optge_trans; eauto.
    * auto.
  + rewrite B2 by tauto. apply A2; tauto.
  + eapply optge_trans; eauto.
  + destruct (B4 n). auto.
    destruct (PCTree.elt_eq n a).
    * subst n. destruct A4. left; auto. right; congruence.
    * right. rewrite H. auto.
  + eauto.
  + exploit B6; eauto. intros [P|P]. auto.
    exploit A6; eauto. intuition.
  + eauto.
  + specialize (B8 n'); specialize (A8 n'). intuition.
  + destruct st1.(aval)!n' eqn:ST1.
    apply B7. apply A9; auto. congruence.
    apply B9; auto.
Qed.


Inductive steps: state -> state -> Prop :=
  | steps_base: forall s, steps s s
  | steps_right: forall s1 s2 s3, steps s1 s2 -> step s2 = inr s3 -> steps s1 s3.

Scheme steps_ind := Induction for steps Sort Prop.

Lemma fixpoint_from_charact:
  forall start res,
  fixpoint_from start = Some res ->
  exists st, steps start st /\ NS.pick st.(worklist) = None /\ res = (L.bot, st.(aval)).
Proof.
  unfold fixpoint; intros.
  eapply (PrimIter.iterate_prop _ _ step
              (fun st => steps start st)
              (fun res => exists st, steps start st /\ NS.pick (worklist st) = None /\ res = (L.bot, aval st))); eauto.
  intros. destruct (step a) eqn:E.
  exists a; split; auto.
  unfold step in E. destruct (NS.pick (worklist a)) as [[n rem]|].
  destruct (fetch code n); discriminate.
  inv E. auto.
  eapply steps_right; eauto.
  constructor.
Qed.

Lemma step_incr:
  forall n s1 s2, step s1 = inr s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof.
    unfold step; intros.
  destruct (NS.pick (worklist s1)) as [[p rem] | ]; try discriminate.
  destruct (fetch code p) as [instr|]; inv H.
  + generalize (propagate_succ_list_charact
                     (transf code p (abstr_value p s1))
                     (successors code p)
                     {| aval := aval s1; worklist := rem; visited := visited s1 |}).
      simpl.
      set (s' := propagate_succ_list {| aval := aval s1; worklist := rem; visited := visited s1 |}
                    (transf code p (abstr_value p s1)) (successors code p)).
      intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
      auto.
  + split. apply optge_refl. auto.
Qed.


Lemma steps_incr:
  forall n s1 s2, steps s1 s2 ->
  optge s2.(aval)!n s1.(aval)!n /\ (s1.(visited) n -> s2.(visited) n).
Proof.
  induction 1.
- split. apply optge_refl. auto.
- destruct IHsteps. exploit (step_incr n); eauto. intros [P Q].
  split. eapply optge_trans; eauto. eauto.
Qed.


Record good_state (st: state) : Prop := {
  gs_stable: forall n,
    st.(visited) n ->
    NS.In n st.(worklist) \/
    (forall i s,
     (fetch code n) = Some i -> In s (successors code n) ->
     optge st.(aval)!s (Some (transf code n (abstr_value n st))));
  gs_defined: forall n v,
    st.(aval)!n = Some v -> st.(visited) n
}.



Lemma step_state_good:
  forall st pc rem instr,
  NS.pick st.(worklist) = Some (pc, rem) ->
  (fetch code pc) = Some instr ->
  good_state st ->
  good_state (propagate_succ_list (mkstate st.(aval) rem st.(visited))
                                  (transf code pc (abstr_value pc st))
                                  (successors code pc)).
Proof.
  intros until instr; intros PICK CODEAT [GOOD1 GOOD2].
  generalize (NS.pick_some _ _ _ PICK); intro PICK2.
  set (out := transf code pc (abstr_value pc st)).
  generalize (propagate_succ_list_charact out (successors code pc) {| aval := aval st; worklist := rem; visited := visited st |}).
  set (st' := propagate_succ_list {| aval := aval st; worklist := rem; visited := visited st |} out
                                  (successors code pc)).
  simpl; intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  constructor; intros.
- (* stable *)
  destruct (A8 n H); auto. destruct (A4 n); auto.
  replace (abstr_value n st') with (abstr_value n st)
  by (unfold abstr_value; rewrite H1; auto).
  exploit GOOD1; eauto. intros [P|P].
+ (* n was on the worklist *)
  rewrite PICK2 in P; destruct P.
  * (* node n is our node pc *)
    subst n. fold out. right; intros.
    assert (i = instr) by congruence. subst i.
    apply A1; auto.
  * (* n was already on the worklist *)
    left. apply A5; auto.
+ (* n was stable before, still is *)
  right; intros. apply optge_trans with st.(aval)!s; eauto.
- (* defined *)
  destruct st.(aval)!n as [v'|] eqn:ST.
  + apply A7. eapply GOOD2; eauto.
  + apply A9; auto. congruence.
Qed.

Lemma step_state_good_2:
  forall st pc rem,
  good_state st ->
  NS.pick (worklist st) = Some (pc, rem) ->
  (fetch code pc) = None ->
  good_state (mkstate st.(aval) rem st.(visited)).
Proof.
  intros until rem; intros [GOOD1 GOOD2] PICK CODE.
  generalize (NS.pick_some _ _ _ PICK); intro PICK2.
  constructor; simpl; intros.
- (* stable *)
  exploit GOOD1; eauto. intros [P | P].
  + rewrite PICK2 in P. destruct P; auto.
    subst n. right; intros. congruence.
  + right; exact P.
- (* defined *)
  eapply GOOD2; eauto.
Qed.


Lemma steps_state_good:
  forall st1 st2, steps st1 st2 -> good_state st1 -> good_state st2.
Proof.
  induction 1; intros.
- auto.
- unfold step in e.
  destruct (NS.pick (worklist s2)) as [[n rem] | ] eqn:PICK; try discriminate.
  destruct (fetch code n) as [instr|] eqn:CODE; inv e.
  eapply step_state_good; eauto.
  eapply step_state_good_2; eauto.
Qed.

Lemma start_state_good:
  forall enode eval, good_state (start_state enode eval).
Proof.
  intros. unfold start_state; constructor; simpl; intros.
- subst n. rewrite NS.add_spec; auto. destruct ( PCTree.elt_eq enode n); subst. auto. inversion H.
Qed.



Lemma start_state_nodeset_good:
  forall enodes, good_state (start_state_nodeset enodes).
Proof.
  intros. unfold start_state_nodeset; constructor; simpl; intros.
- left. auto.
- inversion H.
Qed.
(*
Lemma start_state_allnodes_good:
  good_state start_state_allnodes.
Proof.
  unfold start_state_allnodes; constructor; simpl; intros.
- destruct H as [instr CODE]. left. eapply NS.all_nodes_spec; eauto.
- inversion H.
Qed.*)
Print reachable.

Lemma reachable_visited:
  forall st, good_state st -> NS.pick st.(worklist) = None ->
  forall p q, reachable fetch code successors p q -> st.(visited) p -> st.(visited) q.
Proof.
  
  intros st [GOOD1 GOOD2]  PICK. induction 1; intros.
- auto.
- eapply IHreachable; eauto.
  exploit GOOD1; eauto. intros [P | P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. 
  intros OGE; inv OGE; eapply GOOD2; eauto.
Qed.

Theorem fixpoint_solution:
  forall ep ev res n instr s,
  fixpoint ep ev = Some res ->
  fetch code n = Some instr ->
  In s (successors code n) ->
  (forall n, L.eq (transf code n L.bot) L.bot) ->
  L.ge res!!s (transf code n res!!n).
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_good. intros [GOOD1 GOOD2].
  rewrite RES; unfold PCMap.get; simpl.
  destruct st.(aval)!n as [v|] eqn:STN.
- destruct (GOOD1 n) as [P|P]; eauto.
  eelim NS.pick_none; eauto.
  exploit P; eauto. unfold abstr_value; rewrite STN. intros OGE; inv OGE. auto.
- apply L.ge_trans with L.bot. apply L.ge_bot. apply L.ge_refl. apply L.eq_sym. eauto.
Qed.


Theorem fixpoint_entry:
  forall ep ev res,
  fixpoint ep ev = Some res ->
  L.ge res!!ep ev.
Proof.
  unfold fixpoint; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit (steps_incr ep); eauto. simpl. destruct (PCTree.elt_eq ep ep). intros [P Q].
  rewrite RES; unfold PCMap.get; simpl. inv P; auto. contradiction n; eauto.
Qed.

(*
Theorem fixpoint_allnodes_solution:
  forall res n instr s,
  fixpoint_allnodes = Some res ->
  code!n = Some instr ->
  In s (successors instr) ->
  L.ge res!!s (transf n res!!n).
Proof.
  unfold fixpoint_allnodes; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_allnodes_good. intros [GOOD1 GOOD2].
  exploit (steps_incr n); eauto. simpl. intros [U V].
  exploit (GOOD1 n). apply V. exists instr; auto. intros [P|P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE. rewrite RES; unfold PCMap.get; simpl.
  inv OGE. assumption.
Qed.
*)

Print reachable.
Theorem fixpoint_nodeset_solution:
  forall enodes res e n instr s,
  fixpoint_nodeset enodes = Some res ->
  NS.In e enodes ->
  reachable fetch code successors e n ->
  fetch code n = Some instr ->
  In s (successors code n) ->
  L.ge res!!s (transf code n res!!n).
Proof.
  unfold fixpoint_nodeset; intros.
  exploit fixpoint_from_charact; eauto. intros (st & STEPS & PICK & RES).
  exploit steps_state_good; eauto. apply start_state_nodeset_good. intros GOOD.
  exploit (steps_incr e); eauto. simpl. intros [U V].
  assert (st.(visited) n).
  { eapply reachable_visited; eauto. }
  destruct GOOD as [GOOD1 GOOD2].
  exploit (GOOD1 n); eauto. intros [P|P].
  eelim NS.pick_none; eauto.
  exploit P; eauto. intros OGE. rewrite RES; unfold PCMap.get; simpl.
  inv OGE. assumption.
Qed.

Theorem fixpoint_invariant:
  forall ep ev
    (P: L.t -> Prop)
    (P_bot: P L.bot)
    (P_lub: forall x y, P x -> P y -> P (L.lub x y))
    (P_transf: forall pc instr x, fetch code pc = Some instr -> P x -> P (transf code pc x))
    (P_entrypoint: P ev)
    res pc,
  fixpoint ep ev = Some res ->
  P res!!pc.
Proof.
  intros.
  set (inv := fun st => forall x, P (abstr_value x st)).
  assert (inv (start_state ep ev)).
  {
    red; simpl; intros. unfold abstr_value, start_state; simpl. destruct (PCTree.elt_eq ep x); subst; eauto.
  }
  assert (forall st v n, inv st -> P v -> inv (propagate_succ st v n)).
  {
    unfold inv, propagate_succ. intros.
    destruct (aval st)!n as [oldl|] eqn:E.
    destruct (L.beq oldl (L.lub oldl v)).
    auto.
    unfold abstr_value. simpl. rewrite PCTree.gsspec. destruct (PCTree.elt_eq x n).
    apply P_lub; auto. replace oldl with (abstr_value n st). auto.
    unfold abstr_value; rewrite E; auto.
    apply H1.
    unfold abstr_value. simpl. rewrite PCTree.gsspec. destruct (PCTree.elt_eq x n).
    auto.
    apply H1.
  }
  assert (forall l st v, inv st -> P v -> inv (propagate_succ_list st v l)).
  {
    induction l; intros; simpl. auto.
    apply IHl; auto.
  }
  assert (forall st1 st2, steps st1 st2 -> inv st1 -> inv st2).
  {
    induction 1; intros.
    auto.
    unfold step in e. destruct (NS.pick (worklist s2)) as [[n rem]|]; try discriminate.
    destruct (fetch code n) as [instr|] eqn:INSTR; inv e.
    apply H2. apply IHsteps; auto. eapply P_transf; eauto. apply IHsteps; auto.
    apply IHsteps; auto.
  }
  unfold fixpoint in H. exploit fixpoint_from_charact; eauto.
  intros (st & STEPS & PICK & RES).
  replace (res!!pc) with (abstr_value pc st). eapply H3; eauto.
  rewrite RES; auto.
Qed.

End Kildall.

End Dataflow_Solver.


Require Import Vellvm.CFG.
Print mcfg.