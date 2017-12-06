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



Print mcfg.





Print cfg.
Print block.
Print block_id.
Print raw_id.

Print int.


Lemma test : forall n, n + 1 = n + 2.
Proof. Admitted.




Hint Resolve test.


Lemma test1 : forall n, n + 1 = n + 2.
Proof. auto. Admitted.


Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.




Lemma trace_equiv_err : forall s0 s1 r, trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
  (Vis (trace_map (fun _ : state => ()) <$> Err s0))
  (Vis (trace_map (fun _ : state => ()) <$> Err s1)).
Proof. intros. constructor. constructor. Qed.

Hint Resolve trace_equiv_err.



Lemma trace_equiv_fin : forall s0 r, trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
  (Vis (trace_map (fun _ : state => ()) <$> Fin s0))
  (Vis (trace_map (fun _ : state => ()) <$> Fin s0)).
Proof. intros. constructor. constructor. auto. Qed.

Hint Resolve trace_equiv_fin.


Lemma trace_equiv_tau_left : forall (d1 d2:Trace ()), trace_equiv d1 d2 -> trace_equiv (Tau () d1) d2.
Proof. intros. pfold. constructor. punfold H. Qed.

Hint Resolve trace_equiv_tau_left.

Lemma trace_equiv_tau_right : forall (d1 d2:Trace ()), trace_equiv d1 d2 -> trace_equiv d1 (Tau () d2).
Proof. intros. pfold. constructor. punfold H. Qed.

Hint Resolve trace_equiv_tau_right.



Lemma trace_equiv_tau : forall (r:Trace () -> Trace () -> Prop) (A B: Trace ()) (CIH: r (A) (B)) ,
trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)   (Tau ()
     (A))
  (Tau ()
     (B)).
Proof. intros.
constructor. right. apply CIH. Qed. 



Hint Resolve trace_equiv_tau.


Lemma trace_refl1 : forall (a:Trace ())
, trace_equiv a a.
Proof. pcofix CIH. intros. pfold. destruct a. destruct v. simpl. constructor. constructor. auto.
constructor. constructor. constructor. constructor.
destruct e. simpl.
  +constructor. right. subst. apply CIH.
  +constructor. auto. right. subst. eauto.
  +constructor. auto. auto. right. eauto.
  +constructor. auto. auto. right. subst. apply CIH.
constructor. right. apply CIH. Qed.


Hint Resolve trace_refl1.



Lemma trace_refl2 : forall (r:Trace () -> Trace () -> Prop) (CIH: forall (b c: Trace()), r b c) (a:Trace ()),
trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r) a a.
Proof.
 intros.
 destruct a. destruct v.
  +constructor. constructor. auto.
  +constructor. constructor.
  +constructor. destruct e.
    -constructor. constructor. right; subst. apply CIH.
    -constructor. constructor. auto. right; subst. apply CIH.
    -constructor. constructor. auto. auto. right. apply CIH.
    -constructor. constructor. auto. auto. right. subst. apply CIH.
  +constructor. right. apply CIH.
Qed.






Hint Resolve trace_refl2.

Print Step.
Print state.


Definition generic_start D prog mem e s fn bk iid :=
  match
    match
      match
        match D with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := iid |}, e, s)
              (step_sem prog s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := iid |}, e, s)
              (step_sem prog s')
        | Obs (Fin s0) => Vis (Fin s0)
        | Obs (Err s0) => Vis (Err s0)
        | Obs (Eff m) => Vis (Eff (effects_map (step_sem prog) m))
        end
      with
      | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
      | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
      end
    with
    | Vis (Fin _ as x) => Vis x
    | Vis (Err _ as x) => Vis x
    | Vis (Eff e0) =>
        match mem_step e0 mem with
        | inl e1 => Vis (Eff e1)
        | inr (m', v, k) => Tau () (memD m' (k v))
        end
    | Tau x d' => Tau x (memD mem d')
    end
  with
  | Vis a => Vis a
  | Tau a b => Tau a b
  end
.


Definition generic_step prog mem C p e s fn bk (id:local_id) :=
generic_start (do dv <- C; Step (p, add_env id dv e, s)) prog mem e s fn bk (IId id)
.

Definition generic_function_entry_error f s0 prog mem e s fn bk id :=
generic_start (let 'FunctionEntry _ _ := f in Obs (Err s0)) prog mem e s fn bk id.
(*          (do st <- jump prog (fn p) (bk p) br e s;
           Jump st)*)
Print pc.





Lemma generic_step_refl : forall  (r: Trace () -> Trace () -> Prop) (CIH: forall (st : state) (prog : mcfg)
        (mem : memory),
      r (memD mem (sem prog st))
        (memD mem (sem prog st)))
C prog mem s id e p fn bk, trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r) 
(generic_step prog mem C p e s fn bk id) (generic_step prog mem C p e s fn bk id).
Proof. intros. unfold generic_step, generic_start.
destruct C; simpl; eauto. Qed.


Hint Resolve generic_step_refl.




Lemma generic_function_entry_refl : forall  (r: Trace () -> Trace () -> Prop) (CIH: forall (st : state) (prog : mcfg)
        (mem : memory),
      r (memD mem (sem prog st))
        (memD mem (sem prog st)))
prog mem s0 f s id e fn bk, trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r) 
(generic_function_entry_error f s0 prog mem e s fn bk id) (generic_function_entry_error f s0 prog mem e s fn bk id).
Proof. intros. unfold generic_function_entry_error, generic_start.
destruct f; simpl; eauto. Qed.


Hint Resolve generic_function_entry_refl.
Print pc.

(*
        match
          match f with
          | KRet _ _ _ =>
              t_raise_p p
                "IMPOSSIBLE: Ret void in non-return configuration"
          | KRet_void e' p' => Jump (p', e', s)
          end
        with
        | Step s' => Tau (p, e, f :: s) (step_sem prog s')
        | Jump s' => Tau (p, e, f :: s) (step_sem prog s')
        | Obs (Fin s0) => Vis (Fin s0)
        | Obs (Err s0) => Vis (Err s0)
        | Obs (Eff m) => Vis (Eff (effects_map (step_sem prog) m))
        end*)

Definition jump_solve prog mem e s p br2:=
  match
    match
      match
        match (do st <- jump prog (fn p) (bk p) br2 e s; Jump st) with
        | Step s' => Tau (p, e, s) (step_sem prog s')
        | Jump s' => Tau (p, e, s) (step_sem prog s')
        | Obs (Fin s0) => Vis (Fin s0)
        | Obs (Err s0) => Vis (Err s0)
        | Obs (Eff m) => Vis (Eff (effects_map (step_sem prog) m))
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
        | inl e1 => Vis (Eff e1)
        | inr (m', v0, k) => Tau () (memD m' (k v0))
        end
    | Tau x0 d' => Tau x0 (memD mem d')
    end
  with
  | Vis a => Vis a
  | Tau a b => Tau a b
  end
.



Lemma generic_jump_refl : forall  (r: Trace () -> Trace () -> Prop) (CIH: forall (st : state) (prog : mcfg)
        (mem : memory),
      r (memD mem (sem prog st))
        (memD mem (sem prog st)))
prog mem s e p br2, trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r) 
(jump_solve prog mem e s p br2) (jump_solve prog mem e s p br2).
Proof. intros. unfold jump_solve. destruct (jump prog (fn p) (bk p) br2 e s); simpl; eauto. Qed. 

Hint Resolve generic_jump_refl.

Lemma trace_refl123 : forall st prog mem, trace_equiv (memD mem (sem (prog) st)) (memD mem (sem (prog) st)).
Proof. pcofix CIH. intros. pfold.
assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))). destruct (memD mem (sem prog st)); eauto.
rewrite H. simpl.
unfold stepD. simpl. destruct st; simpl; eauto. destruct p; simpl; eauto.
destruct (fetch prog p); simpl; eauto. destruct c; simpl; eauto. destruct (incr_pc prog p); simpl; eauto.
destruct p; simpl; eauto. destruct pt; simpl; eauto. destruct i; simpl; eauto.
destruct (eval_op e None op); simpl; eauto.
destruct (fn0); simpl; eauto. destruct i; simpl; eauto.

destruct ((find_function_entry prog id0)); simpl; eauto.
destruct (           map_monad (fun '(t0, op) => eval_op e (Some t0) op)); simpl; eauto.
eapply generic_function_entry_refl; eauto.
destruct ((find_function_entry prog id0)); simpl; eauto.
destruct f; simpl; eauto.
destruct f; simpl; eauto.
destruct ptr; simpl; eauto.
destruct (eval_op e (Some t0) v); simpl; eauto.
destruct v0; simpl; eauto.
destruct i; simpl; eauto. destruct fn0; simpl; eauto.
destruct i; simpl; eauto. 
destruct ((find_function_entry prog id)); simpl; eauto.
destruct f; simpl; eauto.
destruct (map_monad (fun '(t0, op) => eval_op e (Some t0) op) args); simpl; eauto.
destruct t; simpl; eauto.
destruct val, ptr; simpl; eauto.

destruct (eval_op e (Some t) v); simpl; eauto.
destruct (eval_op e (Some t0) v0); simpl; eauto.
destruct v2; simpl; eauto.
destruct t; simpl; eauto.
destruct v; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct s; simpl; eauto.
destruct f; simpl; eauto.
destruct s; simpl; eauto.
destruct f; simpl; eauto.
destruct v; simpl; eauto.
destruct (eval_op e (Some t) v); simpl; eauto.
destruct v0; simpl; eauto.
 destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl; eauto;
eapply generic_jump_refl; eauto.
Admitted.
