Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.EqNat.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.


Print value.
Print env.

Definition areg : Set := (local_id * value).
Definition aenv : Set := seq areg.

Print block.
Print code.
Print cmd.
Definition map_exp_to_cmd (e:instr_id * instr) : (instr_id * cmd) := (fst e, CFG.Step (snd e)).
Definition map_term_to_cmd (t: (instr_id*terminator)) : list (instr_id * cmd) := cons (fst t, Term (snd t)) nil.
Definition prep_block (b:block) := map map_exp_to_cmd (blk_code b) ++ map_term_to_cmd (blk_term b).


Definition aenv_fallthrough (l:aenv) :=
  match l with
  | nil => None
  | hd::tl => Some (fst hd)
  end.


Fixpoint list_to_tuple (l: aenv) (t:local_id)  :=
  match l with
  | nil => None
  | hd :: tl => if (decide ((fst hd) = t)) then Some (snd hd, aenv_fallthrough tl) else list_to_tuple tl t
  end.


Definition find_tuple (l:aenv) (i:local_id) :=
  match list_to_tuple l i with
  | Some (t, _) => Some t
  | _ => None
  end.

Definition increase_tuple (l:aenv) (i:local_id) :=
  match list_to_tuple l i with
  | Some (_, Some a) => Some a
  | _ => None
  end.


Fixpoint get_from_aenv (l:aenv)  (i:local_id) :=
  match l with
  | nil => None
  | (iis, ins) :: tl => if decide (iis = i) then Some (ins) else get_from_aenv tl i
  end.
Print prep_block.

Print cmd. Print SV.
Print Expr.


(*Fixpoint eval_op (e:env) (top:option typ) (o:Ollvm_ast.value) *)

Print aenv. Print areg.
Print eval_op. Print err. Print instr_id.
Definition transfer (a:aenv) (i:instr_id * cmd) : aenv :=
  match (fst i), (snd i) with
  | (IId loc), CFG.Step ins => match ins with
                    | INSTR_Op val => match val with
                                      | SV s_value => match s_value with
                                                      | VALUE_Integer n => match eval_op a None (SV (VALUE_Integer n)) with
                                                                           | inl _ => a
                                                                           | inr val => (loc, val) :: a
                                                                           end
                                                      | _ => a
                                                        end
                                      end
                    | _ => a
                             
                    end
                      
  | _, _ => a
  end.



Fixpoint value_analysis_fix (acc:aenv) l (i:instr_id)  :=
  match l with
  | nil => nil
  | hd :: tl => if decide ((fst hd)= i) then acc else (value_analysis_fix (transfer acc hd) tl i)
  end.



Definition value_analysis l (i:instr_id) := value_analysis_fix nil l i.


Print mcfg.

Print find_function.
Print definition.

Print find_block.
Print cfg.


Definition prep_selected_block (m:mcfg) (p:pc) :=
  match find_function m (fn p) with
  | None => None
  | Some func => match find_block (blks (df_instrs func)) (bk p) with
                 | None => None
                 | Some a => Some (prep_block a)
                 end
                   
  end. Print pc.

Definition value_analysis_specific (m:mcfg) (p:pc) :=
  match prep_selected_block m p with
  | None => None
  | Some a => Some (value_analysis a (pt p))
  end.

Print value_analysis_specific.



Lemma find_tuple_implies : forall l i i1,  NoDup (map fst l) -> find_tuple l i = Some i1 ->
                            exists head tl, l = head ++ (cons (i, i1) nil) ++ tl.
Proof. intros. unfold find_tuple in *. induction l. simpl in *. inversion H0. simpl in *. destruct a. simpl in *.

       unfold is_left in *. simpl in *. destruct (decide (l0 = i)). inversion H0. subst. exists nil. eauto.
       inversion H; subst. apply IHl in H4; eauto. inversion H4. inversion H1. subst. eauto.
       exists ( (l0, v) :: x). exists x0. auto. Qed.



Lemma incr_pc_implies : forall l i i1 t,  NoDup (map fst  l) -> list_to_tuple l i = Some (i1, Some t) ->
                            exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof.
  intros. unfold increase_tuple in *. simpl in *. simpl in *. induction l. simpl in *. inversion H0.
  simpl in *. simpl in *. destruct a. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (l0 = i)). subst. simpl in *. inversion H0. subst. destruct l. simpl in *. inversion H3. simpl in *. inversion H3. destruct p. simpl in *. inversion H2. subst. exists nil. simpl in *. exists l. exists v. eauto.  


inversion H; subst. apply IHl in H4; eauto. inversion H4; subst. inversion H1. subst. inversion H2. subst. exists ((l0, v) :: x). simpl in *. exists x0. exists x1. eauto. Qed.


Definition newlist := list (instr_id * cmd).
Definition opt_fallthrough (n:newlist) : option instr_id :=
  match n with
  | nil => None
  | hd :: _ => Some (fst hd)
  end.

  Fixpoint find_in_newlist(n:newlist)  (i:instr_id) :=
  match n with
  | nil => None
  | hd :: tl => if decide ((fst hd) = i) then Some (snd hd, opt_fallthrough tl) else find_in_newlist tl i
  end.

  Lemma incr_pc_implies2 : forall prog i i1 t,  NoDup (map fst (prep_block prog)) ->  block_to_cmd prog i =  Some (i1, Some t) ->  find_in_newlist (prep_block prog) i = Some (i1, Some t).
  Proof. intros. unfold block_to_cmd in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *.
         destruct blk_term. simpl in *. destruct (decide (i0 = i)); subst. inversion H0. simpl in *. induction blk_code; simpl in *. inversion H0. unfold is_left in *. destruct a. simpl in *.
destruct ( decide (i2 = i)). subst. simpl in *. destruct ( decide (i = i)). subst. unfold opt_fallthrough. simpl in *. destruct blk_code. simpl in *. eauto. simpl in *. destruct p. simpl in *. eauto. contradiction n0; eauto. simpl in *. unfold prep_block in *. simpl in *. apply IHblk_code. inversion H. subst. eauto. destruct (decide (i = i2)); subst. contradiction n0; auto. auto. Qed.




  Lemma map_prog : forall prog_code0, ((map fst (map map_exp_to_cmd prog_code0)) = (map fst prog_code0)).
Proof. induction prog_code0; simpl in *; eauto. inversion IHprog_code0. simpl in *. eauto. Qed.



Lemma prog_id_eq : forall prog, (map fst (blk_code prog)) ++ (cons (blk_term_id prog ) nil) =  (map fst (prep_block prog)).
Proof. intros. simpl in *. unfold prep_block. simpl in *. unfold map_term_to_cmd in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct prog. simpl in *. induction blk_code. simpl in *. eauto.
       simpl in *. destruct a. simpl in *. rewrite IHblk_code. eauto. Qed.
       



Lemma get_prog_id : forall prog, NoDup ((map fst (blk_code prog)) ++  (blk_term_id prog ) :: nil) ->
                                 NoDup (map fst (prep_block prog)).
Proof. intros. rewrite <- prog_id_eq. eauto. Qed.




Lemma incr_pc_implies1 : forall l i i1 t,  NoDup (map fst l) ->
                                           find_in_newlist l i = Some (i1, Some t) ->
                                          exists head tl r,  l = head ++ (cons (i, i1) (cons (t, r) nil)) ++ tl.
Proof.  simpl in *. intros. induction l; simpl in *.
       +inversion H0.
       +simpl in *. destruct a. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (i0 = i)). subst. simpl in *. inversion H0. subst.
        *exists nil. simpl in *. destruct l. simpl in *. inversion H3. simpl in *. exists l. simpl in *. destruct p. simpl in *. inversion H3. subst. exists c. eauto.
        *inversion H. subst. apply IHl in H4; eauto. inversion H4. inversion H1. subst. inversion H2. subst. simpl in *. exists ((i0, c) :: x). simpl in *. exists x0. exists x1. eauto. Qed.








Lemma testtest : forall l hd i i1 t r tl a,  NoDup (map fst l) -> l = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl ->   value_analysis_fix a l t =
  transfer (value_analysis_fix a l i) (i, i1).
Proof. intros. simpl in *. generalize a. simpl in *. rewrite H0. rewrite H0 in H. clear H0. induction hd. simpl in *.

unfold is_left.
destruct ( decide (i = t)). subst.
inversion H. subst. contradiction H2.  simpl; eauto.


simpl in *.
destruct ( decide (t = t)). simpl in *. destruct ( decide (i = i)). eauto. contradiction  n0; eauto. contradiction n0; eauto.


simpl in *. unfold is_left in *. simpl in *. destruct a0. simpl in *. destruct ( decide (i0 = t)). subst.

simpl in *. inversion H; subst. clear IHhd. clear H.  clear H3.


assert ( In t [seq fst i | i <- hd ++ [:: (i, i1), (t, r) & tl]]).  induction hd. simpl in *. right. left. auto.
simpl in *. right. apply IHhd. unfold not. intros. unfold not in H2. apply H2. right.  auto.
apply H2 in H. inversion H. destruct (decide (i0 = i)). subst. inversion H. subst.
clear IHhd. clear H. clear H3. assert ( In i [seq fst i | i <- hd ++ [:: (i, i1), (t, r) & tl]]).
induction hd. simpl in *. left. auto. simpl in *. right. apply IHhd. unfold not in *. intros. apply H2. right. auto. apply H2 in H. inversion H.
intros. remember ( (transfer a0 (i0, c))).
 apply IHhd. inversion H; subst; eauto. Qed.






 Lemma testtest1 : forall prog hd i i1 t r tl, NoDup (map fst  (prep_block prog)) ->  (prep_block prog) = hd ++ (cons (i, i1) (cons (t, r) nil)) ++ tl  -> value_analysis  (prep_block prog) t = transfer (value_analysis  (prep_block prog) i) (i, i1).
 Proof.  intros. unfold value_analysis. simpl in *. eapply testtest in H; simpl in *; eauto. Qed.


  Lemma testtest2 : forall prog i i1 t, NoDup ((map fst (blk_code prog)) ++ ( blk_term_id prog ) :: nil) -> block_to_cmd prog i =  Some (i1, Some t)  ->  value_analysis  (prep_block prog) t = transfer (value_analysis  (prep_block prog) i) (i, i1).
  Proof. intros. assert (H' := H). eapply get_prog_id in H.   assert (H'' := H).   assert (H''' := H). 
        eapply  incr_pc_implies2 in H; eauto. eapply incr_pc_implies1 in H''; eauto.
inversion H''. inversion H1. inversion H2. subst. eapply testtest in H'''; eauto. Qed.

  Lemma test5 : forall prog i i1 t head,  NoDup ((map fst (blk_code prog)) ++ (blk_term_id prog :: nil)) ->
                                        block_to_cmd prog i = Some (t, Some i1) ->
                                        value_analysis (prep_block prog) i = head  ->
                                        value_analysis (prep_block prog) (i1) = transfer head (i, t).
Proof. intros. eapply testtest2 in H; eauto. rewrite <- H1; eauto. Qed.



Print lookup_env.





  Definition Subset s s' := forall a, exists b, lookup_env s a = Some b -> lookup_env s' a = Some b.
  Print value_analysis. (*AREG*) Print areg. Print value_analysis. 
  (*instr_id * cmd instr_id seq areg*)
  Print prep_selected_block.
Definition sound_env (m:mcfg) (p:pc) (e:env) :=
  forall prep, prep_selected_block m p = Some prep ->
               Subset (value_analysis prep (pt p)) e.


    Inductive sound_stack : mcfg -> stack -> Prop :=
    | nil_stack : forall p,  sound_stack p nil
    | kret_stack : forall id m p e k (sstack_env: sound_env m p e) (stk:sound_stack m k), sound_stack m ((KRet e id p)::k)
    | kret_void_stack : forall m p e k (sstack_env: sound_env m p e) (stk:sound_stack m k), sound_stack m ((KRet_void e p)::k).


    Print state.
    Print pc_of.
    
 Inductive sound_state : mcfg -> state -> Prop :=
   sound_state_intro : forall (st : state) (m : mcfg) (sstack: sound_stack m (stack_of st)) (senv: sound_env m (pc_of st) (env_of st)), sound_state m st.




Lemma sound_state_1 : 
  forall a e0, exists b0 : value, lookup_env [::] a = Some b0 -> lookup_env e0 a = Some b0.
Proof. intros. exists ( DVALUE_Poison). intros. inversion H. Qed.
Hint Resolve sound_state_1.




Lemma sound_state_2 : forall b id e v op (H2 : Subset
         (value_analysis (prep_block b) (IId id))
         e),
  Subset
    (transfer
       (value_analysis (prep_block b) (IId id))
       (IId id, CFG.Step (INSTR_Op op)))
    (add_env id v e).
Proof. intros. unfold transfer; destruct op; simpl in *. destruct e0; simpl in *; eauto; unfold Subset in *; unfold lookup_env in *; simpl in *; intros; try destruct ( AstLib.RawID.eq_dec a id); eauto. Qed.
Hint Resolve sound_state_2.



        Print value. Print dvalue.
 Lemma nil_subset_true : forall e1,  Subset nil e1.
 Proof. intros. unfold Subset. simpl in *. intros. unfold lookup_env in *. simpl in *. exists ( DVALUE_Poison).  intros.  inversion H. Qed.
 Hint Resolve nil_subset_true.

 
Print stepD. Print transition.
 Lemma step_preserves_sound_stack : forall m st st1, 
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state m st  -> stepD m st = Step st1 -> sound_stack m (stack_of st1).
   Proof. intros. inversion H0; subst. destruct st. destruct p. destruct p. simpl in *.
          remember ( find_function m fn). destruct o; simpl in *. remember (find_block (blks (df_instrs d)) bk). destruct o. remember ( block_to_cmd b pt). destruct o. destruct p. simpl in *.
          destruct c; simpl in *.  destruct o; simpl in *.
          +destruct pt, i; inversion H1.
           *destruct ( eval_op e None op); simpl in *; inversion H1; subst. simpl in *; eauto.
           *(*9*) destruct fn0, i. destruct (find_function_entry m id0); simpl in *. destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *. inversion H1. inversion H1; subst. simpl in *. constructor. simpl in *. eauto. unfold sound_env. simpl in *. eapply test5 in H; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo in senv. rewrite <- Heqo0. rewrite <- Heqo0 in senv. intros. inversion H2. subst. apply senv in H2.  rewrite H. unfold transfer. auto. eauto. inversion H1. inversion H1.
           *destruct ptr. destruct (eval_op e (Some t0) v); simpl in *. inversion H1. destruct v0; inversion H1.
           *destruct fn0. destruct i; inversion H1. destruct (find_function_entry m id); simpl in  *. destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1. destruct t; inversion H1. inversion H1; subst. simpl. constructor. clear H3; clear H7; clear H1. clear H4; clear H5. eapply test5 in H; eauto. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo. rewrite <- Heqo0.
             rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. intros. inversion H1. subst. apply senv in H1. rewrite H. unfold transfer. simpl in *. auto. eauto. inversion H1.
           *destruct val, ptr. destruct ( eval_op e (Some t) v), ( eval_op e (Some t0) v0); simpl in *. inversion H1. inversion H1. inversion H1. destruct v2; inversion H1.
           *inversion H1.
           *destruct t; inversion H1.
          +destruct v. destruct (eval_op e (Some t) v); simpl in *. inversion H1. destruct s; simpl in *. inversion H1. destruct f. inversion H1. inversion H1.
          +destruct s. inversion H1. destruct f. inversion H1. inversion H1.
          +destruct v. destruct (eval_op e (Some t) v); simpl in *. inversion H1. destruct v0; simpl in *. inversion H1. inversion H1. inversion H1. simpl in *. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *. destruct ( jump m fn bk br1 e s); simpl in *. inversion H1. inversion H1. destruct (jump m fn bk br2 e s); simpl in *. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. destruct ( jump m fn bk br e s); simpl in *; inversion H1.
          +simpl in *. inversion H1.
          +simpl in *. inversion H1. inversion H1.
   Qed.

Print sound_env.

Lemma find_block_equiv : forall b0 d0 t, Some b0 = find_block (blks (df_instrs d0)) t -> blk_id b0 = t. Proof.

                                                                                                          intros. destruct d0. simpl in *. destruct df_instrs. simpl in *. induction blks. simpl in *. inversion H. simpl in *. destruct a. simpl in *. destruct ( decide (blk_id = t)). subst. inversion H. subst. simpl in *. auto. apply IHblks. clear IHblks. induction blks. simpl in *. auto. simpl in *. destruct a. simpl in *. destruct ( decide (blk_id0 = t)). subst. inversion H. subst. auto. eauto. Qed.



Lemma value_analysis_at_entry_is_nil : forall b4,

  (value_analysis_fix nil
       (map map_exp_to_cmd (blk_code b4) ++
            map_term_to_cmd (blk_term b4)) (blk_entry_id b4)) = nil.
Proof. intros. destruct b4. simpl in *. unfold blk_entry_id in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. destruct blk_code. simpl in *. unfold is_left. destruct ( decide (i = i) ); eauto.  simpl in *. unfold is_left in *. destruct p. simpl in *. destruct (decide (i0 = i0)). eauto. contradiction n; auto. Qed.






  Lemma jump_equiv_test : forall e s m br1 b pt bk fn  d s0 e0 fn0 bk0 pt0 ( senv : sound_env m {| fn := fn; bk := bk; pt := pt |} e) 
(            H7 : (do st <- jump m fn bk br1 e s; Jump st) =
       Jump ({| fn := fn0; bk := bk0; pt := pt0 |}, e0, s0)) 


              (Heqo : Some d = find_function m fn)
            (Heqo0 : Some b = find_block (blks (df_instrs d)) bk),

                                        
          sound_env m {| fn := fn0; bk := bk0; pt := pt0 |} e0.
  Proof. intros. unfold jump in *. simpl in *.
         unfold find_block_entry in *.
         unfold sound_env in *.
         simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in H7. remember ( find_block (blks (df_instrs d)) br1).




         destruct o. simpl in *. unfold block_to_entry in *. simpl in *. unfold monad_fold_right in *. simpl in *. remember ( (fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp in H7. clear Heqp. generalize Heqo1; intros.


         apply find_block_equiv in Heqo1. unfold blk_entry_pc in *. simpl in *.
 subst.





         unfold blk_entry_pc in *. simpl in *. destruct p. simpl in *. inversion H7. simpl in *. inversion H7. subst. rewrite <- Heqo in H. rewrite <- Heqo2 in H. inversion H. subst. eauto.

         unfold Subset. simpl in *. unfold blk_entry_id in *. simpl in *. unfold fallthrough. simpl in *. destruct b0. simpl in *. unfold prep_block in *. simpl in *. destruct blk_code. simpl in *. unfold value_analysis. simpl in *. unfold is_left. unfold blk_term_id in *. simpl in *.
         destruct (decide (fst blk_term = fst blk_term)).  eauto. eauto. intros. destruct p0. simpl in *. exists  DVALUE_Poison. simpl in *. intros. unfold value_analysis in *. destruct blk_code in *. simpl in *. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (i = i)). simpl in *. unfold lookup_env in *. inversion H0. contradiction n. auto. simpl in *. unfold is_left in *. simpl in *.

destruct (decide (i = i)). inversion H0. contradiction n; eauto. simpl in *. inversion H7.
  Qed.
  Hint Resolve jump_equiv_test.

(* lookup_env (add_env id dv e) id = Some dv.*)


Print Subset.



  
       Lemma step_preserves_sound_env : forall m st st1, 
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state m st  -> stepD m st = Step st1 -> sound_env m (pc_of st1) (env_of st1).
    Proof. intros. destruct st, st1; simpl in *. destruct p, p0; simpl in *. destruct p0, p. inversion H0.
           unfold fetch in *. unfold incr_pc in *. simpl in *.
           remember ( find_function m fn0).  destruct o; simpl in *; inversion H1.
           remember (find_block (blks (df_instrs d)) bk0). destruct o; simpl in *; inversion H1.
           remember (block_to_cmd b pt0). destruct o; simpl in *. destruct p; simpl in *. destruct c. destruct o; inversion H1; subst. destruct pt0, i; inversion H1; subst; simpl in *.
           +remember (eval_op e None op); inversion H1. destruct e1; simpl in *; inversion H1; subst. unfold sound_env in *. simpl in *. eapply test5 in H; eauto.  unfold prep_selected_block in *; simpl in *. rewrite <- Heqo. rewrite <- Heqo0. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. intros. inversion H2; subst. apply senv in H2. rewrite H.

            eauto.






           +(*6*) destruct fn1. destruct i. unfold find_function_entry in *; simpl in *. remember ( find_function m id0). destruct o. remember (find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o. simpl in *. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *. inversion H1. inversion H1; subst. 


unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo2.

simpl in *. rewrite <- Heqo in senv. simpl in *. rewrite <- Heqo0 in senv. rewrite <- Heqo3. intros. inversion H2. unfold value_analysis. simpl in *. unfold prep_block. simpl in *. rewrite value_analysis_at_entry_is_nil. eauto. simpl in *; inversion H1. simpl in *; inversion H1. inversion H1.
           +destruct ptr. destruct ( eval_op e (Some t0) v); simpl in *; inversion H1. destruct v0; inversion H5.
           



            
           +destruct fn1. destruct i; inversion H3. unfold find_function_entry in *. simpl in *. remember (find_function m id). destruct o; simpl in *. remember ( find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o; simpl in *. destruct (map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *. inversion H1. destruct t; inversion H1. subst.  unfold sound_env in *.  simpl in *.
            unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. rewrite <- Heqo2. rewrite <- Heqo3. intros. inversion H2. subst. unfold value_analysis, prep_block; simpl in *. rewrite  value_analysis_at_entry_is_nil. eauto. inversion H1.
           +inversion H1.
           +destruct val, ptr in *. destruct (eval_op e (Some t) v), (eval_op e (Some t0) v0); simpl in *; inversion H1. destruct v2; inversion H1.
           +destruct t; inversion H1.
            *destruct v. destruct (eval_op e (Some t) v), s; simpl in *; inversion H1. destruct f; simpl in *; inversion H1. destruct s; inversion H1. destruct f; simpl in *; inversion H1. destruct v. destruct ( eval_op e (Some t) v); simpl in *. inversion H1. destruct v0; inversion H1. destruct ( StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *. destruct ( jump m fn0 bk0 br1 e s); simpl in *. inversion H1. inversion H1. destruct ( jump m fn0 bk0 br2 e s); simpl in *. inversion H1. inversion H1. destruct ( jump m fn0 bk0 br e s); simpl in *. inversion H1. inversion H1. inversion H1. Qed.




    Lemma jump_preserves_sound_stack : forall m st st1, 
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state m st  -> stepD m st = Jump st1 -> sound_stack m (stack_of st1).
    Proof. intros. destruct st. inversion H0; subst. destruct p. destruct p; simpl in *. simpl in *.

           remember ( find_function m fn). destruct o. remember ( find_block (blks (df_instrs d)) bk).
           destruct o. simpl in *. remember ( block_to_cmd b pt). destruct o; simpl in *. destruct p. simpl in *.
           destruct c. destruct o. destruct pt, i; inversion H1. destruct (eval_op e None op); inversion H1.
           destruct fn0. destruct i; simpl in *; inversion H1. destruct  (find_function_entry m id0); inversion H4; simpl in *. destruct f; simpl in *. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1.
           destruct ptr. simpl in *. destruct ( eval_op e (Some t0) v); simpl in *. inversion H1. destruct v0. simpl in *. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1.
           destruct fn0, i; simpl in *. unfold find_function_entry in *. simpl in *.
remember ( find_function m id). destruct o. remember (find_block (blks (df_instrs d0)) (init (df_instrs d0))). destruct o. simpl in *. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1. destruct t; inversion H1. simpl in *. inversion H1. simpl in *; inversion H1. inversion H1. 


 inversion H1. destruct val, ptr. destruct ( eval_op e (Some t) v),( eval_op e (Some t0) v0); simpl in *. inversion H1. inversion H1. inversion H1. destruct v2. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. inversion H1. simpl in *. inversion H1.


 destruct t; inversion H1. destruct v. destruct (eval_op e (Some t) v); simpl in *. inversion H1. destruct s. inversion H1. destruct f. inversion H1; subst. induction H0. 
 simpl in *. inversion sstack; subst; eauto. inversion H1. destruct s. inversion H1. destruct f. inversion H1. inversion H3; subst. simpl in *. inversion sstack; subst; eauto. 

 destruct v. destruct (eval_op e (Some t) v); simpl in *. inversion H1. destruct v0; simpl in *; inversion H1. destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one); simpl in *.
 eauto.

 unfold jump in *. simpl in *. unfold find_block_entry in *. simpl in *.
 rewrite <- Heqo in H1. destruct (find_block (blks (df_instrs d)) br1); simpl in *.
unfold monad_fold_right in *. simpl in *. remember ((fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp in  H1. destruct p. simpl in *. inversion H1. simpl in *. inversion H1; subst; simpl in *; eauto.

inversion H1. unfold jump in *. unfold find_block_entry in *. simpl in *.  rewrite <- Heqo in H1.
remember (find_block (blks (df_instrs d)) br2). destruct o0.  unfold block_to_entry in *. simpl in *. unfold monad_fold_right in *. simpl in *. remember ((fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end)). rewrite <- Heqp in H1. destruct p; simpl in *. inversion H1. inversion H1. subst. simpl. auto. simpl in *. inversion H1.
unfold jump in *. simpl in *. unfold find_block_entry in *. simpl in *. rewrite <- Heqo in H1.
remember (find_block (blks (df_instrs d)) br). destruct o0. unfold block_to_entry in *. simpl in *. unfold monad_fold_right in *. simpl in *. remember  (fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end). rewrite <- Heqp in H1. destruct p; simpl in *. inversion H1. inversion H1. simpl in *. eauto. simpl in *. inversion H1. inversion H1. simpl in *. inversion H1. simpl in *. inversion H1. Qed.




Print sound_env.


Lemma jump_preserves_sound_env : forall m st st1, 
    (forall b, NoDup ((map fst (blk_code b)) ++ ( blk_term_id b ) :: nil))  -> sound_state m st  -> stepD m st = Jump st1 -> sound_env m (pc_of st1) (env_of st1).
Proof.
  Proof. intros. destruct st, st1. destruct p, p0. destruct p, p0. simpl in *.


         remember (find_function m fn). destruct o; simpl in *; inversion H1.
         remember ( find_block (blks (df_instrs d)) bk). destruct o; simpl in *; inversion H1.
         remember (block_to_cmd b pt). destruct o; simpl in *; inversion H1. destruct p; simpl in *. destruct c.
         destruct o; simpl in *; inversion H1.   destruct pt, i; inversion H1.  destruct  (eval_op e None op); simpl in *; inversion H1. destruct fn1. destruct i.
simpl in *. unfold find_function_entry in *. simpl in *. unfold sound_env in *.
simpl in *. destruct (  match find_function m id0 with
          | Some a =>
              match find_block (blks (df_instrs a)) (init (df_instrs a)) with
              | Some a0 =>
                  Some
                    (FunctionEntry (df_args a)
                       {| fn := id0; bk := init (df_instrs a); pt := blk_entry_id a0 |})
              | None => None
              end
          | None => None
          end); simpl in *. destruct f. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *. inversion H1. inversion H1. inversion H1. inversion H1. destruct ptr. destruct (eval_op e (Some t0) v). simpl in *. inversion H1. simpl in *. destruct v0; inversion H1. destruct fn1, i; simpl in *; inversion H1. destruct (find_function_entry m id); simpl in *; eauto. destruct f; simpl in *; eauto. destruct ( map_monad (fun '(t, op) => eval_op e (Some t) op) args); simpl in *; inversion H1. destruct t; simpl in *; inversion H1. inversion H1. destruct val, ptr. destruct ( eval_op e (Some t) v), ( eval_op e (Some t0) v0); simpl in *; inversion H1. destruct v2; inversion H1. 

destruct t; inversion H1.
         + simpl in *. destruct v. destruct ( eval_op e (Some t) v); simpl in *. inversion H1. destruct s. inversion H1. destruct f. inversion H1. subst.

inversion H0. simpl in *. subst. inversion sstack. subst. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo in senv. rewrite <- Heqo0 in senv. 
remember (find_function m fn0). destruct o0. simpl in *. remember (find_block (blks (df_instrs d0)) bk0). destruct o0. simpl in *. intros. inversion H2. subst. apply sstack_env in H2. unfold Subset in *. simpl in *. unfold lookup_env in *. simpl in *. intros. destruct (AstLib.RawID.eq_dec a id); eauto. 

intros. inversion H2.
intros. inversion H2. simpl in *. inversion H6. destruct s. inversion H1.

destruct f. inversion H6. simpl in *.
inversion H1; subst.
eauto.
 inversion H0. subst. simpl in *. inversion sstack. subst. simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. remember ( find_function m fn0). destruct o0. simpl in *.
simpl in *. remember (find_block (blks (df_instrs d0)) bk0). destruct o0. simpl in *. intros. inversion H2. subst. apply sstack_env in H2. subst. eauto. intros. inversion H2. intros. inversion H2.





inversion H0; subst.

destruct v. destruct (eval_op e (Some t) v); simpl in *. inversion H1. destruct v0; inversion H1.

         +destruct (StepSemantics.Int1.eq x StepSemantics.Int1.one). simpl in *.








eauto. eauto. eauto.


unfold jump in *. unfold find_block_entry in *. simpl in *. rewrite <- Heqo in H6.  unfold block_to_entry in *.  unfold blk_entry_pc in *. unfold blk_entry_id in *. clear H1; clear H3; clear H4. clear H6. simpl in *. rewrite <- Heqo in H5. remember ( find_block (blks (df_instrs d)) br). destruct o0. simpl in *. generalize Heqo2. intros.  eapply find_block_equiv in Heqo3. subst. unfold monad_fold_right in *. remember (
          (fix
           monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                            (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                            (a : A) {struct l} : M A :=
             match l with
             | [::] => mret a
             | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
             end) ). rewrite <- Heqp in H5. clear Heqp. destruct p. simpl in *. inversion H5. simpl in *. inversion H5. subst. eauto.

simpl in *. unfold sound_env in *. simpl in *. unfold prep_selected_block in *. simpl in *. rewrite <- Heqo. generalize Heqo0. intros. eapply find_block_equiv in Heqo0. subst. rewrite <- Heqo2 in H1. inversion H1. subst. unfold Subset. simpl in *. intros. destruct b0. simpl in *. unfold value_analysis in *. simpl in *. unfold prep_block in *. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_code in *. simpl in *. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (fst blk_term = fst blk_term)). simpl in *. unfold lookup_env in *. simpl in *.
exists ( DVALUE_Poison). intros. inversion H2. contradiction n. eauto. simpl in *.



destruct p0. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (i = i)). simpl in *.

unfold lookup_env in *. simpl in *. exists (DVALUE_Poison). intros. inversion H2. contradiction n. eauto. simpl in *. inversion H5.
Qed.





  