Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.Dom Vellvm.CFG  Vellvm.CFGProp Vellvm.AstLib.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.add_instr.

Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.maps.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
     Require Import ssreflect ssrbool seq eqtype ssrnat.
Print find_instr.
Print pc_list.

Require Import compcert.lib.Lattice.
Require Import compcert.lib.Maps.


(*


Definition env_of (s:state ) := snd (fst (s)).
Definition pc_of (s:state) := pt (fst (fst s)).

                                  

  Definition incr_local_pc (b:block) (l:instr_id) :=
    match block_to_cmd b l with
    | Some (_, Some i) => Some i
    | _ => None
    end.


  Definition fetch_local_instr (b:block) (l:instr_id) :=
    match block_to_cmd b l with
    | Some (ins, _) => Some ins
    | _ => None
    end.
  Print state.

(*
Definition pt_exists (b:block) (l:instr_id)  := exists c,  fetch_local_instr b l = Some c.

Definition instr_id_dec := forall (x y : instr_id), {x = y} + {x <> y}.


Print fallthrough.



Definition pt_exists1 (b:block) (l:instr_id) c :=  fetch_local_instr b l = Some c.*)
(*

Inductive edge_pt (b:block) : instr_id -> instr_id -> Prop :=
| edge_step : forall p p1, incr_local_pc b p = Some p1 -> edge_pt b p p1.


Module PtGraph <: GRAPH.
  Definition t := block.
  Definition V := instr_id.
  Definition entry g := blk_entry_id g.
  Definition edge := edge_pt.
  Definition mem := pt_exists.
  Definition eq_dec_V := AstLib.eq_dec_instr_id.
End PtGraph.
Module Export Dom := Dom.Spec PtGraph.


Definition pt_defines (pt:instr_id) (lid:local_id) :=
  match pt with
  | IId id => if (decide (id = lid)) then True else False
  | IVoid _ => False
  end.


Definition def_at_pt (g:block) (p:instr_id) (lid:local_id) : Prop :=
  pt_exists g p /\ pt_defines p lid.


Inductive instr_path (b:block) : instr_id -> instr_id -> Prop :=
| instr_refl : forall i, instr_path b i i
| instr_path_step : forall i i1 i2, instr_path b i i1 -> incr_local_pc b i1 = Some i2 -> instr_path b i i2.
                                                        


Definition uid_sdom_pc (g:block) (p:pc) (lib:local_id) := exists p',  def_at_pt g p' lib /\ instr_path g p' (pt p).

Print lookup_env.
Print local_id.
Definition wf_loc (g:block) (p:pc) (e:env) : Prop :=
forall uid, uid_sdom_pc g p uid -> exists n, lookup_env e uid = Some n.



Print incr_local_pc.
Print fetch_local_instr.
Print instr_id.



Lemma helper : forall b pt p1, incr_local_pc b pt = Some p1 -> instr_path b pt p1.
Proof. intros. eapply instr_path_step in H. eauto. constructor. Qed.


Lemma in_it : forall b p p1 e c a, incr_local_pc b (pt p) = Some p1 -> fetch_local_instr b (pt p) = Some (CFG.Step a) -> (pt p) = IId c -> wf_loc b (mk_pc (fn p) (bk p) p1) e ->
                                     exists n,  In (c, n) e.
Proof. intros. simpl in *. unfold wf_loc in *. unfold uid_sdom_pc in *. Print instr_path. unfold def_at_pt in *. unfold pt_exists in *. simpl in *. unfold pt_defines in *. simpl in *.
       specialize (H2 c). simpl in *. destruct p. simpl in *.  destruct H2. exists pt. split. split. exists (CFG.Step a); eauto. rewrite H1. unfold is_left. destruct (decide (c = c)); eauto. 

       apply helper in H. auto. induction e. simpl. unfold lookup_env in H2. simpl in *. inversion H2. simpl. unfold lookup_env in H2. simpl in *. destruct a0. simpl in *.
       destruct ( RawID.eq_dec c l). subst. exists v. left. eauto. unfold lookup_env in IHe. apply IHe in H2. inversion H2. exists x0. right. eauto. Qed.
Definition second_val a : value := DV (VALUE_Integer a).
Definition first_val a : instr := INSTR_Op (SV (VALUE_Integer a)).




Print add_env.



Print def_at_pt.
Print value.
Print value.
Print dvalue.
Print Ollvm_ast.value.

Inductive rhs (b:block) (p:pc) : int  -> Prop:=
  | rhs_intro : forall v, fetch_local_instr b (pt p) = Some (CFG.Step (first_val v)) -> rhs b p v.

Print lookup_env.

Print state.

Definition get_env (p:state) : env := snd (fst p).
Definition equational_lemma b pc := forall x d v, def_at_pt b (pt x) d /\ rhs b x v /\ incr_local_pc b (pt x) = Some (pc_of pc) -> lookup_env (get_env pc) d = Some (DV (VALUE_Integer v)).
Print uid_sdom_pc.
Print ident.
  Definition wf_use (g:block) (i:instr) (p:pc) : Prop :=
   forall uid, In (ID_Local uid) (instr_uses i) -> uid_sdom_pc g p uid.
  Print instr_path.
  Print blk_entry_id.
  Definition instr_path_reachable b p:= instr_path b (blk_entry_id b) (pt p).

  Inductive wf_insn (b:block) : instr -> pc -> Prop :=
  | wf_insn_intro : forall i p
      (Huse: wf_use b i p)
      (Hreach: instr_path_reachable b  p),
      wf_insn b i p.
  

  
Print pt_exists.
Inductive wf_block (b:block) :=
| wf_code_test : forall (Hlbls: NoDup ((fst (blk_term b)) :: (map (@fst _ _) (blk_code b))))
                        (Hwfis: forall (p:pc), pt_exists b (pt p) -> forall i, wf_insn b i p), wf_block b.
Definition get_pc (st:state) : pc := fst (fst st).






Lemma eq_lemma_correct : forall b st, wf_block b -> instr_path_reachable b (get_pc st) -> equational_lemma b st.
Proof. unfold equational_lemma. simpl in *. intros. unfold get_pc in *. destruct H1. destruct H2. destruct st. simpl in *. destruct p. simpl in *. unfold pc_of in H3. simpl in *. destruct p. simpl in *. inversion H. subst. destruct x. simpl in *.
       
       
       
Print wf_block. (*
Lemma 
Definition def_at_pt b x d /\ (rhs b x i) /\ instr_path b d pc -> lookup_env (env_of p) d = i.

Lemma test : forall a e,  incr_local_pc b (pt p) = Some p1 -> fetch_local_instr b (pt p) = Some (CFG.Step (first_val a)) -> (pt p) = IId c -> Step ((mk_st (fn p) (bk p) (p1)), e, 

Lemma incr : forall e a p1 c b p, incr_local_pc b (pt p) = Some p1 -> fetch_local_instr b (pt p) = Some (CFG.Step (first_val a)) -> (pt p) = IId c -> wf_loc b (mk_pc (fn p) (bk p) p1) e ->
                                  lookup_env e c = Some (second_val a).
 Proof. intros. eapply in_it in H. *)


        (*
Definition first_val a : instr := INSTR_Op (SV (VALUE_Integer a)).

Definition second_val a : value := DV (VALUE_Integer a).

Lemma in_it1 : forall b p p1 e c a, incr_local_pc b (pt p) = Some p1 -> fetch_local_instr b (pt p) = Some (CFG.Step (first_val a)) -> (pt p) = IId c -> wf_loc b (mk_pc (fn p) (bk p) p1) e ->
                                     In (c, (second_val a)) e.
Proof. intros. simpl in *. destruct p. simpl in *. subst. unfold wf_loc in *. unfold uid_sdom_pc in *. unfold def_at_pt in *. unfold pt_exists in *. simpl in *. unfold pt_defines in *. simpl in *. specialize (H2 c). simpl in *. destruct H2. exists (IId c); simpl in *; eauto. split. split. exists (CFG.Step (first_val a)); eauto. unfold is_left. destruct (decide (c = c)); eauto.
       apply helper in H. eauto.
*)

      

(*


Lemma wf_loc_succ : forall b p p1 e a id, wf_block b -> wf_env b p e ->
                                       incr_local_pc p = Some p1
                                       instr_int_rel b p id a ->
                                       wf_loc b 


*)
Print SDom.



Inductive well_scoped_use_at_pt (g:block) (p:instr_id) : ident -> Prop :=
| ws_local : forall lid p', def_at_pt g p' lid -> SDom g p' p -> well_scoped_use_at_pt g p (ID_Local lid).
(*
Definition wf_use (g:block) (ids:list ident) (p:instr_id) : Prop :=
  forall id, In id ids -> well_scoped_use_at_pt g p id.


Inductive wf_instr (g:block) (p:instr_id)  :=
| wf_instr_intro : forall (i:instr)
              (Huse: wf_use g (instr_uses i) p), wf_instr g p.

Print NoDup.

Print pt_exists.
Inductive wf_block (b:block) :=
| wf_code_test : forall (Hlbls: NoDup ((fst (blk_term b)) :: (map (@fst _ _) (blk_code b))))
                        (Hwfis: forall (p:instr_id), pt_exists b p -> wf_instr b p), wf_block b.


Definition at_entry (b:block) (l:instr_id) := blk_entry_id b = l.

Inductive wf_state (b:block) : state -> Prop :=
| wf_state_intro : forall st (Hwfpc : pt_exists b (pc_of st))
                          (Hwfppc: at_entry b (pc_of st) \/ edge_pt b (blk_entry_id b) (pc_of st)), wf_state b st.


Definition init_pc (f:function_id) (b:block) : pc := mk_pc f (blk_id b) (blk_entry_id b).

Definition init_state (f:function_id) (b:block) : state := (init_pc f b, nil, nil).


Print local_id_of_ident.

Definition look_up e id :=
  match (local_id_of_ident id) with
  | inr a => match lookup_env e a with
      | None => failwith ("lookup_env: id =  NOT IN env = " ++ (string_of e))
      | Some v => mret v
             end
  | inl a => failwith ("NON LEFT")
  end
.
Print fetch_local_instr.
Print instr.
Print instr_uses.
*)*)
(*STEP SEMANTICS*)
Definition stepD (b:block) (s:state) : transition state :=
  let '(pc, e, k) := s in
  match (fetch_local_instr b (pt pc)) with
  | None => Obs (Err "ERROR: No instruction")
  | Some cmd => match cmd with
                | CFG.Step ins => match incr_local_pc b (pc_of s) with
                                  | Some next_int => match (pt pc), ins with
                                                     | IId id, (INSTR_Op op) => match (eval_op e None op) with
                                                                                         | inl a => Obs (Err a)
                                                                                         | inr a => Step ((mk_pc (fn pc) (bk pc) next_int), add_env id a e, k)
                                                                                end
                                                     | _, _ => Obs (Err "unimplemented instr")
                                                                   
                                                     end
                                  | None => Obs (Err "no next instr")
                                  end
                | Term (TERM_Ret (t, op)) => match (eval_op e (Some t) op) with
                                             | inl a => Obs (Err a)
                                             | inr a => Obs (Fin a)         
                                             end
                | Term (TERM_Ret_void) => Obs (Fin (DV (VALUE_Bool true)))
                | _ => Obs (Err "Unimplemented term")            
                                              
                end
  end.
CoFixpoint step_sem (b:block) (s:state) : Trace state :=
  match stepD b s with
  | Step s' => Tau s (step_sem b s')
  | Jump s' => Tau s (step_sem b s')
  | Obs (Fin v) => Vis (Fin v)
  | Obs (Err v) => Vis (Err v)
  | Obs (Eff v) => Vis (Err "Wrong instr")
  end.


Definition sem (b:block) (s:state) : Trace () := hide_taus (step_sem b s).



Inductive instr_path (b:block) : instr_id -> instr_id -> Prop :=
| instr_refl : forall i,  instr_path b i i
| instr_step : forall i i1 i2, instr_path b i i1 -> incr_local_pc b i1 = Some i2 -> instr_path b i i2.





Definition pt_defines (pt:instr_id)  :=
  match pt with
  | IId id => True
  | IVoid _ => False
  end.


Definition pt_exists (b:block) (l:instr_id)  (c:cmd) := fetch_local_instr b l = Some c.




Definition def_at_pt (g:block) (p:instr_id) (lid:local_id) : Prop :=
 exists c, pt_exists g p c /\ pt_defines p.
Print instr_id.
Print IId.
  Definition uid_sdom_pc (g:block) (uid:local_id) (p:pc) : Prop :=
    exists (p':pc), def_at_pt g (pt p') uid /\ instr_path g (pt p') (pt p).

Print ident.

  Definition wf_use (g:block) (i:instr_id * instr) (p:pc) : Prop :=
  forall uid, In (ID_Local uid) (instr_uses (snd i)) -> uid_sdom_pc g uid p.

Print blk_entry_id.
    Definition reachable (b:block) (p:pc) : Prop :=
    instr_path b (blk_entry_id b) (pt p).

    
  Inductive wf_insn (b:block) : (instr_id*instr) -> pc -> Prop :=
  | wf_insn_intro : forall i p
      (Huse: wf_use b i p)
      (Hreach: reachable b p),
      wf_insn b i p.

Print cmd.


Inductive insn_at_pc (b:block) (p:pc) (i:instr) : Prop :=
| indn_at_pc_entry : fetch_local_instr b (pt p) = Some (CFG.Step i) -> insn_at_pc b p i.

                                                                                                                      
                                                                                             


  Inductive wf_prog (b:block) : Prop :=
  | wf_prog_intro : forall
      (Hwfis : forall p i, insn_at_pc b p (snd i) -> wf_insn b i p)
      (Hlbls: NoDup ((fst (blk_term b)) :: (map (@fst _ _) (blk_code b)))),
      wf_prog b.


  Definition wf_loc (b:block) (p:pc) (loc:env) : Prop :=
  forall uid, uid_sdom_pc b uid p -> exists n, lookup_env loc uid = Some n.

Print blk_entry_id.
  Definition at_entry (b:block) (p:pc) : Prop :=
    blk_entry_id b = (pt p).


  Definition wf_pc (b:block) (p:pc) :=
    exists c,  fetch_local_instr b (pt p) = Some c.
  Print env_of.


  
(**)
Fixpoint get_backwards_help (cd:code) (p t: instr_id) : option instr_id :=
  match cd with
  | nil => None
  | hd :: cd0 => if decide ((fallthrough cd t) = p) then Some (fst hd) else get_backwards_help cd0 p t
  end.
Definition get_backwards (b:block) (p:instr_id) := get_backwards_help (blk_code b) p (blk_term_id b).

Lemma backwards_forwards_equiv : forall b p p1, incr_local_pc b p = Some p1 -> get_backwards b p1 = Some p.
Proof. Admitted. 


Lemma backwards_never_equals_backwards : forall blk_code p1 p, get_backwards_help blk_code p1 p = Some p1 -> False.
Proof.
Admitted.
Lemma backwards_never_equals_backwards1 : forall blk_code p1 p, get_backwards_help blk_code p p1 = Some p1 -> False.
Proof. Admitted.
  
Lemma forwards_backwards_equiv : forall b p p1, (blk_entry_id b = p -> False) -> get_backwards b p1 = Some p -> incr_local_pc b p = Some p1.
Proof. 
Admitted.




(* single step of SD implies forwards*) 
Print wf_pc.
Definition get_pc (s:state) : pc := fst (fst s).
Print wf_loc.
  Inductive wf_state (b:block) : state -> Prop :=
  | wf_state_intro : forall st
      (Hwfpc: wf_pc b (get_pc st))
      (Hwfloc: wf_loc b (get_pc st) (env_of st)),
      wf_state b st.




Print env.
Print value.
Print dvalue.
Print Expr.

Print instr.

Definition aval_list :=  seq (instr_id * option (raw_id * dvalue)).
Definition whole_struct :=  seq (instr_id * seq (instr_id * option (raw_id * dvalue))).

Definition evaluate (alist:aval_list) (i:instr_id*instr) :=
  match (fst i), (snd i) with
  | IId c, INSTR_Op (SV (VALUE_Integer a)) => (IId c, Some (c, (DV (VALUE_Integer a)))) :: alist
  | _, _ => (fst i, None) :: alist
  end.

Print evaluate.

Fixpoint  eval_code (c:code) (a:aval_list) :=
  match c with
    | nil => nil
    | hd :: tl => (fst hd, evaluate a hd) :: (eval_code tl (evaluate a hd))
  end.

Print eval_code.


    
Definition eval_block (b:block) := eval_code (blk_code b) nil.
Print eval_block.


Fixpoint find_in_list (c:whole_struct) (i:instr_id) :=
  match c, i with
  | nil, _ => None
  | (c, a) :: tl, d => if (decide (c = d)) then Some a else find_in_list tl i                                      
  end.

(*EMATCH*)

Inductive sound_state_base : block -> state -> Prop :=
| sound_regular_state : forall b p e s ae
                               (WF_PC: wf_pc b (pt p))
                               (AN: find_in_list (eval_block b) (pt p) = Some ae)
                               (EM: ematch e ae),  sound_state_base b (p, e, s).



Lemma analyze_succ:
  forall e m rm f n ae am instr s ae' am' bc,
  (analyze rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f rm n ae am = VA.State ae' am' ->
  ematch bc e ae' ->
  mmatch bc m am' ->
  exists ae'' am'',
     (analyze rm f)!!s = VA.State ae'' am''
  /\ ematch bc e ae''
  /\ mmatch bc m am''.
Proof.

Lemma sound_succ_state:
  forall bc pc ae am instr ae' am' s f sp pc' e' m',
  (analyze rm f)!!pc = VA.State ae am ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  transfer f rm pc ae am = VA.State ae' am' ->
  ematch bc e' ae' ->
  mmatch bc m' am' ->
  romatch bc m' rm ->
  genv_match bc ge ->
  bc sp = BCstack ->
  sound_stack bc s m' sp ->
  sound_state_base (State s f (Vptr sp Ptrofs.zero) pc' e' m').
Proof.

Theorem sound_step_base:
  forall st t st', RTL.step ge st t st' -> sound_state_base st -> sound_state_base st'.
Proof.



         
(*

Inductive sound_state_base: state -> Prop :=
  | sound_regular_state:
      forall s f sp pc e m ae am bc
        (AN: (analyze rm f)!!pc = VA.State ae am)





        (EM: ematch bc e ae)
        (RO: romatch bc m rm)
        (MM: mmatch bc m am)
        (GE: genv_match bc ge)
        (SP: bc sp = BCstack),
      sound_state_base (State s f (Vptr sp Ptrofs.zero) pc e m)
*)










Print instr.
Definition opt (i:instr_id*instr) (e:smaller) :=
  match fst i, snd i with
  | IId c, INSTR_Op (SV (VALUE_Ident a)) => match e with
                                            | (id, Some (d, DV (VALUE_Integer f))) :: _ => if (decide (d = c)) then (fst i, INSTR_Op (SV (VALUE_Integer f))) else i
                                            | _ => i
                                            end
  | _, _ => i
  end.






    

Definition code_opt (b:block) : code :=
  let codeanalysis := transfer_analysis b in
  match (blk_code b) with
  | nil => nil
  | cons hd nil => cons hd nil
  | cons hd (cons hd1 nil) => cons hd (cons (opt hd1 codeanalysis) nil)
  | _ => (blk_code b)
 end.


Definition block_opt (b:block) := mk_block (blk_id b) (blk_phis b) (code_opt b) (blk_term b).


(*1. Match ae and e*)

(*Inductive sound_state_base: state -> Prop :=
  | sound_regular_state:
      forall s f sp pc e m ae am bc
        (AN: (analyze rm f)!!pc = VA.State ae am)
        (EM: ematch bc e ae)
        (RO: romatch bc m rm)
        (MM: mmatch bc m am)
        (GE: genv_match bc ge)
        (SP: bc sp = BCstack),
      sound_state_base (State s f (Vptr sp Ptrofs.zero) pc e m)
 .

*)

(*Lemma sound_succ_state:
  forall bc pc ae am instr ae' am' s f sp pc' e' m',
  (analyze rm f)!!pc = VA.State ae am ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  transfer f rm pc ae am = VA.State ae' am' ->
  ematch bc e' ae' ->
  mmatch bc m' am' ->
  romatch bc m' rm ->
  genv_match bc ge ->
  bc sp = BCstack ->
  sound_state_base (State s f (Vptr sp Ptrofs.zero) pc' e' m').
Proof.
  intros. exploit analyze_succ; eauto. intros (ae'' & am'' & AN & EM & MM).
  econstructor; eauto.
Qed.

*)

(*Theorem sound_step_base:
  forall st t st', RTL.step ge st t st' -> sound_state_base st -> sound_state_base st'.*)
Lemma trace_test : forall st p, trace_equiv (sem (block_opt p) st) (sem p st).
Proof. pcofix CIH.
       intros. pfold. assert ( (sem (block_opt p) st) = unroll  (sem (block_opt p) st)). destruct  (sem (block_opt p) st); eauto. rewrite H; clear H.
       assert ((sem p st) = unroll (sem p st)). destruct (sem p st); eauto. rewrite H; clear H.
       simpl in *. destruct p.  simpl in *. unfold block_opt. unfold code_opt. simpl in *. destruct blk_code. simpl in *. admit.
       destruct blk_code. admit. destruct blk_code. destruct st. simpl in *. destruct p1. simpl in *. unfold fetch_local_instr. unfold block_to_cmd. unfold blk_term_id in *. simpl in *. destruct p1. destruct blk_term. simpl in *. destruct (decide (i = pt)); subst.


       admit. destruct p; simpl in *; eauto. destruct ( decide (pt = i0)); subst; eauto. simpl in *. unfold incr_local_pc. simpl in *. unfold block_to_cmd in *. unfold blk_term_id. simpl in *. unfold pc_of. simpl in *.
       destruct ( decide (i = i0)); subst; eauto. destruct (decide (i0 = i0)); subst; eauto. admit.






       destruct p0. unfold opt. unfold transfer_analysis. simpl in *. destruct i2, i3, 0; simpl in *; eauto. unfold transfer_analysis; simpl in *; eauto. unfold transfer_func.
       simpl in *. destruct i0, i1; simpl in *; eauto. destruct p0. simpl in *. unfold opt. simpl in *. destruct i0, i1, op; simpl in *; eauto.
       destruct op0, e0; simpl in *; eauto.
       destruct e1; simpl in *; eauto.
        













       
contradiction n2; eauto.
contradiction n2; eauto.
contradiction n2; eauto.
contradiction n2; eauto.
contradiction n2; eauto.
contradiction n2; eauto.
contradiction n2; eauto.

destruct ( decide (id1 = id)); subst.
contradiction n2; eauto.
destruct ( decide (id1 = id)); subst.
contradiction n2; eauto.
destruct ( decide (id1 = id)); subst.
contradiction n2; eauto.

 decide (id1 = id)

admit.
destruct ( decide (id = id)).

       Admitted.
       

  
                                 
Definition code_opt (c:code) : code :=
  match c with
  | nil => nil
  | cons hd nil => cons hd nil
  | cons hd (cons hd1 nil) => cons hd (cons (opt hd hd1) nil)
  | _ => c
 end.
Print block.

Definition block_opt (b:block) := mk_block (blk_id b) (blk_phis b) (code_opt (blk_code b)) (blk_term b).


Lemma incr_pc_equiv : forall pt blk_term blk_phis blk_id p0 p, ((incr_local_pc
                  {|
                  blk_id := blk_id;
                  blk_phis := blk_phis;
                  blk_code := [:: p; opt p p0];
                  blk_term := blk_term |} pt) =  (incr_local_pc
            {|
            blk_id := blk_id;
            blk_phis := blk_phis;
            blk_code := [:: p; p0];
            blk_term := blk_term |} pt)).
Proof. intros. unfold incr_local_pc. unfold opt. simpl in *. unfold block_to_cmd. unfold blk_term_id. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt)); subst. eauto. destruct p. destruct (decide (pt = i0)). simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct p0; simpl in *; eauto. simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e0; simpl in *; eauto. simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct p0; simpl in *; eauto. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e; simpl in *; eauto. destruct ( decide (pt = i0)); subst; eauto. Qed.





       
Lemma trace_equiv_opt : forall b s, trace_equiv (sem b s) (sem (block_opt b) s).
Proof. pcofix CIH. intros. pfold.  unfold sem in CIH. unfold hide_taus in CIH.
       assert ((sem b s) = unroll (sem b s)). destruct  (sem b s); eauto. rewrite H; clear H.
       assert ( (sem (block_opt b) s) = unroll (sem (block_opt b) s)). destruct (sem (block_opt b) s); eauto. rewrite H; clear H. simpl in *. destruct s. destruct p. destruct p.
remember ( stepD b ({| fn := fn; bk := bk; pt := pt |}, e, s)). generalize Heqt. intro. symmetry in Heqt. 
unfold stepD in Heqt. unfold pc_of in *. simpl in  Heqt. destruct b. destruct blk_code. admit. destruct blk_code. admit.


unfold block_opt. simpl. destruct blk_code. simpl.
remember (           fetch_local_instr
             {|
             blk_id := blk_id;
             blk_phis := blk_phis;
             blk_code := [:: p; p0];
             blk_term := blk_term |} pt). remember (incr_local_pc
                 {|
                 blk_id := blk_id;
                 blk_phis := blk_phis;
                 blk_code := [:: p; p0];
                 blk_term := blk_term |} pt). 

generalize Heqo. generalize Heqo0. intros. rewrite incr_pc_equiv. unfold incr_local_pc in Heqo0. unfold block_to_cmd in Heqo0. unfold blk_term_id in Heqo0. simpl in Heqo0. destruct blk_term. simpl in Heqo0. destruct (decide (i = pt)). rewrite e0 in Heqo. rewrite Heqo0 in Heqo1. unfold pc_of. simpl. rewrite <- Heqo1. admit. destruct p. destruct p0.


rewrite Heqo0 in  Heqo1. unfold fetch_local_instr in Heqo. unfold block_to_cmd in Heqo. unfold blk_term_id in Heqo.
simpl in Heqo. rewrite Heqo in Heqo2. destruct (decide (i = pt)). contradiction n; eauto. destruct ( decide (pt = i0)). rewrite e0 in Heqo2. unfold fetch_local_instr. unfold block_to_cmd. unfold blk_term_id. simpl. destruct ( decide (i = pt)). contradiction n; eauto. destruct ( decide (pt = i0)). rewrite e1 in Heqo1. unfold pc_of.  simpl. rewrite e1. rewrite <- Heqo1. rewrite Heqo0 in Heqt. rewrite Heqo in Heqt. rewrite e1 in Heqt. rewrite <- Heqt in Heqt0. rewrite <- Heqt.



destruct i0; simpl; eauto. destruct i1; simpl; eauto. destruct op. simpl. destruct e2; simpl; eauto.

destruct ( eval_expr eval_op e None (VALUE_Ident id0)); simpl; eauto.
admit. admit. admit. admit. admit. admit. admit. admit. admit. simpl in *. admit. admit. admit. admit. simpl.
destruct ( eval_expr eval_op e None (OP_IBinop iop t1 v1 v2)); simpl. eauto.eauto. admit. destruct ( eval_expr eval_op e None (OP_ICmp cmp t1 v1 v2)); simpl; eauto. admit.
 destruct (  eval_expr eval_op e None (OP_FBinop fop fm t1 v1 v2)); simpl; eauto. admit. destruct ( eval_expr eval_op e None (OP_FCmp cmp t1 v1 v2)); simpl; eauto. admit. admit. admit. admit. contradiction n2; eauto.


destruct (decide (pt = i2)); simpl in *; eauto. subst.



rewrite incr_pc_equiv. unfold incr_local_pc in *. unfold block_to_cmd in *. unfold blk_term_id in *. simpl in Heqt. simpl. unfold pc_of in *. destruct blk_term. simpl in Heqt.  destruct (decide (i = pt)). remember (fetch_local_instr
             {|
             blk_id := blk_id;
             blk_phis := blk_phis;
             blk_code := [:: p; p0];
             blk_term := (i, t0) |} pt).  unfold fetch_local_instr in *. unfold block_to_cmd in *. unfold blk_term_id in *. simpl in Heqt. simpl. destruct (decide (i = pt)). rewrite Heqt. admit. des
       
      

destruct b. unfold block_opt.  unfold code_opt. destruct blk_code. admit. simpl. destruct blk_code. admit. destruct blk_code. unfold stepD in Heqt.

 assert ((incr_local_pc
                  {|
                  blk_id := blk_id;
                  blk_phis := blk_phis;
                  blk_code := [:: p; opt p p0];
                  blk_term := blk_term |} pt) =  (incr_local_pc
            {|
            blk_id := blk_id;
            blk_phis := blk_phis;
            blk_code := [:: p; p0];
            blk_term := blk_term |} pt)). unfold incr_local_pc. unfold opt. simpl in *. unfold block_to_cmd. unfold blk_term_id. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt)); subst. eauto. destruct p. destruct (decide (pt = i0)). simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e1; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct p0; simpl in *; eauto. simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e1; simpl in *; eauto. simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct p0; simpl in *; eauto. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct ( decide (pt = i0)); subst. eauto. eauto.










 rewrite H. rewrite <- Heqo0. destruct o0. simpl in *. destruct p. simpl in *. generalize Heqo. intros. unfold fetch_local_instr in  Heqo. fold block_to_cmd in Heqo. unfold block_to_cmd in Heqo. unfold blk_term_id in Heqo. simpl in *. destruct blk_term. simpl in *.
         unfold fetch_local_instr. unfold block_to_cmd. simpl in *. unfold blk_term_id. simpl in *. destruct (decide (i2 = pt)). simpl in *. rewrite Heqo. admit. destruct ( decide (pt = i0)). simpl in *. rewrite e0 in Heqo1. rewrite  Heqo in Heqo1.
rewrite Heqo.





(*here*)  unfold 










admit.











       +admit. destruct blk_code. simpl in *. admit. destruct blk_code.


        *remember (            fetch_local_instr
              {|
              blk_id := blk_id;
              blk_phis := blk_phis;
              blk_code := [:: p; p0];
              blk_term := blk_term |} pt). unfold pc_of. simpl in *. remember (                incr_local_pc
                  {|
                  blk_id := blk_id;
                  blk_phis := blk_phis;
                  blk_code := [:: p; p0];
                  blk_term := blk_term |} pt
). assert ((incr_local_pc
                  {|
                  blk_id := blk_id;
                  blk_phis := blk_phis;
                  blk_code := [:: p; opt p p0];
                  blk_term := blk_term |} pt) =  (incr_local_pc
            {|
            blk_id := blk_id;
            blk_phis := blk_phis;
            blk_code := [:: p; p0];
            blk_term := blk_term |} pt)). unfold incr_local_pc. unfold opt. simpl in *. unfold block_to_cmd. unfold blk_term_id. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt)); subst. eauto. destruct p. destruct (decide (pt = i0)). simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e1; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct p0; simpl in *; eauto. simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e1; simpl in *; eauto. simpl in *. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct i0; simpl in *; eauto. destruct p0; simpl in *; eauto. destruct i1; simpl in *; eauto. destruct op; simpl in *; eauto. destruct e0; simpl in *; eauto. destruct ( decide (pt = i0)); subst. eauto. eauto. rewrite H. rewrite <- Heqo0. destruct o0. simpl in *. destruct p. simpl in *. generalize Heqo. intros. unfold fetch_local_instr in  Heqo. fold block_to_cmd in Heqo. unfold block_to_cmd in Heqo. unfold blk_term_id in Heqo. simpl in *. destruct blk_term. simpl in *.
         unfold fetch_local_instr. unfold block_to_cmd. simpl in *. unfold blk_term_id. simpl in *. destruct (decide (i2 = pt)). simpl in *. rewrite Heqo. admit. destruct ( decide (pt = i0)). simpl in *. rewrite e0 in Heqo1. rewrite  Heqo in Heqo1.
rewrite Heqo.








       
Inductive step_rel (b:block) : state -> state -> Prop :=
  | step_refl : forall s, step_rel b s s
  | step_rel1 : forall s1 s2 s3, step_rel b s3 s2 -> stepD b s3 = Step s1 -> step_rel b s1 s2.


Print local_id.
Print raw_id.
Print ident.

Definition local_id_of_ident (i:ident) :=
  match i with
  | ID_Global _ => None
  | ID_Local a => Some a
                       
  end.
Print lookup_env.

(*There exists a p1 that defines an l1, there is a step relation between p1 and p, point p has l1 in its env*)
Inductive testy1 (b:block) (p: state) (l:ident) :=
| testy1_intro : forall l1, (exists p1, pt_defines (pc_of p1) l1 /\ step_rel b p1 p) -> local_id_of_ident l = Some l1 -> (exists t, lookup_env (env_of p) l1 = Some t) -> testy1 b p l.

(*applies testy1 to an id which is in the list of identifiers*)
Inductive testy (b:block) (ids:list ident) (p:state)  :=
  | testy_intro : forall id, testy1 b p id -> In id ids -> testy b ids p.


Inductive wf_env  (b:block) (p:state)  : Prop :=
  | wf_env_intro : forall uid a, testy b uid p  -> instr_uses a = uid -> fetch_local_instr b (pc_of p) = Some (CFG.Step a) -> wf_env b p.


Inductive single_step_rel (b:block) (p:state) (p1: state): Prop :=
| sstep_rel :  stepD b p = Step p1 -> single_step_rel b p p1.


Print fetch_local_instr.
Print instr.
Print INSTR_Op.
Print Ollvm_ast.value.
 Print Expr.
Print instr_id.


Inductive instr_int_rel (b:block) (p:state) (c:raw_id) (a:int) :=
| instr_rel_intro : fetch_local_instr b (pc_of p) = Some (CFG.Step (INSTR_Op (SV (VALUE_Integer a)))) ->
                    ((pc_of p) = IId c) -> instr_int_rel b p c a.
Print add_env.
Print local_id.
Print add_env.
Print state.

Definition mk_st (p:pc) (e:env) (s:stack) : state := (p, e, s).

Print state.
Definition get_pc (p:state) : pc := fst (fst p).
  
Lemma wf_loc_succ : forall b p p1 e a id, wf_block b -> wf_env b p ->
                                       single_step_rel b p p1 ->
                                       instr_int_rel b p id a ->
                                       wf_env b (mk_st (get_pc p1) (add_env id (DV (VALUE_Integer a)) e) (stack_of p1)).
Proof. Admitted.


Inductive insn_at_pc (b:block) (s:state) (i:instr) :=
| insn_at_pc_intro : fetch_local_instr b (pc_of s) = Some (CFG.Step i) -> insn_at_pc b s i.
Print instr_uses.
Print ident.

Print lookup_env.
Print look_up.
  Lemma eval_val__wf_loc : forall v b p i,
    wf_block b ->
    wf_env b p ->
    insn_at_pc b p i ->
    In v (instr_uses i) -> exists n, look_up (env_of p) v = inr n.
Proof. Admitted.



Print pc_of. 

Lemma test1 : forall b p c a p1,
    instr_int_rel b p c a -> single_step_rel b p p1 ->  (env_of p1) = ((c, DV (VALUE_Integer a))) :: (env_of p).
Proof. intros. induction H, H0.
unfold env_of, pc_of in *. destruct p, p1. simpl in *. destruct p0, p. simpl in *.
rewrite e in H. unfold incr_local_pc in *. simpl in *. unfold block_to_cmd in *. simpl in *. destruct b. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. unfold pc_of in *. simpl in *. destruct p. simpl in *. subst. destruct (decide (i = IId c)). inversion H. destruct ( find_instr blk_code (IId c) i). destruct p. simpl in *. destruct o. simpl in *. inversion H. subst. unfold add_env. eauto. inversion H. inversion H. Qed.
Print incr_local_pc.


Inductive wf_env2  (b:block) (p:state)  : Prop :=
  | wf_env_intro2 : wf_env2 b p.


Lemma wf_loc_succ1 : forall b p p1 e a id, wf_block b -> wf_env b p ->
                                       incr_local_pc b (pc_of p) = Some (pc_of p1) ->
                                       instr_int_rel b p id a ->
                                       wf_env b (mk_st (get_pc p1) (add_env id (DV (VALUE_Integer a)) e) (stack_of p1)).
Proof. Admitted.

       (* fetch_local_instr b (IId id) = Some (CFG.Step (INSTR_Op (SV (VALUE_Integer a))))*)

Definition change_pt_in_pc (i:instr_id) (p:pc) := (mk_pc (fn p) (bk p) i).

Definition change_pt_e (p:state) (i:instr_id) := (change_pt_in_pc i (get_pc p), env_of p, stack_of p).

(*
Definition test1 := ((mk_pc (fn p) (bk p) i1),(add_env c (DV (VALUE_Integer a)) (env_of p)), st).
 *)


Lemma test2 : forall b e i1 p st c a, incr_local_pc b (pt p) = Some i1 ->
                                      instr_int_rel b (p,e,st) c a ->
                                      stepD b (p, e, st)  = Step (((mk_pc (fn p) (bk p) i1),(add_env c (DV (VALUE_Integer a)) e), st)).
Proof. intros. inversion H. inversion H0. unfold stepD. rewrite H1. rewrite H. destruct p. unfold pc_of in H3. simpl in *. subst. eauto. Qed.

Print instr.
Print ident.
Inductive test3 (b:block) c (p:instr_id) : Prop :=
  | test3_intro : fetch_local_instr b p = Some (CFG.Step (INSTR_Op (SV (VALUE_Ident (ID_Local c))))) -> test3 b c p.





Print fetch_local_instr.



Lemma test4 : forall e c a st b p i1, incr_local_pc b (pt p) = Some i1 ->
                                      fetch_local_instr b (pt p) = Some (CFG.Step (INSTR_Op (SV (VALUE_Integer a)))) -> ((pt p) = IId c) ->
                                      stepD b ((mk_pc (fn p) (bk p) i1), e, st) = Step (((mk_pc (fn p) (bk p) i1), (add_env c (DV (VALUE_Integer a)) e), st)).
Proof. intros. destruct p. simpl in H. simpl.



























         Definition wf_loc (g:Cfg.t) (p:pc) (loc:loc) : Prop :=
         forall uid, uid_sdom_pc g uid p -> exists n, loc uid = Some n.


Lemma test4 : forall b st c a e st1 e1 p i1, instr_int_rel b (p,e,st) c a -> incr_local_pc b (pt p) = Some i1 -> test3 b c i1 ->
              exists p2, stepD b (((mk_pc (fn p) (bk p) i1), e1, st1)) = Step ((p2,(add_env c (DV (VALUE_Integer a)) e), st)).
Proof. intros. inversion H. inversion H1.   eapply test2 in H0. 



       Print block_to_cmd.
Print find_instr.

Print find_instr.

Definition size_two (cd:code) :=
  match cd with
  | nil => True
  | cons _ nil => True
  | cons _ (cons _ nil) => True
  | _ => False
  end.
Fixpoint get_last (cd:code) :=
  match cd with
  | nil => None
  | cons (t, w) nil => Some t
  | cons hd tl => get_last tl
  end.
Print get_last.




Fixpoint get_backwards_help (cd:code) (p t: instr_id) : option instr_id :=
  match cd with
  | nil => None
  | hd :: cd0 => if decide ((fallthrough cd t) = p) then Some (fst hd) else get_backwards_help cd0 p t
  end.
Print get_backwards_help.
Print blk_term_id.
Print get_last.
Definition get_backwards (b:block) (p:instr_id) := get_backwards_help (blk_code b) p (blk_term_id b).

Lemma backwards_forwards_equiv : forall b p p1, incr_local_pc b p = Some p1 -> get_backwards b p1 = Some p.
Proof. Admitted. 


Lemma backwards_never_equals_backwards : forall blk_code p1 p, get_backwards_help blk_code p1 p = Some p1 -> False.
Proof.
Admitted.
Lemma backwards_never_equals_backwards1 : forall blk_code p1 p, get_backwards_help blk_code p p1 = Some p1 -> False.
Proof. Admitted.
  
Lemma forwards_backwards_equiv : forall b p p1, (blk_entry_id b = p -> False) -> get_backwards b p1 = Some p -> incr_local_pc b p = Some p1.
Proof. intros. unfold incr_local_pc. unfold get_backwards in *. unfold blk_entry_id in *. unfold blk_term_id in *.
       unfold fallthrough in *. simpl in *. unfold block_to_cmd. simpl in *. destruct b. simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. destruct (decide (i = p)). subst. apply  backwards_never_equals_backwards1 in H0. inversion H0.
       induction blk_code. simpl in *. admit. induction blk_code. simpl in *. destruct a. simpl in *. unfold is_left in *. simpl in *. destruct ( decide (i0 = p1)). subst. destruct ( decide (p = p1)). subst. contradiction H; eauto.
Admitted.



(* single step of SD implies forwards*) 


       

Definition code_opt (c:code) : code :=
  match c with
  | nil => nil
  | cons hd nil => cons hd nil
  | cons hd (cons hd1 a) => cons hd (cons (test hd hd1) a)
 end.


Definition block_opt (b:block) :=
  mk_block (blk_id b) (blk_phis b) (code_opt (blk_code b)) (blk_term b).
Print block_opt.



Lemma useful_1 : forall i id0 t id1 op bk fn e s blk_id blk_phis id  blk_code
                        
  (r : Trace () -> Trace () -> Prop)
  (CIH : forall (st : state) (b : block),
        wf_block b -> r (hide_taus (step_sem b st)) (hide_taus (step_sem (block_opt b) st))) 
  (wf : wf_block
         {|
         blk_id := blk_id;
         blk_phis := blk_phis;
         blk_code := [:: (IId id0, INSTR_Op (SV (VALUE_Ident id1))), (IId id, INSTR_Op op) & blk_code];
         blk_term := (i, t) |}),  trace_equiv_step (upaco2 (trace_equiv_step (X:=())) r)
    match
      match
        match
          match eval_op e None op with
          | inl a => Obs (Err a)
          | inr a => Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id a e, s)
          end
        with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s)
              (step_sem
                 {|
                 blk_id := blk_id;
                 blk_phis := blk_phis;
                 blk_code := [:: (IId id0, INSTR_Op (SV (VALUE_Ident id1))), (IId id, INSTR_Op op)
                               & blk_code];
                 blk_term := (i, t) |} s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s)
              (step_sem
                 {|
                 blk_id := blk_id;
                 blk_phis := blk_phis;
                 blk_code := [:: (IId id0, INSTR_Op (SV (VALUE_Ident id1))), (IId id, INSTR_Op op)
                               & blk_code];
                 blk_term := (i, t) |} s')
        | Obs (Fin v) => Vis (Fin v)
        | Obs (Err v) => Vis (Err v)
        | Obs (Eff _) => Vis (Err "Wrong instr")
        end
      with
      | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
      | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end
    match
      match
        match
          match eval_op e None op with
          | inl a => Obs (Err a)
          | inr a => Step ({| fn := fn; bk := bk; pt := fallthrough blk_code i |}, add_env id a e, s)
          end
        with
        | Step s' =>
            Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s)
              (step_sem
                 {|
                 blk_id := blk_id;
                 blk_phis := blk_phis;
                 blk_code := [:: (IId id0, INSTR_Op (SV (VALUE_Ident id1))), (IId id, INSTR_Op op)
                               & blk_code];
                 blk_term := (i, t) |} s')
        | Jump s' =>
            Tau ({| fn := fn; bk := bk; pt := IId id |}, e, s)
              (step_sem
                 {|
                 blk_id := blk_id;
                 blk_phis := blk_phis;
                 blk_code := [:: (IId id0, INSTR_Op (SV (VALUE_Ident id1))), (IId id, INSTR_Op op)
                               & blk_code];
                 blk_term := (i, t) |} s')
        | Obs (Fin v) => Vis (Fin v)
        | Obs (Err v) => Vis (Err v)
        | Obs (Eff _) => Vis (Err "Wrong instr")
        end
      with
      | Vis v => Vis (trace_map (fun _ : state => ()) <$> v)
      | Tau _ k => Tau () (trace_map (fun _ : state => ()) k)
      end
    with
    | Vis a => Vis a
    | Tau a b => Tau a b
    end.

Proof. intros. destruct (eval_op e None op); simpl in *; eauto. constructor. right. generalize wf. unfold hide_taus in CIH. simpl in *. apply CIH. Qed.

Hint Resolve useful_1.




    
Lemma equiv_opt : forall st b (wf: wf_block b),  trace_equiv (sem b st) (sem (block_opt b) st).
Proof. pcofix CIH. intros. pfold. assert ( (sem b st) = unroll  (sem b st) ). destruct  (sem b st) ; eauto.
       rewrite H. clear H.


       assert ( (sem (block_opt b) st) = unroll  (sem (block_opt b) st)). destruct  (sem (block_opt b) st); eauto. unfold sem in *.
       rewrite H.  clear H. simpl in *. inversion wf. unfold stepD. destruct st. destruct p. unfold block_opt. simpl in *. destruct p. simpl in *. unfold pc_of. simpl in *. unfold fetch_local_instr in *. unfold block_to_cmd in *. unfold incr_local_pc. simpl in *. unfold block_to_cmd in *. destruct b. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. destruct ( decide (i = pt)); simpl in *; eauto. admit. unfold code_opt. destruct blk_code. simpl in *. eauto. destruct blk_code. simpl in *. admit. simpl in *. destruct p.   destruct (decide (pt = i0)). destruct pt, i1; simpl in *; eauto.   destruct ( eval_op e None op); simpl in *; eauto. unfold test. simpl in *. destruct p0. simpl in *. destruct i0; simpl in *; eauto. admit. constructor. right. generalize wf. apply CIH. destruct p0. simpl in *. unfold pt_exists in Hwfis. unfold fetch_local_instr in Hwfis. unfold block_to_cmd in Hwfis. unfold blk_term_id in Hwfis. simpl in *. destruct  (decide (i = pt)); subst. contradiction n; eauto. destruct (decide (pt = i0)); subst. contradiction n0. eauto. destruct (decide (pt = i2)); simpl in *; eauto. unfold test. simpl in *. subst. specialize (Hwfis i2). destruct ( decide (i = i2)); subst; simpl in *; eauto. contradiction n; eauto.

       
       destruct ( decide (i2 = i0)); subst. contradiction n2; eauto. destruct ( decide (i2 = i2)); subst. destruct i2. simpl in *. destruct i3.
induction Hwfis.  



















  Lemma wf_init_state : 
    forall f b, wf_block b ->
    wf_state b (init_state f b).
  Proof. intros. inversion H; subst. constructor.
         +unfold pt_exists. unfold fetch_local_instr. unfold block_to_cmd. unfold blk_term_id. unfold init_state. unfold init_pc. destruct b; simpl in *; eauto. destruct blk_term. simpl in *. unfold blk_entry_id. simpl in *. unfold blk_term_id in *. simpl in *. unfold pc_of. simpl in *. destruct blk_code; simpl in *; eauto. destruct (decide (i = i)); simpl in *; eauto. contradiction n; auto. destruct p. simpl in *. destruct (decide (i = i0)); subst; simpl in *; eauto. destruct (decide (i0 = i0)); simpl in *; eauto. contradiction n0; eauto.
         +left. unfold init_state. unfold init_pc. unfold pc_of. unfold at_entry. unfold blk_entry_id. simpl in *. eauto. Qed.




  Lemma test1 : forall s s1 b, stepD b s = Step s1 -> exists t, env_of s1 = t :: (env_of s).
  Proof. intros. unfold stepD in H. unfold fetch_local_instr, incr_local_pc in H. unfold block_to_cmd in H. destruct s. destruct p. destruct p. unfold blk_term_id in *. destruct b; simpl in *; eauto. destruct blk_term in *. simpl in *. unfold pc_of in *; simpl in *.
         destruct ( decide (i = pt)); simpl in *; subst; eauto. destruct t; simpl in *; eauto; inversion H. destruct v; simpl in *; eauto. destruct (eval_op e (Some t) v); simpl in *; eauto; inversion H1. destruct ( find_instr blk_code pt i); simpl in *; eauto; inversion H. destruct p; simpl in *; eauto. destruct o; simpl in *; eauto. destruct pt; simpl in *; eauto; inversion H. destruct i0; simpl in *; eauto; inversion H. destruct c; simpl in *. destruct i0; simpl in *; eauto; inversion H. destruct ( eval_op e None op); simpl in *; eauto; inversion H. unfold env_of; simpl in *; eauto. destruct t0; simpl in *; eauto; inversion H. destruct v; simpl in *; eauto. destruct ( eval_op e (Some t0) v); simpl in *; inversion H.

         destruct c; simpl in *; eauto. destruct i0; inversion H. destruct ( eval_op e None op); simpl in *; inversion H; eauto. destruct t0; simpl in *; eauto; inversion H3. destruct v; simpl in *. destruct ( eval_op e (Some t0) v); simpl in *; eauto; inversion H. destruct c; inversion H. destruct t0; simpl in *; inversion H. destruct v; simpl in *; eauto. destruct (eval_op e (Some t0) v); simpl in *; inversion H. destruct c; simpl in *; eauto; inversion H. destruct t0; simpl in *; eauto; inversion H. destruct  v; simpl in *; eauto. destruct ( eval_op e (Some t0) v); inversion H. Qed.


  Lemma test2 : forall s1 s2 b,  step_rel b s1 s2 -> exists t, env_of s1 = t ++ (env_of s2).
  Proof. intros. induction H. exists nil. eauto. inversion IHstep_rel; subst. unfold env_of in *. destruct s3. simpl in *. destruct p. destruct s1. simpl in *. destruct p0. simpl in *. destruct s2. simpl in *. unfold fetch_local_instr in *. unfold incr_local_pc in *. unfold block_to_cmd in *. destruct b. simpl in *. destruct p1.
         simpl in *. unfold blk_term_id in *. simpl in *. destruct blk_term. simpl in *. unfold pc_of in *. simpl in *. destruct p. simpl in *. destruct ( decide (i = pt)); simpl in *; eauto.
destruct t; simpl in *; eauto; inversion H0. destruct v. destruct ( eval_op e (Some t) v); simpl in *; eauto. inversion H0. inversion H0.
destruct ( find_instr blk_code pt i); simpl in *; eauto; inversion H0. destruct p. simpl in *. destruct c; simpl in *; eauto; inversion H0. destruct o; simpl in *; eauto; inversion H0. destruct pt; simpl in *; eauto; inversion H0. destruct i0; simpl in *; eauto; inversion H0. destruct (eval_op e None op); simpl in *; eauto; inversion H0.
unfold add_env in *. rewrite H1. exists ((id, v) :: x); simpl in *; eauto.
destruct t0; simpl in *; eauto; inversion H0. destruct v; simpl in *; eauto. destruct ( eval_op e (Some t0) v); simpl in *; eauto; inversion H0. Qed.
Print instr.

Print fetch_local_instr.



SearchAbout Path.
Print reachable.
Print Path.

Definition exists_path (b:block) (v1 v2:instr_id) := exists p, Path b v1 v2 p.

Lemma incr_local_pc_implies_local_instr : forall b v0 v3, incr_local_pc b v0 = Some v3 -> exists c, fetch_local_instr b v0 = Some c.
Proof. intros. unfold incr_local_pc, fetch_local_instr in *. destruct ( block_to_cmd b v0); simpl in *; eauto.
       +destruct p; eauto.
       +inversion H.
Qed.


       
Lemma edge_pt_exists : forall b v0 v3, pt_exists b v3 -> edge_pt b v0 v3  -> exists t, Path b v0 v3 t.
Proof. intros. inversion H0. subst. assert (Path b v0 v0 (cons v0 nil)). constructor. apply incr_local_pc_implies_local_instr in H1. unfold pt_exists. eauto. eapply path_cons in H2; eauto. Qed.


Lemma edge_path_exists : forall b v1 v2 v3, pt_exists b v3 -> (exists t : seq instr_id,
        Path b v1 v2 t) -> edge_pt b v2 v3 -> exists t, Path b v1 v3 t.
Proof. intros. induction H0. induction H0; eauto.  Qed.

Lemma commut_path : forall b v1 v2 v3, (exists t, Path b v1 v2 t) -> (exists t, Path b v2 v3 t) -> (exists t, Path b v1 v3 t).
Proof. intros. inversion H. inversion H0. induction H2. eauto. apply IHPath in H.
 eapply edge_path_exists in H3. apply H3. inversion H. exists x0. eauto. apply H4.
 exists vs. apply H2. auto. Qed.


Lemma reachable_from_beg : forall b v1 v2, reachable b v1 -> exists_path b v1 v2 -> reachable b v2.
Proof. intros. unfold reachable in *. unfold exists_path in *. eapply commut_path. apply H. apply H0. Qed.
Print SDom.


Print pt_exists.





Definition dfs_uid (pt:instr_id) :=
  match pt with
  | IId id => True
  | IVoid _ => False
  end.



Definition  insn_at_pc (b:block) (pt:instr_id) := exists c, fetch_local_instr b pt = Some c.

Print wf_block.




(*

  Definition def_at_pc (g:Cfg.t) (p:pc) (uid:uid) : Prop :=
    exists c, insn_at_pc g p (uid, c) /\ defs_uid (uid, c). 
*)(*  (** *** Well-formed states *)

  (** We have to extend well-formedness definitions to include all components of
  the Vminus state. *)

  (** The local environment is well-formed at a given program point [p] when it
  contains a binding for every [uid] whose definition strictly dominates [p].
  This is the property that ensures "scope safety" for the SSA program.
  *)
  
(*  Definition uid_sdom_pc (g:Cfg.t) (uid:uid) (p:pc) : Prop :=
    exists p', def_at_pc g p' uid /\ SDom g p' p.
*)
  Definition wf_loc (g:Cfg.t) (p:pc) (loc:loc) : Prop :=
  forall uid, uid_sdom_pc g uid p -> exists n, loc uid = Some n.
 *)

(*  Definition wf_pc (g:cfg) (p:pc) : Prop :=
    let (l, n) := p in
    exists is i, In (l, is) (snd g) /\ Nth i is n.
*)

(*  Definition insn_at_pc (g:cfg) (p:pc) (i:insn) : Prop :=
    let (l, n) := p in
    exists is, In (l, is) (snd g) /\ Nth i is n.
 *)


(*SUCC_PC GRAPH RELATION*)

(*  Lemma dom_step : forall g v1 v2,
81	    Mem g v2 -> Succ g v1 v2 -> forall v', SDom g v' v2 -> Dom g v' v1.
…	*)

(*  Lemma wf_loc_succ : forall g p1 p2 loc uid n c,
   wf_prog g ->
   wf_pc g p2 ->
   insn_at_pc g p1 (uid, c) ->
   succ_pc g p1 p2 ->
   wf_loc g p1 loc ->
   wf_loc g p2 (update loc uid (Some n)).
  Proof.
    intros. red; intros. destruct (Uid.eq_dec uid0 uid). subst.
    rewrite Locals.update_eq; eauto. reflexivity.
    rewrite Locals.update_neq; eauto. apply H3.
    eapply uid_sdom_step; eauto. 
  Qed.

*)*)