Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.transform.
Require Import Vellvm.optimisations.paco_util.
Require Import Vellvm.optimisations.step_trace.
Require Import Vellvm.optimisations.StaticAnalysis.static_analysis.
Require Import Vellvm.optimisations.SSA_semantics.

Require Import Vellvm.DecidableEquality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat.


(*An optimisation takes in a program counter, the overall program and an instruction and returns a fully formed line of code*)

Definition opt := pc -> mcfg -> (instr_id * instr) -> instr.






Fixpoint code_opt (o:opt) (m:mcfg) (c:code) (bk:block_id) (fn:function_id) : code :=
  match c with
  | nil => nil
  | (iid, ins) :: tl => (iid, (o (mk_pc fn bk iid) m (iid, ins))) :: code_opt o m tl bk fn
  end.



Definition block_opt (o:opt) (m:mcfg) (fn:function_id) (b:block) : block := mk_block (blk_id b) (blk_phis b) (code_opt o m (blk_code b) (blk_id b) fn) (blk_term b).


Definition list_block_opt (o:opt) (m:mcfg) (fn:function_id) (l:list block) : list block := map (block_opt o m fn) l.


Definition cfg_opt (o:opt) (m:mcfg) (fn:function_id) (c:cfg) : cfg := mkCFG (init c) (list_block_opt o m fn (blks c)) (glbl c).


Definition function_id_of_dec (d:declaration) : function_id := (dc_name d).


Definition definition_cfg_opt (o:opt) (m:mcfg) (d:definition cfg) : definition cfg := mk_definition cfg (df_prototype d) (df_args d) (cfg_opt o m (function_id_of_dec (df_prototype d)) (df_instrs d)).


Definition list_def_cfg_opt (o:opt) (m:mcfg) (d:list (definition cfg)) : list (definition cfg) := map (definition_cfg_opt o m) d.


Definition modul_opt (o:opt) (m:mcfg) : mcfg := mk_modul cfg (m_name m) (m_target m) (m_datalayout m) (m_globals m) (m_declarations m) (list_def_cfg_opt o m (m_definitions m)).



Definition find_instr_helper cd p t (o:opt) m bk fn :=
  match find_instr cd p t with
  | Some (CFG.Step ins, ret) => Some (CFG.Step (o (mk_pc fn bk p) m (p, ins)), ret)
  | rest => rest
              
  end.


Lemma find_instr_helper_equiv : forall cd o m fn bk p t,find_instr (code_opt o m cd bk fn) p t  = find_instr_helper cd p t o m bk fn.
Proof. intros. unfold  find_instr_helper. simpl in *. induction cd; simpl in *; auto.
       destruct a. simpl in *. destruct ( decide (p = i)); subst. destruct cd. simpl in *.
       auto. simpl. destruct p. simpl in *. auto. auto. Qed.



Definition block_to_cmd_helper b p (o:opt) m fn bk :=
  match block_to_cmd b p with
    | Some (CFG.Step ins, ret) =>  Some (CFG.Step (o (mk_pc fn bk p) m (p, ins)), ret)
    | rest => rest
  end.


Lemma block_to_cmd_helper_equiv : forall (o:opt) m fn p b,  block_to_cmd (block_opt o m fn b) p = block_to_cmd_helper b p o m fn (blk_id b).
Proof. intros. unfold block_to_cmd_helper. unfold block_to_cmd in *. simpl in *. unfold blk_term_id in *.
       simpl in *. destruct b; simpl in *. destruct blk_term; simpl in *. destruct (decide (i = p)).
       eauto. rewrite  find_instr_helper_equiv. eauto. Qed.




Definition  find_block_helper l blk_id o m fn :=
  match find_block l blk_id with
  | Some a => Some (block_opt o m fn a)
  | None => None
  end.


Lemma find_block_helper_equiv : forall l o m fn blk_id, find_block (list_block_opt o m fn l) blk_id  = find_block_helper l blk_id o m fn.
Proof. intros. unfold find_block_helper. simpl in *. induction l.
       +simpl in *. auto.
       +simpl in *. destruct a; simpl in *. destruct (decide (blk_id0 = blk_id)); eauto.
        clear IHl.  induction l; simpl in *. auto. simpl in *.
        destruct (decide (Ollvm_ast.blk_id a = blk_id)); eauto. Qed.




Definition find_func_helper o m fn :=
  match find_function m fn with
  | Some a => Some ( definition_cfg_opt o m a)
  | None => None
  end.



Lemma find_func_helper_equiv : forall o m fn, find_function (modul_opt o m) fn  = find_func_helper o m fn.
Proof. unfold find_func_helper. unfold modul_opt. unfold find_function. simpl in *. intros.
       destruct m; simpl in *. unfold list_def_cfg_opt. simpl in *.
       induction m_definitions; simpl in *. eauto. simpl in *. unfold find_defn.
       simpl in *. unfold definition_cfg_opt. simpl in *.  unfold AstLib.ident_of.
       simpl in *. unfold AstLib.ident_of_definition. simpl in *.
       destruct (decide (AstLib.ident_of (df_prototype a) = ID_Global fn)).
       eauto. simpl in *. clear IHm_definitions. remember ( a :: m_definitions).
       clear Heql. induction m_definitions. simpl in *. auto. simpl in *.
       destruct ( decide (AstLib.ident_of (df_prototype a0) = ID_Global fn)); eauto. Qed.



Definition fetch_helper o m p :=
  match fetch m p with
  | Some ((CFG.Step ins)) => Some (CFG.Step (o (mk_pc (fn p) (bk p) (pt p)) m (pt p, ins)))
  | rest => rest
  end.



Lemma find_function_equiv : forall m fn d, find_function m fn = Some d -> (function_id_of_dec (df_prototype d)) = fn.
Proof. intros. destruct m. simpl in *. induction m_definitions.
       +unfold find_function in *. simpl in *. inversion H.
       +unfold find_function in H. simpl in *. unfold find_defn in H. unfold AstLib.ident_of in *.
        unfold AstLib.ident_of_definition in H. unfold AstLib.ident_of in *.
        unfold AstLib.ident_of_declaration in *. simpl in *.
        destruct (decide (ID_Global (dc_name (df_prototype a)) = ID_Global fn)).
        inversion H; subst.  unfold function_id_of_dec. inversion e. auto. simpl in *.
        unfold find_function in IHm_definitions. simpl in *. apply IHm_definitions.
        clear IHm_definitions. clear n. rewrite H. eauto. Qed.



Lemma find_block_equiv : forall b blks bk, Some b = find_block blks bk -> blk_id b = bk.
Proof. intros. induction blks. simpl in *. inversion H. simpl in H. destruct a. simpl in *.
       destruct ( decide (blk_id = bk) ). subst. inversion H. subst. simpl in *. auto.
       apply IHblks. rewrite H. clear H. clear IHblks. induction blks. simpl in *. auto.
       simpl in *. destruct (decide (Ollvm_ast.blk_id a = bk)); eauto. Qed.




Lemma fetch_helper_equiv : forall o m p, fetch (modul_opt o m) p = fetch_helper o m p.
Proof.  unfold fetch_helper. intros. unfold fetch. simpl in *. destruct p. simpl in *. rewrite find_func_helper_equiv.
        unfold find_func_helper. simpl in *. remember ( find_function m fn).  destruct o0; eauto.
        symmetry in Heqo0. apply find_function_equiv in Heqo0.
        simpl in *. destruct d. simpl in *. unfold function_id_of_dec.  destruct df_instrs; simpl in *.
        destruct df_prototype; simpl in *. rewrite  find_block_helper_equiv. unfold find_block_helper.
        simpl in *. remember ( find_block blks bk). destruct o0; eauto. apply find_block_equiv in Heqo1.
        simpl in *. rewrite  block_to_cmd_helper_equiv. unfold block_to_cmd_helper.
        destruct ( block_to_cmd b pt); eauto. destruct p. destruct c; eauto.
        subst; eauto. Qed.


Lemma incr_pc_unaffected : forall o m p, incr_pc m p = incr_pc (modul_opt o m) p.
Proof. intros. unfold incr_pc. simpl in *. destruct p. rewrite find_func_helper_equiv. unfold find_func_helper.
       remember ( find_function m fn). destruct o0; eauto. destruct d. simpl in *. destruct df_instrs.
       simpl in *. unfold function_id_of_dec. simpl in *. destruct df_prototype. simpl in *.
       rewrite find_block_helper_equiv. unfold find_block_helper. simpl in *. remember (find_block blks bk).
       destruct o0; simpl in *; eauto. rewrite  block_to_cmd_helper_equiv. unfold block_to_cmd_helper.
       simpl in *. destruct (block_to_cmd b pt); eauto. destruct p. simpl in *. destruct c; eauto. Qed.


Lemma find_function_entry_unaffected : forall o m id0, (find_function_entry (modul_opt o m) id0) = (find_function_entry m id0).
Proof. intros. unfold find_function_entry; simpl in *. rewrite  find_func_helper_equiv. unfold find_func_helper. simpl in *. destruct ( find_function m id0); eauto. simpl in *. unfold function_id_of_dec. simpl in *. destruct d. simpl in *.  destruct df_instrs. simpl in *.

rewrite ( find_block_helper_equiv). unfold find_block_helper. simpl in *.
destruct ( find_block blks init); simpl in *; eauto. unfold blk_entry_id. simpl in *. 
destruct b; simpl in *. unfold blk_term_id in *; simpl in *. destruct blk_code. simpl in *. auto. simpl in *. destruct p. simpl in *. eauto. Qed.
       

Lemma jump_unaffected : forall o m fn bk br e s, jump (modul_opt o m) fn bk br e s =  jump m fn bk br e s.
Proof. intros. unfold jump; simpl in *. unfold find_block_entry in *; simpl in *.
       rewrite find_func_helper_equiv. unfold find_func_helper. destruct ( find_function m fn); eauto.
       simpl in *. destruct d; simpl in *. unfold function_id_of_dec. simpl in *. destruct df_instrs. simpl in *. rewrite find_block_helper_equiv. unfold find_block_helper. destruct (find_block blks br); eauto. unfold block_to_entry. simpl in *. unfold monad_fold_right. remember ( (fix
     monad_fold_right (A B : Type) (M : Type -> Type) (H : Functor M) 
                      (H0 : Monad) (f : A -> B -> M A) (l : seq B) 
                      (a : A) {struct l} : M A :=
       match l with
       | [::] => mret a
       | x :: xs => monad_fold_right A B M H H0 f xs a ≫= (fun y : A => f y x)
       end)). rewrite <- Heqp. destruct p; eauto. unfold blk_entry_pc. simpl in *. unfold blk_entry_id. simpl in *. destruct b. simpl in *. unfold blk_term_id. simpl in *. destruct blk_code; simpl in *; eauto. destruct p0; eauto. Qed.
 
(***************** function execution ******************)




Definition individual_step CFG pc insn e pc_next k := 
      match (pt pc), insn  with
      | IId id, INSTR_Op op =>
        do dv <- eval_op e None op;     
          Step (pc_next, add_env id dv e, k)

      | IId id, INSTR_Alloca t _ _ =>
        Obs (Eff (Alloca t (fun (a:value) =>  (pc_next, add_env id a e, k))))
                
      | IId id, INSTR_Load _ t (u,ptr) _ =>
        do dv <- eval_op e (Some u) ptr;     
          match dv with
          | DVALUE_Addr a => Obs (Eff (Load a (fun dv => (pc_next, add_env id dv e, k))))
          | _ => t_raise "ERROR: Load got non-pointer value" 
          end
            
      | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
        do dv <- eval_op e (Some t) val; (* TO SEE: Added new function *)
          (* CHKoh: do dv <- eval_op e val; *)
          do v <- eval_op e (Some u) ptr;
          match v with 
          | DVALUE_Addr a => Obs (Eff (Store a dv (fun _ => (pc_next, e, k))))
          |  _ => t_raise "ERROR: Store got non-pointer value" 
          end

      | _, INSTR_Store _ _ _ _ => t_raise "ERROR: Store to non-void ID" 
            
      (* NOTE : this doesn't yet correctly handle external calls or function pointers *)
      | pt, INSTR_Call (ret_ty, ID_Global fid) args =>
        do fnentry <- trywith ("stepD: no function " ++ (string_of fid)) (find_function_entry CFG fid); 
        let 'FunctionEntry ids pc_f := fnentry in
        do dvs <-  map_monad (fun '(t, op) => (eval_op e (Some t) op)) args;
          match pt, ret_ty with
              | IVoid _, TYPE_Void => Step (pc_f, combine ids dvs, (KRet_void e pc_next::k))
              | IId id, _ =>          Step (pc_f, combine ids dvs, (KRet e id pc_next::k))
              | _, _ => t_raise "Call mismatch void/non-void"
          end        
                
      | _, INSTR_Call (_, ID_Local _) _ => t_raise "INSTR_Call to local"

      | _, INSTR_Unreachable => t_raise "IMPOSSIBLE: unreachable" 

        (* Currently unhandled LLVM instructions *)
      | _, INSTR_Fence 
      | _, INSTR_AtomicCmpXchg 
      | _, INSTR_AtomicRMW
      | _, INSTR_VAArg 
      | _, INSTR_LandingPad => t_raise "Unsupported LLVM intsruction" 

      (* Error states *)                                     
      | _, _ => t_raise "ID / Instr mismatch void/non-void"
      end.

Print individual_step.
(**********+ correct **************)

Print mk_pc.
Print state.

(*Definition opt := pc -> mcfg -> (instr_id * instr) -> instr*)



Print individual_step.
Definition correct_instr (o:opt) (m:mcfg) :=
  forall fn bk id instr e (k:stack) pc_next (wf_prog: wf_program m) (sstate: sound_state m ((mk_pc fn bk id), e, k)),
    individual_step m (mk_pc fn bk id) (o (mk_pc fn bk id) m (id, instr)) e (mk_pc fn bk pc_next) k =  individual_step m (mk_pc fn bk id) instr e  (mk_pc fn bk pc_next) k.




Print finish_item.
Print individual_step.
Definition exec_code1 (mem:memory) (m:mcfg) (fn:function_id) (bk:block_id) (id:instr_id) (instr:instr) (pc_next:instr_id) (k:stack) (e:env) :=
  match (individual_step m (mk_pc fn bk id) (instr) e (mk_pc fn bk pc_next) k) with
  | Step s' => tauitem mem s'
  | Jump s' => tauitem mem s'
  | Obs o => match o with
             | Fin f => visitem mem (Fin f)
             | Err f => visitem mem (Err f)
             | Eff f => match mem_step f mem with
                        | inl _ => visitem mem (Err "err")
                        | inr (m', v, k) => tauitem m' (k v)
                        end
                          
                                
             end
               
 end    
.
Inductive eq_result : finish_item state -> finish_item state -> Prop :=
| tau_eq : forall mem s,  eq_result (tauitem mem s) (tauitem mem s)
| finish_eq : forall mem s, eq_result (visitem mem (Fin s)) (visitem mem (Fin s))
| err_eq : forall mem mem1 s s1, eq_result (visitem mem1 (Err s)) (visitem mem (Err s1))
.




Definition correct_instr1 (o:opt) (m:mcfg) :=
  forall mem fn bk id instr e (k:stack) pc_next (wf_prog: wf_program m) (sstate: sound_state m ((mk_pc fn bk id), e, k)),
    eq_result (exec_code1 mem m fn bk id instr pc_next k e)
              (exec_code1 mem m fn bk id (o (mk_pc fn bk id) m (id, instr)) pc_next k e).
