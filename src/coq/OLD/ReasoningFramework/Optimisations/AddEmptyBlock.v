
Require Import paco.

Require Export Vellvm.ReasoningFramework.OptimisationHints.

Require Import ZArith List String Omega Bool Ascii.
Require Import String Zcompare.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.

From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.

Require Import compcert.lib.Integers.

Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.



Print definition.

Definition emptyblock := [mk_block (Raw 1) nil nil (IVoid 0, TERM_Ret_void)].

Print emptyblock.

Print concat.
Definition add_empty_blocks (d:definition (list block)) := 
  {|
    df_prototype   := (df_prototype d);
    df_args        := (df_args d);
    df_instrs      := cat (df_instrs d) emptyblock;
  |}.
Print modul.


Definition original m v := ( map_option
      (fun x : definition (seq block) =>
       match
         match
           match (df_instrs x ++ emptyblock)%SEQ with
           | [::] => None
           | b :: _ => Some (blk_id b)
           end
         with
         | Some a =>
             Some
               {|
               init := a;
               blks := df_instrs x ++ emptyblock;
               glbl := (globals
                          {|
                          m_name := m_name m;
                          m_target := m_target m;
                          m_datalayout := m_datalayout m;
                          m_globals := m_globals m;
                          m_declarations := m_declarations m;
                          m_definitions := [seq add_empty_blocks i
                                              | i <- m_definitions m] |} ++
                        List.map [eta ID_Local] (df_args x))%list |}
         | None => None
         end
       with
       | Some a =>
           Some
             {|
             df_prototype := df_prototype x;
             df_args := df_args x;
             df_instrs := a |}
       | None => None
       end) (m_definitions m) = Some v).
Print m_definitions.
Definition Smallfunction m x:= (
       match
         match init_of_definition (add_empty_blocks x) with
         | Some a =>
             Some
               {|
               init := a;
               blks := df_instrs x ++ emptyblock;
               glbl := (globals
                          {|
                          m_name := m_name m;
                          m_target := m_target m;
                          m_datalayout := m_datalayout m;
                          m_globals := m_globals m;
                          m_declarations := m_declarations m;
                          m_definitions := [seq add_empty_blocks i
                                              | i <- m_definitions m] |} ++
                        List.map [eta ID_Local] (df_args x))%list |}
         | None => None
         end
       with
       | Some a =>
           Some
             {|
             df_prototype := df_prototype x;
             df_args := df_args x;
             df_instrs := a |}
       | None => None
       end).


Definition apply_small_function m v := map_option (Smallfunction m) (m_definitions m) = Some v.

Theorem original_to_smallfunction : forall m v, original m v <-> apply_small_function m v.
Proof. 
move => m v; split; move => H => //. Qed.




Definition Smallfunction1 m x := 
             {|
             df_prototype := df_prototype x;
             df_args := df_args x;
             df_instrs := {|
               init := match (df_instrs x) with
  | [::] =>  (Raw 1)
  | b :: _ =>  (blk_id b)
end;
               blks := df_instrs x ++ emptyblock;
               glbl := (globals
                          {|
                          m_name := m_name m;
                          m_target := m_target m;
                          m_datalayout := m_datalayout m;
                          m_globals := m_globals m;
                          m_declarations := m_declarations m;
                          m_definitions := [seq add_empty_blocks i
                                              | i <- m_definitions m] |} ++
                        List.map [eta ID_Local] (df_args x))%list |}|}.

Definition Smallfunction2 (c:definition cfg) := Some (c).

Definition applyfunction12 m v := map_option (fun t => (Smallfunction2 (Smallfunction1 m t))) (m_definitions m) = Some v.




Theorem experiment1 : forall m, (fun t => Smallfunction m t)  = (fun y => (Smallfunction2 (Smallfunction1 m y))) .
Proof. move => m. induction m. simpl. rewrite /Smallfunction2/=.
(*Insert old proof here*) 
 Admitted.



Theorem smallfunction_to_smallfunction12 : forall m v, apply_small_function m v <-> applyfunction12 m v.
Proof. move => m v. split;
 move => H.
rewrite /applyfunction12/=.
rewrite <- experiment1.
rewrite /apply_small_function/= in H. auto.
rewrite  /applyfunction12/= in H.
rewrite /apply_small_function/=.
rewrite <- experiment1 in H. auto. Qed.



Definition map_option_map_function m v := map_option (Smallfunction2) (List.map (Smallfunction1 m) (m_definitions m)) = Some v.


Theorem testetstestest  : forall x l, map_option (Smallfunction2) (List.map (Smallfunction1 x) l) = map_option (fun t => (Smallfunction2 (Smallfunction1 x t))) l. Proof.
move => x  l. rewrite map_option_map. auto. Qed.


Theorem smallfunction12_map_option_map : forall m v, applyfunction12 m v <-> map_option_map_function m v.
Proof. move => m v. rewrite /applyfunction12/=.
rewrite /map_option_map_function/=. rewrite map_option_map => //. Qed.




Theorem map_id : forall (l:seq (definition cfg)), map id l = l.
Proof. move => l. induction l => //. inversion IHl. eauto. induction a. simpl. rewrite IHl. rewrite IHl. eauto.
Qed.

Theorem Smallfunction_iden : forall l, map_option (Smallfunction2) l = Some l.
Proof. move => l. induction l; simpl. auto.
  -destruct (map_option Smallfunction2 l). simpl. inversion IHl. auto. auto. inversion IHl. Qed.
Print id.




Theorem map_option_to_id : forall m v, map_option_map_function m v <-> (List.map (Smallfunction1 m) (m_definitions m)) = v.
Proof. move => m v. split; move => H => //. rewrite /map_option_map_function/= in H. rewrite Smallfunction_iden in H. inversion H => //. 
rewrite /map_option_map_function/=. rewrite Smallfunction_iden. inversion H => //. Qed.





Theorem final_map : forall m v, original m v <-> (List.map (Smallfunction1 m) (m_definitions m)) = v.
Proof. move => m v; split; move => H. rewrite <- map_option_to_id. rewrite <- smallfunction12_map_option_map.
rewrite <- smallfunction_to_smallfunction12. rewrite <- original_to_smallfunction => //.
rewrite original_to_smallfunction. rewrite smallfunction_to_smallfunction12. rewrite smallfunction12_map_option_map.
rewrite map_option_to_id => //. Qed.



Theorem correct_empty_blocks : forall p, correct p add_empty_blocks.
Proof.
move=>p.
rewrite /correct; intros. rewrite <- H1. rewrite <- H2.

move: H0; rewrite /optimize/=.
rewrite/mcfg_of_modul/=.
case X : (map_option _ _ )=>[v|]//; case=>Z.
subst  m_opt_semantic. 
rewrite map_option_map in X.
rewrite /cfg_of_definition/= in X.
rewrite /init_of_definition/= in X.
apply final_map in X.
rewrite <- X.
destruct m; simpl in * => //;
induction m_definitions => //. 
rewrite /Smallfunction1/=.  apply remove_some in H. simpl in H. rewrite H. eauto.




induction m_definitions. 

rewrite/mcfg_of_modul/= in H. simpl in H.
rewrite /cfg_of_definition/= in H. simpl in H.
rewrite /init_of_definition/= in H. simpl in H.
induction a0. simpl in H. induction df_instrs. inversion H. simpl in H. apply remove_some in H. rewrite <- H.


(*

rewrite /Smallfunction1/=.
rewrite /new_init_v1/=. 
rewrite /add_empty_blocks/=.

rewrite /sem/=.
rewrite /globals/=.
pcofix CIH. simpl in *.
rewrite /step_sem/=.
rewrite /hide_taus/=. move => //.
pcofix CIH1.
rewrite /trace_map/= in CIH1. induction blks.*)
Admitted.
