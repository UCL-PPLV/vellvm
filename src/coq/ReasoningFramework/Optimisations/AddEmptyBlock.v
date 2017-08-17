
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



Definition new_init (d : definition (seq block)) :=
match (df_instrs d) with
  | [::] => Some (Raw 1)
  | b :: _ => Some (blk_id b)
end.

Definition Smallfunction m x := (
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



Definition new_init_v1 (d : definition (seq block)) :=
match (df_instrs d) with
  | [::] =>  (Raw 1)
  | b :: _ =>  (blk_id b)
end.


Definition Smallfunction1 m x := 
             {|
             df_prototype := df_prototype x;
             df_args := df_args x;
             df_instrs := {|
               init := new_init_v1 x;
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


(*
Definition Smallfunction2 m x := 
           Some (Smallfunction1 m x).

Theorem Smallfunction_equiv_2_3 : forall m v, map (Smallfunction1 m) (m_definitions m) = v <-> map_option (Smallfunction2 m) (m_definitions m) = Some v.
Proof. move => m v. split; intros. destruct m. simpl. 
(*
rewrite /Smallfunction3/= in H.
rewrite /Smallfunction2/=.
rewrite /Smallfunction3/=.
rewrite /add_empty_blocks/=.
rewrite /new_init_v1/=.
rewrite /new_init_v1/= in H.
rewrite /add_empty_blocks/= in H. simpl. simpl in *.
rewrite /map_option/=.
 simpl. 
destruct m_definitions; simpl in H => //. 
inversion H. auto.
simpl. simpl in H.
destruct d. simpl. simpl in *.
destruct df_instrs. simpl. simpl in H.   
*)
Admitted.
*)



Theorem remove_some_definition_definition_cfg : forall (a b: definition cfg), Some a = Some b <-> a = b.
Proof. move => a b => //. split; move => H; inversion H => //. Qed.

Theorem remove_some_definition_definition_cfg1 : forall (a b: seq (definition cfg)), Some a = Some b <-> a = b.
Proof. move => a b => //. split; move => H; inversion H => //. Qed.



Theorem eq_in_option_map : forall a (f1 : definition (seq block) -> option (definition cfg)) (f2 : definition (seq block) -> (definition cfg)) s v,
      f1 a = Some (f2 a) -> (map_option f1 s = Some v <-> map f2 s = v).
Proof. Admitted.




Theorem function_equiv : forall m x v,  Smallfunction1 m x = v <->  Smallfunction m x = Some v.
Proof. move => m x v. 
rewrite /Smallfunction/=.
rewrite /init_of_definition/=.
split; move => H; rewrite /Smallfunction1/= in H;
rewrite /new_init_v1/= in H.
induction x =>//. simpl. simpl in *. induction df_instrs => //. simpl => //. apply remove_some_definition_definition_cfg => //.
simpl. simpl in * => //. apply remove_some_definition_definition_cfg => //.
rewrite /Smallfunction1/=;
rewrite /new_init_v1/=. 
induction x => //. induction df_instrs => //. simpl in *; simpl. apply remove_some_definition_definition_cfg in H => //. simpl. simpl in *.
apply remove_some_definition_definition_cfg in H => //. Qed.

Print map_option.



Theorem map_equiv : forall m v, (map_option (Smallfunction m) (m_definitions m) = Some v <-> map (Smallfunction1 m) (m_definitions m) = v).
Proof. Admitted.



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
apply map_equiv in X.
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
