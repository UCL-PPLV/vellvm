From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.
Require Import paco.

Require Export Vellvm.ReasoningFramework.OptimisationHints.

Require Import ZArith List String Omega Bool.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.Ollvm_ast Vellvm.AstLib Vellvm.CFGProp Vellvm.CFG Vellvm.StepSemantics Vellvm.Ollvm_ast.
Import ListNotations.





Print definition.

Definition emptyblock := [mk_block (Anon 1) nil nil (IVoid 0, TERM_Ret_void)].

Print emptyblock.

Print concat.
Definition add_empty_blocks (d:definition (list block)) := 
  {|
    df_prototype   := (df_prototype d);
    df_args        := (df_args d);
    df_instrs      := cat (df_instrs d) emptyblock;
  |}.



Print definition.


Print related_effect_refl.

Definition partresult (x:definition (seq.seq block)) (m:modul (seq.seq block)) : cfg := {|
               init := match df_instrs x with
                        | [::] => Raw 1
                        | b :: _ => blk_id b
                      end;
               blks := df_instrs x ++ emptyblock;
               glbl := ((map ident_of (m_globals m) ++
                         map ident_of (m_declarations m) ++
                         map ident_of
                           [seq add_empty_blocks i | i <- m_definitions m]) ++
                        map [eta ID_Local] (df_args x))%list |}.

Definition fullresult (m:modul (seq.seq block)) (x:definition (seq.seq block)) : definition cfg :=
{|
             df_prototype := df_prototype x;
             df_args := df_args x;
             df_instrs := partresult x m;
|}.




Theorem firststep : forall (i : nat) (x' : definition cfg) v (m:modul (seq block)) (x: definition (seq block)),
   ( Some x' = Some (fullresult m x)) /\ nth_error (m_definitions m) i = Some x /\ nth_error v i = Some x' -> (nth_error v i = Some x' <->
    (exists x : definition (seq block),
       nth_error (m_definitions m) i = Some x /\
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
               glbl := ((List.map ident_of (m_globals m) ++
                         List.map ident_of (m_declarations m) ++
                         List.map ident_of
                           [seq add_empty_blocks i | i <- m_definitions m]) ++
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
       end = Some x')).
Proof. move => i x' v m x [A [B C]] => //. split; intros => //. exists x. split => //. 
rewrite /fullresult/= in A. rewrite /partresult/= in A. 
 destruct df_instrs => //. 
 Qed.




Theorem remove_some_def_cfg : forall (a b : definition cfg), Some a = Some b <-> a = b.
Proof. move => a b; split; move => H; inversion H => //. Qed.

Theorem exists_m_def_nth_error:
  forall (m : modul (seq block)) (i : nat) (x : definition (seq block)),
  nth_error (m_definitions m) i = Some x ->
  exists x0 : definition (seq block), nth_error (m_definitions m) i = Some x0.
Proof. move => m i x H; exists x => //. Qed.




Theorem secondstep : forall x' (m:modul (seq block)) (x: definition (seq block)) i v, (v = map (fullresult m) (m_definitions m))  -> 
(x' = (fullresult m x) /\ nth_error (m_definitions m) i = Some x  /\ nth_error v i = Some x')
.
Proof. move => x' m x i v H. split; try split => //. move => //.
 destruct x. rewrite /fullresult/= in H. rewrite /partresult/= in H. rewrite /fullresult/=. rewrite /partresult/=. inversion H. 
Admitted.




Theorem correct_empty_blocks : forall p, correct p add_empty_blocks.
Proof.
move=>p.
rewrite /correct; intros; subst a b.

move: H0; rewrite /optimize/=.
rewrite/mcfg_of_modul/=.
case X : (map_option _ _ )=>[v|]//; case=>Z.
subst  m_opt_semantic. 
rewrite map_option_map in X.

Search _ (map_option).
move/map_option_nth: X=>/=X.
rewrite /globals/= in X.

Print nth_error.
Admitted.
(*
have E : v = ??? (* semthing (m_definitions m) *)

               [seq {|  df_prototype := df_prototype d; df_args := df_args d; df_instrs := a |}
               | i <- m_definitions m].

rewrite /map_option in X.

move: v m_semantic m_opt_semantic Z X H. 

move: X.


case X: (map_option _ _)=>//.

Search _ (Some _).

intros. unfold correct. intros. induction m. unfold add_empty_blocks in H1. 
subst a b.

       induction m_definitions. simpl in *.
move: H0; rewrite /optimize H; case=>H0.  
rewrite H0 in H1.  rewrite <- H2. rewrite <- H1. auto.
rewrite -H1 -H2 in IHm_definitions *.
apply: IHm_definitions=>//.
- rewrite -H. rewrite/mcfg_of_modul/=.


rewrite /optimize/= in IHm_definitions.
Admitted.
*)
