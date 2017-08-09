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

Theorem correct_empty_blocks : forall p, correct p add_empty_blocks.
Proof.
move=>p.
rewrite /correct; intros; subst a b.

move: H0; rewrite /optimize/=.
rewrite/mcfg_of_modul/=.
case X : (map_option _ _ )=>[v|]//; case=>Z.
subst  m_opt_semantic. 

have E : v = ??? (* semthing(m_definitions m) *)

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
