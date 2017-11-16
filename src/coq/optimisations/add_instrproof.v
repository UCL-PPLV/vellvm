
Require Import ZArith List String Omega.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.optimisations.transform.
Require Import paco.
Require Import Vellvm.Memory.
Require Import Vellvm.Effects.
Require Import Vellvm.optimisations.add_instr.




Definition unroll (t:Trace ()) :=
match t with
  | Vis a => Vis a
  | Tau a b => Tau a b
end.


Lemma do_nothing_correct : forall mem st prog, trace_equiv (memD mem (sem prog st)) (memD mem (sem (prog_optimise prog) st)).
Proof. pcofix CIH.
intros.
pfold.


assert ((memD mem (sem prog st)) = unroll (memD mem (sem prog st))).
destruct (memD mem (sem prog st)); eauto.
induction prog. induction m_definitions.
-(*empty*) admit.
-(*mdefinitions*)destruct a. destruct df_instrs. destruct blks. 
  +assert ((memD mem
     (sem
        {|
        m_name := m_name;
        m_target := m_target;
        m_datalayout := m_datalayout;
        m_globals := m_globals;
        m_declarations := m_declarations;
        m_definitions := {|
                         df_prototype := df_prototype;
                         df_args := df_args;
                         df_instrs := {|
                                      CFG.init := init;
                                      CFG.blks := [];
                                      CFG.glbl := glbl |} |} :: m_definitions |}
        st)) = unroll (memD mem
     (sem
        {|
        m_name := m_name;
        m_target := m_target;
        m_datalayout := m_datalayout;
        m_globals := m_globals;
        m_declarations := m_declarations;
        m_definitions := {|
                         df_prototype := df_prototype;
                         df_args := df_args;
                         df_instrs := {|
                                      CFG.init := init;
                                      CFG.blks := [];
                                      CFG.glbl := glbl |} |} :: m_definitions |}
        st))). destruct (memD mem
     (sem
        {|
        m_name := m_name;
        m_target := m_target;
        m_datalayout := m_datalayout;
        m_globals := m_globals;
        m_declarations := m_declarations;
        m_definitions := {|
                         df_prototype := df_prototype;
                         df_args := df_args;
                         df_instrs := {|
                                      CFG.init := init;
                                      CFG.blks := [];
                                      CFG.glbl := glbl |} |} :: m_definitions |}
        st)); eauto.

rewrite H. simpl. admit.








  +(*full blks*) admit.
Admitted.
