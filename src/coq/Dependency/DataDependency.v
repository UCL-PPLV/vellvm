Require Import List.
Require Import Nat.
Require Import Bool.

Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.

Require Import Vellvm.Util.
Require Import Vellvm.Dependency.DEPIMP Vellvm.Dependency.SetTheory.

From mathcomp.ssreflect
Require Import ssreflect ssrbool fingraph fintype path
  ssrfun eqtype
  ssrnat seq.




(** Calculating Memory Read in a given expression**)

Fixpoint singleAexpRead (a:aexp) :=
  match a with
  | ANum _ => nil
  | AId b => b :: nil
  | APlus b c => singleAexpRead b ++ singleAexpRead c
  | AMult b c => singleAexpRead b ++ singleAexpRead c
  | AMinus b c => singleAexpRead b ++ singleAexpRead c
end.


Fixpoint singleBexpRead (c:bexp) :=
  match c with
  | BTrue => nil
  | BFalse => nil
  | BEq a b => singleAexpRead b ++ singleAexpRead a
  | BLe a b => singleAexpRead b ++ singleAexpRead a
  | BNot _ => nil
  | BAnd a b => singleBexpRead b ++ singleBexpRead a
end.




Fixpoint sMR (c:com) :=
  match c with
  | CAss a b => singleAexpRead b (**need to check*)
  | CIf a b c => singleBexpRead a ++ sMR b ++ sMR c
  | CWhile a b => singleBexpRead a ++ sMR b
  | CSkip => nil
  | CSeq a b => sMR a ++ sMR b
  | CFor a b c d => sMR d (*done*)
  | CFrom a b c => sMR c
end.



(** Calculating Memory Written in a given expression **)


Fixpoint sMW (c:com) :=
  match c with
  | CAss a _ => a :: nil (**need to check*)
  | CIf _ b c => sMW b ++ sMW c
  | CWhile _ b => sMW b
  | CSeq a b => sMW a ++ sMW b
  | CSkip => nil
  | CFor a b c d => a :: sMW d
  | CFrom a b c => sMW c
end.



Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').






Definition no_data_dependency_calc (a b: com) : bool := nilp ((sMR a u sMW b) n (sMW a u sMR b) n (sMW a u sMW b)).


Definition sampleSingleLineProgram := CAss W (APlus (ANum 1) (ANum 1)).
Definition sampleSingleLineProgram1 := CAss X (APlus (AId W) (AId W)).
Definition sampleSingleLineProgram2 := CAss Y (AMinus (AId W) (ANum 1)).
Definition sampleSingleLineProgram3 := CAss Z (AMult (AId Y) (ANum 5)).
Definition sampleSingleLineProgram4 := CAss W (APlus (AMinus (AId Z) (ANum 1)) (AId X)).


Eval compute in no_data_dependency_calc sampleSingleLineProgram sampleSingleLineProgram1.
Eval compute in no_data_dependency_calc sampleSingleLineProgram1 sampleSingleLineProgram2.
Eval compute in no_data_dependency_calc sampleSingleLineProgram1 sampleSingleLineProgram3.


Fixpoint DataDependencyInCommands (c: com) :=
  match c with
  | CSeq a b => (no_data_dependency_calc a b) || DataDependencyInCommands b
  | CIf _ a b => DataDependencyInCommands a || DataDependencyInCommands b 
  | CWhile _ _ => false
  | CAss _ _ => false
  | CFrom _ _ a => DataDependencyInCommands a
  | CFor _ _ _ a => DataDependencyInCommands a
  | CSkip => false
end.


Theorem test : forall a, cequiv (a) (CFrom 0 1 a).
Proof. split;intros.
-inversion H; subst.
  +apply E_FromEnd.