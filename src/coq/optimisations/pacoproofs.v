Require Import Setoid Program String.
Require Import paco.
Require Import ZArith.
Require Import Omega.
Require Import List.
Set Implicit Arguments.
Set Contextual Implicit.




CoInductive stream A :=
  | ccons : A -> stream A -> stream A.


(* Bisimulation proofs on CoInductive traces essentially work all the same way:
  1. Unroll either side by the required number of steps until the inner most value is equal
  2. Use constructors until the goal is found
  3. Apply CoInductive hypothesis.*)



(*These are the constructors required for step 2.*)
Inductive seq_gen A seq : stream A -> stream A -> Prop :=
  | seq_gen1 : forall n s1 s2 (R : seq s1 s2 : Prop), seq_gen seq (ccons n s1) (ccons n s2)
  | seq_gen2 : forall n s1 s2 (R : seq s1 s2 : Prop), seq_gen seq s1 (ccons n s2)
  | seq_gen3 : forall n s1 s2 (R : seq s1 s2 : Prop), seq_gen seq (ccons n s1) s2
.
Hint Constructors seq_gen.

(*essential for the folding*)
CoInductive seq A : stream A -> stream A -> Prop :=
  | seq_fold : forall s1 s2, seq_gen seq s1 s2 -> seq s1 s2.



(*The main comparison function*)
Definition seq' {A} (s1 s2:stream A) := paco2 (@seq_gen A) bot2 s1 s2.
Hint Unfold seq'.

(*Essential for Paco to work*)
Lemma seq_gen_mon: forall {X}, monotone2 (@seq_gen X). Proof. pmonauto. Qed.
Hint Resolve seq_gen_mon : paco.


CoFixpoint adder n := ccons n (adder (S n)).
CoFixpoint adder1 n := ccons n (adder1 (S (S n))).
(*Coq will not execute any function which it deems to not terminate.
However, it is possible to get 









Definition unroll_one A (s:stream A) :=
  match s with
  | ccons n s' => ccons n s'
  end.

Lemma unroll_one_eq : forall (s:stream nat), s = unroll_one s.
Proof.
  destruct s; auto.
Qed.






Theorem example' : forall n, seq' (adder n) (adder1 n).
Proof.
(*initialise*) pcofix CIH. intros. pfold.
(*useful*) assert (adder1 n = unroll_one (adder1 n)) by ((destruct (adder1 n)); eauto).
(*unfold each side once*) rewrite unroll_one_eq; simpl; rewrite H; simpl.
(*accumulate*) constructor. left. pfold.
(*pick the left side to unfold*) rewrite unroll_one_eq; simpl.
(*accumulate*) constructor.
(*finish*) right. apply CIH.
(*No guardedness checking*)
Qed.





(*Proving optimisations on a strict subset of VELLVM*)

Definition string_bool (a b: string) :=
if string_dec a b then true else false.




(*A variable id is represented as a string*)
Definition variable_id := string.

(*An instruction id is represented as a nat*)
Definition instr_id := nat.



(*Our language will have identifiers and natural numbers*)
Inductive Expr (a : Set) : Set :=
   | VALUE_Ident : variable_id -> Expr a
   | VALUE_Nat : nat -> Expr a
.


Inductive value : Set :=  SV : Expr value -> value.





(* There will be 4 instructions:
  -IfGoto: If the evaluation of the value is equal to 1, then the program branches to the first instruction.
  -GoTo: The equivalent of a skip instruction, the program simply branches onto the next instruction
  -Asn: The assignment of value to the variable id, followed by a branch to instr_iod
  -Term: Terminating with the value stored at S*)
Inductive instruction :=
  | IfGoto : value -> instr_id -> instr_id -> instruction
  | Asn : variable_id -> value -> instr_id -> instruction
  | Goto : instr_id -> instruction
  | Term : string -> instruction
.


(*The state is a combination of a program counter (referencing the current instruction) 
  and a memory represented as a list mapping variable ids to values*)


Definition env := list (variable_id * value).

(*The program by default starts with an empty memory*)
Definition empty_env : env := nil.

Definition pc := nat.

(*The program by default starts on instruction 0*)
Definition start_pc : pc := 0.

(*A program is defined as a list of tuplets composed of an instruction id and instruction.*)
Definition program := list (instr_id*instruction).
Definition state := (env * pc)%type.

(*The start state is a combination of an empty memory starting on the default instruction*)
Definition start_state : state := (empty_env, start_pc).


(*These are some useful functions for interacting with the memory*)


(*Changes variable_id in env with value a. If the variable id doesn't exist in the memory, then it is added*)
Fixpoint change_var (e:env) (v:variable_id) (a:value) : env :=
match e with
 | nil => cons (v, a) nil
 | ((vary, ae)::endtail)%list => match (string_bool vary v) with
                       | true => cons (vary,a) endtail
                       | false => cons (vary,ae) (change_var endtail v a)
                       end
end.

(*Fetches instruction id in program p. Returns None, if there instruction cannot be found*)
Fixpoint fetch_instr (p:program) (i:instr_id) : option instruction :=
match p with
  | nil => (None)
  | ((vary, ae)::endtail)%list => match beq_nat vary i with
                            | true => Some ae
                            | false => fetch_instr endtail i
                            end
end.

(*Fetches the value of the variable id in memory*)
Fixpoint fetch_var (e:env) (var:variable_id) : option value :=
match e with
  | nil => None
  | ((vary, ae)::endtail)%list => match (string_bool vary var) with
                            | true => Some ae
                            | false => fetch_var endtail var
                            end
end.


Fixpoint remove_var (e:env) (var:variable_id) : env :=
match e with
  | nil => e
  | ((vary, ae)::endtail)%list => match (string_bool vary var) with
                            | true => endtail
                            | false => remove_var endtail var
                            end
end.


(*In this language, events either symbolise termination or an error*)
Inductive event :=
  | Error
  | Finish (n:value)
.


CoInductive trace A :=
  | Vis (e:event)
  | Tau (a:A) (t:trace A)
.





Definition eval_expr {A:Set} (f:env -> A -> option value) (e:env) (o:Expr A) :=
match o with
  | VALUE_Ident s => fetch_var e s
  | VALUE_Nat n =>  Some (SV (VALUE_Nat n))
end.


Fixpoint eval_op (e:env) (o:value) :=
match o with
  | SV o' => eval_expr eval_op e o'
end.




Inductive transition X :=
  | Continue (s:X)
  | Obs (m:event)
.

Definition term_execute (var:string) (s:state) : transition state :=
let (e, pc) := s in
match (fetch_var e var) with
  | Some a => Obs (Finish a)
  | None => Obs (Error)
end.


Definition comparison_with_one (o:value) (e:env) : bool :=
match (eval_op e o) with
  | Some (SV (VALUE_Nat 1)) => true
  | _ => false
end.



Definition IfGoto_execute (b:value) (var1 var2:nat) (s:state) : transition state :=
let (e, pc) := s in
match (comparison_with_one b e) with
  | false => Continue (e, var2)
  | true => Continue (e, var1)
end.


Definition Goto_execute (n:nat) (s:state) : transition state :=
let (e, pc) := s in
Continue (e, n).


Definition asn_execute (var:string) (a:value) (s:state) (next:nat) : transition state :=
let (e, pc) := s in
Continue ((change_var e var a), next).



Definition execute_instruction (a:instruction) (s:state) : transition state :=
let (e, pc) := s in
match a with
| Asn var val next => asn_execute var val s next
| IfGoto cond var1 var2 => IfGoto_execute cond var1 var2 s
| Goto next => Goto_execute next s
| Term var => term_execute var s
end.


Definition stepD (p:program) (s:state) : transition state :=
let (env, pc) := s in
match (fetch_instr p pc) with
  | Some a => execute_instruction a s
  | None => Obs (Error)
end.

CoFixpoint step_sem (p:program) (s:state) : trace state := 
match (stepD p s) with
  | Continue s' => Tau s (step_sem p s')
  | Obs s' => Vis s'
end.






Inductive trace_gen A traceq : trace A -> trace A -> Prop :=
  | trace_gen1 : forall n s1 s2 (R : traceq s1 s2 : Prop), trace_gen traceq (Tau n s1) (Tau n s2)
  | trace_gen2 : forall n s1 s2 (R : traceq s1 s2 : Prop), trace_gen traceq s1 (Tau n s2)
  | trace_gen3 : forall n s1 s2 (R : traceq s1 s2 : Prop), trace_gen traceq (Tau n s1) s2
  | trace_gen4 : forall n, trace_gen traceq (Vis n) (Vis n).
Hint Constructors trace_gen.


CoInductive traceq A : trace A -> trace A -> Prop :=
  | traceq_fold : forall s1 s2, trace_gen traceq s1 s2 -> traceq s1 s2.



Definition traceq' {A} (s1 s2:trace A) := paco2 (@trace_gen A) bot2 s1 s2.
Hint Unfold seq'.
Lemma traceq_gen_mon: forall {X}, monotone2 (@trace_gen X). Proof. pmonauto. Qed.
Hint Resolve traceq_gen_mon : paco.



(*Proving no optimisation is correct*)
Definition no_opt (p:program) := p.

Definition tunf A (s:trace A) :=
  match s with
  | Vis a => Vis a
  | Tau a b => Tau a b
  end.

Lemma tunf_eq : forall (s:trace state), s = tunf s.
Proof.
  destruct s; auto.
Qed.






Lemma no_opt_correct: forall n s, traceq' (step_sem n s) (step_sem (no_opt n) s).
Proof. unfold no_opt. pcofix CIH. intros; pfold.
rewrite tunf_eq. simpl. destruct (stepD n s). simpl. constructor. right. auto. 
rewrite tunf_eq. simpl. constructor. Qed.




(*ADDING AN EMPTY INSTRUCTION*)
Require Import ZArith.


(*Instructions are defined by an instruction id, so we want to find the highest number id*)
Fixpoint max (n:nat) (l:list (instr_id*instruction)) :=
match l with
  | nil => n
  | (id,instr)::tl => if (leb id n) then max n tl else max id tl
end.


(*An unused instruction id, will be the first after the highest*)
Definition get_unused_instr (l:list (instr_id*instruction)) := max 0 l + 1.



(*The optimisation adds an unused instruction to the end of the program. This instruction isn't accessed, and branches to another unused instruction*)
Definition optimise (p:program) := 
let maxinstr := get_unused_instr p in p ++ [(maxinstr, Goto (maxinstr + 1))].





(*Useful lemmas*)
Definition fetch_in_two (i:instr_id) (p p1:program) :=
match fetch_instr p i with
  | Some a => Some a
  | None => match fetch_instr p1 i with
            | Some b => Some b
            | None => None
            end
end.




Lemma fetch_in_two_eq: forall i p p1, fetch_instr (p ++ p1) i = fetch_in_two i p p1.
Proof. intros. induction p. simpl.
  -induction p1. 
    *simpl. unfold fetch_in_two. simpl. auto.
    *simpl. unfold fetch_in_two. simpl. destruct a. destruct (i0 =? i). auto. auto.
  -induction p1.
    *simpl. unfold fetch_in_two. simpl. destruct a. destruct (i0 =? i). auto. auto.
    *simpl. unfold fetch_in_two. simpl. destruct a. destruct (i0 =? i). auto. auto.
Qed.



Lemma simple: forall a, a =? a +1 = false.
Proof. intros. induction a. simpl. auto. simpl. auto. Qed.



Print start_state.

Lemma optimise_correct:  forall n s, traceq' (step_sem n s) (step_sem (optimise n) s).
Proof. 
 pcofix CIH. intros. pfold.
induction n. 
(*Empty program*)
  - rewrite tunf_eq. simpl. assert (step_sem (optimise []) s = tunf (step_sem (optimise []) s)).
destruct (step_sem (optimise []) s); eauto. rewrite H. simpl. clear H.
unfold stepD. destruct s. simpl.
unfold optimise. unfold get_unused_instr. unfold max. destruct p. constructor. destruct p. constructor.
simpl.
assert ((step_sem [(1, Goto 2)] (e, 2)) = tunf ((step_sem [(1, Goto 2)] (e, 2)))).
destruct ((step_sem [(1, Goto 2)] (e, 2))); auto. rewrite H. simpl. auto. auto.
  -rewrite tunf_eq. simpl. assert ((step_sem (optimise (a :: n)) s) = tunf (step_sem (optimise (a :: n)) s)). destruct (step_sem (optimise (a :: n)) s); eauto.
rewrite H. clear H. simpl. unfold stepD. destruct s. simpl. rewrite fetch_in_two_eq. destruct a. unfold fetch_in_two.
destruct (i =? p).
    (*Both programs are in unaltered instructions.*)
   *destruct i0.
    +destruct (comparison_with_one v e). constructor. right. auto. constructor. right. auto.
    +constructor. right. auto.
    +constructor. right. auto.
    +destruct (fetch_var e s); auto.

   *unfold fetch_in_two. simpl. destruct (fetch_instr n p). destruct i1.
    +destruct (comparison_with_one v e). constructor. right. auto. constructor. right. auto.
    +constructor. right. auto.
    +constructor. right. auto.
    +destruct (fetch_var e s); auto.
    (*new instruction added*)
    +unfold get_unused_instr. destruct (max 0 ((i, i0) :: n) + 1 =? p).
(*New instruction passing through optimised program*)
{ 
remember (e, max 0 ((i, i0) :: n) + 1 + 1) as state.
remember (optimise ((i, i0) :: n)) as prog. 
assert ((step_sem prog state) = tunf (step_sem prog state)). destruct (step_sem prog state); eauto. rewrite H. clear H. simpl.
unfold stepD. subst. remember ((i, i0) :: n) as list.
(* Fetch instruction is asking for an instruction with a +2 id than the instruction with the highest instruction id.
Optimise adds an instruction with +1 id than list. Obviously fetch_instr should return null, then the proof is trivial*)

assert (fetch_instr (optimise list) (max 0 list + 1 + 1) = None). admit.
rewrite H. constructor. constructor. pfold. constructor.
}
    (*new instruction not found*)
constructor. Admitted.