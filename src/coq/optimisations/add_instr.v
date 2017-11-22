
Require Import ZArith.
Require Import List.
Require Import String Ascii.
Require Import Bool.
Require Import ZArith.Int.
Require Import Vellvm.CFG.
Require Import Vellvm.Ollvm_ast.
Require Import Vellvm.Classes.
Require Import ZArith List String Omega.
Require Import Vellvm.AstLib Vellvm.Ollvm_ast.
Require Import Vellvm.optimisations.wellformedSSA.
Require Import Vellvm.optimisations.EqNat.

From mathcomp.ssreflect
Require Import ssreflect ssrbool seq eqtype ssrnat fintype.



Require Import Equalities.
Import ListNotations.
Print instr_id.
Print raw_id.



(*Instr_id is of type raw_id*)

(*raw_id is an inductive object with three cases:
  -Name: used for string identifiers
  -Anon: used for anonymous identifiers
  -Raw: used for code generation


get_max function calculates the first unused UIS
*)


Fixpoint get_maximum (n:int) (c:code) :=
match c with
  | nil => n (*No more items*)
  | (IId (Raw iid),_)::tl =>if (Z.leb iid n) then get_maximum n tl else get_maximum iid tl (*When the item on the list is a raw iid*)
  | hd::tl => get_maximum n tl (*When the item on the list is not a raw id*)
end.



(*So that an instruction with a unique UID can be added, we need to find to find an unused value*)
Print block.
Print instr_id.
Definition get_terminator_iid (b:block) : Z :=
match b.(blk_term) with
  | (IId (Raw n), _) => n
  | (_, _) => Z0
end.


(*Find the largest instruction (which is either the terminator ID or an instruction from within the code) and adds 1 to it*)
Definition get_first_unused (b:block) : instr_id := IId (Raw (Z.add (get_maximum (get_terminator_iid b) (b.(blk_code))) 1)).

(*Useless instruction*)
Definition no_instr : instr := INSTR_Op (SV (VALUE_Null)).
Print block.

Definition optimise_block (b:block) := mk_block b.(blk_id) b.(blk_phis) (b.(blk_code)++[::(get_first_unused b, no_instr)]) b.(blk_term).


Print block_to_cmd.



Print find_instr.

(*find_instr = 
fix find_instr (cd : code) (p t : instr_id) {struct cd} :
  option (cmd * option instr_id) :=
  match cd with
  | [::] => None
  | (x, i) :: cd0 =>
      if decide (p = x)
      then Some (Step i, Some (fallthrough cd0 t))
      else find_instr cd0 p t
  end*)



Print fallthrough.

(*Some term_id*)


Definition find_instr_double (c d: code) (p t : instr_id) : option (cmd * option instr_id) :=
match (find_instr c p t) with
  | None => find_instr d p t
  | Some (Step i, Some tid ) => if decide (tid = t) then (Some (Step i, Some (fallthrough d t))) else Some (Step i, Some tid)
  | Some (Step i, None) => None
  | Some (Term _, _) => None
end.



Lemma remove_nil_r : forall (a: seq (instr_id * instr)), a = a ++ [::].
Proof. move => //a. induction a. simpl. auto. simpl. rewrite <- IHa. auto. Qed.

Lemma remove_nil_l : forall (a: seq (instr_id * instr)), a = [::] ++ a.
Proof. move => //a. Qed.


Lemma testtest : forall c d p t, find_instr ([::c] ++ d) p t = find_instr_double [::c] d p t.
Proof. 
intros. simpl. destruct c. simpl. unfold find_instr_double. simpl. destruct (decide (p = i)). simpl.
admit. auto. Admitted.


Definition test tid t i3 := 
if eqinstr_id tid t then Some (Step i3, Some t) else Some (Step i3, Some tid).

Lemma foralltest: forall tid t i3, test tid t i3 = Some (Step i3, Some tid). Admitted.

Lemma testtest1 : forall p p0 t, find_instr_double [::p] [::] p0 t = find_instr_double ([::]) ([::p]) p0 t.
Proof. intros. unfold find_instr_double. simpl. destruct p. simpl. destruct (decide (p0 = i)). simpl. admit. admit.
Admitted.

Lemma testtest3: forall t, eqinstr_id t t = true.
Proof. intros. induction t. simpl. admit. admit. Admitted.
Hint Rewrite testtest3.


Lemma not_eq_false : forall (t:instr_id), t <> t -> False.
Proof. intros. unfold not in H. apply H. auto. Qed.



Lemma testtest4 : forall c d p t, find_instr ([::c] ++ [::d]) p t = find_instr_double [::c] [::d] p t.
Proof. intros. induction d, c => //. rewrite /find_instr_double/=. simpl in *. destruct (decide (p = i)). simpl.
destruct (decide (t = t)). simpl. auto. simpl. assert (t = t) by auto. unfold not in n; apply n in H; inversion H.
auto.
Qed.

Lemma testtest5 : forall c d p t, find_instr ([::c] ++ d) p t = find_instr_double [::c] d p t.
Proof. induction d, c => //.
  +intros. unfold find_instr_double. simpl. destruct (decide (p = i)). simpl. destruct (decide (t = t)). simpl. auto. simpl. auto.
auto.
  +intros. unfold find_instr_double in *. simpl in *. unfold fallthrough in *.
destruct a. simpl in *. induction d. simpl in *. destruct (decide (p = i)).
destruct (decide (t = t)). simpl. auto. simpl. apply not_eq_false in n; inversion n.  auto.
simpl in *. destruct a. destruct (decide (p = i)). simpl in *.
destruct (decide (t = t)). simpl. auto. simpl. unfold not in n. assert (t = t) by auto. apply n in H. inversion H.
destruct (decide (p = i1)). simpl. auto.
destruct (decide (p = i3)). simpl in *. auto. auto.
Qed.

Lemma testtest6 : forall c p t,
find_instr (c ++ [::]) p t =
find_instr_double c [::] p t.
Proof. induction c => //. 
  + intros. simpl. destruct a. simpl. unfold find_instr_double. simpl. destruct (decide (p = i)).
simpl. destruct c. simpl. destruct (decide (t = t)).  simpl. auto. simpl. auto. destruct p0. simpl. destruct ((decide (i1 = t))). simpl. subst. auto. simpl. auto.
simpl. unfold find_instr_double in IHc. simpl in *. auto. Qed.


Lemma testtest7 : forall a c p t,
find_instr ((a::c) ++ [::]) p t =
find_instr_double (a::c) [::] p t.
Proof. intros. remember (a :: c) as D. rewrite testtest6. auto. Qed.


Definition testfunc1 d p t :=
match find_instr d p t with
| Some (Step i7, Some tid) =>
    if is_left (decide (tid = t)) then Some (Step i7, Some t) else Some (Step i7, Some tid)
| Some (Step i7, None) => None
| Some (Term _, _) => None
| None => None
end.



Lemma testtest8: forall d p t, find_instr d p t = testfunc1 d p t.
Proof. induction d => //. intros.
rewrite testtest5. simpl. unfold testfunc1, find_instr_double. simpl. destruct a. simpl.
destruct (decide (p = i)). simpl. destruct (decide (t = t)). simpl.
induction d. simpl in *. admit. simpl. destruct a. simpl in *. specialize (IHd t). subst.
admit. simpl. admit.
admit. Admitted.

Lemma testtest9 : forall c d p t, p \notin (map fst c) -> p \notin (map fst d) -> find_instr_double c d p t = find_instr_double (c ++ d) [::] p t.
Proof. induction c, d => //.
  +unfold find_instr_double. simpl. destruct p. simpl. intros. unfold fallthrough. simpl. destruct d.
simpl. destruct (decide (p = s)). simpl. admit. admit.
destruct p0. simpl. induction d. simpl. destruct (decide (p = s)).
simpl. unfold is_left. simpl. destruct (decide (s0 = t)). simpl. subst. auto.
destruct (decide (t = t)). simpl. auto. auto.
simpl. destruct (decide (s0 = t)). subst. destruct (decide (t = t)). auto. auto.
destruct (decide (s0 = t)). simpl. subst. destruct (decide (t = t)). auto. simpl. unfold negb in H0.
simpl in *. unfold not in n1. assert (t = t) by auto. apply n1 in H1. inversion H1.
rewrite e in H0. unfold negb in H0. simpl in *. unfold in_mem in H0. simpl in *. 
assert ((s == s) = true). admit. rewrite H1 in H0. simpl in H0. inversion H0.
destruct (decide (p = s0)). simpl. destruct (decide (t = t)). simpl. auto. simpl. auto.
auto. simpl in *. 
destruct (decide (p = s)). subst. unfold negb in H0. unfold in_mem in H0. simpl in *.
assert ((s == s) = true). admit. rewrite H1 in H0. simpl in *. inversion H0.
simpl in *. simpl in *.

destruct a. simpl in *.
destruct (decide (p = s0)). simpl in *. subst. unfold negb in H0. unfold in_mem in H0. simpl in *.
assert ((s0 == s0) = true). admit. rewrite H1 in H0. simpl in *.
assert ((s0 == s) || true = true).
destruct ((s0 == s)). simpl. auto. simpl. auto.
rewrite H2 in H0. inversion H0. simpl.

unfold fallthrough.
induction d; simpl in *.
destruct (decide (p = i1)). simpl.
destruct (decide (t = t)). simpl. auto. simpl. auto. auto.
simpl in *.
destruct (decide (p = i1)).
unfold negb in H0. unfold in_mem in H0. simpl in *.
subst. 
assert ((i1 == i1) = true). admit. rewrite H1 in H0. simpl. 
admit.
destruct a. unfold fallthrough in *.
destruct d.
destruct (decide (p = i3)).
admit.
simpl. auto. destruct p0.
simpl in *.
unfold negb in H0. unfold in_mem in H0.
simpl in*.
destruct (decide (p = i3)). simpl.
destruct ((decide (i5 = t))).
simpl. subst; auto.
simpl. auto. 
destruct (decide (p = i5)). simpl. induction d. simpl. admit. admit.
(*using proof above*)
admit.
(*trivial*)
admit.
simpl.


intros. unfold find_instr_double. simpl. 
destruct a. destruct p. simpl in *. 
destruct (decide (p0 = s)). simpl in *.
admit.
simpl.



induction c. simpl.
destruct (decide (p0 = s0)). simpl.
(*trivial*) admit.
simpl in *.
(*proof above*) admit.
simpl. destruct a. simpl in *.
destruct (decide (p0 = i1)). simpl in *.
Admitted.















Lemma testtest8 : forall c d p t, t \notin c -> find_instr (c ++ d) p t = find_instr_double c d p t.
Proof. induction c, d => //.
  +intros. rewrite testtest7. auto.
  +intros. unfold find_instr_double. destruct c. 


Lemma remove_nil_r : forall (a: seq instr_id), a = a ++ [::].
Proof. move => //a. induction a. simpl. auto. simpl. rewrite <- IHa. auto. Qed.


Lemma instr_id_comm : forall (a b:instr_id), (a == b) = (b == a).
Proof. intros. induction a, b => //. Qed.

Lemma uniq_comm_single : forall (a b:instr_id), uniq ([::a] ++ [::b]) = uniq ([::b] ++ [::a]).
Proof. intros. unfold uniq. simpl. unfold negb. unfold in_mem. simpl. rewrite instr_id_comm. auto.
Qed.  




Lemma notin_assoc : forall (a b c:instr_id), (a \notin ([::b] ++ [::c])) = ((a \notin [::b]) && (a \notin [::c])).
Proof. move => //a b c. unfold negb. unfold in_mem. simpl. destruct (a == b) => //; destruct (a == c) => //.
Qed.

Lemma in_nil : forall (a:instr_id), (a \in [::]) = false.
Proof. intros. unfold in_mem. simpl. auto. Qed.


Lemma in_assoc : forall (a b:instr_id) (c:seq instr_id), (a \in ([::b] ++ c)) = (a \in [::b]) || (a \in c).
Proof. intros. simpl. induction c => //.
  +simpl. rewrite in_nil => //. rewrite orb_false_r. auto.
  +simpl. unfold in_mem in *. simpl in *. destruct ((a == b)). simpl in *. auto.
simpl in *. destruct ((a == a0)). simpl. auto. simpl. auto. Qed.



Lemma in_assoc_list : forall (a:instr_id) (b c:seq instr_id), (a \in (b ++ c)) = (a \in b) || (a \in c).
Proof. move => a b c. induction b, c => //.
  +simpl. rewrite <- remove_nil_r. rewrite in_nil. rewrite orb_false_r. auto.
  +simpl in *. unfold in_mem in *. simpl in *. destruct (a == a0) => //. Qed.


Lemma in_assoc_r : forall a (b:seq instr_id) i, (i \in b ++ [:: a]) = (i \in b) || (i \in [:: a]).
Proof. intros. rewrite in_assoc_list. auto. Qed.


Lemma notin_assoc_one_list : forall (a b:instr_id) c, (a \notin ([::b] ++ c)) = ((a \notin [::b]) && (a \notin c)).
Proof. intros. unfold negb. induction c => //.
  +simpl. rewrite andb_true_r. auto.
  +simpl in *. unfold in_mem in *. simpl in *. destruct (a == b) => //. Qed.



Lemma notin : forall (a b:instr_id) (c:seq instr_id), (a \notin ([::b] ++ c) = (a \notin (c ++ [::b]))).
Proof. intros. unfold negb. simpl. induction c => //.
  +unfold in_mem. simpl. destruct (a == a0). destruct (a == b). simpl. auto. simpl. auto. rewrite IHc. simpl.
unfold in_mem. simpl. auto. Qed.
(*
Lemma single_in_eq : forall (a i:instr_id), (i \in [:: a]) = (i == a).
Proof. intros. unfold in_mem. simpl. auto. destruct ((i == a)) => //.
Qed.
Lemma testtest : forall (a:instr_id) (b:seq instr_id),  (a \notin b) && uniq b = uniq (b ++ [::a]).
Proof. move => a b => //. induction b.
  +simpl. auto.
  +simpl. rewrite <- IHb. unfold negb. simpl. rewrite in_assoc_r. rewrite in_assoc. simpl.
rewrite single_in_eq. rewrite single_in_eq. rewrite instr_id_comm. unfold in_mem. remember ((mem b) a) as B.
destruct b; simpl => //. simpl. destruct (a0 == a). simpl. auto. simpl. auto.
simpl. destruct (a == i). simpl. destruct (a0 == i). destruct (a0 == a). simpl. auto.
simpl. auto.
destruct (a0 == a). destruct (b a0).




Lemma add_instr_preserves_ssa : forall b, well_form_block b -> well_form_block (optimise_block b).
Proof. move =>// b. constructor. inversion H. unfold unique_instr_id in *. rewrite /optimise_block/=. 
assert (([seq fst i
      | i <- blk_code b ++
             [:: (get_first_unused b, no_instr)]]) = [seq fst i
      | i <- blk_code b] ++ [::fst (get_first_unused b, no_instr)]) => //. destruct b. simpl in *. induction blk_code => //. simpl.
apply IHblk_code in H.


Admitted.



*)
(*

(*The code in a block gets executed sequentially.
This optimisation adds an instruction to the end of that code therefore the impact this might have is on the block terminator instruction.
There are currently 4 implemented terminator instructions:
  | TERM_Ret :  tvalue -> terminator
  | TERM_Ret_void : terminator
  | TERM_Br :  tvalue -> block_id -> block_id ->  terminator
  | TERM_Br_1 : block_id ->  terminator


Explanation:
TERM_Ret - return a typed value
TERM_Ret_void - return void
TERM_Br - branch to either block id depending on the evaluation of a typed value
TERM_Br_1 - branch directly to block_id



Let's add an instruction to a block if and only if its terminating instruction is TERM_Ret.
*)



(*Simple function that returns true if the terminating instruction is a return void*)
Definition terminator_check (b:block) : bool :=
match b.(blk_term) with
  | (_, TERM_Ret_void) => false
  | _ => false
end.


Definition get_blk_id (b:block) : instr_id :=
let term := b.(blk_term) in
match term with 
  | (term_id, term_instr) => term_id
end.

Print block.



Print block_to_cmd.
Print fallthrough.



Definition old (c:code) (p:instr_id) (term_id:instr_id) := find_instr c p term_id.


Definition add_instr_block (b:block) (i:(instr_id * instr)) (b1:(instr_id * terminator)%type) := 
mk_block b.(blk_id) b.(blk_phis) (blk_code b ++ (cons i nil)) b1.
Print blk_term.

Definition get_blk_term (b:block)  :=
let term := b.(blk_term) in
match term with 
  | (term_id, term_instr) => term_instr
end.

Print block.





(*Definition fallthrough (cd: code) term_id : instr_id :=
  match cd with
  | [] => term_id
  | (next, _)::_ => next
  end.*)




Print block_to_cmd.
Print find_instr.



(*
Definition block_to_cmd (b:block) (iid:instr_id) : option (cmd * option instr_id) :=
  let term_id := blk_term_id b in 
  if term_id == iid then
    Some (Term (snd (blk_term b)), None)
  else
    find_instr (blk_code b) iid term_id 
.


Fixpoint find_instr (cd : code) (p:instr_id) (t:instr_id) : option (cmd * option instr_id) :=
  match cd with
  | [] =>  None
  | (x,i)::cd =>
    if p == x then
      Some (Step i, Some (fallthrough cd t))
    else
      find_instr cd p t
  end.


*)


Lemma test : forall c d look term, find_instr (c ++ d) look term = find_instr (c ++ d) look term.
Proof. Admitted.

Definition beq_ascii (a1 a2 : ascii) :=
  match a1, a2 with
  | Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    (eqb b1 c1) && (eqb b2 c2) && (eqb b3 c3) && (eqb b4 c4) &&
    (eqb b5 c5) && (eqb b6 c6) && (eqb b7 c7) && (eqb b8 c8)
  end.


Fixpoint beq_string (s1 s2 : string) :=
  match s1, s2 with
  | EmptyString,  EmptyString  => true
  | String x1 s1, String x2 s2 => beq_ascii x1 x2 && beq_string s1 s2
  | _, _                       => false
  end.


Print raw_id.
Print int.
Definition beq_raw_id (a b: raw_id) : bool:=
match a, b with
  | Name a, Name b => beq_string a b
  | Anon a, Anon b => Z.eqb a b
  | Raw a, Raw b => Z.eqb a b
  | _, _ => false
end.
Print instr_id.



Definition beq_instr_id (a b: instr_id) : bool:=
match a, b with
  | IId a, IId b => beq_raw_id a b
  | IVoid a, IVoid b => Z.eqb a b
  | _, _ => false
end.


Lemma ascii_eq : forall a, beq_ascii a a = true.
Proof. intros a. induction a. simpl.
repeat (rewrite eqb_reflx; simpl). auto. Qed.

Lemma string_eq : forall s, beq_string s s = true.
Proof. intros. induction s.
  -simpl. auto.
  -simpl. rewrite ascii_eq. simpl. rewrite IHs. auto. Qed.




Lemma raw_id_eq : forall a, beq_raw_id a a = true.
Proof. intros. induction a; simpl; try (rewrite string_eq); try (rewrite Z.eqb_refl); auto.
Qed.

Lemma instr_id_eq : forall a, beq_instr_id a a = true.
Proof. intros. induction a; simpl; try (rewrite raw_id_eq); try (rewrite Z.eqb_refl); auto.
Qed.

Print fallthrough.
(*Definition fallthrough (cd: code) term_id : instr_id :=
  match cd with
  | [] => term_id
  | (next, _)::_ => next
  end.*)


Definition double_fallthrough (c d: code) (term_id:instr_id) : instr_id :=
match c with
  | [] => fallthrough d term_id
  | _ => fallthrough c term_id
end.

Lemma double_fallthrough_eq : forall c d term_id, fallthrough (c ++ d) term_id = double_fallthrough c d term_id.
Proof. intros. unfold double_fallthrough. unfold fallthrough.
simpl. destruct c; simpl.
  +simpl. auto.
  +destruct p. auto.
Qed.


Print block_to_cmd.


(*Fixpoint find_instr (cd : code) (p:instr_id) (t:instr_id) : option (cmd * option instr_id) :=
  match cd with
  | [] =>  None
  | (x,i)::cd =>
    if p == x then
      Some (Step i, Some (fallthrough cd t))
    else
      find_instr cd p t
  end.*)



Definition double_find_instr (c d: code) (p :instr_id) (t:instr_id) : option (cmd * option instr_id) :=
match (find_instr c p t) with
  | None => (find_instr d p t)
  | Some (Step i, Some ter) => if beq_instr_id ter t then Some (Step i, Some (fallthrough d t)) else Some (Step i, Some ter)
  | Some (_, _) => find_instr d p t
end.

(*
Lemma help : forall t, (fallthrough [] t) = t.
Proof. intros. unfold fallthrough; simpl; eauto.
Qed.

Lemma help1 : forall p t, find_instr [] p t = None.
Proof. intros. unfold find_instr. auto. Qed.


Lemma help2: forall a d p t, find_instr (a::d) p t = double_find_instr (cons a nil) d p t.
Proof. intros. induction a. simpl. unfold double_find_instr.
simpl. destruct (p == a ). simpl.
rewrite instr_id_eq. auto. auto. Qed.
(* (fallthrough (c ++ d) t))*)





Lemma test12 : forall c d p t, find_instr (c ++ d) p t = double_find_instr c d p t.
Proof. intros.
unfold double_find_instr. simpl.
induction c.
  +simpl. auto.
  +rewrite help2. 
assert (((a :: c) ++ d) = cons a (c ++ d)).
simpl; auto. rewrite H. rewrite help2. 
unfold double_find_instr. rewrite IHc.
simpl. destruct a. simpl.

Definition optimise (b:block) := if terminator_check b then (add_instr_block b (get_blk_id b, no_instr) (get_first_unused b, get_blk_term b)) else b.

Definition prog_optimise (p:modul CFG.cfg) := def_cfg_opt optimise p.

(*
(*V1*)
(*Get new instructions*)

(*Proof: block_to_cmd (optimise b) p = fetch_two_block b (optimise b) (new:code) p*)



Definition fetch_two_block_full  (b:block) (p:instr_id) :=
if terminator_check b then (fetch_two_block b (optimisev1 b) (cons (get_first_unused b, no_instr) nil) p) else (block_to_cmd b p).


Lemma block_eq : forall b p, block_to_cmd (optimisev1 b) p = fetch_two_block_full b p.
Proof. intros. unfold block_to_cmd. unfold fetch_two_block_full. unfold optimisev1. 
unfold terminator_check. destruct b. simpl. destruct blk_term. simpl. unfold blk_term_id. 
unfold block_to_cmd. simpl. unfold fetch_two_block. simpl. unfold blk_term_id. simpl.
destruct t; simpl; auto.
  +unfold block_to_cmd. simpl. unfold blk_term_id. simpl. unfold get_first_unused. simpl.
destruct (i == p). auto.
  *destruct blk_code. simpl. unfold get_terminator_iid. simpl. unfold not in n.
induction i; simpl; auto. induction id. simpl.

Require Import Vellvm.optimisations.transform. 


Definition optimise_addv1 (b:block) := if terminator_check b then cons (get_first_unused b, no_instr) nil else nil.

Definition prog_optimisev1 (p:modul CFG.cfg) := def_cfg_opt optimisev1 p.


(*In the proof, there will always be the case:
  fetch prog pc = ...
  fetch (optimise prog) pc = ...

As seen in the pacoproof.v, it is useful to write (fetch (optimise prog) pc) as a new function of fetch prog pc.
This allows us to 
*)
(*V2*)(*
Definition optimisev2 (b:block) := if terminator_check b then (add_instr_block b (get_blk_id b, no_instr) (
*)
Print block_to_cmd.




Print find_instr.
Print block_to_cmd.



(**************************************************************************)
Definition dual_block_to_cmd (b:block) (i:instr_id) := if terminator_check b then fetch_two_block b (cons (get_first_unused b, no_instr) nil) i else block_to_cmd b i .


Require Import Vellvm.Classes.
Definition dual_fetch (CFG: mcfg) (p:pc) :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- dual_block_to_cmd blk iid;
  mret c.



Lemma test1 : forall b i, dual_block_to_cmd b i = block_to_cmd (optimisev1 b) i.
Proof. intros. unfold dual_block_to_cmd. unfold terminator_check.
destruct b. simpl. unfold optimisev1. simpl. unfold get_first_unused. simpl. destruct blk_term.
simpl. destruct t; simpl; auto.
  -unfold fetch_two_block. simpl. unfold block_to_cmd. simpl. unfold blk_term_id.
simpl. unfold get_terminator_iid. simpl. destruct (i0 == i); auto.
induction blk_code. simpl. auto.
remember (i ==
    IId
      (Raw
         (match i0 with
          | IId (Name _) => 0
          | IId (Anon _) => 0
          | IId (Raw n0) => n0
          | IVoid _ => 0
          end + 1)%Z)) as A. destruct A; auto. simpl. destruct a. simpl.
destruct (i == i1). simpl. unfold fallthrough. simpl.
destruct blk_code. simpl. unfold not in n. destruct i1. simpl. destruct id. simpl.
destruct i0. destruct id; simpl. simpl in *.
Qed.



Print fetch.


Definition fetch1 (CFG : mcfg) (p:pc) : option cmd :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- dual_block_to_cmd blk iid;
  mret c.





Lemma equal_fetch : forall m p, fetch (prog_optimisev1 m) p = fetch1 m p.
Proof. intros.
destruct m. simpl.
induction m_definitions.
  +unfold prog_optimisev1 in *. unfold optimisev1. simpl. unfold def_cfg_opt. simpl. unfold fetch, fetch1. simpl. auto.
  +simpl in *. unfold fetch, fetch1 in *. simpl. destruct p. simpl in *. destruct a. simpl in *.
unfold find_function in *. simpl in *. unfold find_defn in *. simpl in *.
unfold cfg_opt in *. simpl in *. auto. unfold ident_of in *. simpl in *. 
unfold ident_of_definition in *. unfold ident_of in *. simpl in *.

destruct (ident_of_declaration df_prototype == ID_Global fn).
    *simpl in *. destruct df_instrs. simpl in *. induction blks; simpl in *; auto.
      -destruct a. simpl. unfold optimisev1. simpl. unfold terminator_check. simpl.
{destruct blk_term. simpl. destruct t; simpl; destruct (blk_id == bk); try (rewrite test1; unfold optimisev1; simpl; auto);
try (induction blks; simpl; auto).
}
    *auto.
Qed.



Print find_block.

(******************SECOND*************************)



Definition incr_pc1 (CFG : mcfg) (p:pc) : option pc :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, n) <- dual_block_to_cmd blk iid;
  'iid_next <- n;
  mret (mk_pc fid bid iid_next).

Lemma equal_incr_pc : forall m p, incr_pc (prog_optimisev1 m) p = incr_pc1 m p.
Proof. intros. destruct m. simpl.
destruct m_definitions; simpl in *.
  +unfold prog_optimisev1 in *. unfold optimisev1. simpl. unfold def_cfg_opt. simpl. unfold incr_pc, incr_pc1. simpl. auto.
  +simpl in *. unfold incr_pc, incr_pc1 in *. simpl. destruct p. simpl in *. destruct d. simpl in *.
unfold find_function in *. simpl in *. unfold find_defn in *. simpl in *.
unfold cfg_opt in *. simpl in *. auto. unfold ident_of in *. simpl in *. 
unfold ident_of_definition in *. unfold ident_of in *. simpl in *.

destruct (ident_of_declaration df_prototype == ID_Global fn).
    *simpl in *. destruct df_instrs. simpl in *. induction blks.
      -simpl in *. auto.
      -destruct a. simpl. unfold optimisev1. simpl. unfold terminator_check. simpl.
{destruct blk_term. simpl. destruct t; simpl; destruct (blk_id ==bk); try (rewrite test1; unfold optimisev1; simpl; eauto); try (induction blks; simpl; eauto).
}
    *induction m_definitions.
      -simpl. auto.
      -simpl.
{destruct (ident_of_declaration (Ollvm_ast.df_prototype a) == ID_Global fn).
        +simpl. destruct a. simpl in *. induction df_instrs0. 
          -simpl in *. induction blks.
            *simpl. auto.
            *simpl. unfold optimisev1. unfold terminator_check. simpl. destruct a. simpl in *. destruct blk_term. clear IHm_definitions. simpl in *.
{destruct t; simpl; destruct (blk_id == bk);
try (simpl; unfold dual_block_to_cmd, block_to_cmd, blk_term_id; simpl; auto);
try (induction blks; simpl; auto; auto).
unfold fetch_two_block. simpl.
unfold block_to_cmd; simpl in *.
unfold blk_term_id; simpl in *.
  *destruct (i == pt); auto. induction blk_code.
    -simpl. unfold get_blk_id. simpl. induction (pt == i); auto.
    -simpl. destruct a. destruct (pt == i0). simpl.
unfold get_blk_id; simpl in *.
unfold fallthrough. simpl. induction blk_code. simpl.
auto.
auto.
auto.
  *clear IHblks. clear IHblks0. 
unfold fetch_two_block. simpl. unfold block_to_cmd. simpl.
unfold get_blk_id. simpl. unfold blk_term_id. simpl.
subst.
destruct (i == pt); auto.
induction blk_code; auto.
  +simpl. destruct (pt == i); auto.
  +simpl. destruct a0. destruct (pt == i0); auto. unfold fallthrough. 
simpl. destruct blk_code; simpl; auto.
}
  +auto.
}
Qed.*)

*)*)
*)
(**************************************************************************)