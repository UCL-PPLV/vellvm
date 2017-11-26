
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
Require Import Vellvm.optimisations.transform.
Require Import Coq.Logic.FunctionalExtensionality.
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

Definition get_terminator_id (b:block) : instr_id :=
match b.(blk_term) with
| (a, _) => a
end.



(*Find the largest instruction (which is either the terminator ID or an instruction from within the code) and adds 1 to it*)
Definition get_first_unused (b:block) : instr_id := IId (Raw (Z.add (get_maximum (get_terminator_iid b) (b.(blk_code))) 1)).

(*Useless instruction*)
Definition no_instr : instr := INSTR_Op (SV (VALUE_Null)).
Print block.

Definition add_to_block b c :=  mk_block b.(blk_id) b.(blk_phis) (b.(blk_code)++c) b.(blk_term).
Print block.
Print terminator.
Print snd.
Definition term_check (b:block) : bool :=
let term := snd b.(blk_term) in
match term with
  | TERM_Ret_void => true
  | _ => false
end.




Definition optimise_block (b:block) := if (term_check b) then add_to_block b [::(get_first_unused b, no_instr)] else b.
Definition optimise_program (m:mcfg) := def_cfg_opt optimise_block m.





Print find_instr.


(*END GOAL: find_instr (c ++ d) p t = find_instr_double c d p t*) 

Lemma instr_id_eq : forall (i1:instr_id), ((i1 == i1) = true).
Proof. intro.
Admitted.


Definition find_instr_double (c d: code) (p t : instr_id) : option (cmd * option instr_id) :=
match (find_instr c p t) with
  | None => find_instr d p t
  | Some (CFG.Step i, Some tid ) => if decide (tid = t) then (Some (CFG.Step i, Some (fallthrough d t))) else Some (CFG.Step i, Some tid)
  | Some (CFG.Step i, None) => None
  | Some (Term _, _) => None
end.

Lemma not_eq_false : forall (t:instr_id), t <> t -> False.
Proof. intros. unfold not in H. apply H. auto. Qed.


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
Print find_instr.
Definition helper_func d p t : option (cmd * option instr_id) :=
match find_instr d p t with
| Some (CFG.Step i7, Some tid) =>
    if is_left (decide (tid = t)) then Some (CFG.Step i7, Some t) else Some (CFG.Step i7, Some tid)
| Some (CFG.Step i7, None) => None
| Some (Term _, _) => None
| None => None
end.



Lemma find_instr_eq_helper_func: forall d p t, find_instr d p t = helper_func d p t.
Proof. induction d => //. intros.
rewrite testtest5. simpl. unfold helper_func, find_instr_double. simpl. destruct a. simpl.
destruct (decide (p = i)). simpl. destruct (decide (t = t)). simpl.
induction d. simpl in *.
destruct (decide (t = t)); simpl in *; auto.
simpl. destruct a. simpl in *. specialize (IHd t). subst.
destruct ((decide (i1 = t))). simpl. subst. auto. simpl. auto.
assert (t = t) by auto. unfold not in n. apply n in H. inversion H.
specialize (IHd p t). unfold helper_func in IHd. auto.
 Qed.


Lemma find_double_eq : forall c d p t,  p \notin (map fst c) ->
 p \notin (map fst d) -> 
find_instr_double c d p t = find_instr (c ++ d) p t.
Proof. induction c, d => //.
+simpl in *. destruct a. simpl. intros. unfold find_instr_double. simpl. destruct (decide (p = i)).
subst. unfold negb, in_mem in H; simpl in H. rewrite instr_id_eq in H; simpl in H. inversion H.
rewrite cats0. induction c. simpl. auto.
(*by testtest8*)
admit.
intros. simpl in *.

specialize (IHc (p :: d) p0 t).
unfold find_instr_double. simpl in *. destruct a. destruct (decide (p0 = i)).
subst; simpl; unfold negb, in_mem in H; simpl in H. 
assert ((i == i) = true). admit. rewrite H1 in H. simpl in *. inversion H.
 simpl in *. unfold find_instr_double in IHc. apply IHc.
unfold negb in *. admit. auto.

 Admitted.


Definition double_block_to_cmd (b:block) (added_code:code) (iid:instr_id) : option (cmd * option instr_id):=
  let term_id := blk_term_id b in 
  if decide (term_id = iid) then
    Some (Term (snd (blk_term b)), None)
  else
    find_instr_double (blk_code b) added_code iid term_id 
.

Definition double_block_to_cmd_check b added_code iid :=
if (term_check b) then double_block_to_cmd b added_code iid else block_to_cmd b iid.

Lemma double_block_to_cmd_eq : forall b iid, block_to_cmd (optimise_block b) iid = double_block_to_cmd_check b [::(get_first_unused b, no_instr)] iid.
Proof. destruct b. unfold block_to_cmd. simpl.
unfold double_block_to_cmd_check. simpl. unfold double_block_to_cmd. simpl.
unfold optimise_block. simpl. unfold term_check. simpl. destruct blk_term.
simpl. induction t.
  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
  +simpl. unfold block_to_cmd. intros. unfold blk_term_id. simpl.
assert


(find_instr_double blk_code
    [:: (get_first_unused
           {|
           blk_id := blk_id;
           blk_phis := blk_phis;
           blk_code := blk_code;
           blk_term := (i, TERM_Ret_void) |}, no_instr)] iid 
    i


=

(find_instr
    (blk_code ++
     [:: (get_first_unused
            {|
            blk_id := blk_id;
            blk_phis := blk_phis;
            blk_code := blk_code;
            blk_term := (i, TERM_Ret_void) |}, no_instr)]) iid 
    i)). apply find_double_eq. admit. admit. rewrite H. 
destruct (decide (i = iid)); simpl; auto.

  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
  +simpl. unfold block_to_cmd. simpl. unfold blk_term_id. simpl. auto.
Admitted.


Definition double_fetch (CFG : mcfg) (p:pc) : option cmd :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, _) <- double_block_to_cmd_check blk [::(get_first_unused blk, no_instr)] iid;
  mret c.



Definition test1 a (bk:block_id) pt :=
match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match block_to_cmd a0 pt with
        | Some (c, _) => Some c
        | None => None
        end
    | None => None
    end.


Definition test2 a bk pt :=
  match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match double_block_to_cmd_check a0 [:: (get_first_unused a0, no_instr)] pt with
        | Some (c, _) => Some c
        | None => None
        end
    | None => None
    end.
Print find_block.

Lemma testeq : forall a bk pt, test1 (cfg_opt optimise_block a) bk pt = test2 a bk pt.
Proof.
destruct a. simpl. unfold test1, test2.
simpl. destruct df_instrs. simpl. induction blks.
+simpl. auto.
+simpl. intros.



destruct a. simpl. destruct blk_term. simpl; induction t; simpl; destruct (decide (blk_id = bk)); try rewrite <- double_block_to_cmd_eq; auto.



  +admit.
  +admit.
  +admit.
  +admit.
  +admit.
  +admit.
  +admit.
Admitted.


 (* destruct a. destruct df_instrs. induction blks => //.
unfold test1, test2. simpl.









 destruct df_instrs. induction blks => //.
intros. unfold test1, test2. simpl. destruct (decide (blk_id a = bk)).


assert (block_to_cmd (optimise_block a) pt = double_block_to_cmd_check a [:: (get_first_unused a, no_instr)] pt).
apply double_block_to_cmd_eq. rewrite H. auto.

simpl in *. unfold test1, test2 in IHblks. simpl in *.
simpl. specialize (IHblks bk pt). 


assert ( List.find (fun b : block => if decide (blk_id b = bk) then true else false)
    (List.map optimise_block blks) = 
find_block (List.map optimise_block blks) bk).
destruct blks. simpl. auto. simpl.
destruct (decide (blk_id b = bk)). simpl. auto. simpl. f_equal.
apply functional_extensionality. intros. destruct (decide (blk_id x = bk)) => //.
unfold is_left in H. simpl in *. destruct blks. simpl in *. auto.
simpl in *. apply IHblks. Qed.*) 


Definition test1_v1 mcfg fn bk pt :=
match find_function mcfg fn with
| Some a => test1 a bk pt
| None => None
end.

Definition test2_v1 mcfg fn bk pt :=
match find_function mcfg fn with
| Some a => test2 a bk pt
| None => None
end.



Lemma testeq_v1 : forall mcfg fn bk pt, test1_v1 (optimise_program mcfg) fn bk pt = test2_v1 mcfg fn bk pt.
Proof. intros. unfold test1_v1. simpl. unfold test2_v1.
destruct mcfg. induction m_definitions.
  +simpl. auto.
  +unfold find_function. simpl. unfold find_defn. simpl.
unfold cfg_opt. simpl. unfold alter_blocks. simpl. unfold ident_of. simpl. unfold ident_of_definition. simpl.
destruct (decide (ident_of (df_prototype a) = ID_Global fn)). simpl.
rewrite testeq. auto.
simpl.
unfold find_function in *. simpl in *.
unfold find_defn in *. simpl in *. rewrite IHm_definitions. auto.
Qed.


Lemma double_fetch_eq : forall m p, fetch (optimise_program m) p = double_fetch m p.
Proof. intros. unfold double_fetch. unfold fetch. simpl.
destruct p. simpl.
destruct m. simpl. induction m_definitions. simpl. auto.
unfold find_function. simpl. unfold find_defn. unfold ident_of.
simpl. unfold ident_of_definition. simpl.
destruct (decide (ident_of (df_prototype a) = ID_Global fn)). simpl.
destruct a. simpl. destruct df_instrs. simpl. induction blks.
simpl. auto.
simpl.  unfold optimise_block. simpl. destruct a. simpl. unfold term_check.

destruct blk_term. simpl.
destruct t.

  +simpl in *. destruct (decide (blk_id = bk) ). simpl. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
  +simpl in *. destruct (decide (blk_id = bk)). simpl in *. rewrite <- double_block_to_cmd_eq. auto. admit.
(*
simpl.


unfold find_function in *. simpl in *.

assert (Util.find_map (find_defn fn)
                      (List.map (cfg_opt optimise_block) m_definitions)
= Util.find_map
    (fun d : definition cfg =>
     if decide (ident_of (df_prototype d) = ID_Global fn)
     then Some d
     else None) (List.map (cfg_opt optimise_block) m_definitions)).
simpl. unfold find_defn. f_equal. apply functional_extensionality.
intros. unfold is_left. simpl.
unfold ident_of. unfold ident_of_definition. unfold ident_of.
destruct (decide (ident_of_declaration (df_prototype x) = ID_Global fn)); auto.









rewrite H in IHm_definitions.




assert (Util.find_map (find_defn fn) m_definitions
=
(Util.find_map
    (fun d : definition cfg =>
     if decide (ident_of (df_prototype d) = ID_Global fn)
     then Some d
     else None) m_definitions)).

unfold find_defn. unfold is_left.
f_equal.
apply functional_extensionality. intros.
unfold ident_of. unfold ident_of_definition.
unfold ident_of.
destruct (decide (ident_of_declaration (df_prototype x) = ID_Global fn)); simpl; eauto.
rewrite H0 in IHm_definitions.

induction m_definitions.
simpl in *. auto. 
assert (match find_function (optimise_program m) fn with
| Some a =>
    match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match block_to_cmd a0 pt with
        | Some (c, _) => Some c
        | None => None
        end
    | None => None
    end
| None => None
end = test1_v1 (optimise_program m) fn bk pt) by auto.
assert (match find_function m fn with
| Some a =>
    match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match
          double_block_to_cmd a0 [:: (get_first_unused a0, no_instr)] pt
        with
        | Some (c, _) => Some c
        | None => None
        end
    | None => None
    end
| None => None
end = test2_v1 m fn bk pt) by auto.
rewrite H; rewrite H0. apply testeq_v1.  *) Admitted.

(*********************************)





Definition double_incr_pc (CFG:mcfg) (p:pc) : option pc :=
  let 'mk_pc fid bid iid := p in 
  'cfg <- find_function CFG fid;
  'blk <- find_block (blks (df_instrs cfg)) bid;
  '(c, n) <- double_block_to_cmd_check blk [::(get_first_unused blk, no_instr)] iid;
  'iid_next <- n;
  mret (mk_pc fid bid iid_next).




Definition test3_v1 a bk pt fn := 
match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match block_to_cmd a0 pt with
        | Some (_, Some a2) =>
            Some {| fn := fn; bk := bk; pt := a2 |}
        | Some (_, None) => None
        | None => None
        end
    | None => None
    end
.

Definition test4_v1 a bk pt fn  :=
match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match
          double_block_to_cmd a0
            [:: (get_first_unused a0, no_instr)] pt
        with
        | Some (_, Some a2) =>
            Some {| fn := fn; bk := bk; pt := a2 |}
        | Some (_, None) => None
        | None => None
        end
    | None => None
    end
.




Lemma test_eq2 : forall a bk pt fn, test3_v1 (cfg_opt optimise_block a) bk pt fn = test4_v1 a bk pt fn.
Proof. intros. (*
destruct a. destruct df_instrs. simpl. induction blks.
  +unfold test3_v1, test4_v1. simpl. auto.
  +unfold test3_v1, test4_v1 in *. simpl in *.
destruct (decide (blk_id a = bk)). rewrite double_block_to_cmd_eq. auto.
simpl in *.
assert ( find_block (List.map optimise_block blks) bk =
  List.find
    (fun b : block =>
     if decide (blk_id b = bk) then true else false)
    (List.map optimise_block blks)).
destruct blks; simpl; auto. destruct (decide (blk_id b = bk)); simpl; auto.
f_equal. apply functional_extensionality. intros. destruct (decide (blk_id x = bk)); simpl; auto.
rewrite H in IHblks.
assert (find_block blks bk =   List.find
    (fun b : block =>
     if decide (blk_id b = bk) then true else false) blks).
destruct blks; simpl; auto. destruct (decide (blk_id b = bk)); simpl; auto. f_equal.
apply functional_extensionality. intros. destruct (decide (blk_id x = bk)); simpl; auto.
rewrite H0 in IHblks. simpl in *.
induction blks. simpl in *. auto. simpl in *.
destruct (decide (blk_id a0 = bk)). simpl in *. auto.
 simpl in *. rewrite H0. rewrite H. apply IHblks. *) Admitted.



Definition test3_v2 m bk pt fn :=
match find_function m fn with
| Some a => test3_v1 a bk pt fn
| None => None
end.


Definition test4_v2 m bk pt fn :=
match find_function m fn with
| Some a => test4_v1 a bk pt fn
| None => None
end.



Lemma test_eq3 : forall mcfg fn bk pt, test3_v2 (optimise_program mcfg) fn bk pt = test4_v2 mcfg fn bk pt.
Proof. intros. unfold test3_v2, test4_v2. destruct mcfg. induction m_definitions.
  +simpl. auto.
  +unfold find_function; simpl in *.  unfold find_defn. simpl. unfold ident_of.
simpl. unfold ident_of_definition. simpl.
destruct (decide (ident_of (df_prototype a) = ID_Global pt)). rewrite test_eq2. auto.
simpl.
unfold find_function in *. simpl. unfold find_defn in *. simpl in *.
rewrite IHm_definitions. auto. Qed.






Lemma double_incr_pc_eq : forall m p, incr_pc (optimise_program m) p = double_incr_pc m p.
Proof. intros. destruct p. simpl.
assert (match find_function (optimise_program m) fn with
| Some a =>
    match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match block_to_cmd a0 pt with
        | Some (_, Some a2) =>
            Some {| fn := fn; bk := bk; pt := a2 |}
        | Some (_, None) => None
        | None => None
        end
    | None => None
    end
| None => None
end = test3_v2 (optimise_program m) bk pt fn). unfold test3_v2. unfold test3_v1.
auto. rewrite H. clear H.

assert (match find_function m fn with
| Some a =>
    match find_block (blks (df_instrs a)) bk with
    | Some a0 =>
        match
          double_block_to_cmd a0
            [:: (get_first_unused a0, no_instr)] pt
        with
        | Some (_, Some a2) =>
            Some {| fn := fn; bk := bk; pt := a2 |}
        | Some (_, None) => None
        | None => None
        end
    | None => None
    end
| None => None
end = test4_v2 m bk pt fn). unfold test4_v2. unfold test4_v1. simpl.
Admitted.



(**************)
(*Jump equiv*)



Print jump.
Locate jump.
Print find_block.

Definition jump_test1 a function_id end_bid:=
      match find_block (blks (df_instrs a)) end_bid with
      | Some a0 => Some (block_to_entry function_id a0)
      | None => None
      end
.
Print jump_test1.

Print find_block.


Definition jump_test2 a function_id end_bid :=
      match find_block (blks (df_instrs a)) end_bid with
      | Some a0 => Some (block_to_entry function_id (optimise_block a0))
      | None => None
      end.
Print jump_test1.


Lemma jump_test_eq : forall mcfg function_id end_bid, jump_test1 (cfg_opt optimise_block mcfg) function_id end_bid = jump_test2 mcfg function_id end_bid.
Proof. intros. unfold jump_test1, jump_test2. simpl. destruct mcfg. simpl. destruct df_instrs. simpl.
induction blks. simpl. auto.
simpl. unfold optimise_block. simpl. unfold blk_id. simpl. destruct a. simpl.

unfold term_check. simpl. destruct blk_term. simpl. destruct t.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
simpl. destruct (decide (blk_id = end_bid)). simpl. auto. admit.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
destruct (decide (blk_id = end_bid)). simpl. auto. admit.
Admitted.