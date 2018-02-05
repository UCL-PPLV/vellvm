
Require Import Equivalence EquivDec.
Require Import Coqlib.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.



Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter init: forall (A: Type), A -> t A.
  Parameter get: forall (A: Type), elt -> t A -> A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Axiom gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Axiom gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Parameter map: forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.



Module Type TREE.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), elt -> t A -> option A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Parameter remove: forall (A: Type), elt -> t A -> t A.

  Axiom gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Axiom grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Axiom gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Axiom grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.




  Parameter beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Axiom beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).


  Parameter map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).


  Parameter map1:
    forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).


  Parameter combine:
    forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C.
  Axiom gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).

  Parameter elements:
    forall (A: Type), t A -> list (elt * A).
  Axiom elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Axiom elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Axiom elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Axiom elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Axiom elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.

  Parameter fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Axiom fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.

  Parameter fold1:
    forall (A B: Type), (B -> A -> B) -> t A -> B -> B.
  Axiom fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
End TREE.
