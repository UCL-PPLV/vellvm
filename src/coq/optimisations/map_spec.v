
Require Import Equivalence EquivDec.
Require Import Coqlib.
Require Import Equalities.
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
End TREE.




Module Type TREE1.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.

  Axiom elt_eq_refl : forall x : elt, eq x x.
  Axiom elt_eq_sym : forall x y : elt, eq x y -> eq y x.
  Axiom elt_eq_trans : forall x y z : elt, eq x y -> eq y z -> eq x z.
  Parameter elt_eqb : elt -> elt -> bool.
  Parameter elt_eqb_eq : forall x y, elt_eqb x y = true <-> eq x y.

  Parameter val: Type.
  Parameter val_eq : val -> val -> Prop.
  Parameter val_eqb : val -> val -> bool.
  Parameter val_eqb_eq : forall x y, val_eqb x y = true <-> val_eq x y.



  
  
  Parameter t: Type.
  Parameter empty: t.
  Parameter get: elt -> t -> option val.
  Parameter set: elt -> val -> t -> t.
  Parameter remove: elt -> t -> t.

  Axiom gempty:
    forall (i: elt), get i (empty) = None.
  Axiom gss:
    forall  (i: elt) (x: val) (m: t), get i (set i x m) = Some x.
  Axiom gso:
    forall (i j: elt) (x: val) (m: t),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (i j: elt) (x: val) (m: t),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Axiom grs:
    forall (i: elt) (m: t), get i (remove i m) = None.
  Axiom gro:
    forall (i j: elt) (m: t),
    i <> j -> get i (remove j m) = get i m.
  Axiom grspec:
    forall  (i j: elt) (m: t),
    get i (remove j m) = if elt_eq i j then None else get i m.




  Parameter beq:  t -> t -> bool.
  
  Axiom beq_correct:
    forall  (t1 t2: t),
    beq t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => val_eqb y1 y2 = true
     | _, _ => False
    end).


  Parameter combine:
    (option val -> option val -> option val) -> t -> t -> t.
  Axiom gcombine:
    forall (f: option val -> option val -> option val),
    f None None = None ->
    forall (m1: t) (m2: t) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
End TREE1.


