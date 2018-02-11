Ltac dupl x := generalize x; intro.
Ltac contra_destr x := remember x; destruct x; try contradiction; auto.
Ltac inv x := inversion x; subst; auto.


Ltac destr_eq t := destruct t eqn:?; simpl; eauto.
Ltac destr t := destruct t; simpl; eauto.
Ltac appl t y := generalize y; intro; apply t in y.


Ltac break_inner_match' t :=
  match t with
   | context[match ?X with _ => _ end] => break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

Ltac break_inner_match_goal :=
  match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

Ltac break_goal :=  break_inner_match_goal; simpl in *; eauto; try constructor.
Ltac try_resolve := try (repeat break_goal); try constructor.
