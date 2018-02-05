Ltac dupl x := generalize x; intro.
Ltac contra_destr x := remember x; destruct x; try contradiction; auto.
Ltac save_destr x := remember x; destruct x.
Ltac inv x := inversion x; subst; auto.