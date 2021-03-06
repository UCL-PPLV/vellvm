Require Import Coqlib.
Require Import  Vellvm.Ollvm_ast Vellvm.Classes Vellvm.Util Vellvm.CFGProp Vellvm.CFG.
Require Import Vellvm.optimisations.local_cfg.
Require Import Vellvm.optimisations.maps.
Require Import FSets.


Module Type SEMILATTICE.


  Parameter t: Type.
  Parameter eq: t -> t -> Prop.
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Parameter beq: t -> t -> bool.
  Axiom beq_correct: forall x y, beq x y = true -> eq x y.
  Parameter ge: t -> t -> Prop.
  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Parameter bot: t.
  Axiom ge_bot: forall x, ge x bot.
  Parameter lub: t -> t -> t.
  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End SEMILATTICE.


Module Type SEMILATTICE_WITH_TOP.

  Include SEMILATTICE.
  Parameter top: t.
  Axiom ge_top: forall x, ge top x.

End SEMILATTICE_WITH_TOP.



Module LPMap1(L: SEMILATTICE) <: SEMILATTICE.

  Definition t := PCTree.t L.t.

  Definition get (p: local_pc) (x: t) : L.t :=
  match x!p with None => L.bot | Some x => x end.


  Definition set (p: local_pc) (v: L.t) (x: t) : t :=
  if L.beq v L.bot
  then PCTree.remove p x
  else PCTree.set p v x.

SearchAbout local_pc.
  
  Lemma gsspec:
  forall p v x q,
  L.eq (get q (set p v x)) (if local_pcDec.eq_dec q p then v else get q x).
  Proof.
  intros. unfold set, get.
  destruct (L.beq v L.bot) eqn:EBOT.
  rewrite PCTree.grspec. destruct ( PCTree.elt_eq q p). subst. destruct (local_pcDec.eq_dec p p). SearchAbout L.eq. eapply L.eq_sym. apply L.beq_correct; eauto. contradiction n; eauto.
destruct ( local_pcDec.eq_dec q p). subst.  contradiction n; eauto. apply L.eq_refl.
  rewrite PCTree.gsspec. destruct ( PCTree.elt_eq q p). subst. destruct ( local_pcDec.eq_dec p p). apply L.eq_refl. contradiction n; eauto. destruct (local_pcDec.eq_dec q p ) eqn:?. subst. contradiction n; eauto. eapply L.eq_refl.
  Qed.




Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof. unfold eq; intros; apply L.eq_refl. Qed.


Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool := PCTree.beq L.beq x y.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold beq; intros; red; intros. unfold get.
  rewrite PCTree.beq_correct in H. specialize (H p).
  destruct (x!p); destruct (y!p); intuition.
  apply L.beq_correct; auto.
  apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot : t := PCTree.empty _.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot, get; intros; simpl. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.


Section COMBINE.

  Variable f: option L.t -> option L.t -> option L.t.
Hypothesis f_none_none: f None None = None.

Definition opt_eq (ox oy: option L.t) : Prop :=
  match ox, oy with
  | None, None => True
  | Some x, Some y => L.eq x y
  | _, _ => False
  end.

Lemma opt_eq_refl: forall ox, opt_eq ox ox.
Proof.
  intros. unfold opt_eq. destruct ox. apply L.eq_refl. auto.
Qed.

Lemma opt_eq_sym: forall ox oy, opt_eq ox oy -> opt_eq oy ox.
Proof.
  unfold opt_eq. destruct ox; destruct oy; auto. apply L.eq_sym.
Qed.

Lemma opt_eq_trans: forall ox oy oz, opt_eq ox oy -> opt_eq oy oz -> opt_eq ox oz.
Proof.
  unfold opt_eq. destruct ox; destruct oy; destruct oz; intuition.
  eapply L.eq_trans; eauto.
Qed.

Definition opt_beq (ox oy: option L.t) : bool :=
  match ox, oy with
  | None, None => true
  | Some x, Some y => L.beq x y
  | _, _ => false
  end.

Lemma opt_beq_correct:
  forall ox oy, opt_beq ox oy = true -> opt_eq ox oy.
Proof.
  unfold opt_beq, opt_eq. destruct ox; destruct oy; try congruence.
  intros. apply L.beq_correct; auto.
  auto.
Qed.

Definition tree_eq (m1 m2: PCTree.t L.t) : Prop :=
  forall i, opt_eq (PCTree.get i m1) (PCTree.get i m2).

Lemma tree_eq_refl: forall m, tree_eq m m.
Proof.
intros; red; intros; apply opt_eq_refl. Qed.

Lemma tree_eq_sym: forall m1 m2, tree_eq m1 m2 -> tree_eq m2 m1.
Proof.
intros; red; intros; apply opt_eq_sym; auto. Qed.

Lemma tree_eq_trans: forall m1 m2 m3, tree_eq m1 m2 -> tree_eq m2 m3 -> tree_eq m1 m3.
Proof.
intros; red; intros; apply opt_eq_trans with (PCTree.get i m2); auto. Qed.

Inductive changed: Type := Unchanged | Changed (m: PCTree.t L.t).



Fixpoint combine_r  (p1: PCTree.t L.t) :=
  match p1 with
  | nil => nil
  | (key, val) :: tl => (key, f None val) :: combine_r tl
  end.
Print get. Print PCTree.get.
Fixpoint combine1 (p:PCTree.t L.t) (p1:PCTree.t L.t) :=
  match p with
  | nil => combine_r p1
  | (key, val) :: tl => (key, f val (PCTree.get key p1)) :: (combine1 tl p1)                       
  end.

Print opt_eq.

Print combine. 
Lemma gcombine:
  forall m1 m2 i, opt_eq (PCTree.get i (combine1 m1 m2)) (f (PCTree.get i m1) (PCTree.get i m2)).
Proof. induction m1; simpl in *.
       +intros. induction m2. simpl in *. rewrite f_none_none. eauto. simpl in *. destruct a. simpl in *. destruct ( PCTree.elt_eq e i); eauto. eapply opt_eq_refl.
       +intros. destruct a. simpl in *. destruct ( PCTree.elt_eq e i); subst; eauto.  eapply opt_eq_refl.
Qed.


End COMBINE.

Lemma gcombine_bot:
  forall f t1 t2 p,
  f None None = None ->
  L.eq (get p (combine1 f t1 t2))
       (match f t1!p t2!p with Some x => x | None => L.bot end).
Proof. intros. unfold get. simpl in *. generalize (gcombine f H t1 t2 p). unfold opt_eq. simpl in *. destruct ((combine1 f t1 t2) ! p). intros. destruct ( f t1 ! p t2 ! p). eauto. inversion H0. intros. destruct ( f t1 ! p t2 ! p ). inversion H0. eapply L.eq_refl. Qed.

Definition lub (x y: t) : t :=
  PCTree.combine
    (fun a b =>
       match a, b with
       | Some u, Some v => Some (L.lub u v)
       | None, _ => b
       | _, None => a
       end)
    x y.


Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros.
  eapply L.ge_trans. apply L.ge_refl.
  apply gcombine_bot; auto. unfold get. destruct ( x ! p).
  destruct (y ! p ). simpl in *.  apply L.ge_lub_left. eapply L.ge_refl. eapply L.eq_refl.
  destruct (y ! p). eapply L.ge_bot. eapply L.ge_refl. eapply L.eq_refl. Qed.


Lemma ge_lub_right:
  forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_bot; auto.
  unfold get. destruct y!p. destruct x!p.
  apply L.ge_lub_right.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_bot.
Qed.
End LPMap1.



















Module LPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
  | Bot: t'
  | Top_except: PCTree.t L.t -> t'.

Definition t: Type := t'.

Definition get (p: local_pc) (x: t) : L.t :=
  match x with
  | Bot => L.bot
  | Top_except m => match m!p with None => L.top | Some x => x end
  end.

Definition set (p: local_pc) (v: L.t) (x: t) : t :=
  match x with
  | Bot => Bot
  | Top_except m =>
      if L.beq v L.bot
      then Bot
      else Top_except (if L.beq v L.top then PCTree.remove p m else PCTree.set p v m)
  end. SearchAbout local_pc.

Lemma gsspec:
  forall p v x q,
  x <> Bot -> ~L.eq v L.bot ->
  L.eq (get q (set p v x)) (if local_pcDec.eq_dec q p then v else get q x).
Proof.
  intros. unfold set. destruct x. congruence.
  destruct (L.beq v L.bot) eqn:EBOT.
  elim H0. apply L.beq_correct; auto.
  destruct (L.beq v L.top) eqn:ETOP; simpl.
  rewrite PCTree.grspec. 

destruct ( PCTree.elt_eq q p). subst. destruct (local_pcDec.eq_dec p p). apply L.eq_sym.
eapply L.beq_correct. eauto. contradiction n; eauto.
destruct (local_pcDec.eq_dec q p). subst. contradiction n; eauto. eapply L.eq_refl.
rewrite PCTree.gsspec. destruct (PCTree.elt_eq q p). subst. destruct (local_pcDec.eq_dec p p). eapply L.eq_refl. contradiction n; eauto. destruct ( local_pcDec.eq_dec q p ). subst. contradiction n; eauto. apply L.eq_refl. 
 Qed.


Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof.
  intros. unfold eq. simpl in *. intros. apply L.eq_refl. Qed.




Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
intros. unfold eq in *. intros. eapply L.eq_sym.   eauto. Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
unfold eq. intros. eapply L.eq_trans; eauto. Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Top_except m, Top_except n => PCTree.beq L.beq m n
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  destruct x; destruct y; simpl; intro; try congruence.
  apply eq_refl.
  red; intro; simpl.
  rewrite PCTree.beq_correct in H. generalize (H p).
  destruct (t0!p); destruct (t1!p); intuition.
  apply L.beq_correct; auto.
  apply L.eq_refl.
Qed.
  
Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.


Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.


Definition bot := Bot.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot; intros; simpl. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.


Definition top := Top_except (PCTree.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof.
  unfold top; intros; simpl. eauto. 
Qed.


Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.


Module LM := LPMap1(L).

Definition opt_lub (x y: L.t) : option L.t :=
  let z := L.lub x y in
  if L.beq z L.top then None else Some z.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top_except m, Top_except n =>
      Top_except
        (PCTree.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | _, _ => None
              end)
           m n)
  end.

Lemma gcombine_top:
  forall f t1 t2 p,
  f None None = None ->
  L.eq (get p (Top_except (LM.combine1 f t1 t2)))
       (match f t1!p t2!p with Some x => x | None => L.top end).
Proof. intros. induction t1; simpl in *.
       +induction t2. simpl in *. rewrite H. apply L.eq_refl. simpl in *. destruct a. simpl in *.
        destruct ( PCTree.elt_eq e p); subst; eauto. apply L.eq_refl.
       +destruct a; simpl in *. destruct ( PCTree.elt_eq e p); subst; eauto. eapply L.eq_refl.
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros. destruct x; destruct y.
  rewrite get_bot. apply L.ge_bot.
  rewrite get_bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
  unfold get. destruct t0!p. destruct t1!p.
  unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
  apply L.ge_top. apply L.ge_lub_left.
  apply L.ge_top.
  apply L.ge_top.
Qed.


  
Lemma ge_lub_right:
  forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros. destruct x; destruct y.
  rewrite get_bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.
  rewrite get_bot. apply L.ge_bot.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
  unfold get. destruct t0!p; destruct t1!p.
  unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
  apply L.ge_top. apply L.ge_lub_right.
  apply L.ge_top.
  apply L.ge_top.
  apply L.ge_top.
Qed.


End LPMap.


(*************************)






Module lidMap1(L: SEMILATTICE) <: SEMILATTICE.

  Definition t := lidTree.t L.t.

  Definition get (p: local_id) (x: t) : L.t :=
  match x#p with None => L.bot | Some x => x end.


  Definition set (p: local_id) (v: L.t) (x: t) : t :=
  if L.beq v L.bot
  then lidTree.remove p x
  else lidTree.set p v x.

SearchAbout local_id.
  
  Lemma gsspec:
  forall p v x q,
  L.eq (get q (set p v x)) (if loc_id_eq q p then v else get q x).
  Proof.
  intros. unfold set, get.
  destruct (L.beq v L.bot) eqn:EBOT.
  rewrite lidTree.grspec. destruct ( lidTree.elt_eq q p). subst. destruct (loc_id_eq p p) eqn:?.
  apply L.eq_sym. SearchAbout L.beq. apply L.beq_correct in EBOT. eauto. contradiction n; eauto.
  destruct (loc_id_eq q p). subst. contradiction n; eauto. eapply L.eq_refl.
  rewrite lidTree.gsspec. unfold lidTree.elt_eq. destruct (loc_id_eq q p); eapply L.eq_refl.
Qed.

Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof. unfold eq; intros; apply L.eq_refl. Qed.


Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  unfold eq; intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  unfold eq; intros. eapply L.eq_trans; eauto.
Qed.

Definition beq (x y: t) : bool := lidTree.beq L.beq x y.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  unfold beq; intros; red; intros. unfold get.
  rewrite lidTree.beq_correct in H. specialize (H p).
  destruct (x#p); destruct (y#p); intuition.
  apply L.beq_correct; auto.
  apply L.eq_refl.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot : t := lidTree.empty _.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot, get; intros; simpl. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.


Section COMBINE.

  Variable f: option L.t -> option L.t -> option L.t.
Hypothesis f_none_none: f None None = None.

Definition opt_eq (ox oy: option L.t) : Prop :=
  match ox, oy with
  | None, None => True
  | Some x, Some y => L.eq x y
  | _, _ => False
  end.

Lemma opt_eq_refl: forall ox, opt_eq ox ox.
Proof.
  intros. unfold opt_eq. destruct ox. apply L.eq_refl. auto.
Qed.

Lemma opt_eq_sym: forall ox oy, opt_eq ox oy -> opt_eq oy ox.
Proof.
  unfold opt_eq. destruct ox; destruct oy; auto. apply L.eq_sym.
Qed.

Lemma opt_eq_trans: forall ox oy oz, opt_eq ox oy -> opt_eq oy oz -> opt_eq ox oz.
Proof.
  unfold opt_eq. destruct ox; destruct oy; destruct oz; intuition.
  eapply L.eq_trans; eauto.
Qed.

Definition opt_beq (ox oy: option L.t) : bool :=
  match ox, oy with
  | None, None => true
  | Some x, Some y => L.beq x y
  | _, _ => false
  end.

Lemma opt_beq_correct:
  forall ox oy, opt_beq ox oy = true -> opt_eq ox oy.
Proof.
  unfold opt_beq, opt_eq. destruct ox; destruct oy; try congruence.
  intros. apply L.beq_correct; auto.
  auto.
Qed.

Definition tree_eq (m1 m2: lidTree.t L.t) : Prop :=
  forall i, opt_eq (lidTree.get i m1) (lidTree.get i m2).

Lemma tree_eq_refl: forall m, tree_eq m m.
Proof.
intros; red; intros; apply opt_eq_refl. Qed.

Lemma tree_eq_sym: forall m1 m2, tree_eq m1 m2 -> tree_eq m2 m1.
Proof.
intros; red; intros; apply opt_eq_sym; auto. Qed.

Lemma tree_eq_trans: forall m1 m2 m3, tree_eq m1 m2 -> tree_eq m2 m3 -> tree_eq m1 m3.
Proof.
intros; red; intros; apply opt_eq_trans with (lidTree.get i m2); auto. Qed.




Fixpoint combine_r  (p1: lidTree.t L.t) :=
  match p1 with
  | nil => nil
  | (key, val) :: tl => (key, f None val) :: combine_r tl
  end.
Print get. Print PCTree.get.
Fixpoint combine (p:lidTree.t L.t) (p1:lidTree.t L.t) :=
  match p with
  | nil => combine_r p1
  | (key, val) :: tl => (key, f val (lidTree.get key p1)) :: (combine tl p1)                       
  end.

Print opt_eq.

Print combine.






Lemma gcombine:
  forall m1 m2 i, opt_eq (lidTree.get i (combine m1 m2)) (f (lidTree.get i m1) (lidTree.get i m2)).
Proof. induction m1; simpl in *.
       +intros. induction m2. simpl in *. rewrite f_none_none. eauto. simpl in *. destruct a. simpl in *. destruct ( lidTree.elt_eq e i); subst; unfold opt_eq; eauto.
        destruct ( f None o); eauto; try eapply L.eq_refl.
       +intros. destruct a. simpl in *. destruct (lidTree.elt_eq e i). unfold opt_eq; subst; eauto. destruct ( f o m2 # i); eauto; eapply L.eq_refl. eauto.
        Qed.

End COMBINE.

Lemma gcombine_bot:
  forall f t1 t2 p,
  f None None = None ->
  L.eq (get p (combine f t1 t2))
       (match f t1#p t2#p with Some x => x | None => L.bot end).
Proof. intros. unfold get. simpl in *. generalize (gcombine f H t1 t2 p). unfold opt_eq. simpl in *. destruct ((combine f t1 t2) # p). intros. destruct ( f t1 # p t2 # p). eauto. inversion H0. intros. destruct ( f t1 # p t2 # p ). inversion H0. eapply L.eq_refl. Qed.

Definition lub (x y: t) : t :=
  lidTree.combine
    (fun a b =>
       match a, b with
       | Some u, Some v => Some (L.lub u v)
       | None, _ => b
       | _, None => a
       end)
    x y.


Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros.
  eapply L.ge_trans. apply L.ge_refl.
  apply gcombine_bot; auto. unfold get. destruct ( x # p).
  destruct (y # p ). simpl in *.  apply L.ge_lub_left. eapply L.ge_refl. eapply L.eq_refl.
  destruct (y # p). eapply L.ge_bot. eapply L.ge_refl. eapply L.eq_refl. Qed.


Lemma ge_lub_right:
  forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_bot; auto.
  unfold get. destruct y#p. destruct x#p.
  apply L.ge_lub_right.
  apply L.ge_refl. apply L.eq_refl.
  apply L.ge_bot.
Qed.
End lidMap1.









Module lidPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

Inductive t' : Type :=
  | Bot: t'
  | Top_except: lidTree.t L.t -> t'.

Definition t: Type := t'.

Definition get (p: local_id) (x: t) : L.t :=
  match x with
  | Bot => L.bot
  | Top_except m => match m#p with None => L.top | Some x => x end
  end.

Definition set (p: local_id) (v: L.t) (x: t) : t :=
  match x with
  | Bot => Bot
  | Top_except m =>
      if L.beq v L.bot
      then Bot
      else Top_except (if L.beq v L.top then lidTree.remove p m else lidTree.set p v m)
  end.
SearchAbout local_id.
Lemma gsspec:
  forall p v x q,
  x <> Bot -> ~L.eq v L.bot ->
  L.eq (get q (set p v x)) (if loc_id_eq q p then v else get q x).
Proof.
  intros. unfold set. destruct x. congruence.
  destruct (L.beq v L.bot) eqn:EBOT.
  elim H0. apply L.beq_correct; auto.
  destruct (L.beq v L.top) eqn:ETOP; simpl.
  rewrite lidTree.grspec. 

  destruct ( lidTree.elt_eq q p). subst.
  destruct (loc_id_eq p p). eapply L.eq_sym.
eapply L.beq_correct. eauto.

  contradiction n; eauto.
destruct (loc_id_eq q p). subst. contradiction n; eauto.
eapply L.eq_refl. 
rewrite lidTree.gsspec. unfold lidTree.elt_eq. destruct (loc_id_eq q p). eapply L.eq_refl. eapply L.eq_refl. 
Qed.

Definition eq (x y: t) : Prop :=
  forall p, L.eq (get p x) (get p y).

Lemma eq_refl: forall x, eq x x.
Proof.
  intros. unfold eq. simpl in *. intros. apply L.eq_refl. Qed.




Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
intros. unfold eq in *. intros. eapply L.eq_sym.   eauto. Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
unfold eq. intros. eapply L.eq_trans; eauto. Qed.

Definition beq (x y: t) : bool :=
  match x, y with
  | Bot, Bot => true
  | Top_except m, Top_except n => lidTree.beq L.beq m n
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  destruct x; destruct y; simpl; intro; try congruence.
  apply eq_refl.
  red; intro; simpl.
  rewrite lidTree.beq_correct in H. generalize (H p).
  destruct (t0#p); destruct (t1#p); intuition.
  apply L.beq_correct; auto.
  apply L.eq_refl.
Qed.
  
Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  unfold ge, eq; intros. apply L.ge_refl. auto.
Qed.


Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.


Definition bot := Bot.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot; intros; simpl. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.


Definition top := Top_except (lidTree.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof.
  unfold top; intros; simpl. eauto. 
Qed.


Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.


Module LM := lidMap1(L).

Definition opt_lub (x y: L.t) : option L.t :=
  let z := L.lub x y in
  if L.beq z L.top then None else Some z.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top_except m, Top_except n =>
      Top_except
        (lidTree.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => opt_lub u v
              | _, _ => None
              end)
           m n)
  end.

Lemma gcombine_top:
  forall f t1 t2 p,
  f None None = None ->
  L.eq (get p (Top_except (LM.combine f t1 t2)))
       (match f t1#p t2#p with Some x => x | None => L.top end).
Proof. intros. induction t1; simpl in *.
       +induction t2. simpl in *. rewrite H. apply L.eq_refl. simpl in *. destruct a. simpl in *.
        destruct ( lidTree.elt_eq e p); subst; eauto. apply L.eq_refl.
       +destruct a; simpl in *. destruct ( lidTree.elt_eq e p); subst; eauto. eapply L.eq_refl.
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, lub; intros. destruct x; destruct y.
  rewrite get_bot. apply L.ge_bot.
  rewrite get_bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
  unfold get. destruct t0#p. destruct t1#p.
  unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
  apply L.ge_top. apply L.ge_lub_left.
  apply L.ge_top.
  apply L.ge_top.
Qed.


  
Lemma ge_lub_right:
  forall x y, ge (lub x y) y.
Proof.
  unfold ge, lub; intros. destruct x; destruct y.
  rewrite get_bot. apply L.ge_bot.
  apply L.ge_refl. apply L.eq_refl.
  rewrite get_bot. apply L.ge_bot.
  eapply L.ge_trans. apply L.ge_refl. apply gcombine_top; auto.
  unfold get. destruct t0#p; destruct t1#p.
  unfold opt_lub. destruct (L.beq (L.lub t2 t3) L.top) eqn:E.
  apply L.ge_top. apply L.ge_lub_right.
  apply L.ge_top.
  apply L.ge_top.
  apply L.ge_top.
Qed.


End lidPMap.


(*************************)