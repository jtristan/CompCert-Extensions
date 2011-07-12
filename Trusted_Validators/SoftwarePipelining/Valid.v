
Require Import List. 
Require Import SE. 
Require Import Sym. 

Import Sym.M. 

Fixpoint repeat (l : list instruction) (n : nat) {struct n} : list instruction :=
  match n with
  | O => nil
  | S n => List.app l (repeat l n)
  end.

Lemma repeat_inv : 
  forall (n : nat) l,
  l ++ repeat l n = repeat l n ++ l.
Proof. 
  induction n; intros. 
  simpl. rewrite app_nil_end. trivial. 
  simpl.
  rewrite app_ass.  
  rewrite <- IHn. trivial. 
Qed.  

Lemma repeat_plus:
  forall l a b, 
  repeat l (a + b) = repeat l a ++ repeat l b. 
Proof. 
  induction a; intros.
  simpl. trivial.  
  simpl. rewrite IHa.  
  rewrite app_ass. trivial. 
Qed. 
  
Lemma repeat_prod:
  forall l a b,
  repeat l (a * b) = repeat (repeat l b) a.
Proof. 
  induction a; intros. 
  simpl. trivial. 
  simpl. rewrite <- IHa. 
  rewrite repeat_plus. trivial. 
Qed. 
 
Lemma dec_to_eq :
  forall b p bt e mu delta n,
  dec (evaluate (repeat b mu)) (evaluate (p ++ e)) = true ->
  dec (evaluate (e ++ (repeat b delta))) (evaluate (bt ++ e)) = true ->
  (evaluate (repeat b (mu + n * delta))) ~ (evaluate (p ++ repeat bt n ++ e)).
Proof. 
  induction n; intros. 
  
  simpl. generalize (dec_correct H); intro. 
  rewrite <- H1. 
  assert (mu + 0 = mu)%nat by omega.
  rewrite H2. auto. 

  simpl. rewrite repeat_inv.
  rewrite app_ass. 
  generalize (IHn H H0); intro IND. clear IHn. 
  generalize (dec_correct H0); intro END. clear H H0. 
  rewrite repeat_plus.
  assert (delta0 + n * delta0 = n * delta0 + delta0)%nat by omega.
  rewrite H. clear H.  
  rewrite repeat_plus. 
  rewrite <- app_ass. rewrite <- app_ass. 
  rewrite decomposition. rewrite <- repeat_plus.
  rewrite decomposition.
  assert ((evaluate (repeat b (mu + n * delta0))) ^^ (evaluate (repeat b delta0)) ~ (evaluate (p ++ repeat bt n ++ e)) ^^ (evaluate (repeat b delta0))).
  auto. 
  rewrite H. clear H. 
  assert ((evaluate (p ++ repeat bt n)) ^^ (evaluate (bt ++ e)) ~ (evaluate (p ++ repeat bt n)) ^^ (evaluate (e ++ repeat b delta0))). 
  auto. 
  rewrite H. clear H. 
  rewrite <- decomposition. 
  rewrite <- decomposition. 
  rewrite app_ass. rewrite app_ass. rewrite app_ass. trivial. 
Qed.  

Lemma final :
  forall ge b p bt e mu delta n,
  dec (evaluate (repeat b mu)) (evaluate (p ++ e)) = true ->
  dec (evaluate (e ++ (repeat b delta))) (evaluate (bt ++ e)) = true ->
  forall s s',
  lsteps ge (repeat b (mu + n * delta)) s s' -> lsteps ge (p ++ repeat bt n ++ e) s s'.
Proof. 
  intros. 
  generalize (dec_to_eq _ _ _ _ _ _ n H H0); intro.
  generalize (correct H2); intro. 
  rewrite <- H3. trivial. 
Qed.  



Lemma dec_elt_to_dec : 
  forall b p bt mu delta r n,
  only (get (evaluate (repeat b delta)) r) r = true ->
  only (get (evaluate bt) r) r = true ->
  dec_elt (get (evaluate (repeat b mu)) r) (get (evaluate p) r) = true ->
  dec_elt (get (evaluate (repeat b delta)) r) (get (evaluate bt) r) = true ->
  (get (evaluate (repeat b (mu + n * delta))) r) = (get (evaluate (p ++ repeat bt n)) r).
Proof. 
  induction n; intros. 

  simpl. 
  assert (mu + 0 = mu)%nat by omega. rewrite H3. clear H3.
  rewrite <- app_nil_end. 
  generalize (dec_elt_correct H1); intro. trivial.  
  
  generalize (IHn H H0 H1 H2); intro IND. 
  generalize (dec_elt_correct H2); intro END.
  clear IHn H1 H2. 
  simpl. 
  rewrite repeat_inv. rewrite <- app_ass. 
  rewrite repeat_plus. 
  assert (delta0 + n * delta0 = n * delta0 + delta0)%nat by omega.
  rewrite H1. clear H1. 
  rewrite repeat_plus. rewrite <- app_ass. 
  assert ((evaluate ((repeat b mu ++ repeat b (n * delta0)) ++ repeat b delta0)) ~ ((evaluate ((repeat b mu ++ repeat b (n * delta0)))) ^^ (evaluate (repeat b delta0)))). 
  auto. 
  generalize (get_compatibility r H1); intro.
  rewrite H2. clear H2. 
  assert ((evaluate ((p ++ repeat bt n) ++ bt)) ~ (evaluate (p ++ repeat bt n)) ^^ (evaluate (bt))).
  auto. 
  generalize (get_compatibility r H2); intro. 
  rewrite H3. clear H2 H3 H1.  
  generalize (get_decomposition); intro. 
  generalize (get_decomposition ((evaluate (repeat b mu ++ repeat b (n * delta0)))) H); intro.
  generalize (get_decomposition (evaluate (p ++ repeat bt n)) H0); intro.
  rewrite <- IND in H3. 
  rewrite repeat_plus in H3.
  rewrite <- END in H3.
  rewrite H3 in H2. 
  inversion H2; subst. trivial. 
Qed.  

Lemma cut_repeat_one:
  forall ge l i s s',
  lsteps ge (i :: l) s s' ->
  exists si, lsteps ge (i :: nil) s si /\ lsteps ge l si s'.
Proof. 
  intros. 
  destruct i; intros. 

  inversion H; subst; try congruence. inversion H0; subst. 
  exists (mkst stack c sp (Registers.Regmap.set res (Registers.Regmap.get arg rs) rs) m).
  split. 
  eapply exec_Imove; eauto. eapply exec_start; eauto. 
  auto. 

  inversion H; subst; try congruence. inversion H0; subst. 
  exists (mkst stack c sp (Registers.Regmap.set res v rs) m).
  split. 
  eapply exec_Iop; eauto. eapply exec_start; eauto. 
  auto.

  inversion H; subst; try congruence. inversion H0; subst. 
  exists (mkst stack c sp (Registers.Regmap.set dst v rs) m0). 
  split. 
  eapply exec_Iload; eauto. eapply exec_start; eauto. 
  auto. 

  inversion H; subst; try congruence. inversion H0; subst. 
  exists (mkst stack c sp rs m'). 
  split. 
  eapply exec_Istore; eauto. eapply exec_start; eauto. 
  auto.  
  
Qed.   

Lemma cut_repeat:
  forall ge l l' s s',
  lsteps ge (l ++ l') s s' ->
  exists si, lsteps ge l s si /\ lsteps ge l' si s'.
Proof. 
  induction l; intros. 
  simpl in H. 
  exists s. 
  split; trivial. 
  eapply exec_start; eauto. 
  simpl in H. 
  generalize (cut_repeat_one _ _ _ _ _ H); intro.
  destruct H0 as [si [A B]]. 
  generalize (IHl _ _ _ B); intro.
  destruct H0 as [sif [C D]].
  exists sif. intuition. 
  destruct a. 
  destruct s. eapply exec_Imove ; eauto. 
  inversion A; subst; try congruence. inversion H0; subst. inversion H3; subst; try congruence.     
  destruct s. 
  inversion A; subst; try congruence. inversion H2; subst.  inversion H0; subst. inversion H4; subst; try congruence.
  eapply exec_Iop; eauto. 
  destruct s. 
  inversion A; subst; try congruence. inversion H2; subst.  inversion H0; subst. inversion H5; subst; try congruence.
  eapply exec_Iload; eauto. 
  destruct s. 
  inversion A; subst; try congruence. inversion H2; subst.  inversion H0; subst. inversion H5; subst; try congruence.
  eapply exec_Istore; eauto. 
Qed.   

Lemma cut_repeat_plus:
  forall ge a b l s s',
  lsteps ge (repeat l (a + b)) s s' -> exists si, lsteps ge (repeat l a) s si /\ lsteps ge (repeat l b) si s'.
Proof. 
  intros. 
  rewrite repeat_plus in H.
  generalize (cut_repeat _ _ _ _ _ H); intro.
  trivial. 
Qed. 







