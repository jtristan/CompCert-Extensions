
Require Import List.
Require Import RTL.
Require Import Coqlib. 
Require Import Maps. 
Require Import Smallstep. 
Require Import Events. 
Require Import Registers. 
Require Import SE. 

Parameter ooo : Op.operation -> option SE.operation. 

Definition convert (i : RTL.instruction) : option instruction :=
  match i with
  | RTL.Iop Op.Omove (b :: nil) c l => Some (Imove b c)
  | RTL.Iop Op.Omove _ c l => None
  | RTL.Iop (Op.Ocmp _) b c l => None
  | RTL.Iop o b c l => match ooo o with Some o => Some (Iop o b c) | None => None end
  | RTL.Iload a b c d l => Some (Iload a b c d)
  | RTL.Istore a b c d l => Some (Istore a b c d)
  | _ => None
  end. 

Axiom inst_eq : forall (x y : instruction), {x = y} + {x <> y}. 

Definition ieq (i : RTL.instruction) (j : instruction) : bool :=
  match convert i with
  | Some i => if inst_eq i j then true else false
  | None => false
  end. 

Definition next (i : RTL.instruction) : option positive :=
  match i with
  | RTL.Iop _ _ _ l => Some l 
  | RTL.Iload _ _ _ _ l => Some l
  | RTL.Istore _ _ _ _ l => Some l
  | RTL.Inop l => Some l
  | _ => None
  end.
   
Fixpoint not_in r lr {struct lr} : bool :=
  match lr with
  | nil => true
  | i :: l => if peq r i then false else not_in r l
  end.

Lemma inversion_not_in:
  forall r l a,
  not_in r (a :: l) = true -> a <> r /\ not_in r l = true.
Proof. 
  intros. 
  simpl in H. 
  case_eq (peq r a); intros. 
  rewrite H0 in H. congruence. 
  rewrite H0 in H. 
  intuition.
Qed. 

Fixpoint in_ r lr {struct lr} : bool :=
  match lr with
  | nil => false
  | i :: l => if peq r i then true else in_ r l
  end.

Lemma inversion_in_:
  forall r l a,
  in_ r (a :: l) = true-> a = r \/ in_ r l = true.
Proof. 
  intros. 
  simpl in H. 
  case_eq (peq r a); intros. 
  rewrite H0 in H. clear H0; subst. 
  left; trivial. 
  rewrite H0 in H. 
  right; trivial. 
Qed. 

Fixpoint match_straight_new (graph : code) (src target : positive) (regs : list reg) (l : list instruction) {struct l} : bool :=
  not_in src regs &&
  match l with 
  | nil => false
  | i :: nil => if peq src target then true else false && match graph ! src with
                  | Some j => if ieq j i 
                         then match next j with
                                  | Some p => not_in p (src :: regs)
                                  | None => false
                                  end
                         else false
                 | None => false
                 end
  | i :: l =>  match graph ! src with
                  | Some j => if ieq j i 
                         then match next j with
                                  | Some p => match_straight_new graph p target (src :: regs) l 
                                  | None => false
                                  end
                         else false
                 | None => false
                 end
  end.

Fixpoint match_straight (graph : code) (src target : positive) (regs : list reg) (l : list instruction) {struct l} : bool :=
  not_in src regs &&
  match l with 
  | nil => if peq src target then true else false
  | i :: l => match graph ! src with
                  | Some j => if ieq j i 
                         then match next j with
                                  | Some p => match_straight graph p target (src :: regs) l 
                                  | None => false
                                  end
                         else false
                 | None => false
                 end
  end.

Lemma inversion_match_straight:
  forall g src target regs a l,
  match_straight g src target regs (a :: l) = true ->
  not_in src regs = true /\
  exists j, g ! src = Some j /\ 
  convert j = Some a /\
  exists p, next j = Some p /\ match_straight g p target (src :: regs) l = true.
Proof.
  intros. 
  simpl in H. 
  case_eq (not_in src regs); intros. 2: rewrite H0 in H; simpl in H; congruence.  
  rewrite H0 in H. simpl in H.
  case_eq (g ! src); intros. 2: rewrite H1 in H; congruence. 
  rewrite H1 in H. 
  case_eq (ieq i a); intros. 
  2: rewrite H2 in H; congruence. 
  rewrite H2 in H. 
  case_eq (next i); intros. 
  2: rewrite H3 in H; congruence. 
  rewrite H3 in H. 
  unfold ieq in H2. 
  case_eq (convert i); intros. 
  2: rewrite H4 in H2; congruence. 
  rewrite H4 in H2. 
  case_eq (inst_eq i0 a); intros.
  2: rewrite H5 in H2; congruence. 
  clear H5; subst. clear H2. 
  intuition. 
  exists i. intuition. 
  exists p. intuition.
Qed.  

Lemma in_or_not:
  forall r1 r2 l,
  in_ r1 l = true ->
  not_in r2 l = true ->
  r1 <> r2.
Proof. 
  induction l; intros. 
  simpl in H. congruence.
  generalize (inversion_in_ _ _ _ H); intro. 
  generalize (inversion_not_in _ _ _ H0); intro. 
  destruct H2. 
  destruct H1. 
  subst.
  trivial. 
  eapply IHl; eauto. 
Qed. 
  
Lemma path_aux:
  forall graph src l src2 target regs,
  in_ src regs = true ->
  match_straight graph src2 target regs l = true ->
  src <> target.
Proof. 
  induction l; intros. 
  
  simpl in H0. 
  case_eq (not_in src2 regs); intros. 
  rewrite H1 in H0. simpl in H0. 
  case_eq (peq src2 target); intros. 
  clear H2. subst. eapply in_or_not; eauto.
  rewrite H2 in H0. congruence. 
  rewrite H1 in H0. simpl in H0. congruence. 

  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro.
  destruct H1 as [A [j [B [C [p [ D E]]]]]].
  case_eq (length l); intros. 

  destruct l. 2: simpl in H1; congruence.
  simpl in E. 
  case_eq (peq p target); intros. rewrite H2 in E.  clear H2. subst. 
  case_eq (peq target src2); intros. rewrite H2 in E. simpl in E. congruence.
  rewrite H2 in E. 
  case_eq (not_in target regs); intros.
  eapply in_or_not; eauto. 
  rewrite H3 in E. simpl in E. congruence. 

  rewrite H2 in E. destruct  (if peq p src2 then false else not_in p regs); simpl in E; try congruence.  
  assert (in_ src (src2 :: regs) = true). simpl.  rewrite H. destruct (peq src src2); trivial.  
  generalize (IHl _ _ _ H2 E); intro.
  trivial. 
Qed. 
   
Lemma path_move:
  forall graph src target a l,
  match_straight graph src target nil (a :: l) = true ->
  src <> target.
Proof. 
  intros. 
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H0 as [A [j [B [C [p [ D E]]]]]].  
  eapply (path_aux graph src l p target (src :: nil)); eauto.
  simpl; trivial. 
  case_eq (peq src src); intros.
  trivial. 
  congruence. 
Qed. 

Lemma match_straight_uniqueness :
  forall g w1 w2 src target regs, 
  match_straight g src target regs w1 = true ->
  match_straight g src target regs w2 = true ->
  w1 = w2.
Proof. 
  induction w1; intros. 
  simpl in H. 
  case_eq (peq src target); intros.
  clear H1. subst. destruct w2. trivial. 
  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro.
  destruct H1 as [A [j [B [C [p [ D E]]]]]].
  assert (in_ target (target :: regs) = true). simpl. case_eq (peq target target); intros. trivial. congruence.  
  generalize (path_aux _ _ _ _ _ _ H1 E); intros.
  congruence. 
  rewrite H1 in H. destruct (not_in src regs); simpl in H; congruence.
  
  destruct w2. admit. (* facile *)
  generalize (inversion_match_straight _ _ _ _ _ _ H);intro. 
  generalize (inversion_match_straight _ _ _ _ _ _ H0);intro.
  destruct H1 as [A1 [j1 [B1 [C1 [p1 [D1 E1]]]]]].
  destruct H2 as [A2 [j2 [B2 [C2 [p2 [D2 E2]]]]]].
  rewrite B2 in B1. inversion B1; subst. 
  rewrite D2 in D1. inversion D1; subst. 
  generalize (IHw1 w2 _ _ _ E1 E2); intro.
  subst. 
  rewrite C2 in C1. inversion C1; subst.
  trivial. 
Qed.   

Lemma inversion_match_straight_inv:
  forall g target a l src regs,
  match_straight g src target regs (l ++ (cons a nil)) = true ->
  exists p, exists i,
  g ! p = Some i /\ convert i = Some a /\ next i = Some target /\ match_straight g src p regs l =true.
Proof. 
  induction l; intros.
  replace (nil ++ a :: nil) with (a :: nil) in H.
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro. 
  destruct H0 as [A [j [B [C [p [D E]]]]]].
  simpl. exists src. exists j. intuition. simpl in E.  
  assert (p = target). destruct (peq p target); try congruence. destruct (if peq p src then false else not_in p regs); try congruence. simpl in E. congruence.
  simpl in E. congruence. congruence. 
  rewrite A. 
  simpl. destruct (peq src src); congruence.
  simpl. trivial. 
  rewrite <- app_comm_cons in H. 
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H0 as [A [j [B [C [p [D E]]]]]].
  generalize (IHl _ _ E); intro. 
  destruct H0 as [p' [i' [A' [B' [C' D']]]]]. 
  simpl in D'. 
  exists p'. exists i'. 
  intuition. 
  simpl.
  rewrite A. simpl. 
  rewrite B. 
  unfold ieq. rewrite C. 
  assert ((if inst_eq a0 a0 then true else false) = true). destruct (inst_eq a0 a0); congruence.
  rewrite H0. 
  rewrite D.
  trivial. 
Qed. 
  
Lemma linearity_aux:
  forall g w1 src l1 l2 r w2,
  match_straight g src l1 r w1 = true ->
  match_straight g src l2 r w2 = true ->
  (length w1 < length w2)%nat ->
  exists r', exists w, match_straight g l1 l2 r' w = true.
Proof. 
  induction w1; intros. 
  simpl in H. 
  case_eq (not_in src r); intros.
  rewrite H2 in H. simpl in H. 
  case_eq (peq src l1); intros. 
  clear H3. subst. exists r; exists w2. trivial. 
  rewrite H3 in H. congruence. 
  rewrite H2 in H. simpl in H. congruence. 
  
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H2 as [A [j [B [C [p [D E]]]]]].
  destruct w2. simpl in H1. elimtype False. omega.
  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro.
  destruct H2 as [A' [j' [B' [C' [p' [D' E']]]]]].
  rewrite B in B'. inversion B'; subst. rewrite D' in D. inversion D; subst. 
  assert (length w1 < length w2)%nat. simpl in H1. omega.
  generalize (IHw1 _ _ _ _ _ E E' H2); intro.
  destruct H3 as [r' [w GEN]]. 
  exists r'; exists w. trivial. 
Qed. 

Lemma linearity_aux_boing:
  forall g w1 src l1 l2 r w2,
  match_straight g src l1 r w1 = true ->
  match_straight g src l2 r w2 = true ->
  (length w1 < length w2)%nat ->
  exists w, exists r',
  (length w > O)%nat /\ 
 match_straight g l1 l2 r' w = true /\
 w2 = w1 ++ w.
Proof. 
  induction w1; intros. 
  simpl in H. exists w2; exists r. simpl; intuition. admit. (* oui *) 
  
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro. 
  destruct H2 as [A [j [B [C [p [D E]]]]]].
  destruct w2. elimtype False. simpl in H1. omega.
  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro.
  destruct H2 as [A' [j' [B' [C' [p' [D' E']]]]]].  
  rewrite B in B'. inversion B'; subst. rewrite D' in D. inversion D; subst. 
  assert (length w1 < length w2)%nat. simpl in H1. omega.
  generalize (IHw1 _ _ _ _ _ E E' H2); intro.
  destruct H3 as [w [r' [P [Q R]]]]. 
  exists w; exists r'. 
  rewrite <- app_comm_cons. 
  rewrite Q. 
  rewrite C in C' . intuition. congruence. 
Qed.
 
Lemma no_target :
  forall g w src target regs,
  in_ target regs = true ->
  match_straight g src target regs w = true ->
  False. 
Proof. 
  induction w; intros. 
  simpl in H0. assert (src = target). admit. subst. admit. (*trivial in not in*) 
  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro. 
  destruct H1 as [A [j [B [C [p [D E]]]]]].
  assert (in_ target (src :: regs) = true). simpl. rewrite H. admit. (* trivial *)
  generalize (IHw _ _ _ H1 E); intro.
  inversion H2.
Qed.  

Lemma straight_one:
  forall g target w src regs i a,
  (length w > O)%nat ->
  match_straight g src target regs w = true ->
  g ! src = Some i -> next i = Some target ->
  convert i = Some a -> 
  w = a :: nil.
Proof. 
  intros until 1. revert H. intro POUM. intros.  destruct w. simpl in H. 
  simpl in POUM. elimtype False. omega. 
  
  destruct w. 
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro. 
  destruct H3 as [A [j [B [C [p [D E]]]]]].
  rewrite H0 in B. inversion B; subst. rewrite C in H2. inversion H2; subst. trivial. 

  generalize (inversion_match_straight _ _ _ _ _ _ H); intro. 
  destruct H3 as [A [j [B [C [p [D E]]]]]].
  rewrite H0 in B. inversion B; subst. rewrite H2 in C. inversion C; subst. 
  rewrite H1 in D. inversion D; subst. clear B C D. 
  
  generalize (inversion_match_straight _ _ _ _ _ _ E); intro.
  destruct H3 as [A' [j' [B' [C' [p' [D' E']]]]]].
  assert (in_ p (p :: src :: regs)= true). simpl. admit. (* trivial *)
  generalize (no_target _ _ _ _ _ H3 E'); intro. 
  inversion H4. 
Qed. 
  
Lemma great:
  forall g w1 src l1 l2 r w2 a i,
  match_straight g src l1 r w1 = true ->
  match_straight g src l2 r w2 = true ->
  (length w1 < length w2)%nat ->
  g ! l1 = Some i -> next i = Some l2 ->
  convert i = Some a -> 
  w2 = w1 ++ (cons a nil).
Proof. 
  intros. 
  generalize (linearity_aux_boing _ _ _ _ _ _ _ H H0 H1); intro.
  destruct H5 as [w [r' [A [B C]]]]. 
  rewrite C. 
  generalize (straight_one _ _ _ _ _ _ _ A B H2 H3 H4); intro.
  rewrite H5. 
  trivial. 
Qed. 

Lemma plop:
  forall g l1 l2 i,
  g ! l1 = Some i -> next i = Some l2 ->  
  forall w1 w2 r src,
  match_straight g src l1 r w1 = true ->
  match_straight g src l2 r w2 = true ->
  (length w1 < length w2)%nat.
Proof. 
  induction w1; intros.
  simpl. admit. (* detruire w2 et sanity check*)
  
  generalize (inversion_match_straight _ _ _ _ _ _ H1); intro. 
  destruct H3 as [A [j [B [C [p [D E]]]]]].
  destruct w2. 
  

  generalize (inversion_match_straight _ _ _ _ _ _ H4); intro. 
  destruct H5 as [A' [j' [B' [C' [p' [D' E']]]]]].
  rewrite B in B' . inversion B'; subst. rewrite C in C'. inversion C'; subst. rewrite D in D'. inversion D'; subst.
  
  generalize (IHw1 _ _ _ E E'); intro.
  simpl. omega. 
Qed.   
 

Lemma linearity_aux_2:
  forall g w src l1 l2 r,
  match_straight g src l1 r w = true ->
  match_straight g src l2 r w = true ->
  l1 = l2. 
Proof. 
  induction w; intros. 
  simpl in H; simpl in H0. admit. (* trivial *)

  generalize (inversion_match_straight _ _ _ _ _ _ H); intro. 
  destruct H1 as [A [j [B [C [p [D E]]]]]].
  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro. 
  destruct H1 as [A' [j' [B' [C' [p' [D' E']]]]]].
  rewrite B in B'. inversion B'; subst. rewrite D' in D. inversion D; subst.   
  generalize (IHw _ _ _ _ E E'); intro. trivial. 
Qed.  

(*
Lemma triangle:
  forall g w src l i j regs,
  match_straight g src l regs w = true ->
  g ! src = Some i ->  g ! l = Some j -> next i = next j ->
  l <> src -> False.
Proof. 
  intros. destruct w. 
  simpl in H.
  case_eq (peq src l); intros. congruence.
  rewrite H4 in H. destruct (not_in src regs); simpl in H; congruence.
  
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H4 as [A [ii [B [C [p [D E]]]]]].
  rewrite H0 in B. inversion B; subst.   
  *)

Lemma losange:
  forall g src w1 l1 l2 r w2 i1 i2,
  match_straight g src l1 r w1 = true ->
  match_straight g src l2 r w2 = true ->
  g ! l1 = Some i1 -> g ! l2 = Some i2 ->
  next i1 = next i2 ->
  l1 = l2.
Proof. 
  intros.
  generalize (linearity _ _ _ _ _ _ _ H H0); intro. 
  destruct H4. 
  destruct H4 as [r' [w G]].
  destruct w. simpl in G. admit. (* trivial *)
  generalize (inversion_match_straight _ _ _ _ _ _ G); intro. 
  destruct H4 as [A [ii [B [C [p [D E]]]]]].
  rewrite B in H1. inversion H1; subst. rewrite D in H3.   

  destruct w. 
  simpl in E. 
  assert (p <> l1). admit. 
  assert (p = l2). admit. 
  generalize (path_aux); intro.
  generalize (inversion_match_straight _ _ _ _ _ _ G); intro.
  destruct H7 as [A' [ii' [B' [C' [p' [D' E']]]]]].
  assert (in_ l1 (l1 :: r') = true). admit.  
  generalize (path_aux _ _ _ _ _ _ H7 E'); intro.  
 


  induction w1; intros.
  simpl in H. 
  case_eq (not_in src r); intros.
  rewrite H4 in H. simpl in H. 
  case_eq (peq src l1); intros. 
  clear H5. subst.
  destruct w2.
  simpl in H0. rewrite H4 in H0. simpl in H0. 
  case_eq (peq l1 l2); intros. 
  clear H5. trivial.  rewrite H5 in H0. congruence. 
  generalize (inversion_match_straight _ _ _ _ _ _ H0); intro. 
  destruct H5 as [A [j [B [C [p [D E]]]]]].
  rewrite B in H1. inversion H1; subst. rewrite D in H3. 
  
  

Lemma test:
  forall ge g src stack l1 w1 w2 i a sp rs1 m1 l2 rs2 m2 t,   
  match_straight g src l1 nil w1 = true ->
  g!l1 = Some i -> convert i = Some a ->
  step ge (State stack g sp l1 rs1 m1) t (State stack g sp l2 rs2 m2) ->
  match_straight g src l2 nil w2 = true ->
  w2 <> nil ->
  w2 = w1 ++ (cons a nil).
Proof. 
  intros.
  assert (exists b, exists w, w2 = w ++ (cons b nil)). admit.  
  destruct H5 as [b [w L]]. 
  subst.
  generalize (inversion_match_straight_inv _ _ _ _ _ _ H3); intro. 
  destruct H5 as [p [ii [A [B [C D]]]]].

  assert (next i = Some l2). (* Doit provenir de la reduction *) admit.
  unfold node in H5. 
  rewrite <- C in H5.
  generalize (losange _ _ _ _ _ _ _ _ _ H D H0 A H5); intro.
  subst. 
  generalize (match_straight_uniqueness _ _ _ _ _ _ D H); intro.subst. 
  
  rewrite H0 in A. inversion A; subst. rewrite B in H1. congruence. 
Qed. 

Lemma linear_to_real: 
  forall ge stack graph target sp l src rs m rs' m',
  match_straight graph src target l = true ->  
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m') ->
  star step ge (State stack graph sp src rs m) E0 (State stack graph sp target rs' m').
Proof. 
  induction l; intros.

  inversion H0; subst; try congruence.
  simpl in H. 
  case_eq (peq src target); intros. 2: rewrite H1 in H; congruence. 
  clear H1. subst. eapply Smallstep.star_refl; eauto.

  simpl in H. 
  case_eq (graph ! src); intros.
  2: rewrite H1 in H; congruence. 
  rewrite H1 in H. 
  case_eq (ieq i a); intros.
  2: rewrite H2 in H; congruence. 
  rewrite H2 in H. 
  case_eq (next i); intros. 
  2:rewrite H3 in H; congruence. 
  rewrite H3 in H.
 
  inversion H0; subst.
 
  inversion H4; subst. inversion H5; subst. 
  generalize (IHl _ _ _ _ _ H H7); intro.
  assert (E0 = E0 ** E0). traceEq. 
  eapply star_left; eauto.
  unfold ieq in H2. 
  case_eq (convert i); intros. 
  2: rewrite H9 in H2; congruence. 
  rewrite H9 in H2. 
  case_eq (inst_eq i0 (Imove arg res)); intros. 
  2: rewrite H10 in H2; congruence. 
  clear H10. subst. 
  destruct i; simpl in H9; try congruence.
  analyze H9 for o (ooo o) l. Show 10.  



  inversion H4; subst. inversion H6; subst. 
  generalize (IHl _ _ _ _ _ H H8); intro.
  eapply star_one; eauto. 
  admit. 

  inversion H4; subst. inversion H7; subst. 
  generalize (IHl _ _ _ _ _ H H9); intro.
  assert (E0 = E0 ** E0). traceEq. 
  eapply star_left; eauto. 
  unfold ieq in H2. 
  case_eq (convert i); intros. 
  2: rewrite H11 in H2; congruence. 
  rewrite H11 in H2. 
  case_eq (inst_eq i0 (Iload chunk addr args dst)); intros. 
  2: rewrite H12 in H2; congruence. 
  clear H12. subst. 
  destruct i; simpl in H11; try congruence.
  admit. (* infamie liee a ooo et oo*) 
  
  inversion H11; subst. 
  simpl in H3. inversion H3; subst. 
  eapply RTL.exec_Iload; eauto. 

  
(*
Inductive cstar (ge: genv) (l : list node): RTL.state -> trace -> RTL.state -> Prop :=
  | star_refl: forall s g sp p rs m,
      In p l ->
      cstar ge l (State s g sp p rs m) E0 (State s g sp p rs m)
  | star_step: forall s1 g1 sp1 p1 rs1 m1 s2 g2 sp2 p2 rs2 m2 s3 g3 sp3 p3 rs3 m3 t1 t2 t ,
      In p1 l ->
      step ge (State s1 g1 sp1 p1 rs1 m1) t1 (State s2 g2 sp2 p2 rs2 m2) -> cstar ge l (State s2 g2 sp2 p2 rs2 m2) t2 (State s3 g3 sp3 p3 rs3 m3) -> t = t1 ** t2 ->
      cstar ge l (State s1 g1 sp1 p1 rs1 m1) t (State s3 g3 sp3 p3 rs3 m3).

  *)

(*
Fixpoint match_straight_aux (graph : code) (src target : positive) (l : list instruction) {struct l} : bool :=
  match l with 
  | nil => if peq src target then true else false
  | i :: l => match graph ! src with
                  | Some j => if ieq j i 
                         then match next j with
                                  | Some p => match_straight_aux graph p target l 
                                  | None => false
                                  end
                         else false
                 | None => false
                 end
  end. 

Definition match_straight (graph : code) (src target : positive) (l : list instruction) : bool :=
  match_straight_aux graph src target l && if peq src target then false else true.
*)

Inductive sstar (ge: genv): nat -> RTL.state -> trace -> RTL.state -> Prop :=
  | star_refl: forall s,
      sstar ge O s E0 s
  | star_step: forall n s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> sstar ge n s2 t2 s3 -> t = t1 ** t2 ->
      sstar ge (S n) s1 t s3.

Definition shortest (l l' : node) (n : nat) ge stack stack' g g' sp sp' rs m t : Prop := ~ (exists p, exists rs', exists m', 
  (p < n)%nat /\ sstar ge p (State stack g sp l rs m) t (State stack' g' sp' l' rs' m')).

Parameter P : genv -> RTL.state -> trace -> RTL.state -> Prop. 
Axiom no_loop : 
  forall ge stack stack' g g' sp sp' pc rs rs' m m' t, 
  P ge (State stack g sp pc rs m) t (State stack' g' sp' pc rs' m') ->
  (State stack g sp pc rs m) = (State stack' g' sp' pc rs' m').
Axiom invariant_goes :
  forall ge S t S' Sf t',
  P ge S t S' -> step ge S' t' Sf -> P ge S (t ** t') Sf.
Axiom inversion_P: 
  forall ge S t S',
  P ge S t S' -> (t = E0 /\ S = S') \/ exists Si, exists t1, exists t2, step ge S t1 Si /\ P ge Si t2 S' /\ t = t1 ** t2. 

Lemma balaise : 
  forall ge stack graph target sp l src rs m rs' m',
  
  match_straight graph src target regs l = true ->  
  P ge (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
Proof. 
  induction l; intros. 
  simpl in H. 
  assert (src = target). case_eq (peq src target); intros. trivial. rewrite H1 in H. congruence. 
  subst. 
  generalize (no_loop _ _ _ _ _ _ _ _ _ _ _ _ _ H0); intro. inversion H1; subst.
  eapply exec_start; eauto.
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H1 as [A [j [B [C [p [ D E]]]]]].
  generalize (path_move _ _ _ _ _ H); intro.
  generalize (inversion_P _ _ _ _ H0); intro.
  destruct H2.
  intuition. congruence.
  destruct H2 as [Si [t1 [t2 [F [G I]]]]].

  destruct Si. 
  assert (t1 = E0). 
    inversion F; subst; try congruence.
  subst. simpl in I. 
  subst. 
  assert (p = pc). 
    unfold next in D. 
    inversion F; subst; try congruence; 
    try (rewrite B in H3; inversion H3; subst; congruence);
    try (rewrite B in H4; inversion H4; subst; congruence);
    try (rewrite B in H5; inversion H5; subst; congruence). 
  subst. 
  assert (graph = c /\ stack0 = stack /\ sp0 = sp). 
    intuition; inversion F; subst; try congruence.
  intuition. subst.
  assert (match_straight c pc target nil l = true). (* pour test *) admit. 
  generalize (IHl _ rs0 m0 rs' m' H2 G); intro. 
  admit. (* plop *)

  inversion F; subst. 
  rewrite H9 in B. inversion B; subst. simpl in D. congruence. 
  rewrite H9 in B. inversion B; subst. simpl in D. congruence.
  inversion F; subst. 
  rewrite H9 in B. inversion B; subst. simpl in D. congruence.
Qed.   

Lemma balaise : 
  forall ge stack graph target sp l src rs m rs' m',
  match_straight graph src target nil l = true ->  
  P ge (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
Proof. 
  induction l; intros. 
  simpl in H. 
  assert (src = target). case_eq (peq src target); intros. trivial. rewrite H1 in H. congruence. 
  subst. 
  generalize (no_loop _ _ _ _ _ _ _ _ _ _ _ _ _ H0); intro. inversion H1; subst.
  eapply exec_start; eauto.
  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H1 as [A [j [B [C [p [ D E]]]]]].
  generalize (path_move _ _ _ _ _ H); intro.
  generalize (inversion_P _ _ _ _ H0); intro.
  destruct H2.
  intuition. congruence.
  destruct H2 as [Si [t1 [t2 [F [G I]]]]].

  destruct Si. 
  assert (t1 = E0). 
    inversion F; subst; try congruence.
  subst. simpl in I. 
  subst. 
  assert (p = pc). 
    unfold next in D. 
    inversion F; subst; try congruence; 
    try (rewrite B in H3; inversion H3; subst; congruence);
    try (rewrite B in H4; inversion H4; subst; congruence);
    try (rewrite B in H5; inversion H5; subst; congruence). 
  subst. 
  assert (graph = c /\ stack0 = stack /\ sp0 = sp). 
    intuition; inversion F; subst; try congruence.
  intuition. subst.
  assert (match_straight c pc target nil l = true). (* pour test *) admit. 
  generalize (IHl _ rs0 m0 rs' m' H2 G); intro. 
  admit. (* plop *)

  inversion F; subst. 
  rewrite H9 in B. inversion B; subst. simpl in D. congruence. 
  rewrite H9 in B. inversion B; subst. simpl in D. congruence.
  inversion F; subst. 
  rewrite H9 in B. inversion B; subst. simpl in D. congruence.
Qed.   
  



Lemma plop:
  forall ge stack c sp src rs m rsi mi j a pc rs' m' l, 
step ge (State stack c sp src rs m) E0 (State stack c sp pc rsi mi) ->
c ! src = Some j -> convert j = Some a -> next j = Some pc -> 
lsteps ge l (mkst stack c sp rsi mi) (mkst stack c sp rs' m') ->
lsteps ge (a :: l) (mkst stack c sp rs m) (mkst stack c sp rs' m').
Proof. 
  intros. 
  destruct a. 
  admit. 
  admit. (* deux cas merdics a cause de ooo *)

  destruct j; simpl in *|-; try congruence. 
  admit. (* bordel de ooo*)
  
  inversion H2; subst. inversion H1; subst. inversion H; subst; try congruence.
  rewrite H0 in H7. inversion H7; subst. 
  eapply exec_Iload; eauto.
Admitted. 
 
(*
Lemma test : 
  forall ge stack graph target sp l src rs m rs' m' n regs,
  match_straight graph src target regs l = true ->  
  sstar ge n (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  shortest src target n ge stack stack graph graph sp sp rs m E0 ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
*)



Lemma test : 
  forall ge stack graph target sp l src rs m rs' m' n,
  match_straight graph src target nil l = true ->  
  sstar ge n (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  shortest src target n ge stack stack graph graph sp sp rs m E0 ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
Proof. 
  induction l; intros. 
  
  simpl in H. assert (src = target). case_eq (peq src target); intros. trivial. rewrite H2 in H. congruence.  
  subst. clear H. 
  unfold shortest in H1. 
  intuition. 
  assert (sstar ge O (State stack graph sp target rs m) E0 (State stack graph sp target rs m)). 
  eapply star_refl; eauto.
  destruct n. 
  inversion H0; subst. 
  eapply exec_start; eauto. 
  elimtype False. apply H1. 
  exists O. exists rs. exists m.   
  intuition; try omega.

  generalize (inversion_match_straight _ _ _ _ _ _ H); intro.
  destruct H2 as [A [j [B [C [p [ D E]]]]]].

  assert (src <> target). admit.  
  destruct n. inversion H0; congruence. (* grace a src <> target *)
  unfold shortest in H1.
  inversion H0; subst. 
  destruct s2.
 
 assert (match_straight graph p target nil l = true). admit. (* completement faux, tricherie pour test *)
  assert (t1 = E0). 
    inversion H4; subst; try congruence.
  subst. simpl in H6. 
  subst. 
  assert (p = pc). 
    unfold next in D. 
    inversion H4; subst; try congruence;
    try (rewrite B in H7; inversion H7; subst; congruence);
    try (rewrite B in H8; inversion H8; subst; congruence);
    try (rewrite B in H9; inversion H9; subst; congruence). 
  subst. 
  assert (graph = c /\ stack0 = stack /\ sp0 = sp). 
    intuition; inversion H4; subst; try congruence.
  intuition. subst.
  assert (    shortest pc target n ge stack stack c c sp sp rs0 m0 E0). 
    unfold shortest. intuition. 
    destruct H6 as [p [rs'' [m'' [I J]]]].
    assert (sstar ge (S p) (State stack c sp src rs m) (E0 ** E0) (State stack c sp target rs'' m'')). 
    eapply star_step; eauto.
    apply H1. 
    exists (S p). exists rs''. exists m''. 
    intuition. 
  generalize (IHl _ _ _ _ _ _ H3 H5 H6); intro.
  eapply plop; eauto.

  inversion H4; subst. 
  rewrite H13 in B. inversion B; subst. simpl in D. congruence. 
  rewrite H13 in B. inversion B; subst. simpl in D. congruence.
  inversion H4; subst. 
  rewrite H13 in B. inversion B; subst. simpl in D. congruence.
Qed. 
  
  




  



Lemma test : 
  forall ge stack graph target sp l src rs m rs' m',
  match_straight graph src target nil l = true ->  
  star step ge (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
Proof.   
  induction l; intros. 

  simpl in H.
  case_eq (peq src target); intros. 2: rewrite H1 in H; congruence. 
  clear H1. 
  subst. 


 


Tactic Notation "remember" constr(a) "in" hyp(H) 
  "as" ident(x) ident(EQ) := 
  (set (x:=a) in H; assert (EQ: a = x) 
   by reflexivity; clearbody x).

Tactic Notation "remember" constr(a) "in" hyp(H) 
  "as" ident(x) := 
  let EQ := fresh "EQ" in remember a in H as x EQ.

Tactic Notation "killif" hyp(H) "as" ident(y) :=
  match type of H with context[if ?x then _ else _] => 
  remember x in H as y; destruct y; try congruence
  end. 

Tactic Notation "killif" hyp(H) :=
  let y := fresh in killif H as y. 

Tactic Notation "analyze" hyp(H) "for" constr(a) "as" ident(x) :=
  remember a in H as x;
  let rec doit _ := 
    match type of H with 
    | context [x] => destruct x; try congruence; try doit tt
    end
    in
  try doit tt.

Tactic Notation "analyze" hyp(H) "for" constr(a) :=
  let x := fresh "x" in try (analyze H for a as x); try repeat killif H.
Tactic Notation "analyze" hyp(H) "for" constr(a1) constr(a2) :=
  analyze H for a1; analyze H for a2.
Tactic Notation "analyze" hyp(H) "for" constr(a1) constr(a2) constr(a3) :=
  analyze H for a1; analyze H for a2 a3.
(*

*)
 
 
Lemma test : 
  forall ge stack graph target sp l src rs m rs' m',
  match_path graph src target l = true ->  
  sstar ge (length l) (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
Proof. 
  induction l; intros. 
  
  simpl in H0. inversion H0; subst. eapply exec_start; eauto. 

  simpl in H0. simpl in H. 
  case_eq (graph ! src); intros.
  2: rewrite H1 in H; congruence. 
  rewrite H1 in H. 
  case_eq (ieq i a); intros.
  2: rewrite H2 in H; congruence. 
  rewrite H2 in H. 
  case_eq (next i); intros. 
  2:rewrite H3 in H; congruence. 
  rewrite H3 in H. 
  
  inversion H0; subst. destruct s2. 
  assert (t2 = E0 /\ stack = stack0 /\ sp = sp0 /\ c = graph /\ pc = p). admit. intuition. subst. 
  generalize (IHl _ _ _ _ _ H H6); intro.
  clear IHl H0 H6. 
  unfold ieq in H2. 
  case_eq (convert i); intros.
  2: rewrite H0 in H2; congruence.
  rewrite H0 in H2. 
  case_eq (inst_eq i0 a); intros. 
  2: rewrite H6 in H2; congruence. 
  clear H6. subst. clear H2. 
  
  destruct a. 
  admit. 
  admit. 

  unfold convert in H0. analyze H0 for i.
  admit. (* Saloperie ooo*)
  
  subst.
  inversion H0; subst.simpl in H3. inversion H3; subst. 
  inversion H5; subst; try congruence. 
  rewrite H1 in H13. inversion H13; subst. 
  eapply exec_Iload; eauto. 
  
  Lemma test : 
  forall ge stack graph target sp l src rs m rs' m',
  match_path graph src target l = true ->  
  star step ge (State stack graph sp src rs m) E0 (State stack graph sp target rs' m') ->
  lsteps ge l (mkst stack graph sp rs m) (mkst stack graph sp rs' m').
Proof.
  induction l; intros. 
  
  simpl in H. 
  case_eq (peq src target); intros. 
  clear H1. subst. inversion H0; subst. eapply exec_start; eauto.  
  
  rewrite H1 in H. congruence. 
 
  assert (length (a :: l) > 0)%nat. simpl. omega. 
  generalize (path_move _ _ _ _ H1 H); intro DIFF. clear H1.  
  simpl in H. 
  case_eq (graph ! src); intros.
  2: rewrite H1 in H; congruence. 
  rewrite H1 in H. 
  case_eq (ieq i a); intros.
  2: rewrite H2 in H; congruence. 
  rewrite H2 in H. 
  case_eq (next i); intros. 
  2:rewrite H3 in H; congruence. 
  rewrite H3 in H. 

  inversion H0; subst. inversion H0; congruence.  
  destruct s2. 
  generalize (IHl p rs0 m0 rs' m' H); intro.
  assert (t1 = E0). 
    inversion H4; subst; try congruence.
  subst. simpl in H6. 
  subst. 
  assert (p = pc). 
    unfold next in H3. 
    inversion H4; subst; try congruence;
    try (rewrite H1 in H8; inversion H8; subst; congruence);
    try (rewrite H1 in H9; inversion H9; subst; congruence);
    try (rewrite H1 in H10; inversion H10; subst; congruence). 
  subst. 
  assert (graph = c /\ stack0 = stack /\ sp0 = sp). 
    intuition; inversion H4; subst; try congruence.
  intuition. subst.   
  
  generalize (H7 H5); intro. 
  
  unfold ieq in H2.
  case_eq (convert i); intros. 
  2: rewrite H8 in H2; congruence. 
  rewrite H8 in H2. 
  case_eq (inst_eq i0 a); intros.
  2: rewrite H9 in H2; congruence. 
  clear H9. subst.
  destruct i; simpl in H8; try congruence; simpl in H3; inversion H3; subst. 
  inversion H4; subst; try congruence. admit. (* Saloperies a cause de oo ooo etc...*) 

  inversion H8; subst. inversion H4; subst; try congruence. rewrite H1 in H12; inversion H12; subst. 
  eapply exec_Iload; eauto.
  
  inversion H8; subst. inversion H4; subst; try congruence. rewrite H1 in H12; inversion H12; subst. 
  eapply exec_Istore; eauto.   

  inversion H4; subst. 
    rewrite H14 in H1. inversion H1; subst. simpl in H3. congruence. 
    rewrite H14 in H1. inversion H1; subst. simpl in H3. congruence.  
  inversion H4; subst. 
    rewrite H14 in H1. inversion H1; subst. simpl in H3. congruence.    
Qed.   


  
   


Fixpoint match_path (graph : code) (src target : positive) (l : list instruction) {struct l} : bool :=
  match l with 
  | nil => if peq src target then true else false
  | i :: l => match graph ! src with
                  | Some j => if ieq j i 
                         then match next j with
                                  | Some p => match_path graph p target l
                                  | None => false
                                  end
                         else false
                 | None => false
                 end
  end.








