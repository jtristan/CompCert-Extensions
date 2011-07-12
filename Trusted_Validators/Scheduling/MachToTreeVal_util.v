Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Mach.
Require Import Locations.
Require Import Maps.
Require Import Floats.
Require Import Machabstr.
Require Import Stackingproof.
Require Import Values.
Require Import Globalenvs.
Require Import Mem.
Require Import Events.
Require Import Two_level_repr.
Require Import Valcommon.
Require Import BasicLib. 
Require Import MachToTreeVal.

Section Val. 

Variable f : Mach.function. 
Variable cfg : Two_level_repr.function. 

Notation "a && b" := (andb a b). 

(** usefull lemmas *)

Lemma incl_prop:
  forall (i : Mach.instruction) c l,
  incl (i :: c) l -> incl c l.
Proof. 
  intros. 
  unfold incl in H. 
  unfold incl. 
  intros. 
  generalize (in_cons i a c H0); intro.
  eapply H; eauto. 
Qed. 

Lemma dec_imp_leibniz:
  forall (A : Set) (x y : A) (dec : forall x y, {x = y} + {x <> y}),
  (if dec x y then true else false) = true ->  x = y.
Proof. 
  intros. 
  case_eq (dec x y); intros. 
  trivial. 
  rewrite H0 in H. inversion H. 
Qed. 

Lemma dec_eq:
  forall (A : Set) (x : A) (dec : forall x y, {x = y} + {x <> y}),
  (if dec x x then true else false) = true. 
Proof. 
  intros. 
  case_eq (dec x x); intros. trivial. 
  congruence. 
Qed. 

Lemma find_label_prop:
  forall c c' lbl,
  find_label lbl c = Some c' ->
  incl (Mlabel lbl :: c') c.
Proof. 
  induction c; intros. 
  simpl in H. inversion H. 
  unfold incl. intros. simpl in H. 
  case_eq (is_label lbl a); intros. 
  rewrite H1 in H. injection H; intros; subst. 
  destruct a; try (simpl in H1; congruence).
  case_eq (peq lbl l); intros. 
    clear H2. subst. trivial.
    inversion H1; subst.
    assert (lbl = l). eapply dec_imp_leibniz; eauto. 
    congruence. 
    
  apply in_cons; eauto. 
  rewrite H1 in H. 
  generalize (IHc _ _ H); intro. 
  unfold incl in H2.  generalize (H2 a0 H0); intro.
  trivial. 
Qed.  

Lemma and_destruct: forall (a b : bool), a && b = true -> a = true /\ b = true.
intros a b.
case a; case b; auto.
Qed.

Lemma incl_tail:
  forall (l : code), incl (tail l) l.
Proof.
  destruct l.
  simpl; red; intuition trivial.
  simpl. red. intuition. 
Qed. 

Hint Resolve incl_prop. 
Hint Resolve dec_imp_leibniz. 
Hint Resolve find_label_prop. 
Hint Resolve and_destruct. 
Hint Resolve dec_eq. 
Hint Resolve incl_tail. 

Lemma mem_correct: 
  forall lbl keys,  
  mem lbl keys = true -> In lbl keys.
Proof. 
  induction keys; simpl ; intros. 
  congruence.
  case_eq (peq lbl a); intros. 
  clear H0; subst. intuition trivial. 
  rewrite H0 in H. 
  auto. 
Qed. 

Lemma mem_complete:
  forall lbl keys,
  mem lbl keys = false -> ~ In lbl keys. 
Proof. 
  induction keys; simpl; intros. 
  congruence. 
  intro. destruct H0. 
  subst. 
  case_eq (peq lbl lbl); intros. 
    rewrite H0 in H. congruence. 
    rewrite H0 in H. auto. 
  case_eq (peq lbl a); intros. 
  rewrite H1 in H. congruence. 
  rewrite H1 in H. generalize (IHkeys H); intro.  auto.
Qed.  

Definition suffix (l : code) (l' : code) : Prop := exists l1, l' = l1 ++ l. 

Lemma suffix_trans:
  forall i j w w',
  i <> j ->
  suffix (i :: w) (j :: w') ->
  suffix (i :: w) w'.
Proof. 
  intros. 
  unfold suffix in H0. 
  unfold suffix. 
  destruct H0.
  destruct x. 
  simpl in H0. inversion H0. congruence. 
  rewrite <- app_comm_cons in H0. inversion H0. 
  subst. exists x; trivial. 
Qed. 

Lemma In_mem:
  forall lbl ls,
  In lbl ls -> mem lbl ls = true.
Proof. 
  induction ls; intros. 
  inversion H. 
  simpl. case_eq (peq lbl a); intros. 
  trivial. destruct H. congruence. 
  eapply IHls; eauto. 
Qed. 

Lemma unic_prop:
  forall x lbl w ls,
  In lbl ls ->
  label_unicity (x ++ Mlabel lbl :: w) ls = false.
Proof. 
  induction x; intros. 
  simpl. 
  assert (mem lbl ls = true). eapply In_mem; eauto.  
  rewrite H0. trivial. 
  rewrite <- app_comm_cons.  
  destruct a; try (simpl;  eapply IHx; eauto). 
  simpl. 
  case_eq (mem l ls); intros. 
  trivial. 
  assert (In lbl (l :: ls)). right; trivial.  
  eapply IHx; eauto. 
Qed. 

Lemma label_unicity_prop_gen:
  forall c lbl ls w,
  label_unicity c ls = true ->
  ~ In lbl ls ->
  suffix (Mlabel lbl :: w) c ->
  find_label lbl c = Some w.
Proof. 
  induction c; intros. 
  unfold suffix in H1. 
  destruct H1. elimtype False. destruct x. simpl in H1; congruence. rewrite <- app_comm_cons in H1. inversion H1.   
  destruct a; try (simpl; simpl in *|-;
  eapply IHc; eauto; 
  unfold suffix in H1; destruct H1;
  unfold suffix;
  destruct x; [simpl in H1; congruence |
  rewrite <- app_comm_cons in H1;
  inversion H1; subst; exists x; trivial]).
  case_eq (peq lbl l); intros. 
    simpl. rewrite H2. clear H2. subst. 
    unfold suffix in H1. destruct H1. 
    destruct x. simpl in *|-; subst; inversion H1; trivial.
    rewrite <- app_comm_cons in H1. inversion H1; subst. simpl in H. 
       case_eq (mem l ls); intros. 
       rewrite H2 in H. congruence.  rewrite H2 in H. 
    assert (In l (l :: ls)). left; trivial. rewrite unic_prop in H. congruence.  trivial.  
    assert (suffix (Mlabel lbl :: w) c). eapply suffix_trans; eauto. 
    congruence. 
    simpl in H. 
    case_eq (mem l ls); intros. 
      rewrite H4 in H.  congruence. 
      rewrite H4 in H. 
    assert (~ In lbl (l :: ls)). intro. unfold In in H5. destruct H5. congruence. 
       unfold In in H0. congruence. 
    generalize (IHc _ _ _ H H5 H3); intro. 
    simpl. rewrite H2. trivial. 
Qed. 
     
Lemma unique_label:
  forall f lbl w, 
  label_unicity (fn_code f) nil = true ->
  suffix (Mlabel lbl :: w) (fn_code f) ->
  find_label lbl (fn_code f) = Some w.
Proof. 
  intros. eapply label_unicity_prop_gen; eauto. 
Qed.  
 
Lemma find_label_suff:
  forall lbl c c',
  find_label lbl c = Some c' ->
  suffix c' c.
Proof. 
  induction c; intros. 
  simpl in H. congruence. 
  simpl in H. 
  case_eq (is_label lbl a); intros. 
    rewrite H0 in H. 
    inversion H; subst. exists (cons a nil). 
    rewrite <- app_comm_cons. simpl. trivial.
    rewrite H0 in H. 
    generalize (IHc _ H); intro. inversion H1. 
    exists (a :: x). 
    rewrite <- app_comm_cons. subst. trivial. 
Qed.     
  
Lemma find_label_suff2:
  forall lbl c c',
  find_label lbl c = Some c' ->
  suffix (Mlabel lbl :: c') c.
Proof. 
  induction c; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  case_eq (is_label lbl a); intros.
    destruct a; try (inversion H0). 
    assert (lbl = l). eauto. subst. 
    rewrite H0 in H. 
    inversion H; subst. exists (@nil Mach.instruction). 
    trivial.
    rewrite H0 in H. 
    generalize (IHc _ H); intro. inversion H1. subst.  
    exists (a :: x).  
    rewrite <- app_comm_cons. subst. trivial. 
Qed.     

Lemma suff_tail:
  forall c,
  suffix (tail c) c.
Proof. 
  destruct c. 
  simpl. exists (@nil Mach.instruction).
  simpl. trivial.
  exists (i :: nil). simpl. trivial. 
Qed.   

Lemma get_labels_prop:
  forall lbl c,
  In lbl (get_labels c) ->
  exists w, suffix (Mlabel lbl :: w) c.
Proof. 
  induction c; intros. 
  simpl in H. inversion H.
  destruct a; simpl in H; try (generalize (IHc H); intro; destruct H0; inversion H0; subst; unfold suffix; exists x).
  exists (Mach.Mgetstack i t m :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Msetstack m i t :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mgetparam i t m :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mop o l m :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mload m a l m0 :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mstore m a l m0 :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mcall s s0 :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Malloc :: x0); rewrite <- app_comm_cons; congruence.
  destruct H. subst. exists c. exists (@nil Mach.instruction). trivial. 
  generalize (IHc H); intro; destruct H0; inversion H0; subst; unfold suffix; exists x.
  exists (Mach.Mlabel l :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mgoto l :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mcond c0 l l0 :: x0); rewrite <- app_comm_cons; congruence.
  exists (Mach.Mreturn :: x0); rewrite <- app_comm_cons; congruence.
Qed.   

Lemma suffix_fond:
  forall c i w,
  suffix (i :: w) c  -> suffix w c.
Proof. 
  intros. 
  inversion H.  unfold suffix. 
  subst. exists (x ++ i :: nil). 
  rewrite app_ass. simpl. trivial. 
Qed.  

Lemma check_target_prop_aux: 
  forall lbl c w,
  suffix c (fn_code f) ->
  check_target_aux c (get_labels (fn_code f)) = true ->
  suffix (Mach.Mgoto lbl :: w) c ->
  exists w', 
  suffix (Mach.Mlabel lbl :: w') (fn_code f).
Proof. 
  induction c; intros. 
  inversion H1. destruct x. simpl in H2; congruence. rewrite <- app_comm_cons in H2. congruence.  
  simpl in H0. 
  destruct a.
  assert (Mgoto lbl <> Mach.Mgetstack i t m). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Msetstack m i t). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Mgetparam i t m). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Mop o l m). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Mload m a l m0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Mstore m a l m0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Mcall s s0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Malloc). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mgoto lbl <> Mach.Mlabel l). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro.
  case_eq (peq lbl l); intros. 
    clear H4. subst. exists c. trivial.  
    generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H5 H0 H3); intro.
  inversion H6. inversion H7. subst. 
  exists x. 
  exists x0.  
  trivial.    

  generalize (essai _ _ H0); intro. destruct H2. 
  case_eq (peq lbl l); intros. 
  clear H4. subst. 
  generalize (mem_correct _ _ H2); intro. 
  generalize (get_labels_prop _ _ H4); intro.
  generalize (suffix_fond _ _ _ H); intro. 
  destruct H5. 
  inversion H5. unfold suffix.
  exists x. 
  exists x0. trivial. 
  
  assert (Mgoto lbl <> Mach.Mgoto l). congruence.    
  generalize (suffix_trans _ _ _ _ H5 H1); intro.
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H7 H3 H6); intro.
  inversion H8. inversion H9.  
  exists x. exists x0. trivial.       

  assert (Mgoto lbl <> Mach.Mcond c0 l l0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (essai _ _ H0); intro. destruct H5. 
  generalize (IHc _ H4 H6 H3); intro. trivial. 
  (* inversion H4. inversion H7. 
  exists x. unfold suffix.  
  exists x0. trivial.  *)

  assert (Mgoto lbl <> Mach.Mreturn). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  
Qed.   

Lemma check_target_prop: 
  forall lbl w,
  check_target f = true ->
  suffix (Mach.Mgoto lbl :: w) (fn_code f) ->
  exists w',
  suffix (Mach.Mlabel lbl :: w') (fn_code f).
Proof. 
  intros.
  assert (suffix (fn_code f) (fn_code f)). exists (@nil Mach.instruction). trivial. 
  eapply check_target_prop_aux; eauto.
Qed. 

Lemma check_target_prop_aux2: 
  forall lbl c w cond args,
  suffix c (fn_code f) ->
  check_target_aux c (get_labels (fn_code f)) = true ->
  suffix (Mach.Mcond cond args lbl :: w) c ->
  exists w', 
  suffix (Mach.Mlabel lbl :: w') (fn_code f).
Proof. 
  induction c; intros. 
  inversion H1. destruct x. simpl in H2; congruence. rewrite <- app_comm_cons in H2. congruence.  
  simpl in H0. 
  destruct a.
  assert (Mach.Mcond cond args lbl <> Mach.Mgetstack i t m). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Msetstack m i t). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Mgetparam i t m). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Mop o l m). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Mload m a l m0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Mstore m a l m0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Mcall s s0). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Malloc). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  

  assert (Mach.Mcond cond args lbl <> Mach.Mlabel l). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro.
  case_eq (peq lbl l); intros. 
    clear H4. subst. exists c. trivial.  
    generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H5 H0 H3); intro.
  inversion H6. inversion H7. subst. 
  exists x. 
  exists x0.  
  trivial.    

  assert (Mach.Mcond cond args lbl <> Mach.Mgoto l). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro.
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (essai _ _ H0); intro. destruct H5. 
  generalize (IHc _ _ _ H4 H6 H3); intro. trivial.

  generalize (essai _ _ H0); intro. destruct H2. 
  case_eq (peq lbl l0); intros. 
  clear H4. subst. 
  generalize (mem_correct _ _ H2); intro. 
  generalize (get_labels_prop _ _ H4); intro.
  generalize (suffix_fond _ _ _ H); intro. 
  destruct H5. 
  inversion H5. unfold suffix.
  exists x. 
  exists x0. trivial. 

  assert (Mach.Mcond cond args lbl <> Mach.Mcond c0 l l0). congruence.    
  generalize (suffix_trans _ _ _ _ H5 H1); intro.
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H7 H3 H6); intro.
  inversion H8. inversion H9.  
  exists x. exists x0. trivial.       

  assert (Mach.Mcond cond args lbl <> Mach.Mreturn). congruence.    
  generalize (suffix_trans _ _ _ _ H2 H1); intro. 
  generalize (suffix_fond _ _ _ H); intro. 
  generalize (IHc _ _ _ H4 H0 H3); intro.
  inversion H5. inversion H6. 
  exists x. unfold suffix.  
  exists x0. trivial.  
Qed.   

Lemma check_target_prop2: 
  forall lbl w cond args,
  check_target f = true ->
  suffix (Mach.Mcond cond args lbl :: w) (fn_code f) ->
  exists w',
  suffix (Mach.Mlabel lbl :: w') (fn_code f).
Proof. 
  intros.
  assert (suffix (fn_code f) (fn_code f)). exists (@nil Mach.instruction). trivial. 
  eapply check_target_prop_aux2; eauto.
Qed. 

Lemma skip_control_correct:
  forall ge f sp parent s n c rs fr m c',
    skip_control s (fn_code f) c n = Some c' ->
    Machabstr.exec_instrs ge f sp parent c rs fr m E0 c' rs fr m.
Proof. 
  induction n; intros. 
  simpl in H. inversion H. 
  destruct c. 
    simpl in H. inversion H. 
    destruct i; try ( 
    simpl in H; inversion H; subst; eapply Machabstr.exec_refl). 
    case_eq (mem l s); intros. 
      simpl in H. rewrite H0 in H. inversion H. eapply Machabstr.exec_refl. 
      simpl in H. rewrite H0 in H. 
      generalize (IHn c rs fr m c' H); intro. 
      assert (Machabstr.exec_instrs ge f0 sp parent (Mlabel l :: c) rs fr m E0 c rs fr m).
        eapply Machabstr.exec_one; eauto. 
        eapply Machabstr.exec_Mlabel; eauto.
        eapply Machabstr.exec_trans; eauto.
      traceEq. 
    case_eq (mem l s); intros. 
      simpl in H.
      case_eq (find_label l (fn_code f0)); intros. 
        rewrite H1 in H. rewrite H0 in H. inversion H. 
        subst. eapply Machabstr.exec_refl.
        rewrite H1 in H. inversion H.
      simpl in H. 
      case_eq (find_label l (fn_code f0)); intros. 
      rewrite H1 in H. rewrite H0 in H. 
      generalize (IHn _ rs fr m _ H); intro. 
      assert (Machabstr.exec_instrs ge f0 sp parent (Mgoto l :: c) rs fr m E0 c0 rs fr m). 
        eapply Machabstr.exec_one; eauto. 
        eapply Machabstr.exec_Mgoto; eauto.
        eapply Machabstr.exec_trans; eauto.
        traceEq. 
      rewrite H1 in H. inversion H. 
Qed. 


Lemma test_out_prop:
  forall sub lbl, test_out sub lbl = true -> sub = Two_level_repr.Mout lbl. 
Proof. 
  destruct sub; intros; try (simpl in H; inversion H).
  case_eq (peq lbl l); intros. 
    congruence. 
    rewrite H0 in H. inversion H.
Qed.  

Lemma skip_control_valid:
  forall s n l l',
  skip_control s (fn_code f) l n = Some l' ->
  forall t, validTreeProp f s l' t -> validTreeProp f s l t.
Proof. 
  induction n; intros.
  simpl in H. inversion H. 
  destruct l. simpl in H. inversion H.
  destruct i; try (simpl in H; inversion H; subst; trivial).
    case_eq (mem l0 s); intros. 
      rewrite H1 in H2. 
      inversion H2; subst. trivial. 
      rewrite H1 in H2. 
      generalize (IHn _ _ H2 _ H0); intro.
      eapply labelControl; eauto. eapply mem_complete; eauto.  
    case_eq (find_label l0 (fn_code f)); intros. 
      rewrite H1 in H2. 
      case_eq (mem l0 s); intros. 
        rewrite H3 in H2. inversion H2; subst. trivial. 
        rewrite H3 in H2. 
        generalize (IHn _ _ H2 _ H0); intro. 
        eapply gotoControl; eauto. eapply mem_complete; eauto. 
    rewrite H1 in H2. 
  inversion H2. 
Qed.     

Lemma skip_stop:
  forall s n l0 c l w,
  skip_control s c l0 n = Some (Mlabel l :: w) ->
  In l s.
Proof. 
  induction n; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  case_eq l0; intros.
  rewrite H0 in H. inversion H. 
  rewrite H0 in H. 
  destruct i; try (inversion H). 
  case_eq (mem l2 s); intros. 
    rewrite H1 in H2. inversion H2; subst. eapply mem_correct; eauto. 
    rewrite H1 in H2. 
    eapply IHn; eauto. 
  case_eq (find_label l2 c); intros. 
  rewrite H1 in H2. 
  case_eq (mem l2 s); intros. 
    rewrite H3 in H2. inversion H2; subst. 
    rewrite H3 in H2. eapply IHn; eauto. 
  rewrite H1 in H2. inversion H2. 
Qed. 

Lemma skip_stop2:
  forall s n l0 c l w,
  skip_control s c l0 n = Some (Mgoto l :: w) ->
  In l s.
Proof. 
  induction n; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  case_eq l0; intros.
  rewrite H0 in H. inversion H. 
  rewrite H0 in H. 
  destruct i; try (inversion H). 
  case_eq (mem l2 s); intros. 
    rewrite H1 in H2. inversion H2. 
    rewrite H1 in H2. eapply IHn; eauto.  
  case_eq (find_label l2 c); intros. 
  rewrite H1 in H2. 
  case_eq (mem l2 s); intros. 
    rewrite H3 in H2. inversion H2; subst. eapply mem_correct; eauto.  
    rewrite H3 in H2. eapply IHn; eauto. 
  rewrite H1 in H2. inversion H2. 
Qed. 

Lemma link: forall s t l, validTreeBase f s l t = true -> validTreeProp f s l t.
  induction t; intros.

  (* getstack *)
  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i0; try inversion H. clear H3. 
    generalize (and_destruct _ _ H); intro. destruct H2. clear H.  
    generalize (IHt l0 H3); intro. clear H3.
    assert (validTreeProp f s (Mach.Mgetstack i0 t m :: l0) (Mgetstack i0 t m t0)).
      generalize (and_destruct _ _ H2); intro. destruct H3. 
      generalize (and_destruct _ _ H3); intro. destruct H5. clear H2 H3. 
      eapply getStackSync; eauto. 
    subst. 
    eapply skip_control_valid; eauto.
    generalize (essai _ _ H2); intro. destruct H1. 
    generalize (essai _ _ H1); intro. destruct H5. 
    assert (i = i0). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence.   
    assert (t1 = t). generalize (dec_imp_leibniz _ _ _ _ H6); intro; congruence. 
    assert (m0 = m). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence. 
    subst. trivial. 

  rewrite H0 in H. inversion H. 

  (* setstack *)

  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i0; try inversion H. clear H3. 
    generalize (and_destruct _ _ H); intro. destruct H2. clear H.  
    generalize (IHt l0 H3); intro. clear H3.

  eapply skip_control_valid; eauto. 
  generalize (essai _ _ H2); intro. destruct H3. generalize (essai _ _ H3); intro. destruct H5.   
  assert (i0 = i). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence. 
  assert (t1 = t). generalize (dec_imp_leibniz _ _ _ _ H6); intro; congruence. 
  assert (m0 = m). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence. subst. 
  eapply setStackSync; eauto. 
  rewrite H0 in H. inversion H.   

  (* getparam *)

  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i0; try inversion H. clear H3. 
    generalize (and_destruct _ _ H); intro. destruct H2. clear H.  
    generalize (IHt l0 H3); intro. clear H3.

  eapply skip_control_valid; eauto. 
  generalize (essai _ _ H2); intro. destruct H3. generalize (essai _ _ H3); intro. destruct H5.   
  assert (i0 = i). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence. 
  assert (t1 = t). generalize (dec_imp_leibniz _ _ _ _ H6); intro; congruence.  
  assert (m0 = m). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence.  subst. 
  eapply getParamSync; eauto. 
  rewrite H0 in H. inversion H.   

  (* op *)

  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l0 (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i; try inversion H. clear H3. 
    generalize (and_destruct _ _ H); intro. destruct H2. clear H.  
    generalize (IHt l1 H3); intro. clear H3.  

  eapply skip_control_valid; eauto. 
  generalize (essai _ _ H2); intro. destruct H3. generalize (essai _ _ H3); intro. destruct H5.   
  assert (o0 = o). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence. 
  assert (l = l2). generalize (dec_imp_leibniz _ _ _ _ H6); intro; congruence. 
  assert (m0 = m). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence.  subst.
  eapply opSync; eauto. 
  rewrite H0 in H. inversion H.   

  (* load *)

  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l0 (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i; try inversion H. clear H3. 
    generalize (and_destruct _ _ H); intro. destruct H2. clear H.  
    generalize (IHt l1 H3); intro. clear H3.

  eapply skip_control_valid; eauto. 
  generalize (essai _ _ H2); intro. destruct H3. generalize (essai _ _ H3); intro. destruct H5. generalize (essai _ _ H5); intro. destruct H7.    
  assert (m = m1). generalize (dec_imp_leibniz _ _ _ _ H8); intro; congruence. 
  assert (a = a0). generalize (dec_imp_leibniz _ _ _ _ H7); intro; congruence. 
  assert (l2 = l). generalize (dec_imp_leibniz _ _ _ _ H6); intro; congruence. 
  assert (m2 = m0). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence.  subst. 
  eapply loadSync; eauto. 
  rewrite H0 in H. inversion H.   

  (* store *)

  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l0 (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i; try inversion H. clear H3. 
    generalize (and_destruct _ _ H); intro. destruct H2. clear H.  
    generalize (IHt l1 H3); intro. clear H3.

  eapply skip_control_valid; eauto. 
    generalize (essai _ _ H2); intro. destruct H3. generalize (essai _ _ H3); intro. destruct H5. generalize (essai _ _ H5); intro. destruct H7.   
  assert (m = m1). generalize (dec_imp_leibniz _ _ _ _ H8); intro; congruence. 
  assert (a = a0). generalize (dec_imp_leibniz _ _ _ _ H7); intro; congruence. 
  assert (l2 = l). generalize (dec_imp_leibniz _ _ _ _ H6); intro; congruence. 
  assert (m2 = m0). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence.  subst. 
  eapply storeSync; eauto. 
  rewrite H0 in H. inversion H.   

  (* alloc *)

  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i; try inversion H. clear H3.   
    generalize (IHt l0 H); intro. clear H.

  eapply skip_control_valid; eauto. 
  subst. 
  eapply allocSync; eauto. 
  rewrite H0 in H. inversion H.   
    
  (* cond *)

  inversion H; subst. 
  case_eq (skip_control s (fn_code f) l0 (length (fn_code f))); intros. 
    rewrite H0 in H1.
    case_eq c0; intros. 
    rewrite H2 in H1. inversion H1. 
    rewrite H2 in H1. 
    destruct i; try inversion H1. clear H4.
    generalize (and_destruct _ _ H1); intro. destruct H3. clear H1.
    generalize (and_destruct _ _ H3); intro. clear H3. destruct H1.
    generalize (and_destruct _ _ H1); intro. clear H1. destruct H5.
    assert (c = c1). generalize (dec_imp_leibniz _ _ _ _ H1); intro; congruence. 
    assert (l = l2). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence. 
    subst. 
    case_eq (mem l3 s); intros.
      rewrite H2 in H4. 
      generalize (test_out_prop _ _ H4); intro.
      subst. 
      generalize (IHt2 _ H3); intro.  
      assert (validTreeProp f s (Mach.Mcond c1 l2 l3 :: l1) (Mcond c1 l2 (Mout l3) t2)).
        eapply condBack; eauto.
        eapply mem_correct; eauto.
        subst. 
        eapply skip_control_valid; eauto. 
        
    rewrite H2 in H4. 
    case_eq (find_label l3 (fn_code f)); intros. 
      rewrite H6 in H4. 
    generalize (IHt1 _ H4); intro. 
    generalize (IHt2 _ H3); intro.
    assert (validTreeProp f s (Mach.Mcond c1 l2 l3 :: l1) (Mcond c1 l2 t1 t2)).
      eapply condSync; eauto.
      eapply mem_complete; eauto. 
      eapply skip_control_valid; eauto. 

  rewrite H6 in H4. inversion H4. 
  rewrite H0 in H1. inversion H1. 
  
  (* out *)
  unfold validTreeBase in H.
  case_eq (skip_control s (fn_code f) l0 (length (fn_code f))); intros. 
    rewrite H0 in H. 
    case_eq c; intros. 
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct i; try inversion H. clear H3. 
    assert (validTreeProp f s (Mlabel l :: l1) (Mout l)). 
      eapply outSync; eauto. 
      assert (l2 = l). generalize (dec_imp_leibniz _ _ _ _ H); intro; congruence.  subst. 
      eapply skip_stop; eauto.  
    subst.
    assert (l2 = l). generalize (dec_imp_leibniz _ _ _ _ H); intro; congruence.  subst. 
    eapply skip_control_valid; eauto.
    assert (l2 = l). generalize (dec_imp_leibniz _ _ _ _ H); intro; congruence.  subst. 
    eapply skip_control_valid; eauto.
    assert (validTreeProp f s (Mgoto l :: l1) (Mout l)). 
      eapply gotoSync; eauto. 
      eapply skip_stop2; eauto.  
    subst.
    trivial. (* extremement etrange *) 
    rewrite H0 in H. inversion H. 
Qed.   

Lemma suff_lab:
  forall lbl w c,
  suffix (Mlabel lbl :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
  exists (x ++ Mlabel lbl :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_getstack:
  forall i t m w c,
  suffix (Mach.Mgetstack i t m :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Mgetstack i t m :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_setstack:
  forall i t m w c,
  suffix (Mach.Msetstack i t m :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Msetstack i t m :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_getparam:
  forall i t m w c,
  suffix (Mach.Mgetparam i t m :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Mgetparam i t m :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_op:
  forall i t m w c,
  suffix (Mach.Mop i t m :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Mop i t m :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_load:
  forall a b e d w c,
  suffix (Mach.Mload a b e d :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Mload a b e d :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_store:
  forall a b e d w c,
  suffix (Mach.Mstore a b e d :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Mstore a b e d :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Lemma suff_alloc:
  forall w c,
  suffix (Mach.Malloc :: w) c -> suffix w c.
Proof. 
  intros. 
  inversion H. 
   exists (x ++ Mach.Malloc :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. trivial.  
Qed. 

Hint Resolve suff_lab : suff. 
Hint Resolve suff_getstack : suff.
Hint Resolve suff_setstack : suff. 
Hint Resolve suff_getparam : suff. 
Hint Resolve suff_op : suff. 
Hint Resolve suff_load : suff. 
Hint Resolve suff_store : suff. 
Hint Resolve suff_alloc : suff.  

Definition put (i : Mach.instruction) (sub : instructions_tree) : option instructions_tree :=
  match i with
  | Mach.Mgetstack i t m => Some (Mgetstack i t m sub)
  | Mach.Msetstack m i t => Some (Msetstack m i t sub)
  | Mach.Mgetparam i t m => Some (Mgetparam i t m sub)
  | Mach.Mop a b c => Some (Mop a b c sub)
  | Mach.Mload a b c d => Some (Mload a b c d sub)
  | Mach.Mstore a b c d => Some (Mstore a b c d sub)
  | Mach.Malloc => Some (Malloc sub)
  | _ => None
  end.

Lemma list_prop':
  forall l k (a : positive),
  In k (a :: l) -> a <> k -> In k l.
Proof. 
  induction l; intros.
  inversion H. congruence. trivial. 
  unfold In in H. destruct H. congruence.
  destruct H. subst.  unfold In; left; trivial.
  assert (In k l = (fix In (a : positive) (l : list positive) {struct l} : Prop :=
       match l with
       | nil => False
       | b :: m => b = a \/ In a m
       end) k l). 
       unfold In. trivial. 
  rewrite <- H1 in H. eapply in_cons; eauto. 
Qed.  

Lemma fold_false:
  forall l f,
  fold_left
      (fun (acc : bool) (k : label) =>
       f k && acc) l false = true -> False. 
Proof. 
  induction l; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  assert (f0 a && false = false).  
    case_eq (f0 a); intros. 
    simpl. trivial. 
    simpl. trivial. 
  rewrite H0 in H. 
  eapply IHl; eauto. 
Qed.   
 
Lemma fold_prop:
  forall l k keys,
  List.fold_left (fun acc => fun k => (validLabel f cfg keys k) && acc ) l true = true ->
  In k l -> validLabel f cfg keys k = true.
Proof. 
  induction l; intros. 
    inversion H0. 
    case_eq (peq k a); intros.
    rewrite e. simpl in H. 
      case_eq (validLabel f cfg keys a); intros. 
      trivial. 
      rewrite H2 in H. simpl in H.  
        generalize (fold_false l (fun k => validLabel f cfg keys k) H); intro. 
        intuition. 
      simpl in H. 
      assert (In k l).
        eapply list_prop'; eauto. 
      eapply IHl; eauto. 
      case_eq (validLabel f cfg keys a); intros. 
      rewrite H3 in H. simpl in H. auto. 
      rewrite H3 in H. simpl in H. elimtype False. 
      generalize (fold_false l (fun k => validLabel f cfg keys k) H); intro. 
      intuition. 
Qed.     

Lemma isIn: 
  forall c1 l i,
  (cfg_code c1) ! l = Some i ->  
  In l (PTree.xkeys (cfg_code c1) xH).
Proof.
  intros.
  generalize (PTree.elements_correct _ _ H); intro. 
  unfold PTree.xkeys. unfold PTree.elements in H0. 
  generalize (in_map (@fst positive instruction) (PTree.xelements (cfg_code c1) 1) (l,i) H0); intro.
  simpl in H1. trivial. 
Qed.  

Lemma recover:
  forall (A B : Set) elt l,
  In elt (@fst A B) ## l -> 
  exists v, In (elt,v) l. 
Proof.
  induction l; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  destruct H. 
  subst. 
  exists (snd a). simpl. left. destruct a. simpl. trivial.  
  generalize (IHl H); intro. destruct H0 as [v PROP]. 
  exists v. simpl.  right; trivial. 
Qed. 

Lemma domain:
  forall lbl,
  In lbl (PTree.xkeys (cfg_code (fn_body cfg)) 1) ->
  exists im, (cfg_code (fn_body cfg))!lbl = Some im.
Proof. 
  intros. 
  unfold PTree.xkeys in H.
  assert (exists v, In (lbl,v) (PTree.xelements (cfg_code (fn_body cfg)) 1)). 
    eapply recover; eauto. 
  destruct H0 as [v PROP]. 
  exists v. eapply PTree.elements_complete; eauto.
Qed.  

Lemma remove_prop:
  forall l qqch elt,
  In elt (remove l qqch) -> In elt l.
Proof. 
  induction l; intros. 
  simpl in H; inversion H.
  simpl in H. 
  case_eq (peq a qqch); intros. 
    rewrite H0 in H. clear H0. subst. 
    generalize (IHl _ _ H); intro. 
    unfold In. right; trivial. 
    rewrite H0 in H. clear H0. 
    simpl in H.
    destruct H. subst. unfold In. left; trivial. 
    generalize (IHl _ _ H); intro. 
    unfold In. right; trivial. 
Qed. 
     
Lemma domain_reduced:
  forall lbl,
  In lbl (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1) (cfg_head (fn_body cfg)))->
  exists im, (cfg_code (fn_body cfg))!lbl = Some im.
Proof. 
  intros.
  generalize (remove_prop _ _ _ H); intro. 
  eapply domain; eauto. 
Qed. 
  
Lemma fold_prop_2:
  forall li lou l lbl i h,
  fold_left
      (fun (acc : bool) (k : positive) =>
       match l ! k with
       | Some i => wf_instruction i lou h
       | None => false
       end && acc) li true = true ->
  In lbl li ->
  l ! lbl = Some i ->
  wf_instruction i lou h = true.
Proof.
  induction li; intros. 
  inversion H0. 
  inversion H0.
  subst. simpl in H. 
  case_eq ((match l ! lbl with
        | Some i => wf_instruction i lou h
        | None => false
        end )); intros.
   rewrite H1 in H2. trivial. 
   rewrite H2 in H. simpl in H. elimtype False.
   generalize (fold_false li (fun k => match l ! k with
        | Some i => wf_instruction i lou h
        | None => false
        end) H); intro. trivial.  
 simpl in H.
 case_eq ((match l ! a with
        | Some i => wf_instruction i lou h
        | None => false
        end )); intros.
        rewrite H3 in H. simpl in H.
  inversion H0. subst. 
  rewrite H1 in H3. trivial. 
  generalize (IHli _ _ lbl i _ H H4 H1); intro. trivial. 
  rewrite H3 in H. simpl in H. elimtype False.
   generalize (fold_false li (fun k => match l ! k with
        | Some i => wf_instruction i lou h
        | None => false
        end) H); intro. trivial.  
Qed.   
  
Lemma remove_prop2:
  forall c elt qqch,
  In elt c ->
  elt <> qqch ->
  In elt (remove c qqch).
Proof. 
  induction c; intros. 
  inversion H. 
  destruct H. 
  subst. simpl. 
  case_eq (peq elt qqch); intros. 
    congruence. 
  left; trivial. 
  generalize (IHc _ _ H H0); intro. 
  simpl. 
  case_eq (peq a qqch); intros. 
  trivial. 
  right; trivial.
Qed.  

Lemma wf_call:
  forall lbl a b l,
  wf_cfg cfg = true ->
  (cfg_code (fn_body cfg)) ! lbl = Some (Mcall a b l) ->
  In l (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))). 
Proof.
  intros. 
  unfold wf_cfg in H. 
  generalize (isIn _ _ _ H0); intro.
  assert (wf_instruction (Mcall a b l) (PTree.xkeys (cfg_code (fn_body cfg)) 1) ((cfg_head (fn_body cfg))) = true).
    eapply fold_prop_2; eauto. 
  inversion H2; subst.
  generalize (essai _ _ H4); intro. destruct H3. 
  eapply remove_prop2; eauto. 
  eapply mem_correct; eauto. 
  case_eq (peq l (cfg_head (fn_body cfg))); intros.
    rewrite H6 in H5. congruence. 
    trivial. 
Qed.  

Lemma wf_tree:
  forall lbl tree,
  wf_cfg cfg = true ->
  (cfg_code (fn_body cfg)) ! lbl = Some (Two_level_repr.Mtree tree) ->
  wf_instruction (Mtree tree) (PTree.xkeys (cfg_code (fn_body cfg)) 1)
           (cfg_head (fn_body cfg)) = true.
Proof.
  intros. unfold wf_cfg in H. 
  generalize (isIn _ _ _ H0); intro.
  generalize (fold_prop_2 _ _ _ _ _ _ H H1 H0); intro.
  trivial. 
Qed. 

Lemma wf_tree_more:
  forall tge sp parent tree rs fr m t lbl' rs' fr' m',
  wf_instruction (Mtree tree)  (PTree.xkeys (cfg_code (fn_body cfg)) 1)
           (cfg_head (fn_body cfg)) = true ->
  Two_level_repr.exec_instructions_tree tge  tree sp parent  rs fr m t lbl' rs' fr' m' ->
  In lbl' (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))).
Proof.
  induction tree; intros; try ( 
  simpl in H; inversion H0; subst; eapply IHtree; eauto).
  simpl in H.
  generalize (essai _ _ H); intro. destruct H1. inversion H0; subst.
  eapply IHtree1; eauto. eapply IHtree2; eauto.
  inversion H0; subst. simpl in H.
  generalize (essai _ _ H); intro. destruct H1. 
  eapply remove_prop2; eauto. 
  eapply mem_correct; eauto. 
  case_eq (peq lbl' (cfg_head (fn_body cfg))); intros.
    rewrite H3 in H2. congruence. 
    trivial. 
Qed. 

Lemma wf_instr:
  forall tge sp parent lbl instr rs fr m t lbl' rs' fr' m' c,
  wf_cfg cfg = true ->
  (cfg_code (fn_body cfg)) ! lbl = Some instr ->
  validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))) c instr ->
  Two_level_repr.exec_instruction tge  (fn_body cfg) sp parent instr rs
       fr m t lbl' rs' fr' m' ->
  In lbl' (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))).
Proof.
  intros. 
  inversion H2; subst. inversion H1; subst.
  inversion H5; subst. trivial. inversion H5. 
  inversion H1; subst. inversion H2; subst.
  generalize (wf_tree _ _ H H0); intro.
  eapply wf_tree_more; eauto. 
  inversion H4. inversion H4.  
Qed.   

Lemma link_gen:
  forall lbl c i,
  validLabel f cfg (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))) lbl = true -> 
  wf_cfg cfg = true ->
  find_label lbl (fn_code f) = Some c ->
  (cfg_code (fn_body cfg))!lbl = Some i ->
  validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))) c i.
Proof. 
  intros until 1. intro WF. intros.  
  unfold validLabel in H. 
  rewrite H1 in H. 
  rewrite H0 in H. 

  destruct i. 
  
  eapply vTree; eauto.
  unfold validTreeIn in H. rewrite H0 in H. 
  eapply link; eauto.

  case_eq c; intros. 
  rewrite H2 in H. inversion H. 
  rewrite H2 in H. 
  destruct i; try inversion H. clear H4. 
  case_eq l0; intros. 
  rewrite H3 in H. inversion H. 
  rewrite H3 in H. 
  destruct i; try inversion H. clear H5. 
  eapply vCall; eauto.
  repeat (generalize (essai _ _ H); clear H; intro H; destruct H).  
  assert (s = s1). generalize (dec_imp_leibniz _ _ _ _ H); intro; congruence. 
  assert (s0 = s2). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence. 
  assert (l = l2). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence. 
  subst. clear H.
  generalize (wf_call _ _ _ _ WF H1); intro. 
  eapply validCall; eauto. 
  eapply outSync; eauto.
 
  case_eq c; intros. 
  rewrite H2 in H. inversion H. 
  rewrite H2 in H. 
  destruct i; try inversion H. 
  eapply vRet; eauto. 
  eapply validReturn; eauto. 
Qed. 

End Val.

Section TRIVIA.

Variable p: Mach.program.
Variable tp : program. 
Hypothesis tr_ok: transf_program p = Some tp. 
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact tr_ok.
Qed.

Axiom functions_translated:
  forall (v: val) (tf: Two_level_repr.fundef),
  Genv.find_funct tge v = Some tf ->
  exists f,
  Genv.find_funct ge v = Some f /\ transf_fundef f = Some tf.

Axiom function_ptr_translated:
  forall (b: Values.block) (tf: Two_level_repr.fundef),
  Genv.find_funct_ptr tge b = Some tf ->
  exists f,
  Genv.find_funct_ptr ge b = Some f /\ transf_fundef f = Some tf.
(*
Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = Some tf ->
  Mach.funsig f = Two_level_repr.funsig tf.
Proof.
  intros f tf. destruct f; simpl. 
  unfold transf_function.
  destruct (elaborate (fn_code f)).
  case_eq (if validCFG f
        (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
           (Mach.fn_framesize f)) && label_unicity (fn_code f) nil &&
      wf_cfg
        (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
           (Mach.fn_framesize f)) &&
      mem
        (cfg_head
           (fn_body
              (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                 (Mach.fn_framesize f))))
        (PTree.xkeys
           (cfg_code
              (fn_body
                 (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                    (Mach.fn_framesize f)))) 1) &&
      match head (fn_code f) with
      | Some (Mach.Mgetstack _ _ _) => false
      | Some (Mach.Msetstack _ _ _) => false
      | Some (Mach.Mgetparam _ _ _) => false
      | Some (Mach.Mop _ _ _) => false
      | Some (Mach.Mload _ _ _ _) => false
      | Some (Mach.Mstore _ _ _ _) => false
      | Some (Mach.Mcall _ _) => false
      | Some Mach.Malloc => false
      | Some (Mlabel lbl) =>
          if peq lbl
               (cfg_head
                  (fn_body
                     (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                        (Mach.fn_framesize f))))
          then true
          else false
      | Some (Mgoto _) => false
      | Some (Mach.Mcond _ _ _) => false
      | Some Mach.Mreturn => false
      | None => false
      end
   then
    Some
      (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
         (Mach.fn_framesize f))
   else None (A:=Two_level_repr.function)); intros.
   inversion H0. subst. 
  case_eq (if validCFG f
          (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
             (Mach.fn_framesize f)) && label_unicity (fn_code f) nil &&
        wf_cfg
          (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
             (Mach.fn_framesize f)) &&
        mem
          (cfg_head
             (fn_body
                (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                   (Mach.fn_framesize f))))
          (PTree.xkeys
             (cfg_code
                (fn_body
                   (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                      (Mach.fn_framesize f)))) 1) &&
        (match head (fn_code f) with
        | Some (Mach.Mgetstack _ _ _) => false
        | Some (Mach.Msetstack _ _ _) => false
        | Some (Mach.Mgetparam _ _ _) => false
        | Some (Mach.Mop _ _ _) => false
        | Some (Mach.Mload _ _ _ _) => false
        | Some (Mach.Mstore _ _ _ _) => false
        | Some (Mach.Mcall _ _) => false
        | Some Mach.Malloc => false
        | Some (Mlabel lbl) =>
            if peq lbl
                 (cfg_head
                    (fn_body
                       (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                          (Mach.fn_framesize f))))
            then true
            else false
        | Some (Mgoto _) => false
        | Some (Mach.Mcond _ _ _) => false
        | Some Mach.Mreturn => false
        | None => false
        end)); intros. 
  rewrite H1 in H2. inversion H2. subst. simpl. trivial. 
  rewrite H1 in H2. congruence. 
  congruence. congruence. 
  intros. inversion H. subst. simpl. trivial. 
Qed.
*)
Lemma functions_translated2:
  forall v f,
  Genv.find_funct (Genv.globalenv p) v = Some f ->
  Genv.find_funct (Genv.globalenv tp) v = transf_fundef f
  /\ transf_fundef f <> None.
Proof.
  intros.  
  generalize (@Genv.find_funct_transf_partial _ _ _ transf_fundef p tp tr_ok _ _ H); intro.
  trivial. 
Qed. 

Lemma function_ptr_translated2:
  forall v f,
  Genv.find_funct_ptr (Genv.globalenv p) v = Some f ->
  Genv.find_funct_ptr (Genv.globalenv tp) v = transf_fundef f 
  /\ transf_fundef f <> None.
Proof. 
  intros.  
  generalize (@Genv.find_funct_ptr_transf_partial _ _ _ transf_fundef p tp tr_ok _ _ H); intro.
  trivial. 
Qed. 

Lemma symbols_preserved2:
  forall id,
  (@Genv.find_symbol Two_level_repr.fundef)((@Genv.globalenv Two_level_repr.fundef _) tp) id = Genv.find_symbol (Genv.globalenv p) id.
Proof.
  intros. 
  generalize (Genv.find_symbol_transf_partial _ _ tr_ok id); intro.
  trivial. 
Qed. 
 
Lemma env_doesnt_matter1:
  forall sp op vl,
  eval_operation (Genv.globalenv p) sp op vl = 
  eval_operation (Genv.globalenv tp) sp op vl.
Proof. 
  intros. 
  unfold transf_program in tr_ok. 
  unfold eval_operation; destruct op; trivial. 
  unfold fundef. 
  unfold fundef in *|-. 
  generalize (Genv.find_symbol_transf_partial transf_fundef p tr_ok i); intro.
  unfold Two_level_repr.fundef in H. rewrite <- H. trivial.  
Qed.

Lemma env_doesnt_matter2:
  forall sp addr vl,
  eval_addressing (Genv.globalenv p) sp addr vl = 
  eval_addressing (Genv.globalenv tp) sp addr vl.
Proof. 
  intros. 
  unfold transf_program in tr_ok. 
  unfold eval_addressing; destruct addr; trivial. 
  generalize (Genv.find_symbol_transf_partial transf_fundef p tr_ok i); intro.
  unfold Two_level_repr.fundef in H. rewrite <- H. trivial.  
  generalize (Genv.find_symbol_transf_partial transf_fundef p tr_ok i); intro.
  unfold Two_level_repr.fundef in H. rewrite <- H. trivial.  
Qed.  

End TRIVIA. 

Lemma invert_transf:
  forall f tf,
  transf_function f = Some tf -> 
  exists t',
  (elaborate (fn_code f) = Some t' /\
  tf = (Two_level_repr.mkfunction (Mach.fn_sig f) t' (Mach.fn_stacksize f) (Mach.fn_framesize f)) /\
  validCFG f tf = true) /\ label_unicity (fn_code f) nil = true /\ 
  wf_cfg tf = true 
          /\ mem (cfg_head (fn_body tf)) (remove (PTree.xkeys (cfg_code (fn_body tf)) 1) (cfg_head (fn_body tf))) = false
          /\ (match (cfg_code (fn_body tf)) ! (cfg_head (fn_body tf)) with | Some i => true | None => false end) = true 
          /\ validLabel f tf (remove (PTree.xkeys (cfg_code (fn_body tf)) 1) (cfg_head (fn_body tf))) (cfg_head (fn_body tf)) = true
          /\ (match head (tail (fn_code f)) with | Some (Mach.Mreturn) => false | Some (Mach.Mcall _ _) => false | _ => true end) = true
          /\ match head (fn_code f) with | Some (Mlabel lbl) => if peq lbl (cfg_head (fn_body tf)) then true else false | _ => false end = true
          /\ (match (cfg_code (fn_body tf)) ! (cfg_head (fn_body tf)) with | Some Mreturn => false | _ => true end) = true 
          /\ check_target f = true.
Proof. 
  intros. 
  unfold transf_function in H. 
  case_eq (elaborate (fn_code f)); intros. 
  rewrite H0 in H. 
  case_eq (validCFG f
          (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
             (Mach.fn_framesize f)) && label_unicity (fn_code f) nil &&
        wf_cfg
          (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
             (Mach.fn_framesize f)) &&
        negb
          (mem
             (cfg_head
                (fn_body
                   (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                      (Mach.fn_framesize f))))
             (remove
                (PTree.xkeys
                   (cfg_code
                      (fn_body
                         (Two_level_repr.mkfunction (Mach.fn_sig f) c
                            (Mach.fn_stacksize f) (Mach.fn_framesize f)))) 1)
                (cfg_head
                   (fn_body
                      (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                         (Mach.fn_framesize f)))))) &&
        match
          (cfg_code
             (fn_body
                (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                   (Mach.fn_framesize f))))
          ! (cfg_head
               (fn_body
                  (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                     (Mach.fn_framesize f))))
        with
        | Some _ => true
        | None => false
        end &&
        validLabel f
          (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
             (Mach.fn_framesize f))
          (remove
             (PTree.xkeys
                (cfg_code
                   (fn_body
                      (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                         (Mach.fn_framesize f)))) 1)
             (cfg_head
                (fn_body
                   (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                      (Mach.fn_framesize f)))))
          (cfg_head
             (fn_body
                (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                   (Mach.fn_framesize f)))) &&
        match head (tail (fn_code f)) with
        | Some (Mach.Mgetstack _ _ _) => true
        | Some (Mach.Msetstack _ _ _) => true
        | Some (Mach.Mgetparam _ _ _) => true
        | Some (Mach.Mop _ _ _) => true
        | Some (Mach.Mload _ _ _ _) => true
        | Some (Mach.Mstore _ _ _ _) => true
        | Some (Mach.Mcall _ _) => false
        | Some Mach.Malloc => true
        | Some (Mlabel _) => true
        | Some (Mgoto _) => true
        | Some (Mach.Mcond _ _ _) => true
        | Some Mach.Mreturn => false
        | None => true
        end &&
        match head (fn_code f) with
        | Some (Mach.Mgetstack _ _ _) => false
        | Some (Mach.Msetstack _ _ _) => false
        | Some (Mach.Mgetparam _ _ _) => false
        | Some (Mach.Mop _ _ _) => false
        | Some (Mach.Mload _ _ _ _) => false
        | Some (Mach.Mstore _ _ _ _) => false
        | Some (Mach.Mcall _ _) => false
        | Some Mach.Malloc => false
        | Some (Mlabel lbl) =>
            if peq lbl
                 (cfg_head
                    (fn_body
                       (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                          (Mach.fn_framesize f))))
            then true
            else false
        | Some (Mgoto _) => false
        | Some (Mach.Mcond _ _ _) => false
        | Some Mach.Mreturn => false
        | None => false
        end &&
        match
          (cfg_code
             (fn_body
                (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                   (Mach.fn_framesize f))))
          ! (cfg_head
               (fn_body
                  (Two_level_repr.mkfunction (Mach.fn_sig f) c (Mach.fn_stacksize f)
                     (Mach.fn_framesize f))))
        with
        | Some (Mtree _) => true
        | Some (Mcall _ _ _) => true
        | Some Mreturn => false
        | None => true
        end && check_target f); intros. 
  rewrite H1 in H.  
  inversion H.
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  generalize (essai _ _ H1); clear H1; intro; destruct H1. 
  exists c; intuition trivial.
  simpl in H9. simpl. 
  destruct (mem (cfg_head c) (remove (PTree.xkeys (cfg_code c) 1) (cfg_head c))). 
  simpl in H9; inversion H9. trivial.
  rewrite H1 in H. congruence. 
  rewrite H0 in H. congruence.
Qed. 
