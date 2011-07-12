Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.
Require Import Machabstr.

Require Import Valcommon.
Require Import Repr.
Require Import BasicLib. 

Lemma bb_no_trace:
  forall ge f sp parent c rs fr m t c' rs' fr' m',
  exec_block_body ge f sp parent c rs fr m t c' rs' fr' m' ->
  t = E0.
Proof. 
  intros. 
  induction H. 
  trivial. 
  inversion H; subst; trivial. 
  subst. traceEq. 
Qed. 

Lemma nb_no_trace:
  forall FF ge sp parent c rs fr m t c' rs' fr' m',
  exec_nb_instrs FF ge sp parent c rs fr m t c' rs' fr' m' ->
  t = E0.
Proof. 
  intros. 
  induction H. 
  trivial. trivial. 
Qed. 

Lemma bb_nb_aux:
  forall ge f sp parent c rs fr m c' rs' fr' m',
  exec_instr ge f sp parent c rs fr m E0 c' rs' fr' m' ->
  exec_nb_instrs fundef ge sp parent c rs fr m E0 c' rs' fr' m'.
Proof. 
    intros. inversion H; subst; inversion H; subst; eapply Valcommon.exec_trans_bl; eauto. 
  
  generalize (Valcommon.exec_Mgetstack fundef ge sp parent _ _ dst c' rs fr' m' v H0).
  eauto. 
  rewrite H13. eapply Valcommon.exec_refl_bl; eauto. 

  generalize (Valcommon.exec_Msetstack fundef ge sp parent _ _ _ c' rs' fr m' fr' H0).
  eauto. 
  eapply Valcommon.exec_refl_bl; eauto. 

  generalize (Valcommon.exec_Mgetparam fundef ge sp parent _ _ dst c' rs fr' m' v H0).
  eauto. 
  rewrite H13. eapply Valcommon.exec_refl_bl; eauto. 

  generalize (Valcommon.exec_Mop fundef ge sp parent _ _ res c' rs fr' m' v H0).
  eauto. 
  rewrite H13. eapply Valcommon.exec_refl_bl; eauto. 

  generalize (Valcommon.exec_Mload fundef ge sp parent _ _ _ dst c' rs fr' m' _ _ H0 H1).
  eauto. 
  rewrite H15. eapply Valcommon.exec_refl_bl; eauto. 

  generalize (Valcommon.exec_Mstore fundef ge sp parent _ _ _ src c' rs' fr' m _ _ H0 H1).
  eauto. 
  eapply Valcommon.exec_refl_bl; eauto. 

  generalize (Valcommon.exec_Malloc fundef ge sp parent c' _ fr' _ _ _  _ H0 H1).
  eauto. 
  rewrite H3. eapply Valcommon.exec_refl_bl; eauto. 
Qed. 


Lemma bb_nb :
  forall ge f sp parent c rs fr m c' rs' fr' m',
  exec_block_body ge f sp parent c rs fr m E0 c' rs' fr' m' ->
  exec_nb_instrs fundef ge sp parent c rs fr m E0 c' rs' fr' m'.
Proof. 
  intros until 1. 
  induction H. 
  eapply Valcommon.exec_refl_bl; eauto. 
  assert (t = E0). inversion H; subst; trivial. 
  subst. eapply bb_nb_aux; eauto. 

  clear H. clear H0.   
  induction IHexec_block_body1. 
  generalize (nb_no_trace fundef _ _ _ _ _ _ _ _ _ _ _ _ IHexec_block_body2). 
  intro; subst. assert (E0 ** E0 = E0). traceEq. 
  rewrite H. auto. 

  generalize (nb_no_trace fundef _ _ _ _ _ _ _ _ _ _ _ _ IHexec_block_body2). 
  intro; subst. assert (E0 ** E0 = E0). traceEq. rewrite H0. 
  assert (E0 ** E0 = E0 ** E0). traceEq. 
  generalize (IHIHexec_block_body1 IHexec_block_body2 H1). 
  intro. rewrite H0 in H2. eapply Valcommon.exec_trans_bl; eauto. 
Qed.   


Lemma nb_bb :
  forall ge f sp parent c rs fr m c' rs' fr' m',
  exec_nb_instrs fundef ge sp parent c rs fr m E0 c' rs' fr' m' ->
  exec_block_body ge f sp parent c rs fr m E0 c' rs' fr' m'.
Proof. 
  intros. induction H. 
  eapply exec_refl_bl. 
  eapply exec_trans_bl; eauto. 
  inversion H; eapply exec_one_bl. 
  eapply exec_Mgetstack; eauto. 
  eapply exec_Msetstack; eauto. 
  eapply exec_Mgetparam; eauto. 
  eapply exec_Mop; eauto. 
  eapply exec_Mload; eauto. 
  eapply exec_Mstore; eauto. 
  eapply exec_Malloc; eauto. 
  traceEq. 
Qed.    
  


Definition check_glue h1 h2 :=
match h1 with
|error => match h2 with 
                |error => true
                |value x2 => false
                end
|value x1 => match h2 with
                    |error => false
                    |value x2 => if instruction_eq x1 x2 then true else false
                    end
end.

(** The validation function for the whole code *)

Lemma glue_correct:
forall x y,
check_glue x y = true -> x = y.
Proof. 
  intros. unfold check_glue in H. 
  caseEq x; caseEq y; intros; rewrite H0 in H; rewrite H1 in H; try (discriminate); trivial. 
  caseEq (instruction_eq i0 i); intros. congruence. 
  rewrite H2 in H. discriminate. 
Qed.  

Fixpoint validate (c tc : code) (c1 c2 : code) {struct c} : bool :=
  match c with 
  | nil => match tc with 
               | nil => true 
               | _ => false
               end
  | i :: l => 
               match tc with
               | nil => false
               | i' :: l' =>
                   if nbranchset i && nbranchset i' then validate l l' (c1 ++ i :: nil) (c2 ++ i' :: nil) 
                   else
                   check_glue (value i) (value i') && nbic c1 c2 && validate l l' nil nil 
               end
  end.

(** Form static to dynamic*)

Fixpoint to_next_block (c : code) {struct c} : code :=
  match c with
  | nil => nil
  | (Mgoto lbl) :: l => l
  | (Mcall sig n) :: l => l
  | (Mlabel lbl) :: l => l
  | (Mcond cmp rl lbl) :: l => l
  | (Mreturn) :: l => l
  | i :: l => to_next_block l
  end.
       
Lemma to_next_block_prop:
  forall a c,
  nbranchset a = true -> to_next_block (a :: c) = to_next_block c.
Proof. 
  intros. destruct a; inversion H; simpl; trivial. 
Qed.

Lemma lnbranchset_prop_coin:
  forall x a,
  lnbranchset (a :: x) = true -> nbranchset a = true /\ lnbranchset x = true.
Proof. 
  intros. split. 
  destruct a; inversion H; simpl; congruence. 
  destruct a; inversion H; simpl; trivial. 
Qed.

Lemma to_next_block_prop1:
  forall x0 c x1,
  c = x0 ++ Mreturn :: x1 ->
  lnbranchset x0 = true ->
  to_next_block c = x1.
Proof. 
  induction x0. 
  intros. rewrite H. simpl. trivial. 
  intros. generalize (lnbranchset_prop_coin _ _ H0). intuition.  
  destruct a; inversion H2;rewrite H;simpl;  
  generalize (IHx0 _ _ (refl_equal (x0 ++ Mreturn :: x1)) H3); intro; 
  trivial. 
Qed.

Lemma to_next_block_prop2:
  forall x k,
  lnbranchset x = true -> to_next_block (x ++ k) = to_next_block k.
Proof. 
  intros. induction x. simpl. trivial. 
  rewrite <- app_comm_cons. 
  generalize (lnbranchset_prop_coin _ _ H). intro. 
  destruct H0. generalize (IHx H1). intro. 
  destruct a; inversion H0; simpl; auto. 
Qed.
            
Lemma validate_propagation1_aux:
forall c tc f tf,
validate c tc f tf = true ->
validate (to_next_block c) (to_next_block tc) nil nil = true. 
Proof. 
  induction c.
  
  intros. inversion H. caseEq (tc). intro; subst. 
  simpl. trivial. intros. rewrite H0 in H. simpl in H. inversion H. 

  intros. simpl in H. caseEq tc. intro. rewrite H0 in H. inversion H. 
  intros. rewrite H0 in H. 
  
  caseEq (nbranchset a); caseEq (nbranchset i); intros.  
  
  (* cas instruciton en sequence *)

  rewrite H1 in H; rewrite H2 in H; simpl in H; 
  generalize (IHc l (f ++ a :: nil) (tf ++ i :: nil) H); intro; 
  rewrite to_next_block_prop; auto. rewrite to_next_block_prop; auto. 
  
  (* cas branchement *)

  rewrite H1 in H. rewrite H2 in H. simpl in H.  
  caseEq (instruction_eq a i); intros. 
  rewrite e in H2. rewrite H2 in H1. congruence.
  generalize (essai _ _ H). intros. destruct H4. 
  generalize (essai _ _ H4). intros. destruct H6. 
  rewrite H3 in H6. discriminate. 

  rewrite H1 in H. rewrite H2 in H. simpl in H. 
  caseEq (instruction_eq a i); intros. 
  rewrite e in H2. rewrite H2 in H1. congruence. 
  generalize (essai _ _ H). intros. destruct H4. 
  generalize (essai _ _ H4). intros. destruct H6. 
  rewrite H3 in H6. discriminate.   

   rewrite H1 in H. rewrite H2 in H. simpl in H. 
   caseEq (instruction_eq a i). intros. rewrite H3 in H. 
  generalize (essai _ _ H). intros. destruct H4. 
  generalize (essai _ _ H4). intros. destruct H6.    
  rewrite e. destruct i; inversion H1; simpl; trivial. 
  intros. rewrite H3 in H. 
  generalize (essai _ _ H). intros. destruct H4. 
  generalize (essai _ _ H4). intros. destruct H6. congruence. 
Qed.

Lemma validate_propagation1:
forall c tc,
validate c tc nil nil = true ->
validate (to_next_block c) (to_next_block tc) nil nil = true. 
Proof. 
  intros. eapply validate_propagation1_aux; eauto. 
Qed. 

Lemma find_label_prop:
  forall i c lbl,
  nbranchset i = true -> find_label lbl (i :: c) = find_label lbl c. 
Proof. 
  intros. 
  destruct i; inversion H; simpl; trivial. 
Qed.

Lemma validate_propagation2_aux:
forall c tc c' tc' f tf lbl,
validate c tc f tf = true ->
find_label lbl c = Some c' ->
find_label lbl tc = Some tc' ->
validate c' tc' nil nil = true.
Proof. 
  induction c. 

  intros. simpl in H0. congruence. 

  intros. simpl in H. 
  caseEq tc. intro. rewrite H2 in H. congruence. 
  intros. rewrite H2 in H. 

  caseEq (nbranchset a); caseEq (nbranchset i);intros; 
  rewrite H3 in H; rewrite H4 in H; simpl in H.

  rewrite H2 in H1. rewrite find_label_prop in H0; auto. 
  rewrite find_label_prop in H1; auto. 
  generalize (IHc l c' tc' (f ++ a :: nil) (tf ++ i :: nil) lbl H H0 H1). 
  intros. trivial.
  
  caseEq (instruction_eq a i). 
  intro. rewrite e in H4. rewrite H4 in H3. congruence.
  intros. rewrite H5 in H. simpl in H. congruence.

  caseEq (instruction_eq a i). 
  intro. rewrite e in H4. rewrite H4 in H3. congruence.
  intros. rewrite H5 in H. simpl in H. congruence.  

  caseEq (instruction_eq a i). 
  2:intros; rewrite H5 in H; simpl in H; congruence. 
  intros. 
  rewrite H5 in H. rewrite H2 in H1. rewrite e in H0. 
  rewrite e in H4. 
  generalize (essai _ _ H). intro. destruct H6. 
  generalize (essai _ _ H6). intro. destruct H8. 
  destruct i; inversion H3. 
  simpl in H1; simpl in H0; generalize (IHc l c' tc' nil nil lbl H7 H0 H1); intro; trivial.  
 2: simpl in H1; simpl in H0; generalize (IHc l c' tc' nil nil lbl H7 H0 H1); intro; trivial. 
 2: simpl in H1; simpl in H0; generalize (IHc l c' tc' nil nil lbl H7 H0 H1); intro; trivial.  
 2: simpl in H1; simpl in H0; generalize (IHc l c' tc' nil nil lbl H7 H0 H1); intro; trivial.  

  generalize H0. generalize H1. intros B1 B2. 
  simpl in H1. simpl in H0. caseEq (peq lbl l0). 
  intros. rewrite H10 in H0. rewrite H10 in H1. 
  injection H1. injection H0. intros. rewrite <- H11. rewrite <- H12. 
  trivial. 
  
  intros. rewrite H10 in H0. rewrite H10 in H1. 
  generalize (IHc l c' tc' nil nil lbl H7 H0 H1). intro. trivial. 
Qed.

Lemma validate_propagation2:
forall c tc c' tc' lbl,
validate c tc nil nil = true ->
find_label lbl c = Some c' ->
find_label lbl tc = Some tc' ->
validate c' tc' nil nil = true.
Proof. 
  intros. eapply validate_propagation2_aux; eauto. 
Qed.
 
Lemma find_label_validated_aux:
  forall c tc k1 lbl f tf,
  validate c tc f tf = true ->
  find_label lbl c = Some k1 ->
  exists k2,
  find_label lbl tc = Some k2.
Proof. 
  induction c. 
  intros. simpl in H0. congruence. 
  intros. 
  caseEq tc. 
  intro. rewrite H1 in H. inversion H.  
  intros. subst. 
  simpl in H. simpl in H0. 
  caseEq (is_label lbl a). 
  intros. rewrite H1 in H0. 
  caseEq (nbranchset a). intro. rewrite H2 in H. 
  caseEq (nbranchset i). intro. rewrite H3 in H. 
  destruct a; inversion H1; inversion H2. 
  intros. rewrite H3 in H. simpl in H. 
  caseEq (instruction_eq a i). 
  intros. rewrite <- e in H3. rewrite H3 in H2. congruence. 
  intros. rewrite H4 in H. simpl in H. congruence. 
  
  intros. rewrite H2 in H. simpl in H. 
  caseEq (instruction_eq a i). intros. 
  rewrite e in H1. simpl. rewrite H1. exists l. trivial. 
  intros. rewrite H3 in H. simpl in H. congruence. 

  intros. rewrite H1 in H0. 
  caseEq (nbranchset a). 
  intro. rewrite H2 in H. 
  caseEq (nbranchset i). intro. rewrite H3 in H. 
  simpl in H. generalize (IHc _ _ _ _ _ H H0). intros. 
  destruct H4. assert (find_label lbl (i :: l) = find_label lbl l). 
  destruct i; inversion H3; simpl; trivial. 
  rewrite H5. exists x. trivial. 
  
  intro. rewrite H3 in H. simpl in H. caseEq (instruction_eq a i). 
  intros. rewrite <- e in H3. rewrite H3 in H2. congruence. 
  intros. rewrite H4 in H. simpl in H. congruence. 
 intros. rewrite H2 in H. simpl in H. 
  caseEq (instruction_eq a i). intros. rewrite <- e. 
  simpl. rewrite H1. generalize (essai _ _ H). 
  intros. destruct H4. generalize (IHc _ _ _ _ _ H5 H0). 
  intro. destruct H6. exists x. trivial. 
  
  intros. rewrite H3 in H. simpl in H. congruence. 
Qed.
 
Lemma find_label_validated:
  forall f tf,
  validate (fn_code f) (fn_code tf) nil nil = true ->
  forall lbl k1, find_label lbl (fn_code f) = Some k1 ->
  exists k2,
  find_label lbl (fn_code tf) = Some k2.
Proof. 
  intros. eapply find_label_validated_aux; eauto. 
Qed. 

(** Some rewriting lemmas *)

Lemma decomposition2_aux:
  forall FF ge sp parent c rs fr m c' rs' fr' m' i l,
  exec_nb_instrs FF ge sp parent c rs fr m E0 c' rs' fr' m' ->
  c' = i :: l -> 
  nbranchset i = false -> 
  exists c1,
  c = c1 ++ c' /\ lnbranchset c1 = true.
Proof. 
  intros until 1. 
  induction H. 
  intros. exists (@nil instruction). simpl. intuition trivial. 

  intros. 
  generalize (IHexec_nb_instrs H1 H2). intro. 
  clear IHexec_nb_instrs. destruct H3. destruct H3.  
  inversion H.   
  
    exists ((Mgetstack ofs ty dst) :: x). split.
    rewrite <- app_comm_cons. congruence. 
    simpl. trivial. 
    exists ((Msetstack src ofs ty) :: x). split.
    rewrite <- app_comm_cons. congruence.
    simpl. auto.
    exists ((Mgetparam ofs ty dst) :: x). split.
    rewrite <- app_comm_cons. congruence.
    simpl. auto.
    exists ((Mop op args res) :: x). split.
    rewrite <- app_comm_cons. congruence.
    simpl. auto.
    exists ((Mload chunk addr args dst) :: x). split.
    rewrite <- app_comm_cons. congruence.
    simpl. auto.
    exists ((Mstore chunk addr args src) :: x). split. 
    rewrite <- app_comm_cons. congruence.
    simpl. auto. 
    exists (Malloc :: x). split. 
    rewrite <- app_comm_cons. congruence.
    simpl. auto. 

Qed. 

Lemma decomposition2:
  forall ge f sp parent c rs fr m t c' rs' fr' m' i l,
  exec_block_body ge f sp parent c rs fr m t c' rs' fr' m' ->
  c' = i :: l -> 
  nbranchset i = false -> 
  exists c1,
  c = c1 ++ c' /\ lnbranchset c1 = true.
Proof. 
  intros. 
  
  generalize (bb_no_trace _ _ _ _ _  _ _ _ _ _ _ _ _ H). intro; subst. 
  generalize (bb_nb _ _ _ _ _ _ _ _ _ _ _ _ H). intro. 
  eapply decomposition2_aux; eauto. 
  Qed. 

Lemma app_nil: forall (l : list instruction), l ++ nil = l. 
induction l; simpl ; auto. rewrite IHl. trivial. Qed.   

Lemma get_infos_aux_gen3:
  forall tc x c i l f tf,
  validate c tc f tf = true ->
  c = x ++ (i :: l) -> lnbranchset x = true -> nbranchset i = false ->
  exists tc1,
  nbic (f ++ x) (tf ++ tc1) = true /\ 
  lnbranchset tc1 = true /\ exists tc', tc = tc1 ++ ( i :: tc').
Proof. 
    induction tc. 
     

  intros. caseEq x. intro. rewrite H3 in H0. rewrite H0 in H. inversion H. 
  intros. rewrite H3 in H0. rewrite H0 in H. inversion H. 
 
  intros. caseEq x. intro. 
  exists (@nil instruction). split. simpl. 
  rewrite H3 in H0. simpl in H0. rewrite H0 in H. 
  simpl in H. rewrite H2 in H. simpl in H. 
  generalize (essai _ _ H). intro. destruct H4. 
  generalize (essai _ _ H4). intro. destruct H6. simpl. trivial.
  rewrite app_nil. rewrite app_nil. trivial .
  split. simpl; trivial. exists tc. simpl. 
  rewrite H0 in H. rewrite H3 in H. simpl in H. 
  rewrite H2 in H. simpl in H. 
  generalize (essai _ _ H). intros. destruct H4. 
  generalize (essai _ _ H4). intro. destruct H6. 
  caseEq (instruction_eq i a). intros. rewrite e. trivial. 
  intros. rewrite H8 in H6. congruence. 
 
  intros. rewrite H3 in H0. rewrite H0 in H.  
  rewrite H3 in H1. generalize (lnbranchset_prop_coin _ _ H1). intro. 
  assert (l0 ++ i :: l = l0 ++ i ::l). congruence.
  destruct H4. simpl in H. 
  rewrite H4 in H. 
  caseEq (nbranchset a). intros. rewrite H7 in H. 
  simpl in H. 
  generalize (IHtc l0 (l0 ++ i :: l) i l (f ++ i0 :: nil) (tf ++ a :: nil) H H5 H6 H2). 
  intro. 
  destruct H8. destruct H8. destruct H9. exists (a :: x0). split. 
  rewrite app_ass in H8. rewrite app_ass in H8. 
  rewrite <- app_comm_cons in H8.  rewrite <- app_comm_cons in H8.  
  simpl in H8. trivial. 
  (* destruct i0; destruct a; inversion H4; inversion H7; simpl;auto.  *)
  split. destruct a; inversion H7; simpl; trivial. destruct H10. 
  exists x1. rewrite <- app_comm_cons. congruence. 

  intro. rewrite H7 in H. simpl in H. 
  generalize (essai _ _ H). intro. destruct H8. 
  generalize (essai _ _ H8). intro. destruct H10. 
  caseEq (instruction_eq i0 a). intro. rewrite e in H4. rewrite H4 in H7. 
  congruence. intros. rewrite H12 in H10. congruence. 
Qed.

Lemma get_infos_gen3:
  forall tc x c i l,
  validate c tc nil nil = true ->
  c = x ++ (i :: l) -> lnbranchset x = true -> nbranchset i = false ->
  exists tc1,
  nbic x tc1 = true /\ 
  lnbranchset tc1 = true /\ exists tc', tc = tc1 ++ ( i :: tc').
Proof.
  intros. 
  
  generalize (get_infos_aux_gen3 _ _ _ _ _ _ _ H H0 H1 H2). intro. 
  simpl in H3. trivial. 
  
Qed.



Lemma end_of_line:
  forall x1,
  validate (Mreturn :: nil) x1 nil nil = true ->
  x1 = Mreturn :: nil.
Proof. 
  intros. caseEq x1. 
  intro. rewrite H0 in H. simpl in H. congruence.
  intros. caseEq l. intro. subst. 
  destruct i; inversion H. trivial.  
  intros. rewrite H1 in H0. rewrite H0 in H. 
  inversion H. 
  generalize (essai _ _ H3). intro. destruct H2. 
  congruence. 
Qed.
  

Scheme exec_spec_instrs_ind := Minimality for exec_instrs Sort Prop
   with exec_spec_ind_function_ind := Minimality for exec_function Sort Prop.

Require Import Repr. 

Lemma dec1:
  forall ge f sp parent c c' rs fr m rs' fr' m' t,
  exec_block_end ge f sp parent c rs fr m t c' rs' fr' m' ->
  exists i, exists l, c = i :: l /\ nbranchset i = false.
Proof. 
  intros. inversion H. 
  exists (Mlabel lbl). exists c'. intuition trivial. 
  exists (Mgoto lbl). exists c0. intuition trivial. 
  exists (Mcond cond args lbl). exists c0. intuition trivial. 
  exists (Mcond cond args lbl). exists c'. intuition trivial. 

  exists (Mcall sig ros). exists c'. intuition trivial. 


Qed.

Scheme glue_block_end_ind := Minimality for exec_block_end Sort Prop
  with glue_function_ind := Minimality for exec_function Sort Prop.





Scheme exec_instrs_ind2 := Minimality for exec_instrs Sort Prop
   with exec_function_ind2 := Minimality for exec_function Sort Prop.

Parameter schedule_code : code -> option code. 

Definition transf_code (c: code) : option code :=
  match schedule_code c with
  | None => None
  | Some tc => if validate c tc nil nil then Some tc else None
  end.

Definition transf_function (f : function) : option function :=
match transf_code f.(fn_code) with
     | None => None
     | Some tc =>
       Some (mkfunction f.(fn_sig) tc f.(fn_stacksize) f.(fn_framesize))
  end. 

Definition transf_fundef (f: fundef) : option fundef :=
match f with
  | Internal f => match transf_function f with
       | None => None
       | Some f => Some (Internal f)
   
  end
  | External f => Some (External f)
  end.

Require Import Machtyper. 
(*
Definition transf_fundef (f : fundef) : option fundef :=
match transf_fundef_aux f with
  | Some f => if Machtyper.wt_fundef_set f then Some f else None
  | None => None
  end.
*)
Definition transf_program (p: program) : option program :=
  match transform_partial_program transf_fundef p with
  | Some p => if typer p then Some p else None
  | None => None
  end. 

Lemma talk:
  forall f tf,
  transf_function f = Some tf -> 
  validate (fn_code f) (fn_code tf) nil nil = true.
Proof. 
  intros. 
  unfold transf_function in H. 
  caseEq (transf_code (fn_code f));intros;rewrite H0 in H; try congruence.  
  unfold transf_code in H0. 
  caseEq (schedule_code (fn_code f));intros;rewrite H1 in H0; try congruence. 
  caseEq (validate (fn_code f) c0 nil nil); intros; rewrite H2 in H0; try congruence. 
  injection H. intro. assert (fn_code tf = c). subst. trivial. 
  injection H0. intro. rewrite <- H5 in H4. rewrite <- H4 in H2. trivial.  
Qed.
(*
Lemma rewrite_transf_fundef:
  forall p tp,
  transf_fundef p = Some tp -> 
  transf_fundef_aux p = Some tp.
Proof. 
  intros. unfold transf_fundef in H. 
  case_eq (transf_fundef_aux p); intros. 
  rewrite H0 in H. 
  case_eq (wt_fundef_set f); intros. 
  rewrite H1 in H. trivial. 
  rewrite H1 in H. inversion H. 
  rewrite H0 in H. inversion H. 
Qed.   
  *)
Lemma env_doesnt_matter1:
  forall p tp,
  transf_program p = Some tp ->
  forall sp op vl,
  eval_operation (Genv.globalenv p) sp op vl = 
  eval_operation (Genv.globalenv tp) sp op vl.
Proof. 
  intros. 
  unfold transf_program in H.
  case_eq (transform_partial_program transf_fundef p); intros.
  rewrite H0 in H.
  case_eq (typer p0); intros. 
  rewrite H1 in H. inversion H; subst.    
  unfold eval_operation; destruct op; trivial. 
  rewrite (Genv.find_symbol_transf_partial transf_fundef p H0 i); eauto.
  rewrite H1 in H. inversion H.
  rewrite H0 in H. inversion H.    
Qed.

Lemma env_doesnt_matter2:
  forall p tp,
  transf_program p = Some tp ->
  forall sp addr vl,
  eval_addressing (Genv.globalenv p) sp addr vl = 
  eval_addressing (Genv.globalenv tp) sp addr vl.
Proof. 
  intros. 
  unfold transf_program in H.
  case_eq (transform_partial_program transf_fundef p); intros.
  rewrite H0 in H.
  case_eq (typer p0); intros. 
  rewrite H1 in H. inversion H; subst.     
  unfold eval_addressing; destruct addr; trivial. 
  rewrite (Genv.find_symbol_transf_partial transf_fundef p H0 i); eauto. 
  rewrite (Genv.find_symbol_transf_partial transf_fundef p H0 i); eauto.   
  rewrite H1 in H. inversion H.
  rewrite H0 in H. inversion H.   
Qed.  

Lemma trans_program_inv:
  forall p tp,
  transf_program p = Some tp ->
  transform_partial_program transf_fundef p = Some tp. 
Proof. 
  intros. 
  unfold transf_program in H. 
  case_eq (transform_partial_program transf_fundef p); intros.
  rewrite H0 in H.
  case_eq (typer p0); intros. 
  rewrite H1 in H. trivial. 
  rewrite H1 in H. inversion H.
  rewrite H0 in H. inversion H.   
Qed.       

Lemma find_function_prop:
  forall p tp,
  transf_program p = Some tp ->
  forall l rs f,
  find_function (Genv.globalenv p) l rs = Some (Internal f) ->
  exists tf,
  find_function (Genv.globalenv tp) l rs = Some (Internal tf) /\ 
  validate (fn_code f) (fn_code tf) nil nil = true.
Proof. 
  intros. 
  generalize (trans_program_inv _ _ H); clear H; intro H.  
  unfold find_function in H0. caseEq l; intros; rewrite H1 in H0.  
  generalize (Genv.find_funct_transf_partial transf_fundef H H0). 
  intros. destruct H2. caseEq (transf_fundef (Internal f)). intros. 
  case_eq (f0). intros.  
  exists f1. split. simpl. subst. rewrite H4 in H2. trivial. 
  eapply talk; eauto. unfold transf_fundef in H4. 
  case_eq (transf_function f); intros. subst. 
  (*generalize (rewrite_transf_fundef _ _ H4); clear H4 ; intro H4. *)
  rewrite H6 in H4. 
    injection H4; intros. (*rewrite H6 in H1.*) congruence. 
  rewrite H6 in H4. intros. congruence. 
  intros. rewrite H5 in H4. 
    unfold transf_fundef in H4. 
    case_eq (transf_function f); intros. 
    rewrite H6 in H4. congruence. 
    rewrite H6 in H4. congruence. 
  intro. congruence.   (* A REFAIRE CA MARCHE MAIS YA DES VIEUX BOUTS *)
  
  generalize (Genv.find_symbol_transf_partial transf_fundef p H i). 
  intro. 
  caseEq (Genv.find_symbol (Genv.globalenv p) i). 
  intros. rewrite H3 in H0. 
  generalize (Genv.find_funct_ptr_transf_partial transf_fundef H H0).
  intro. destruct H4. caseEq (transf_fundef (Internal f)). 
  intros. case_eq f0. intros. subst.  
  exists f1. simpl. rewrite H2. rewrite H3. split. rewrite H6 in H4. trivial.    
  eapply talk; eauto. 
  unfold transf_fundef in H6. case_eq (transf_function f); intros.
  rewrite H1 in H6. congruence.  
  rewrite H1 in H6. congruence. intros; subst. 
  unfold transf_fundef in H6. 
    case_eq (transf_function f); intros. rewrite H1 in H6. congruence. 
    rewrite H1 in H6. congruence. intros. congruence. 

  intro. rewrite H3 in H0. congruence. 
Qed. 


Lemma find_function_prop_aux:
  forall p tp,
  transf_program p = Some tp ->
  forall l rs f  ge tge parent m t rs'  ,
  find_function (Genv.globalenv p) l rs = Some (External f) ->
  exec_function ge (External f) parent rs m t rs' m -> 
  exists tf,
  find_function (Genv.globalenv tp) l rs = Some (External tf) /\ 
  exec_function tge (External tf) parent rs m t rs' m.
Proof. 
  intros. 
  generalize (trans_program_inv _ _ H); clear H; intro H.  
  exists f. split. 
  
  unfold find_function. unfold find_function in H0. 
  case_eq l; intros. 
  rewrite H2 in H0.  
  
  generalize (Genv.find_funct_transf_partial transf_fundef H H0). 
  intro. destruct H3. simpl in H3. trivial. 
  
  rewrite H2 in H0. 
  
  generalize (Genv.find_symbol_transf_partial transf_fundef p H i).
  intros. rewrite <- H3 in H0. 
  case_eq (Genv.find_symbol (Genv.globalenv tp) i); intros. 
  rewrite H4 in H0. 
  generalize (Genv.find_funct_ptr_transf_partial transf_fundef H H0).
  intro. simpl in H5. destruct H5. trivial. 
  rewrite H4 in H0. inversion H0. 

  inversion H1; subst. 
  eapply exec_funct_external; eauto.  

Qed.   

Scheme exec_block_end_ind4 := Minimality for exec_block_end Sort Prop
  with exec_instrs_ind4 := Minimality for exec_instrs Sort Prop 
 with exec_function_body_ind4 := Minimality for exec_function_body Sort Prop
  with exec_function_ind4 := Minimality for exec_function Sort Prop.



Lemma abstraction_check:
  forall ge tge f tf sp parent c1 c2 tc1 tc2 rs fr m rs' fr' m' t,
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->  
  nbic c1 tc1 = true ->
  exec_block_body ge f sp parent (c1 ++ c2) rs fr m t c2 rs' fr' m'->
  exec_block_body tge tf sp parent (tc1 ++ tc2) rs fr m t tc2 rs' fr' m'.
Proof. 
  intros. 
  generalize (bb_no_trace _ _ _ _ _ _ _ _ _ _ _ _ _ H2). intro; subst. 
  eapply nb_bb; eauto. 
  eapply nbic_imply_equivalence; eauto. 
  eapply bb_nb; eauto. 
Qed. 

Lemma transf_function_correct : 
  forall p tp f rs m t,
  transf_program p = Some tp ->
  exec_function (Genv.globalenv p) f empty_frame (Regmap.init Vundef) (Genv.init_mem p) t rs m ->
  forall tf,
  transf_fundef f = Some tf ->
  exec_function (Genv.globalenv tp) tf empty_frame (Regmap.init Vundef) (Genv.init_mem p) t rs m.
Proof.
  intros until 1. intro. 
  eapply (exec_function_ind4 (Genv.globalenv p)) with
   (P := fun  (f: function) sp parent (c: code) rs fr m t (c':code) rs' fr' m' =>
            forall i tf tc k,
            transf_function f = Some tf ->  
            nbranchset i = false -> 
            validate k tc nil nil = true ->
            c = i :: k -> 
            exists tc', exec_block_end (Genv.globalenv tp) tf sp parent (i :: tc) rs fr m t tc' rs' fr' m' 
            /\ validate c' tc' nil nil = true) 
  
   (P0 := fun (f:function) sp parent (c:code) rs fr m t (cx:code) rs' fr' m' =>
            forall tf tc k, transf_function f = Some tf -> 
            cx = Mreturn :: k -> 
            validate c tc nil nil = true ->
            exists k', exec_instrs (Genv.globalenv tp) tf sp parent tc rs fr m t (Mreturn :: k') rs' fr' m')

   (P1 := fun  (f:function) parent v1 v2 rs m t rs' m' =>
              forall tf, transf_function f = Some tf -> exec_function_body (Genv.globalenv tp) tf parent v1 v2 rs m t rs' m')

   (P2 := fun  (f:fundef) parent rs m t rs' m' =>
              forall tf, transf_fundef f = Some tf -> exec_function (Genv.globalenv tp) tf parent rs m t rs' m')
              
  ; eauto; intros.

  exists tc. injection H4; intros; subst. split; auto. 
  eapply exec_Mlabel; eauto. 
  
  generalize (talk _ _ H2). intro. 
  generalize (find_label_validated _ _ H6 _ _ H1). intro. 
  destruct H7. exists x. 
  generalize (validate_propagation2 _ _ _ _ _ H6 H1 H7). intro. 
  split; auto. injection H5; intros; subst. 
  eapply exec_Mgoto; eauto. 

  generalize (talk _ _ H3). intro. 
  generalize (find_label_validated _ _ H7 _ _ H2). intro. 
  destruct H8. exists x. 
  generalize (validate_propagation2 _ _ _ _ _ H7 H2 H8). intro. 
  split; auto. injection H6; intros; subst. 
  eapply exec_Mcond_true; eauto. 

  exists tc. injection H5;intros;subst. split; auto. 
  eapply exec_Mcond_false; eauto. 

  (* call *)
  
  exists tc. injection H7; intros; subst. split; auto. 
  destruct f'. 
  generalize (find_function_prop _ _ H ros rs0 f1 H1). intros. 
  destruct H8. destruct H8.   
  generalize (H3 (Internal x)). intro.
  
  assert (transf_fundef (Internal f1) = Some (Internal x)). 
    unfold find_function in H1. unfold find_function in H8. 
    caseEq ros; intros. rewrite H11 in H8. rewrite H11 in H1. 
      generalize (trans_program_inv _ _ H); clear H; intro H.  
    
    generalize (Genv.find_funct_transf_partial transf_fundef H). 
    intros. generalize (H12 (rs0 m1) (Internal f1) H1). intro.
    destruct H13.  rewrite H13 in H8. auto.

    rewrite H11 in H8. rewrite H11 in H1. 
      generalize (trans_program_inv _ _ H); clear H; intro H.  
    generalize (Genv.find_symbol_transf_partial transf_fundef _ H i).
    intro. rewrite H12 in H8. 
    caseEq (Genv.find_symbol (Genv.globalenv p) i); intros. 
    rewrite H13 in H8. rewrite H13 in H1. 
    generalize (Genv.find_funct_ptr_transf_partial transf_fundef H). 
    intro. generalize (H14 b (Internal f1) H1). intro. destruct H15. 
    rewrite H15 in H8. auto. 
    rewrite H13 in H8. congruence. 

  generalize (H10 H11). intro. 

  eapply exec_Mcall; eauto. 
  
  (* call externe *)
  inversion H2; subst. 
  generalize (find_function_prop_aux _ _ H ros rs0 e (Genv.globalenv p) (Genv.globalenv tp) fr m' t0 (Regmap.set  (Conventions.loc_result (ef_sig e)) res rs0) H1 H2). intros. 
  destruct H8. destruct H8.   
  eapply exec_Mcall; eauto. 

  
  (* cas one_block *)
  intros. assert (nbranchset Mreturn = false). simpl. trivial. 
  generalize (decomposition2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H3 H5). 
  intro. destruct H6. destruct H6. rewrite H3 in H6. 
  generalize (get_infos_gen3 _ _ _ _ _ H4 H6 H7 H5). intro. 
  exists (to_next_block tc). 
  destruct H8. destruct H8. destruct H9. destruct H10. rewrite H6 in H1. rewrite <- H3 in H1. 

  generalize (env_doesnt_matter1 _ _ H). intro ENV1. 
  generalize (env_doesnt_matter2 _ _ H). intro ENV2. 
  
  generalize (abstraction_check _ (Genv.globalenv tp) _ tf _ _ _ _ _ (Mreturn :: x1) _ _ _ _ _ _ _ ENV1 ENV2 H8 H1). intro. 
  rewrite <- H10 in H11. 
  generalize (to_next_block_prop1 _ _ _ H10 H9). 
  intro. rewrite H12. eapply exec_one_block; eauto.  

  (* cas add_block *)

   intros. 

  (* on commence par reecrire nos hypothese *)
  generalize (dec1 _ _ _ _ _ _ _ _  _ _ _ _ _ H2).
  intros. destruct H10 as [i [l [A B]]].  
  generalize (decomposition2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 A B). intro. 
  destruct H10 as [c [C D]]. 
  rewrite C in H1. rewrite A in C. 
  subst. 

  (* on va chercher le check et on reecrit tc *) (* was : c ++ i :: l *)
  generalize (get_infos_gen3 _ _ _ _ _ H9 (refl_equal (c ++ i :: l)) D B). intro. 
  destruct H6 as [tc1 [E [F G]]]. 
  destruct G. subst. 
  
  generalize (env_doesnt_matter1 _ _ H). intro ENV1. 
  generalize (env_doesnt_matter2 _ _ H). intro ENV2.   

  generalize (abstraction_check _ (Genv.globalenv tp) _ tf _ _ _ _ _ (i :: x) _ _ _ _ _ _ _ ENV1 ENV2 E H1). 
  intro.  
  generalize (validate_propagation1 _ _ H9). intro. 
  rewrite to_next_block_prop2 in H8; auto. 
  rewrite to_next_block_prop2 in H8; auto. 
  assert (i :: l = i :: to_next_block (i :: l)). 
  destruct i; inversion B; simpl; trivial. 
  generalize (H3 _ _ _ _ H7 B H8 H10). intro. 
  destruct H11. destruct H11. 
  generalize (H5 _ _ _ H7 (refl_equal (Mreturn :: k)) H12). intro. 
  destruct H13. exists x1. 
  eapply exec_add_block; eauto. 
  assert (i :: x = i :: to_next_block (i :: x)). 
  destruct i; inversion B; simpl; trivial.   
  rewrite <- H14 in H11. auto. 

  generalize (talk _ _ H6). intro. 
  generalize (H5 _ _ _ H6 (refl_equal (Mreturn :: c)) H7). intro. 
  destruct H8. 
  assert (fn_stacksize f0 = fn_stacksize tf).
  unfold transf_function in H6. 
  caseEq (transf_code (fn_code f0)).
  intros. rewrite H9 in H6. injection H6; intro. 
  rewrite <- H10. simpl. trivial. 
  intro. rewrite H9 in H6. discriminate. 

  assert (fn_framesize f0 = fn_framesize tf).
  unfold transf_function in H6.
  caseEq (transf_code (fn_code f0)).
  intros. rewrite H10 in H6. injection H6; intro. 
  rewrite <- H11. simpl. trivial. 
  intro. rewrite H10 in H6. discriminate. 
  rewrite H9 in H1. rewrite H10 in H8. 
  eapply exec_funct_body; eauto. 
  
  unfold init_frame. rewrite <- H10. auto. 
  simpl in H3. case_eq (transf_function f0); intros. rewrite H4 in H3. 
  injection H3; intros; subst. 
  eapply exec_funct_internal; eauto. 
  rewrite H4 in H3. inversion H3. 

  simpl in H4. injection H4; intros; subst. 
  eapply exec_funct_external; eauto. 

(*
  intros. generalize (H2 link ra H4 H5 _ H3). 
  intro. auto. *)
Qed.

Theorem transf_program_correct_aux:
  forall (p tp : program) (r : val) (t : trace),
  transf_program p = Some tp ->
  exec_program p t r ->
  exec_program tp t r.
Proof.
  intros. destruct H0 as [b].  destruct H0 as [f]. destruct H0 as [rs].
  destruct H0 as [m]. destruct H0. destruct H1. destruct H2. destruct H3.

  cut (exists tf, transf_fundef f = Some tf).
    intro E; destruct E as [tf]. 

    exists b; exists tf; exists rs; exists m.
      generalize (trans_program_inv _ _ H); intro H'.  
    rewrite (transform_partial_program_main transf_fundef p H').
    rewrite (Genv.init_mem_transf_partial transf_fundef p H').
    rewrite (Genv.find_symbol_transf_partial transf_fundef p H').
    generalize (Genv.find_funct_ptr_transf_partial transf_fundef H' H1).
    intro. destruct H4. 
  
  (*
  assert (SIG : fn_sig f = fn_sig tf).
  unfold transf_function in H5. 
  caseEq (transf_code (fn_code f)); intros; rewrite H8 in H5.
  injection H5; intro. rewrite <- H9. simpl. trivial.
  discriminate. 
  *)

  split; try split; try split; try split; trivial; try congruence.  

  eapply (transf_function_correct p tp f rs m t H); trivial.
    generalize (trans_program_inv _ _ H); clear H; intro H.  
  generalize (Genv.find_funct_ptr_transf_partial transf_fundef H H1).
  intros. destruct H3. 
  caseEq (transf_fundef f). intros. exists f0. trivial.
  intros. rewrite H5 in H4. intuition.
Qed.

Theorem transf_program_correct:
  forall (p tp : program) (r : val) (t : trace),
  transf_program p = Some tp ->
  Machabstr.exec_program p t r ->
  Machabstr.exec_program tp t r. 
Proof. 
  intros. 
  eapply eq2; eauto.  
  generalize (eq1 _ _ _ H0). 
  intro. eapply transf_program_correct_aux; eauto. 
Qed. 
 
Theorem transf_program_preserve_typing:
  forall (p tp : program),
  transf_program p = Some tp ->
  Machtyping.wt_program tp. 
Proof. 
  intros. 
  unfold transf_program in H. 
  case_eq (transform_partial_program transf_fundef p); intros. 
  rewrite H0 in H. 
  case_eq (typer p0); intros. 
  eapply Machtyper.typer_correct; eauto. 
 rewrite H1 in H. injection H; intros; subst ; trivial. 
 rewrite H1 in H. inversion H. 
 rewrite H0 in H. inversion H. 
Qed. 






