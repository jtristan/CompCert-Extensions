(***********************************************************************)
(*                                                                     *)
(*                        Compcert Extensions                          *)
(*                                                                     *)
(*                       Jean-Baptiste Tristan                         *)
(*                                                                     *)
(*  All rights reserved.  This file is distributed under the terms     *)
(*  described in file ../../LICENSE.                                   *)
(*                                                                     *)
(***********************************************************************)



Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats. 
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import FSets.
Require Import FSetWeakInterface. 
Require Import FSetWeakList.  
Require Import FSetWeakFacts. 
Require Import FSetWeakProperties. 
Require Import DecidableType. 
Require Import Setoid. 
Require Import RTL. 
Require Import Base.  
Require Import Formalization. 

Fixpoint of_value (ge : genv) (v : symbolic_value) (s : state) {struct v} := 
  match v with
  | Sreg r => Some (s.(rs) # r)
  | Sop op args =>  
    match (of_value_list ge args s) with 
    | Some e => eval_operation  _ ge s.(sp) op e 
    | None => None
    end
  | Sload mc addr args m =>  
    match of_value_list ge args s, (of_mem ge m s) with
    | Some e, Some mm =>
      match eval_addressing ge s.(sp) addr e with
      | Some a => Mem.loadv mc mm a 
      | _ => None
      end
    | _, _ => None
    end
  end

with of_mem ge (m : symbolic_mem) (s : state) {struct m} :=
  match m with
  | Smem => Some (s.(mm))
  | Sstore mc addr args v m =>
    match of_value_list ge args s with
    | Some e =>  
       match (eval_addressing ge s.(sp) addr e), (of_value ge v s), (of_mem ge m s) with
       | Some a, Some f, Some m => Mem.storev mc m a f
       | _, _, _ => None
       end
  | None => None
  end
  end

with of_value_list ge  (vl : symbolic_value_list) (s : state) {struct vl} :=
  match vl with
  | Snil => Some nil
  | Scons v vl => 
    match (of_value ge v s), (of_value_list ge vl s) with
    | Some e, Some l => Some (e :: l)
    | _, _ => None
    end
  end. 

Inductive sem : genv -> sym_state -> state -> state -> Prop :=
  | Sem_intro:
    forall ge s s' stack c sp rs rs' m m' t,
    s = mkst stack c sp rs m ->
    s' = mkst stack c sp rs' m' ->
    of_mem ge t.(mem) s = Some m' ->
    (forall r e, In (r,e) (PTree.elements (t.(file))) -> of_value ge e s = Some (rs' # r)) ->
    (forall r, ~ In r (map (@fst _ symbolic_value) (PTree.elements (t.(file)))) -> rs # r = rs' # r) ->
    sem ge t s s'. 

Lemma lsteps_is_flat: 
  forall ge l s s',
  lsteps ge l s s' -> s.(stack) = s'.(stack) /\ s.(sp) = s'.(sp) /\ s.(c) = s'.(c). 
Proof. 
  induction l; intros. 
  inversion H; subst; try congruence. intuition. 
  destruct a; inversion H; subst; try congruence; inversion H0; subst.
  generalize (IHl _ _ H3); intro. simpl in H1; simpl. intuition.
  generalize (IHl _ _ H4); intro. simpl in H1; simpl. intuition.
  generalize (IHl _ _ H5); intro. simpl in H1; simpl. intuition.
  generalize (IHl _ _ H5); intro. simpl in H1; simpl. intuition.
Qed.   

Lemma elements_fold_1n:
  forall r l w s0 ge x, 
  ~ In r (map (@fst positive _) l) ->
  (fold_left
   (fun (a : (option (Regmap.t val))) (p : positive * symbolic_value) =>
   match a with
        | Some m => 
            match of_value ge (snd p) s0 with
            | Some v => Some m # (fst p) <- v
            | None => None (A:=val * PTree.t val)
            end
        | None => None (A:=val * PTree.t val)
        end
    ) l w) = Some x -> exists k, w = Some k /\ k # r = x # r.
Proof. 
  induction l; intros. 
  simpl in H0. subst. exists x.  intuition. 
  simpl in H0. 
  generalize (IHl 
     match w with
       | Some m =>
           match of_value ge (snd a) s0 with
           | Some v => Some m # (fst a) <- v
           | None => None (A:=val * PTree.t val)
           end
       | None => None (A:=val * PTree.t val)
       end ); intro.
  generalize (elements_fold_0 _ _ _ H); intro.
  generalize (H1 s0 ge x H2 H0); intro.
  destruct H3. destruct H3. 
  case_eq w; intros. 
  subst. 
  case_eq (of_value ge (snd a) s0); intros. rewrite H5 in H3. 
  rewrite <- H4. inversion H3; subst. 
  exists t. intuition. 
  clear IHl H0 H1.
  simpl in H. intuition.
  rewrite Regmap.gso; congruence. 
  rewrite H5 in H3; congruence. 
  subst; congruence.
Qed.  

Lemma fatigue:
  forall ge r s0 s1 l w x,
  In (r, s1) l -> 
  list_norepet (map (fst (A:=PTree.elt) (B:=symbolic_value)) l) ->
  fold_left (fun (a : option (Regmap.t val)) (p : positive * symbolic_value) =>
        match a with
        | Some m => 
            match of_value ge (snd p) s0 with
            | Some v => Some m # (fst p) <- v
            | None => None (A:=val * PTree.t val)
            end
        | None => None (A:=val * PTree.t val)
        end) l w = Some x -> 
  of_value ge (s1) s0 = Some (x # r).
Proof. 
  induction l; intros. 
  inversion H.

  inversion H; subst. 
  simpl in H1. simpl in H0. 
  assert (list_norepet ((r :: nil) ++ map (fst (A:=PTree.elt) (B:=symbolic_value)) l)). trivial. 
  generalize (list_norepet_app (r :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l)); intro. intuition.  
  assert (In r (r :: nil)). simpl. left. trivial.
  generalize (@list_disjoint_notin _ (r :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l) r H7 H5); intro.
  generalize (elements_fold_1n _ _ _ _ _ _ H8 H1); intro.
  destruct H9. destruct H9.
  case_eq w; intros; subst; try congruence. 
  case_eq (of_value ge s1 s0); intros. 
  rewrite H11 in H9. 2: rewrite H11 in H9; congruence. 
  clear IHl H1 H0 H2 H7 H6 H8 H3 H4. 
  inversion H9; subst. 
  rewrite <- H10. rewrite Regmap.gss. trivial. 

  simpl in H0. inversion H0. simpl in H1.  eapply IHl; eauto. 
Qed. 
(*
Lemma elements_fols_not_in:
  forall r ge s0 l w, 
  ~ In r (map (@fst positive _) l) ->
    fold_left (fun (a : option (Regmap.t val)) (p : positive * symbolic_value) =>
        match a with
        | Some m => 
            match of_value ge (snd p) s0 with
            | Some v => Some m # (fst p) <- v
            | None => None (A:=val * PTree.t val)
            end
        | None => None (A:=val * PTree.t val)
        end) l w = Some x -> exists k, w = Some k /\ k # r = x # r.
Proof.
  induction l; intros. 
  simpl. trivial. 
  simpl. generalize (IHl (match w ! r with
  | Some m =>
      match of_value ge (snd a) s0 with
      | Some v => Some m # (fst a) <- v
      | None => None (A:=val * PTree.t val)
      end
  | None => None (A:=val * PTree.t val)
  end)); intro.
  generalize (elements_fold_0 _ _ _ H); intro.
  generalize (H0 H1); intro. 
  rewrite H2. 
  destruct a. simpl; simpl in *|-. 
  generalize (peq p r); intro. 
  destruct H3. 
  intuition. rewrite PTree.gso. trivial. congruence.   
Qed. 
*)
Lemma sem_value:
  forall ge s0 t r s,
  sem ge t s0 s -> 
  of_value ge (find r (file t))  s0 = Some s.(rs) # r.
Proof.
  intros. unfold find. 
  case_eq ((file t) ! r) ; intros.
  inversion H; subst. 
  generalize (PTree.elements_correct _ _ H0); intro. eapply H4; eauto. 
  simpl. 
  inversion H; subst. 
  simpl.  
  rewrite H5. trivial. 
  intuition. generalize (elements_2 _ _ H1); intro. 
  destruct H2. generalize (PTree.elements_complete _ _ _ H2); intro.
  congruence. 
Qed. 

Lemma ovl_inv_strong:
  forall ge s0 l t s,
  sem ge t s0 s -> 
  of_value_list ge (get_args l (file t)) s0 = Some (s.(rs) ## l).
Proof. 
  induction l; intros. 
  simpl. trivial. 
  simpl. 
  generalize  (sem_value _ _ _ a _ H); intro. rewrite H0.
  generalize (IHl _ _ H); intro.
   rewrite H1. trivial. 
Qed. 

Lemma ovl_inv:
  forall ge l0 s x,
  of_value_list ge (get_args l0 (PTree.empty symbolic_value)) s = Some x -> x =(s.(rs) ## l0).
Proof. 
  induction l0; intros. 
  simpl. simpl in H. congruence.  
  simpl. simpl in H. 
  case_eq (of_value ge (find a (PTree.empty symbolic_value)) s); intros. 
  rewrite H0 in H. 
  case_eq (of_value_list ge (get_args l0 (PTree.empty symbolic_value)) s); intros. 
  rewrite H1 in H. 
  inversion H; subst. 
  generalize (IHl0 _ _ H1); intros. subst. 
  unfold find in H0. rewrite PTree.gempty in H0.
  simpl in H0. inversion H0; subst.
  trivial. 

  rewrite H1 in H. congruence. 
  rewrite H0 in H. congruence. 
Qed. 

Lemma value_op:
  forall ge t s r op args v s',
  sem ge t s s' -> s'.(rs) = r -> 
  eval_operation fundef ge s.(sp) op r ## args = Some v ->
  of_value ge (Sop op (get_args args (file t))) s = Some v.
Proof. 
  intros. 
  simpl. 
  generalize (ovl_inv_strong _ _ args _ _ H); intro.
  rewrite H2. rewrite H0. trivial. 
Qed.      

Lemma value_load:
  forall ge t s s' chunk addr args a0 v,
  sem ge t s s' -> 
  eval_addressing ge s.(sp) addr s'.(rs) ## args = Some a0 ->
  loadv chunk s'.(mm) a0 = Some v ->
  of_value ge (Sload chunk addr (get_args args (file t)) (mem t)) s = Some v.
Proof.
  intros. 
  simpl. 
  generalize (ovl_inv_strong _ _ args _ _ H); intro.
  rewrite H2. 
  inversion H; subst. 
  case_eq (of_mem ge (mem t) (mkst stack c sp rs m)); intros. 
    rewrite H3 in H5. 2: rewrite H3 in H5; congruence. 
  rewrite H0.
  simpl in H1. 
  inversion H5; subst. 
  congruence. 
Qed. 

Lemma one_aux :
  forall ge t s0 si sj a,
  sem ge t s0 si -> lsteps ge (a :: nil) si sj -> sem ge (symbolic_evaluation_rec (a:: nil) t) s0 sj.
Proof.
  intros.
  generalize H; intro BACKUP.  
  inversion H; subst. 

  destruct a. 
  
  inversion H0; subst; try congruence. inversion H1; subst. clear H1. inversion H2; subst. clear H2. 
  inversion H7; subst; try congruence. 
  simpl. 
  eapply Sem_intro; eauto; simpl.

  intros. generalize (peq res r); intro. destruct H2. 

     subst. rewrite Regmap.gss. 
     assert (e = find arg (file t)). 
         assert (PTree.get r (PTree.set r (find arg (file t)) (file t)) = Some (find arg (file t))). 
         rewrite PTree.gss. trivial. 
         generalize (PTree.elements_correct _ _ H2); intro. 
         generalize (PTree.elements_keys_norepet (PTree.set r (find arg (file t)) (file t))); intro. 
         generalize (PTree.elements_complete _ _ _ H1); intro. rewrite PTree.gss in H9. inversion H9; subst; trivial.  
     subst. unfold find. case_eq ((file t) ! arg); intros. 
     eapply H4; eauto. eapply PTree.elements_correct; eauto.
     simpl. rewrite H5. trivial. intuition. generalize (elements_2 _ _ H6); intro. 
     destruct H8. generalize (PTree.elements_complete _ _ _ H8); intro. congruence.
 
     rewrite Regmap.gso; auto. eapply H4; eauto. 
        generalize (PTree.elements_complete _ _ _ H1); intro. 
        rewrite PTree.gso in H2; auto. eapply PTree.elements_correct; eauto.  

  intros. generalize (peq res r); intro. destruct H2. 

    subst. intuition.  
    assert (PTree.get r ((PTree.set r (find arg (file t)) (file t))) = Some (find arg (file t))).
      rewrite PTree.gss. trivial. 
    generalize (PTree.elements_correct _ _ H2); intro. 
    generalize (in_map _ _ _ _ H6); intro.
    generalize (H1 H8); intro. inversion H9. 

    
    rewrite Regmap.gso; auto. rewrite H5; auto. 
    assert (PTree.get r (PTree.set res (find arg (file t)) (file t)) = None). 
      case_eq (PTree.get r (PTree.set res (find arg (file t)) (file t))); intros.
      generalize (PTree.elements_correct _ _ H2); intro. 
      generalize (in_map _ _ _ _ H6); intro. intuition.
      trivial. 
    rewrite PTree.gso in H2; auto. intuition. 
    generalize (elements_2 _ _ H6); intro. destruct H8. 
    generalize (PTree.elements_complete _ _ _ H8); intro. congruence.  


  (* autre cas *)
 
  inversion H0; subst; try congruence. inversion H1; subst. clear H1. inversion H6; subst. clear H6. 
  inversion H8; subst; try congruence. 
  simpl. 
  eapply Sem_intro; eauto; simpl.

  intros. generalize (peq res r); intro. destruct H6. 

     subst. rewrite Regmap.gss. 
     assert (e = Sop op (get_args args (file t))). 
         assert (PTree.get r (PTree.set r (Sop op (get_args args (file t))) (file t)) = Some (Sop op (get_args args (file t)))). 
         rewrite PTree.gss. trivial. 
         generalize (PTree.elements_correct _ _ H6); intro. 
         generalize (PTree.elements_keys_norepet (PTree.set r (Sop op (get_args args (file t))) (file t))); intro. 
         generalize (PTree.elements_complete _ _ _ H1); intro. rewrite PTree.gss in H10. inversion H10; subst; trivial.  
     subst. eapply value_op; eauto.  
 
     rewrite Regmap.gso; auto. eapply H4; eauto. 
        generalize (PTree.elements_complete _ _ _ H1); intro. 
        rewrite PTree.gso in H6; auto. eapply PTree.elements_correct; eauto.  

  intros. generalize (peq res r); intro. destruct H6. 

    subst. intuition.  
    assert (PTree.get r (PTree.set r (Sop op (get_args args (file t))) (file t)) = Some (Sop op (get_args args (file t)))). 
      rewrite PTree.gss. trivial. 
    generalize (PTree.elements_correct _ _ H6); intro. 
    generalize (in_map _ _ _ _ H7); intro.
    generalize (H1 H9); intro. inversion H10. 

    
    rewrite Regmap.gso; auto. rewrite H5; auto. 
    assert (PTree.get r (PTree.set res (Sop op (get_args args (file t))) (file t)) = None). 
      case_eq (PTree.get r (PTree.set res (Sop op (get_args args (file t))) (file t))); intros.
      generalize (PTree.elements_correct _ _ H6); intro. 
      generalize (in_map _ _ _ _ H7); intro. intuition.
      trivial. 
    rewrite PTree.gso in H6; auto. intuition. 
    generalize (elements_2 _ _ H7); intro. destruct H9. 
    generalize (PTree.elements_complete _ _ _ H9); intro. congruence.  

  (* autre cas *)

  inversion H0; subst; try congruence. inversion H1; subst. clear H1. inversion H7; subst. clear H7. 
  inversion H9; subst; try congruence. 
  simpl. 
  eapply Sem_intro; eauto; simpl.

  intros. generalize (peq dst r); intro. destruct H7. 

     subst. rewrite Regmap.gss. 
     assert (e = Sload chunk addr (get_args args (file t)) (mem t)).  
         assert (PTree.get r (PTree.set r (Sload chunk addr (get_args args (file t)) (mem t)) (file t)) = Some (Sload chunk addr (get_args args (file t)) (mem t))). 
         rewrite PTree.gss. trivial. 
         generalize (PTree.elements_correct _ _ H7); intro. 
         generalize (PTree.elements_keys_norepet (PTree.set r (Sload chunk addr (get_args args (file t)) (mem t)) (file t))); intro. 
         generalize (PTree.elements_complete _ _ _ H1); intro. rewrite PTree.gss in H11. inversion H11; subst; trivial.  
     subst. eapply value_load; eauto.  
 
     rewrite Regmap.gso; auto. eapply H4; eauto. 
        generalize (PTree.elements_complete _ _ _ H1); intro. 
        rewrite PTree.gso in H7; auto. eapply PTree.elements_correct; eauto.  

  intros. generalize (peq dst r); intro. destruct H7. 

    subst. intuition.  
    assert (PTree.get r (PTree.set r (Sload chunk addr (get_args args (file t)) (mem t)) (file t)) = Some (Sload chunk addr (get_args args (file t)) (mem t))). 
      rewrite PTree.gss. trivial. 
    generalize (PTree.elements_correct _ _ H7); intro. 
    generalize (in_map _ _ _ _ H8); intro.
    generalize (H1 H10); intro. inversion H11. 

    
    rewrite Regmap.gso; auto. rewrite H5; auto. 
    assert (PTree.get r (PTree.set dst (Sload chunk addr (get_args args (file t)) (mem t)) (file t)) = None). 
      case_eq (PTree.get r (PTree.set dst (Sload chunk addr (get_args args (file t)) (mem t)) (file t))); intros.
      generalize (PTree.elements_correct _ _ H7); intro. 
      generalize (in_map _ _ _ _ H8); intro. intuition.
      trivial. 
    rewrite PTree.gso in H7; auto. intuition. 
    generalize (elements_2 _ _ H8); intro. destruct H10. 
    generalize (PTree.elements_complete _ _ _ H10); intro. congruence.  

  (* autre cas *)

  inversion H0; subst; try congruence. inversion H1; subst. clear H1. inversion H7; subst. clear H7. 
  inversion H9; subst; try congruence. 
  simpl. 
  eapply Sem_intro; eauto; simpl.

  rewrite (ovl_inv_strong _ _ args _ _ BACKUP).
  simpl.
  rewrite H2.
  rewrite (sem_value _ _ _ src _ BACKUP).
  rewrite H3. 
  simpl. 
  rewrite H6. 
  trivial. 
Qed. 

Lemma one : 
  forall ge s0 l t s s',
  sem ge t s0 s -> lsteps ge l s s' -> 
  sem ge (symbolic_evaluation_rec l t) s0 s'. 
Proof. 
  induction l; intros.  
  inversion H0; subst; try congruence. simpl. trivial. 
 
  case_eq a; intros; subst.

  inversion H0; subst; try congruence. inversion H1; subst. clear H1.
  assert (sem ge (symbolic_evaluation_rec (Imove arg res :: nil) t) s0 (mkst stack c sp rs # res <- (rs# arg) m)).
    eapply one_aux; eauto.
    eapply exec_Imove; eauto.
    eapply exec_start; eauto. 
  generalize (IHl _ _ _ H1 H4); intro.
  simpl in H2. simpl. trivial. 
  
  inversion H0; subst; try congruence. inversion H1; subst. clear H1.
  assert (sem ge (symbolic_evaluation_rec (Iop op args res :: nil) t) s0 (mkst stack c sp rs # res <- v m)).
    eapply one_aux; eauto.
    eapply exec_Iop; eauto.
    eapply exec_start; eauto. 
  generalize (IHl _ _ _ H1 H5); intro.
  simpl in H3. simpl. trivial. 

  inversion H0; subst; try congruence. inversion H1; subst. clear H1.
  assert (sem ge (symbolic_evaluation_rec (Iload chunk addr args dst :: nil) t) s0 (mkst stack c sp rs # dst <- v m0)).
    eapply one_aux; eauto.
    eapply exec_Iload; eauto.
    eapply exec_start; eauto. 
  generalize (IHl _ _ _ H1 H6); intro.
  simpl in H3. simpl. trivial. 
 
  inversion H0; subst; try congruence. inversion H1; subst. clear H1.
  assert (sem ge (symbolic_evaluation_rec (Istore chunk addr args src :: nil) t) s0 (mkst stack c sp rs m')).
    eapply one_aux; eauto.
    eapply exec_Istore; eauto.
    eapply exec_start; eauto. 
  generalize (IHl _ _ _ H1 H6); intro.
  simpl in H3. simpl. trivial.  
Qed. 
  
Definition satisfy_value (ge : genv) (s : state) (v : tv) := 
  match v with 
  | V v => exists x, of_value ge v s = Some x
  | M v => exists x, of_mem ge v s = Some x
  end.
Definition satisfy_sym_state (ge : genv) (s : state) (sy : sym_state) := forall e, Constraints.In e sy.(cons) -> satisfy_value ge s e.



Lemma  two_aux_aux_list:
  forall ge s0 args t s,
  sem ge t s0 s -> 
  of_value_list ge (get_args args (file t))  s0 = Some s.(rs) ## args.
Proof. 
  induction args; intros.
  simpl. trivial. 
  simpl.
  assert (of_value ge (find a (file t)) s0 = Some (s.(rs) # a)).
    eapply sem_value; eauto.
  rewrite H0. 
  generalize (IHargs _ _ H); intro. 
  rewrite H1. 
  trivial. 
Qed. 

Lemma sem_id:
  forall ge t s s',
  sem ge t s s' -> s.(stack) = s'.(stack) /\ s.(sp) = s'.(sp) /\ s.(c) = s'.(c).
Proof. 
  intros. inversion H; subst. simpl. intuition. 
Qed. 

Lemma two_aux : 
  forall ge s0 a t s s',
  satisfy_sym_state ge s0 t -> sem ge t s0 s -> lsteps ge (a :: nil) s s' -> 
  satisfy_sym_state ge s0 (symbolic_evaluation_rec (a :: nil) t).
Proof. 
  intros.
  unfold satisfy_sym_state in H.
  unfold satisfy_sym_state. 
  intros. 
  
  destruct a; simpl in H2. 

  eauto.

  rewrite P.add_union_singleton in H2. 
  generalize (Constraints.union_1 H2); clear H2; intro. 
  destruct H2; eauto. 
  generalize (Constraints.singleton_1 H2); clear H2; intro. 
  unfold Constraints.E.eq in H2. unfold Constraint.eq in H2. subst. 
  unfold satisfy_value. simpl.
  inversion H1; subst; try congruence. inversion H2; subst. clear H2. 
  assert (of_value_list ge (get_args args (file t)) s0 = Some rs ## args).  
    assert (rs = (mkst stack c sp rs m).(Base.rs)). trivial. rewrite H2. 
    eapply two_aux_aux_list; eauto. 
 exists v. rewrite H2. generalize (sem_id _ _ _ _ H0); intro. intuition. simpl in *|-; subst; trivial. 
  
  rewrite P.add_union_singleton in H2. 
  generalize (Constraints.union_1 H2); clear H2; intro. 
  destruct H2; eauto. 
  generalize (Constraints.singleton_1 H2); clear H2; intro. 
  unfold Constraints.E.eq in H2. unfold Constraint.eq in H2. subst. 
  unfold satisfy_value. simpl.
  inversion H1; subst; try congruence. inversion H2; subst. clear H2. 
  assert (of_value_list ge (get_args args (file t)) s0 = Some rs ## args).  
    assert (rs = (mkst stack c sp rs m0).(Base.rs)). trivial. rewrite H2. 
    eapply two_aux_aux_list; eauto. 
  rewrite H2. generalize (sem_id _ _ _ _ H0); intro. intuition. simpl in *|-; subst; trivial.   
  inversion H0; subst. 

  rewrite H3. exists v. rewrite <- H4. 
  rewrite H8. congruence. 

  rewrite P.add_union_singleton in H2. 
  generalize (Constraints.union_1 H2); clear H2; intro. 
  destruct H2; eauto. 
  generalize (Constraints.singleton_1 H2); clear H2; intro. 
  unfold Constraints.E.eq in H2. unfold Constraint.eq in H2. subst.
  inversion H1; subst; try congruence.
    assert (of_value_list ge (get_args args (file t)) s0 = Some rs ## args).  
    assert (rs = (mkst stack c sp rs m0).(Base.rs)). trivial. rewrite H5. 
    eapply two_aux_aux_list; eauto. 
  generalize (sem_id _ _ _ _ H0); intro. intuition. simpl in *|-; subst; trivial.
  generalize (sem_value _ _ _ src _ H0); intro.
  inversion H0; subst. 
  simpl. inversion H2; subst.  

  rewrite H5. simpl in H3. rewrite H3. rewrite H6. rewrite H10. simpl. 
  exists m'. rewrite <- H4. congruence.

Qed.  

Lemma two : 
  forall ge s0 l t s s',
  satisfy_sym_state ge s0 t -> sem ge t s0 s -> lsteps ge l s s' -> 
  satisfy_sym_state ge s0 (symbolic_evaluation_rec l t). 
Proof. 
  induction l; intros. 
  inversion H0; subst; try congruence.
  simpl. trivial.  
  
  case_eq a; intros; subst. 
  
  inversion H1; subst; try congruence.
  inversion H2; subst. 
  assert (lsteps ge (Imove arg res :: nil) (mkst stack c sp rs m) (mkst stack c sp rs # res <- (rs # arg) m)). 
    eapply exec_Imove; eauto. 
    eapply exec_start; eauto. 
  assert (satisfy_sym_state ge s0 (symbolic_evaluation_rec (Imove arg res :: nil) t)). 
    eapply two_aux; eauto. 
  generalize (one_aux _ _ _ _ _ _ H0 H3); intro. 
  generalize (IHl _ _ _ H4 H6 H5); intro. 
  simpl in H7. simpl. trivial. 

  inversion H1; subst; try congruence.
  inversion H2; subst.
  assert (lsteps ge (Iop op args res :: nil) (mkst stack c sp rs m) (mkst stack c sp rs # res <- v m)). 
    eapply exec_Iop; eauto. 
    eapply exec_start; eauto.   
  assert (satisfy_sym_state ge s0 (symbolic_evaluation_rec (Iop op args res :: nil) t)). 
    eapply two_aux; eauto.
  generalize (one_aux _ _ _ _ _ _ H0 H4); intro. 
  generalize (IHl _ _ _ H5 H7 H6); intro. 
  simpl in H8. simpl. trivial. 

  inversion H1; subst; try congruence.
  inversion H2; subst. 
  assert (lsteps ge (Iload chunk addr args dst :: nil) (mkst stack c sp rs m0) (mkst stack c sp rs # dst <- v m0)).
      eapply exec_Iload; eauto. 
    eapply exec_start; eauto.
  assert (satisfy_sym_state ge s0 (symbolic_evaluation_rec (Iload chunk addr args dst :: nil) t)). 
    eapply two_aux; eauto.
  generalize (one_aux _ _ _ _ _ _ H0 H5); intro.   
  generalize (IHl _ _ _ H6 H8 H7); intro. 
  simpl in H9. simpl. trivial. 

  inversion H1; subst; try congruence.
  inversion H2; subst. 
  assert ( lsteps ge (Istore chunk addr args src :: nil) (mkst stack c sp rs m0) (mkst stack c sp rs m')). 
      eapply exec_Istore; eauto. 
      eapply exec_start; eauto.
  assert (satisfy_sym_state ge s0 (symbolic_evaluation_rec (Istore chunk addr args src :: nil) t)). 
    eapply two_aux; eauto.
  generalize (one_aux _ _ _ _ _ _ H0 H5); intro.   
  generalize (IHl _ _ _ H6 H8 H7); intro. 
  simpl in H9. simpl. trivial.
Qed.  

(* Contient des enonces classiques sur les cas de bases *)
Theorem correct : 
  forall ge l s s',
  lsteps ge l s s' -> sem ge (symbolic_evaluation l) s s' /\ satisfy_sym_state ge s (symbolic_evaluation l).
Proof. 
  intros. unfold symbolic_evaluation.  
  split. 
  eapply one; eauto. unfold initial_state. destruct s; destruct s'.  eapply Sem_intro; eauto.
  intros. simpl in H0. inversion H0. 
  eapply two; eauto. 
  unfold satisfy_sym_state. 
  intros. simpl in H0. inversion H0. 
  unfold initial_state. destruct s; destruct s'.  eapply Sem_intro; eauto.  intros. simpl in H0. inversion H0. 
Qed. 

Lemma of_subst_1:
  (forall e ge stack c sp res rs arg m,
  of_value ge e (mkst stack c sp rs # res <- (rs # arg) m) =
  of_value ge (substitute_value e (PTree.set res (Sreg arg) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp res rs arg m,  
  of_mem ge e (mkst stack c sp rs # res <- (rs # arg) m) =
  of_mem ge (substitute_memory e (PTree.set res (Sreg arg) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp res rs arg m,  
  of_value_list ge e (mkst stack c sp rs # res <- (rs # arg) m) =
  of_value_list ge (substitute_value_list e (PTree.set res (Sreg arg) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)). 
Proof. 
  eapply (symbolic_combined_ind 
  (fun e => forall ge stack c sp res rs arg m,
  of_value ge e (mkst stack c sp rs # res <- (rs # arg) m) =
  of_value ge (substitute_value e (PTree.set res (Sreg arg) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp res rs arg m,  
  of_mem ge e (mkst stack c sp rs # res <- (rs # arg) m) =
  of_mem ge (substitute_memory e (PTree.set res (Sreg arg) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp res rs arg m,  
  of_value_list ge e (mkst stack c sp rs # res <- (rs # arg) m) =
  of_value_list ge (substitute_value_list e (PTree.set res (Sreg arg) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))); eauto; intros; simpl.

  generalize (peq res r); intros. 
  destruct H. subst. 
  rewrite Regmap.gss. unfold find. rewrite PTree.gss. simpl. trivial. 
  rewrite Regmap.gso; auto. unfold find. rewrite PTree.gso; auto. rewrite PTree.gempty. trivial. 

  rewrite H. trivial.

  rewrite H. rewrite H0. trivial. 

  rewrite H. rewrite H0. rewrite H1. trivial. 

  rewrite H. rewrite H0. trivial. 
Qed. 

Lemma simple_args:
  forall ge args stack c sp rs m, of_value_list ge (get_args args (PTree.empty symbolic_value)) (mkst stack c sp rs m) = Some rs ## args. 
Proof. 
  induction args; intros.
  simpl.  trivial. 
  simpl. unfold find. rewrite PTree.gempty. simpl. rewrite IHargs. trivial. 
Qed. 

Lemma of_subst_2:
  (forall e ge stack c sp res rs args op m v,
  eval_operation fundef ge sp op rs ## args = Some v ->
  of_value ge e (mkst stack c sp rs # res <- v m) =
  of_value ge (substitute_value e (PTree.set res (Sop op (get_args args (PTree.empty symbolic_value))) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp res rs args op m v,  
  eval_operation fundef ge sp op rs ## args = Some v ->
  of_mem ge e (mkst stack c sp rs # res <- v m) =
  of_mem ge (substitute_memory e (PTree.set res (Sop op (get_args args (PTree.empty symbolic_value))) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp res rs args op m v,  
  eval_operation fundef ge sp op rs ## args = Some v ->
  of_value_list ge e (mkst stack c sp rs # res <- v m) =
  of_value_list ge (substitute_value_list e (PTree.set res (Sop op (get_args args (PTree.empty symbolic_value))) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)). 
Proof. 
  eapply (symbolic_combined_ind 
  (fun e => forall ge stack c sp res rs args op m v,
  eval_operation fundef ge sp op rs ## args = Some v ->
  of_value ge e (mkst stack c sp rs # res <- v m) =
  of_value ge (substitute_value e (PTree.set res (Sop op (get_args args (PTree.empty symbolic_value))) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp res rs args op m v,  
  eval_operation fundef ge sp op rs ## args = Some v ->
  of_mem ge e (mkst stack c sp rs # res <- v m) =
  of_mem ge (substitute_memory e (PTree.set res (Sop op (get_args args (PTree.empty symbolic_value))) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp res rs args op m v,  
  eval_operation fundef ge sp op rs ## args = Some v ->
  of_value_list ge e (mkst stack c sp rs # res <- v m) =
  of_value_list ge (substitute_value_list e (PTree.set res (Sop op (get_args args (PTree.empty symbolic_value))) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  ); eauto; intros; simpl.

  generalize (peq res r); intros. 
  destruct H0. subst. 
  rewrite Regmap.gss. unfold find. rewrite PTree.gss. simpl. 
  rewrite simple_args. congruence. 
  rewrite Regmap.gso; auto. unfold find. rewrite PTree.gso; auto. rewrite PTree.gempty. trivial. 

  rewrite (H ge stack c sp res rs args op m v H0). trivial.

  rewrite (H ge stack c sp res rs args op m0 v H1). rewrite (H0 ge stack c sp res rs args op m0 v H1). trivial. 

  rewrite (H ge stack c sp res rs args op m0 v H2). rewrite (H0 ge stack c sp res rs args op m0 v H2). rewrite (H1 ge stack c sp res rs args op m0 v H2). trivial. 

  rewrite (H ge stack c sp res rs args op m v H1). rewrite (H0 ge stack c sp res rs args op m v H1). trivial. 
Qed.   

Lemma of_subst_3:
  (forall e ge stack c sp res rs args m v a chunk addr,
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->  
  of_value ge e (mkst stack c sp rs # res <- v m) =
  of_value ge (substitute_value e (PTree.set res (Sload chunk addr (get_args args (PTree.empty symbolic_value)) Smem) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp res rs args m v a chunk addr,  
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->
  of_mem ge e (mkst stack c sp rs # res <- v m) =
  of_mem ge (substitute_memory e (PTree.set res (Sload chunk addr (get_args args (PTree.empty symbolic_value)) Smem) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp res rs args m v a chunk addr,  
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->
  of_value_list ge e (mkst stack c sp rs # res <- v m) =
  of_value_list ge (substitute_value_list e (PTree.set res (Sload chunk addr (get_args args (PTree.empty symbolic_value)) Smem) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m)). 
Proof. 
  eapply (symbolic_combined_ind 
  (fun e => forall ge stack c sp res rs args m v a chunk addr,
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->  
  of_value ge e (mkst stack c sp rs # res <- v m) =
  of_value ge (substitute_value e (PTree.set res (Sload chunk addr (get_args args (PTree.empty symbolic_value)) Smem) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp res rs args m v a chunk addr,  
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->
  of_mem ge e (mkst stack c sp rs # res <- v m) =
  of_mem ge (substitute_memory e (PTree.set res (Sload chunk addr (get_args args (PTree.empty symbolic_value)) Smem) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp res rs args m v a chunk addr,  
  eval_addressing ge sp addr rs ## args = Some a ->
  loadv chunk m a = Some v ->
  of_value_list ge e (mkst stack c sp rs # res <- v m) =
  of_value_list ge (substitute_value_list e (PTree.set res (Sload chunk addr (get_args args (PTree.empty symbolic_value)) Smem) (PTree.empty symbolic_value)) Smem) (mkst stack c sp rs m))
  ); eauto; intros; simpl.

  generalize (peq res r); intros. 
  destruct H1. subst. 
  rewrite Regmap.gss. unfold find. rewrite PTree.gss. simpl.  
  rewrite simple_args. rewrite H. congruence. 
  rewrite Regmap.gso; auto. unfold find. rewrite PTree.gso; auto. rewrite PTree.gempty. trivial. 

  rewrite (H ge stack c sp res rs args m v _ _ _ H0 H1). trivial.

  rewrite (H ge stack c sp res rs args m0 v _ _ _ H1 H2). rewrite (H0 ge stack c sp res rs args m0 v _ _ _ H1 H2). trivial. 

  rewrite (H ge stack c sp res rs args m0 v _ _ _ H2 H3). rewrite (H0 ge stack c sp res rs args m0 v _ _ _ H2 H3). 
  rewrite (H1 ge stack c sp res rs args m0 v _ _ _ H2 H3). trivial. 

  rewrite (H ge stack c sp res rs args m v _ _ _ H1 H2). rewrite (H0 ge stack c sp res rs args m v _ _ _ H1 H2). trivial. 
Qed.   

Lemma of_subst_4:
  (forall e ge stack c sp src rs args m a chunk addr m',
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  of_value ge e (mkst stack c sp rs m') =
  of_value ge (substitute_value e (PTree.empty symbolic_value) (Sstore chunk addr (get_args args (PTree.empty symbolic_value))
        (find src (PTree.empty symbolic_value)) Smem)) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp src rs args m a chunk addr m',  
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  of_mem ge e (mkst stack c sp rs m') =
  of_mem ge (substitute_memory e (PTree.empty symbolic_value) (Sstore chunk addr (get_args args (PTree.empty symbolic_value))
        (find src (PTree.empty symbolic_value)) Smem)) (mkst stack c sp rs m)) /\
  (forall e ge stack c sp src rs args m a chunk addr m',  
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  of_value_list ge e (mkst stack c sp rs m') =
  of_value_list ge (substitute_value_list e (PTree.empty symbolic_value) (Sstore chunk addr (get_args args (PTree.empty symbolic_value))
        (find src (PTree.empty symbolic_value)) Smem)) (mkst stack c sp rs m)). 
Proof. 
  eapply (symbolic_combined_ind 
  (fun e => forall ge stack c sp src rs args m a chunk addr m',
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  of_value ge e (mkst stack c sp rs m') =
  of_value ge (substitute_value e (PTree.empty symbolic_value) (Sstore chunk addr (get_args args (PTree.empty symbolic_value))
        (find src (PTree.empty symbolic_value)) Smem)) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp src rs args m a chunk addr m',  
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  of_mem ge e (mkst stack c sp rs m') =
  of_mem ge (substitute_memory e (PTree.empty symbolic_value) (Sstore chunk addr (get_args args (PTree.empty symbolic_value))
        (find src (PTree.empty symbolic_value)) Smem)) (mkst stack c sp rs m))
  (fun e => forall ge stack c sp src rs args m a chunk addr m',  
  eval_addressing ge sp addr rs ## args = Some a ->
  storev chunk m a rs # src = Some m' ->
  of_value_list ge e (mkst stack c sp rs m') =
  of_value_list ge (substitute_value_list e (PTree.empty symbolic_value) (Sstore chunk addr (get_args args (PTree.empty symbolic_value))
        (find src (PTree.empty symbolic_value)) Smem)) (mkst stack c sp rs m))
  ); eauto; intros; simpl.

  unfold find. rewrite PTree.gempty. simpl. trivial.  

  rewrite (H ge stack c sp src rs args m _ _ _ _ H0 H1). trivial.

  rewrite (H ge stack c sp src rs args m0 _ _ _ m' H1 H2). rewrite (H0 ge stack c sp src rs args m0 _ _ _ m' H1 H2). trivial. 

  rewrite simple_args. rewrite H. unfold find. rewrite PTree.gempty. simpl. congruence. 

  rewrite (H ge stack c sp src rs args m0 _ _ _ m' H2 H3). rewrite (H0 ge stack c sp src rs args m0 _ _ _ m' H2 H3). 
  rewrite (H1 ge stack c sp src rs args m0 _ _ _ m' H2 H3). trivial. 

  rewrite (H ge stack c sp src rs args m _ _ _ m' H1 H2). rewrite (H0 ge stack c sp src rs args m _ _ _ m' H1 H2). trivial. 
Qed.   

Lemma cons_in_rew:
  forall e a l,
  Constraints.In e (cons (symbolic_evaluation_rec (a :: nil) initial_state) ^^ (symbolic_evaluation_rec l initial_state)) ->
  Constraints.In e (cons (symbolic_evaluation_rec (a :: l) initial_state)). 
Proof. 
  intros. 
  assert (((symbolic_evaluation_rec (a :: nil) initial_state) ^^ (symbolic_evaluation_rec l initial_state)) ~ (symbolic_evaluation_rec (a :: l) initial_state)).
    eapply seq_symmetry. 
    assert ((symbolic_evaluation_rec (a :: l) initial_state) ~ (symbolic_evaluation_rec l (symbolic_evaluation_rec (a :: nil) initial_state))).
    eapply step_eval_sym; eauto.
    eapply seq_transitivity; eauto.
   rewrite decomposition.
   eapply seq_reflexivity. 
 inversion H0; subst. 
 clear H0 H1 H2. 
 rewrite <- H3.
 trivial. 
Qed. 

Lemma three_aux:
  forall ge s a l si,
  satisfy_sym_state ge s (symbolic_evaluation_rec (a :: l) initial_state) ->
  lsteps ge (a :: nil) s si ->
  satisfy_sym_state ge si (symbolic_evaluation_rec l initial_state).
Proof.
  intros. 
  unfold satisfy_sym_state in H. unfold satisfy_sym_state. 
  intros. 
  destruct e. 
  assert (Constraints.In ( V(substitute_value s0 (file (symbolic_evaluation_rec (a :: nil) initial_state)) (mem (symbolic_evaluation_rec (a :: nil) initial_state)))) 
             (cons (symbolic_evaluation_rec (a :: l) initial_state)) ).
      generalize (cons_get'); intro. 
     assert (     substitute_value_ext (V s0)
       (file (symbolic_evaluation_rec (a :: nil) initial_state))
       (mem (symbolic_evaluation_rec (a :: nil) initial_state)) =
     V
       (substitute_value s0
          (file (symbolic_evaluation_rec (a :: nil) initial_state))
          (mem (symbolic_evaluation_rec (a :: nil) initial_state)))). 
          simpl. trivial. 
     generalize (H2 (V
     (substitute_value s0
        (file (symbolic_evaluation_rec (a :: nil) initial_state))
        (mem (symbolic_evaluation_rec (a :: nil) initial_state)))) (symbolic_evaluation_rec (a :: nil) initial_state) (symbolic_evaluation_rec l initial_state) (V s0) H1 H3); intro.
     eapply cons_in_rew; eauto. 
    
  generalize (H _ H2); intro. 
  clear H H2.

  destruct a.
 
  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Imove r r0 :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H6; subst; try congruence. clear H3 H6. 
  exists x. rewrite <- H.
  unfold find. rewrite PTree.gempty.  
  destruct of_subst_1 as [A [B C]]. eapply A; eauto. 

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Iop o l0 r :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H7; subst; try congruence. clear H3 H7. 
  exists x. rewrite <- H.
  destruct of_subst_2 as [A [B C]]. eapply A; eauto. 

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Iload m a l0 r  :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H8; subst; try congruence. clear H3 H8. 
  exists x. rewrite <- H.
  destruct of_subst_3 as [A [B C]]. eapply A; eauto. 

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Istore m a l0 r :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H8; subst; try congruence. clear H3 H8. 
  exists x. rewrite <- H.
  destruct of_subst_4 as [A [B C]]. eapply A; eauto.

  assert (Constraints.In ( M(substitute_memory s0 (file (symbolic_evaluation_rec (a :: nil) initial_state)) (mem (symbolic_evaluation_rec (a :: nil) initial_state)))) 
             (cons (symbolic_evaluation_rec (a :: l) initial_state)) ).
      generalize (cons_get'); intro. 
     assert (     substitute_value_ext (M s0)
       (file (symbolic_evaluation_rec (a :: nil) initial_state))
       (mem (symbolic_evaluation_rec (a :: nil) initial_state)) =
     M
       (substitute_memory s0
          (file (symbolic_evaluation_rec (a :: nil) initial_state))
          (mem (symbolic_evaluation_rec (a :: nil) initial_state)))). 
          simpl. trivial. 
     generalize (H2 (M
     (substitute_memory s0
        (file (symbolic_evaluation_rec (a :: nil) initial_state))
        (mem (symbolic_evaluation_rec (a :: nil) initial_state)))) (symbolic_evaluation_rec (a :: nil) initial_state) (symbolic_evaluation_rec l initial_state) (M s0) H1 H3); intro.
     eapply cons_in_rew; eauto. 
    
  generalize (H _ H2); intro. 
  clear H H2.

  destruct a.      

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Imove r r0 :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H6; subst; try congruence. clear H3 H6. 
  exists x. rewrite <- H.
  unfold find. rewrite PTree.gempty.  
  destruct of_subst_1 as [A [B C]]. eapply B; eauto. 

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Iop o l0 r :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H7; subst; try congruence. clear H3 H7. 
  exists x. rewrite <- H.
  destruct of_subst_2 as [A [B C]]. eapply B; eauto. 

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Iload m a l0 r  :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H8; subst; try congruence. clear H3 H8. 
  exists x. rewrite <- H.
  destruct of_subst_3 as [A [B C]]. eapply B; eauto. 

  simpl in H3. destruct H3. unfold satisfy_value.
  assert (sem ge (symbolic_evaluation_rec (Istore m a l0 r :: nil) initial_state) s si).
    eapply one; eauto. unfold initial_state. destruct s. eapply Sem_intro; eauto. intros. simpl in H2. inversion H2.   
  inversion H0; subst; try congruence. inversion H3; subst. inversion H8; subst; try congruence. clear H3 H8. 
  exists x. rewrite <- H.
  destruct of_subst_4 as [A [B C]]. eapply B; eauto.
Qed. 

Lemma in_easy_aux: 
  forall l f m E, 
  Constraints.Subset E (cons (symbolic_evaluation_rec l (mkstate f m E))).
Proof. 
  induction l; intros. 
  simpl. eapply P.subset_refl. 
  simpl. 
  destruct a. 
  eapply IHl; eauto. 
  generalize (IHl (PTree.set r (Sop o (get_args l0 f)) f) m (Constraints.add (V (Sop o (get_args l0 f))) E)); intro.
  clear IHl. 
  assert (Constraints.Subset E (Constraints.add (V(Sop o (get_args l0 f))) E)). 
    eapply P.subset_add_2; eauto.
    eapply P.subset_refl. 
  eapply P.subset_trans; eauto.
  generalize (IHl (PTree.set r (Sload m0 a (get_args l0 f) m) f) m (Constraints.add (V (Sload m0 a (get_args l0 f) m)) E)); intro.
  clear IHl. 
  assert (Constraints.Subset E (Constraints.add (V (Sload m0 a (get_args l0 f) m)) E)). 
    eapply P.subset_add_2; eauto.
    eapply P.subset_refl. 
  eapply P.subset_trans; eauto. 
  generalize (IHl f (Sstore m0 a (get_args l0 f) (find r f) m) (Constraints.add (M (Sstore m0 a (get_args l0 f) (find r f) m)) E)); intro.
  clear IHl. 
  assert (Constraints.Subset E (Constraints.add (M (Sstore m0 a (get_args l0 f) (find r f) m)) E)). 
    eapply P.subset_add_2; eauto.
    eapply P.subset_refl. 
    eapply P.subset_trans; eauto.
Qed. 

Lemma in_easy:
  forall v l E f m,
  Constraints.In v (cons (symbolic_evaluation_rec l (mkstate f m (Constraints.add v E)))). 
Proof. 
  intros. 
  generalize (in_easy_aux l f m (Constraints.add v E)); intro.
  eapply P.in_subset; eauto. 
  eapply Constraints.add_1; eauto.
Qed.  

Lemma three:
  forall ge l s, 
  satisfy_sym_state ge s (symbolic_evaluation_rec l initial_state) -> exists s', lsteps ge l s s'.
Proof. 
  induction l; intros.
  exists s. eapply exec_start; eauto.

  case_eq a; intros; subst.

  assert (lsteps ge (Imove r r0 :: nil) s (mkst (stack s) (c s) (sp s) (rs s) # r0 <- ((rs s) # r) (mm s))).
    destruct s; simpl. 
    eapply exec_Imove; eauto.
    eapply exec_start; eauto. 
  generalize (three_aux _ _ _ _ ((mkst s.(stack) s.(c) s.(sp) (s.(rs) # r0 <- (s.(rs) # r)) s.(mm))) H H0); intro.
  generalize (IHl _ H1); intro. 
  destruct H2. exists x. 
  eapply exec_Imove; eauto.
  destruct s; trivial. 

  generalize H; intro SAT. 
  simpl in H.
  unfold satisfy_sym_state in H.
  assert (Constraints.In 
             ( V (Sop o (get_args l0 (PTree.empty symbolic_value))))
             (cons
         (symbolic_evaluation_rec l
            (mkstate
               (PTree.set r
                  (Sop o (get_args l0 (PTree.empty symbolic_value)))
                  (PTree.empty symbolic_value)) Smem
               (Constraints.add
                  ( V(Sop o (get_args l0 (PTree.empty symbolic_value))))
                  Constraints.empty))))).
               eapply in_easy; eauto. 
  generalize (H _ H0); intro. 
  clear H H0. 
  unfold satisfy_value in H1. 
  destruct  H1. inversion H. 
  case_eq (of_value_list ge (get_args l0 (PTree.empty symbolic_value)) s); intros. 
    rewrite H0 in H1.
      assert (l1 = (s.(rs) ## l0)). 
          eapply ovl_inv; eauto. 
      subst. 
    assert (lsteps ge (Iop o l0 r :: nil) s (mkst s.(stack) s.(c) s.(sp) (s.(rs)#r <- x) s.(mm))).
      destruct s. simpl. 
      eapply exec_Iop; eauto.
      simpl. eapply exec_start; eauto.
  
  generalize (IHl (mkst (stack s) (c s) (sp s) (rs s) # r <- x (mm s))); intro.
  generalize (three_aux _ _ _ _ (mkst s.(stack) s.(c) s.(sp) (s.(rs)#r <- x) s.(mm)) SAT H2); intro.
  generalize (IHl _ H4); intro. 
  destruct H5. exists x0. eapply exec_Iop; eauto.
  destruct s; trivial. 

  rewrite H0 in H1. congruence. 

  generalize H; intro SAT. 
  simpl in H.
  unfold satisfy_sym_state in H.
  assert (Constraints.In (V (Sload m a0 (get_args l0 (PTree.empty symbolic_value)) Smem))
      (cons
         (symbolic_evaluation_rec l
            (mkstate
               (PTree.set r
                  (Sload m a0 (get_args l0 (PTree.empty symbolic_value)) Smem)
                  (PTree.empty symbolic_value)) Smem
               (Constraints.add
                  (V (Sload m a0 (get_args l0 (PTree.empty symbolic_value)) Smem))
                  Constraints.empty))))). 
                  eapply in_easy; eauto. 
  generalize (H _ H0); intro. 
  clear H H0. 
  unfold satisfy_value in H1. 
  destruct  H1. inversion H. 
  case_eq (of_value_list ge (get_args l0 (PTree.empty symbolic_value)) s); intros. 
    rewrite H0 in H1.
      assert (l1 = (s.(rs) ## l0)). 
          eapply ovl_inv; eauto. 
      subst.
  case_eq (eval_addressing ge (sp s) a0 (rs s) ## l0); intros. 
    rewrite H2 in H1. 
    assert (lsteps ge (Iload m a0 l0 r:: nil) s (mkst s.(stack) s.(c) s.(sp) (s.(rs)#r <- x) s.(mm))).
      destruct s. simpl. 
      eapply exec_Iload; eauto.
      simpl. eapply exec_start; eauto.    
  generalize (IHl (mkst (stack s) (c s) (sp s) (rs s) # r <- x (mm s))); intro.
  generalize (three_aux _ _ _ _ (mkst s.(stack) s.(c) s.(sp) (s.(rs)#r <- x) s.(mm)) SAT H3); intro.
  generalize (IHl _ H5); intro. 
  destruct H6. exists x0. eapply exec_Iload; eauto.
  destruct s; trivial. 

  rewrite H2 in H1. congruence.
  rewrite H0 in H1. congruence. 

  generalize H; intro SAT. 
  simpl in H.
  unfold satisfy_sym_state in H. 
  assert (Constraints.In ( M(Sstore m a0 (get_args l0 (PTree.empty symbolic_value)) (find r (PTree.empty symbolic_value)) Smem))
      (cons
         (symbolic_evaluation_rec l
            (mkstate (PTree.empty symbolic_value)
               (Sstore m a0 (get_args l0 (PTree.empty symbolic_value))
                  (find r (PTree.empty symbolic_value)) Smem)
               (Constraints.add
                  (M
                     (Sstore m a0 (get_args l0 (PTree.empty symbolic_value))
                        (find r (PTree.empty symbolic_value)) Smem))
                  Constraints.empty))))).
                eapply in_easy; eauto.    
  generalize (H _ H0); intro. 
  clear H H0. 
  unfold satisfy_value in H1. 
  destruct  H1. inversion H. 
  case_eq (of_value_list ge (get_args l0 (PTree.empty symbolic_value)) s); intros. 
    rewrite H0 in H1.
      assert (l1 = (s.(rs) ## l0)). 
          eapply ovl_inv; eauto. 
      subst.
  case_eq (eval_addressing ge (sp s) a0 (rs s) ## l0); intros. 
    rewrite H2 in H1. 
  case_eq (of_value ge (find r (PTree.empty symbolic_value)) s); intros. 
    rewrite H3 in H1. 
    assert (lsteps ge (Istore m a0 l0 r:: nil) s (mkst s.(stack) s.(c) s.(sp) s.(rs) x)).
      destruct s. simpl. simpl in H1. simpl in H2. 
      unfold find in H3. rewrite PTree.gempty in H3. simpl in H3. 
      inversion H3; subst. 
      eapply exec_Istore; eauto.
      eapply exec_start; eauto.    
  generalize (IHl (mkst (stack s) (c s) (sp s) (rs s) x)); intro.
  generalize (three_aux _ _ _ _ (mkst s.(stack) s.(c) s.(sp) s.(rs) x) SAT H4); intro.
  generalize (IHl _ H6); intro. 
  destruct H7. exists x0. inversion H4; subst; try congruence.  eapply exec_Istore; eauto.
  simpl.
        unfold find in H3. rewrite PTree.gempty in H3. simpl in H3. 
      inversion H3; subst. 
      trivial.  

  rewrite H3 in H1. congruence. 
  rewrite H2 in H1. congruence.
  rewrite H0 in H1. congruence.   
Qed. 

Axiom regmap_exten : 
  forall (rs rs' : Regmap.t val), 
  (forall r, rs # r = rs' # r) -> 
  rs = rs'. 

Lemma sem_functional :
  forall ge s a b t, sem ge t s a -> sem ge t s b -> a = b. 
Proof. 
  intros. 
  inversion H; subst. inversion H0; subst.
  inversion H1; subst. 
  rewrite H6 in H3. inversion H3; subst. 
  cut (rs' = rs'0). intro. subst; trivial. 
  clear H6 H3 H0 H1 H.
  assert (forall x, rs' # x = rs'0 # x).
  intro. 
  case_eq (PTree.get x (file t)); intros.
  generalize (PTree.elements_correct _ _ H); intro. 
  generalize (H4 _ _ H0); intro. 
  generalize (H7 _ _ H0); intro. 
  congruence. 
  assert (~ In x (map (fst (A:=positive) (B:=symbolic_value)) (PTree.elements (file t)))). 
  intuition. 
  generalize (elements_2 _ _ H0); intro.
  destruct H1. 
  generalize (PTree.elements_complete _ _ _ H1); intro.
  congruence. 
  generalize (H5 _ H0); intro. 
  generalize (H8 _ H0); intro. 
  congruence. 
  eapply regmap_exten; eauto. 
Qed. 

Theorem complete : 
  forall ge l s s',
  sem ge (symbolic_evaluation l) s s' /\ satisfy_sym_state ge s (symbolic_evaluation l) -> lsteps ge l s s'. 
Proof. 
  intros. 
  destruct H.
  generalize (three _ _ _ H0); intros. 
  destruct H1.

  assert (sem ge (symbolic_evaluation l) s x). 
    unfold symbolic_evaluation. eapply one; eauto. 
    unfold initial_state. destruct s.   simpl. eapply Sem_intro; eauto.  intros. simpl in H2.  intuition.
    generalize (sem_functional _ _ _ _ _ H H2); intro.
    subst; trivial. 
Qed. 
  
Theorem fonda: 
  forall ge l s s',
  lsteps ge l s s' <-> sem ge (symbolic_evaluation l) s s' /\ satisfy_sym_state ge s (symbolic_evaluation l). 
Proof. 
  intros. 
  split; intros. 
  eapply correct; eauto.
  eapply complete; eauto. 
Qed.

Lemma eq_to_sem_aux: 
  forall ge o l1 l2 s s',
  weq o (symbolic_evaluation l1) (symbolic_evaluation l2) ->lsteps ge l1 s s' -> exists t', lsteps ge l2 s t' /\ state_eq o s' t'. 
Proof. 
  intros until 1. intros. 
  generalize (correct _ _ _ _ H0); intro.
  destruct H1.
  inversion H; subst. 
  
  assert ( satisfy_sym_state ge s (symbolic_evaluation l2)). 
    unfold satisfy_sym_state. intros. 
    unfold satisfy_sym_state in H2. apply H2. rewrite H5. trivial. 

  generalize (three _ _ _ H6); intro.
  destruct H7. exists x.

  split; trivial. 

  

  generalize (correct _ _ _ _ H7); intro. 
  destruct H8. 

  clear H H7 H2 H6 H9 H5. 

  inversion H1; subst. clear H1.  
  inversion H8; subst. clear H8. 
  
  inversion H; subst. 

  eapply Steq_intro; intros.
  
  generalize (H3 x H1); intro. simpl.
  clear H5 H2.
  
  case_eq ( (file (symbolic_evaluation l1)) ! x); intros. 
  generalize (PTree.elements_correct _ _ H2); intro.
  rewrite H8 in H2. 
  generalize (PTree.elements_correct _ _ H2); intro.
  generalize (H6 _ _ H5); intro. 
  generalize (H9 _ _ H11); intro. 
  congruence. 

  assert (~
     In x
       (map (fst (A:=positive) (B:=symbolic_value))
          (PTree.elements (file (symbolic_evaluation l1))))). 
          intuition. 
          generalize (elements_2 _ _ H5); intro. 
          destruct H11. 
          generalize (PTree.elements_complete _ _ _ H11); intro.
          congruence.
   assert (~
     In x
       (map (fst (A:=positive) (B:=symbolic_value))
          (PTree.elements (file (symbolic_evaluation l2))))).
          intuition. 
          generalize (elements_2 _ _ H11); intro. 
          destruct H12. 
          generalize (PTree.elements_complete _ _ _ H12); intro.
          congruence.
  
  generalize (H7 _ H5); intro.
  generalize (H10 _ H11); intro. 
  congruence. 
  
  simpl. clear H10 H7 H9. 
  rewrite H4 in H5. rewrite H5 in H2. congruence.

   simpl. clear H10 H7 H9. 
  rewrite H4 in H5. rewrite H5 in H2. congruence.

 simpl. clear H10 H7 H9. 
  rewrite H4 in H5. rewrite H5 in H2. congruence.

Qed.    

Lemma closure:
  forall ge s t o,
  (forall x, In x o -> (rs s) # x = (rs t) # x) ->
  mm s = mm t ->
  sp s = sp t ->  
(forall s0, 
      (forall r : reg, In_value r s0 -> In r o) ->
      of_value ge s0 t = of_value ge s0 s) /\
(forall s0, 
      (forall r : reg, In_mem r s0 -> In r o)  ->
      of_mem ge s0 t = of_mem ge s0 s) /\
(forall s0, 
      (forall r : reg, In_value_list r s0 -> In r o)  ->      
      of_value_list ge s0 t = of_value_list ge s0 s).
Proof. 
  intros ge s t o E1 E2 E3. 
  eapply (symbolic_combined_ind 
  (fun s0 =>
      (forall r : reg, In_value r s0 -> In r o) ->
      of_value ge s0 t = of_value ge s0 s) 
(fun s0 =>
      (forall r : reg, In_mem r s0 -> In r o)  ->
      of_mem ge s0 t = of_mem ge s0 s) 
(fun s0 =>  
        (forall r : reg, In_value_list r s0 -> In r o)  ->      
      of_value_list ge s0 t = of_value_list ge s0 s)
); eauto; intros; simpl.

  generalize (H r); intro.
  rewrite (E1 r); trivial.
  eapply H0; eauto. eapply In_reg; eauto.   

  rewrite H. rewrite E3. destruct (of_value_list ge s0 s); trivial.
  intros. eapply H0; eauto. inversion H1; subst.
  eapply In_op; eauto. eapply In_op; eauto.  

  rewrite E3. rewrite H. destruct (of_value_list ge s0 s); trivial. 
  rewrite H0. destruct (of_mem ge s1 s); trivial. 
  intros. eapply H1; eauto. eapply In_load_2; eauto.
  intros. eapply H1; eauto. eapply In_load_1; eauto.
  congruence. 

  rewrite E3. rewrite H. destruct (of_value_list ge s0 s); trivial. 
  destruct (eval_addressing ge (sp t) a l). 
  rewrite H0. destruct (of_value ge s1 s); trivial. 
  rewrite H1. destruct (of_mem ge s2 s); trivial. 
  intros. eapply H2; eauto. eapply In_store_3; eauto. 
  intros. eapply H2; eauto. eapply In_store_1; eauto.
  trivial. 
  intros. eapply H2; eauto. eapply In_store_2; eauto.   
  
  rewrite H. destruct (of_value ge s0 s); trivial. 
  rewrite H0. destruct (of_value_list ge s1 s); trivial. 
  intros. eapply H1. eapply In_cons_2; eauto.
  intros. eapply H1. eapply In_cons_1; eauto.
Qed.   

Lemma eq_to_sem_aux2:
  forall ge o s t l,
  state_eq o s t -> satisfy_sym_state ge s l -> domain l o ->satisfy_sym_state ge t l.
Proof. 
  intros. 
  inversion H; subst.
  inversion H1; subst.
  unfold satisfy_sym_state in H0. 
  unfold satisfy_sym_state. 
  intros. 
  generalize (H0 e H9); intro. 
  generalize (H8 e H9); intro.
  unfold satisfy_value in H10. 
  unfold satisfy_value.

  generalize (closure ge _ _ _ H2 H3 H5); intro.
  destruct H12 as [A [B C]]. 
  destruct e. 
  destruct H10. exists x. rewrite <- H10.
  rewrite A; trivial. intros. eapply H11; eauto. 
  eapply In_V; eauto. 
  destruct H10. exists x. rewrite <- H10.
  rewrite B; trivial. intros. eapply H11; eauto. 
  eapply In_M; eauto.
Qed.    

Lemma eq_to_sem_aux3:
  forall ge o l S T S' T',
  state_eq o S T ->
  sem ge l S S' ->
  sem ge l T T' ->
  domain l o ->
  state_eq o S' T'.
Proof. 
  intros.
  inversion H2; subst. 
  inversion H; subst. 
  inversion H0; subst. 
  inversion H1; subst. 

  generalize (closure ge _ _ _ H6 H7 H9); intros. 
  destruct H10 as [A [B C]]. 
 
  eapply Steq_intro; eauto.

  intros. 
  case_eq ((file l) ! x); intros.
  generalize (H3 _ H10 _ H11); intro. 
  generalize (A _ H18); intro.
  simpl. 
  rewrite (H13 x) in H19. rewrite (H16 x) in H19. congruence. 
  generalize (PTree.elements_correct _ _ H11); intro. trivial.  
  generalize (PTree.elements_correct _ _ H11); intro. trivial.    
  simpl. 

  rewrite <- H17.
  rewrite <- H14. 
  simpl in H6. eapply H6; eauto.
  intuition. 
  generalize (elements_2 _ _ H18); intro.
  destruct H19. 
  generalize (PTree.elements_complete _ _ _ H19); intro.
  congruence. 
  intuition. 
  generalize (elements_2 _ _ H18); intro.
  destruct H19. 
  generalize (PTree.elements_complete _ _ _ H19); intro.
  congruence. 

 
  simpl. simpl in H7. subst. 
  generalize (B _ H4); intro. 
  rewrite <- H7 in H12. congruence. 
Qed.  
  
Lemma eq_to_sem: 
  forall ge o l1 l2 s t s' t1 t2,
  t1 = symbolic_evaluation l1 -> t2 = symbolic_evaluation l2 ->
  weq o t1 t2 -> domain t2 o -> 
  state_eq o s t -> lsteps ge l1 s s' -> exists t', lsteps ge l2 t t' /\ state_eq o s' t'.
Proof. 
  intros. subst. 
  generalize (eq_to_sem_aux _ _ _ _ _ _ H1 H4); intro.
  destruct H as [t' [A B]]. 
  inversion H1; subst. 
  generalize (correct _ _ _ _ A); intro. destruct H6.
  inversion H3; subst.
  generalize (eq_to_sem_aux2 _ _ _ _ _ H3 H7 H2); intro.
  generalize (three _ _ _ H12); intro. 
  destruct H13. exists x. split; trivial.

  generalize (correct _ _ _ _ H13); intro. destruct H14. 

  generalize (eq_to_sem_aux3 ); intro.
  generalize (eq_to_sem_aux3 _ _ _ _ _ _ _ H3 H6 H14 H2); intro. 
  
  eapply steq_trans; eauto.
Qed.
