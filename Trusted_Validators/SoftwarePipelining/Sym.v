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
Require Import SE. 

Inductive symbolic_value : Set :=
  | Sreg : reg -> symbolic_value
  | Sop : operation -> symbolic_value_list -> symbolic_value
  | Sload : memory_chunk -> addressing -> symbolic_value_list -> symbolic_mem -> symbolic_value
with symbolic_mem : Set :=
  | Smem : symbolic_mem
  | Sstore : memory_chunk -> addressing -> symbolic_value_list -> symbolic_value -> symbolic_mem -> symbolic_mem
with symbolic_value_list : Set :=
  | Snil : symbolic_value_list
  | Scons : symbolic_value -> symbolic_value_list -> symbolic_value_list.  
 
Scheme symbolic_value_ind2 := Induction for symbolic_value Sort Prop
  with symbolic_mem_ind2 := Induction for symbolic_mem Sort Prop 
  with symbolic_value_list_ind2 := Induction for symbolic_value_list Sort Prop.

Combined Scheme symbolic_combined_ind from symbolic_value_ind2, symbolic_mem_ind2, symbolic_value_list_ind2. 

Inductive tv : Set := V : symbolic_value -> tv | M : symbolic_mem -> tv. 
Parameter eq_dec_sv : forall x y : symbolic_value, { eq x y } + { ~ eq x y }.
Parameter eq_dec_sm : forall x y : symbolic_mem, { eq x y } + { ~ eq x y }.

Definition eq_dec_s : forall x y : tv, { eq x y } + { ~ eq x y }.
Proof.
  generalize eq_dec_sv. 
  generalize eq_dec_sm. 
  decide equality.
Qed.   

Definition sym_file : Set := PTree.t symbolic_value. 

Module Constraint <: DecidableType. 
Definition t := tv. 
Definition eq (s s' : t) := s = s'.
Lemma  eq_refl : forall x : t, eq x x. unfold eq; auto. Qed.   
Lemma eq_sym : forall x y : t, eq x y -> eq y x. unfold eq; auto. Qed. 
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq; congruence. Qed. 
Definition  eq_dec := eq_dec_s. (* Egalite de caml *)
End Constraint. 

Module Constraints := Make Constraint.
Module P := Properties Constraints. 

Record sym_state : Set := mkstate {
  file : sym_file; 
  mem : symbolic_mem; 
  cons : Constraints.t
}. 

Definition initial_state := mkstate (@PTree.empty symbolic_value) Smem Constraints.empty.

Definition find (r : reg) (m : sym_file) : symbolic_value :=
  match PTree.get r m with
  | None => Sreg r
  | Some v => v
  end. 

(* LIB Extension *) 

Lemma elements_fold_0:
  forall r l a,
   ~ In r (map (fst (A:=positive) (B:=symbolic_value)) (a :: l)) -> ~ In r (map (fst (A:=positive) (B:=symbolic_value)) l).
Proof. 
  induction l; intros. 
  simpl. auto. 
  simpl. simpl in H. intuition. 
Qed. 

Lemma elements_fold_1:
  forall r f l w, 
  ~ In r (map (@fst positive _) l) ->
  (fold_left
   (fun (a : PTree.t symbolic_value) (p : positive * symbolic_value) =>
    PTree.set (fst p) (f (snd p)) a) l w) ! r = w ! r.
Proof. 
  induction l; intros. 
  simpl. trivial. 
  simpl. generalize (IHl (PTree.set (fst a) (f (snd a)) w)); intro.
  generalize (elements_fold_0 _ _ _ H); intro.
  generalize (H0 H1); intro. 
  rewrite H2. 
  destruct a. simpl; simpl in *|-. 
  generalize (peq p r); intro. 
  destruct H3. 
  intuition. rewrite PTree.gso. trivial. congruence.   
Qed. 

Lemma norepet_0:
  forall r l, 
  list_norepet (r :: map (fst (A:=PTree.elt) (B:=symbolic_value)) l) -> ~ In r (map (fst (A:=positive) (B:=symbolic_value)) l). 
Proof. 
  induction l; intros. 
  simpl. auto.
  simpl. simpl in H. 
  generalize (peq (fst a) r); intro. destruct H0. 
  subst. inversion H; subst. simpl in H2. intuition.  
  intuition. eapply IHl; eauto.  
  assert (list_norepet
      ((r :: nil) ++ (fst a :: nil) ++  map (fst (A:=PTree.elt) (B:=symbolic_value)) l)). 
  simpl. trivial.
  generalize (list_norepet_app (r :: nil) ((fst a :: nil) ++ map (fst (A:=PTree.elt) (B:=symbolic_value)) l)); intro. 
  intuition. 
  generalize (list_norepet_app (fst a :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l)); intro. 
  intuition.
  generalize (list_disjoint_cons_right H6); intro.
  generalize (list_norepet_append H3 H4 H8); intro. simpl in H11. 
  trivial. 
Qed.   

Lemma elements_fold: 
  forall f l r s w,
  In (r, s) l ->
  list_norepet (map (fst (A:=PTree.elt) (B:=symbolic_value)) l) ->
  (fold_left
     (fun (a : PTree.t symbolic_value) (p : positive * symbolic_value) =>
      PTree.set (fst p) (f (snd p)) a) l w) ! r = Some (f s).
Proof. 
  induction l; intros. 
  inversion H. 
  inversion H. subst. 
  simpl. rewrite elements_fold_1. rewrite PTree.gss. trivial. 
  simpl in H0. 
  assert (list_norepet ((r :: nil) ++ map (fst (A:=PTree.elt) (B:=symbolic_value)) l)). trivial. 
  generalize (list_norepet_app (r :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l)); intro. intuition.
  assert (In r (r :: nil)). simpl. left. trivial.
  generalize (@list_disjoint_notin _ (r :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l) r H7 H5); intro.
  intuition. 
  simpl. inversion H0.  
  generalize (IHl r s (PTree.set (fst a) (f (snd a)) w) H1 H5); intro.
  trivial. 
Qed.   

Lemma elements_2: 
  forall r l,
      In r (map (fst (A:=positive) (B:=symbolic_value)) l) ->
      exists s, In (r,s) l. 
Proof. 
  induction l; intros. 
  simpl in H. inversion H. 
  simpl in H. destruct H. 
  subst. destruct a. simpl. exists s.  left; trivial. 
  simpl. generalize (IHl H); intro. destruct H0. exists x. right; trivial. 
Qed. 

(* Fin *)

Fixpoint get_args (args : list reg) (m : sym_file) {struct args} : symbolic_value_list :=
  match args with
  | nil => Snil
  | arg :: args => Scons (find arg m) (get_args args m)
  end. 

Fixpoint symbolic_evaluation_rec (l : list instruction) (s : sym_state) {struct l} : sym_state :=
  match l with
  | nil => s
  | Imove src dst :: l => let v := find src s.(file) in
                                              symbolic_evaluation_rec l (mkstate (PTree.set dst v s.(file)) s.(mem) s.(cons))
  | Iop op args dst :: l => let v := Sop op (get_args args s.(file)) in 
                                              symbolic_evaluation_rec l (mkstate (PTree.set dst v s.(file)) s.(mem) (Constraints.add (V v) s.(cons)))
  | Iload mc addr args dst :: l => let v := Sload mc addr (get_args args s.(file)) s.(mem) in
                                              symbolic_evaluation_rec l (mkstate (PTree.set dst v s.(file)) s.(mem) (Constraints.add (V v) s.(cons)))
  | Istore mc addr args src :: l => let v := Sstore mc addr (get_args args s.(file)) (find src s.(file)) s.(mem) in
                                              symbolic_evaluation_rec l (mkstate s.(file) v (Constraints.add (M v) s.(cons)))
  end. 

Definition symbolic_evaluation (l : list instruction) : sym_state := symbolic_evaluation_rec l initial_state. 
 
Inductive symbolic_equivalence : sym_state -> sym_state -> Prop :=
  | Seq : forall s s',  (forall x, s.(file) ! x = s'.(file) ! x) -> s.(mem) = s'.(mem) -> Constraints.Equal s.(cons) s'.(cons) -> symbolic_equivalence s s'. 

Notation "a ~ b" := (symbolic_equivalence a b) (at level 1). 

Lemma seq_reflexivity: forall s, s ~ s. 
Proof. 
  intros. 
  apply Seq; auto.
  apply P.equal_refl.  
Qed.  

Lemma seq_symmetry: forall s s', s ~ s' -> s' ~ s.
Proof. 
  intros.
  inversion H; subst. 
  eapply Seq; eauto.
  rewrite H2. apply P.equal_refl. 
Qed. 
  
Lemma seq_transitivity: forall s1 s2 s3, s1 ~ s2 -> s2 ~ s3 -> s1 ~ s3.
Proof. 
  intros. 
  inversion H; subst. 
  inversion H0; subst. 
  eapply Seq; eauto. 
  intros. generalize (H1 x); intro. generalize (H4 x); intro. congruence. 
  congruence. 
  unfold Constraints.Equal in *|-. 
  unfold Constraints.Equal.
  intro. generalize (H3 a); intro. generalize (H6 a); intro.   
  intuition.
Qed. 

Add Relation sym_state symbolic_equivalence
    reflexivity proved by (@seq_reflexivity)
    symmetry proved by (@seq_symmetry)
    transitivity proved by (@seq_transitivity)
as sym_eq. 

Lemma step_eval_sym : 
  forall (a : instruction) (l : list instruction) (t : sym_state),  
  (symbolic_evaluation_rec (a :: l) t) ~
  (symbolic_evaluation_rec l (symbolic_evaluation_rec (a :: nil) t)).
Proof. 
  intros. 
  destruct a; intros.
  simpl. eapply seq_reflexivity; eauto. 
  simpl. eapply seq_reflexivity; eauto.   
  simpl. eapply seq_reflexivity; eauto. 
  simpl. eapply seq_reflexivity; eauto. 
Qed. 

Lemma get_args_ok:
  forall x1 x2 l,
  (forall x : positive, (file x1) ! x = (file x2) ! x) -> 
  get_args l (file x1) = get_args l (file x2).
Proof. 
  induction l; intros. 
  simpl. trivial. 
  simpl. rewrite IHl; trivial.
  generalize (H a); intro.  unfold find. unfold find in H0. rewrite H0.
  trivial .
Qed. 

Lemma symbolic_evaluation_compatible_one:
  forall a x1 x2, x1 ~ x2 -> (symbolic_evaluation_rec (a :: nil) x1) ~ (symbolic_evaluation_rec (a :: nil) x2).
Proof. 
  intros. 
  inversion H; subst.
  eapply Seq; eauto.

  intro. generalize (H0 x); intro. 

  destruct a; simpl; trivial; unfold find.

  generalize (peq x r0); intro. destruct H4.  
    subst. rewrite PTree.gss. rewrite PTree.gss. unfold find in H0. rewrite H0. trivial. 
    rewrite PTree.gso. rewrite PTree.gso. trivial. trivial. trivial.

  generalize (peq x r); intro. destruct H4.  
    subst. rewrite PTree.gss. rewrite PTree.gss. 
    generalize (get_args_ok x1 x2 l H0); intro. rewrite H4. trivial.   
    rewrite PTree.gso. rewrite PTree.gso. trivial. trivial. trivial. 

  generalize (peq x r); intro. destruct H4.  
    subst. rewrite PTree.gss. rewrite PTree.gss. unfold find. 
    generalize (get_args_ok x1 x2 l H0); intro. rewrite H4. rewrite H1.  trivial.   
    rewrite PTree.gso. rewrite PTree.gso. trivial. trivial. trivial. 

  destruct a; simpl; trivial; unfold find.
  unfold find. unfold find in H0.  rewrite H0. 
  rewrite H1. generalize (get_args_ok x1 x2 l H0); intro. rewrite H3.  trivial.

  destruct a; simpl; trivial.
  generalize (get_args_ok x1 x2 l H0); intro. rewrite H3. 
  rewrite H2.  unfold Constraints.Equal. intuition.
  generalize (get_args_ok x1 x2 l H0); intro. rewrite H3. 
  rewrite H2. rewrite H1. unfold Constraints.Equal. intuition. 
  rewrite H2. rewrite H1.
  unfold find.  generalize (get_args_ok x1 x2 l H0); intro. rewrite H3.
  generalize (H0 r); intro. unfold find in H4. rewrite H4.  
  eapply P.equal_refl; eauto. 
Qed.  

Lemma symbolic_evaluation_compatible:
  forall (l : list instruction) (x1 x2 : sym_state),
  x1 ~ x2 -> (symbolic_evaluation_rec l x1) ~ (symbolic_evaluation_rec l x2). 
Proof. 
  induction l; intros. 
  simpl. trivial. 
  
  rewrite step_eval_sym.
  generalize (symbolic_evaluation_compatible_one a _ _ H); intro.
  generalize (IHl _ _ H0); intro. 
  rewrite H1.
  rewrite <- step_eval_sym. 
  apply seq_reflexivity. 
Qed.  

Add Morphism symbolic_evaluation_rec 
   with signature symbolic_equivalence ==> symbolic_equivalence as sym_eval_mor.
Proof. 
  intros.
  eapply symbolic_evaluation_compatible; eauto. 
Qed. 

Lemma star_eval_sym : forall (l1 l2 : list instruction) (t : sym_state), 
   (symbolic_evaluation_rec (l1 ++ l2) t) ~ (symbolic_evaluation_rec l2  (symbolic_evaluation_rec l1 t)).  
Proof. 
  induction l1; intros.

  simpl. eapply seq_reflexivity; eauto.  
  rewrite <- app_comm_cons.
  rewrite step_eval_sym. 
  generalize (IHl1 l2 (symbolic_evaluation_rec (a :: nil) t)); intro. 
  rewrite H.
  assert ((symbolic_evaluation_rec (a :: l1) t) ~ (symbolic_evaluation_rec l1
      (symbolic_evaluation_rec (a :: nil) t))). 
      eapply step_eval_sym; eauto.
  rewrite H0.
  eapply seq_reflexivity. 
Qed. 

Lemma associativity : forall (l1 l2 l3 : list instruction) x, 
  (symbolic_evaluation_rec l3 (symbolic_evaluation_rec (l1 ++ l2) x)) 
  ~ (symbolic_evaluation_rec (l2 ++ l3) (symbolic_evaluation_rec l1 x)).
Proof. 
  intros.
  repeat (rewrite star_eval_sym).
  eapply seq_reflexivity. 
Qed. 

Fixpoint substitute_value (v : symbolic_value) (f : sym_file) (m : symbolic_mem) {struct v} : symbolic_value := 
  match v with
  | Sreg r => find r f
  | Sop op args  => Sop op (substitute_value_list args f m)
  | Sload mc addr args mem => Sload mc addr (substitute_value_list args f m) (substitute_memory mem f m)
  end
with substitute_memory (mem : symbolic_mem)  (f : sym_file) (m : symbolic_mem) {struct mem} : symbolic_mem := 
  match mem with
  | Smem => m
  | Sstore mc addr args arg mem => Sstore mc addr (substitute_value_list args f m) (substitute_value arg f m) (substitute_memory mem f m)
  end
with substitute_value_list (l : symbolic_value_list) (f : sym_file) (m : symbolic_mem) {struct l} : symbolic_value_list := 
  match l with
  | Snil => Snil
  | Scons arg args => Scons (substitute_value arg f m) (substitute_value_list args f m)
  end.
 
Lemma subst_empty : (forall v, substitute_value v (PTree.empty symbolic_value) Smem = v) 
                                                  /\ (forall v, substitute_memory v (PTree.empty symbolic_value) Smem = v)
                                                  /\ (forall v, substitute_value_list v (PTree.empty symbolic_value) Smem = v).
Proof.
  eapply (symbolic_combined_ind 
       (fun v => substitute_value v (PTree.empty symbolic_value) Smem = v)
       (fun v => substitute_memory v (PTree.empty symbolic_value) Smem = v)
       (fun v => substitute_value_list v (PTree.empty symbolic_value) Smem = v)
 ); eauto; intros; simpl. 

  unfold find. rewrite PTree.gempty. trivial.  
  rewrite H. trivial. 
  rewrite H. rewrite H0. trivial. 
  rewrite H. rewrite H0. rewrite H1.  trivial. 
  rewrite H. rewrite H0. trivial. 
Qed. 
  
Definition substitute_value_ext (v : tv) f m  := 
  match v with
  | V v => V (substitute_value v f m)
  | M v => M (substitute_memory v f m)
  end. 

Definition delta (t1 t2 : sym_state) : sym_state :=
  let new_file := PTree.fold (fun tbuild r v => 
                                         PTree.set r (substitute_value v t1.(file) t1.(mem)) tbuild
                                       ) t2.(file) t1.(file) in
  let new_mem := substitute_memory t2.(mem) t1.(file) t1.(mem) in
  let new_constraints := Constraints.union t1.(cons) 
              (Constraints.fold (fun c csbuild => Constraints.add (substitute_value_ext c t1.(file) t1.(mem)) csbuild) t2.(cons) Constraints.empty) in                                    
   mkstate new_file new_mem new_constraints. 

Notation "a ^^ b" := (delta a b) (at level 0).

Lemma delta_compatible_right :
  forall x y z, x ~ y -> z ^^ x ~  z ^^ y.
Proof. 
  intros. 
  inversion H; subst. 
  eapply Seq; eauto; unfold delta; simpl. 
  intro. 
  repeat (rewrite PTree.fold_spec). 
  generalize (H0 x0); intro. 
  generalize (PTree.elements_keys_norepet (file x)); intro.
  generalize (PTree.elements_keys_norepet (file y)); intro.

  case_eq ((file x) ! x0); case_eq ((file y) ! x0); intros.
  rewrite H6 in H3. rewrite H7 in H3. subst. 
  generalize (PTree.elements_correct _ _ H6); intro.
  generalize (PTree.elements_correct _ _ H7); intro.
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H8 H5).
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H9 H4).
  congruence. 
  rewrite H6 in H3. rewrite H7 in H3. subst. 
  generalize (PTree.elements_correct _ _ H7); intro.
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H8 H4).
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file y)))).
     generalize (PTree.elements_complete (file y) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file y)) H10); intro. destruct H11. 
     generalize (H9 x1 H11); intro. congruence.  
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H9).
  congruence. 
  rewrite H6 in H3. rewrite H7 in H3. subst. 
  generalize (PTree.elements_correct _ _ H6); intro.
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H8 H5).
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file x)))).
     generalize (PTree.elements_complete (file x) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file x)) H10); intro. destruct H11. 
     generalize (H9 x1 H11); intro. congruence.  
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H9).
  congruence. 
  rewrite H6 in H3. rewrite H7 in H3. subst. 
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file x)))).
     generalize (PTree.elements_complete (file x) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file x)) H9); intro. destruct H10. 
     generalize (H8 x1 H10); intro. congruence.
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file y)))).
     generalize (PTree.elements_complete (file y) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file y)) H10); intro. destruct H11. 
     generalize (H9 x1 H11); intro. congruence.  
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H8).
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H9).
  congruence. 
 
  rewrite H1. trivial.

  clear H0 H1 H. eapply P.union_equal_2; eauto. 
  generalize (P.fold_0 (cons x) Constraints.empty (fun e a => Constraints.add (substitute_value_ext e (file z) (mem z)) a)); intro.
  destruct H as [l [A [B C]]]. 
  generalize (P.fold_0 (cons y) Constraints.empty (fun e a => Constraints.add (substitute_value_ext e (file z) (mem z)) a)); intro.
  destruct H as [l' [A' [B' C']]].
  assert (forall a, InA Constraints.E.eq a l <-> InA Constraints.E.eq a l').
    intro. 
    generalize (B a); intro. 
    generalize (B' a); intro. rewrite <- H2 in H0. tauto.   
  unfold Constraints.Equal. intro.
  rewrite C. rewrite C'.
  assert (Setoid_Theory Constraints.t Constraints.Equal). constructor; eauto with set.  
   assert (compat_op Constraint.eq Constraints.Equal
       (fun (e : Constraints.elt) (a0 : Constraints.t) =>
        Constraints.add (substitute_value_ext e (file z) (mem z)) a0)). 
        unfold compat_op.  intros.  rewrite H1. rewrite H3. eapply P.equal_refl; eauto. 
  assert ( transpose Constraints.Equal
       (fun (e : Constraints.elt) (a0 : Constraints.t) =>
        Constraints.add (substitute_value_ext e (file z) (mem z)) a0)). 
        unfold transpose. intros. rewrite P.add_add. eapply P.equal_refl; eauto.    
  
  generalize (@fold_right_equal Constraint.t Constraint.eq Constraint.eq_refl Constraint.eq_sym Constraint.eq_trans Constraint.eq_dec
                        Constraints.t Constraints.Equal H0 (fun (e : Constraints.elt) (a0 : Constraints.t) =>
      Constraints.add (substitute_value_ext e (file z) (mem z)) a0) H1 H3 Constraints.empty l l' A A' H); intro.
   unfold Constraints.Equal in H4. generalize (H4 a); intro. rewrite H5. intuition.  
Qed.   

Add Morphism delta
   with signature symbolic_equivalence ==> symbolic_equivalence as delta_mor_right.
Proof. 
  intros.
  eapply delta_compatible_right; eauto. 
Qed. 

Lemma subst_on_the_left:
  forall x y, (forall r : positive, (file x) ! r = (file y) ! r) -> mem x = mem y ->
  (forall v, substitute_value v (file x) (mem x) = substitute_value v (file y) (mem y)) /\
  (forall v, substitute_memory v (file x) (mem x) = substitute_memory v (file y) (mem y)) /\
  (forall v, substitute_value_list v (file x) (mem x) = substitute_value_list v (file y) (mem y)).
Proof.
  intros x y FILE MEM.  
    eapply (symbolic_combined_ind 
       (fun v => substitute_value v (file x) (mem x) = substitute_value v (file y) (mem y))
       (fun v => substitute_memory v (file x) (mem x) = substitute_memory v (file y) (mem y))
       (fun v => substitute_value_list v (file x) (mem x) = substitute_value_list v (file y) (mem y))
 ); eauto; intros; simpl.
  unfold find. rewrite FILE. trivial. 
  rewrite H. trivial. 
  rewrite H; rewrite H0. trivial. 
  rewrite H; rewrite H0; rewrite H1. trivial. 
  rewrite H; rewrite H0. trivial. 
Qed. 

Lemma delta_compatible_left_aux_ptree:
   forall x y x0 l w z,
   (forall r, w ! r = z ! r) ->
  (forall v : symbolic_value, substitute_value v (file x) (mem x) = substitute_value v (file y) (mem y)) -> 
  (fold_left (fun (a : PTree.t symbolic_value) (p : positive * symbolic_value) =>
    PTree.set (fst p) (substitute_value (snd p) (file x) (mem x)) a) l w) ! x0 
                 =
   (fold_left (fun (a : PTree.t symbolic_value) (p : positive * symbolic_value) =>
    PTree.set (fst p) (substitute_value (snd p) (file y) (mem y)) a) l z) ! x0.
Proof. 
  induction l; intros.
  simpl. rewrite H. trivial. 
  simpl. 
  rewrite (IHl (PTree.set (fst a) (substitute_value (snd a) (file x) (mem x)) w) (PTree.set (fst a) (substitute_value (snd a) (file y) (mem y)) z)). 
 trivial. intro. rewrite H0. 
   
  generalize (peq (fst a) r); intros. 
    destruct H1. 
    subst. rewrite PTree.gss. rewrite PTree.gss. trivial. 
    rewrite PTree.gso; auto. rewrite PTree.gso; auto.  

  intro. rewrite H0. trivial. 
Qed.

Lemma delta_compatible_left_aux_constraints:
  forall x y l W,
(forall v : symbolic_value, substitute_value v (file x) (mem x) = substitute_value v (file y) (mem y)) ->
(forall v : symbolic_mem, substitute_memory v (file x) (mem x) = substitute_memory v (file y) (mem y)) ->
Constraints.Equal
  (fold_left
     (fun (a : Constraints.t) (e : Constraints.elt) =>
      Constraints.add
        match e with
        | V v => V (substitute_value v (file x) (mem x))
        | M v => M (substitute_memory v (file x) (mem x))
        end a) l W)
  (fold_left
     (fun (a : Constraints.t) (e : Constraints.elt) =>
      Constraints.add
        match e with
        | V v => V (substitute_value v (file y) (mem y))
        | M v => M (substitute_memory v (file y) (mem y))
        end a) l W).
Proof. 
  induction l; intros. 
  simpl. apply P.equal_refl.
  simpl.  rewrite IHl. 
  intro. rewrite H. trivial. 
  intro. rewrite H0; trivial. 
  destruct a. rewrite H. apply P.equal_refl.
  rewrite H0. apply P.equal_refl.
Qed.  
  
Lemma delta_compatible_left :
  forall x y z, x ~ y -> x ^^ z ~  y ^^ z.
Proof. 
  intros. 
  inversion H; subst.
  generalize (subst_on_the_left _ _ H0 H1); intro. destruct H3 as [A [B C]].  
  eapply Seq; eauto. 
  
  intro. simpl.
  rewrite PTree.fold_spec. rewrite PTree.fold_spec. 
  induction (PTree.elements (file z)). simpl.  rewrite H0. trivial. 
  simpl. eapply delta_compatible_left_aux_ptree; eauto.
  intro. 
    generalize (peq (fst a) r); intros. 
    destruct H3. 
    subst. rewrite PTree.gss. rewrite PTree.gss. rewrite A.  trivial. 
    rewrite PTree.gso; auto. rewrite PTree.gso; auto.  

  
  simpl. rewrite B. trivial.   

  simpl. rewrite H2. eapply P.union_equal_2; eauto. 
  unfold substitute_value_ext. 
  repeat rewrite Constraints.fold_1.   
  eapply delta_compatible_left_aux_constraints; eauto. 
Qed. 

Lemma neutral_right: forall u, u ^^ initial_state ~ u.
Proof. 
  intros.
  eapply Seq; eauto. 
  simpl. 
  rewrite Constraints.fold_1. simpl. 
  unfold Constraints.Equal. intro. 
  intuition. 
  generalize (Constraints.union_1 H); intro.
  destruct H0. 
  trivial. inversion H0. 
  eapply Constraints.union_2; eauto.
Qed.  

Axiom fold_id: forall u,
Constraints.Equal (Constraints.fold (fun (e : Constraints.elt) (a : Constraints.t) => Constraints.add e a) u Constraints.empty) u.
(*
Proof. 
  intro. 
  eapply (@P.set_induction (fun u => Constraints.Equal (Constraints.fold (fun (e : Constraints.elt) (a : Constraints.t) => Constraints.add e a) u Constraints.empty) u)); intros. 

  generalize (P.empty_is_empty_1 H); intro.     
  unfold Constraints.Equal. intro. intuition.

  unfold Constraints.Empty in H. generalize (H a); intro.   
  rewrite Constraints.fold_1 in H1. BLOB

  rewrite H0 in H1. inversion H1.  

   assert (
    Constraints.Equal (Constraints.fold
     (fun (e : Constraints.elt) (a : Constraints.t) => Constraints.add e a)
     s' Constraints.empty) 
     (Constraints.add x (Constraints.fold
     (fun (e : Constraints.elt) (a : Constraints.t) => Constraints.add e a)
     s Constraints.empty))). BLOB
  rewrite H2. clear H2. 
  rewrite H.
  unfold P.Add in H1.
  unfold Constraints.Equal. intro. 
  generalize (H1 a); intro. 
  split; intro. destruct H2. 
  eapply H4; eauto. 
  rewrite P.add_union_singleton in H3.
  generalize (Constraints.union_1 H3); intro. 
  destruct H5. 
  left. eapply Constraints.singleton_1; eauto.
  right. trivial. 
  destruct H2. generalize (H2 H3); intro. 
  destruct H5. 
  eapply Constraints.add_1; eauto.  
  rewrite P.add_union_singleton. eapply Constraints.union_3; eauto.
Qed.   
*)  


Lemma exten_to_fold:
  forall f g e i, f = g -> Constraints.Equal (Constraints.fold f e i) (Constraints.fold g e i). 
Proof. 
  intros.  
  rewrite H. apply P.equal_refl. 
Qed.  

Lemma neutral_left: forall u, initial_state ^^ u ~ u. 
Proof.
  intro.
  eapply Seq; eauto. 
  unfold delta. simpl. 
  rewrite PTree.fold_spec. intro. 
  case_eq ((file u)! x); intros.   
    generalize (PTree.elements_correct _ _ H); intro. 
    generalize (PTree.elements_keys_norepet (file u)).
    intro. 
    generalize (elements_fold (fun v => substitute_value v (PTree.empty symbolic_value) Smem) _ _ _ (PTree.empty symbolic_value) H0 H1); intro.
    rewrite H2. generalize subst_empty; intro. destruct H3 as [A [B C]]. rewrite A. trivial.  
    assert (~ In x (map (@fst positive _)  (PTree.elements (file u)))). intuition. 
    generalize (elements_2 _ _ H0); intro. 
    destruct H1. generalize (PTree.elements_complete _ _ _ H1); intro. congruence. 
    generalize (elements_fold_1 x (fun v => substitute_value v (PTree.empty symbolic_value) Smem) _ (PTree.empty symbolic_value) H0); intro.
    rewrite H1. rewrite PTree.gempty. trivial.
 
  simpl. 
  generalize subst_empty; intro. destruct H. destruct H0. 
  eapply H0; eauto.
  simpl. (* rewrite Constraints.fold_1. *)
  rewrite P.empty_union_1. eapply P.empty_is_empty_2. eapply P.equal_refl.
  
  generalize subst_empty; intro.  destruct H as [H0 [H1 H2]]. 
  (* unfold Constraints.Equal. intro. *) 
  unfold substitute_value_ext. 
  assert ((fun (c : Constraints.elt) (csbuild : Constraints.t) =>
      Constraints.add
        match c with
        | V v => V (substitute_value v (PTree.empty symbolic_value) Smem)
        | M v => M (substitute_memory v (PTree.empty symbolic_value) Smem)
        end csbuild) = (fun (e : Constraints.elt) (a0 : Constraints.t) => Constraints.add e a0)).
        apply extensionality. intro. apply extensionality. intro. 
        destruct x. rewrite H0. trivial. 
        rewrite H1. trivial.
  rewrite (exten_to_fold _ _ (cons u) Constraints.empty H).  
  eapply fold_id; eauto. 
Qed.   

Lemma in_is_in:
  forall c s,
     Constraints.In c s -> In c (Constraints.elements s).
Proof. 
  intros. 
  generalize (Constraints.elements_1 H); intro. 
  unfold Constraints.E.eq in H0. unfold Constraint.eq in H0. 
  generalize (InA_alt (fun s s' : tv => s = s') c (Constraints.elements s)); intro. 
  intuition. destruct H1 as [y [A B]].
  subst; trivial. 
Qed. 

Lemma in_is_in':
  forall c s,
      In c (Constraints.elements s) -> Constraints.In c s.
Proof.
  intros. 
  eapply Constraints.elements_2; eauto. 
  unfold Constraints.E.eq. unfold Constraint.eq.   
  generalize (InA_alt (fun s s' : tv => s = s') c (Constraints.elements s)); intro.
  intuition. 
  assert (exists y : tv, c = y /\ In y (Constraints.elements s)). 
    exists c. intuition. 
  generalize (H2 H0); intro. 
  subst; trivial. 
Qed.   

Lemma delta_get :
  forall x u v,
  find x (file (u ^^ v)) = substitute_value (find x (file v)) (file u) (mem u).
Proof.
  intros. 
  case_eq (find x (file v)); intros. 
  simpl. 
  unfold find in H. unfold find.
  rewrite PTree.fold_spec. 
  case_eq ((file v) ! x); intros.
  
  generalize (PTree.elements_correct _ _ H0); intro. 
  generalize (PTree.elements_keys_norepet (file v)); intro.
  generalize (elements_fold (fun e => (substitute_value e (file u) (mem u))) _ _ _ (file u) H1 H2); intro.
  rewrite H3. rewrite H0 in H. subst. simpl. unfold find.    trivial. 

   assert ( ~ In r (map (@fst positive _) (PTree.elements (file v)))).
     rewrite H0 in H. inversion H; subst. 
     generalize (PTree.elements_complete (file v) r); intro. intuition. 
     generalize (elements_2 r (PTree.elements (file v)) H2); intro. destruct H3. 
     generalize (H1 x H3); intro. congruence.  

  generalize (elements_fold_1 _ (fun e => (substitute_value e (file u) (mem u))) _ (file u) H1); intro. rewrite H0 in H. inversion H ;subst.  
  rewrite H2. trivial. 

  simpl. 
  unfold find in H. unfold find.
  rewrite PTree.fold_spec. 
  case_eq ((file v) ! x); intros.
  
  generalize (PTree.elements_correct _ _ H0); intro. 
  generalize (PTree.elements_keys_norepet (file v)); intro.
  generalize (elements_fold (fun e => (substitute_value e (file u) (mem u))) _ _ _ (file u) H1 H2); intro.
  rewrite H3. unfold find in H. rewrite H0 in H. subst. simpl. unfold find.    trivial. 
  rewrite H0 in H. inversion H. 

  simpl. 
  unfold find in H. unfold find.
  rewrite PTree.fold_spec. 
  case_eq ((file v) ! x); intros.
  
  generalize (PTree.elements_correct _ _ H0); intro. 
  generalize (PTree.elements_keys_norepet (file v)); intro.
  generalize (elements_fold (fun e => (substitute_value e (file u) (mem u))) _ _ _ (file u) H1 H2); intro.
  rewrite H3. unfold find in H. rewrite H0 in H. subst. simpl. unfold find.    trivial.
  rewrite H0 in H. inversion H. 
Qed. 

Lemma delta_get' :
  forall x u v n,
  (file (u ^^ v)) ! x = Some n -> substitute_value (find x (file v)) (file u) (mem u) = n.
Proof. 
  intros. 
  rewrite <- delta_get. unfold find. rewrite H. trivial.  
Qed. 

Lemma cons_get_aux:
  forall u l c w,
  ~ Constraints.In c w ->
  Constraints.In c
      (fold_left
         (fun (a : Constraints.t) (e : Constraints.elt) =>
          Constraints.add (substitute_value_ext e (file u) (mem u)) a)
         l w) ->
exists c' : Constraints.elt,
  In c' l /\ substitute_value_ext c' (file u) (mem u) = c.
Proof. 
  induction l; intros. 
  simpl in H0. congruence. 
  simpl in H0. 
  generalize (IHl c (Constraints.add (substitute_value_ext a (file u) (mem u)) w)); clear IHl; intro IHl.
  generalize (eq_dec_s c (substitute_value_ext a (file u) (mem u))); intros. 
  destruct H1. 
  exists a. intuition.  
  assert (~
      Constraints.In c
        (Constraints.add (substitute_value_ext a (file u) (mem u)) w)).
  intuition.
  rewrite P.add_union_singleton in H1. generalize (Constraints.union_1 H1); intro. destruct H2. inversion H2; subst. congruence. inversion H4. congruence.        
  generalize (IHl H1 H0); clear IHl; intro IHl. 
  destruct IHl as [c' [A B]]. 
  exists c'. 
  split. unfold In. right; trivial. 
  trivial. 
Qed. 

Lemma cons_get_aux_2:
  forall u c v,
  Constraints.In c
      (fold_left
         (fun (a : Constraints.t) (e : Constraints.elt) =>
          Constraints.add (substitute_value_ext e (file u) (mem u)) a)
         v Constraints.empty) ->
exists c' : Constraints.elt,
  In c' v /\ substitute_value_ext c' (file u) (mem u) = c. 
Proof. 
  intros. 
  eapply cons_get_aux; eauto. 
  intuition. 
  inversion H0. 
Qed. 

Lemma cons_get :
  forall c u v,
  Constraints.In c (cons (u ^^ v)) -> (exists c', Constraints.In c' (cons v) /\ substitute_value_ext c' (file u) (mem u) = c) \/ Constraints.In c (cons u).
Proof. 
  intros. simpl in H. 
  generalize (Constraints.union_1 H); intro. clear H. 
  destruct H0. right; trivial. 
  left.
  rewrite Constraints.fold_1 in H.
  generalize (cons_get_aux_2 _ _ _ H); intro. 
  destruct H0 as [c' [A B]]. 
  exists c'. 
  split. 
  eapply in_is_in'; eauto.  
  trivial. 
Qed. 

Lemma in_fold:
  forall e u l w,
    Constraints.In e w ->
    Constraints.In e
  (fold_left
     (fun (a : Constraints.t) (e : Constraints.elt) =>
      Constraints.add (substitute_value_ext e (file u) (mem u)) a) l w).
Proof. 
  induction l; intros. 
  simpl. trivial. 
  simpl. 
  generalize (IHl (Constraints.add (substitute_value_ext a (file u) (mem u)) w)); intros.  
  eapply H0; eauto. 
  rewrite P.add_union_singleton. eapply Constraints.union_3; eauto.
Qed.   

Lemma cons_get_aux':
  forall u l c c' w,
  ~ Constraints.In c w ->
    In c' l -> substitute_value_ext c' (file u) (mem u) = c ->
  Constraints.In c
      (fold_left
         (fun (a : Constraints.t) (e : Constraints.elt) =>
          Constraints.add (substitute_value_ext e (file u) (mem u)) a)
         l w).
Proof. 
  induction l; intros. 
  inversion H0. 
  inversion H0; subst. 
  simpl.  
  eapply in_fold; eauto. rewrite P.add_union_singleton. eapply Constraints.union_2; eauto. eapply Constraints.singleton_2; eauto.   
  assert (substitute_value_ext c' (file u) (mem u) =
     substitute_value_ext c' (file u) (mem u)). trivial.   
  simpl. 
  generalize (eq_dec_s (substitute_value_ext c' (file u) (mem u)) (substitute_value_ext a (file u) (mem u))); intro.
  destruct H3. 
  rewrite e. 
    eapply in_fold; eauto. rewrite P.add_union_singleton. eapply Constraints.union_2; eauto. eapply Constraints.singleton_2; eauto.  
  assert (~
     Constraints.In (substitute_value_ext c' (file u) (mem u))
       (Constraints.add (substitute_value_ext a (file u) (mem u)) w)).  
       intuition. 
        rewrite P.add_union_singleton in H3. generalize (Constraints.union_1 H3); intro. destruct H4. inversion H4; subst. congruence. inversion H6. congruence.        
    generalize (IHl (substitute_value_ext c' (file u) (mem u)) c' (Constraints.add (substitute_value_ext a (file u) (mem u)) w) H3 H2 H1); intro.
    trivial. 
Qed. 

Lemma cons_get'_2:
  forall u l c c',
    In c' l -> substitute_value_ext c' (file u) (mem u) = c ->
  Constraints.In c
      (fold_left
         (fun (a : Constraints.t) (e : Constraints.elt) =>
          Constraints.add (substitute_value_ext e (file u) (mem u)) a)
         l Constraints.empty).
Proof. 
  intros. 
  eapply cons_get_aux'; eauto. 
  intuition. 
  inversion H1. 
Qed. 

Lemma cons_get' :
  forall c u v c',
  Constraints.In c' (cons v) -> substitute_value_ext c' (file u) (mem u) = c -> Constraints.In c (cons (u ^^ v)). 
Proof. 
  intros. 
  simpl. 
  eapply Constraints.union_3; eauto.
  rewrite Constraints.fold_1. 
  eapply cons_get'_2; eauto.
  eapply in_is_in; eauto.
Qed.  

Lemma subst_assoc : (forall v f1 f2, 
     substitute_value v (file (f2 ^^ f1)) (mem (f2 ^^ f1)) = substitute_value (substitute_value v (file f1) (mem f1)) (file f2) (mem f2)) 
     /\ (forall v f1 f2, 
     substitute_memory v (file (f2 ^^ f1)) (mem (f2 ^^ f1)) = substitute_memory (substitute_memory v (file f1) (mem f1)) (file f2) (mem f2))
     /\ (forall v f1 f2, 
     substitute_value_list v (file (f2 ^^ f1)) (mem (f2 ^^ f1)) = substitute_value_list (substitute_value_list v (file f1) (mem f1)) (file f2) (mem f2)).
Proof. 
  eapply (symbolic_combined_ind 
       (fun v => forall f1 f2, 
       substitute_value v (file (f2 ^^ f1)) (mem (f2 ^^ f1)) = substitute_value (substitute_value v (file f1) (mem f1)) (file f2) (mem f2)) 
       (fun v => forall f1 f2, 
       substitute_memory v (file (f2 ^^ f1)) (mem (f2 ^^ f1)) = substitute_memory (substitute_memory v (file f1) (mem f1)) (file f2) (mem f2))
       (fun v => forall f1 f2, 
       substitute_value_list v (file (f2 ^^ f1)) (mem (f2 ^^ f1)) = substitute_value_list (substitute_value_list v (file f1) (mem f1)) (file f2) (mem f2))
 ); eauto; intros.
  
  (* Sreg *)
  simpl. rewrite PTree.fold_spec. 
  case_eq ((file f1) ! r); intros.
 
  generalize (PTree.elements_correct _ _ H); intro. 
  unfold find. rewrite H. 
  generalize (PTree.elements_keys_norepet (file f1)); intro.
  generalize (elements_fold (fun e => (substitute_value e (file f2) (mem f2))) _ _ _ (file f2) H0 H1); intro.
  rewrite H2. trivial. 

   assert ( ~ In r (map (@fst positive _) (PTree.elements (file f1)))). 
     generalize (PTree.elements_complete (file f1) r); intro. intuition. 
     generalize (elements_2 r (PTree.elements (file f1)) H1); intro. destruct H2. 
     generalize (H0 x H2); intro. congruence.  

  generalize (elements_fold_1 _ (fun e => (substitute_value e (file f2) (mem f2))) _ (file f2) H0); intro. 
  unfold find. rewrite H. simpl. rewrite H1. unfold find. trivial. 

  (* Sop *)
  replace (substitute_value (substitute_value (Sop o s) (file f1) (mem f1)) (file f2)
  (mem f2)) with (Sop o (substitute_value_list s (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))).
    simpl. trivial. 
    simpl.  rewrite <- H. simpl. trivial. 
  
  (* Sload *)
  replace (substitute_value (substitute_value (Sload m a s s0) (file f1) (mem f1))
  (file f2) (mem f2)) with (Sload m a (substitute_value_list s (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))
  (substitute_memory s0 (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))).
    simpl. trivial.
  simpl. rewrite <- H. rewrite <- H0. trivial. 

  (* Store *) 
  replace (substitute_memory (substitute_memory (Sstore m a s s0 s1) (file f1) (mem f1))
  (file f2) (mem f2)) with (Sstore m a (substitute_value_list s (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))
  (substitute_value s0 (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))
  (substitute_memory s1 (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))).
  simpl. trivial. 
  simpl. rewrite <- H. rewrite <- H0. rewrite <- H1. trivial. 

  (* Scons *)
  replace (substitute_value_list (substitute_value_list (Scons s s0) (file f1) (mem f1))
  (file f2) (mem f2)) with (Scons (substitute_value s (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))
  (substitute_value_list s0 (file (f2) ^^ (f1)) (mem (f2) ^^ (f1)))). 
  simpl. trivial. 
  simpl. rewrite <- H. rewrite <- H0. trivial. 
Qed. 

Lemma undefined:  forall a b x, (a ^^ b).(file) ! x = None -> a.(file) ! x = None /\ b.(file) ! x = None.
  intros. 
  unfold delta in H. simpl in H.
  rewrite PTree.fold_spec in H. 
  case_eq (b.(file) ! x); intros. 
    generalize (PTree.elements_correct _ _ H0); intro. 
    generalize (PTree.elements_keys_norepet (file b)); intro. 
    generalize (elements_fold (fun v => substitute_value v (file a) (mem a)) _ _ _ (file a) H1 H2); intro.
    rewrite H3 in H. congruence. 
  intuition. 
  assert ( ~ In x (map (@fst positive _) (PTree.elements (file b)))). 
    intuition.
    generalize (elements_2 _ _ H1); intro. destruct H2. 
    generalize (PTree.elements_complete _ _ _ H2); intro. 
    congruence. 
  generalize (elements_fold_1 _ (fun v => substitute_value v (file a) (mem a)) _ (file a) H1); intro.
  rewrite H2 in H. 
  trivial. 
Qed. 

Lemma defined : 
  forall a b x q, (a ^^ b).(file) ! x = Some q -> (exists p, a.(file) ! x = Some p) \/ (exists p, b.(file) ! x = Some p).
Proof. 
  intros. 
  unfold delta in H. simpl in H. 
  rewrite PTree.fold_spec in H. 
  case_eq  (b.(file) ! x); intros. right. exists s. trivial. 
  assert ( ~ In x (map (@fst positive _) (PTree.elements (file b)))). 
    intuition.
    generalize (elements_2 _ _ H1); intro. destruct H2. 
    generalize (PTree.elements_complete _ _ _ H2); intro. 
    congruence. 
  generalize (elements_fold_1 _ (fun v => substitute_value v (file a) (mem a)) _ (file a) H1); intro.
  rewrite H2 in H. 
  left. exists q. trivial. 
Qed.  

Lemma associativity_delta : forall t u v, (t ^^ u) ^^ v ~ t ^^ (u ^^ v).
Proof.
  intros.
  generalize (subst_assoc); intro.  destruct H as [VAL [MEM LIST]]. 
  destruct v. 
  eapply Seq.   
  
  intro.
  
  assert (find x (file ((t) ^^ (u)) ^^ (mkstate file0 mem0 cons0)) = find x (file (t) ^^ ((u) ^^ (mkstate file0 mem0 cons0)))).
  rewrite delta_get. rewrite VAL. rewrite <- delta_get.
  symmetry. eapply delta_get; eauto.   
  unfold find in H. 
  case_eq ((file ((t) ^^ (u)) ^^ (mkstate file0 mem0 cons0)) ! x); case_eq ((file (t) ^^ ((u) ^^ (mkstate file0 mem0 cons0))) ! x); intros.
    rewrite H0 in H. rewrite H1 in H. congruence.  
    rewrite H0 in H. rewrite H1 in H. 
            generalize (undefined _ _ _ H0); intro. destruct H2. generalize (undefined _ _ _ H3); intro. 
            destruct H4. 
            generalize (defined _ _ _ _ H1); intro. destruct H6. 
            destruct H6. generalize (defined _ _ _ _ H6); intro. destruct H7. 
            destruct H7. congruence. 
            destruct H7. congruence. 
            destruct H6. congruence. 
    rewrite H0 in H. rewrite H1 in H. 
            generalize (undefined _ _ _ H1); intro. destruct H2. generalize (undefined _ _ _ H2); intro. 
            destruct H4. 
            generalize (defined _ _ _ _ H0); intro. destruct H6. 
            destruct H6. congruence. 
            destruct H6. generalize (defined _ _ _ _ H6); intro. destruct H7. 
            destruct H7. congruence. 
            destruct H7. congruence. 
            trivial. 

  simpl. rewrite <- MEM. simpl. trivial. 
 
  unfold Constraints.Equal.
  intro.  intuition. 
  generalize (cons_get _ _ _ H); intro.  
  destruct H0.  destruct H0 as [c' [A B]]. 
  destruct c'; unfold substitute_value_ext in B. 
  rewrite VAL in B.  
  eapply cons_get'; eauto.
  eapply cons_get'; eauto.  
  simpl. trivial. 
  rewrite MEM in B.  
  eapply cons_get'; eauto.
  eapply cons_get'; eauto.  
  simpl. trivial. 

  generalize (cons_get _ _ _ H0); intro.
  destruct H1. destruct H1 as [c' [A B]].
  eapply cons_get'; eauto.
  simpl.  eapply Constraints.union_2; eauto.

  simpl.  eapply Constraints.union_2; eauto.

  generalize (cons_get _ _ _ H); intro.  
  destruct H0.  destruct H0 as [c' [A B]].
  generalize (cons_get _ _ _ A); intro.
  destruct H0.  destruct H0 as [c'' [A' B']].
  eapply cons_get'; eauto.
  destruct c''; unfold substitute_value_ext.      
  rewrite VAL. rewrite <- B' in B. unfold substitute_value_ext in B. congruence.
  rewrite MEM. rewrite <- B' in B. unfold substitute_value_ext in B. congruence. 

   simpl. eapply Constraints.union_2; eauto.   eapply Constraints.union_3; eauto.
   rewrite Constraints.fold_1. eapply cons_get'_2; eauto. eapply in_is_in; eauto. 

  simpl. rewrite P.union_assoc. eapply Constraints.union_2; eauto. 

Qed. 
  
Lemma in_map:
  forall T r v l,
   In (r, v) l -> In r (map (fst (A:=PTree.elt) (B:=T)) l). 
Proof. 
  induction l; intros. 
  simpl in H. inversion H. 
  simpl in H. destruct H. 
  subst. simpl. left. trivial. 
  simpl. right. apply IHl; auto.
Qed.  

Lemma well_known_list : forall r v l, 
  In (r,v) l ->
  (forall x, x <> r -> forall y, ~ In (x,y) l) ->
  list_norepet (map (fst (A:=PTree.elt) (B:=symbolic_value)) l) ->
  l = (r,v) :: nil.
Proof.
  intros. 
  assert (l <> nil). destruct l. inversion H. congruence.   
  destruct l. inversion H. 
  destruct p. 
  assert (e = r). generalize (peq e r); intro. destruct H3. trivial. 
    generalize (H0 e n s); intro. simpl in H3. tauto. 
  subst. 
  assert (s = v). generalize (eq_dec_sv s v); intro. destruct H3. trivial. simpl in H1. inversion H. congruence.   
    assert (In (r,v) l) by trivial. clear H3. 
    assert (list_norepet ((r :: nil) ++ map (fst (A:=PTree.elt) (B:=symbolic_value)) l)). trivial. 
    generalize (list_norepet_app (r :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l)); intro. intuition. 
    assert (In r (r :: nil)). simpl. left; trivial. 
    generalize (@list_disjoint_notin  _ (r :: nil) (map (fst (A:=PTree.elt) (B:=symbolic_value)) l) r H9 H7); intro .
    intuition. generalize (in_map _ _ _ l H4); intro. intuition.   
  subst. 
  assert (l = nil). destruct l. trivial. 
  destruct p. 
  generalize (peq e r); intro. destruct H3. subst. simpl in H1. inversion H1. intuition. 
  assert (In r (r :: map (fst (A:=PTree.elt) (B:=symbolic_value)) l)). simpl. left; trivial. intuition. 
  generalize (H0 e n s); intro. simpl in H3. intuition. 
  subst. trivial. 
Qed. 

Lemma elements_one : forall r v,   
(PTree.elements ((PTree.set r v) (PTree.empty symbolic_value)) = ((r,v) :: nil)).
Proof.
  intros. 
  assert ((PTree.set r v (PTree.empty symbolic_value)) ! r = Some v).
    rewrite PTree.gss. trivial. 
  assert (forall x, x <> r -> (PTree.set r v (PTree.empty symbolic_value)) ! x = None). 
    intros. 
    rewrite PTree.gso. rewrite PTree.gempty. trivial. trivial. 
  generalize (PTree.elements_correct _ _ H); intro. 
   assert (forall x y, x <> r -> ~ In (x,y) (PTree.elements (PTree.set r v (PTree.empty symbolic_value)))).
     intros. intuition. 
     generalize (PTree.elements_complete _ _ _ H3); intro.
     generalize (H0 x H2); intro. 
     congruence. 
  clear H H0.
  generalize (PTree.elements_keys_norepet (PTree.set r v (PTree.empty symbolic_value))); intro.
   eapply well_known_list; eauto. 
Qed. 

Lemma subst_one: forall a t, find a (file t) = substitute_value (find a (PTree.empty symbolic_value)) (file t) (mem t). 
Proof. 
  intros. 
  unfold find.
  rewrite PTree.gempty. 
  simpl. unfold find. trivial. 
Qed. 
  
Lemma subst_list: forall l t, get_args l (file t) = substitute_value_list (get_args l (PTree.empty symbolic_value)) (file t) (mem t). 
Proof.
  induction l; intros.    
  simpl. trivial. 
  simpl. rewrite (IHl t).
  rewrite subst_one. trivial. 
Qed. 
   
Lemma distrib_one: forall a t, (symbolic_evaluation_rec (a :: nil) t) ~ (t ^^ (symbolic_evaluation_rec (a :: nil) initial_state)).
Proof. 
  intros. 
  destruct a. 

  (* Move *)

  eapply Seq. 
  simpl. rewrite PTree.fold_spec. 
  rewrite elements_one.
  simpl. 
  unfold find. rewrite PTree.gempty. simpl. unfold find.     
  case_eq (PTree.eq eq_dec_sv (PTree.set r0 match (file t) ! r with
                   | Some v => v
                   | None => Sreg r
                   end (file t))
     (PTree.set r0 match (file t) ! r with
                   | Some v => v
                   | None => Sreg r
                   end (file t))); intros; trivial; congruence. 
  simpl. trivial. 
  simpl. rewrite Constraints.fold_1. simpl. 
    rewrite P.empty_union_2; eauto.
    eapply P.equal_refl. 

  (* op *)

  eapply Seq. 
  simpl. rewrite PTree.fold_spec. 
  rewrite elements_one. 
  simpl.
  rewrite subst_list. 
  case_eq (PTree.eq eq_dec_sv
     (PTree.set r
        (Sop o
           (substitute_value_list (get_args l (PTree.empty symbolic_value))
              (file t) (mem t))) (file t))
     (PTree.set r
        (Sop o
           (substitute_value_list (get_args l (PTree.empty symbolic_value))
              (file t) (mem t))) (file t))); intros; trivial; congruence. 
  simpl. trivial. 
  simpl. rewrite Constraints.fold_1. simpl. 
  rewrite P.union_sym. rewrite P.union_add.
   rewrite P.empty_union_1; eauto.
   rewrite subst_list. 
   eapply P.equal_refl. 

  (* load *)
   
  eapply Seq. 
  simpl. rewrite PTree.fold_spec. 
  rewrite elements_one. 
  simpl.
  rewrite subst_list. 
  case_eq (PTree.eq eq_dec_sv
     (PTree.set r
        (Sload m a
           (substitute_value_list (get_args l (PTree.empty symbolic_value))
              (file t) (mem t)) (mem t)) (file t))
     (PTree.set r
        (Sload m a
           (substitute_value_list (get_args l (PTree.empty symbolic_value))
              (file t) (mem t)) (mem t)) (file t))); intros; trivial; congruence. 
  simpl. trivial. 
  simpl. rewrite Constraints.fold_1. simpl. 
  rewrite P.union_sym. rewrite P.union_add.
   rewrite P.empty_union_1; eauto.
   rewrite subst_list. 
   eapply P.equal_refl.   

  (* store *)

  eapply Seq. 
  simpl. rewrite PTree.fold_spec. 
  simpl. 
  case_eq (PTree.eq eq_dec_sv (file t) (file t)); intros; trivial; congruence. 
  simpl. rewrite subst_list. rewrite subst_one. trivial.  
  simpl. rewrite Constraints.fold_1. simpl.
  rewrite <- subst_list. rewrite <- subst_one.
  rewrite P.union_sym. rewrite P.union_add. 
  rewrite P.empty_union_1; eauto.    
   eapply P.equal_refl.
Qed.   

Lemma distributivity: forall l u v, (symbolic_evaluation_rec l (u ^^ v)) ~ (u ^^ (symbolic_evaluation_rec l v)).
Proof. 
  induction l; intros. 
  simpl. apply seq_reflexivity.
  rewrite step_eval_sym.
  rewrite distrib_one; eauto.
  rewrite associativity_delta. 
  rewrite <- distrib_one. 
  rewrite (IHl u (symbolic_evaluation_rec (a :: nil) v)).
  rewrite <- step_eval_sym. 
  apply seq_reflexivity.
Qed.  
 
Lemma decomposition: forall l u, (symbolic_evaluation_rec l u) ~ (u ^^ (symbolic_evaluation_rec l initial_state)). 
Proof. 
  intros. 
  rewrite <- (distributivity l u initial_state). 
  rewrite neutral_right.
  eapply seq_reflexivity; eauto.  
Qed.   

Lemma parametricity : forall l1 l2 x,
  (symbolic_evaluation_rec l1 initial_state) ~ (symbolic_evaluation_rec l2 initial_state) ->
  (symbolic_evaluation_rec (x ++ l1) initial_state) ~ (symbolic_evaluation_rec (x ++ l2) initial_state).
Proof.
  intros.
  rewrite star_eval_sym.  
  rewrite decomposition.
  rewrite H. 
  rewrite <- decomposition.
  rewrite <- star_eval_sym.  
  apply seq_reflexivity. 
Qed. 
 
(* SEMANTIQUE *)
(*
Record state : Set := mkst {
  stack: list stackframe;
  c: code;            
  sp: val;                    
  rs: regset;             
  mm: Mem.mem
}.               
*)
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
    assert (rs = (mkst stack c sp rs m).(SE.rs)). trivial. rewrite H2. 
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
    assert (rs = (mkst stack c sp rs m0).(SE.rs)). trivial. rewrite H2. 
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
    assert (rs = (mkst stack c sp rs m0).(SE.rs)). trivial. rewrite H5. 
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

Lemma eq_to_sem: 
  forall ge l1 l2 s s',
  (symbolic_evaluation l1) ~ (symbolic_evaluation l2) -> (lsteps ge l1 s s' <-> lsteps ge l2 s s'). 
Proof. 
  intros.
  inversion H; subst. 
  intuition. 
  generalize (correct _ _ _ _  H3); intro.  
  destruct H4. 
  eapply complete; eauto. 
  split.
  inversion H4; subst. 
  eapply Sem_intro; eauto. 
  congruence. 
  intros. 
  eapply H9; eauto. generalize (PTree.elements_complete _ _ _ H6); intro. 
  generalize  (H0 r); intro. rewrite <- H11 in H7. eapply PTree.elements_correct; eauto. 
  intros. eapply H10. intuition. 
    generalize (H0 r); intro. 
    generalize (elements_2 _ _ H7); intro. destruct H12. 
    generalize (PTree.elements_complete _ _ _ H12); intro. rewrite H13 in H11. 
    assert ((file (symbolic_evaluation l2)) ! r = Some x). symmetry. trivial.    
    generalize (PTree.elements_correct _ _ H14); intro. 
        generalize (in_map _ _ _ _ H15); intro. intuition.  
    
  unfold satisfy_sym_state. intros. rewrite <- H2 in H6.
  unfold satisfy_sym_state in H5. 
  eapply H5; eauto. 

  generalize (correct _ _ _ _  H3); intro.  
  destruct H4. 
  eapply complete; eauto. 
  split.
  inversion H4; subst. 
  eapply Sem_intro; eauto. 
  congruence. 
  intros. 
  eapply H9; eauto. generalize (PTree.elements_complete _ _ _ H6); intro. 
  generalize  (H0 r); intro. rewrite H11 in H7. eapply PTree.elements_correct; eauto. 
  intros. eapply H10. intuition. 
    generalize (H0 r); intro. 
    generalize (elements_2 _ _ H7); intro. destruct H12. 
    generalize (PTree.elements_complete _ _ _ H12); intro. rewrite <- H11 in H13. 
    generalize (PTree.elements_correct _ _ H13); intro. 
        generalize (in_map _ _ _ _ H14); intro. intuition.  
    
  unfold satisfy_sym_state. intros. rewrite H2 in H6.
  unfold satisfy_sym_state in H5. 
  eapply H5; eauto. 
Qed. 

Definition check (t1 t2 : sym_state) : bool :=
        (PTree.beq (fun a b => if eq_dec_sv a b then true else false) t1.(file) t2.(file))
  && (if eq_dec_sm t1.(mem) t2.(mem) then true else false) 
  && (Constraints.equal t1.(cons) t2.(cons)).

Lemma check_correct : 
  forall t1 t2, check t1 t2 = true -> t1 ~ t2. 
Proof.
  intros. 
  unfold check in H. 
  case_eq (PTree.beq
      (fun a b : symbolic_value => if eq_dec_sv a b then true else false)
      (file t1) (file t2) ); intros. 
  rewrite H0 in H.
  simpl in H. 
  case_eq (if eq_dec_sm (mem t1) (mem t2)
     then true
     else false); intros. 
  rewrite H1 in H.
  simpl in H. 
  eapply Seq; eauto.
  assert (forall x y : symbolic_value,
      (if eq_dec_sv x y then true else false) = true -> x = y).
  intros. 
  case_eq (eq_dec_sv x y); intros. congruence. rewrite H3 in H2; congruence. 
  generalize (PTree.beq_correct (fun (a : symbolic_value) b => a = b) 
                       (fun a b : symbolic_value => if eq_dec_sv a b then true else false)
                       H2 t1.(file) t2.(file) H0); intro.
  intro. unfold PTree.exteq in H3. 
  generalize (H3 x); intro. clear H3.
  case_eq ((file t1) ! x); intros. rewrite H3 in H4. 
  case_eq ((file t2) ! x); intros. rewrite H5 in H4. congruence.   
  rewrite H5 in H4. inversion H4. 
  rewrite H3 in H4. 
  case_eq ((file t2) ! x); intros. 
  rewrite H5 in H4. inversion H4. trivial. 
  case_eq (eq_dec_sm (mem t1) (mem t2)); intros.
  trivial. rewrite H2 in H1. congruence. 
  eapply Constraints.equal_2; eauto.
  rewrite H1 in H. simpl in H. congruence. 
  rewrite H0 in H. simpl in H. congruence. 
Qed. 

Definition elt := symbolic_value. 

Definition get (t : sym_state) (r : reg) : elt := find r (file t).

Definition elt_dec (e e' : elt) : bool := if eq_dec_sv e e' then true else false. 

Fixpoint delta_mini_value (e' e : elt) {struct e} : option elt :=  
  match e with
  | Sreg r => Some e' 
  | Sop op args  => match delta_mini_value_list e' args with 
                                 | None => None 
                                 | Some l => Some (Sop op l)
                                 end
  | Sload mc addr args mem => None
  end
with delta_mini_value_list (e' : elt)  (l : symbolic_value_list) {struct l} : option symbolic_value_list := 
  match l with
  | Snil => Some Snil
  | Scons arg args => match (delta_mini_value e' arg), (delta_mini_value_list e' args) with 
                                     | Some a, Some l => Some (Scons a l) 
                                     | _, _ => None
                                     end
  end.

Fixpoint only (e : elt) (r : reg) {struct e}: bool :=
  match e with
  | Sreg re => if peq r re then true else false 
  | Sop op args  => only_list args r
  | Sload mc addr args mem => false 
  end
with only_list (l : symbolic_value_list) (r : reg) {struct l} : bool := 
  match l with
  | Snil => true
  | Scons arg args => only arg r && only_list args r
  end.

Definition Pr (v2 v1 : symbolic_value) : Prop :=
  forall a b r v, 
  get (a ^^ b) r = v -> get a r = v1 -> get b r = v2 ->
  only v2 r = true ->
  delta_mini_value v1 v2 = Some v. 

Lemma substitute_only:
  (forall v a r v1, 
  (file a) ! r = Some v1 ->
  only v r = true ->
  delta_mini_value v1 v = Some (substitute_value v (file a) (mem a))) /\
  (forall (m : symbolic_mem), True) /\
  (forall l a r v1, 
  (file a) ! r = Some v1 ->  
  only_list l r = true ->
  delta_mini_value_list v1 l = Some (substitute_value_list l (file a) (mem a))).
Proof. 
    eapply (symbolic_combined_ind 
       (fun v =>forall a r v1, 
  (file a) ! r = Some v1 ->
  only v r = true ->
  delta_mini_value v1 v = Some (substitute_value v (file a) (mem a)))
       (fun v => True )
       (fun l => forall a r v1, 
  (file a) ! r = Some v1 ->  
  only_list l r = true ->
  delta_mini_value_list v1 l = Some (substitute_value_list l (file a) (mem a)))
 ); eauto; intros; simpl.
  simpl in H0. 
  case_eq (peq r0 r); intros.
  clear H1. subst. unfold find. rewrite H. trivial. 
  rewrite H1 in H0. congruence.
  simpl in H1. generalize (H _ _ _ H0 H1); intro. rewrite H2. trivial. 
  simpl in H2. congruence. 
  simpl in H2.
  case_eq (only s r); intros. 
  rewrite H3 in H2. simpl in H2. 
  generalize (H _ _ _ H1 H3); intro. rewrite H4. 
  generalize (H0 _ _ _ H1 H2); intro. rewrite H5. trivial. 
  rewrite H3 in H2. simpl in H2.  congruence. 
Qed. 

Lemma substitute_only_none:
  (forall v a r, 
  (file a) ! r = None ->
  only v r = true ->
  delta_mini_value (Sreg r) v = Some (substitute_value v (file a) (mem a))) /\
  (forall (m : symbolic_mem), True) /\
  (forall l a r, 
  (file a) ! r = None ->  
  only_list l r = true ->
  delta_mini_value_list (Sreg r) l = Some (substitute_value_list l (file a) (mem a))).
Proof. 
    eapply (symbolic_combined_ind 
       (fun v =>forall a r, 
  (file a) ! r = None ->
  only v r = true ->
  delta_mini_value (Sreg r) v = Some (substitute_value v (file a) (mem a)))
       (fun v => True )
       (fun l => forall a r, 
  (file a) ! r = None ->  
  only_list l r = true ->
  delta_mini_value_list (Sreg r) l = Some (substitute_value_list l (file a) (mem a)))
 ); eauto; intros; simpl.
  simpl in H0.   
  case_eq (peq r0 r); intros.
  clear H1. subst. unfold find. rewrite H. trivial. 
  rewrite H1 in H0. congruence.
  simpl in H1. generalize (H _ _ H0 H1); intro. rewrite H2. trivial. 
  simpl in H2. congruence. 
  simpl in H2.
  case_eq (only s r); intros. 
  rewrite H3 in H2. simpl in H2. 
  generalize (H _ _ H1 H3); intro. rewrite H4. 
  generalize (H0 _ _ H1 H2); intro. rewrite H5. trivial. 
  rewrite H3 in H2. simpl in H2.  congruence. 
Qed. 

Lemma mini_delta: forall v2 v1, forall a b r v, 
  get (a ^^ b) r = v -> get a r = v1 -> get b r = v2 ->
  only v2 r = true ->
  delta_mini_value v1 v2 = Some v. 
Proof.
  destruct v2; intros.
  
  simpl. inversion H2; subst. 
  case_eq (peq r0 r); intros. 
  clear H. subst. 2: rewrite H in H4; congruence.
  clear H4. 
  unfold get in *|-. 
  unfold delta. simpl. 
  rewrite PTree.fold_spec. 
  unfold find in H1. case_eq ((file b) ! r); intros. 
  rewrite H in H1. inversion H1; subst. 
  generalize (PTree.elements_correct _ _ H); intro. 
  generalize (PTree.elements_keys_norepet (file b)); intro. 
  generalize (elements_fold (fun v => substitute_value v (file a) (mem a)) _ _ _ (file a) H1 H3); intro.
  unfold get. unfold elt in H4. simpl. unfold find. 
  rewrite H4. simpl. unfold find. trivial.  

  unfold get. simpl.
  assert (~ In r (map (fst (A:=positive) (B:=symbolic_value)) (PTree.elements (file b)))).
  intuition. 
  generalize (elements_2 _ _ H0); intro. destruct H3. 
  generalize (PTree.elements_complete _ _ _ H3); intro. congruence. 
  generalize (elements_fold_1 r (fun v => substitute_value v (file a) (mem a)) _ (file a) H0); intro.
  unfold elt in H3. unfold find. rewrite H3. trivial.  

  simpl. simpl in H2.  
  unfold get in *|-. 
  unfold delta in H. simpl in H. 
  rewrite PTree.fold_spec in H. 
  unfold find in H1. case_eq ((file b) ! r); intros. rewrite H3 in H1. 2: rewrite H3 in H1; congruence.  subst. 
  generalize (PTree.elements_correct _ _ H3); intro. 
  generalize (PTree.elements_keys_norepet (file b)); intro. 
  generalize (elements_fold (fun v => substitute_value v (file a) (mem a)) _ _ _ (file a) H H0); intro.
  simpl in H1. unfold elt in H1. unfold find. rewrite H1.
  generalize (substitute_only); intro. 
  destruct H4. 
  destruct H5. 
  case_eq ((file a) ! r); intros. 
  generalize (H6 _ _ _ _ H7 H2); intro. rewrite H8. trivial. 
  generalize (substitute_only_none); intro. 
  destruct H8 as [A [B C]]. 
  rewrite (C _ _ _ H7 H2). trivial.  
 
  simpl in H2. congruence. 
  Qed. 
  
Lemma get_compat:
  forall a b r,
  a ~ b -> get a r = get b r. 
Proof. 
  intros. 
  unfold get. 
  unfold find. 
  inversion H; subst. 
  generalize (H0 r); intro.
  rewrite H3. trivial. 
Qed. 

Module M : SE.Eval.
Definition t := sym_state. 
Definition eq := symbolic_equivalence. 
Definition eq_refl := seq_reflexivity.
Definition eq_sym := seq_symmetry. 
Definition  eq_trans := seq_transitivity. 
Add Relation t eq
    reflexivity proved by (@eq_refl)
    symmetry proved by (@eq_sym)
    transitivity proved by (@eq_trans)
as sym_eq. 
Definition delta := delta. 
Lemma delta_assoc : forall t t' t'', t ^^ (t' ^^ t'') ~ (t ^^ t') ^^ t''. intros. eapply eq_sym. eapply associativity_delta. Qed.      
Lemma delta_compatible_right : forall t t' t'', t ~ t' -> t'' ^^ t ~  t'' ^^ t'. 
  intros. eapply delta_compatible_right. trivial. Qed.  
Definition delta_compatible_left := delta_compatible_left. 
Definition I := initial_state. 
Definition init_neutral_left := neutral_left.
Definition init_neutral_right := neutral_right.  
Definition evaluate := symbolic_evaluation. 
Lemma kernel : (evaluate nil) ~ I. unfold evaluate. unfold symbolic_evaluation. unfold I. simpl. eapply Seq; eauto. simpl. eapply P.equal_refl. Qed.    
Lemma decomposition : forall l l', (evaluate (l ++ l')) ~ ((evaluate l) ^^ (evaluate l')).
Proof. 
  intros. 
  unfold evaluate. unfold symbolic_evaluation. rewrite star_eval_sym. eapply decomposition. Qed. 
Definition dec := check. 
Definition dec_correct := check_correct. 
Lemma correct : forall l l', (evaluate l) ~ (evaluate l') -> forall ge s s', (lsteps ge l s s' <-> lsteps ge l' s s').
Proof. 
  intros. 
  eapply eq_to_sem; eauto. Qed. 

Definition elt := elt. 
Definition get := get. 
Definition only := only. 
Definition delta_mini := delta_mini_value. 

Definition get_compatibility := get_compat. 

Lemma get_decomposition : 
  forall a b r, 
  only (get b r) r = true ->
  delta_mini (get a r) (get b r) = Some (get (a ^^ b) r). 
Proof. 
  intros. eapply mini_delta; eauto. 
Qed. 

Definition dec_elt (e e' : elt) : bool := if eq_dec_sv e e' then true else false. 
Lemma dec_elt_correct : forall e e', dec_elt e e' = true -> e = e'. 
Proof. 
  intros. unfold dec_elt in H. 
  case_eq (eq_dec_sv e e'); intros. 
  clear H0. subst. trivial. 
  rewrite H0 in H. congruence. 
Qed. 

End M.    
(*
Import M. 

Lemma plop: 
  forall x l1 l2, 
  (evaluate l1) ~ (evaluate l2) ->
  (evaluate (x ++ l1))  ~ (evaluate (x ++ l2)).
Proof. 
  intros. 
  rewrite decomposition. 
  rewrite decomposition.  
  auto.  
Qed.

Add LoadPath "/usr/local/lib/zenon".
Require Import "zenon". 

Lemma ploprrr : forall x l1 l2, ((eq (evaluate l1) (evaluate l2))->(eq (evaluate (List.app x l1)) (evaluate (List.app x l2)))).
intros x l1 l2.
apply NNPP. intro zenon'G.
apply (zenon_notimply_s _ _ zenon'G). zenon_intro zenon'H14. zenon_intro zenon'H13.
generalize (decomposition x). zenon_intro zenon'H15.
generalize (zenon'H15 l2). zenon_intro zenon'H16.
generalize (@eq_sym (evaluate (List.app x l2))). zenon_intro zenon'H17.
generalize (zenon'H17 (evaluate (List.app x l1))). zenon_intro zenon'H18.
apply (zenon_imply_s _ _ zenon'H18); [ zenon_intro zenon'H1a | zenon_intro zenon'H19 ].
elim (classic (eq (delta (evaluate x) (evaluate l2)) (evaluate (List.app x l1)))); [ zenon_intro zenon'H1b | zenon_intro zenon'H1c ].
generalize (@eq_trans (evaluate (List.app x l2))). zenon_intro zenon'H1d.
generalize (zenon'H1d (delta (evaluate x) (evaluate l2))). zenon_intro zenon'H1e.
generalize (zenon'H1e (evaluate (List.app x l1))). zenon_intro zenon'H1f.
apply (zenon_imply_s _ _ zenon'H1f); [ zenon_intro zenon'H21 | zenon_intro zenon'H20 ].
exact (zenon'H21 zenon'H16).
apply (zenon_imply_s _ _ zenon'H20); [ zenon_intro zenon'H1c | zenon_intro zenon'H22 ].
exact (zenon'H1c zenon'H1b).
exact (zenon'H1a zenon'H22).
generalize (zenon'H15 l1). zenon_intro zenon'H23.
generalize (@eq_sym (evaluate (List.app x l1))). zenon_intro zenon'H24.
generalize (zenon'H24 (delta (evaluate x) (evaluate l2))). zenon_intro zenon'H25.
apply (zenon_imply_s _ _ zenon'H25); [ zenon_intro zenon'H26 | zenon_intro zenon'H1b ].
elim (classic (eq (delta (evaluate x) (evaluate l1)) (delta (evaluate x) (evaluate l2)))); [ zenon_intro zenon'H27 | zenon_intro zenon'H28 ].
generalize (@eq_trans (evaluate (List.app x l1))). zenon_intro zenon'H29.
generalize (zenon'H29 (delta (evaluate x) (evaluate l1))). zenon_intro zenon'H2a.
generalize (zenon'H2a (delta (evaluate x) (evaluate l2))). zenon_intro zenon'H2b.
apply (zenon_imply_s _ _ zenon'H2b); [ zenon_intro zenon'H2d | zenon_intro zenon'H2c ].
exact (zenon'H2d zenon'H23).
apply (zenon_imply_s _ _ zenon'H2c); [ zenon_intro zenon'H28 | zenon_intro zenon'H2e ].
exact (zenon'H28 zenon'H27).
exact (zenon'H26 zenon'H2e).
generalize (@delta_compatible_right (evaluate l2)). zenon_intro zenon'H2f.
generalize (zenon'H2f (evaluate l1)). zenon_intro zenon'H30.
generalize (zenon'H30 (evaluate x)). zenon_intro zenon'H31.
apply (zenon_imply_s _ _ zenon'H31); [ zenon_intro zenon'H33 | zenon_intro zenon'H32 ].
generalize (@eq_sym (evaluate l1)). zenon_intro zenon'H34.
generalize (zenon'H34 (evaluate l2)). zenon_intro zenon'H35.
apply (zenon_imply_s _ _ zenon'H35); [ zenon_intro zenon'H37 | zenon_intro zenon'H36 ].
exact (zenon'H37 zenon'H14).
exact (zenon'H33 zenon'H36).
generalize (@eq_sym (delta (evaluate x) (evaluate l2))). zenon_intro zenon'H38.
generalize (zenon'H38 (delta (evaluate x) (evaluate l1))). zenon_intro zenon'H39.
apply (zenon_imply_s _ _ zenon'H39); [ zenon_intro zenon'H3a | zenon_intro zenon'H27 ].
exact (zenon'H3a zenon'H32).
exact (zenon'H28 zenon'H27).
exact (zenon'H1c zenon'H1b).
exact (zenon'H13 zenon'H19).
Qed.

*)






 
 
 
