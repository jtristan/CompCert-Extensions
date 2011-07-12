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

(** Definition of symbolic state *)

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

(** Definition of symbolic evaluation *)

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

Inductive weq : observables -> sym_state -> sym_state -> Prop :=
  | Seq_weak : forall o s s',  
            (forall x, In x o -> s.(file) ! x = s'.(file) ! x) -> 
            s.(mem) = s'.(mem) -> 
            Constraints.Equal s.(cons) s'.(cons) -> 
            weq o s s'. 

Lemma rewrite_left : forall t1 t2, t1 ~ t2 -> forall o s, weq o t1 s -> weq o t2 s.
Proof. 
  intros. 
  inversion H; subst. inversion H0; subst. 
  destruct t1; destruct t2; destruct s; simpl in *|-; subst; subst.
  rewrite H6 in H3. 
  eapply Seq_weak; eauto.
  intros. simpl.
  generalize (H4 x H2); intro. generalize (H1 x); intro. congruence. 
  simpl. rewrite H3. eapply P.equal_refl.
Qed.

Lemma rewrite_right : forall t1 t2, t1 ~ t2 -> forall o s, weq o s t1 -> weq o s t2.
Proof. 
  intros. 
  inversion H; subst. inversion H0; subst. 
  destruct t1; destruct t2; destruct s; simpl in *|-; subst; subst.
  rewrite H3 in H6. 
  eapply Seq_weak; eauto.
  intros. simpl.
  generalize (H4 x H2); intro. generalize (H1 x); intro. congruence. 
Qed.   

Lemma obs_rewrite_right : forall o x y z, weq o x y -> weq o (z ^^ x) (z ^^ y).
Proof. 
  intros. 
  inversion H; subst. 
  eapply Seq_weak; eauto; unfold delta; simpl.
 
  intros. 
  repeat (rewrite PTree.fold_spec). 
  generalize (H0 x0 H3); intro. 
  generalize (PTree.elements_keys_norepet (file x)); intro.
  generalize (PTree.elements_keys_norepet (file y)); intro.

  case_eq ((file x) ! x0); case_eq ((file y) ! x0); intros.
  rewrite H7 in H4. rewrite H8 in H4. subst. 
  generalize (PTree.elements_correct _ _ H7); intro.
  generalize (PTree.elements_correct _ _ H8); intro.
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H9 H6).
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H10 H5).
  congruence.  

  rewrite H7 in H4. rewrite H8 in H4. subst. 
  generalize (PTree.elements_correct _ _ H8); intro.
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H9 H5).
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file y)))).
     generalize (PTree.elements_complete (file y) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file y)) H11); intro. destruct H12. 
     generalize (H10 x1 H12); intro. congruence.  
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H10).
  congruence. 
  rewrite H7 in H4. rewrite H8 in H4. subst. 
  generalize (PTree.elements_correct _ _ H7); intro.
  rewrite (elements_fold  (fun p => substitute_value p (file z) (mem z)) _ _ _ (file z) H9 H6).
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file x)))).
     generalize (PTree.elements_complete (file x) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file x)) H11); intro. destruct H12. 
     generalize (H10 x1 H12); intro. congruence.  
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H10).
  congruence. 
  rewrite H7 in H4. rewrite H8 in H4. subst. 
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file x)))).
     generalize (PTree.elements_complete (file x) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file x)) H10); intro. destruct H11. 
     generalize (H9 x1 H11); intro. congruence.
     assert ( ~ In x0 (map (@fst positive _) (PTree.elements (file y)))).
     generalize (PTree.elements_complete (file y) x0); intro. intuition. 
     generalize (elements_2 x0 (PTree.elements (file y)) H11); intro. destruct H12. 
     generalize (H10 x1 H12); intro. congruence.  
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H9).
  rewrite (elements_fold_1 x0 (fun p => substitute_value p (file z) (mem z)) _ (file z) H10).
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

Lemma weq_reflexivity: forall o s, weq o s s. 
Proof. 
  intros. 
  apply Seq_weak; auto.
  apply P.equal_refl.  
Qed.  

Lemma weq_symmetry: forall o s s', weq o s s' -> weq o s' s.
Proof. 
  intros.
  inversion H; subst. 
  eapply Seq_weak; eauto.
  intros. generalize (H0 _ H3); intros. congruence. 
  rewrite H2. apply P.equal_refl. 
Qed. 
  
Lemma weq_transitivity: forall o s1 s2 s3, weq o s1 s2 -> weq o s2 s3 -> weq o s1 s3.
Proof. 
  intros. 
  inversion H; subst. 
  inversion H0; subst. 
  eapply Seq_weak; eauto. 
  intros. generalize (H1 x H7); intro. generalize (H4 x H7); intro. congruence. 
  congruence. 
  unfold Constraints.Equal in *|-. 
  unfold Constraints.Equal.
  intro. generalize (H3 a); intro. generalize (H6 a); intro.   
  intuition.
Qed. 

Inductive In_value : reg -> symbolic_value -> Prop :=
  | In_reg : forall x, In_value x (Sreg x)  
  | In_op : forall x o l, In_value_list x l -> In_value x (Sop o l)
  | In_load_1 : forall x mc addr l m, In_value_list x l -> In_value x (Sload mc addr l m)
  | In_load_2 : forall x mc addr l m, In_mem x m -> In_value x (Sload mc addr l m)
with In_mem : reg -> symbolic_mem -> Prop :=
  | In_store_1 : forall x mc addr l v m, In_value x v -> In_mem x (Sstore mc addr l v m)  
  | In_store_2 : forall x mc addr l v m, In_value_list x l -> In_mem x (Sstore mc addr l v m)  
  | In_store_3 : forall x mc addr l v m, In_mem x m -> In_mem x (Sstore mc addr l v m)  
with In_value_list : reg -> symbolic_value_list -> Prop :=
  | In_cons_1 : forall x v l, In_value x v -> In_value_list x (Scons v l)
  | In_cons_2 : forall x v l, In_value_list x l -> In_value_list x (Scons v l).

Inductive In_ext : reg -> tv -> Prop :=
  | In_V : forall x v, In_value x v -> In_ext x (V v)
  | In_M : forall x m, In_mem x m -> In_ext x (M m). 

Inductive domain : sym_state -> observables -> Prop :=
  |  Dom : forall obs st, 
            (forall x, In x obs -> forall v, st.(file) ! x = Some v -> (forall y, In_value y v -> In y obs)) ->  
            (forall x, In_mem x st.(mem) -> In x obs) ->
            (forall e, Constraints.In e st.(cons) -> (forall y, In_ext y e -> In y obs)) -> (* Ajout recent *)
            domain st obs. 
Check substitute_value. 

Lemma domain_prop_1_aux: forall obs rs m,
  (forall x, In x obs -> forall v, rs ! x = Some v -> (forall y, In_value y v -> In y obs)) ->  
  (forall x, In_mem x m -> In x obs) ->
  (forall v, (forall y, In_value y v -> In y obs) -> forall y, In_value y (substitute_value v rs m) -> In y obs) /\
  (forall v, (forall y, In_mem y v -> In y obs) -> forall y, In_mem y (substitute_memory v rs m) -> In y obs) /\
  (forall v, (forall y, In_value_list y v -> In y obs) -> forall y, In_value_list y (substitute_value_list v rs m) -> In y obs). 
Proof.
  intros obs rfs m A B. 
  eapply (symbolic_combined_ind 
  (fun v => (forall y, In_value y v -> In y obs) -> forall y, In_value y (substitute_value v rfs m) -> In y obs)
  (fun v => (forall y, In_mem y v -> In y obs) -> forall y, In_mem y (substitute_memory v rfs m) -> In y obs)
  (fun v => (forall y, In_value_list y v -> In y obs) -> forall y, In_value_list y (substitute_value_list v rfs m) -> In y obs)
  ); intros; eauto; simpl.
  
  simpl in H0. 
  unfold find in H0. 
  case_eq (rfs ! r); intros. 
  rewrite H1 in H0. 
  eapply A; eauto.
  eapply H; eauto. 
  eapply In_reg; eauto. 

  rewrite H1 in H0. 
  inversion H0; subst. 
  eapply H; eauto. 
    
  simpl in H1. inversion H1; subst. 
  eapply H; eauto. 
  intros. eapply H0; eauto. 
  eapply In_op; eauto. 

  simpl in H2. inversion H2; subst. 
  eapply H; eauto. 
  intros. eapply H1; eauto. 
  eapply In_load_1; eauto. 
  eapply H0; eauto. 
  intros. eapply H1; eauto. 
  eapply In_load_2; eauto. 

  simpl in H3. inversion H3; subst.
  eapply H0; eauto.
  intros. eapply H2; eauto.
  eapply In_store_1; eauto.
  eapply H; eauto.
  intros. eapply H2; eauto.
  eapply In_store_2; eauto.
  eapply H1; eauto.
  intros. eapply H2; eauto.
  eapply In_store_3; eauto.

  simpl in H2. inversion H2; subst.
  eapply H; eauto. 
  intros. eapply H1; eauto. 
  eapply In_cons_1; eauto. 
  eapply H0; eauto. 
  intros. eapply H1; eauto. 
  eapply In_cons_2; eauto.
Qed.    

Lemma domain_prop_1: forall o a b, domain a o -> domain b o -> domain (a ^^ b) o.
Proof.
  intros.
  inversion H; subst. inversion H0; subst. 
  eapply Dom; eauto. 

  intros. simpl in H8.

  case_eq ((file b) ! x); intros. 

  rewrite PTree.fold_spec in H8. 
  generalize (PTree.elements_keys_norepet (file b)); intro.
  generalize (PTree.elements_correct _ _ H10); intro. 
  generalize (elements_fold (fun v => (substitute_value v (file a) (mem a))) (PTree.elements (file b)) _ _ (file a) H12 H11); intro.
  rewrite H13 in H8. 
  inversion H8; subst. 
  generalize (domain_prop_1_aux _ _ _ H1 H2); intro.
  destruct H14 as [E1 [E2 E3]].
  generalize (H4 _ H7 _ H10); intro. 
  eapply E1; eauto. 

  rewrite PTree.fold_spec in H8.
  assert (~ In x (map (fst (A:=positive) (B:=symbolic_value)) (PTree.elements (file b)))).
      intuition. 
      generalize (elements_2 _ _ H11); intro. 
      destruct H12. 
      generalize (PTree.elements_complete _ _ _ H12); intro.
      congruence. 
  generalize (elements_fold_1 x (fun v => substitute_value v (file a) (mem a)) (PTree.elements (file b)) (file a) H11); intro.
  rewrite H12 in H8. 
  eapply H1; eauto. 
  
  (* Memory *)
  simpl. intros.
  generalize (domain_prop_1_aux _ _ _ H1 H2); intro.
  destruct H8 as [E1 [E2 E3]].
  eapply E2; eauto. 

  (* constraints *)
  intros.
  generalize (cons_get _ _ _ H7); intro.
  destruct H9.

  destruct H9 as [c' [A B]]. 
  destruct e.
  unfold substitute_value_ext in B. 
  destruct c'; try congruence. 
  inversion B; subst.
  generalize (domain_prop_1_aux _ _ _ H1 H2); intro.
  destruct H9 as [E1 [E2 E3]].
  generalize (H6 _ A); intro. 
  inversion H8; subst. 
  eapply E1; eauto. 
  intros. eapply H9; eauto. 
  eapply In_V; eauto. 

  unfold substitute_value_ext in B. 
  destruct c'; try congruence. 
  inversion B; subst.
  generalize (domain_prop_1_aux _ _ _ H1 H2); intro.
  destruct H9 as [E1 [E2 E3]].
  generalize (H6 _ A); intro. 
  inversion H8; subst. 
  eapply (E2 s0); eauto. 
  intros. eapply H9; eauto. 
  eapply In_M; eauto. 

  eapply H3; eauto.   
Qed. 
 

  
  

Lemma domain_prop_2:
  forall o a b, weq o a b -> domain a o -> domain b o.
Proof. 
  intros. 
  inversion H; subst. 
  inversion H0; subst. 
  eapply Dom; eauto.
  intros. 
  generalize (H1 _ H7); intro. 
  rewrite <- H10 in H8.
  generalize (H4 _ H7 _ H8); intro. 
  generalize (H11 _ H9); intro. 
  trivial. 

  intros. 
  rewrite <- H2 in H7.
  generalize (H5 _ H7); intro. 
  trivial. 
  
  intros. 
  rewrite <- H3 in H7.
  generalize (H6 _ H7); intro.
  generalize (H9 _ H8); intro.
  trivial. 
Qed.   



Lemma subst_obs:
  forall obs x y, 
  (forall r : positive, In r obs -> (file x) ! r = (file y) ! r) -> mem x = mem y ->
  (forall v, (forall r, In_value r v -> In r obs) -> substitute_value v (file x) (mem x) = substitute_value v (file y) (mem y)) /\
  (forall v, (forall r, In_mem r v -> In r obs) ->   substitute_memory v (file x) (mem x) = substitute_memory v (file y) (mem y)) /\
  (forall v, (forall r, In_value_list r v -> In r obs) ->   substitute_value_list v (file x) (mem x) = substitute_value_list v (file y) (mem y)).
Proof. 
  intros obs x y FILE MEM.
    eapply (symbolic_combined_ind 
       (fun v => (forall r, In_value r v -> In r obs) ->substitute_value v (file x) (mem x) = substitute_value v (file y) (mem y))
       (fun v => (forall r, In_mem r v -> In r obs) ->substitute_memory v (file x) (mem x) = substitute_memory v (file y) (mem y))
       (fun v => (forall r, In_value_list r v -> In r obs) ->substitute_value_list v (file x) (mem x) = substitute_value_list v (file y) (mem y))
 ); eauto; intros; simpl.
  unfold find. rewrite FILE. trivial. apply H. apply In_reg; auto.  
  rewrite H. trivial. intros. apply H0. apply In_op; auto.  
  rewrite H. rewrite H0. trivial. intros. apply H1. apply In_load_2; auto. 
      intros. apply H1. apply In_load_1; auto.   
  rewrite H. rewrite H0. rewrite H1. trivial.
  intros. apply H2. apply In_store_3; auto.
  intros. apply H2. apply In_store_1; auto.
  intros. apply H2. apply In_store_2; auto.
  rewrite H. rewrite H0. trivial.
  intros. apply H1. apply In_cons_2; auto. 
  intros. apply H1. apply In_cons_1; auto.   
Qed.   

Lemma obs_rewrite_left : forall o x y z, domain z o -> weq o x y -> weq o (x ^^ z) (y ^^ z).
Proof. 
  intros. 
  inversion H; subst. 
  inversion H0; subst. 
  eapply Seq_weak; eauto.

  intros. 
  simpl. repeat (rewrite PTree.fold_spec).
  generalize (H1 x0 H7); intro. 
  case_eq ((file z) ! x0); intros.

  generalize (H8 s H9); intro. 
  generalize (PTree.elements_correct _ _ H9); intro.
  generalize (PTree.elements_keys_norepet (file z)); intro. 
  generalize (elements_fold (fun v => substitute_value v (file x) (mem x)) _ _ _ (file x) H11 H12); intro.
  generalize (elements_fold (fun v => substitute_value v (file y) (mem y)) _ _ _ (file y) H11 H12); intro.
  rewrite H13. rewrite H14. 
  generalize (subst_obs _ _ _ H4 H5); intro.
  destruct H15 as [A [B C]]. 
  rewrite A; auto. 

  assert (~ In x0 (map (fst (A:=positive) (B:=symbolic_value)) (PTree.elements (file z)))).
  intuition.
  generalize (elements_2 _ _ H10); intro. destruct H11.  
  generalize (PTree.elements_complete _ _ _ H11); intro.
  congruence. 
  generalize (elements_fold_1 _ (fun v => substitute_value v (file x) (mem x)) _ (file x) H10); intro.
  generalize (elements_fold_1 _ (fun v => substitute_value v (file y) (mem y)) _ (file y) H10); intro.  
  rewrite H11. rewrite H12. apply H4; auto. 
  
  simpl. 
  generalize (subst_obs _ _ _ H4 H5); intro.
  destruct H7 as [A [B C]]. 
  rewrite B. trivial. 
  intros. eapply H2; eauto. 
 
  (* constraints *)
  unfold Constraints.Equal. intros. 
  unfold Constraints.Equal in H6.
  generalize (H6 a); intro IMP. destruct IMP. 
  
  split. 

  intro.
  generalize (cons_get _ _ _ H9); intro.
  destruct H10.
  destruct H10 as [c' [A B]].
  generalize (subst_obs o x y H4 H5); intro.
  destruct H10 as [D [E F]]. 
  destruct c'. 
  simpl in B. 
  destruct a; inversion B; subst.
  rewrite D. 
  eapply cons_get'; eauto.
  intros. eapply H3; eauto.
  eapply In_V; eauto.
  simpl in B. 
  destruct a; inversion B; subst.
  rewrite E. 
  eapply cons_get'; eauto.
  intros. eapply H3; eauto.
  eapply In_M; eauto.  
  generalize (H7 H10); intro. 
  simpl. 
  eapply Constraints.union_2; eauto.  

  intro.
  generalize (cons_get _ _ _ H9); intro.
  destruct H10.
  destruct H10 as [c' [A B]].
  generalize (subst_obs o x y H4 H5); intro.
  destruct H10 as [D [E F]]. 
  destruct c'. 
  simpl in B. 
  destruct a; inversion B; subst.
  rewrite <- D. 
  eapply cons_get'; eauto.
  intros. eapply H3; eauto.
  eapply In_V; eauto.
  simpl in B. 
  destruct a; inversion B; subst.
  rewrite <- E. 
  eapply cons_get'; eauto.
  intros. eapply H3; eauto.
  eapply In_M; eauto.  
  generalize (H8 H10); intro. 
  simpl. 
  eapply Constraints.union_2; eauto. 


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










 
 
 
