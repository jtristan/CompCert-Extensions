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


(** Label Synchronizing : placing labels before trace validation *)

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
Require Import Conventions.
Require Import Mach. 
Require Import Machabstr. 

Fixpoint get_labels (c : code) {struct c} : list label :=
  match c with
  | nil => nil
  | Mgoto lbl :: c => lbl :: get_labels c
  | Mcond a b lbl :: c => lbl :: get_labels c 	
  | i :: c => get_labels c
  end. 

Record state : Set := mkstate {
  fresh_label : label;
  base_set : list label;
  proof : forall x, In x base_set -> Plt x fresh_label 
}.

Fixpoint get_max (l : list label) {struct l} : label :=
  match l with
  | nil => 1%positive 
  | i :: l => let j := get_max l in if plt i j then j else i
  end. 

Lemma proof_gen:
  forall s f,
  (forall x, In x s -> Plt x f) ->
  forall x, In x s -> Plt x (Psucc f).
Proof. 
  intros. 
  generalize (H x H0); intro. 
  eapply Plt_trans_succ; eauto. 
Qed. 

Definition bind (s : state) : (label * state) :=
  (s.(fresh_label), mkstate (Psucc s.(fresh_label)) s.(base_set) (proof_gen s.(base_set) s.(fresh_label) s.(proof))).

Lemma Plt_Psucc_monotonic:
  forall x y, Plt x y -> Plt (Psucc x) (Psucc y).
Proof.
  unfold Plt. intros. 
  repeat (rewrite Psucc_Zsucc).
  eapply Zsucc_lt_compat; eauto. 
Qed.   

Lemma Plt_Psucc_one:  
  forall x, Plt 1 (Psucc x). 
Proof. 
  unfold Plt. intros. rewrite Psucc_Zsucc.
  simpl. 
  generalize (Zgt_pos_0 x); intro. 
  generalize (Zplus_gt_compat_l _ _ 1 H); intro.
  generalize (Zgt_lt _ _ H0); intro. 
  simpl (1 + 0) in H1.
  rewrite Zpos_plus_distr.
  rewrite Zplus_comm. 
  trivial. 
Qed. 
     
Lemma Plt_inv:
  forall x y, ~ Plt x y -> Plt y x \/ x = y.
Proof. 
  unfold Plt. intros.
  generalize (Znot_lt_ge _ _ H); intro.
  generalize (Zge_le _ _ H0); intro. 
  generalize (Zle_lt_or_eq _ _ H1); intro. 
  intuition trivial. 
  right. injection H3. intuition trivial. congruence. 
Qed.  

Lemma bootstrap_proof:
  forall s,
  forall x, In x s -> Plt x (Psucc (get_max s)).
Proof. 
  induction s; intros. 
  inversion H.
  simpl in H. destruct H.  
  subst.  simpl. 
  case_eq (plt x (get_max s)); intros. eapply Plt_trans_succ; eauto. 
  eapply Plt_succ; eauto. 
  simpl. 
  case_eq (plt a (get_max s)); intros. 
    eapply IHs; eauto. 
    generalize (IHs _ H); intro. 
    generalize (Plt_succ_inv _ _ H1); intro.
    generalize (Plt_inv _ _ n); intro. 
    destruct H3. 
    destruct H2.
    generalize (Plt_succ a); intro. eapply Plt_trans; eauto. eapply Plt_trans_succ; eauto. 
    subst. eapply Plt_trans_succ; eauto. 
    subst. trivial. 
Qed. 

Definition init_state (s : list label) : state :=
  mkstate (Psucc (get_max s)) s (bootstrap_proof s).  

Fixpoint sync_code (c : code) (s : state) {struct c} : code := 
  match c with
  | nil => nil
  | Mreturn :: c => let (lbl,s') := bind s in (Mlabel lbl :: Mreturn :: sync_code c s')
  | (Mcall _ _) as i :: c => let (lbl,s') := bind s in let (lbl',s'') := bind s' in (Mlabel lbl :: i :: Mlabel lbl' :: sync_code c s'')
  | i :: c => (i :: sync_code c s)
  end. 

Definition sync_function (f : function) : function  := 
  let (lbl,s') := bind (init_state (get_labels (fn_code f))) in
  mkfunction (fn_sig f) (Mlabel lbl :: sync_code (fn_code f) s') (fn_stacksize f) (fn_framesize f).

Definition sync_fundef (f: fundef) : fundef :=
  transf_fundef sync_function f.

Definition sync_program (p: program) : program :=
  transform_program sync_fundef p.

 