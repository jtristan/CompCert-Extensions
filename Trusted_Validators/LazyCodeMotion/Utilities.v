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
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import DecidableType. 
Require Import FSetWeakInterface. 
Require Import FSetWeakFacts. 
Require Import FSetWeakProperties. 
Require Import FSetWeakList. 
Require Import Errors. 

Fixpoint mem elt l  {struct l} : bool := 
  match l with
  | nil => false
  | x :: l => if peq x elt then true else false || mem elt l
  end. 

Inductive instruction_mod_succ: Set :=
  | MInop: instruction_mod_succ
  | MIop: operation -> list reg -> reg -> instruction_mod_succ
  | MIload: memory_chunk -> addressing -> list reg -> reg -> instruction_mod_succ
  | MIstore: memory_chunk -> addressing -> list reg -> reg -> instruction_mod_succ
  | MIcall: signature -> reg + ident -> list reg -> reg -> instruction_mod_succ
  | MItailcall: signature -> reg + ident -> list reg -> instruction_mod_succ
  | MIalloc: reg -> reg -> instruction_mod_succ
  | MIcond: condition -> list reg -> instruction_mod_succ
  | MIreturn: option reg -> instruction_mod_succ.

Parameter inst_ms_eq : forall (i1 i2 : instruction_mod_succ), {i1 = i2} + {i1 <> i2}. 

Definition mask_succ (i : instruction) : instruction_mod_succ :=
  match i with
  | Inop s => MInop 
  | Iop op args res s => MIop op args res 
  | Iload chunk addr args dst s => MIload chunk addr args dst 
  | Istore chunk addr args src s => MIstore chunk addr args src 
  | Icall sig ros args res s => MIcall sig ros args res 
  | Itailcall sig ros args => MItailcall sig ros args
  | Ialloc arg res s => MIalloc arg res 
  | Icond cond args ifso ifnot => MIcond cond args
  | Ireturn optarg => MIreturn optarg
  end. 

Axiom inst_eq : forall (o1 : instruction) o2, {o1 = o2} + {o1 <> o2}. 
Axiom op_eq : forall (o1 : operation) o2, {o1 = o2} + {o1 <> o2}. 

(* is_non_standard determine si un registre a ete introduit par une transformation *)

Definition is_non_standard (regs : list reg) (i : option instruction) : bool :=
  match i with
  | Some (Iop op rl r s) => if mem r regs then false else true
  | Some (Iload chunk addr args dst s) => if mem dst regs then false else true
  | _ => false
  end.

(* regs renvoie la liste des registres ecrits *)

Definition regs (i : RTL.instruction) : list reg := 
  match i with
  | Inop s =>  nil
  | Iop op lr r s => cons r lr 
  | Iload mc ad lr r s => cons r lr
  | Istore mc ad lr r s => cons r lr
  | Icall si ri lr r s => match ri with | inl rr => cons rr (cons r lr) | inr _ => cons r lr end
  | Itailcall si ri lr => match ri with | inl rr => cons rr lr | inr _ => lr end
  | Ialloc r1 r2 s => cons r2 (cons r1 nil)
  | Icond c lr s1 s2 => lr
  | Ireturn orr => match orr with | None => nil | Some r => cons r nil end
  end. 

(* compute_standard_regs calcule les registres du code initial*)
Definition compute_standard_regs (g : RTL.code) : list reg :=
  PTree.fold (fun l n i => l ++ regs i) g nil.

Definition count_nodes (g : RTL.code) : nat :=
  PTree.fold (fun count _ _ => S count) g O.

Inductive approx : Set := 
    | Novalue
    | Unknown
    | Op : operation -> list reg -> approx
    | Load : memory_chunk -> addressing -> list reg -> approx.

Module Approx <: SEMILATTICE_WITH_TOP.
  Definition t := approx.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).
  Axiom eq_dec: forall (x y: t), {x=y} + {x<>y}.

  Definition beq (x y: t) := if eq_dec x y then true else false.
  Lemma beq_correct: forall x y, beq x y = true -> x = y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.
  Definition ge (x y: t) : Prop :=
    x = Unknown \/  y = Novalue \/ x = y.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; tauto.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; intuition congruence.
  Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold eq, ge; intros; congruence.
  Qed.
  Definition bot := Novalue.
  Definition top := Unknown.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot; tauto.
  Qed.
  Lemma ge_top: forall x, ge top x.
  Proof. 
    unfold ge, bot; tauto.
  Qed.
  Definition lub (x y: t) : t :=
    if eq_dec x y then x else
    match x, y with
    | Novalue, _ => y
    | _, Novalue => x
    | _, _ => Unknown
    end.
  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq; intros.
    case (eq_dec x y); case (eq_dec y x); intros; try congruence.
    destruct x; destruct y; auto.
  Qed.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub; intros.
    case (eq_dec x y); intro.
    apply ge_refl. apply eq_refl.
    destruct x; destruct y; unfold ge; tauto.
  Qed.
End Approx.

Lemma not_list: forall (e : reg) e' l, ~ In e (e' :: l) -> e <> e' /\ ~ In e l.
Proof. 
  intros. 
  generalize (peq e e'); intros. 
  destruct H0. 
  simpl in H. 
  destruct H. left. symmetry. trivial. 
  split; trivial. 
  simpl in H. intuition. 
Qed. 

Lemma mem_false : 
  forall r l, mem r l = false -> ~ In r l. 
Proof. 
  induction l.  
  intros. simpl. intuition. 
  intros. simpl. 
  simpl in H. 
  case_eq (peq a r); intros.
  rewrite H0 in H. inversion H. 
  rewrite H0 in H. generalize (IHl H); intro. 
  intro. destruct H2. congruence. 
  congruence. 
Qed. 
  
Lemma extended_gso:
  forall l rs (res : reg) (v : val),
  ~ In res l -> (rs # res <- v) ## l = rs ## l.
Proof. 
  induction l; intros. 
  simpl. trivial. 
  simpl.
  generalize (not_list res a l H); intro NL. destruct NL.  
  rewrite Regmap.gso; auto. 
  generalize (IHl rs res v H1); intro.
  rewrite H2. trivial.  
Qed.

Lemma in_prop:
  forall (A : Set) (e : A) l l', In e l -> In e (l ++ l').
Proof. 
  induction l; intros. 
  simpl in H. inversion H.
  simpl in H. simpl. destruct H. 
  left; trivial. 
  right. eapply IHl; eauto. 
Qed.  

Lemma in_prop':
  forall (A : Set) (e : A) l l', In e l' -> In e (l ++ l').
Proof. 
  induction l; intros. 
  simpl in H. simpl. trivial.
  simpl. right. eapply IHl; eauto. 
Qed.  

Lemma fold_concat:
  forall r l acc f, 
  In r acc ->
  In r (fold_left (fun (a : list reg) (p : positive * instruction) => a ++ f p) l acc). 
Proof. 
  induction l; intros. 
  simpl. trivial. 
  simpl. eapply IHl; eauto.
  eapply in_prop; eauto.
Qed.     

Lemma regs_prop_aux:
  forall l r i pc l', 
  In r (regs i) -> 
  In (pc, i) l ->
  In r
  (fold_left
     (fun (a : list reg) (p : positive * instruction) =>
      a ++ regs (snd p)) l l').
Proof. 
  induction l; intros. 
  simpl in H0. inversion H0. 
  simpl in H0. 
  destruct H0. 
  subst. simpl. 
        eapply fold_concat; eauto.
         eapply in_prop'; eauto. 
  assert (a :: l = cons a nil ++ l) by trivial. 
  rewrite H1. rewrite fold_left_app. simpl.  
  eapply IHl; eauto. 
Qed. 

Lemma regs_prop : forall (g : RTL.code) pc i, 
    g ! pc =  Some i -> 
    forall r, In r (regs i) -> In r (compute_standard_regs g). 
Proof. 
  intros. 
  unfold compute_standard_regs. 
  rewrite PTree.fold_spec. 
  generalize (PTree.elements_correct _ _  H); intro.
  eapply regs_prop_aux; eauto.    
Qed.  

Record std_state : Set := mk_std_state {
  fu : function;
  sp : val;
  rs : regset;
  m : Mem.mem
}. 

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

Tactic Notation "instantiate" hyp(H) "with" hyp(H') :=
  generalize (H _ _ H'); clear H H'; intro H.   

Lemma R_or_1 : forall x y : bool,
  (x || y) = true -> x = true \/ y = true. 
Proof. 
  intros. 
  case_eq (x); intros. 
  left; trivial. 
  rewrite H0 in H. 
  simpl in H. right. trivial. 
Qed.

Lemma R_and_1 : forall x y,
  x && y = true -> x = true /\ y = true.
Proof. 
  intros. 
  case_eq x; intros; subst.
  simpl in H. auto. 
  simpl in H. congruence.  
 Qed.


Tactic Notation "destructb_one" constr(H) := 

    match type of H with

    | (_ || _) = true => destruct (@R_or_1 _ _ H)

    | (_ && _) = true => destruct (@R_and_1 _ _ H)
    end.

Tactic Notation "destructb" constr(H0) := 
  let rec go H := 
    let H1 := fresh in let H2 := fresh in 

    match type of H with

    | (_ || _) = true => destruct (@R_or_1 _ _ H) as [H1|H1]; [ go H1 | go H1 ]

    | (_ && _) = true => destruct (@R_and_1 _ _ H) as [H1 H2]; go H1; go H2
    | _ => try tauto
    end in
  go H0.

 