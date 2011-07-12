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
Require Import Valcommon.  
Require Import Machtyping. 
Require Import BasicLib.

Lemma list_spec_eq : forall (x y : list typ * typ), {x = y} + {x <> y}.
Proof.
generalize typ_eq; intro.
generalize (list_typ_eq); intro. 
decide equality.
Defined.

Definition wt_instr_set (i : instruction) : bool :=
  match i with
  | Mlabel lbl => 
      true
  | Mgetstack ofs ty r => 
      if (typ_eq (mreg_type r)  ty) then true else false
  | Msetstack r ofs ty => 
      andb (if (typ_eq (mreg_type r) ty) then true else false )
       (
       if (zlt 24 (Int.signed ofs)) then true else false 
       || 
       if (zeq 24 (Int.signed ofs)) then true else false )
  | Mgetparam ofs ty r => 
      if (typ_eq (mreg_type r)  ty) then true else false
  | Mop Omove (r1 :: nil) r => 
      if (typ_eq (mreg_type r1)  (mreg_type r)) then true else false 
  | Mop Oundef nil r => 
      true
  | Mop op args res => 
      andb (if (operation_eq op Omove) then false else true )
      ( andb (if (operation_eq op Oundef) then false else true )
      (if (list_spec_eq (List.map mreg_type args, mreg_type res)  (type_of_operation op)) then true else false)) 
  | Mload chunk addr args dst =>
      andb (if (list_typ_eq (List.map mreg_type args)  (type_of_addressing addr)) then true else false )
      (if (typ_eq (mreg_type dst)  (type_of_chunk chunk)) then true else false )
  | Mstore chunk addr args src =>
      andb(if (list_typ_eq (List.map mreg_type args)  (type_of_addressing addr)) then true else false )
      (if (typ_eq (mreg_type src)  (type_of_chunk chunk)) then true else false )
  | Mcall sig ros =>
      match ros with inl r => if (typ_eq (mreg_type r) Tint) then true else false | inr s => true end 
  | Malloc => true
  | Mgoto lbl => true
  | Mcond cond args lbl => 
     if (list_typ_eq (List.map mreg_type args)  (type_of_condition cond)) then true else false 
  | Mreturn => true
  end. 

Hint Constructors wt_instr : typ.  

Lemma open_dec:
  forall (A : Set) (t1 t2 : A) (eq_dec : forall t1 t2, {t1 = t2} + {t1 <> t2}), 
  (if (eq_dec t1 t2) then true else false) = true -> t1 = t2. 
Proof. 
  intros. 
  case_eq (eq_dec t1 t2); intros. 
  trivial. 
  rewrite H0 in H. inversion H. 
Qed. 

Hint Rewrite open_dec : typ. 
Hint Unfold wt_instr_set : typ. 

Require Import Omega. 

Lemma wt_instr_prop:
  forall i, wt_instr_set i = true -> Machtyping.wt_instr i. 
Proof. 
  intros. destruct i. 


  simpl in H. generalize (open_dec _ _ _ _ H). auto with typ. 

  simpl in H. 
  generalize (andb_prop _ _ H); clear H; intro; destruct H.   
  generalize (open_dec _ _ _ _ H). intro. 
  eapply wt_Msetstack; eauto. 
  case_eq (zlt 24 (Int.signed i)); intros. omega. rewrite H2 in H0. 
  case_eq (zeq 24 (Int.signed i)); intros. omega. rewrite H3 in H0. inversion H0.   
  
  simpl in H. generalize (open_dec _ _ _ _ H). auto with typ. 

  destruct o; try (
  unfold wt_instr_set in H;
      generalize (andb_prop _ _ H); clear H; intro; destruct H;  
    generalize (andb_prop _ _ H0); clear H0; intro; destruct H0; 
    generalize (open_dec _ _ _ _ H1); intro; 
    eapply wt_Mop; eauto; discriminate; discriminate ).

    unfold wt_instr_set in H. 
    destruct l. inversion H. destruct l. 
    case_eq (typ_eq (mreg_type m0) (mreg_type m)); intros. 
    auto with typ. 
    rewrite H0 in H. inversion H. inversion H. 

    unfold wt_instr_set in H. 
    destruct l. eauto with typ. 
    generalize (andb_prop _ _ H); clear H; intro; destruct H.
    simpl in H0. inversion H0. 
    
    simpl in H. 
    generalize (andb_prop _ _ H); clear H; intro; destruct H. 
    generalize (open_dec _ _ _ _ H); intro. 
    generalize (open_dec _ _ _ _ H0); intro. eauto with typ. 
    
     simpl in H. 
    generalize (andb_prop _ _ H); clear H; intro; destruct H. 
    generalize (open_dec _ _ _ _ H); intro. 
    generalize (open_dec _ _ _ _ H0); intro. eauto with typ. 

  simpl in H. 
  case_eq s0; intros; rewrite H0 in H. 
  generalize (open_dec _ _ _ _ H); intro. eauto with typ. 
  eauto with typ. 

  eauto with typ. 
  
  eauto with typ. 

  eauto with typ. 

  simpl in H. 
  generalize (open_dec _ _ _ _ H); intro. eauto with typ. 

  eauto with typ. 
Qed. 

Fixpoint wt_code_set (c : code) {struct c} : bool :=
  match c with
  | nil => true
  | i :: l => wt_instr_set i && wt_code_set l
  end. 

Definition lteq (n m : Z) : bool :=
  (if (zlt n m) then true else false) || (if (zeq n m) then true else false). 

Definition wt_function_set (f : function) : bool :=
  andb (wt_code_set f.(fn_code)) 
  (andb (lteq 0 f.(fn_stacksize)) 
  (andb (lteq 24 f.(fn_framesize)) (lteq f.(fn_framesize) (-Int.min_signed)))).
  

Lemma open_zlt:
  forall n m,
  (if (zlt n m) then true else false) = true -> n <= m.
Proof. 
  intros. 
  case_eq (zlt n m); intros. omega. rewrite H0 in H. congruence.   
Qed. 

Lemma wt_code_prop:
  forall c instr, 
  wt_code_set c = true ->
  In instr c ->
  wt_instr instr.
Proof. 
  induction c; intros. 
  inversion H0. 
  simpl in *|-. 
  generalize (andb_prop _ _ H); clear H; intro. 
  destruct H. destruct H0. 

  subst. eapply wt_instr_prop; eauto. 
  eapply IHc; eauto. 
Qed. 
  

Lemma wt_function_prop:
  forall f,
  wt_function_set f = true -> wt_function f. 
Proof. 
  intros. 
  unfold wt_function_set in H. 
  generalize (andb_prop _ _ H); clear H; intro; destruct H. 
  generalize (andb_prop _ _ H0); clear H0; intro; destruct H0. 
  generalize (andb_prop _ _ H1); clear H1; intro; destruct H1. 
  unfold lteq in *|-. 
  generalize (orb_prop _ _ H0); clear H0; intro; 
  generalize (orb_prop _ _ H1); clear H1; intro; 
  generalize (orb_prop _ _ H2); clear H2; intro; 
  destruct H0 ; destruct H1 ; destruct H2;   
  try (generalize (open_dec _ _ _ H0));  
  try (generalize (open_dec _ _ _ H1)); 
  try (generalize (open_dec _ _ _ H2)); 
  try (generalize (open_zlt _ _ H0)); 
  try (generalize (open_zlt _ _ H1)); 
  try (generalize (open_zlt _ _ H2)); 
  try intros; 
  eapply mk_wt_function; eauto; try omega;
  intros; try (eapply wt_code_prop); eauto; try omega.

  case_eq (zeq (fn_framesize f) (- Int.min_signed)); intros.
    omega. rewrite H5 in H2. inversion H2. 

  case_eq (zeq 24 (fn_framesize f)); intros. 
    omega. rewrite H5 in H1. inversion H1.

  case_eq (zeq 24 (fn_framesize f)); intros. 
    omega. rewrite H4 in H1. inversion H1.    

  case_eq (zeq (fn_framesize f) (- Int.min_signed)); intros.
    omega. rewrite H4 in H2. inversion H2.

  case_eq (zeq 0 (fn_stacksize f)); intros.  
    omega. rewrite H5 in H0. inversion H0. 

  case_eq (zeq 0 (fn_stacksize f)); intros.  
    omega. rewrite H4 in H0. inversion H0.

   case_eq (zeq (fn_framesize f) (- Int.min_signed)); intros.
    omega. rewrite H4 in H2. inversion H2.

 case_eq (zeq 0 (fn_stacksize f)); intros.  
    omega. rewrite H4 in H0. inversion H0.

  case_eq (zeq 24 (fn_framesize f)); intros. 
    omega. rewrite H4 in H1. inversion H1.    

 case_eq (zeq 0 (fn_stacksize f)); intros.  
    omega. rewrite H3 in H0. inversion H0.

  case_eq (zeq 24 (fn_framesize f)); intros. 
    omega. rewrite H3 in H1. inversion H1.    

  case_eq (zeq (fn_framesize f) (- Int.min_signed)); intros.
    omega. rewrite H3 in H2. inversion H2.     
Qed. 

Fixpoint loc_args_ver (l : list loc) {struct l} : bool :=
  match l with
  | S _ :: _ => false
  | R _ :: l => loc_args_ver l 
  | nil => true
  end. 

Lemma loc_args_ver_correct:
  forall l,
  loc_args_ver l = true -> forall sl, ~In (S sl) l.
Proof. 
  induction l; intros. 
  simpl in H. auto. 
  simpl in H. case_eq a; intros. 
  subst. generalize (IHl H); intro. 
  generalize (H0 sl); intro. 
  simpl. intro. destruct H2. inversion H2. 
  congruence. 
  rewrite H0 in H. subst. inversion H. 
Qed. 
   
  

Definition wt_fundef_set (f : fundef) : bool :=
  match f with
  | Internal f => wt_function_set f
  | External f => loc_args_ver (Conventions.loc_arguments f.(ef_sig))
  end. 

Lemma wt_fundef_prop:
  forall f, wt_fundef_set f = true -> wt_fundef f. 
Proof. 
  intros. destruct f. 
  simpl in H. eapply wt_function_internal; eauto. 
  eapply wt_function_prop; eauto. 

  eapply wt_fundef_external; eauto. 
Qed. 
  
Fixpoint wt_fundef_list_set ( l : list (ident * fundef)) {struct l} : bool :=
  match l with 
  | nil => true
  | (i,f) :: l => andb (wt_fundef_set f) (wt_fundef_list_set l)
  end. 

Lemma wt_fundef_list_prop:
  forall l,
  wt_fundef_list_set l = true ->
  forall i f, In (i, f) l -> wt_fundef f.
Proof. 
  induction l; intros. 
  inversion H0. 
  inversion H0.  
  subst. simpl in H. 
  generalize (andb_prop _ _ H). intro. destruct H1. 
  eapply wt_fundef_prop; eauto. 

  simpl in H. 
  eapply IHl; eauto. 
  case_eq (wt_fundef_list_set l); intros; trivial. 
  rewrite H2 in H. inversion H. 
  case_eq a; intros. subst. case (wt_fundef_set f0). trivial. trivial.    
Qed. 

Definition typer (p : program) : bool :=
  wt_fundef_list_set (p.(prog_funct)). 

Theorem typer_correct:
  forall p,
  typer p = true -> wt_program p. 
Proof. 
  intros. 
  unfold wt_program. intros. 
  eapply wt_fundef_list_prop; eauto. 
  unfold typer in H. 
   trivial.  
Qed. 


     