(** the proof of semantics preservation for Label Cleaning *)

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
Require Import LabelCleaning.

(** trois petites proprietes utiles *)

Lemma incl_prop:
  forall (i : instruction) c l,
  incl (i :: c) l -> incl c l.
Proof. 
  intros. 
  unfold incl in H. 
  unfold incl. 
  intros. 
  generalize (in_cons i a c H0); intro.
  eapply H; eauto. 
Qed. 
     
Lemma peq_prop:
  forall l b,
  (if peq l l then true else b) = true.
Proof. 
  intros. 
  case_eq (peq l l); intros.
  trivial. 
  congruence. 
Qed. 

Lemma find_label_prop:
  forall c c' lbl,
  find_label lbl c = Some c' ->
  incl c' c.
Proof. 
  induction c; intros. 
  simpl in H. inversion H. 
  unfold incl. intros. simpl in H. 
  case_eq (is_label lbl a); intros. 
  rewrite H1 in H. injection H; intros; subst.
  apply in_cons; eauto. 
  rewrite H1 in H. 
  generalize (IHc _ _ H); intro. 
  unfold incl in H2.  generalize (H2 a0 H0); intro.
  apply in_cons; eauto. 
Qed. 

Hint Resolve incl_prop. 
Hint Resolve peq_prop. 
Hint Resolve find_label_prop. 

(* is_targetted specification *)

Lemma is_targetted_spec_goto:
  forall lbl c,
  In (Mgoto lbl) c -> is_targetted lbl c = true.
Proof. 
  induction c; intros. 
  inversion H. 
  destruct a; try (simpl; simpl in H; destruct H; [inversion H | eapply IHc; trivial]).
  case_eq (peq lbl l); intros.
    clear H0; subst. simpl. auto.  
    simpl in H. destruct H. congruence.  simpl. rewrite H0. eapply IHc; trivial.
   case_eq (peq lbl l0); intros.
    clear H0; subst. simpl. auto. 
    simpl in H. destruct H. congruence.  simpl. rewrite H0. eapply IHc; trivial. 
Qed. 

Lemma is_targetted_spec_cond:
  forall lbl cond rl c,
  In (Mcond cond rl  lbl) c -> is_targetted lbl c = true.
Proof. 
  induction c; intros. 
  inversion H. 
  destruct a; try (simpl; simpl in H; destruct H; [inversion H | eapply IHc; trivial]).
  case_eq (peq lbl l); intros.
    clear H0; subst. simpl. auto.
    simpl in H. destruct H. congruence.  simpl. rewrite H0. eapply IHc; trivial.
   case_eq (peq lbl l0); intros.
    clear H0; subst. simpl. auto. 
    simpl in H. destruct H. congruence.  simpl. rewrite H0. eapply IHc; trivial. 
Qed.    

(* remove_labels sprecification *)

Lemma remove_labels_spec:
  forall f lbl c c',
  incl c (fn_code f) ->
  find_label lbl c = Some c' ->
  is_targetted lbl (fn_code f) = true ->
  find_label lbl (remove_labels c (fn_code f)) =
  Some (remove_labels c' (fn_code f)).
Proof.
  induction c; intros. 
  simpl in H0. inversion H0. 
  destruct a; try (simpl; eapply IHc; eauto). 
  simpl.
  case_eq (peq lbl l); intros. 
    clear H2. subst. rewrite H1. simpl. 
  assert ((if peq l l then true else false) = true).
    auto. 
  rewrite H2. simpl in H0. rewrite H2 in H0. injection H0; intros; subst; trivial.   
  case_eq (is_targetted l (fn_code f)); intros. 
    simpl. rewrite H2. eapply IHc; eauto. 
    simpl in H0. rewrite H2 in H0. trivial. 
    simpl in H0. rewrite H2 in H0. eapply IHc; eauto.    
Qed. 

(** preservation *)

Section PRESERVATION.

Variable p: program.
Let tp := clean_program p.
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (clean_fundef f).
Proof (@Genv.find_funct_transf _ _ _ clean_fundef p).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (clean_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ clean_fundef p).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ clean_fundef p).

Lemma sig_preserved:
  forall f, funsig (clean_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Definition exec_instr_prop
  (f: function) (sp: val) (parent: frame) (c: code) (rs : regset) (fr : frame)
  (m : mem) (t : trace) (c' : code) (rs' : regset) (fr' : frame) (m' : mem): Prop :=
  incl c (fn_code f) ->
  (exec_instr tge (clean_function f) sp parent (remove_labels c (fn_code f)) rs fr m t (remove_labels c' (fn_code f)) rs' fr' m' /\ incl c' (fn_code f))
  \/ ((exists lbl, head c = Some (Mlabel lbl) /\ is_targetted lbl (fn_code f) = false) 
  /\ exec_instrs tge (clean_function f) sp parent (remove_labels c (fn_code f)) rs fr m t (remove_labels c (fn_code f)) rs fr m). 

Definition exec_instrs_prop
  (f: function) (sp: val) (parent: frame) (c: code) (rs : regset) (fr : frame)
  (m : mem) (t : trace) (c' : code) (rs' : regset) (fr' : frame) (m' : mem): Prop :=
  incl c (fn_code f) -> incl c' (fn_code f) /\
  exec_instrs tge (clean_function f) sp parent (remove_labels c (fn_code f)) rs fr m t (remove_labels c' (fn_code f)) rs' fr' m'.

Definition exec_function_body_prop
    (f : function) (parent : frame) (link : val) (ra : val) (rs : regset) (m : mem) (t : trace) 
    (rs' : regset) (m' : mem): Prop :=
    exec_function_body ge f parent link ra rs m t rs' m' ->
    exec_function_body tge (clean_function f) parent link ra rs m t rs' m'.

Definition exec_function_prop
  (f : fundef) (parent : frame) (rs : regset) (m : mem) (t : trace) (rs' : regset) (m' : mem) :=
  exec_function tge (clean_fundef f) parent rs m t rs' m'. 

Scheme exec_instr_ind4 := Minimality for Machabstr.exec_instr Sort Prop
  with exec_instrs_ind4 := Minimality for Machabstr.exec_instrs Sort Prop
  with exec_function_body_ind4 := Minimality for Machabstr.exec_function_body Sort Prop
  with exec_function_ind4 := Minimality for Machabstr.exec_function Sort Prop.

Lemma clean_function_correct:
  forall f parent rs m t rs' m', 
  exec_function ge f parent rs m t rs' m' ->
  exec_function_prop f parent rs m t rs' m'.
Proof. 
  apply (exec_function_ind4 ge
                                              exec_instr_prop
                                              exec_instrs_prop
                                              exec_function_body_prop
                                              exec_function_prop); red; intros; simpl.  
  (* Mlabel *) 
  case_eq (is_targetted lbl (fn_code f)); intros.   
  left. split. try eapply exec_Mlabel; eauto. eauto.  
  right. split. exists lbl. split; trivial.   eapply exec_refl; eauto. 
  (* Mgetstack *)
  left. split. constructor; eauto. eauto.
  (* Msetstack *)
  left. split. constructor; eauto. eauto. 
  (* Mgetparam *)
  left. split. constructor; eauto. eauto.
  (* Mop *)
  left. split. constructor; eauto.
  rewrite (eval_operation_preserved symbols_preserved). trivial. eauto. 
  (* Mload *)
  left. split.  eapply exec_Mload; eauto. 
  rewrite (eval_addressing_preserved symbols_preserved). trivial.
  eauto. 
  (* Mstore *)
  left. split. eapply exec_Mstore; eauto. 
  rewrite (eval_addressing_preserved symbols_preserved). trivial.
  eauto.
  (* Mcall *)
  left. split.  eapply exec_Mcall; eauto. 
  destruct ros.
  simpl. eapply functions_translated; eauto.
  simpl. rewrite symbols_preserved. 
  simpl in H. 
  case_eq (Genv.find_symbol ge i); intros. 
  rewrite H3 in H. eapply function_ptr_translated; eauto. 
  rewrite H3 in H. inversion H.
  eapply H1; eauto.
  eauto.
  (* Malloc *)
  left. split.  eapply exec_Malloc; eauto. eauto.
  (* Mgoto *)
  left. split. eapply exec_Mgoto; eauto. simpl.
  eapply remove_labels_spec; eauto.
  unfold incl. intros; trivial.
  assert (In (Mgoto lbl) (fn_code f)). 
    unfold incl in H0.
    assert (Mgoto lbl = Mgoto lbl \/ In (Mgoto lbl) c). 
    left. trivial. 
    generalize (H0 (Mgoto lbl) H1); intro. trivial.
    eapply is_targetted_spec_goto; eauto. 
    eauto. 
  (* Mcondtrue *)
  left. split. eapply exec_Mcond_true; eauto. simpl. 
  eapply remove_labels_spec; eauto.
  unfold incl. intros; trivial.
  assert (In (Mcond cond args lbl) (fn_code f)). 
    unfold incl in H0.
    assert (Mcond cond args lbl = Mcond cond args lbl \/ In (Mcond cond args lbl) c). 
    left. trivial. 
    generalize (H1 (Mcond cond args lbl) H2); intro. trivial.
    eapply is_targetted_spec_cond; eauto. 
    eauto. 
  (* Mcondfalse *)
  left. split.  eapply exec_Mcond_false; eauto.
  eauto.
  (* refl *) 
  split; trivial. eapply exec_refl; eauto. 
  (* one *)
  red in H0.
  generalize (H0 H1); intro. 
  destruct H2. 
  destruct H2. split; trivial.  
  eapply exec_one; eauto. 
  destruct H2. destruct H2 as [lbl [F G]].
  assert (c = Mlabel lbl :: c').
    unfold head in F. case_eq c; intros.
    subst. inversion F. 
    subst. injection F; intros; subst. 
    inversion H; subst.  trivial.       
  rewrite H2 in H1.
  split. eauto.
  subst. inversion H; subst. simpl. simpl in G. rewrite G.  eapply exec_refl; eauto. 
  (* trans *)
  red in H0. red in H2.
  generalize (H0 H4); intro. destruct H5. generalize (H2 H5); intro. destruct H7. 
  split; trivial. eapply exec_trans; eauto. 
  (* function body *)
  red in H3. eapply exec_funct_body; eauto.
  simpl. simpl in H3.  
  assert (incl (fn_code f) (fn_code f)). unfold incl. intros; trivial. 
  generalize (H3 H5); intro. destruct H6. 
  eapply H7. 
  (* internal function *)
  red in H0. eapply exec_funct_internal; eauto. 
  (* external function *)
  eapply exec_funct_external; eauto. 
Qed.

End PRESERVATION.     
         
Theorem clean_program_correct:
  forall p tp t r,
  clean_program p = tp ->
  exec_program p t r -> 
  exec_program tp t r.
Proof. 
  intros. 
  unfold exec_program in H0.
  destruct H0 as [b [f [rs [m [A [B [C D]]]]]]].
  unfold exec_program. 
  generalize (function_ptr_translated _ _ _ B); intro.
  repeat (rewrite <- H). 
  repeat (rewrite symbols_preserved). 
  exists b; exists (clean_fundef f); exists rs ; exists m; intuition trivial.
  eapply clean_function_correct; eauto. 
  unfold clean_program.
  rewrite Genv.init_mem_transf. trivial. 
Qed.      


  
