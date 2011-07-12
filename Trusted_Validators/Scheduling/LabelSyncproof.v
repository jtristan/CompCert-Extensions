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


(** the proof of semantics preservation for Label Synchronization *)

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
Require Import LabelCleaningproof. 
Require Import MachToTreeVal. 
Require Import MachToTreeVal_util.
Require Import LabelSync.

(** lemmes *)

Lemma suff_in:
  forall c i glob,
  suffix (i :: c) glob -> In i glob.
Proof.  
  destruct c; intros.
  inversion H. subst. clear H. induction x; simpl. left; trivial. right; trivial. 
  inversion H. subst. clear H. induction x; simpl. left; trivial. right; trivial. 
Qed. 
  
Lemma targets_in:
  forall lbl glob, 
  is_targetted lbl glob = true -> In lbl (get_labels glob).
Proof. 
  induction glob; intros. 
  simpl in H. inversion H. 
  destruct a. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto. 
  simpl in *|-; simpl; eapply IHglob; eauto.

  simpl in H. 
  case_eq (peq lbl l); intros. clear H0. subst. 
  case_eq (peq l l); intros.
  clear H0; subst. simpl. left.  trivial.
  rewrite H0 in H. simpl. right. eapply IHglob; eauto.
  rewrite H0 in H. simpl . right. eapply IHglob; eauto.
 
  simpl in H. 
  case_eq (peq lbl l0); intros. clear H0. subst. 
  case_eq (peq l0 l0); intros.
  clear H0; subst. simpl. left.  trivial.
  rewrite H0 in H. simpl. right. eapply IHglob; eauto.
  rewrite H0 in H. simpl . right. eapply IHglob; eauto.

  simpl in *|-; simpl; eapply IHglob; eauto.  
Qed. 

Lemma freshness_aux:
  forall lbl c c' glob s,
  s.(base_set) = get_labels (glob) ->
  suffix c glob ->
  is_targetted lbl glob = true ->
  find_label lbl c = Some c' ->
 exists s',
  find_label lbl (sync_code c s) = Some (sync_code c' s').
Proof. 
  induction c; intros.
  simpl in H2. inversion H2. 
  destruct a.
  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_getstack; eauto. 
  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_setstack; eauto. 
  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_getparam; eauto. 
  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_op; eauto. 
  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_load; eauto. 
  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_store; eauto. 

  (* call *)
  simpl. 
  remembertac expr  (sync_code c
               (mkstate (Psucc (Psucc (fresh_label s))) (base_set s)
                  (proof_gen (base_set s) (Psucc (fresh_label s))
                     (proof_gen (base_set s) (fresh_label s) (proof s))))). 
  case_eq (peq lbl (fresh_label s)); intros. 
  generalize s.(proof). intro. 
  assert (In lbl s.(base_set)). rewrite H. eapply targets_in; eauto.  
  generalize (H4 lbl H5); intro.  generalize (Plt_ne _ _ H6); intro. congruence. 
  
  case_eq (peq lbl (Psucc (fresh_label s))); intros. 
  generalize s.(proof). intro. 
  assert (In lbl s.(base_set)). rewrite H. eapply targets_in; eauto.  
  generalize (H5 lbl H6); intro. rewrite e in H7. generalize (Plt_trans_succ _ _ H7); intro. 
  generalize (Plt_ne _ _ H8); intro. congruence. 
  simpl in *|-. 
  assert (suffix c glob). inversion H0. exists (x ++ Mcall s0 s1 :: nil). 
  rewrite app_ass. simpl; trivial.
  assert (base_set (mkstate (Psucc (Psucc (fresh_label s))) (base_set s)
               (proof_gen (base_set s) (Psucc (fresh_label s)) 
                  (proof_gen (base_set s) (fresh_label s) (proof s)))) = get_labels glob).
  simpl. trivial.  
  generalize (IHc _ _ _ H6 H5 H1 H2); intro. 
  subst. eapply IHc; eauto. 


  simpl in *|-; simpl; eapply IHc; eauto. eapply suff_alloc; eauto. 

  (* label *)

  case_eq (peq lbl l); intros. 
  clear H3. subst. simpl. 
  case_eq (if peq l l then true else false); intros.
  simpl in H2.
  rewrite H3 in H2. inversion H2. exists s. trivial. 
  simpl in H2. rewrite H3 in H2. eapply IHc; eauto. eapply suff_lab; eauto. 
  simpl. rewrite H3. eapply IHc; eauto. eapply suff_lab; eauto.  
  simpl in H2. rewrite H3 in H2. trivial. 
 
  simpl in *|-. simpl. eapply IHc; eauto. 
  inversion H0. exists (x ++ Mgoto l :: nil). rewrite app_ass. simpl; trivial. 

  simpl in *|-. simpl. eapply IHc; eauto. 
  inversion H0. exists (x ++ Mcond c0 l l0 :: nil). rewrite app_ass. simpl; trivial. 

  simpl in *|-. simpl. 
  case_eq (peq lbl (fresh_label s)); intros; try eapply IHc; eauto.
  
  generalize s.(proof). intro. 
  assert (In lbl s.(base_set)). rewrite H. eapply targets_in; eauto.  
  generalize (p lbl H4); intro.  generalize (Plt_ne _ _ H5); intro. congruence. 

  inversion H0. exists (x ++ Mreturn :: nil). rewrite app_ass. simpl. trivial.
Qed.

Lemma freshness:
  forall lbl c' glob s,
  s.(base_set) = get_labels (glob) ->
  is_targetted lbl glob = true ->
  find_label lbl glob = Some c' ->
 exists s',
  find_label lbl (sync_code glob s) = Some (sync_code c' s').
Proof. 
  intros. eapply freshness_aux; eauto.
  exists (@nil instruction). 
  trivial. 
Qed. 
 
(** preservation *) 

Section PRESERVATION.

Variable p: program.
Let tp := sync_program p.
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (sync_fundef f).
Proof (@Genv.find_funct_transf _ _ _ sync_fundef p). 

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (sync_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ sync_fundef p).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ sync_fundef p).

Lemma sig_preserved:
  forall f, funsig (sync_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Definition mem := Mem.mem. 

Definition exec_instr_prop
  (f: function) (sp: val) (parent: frame) (c: code) (rs : regset) (fr : frame)
  (m : mem) (t : trace) (c' : code) (rs' : regset) (fr' : frame) (m' : mem): Prop :=
  base_set (snd (bind (init_state (get_labels (fn_code f))))) = get_labels (fn_code f) ->
  suffix c (fn_code f) ->
  (forall s, exists s',
  exec_instrs tge (sync_function f) sp parent (sync_code c s) rs fr m t (sync_code c' s') rs' fr' m') 
  /\ suffix c' (fn_code f).
 
Definition exec_instrs_prop
  (f: function) (sp: val) (parent: frame) (c: code) (rs : regset) (fr : frame)
  (m : mem) (t : trace) (c' : code) (rs' : regset) (fr' : frame) (m' : mem): Prop :=
  base_set (snd (bind (init_state (get_labels (fn_code f))))) = get_labels (fn_code f) ->
  suffix c (fn_code f) ->
  (forall s, exists s',
  exec_instrs tge (sync_function f) sp parent (sync_code c s) rs fr m t (sync_code c' s') rs' fr' m')
  /\ suffix c' (fn_code f). 

Definition exec_function_body_prop
    (f : function) (parent : frame) (link : val) (ra : val) (rs : regset) (m : mem) (t : trace) 
    (rs' : regset) (m' : mem): Prop :=
    exec_function_body tge (sync_function f) parent link ra rs m t rs' m'.

Definition exec_function_prop
  (f : fundef) (parent : frame) (rs : regset) (m : mem) (t : trace) (rs' : regset) (m' : mem) :=
  exec_function tge (sync_fundef f) parent rs m t rs' m'. 

Scheme exec_instr_ind4 := Minimality for Machabstr.exec_instr Sort Prop
  with exec_instrs_ind4 := Minimality for Machabstr.exec_instrs Sort Prop
  with exec_function_body_ind4 := Minimality for Machabstr.exec_function_body Sort Prop
  with exec_function_ind4 := Minimality for Machabstr.exec_function Sort Prop.

Lemma sync_function_correct:
  forall f parent rs m t rs' m', 
  exec_function ge f parent rs m t rs' m' ->
  exec_function_prop f parent rs m t rs' m'.
Proof. 
  apply (exec_function_ind4 ge
                                              exec_instr_prop
                                              exec_instrs_prop
                                              exec_function_body_prop
                                              exec_function_prop); red; intros; simpl; intuition.    
  (* Mlabel *)  
  exists s; eapply exec_one; eapply exec_Mlabel; eauto.
  eapply suff_lab; eauto. 
  (* Mgetstack *)
  exists s; eapply exec_one; eapply exec_Mgetstack; eauto.
  eapply suff_getstack; eauto. 
  (* Msetstack *)
  exists s; eapply exec_one; eapply exec_Msetstack; eauto.
  eapply suff_setstack; eauto. 
  (* Mgetparam *)
  exists s; eapply exec_one; eapply exec_Mgetparam; eauto.
  eapply suff_getparam; eauto. 
  (* Mop *)
  rewrite <- (eval_operation_preserved symbols_preserved) in H. 
  exists s; eapply exec_one; eapply exec_Mop; eauto. 
  eapply suff_op; eauto. 
  (* Mload *)
  rewrite <- (eval_addressing_preserved symbols_preserved) in H.
  exists s; eapply exec_one; eapply exec_Mload; eauto. 
  eapply suff_load; eauto. 
  (* Mstore *)
  rewrite <- (eval_addressing_preserved symbols_preserved) in H.
  exists s; eapply exec_one; eapply exec_Mstore; eauto.
  eapply suff_store; eauto. 
  (* Mcall *)
  exists (snd (bind (snd (bind s)))). 
  remembertac expr (mkstate (Psucc (Psucc (fresh_label s))) (base_set s)
                 (proof_gen (base_set s) (Psucc (fresh_label s))
                    (proof_gen (base_set s) (fresh_label s) (proof s)))). 
  simpl. 
  assert (exec_instrs tge (sync_function f) sp parent (Mlabel (fresh_label s)
   :: Mcall sig ros
      :: Mlabel (Psucc (fresh_label s))
         :: sync_code c (expr)) rs fr m E0
         (Mcall sig ros
      :: Mlabel (Psucc (fresh_label s))
         :: sync_code c (expr)) rs fr m).
         eapply exec_one; eauto. 
         eapply exec_Mlabel; eauto.
  assert (exec_instrs tge (sync_function f) sp parent
     (Mcall sig ros
      :: Mlabel (Psucc (fresh_label s))
         :: sync_code c (expr)) rs fr m t 
         (Mlabel (Psucc (fresh_label s))
         :: sync_code c (expr)) rs' fr m').
         eapply exec_one; eauto. 
         eapply exec_Mcall; eauto. 
  destruct ros. simpl in H. simpl. eapply functions_translated; eauto.
  simpl in H. simpl. rewrite symbols_preserved. 
  destruct (Genv.find_symbol ge i). eapply function_ptr_translated; eauto.
  inversion H. inversion H1. eapply exec_funct_internal; eauto.
  eapply exec_funct_external; eauto. 
  assert (exec_instrs tge (sync_function f) sp parent
     (Mlabel (Psucc (fresh_label s))
         :: sync_code c (expr)) rs fr m E0
         (sync_code c (expr)) rs fr m).
           eapply exec_one; eauto. 
         eapply exec_Mlabel; eauto.
  assert (t = E0 ** t). traceEq. 
  generalize (exec_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H4 H5 H7); intro.
  assert (t = t ** E0). traceEq.
  eapply exec_trans; eauto. 
  eapply exec_one; eauto. 
  clear H7 H9. subst. eapply exec_Mlabel; eauto. 
  inversion H3. 
  unfold suffix. exists (x ++ Mcall sig ros :: nil). 
  rewrite app_ass. simpl. trivial.  
  (* Malloc *)
  exists s; eapply exec_one; eapply exec_Malloc; eauto.
  eapply suff_alloc; eauto. 
  (* Mgoto *)
  assert (is_targetted lbl (fn_code f) = true). eapply is_targetted_spec_goto; eauto. eapply suff_in; eauto. 
  generalize (freshness lbl c' (fn_code f) (snd (bind ((init_state (get_labels (fn_code f)))))) H0 H2 H); intro. 
  destruct H3 as [s' H3]. exists s'.  
  eapply exec_one; eapply exec_Mgoto. simpl. 
  case_eq (peq lbl (Psucc (get_max (get_labels (fn_code f))))); intros.
    generalize (proof ((init_state (get_labels (fn_code f))))); intro. 
    generalize (targets_in _ _ H2); intro. 
    generalize (H5 _ H6); intro. simpl in H7. clear H4. subst.   
    elimtype False. eapply Plt_strict; eauto. 
    auto. 
  eapply find_label_suff; eauto. 
  (* Mcondtrue *)
  assert (is_targetted lbl (fn_code f) = true). eapply is_targetted_spec_cond; eauto. eapply suff_in; eauto.  
  generalize (freshness lbl c' (fn_code f) (snd (bind (init_state (get_labels (fn_code f))))) H1 H3 H0); intro. 
  destruct H4 as [s' H4]. exists s'.  
  generalize (proof ((init_state (get_labels (fn_code f))))); intro. 
  generalize (targets_in _ _ H3); intro. 
  generalize (H5 _ H6); intro. simpl in H7. 
  eapply exec_one; eapply exec_Mcond_true; auto.
    simpl. 
    case_eq (peq lbl (Psucc (get_max (get_labels (fn_code f))))); intros.
    clear H8. subst. 
    elimtype False. eapply Plt_strict; eauto.
    auto. 
  eapply find_label_suff; eauto.  
  (* Mcondfalse *)
  exists s; eapply exec_one; eapply exec_Mcond_false; eauto. 
  inversion H1. exists (x ++ Mcond cond args lbl :: nil). rewrite app_ass. simpl; trivial. 
  (* refl *) 
  exists s. eapply exec_refl; eauto. 
  (* one *)
  unfold exec_instr_prop in H0.
  generalize (H0 H1 H2); intro. destruct H3. 
  generalize (H3 s); intro. destruct H5 as [s' H5]. 
  exists s'. trivial.
  unfold exec_instr_prop in H0.
  generalize (H0 H1 H2); intro. destruct H3. 
  trivial. 
  (* trans *)
  unfold exec_instrs_prop in *|-.
  generalize (H0 H4 H5); intro. destruct H6.
  generalize (H6 s); intro. destruct H8 as [s' H8]. 
  generalize (H2 H4 H7); intro. destruct H9. 
  generalize (H9 s'); intro. destruct H11 as [s'' H11]. 
  exists s''. eapply exec_trans; eauto.
    unfold exec_instrs_prop in *|-.
  generalize (H0 H4 H5); intro. destruct H6. 
  generalize (H2 H4 H7); intro. destruct H8.
  trivial. 
  (* function body *)
  unfold exec_instrs_prop in H3.
  assert (base_set (snd (bind (init_state (get_labels (fn_code f))))) = get_labels (fn_code f)).
    simpl. trivial.  
  assert (suffix (fn_code f) (fn_code f)).
    exists (@nil instruction). trivial. 
  generalize (H3 H4 H5); intro. destruct H6. 
  generalize (H6 (snd (bind (init_state (get_labels (fn_code f)))))); intro. 
  destruct H8 as [s' H8]. 
  simpl in H8. 
  remembertac expr (mkstate (Psucc (fresh_label s')) (base_set s')
                   (proof_gen (base_set s') (fresh_label s') (proof s'))).  
  generalize (exec_Mlabel tge (sync_function f) (Vptr stk (Int.repr (- fn_framesize f))) parent (fresh_label s') (Mreturn :: sync_code c expr) rs' fr3 m2); intro.
  generalize (exec_one _ _ _ _ _ _ _ _ _ _ _ _ _ H9); intro.
  assert (t = t ** E0). traceEq. 
  generalize (exec_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8 H10 H11); intro.
  unfold sync_function. simpl. 
  eapply exec_funct_body; eauto.
  eapply exec_trans; eauto.   
  remembertac begin (mkstate
                       (Psucc (Psucc (get_max (get_labels (fn_code f)))))
                       (get_labels (fn_code f))
                       (proof_gen (get_labels (fn_code f))
                          (Psucc (get_max (get_labels (fn_code f))))
                          (bootstrap_proof (get_labels (fn_code f))))). 
  simpl. eapply exec_one. eapply exec_Mlabel; eauto. 
  traceEq. 
  (* internal function *)
  eapply exec_funct_internal; eauto. 
  (* external function *)
  eapply exec_funct_external; eauto. 
Qed.

End PRESERVATION.

Theorem sync_program_correct:
  forall p tp t r,
  sync_program p = tp ->
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
  exists b; exists (sync_fundef f); exists rs ; exists m; intuition trivial.
  eapply sync_function_correct; eauto. 
  unfold sync_program.
  rewrite Genv.init_mem_transf. trivial. 
Qed.  
  
       

