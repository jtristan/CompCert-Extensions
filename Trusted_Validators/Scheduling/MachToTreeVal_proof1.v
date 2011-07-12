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
Require Import MachToTreeVal_util.

Section Val. 

Variable f : Mach.function. 
Variable cfg : Two_level_repr.function. 

Notation "a && b" := (andb a b). 

Inductive FatArrow : 
       genv -> val -> frame -> instruction -> 
       regset -> frame -> Mem.mem -> trace -> 
       regset -> frame -> Mem.mem -> Prop :=
  | Fat_intro:
    forall ge sp parent rs fr m, 
    FatArrow ge  sp parent Two_level_repr.Mreturn rs fr m E0 rs fr m 
  | Fat_push:
    forall ge sp parent instr rs fr m t lbl rs' fr' m' t' instr' rsf frf mf tf,
    exec_instruction ge (fn_body cfg) sp parent instr rs fr m t lbl rs' fr' m' ->
    (cfg_code (fn_body cfg))!lbl = Some instr' ->
    FatArrow ge  sp parent instr' rs' fr' m' t' rsf frf mf -> 
    tf = t ** t' ->
    FatArrow ge sp parent instr rs fr m tf rsf frf mf. 

Lemma linear_isFat:
  forall ge tge sp parent keys c i instr rs fr m c' rs' fr' m' tr,
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
  nbranchset i = true ->
  Machabstr.exec_instr ge f sp parent (i :: c) rs fr m tr c' rs' fr' m' ->
  validProp f keys (i :: c')instr ->
  exists instr', (validProp f keys c instr' /\ 
  (forall rsf frf mf tf, FatArrow tge sp parent instr' rs' fr' m' tf rsf frf mf ->
                                FatArrow tge sp parent instr rs fr m (tr ** tf) rsf frf mf
  )).
Proof. 
  intros until tr. intros ENV1 ENV2. intros.  
  inversion H0; subst; try (inversion H).

  inversion H1; subst; inversion H2 ;subst;   
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst;
  eapply Fat_push; eauto;[
  eapply Two_level_repr.exec_Mtree; eauto;
  inversion H4; subst | idtac ].    
  eapply Two_level_repr.exec_Mgetstack; eauto. 
  traceEq.

  inversion H1; subst; inversion H2 ;subst;   
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst;
  eapply Fat_push; eauto;[
  eapply Two_level_repr.exec_Mtree; eauto;
  inversion H4; subst | idtac ].    
  eapply Two_level_repr.exec_Msetstack; eauto. 
  traceEq.

  inversion H1; subst; inversion H2 ;subst;   
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst;
  eapply Fat_push; eauto;[
  eapply Two_level_repr.exec_Mtree; eauto;
  inversion H4; subst | idtac ].    
  eapply Two_level_repr.exec_Mgetparam; eauto. 
  traceEq.

  inversion H1; subst; inversion H2 ;subst;   
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst;
  eapply Fat_push; eauto;[
  eapply Two_level_repr.exec_Mtree; eauto;
  inversion H4; subst | idtac ].    
  eapply Two_level_repr.exec_Mop; eauto. 
  rewrite <- ENV1. trivial.  
  traceEq. 

  inversion H1; subst; inversion H2 ;subst;   
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst;
  eapply Fat_push; eauto;[
  eapply Two_level_repr.exec_Mtree; eauto;
  inversion H4; subst | idtac ].    
  eapply Two_level_repr.exec_Mload; eauto. 
  rewrite <- ENV2. trivial. 
  traceEq.

  inversion H1; subst; inversion H2 ;subst;   
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst;
  eapply Fat_push; eauto;[
  eapply Two_level_repr.exec_Mtree; eauto;
  inversion H4; subst | idtac ].    
  eapply Two_level_repr.exec_Mstore; eauto. 
  rewrite <- ENV2. trivial.  
  traceEq. 

  inversion H1; subst; inversion H2 ;subst.
  exists (Mtree sub);
  split; [eapply vTree; eauto| idtac];
  intros;
  inversion H3; subst. 
  eapply Fat_push; eauto. 
  eapply Two_level_repr.exec_Mtree; eauto. 
  inversion H5; subst. 
  eapply Two_level_repr.exec_Malloc; eauto. 
  traceEq.  
Qed.   
  
Lemma reverse_Fat:
  forall ge sp parent instr rs fr m tf rsf frf mf,
  FatArrow ge sp parent instr rs fr m tf rsf frf mf ->
  forall lbl, (cfg_code (fn_body cfg))!lbl = Some instr ->
  exists lbl', (
  Two_level_repr.exec_instrs ge (fn_body cfg) sp parent lbl rs fr m tf lbl' rsf frf mf /\
  (cfg_code (fn_body cfg))!lbl' = Some Mreturn).  
Proof. 
  intros until 1. 
  induction H.
 
  intro. exists lbl. split; trivial. eapply Two_level_repr.exec_refl; eauto. 

  intros. subst. generalize (IHFatArrow lbl H0); intro.
  destruct H2 as [lbl' FIN].
  destruct FIN. 
  exists lbl'. 
  split; trivial. eapply Two_level_repr.exec_add; eauto.
Qed.

Lemma goto_isFat:
  forall ge tge sp parent c lbl instr rs fr m c' rs' fr' m' tr,
  Machabstr.exec_instr ge f sp parent (Mach.Mgoto lbl :: c) rs fr m tr c' rs' fr' m' ->  
  validCFG f cfg = true ->
  suffix (Mach.Mgoto lbl :: c) (fn_code f) ->
  label_unicity (fn_code f) nil = true ->
  wf_cfg cfg = true ->
  validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg))) (Mach.Mgoto lbl :: c) instr ->
  exists instr', (validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg))) c' instr' /\ 
  (forall rsf frf mf tf, FatArrow tge sp parent instr' rs' fr' m' tf rsf frf mf ->
                                FatArrow tge sp parent instr rs fr m (tr ** tf) rsf frf mf
  )).
Proof.
  intros until 1. intro VAL. intro SUFF. intro UNI. intro WF. intros.  
  inversion H; subst. 
  case_eq (mem lbl (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg)))); intros. 
  
  (*cle *)
  
  inversion H0; subst. 
  inversion H2; subst. 
  generalize (mem_correct _ _ H1); intro; contradiction.  
  assert (exists instr', (cfg_code (fn_body cfg))!lbl = Some instr').   
    eapply domain_reduced; eauto. 
  destruct H3 as [instr' H3]. 
  exists instr'. 
  split.
  unfold validCFG in VAL. 
  generalize (fold_prop _  _ _ _ _ VAL H6); intro.
  unfold validLabel in H4. 
  rewrite H3 in H4.
  destruct instr'.

  unfold validTreeIn in H4.  
  rewrite H14 in H4.  
  eapply vTree; eauto. eapply link; eauto. 
  
  eapply vCall ;eauto. 
  rewrite H14 in H4. 
  case_eq c'; intros.
  subst. congruence. 
  rewrite H5 in H4. destruct i; try (inversion H4). clear H8.  
  destruct l0; try (inversion H4). clear H8. destruct i; try (inversion H4). clear H8. 
    repeat (generalize (essai _ _ H4); clear H4; intro H4; destruct H4).  
  assert (s = s1). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence. 
  assert (s0 = s2). generalize (dec_imp_leibniz _ _ _ _ H8); intro; congruence. 
  assert (l = l1). generalize (dec_imp_leibniz _ _ _ _ H7); intro; congruence. 
  subst.
  assert (In l1 (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg)))). eapply wf_call; eauto. 
  eapply validCall; eauto.
  eapply outSync; eauto. 

   rewrite H14 in H4. 
   destruct c'; try (inversion H4). clear H7.
   destruct i; try (inversion H4). 
   eapply vRet; eauto.
   eapply validReturn; eauto. 

  intros. 
  assert (exec_instruction tge (fn_body cfg) sp parent (Mtree (Two_level_repr.Mout lbl)) rs' fr' m' E0 lbl
  rs' fr' m').
  eapply exec_Mtree; eauto. 
  eapply exec_Mout; eauto. 
  eapply Fat_push; eauto. 
  
  
  inversion H2. 
  inversion H2. 

  (* pas cle *)

  inversion H0; subst.
  inversion H2; subst. 
  exists (Mtree t).
    rewrite H14 in H8. inversion H8; subst. 
  split; intros. 
  eapply vTree; eauto.
  assert (E0 ** tf = tf). traceEq. 
  rewrite H4. trivial.
  generalize (mem_complete _ _ H1); intro; contradiction. 
  
  inversion H2. 
  inversion H2.
Qed.   

Lemma cond_isFat:
  forall ge tge sp parent c cond args lbl instr rs fr m c' rs' fr' m' tr,
  Machabstr.exec_instr ge f sp parent (Mach.Mcond cond args lbl :: c) rs fr m tr c' rs' fr' m' ->
  validCFG f cfg = true ->
  suffix (Mach.Mcond cond args lbl :: c) (fn_code f) ->
  label_unicity (fn_code f) nil = true ->
  wf_cfg cfg = true ->
  validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg))) (Mach.Mcond cond args lbl :: c) instr ->
  exists instr', (validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg))) c' instr' /\ 
  (forall rsf frf mf tf, FatArrow tge sp parent instr' rs' fr' m' tf rsf frf mf ->
                                FatArrow tge sp parent instr rs fr m (tr ** tf) rsf frf mf
  )).
Proof.
  intros until 1. intro VAL. intro SUFF. intro UNI. intro WF. intros.
  inversion H; subst. 

  (* true *) 
  case_eq (mem lbl (remove (PTree.xkeys (cfg_code (fn_body cfg)) 1)
          (cfg_head (fn_body cfg)))); intros. 

  (* cle *)
  inversion H0. 
  inversion H2.
    generalize (mem_correct _ _ H1); intro. congruence. 
   
  subst.  
     generalize (mem_correct _ _ H1); intro. 
    assert (exists instr', (cfg_code (fn_body cfg))!lbl = Some instr'). 
      eapply domain_reduced; eauto. 
    destruct H4 as [instr' H4]. 
    exists instr'.
    split. 
      unfold validCFG in VAL. 
      generalize (fold_prop _ _ _ _ _ VAL H10); intro.
      unfold validLabel in H5. 
      rewrite H4 in H5.
      destruct instr'.

  unfold validTreeIn in H5.  
  rewrite H17 in H5.  
  eapply vTree; eauto. eapply link; eauto. 
     
   eapply vCall; eauto. 
  rewrite H17 in H5. 
  case_eq c'; intros.
  subst. congruence. 
  rewrite H6 in H5. destruct i; try (inversion H5). clear H8.  
  destruct l0; try (inversion H5). clear H8. destruct i; try (inversion H5). clear H8. 
    repeat (generalize (essai _ _ H5); clear H5; intro H5; destruct H5).  
  assert (s = s1). generalize (dec_imp_leibniz _ _ _ _ H5); intro; congruence. 
  assert (s0 = s2). generalize (dec_imp_leibniz _ _ _ _ H8); intro; congruence. 
  assert (l = l1). generalize (dec_imp_leibniz _ _ _ _ H7); intro; congruence. 
  subst.
  assert (In l1 (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg)))). eapply wf_call; eauto. 
  eapply validCall; eauto.
  eapply outSync; eauto. 

     rewrite H17 in H5. 
   destruct c'; try (inversion H5). clear H7.
   destruct i; try (inversion H5). 
   eapply vRet; eauto.
   eapply validReturn; eauto.

  intros. 
  assert (exec_instruction tge (fn_body cfg) sp parent (Mtree (Two_level_repr.Mout lbl)) rs' fr' m' E0 lbl
  rs' fr' m').
  eapply exec_Mtree; eauto. 
  eapply exec_Mout; eauto. 
  eapply Fat_push; eauto.
  eapply exec_Mtree; eauto. 
  eapply exec_Mcond_true; eauto. 
  eapply exec_Mout; eauto. 

  inversion H2. 
  inversion H2.

  (* pas cle *) 

  inversion H0; subst. 
  inversion H2; subst. 
  exists (Mtree sub1). 
  assert (c' = l'). rewrite H17 in H9. inversion H9; trivial.  
  subst. 
  split. 
  eapply vTree; eauto.
  intros. inversion H3; subst. 
  eapply Fat_push; eauto. 
  eapply Two_level_repr.exec_Mtree; eauto.
  eapply Two_level_repr.exec_Mcond_true; eauto. inversion H4; subst. eauto. 
  traceEq. 
  generalize (mem_complete _ _ H1); intro. congruence.  

  inversion H2. 
  inversion H2.

  (* false *) 

  inversion H0; subst. 
  inversion H1; subst. 
  exists (Mtree sub2). 
  split. 
  eapply vTree; eauto. 
  intros. inversion H2; subst. inversion H3; subst. 
  eapply Fat_push; eauto. 
  eapply exec_Mtree; eauto.
  eapply exec_Mcond_false; eauto. 
  traceEq. 

    exists (Mtree sub2). 
  split. 
  eapply vTree; eauto. 
  intros. inversion H2; subst. inversion H3; subst. 
  eapply Fat_push; eauto. 
  eapply exec_Mtree; eauto.
  eapply exec_Mcond_false; eauto. 
  traceEq. 
  
  inversion H1. 
  inversion H1. 
Qed.   

Lemma label_isFat:
  forall ge tge sp parent c lbl instr rs fr m c' rs' fr' m' tr,
  Machabstr.exec_instr ge f sp parent (Mach.Mlabel lbl :: c) rs fr m tr c' rs' fr' m' ->
  validCFG f cfg = true ->
  suffix (Mach.Mlabel lbl :: c) (fn_code f) ->
  label_unicity (fn_code f) nil = true ->
  wf_cfg cfg = true ->
  validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg))) (Mach.Mlabel lbl :: c) instr ->
  exists instr', (validProp f (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg))) c' instr' /\ 
  (forall rsf frf mf tf, FatArrow tge sp parent instr' rs' fr' m' tf rsf frf mf ->
                                FatArrow tge sp parent instr rs fr m (tr ** tf) rsf frf mf
  )).
Proof. 
  intros until 1. intro VAL. intro SUFF. intro UNI. intro WF. intros.  
  inversion H; subst.
  case_eq (mem lbl (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg)))); intros.

  (* cle *) 

  inversion H0; subst.
  inversion H2; subst.
  generalize (mem_correct _ _ H1); intro; contradiction. 
  assert (exists instr', (cfg_code (fn_body cfg))!lbl = Some instr'). 
    eapply domain_reduced; eauto. 
  destruct H3 as [instr' H3]. 
  exists instr'. 
  split.
  unfold validCFG in VAL. 
  generalize (fold_prop _ _ _ _ _ VAL H6); intro.
  unfold validLabel in H4. 
  rewrite H3 in H4.
  destruct instr'.

  unfold validTreeIn in H4. 
  assert (find_label lbl (fn_code f) = Some c'). eapply label_unicity_prop_gen; eauto.   
  rewrite H5 in H4.  
  eapply vTree; eauto. eapply link; eauto. 
  
  eapply vCall ;eauto. 
  assert (find_label lbl (fn_code f) = Some c'). eapply label_unicity_prop_gen; eauto.  
  rewrite H5 in H4. 
  case_eq c'; intros.
  subst. congruence. 
  rewrite H7 in H4. destruct i; try (inversion H4). clear H9.  
  destruct l0; try (inversion H4). clear H9. destruct i; try (inversion H4). clear H9. 
    repeat (generalize (essai _ _ H4); clear H4; intro H4; destruct H4).  
  assert (s = s1). generalize (dec_imp_leibniz _ _ _ _ H4); intro; congruence. 
  assert (s0 = s2). generalize (dec_imp_leibniz _ _ _ _ H9); intro; congruence. 
  assert (l = l1). generalize (dec_imp_leibniz _ _ _ _ H8); intro; congruence. 
  subst.
  assert (In l1 (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg)))). eapply wf_call; eauto. 
  eapply validCall; eauto.
  eapply outSync; eauto. 

   assert (find_label lbl (fn_code f) = Some c'). eapply label_unicity_prop_gen; eauto. 
   rewrite H5 in H4. 
   destruct c'; try (inversion H4). clear H8.
   destruct i; try (inversion H4). 
   eapply vRet; eauto.
   eapply validReturn; eauto. 

  intros. 
  assert (exec_instruction tge (fn_body cfg) sp parent (Mtree (Two_level_repr.Mout lbl)) rs' fr' m' E0 lbl
  rs' fr' m').
  eapply exec_Mtree; eauto. 
  eapply exec_Mout; eauto. 
  eapply Fat_push; eauto. 
  
  
  inversion H2. 
  inversion H2. 

  (* pas cle *)

  inversion H0; subst.
  inversion H2; subst. 
  exists (Mtree t).
  split; intros. 
  eapply vTree; eauto. 
  assert (E0 ** tf = tf). traceEq. 
  rewrite H4. trivial.
  generalize (mem_complete _ _ H1); intro; contradiction. 
  
  inversion H2. 
  inversion H2.
Qed. 

End Val. 

(****************************)
(** Machabstr vers MachTree *)
(****************************)
 
Lemma test:
  forall p tp,
  transf_program p = Some tp ->
  forall f parent rs m t rs' m',
  Machabstr.exec_function (Genv.globalenv p) f parent rs m t rs' m' ->
  forall tf, transf_fundef f = Some tf -> 
  exec_function (Genv.globalenv tp) tf parent rs m t rs' m' .
Proof. 
  intros p tp TRANSP.

  generalize (Machabstr.exec_function_ind4 (Genv.globalenv p) 
            (fun f sp parent c rs fr m t c' rs' fr' m' =>
             forall tf instr,           
             transf_function f = Some tf ->
             suffix c (fn_code f) ->
             validProp f (remove (PTree.xkeys (cfg_code (fn_body tf)) 1)
          (cfg_head (fn_body tf))) c instr ->
             (exists instr', (validProp f (remove (PTree.xkeys (cfg_code (fn_body tf)) 1)
          (cfg_head (fn_body tf))) c' instr' /\ 
             (forall rsf frf mf tfi, FatArrow tf (Genv.globalenv tp) sp parent instr' rs' fr' m' tfi rsf frf mf ->
                                           FatArrow tf (Genv.globalenv tp) sp parent instr rs fr m (t ** tfi) rsf frf mf)
            )) /\ suffix c' (fn_code f))
            (fun f sp parent c rs fr m t c' rs' fr' m' =>
            forall tf instr, 
            transf_function f = Some tf ->
            suffix c (fn_code f) ->
            validProp f (remove (PTree.xkeys (cfg_code (fn_body tf)) 1)
          (cfg_head (fn_body tf))) c instr ->
            (exists instr', (validProp f (remove (PTree.xkeys (cfg_code (fn_body tf)) 1)
          (cfg_head (fn_body tf))) c' instr' /\ 
            (forall rsf frf mf tfi, FatArrow tf (Genv.globalenv tp) sp parent instr' rs' fr' m' tfi rsf frf mf ->
                                          FatArrow tf (Genv.globalenv tp) sp parent instr rs fr m (t ** tfi) rsf frf mf)
            )) /\ suffix c' (fn_code f))
            (fun f parent link ra rs m t rs' m' =>
            forall tf,
            transf_function f = Some tf ->
            exec_function_body (Genv.globalenv tp) tf parent link ra rs m t rs' m'
            )
            (fun f parent rs m t rs' m' =>
             forall tf, transf_fundef f = Some tf -> 
             exec_function (Genv.globalenv tp) tf parent rs m t rs' m' 
            )
            ); intro.

  generalize (env_doesnt_matter1 _ _ TRANSP); intro ENV1.
  generalize (env_doesnt_matter2 _ _ TRANSP); intro ENV2.

  apply H; clear H; intros.

  (* label *)
  split.
  generalize (invert_transf _ _ H); intro. 
  destruct H2 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
  eapply (label_isFat f tf (Genv.globalenv p)); eauto.
  eapply Machabstr.exec_Mlabel; eauto. 
  
  inversion H0. exists (x ++ cons (Mach.Mlabel lbl) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* getstack *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. 

  simpl; trivial. 
  eapply Machabstr.exec_Mgetstack; eauto.
  
  inversion H1. exists (x ++ cons (Mach.Mgetstack ofs ty dst) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* setstack *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. simpl; trivial. 
  eapply Machabstr.exec_Msetstack; eauto.
  
  inversion H1. exists (x ++ cons (Mach.Msetstack src ofs ty) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* getparam *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. simpl; trivial. 
  eapply Machabstr.exec_Mgetparam; eauto.
  
  inversion H1. exists (x ++ cons (Mach.Mgetparam ofs ty dst) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* op *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. simpl; trivial. 
  eapply Machabstr.exec_Mop; eauto.
  
  inversion H1. exists (x ++ cons (Mach.Mop op args res) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* load *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. simpl; trivial. 
  eapply Machabstr.exec_Mload; eauto.
  
  inversion H2. exists (x ++ cons (Mach.Mload chunk addr args dst) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* store *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. simpl; trivial. 
  eapply Machabstr.exec_Mstore; eauto.
  
  inversion H2. exists (x ++ cons (Mach.Mstore chunk addr args src) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  
 
  (* call *)
  
  split. 
  inversion H4; subst.
  inversion H5.

  inversion H5; subst.
  exists (Mtree (Two_level_repr.Mout lbl)).
  split. 
  eapply vTree; eauto. 
  intros. inversion H6; subst.  
  inversion H7; subst.
  inversion H16; subst. 
  eapply Fat_push; eauto.
 
  assert (
        Two_level_repr.find_function (Genv.globalenv tp) ros rs = transf_fundef f' 
        /\ transf_fundef f' <> None).
  destruct ros. 
  simpl. simpl in H. 
  eapply functions_translated2; eauto.
  simpl. simpl in H. 
  case_eq (Genv.find_symbol (Genv.globalenv tp) i); intros.  
   generalize (symbols_preserved2 p tp TRANSP i); intro.
   rewrite  H12 in H13. rewrite <- H13 in H. 
   eapply function_ptr_translated2; eauto. 
  generalize (symbols_preserved2 p tp TRANSP i); intro. 
  rewrite  H12 in H13. rewrite <- H13 in H.  congruence. 
    
  destruct H12. destruct (transf_fundef f').  
  eapply Two_level_repr.exec_Mcall; eauto.
  (*eapply H1; eauto. *)
  congruence. traceEq. 
  
  inversion H5. 

  inversion H3. exists (x ++ cons (Mach.Mcall sig ros) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.    

  (* alloc *) 
  split. 
  eapply linear_isFat with (ge := (Genv.globalenv p)); eauto. simpl; trivial. 
  eapply Machabstr.exec_Malloc; eauto.
  
  inversion H2. exists (x ++ cons (Mach.Malloc) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.  

  (* goto *)
  split. 
  generalize (invert_transf _ _ H0); intro. 
  destruct H3 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
  eapply (goto_isFat f tf (Genv.globalenv p)); eauto.
  eapply Machabstr.exec_Mgoto; eauto. 

  eapply find_label_suff; eauto. 

  (* cond true *)
  
  split.
  generalize (invert_transf _ _ H1); intro. 
  destruct H4 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
  eapply (cond_isFat f tf (Genv.globalenv p)); eauto. 
  eapply Machabstr.exec_Mcond_true; eauto. 

  eapply find_label_suff; eauto. 

  (* cond false *)

  split.
    generalize (invert_transf _ _ H0); intro. 
  destruct H3 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
  eapply (cond_isFat f tf (Genv.globalenv p)); eauto. 
  eapply Machabstr.exec_Mcond_false; eauto.

  inversion H1. exists (x ++ cons (Mach.Mcond cond args lbl) nil). 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. auto.    
  
  (* refl *)
  split; trivial. 
  exists instr. split; trivial. intros. assert (E0 ** tfi = tfi). traceEq. rewrite H3. trivial.
  
  (* one *)
  generalize (H0 _ _ H1 H2 H3); intro.
  clear H0. destruct H4 as [[instr' [V FAT]] SUFF].  
  split; trivial. 
  exists instr'; split; trivial.

  (* trans *)
  generalize (H0 _ _ H4 H5 H6); intro. clear H0. 
  destruct H7 as [[instri[Vi FATi]] SUFFi]. 
  generalize (H2 _ _ H4 SUFFi Vi); intro. clear H2. 
  destruct H0 as [[instrj[Vj FATj]] SUFFj]. 
  split; trivial.
  subst.  
  exists instrj; split; trivial.
  intros. assert ((t1 ** t2) ** tfi = t1 ** t2 ** tfi). traceEq. 
  rewrite H2. auto. 

  (* funct_body *)

  assert (exists instr, (cfg_code (fn_body tf))!(cfg_head (fn_body tf)) = Some instr /\ validProp f (remove (PTree.xkeys (cfg_code (fn_body tf)) 1)
          (cfg_head (fn_body tf))) ((fn_code f)) instr).
    generalize (invert_transf _ _ H4); intro. 
    destruct H5 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]].
    assert (exists im, (cfg_code (fn_body tf)) ! (cfg_head (fn_body tf)) = Some im). 
      destruct (cfg_code (fn_body tf)) ! (cfg_head (fn_body tf)). exists i. trivial. 
      inversion HN. 
    destruct H5. exists x. 
    split; trivial.
    unfold validCFG in VAL.
    assert (fn_code f = Mlabel (cfg_head (fn_body tf)) :: tail (fn_code f)). 
      destruct (fn_code f). simpl in HE2. inversion HE2. 
      simpl in HE2. simpl. destruct i; try (inversion HE2). 
      case_eq (peq l (cfg_head (fn_body tf))); intros. 
      clear H6; subst; trivial. 
      rewrite H6 in HE2. congruence. 
    assert (validProp f (remove (PTree.xkeys (cfg_code (fn_body tf)) 1)
          (cfg_head (fn_body tf))) (tail (fn_code f)) x). 
    eapply link_gen; eauto. rewrite H6. simpl. 
    case_eq (peq (cfg_head (fn_body tf)) (cfg_head (fn_body tf))); intros. 
    trivial. congruence. 
    inversion H7. 
    eapply vTree; eauto. rewrite H6. 
    eapply labelControl; eauto. eapply mem_complete; eauto. 
    inversion H8. case_eq (head (tail (fn_code f))); intros.
                        rewrite H15 in SHMOK. 
                        rewrite <- H11 in H15. inversion H15.
                        destruct i; try (inversion H17); try (inversion SHMOK).
                        rewrite <- H11 in H15. inversion H15.  
    inversion H8. case_eq (head (tail (fn_code f))); intros.
                        rewrite H13 in SHMOK. 
                        rewrite <- H12 in H13. inversion H13.
                        destruct i; try (inversion H15); try (inversion SHMOK).
                        rewrite <- H12 in H13. inversion H13.  

  destruct H5 as [instr [PR V]]. 
  assert (suffix ((fn_code f)) ((fn_code f))). exists (@nil Mach.instruction); simpl; trivial.  
  generalize (H3 _ _ H4 H5 V); intro. clear H3. 
  destruct H6 as [[instr' [Vf FATf]] SUFF].
  inversion Vf; subst. inversion H3. inversion H3. inversion H3; subst.  
  
  assert (FatArrow tf (Genv.globalenv tp) (Vptr stk (Int.repr (- Mach.fn_framesize f))) parent Mreturn rs' fr3 m2 E0 rs' fr3 m2). 
  eapply Fat_intro; eauto.  
  generalize (FATf _ _ _ _ H6); intro FAT. clear FATf.  
 
  generalize (reverse_Fat _ _ _ _ _ _ _ _ _ _ _ _ FAT _ PR); intro.
  destruct H7 as [instr' [PRINC RET]]. 
  
  assert (t ** E0 = t). traceEq. rewrite H7 in PRINC.
  generalize (invert_transf _ _ H4); intro.
  destruct H8 as [t' [[EL [DEF ]VAL] [UNI [WF [HE1 [VE [SHMOK [HE2 [RETT GOTO]]]]]]]]].
  clear H7. subst. 
  eapply Two_level_repr.exec_funct_body; eauto.

  (* internal *)
  simpl in H1. destruct (transf_function f). inversion H1. subst.  
  eapply Two_level_repr.exec_funct_internal; eauto. intros. 
  (*eapply H0; eauto.*)
  congruence. 

  (* external *)
  simpl in H2. inversion H2; subst. 
  eapply Two_level_repr.exec_funct_external; eauto.  
Qed. 

Theorem transf_correct_2:
  forall p tp t r,
  transf_program p = Some tp ->
  Machabstr.exec_program p t r ->
  Two_level_repr.exec_program tp t r.
Proof. 
  intros.
  unfold Machabstr.exec_program in H0.
  unfold Two_level_repr.exec_program. 
  destruct H0 as [b [f [rs [m [D [E [F G]]]]]]].
  generalize (symbols_preserved p tp H (prog_main p)); intro.
  generalize (function_ptr_translated2 p tp H b f E); intro.
  destruct H1 as [I J]. 
  case_eq (transf_fundef f); intros. 
  exists b; exists f0; exists rs; exists m.
  assert (prog_main p = prog_main tp). 
    rewrite (transform_partial_program_main transf_fundef p H).
    trivial. 
  intuition auto.
  rewrite <- H2. rewrite <- D. trivial.  
  rewrite H1 in I. trivial. 
  eapply test; eauto. 
  rewrite (Genv.init_mem_transf_partial transf_fundef p H). eauto. 
  congruence. 
Qed.   
  