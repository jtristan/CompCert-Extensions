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

Lemma validskip_linear:
  forall s i,
 (* nbranchset i = true -> *)
  forall l t,
  validTreeProp f s l t ->
  forall subtree,
  suffix l (fn_code f) ->
  put i subtree = Some t ->
  exists l', (validTreeProp f s (i :: l') t /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (i :: l') rs fr m)
  /\ suffix (i :: l') (fn_code f)).
Proof.

  intros s i. 

  apply (validTreeProp_ind f s
      ( fun (l : code) (t : instructions_tree) => 
        forall subtree,
        suffix l (fn_code f) ->
        put i subtree = Some t ->
        exists l', (validTreeProp f s (i :: l') t
         /\
         (forall ge sp parent rs fr m,
         Machabstr.exec_instrs ge f sp parent l rs fr m E0 (i :: l') rs fr m)
         /\ suffix (i :: l') (fn_code f)
         ))
      ); intros.

  (* label *)

  assert (suffix l (fn_code f)) . eapply suff_lab; eauto. 
  generalize (H1 subtree H4 H3); intro. clear H1.
  destruct H5 as [l' [E [F G]]]. 
  exists l'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mlabel; eauto. 
  traceEq.

  (* goto *)

  assert (suffix l' (fn_code f)) . eauto.
    eapply find_label_suff; eauto. 
  generalize (H1 subtree H5 H4); intro. clear H1.
  destruct H6 as [l0' [E [F G]]]. 
  exists l0'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mgoto; eauto. 
  traceEq.          

  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply getStackSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.
  
  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply setStackSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.

  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply getParamSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.

  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply opSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.

  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply loadSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.

  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply storeSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.

  destruct i; try (inversion H2); simpl in H2; inversion H2; subst.  
  exists l; subst; split.
  eapply allocSync; eauto. split; trivial.  
  intros.
  eapply Machabstr.exec_refl; eauto.

  

  destruct i; try (inversion H6); simpl in H6; inversion H6; subst.
  destruct i; try (inversion H1); simpl in H1; inversion H1; subst.
  destruct i; try (inversion H1); simpl in H1; inversion H1; subst.
  destruct i; try (inversion H3); simpl in H3; inversion H3; subst. 
Qed. 

Lemma validskip_out:
  forall s lbl l t,
  validTreeProp f s l t ->
  t = Mout lbl ->
  suffix l (fn_code f) ->
  (exists l', (validTreeProp f s (Mach.Mlabel lbl :: l') t /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mlabel lbl :: l') rs fr m)
  /\ suffix (Mach.Mlabel lbl :: l') (fn_code f))) \/
  (exists l', (validTreeProp f s (Mach.Mgoto lbl :: l') t /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mgoto lbl :: l') rs fr m)
  /\ suffix (Mach.Mgoto lbl :: l') (fn_code f))).
Proof.
  intros until lbl. 

  apply (validTreeProp_ind f s
      ( fun (l : code) (t : instructions_tree) => 
        t = Mout lbl ->
        suffix l (fn_code f) ->
        (exists l', (validTreeProp f s (Mach.Mlabel lbl :: l') t
         /\
         (forall ge sp parent rs fr m,
         Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mlabel lbl :: l') rs fr m)
         /\ suffix (Mach.Mlabel lbl :: l') (fn_code f)
         )) \/ (exists l', (validTreeProp f s (Mach.Mgoto lbl :: l') t /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mgoto lbl :: l') rs fr m)
  /\ suffix (Mach.Mgoto lbl :: l') (fn_code f))))
      ); intros. 


  (* avance label *)
  subst. 
  assert (Mout lbl = Mout lbl). 
    trivial.
  assert (suffix l (fn_code f)). eapply suff_lab; eauto. 
  generalize (H1 H2 H4); intro. clear H1.
  destruct H5. 
  destruct H1 as [l' [E [F G]]]. 
  left. exists l'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mlabel; eauto. 
  traceEq.

 destruct H1 as [l' [E [F G]]]. 
  right. exists l'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mlabel; eauto. 
  traceEq.

  (* avance goto *)
  subst. 
  assert (Mout lbl = Mout lbl). 
    trivial.
  assert (suffix l' (fn_code f)). eapply find_label_suff; eauto. 
  generalize (H1 H3 H5); intro. clear H1.
  destruct H6. 
  destruct H1 as [l0' [E [F G]]]. 
  left. exists l0'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mgoto; eauto. 
  traceEq.
  destruct H1 as [l0' [E [F G]]]. 
  right. exists l0'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mgoto; eauto. 
  traceEq.

 
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H5.   

  injection H0; intros; subst.
   right. exists l.
   subst. 
   split; trivial. 
   eapply gotoSync; eauto.
   split; trivial. 
  intros.
  eapply Machabstr.exec_refl; eauto. 

  (* syncro *)
   injection H0; intros; subst.
   left. exists l.
   subst. 
   split; trivial. 
   eapply outSync; eauto.
   split; trivial. 
  intros.
  eapply Machabstr.exec_refl; eauto.

  inversion H2. 
 
Qed. 


Lemma validskip_cond:
  forall s cond rl l t,
  validTreeProp f s l t ->
  forall sub1 sub2,
  t = Mcond cond rl sub1 sub2 ->
  suffix l (fn_code f) ->
  exists l', exists lbl, (validTreeProp f s (Mach.Mcond cond rl lbl :: l') t /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mcond cond rl lbl :: l') rs fr m)
  /\ suffix (Mach.Mcond cond rl lbl :: l') (fn_code f)).
Proof.
  intros until rl. 

  apply (validTreeProp_ind f s
      ( fun (l : code) (t : instructions_tree) => 
        forall sub1 sub2, 
        t = Mcond cond rl sub1 sub2 ->
        suffix l (fn_code f) ->
        exists l', exists lbl, (validTreeProp f s (Mach.Mcond cond rl lbl :: l') t
         /\
         (forall ge sp parent rs fr m,
         Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mcond cond rl lbl :: l') rs fr m)
         /\ suffix (Mach.Mcond cond rl lbl :: l') (fn_code f)
         ))
      ); intros. 


  (* avance label *)
  subst. 
  assert (Mcond cond rl sub1 sub2 = Mcond cond rl sub1 sub2). 
    trivial.  
  assert (suffix l (fn_code f)). eapply suff_lab; eauto. 
  generalize (H1 sub1 sub2 H2 H4); intro. clear H1.
  destruct H5 as [l' [lbl' [E [F INCL]]]]. 
  exists l'. exists lbl'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mlabel; eauto. 
  traceEq. 

  (* avance goto *)
  subst. 
  assert (Mcond cond rl sub1 sub2 = Mcond cond rl sub1 sub2). 
    trivial.
  assert (suffix l' (fn_code f)). eapply find_label_suff; eauto.  
  generalize (H1 sub1 sub2 H3 H5); intro. clear H1.
  destruct H6 as [l0' [lbl' [E [F INCL]]]]. 
  exists l0'. exists lbl'. 
  split; trivial. split; trivial.  
  intros. 
  generalize (F ge sp parent rs fr m); intro. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mgoto; eauto. 
  traceEq. 

 
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  inversion H1.
  
  (* syncro *)
  exists l. exists lbl.  
  subst. 
  split. injection H5; intros; subst.   
  eapply condSync; eauto.
  split; trivial. 
  intros. injection H5; intros; subst. 
  eapply Machabstr.exec_refl; eauto.
  injection H5; intros; subst; trivial. 

  inversion H0. 
  inversion H0.

  exists l. exists lbl.  
  subst. 
  split. injection H2; intros; subst.   
  eapply condBack; eauto.
  split; trivial. 
  intros. injection H2; intros; subst. 
  eapply Machabstr.exec_refl; eauto.
  injection H2; intros; subst; trivial. 
Qed. 

Lemma validskipnext_linear:
  forall s l i t subtree,
  put i subtree = Some t ->
  validTreeProp f s l t ->
  suffix l (fn_code f) ->
  exists l', validTreeProp f s (i :: l') (t) /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (i :: l') rs fr m)
  /\ suffix (i :: l') (fn_code f). 
Proof. 
  intros. 
  eapply validskip_linear; eauto.
Qed.  

Lemma validskipnext_out:
  forall s l lbl,
  validTreeProp f s l (Mout lbl) ->
  suffix l (fn_code f) ->
  (exists l', validTreeProp f s (Mach.Mlabel lbl :: l') (Mout lbl) /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mlabel lbl :: l') rs fr m)
  /\ suffix (Mlabel lbl :: l') (fn_code f)) \/
  (exists l', validTreeProp f s (Mach.Mgoto lbl :: l') (Mout lbl) /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mgoto lbl :: l') rs fr m)
  /\ suffix (Mgoto lbl :: l') (fn_code f)). 
Proof. 
  intros. 
  eapply validskip_out; eauto.
Qed.  

Lemma validskipnext_cond:
  forall s l cond rl sub1 sub2,
  validTreeProp f s l (Mcond cond rl sub1 sub2) ->
  suffix l (fn_code f) ->
  exists l', exists lbl, validTreeProp f s (Mach.Mcond cond rl lbl :: l') (Mcond cond rl sub1 sub2) /\
  (forall ge sp parent rs fr m,
  Machabstr.exec_instrs ge f sp parent l rs fr m E0 (Mach.Mcond cond rl lbl :: l') rs fr m)
  /\ suffix (Mach.Mcond cond rl lbl :: l') (fn_code f). 
Proof. 
  intros. 
  eapply validskip_cond; eauto.
Qed.  

Lemma validTreeProp_correct_1:
  forall tge t sp parent rs fr m tr tar rs' fr' m',
  Two_level_repr.exec_instructions_tree tge t sp parent rs fr m tr tar rs' fr' m' ->
  forall ge l s,
    (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
  suffix l (fn_code f) ->
  validTreeProp f s l t -> 
  exists w, 
  ((Machabstr.exec_instrs ge f sp parent l rs fr m tr (Mlabel tar :: w) rs' fr' m'  /\ suffix (Mlabel tar :: w) (fn_code f))
  \/ (Machabstr.exec_instrs ge f sp parent l rs fr m tr (Mgoto tar :: w) rs' fr' m' /\ suffix (Mgoto tar :: w) (fn_code f))
  \/ (exists cond, exists  rl, Machabstr.exec_instrs ge f sp parent l rs fr m tr (Mach.Mcond cond rl tar :: w) rs' fr' m' /\ suffix (Mach.Mcond cond rl  tar :: w) (fn_code f) /\ eval_condition cond rs' ## rl = Some true) 
  ). 
Proof.
  
  generalize (exec_instructions_tree_ind
            ( fun (tge: genv) t sp parent rs fr m tr lbl rs' fr' m' => 
            forall ge l s,
              (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
            suffix l (fn_code f) ->
            validTreeProp f s l t -> 
            exists w, 
  ((Machabstr.exec_instrs ge f sp parent l rs fr m tr (Mlabel lbl :: w) rs' fr' m'  /\ suffix (Mlabel lbl :: w) (fn_code f))
  \/ (Machabstr.exec_instrs ge f sp parent l rs fr m tr (Mgoto lbl :: w) rs' fr' m' /\ suffix (Mgoto lbl :: w) (fn_code f))
  \/ (exists cond , exists rl, Machabstr.exec_instrs ge f sp parent l rs fr m tr (Mach.Mcond cond rl lbl :: w) rs' fr' m' /\ suffix (Mach.Mcond cond rl  lbl :: w) (fn_code f) /\ eval_condition cond rs' ## rl = Some true)   
  ))); intro.             

  apply H; clear H; intros.  
 
    (* getstack *)
  assert (put (Mach.Mgetstack ofs ty dst) subtree = Some (Mgetstack ofs ty dst subtree)). trivial.  
  generalize (validskipnext_linear _ _ _ _ _ H6 H5 H4); intro. 
  destruct H7 as [l' [F [G INCL]]].  inversion F; subst.
  assert (suffix l' (fn_code f)). eapply suff_getstack; eauto. 
  generalize (H1 ge0 _ _ H2 H3 H7 H8); intro.
  destruct H9. exists x. destruct H9. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mgetstack ofs ty dst :: l') rs fr
  m E0 l' (Regmap.set dst v rs) fr m).
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_Mgetstack; eauto. 
  destruct H9. 
  left. split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mgetstack ofs ty dst :: l') rs fr m t (Mlabel lbl :: x)
  rs' fr' m'). 
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans; eauto. 
  traceEq.
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mgetstack ofs ty dst :: l') rs fr
  m E0 l' (Regmap.set dst v rs) fr m).
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_Mgetstack; eauto. 
  destruct H9. destruct H9.  
  right. left. split; trivial.
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mgetstack ofs ty dst :: l') rs fr m t (Mgoto lbl :: x)
  rs' fr' m'). 
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans; eauto. 
  traceEq.    

  right. right. intros. destruct H9. destruct H9. 
  exists x0; exists x1. destruct H9.  
    assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mgetstack ofs ty dst :: l') rs fr m t (Mach.Mcond x0 x1 lbl :: x)
  rs' fr' m'). 
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  split; trivial. eapply Machabstr.exec_trans; eauto. 
  traceEq.    

  (* setstack *)

  assert (put (Mach.Msetstack src ofs ty) subtree = Some (Msetstack src ofs ty subtree)) as PUT. trivial. 
 
  generalize (validskipnext_linear _ _ _ _ _ PUT H5 H4); intro VAL; 
  destruct VAL as [l' [F [G INCL]]];  inversion F; subst;
  assert (suffix l' (fn_code f)) as SUF; try (eapply suff_setstack; eauto);  
  generalize (H1 ge0 _ _ H2 H3 SUF H7); intro PRINC;
  destruct PRINC as [x PRINC]; exists x;
  destruct PRINC as [ [PRINC SUFF] | [ [PRINC SUFF ] | [cond [rl [PRINC JOB (*[SUFF EV]*)]]] ]];
  [left | right;left | right;right; exists cond; exists rl]; try (
    split; trivial;
  generalize (G ge0 sp parent rs fr m); intro;  
  eapply Machabstr.exec_trans; eauto; [
  eapply Machabstr.exec_trans; eauto ;eapply Machabstr.exec_one; eauto; eapply Machabstr.exec_Msetstack; eauto |
  traceEq]).
 
  (* getparam *)

   assert (put (Mach.Mgetparam ofs ty dst) subtree = Some (Mgetparam ofs ty dst subtree)) as PUT. trivial. 
 
  generalize (validskipnext_linear _ _ _ _ _ PUT H5 H4); intro VAL; 
  destruct VAL as [l' [F [G INCL]]];  inversion F; subst;
  assert (suffix l' (fn_code f)) as SUF; try (eapply suff_getparam; eauto);  
  generalize (H1 ge0 _ _ H2 H3 SUF H7); intro PRINC;
  destruct PRINC as [x PRINC]; exists x;
  destruct PRINC as [ [PRINC SUFF] | [ [PRINC SUFF ] | [cond [rl [PRINC JOB (*[SUFF EV]*)]]] ]];
  [left | right;left | right;right; exists cond; exists rl]; try (
    split; trivial;
  generalize (G ge0 sp parent rs fr m); intro;  
  eapply Machabstr.exec_trans; eauto; [
  eapply Machabstr.exec_trans; eauto ;eapply Machabstr.exec_one; eauto; eapply Machabstr.exec_Mgetparam; eauto |
  traceEq]).
  
  (* op *)

    assert (put (Mach.Mop op args res) subtree = Some (Mop op args res subtree)) as PUT. trivial. 
 
  generalize (validskipnext_linear _ _ _ _ _ PUT H5 H4); intro VAL; 
  destruct VAL as [l' [F [G INCL]]];  inversion F; subst;
  assert (suffix l' (fn_code f)) as SUF; try (eapply suff_op; eauto);  
  generalize (H1 ge0 _ _ H2 H3 SUF H7); intro PRINC;
  destruct PRINC as [x PRINC]; exists x;
  destruct PRINC as [ [PRINC SUFF] | [ [PRINC SUFF ] | [cond [rl [PRINC JOB (*[SUFF EV]*)]]] ]];
  [left | right;left | right;right; exists cond; exists rl]; try (
    split; trivial;
  generalize (G ge0 sp parent rs fr m); intro;  
  eapply Machabstr.exec_trans; eauto; [
  eapply Machabstr.exec_trans; eauto ;eapply Machabstr.exec_one; eauto; eapply Machabstr.exec_Mop; eauto |
  traceEq]). rewrite H2; trivial. rewrite H2; trivial. rewrite H2; trivial. 

  (* load *)

  assert (put (Mach.Mload chunk addr args dst) subtree = Some (Mload chunk addr args dst subtree)) as PUT. trivial. 
 
  generalize (validskipnext_linear _ _ _ _ _ PUT H6 H5); intro VAL; 
  destruct VAL as [l' [F [G INCL]]];  inversion F; subst;
  assert (suffix l' (fn_code f)) as SUF; try (eapply suff_load; eauto);  
  generalize (H2 ge0 _ _ H3 H4 SUF H8); intro PRINC;
  destruct PRINC as [x PRINC]; exists x;
  destruct PRINC as [ [PRINC SUFF] | [ [PRINC SUFF ] | [cond [rl [PRINC JOB (*[SUFF EV]*)]]] ]];
  [left | right;left | right;right; exists cond; exists rl]; try (
    split; trivial;
  generalize (G ge0 sp parent rs fr m); intro;  
  eapply Machabstr.exec_trans; eauto; [
  eapply Machabstr.exec_trans; eauto ;eapply Machabstr.exec_one; eauto; eapply Machabstr.exec_Mload; eauto |
  traceEq]). rewrite H4; trivial. rewrite H4; trivial. rewrite H4; trivial. 

  (* store *)

  assert (put (Mach.Mstore chunk addr args src) subtree = Some (Mstore chunk addr args src subtree)) as PUT. trivial. 
 
  generalize (validskipnext_linear _ _ _ _ _ PUT H6 H5); intro VAL; 
  destruct VAL as [l' [F [G INCL]]];  inversion F; subst;
  assert (suffix l' (fn_code f)) as SUF; try (eapply suff_store; eauto);  
  generalize (H2 ge0 _ _ H3 H4 SUF H8); intro PRINC;
  destruct PRINC as [x PRINC]; exists x;
  destruct PRINC as [ [PRINC SUFF] | [ [PRINC SUFF ] | [cond [rl [PRINC JOB (*[SUFF EV]*)]]] ]];
  [left | right;left | right;right; exists cond; exists rl]; try (
    split; trivial;
  generalize (G ge0 sp parent rs fr m); intro;  
  eapply Machabstr.exec_trans; eauto; [
  eapply Machabstr.exec_trans; eauto ;eapply Machabstr.exec_one; eauto; eapply Machabstr.exec_Mstore; eauto |
  traceEq]). rewrite H4; trivial. rewrite H4; trivial. rewrite H4; trivial. 
 
  (* alloc *)

  assert (put (Mach.Malloc) subtree = Some (Malloc subtree)) as PUT. trivial. 
 
  generalize (validskipnext_linear _ _ _ _ _ PUT H6 H5); intro VAL; 
  destruct VAL as [l' [F [G INCL]]];  inversion F; subst;
  assert (suffix l' (fn_code f)) as SUF; try (eapply suff_alloc; eauto);
  generalize (H2 ge0 _ _ H3 H4 SUF H9); intro PRINC;
  destruct PRINC as [x PRINC]; exists x;
  destruct PRINC as [ [PRINC SUFF] | [ [PRINC SUFF ] | [cond [rl [PRINC JOB (*[SUFF EV]*)]]] ]];
  [left | right;left | right;right; exists cond; exists rl]; try (
    split; trivial;
  generalize (G ge0 sp parent rs fr m); intro;  
  eapply Machabstr.exec_trans; eauto; [
  eapply Machabstr.exec_trans; eauto ;eapply Machabstr.exec_one; eauto; eapply Machabstr.exec_Malloc; eauto |
  traceEq]). 

  (* cond true *)
  revert H2 H3. intros ENV1 ENV2. revert H4 H5. intros H2 H3.  
  generalize (validskipnext_cond _ _ _ _ _ _ H3 H2); intro.
  destruct H4 as [l' [lbl' [F [G INCL]]]].
  inversion F; subst. 
  assert (suffix l'0 (fn_code f)). eapply find_label_suff; eauto.  
  generalize (H1 ge0 _ _ ENV1 ENV2 H4 H13); intro.
  destruct H5. exists x.  
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr
  m E0 l'0 rs fr m). 
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_Mcond_true; eauto. 
  destruct H5. destruct H5. 
  left. split; trivial.
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mlabel lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto.
  traceEq.
  eapply Machabstr.exec_trans; eauto. 
  traceEq.
  right. destruct H5. destruct H5.  left.  split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mgoto lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto.
  traceEq.
  eapply Machabstr.exec_trans; eauto. 
  traceEq.  
  right. 
  intros. destruct H5. destruct H5. exists x0; exists x1. 
  destruct H5. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mach.Mcond x0 x1 lbl :: x)
  rs' fr' m').
  eapply Machabstr.exec_trans;eauto.
  traceEq.
  split; trivial. eapply Machabstr.exec_trans; eauto. 
  traceEq.  


  exists l'. right. right. intros. 
  inversion H0; subst. exists cond; exists args. split; trivial.
  split; trivial. 
  
(*
  assert (exists l0, find_label lbl' (fn_code f) = Some l0).
    plop
  destruct H4 as [l0 H4]. 
  assert (suffix (Mlabel lbl' :: l0) (fn_code f)). eapply find_label_suff2; eauto.  
  assert (validTreeProp f s (Mlabel lbl' :: l0) (Mout lbl')). 
  eapply outSync; eauto.   
  generalize (H1 ge0 _ s ENV1 ENV2 H5 H7); intro.
  destruct H8. 
  exists x. 
  destruct H8. destruct H8. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr
  m E0 l0 rs fr m). 
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_Mcond_true; eauto. 
  destruct H8. destruct H8. 
  left. split; trivial. 
  eapply Machabstr.exec_trans; eauto. 
*)



  (* cond false *)
 revert H2 H3. intros ENV1 ENV2. revert H4 H5. intros H2 H3.  
  generalize (validskipnext_cond _ _ _ _ _ _ H3 H2); intro. 
  destruct H4 as [l' [lbl' [F [G INCL]]]].
  inversion F; subst. 
  assert (suffix l' (fn_code f)). 
    inversion INCL. exists (x ++ Mach.Mcond cond args lbl' :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons.  trivial. 
  generalize (H1 ge0 _ _ ENV1 ENV2 H4 H12); intro.
  destruct H5. exists x. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr
  m E0 l' rs fr m). 
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_Mcond_false; eauto. 
  destruct H5. destruct H5.   
  left. split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mlabel lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans;eauto. 
  traceEq. destruct H5. destruct H5. 
  right. left.  split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mgoto lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans;eauto. 
  traceEq.     
  destruct H5. destruct H5. destruct H5. 
  right; right. exists x0; exists x1. split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mach.Mcond x0 x1 lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans;eauto. 
  traceEq.      
 
    assert (suffix l' (fn_code f)). 
    inversion INCL. exists (x ++ Mach.Mcond cond args lbl' :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons.  trivial. 
  generalize (H1 ge0 _ _ ENV1 ENV2 H4 H11); intro.
  destruct H5. exists x. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr
  m E0 l' rs fr m). 
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_Mcond_false; eauto. 
  destruct H5. destruct H5. 
  left. split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mlabel lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans;eauto. 
  traceEq. destruct H5. destruct H5. 
  right. left. split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mgoto lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans;eauto. 
  traceEq.      
  destruct H5. destruct H5. destruct H5. 
  right; right. 
  exists x0; exists x1. split; trivial. 
  assert (Machabstr.exec_instrs ge0 f sp parent (Mach.Mcond cond args lbl' :: l') rs fr m t (Mach.Mcond x0 x1 lbl :: x)
  rs' fr' m').  
  eapply Machabstr.exec_trans;eauto. 
  traceEq.
  eapply Machabstr.exec_trans;eauto. 
  traceEq.       

  (* out *)
  revert H H0. intros ENV1 ENV2. revert H1 H2. intros H H0. 
  generalize (validskipnext_out _ _ _ H0 H); intro.
  destruct H1. 
  destruct H1 as [l' [F [G INCL]]].
  assert (suffix l' (fn_code f)). eapply suff_lab; eauto.  
  exists l'.  
  left. split.  
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_refl; eauto.
  traceEq.  
  trivial.
  destruct H1 as [l' [F [G INCL]]].
  exists l'. 
  right. left. split. 
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_refl; eauto.
  traceEq. trivial.     
Qed.   

End Val. 

(****************************)
(** MachTree vers Machasbtr *)
(****************************)

Lemma validLabel_correct:
  forall p tp,
  transf_program p = Some tp ->
  forall (tf : Two_level_repr.fundef) (parent : frame) (rs : regset) (m : Mem.mem) (t : trace) (rs' : regset) (m' : Mem.mem),
  exec_function (Genv.globalenv tp) tf parent rs m t rs' m' ->
  forall f, transf_fundef f = Some tf -> 
  Machabstr.exec_function (Genv.globalenv p) f parent rs m t rs' m'.
Proof. 
  intros p tp TRANSF. 

  generalize (env_doesnt_matter1 _ _ TRANSF); intro ENV1.
  generalize (env_doesnt_matter2 _ _ TRANSF); intro ENV2. 

  generalize (Two_level_repr.exec_function_ind5 
             (Genv.globalenv tp) 

             (fun (tc : Two_level_repr.cfg) (sp :val) (parent :frame) instr (rs : regset) (fr : frame) (m : Mem.mem) (t : trace) (lbl' : label) (rs' : regset) (fr' : frame) (m' : Mem.mem) => 
              forall f tf c, 
              tc = fn_body tf ->
              suffix c (fn_code f) -> 
              validProp f ((remove (PTree.xkeys (cfg_code (fn_body tf)) xH)
          (cfg_head (fn_body tf)))) c instr ->
              transf_fundef (Internal f) = Some (Internal tf) -> exists w,                                                                                                                                                                                              (* suffix (Mlabel lbl' :: w) (fn_code f) *)
              ((Machabstr.exec_instrs (Genv.globalenv p) f sp parent c rs fr m t (Mlabel lbl' :: w) rs' fr' m' /\ suffix (Mlabel lbl' :: w) (fn_code f))
              \/ (Machabstr.exec_instrs (Genv.globalenv p) f sp parent c rs fr m t (Mgoto lbl' :: w) rs' fr' m' /\ suffix (Mgoto lbl' :: w) (fn_code f))
              \/ (exists cond, exists args, Machabstr.exec_instrs (Genv.globalenv p) f sp parent c rs fr m t (Mach.Mcond cond args lbl' :: w) rs' fr' m' /\ suffix (Mach.Mcond cond args lbl' :: w) (fn_code f) /\ eval_condition cond rs' ## args = Some true))
            ) 

             (fun (tc : Two_level_repr.cfg) (sp :val) (parent :frame) (lbl :label) (rs : regset) (fr : frame) (m : Mem.mem) (t : trace) (lbl' : label) (rs' : regset) (fr' : frame) (m' : Mem.mem) =>
             forall f tf c,
             tc = fn_body tf ->
             suffix c (fn_code f) -> label_unicity (fn_code f) nil = true ->
             transf_fundef (Internal f) = Some (Internal tf) -> 
             validLabel f tf ((remove (PTree.xkeys (cfg_code (fn_body tf)) xH)
          (cfg_head (fn_body tf)))) lbl = true ->
             find_label lbl (fn_code f) = Some c -> exists w, find_label lbl' (fn_code f) = Some w /\
             Machabstr.exec_instrs (Genv.globalenv p) f sp parent c rs fr m t  w rs' fr' m' /\ suffix w (fn_code f)
             )

             (fun (tf : Two_level_repr.function) (parent : frame) (link : val) (ra : val) (rs : regset) (m : Mem.mem) (t : trace) (rs' : regset) (m' : Mem.mem) =>
             forall f,
             transf_function f = Some tf ->
             Machabstr.exec_function_body (Genv.globalenv p) f parent link ra rs m t rs' m'
             )

             (fun (tf : Two_level_repr.fundef) (parent : frame) (rs : regset) (m : Mem.mem) (t : trace) (rs' : regset) (m' : Mem.mem) => 
                          forall f, transf_fundef f = Some tf -> 
                          Machabstr.exec_function (Genv.globalenv p) f parent rs m t rs' m'
             )); intro.
 
  apply H; clear H; intros. 
  
  (* call *)

  subst. 
  inversion H4; subst. 
  inversion H2; subst. 
 
    destruct ros. simpl. simpl in H. 
    generalize (functions_translated p _ _ _ H); intro.
    destruct H6 as [ff [A B]].    
 
  generalize (H1 _ B); intro. 
  assert (Two_level_repr.exec_instructions_tree (Genv.globalenv tp) (Two_level_repr.Mout lbl) sp parent rs' fr m' E0 lbl rs' fr m').
    eapply exec_Mout; eauto.
  assert (suffix l (fn_code f)). 
    inversion H3. exists (x ++ Mach.Mcall sig (inl ident m0) :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. simpl. trivial.  

  generalize (validTreeProp_correct_1 _ _ _ _ _ _ _ _ _ _ _ _ _ H7 (Genv.globalenv p) _ _ ENV1 ENV2 H8 H11); intro.
  destruct H10 as [w H10]. destruct H10. destruct H10 as [E F].     
  exists w. 
  left.  split; trivial. 
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mcall; eauto. 
  traceEq. 

  destruct H10. destruct H10 as [E F]. 
  exists w. right. left. split; trivial.
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mcall; eauto. 
  traceEq. 

  destruct H10. destruct H10. destruct H10 as [E F]. 
  exists w. right. right. exists x; exists x0. split; trivial.
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mcall; eauto. 
  traceEq. 

   simpl. simpl in H. 
   case_eq (Genv.find_symbol (Genv.globalenv tp) i); intros. 
   rewrite H6 in H.  
    generalize (function_ptr_translated p _ _ _ H); intro.
    destruct H7 as [ff [A B]].
 
    generalize (H1 _ B); intro. 
  assert (Two_level_repr.exec_instructions_tree (Genv.globalenv tp) (Two_level_repr.Mout lbl) sp parent rs' fr m' E0 lbl rs' fr m').
    eapply exec_Mout; eauto.
  assert (suffix l (fn_code f)). 
    inversion H3. exists (x ++ Mach.Mcall sig (inr mreg i) :: nil). 
    rewrite app_ass. rewrite <- app_comm_cons. simpl. trivial.  

  generalize (validTreeProp_correct_1 _ _ _ _ _ _ _ _ _ _ _ _ _ H8 (Genv.globalenv p) _ _ ENV1 ENV2 H10 H11); intro.
  destruct H12 as [w H12]. destruct H12.  
  destruct H12 as [E F]. 
  exists w. 
  left. split; trivial.
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mcall; eauto. simpl.
  generalize symbols_preserved2; intro. 
  rewrite (symbols_preserved2 p tp TRANSF i) in H6. 
  rewrite H6.  trivial. 
  traceEq.   
  
  destruct H12. destruct H12 as [E F]. 
  exists w. 
  right. left. split; trivial.
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mcall; eauto. simpl.
  generalize symbols_preserved2; intro. 
  rewrite (symbols_preserved2 p tp TRANSF i) in H6. 
  rewrite H6.  trivial. 
  traceEq.   

  destruct H12. destruct H12. 
  destruct H12 as [E F]. 
  exists w. 
  right. right. exists x; exists x0. split; trivial.
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mcall; eauto. simpl.
  generalize symbols_preserved2; intro. 
  rewrite (symbols_preserved2 p tp TRANSF i) in H6. 
  rewrite H6.  trivial. 
  traceEq.   

  rewrite H6 in H. inversion H. 

  inversion H2. 

  (* tree *)
  inversion H2; subst.
  eapply validTreeProp_correct_1; eauto.
  inversion H4. 
  inversion H4. 
   
  (* refl *)
  exists c. 
  split. trivial. split. eapply Machabstr.exec_refl; eauto. 
  eapply find_label_suff; eauto. 

  (* trans *) 
  rewrite H4 in H. 
  assert (wf_cfg tf = true).
    simpl in H7. 
    case_eq (transf_function f); intros. 
    rewrite H10 in H7. 
    generalize (invert_transf _ _ H10); intro.
    destruct H11 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]].
    inversion H7. rewrite <- H12.  trivial.
    rewrite H10 in H7. inversion H7. 
  revert H10. intro WF2.   
  generalize (link_gen _ _ _ _ _ H8 WF2 H9 H); intro.  
  generalize (H1 _ _ _ H4 H5 H10 H7); intro. 
  destruct H11. destruct H11.  destruct H11.  
  assert (find_label lbl' (fn_code f) = Some x).  eapply label_unicity_prop_gen; eauto. 
  assert (suffix x (fn_code f)). eapply suff_lab; eauto.  
  assert (validLabel f tf (remove (PTree.xkeys (cfg_code (fn_body tf)) xH)
          (cfg_head (fn_body tf))) lbl' = true).
    simpl in H7. case_eq (transf_function f); intros. 
    rewrite H15 in H7. inversion H7; subst.
    generalize (invert_transf _ _ H15); intro. 
    destruct H4 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
    unfold validCFG in VAL. 
     eapply fold_prop; eauto. eapply wf_instr; eauto.
     rewrite H15 in H7. inversion H7.  
  generalize (H3 _ _ _ H4 H14 H6 H7 H15 H13); intros.
  destruct H16. exists x0. intuition.  
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mlabel; eauto.
  traceEq.
 
 destruct H11. destruct H11.  
 assert (exists xx, suffix (Mlabel lbl' :: xx) (fn_code f)). 
   simpl in H7. case_eq (transf_function f); intros. 
   generalize (invert_transf _ _ H13); intro. 
    destruct H14 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]].
    eapply check_target_prop; eauto. 
    rewrite H13 in H7. inversion H7. 
 destruct H13 as [xx SUFXX]. 
  assert (find_label lbl' (fn_code f) = Some xx).  eapply label_unicity_prop_gen; eauto. 
  assert (suffix xx (fn_code f)). eapply suff_lab; eauto.  
  assert (validLabel f tf (remove (PTree.xkeys (cfg_code (fn_body tf)) xH) (cfg_head (fn_body tf))) lbl' = true).
    simpl in H7. case_eq (transf_function f); intros. 
    rewrite H15 in H7. inversion H7; subst.
    generalize (invert_transf _ _ H15); intro. 
    destruct H4 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
    unfold validCFG in VAL. 
     eapply fold_prop; eauto. eapply wf_instr; eauto.
     rewrite H15 in H7. inversion H7.  
  generalize (H3 _ _ _ H4 H14 H6 H7 H15 H13); intros.
  destruct H16. exists x0. intuition.    
  assert (Machabstr.exec_instrs (Genv.globalenv p) f sp parent (Mgoto lbl' :: x) rs' fr' m' E0 xx rs' fr' m').
    eapply Machabstr.exec_one; eauto.
    eapply Machabstr.exec_Mgoto; eauto. 
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_trans; eauto.
  traceEq. 

  destruct H11. destruct H11. destruct H11. 
 assert (exists xx, suffix (Mlabel lbl' :: xx) (fn_code f)). 
   simpl in H7. case_eq (transf_function f); intros. 
   generalize (invert_transf _ _ H13); intro. 
    destruct H14 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]].
    destruct H12. eapply check_target_prop2; eauto.  
    rewrite H13 in H7. inversion H7. 
 destruct H13 as [xx SUFXX]. 
  assert (find_label lbl' (fn_code f) = Some xx).  eapply label_unicity_prop_gen; eauto. 
  assert (suffix xx (fn_code f)). eapply suff_lab; eauto.  
  assert (validLabel f tf (remove (PTree.xkeys (cfg_code (fn_body tf)) xH) (cfg_head (fn_body tf))) lbl' = true).
    simpl in H7. case_eq (transf_function f); intros. 
    rewrite H15 in H7. inversion H7; subst.
    generalize (invert_transf _ _ H15); intro. 
    destruct H4 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]]. 
    unfold validCFG in VAL. 
     eapply fold_prop; eauto. eapply wf_instr; eauto.
     rewrite H15 in H7. inversion H7.  
  generalize (H3 _ _ _ H4 H14 H6 H7 H15 H13); intros.
  destruct H16. exists x2. intuition.    
  assert (Machabstr.exec_instrs (Genv.globalenv p) f sp parent (Mach.Mcond x0 x1 lbl' :: x) rs' fr' m' E0 xx rs' fr' m').
    eapply Machabstr.exec_one; eauto.
    eapply Machabstr.exec_Mcond_true; eauto. 
  eapply Machabstr.exec_trans; eauto.
  eapply Machabstr.exec_trans; eauto.
  traceEq.   


  (* funct_body *)
  assert (transf_fundef (Internal f0) = Some (Internal f)).
    simpl. rewrite H5. trivial.
  generalize (invert_transf _ _ H5); intro. 
  destruct H7 as [t' [[ELAB [MK VAL]] [UNI [WF [HE1 [HN [VE [SHMOK [HE2 [RET GOTO]]]]]]]]]].  

  assert (validLabel f0 f (remove (PTree.xkeys (cfg_code (fn_body f)) xH) (cfg_head (fn_body f))) lw = true).
    unfold validCFG in VAL. 
    eapply fold_prop; eauto. 

    (* monstrueux *)
    generalize (isIn _ _ _ H4); intro. 
    assert (lw <> (cfg_head (fn_body f))). 
      case_eq (peq lw (cfg_head (fn_body f))); intros. 
      clear H8. rewrite <- e in RET. 
      assert ((cfg_code (fn_body f)) ! lw = (Two_level_repr.cfg_code (Two_level_repr.fn_body f)) ! lw). trivial. 
     (* rewrite H8 in RET. *)
      rewrite H4 in RET. inversion RET.
      trivial. 
      generalize (mem_complete _ _ HE1); intro.
      
    eapply remove_prop2; eauto. 
  unfold validLabel in H7. 

  assert ((cfg_code (fn_body f)) ! lw = Some Two_level_repr.Mreturn).
    trivial. 

  rewrite H8 in H7. 
  case_eq (find_label lw (fn_code f0)); intros. 
    rewrite H9 in H7. 
    case_eq c; intros.
    rewrite H10 in H7.  congruence. 
    rewrite H10 in H7. 
    destruct i; inversion H7. clear H7. 

  assert (suffix (tail (fn_code f0)) (fn_code f0)). eapply suff_tail; eauto.
  assert (head (fn_code f0) = Some (Mlabel (cfg_head (fn_body f)))).
    destruct (head (fn_code f0)); try (inversion HE2). clear H12. 
    destruct i; try (inversion HE2). clear H12. 
    case_eq (peq l0 (cfg_head (fn_body f))); intros. 
    clear H11. subst; trivial.
    rewrite H11 in HE2. inversion HE2. 
  assert (Mlabel (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) :: tail (fn_code f0) = (fn_code f0)).  
    destruct (fn_code f0). 
    inversion H11. 
    simpl in H11. inversion H11; subst. simpl. trivial.
    revert H12; intro H16. 
  assert (find_label (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) (fn_code f0) = Some (tail (fn_code f0))). 
     rewrite <- H16. simpl. 
     assert ((if peq (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) then true else false) = true).
     destruct (Two_level_repr.cfg_head (Two_level_repr.fn_body f)). 
       case_eq (peq (xI l0) (xI l0)); intros. trivial. congruence. 
       case_eq (peq (xO l0) (xO l0)); intros. trivial. congruence.
       case_eq (peq 1 1); intros. trivial. congruence.  
     rewrite H12. trivial.  
   assert ( validLabel f0 f (remove (PTree.xkeys (cfg_code (fn_body f)) xH) (cfg_head (fn_body f)))
    (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) = true). trivial. (* unfold validCFG in VAL. eapply fold_prop; eauto. *) 
    (* eapply mem_correct; eauto. *)
  generalize (H3 f0 f (tail (fn_code f0)) (refl_equal (fn_body f)) H7 UNI H6 H13 H12); intro.
  destruct H14 as [w [FL [HYP INCL]]]. 
  clear H16. 
  assert (Two_level_repr.fn_stacksize f = Mach.fn_stacksize f0). subst; trivial.  
  assert (Two_level_repr.init_frame f = Machabstr.init_frame f0). subst; trivial. 
  assert (Two_level_repr.fn_framesize f = Mach.fn_framesize f0). subst; trivial. 
  rewrite H14 in *|-. rewrite H15 in *|-. rewrite H16 in *|-. 
 eapply Machabstr.exec_funct_body; eauto.   
  assert (Mlabel (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) :: tail (fn_code f0) = (fn_code f0)).  
  destruct (fn_code f0). 
  inversion H11. 
  simpl in H11. inversion H11; subst. simpl. trivial. 
  assert (Machabstr.exec_instrs (Genv.globalenv p) f0
  (Vptr stk (Int.repr (- Mach.fn_framesize f0))) parent (fn_code f0) rs fr2 m1 E0 (tail (fn_code f0)) rs fr2 m1).
  rewrite <- H17. 
  eapply Machabstr.exec_one; eauto.
  eapply Machabstr.exec_Mlabel; eauto.
  assert (t = E0 ** t). traceEq. 
  generalize (Machabstr.exec_trans _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _ _ _ H18 HYP H19); intro.
  rewrite H10 in H9. rewrite FL in H9. inversion H9. rewrite H22 in H20. eapply H20; eauto.  
  rewrite H9 in H7. inversion H7. 
(* 
  assert (Mlabel (Two_level_repr.cfg_head (Two_level_repr.fn_body f)) :: tail (fn_code f0) = (fn_code f0)).  
    destruct (fn_code f0). 
    inversion H11. 
    simpl in H11. inversion H11; subst. simpl. trivial. 
  rewrite H17 in HYP.
  
  assert (c = w). 
    assert (find_label lw (fn_code f0) = Some w). eapply label_unicity_prop_gen; eauto.
    rewrite H19 in H9. inversion H9; trivial. 

  assert (exists w', w = Mach.Mreturn :: w'). 
    exists l. congruence.   
  destruct H20 as [w' REW]. 
 
  assert (Machabstr.exec_instrs (Genv.globalenv p) f0
        (Vptr stk (Int.repr (- Mach.fn_framesize f0))) parent (Mlabel lw :: Mach.Mreturn :: w') rs' fr3 m2
        E0 (Mach.Mreturn :: w') rs' fr3 m2 ).
        eapply Machabstr.exec_one; eauto.
        eapply Machabstr.exec_Mlabel; eauto.
  assert (t = t ** E0). traceEq.
  rewrite REW in HYP. 
  generalize (Machabstr.exec_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t HYP H20 H21); intro.  

  eapply Machabstr.exec_funct_body; eauto.

  rewrite H9 in H7. congruence. 
*)
  (* internal *)
  destruct f0. 
  unfold transf_fundef in H1. 
  case_eq (transf_function f0); intros.  
  rewrite H2 in H1. 
  eapply Machabstr.exec_funct_internal; eauto.
  intros. eapply H0; eauto. 
  congruence.
  rewrite H2 in H1. congruence. 
  simpl in H1. congruence. 

  (* external *)
  destruct f. 
  unfold transf_fundef in H2. case_eq (transf_function f); intros. 
  rewrite H3 in H2. congruence. rewrite H3 in H2. congruence.
  simpl in H2. inversion H2. 
  eapply Machabstr.exec_funct_external; eauto.
Qed. 
  
Theorem transf_correct_1:
  forall p tp t r,
  transf_program p = Some tp ->
  Two_level_repr.exec_program tp t r ->
  Machabstr.exec_program p t r.
Proof. 
  intros. 
  unfold Machabstr.exec_program.
  unfold Two_level_repr.exec_program in H0. 
  destruct H0 as [b [f [rs [m [D [E [F G]]]]]]].
  generalize (symbols_preserved p tp H (prog_main p)); intro.
  generalize (function_ptr_translated p tp b f E); intro.
  destruct H1 as [tf [I J]]. 
  exists b; exists tf; exists rs; exists m.
  assert (prog_main p = prog_main tp). 
    rewrite (transform_partial_program_main transf_fundef p H).
    trivial. 
  intuition auto.
  rewrite <- H0. rewrite H1.  trivial. 
  eapply validLabel_correct; eauto. 
  rewrite <- (Genv.init_mem_transf_partial transf_fundef p H). 
  trivial. 
Qed. 