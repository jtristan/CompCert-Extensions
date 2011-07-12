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
Require Import RTL2. 
Require Import Lattice.
Require Import Kildall.
Require Import DecidableType. 
Require Import FSetWeakInterface. 
Require Import FSetWeakFacts. 
Require Import FSetWeakProperties. 
Require Import FSetWeakList. 
Require Import Errors. 
Require Import Utilities. 
Require Import EqualityAnalysis. 
Require Import EqualityAnalysisproof. 
Require Import AnticipabilityChecker. 
Require Import Unification. 
Require Import Val. 
Require Import String. 

Module M : UnificationEngine.

Definition em := msg "Validation failure : lazy code motion\n".

Parameter transformation : function -> code. 

Fixpoint check_op_aux (inf : D.t) inf' a a' N {struct N} : bool :=
  match N with 
  | S N =>
      if Approx.eq_dec a a' then true (* The two instructions are identical up to successors and destination *)
      else                            (* otherwise we can try to unify them *)
      match a, a' with 
      (* maybe we are facing some redundancy elimination *)
      | _ , Op Omove (cons r nil) => let a' := D.get r inf' in 
                                     if Approx.eq_dec a' Unknown 
                                     then false
                                     else check_op_aux inf inf' a a' N (* what about NoValue ? *)
      | _, _ => false
      end
  | O => false
  end.

Definition check_op (f tf : function) (inf inf' : D.t) a a': bool :=
   check_op_aux inf inf' a a' 2. 

Lemma check_op_aux_correct:
  forall ge tge stack f sp pc1 rs m pc1' rs' m' rs2 tf pc2 stack' t o l o0 l0 r0 i j, 
    (forall op sp lv m, eval_operation ge sp op lv m = eval_operation tge sp op lv m) ->
  step ge (State stack f sp pc1 rs m) t (State stack f sp pc1' rs' m') ->
  (fn_code f) ! pc1 = Some i -> (fn_code tf) ! pc2 = Some j -> mask_succ i <> mask_succ j ->
  mask_succ j = MIop o0 l0 r0 -> mask_succ i = MIop o l r0 ->
  respectful (fn_code f) rs rs2 ->
  state_holds ge (analyze f) !! pc1 (State stack f sp pc1 rs m) ->
  state_holds tge (analyze tf) !! pc2 (State stack' tf sp pc2 rs2 m) ->
  check_op_aux (analyze f)!!pc1 (analyze tf) !! pc2 (Op o l) (Op o0 l0) 2 = true ->
  exists pc2' : node,
    exists rs2' : regset,
      step tge (State stack' tf sp pc2 rs2 m) t
        (State stack' tf sp pc2' rs2' m') /\ respectful (fn_code f) rs' rs2'.
Proof.
  intros until 1. revert H; intro ENVOP. intros until 7. intro USELESS. intros.   

  unfold check_op_aux in H7. killif H7.     
  analyze H7 for o0 l0. 

        (* ici c est e qui est interessant ! *)
        clear EQ EQ2 n n0 EQ3. subst. 
        unfold state_holds in H6.
        assert ( D.get r (analyze tf)!!pc2 = Op o l) by (symmetry; trivial). clear e.  
        generalize (H6 _ _ H8); intro. clear H6. 
       assert (exists ppc, i = Iop o l r0 ppc). 
        unfold mask_succ in H4. analyze H4 for i. exists n. inversion H4; subst. trivial.  
        destruct H6. inversion H; subst; try congruence; trivial. 
        assert (exists pc2', j = Iop Omove (r :: nil) r0 pc2'). unfold mask_succ in H3. analyze H3 for j. inversion H3; subst; trivial. exists n; trivial.  
        destruct H6 as [pc2' H6]. subst. 
        exists pc2'. exists (rs2 # r0 <- v). 
        split. 
        
        generalize (exec_Iop);intros. 
        generalize (exec_Iop tge stack' _ sp _ rs2 m' _ _ _ _ v H1); intro.
        eapply H6; eauto. clear H6.  
        simpl .
        unfold eq_holds in H9. simpl in H9.

      assert (forall r, In r l -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. right; trivial.
      assert (rs ## l = rs2 ## l) by (eapply sub_respect; eauto).
   
     rewrite <- H11 in H9. rewrite <- ENVOP in H9.   

     congruence.          
      rewrite H0 in H17; inversion H17; subst. 
    eapply respectful_update; eauto. 

        analyze H7 for (D.get r (analyze tf)!!pc2).  
        analyze H7 for o0.  
        analyze H7 for o1. 
        analyze H7 for l1.
Qed.

Lemma check_op_correct:
  forall ge tge stack f sp pc1 rs m pc1' rs' m' rs2 tf pc2 stack' t o l o0 l0 r0 i j, 
    (forall op sp lv m, eval_operation ge sp op lv m = eval_operation tge sp op lv m) ->
  step ge (State stack f sp pc1 rs m) t (State stack f sp pc1' rs' m') ->
  (fn_code f) ! pc1 = Some i -> (fn_code tf) ! pc2 = Some j -> mask_succ i <> mask_succ j ->
  mask_succ j = MIop o0 l0 r0 -> mask_succ i = MIop o l r0 ->
  respectful (fn_code f) rs rs2 ->
  state_holds ge (analyze f) !! pc1 (State stack f sp pc1 rs m) ->
  state_holds tge (analyze tf) !! pc2 (State stack' tf sp pc2 rs2 m) ->
  check_op f tf (analyze f)!!pc1 (analyze tf) !! pc2 (Op o l) (Op o0 l0) = true ->
  exists pc2' : node,
    exists rs2' : regset,
      step tge (State stack' tf sp pc2 rs2 m) t
        (State stack' tf sp pc2' rs2' m') /\ respectful (fn_code f) rs' rs2'.
Proof. 
  intros. 
  unfold check_op in H9. 
  eapply check_op_aux_correct; eauto. 
Qed.    
 
End M.

Module T := Val.Val (M). 



   
  