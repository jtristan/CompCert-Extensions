
Require Import RTL. 
Require Import RTL2. 
Require Import Unification.
Require Import Errors. 
Require Import Validator. 
Require Import Validatorproof. 
Require Import RTL2RTL. 
Require Import AST. 

Module Type VAL. 

  Variable transf_fundef : RTL.fundef -> res RTL.fundef.
  Variable transf_program : RTL.program -> res RTL.program. 

  Hypothesis generic : transf_program  = transform_partial_program transf_fundef.

  Hypothesis transf_program_correct :
       forall prog tprog (beh: Smallstep.program_behavior),
       transf_program prog = OK tprog ->
       RTL.exec_program prog beh -> RTL.exec_program tprog beh.

End VAL. 

Module Val (E : UnificationEngine) : VAL.
 
  Module T := Valigatorproof (E). 
  Definition transf_fundef := T.V.transf_fundef.
  Definition transf_program := T.V.transf_program.
  Theorem transf_program_correct :
       forall prog tprog (beh: Smallstep.program_behavior),
       transf_program prog = OK tprog ->
       RTL.exec_program prog beh -> RTL.exec_program tprog beh.
Proof. 
  intros. 
  eapply RTL2RTL.sem_equiv2; eauto. 
  eapply T.transf_program_correct; eauto.
  eapply RTL2RTL.sem_equiv1; eauto.
Qed.
  Lemma generic :  transf_program  = transform_partial_program transf_fundef.
Proof. 
  unfold transf_program. trivial. 
Qed.      

End Val.  
      
   