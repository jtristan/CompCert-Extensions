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

Require Import Valcommon.
Require Import BasicLib. 

Require Import MachToTreeVal.
Require Import MachToTreeVal_util.
Require Import MachToTreeVal_proof1.
Require Import MachToTreeVal_proof2.
Require Import Two_level_repr.
Require Import ExtValcommon.
Require Import Tracever.
Require Import LabelCleaning. 
Require Import LabelCleaningproof. 
Require Import LabelSync. 
Require Import LabelSyncproof. 

Require Import Machtyper. 

Parameter trace_scheduling : Mach.code -> option Mach.code. 

Definition transf_function f : option Mach.function :=
  match trace_scheduling (fn_code f) with 
  | None => None
  | Some tc =>
         Some (Mach.mkfunction (Mach.fn_sig f) tc (Mach.fn_stacksize f) (Mach.fn_framesize f)) 
  end.

Definition transf_fundef (f: Mach.fundef) : option Mach.fundef :=
match f with
  | Internal f => 
       match transf_function f with
       | None => None
       | Some f => Some (Internal f)
       end
  | External f => Some (External f)
  end.

Definition transf_program (p: Mach.program) : option Mach.program :=
  let p := sync_program (clean_program p) in
  match transform_partial_program transf_fundef p with
  | Some tp => 
          match MachToTreeVal.transf_program p with
          | Some p_tree =>
                      match MachToTreeVal.transf_program tp with 
                      | Some tp_tree => if Tracever.check_program p_tree tp_tree 
                                                  then (if typer tp then Some tp else None) else None
                      | None => None
                      end
          | None => None
          end
  | None => None
  end.

Theorem transformation_correct:
  forall p tp t r,
  transf_program p = Some tp ->
  Machabstr.exec_program p t r ->
  Machabstr.exec_program tp t r.
Proof. 
  intros. 
  unfold transf_program in H. 
  remembertac pr (sync_program (clean_program p)). 
  case_eq (transform_partial_program transf_fundef pr); intros. 
  rewrite H1 in H. 
  case_eq (MachToTreeVal.transf_program pr); intros. 
  rewrite H2 in H. 
  case_eq (MachToTreeVal.transf_program p0); intros. 
  rewrite H3 in H. 
  case_eq (check_program p1 p2); intros. 
  rewrite H4 in H.
  case_eq (typer p0); intros. 
  rewrite H5 in H.  
  inversion H; subst.
  eapply transf_correct_1; eauto.
  eapply check_correct; eauto. 
  eapply transf_correct_2; eauto.
  eapply sync_program_correct; eauto. 
  eapply clean_program_correct; eauto.
  rewrite H5 in H. inversion H.  
  rewrite H4 in H. inversion H. 
  rewrite H3 in H. inversion H. 
  rewrite H2 in H. inversion H. 
  rewrite H1 in H. inversion H. 
Qed.   

Theorem transf_program_preserve_typing:
  forall p tp,
  transf_program p = Some tp ->
  Machtyping.wt_program tp.
Proof. 
  intros. 
  unfold transf_program in H. 
  remembertac pr (sync_program (clean_program p)). 
  case_eq (transform_partial_program transf_fundef pr); intros. 
  rewrite H0 in H. 
  case_eq (MachToTreeVal.transf_program pr); intros. 
  rewrite H1 in H. 
  case_eq (MachToTreeVal.transf_program p0); intros. 
  rewrite H2 in H. 
  case_eq (check_program p1 p2); intros. 
  rewrite H3 in H.
  case_eq (typer p0); intros.
  rewrite H4 in H. 
  inversion H; subst.  
  eapply Machtyper.typer_correct; eauto.
  rewrite H4 in H. inversion H. 
  rewrite H3 in H. inversion H. 
  rewrite H2 in H. inversion H. 
  rewrite H1 in H. inversion H. 
  rewrite H0 in H. inversion H.
Qed.     

