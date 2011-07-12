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
Require Import AnticipabilityChecker.

Section AN2. 

Variable ge : genv. 

(** We first define the specification of the function and show correctness wrt this spec *)

Section ANT. 

Variable cfg : RTL.code. 
Variable a : approx. 

Fixpoint ant_spec (pc : node) (cmpt : nat) {struct cmpt} : bool :=
  match cmpt with 
  | O => false
  | S n =>
          match cfg!pc with
          | Some (Ireturn _) => false
          | Some (Itailcall _ _ _) => false
          | Some (Icond _ _ s1 s2) => ant_spec s1 n && ant_spec s2 n                    
          | Some (Inop s) => ant_spec s n                                          
          | Some (Icall _ _ _ r s) => false
          | Some (Ialloc _ r s) => 
                     if memory_sensible a then false
                     else
                     if AnticipabilityChecker.sensible a r then false
                     else ant_spec s n 
          | Some (Istore _ _ _ _ s) => 
                     if memory_sensible a then false
                     else ant_spec s n 
          | Some (Iop op args r s) => 
                     if AnticipabilityChecker.sensible a r then false
                     else
                     if Approx.beq a (Op op args) then true
                     else ant_spec s n                         
          | Some (Iload chk addr args r s) =>
                     if AnticipabilityChecker.sensible a r then false
                     else
                     if Approx.beq a (Load chk addr args) then true
                     else ant_spec s n                                                                            
          | None => false
          end
   end. 
  
End ANT.

Definition state_inv (st : info_map) g a : Prop := 
  forall pc, 
    match st!pc with
    | Some Found => exists N, ant_spec g a pc N = true
    | Some NotFound => True
    | Some Visited => True
    | Some Dunno => True   
    | None => True
    end. 

Lemma state_visited :
  forall st g a pc,
  state_inv st g a ->
  state_inv (PTree.set pc Visited st) g a. 
Proof. 
  intros. 
  unfold state_inv in H. 
  unfold state_inv. intro. 
  generalize (peq pc0 pc); intro. 
  destruct H0. 

  subst. rewrite PTree.gss. trivial. 
  
  rewrite PTree.gso; auto. 
  generalize (H pc0); intro. trivial. 
Qed. 

Lemma ant_spec_increase :
  forall n g a pc m,
  ant_spec g a pc n = true -> (m > n)%nat -> ant_spec g a pc m = true.
Proof. 
  induction n; intros. 
  simpl in H. inversion H.
  destruct m. elimtype False. omega.
  assert (m > n)%nat. omega.    
  simpl in H. simpl. 
  case_eq (g ! pc); intros. rewrite H2 in H.   
  case_eq i; intros; rewrite H3 in H. 

  generalize (IHn g a n0 m H H1); intro. trivial.  
  repeat killif H. 
       rewrite EQ. rewrite EQ0. trivial. 
       rewrite EQ. rewrite EQ0. trivial. eapply IHn; eauto.
  repeat killif H. 
       rewrite EQ. rewrite EQ0. trivial. 
       rewrite EQ. rewrite EQ0. trivial. eapply IHn; eauto.
  repeat killif H. 
       rewrite EQ. eapply IHn; eauto.        
  inversion H. 
  inversion H. 
  repeat killif H. 
       rewrite EQ. rewrite EQ0. eapply IHn; eauto.
  assert (ant_spec g a n0 n = true /\ ant_spec g a n1 n = true). 
     destruct (ant_spec g a n0 n); destruct (ant_spec g a n1 n).
     split; trivial. simpl in H. inversion H. simpl in H. inversion H. simpl in H. inversion H. 
  destruct H4. 
  generalize (IHn g a n0 m H4 H1); intro.
  generalize (IHn g a n1 m H5 H1); intro.
  rewrite H6. rewrite H7. trivial. 
  inversion H. 
  rewrite H2 in H. inversion H.
Qed.   
       
Lemma ant_checker_correct_aux :
  forall n g a pc st st',
  state_inv st g a ->
  ant_checker g a pc st n = (st',true) ->
  (exists m, ant_spec g a pc m = true) /\ state_inv st' g a.
Proof. 
  induction n; intros.  
  simpl in H0. inversion H0. 
  simpl in H0.
  case_eq (st ! pc); intros.
  2 : rewrite H1 in H0; congruence.  
  rewrite H1 in H0. 
   
  case_eq i; intros; rewrite H2 in H0; try congruence. 
  subst. inversion H0; subst. split; trivial. 
  unfold state_inv in H. 
  generalize (H pc); intro. rewrite H1 in H2. trivial. 


  case_eq (g ! pc); intros; rewrite H3 in H0; subst; try congruence. 
  analyze H0 for i0. 


  case_eq (ant_checker g a n0 (PTree.set pc Visited st) n); intros. subst. 
  rewrite H2 in H0. 
  destruct b; try congruence. 
  inversion H0; subst.   
  assert (state_inv (PTree.set pc Visited st) g a) by (eapply state_visited; eauto).   
  generalize (IHn g a n0 (PTree.set pc Visited st) i H4 H2);intros.
  destruct H5. destruct H5.
  split. 
  exists (S x). simpl. rewrite H3. trivial.
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. 
  subst. 
  rewrite PTree.gss. 
  exists (S x). simpl. rewrite H3. trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H.  generalize (H6 pc0); intro; trivial.   


  subst. split. exists (S 0). simpl. rewrite H3. 
  rewrite EQ0. rewrite EQ1. trivial. 
  inversion H0; subst. 
   (* debut *)
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S 1). simpl. rewrite H3. rewrite EQ0. rewrite EQ1.  trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H.  generalize (H pc0); intro; trivial. 
  
  case_eq (ant_checker g a n0 (PTree.set pc Visited st) n); intros. subst. 
  rewrite H2 in H0. 
  destruct b; try congruence. 
  inversion H0; subst.   
  assert (state_inv (PTree.set pc Visited st) g a) by (eapply state_visited; eauto). 
  generalize (IHn g a n0 (PTree.set pc Visited st) i H4 H2);intros.
  destruct H5. destruct H5. split.  
  exists (S x). simpl. rewrite H3. rewrite EQ0. rewrite EQ1. trivial.
   (* debut *)
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x). simpl. rewrite H3. rewrite EQ0. rewrite EQ1.  trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H6.  generalize (H6 pc0); intro; trivial.   
  
  subst. split. exists (S 0). simpl. rewrite H3. 
  rewrite EQ0. rewrite EQ1. trivial.
   (* debut *)
  inversion H0; subst. 
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S 1). simpl. rewrite H3. rewrite EQ0. rewrite EQ1.  trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H.  generalize (H pc0); intro; trivial.   

  case_eq (ant_checker g a n0 (PTree.set pc Visited st) n); intros. subst. 
  rewrite H2 in H0. 
  destruct b; try congruence. 
  inversion H0; subst.   
  assert (state_inv (PTree.set pc Visited st) g a) by (eapply state_visited; eauto). 
  generalize (IHn g a n0 (PTree.set pc Visited st) i H4 H2);intros.
  destruct H5. destruct H5. split. 
  exists (S x). simpl. rewrite H3. rewrite EQ0. rewrite EQ1. trivial.
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x). simpl. rewrite H3. rewrite EQ0. rewrite EQ1.  trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H6.  generalize (H6 pc0); intro; trivial.   
  

  case_eq (ant_checker g a n0 (PTree.set pc Visited st) n); intros. subst. 
  rewrite H2 in H0. 
  destruct b; try congruence. 
  inversion H0; subst.   
  assert (state_inv (PTree.set pc Visited st) g a) by (eapply state_visited; eauto). 
  generalize (IHn g a n0 (PTree.set pc Visited st) i H4 H2);intros.
  destruct H5. destruct H5. split. 
  exists (S x). simpl. rewrite H3. rewrite EQ0. trivial. 
    unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x). simpl. rewrite H3. rewrite EQ0.  trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H6.  generalize (H6 pc0); intro; trivial.   

  case_eq (ant_checker g a n0 (PTree.set pc Visited st) n); intros. subst. 
  rewrite H2 in H0. 
  destruct b; try congruence. 
  inversion H0; subst.   
  assert (state_inv (PTree.set pc Visited st) g a) by (eapply state_visited; eauto). 
  generalize (IHn g a n0 (PTree.set pc Visited st) i H4 H2);intros.
  destruct H5. destruct H5. split. 
   exists (S x). simpl. rewrite H3. rewrite EQ0. rewrite EQ1.  trivial. 
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x). simpl. rewrite H3. rewrite EQ0. rewrite EQ1.  trivial. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H6.  generalize (H6 pc0); intro; trivial.   

  case_eq (ant_checker g a n0 (PTree.set pc Visited st) n); intros. subst. 
  case_eq (ant_checker g a n1 i n); intros. rewrite H2 in H0.  rewrite H4 in H0. 
  destruct b; destruct b0; simpl in H0; inversion H0; try congruence.
     
  subst. 
  assert (state_inv (PTree.set pc Visited st) g a) by (eapply state_visited; eauto).  
  generalize (IHn g a n0 (PTree.set pc Visited st) i H5 H2);intros. 
  destruct H6. 
  generalize (IHn g a n1 i i0 H7 H4); intro.
  destruct H8. 
  destruct H6; destruct H8. 
  split. 
  assert ((x > x0)%nat \/ (x0 > x)%nat \/ x = x0 ) by omega. 
  destruct H10. 
  exists (S x). simpl. rewrite H3. rewrite H6. simpl. eapply ant_spec_increase; eauto. 
  destruct H10. 
  exists (S x0). simpl. rewrite H3. rewrite H8. 
  assert (ant_spec g a n0 x0= true) by ( eapply ant_spec_increase; eauto).
  rewrite H11. simpl; trivial. 
  subst. exists (S x0). simpl. rewrite H3. rewrite H6. rewrite H8. simpl; trivial.
(* debut *) 
  assert ((x > x0)%nat \/ (x0 > x)%nat \/ x = x0 ) by omega. 
  destruct H10.   
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x). simpl. rewrite H3. rewrite H6. simpl. eapply ant_spec_increase; eauto. 
  rewrite PTree.gso; auto. 
  unfold state_inv in H7.  generalize (H9 pc0); intro; trivial.
  destruct H10. 
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x0). simpl. rewrite H3. rewrite H8. simpl. assert (ant_spec g a n0 x0= true) by (eapply ant_spec_increase; eauto).
  rewrite H11. trivial.  
  rewrite PTree.gso; auto. 
  unfold state_inv in H7.  generalize (H9 pc0); intro; trivial.
  subst. 
  unfold state_inv. intro. 
  generalize (peq pc pc0); intro PEQ. 
  destruct PEQ. subst. 
  rewrite PTree.gss. 
  exists (S x0). simpl. rewrite H3. rewrite H8. simpl.  rewrite H6.  trivial.  
  rewrite PTree.gso; auto. 
  unfold state_inv in H7.  generalize (H9 pc0); intro; trivial.
Qed.          

Lemma state_inv_init_aux :
  forall l st,
    (forall pc x, st ! pc = Some x -> x = Dunno) ->
    forall pc x,
    (fold_left
       (fun (a : PTree.t info) (p : positive * instruction) =>
        PTree.set (fst p) Dunno a) l st) 
    ! pc = Some x -> x = Dunno.
Proof. 
  induction l; intros. 
  simpl in H0. generalize (H pc x H0); intro. rewrite H1 in H0. inversion H0; subst. trivial. 
  assert (a :: l = (cons a nil) ++ l). simpl. trivial. 
  rewrite H1 in H0. 
  rewrite fold_left_app in H0.  
  simpl in H0. 
  assert (forall pc x, (PTree.set (fst a) Dunno st) ! pc = Some x -> x = Dunno). 
    intros. 
    generalize (H pc0); intro. 
    generalize (peq (fst a) pc0); intro. 
   destruct H4.
   subst. rewrite PTree.gss in H2. inversion H2; subst; trivial. 
   rewrite PTree.gso in H2; auto. 
   generalize (IHl _ H2 _ _ H0); intro. trivial. 
Qed.  
 
Lemma state_inv_init_aux2 :
  forall pc g x,  
        (PTree.fold
          (fun (st : PTree.t info) (p : positive) (_ : instruction) =>
           PTree.set p Dunno st) g (PTree.empty info)) ! pc = Some x -> x = Dunno.  
Proof. 
  intros. 
  rewrite PTree.fold_spec in H.
  eapply state_inv_init_aux; eauto. 
  intros. rewrite PTree.gempty in H0. inversion H0. 
Qed.

Lemma state_inv_init :
  forall g a,
  state_inv (     (PTree.fold
          (fun (st : PTree.t info) (p : positive) (_ : instruction) =>
           PTree.set p Dunno st) g (PTree.empty info))) g a.
Proof. 
  intros.  
  unfold state_inv. intro. 
  case_eq ((PTree.fold
     (fun (st : PTree.t info) (p : positive) (_ : instruction) =>
      PTree.set p Dunno st) g (PTree.empty info)) ! pc); intros. 
  generalize (state_inv_init_aux2 _ _ _ H); intro. rewrite H0. trivial. 
  trivial. 
Qed. 
 
Theorem ant_checker_correct :
  forall g a pc n, 
  snd (ant_checker g a pc (PTree.fold (fun st p _ => PTree.set p Dunno st) g (PTree.empty info)) n) = true ->
  exists m, ant_spec g a pc m = true.
Proof. 
  intros. 
  case_eq  (ant_checker g a pc
         (PTree.fold
            (fun (st : PTree.t info) (p : positive) (_ : instruction) =>
             PTree.set p Dunno st) g (PTree.empty info)) n); intros. 
  generalize (state_inv_init g a); intro. 
  rewrite H0 in H. simpl in H. subst. 
  generalize (ant_checker_correct_aux n g a pc _ i H1 H0); intro.
  destruct H. trivial. 
Qed.

(** Then we show that the specification imply the well defidness of approximations, 
       considering that the execution is well defined *)

Inductive well_defined : approx -> std_state -> Prop :=
  | Wd_op : forall st o lr, 
                    (exists v, eval_operation ge st.(sp) o st.(rs)##lr st.(m) = Some v) -> well_defined (Op o lr) st
  |  Wd_load : forall st mc addr lr, 
                        (exists a,  exists v, eval_addressing ge st.(sp) addr st.(rs)##lr = Some a /\
                        Mem.loadv mc st.(m) a = Some v) ->
                        well_defined (Load mc addr lr) st. 
 
Inductive program_continues (ge: genv) (s : state) : Smallstep.program_behavior -> Prop :=
  | program_terminates: forall t s' r,
      Smallstep.star step ge s t s' ->
      final_state s' r ->
      program_continues ge s (Smallstep.Terminates t r)
  | program_diverges: forall T,
      Smallstep.forever step ge s T ->
      program_continues ge s (Smallstep.Diverges T).
  
Lemma mem_unsensible : 
  forall o rs0 lr sp0 x m',
  memory_sensible (Op o lr) = false ->
  eval_operation ge sp0 o rs0 ## lr m' = Some x ->
  forall m, eval_operation ge sp0 o rs0 ## lr m = Some x.
Proof. 
  intros. 
  unfold memory_sensible in H. 
  analyze H for o; subst; trivial. 
Qed. 
 
Lemma spec_imply_wd : 
  forall g a n pc stack sp rs m beh,
  ant_spec (fn_code g) a pc n = true -> 
  program_continues ge (State stack g sp pc rs m) beh ->
  well_defined a (mk_std_state g sp rs m).
Proof. 
  induction n; intros. 
  simpl in H. inversion H.   
  simpl in H.
 
   inversion H0; subst.
  
  (* programme termine *) 

  inversion H1; subst. inversion H2. inversion H3; subst.  
  
  (* Inop*)
  rewrite H13 in H. eapply IHn; eauto. eapply program_terminates; eauto.  

  (* Iop *)
  rewrite H13 in H. 
  case_eq (sensible a res); intros. 
      rewrite H5 in H. inversion H. 
      rewrite H5 in H. 
  case_eq (Approx.beq a (Op op args)); intros.
 
      rewrite H6 in H. 
      unfold Approx.beq in H6. 
      case_eq ( Approx.eq_dec a (Op op args)); intros. 
      clear H7. subst. 
      eapply Wd_op; eauto. 
      rewrite H7 in H6. inversion H6.

  rewrite H6 in H. 
  assert (program_continues ge (State stack g sp pc' rs # res <- v m) (Smallstep.Terminates t2 r)).
      eapply program_terminates; eauto.  
  generalize (IHn _ _ _ _ _ _ H H7); intro.         
  inversion H8; subst. 
      inversion H8; subst.  
      destruct H15. simpl in H10. 
      eapply Wd_op; eauto. 
      exists x. simpl.  
      rewrite extended_gso in H10; auto. 
      unfold sensible in H5. eapply mem_false; eauto.  

      inversion H8; subst.  
      destruct H16 as [a [v0 [A B]]]. 
      eapply Wd_load; eauto. exists a; exists v0. 
      simpl in A. simpl in B. simpl. split; trivial.  
      rewrite extended_gso in A; auto. 
      unfold sensible in H5. eapply mem_false; eauto.           

  (* load *)
  rewrite H13 in H. 
  case_eq (sensible a dst); intros. 
      rewrite H5 in H. inversion H. 
      rewrite H5 in H. 
  case_eq (Approx.beq a (Load chunk addr args)); intros. 
 
      rewrite H6 in H. 
      unfold Approx.beq in H6. 
      case_eq ( Approx.eq_dec a (Load chunk addr args)); intros. 
      clear H7. subst. 
      eapply Wd_load; eauto. 
      rewrite H7 in H6. inversion H6.

  rewrite H6 in H. 
  assert (program_continues ge (State stack g sp pc' rs # dst <- v m) (Smallstep.Terminates t2 r)).
      eapply program_terminates; eauto.  
  generalize (IHn _ _ _ _ _ _ H H7); intro.         
  inversion H8; subst. 
      inversion H8; subst.  
      destruct H16. simpl in H10. 
      eapply Wd_op; eauto. 
      exists x. simpl.  
      rewrite extended_gso in H10; auto. 
      unfold sensible in H5. eapply mem_false; eauto.  

      inversion H8; subst.  
      destruct H17 as [a [v0 [A B]]]. 
      eapply Wd_load; eauto. exists a; exists v0. 
      simpl in A. simpl in B. simpl. split; trivial.  
      rewrite extended_gso in A; auto. 
      unfold sensible in H5. eapply mem_false; eauto.    

(* store *)
  rewrite H13 in H. 
  case_eq (memory_sensible a); intros. 
      rewrite H5 in H. inversion H. 
      rewrite H5 in H.
   assert (program_continues ge (State stack g sp pc' rs m') (Smallstep.Terminates t2 r)).
      eapply program_terminates; eauto.  
    generalize (IHn _ _ _ _ _ _ H H6); intro.         
  inversion H7; subst. 
      inversion H7; subst.  
      destruct H12. simpl in H9. 
      eapply Wd_op; eauto. 
      exists x. simpl.  
      eapply mem_unsensible; eauto. 
 
      simpl in H5. inversion H5. 

  (* call *)
  rewrite H13 in H. inversion H.          

  (* tailcall *)
  rewrite H13 in H. inversion H.          

   (* alloc *)
  rewrite H13 in H. 
  repeat killif H.
  assert (program_continues ge (State stack g sp pc' (rs # res <-  (Vptr b Int.zero)) m') (Smallstep.Terminates t2 r)).
      eapply program_terminates; eauto.  
    generalize (IHn _ _ _ _ _ _ H H5); intro.
    inversion H6; subst. 
    eapply Wd_op; eauto. 
    inversion H6; subst. simpl in H11. destruct H11. exists x. simpl. 
    rewrite extended_gso in H8. eapply mem_unsensible; eauto. 
    unfold sensible in EQ0. 
    eapply mem_false; eauto.               
   
  simpl in EQ. inversion EQ. 
 
  (* cond *)
  rewrite H13 in H. 
  assert (ant_spec (fn_code g) a ifso n = true /\  ant_spec (fn_code g) a ifnot n = true).
    destruct (ant_spec (fn_code g) a ifso n); destruct (ant_spec (fn_code g) a ifnot n). 
    split; trivial. simpl in H; inversion H. simpl in H; inversion H.  simpl in H; inversion H. 
    destruct H5. 
  assert (program_continues ge (State stack g sp ifso rs m) (Smallstep.Terminates t2 r)).
      eapply program_terminates; eauto.
    generalize (IHn _ _ _ _ _ _ H5 H7); intro.
    trivial. 

  (* cond *)   
  rewrite H13 in H. 
  assert (ant_spec (fn_code g) a ifso n = true /\  ant_spec (fn_code g) a ifnot n = true).
    destruct (ant_spec (fn_code g) a ifso n); destruct (ant_spec (fn_code g) a ifnot n). 
    split; trivial. simpl in H; inversion H. simpl in H; inversion H.  simpl in H; inversion H. 
    destruct H5. 
  assert (program_continues ge (State stack g sp ifnot rs m) (Smallstep.Terminates t2 r)).
      eapply program_terminates; eauto.
    generalize (IHn _ _ _ _ _ _ H6 H7); intro.
    trivial. 

  (* return *)
  rewrite H13 in H. inversion H. 
 
  (* le progrqmme ne termine pas *)

  inversion H1; subst. inversion H2; subst. 

  (* Inop*)
  rewrite H12 in H. eapply IHn; eauto. eapply program_diverges; eauto. 

  (* Iop *)
  rewrite H12 in H. 
  case_eq (sensible a res); intros. 
      rewrite H4 in H. inversion H. 
      rewrite H4 in H. 
  case_eq (Approx.beq a (Op op args)); intros.
 
      rewrite H5 in H. 
      unfold Approx.beq in H5. 
      case_eq ( Approx.eq_dec a (Op op args)); intros. 
      clear H6. subst. 
      eapply Wd_op; eauto. 
      rewrite H6 in H5. inversion H5.

  rewrite H5 in H.
  assert (program_continues ge ((State stack g sp pc' rs # res <- v m)) (Smallstep.Diverges T0)). 
      eapply program_diverges; eauto.  
  generalize (IHn _ _ _ _ _ _  H H6); intro.         
  inversion H7; subst. 
      inversion H7; subst.  
      destruct H14. simpl in H9. 
      eapply Wd_op; eauto. 
      exists x. simpl.  
      rewrite extended_gso in H9; auto. 
      unfold sensible in H4. eapply mem_false; eauto.  
  
      inversion H7; subst.  
      destruct H15 as [a [v0 [A B]]]. 
      eapply Wd_load; eauto. exists a; exists v0. 
      simpl in A. simpl in B. simpl. split; trivial.  
      rewrite extended_gso in A; auto. 
      unfold sensible in H4. eapply mem_false; eauto. 

  (* load *)
  rewrite H12 in H. 
  case_eq (sensible a dst); intros. 
      rewrite H4 in H. inversion H. 
      rewrite H4 in H. 
  case_eq (Approx.beq a (Load chunk addr args)); intros. 
 
      rewrite H5 in H. 
      unfold Approx.beq in H5. 
      case_eq ( Approx.eq_dec a (Load chunk addr args)); intros. 
      clear H6. subst. 
      eapply Wd_load; eauto. 
      rewrite H6 in H5. inversion H5.

  rewrite H5 in H. 
  assert (program_continues ge (State stack g sp pc' rs # dst <- v m) (Smallstep.Diverges T0)).
      eapply program_diverges; eauto.  
  generalize (IHn _ _ _ _ _ _ H H6); intro.         
  inversion H7; subst. 
      inversion H7; subst.  
      destruct H15. simpl in H9. 
      eapply Wd_op; eauto. 
      exists x. simpl.  
      rewrite extended_gso in H9; auto. 
      unfold sensible in H5. eapply mem_false; eauto.  

      inversion H7; subst.  
      destruct H16 as [a [v0 [A B]]]. 
      eapply Wd_load; eauto. exists a; exists v0. 
      simpl in A. simpl in B. simpl. split; trivial.  
      rewrite extended_gso in A; auto. 
      unfold sensible in H4. eapply mem_false; eauto.    

(* store *)
  rewrite H12 in H. 
  case_eq (memory_sensible a); intros. 
      rewrite H4 in H. inversion H. 
      rewrite H4 in H.
   assert (program_continues ge (State stack g sp pc' rs m') (Smallstep.Diverges T0)).
      eapply program_diverges; eauto.  
    generalize (IHn _ _ _ _ _ _ H H5); intro.         
  inversion H6; subst. 
      inversion H6; subst.  
      destruct H11. simpl in H8. 
      eapply Wd_op; eauto. 
      exists x. simpl.  
      eapply mem_unsensible; eauto. 
 
      simpl in H4. inversion H4. 

  (* call *)
  rewrite H12 in H. inversion H.          

  (* tailcall *)
  rewrite H12 in H. inversion H.          

   (* alloc *)
  rewrite H12 in H. 
  repeat killif H.
  assert (program_continues ge (State stack g sp pc' (rs # res <-  (Vptr b Int.zero)) m') (Smallstep.Diverges T0)).
      eapply program_diverges; eauto.  
    generalize (IHn _ _ _ _ _ _ H H4); intro.
    inversion H5; subst. 
    eapply Wd_op; eauto. 
    inversion H5; subst. simpl in H10. destruct H10. exists x. simpl. 
    rewrite extended_gso in H7. eapply mem_unsensible; eauto. 
    unfold sensible in EQ0. 
    eapply mem_false; eauto.               
   
  simpl in EQ. inversion EQ. 
 
  (* cond *)
  rewrite H12 in H. 
  assert (ant_spec (fn_code g) a ifso n = true /\  ant_spec (fn_code g) a ifnot n = true).
    destruct (ant_spec (fn_code g) a ifso n); destruct (ant_spec (fn_code g) a ifnot n). 
    split; trivial. simpl in H; inversion H. simpl in H; inversion H.  simpl in H; inversion H. 
    destruct H4. 
  assert (program_continues ge (State stack g sp ifso rs m) (Smallstep.Diverges T0)).
      eapply program_diverges; eauto.
    generalize (IHn _ _ _ _ _ _ H4 H6); intro.
    trivial. 

  (* cond *)   
  rewrite H12 in H. 
  assert (ant_spec (fn_code g) a ifso n = true /\  ant_spec (fn_code g) a ifnot n = true).
    destruct (ant_spec (fn_code g) a ifso n); destruct (ant_spec (fn_code g) a ifnot n). 
    split; trivial. simpl in H; inversion H. simpl in H; inversion H.  simpl in H; inversion H. 
    destruct H4. 
  assert (program_continues ge (State stack g sp ifnot rs m) (Smallstep.Diverges T0)).
      eapply program_diverges; eauto.
    generalize (IHn _ _ _ _ _ _ H5 H6); intro.
    trivial. 

  (* return *)
  rewrite H12 in H. inversion H.
Qed.  

End AN2.    

Lemma ant_standard:
  forall f o l x pc,
  ant_spec (fn_code f) (Op o l) pc x = true ->
  forall e, In e l -> In e (compute_standard_regs (fn_code f)).
Proof. 
  induction x; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  case_eq ((fn_code f) ! pc); intros. 
  rewrite H1 in H. 
  destruct i. 
  eapply IHx; eauto. 
  repeat killif H. unfold Approx.beq in EQ0. killif EQ0. 
  clear EQ1. inversion e0; subst. eapply regs_prop; eauto. simpl. right; trivial. 
  eapply IHx; eauto. 
  repeat killif H. unfold Approx.beq in EQ0.  killif EQ0. eapply IHx; eauto.  
  destruct o; try congruence; eapply IHx; eauto. 
  inversion H.
  inversion H. 
  destruct o; try congruence; killif H; eapply IHx; eauto.
  assert (ant_spec (fn_code f) (Op o l) n x = true). 
      destruct (ant_spec (fn_code f) (Op o l) n x); destruct (ant_spec (fn_code f) (Op o l) n0 x). 
      trivial. simpl in H; congruence. simpl in H; congruence. simpl in H; congruence. 
  eapply IHx; eauto.          
  inversion H. 
  rewrite H1 in H. inversion H. 
Qed. 

Lemma ant_standard_load:
  forall f mc addr l x pc,
  ant_spec (fn_code f) (Load mc addr l) pc x = true ->
  forall e, In e l -> In e (compute_standard_regs (fn_code f)).
Proof. 
  induction x; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  case_eq ((fn_code f) ! pc); intros. 
  rewrite H1 in H. 
  destruct i. 
  eapply IHx; eauto. 
  repeat killif H. unfold Approx.beq in EQ0. killif EQ0. eapply IHx; eauto.
  repeat killif H.  unfold Approx.beq in EQ0.  killif EQ0. clear EQ1. inversion e0; subst. 
  eapply regs_prop; eauto. simpl. right; trivial. 
  unfold Approx.beq in EQ0.  killif EQ0. eapply IHx; eauto.     
  inversion H.
  inversion H.
  inversion H. 
  inversion H.  
  assert (ant_spec (fn_code f) (Load mc addr l) n x = true).  
      destruct (ant_spec (fn_code f) (Load mc addr l) n x); destruct (ant_spec (fn_code f) (Load mc addr l) n0 x). 
      trivial. simpl in H; congruence. simpl in H; congruence. simpl in H; congruence. 
  eapply IHx; eauto.          
  inversion H. 
  rewrite H1 in H. inversion H. 
Qed. 
