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


(* Valigator proof *)

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
Require Import Mem. 
Require Import Events.    
Require Import Utilities. 
Require Import EqualityAnalysis. 
Require Import EqualityAnalysisproof. 
Require Import AnticipabilityChecker. 
Require Import AnticipabilityCheckerproof. 
Require Import Unification. 
Require Import Validator.

Module Valigatorproof (E : UnificationEngine).

Module V := Validator.Valigator (E).  
Module Uni := UE (E). 

Section M.

Definition unification := Uni.unification. 
Definition unification_correct := Uni.unification_correct. 

Lemma symbols_preserved:
  forall prog tprog ge tge, V.transf_program prog = OK tprog -> 
  ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
 forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  unfold transf_program. intros. subst.  
 eapply Genv.find_symbol_transf_partial; eauto.
 unfold V.transf_program in H. 
eauto. 
Qed.

Lemma functions_translated:
  forall prog tprog ge tge, V.transf_program prog = OK tprog -> 
  ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ V.transf_fundef f = OK tf.
Proof.  
  intros. subst. 
  generalize (Genv.find_funct_transf_partial V.transf_fundef H H2); intro.
  trivial. 
Qed.

Lemma function_ptr_translated:
  forall prog tprog ge tge, V.transf_program prog = OK tprog -> 
  ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ V.transf_fundef f = OK tf.
Proof.  
  intros. subst. 
  generalize (Genv.find_funct_ptr_transf_partial V.transf_fundef H H2); intro.
  trivial. 
Qed.

Lemma sig_function_translated:
  forall prog tprog ge tge, V.transf_program prog = OK tprog -> 
  ge = Genv.globalenv prog -> tge = Genv.globalenv tprog ->
  forall f tf, V.transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros. subst. destruct f. simpl. 
  simpl in H2. monadInv H2. simpl. 
  unfold V.transf_function in EQ.
  killif EQ. inversion EQ; subst. simpl; trivial. 
  simpl. 
  simpl in H2. monadInv H2. simpl. trivial.      
Qed.

Section M. 

Variable prog : program. 
Variable tprog : program. 
Hypothesis TRANSF: V.transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma eval_op_env:
  forall op sp lv m,
  eval_operation ge sp op lv m = eval_operation tge sp op lv m.
Proof. 
  intros. 
  destruct op; simpl; try congruence.
  destruct (lv); simpl; try congruence. 
  rewrite (symbols_preserved prog tprog ge tge TRANSF); simpl; try congruence.
  unfold ge. trivial.   
  unfold tge. trivial. 
Qed. 

Lemma eval_addr_env:
  forall sp addr lv,     
  eval_addressing ge sp addr lv = eval_addressing tge sp addr lv.
Proof. 
  intros. 
  destruct addr; simpl; try congruence. 
  destruct lv; simpl; try congruence. 
 rewrite (symbols_preserved prog tprog ge tge TRANSF); simpl; try congruence.
  unfold ge. trivial.   
  unfold tge. trivial. 
  destruct lv; simpl; try congruence.
  destruct v; simpl; try congruence. 
  destruct lv; simpl; try congruence.
 rewrite (symbols_preserved prog tprog ge tge TRANSF); simpl; try congruence.
  unfold ge. trivial.   
  unfold tge. trivial. 
Qed.   

Inductive match_stackframe : stackframe -> stackframe -> Prop :=
  | Mstackframe : forall f tf rs rs' r sp pc pc',
            V.validate f tf = true ->
            respectful (fn_code f) rs rs' ->
            V.crawl_aux f tf pc pc' pc (successors tf) (compute_standard_regs (fn_code f)) (count_nodes tf.(fn_code)) = true -> 
            match_stackframe (Stackframe r f sp pc rs) (Stackframe r tf sp pc' rs').
 
Inductive weak_match : state -> state -> Prop :=
  | Wstate : forall f tf stack stack' sp pc pc' rs m rs',
           V.validate f tf = true ->
           respectful (fn_code f) rs rs' -> 
           list_forall2 match_stackframe stack stack' -> 
           weak_match (State stack f sp pc' rs m) (State stack' tf sp pc rs' m)  
  | Wcall :
       forall stack stack' f tf args m,
       list_forall2 match_stackframe stack stack' ->
       V.transf_fundef f = OK tf ->
       weak_match (Callstate stack f args m) (Callstate stack' tf args m)
  | Wreturn :
       forall stack stack' v m,
       list_forall2 match_stackframe stack stack' -> 
       weak_match (Returnstate stack v m) (Returnstate stack' v m).

Inductive match_states : state -> state -> Prop :=
  | Mstate : forall f tf stack stack' sp pc rs m rs',
           V.validate f tf = true ->
           respectful (fn_code f) rs rs' -> 
           list_forall2 match_stackframe stack stack' -> 
           match_states (State stack f sp pc rs m) (State stack' tf sp pc rs' m)
  | Mcall :
       forall stack stack' f tf args m,
       list_forall2 match_stackframe stack stack' ->
       V.transf_fundef f = OK tf ->
       match_states (Callstate stack f args m) (Callstate stack' tf args m)
  | Mreturn :
       forall stack stack' v m,
       list_forall2 match_stackframe stack stack' -> 
       match_states (Returnstate stack v m) (Returnstate stack' v m).

(** *correctness proof for unification *)



Theorem unification_correct' : 
  forall f tf i j pc1 pc2 sp rs m stack stack' t rs2 pc1' rs' m', 
  match_states (State stack f sp pc1 rs m) (State stack' tf sp pc2 rs2 m)  ->
  state_holds ge (analyze f)!!pc1  (State stack f sp pc1 rs m)  ->
  state_holds tge (analyze tf)!!pc2  (State stack' tf sp pc2 rs2 m)  ->
  (fn_code f)!pc1 = Some i -> (fn_code tf)!pc2 = Some j ->  
  unification f tf (analyze f)!!pc1 (analyze tf)!!pc2 i j = true ->
  step ge (State stack f sp pc1 rs m) t (State stack f sp pc1' rs' m') -> 
  exists pc2', exists rs2',  step tge (State stack' tf sp pc2 rs2 m)  t (State stack' tf sp pc2' rs2' m') /\ weak_match (State stack f sp pc1' rs' m') (State stack' tf sp pc2' rs2' m'). 
Proof. 
  intros until 1. intro NOUV. intros.  
  inversion H4; subst; inversion H; subst.

  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H17 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.
  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H18 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.
  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H19 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.
  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H19 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.  
  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H19 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.
  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H18 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.
  generalize (Uni.unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env eval_addr_env H18 NOUV H0 H1 H2 H3 H4); intro CO.
  destruct CO as [pc2' [rs2' [A B]]]. exists pc2'; exists rs2'; split ;trivial.
   eapply Wstate; eauto.
Qed.    

(** *Proof of correctness of anticipability *)

Lemma ill_defined_prop: 
  forall ge f op args res s pc stack sp rs m st,
  V.ill_defined (Iop op args res s) = false -> 
  f.(fn_code) ! pc = Some (Iop op args res s) ->
  st = State stack f sp pc rs m ->
  exists rs', step ge st Events.E0 (State stack f sp s rs' m).
Proof. 
  intros. 
  unfold V.ill_defined in H. 
  analyze H for op. 
  assert (exists v, eval_operation ge sp (Ointconst i) (rs ## args) m = Some v).
    rewrite EQ0. simpl. exists (Vint i). trivial. 
  destruct H2 as [v H2]. 
  exists (Regmap.set res v rs). 
  subst. eapply exec_Iop; eauto.
  assert (exists v, eval_operation ge sp (Ofloatconst f0) (rs ## args) m = Some v).
    rewrite EQ0. simpl. exists (Vfloat f0). trivial. 
  destruct H2 as [v H2]. 
  exists (Regmap.set res v rs). 
  subst. eapply exec_Iop; eauto.
Qed.   

Theorem anticipable_correct :
  forall f tf pc n st stack stack' sp rs m st2 rs2 beh,
  program_continues ge st beh ->
  V.anticipable (fn_code f) (fn_code tf) pc n = true -> 
  weak_match st st2 ->
  st = State stack f sp pc rs m ->
  st2 = State stack' tf sp n rs2 m ->   
  exists st', step tge st2 E0 st'.
Proof.
  intros. 
  unfold V.anticipable in H0. 
  case_eq ((fn_code tf)!n); intros.
  rewrite H4 in H0. 
  analyze H0 for i.
 
  generalize (ant_checker_correct _ _ _ _ H0); clear H0; intro H0. 
  destruct H0.
      subst. 
      generalize (spec_imply_wd _ _ _ _ _ _ _ _ _ _ H0 H); intro.    
      inversion H2; subst. 
      destruct H7. simpl in H3. 
      exists (State stack' tf sp n0 (rs2 # r <- x0) m). 
      eapply exec_Iop; eauto. rewrite <- eval_op_env. 
      inversion H1; subst. 
      assert (rs ## l = rs2 ## l). eapply sub_respect; eauto. intros. eapply ant_standard; eauto.  
      rewrite <- H5. trivial.
 
  rewrite EQ in H4. 
  generalize (ill_defined_prop tge _ _ _ _ _ _ _ _ _ _ _ EQ0 H4 H3); intro. 
  destruct H5 as [rs' H5]. exists (State stack' tf sp n0 rs' m). 
  trivial. 

  generalize (ant_checker_correct _ _ _ _ H0); clear H0; intro H0. 
  destruct H0.
      subst. 
      generalize (spec_imply_wd _ _ _ _ _ _ _ _ _  _ H0 H); intro.    
      inversion H2; subst. 
      destruct H8. simpl in H3. destruct H3 as [v [A B]].   
      exists (State stack' tf sp n0 (rs2 # r <- v) m). 
      eapply exec_Iload; eauto. rewrite <- eval_addr_env. 
      inversion H1; subst.
      assert (rs ## l = rs2 ## l). eapply sub_respect; eauto. intros. eapply ant_standard_load; eauto.   
      rewrite <- H3. trivial.  

  rewrite H4 in H0. inversion H0.  
Qed.         

Theorem anticipable_correct' :
  forall f tf pc n stack stack' sp rs m rs2 beh,
  program_continues ge (State stack f sp pc rs m) beh ->
  V.anticipable (fn_code f) (fn_code tf) pc n = true -> 
  weak_match (State stack f sp pc rs m) (State stack' tf sp n rs2 m) ->
  exists st', step tge (State stack' tf sp n rs2 m) E0 st'.
Proof. 
  intros. 
  eapply anticipable_correct; eauto. 
Qed. 

(** *Proof of correctness of path Checking *)

Lemma crawl_one:
  forall f tf stack stack' sp0 base source rs1 rs1' m1 n0 beh,
  weak_match (State stack f sp0 base rs1 m1) (State stack' tf sp0 source rs1' m1) ->
  successors tf source = n0 :: nil ->
  is_non_standard (compute_standard_regs (fn_code f)) (fn_code tf) ! source = true ->
  V.anticipable (fn_code f) (fn_code tf) base source = true ->
  program_continues ge (State stack f sp0 base rs1 m1) beh ->
  exists rsi : regset,
  step tge (State stack' tf sp0 source rs1' m1) E0
  (State stack' tf sp0 n0 rsi m1) /\
  weak_match (State stack f sp0 base rs1 m1)
  (State stack' tf sp0 n0 rsi m1). 
Proof. 
  intros. 
  generalize (anticipable_correct' _ _ _ _ _ _ _ _ _ _ _ H3 H2 H); intro.
  destruct H4.
  unfold V.anticipable in H2.
  analyze H2 for ((fn_code tf) ! source). 
  analyze H2 for i.
  
  inversion H4; try congruence; subst.
  exists ( rs1' # res <- v ). 
     split. 
        eapply exec_Iop; eauto. 
        unfold successors in H0. 
        rewrite H12 in H0. 
        inversion H0; subst. trivial. 
        
        inversion H; subst. 
        eapply Wstate; eauto.
        unfold respectful. intros. 
        generalize (peq x res); intro.  
        destruct H6. 
        subst.    

       rewrite H12 in H1. simpl in H1. killif H1. 
       assert (~ In res (compute_standard_regs (fn_code f))). eapply mem_false; eauto.
       congruence.    

        rewrite Regmap.gso; auto.

  inversion H4; try congruence; subst.
  exists ( rs1' # res <- v ). 
     split. 
        eapply exec_Iop; eauto. 
        unfold successors in H0. 
        rewrite H12 in H0. 
        inversion H0; subst. trivial. 
        
        inversion H; subst. 
        eapply Wstate; eauto.
        unfold respectful. intros. 
        generalize (peq x res); intro.  
        destruct H6. 
        subst.    

       rewrite H12 in H1. simpl in H1. killif H1. 
       assert (~ In res (compute_standard_regs (fn_code f))). eapply mem_false; eauto.
       congruence.           

        rewrite Regmap.gso; auto.

  inversion H4; try congruence; subst.
  exists ( rs1' # dst <- v ). 
     split. 
        eapply exec_Iload; eauto. 
        unfold successors in H0. 
        rewrite H12 in H0. 
        inversion H0; subst. trivial. 
        
        inversion H; subst. 
        eapply Wstate; eauto.
        unfold respectful. intros. 
        generalize (peq x dst); intro.  
        destruct H6. 
        subst.    
       rewrite H12 in H1. simpl in H1. killif H1. 
       assert (~ In dst (compute_standard_regs (fn_code f))). eapply mem_false; eauto.
       congruence.    
        rewrite Regmap.gso; auto.   
Qed.      

Theorem crawl_aux_correct :
  forall cmpt f tf stack stack' sp base source rs1 rs1' m1 s1 s1' beh,
  s1 = State stack f sp base rs1 m1 ->
  s1' = State stack' tf sp source rs1' m1 ->
  weak_match s1 s1' ->
  program_continues ge s1 beh->
  V.crawl_aux f tf base source base (successors tf) (compute_standard_regs (fn_code f)) cmpt = true ->
  exists s1'', Smallstep.star step tge s1' E0 s1'' /\ match_states s1 s1''.
Proof. 
  induction cmpt; intros. 
  simpl in H3. inversion H3. 
  simpl in H3. 
  killif H3.
  clear EQ. subst.
  exists (State stack' tf sp base rs1' m1). 
  split; trivial. eapply Smallstep.star_refl; eauto.      

  subst. inversion H1; subst.  eapply Mstate; eauto.
  
  killif H3. 
  analyze H3 for (successors tf source). 
  subst. 
  assert (V.anticipable (fn_code f) (fn_code tf) base source = true /\
     V.crawl_aux f tf base n0 base (successors tf)
       (compute_standard_regs (fn_code f)) cmpt = true). 
     destruct (V.anticipable (fn_code f) (fn_code tf) base source); destruct (V.crawl_aux f tf base n0 base (successors tf)
       (compute_standard_regs (fn_code f)) cmpt). split; trivial. simpl in H3; inversion H3.  simpl in H3; inversion H3.  simpl in H3; inversion H3.  
  destruct H.  
  assert (exists rsi, step tge (State stack' tf sp source rs1' m1) E0 (State stack' tf sp n0 rsi m1) /\ weak_match (State stack f sp base rs1 m1) (State stack' tf sp n0 rsi m1)). 
     eapply crawl_one; eauto. 
  destruct H4 as [rsi [STEP WM]]. 
  inversion WM; subst. 
  set (ss := State stack f sp base rs1 m1). 
  set (st := State stack' tf sp n0 rsi m1).
  assert (ss = State stack f sp base rs1 m1)  by trivial. 
  assert (st = State stack' tf sp n0 rsi m1) by trivial. 
  rewrite <- H4 in WM.  
  rewrite <- H5 in WM.  
  generalize (IHcmpt f tf stack stack' sp base n0 rs1
           rsi m1 ss st beh H4 H5 WM H2 H0); intro.
  destruct H6 as [s1'' [STAR MS]]. 
  exists s1''. split; trivial. 
  eapply Smallstep.star_left; eauto.
Qed.   
 
Theorem crawl_aux_correct' :
  forall cmpt f tf stack stack' sp base source rs1 rs1' m1 beh,
  weak_match (State stack f sp base rs1 m1) (State stack' tf sp source rs1' m1) ->
  program_continues ge (State stack f sp base rs1 m1) beh->
  V.crawl_aux f tf base source base (successors tf) (compute_standard_regs (fn_code f)) cmpt = true ->
  exists s1'', Smallstep.star step tge (State stack' tf sp source rs1' m1) E0 s1'' /\ match_states (State stack f sp base rs1 m1) s1''.
Proof. 
  intros. eapply crawl_aux_correct; eauto. 
Qed. 

(** *Final proof of correctness : if the initial program reduces, the transformed program reduces 
         the same state *)   

Lemma fold_and:
  forall (A : Set) (expr b : bool) (l : list bool) a,
  fold_left (fun b _ => expr && b) l (a && b) = true ->
  a = true.
Proof. 
  intros. 
  destruct a. trivial. 
  elimtype False. 
  induction l; intros. 
  simpl in H. inversion H. 
  eapply IHl; eauto.
  simpl in H. 
  assert (expr && false = false && b). 
      simpl. destruct expr; simpl; congruence.
  rewrite <- H0; trivial.
Qed.     

Lemma full_verif_aux:
  forall f tf info info' link csr n i, 
  link = (fun x => x) ->
  csr = compute_standard_regs (fn_code f) ->
  forall l b, 
       fold_left
       (fun (a : bool) (p : positive * instruction) =>
        V.check_point f tf (fst p) info info' link csr && a)
       l b = true ->
   In (n,i) l ->
  V.check_point f tf n info info' link csr = true.
Proof. 
  induction l; intros. 
  inversion H2. 
  inversion H2. 
  subst.
  simpl in H1.
  destruct (V.check_point f tf n info info' (fun x : node => x)
  (compute_standard_regs (fn_code f)) ). 
  trivial.
  elimtype False. 
  clear IHl H2. 
  induction l; intros. 
  simpl in H1. inversion H1.
  simpl in H1. 
  assert ((   V.check_point f tf (fst a) info info' (fun x : node => x)
          (compute_standard_regs (fn_code f)) && false) = false && b). 
   simpl. destruct (V.check_point f tf (fst a) info info' (fun x : node => x)
  (compute_standard_regs (fn_code f)) ). 
  simpl. trivial. trivial. 
  rewrite H in H1. eapply IHl; eauto.  
  simpl in H1. 
  generalize (IHl _ H1 H3); intro.
  trivial. 
Qed. 

Lemma full_verif:
  forall f tf info info' link csr,
  link = (fun x => x) ->
  csr = compute_standard_regs (fn_code f) ->
  PTree.fold (fun res n i => V.check_point f tf n info info' link csr && res) f.(fn_code) true = true ->
  forall n i, (fn_code f) ! n = Some i ->
  V.check_point f tf n info info' link csr = true.
Proof. 
  intros. 
  rewrite PTree.fold_spec in H1.
  generalize (PTree.elements_correct _ _ H2); intro.
  eapply full_verif_aux; eauto. 
Qed.  

Lemma succ_step:
  forall ge tf n0 pc sp0 stack' rs' m0 rs2' pc2' m0',
  successors tf pc = n0 :: nil ->
  step ge (State stack' tf sp0 pc rs' m0) E0
          (State stack' tf sp0 pc2' rs2' m0') -> n0 = pc2'.
Proof. 
  intros. 
  unfold successors in *|-. 
  inversion H0; subst; 
  try (rewrite H2 in H; inversion H; subst; trivial); 
  try (rewrite H3 in H; inversion H; subst; trivial);
  try (rewrite H4 in H; inversion H; subst; trivial).
Qed.  

Lemma and_and:
  forall a b, a && b = true -> a = true /\ b = true. 
Proof. 
  destruct a; destruct b ; simpl; split; trivial; try congruence.
Qed.  

Lemma same_successors:
  forall f tf,
  fn_code f = fn_code tf ->
  successors f = successors tf.
Proof. 
  intros. 
  unfold successors. rewrite H. trivial. 
Qed. 

Lemma same_transfer:
  forall f tf,
  fn_code f = fn_code tf ->
  transfer f = transfer tf.
Proof. 
  intros. 
  unfold transfer. rewrite H. trivial. 
Qed. 

Lemma same_analyze:
  forall f tf,
  fn_code f = fn_code tf -> fn_entrypoint f = fn_entrypoint tf -> fn_nextpc f = fn_nextpc tf -> analyze f = analyze tf. 
Proof. 
  intros. unfold analyze.
  rewrite H0. 
  rewrite H1. 
  generalize (same_successors _ _ H); intro. 
  rewrite H2.  
  generalize (same_transfer _ _ H); intro. 
  rewrite H3.  
  trivial. 
Qed.   

Theorem test :
  forall u v t u',
  Smallstep.program_was step (initial_state prog) ge u ->
  Smallstep.program_was step (initial_state tprog) tge v ->
  match_states u v ->
  step ge u t u' ->
  forall beh, Smallstep.program_will step final_state ge u' beh -> 
  exists v', Smallstep.plus step tge v t v' /\ match_states u' v'.
Proof.
  intros u v t u' WAS WAS' MATCH STEP beh WILL. 
  inversion STEP; subst. 

  (* Inop *)

  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H7. unfold V.validate_graphs in H7.
  destruct (and_and _ _ H7) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst.  
  generalize (init_correct tge _ _ H0); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H1 INIT); intro HOLDS. 
  clear H0 H1. 

  inversion WAS; subst.  
  generalize (init_correct ge _ _ H0); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H1 INIT2); intro HOLDS2. 
  clear H0 H1. 

   (* unification *)  
    unfold holds in HOLDS. destruct HOLDS as [HO1 HO2].
    unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22]. 
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _  _ _ MATCH HO12 HO1 H EQ UNI STEP); intro WEAK. 

  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.       
   analyze CRAWL for ( map (fun x : node => x) (n :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp pc' rs m) beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 
   rewrite H in EQ0. inversion EQ0; subst. 
   simpl in EQ2. inversion EQ2; subst.   
  assert (EQO : n0 = pc2'). 
      eapply succ_step; eauto. unfold successors; trivial. 
  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT CRAWL); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial.  
    eapply Smallstep.plus_left; eauto.
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0. 

  (* Iop *)
  
  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H10. unfold V.validate_graphs in H10.
  destruct (and_and _ _ H8) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H1); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H2 INIT); intro HOLDS. 
  clear H1 H2.  

  inversion WAS; subst.  
  generalize (init_correct ge _ _ H1); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H2 INIT2); intro HOLDS2. 
  clear H1 H2. 
  unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22]. 

   (* unification *)
    destruct HOLDS as [STH STKH].
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  MATCH HO12 STH H EQ UNI STEP); intro WEAK.
   
  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.       
   analyze CRAWL for ( map (fun x : node => x) (n :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp pc' (rs # res <- v0) m) beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 
   rewrite H in EQ0. inversion EQ0; subst. 
   simpl in EQ2. inversion EQ2; subst.   
  assert (EQO : n0 = pc2'). 
      eapply succ_step; eauto. unfold successors; trivial. 
  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT CRAWL); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto.
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0. 

  (* Iload *)
 
  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H9. unfold V.validate_graphs in H9.
  destruct (and_and _ _ H9) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H2); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H3 INIT); intro HOLDS.
  clear H2 H3. 

  inversion WAS; subst.  
  generalize (init_correct ge _ _ H2); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H3 INIT2); intro HOLDS2. 
  clear H1 H2. 
  unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22].  

   (* unification *)
    destruct HOLDS as [STH STKH].
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  MATCH HO12 STH H EQ UNI STEP); intro WEAK.
   
  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.       
   analyze CRAWL for ( map (fun x : node => x) (n :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp pc' (rs # dst <- v0) m) beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 
   rewrite H in EQ0. inversion EQ0; subst. 
   simpl in EQ2. inversion EQ2; subst.   
  assert (EQO : n0 = pc2'). 
      eapply succ_step; eauto. unfold successors; trivial. 
  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT CRAWL); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto.
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0. 

  (* Istore*)

  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H9. unfold V.validate_graphs in H9.
  destruct (and_and _ _ H9) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H2); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H3 INIT); intro HOLDS.
  clear H2 H3. 

  inversion WAS; subst.  
  generalize (init_correct ge _ _ H2); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H3 INIT2); intro HOLDS2. 
  clear H2 H3. 
  unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22].  

   (* unification *)
    destruct HOLDS as [STH STKH].
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  MATCH HO12 STH H EQ UNI STEP); intro WEAK.
   
  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.       
   analyze CRAWL for ( map (fun x : node => x) (n :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp pc' rs m') beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 
   rewrite H in EQ0. inversion EQ0; subst. 
   simpl in EQ2. inversion EQ2; subst.   
  assert (EQO : n0 = pc2'). 
      eapply succ_step; eauto. unfold successors; trivial. eauto.  
  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT CRAWL); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto.
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0. 

  (* Icall *)
 
  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst. generalize H10; intro BACKUP.  
  unfold V.validate in H10. unfold V.validate_graphs in H10.
  destruct (and_and _ _ H8) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H1); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H2 INIT); intro HOLDS. 
  clear H1 H2.  

   (* unification *)
    destruct HOLDS as [STH STKH].
    unfold state_holds in STH. 

  (* l unification va se faire sur place *)

    assert (exists pc2', i = Icall (funsig fc) ros args res pc2').
          unfold V.unification in UNI. unfold V.M.unification in UNI.   simpl in UNI. 
          case_eq  (inst_ms_eq (MIcall (funsig fc) ros args res) (mask_succ i)); intros. 
          clear H1.  
          unfold mask_succ in e. analyze e for i. exists n; trivial. inversion e ;subst; trivial.
          rewrite H1 in UNI. inversion UNI.
     
    destruct H1. subst. 
     assert (exists tf, find_function tge ros rs' = Some tf /\ V.transf_fundef fc = OK tf).
              unfold find_function. unfold find_function in H0. 
              destruct ros. eapply functions_translated; eauto. 
                   
              assert (rs # r = rs' # r). 
                  eapply sub_respect_simple; eauto.
                  eapply regs_prop; eauto. simpl.  left. trivial.
                  rewrite <- H1. trivial.  

       rewrite <- (symbols_preserved prog tprog ge tge) in H0.          
      destruct (Genv.find_symbol tge i). eapply function_ptr_translated; eauto. 
                  inversion H0.
                  trivial. unfold ge; trivial. unfold tge; trivial.  

     destruct H1 as [tfx [H6 TF]].  
     exists (Callstate (Stackframe res tf sp x rs' :: stack') tfx (rs' ## args) m).
        
     assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. destruct ros. right; right; trivial.  right; trivial.   
     assert (rs ## args = rs' ## args) by (eapply sub_respect; eauto). 
   split; trivial.           
   eapply Smallstep.plus_one; eauto. eapply exec_Icall; eauto. 
        
   eapply sig_function_translated; eauto.  

   assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. destruct ros. right; right; trivial.  right; trivial.    
     assert (rs ## args = rs' ## args) by (eapply sub_respect; eauto). 
  rewrite H4.      eapply Mcall; eauto.   
  eapply list_forall2_cons; eauto.
  eapply Mstackframe; eauto. 
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)) . 
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.
 
   analyze CRAWL for ( map (fun x : node => x) (n :: nil)). (* count_nodes incorrect dans CRAWLm mauvais graphe *)
     simpl in EQ2. inversion EQ2; subst.  
   assert (pc' = n1). unfold successors in EQ0. rewrite H in EQ0. congruence.  
   assert (x = n0). unfold successors in EQ1. rewrite EQ in EQ1. congruence.  
   subst. trivial. 

  unfold successors in EQ0. rewrite H in EQ0. inversion EQ0. 

  (* tailcall *)
 
  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst. generalize H10; intro BACKUP.  
  unfold V.validate in H10. unfold V.validate_graphs in H10.
  destruct (and_and _ _ H8) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H1); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H2 INIT); intro HOLDS. 
  clear H1 H2.  

   (* unification *)
    destruct HOLDS as [STH STKH].
    unfold state_holds in STH. 

  (* l unification va se faire sur place *)

   assert (i = Itailcall (funsig fc) ros args).
          unfold V.unification in UNI. unfold V.M.unification in UNI. 
          unfold unification in UNI. simpl in UNI. 
          case_eq  (inst_ms_eq (MItailcall (funsig fc) ros args) (mask_succ i)); intros. 
          clear H1.  
          unfold mask_succ in e. analyze e for i. 
          rewrite H1 in UNI. inversion UNI.
     
     assert (exists tf, find_function tge ros rs' = Some tf /\ V.transf_fundef fc = OK tf).
              unfold find_function. unfold find_function in H0. 
              destruct ros. eapply functions_translated; eauto. 

              assert (rs # r = rs' # r). 
                  eapply sub_respect_simple; eauto.
                  eapply regs_prop; eauto. simpl.  left. trivial.
                  rewrite <- H2. trivial.                     

       rewrite <- (symbols_preserved prog tprog ge tge) in H0.          
      destruct (Genv.find_symbol tge i0). eapply function_ptr_translated; eauto. 
                  inversion H0.
                  trivial. unfold ge; trivial. unfold tge; trivial.  

     destruct H2 as [tfx [H6 TF]].  
     exists (Callstate stack' tfx (rs' ## args) (free m stk)).
        
     assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. destruct ros. right; trivial. trivial.   
     assert (rs ## args = rs' ## args) by (eapply sub_respect; eauto). 
   split; trivial.           
   eapply Smallstep.plus_one; eauto. subst.  eapply exec_Itailcall; eauto. 
        
   eapply sig_function_translated; eauto.  

   assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto.  simpl. destruct ros. right; trivial. trivial.   
     assert (rs ## args = rs' ## args) by (eapply sub_respect; eauto). 
  rewrite H5.      eapply Mcall; eauto.   
 
  (* Ialloc *)
  
  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H9. unfold V.validate_graphs in H9.
  destruct (and_and _ _ H9) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H2); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H3 INIT); intro HOLDS. 
  clear H2 H3. 

  inversion WAS; subst.  
  generalize (init_correct ge _ _ H2); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H3 INIT2); intro HOLDS2. 
  clear H2 H3. 
  unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22]. 

   (* unification *)
    destruct HOLDS as [STH STKH].
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  MATCH HO12 STH H EQ UNI STEP); intro WEAK.
   
  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.       
   analyze CRAWL for ( map (fun x : node => x) (n :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp pc' (rs # res <- (Vptr b Int.zero)) m') beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 
   rewrite H in EQ0. inversion EQ0; subst. 
   simpl in EQ2. inversion EQ2; subst.   
  assert (EQO : n0 = pc2'). 
      eapply succ_step; eauto. unfold successors; trivial. eauto.  
  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT CRAWL); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto.
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.   

  (* Icond *)
 
  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H8. unfold V.validate_graphs in H8.
  destruct (and_and _ _ H8) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H1); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H2 INIT); intro HOLDS.
  clear H1 H2. 

  inversion WAS; subst.  
  generalize (init_correct ge _ _ H1); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H2 INIT2); intro HOLDS2. 
  clear H1 H2. 
  unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22].  

   (* unification *)
    destruct HOLDS as [STH STKH].
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  MATCH HO12 STH H EQ UNI STEP); intro WEAK.
   
  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.     
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0; subst.
  
   analyze CRAWL for (map (fun x : node => x) (n :: n0 :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp ifso rs m) beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 



   generalize (and_and _ _ CRAWL); intro. destruct H2.  
   simpl in EQ2. inversion EQ2; subst.    
  subst. rewrite H in EQ0. inversion EQ; subst.
  inversion EQ0; subst.  

  (* horrible :) *)
  assert (n1 = pc2'). rewrite H6 in EQ1. analyze EQ1 for i.
  inversion EQ1; subst. 
  inversion STEP'; try congruence; subst; trivial.    
  unfold V.unification in UNI. unfold V.M.unification in UNI.  killif UNI. 
  unfold mask_succ in e. inversion e; subst. 
  rewrite EQ in H11. inversion H11; subst. 
  (*clear CRAWL H4 H5 H3 EQ3 H8 FOLD. *)
     assert (forall r, In r args0 -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto.  
     assert (rs ## args0 = rs2' ## args0) by (eapply sub_respect; eauto).
     rewrite <- H7 in H20. congruence. 
  simpl in UNI. inversion UNI. 

  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT H2); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto.

  (* Icond *)

  (* 1ere etape : recuperer les calculs *)
  inversion MATCH; subst.
  unfold V.validate in H8. unfold V.validate_graphs in H8.
  destruct (and_and _ _ H8) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H1); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H2 INIT); intro HOLDS.
  clear H1 H2. 

    inversion WAS; subst.  
  generalize (init_correct ge _ _ H1); intro INIT2.
  generalize (analysis_correctness_generalized ge _ _ _ H2 INIT2); intro HOLDS2. 
  unfold holds in HOLDS2. destruct HOLDS2 as [HO12 HO22]. 
 

   (* unification *)
    destruct HOLDS as [STH STKH].
    generalize (unification_correct' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  MATCH HO12 STH H EQ UNI STEP); intro WEAK.
   
  (* crawling *)
  
   unfold V.crawl in CRAWL. 
   analyze CRAWL for (successors f pc) (successors tf pc) (map (fun x : node => x) (successors f pc)).
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0.     
   unfold successors in EQ0. rewrite H in EQ0. inversion EQ0; subst.
  
   analyze CRAWL for (map (fun x : node => x) (n :: n0 :: nil)).
   generalize (crawl_aux_correct'); intro. 
   destruct WEAK as [pc2' [ rs2'[STEP' WEAK]]]. 
   inversion WEAK; subst.  
   assert (CONT : program_continues ge
         (State s f sp ifnot rs m) beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  
   unfold successors in *|-. 



   generalize (and_and _ _ CRAWL); intro. destruct H4.  
   simpl in EQ2. inversion EQ2; subst.    
  subst. rewrite H in EQ0. inversion EQ; subst.
  inversion EQ0; subst.
  
  assert (n2 = pc2'). rewrite H11 in EQ1. analyze EQ1 for i.
  inversion EQ1; subst. 
  inversion STEP'; try congruence; subst; trivial.
  unfold V.unification in UNI. unfold V.M.unification in UNI.     
 killif UNI. 
  unfold mask_succ in e. inversion e; subst. 
  rewrite EQ in H13. inversion H13; subst. 
  clear CRAWL H4 H5 H3 EQ3 H8 FOLD. 
     assert (forall r, In r args0 -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto.  
     assert (rs ## args0 = rs2' ## args0) by (eapply sub_respect; eauto).
     rewrite <- H4 in H22. congruence. 
  simpl in UNI. inversion UNI. 

 
  subst. 

   generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  WEAK CONT H5); intro GO.

   (* reconstruction *)
  
    destruct GO as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto.

  (* state -> return *) 

  inversion MATCH; subst.
  unfold V.validate in H7. unfold V.validate_graphs in H7.
  destruct (and_and _ _ H7) as [FOLD ENTRY]. 
  assert (CP: V.check_point f tf pc (analyze f) (analyze tf) (fun x  => x) (compute_standard_regs (fn_code f)) = true).
    eapply full_verif; eauto.
  unfold V.check_point in CP. 
  rewrite H in CP. 
  analyze CP for (fn_code tf) ! pc.
  destruct (and_and _ _ CP) as [UNI CRAWL]. 

  (* 2eme etape : recuperer l'information de l'analyse d'egalites *)
  inversion WAS'; subst. 
  generalize (init_correct tge _ _ H0); intro INIT.
  generalize (analysis_correctness_generalized tge _ _ _ H1 INIT); intro HOLDS. 

   (* unification *)
    destruct HOLDS as [STH STKH].
    
   
  exists (Returnstate stack' (regmap_optget or Vundef rs') (free m stk)). 
  split. 

  eapply Smallstep.plus_one; eauto.
  eapply exec_Ireturn; eauto.
  unfold V.unification in UNI. unfold V.M.unification in UNI.   
  analyze UNI for (inst_ms_eq (mask_succ (Ireturn or)) (mask_succ i)).
  simpl in e. unfold mask_succ in e. 
  destruct i; try congruence. 
  simpl in UNI. inversion UNI.  

  assert (regmap_optget or Vundef rs = regmap_optget or Vundef rs'). 
    unfold regmap_optget. 
    case_eq or; intros; trivial.  
    rewrite H2 in H. 
    eapply sub_respect_simple; eauto. 
    eapply regs_prop; eauto. simpl.
    left; trivial.      

  rewrite H2. 
  eapply Mreturn; eauto. 

  (* call -> state *)

  inversion MATCH; subst.
  simpl in H6.
  generalize (bind_inversion _ _ H6); intro.
  destruct H0 as [f' [TR EQ]]. 
  exists (State stack' f' (Vptr stk Int.zero) (fn_entrypoint f') (init_regs args (fn_params f')) m').  
  split. 
 
  (* reduction *)
  inversion EQ; subst. 
  eapply Smallstep.plus_one; eauto. 
  eapply exec_function_internal; eauto.
  unfold V.transf_function in TR. 
  analyze TR for ( V.validate f
           (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
              (E.transformation f) (fn_entrypoint f)  (V.compute_nextpc (E.transformation f))
              (V.compute_nextpc_correct (E.transformation f)))).
  inversion TR; subst. simpl. trivial.   

  (* matching *)
  unfold V.transf_function in TR.
  analyze TR for ( V.validate f
           (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
              (E.transformation f) (fn_entrypoint f)  (V.compute_nextpc (E.transformation f))
              (V.compute_nextpc_correct (E.transformation f)))).
  inversion TR; subst. 
  simpl. trivial.  
  simpl. eapply Mstate; eauto. 
  unfold respectful. intros. 
  trivial.  

  (* call -> return *)

  inversion MATCH; subst. 
  simpl in H6. inversion H6; subst. 
  exists (Returnstate stack' res m).   
  split. 
 
  (* reduction *)
  eapply Smallstep.plus_one; eauto.
  eapply exec_function_external; eauto.  

  (* matching *)
  eapply Mreturn; eauto. 

  (* return -> state *) 

  inversion MATCH; subst. 
  inversion H3; subst. 
  inversion H1; subst. 
  assert (step tge (Returnstate (Stackframe res tf sp pc' rs' :: bl) vres m) E0
           (State bl tf sp pc' rs' # res <- vres m)). 
    eapply exec_return; eauto. 
  assert (weak_match (State s c sp pc rs # res <- vres m) (State bl tf sp pc' rs' # res <- vres m)).
    eapply Wstate; eauto.  
    eapply respectful_update; eauto. 

   generalize (crawl_aux_correct'); intro.
   assert (CONT : program_continues ge
        (State s c sp pc rs # res <- vres m)  beh). (* disparaitra quand nettoyage *)
      inversion WILL; subst. 
      eapply program_terminates; eauto.
      eapply program_diverges; eauto.  

  generalize (crawl_aux_correct' _ _ _ _ _ _ _ _ _ _ _ _  H0 CONT H10); intro.
  
   (* reconstruction *)
  
    destruct H5 as [s1'' [RED MATCHGOAL]].
    exists s1''. 
    split ; trivial. 
    eapply Smallstep.plus_left; eauto. 
Qed. 
 
(** *End of the proof *)

Lemma initial_match:
  forall s,
  initial_state prog s -> exists s',
  initial_state tprog s' /\ match_states s s'. 
Proof. 
  intros. 
  inversion H; subst.
  assert (ge = Genv.globalenv prog) by trivial. 
  assert (tge = Genv.globalenv tprog) by trivial. 
  generalize (function_ptr_translated prog tprog ge tge TRANSF H3 H4 _ _ H1); intro.
  destruct H5 as [tf [FFPTR TF]].
  rewrite <- (symbols_preserved prog tprog ge tge) in H0; try congruence. 
  generalize sig_function_translated ; intro. 
  rewrite <- (sig_function_translated prog tprog ge tge TRANSF H3 H4 _ _ TF) in H2. 
  assert (m0 = Genv.init_mem prog) by trivial.
  assert (prog_main tprog = prog_main prog).
     unfold V.transf_program in TRANSF.  
     eapply transform_partial_program_main; eauto.
  rewrite <- H7 in H0. 
  assert (Genv.init_mem tprog = m0).
    rewrite H6.
    unfold V.transf_program in TRANSF.  
    eapply Genv.init_mem_transf_partial; eauto.  
   
  exists (Callstate nil tf nil m0).
  split. 
  rewrite <- H8. eapply initial_state_intro; eauto.
  eapply Mcall; eauto.
  econstructor.
Qed.   
    
Lemma final_match:
  forall s s' r,
  match_states s s' ->
  final_state s r ->
  final_state s' r. 
Proof. 
  intros. 
  inversion H0; subst.
  inversion H; subst. 
  inversion H5; subst. 
  auto.  
Qed. 

End M. 

Theorem transf_program_correct:
  forall prog tprog (beh: Smallstep.program_behavior),
  V.transf_program prog = OK tprog ->
  exec_program prog beh -> exec_program tprog beh.
Proof. 
  intros.
  unfold exec_program.
  unfold exec_program in H0.
  generalize (test prog tprog H); intro SIM.
  generalize (initial_match prog tprog H); intro INIT.
  generalize (final_match); intro FINAL.  

  eapply Smallstep.simulation_plus_preservation_gen; eauto.
Qed.
End M.  
End Valigatorproof.

 

