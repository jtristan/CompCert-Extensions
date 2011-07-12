 
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

Definition respectful g (rs rs' : regset) : Prop :=
  let csr := compute_standard_regs g in
  forall x, In x csr -> rs # x = rs' # x.

Lemma respectful_update: forall g rs rs' r v, respectful g rs rs' -> respectful g (rs # r <- v) (rs' # r <- v).
Proof. 
  intros. 
  unfold respectful in H. unfold respectful. intros. 
  generalize (H x H0); intro. 
  generalize (peq x r); intros. destruct H2. 
  subst. rewrite Regmap.gss. rewrite Regmap.gss. trivial.   
  rewrite  Regmap.gso; auto. rewrite Regmap.gso; auto.
Qed.  

Lemma qui_peut_le_plus_peut_le_moins: 
  forall (l : list reg) (a : reg) (P : reg -> Prop), 
   (forall r, In r (a :: l) -> P r) -> forall r, In r l -> P r.
Proof. 
  intros. 
  generalize (peq r a); intros. destruct H1. 
  subst.  
  assert (In a (a :: l)). simpl; left; trivial. 
  generalize (H a H1); intro. trivial.  
  generalize (H r); intro. 
  assert (In r (a :: l)). simpl. right; trivial. 
  eauto. 
Qed.  
    
Lemma sub_respect:
  forall g rs rs' args,
  respectful g rs rs' ->
  (forall r : reg, In r args -> In r (compute_standard_regs g)) ->
  rs ## args = rs' ## args.
Proof. 
  induction args; intros.   
  simpl. trivial. 
  simpl. 
  assert (forall r : reg, In r args -> In r (compute_standard_regs g)). 
      generalize (qui_peut_le_plus_peut_le_moins args a (fun r => In r (compute_standard_regs g)) H0); intro. 
      trivial.  
  generalize (IHargs H H1); intro. rewrite H2.
  assert (In a (a :: args)) by (simpl; left; trivial). 
  generalize (H0 a H3); intro. 
  unfold respectful in H. 
  generalize (H a H4); intro. rewrite H5. 
  trivial. 
Qed.  

Lemma sub_respect_simple:
  forall g rs rs' r,
  respectful g rs rs' ->
  In r (compute_standard_regs g) ->
  rs # r = rs' # r.
Proof. 
  intros. 
  unfold respectful in H. eapply H; eauto. 
Qed. 

Module Type UnificationEngine. 
Variable em : errmsg.
Variable transformation : function -> code. 
Variable check_op : function -> function -> D.t -> D.t -> Approx.t -> Approx.t -> bool. 
Hypothesis check_op_correct:
  forall ge tge stack f sp pc1 rs m pc1' rs' m' rs2 tf pc2 stack' t o l o0 l0 r0 i j, 
    (forall op sp lv m, eval_operation ge sp op lv m = eval_operation tge sp op lv m) ->
  step ge (State stack f sp pc1 rs m) t (State stack f sp pc1' rs' m') ->
  (fn_code f) ! pc1 = Some i -> (fn_code tf) ! pc2 = Some j -> mask_succ i <> mask_succ j ->
  mask_succ j = MIop o0 l0 r0 -> mask_succ i = MIop o l r0 ->
  respectful (fn_code f) rs rs2 ->
  state_holds ge (analyze f) !! pc1 (State stack f sp pc1 rs m) ->
  state_holds tge (analyze tf) !! pc2 (State stack' tf sp pc2 rs2 m) ->
  check_op f tf (analyze f) !! pc1 (analyze tf) !! pc2 (Op o l) (Op o0 l0) = true ->
  exists pc2' : node,
    exists rs2' : regset,
      step tge (State stack' tf sp pc2 rs2 m) t
        (State stack' tf sp pc2' rs2' m') /\ respectful (fn_code f) rs' rs2'.

End UnificationEngine. 

Module UE (M : UnificationEngine).  

Definition check_op := M.check_op. 

Section UNIFICATION. 

Variable f tf : function. 
Variable inf inf' : D.t.

Definition unification (i j : instruction) : bool :=
  let i := mask_succ i in
  let j := mask_succ j in
  if inst_ms_eq i j then true 
  else 
    match i, j with
    | MIop op rl r, MIop op' rl' r' => peq r r' && check_op f tf inf inf' (Op op rl) (Op op' rl') (* changer l entier ! *)
    | MIload chunk addr args dst,  MIop Omove (cons rs nil) rd => peq rd dst && Approx.eq_dec (Load chunk addr args) (D.get rs inf') 
    | _, _ => false
    end.  

End UNIFICATION.

Theorem unification_correct : 
  forall ge tge f tf i j pc1 pc2 sp rs m st1 st2 stack stack' t rs2 pc1' rs' m', 
  (forall op sp lv m, eval_operation ge sp op lv m = eval_operation tge sp op lv m) ->
  (forall sp addr lv, eval_addressing ge sp addr lv = eval_addressing tge sp addr lv) ->
  st1 = State stack f sp pc1 rs m ->
  st2 = State stack' tf sp pc2 rs2 m ->
  respectful (fn_code f) rs rs2 ->
  state_holds ge (analyze f)!!pc1 st1 -> 
  state_holds tge (analyze tf)!!pc2 st2 -> 
  (fn_code f)!pc1 = Some i -> (fn_code tf)!pc2 = Some j ->  
  unification f tf (analyze f) !!pc1 (analyze tf)!!pc2 i j = true ->
  step ge st1 t (State stack f sp pc1' rs' m') ->  
  exists pc2', exists rs2',  step tge st2 t (State stack' tf sp pc2' rs2' m') /\ respectful (fn_code f) rs' rs2'. 
Proof. 
  intros until 1. revert H. intro eval_op_env. intro eval_addr_env.  intro. intro. intro EQST. intro NOUV. intros.   
  unfold unification in H4.

  killif H4. 

    rewrite H in H5. 
    inversion H5; subst. 

    (* Inop *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
  assert (exists pc2', j = Inop pc2'). unfold mask_succ in e. analyze e for j. exists n; trivial. 
  destruct H. exists x.  exists rs2.  
    rewrite H in H3. 
   split. 
        eapply exec_Inop; eauto.
        trivial. 

    (* Iop *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
    assert (exists pc2', j = Iop op args res pc2'). unfold mask_succ in e. analyze e for j. exists n. inversion e; subst. trivial. 
    destruct H. exists x. exists (rs2 # res <- v) .
        rewrite H in H3.
   subst.  split.  
        eapply exec_Iop; eauto. rewrite <- eval_op_env.  
        assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. right; trivial. 
        assert (rs ## args = rs2 ## args) by (eapply sub_respect; eauto).
        congruence.  
        eapply respectful_update; eauto. 

    (* Iload *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
    assert (exists pc2', j = Iload chunk addr args dst pc2'). 
          unfold mask_succ in e. analyze e for j. exists n; trivial. inversion e ;subst; trivial.    
    destruct H. exists x. exists  (rs2 # dst <- v).
        rewrite H in H3.
 split.  
        eapply exec_Iload; eauto.  rewrite <- eval_addr_env. 
        assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. right; trivial.   
        assert (rs ## args = rs2 ## args) by (eapply sub_respect; eauto). 
        congruence. 
        eapply respectful_update; eauto.   

    (* Istore *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
    assert (exists pc2', j = Istore chunk addr args src pc2'). 
          unfold mask_succ in e. analyze e for j. exists n; trivial. inversion e ;subst; trivial.    
    destruct H. exists x. exists rs2  .
        rewrite H in H3.
  split.  
        assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. right; trivial.   
        assert (rs' ## args = rs2 ## args) by (eapply sub_respect; eauto). 
           rewrite H7 in H17. 
   eapply exec_Istore; eauto.  rewrite <- eval_addr_env. eauto.  
        assert (rs' # src = rs2 # src). eapply sub_respect_simple; eauto. eapply regs_prop; eauto. simpl; trivial. left; trivial.   
        rewrite <- H8.  trivial.   
       trivial. 

    (* Ialloc *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
    assert (exists pc2', j = Ialloc arg res pc2'). 
          unfold mask_succ in e. analyze e for j. exists n; trivial. inversion e ;subst; trivial.    
    destruct H. exists x. exists  (rs2 # res <- (Vptr b Int.zero)) .
        rewrite H in H3.
    split.  
        assert (In arg (compute_standard_regs (fn_code f))). eapply regs_prop; eauto. simpl. right. left. trivial.  
   eapply exec_Ialloc; eauto. 
        assert (rs # arg = rs2 # arg). eapply sub_respect_simple; eauto.   
        rewrite <- H7. trivial.  
        eapply respectful_update; eauto. 

    (* Icond *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
    assert (exists pc2', exists pc2'', j = Icond cond args pc2'  pc2''). 
       unfold mask_succ in e. analyze e for j. exists n; exists n0.  inversion e; subst. trivial.     
    destruct H. destruct H. exists x. exists  rs2 . 
    rewrite H in H3.
   split. 
        eapply exec_Icond_true; eauto. 
        assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. 
        assert (rs' ## args = rs2 ## args) by (eapply sub_respect; eauto). 
        rewrite <- H7; trivial.  
        trivial. 

    (* Icond *)
    rewrite H13 in H2. 
    inversion H2. clear EQ. rewrite <- H0 in e. 
    simpl in e. 
    assert (exists pc2', exists pc2'', j = Icond cond args pc2'  pc2''). 
       unfold mask_succ in e. analyze e for j. exists n; exists n0.  inversion e; subst. trivial.     
    destruct H. destruct H. exists x0. exists  rs2. 
    rewrite H in H3.
   split. 
        eapply exec_Icond_false; eauto. 
        assert (forall r, In r args -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. 
        assert (rs' ## args = rs2 ## args) by (eapply sub_respect; eauto). 
        rewrite <- H7; trivial.  
        trivial.

  (* les instructions masquees n'etaient pas egales *)
  clear EQ. 
  analyze H4 for (mask_succ i) (mask_succ j).  
    assert (r = r0). destruct (peq r r0); trivial. simpl in H4.  congruence. 
    assert (check_op f tf (analyze f)!!pc1 (analyze tf)!!pc2 (Op o l) (Op o0 l0) = true). 
        destruct (check_op f tf (analyze f)!!pc1 (analyze tf)!!pc2 (Op o l) (Op o0 l0)); trivial; simpl in H4; try congruence.  
        destruct (peq r r0); trivial. 

  subst. 
  generalize M.check_op_correct; intro.
  generalize (M.check_op_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eval_op_env H5 H2 H3 n EQ0 EQ EQST NOUV H1 H7); intro.
  trivial. 
 
(*
  unfold check_op in H7.    
  analyze H7 for o0 l0. 

        
        (* ici c est e qui est interessant ! *)
        clear n1 n0 EQ2 EQ4 EQ5. subst. 
        unfold state_holds in H1.
        assert ( D.get r1 (analyze tf)!!pc2 = Op o l) by (symmetry; trivial). clear e.  
        generalize (H1 _ _ H); intro. clear H1. 
       assert (exists ppc, i = Iop o l r0 ppc). 
        unfold mask_succ in EQ. analyze EQ for i. exists n0. inversion EQ; subst. trivial.  
        destruct H1. inversion H5; subst; try congruence; trivial. 
        assert (exists pc2', j = Iop Omove (r1 :: nil) r0 pc2'). unfold mask_succ in EQ0. analyze EQ0 for j. inversion EQ0; subst; trivial. exists n0; trivial.  
        destruct H1 as [pc2' H1]. subst. 
        exists pc2'. exists (rs2 # r0 <- v). 
        split. 
        
        generalize (exec_Iop);intros. 
        generalize (exec_Iop tge stack' _ sp _ rs2 m' _ _ _ _ v H3); intro.
        apply H6. clear H1 H6.  
        simpl .
        unfold eq_holds in H0. simpl in H0.

      assert (forall r, In r l -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. right; trivial.
      assert (rs ## l = rs2 ## l) by (eapply sub_respect; eauto).
   
     rewrite <- H6 in H0. rewrite <- eval_op_env in H0.   

     congruence.          
      rewrite H2 in H14; inversion H14; subst. 
    eapply respectful_update; eauto. 

        analyze H7 for (D.get r1 (analyze tf)!!pc2).  
        analyze H7 for o0.  
        analyze H7 for o1. 
        analyze H7 for l1. 
*)
    
        analyze H4 for o l0. 
        assert (r0 = r). destruct (peq r0 r); trivial; simpl in H4; try congruence.  
        assert ((D.get r1 (analyze tf)!!pc2 ) = (Load m0 a l)). 
            case_eq (Approx.eq_dec (Load m0 a l) (D.get r1 (analyze tf)!!pc2)); intros. 
            symmetry; trivial. 
            rewrite H7 in H4. simpl in H4. destruct (peq r0 r); try congruence.
            simpl in H4.   congruence. 
        subst. 
        assert (exists pc1', i = Iload m0 a l r pc1'). 
            unfold mask_succ in EQ. 
            analyze EQ for i. inversion EQ; subst. 
            inversion H5; subst; try congruence. exists n0; trivial.  
        assert (exists pc2', j = Iop Omove (r1 :: nil) r pc2'). 
            unfold mask_succ in EQ0. 
            analyze EQ0 for j. 
            inversion EQ0; subst. exists n0. trivial. 
        destruct H0. 
        subst. destruct H. subst. 
        inversion H5; subst; try congruence.  
        exists x. exists (rs2 # dst <- v). 
        rewrite H12 in H2; inversion H2; subst.
       split. 
        generalize (exec_Iop tge stack' _ sp _ rs2 m' _ _ _ _ v H3); intro.          
        apply H.
      assert (forall r, In r l -> In r (compute_standard_regs (fn_code f))). intros. eapply regs_prop; eauto. simpl. right; trivial. 
       assert (rs ## l = rs2 ## l) by (eapply sub_respect; eauto).
        clear H H2 H12 H5 n EQ EQ0 H4.  
        unfold state_holds in H1.
        instantiate H1 with H7.  
        unfold eq_holds in H1. 
        destruct H1 as [aa [A B]]. 
        simpl in A; simpl in B. 
        simpl. rewrite <- B. 

      rewrite <- eval_addr_env in A. 
      congruence.

        eapply respectful_update; eauto.       
Qed.

Theorem unification_correct' : 
  forall ge tge f tf i j pc1 pc2 sp rs m stack stack' t rs2 pc1' rs' m', 
  (forall op sp lv m, eval_operation ge sp op lv m = eval_operation tge sp op lv m) ->
  (forall sp addr lv, eval_addressing ge sp addr lv = eval_addressing tge sp addr lv) ->
  respectful (fn_code f) rs rs2 ->
  state_holds ge (analyze f)!!pc1(State stack f sp pc1 rs m)  -> 
  state_holds tge (analyze tf)!!pc2 (State stack' tf sp pc2 rs2 m) -> 
  (fn_code f)!pc1 = Some i -> (fn_code tf)!pc2 = Some j ->  
  unification f tf (analyze f)!!pc1 (analyze tf)!!pc2 i j = true ->
  step ge (State stack f sp pc1 rs m) t (State stack f sp pc1' rs' m') ->  
  exists pc2', exists rs2',  step tge (State stack' tf sp pc2 rs2 m) t (State stack' tf sp pc2' rs2' m') /\ respectful (fn_code f) rs' rs2'.
Proof. 
  intros. eapply unification_correct; eauto. 
Qed.  

End UE.




