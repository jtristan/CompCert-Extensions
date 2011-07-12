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
Require Import Mem. 
Require Import Events.    
Require Import EqualityAnalysis. 


Section AN. 

Variable ge : genv. 


(** *Correcteness proof for analysis of equalities *)
 

 
Definition eq_holds (r : reg) (a : approx) (st : std_state) : Prop := 
     match a with
     | Op op lr => eval_operation ge st.(sp) op st.(rs)##lr st.(m) = Some st.(rs)#r
     | Load mc addr lr => exists a, eval_addressing ge st.(sp) addr st.(rs)##lr = Some a /\ Mem.loadv mc st.(m) a = Some st.(rs)#r
     | Novalue => False
     | Unknown => True
     end.

Definition state_holds (eq : D.t) (st : state) : Prop :=
  match st with 
  | State stack f sp pc rs m => forall (r : reg) (a : approx), D.get r eq = a -> eq_holds r a (mk_std_state f sp rs m)
  | _ => True
  end. 

Definition stackframe_holds (st : stackframe) :=
  forall m, 
  match st with
  | Stackframe res f sp pc rs =>  forall (r : reg) (a : approx), D.get r ((analyze f)!!pc) = a -> forall v, eq_holds r a (mk_std_state f sp rs#res <- v m)
  end.   

Definition stack_holds (st : state) : Prop :=
  match st with 
  | State stack c sp pc rs m => forall i, In i stack -> stackframe_holds i
  | Callstate stack f args m => forall i, In i stack -> stackframe_holds i
  | Returnstate stack v m => forall i, In i stack -> stackframe_holds i
  end. 

Definition holds (st : state) : Prop := 
  match st with
  | State stack f sp pc rs m => state_holds (analyze f)!!pc st /\ stack_holds st
  | Callstate stack f args m => stack_holds st
  | Returnstate stack v m => stack_holds st
  end. 

Lemma top_unknown : forall r, D.get r D.top = Unknown.
Proof. 
  intros. 
  unfold D.top. simpl. rewrite PTree.gempty. unfold Approx.top. trivial.  
Qed. 

Lemma top_always_holds : forall (st : state), state_holds D.top st.
Proof. 
  unfold state_holds; intros.
  destruct st; trivial. 
  intros. rewrite top_unknown in H. subst.  
  unfold eq_holds. trivial. 
Qed. 

Lemma get_greater : forall m1 m2 r,
  D.ge m2 m1 -> Approx.ge (D.get r m2) (D.get r m1). 
Proof. 
  intros. 
  unfold D.ge in H. generalize (H r); clear H; intro H. 
  trivial. 
Qed.   

Lemma holds_decreasing : forall (m1 m2 : D.t), D.ge m2 m1 -> forall st, state_holds m1 st -> state_holds m2 st.
Proof.
  unfold state_holds. intros. 
  destruct st; trivial. intros. 
  generalize (get_greater _ _ r H); clear H; intro H. unfold Approx.ge in H. 

  destruct H. rewrite H1 in H. rewrite H. unfold eq_holds; trivial. 
  destruct H. generalize (H0 r Novalue H); intro. unfold eq_holds; contradiction. 
  rewrite H1 in H. assert (D.get r m1 = a). symmetry. trivial. 
  generalize (H0 _ _ H2); intro; trivial. 
Qed. 

Lemma greater_than_top : forall m, D.ge m D.top -> forall r, D.get r m = Unknown. 
Proof. 
  intros. unfold D.ge in H. 
  generalize (H r); intro. rewrite top_unknown in H0. 
  unfold Approx.ge in H0. 
  destruct H0. trivial. 
  destruct H0. congruence. trivial. 
Qed. 

Lemma analyze_correct_start : forall f st, state_holds (analyze f)!!(f.(fn_entrypoint)) st. 
Proof. 
  intros. 
  unfold analyze. 
  generalize (DS.fixpoint_entry (successors f) (fn_nextpc f) (transfer f)
      ((fn_entrypoint f, D.top) :: nil)); intros; subst.
  case_eq (DS.fixpoint (successors f) (fn_nextpc f) (transfer f)
         ((fn_entrypoint f, D.top) :: nil)); intros. 
  assert (In (fn_entrypoint f, D.top) ((fn_entrypoint f, D.top) :: nil)).  
    unfold In. left; trivial. 
  generalize (H t (fn_entrypoint f) D.top H0 H1); intro. 
  unfold DS.L.ge in H2. 
  generalize (greater_than_top _ H2); clear H2; intro H2. 
  unfold state_holds. 
  destruct st; trivial. 
  intros. generalize (H2 r); intro. 
  assert (D.get r (@PMap.get D.t (fn_entrypoint f) t) = D.get r (@PMap.get DS.L.t (fn_entrypoint f) t)).  trivial. 
  rewrite H5 in H3. rewrite H4 in H3.
  rewrite <- H3. unfold eq_holds; trivial.  

  rewrite PMap.gi. unfold state_holds. 
  destruct st; trivial. 
  intros. rewrite top_unknown in H1. rewrite <- H1.    
  unfold eq_holds; trivial. 
Qed. 

Lemma analyze_correct_transf:
  forall f pc st pc' ast,
  In pc' (successors f pc) ->
  transfer f pc (analyze f)!!pc  = ast ->
  state_holds ast st /\ stack_holds st->
  state_holds (analyze f)!!pc' st /\ stack_holds st.
Proof. 
  intros. 
  unfold analyze. 
  generalize (DS.fixpoint_solution (successors f) (fn_nextpc f) (transfer f)
      ((fn_entrypoint f, D.top) :: nil)); intros; subst.
  case_eq ( DS.fixpoint (successors f) (fn_nextpc f) (transfer f)
         ((fn_entrypoint f, D.top) :: nil)); intros. 
  assert (Plt pc (fn_nextpc f)). generalize f.(fn_code_wf); intro. generalize (H3 pc); intro. destruct H4.  trivial.
      unfold successors in H. rewrite H4 in H. inversion H. 
 
  generalize (H2 t pc pc' H0 H3 H); intro. 
  destruct H1. split; trivial. 
  eapply holds_decreasing; eauto. 
  unfold analyze in H1. rewrite H0 in H1. trivial. 

  destruct H1. split; trivial. 
  rewrite PMap.gi. unfold state_holds. 
  destruct st; trivial. 
  intros. rewrite top_unknown in H4. rewrite <- H4.    
  unfold eq_holds; trivial. 
Qed. 

Lemma analyze_correct_transf_bis:
  forall f pc pc' es,
  In pc' (successors f pc) ->
  transfer f pc (analyze f)!!pc = es ->
  D.ge (analyze f)!!pc' es.
Proof. 
    intros. unfold analyze. 
  generalize (DS.fixpoint_solution (successors f) (fn_nextpc f) (transfer f)
      ((fn_entrypoint f, D.top) :: nil)); intros; subst.
  case_eq ( DS.fixpoint (successors f) (fn_nextpc f) (transfer f)
         ((fn_entrypoint f, D.top) :: nil)); intros. 
  rewrite H0 in *|-. 
  assert (Plt pc (fn_nextpc f)). generalize f.(fn_code_wf); intro. generalize (H2 pc); intro. destruct H3.  trivial. 
        unfold successors in H. rewrite H3 in H. inversion H. 
  assert (Some t = Some t). trivial.  
  generalize (H1 t pc pc' H3 H2 H); intro. 

  unfold DS.L.ge in H4. unfold D.ge in H4.  
  assert (@PMap.get DS.L.t = @PMap.get D.t). trivial.   
  
  unfold analyze. rewrite H0. unfold D.ge. trivial. 

  rewrite PMap.gi. eapply D.ge_top; eauto. 
Qed. 

Lemma transp_incr : forall a res, transp a res = a \/ transp a res = Unknown. 
Proof. 
  intros. 
  destruct a; simpl. 
  left; trivial. 
  left; trivial. 
  case_eq (Utilities.mem res l); intros. 
    right; trivial. 
    left; trivial. 
  case_eq (Utilities.mem res l); intros. 
    right; trivial. 
    left; trivial. 
Qed. 
 
Lemma transp_incr_bis: forall a, transp_mem a = a \/ transp_mem a = Unknown.
Proof. 
  intros. 
  destruct a; simpl; intuition. 
  destruct o; intuition. 
Qed. 

Lemma transp_bot : forall r, transp Novalue r = Novalue. 
Proof. 
  simpl; trivial. 
Qed. 

Lemma transp_top : forall r, transp Unknown r = Unknown. 
Proof. 
  simpl; trivial. 
Qed. 
  
Lemma trans_prop_1 :
  forall res m, D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp a res) m) m. 
Proof. 
  intros. 
  unfold D.ge. intro. 
  rewrite D.gmap; auto. 
  generalize (transp_incr (D.get p m) res); intro. 
  destruct H. 
  rewrite H. unfold Approx.ge. right; right; trivial. 
  rewrite H. unfold Approx.ge. left; trivial. 
Qed. 
  
Lemma transp_prop_2 :
  forall r res l o m,   
 D.get r
         (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
            m) = Op o l ->
      ~ In res l.
Proof. 
  intros. 
  rewrite D.gmap in H. 
  unfold transp in H. 
  destruct (D.get r m); intros; try congruence. 
  case_eq (Utilities.mem res l0); intros. 
    rewrite H0 in H. congruence. 
    rewrite H0 in H. inversion H; subst.  eapply mem_false; eauto. 
  case_eq (Utilities.mem res l0); intros.  
    rewrite H0 in H. congruence. 
    rewrite H0 in H. congruence. 
  eapply transp_bot; eauto.  
  eapply transp_top; eauto. 
Qed. 
  
Lemma transp_prop_3 :
  forall r res m1 a l m,   
 D.get r
         (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
            m) = Load m1 a l ->
      ~ In res l.
Proof. 
  intros. 
  rewrite D.gmap in H. 
  unfold transp in H. 
  destruct (D.get r m); intros; try congruence. 
  case_eq (Utilities.mem res l0); intros. 
    rewrite H0 in H. congruence. 
    rewrite H0 in H. congruence.  
  case_eq (Utilities.mem res l0); intros.  
    rewrite H0 in H. congruence. 
    rewrite H0 in H. inversion H; subst.  eapply mem_false; eauto. 
  eapply transp_bot; eauto.  
  eapply transp_top; eauto. 
Qed. 

Lemma transp_prop_4 :
  forall f r pc o l sp rs m, 
 D.get r
         (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (analyze f) !! pc) = Op o l ->
   eval_operation ge sp o rs ## l m = Some rs # r -> 
   forall m', eval_operation ge sp o rs ## l m' = Some rs # r. 
Proof. 
  intros. 
  rewrite D.gmap in H. 
  unfold transp_mem in H. 
  case_eq (D.get r (analyze f) !! pc); intros. 
    rewrite H1 in H. inversion H.  
    rewrite H1 in H. inversion H. 
    rewrite H1 in H. 
    destruct o0; try (  
       inversion H; subst; 
       simpl; simpl in *|-; 
       trivial). 
    rewrite H1 in H. inversion H. 
  simpl. trivial. 
  simpl; trivial.
Qed.    

Lemma transp_prop_5 : 
  forall f r pc m a l,
D.get r
         (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (analyze f) !! pc) = Load m a l -> False.
Proof. 
  intros. 
  rewrite D.gmap in H; try (simpl; trivial). 
  destruct (D.get r (analyze f) !! pc); try (inversion H).   
  destruct o; congruence. 
Qed. 

Lemma transp_prop_6 :
  forall m,
  D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a) m) m. 
Proof. 
  intros. 
  unfold D.ge. intros. rewrite D.gmap; try (simpl; trivial).
  unfold Approx.ge.  
  destruct (D.get p m); simpl; intuition. 
  destruct o; intuition. 
Qed.   

Lemma transfer_op_correct : 
  forall f pc stack sp rs m op args res pc' v, 
  state_holds (analyze f) !! pc (State stack f sp pc rs m) ->
  (fn_code f) ! pc = Some (Iop op args res pc') ->
  eval_operation ge sp op rs ## args m = Some v ->
  state_holds (transfer f pc (analyze f) !! pc)
     (State stack f sp pc' rs # res <- v m). 
Proof. 
  intros.   
  assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
            (analyze f) !! pc) ((analyze f) !! pc)). 
  eapply trans_prop_1; eauto. 
  generalize (holds_decreasing _ _ H2); intro.    
  unfold transfer. rewrite H0. 
  unfold state_holds. intros. 
  unfold state_holds in H. 
  generalize (peq res r); intro. destruct H5. 

  rewrite e in H4. 
  rewrite D.gss in H4. 
  case_eq (Utilities.mem r args); intros. 
  rewrite H5 in H4. rewrite <- H4. unfold eq_holds; trivial. 
  rewrite H5 in H4.  rewrite <- H4. 
  unfold eq_holds. simpl. rewrite e. 
  rewrite PMap.gss.   
  rewrite extended_gso; auto.
  eapply mem_false; eauto. 
  
  rewrite D.gso in H4; auto. 
  unfold D.ge in H2. 
  generalize (H2 r); clear H2; intro H2. 
  unfold Approx.ge in H2. 
  destruct H2. rewrite H4 in H2. 
  rewrite H2. unfold eq_holds. trivial. 
  destruct H2. 
  generalize (H _ _ H2); intro.
  inversion H5.  
  rewrite H2 in H4. generalize (H _ _ H4); intro. 
  unfold eq_holds. 
  destruct a. 
  inversion H5. 
  trivial.
 
  simpl. rewrite PMap.gso; auto. inversion H5. 
  rewrite extended_gso; auto. 
  rewrite H4 in H2.
  eapply transp_prop_2; eauto.   
  
  simpl. inversion H5.  simpl in H6. 
  rewrite PMap.gso; auto. rewrite extended_gso; auto. 
  rewrite H4 in H2.     
  eapply transp_prop_3; eauto. 
Qed. 

Lemma transfer_load_correct :
  forall f pc stack sp rs m args pc' v dst addr chunk a,
  state_holds (analyze f) !! pc (State stack f sp pc rs m) ->
  loadv chunk m a = Some v ->
  eval_addressing ge sp addr rs ## args = Some a ->
  (fn_code f) ! pc = Some (Iload chunk addr args dst pc') ->
  state_holds (transfer f pc (analyze f) !! pc)
  (State stack f sp pc' rs # dst <- v m). 
Proof.

  intros. 
  assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp a dst)
            (analyze f) !! pc) ((analyze f) !! pc)). 
  eapply trans_prop_1; eauto. 
  generalize (holds_decreasing _ _ H3); intro.    
  unfold transfer. rewrite H2. 
  unfold state_holds. intros. 
  unfold state_holds in H. 
  generalize (peq dst r); intro. destruct H6. 

  rewrite e in H5. 
  rewrite D.gss in H5. 
  case_eq (Utilities.mem r args); intros. 
  rewrite H6 in H5. rewrite <- H5. unfold eq_holds; trivial. 
  rewrite H6 in H5.  rewrite <- H5. 
  unfold eq_holds. simpl. rewrite e. 
  rewrite PMap.gss.   
  rewrite extended_gso; auto.
  exists a. split;  trivial. 
  eapply mem_false; eauto. 
  
  rewrite D.gso in H5; auto. 
  unfold D.ge in H3. 
  generalize (H3 r); clear H3; intro H3. 
  unfold Approx.ge in H3. 
  destruct H3. rewrite H5 in H3. 
  rewrite H3. unfold eq_holds. trivial. 
  destruct H3. 
  generalize (H _ _ H3); intro.
  inversion H6.  
  rewrite H3 in H5. generalize (H _ _ H5); intro. 
  unfold eq_holds. 
  destruct a0. 
  inversion H6. 
  trivial.
 
  simpl. rewrite PMap.gso; auto. inversion H6. 
  rewrite extended_gso; auto. 
  rewrite H5 in H3.
  eapply transp_prop_2; eauto.   
  
  simpl. inversion H6.  simpl in H7. 
  rewrite PMap.gso; auto. rewrite extended_gso; auto. 
  rewrite H5 in H3.      
  eapply transp_prop_3; eauto. 
Qed. 

Lemma transfer_store_correct :
  forall f pc sp rs m  addr args a src m' chunk pc' stack,
  state_holds (analyze f) !! pc (State stack f sp pc rs m) ->
  storev chunk m a rs # src = Some m' ->
  eval_addressing ge sp addr rs ## args = Some a ->
  (fn_code f) ! pc = Some (Istore chunk addr args src pc') ->
  state_holds (transfer f pc (analyze f) !! pc) (State stack f sp pc' rs m'). 
Proof. 
  intros. 
  unfold state_holds. intros. 
  unfold transfer in H3.  rewrite H2 in H3. 
  unfold state_holds in H. 
  assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (analyze f) !! pc) ((analyze f) !! pc)). 
  eapply transp_prop_6; eauto.  
  unfold D.ge in H4. 
  generalize (H4 r); clear H4; intro H4. 
  unfold Approx.ge in H4. 
  destruct H4.  
  rewrite H4 in H3. rewrite <- H3. unfold eq_holds. trivial. 
  destruct H4. generalize (H r Novalue H4); intro. 
    unfold eq_holds in H5. inversion H5. 
    rewrite H4 in H3. 
    generalize (H _ _ H3); clear H; intro H.  
    destruct a0; trivial; try congruence. 
    simpl. simpl in H. rewrite H3 in H4. 
    eapply transp_prop_4; eauto. 
    rewrite H3 in H4. 
    elimtype False. eapply transp_prop_5; eauto. 
Qed. 



Lemma filter_1:
  forall f r res o l pc,
  D.get r
       (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
          (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
             (analyze f) !! pc)) = Op o l ->
   D.get r (analyze f) !! pc = Op o l.
Proof. 
  intros. 
  rewrite D.gmap in H; simpl; trivial. 
  rewrite D.gmap in H; simpl; trivial. 
  destruct (D.get r (analyze f) !! pc); simpl in H; try congruence.
  killif H.  simpl in H. inversion H. 
  simpl in H. analyze H for o0.
  killif H. simpl in H. inversion H. 
  simpl in H. inversion H.
Qed. 

Lemma filter_2:
  forall f r res o l pc,
  D.get r
       (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
          (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
             (analyze f) !! pc)) = Op o l ->
  D.get r
          (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
             (analyze f) !! pc) = Op o l.
Proof. 
  intros. 
  rewrite D.gmap in H; simpl; trivial. 
  rewrite D.gmap in H; simpl; trivial.
  rewrite D.gmap; simpl ; trivial.   
  destruct (D.get r (analyze f) !! pc); simpl in H; try congruence. 
  killif H.  simpl in H. inversion H. 
  simpl in H. 
  analyze H for o0; inversion H; simpl; subst; rewrite EQ; trivial.
  killif H. simpl in H. inversion H. 
  simpl in H. inversion H.
Qed.          
 
Lemma filter_3:
  forall f r res o l pc,
  D.get r
       (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
          (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
             (analyze f) !! pc)) = Op o l ->     
  D.get r
       (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
             (analyze f) !! pc) = Op o l. 
Proof. 
  intros. 
  rewrite D.gmap in H; simpl; trivial. 
  rewrite D.gmap in H; simpl; trivial.
  rewrite D.gmap; simpl ; trivial.   
  destruct (D.get r (analyze f) !! pc); simpl in H; try congruence. 
  killif H.  simpl in H. inversion H. 
  killif H. simpl in H. inversion H. 
Qed.          

Lemma transfer_call_correct : 
  forall f pc sp rs m ros args res pc' f0 stack,
  state_holds (analyze f) !! pc (State stack f sp pc rs m) ->
  (fn_code f) ! pc = Some (Icall (funsig f0) ros args res pc') ->
  forall r a m' v, 
  D.get r (transfer f pc (analyze f) !! pc) = a ->
 eq_holds r a (mk_std_state f sp rs # res <- v m'). 
Proof.
  intros. 
   
  unfold transfer in H1. 
  rewrite H0 in H1. 
  generalize (peq r res); intro. 
  destruct H2.   
    
    subst. rewrite D.gss; auto. 
    unfold eq_holds. trivial. 
 
    rewrite D.gso in H1; auto. 
    assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc) ((analyze f) !! pc)).  
    eapply trans_prop_1; eauto.  
    assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc)) (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc)). 
   eapply transp_prop_6; eauto. 
   assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc)) ((analyze f) !! pc)). 
   eapply D.ge_trans; eauto. 
   generalize (transp_prop_6 ((analyze f)!! pc)); intro. 
   
   generalize H1; intro TRI. 
   rewrite D.gmap in TRI; try (simpl; trivial). 
   rewrite D.gmap in TRI; try (simpl; trivial). 

   generalize (transp_incr a res); intro. 
   generalize (transp_incr_bis a); intro. 

   destruct a.  

   unfold transp_mem in TRI. 
   analyze TRI for (transp (D.get r (analyze f) !! pc) res).
   unfold transp in EQ. 
   analyze EQ for  (D.get r (analyze f) !! pc). 
   unfold state_holds in H. 
   generalize (H _ _ EQ0); intro. inversion H8. 
   analyze TRI for o. 

   unfold eq_holds. trivial.
 
   simpl .
    assert (D.get r (analyze f) !! pc = Op o l). eapply filter_1; eauto. 
    assert (D.get r
          (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
             (analyze f) !! pc) = Op o l). eapply filter_2; eauto. 
   assert ( D.get r
       (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
             (analyze f) !! pc) = Op o l). eapply filter_3; eauto. 
   rewrite PMap.gso; auto. rewrite extended_gso; auto.
  unfold state_holds in H. generalize (H _ _ H8); intro. 
  unfold eq_holds in H11. simpl in H11. 
   eapply transp_prop_4; eauto. 
   eapply transp_prop_2; eauto. 
  
   unfold transp_mem in TRI. 
   analyze TRI for (transp (D.get r (analyze f) !! pc) res).  
   analyze TRI for o. 
 Qed. 

Lemma transfer_alloc_correct : 
  forall f pc sp rs m arg res pc' stack,
  state_holds (analyze f) !! pc (State stack f sp pc rs m) ->
  (fn_code f) ! pc = Some (Ialloc  arg res pc') ->
  forall r a m' v, 
  D.get r (transfer f pc (analyze f) !! pc) = a ->
 eq_holds r a (mk_std_state f sp rs # res <- v m'). 
Proof.
  intros. 
   
  unfold transfer in H1. 
  rewrite H0 in H1. 
  generalize (peq r res); intro. 
  destruct H2.   
    
    subst. rewrite D.gss; auto. 
    unfold eq_holds. trivial. 
 
    rewrite D.gso in H1; auto. 
    assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc) ((analyze f) !! pc)).  
    eapply trans_prop_1; eauto.  
    assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc)) (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc)). 
   eapply transp_prop_6; eauto. 
   assert (D.ge (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
            (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
               (analyze f) !! pc)) ((analyze f) !! pc)). 
   eapply D.ge_trans; eauto. 
   generalize (transp_prop_6 ((analyze f)!! pc)); intro. 
   
   generalize H1; intro TRI. 
   rewrite D.gmap in TRI; try (simpl; trivial). 
   rewrite D.gmap in TRI; try (simpl; trivial). 

   generalize (transp_incr a res); intro. 
   generalize (transp_incr_bis a); intro. 

   destruct a.  

   unfold transp_mem in TRI. 
   analyze TRI for (transp (D.get r (analyze f) !! pc) res).
   unfold transp in EQ. 
   analyze EQ for  (D.get r (analyze f) !! pc). 
   unfold state_holds in H. 
   generalize (H _ _ EQ0); intro. inversion H8. 
   analyze TRI for o. 

   unfold eq_holds. trivial.
 
   simpl .
    assert (D.get r (analyze f) !! pc = Op o l). eapply filter_1; eauto. 
    assert (D.get r
          (D.map (fun (_ : positive) (a : Approx.t) => transp a res)
             (analyze f) !! pc) = Op o l). eapply filter_2; eauto. 
   assert ( D.get r
       (D.map (fun (_ : positive) (a : Approx.t) => transp_mem a)
             (analyze f) !! pc) = Op o l). eapply filter_3; eauto. 
   rewrite PMap.gso; auto. rewrite extended_gso; auto.
  unfold state_holds in H. generalize (H _ _ H8); intro. 
  unfold eq_holds in H11. simpl in H11. 
   eapply transp_prop_4; eauto. 
   eapply transp_prop_2; eauto. 
  
   unfold transp_mem in TRI. 
   analyze TRI for (transp (D.get r (analyze f) !! pc) res).  
   analyze TRI for o. 
 Qed. 

Lemma abstract_interpretation_correct : 
  forall f t stack c sp pc rs m es es' st st',
  c = f.(fn_code) ->
  st = State stack f sp pc rs m ->
  es = (analyze f)!!pc ->
  step ge st t st' ->
  state_holds es st  /\ stack_holds st ->
  transfer f pc es = es' ->
  state_holds es' st' /\ stack_holds st'. 
Proof. 
  intros.
  inversion H2; subst. 

  (* Inop *)
  inversion H6; subst. 
  destruct H3. split; trivial. 
  unfold transfer. rewrite H5. 
  unfold state_holds. intros. 
  unfold state_holds in H. 
  generalize (H _ _ H1); intro. trivial. 

  (* Iop *)
  inversion H7; subst.  
  destruct H3. split; trivial.
  eapply transfer_op_correct; eauto.  

  (* Load *)
  inversion H8; subst. 
  destruct H3. split; trivial. 
  eapply transfer_load_correct; eauto.

  (* store *)   
  inversion H8; subst. 
  destruct H3. split; trivial. 
  eapply transfer_store_correct; eauto. 

  (* call *)
  inversion H8; subst. 
  split. simpl. trivial. 
  simpl. destruct H3. simpl in H0. 
  intro. inversion H8; subst. clear H8.  
  generalize (H0 i); intro. intro. 
  destruct H3; eauto. 
  subst. unfold stackframe_holds.  intros. 

  assert (forall r a, D.get r (transfer f pc (analyze f) !! pc) = a ->  eq_holds r a (mk_std_state f sp rs # res <- v m0)).  
    intros. 
    eapply transfer_call_correct; eauto. 

  assert (In pc' (successors f pc)). 
    unfold successors. rewrite H5. 
    simpl; trivial. left; trivial.

  assert ( transfer f pc (analyze f) !! pc = transfer f pc (analyze f) !! pc) by  trivial.  

  generalize (analyze_correct_transf_bis f pc pc' (transfer f pc (analyze f) !! pc) H7 H8); intro. 
  unfold D.ge in H9. generalize (H9 r); intro. unfold Approx.ge in H10. 
  destruct H10. rewrite H10 in H3. rewrite <- H3. unfold eq_holds. trivial. 
  destruct H10. generalize (H4 _ _ H10); intro. unfold eq_holds in H11. inversion H11. 
   
  subst. eapply H4; eauto. 

  (* tailcall *)
  inversion H8; subst. 
  destruct H3; split; trivial. 
  simpl. trivial. 

  (* alloc *)
  inversion H8; subst. 
  destruct H3; split; trivial. 
  unfold state_holds. intros. 
  eapply transfer_alloc_correct; eauto. 

  (* cond *)
  inversion H7; subst. 
  destruct H3; split; trivial. 
  unfold transfer. rewrite H5. 
  simpl. intros. unfold state_holds in H. eapply H; eauto. 
 
  (* cond *)
  inversion H7; subst. 
  destruct H3; split; trivial. 
  unfold transfer. rewrite H5. 
  simpl. intros. unfold state_holds in H. eapply H; eauto. 

  (* return *)
 
  inversion H6; subst. 
  destruct H3; split; trivial. 
  simpl. trivial.

  (* fin *) 

  inversion H6. 
  inversion H6. 
  inversion H5. 
Qed. 
 
Lemma return_correct : 
  forall f t stack v m st st' s  sp pc rs m',
  st = Returnstate stack v m ->
  st' = State s f sp pc rs m' ->
  step ge st t st' ->
  stack_holds st ->
  state_holds (analyze f)!!pc st' /\ stack_holds st'.
Proof. 
  intros f t0 stack v m0 st st' s sp0 pc rs0 m' EQ1 EQ2 STEP HOLD.
  subst. simpl in HOLD. 
  inversion STEP; subst.  
  generalize (HOLD (Stackframe res f sp0 pc rs)); intro. 
  assert (In (Stackframe res f sp0 pc rs) (Stackframe res f sp0 pc rs :: s)). unfold In; left; trivial. 
  generalize (H H0); intro. 
  unfold stackframe_holds in H1.
  generalize (H1 m'); intro PROP.
  clear H1 H0 H STEP. 
  simpl.  split. intros.  eapply PROP; eauto.
  simpl. intros. 
  assert (In i s -> In i (Stackframe res f sp0 pc rs :: s)). intro. unfold In; right; trivial. 
  generalize (HOLD i (H0 H)); intro. trivial. 
Qed.  

Lemma call_correct : 
  forall f t stack args m st st' s c sp pc rs m',
  st = Callstate stack (Internal f) args m ->
  st' = State s c sp pc rs m' ->
  step ge st t st' ->
  stack_holds st ->
  state_holds (analyze f)!!pc st' /\ stack_holds st'.
Proof. 
  intros f t stack args m0 st st' s c0 sp0 pc rs0 m' EQ1 EQ2 STEP HOLD.
  subst. simpl in HOLD. 
  inversion STEP; subst.
  split; trivial.
  eapply analyze_correct_start; eauto. 
Qed.    
   
Lemma ext_call_correct :
  forall f t stack args m st st',
  st = Callstate stack (External f) args m ->
  step ge st t st' ->
  stack_holds st ->
  stack_holds st'.
Proof.
  intros f t0 stack args m0 st st' EQ STEP HOLD.
  subst. inversion STEP; subst.
  trivial. 
Qed.   

Lemma abstract_interpretation_correct_bis : 
  forall f t stack c sp pc rs m es es' st st',
  c = f.(fn_code) ->
  st = State stack f sp pc rs m ->
  es = (analyze f)!!pc ->
  step ge st t st' ->
  state_holds es st  /\ stack_holds st ->
  transfer f pc es = es' ->
  stack_holds st'.
Proof. 
  intros. 
  generalize (abstract_interpretation_correct f t stack c sp pc rs m es es' st st' H H0 H1 H2 H3 H4); intro.
  destruct H5; trivial. 
Qed. 

Lemma analysis_correctness_step:
  forall st t st',
  holds st ->
  step ge st t st' ->
  holds st'. 
Proof. 
  intros st t st' HOLD STEP.
  inversion STEP; subst; unfold holds in HOLD; unfold holds. 
    
   
  (* Inop *)

  destruct HOLD as[HO1 HO2].
  assert (In pc' ((successors f) pc)). 
      unfold successors. rewrite H. unfold In. left; trivial.  
  subst.   
  eapply analyze_correct_transf; eauto. 
  eapply abstract_interpretation_correct; eauto. 

  (* Iop *)

  destruct HOLD as [HO1 HO2].
  assert (In pc' ((successors f) pc)).       unfold successors. rewrite H. unfold In. left; trivial.  
  subst.   
  eapply analyze_correct_transf; eauto. 
  eapply abstract_interpretation_correct; eauto. 

  (* Iload *) 
  destruct HOLD as [HO1 HO2].
  assert (In pc' ((successors f) pc)).       unfold successors. rewrite H. unfold In. left; trivial.   
  subst.   
  eapply analyze_correct_transf; eauto. 
  eapply abstract_interpretation_correct; eauto. 

  (* Istore *)
  destruct HOLD as [HO1 HO2].
  assert (In pc' ((successors f) pc)).       unfold successors.  rewrite H. unfold In. left; trivial.   
  subst.   
  eapply analyze_correct_transf; eauto. 
  eapply abstract_interpretation_correct; eauto. 

  (* Icall *)

  destruct HOLD as [HO1 HO2]. 
  subst. 
  eapply abstract_interpretation_correct_bis; eauto.

  (* Itailcall *) 

  destruct HOLD as [HO1 HO2]. 
  subst. 
  eapply abstract_interpretation_correct_bis; eauto.

  (* Ialloc *)
  destruct HOLD as [HO1 HO2].
  assert (In pc' ((successors f) pc)).       unfold successors.  rewrite H. unfold In. left; trivial.   
  subst.   
  eapply analyze_correct_transf; eauto.
  eapply abstract_interpretation_correct; eauto. 

  (* Icond *)
  destruct HOLD as [HO1 HO2].
  assert (In ifso ((successors f) pc)).       unfold successors.  rewrite H. unfold In. left; trivial.   
  subst.   
  eapply analyze_correct_transf; eauto.
  eapply abstract_interpretation_correct; eauto. 

  (* Icond *)
  destruct HOLD as [HO1 HO2].
  assert (In ifnot ((successors f) pc)).       unfold successors.  rewrite H. unfold In. right. left. trivial.   
  subst.   
  eapply analyze_correct_transf; eauto.
  eapply abstract_interpretation_correct; eauto. 
  
  (* instruciton return, prouvee a la main sans appel au lemme *)
  destruct HOLD as [EQ HOLD].  
  simpl. simpl in HOLD. trivial.   

  (* callstate vers state *)
  eapply call_correct; eauto.

  (* callsate vers returnstate *)  
  eapply ext_call_correct; eauto.

  (* returnstate vers state *)
  simpl in HOLD.
  generalize (HOLD (Stackframe res c sp pc rs)); intro.
  assert (Stackframe res c sp pc rs = Stackframe res c sp pc rs \/ In (Stackframe res c sp pc rs) s). 
      left; trivial.
  generalize (H H0); intro. 
  unfold stackframe_holds in H1.
  generalize (H1 m); clear H1; intro. split; trivial. 
  unfold state_holds.  intros. eapply H1.  auto. simpl. 
  intros. 
  assert (Stackframe res c sp pc rs = i \/ In i s) by (right; trivial). 
  eapply HOLD; eauto. 
Qed. 
  
Theorem analysis_correctness_generalized:
  forall st t st', 
  Smallstep.star RTL2.step ge st t st' ->  
  holds st ->
  holds st'.
Proof. 
   intros st t st' STEPS. 
   induction STEPS ; intros. 
   trivial.
   eapply IHSTEPS; eauto.
   eapply analysis_correctness_step; eauto.
Qed. 

Lemma init_correct:
  forall p st, initial_state p st -> holds st.
Proof. 
  intros. 
  inversion H; subst. 
  unfold holds. unfold stack_holds. 
  intros. inversion H3.  
Qed. 

End AN. 

