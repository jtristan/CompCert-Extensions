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
Require Import Arith. 
Require Import Max. 
Require Import Plus. 
Require Import Recdef. 
Require Import Valcommon. 
Require Import Two_level_repr. 
Require Import BasicLib.

Fixpoint heigth (t : instructions_tree) {struct t} : nat :=
  match t with 
  | Mgetstack i t m sub => plus 1 (heigth sub)
  | Msetstack m i t sub => plus 1 (heigth sub)
  | Mgetparam i t m sub => plus 1 (heigth sub)
  | Mop op rl m sub => plus 1 (heigth sub)
  | Mload chk addr rl m sub => plus 1 (heigth sub)
  | Mstore chk addr rl m sub => plus 1 (heigth sub)
  | Malloc sub => plus 1 (heigth sub)
  | Mcond c l sub1 sub2 => plus 1 (Max.max (heigth sub1) (heigth sub2))
  | Mout lbl	 => 1%nat
  end. 

Definition mes (d : instructions_tree * instructions_tree) := 
  let (t1,t2) := d in plus (heigth t1) (heigth t2). 
 
Lemma max_prop:
  forall a b, 
  (a < Datatypes.S  (Max.max b a))%nat. 
Proof. 
  intros. 
  generalize (le_max_l a b); intro. 
  eauto with arith. 
Qed. 
  
Lemma max_prop_inv:
  forall a b,
  (a < Datatypes.S  (Max.max a b))%nat. 
Proof. 
  intros. rewrite max_comm. eapply max_prop; eauto.   
Qed.  

Fixpoint listCheck (l1 l2 : expression_list) {struct l1} : bool :=
  match l1,l2 with 
  | Enil, Enil => true
  | Econs i1 l1, Econs i2 l2 => andb (beq_expression i1 i2) (listCheck l1 l2)
  | _,_ => false
  end. 

Fixpoint listGet (l : list mreg) (f : forest) {struct l} : expression_list :=
  match l with 
  | nil => Enil
  | i :: l => Econs (f # (Reg i))  (listGet l f)
  end. 

Function validate_trees (d : instructions_tree * instructions_tree) (f1 f2 : forest) (s1 s2 : constset.t) {measure mes d} : bool :=
  match d with
  | (Mout lbl, Mout lbl') => if peq lbl lbl' then andb (check f1 f2) (constset.subset s2 s1) else false
  | (Mcond c l sub1 sub2, Mcond c' l' sub1' sub2') =>
      if condition_eq c c' then 
      if listCheck (listGet l f1) (listGet l' f2) then
      andb (validate_trees (sub1, sub1') f1 f2 s1 s2) (validate_trees (sub2, sub2') f1 f2 s1 s2) 
      else false
      else false
  | (Mgetstack i t m sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Mgetstack i t m)) f2 (constset.add (Const (Egetstack i t f1 # Stack) (Reg m)) s1) s2
  | (Msetstack m i t sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Msetstack m i t)) f2 (constset.add (Const (Esetstack f1 # Stack f1 # (Reg m) i t) (Stack)) s1) s2
  | (Mgetparam i t m sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Mgetparam i t m)) f2 (constset.add (Const (Egetparam i t) (Reg m)) s1) s2
  | (Mop op rl m sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Mop op rl m)) f2 (constset.add (Const (Eop op (list_translation rl f1)) (Reg m)) s1) s2
  | (Mload chk addr rl m sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Mload chk addr rl m)) f2 (constset.add (Const (Eload chk addr (list_translation rl f1) f1 # (Mem)) (Reg m)) s1) s2
  | (Mstore chk addr rl m sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Mstore chk addr rl m)) f2 (constset.add (Const (Estore f1# Mem chk addr (list_translation rl f1) f1 # (Reg m)) (Mem)) s1) s2
  | (Malloc sub,t2) => validate_trees (sub, t2) (update f1 (Mach.Malloc)) f2 (constset.add (BiConst (Emalloc2 f1 # (Reg Conventions.loc_alloc_argument) f1 # Mem) (Mem) (Emalloc1 f1 # (Reg Conventions.loc_alloc_argument) f1 # Mem) (Reg Conventions.loc_alloc_result)) s1) s2
  | (t1,Mgetstack i t m sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Mgetstack i t m)) s1 (constset.add (Const (Egetstack i t f2 # Stack) (Reg m)) s2)
  | (t1,Msetstack m i t sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Msetstack m i t)) s1 (constset.add (Const (Esetstack f2 # Stack f2 # (Reg m) i t) (Stack)) s2)
  | (t1,Mgetparam i t m sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Mgetparam i t m)) s1 (constset.add (Const (Egetparam i t) (Reg m)) s2)
  | (t1,Mop op rl m sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Mop op rl m)) s1 (constset.add (Const (Eop op (list_translation rl f2)) (Reg m)) s2)
  | (t1,Mload chk addr rl m sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Mload chk addr rl m)) s1 (constset.add (Const (Eload chk addr (list_translation rl f2) f2 # (Mem)) (Reg m)) s2)
  | (t1,Mstore chk addr rl m sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Mstore chk addr rl m)) s1 (constset.add (Const (Estore f2 # Mem chk addr (list_translation rl f2) f2 # (Reg m)) (Mem)) s2)
  | (t1,Malloc sub) => validate_trees (t1, sub) f1 (update f2 (Mach.Malloc)) s1 (constset.add (BiConst (Emalloc2 f2 # (Reg Conventions.loc_alloc_argument) f2 # Mem) (Mem) (Emalloc1 f2 # (Reg Conventions.loc_alloc_argument) f2 # Mem) (Reg Conventions.loc_alloc_result)) s2)
  | (Mout l,Mcond c li sub1 sub2) => false
  | (Mcond c li sub1 sub2, Mout l) => false
end.  
  (* 1 *)
 intros; subst; simpl; omega. intros; subst; simpl; omega.  intros; subst; simpl; omega.  intros; subst; simpl; omega.
 intros; subst; simpl; omega. intros; subst; simpl; omega.  intros; subst; simpl; omega.  intros; subst; simpl; omega.
 intros; subst; simpl; omega. intros; subst; simpl; omega.  intros; subst; simpl; omega.  intros; subst; simpl; omega.
 intros; subst; simpl; omega. intros; subst; simpl; omega.  
 intros. simpl.     
  cut (heigth sub2 < Datatypes.S (Max.max (heigth sub1) (heigth sub2)))%nat. 
  cut (heigth sub2' < Datatypes.S (Max.max (heigth sub1') (heigth sub2')))%nat. 
  intros. omega. eapply max_prop. eapply max_prop. 
 intros. simpl.      
  cut (heigth sub1 < Datatypes.S (Max.max (heigth sub1) (heigth sub2)))%nat. 
  cut (heigth sub1' < Datatypes.S (Max.max (heigth sub1') (heigth sub2')))%nat. 
  omega.  eapply max_prop_inv. eapply max_prop_inv. 
 intros; subst; simpl; omega.  intros; subst; simpl; omega.
 intros; subst; simpl; omega. intros; subst; simpl; omega.  intros; subst; simpl; omega.  intros; subst; simpl; omega.
 intros; subst; simpl; omega. 
Qed.

Fixpoint plug (c : list Mach.instruction) (tr : instructions_tree) {struct c} : instructions_tree :=
  match c with
  | nil => tr
  | Mach.Mgetstack i0 t r :: c => Mgetstack i0 t r (plug c tr)
  | Mach.Msetstack r i0 t :: c => Msetstack r i0 t (plug c tr)
  | Mach.Mgetparam i0 t r :: c => Mgetparam i0 t r (plug c tr)
  | Mach.Mop op rl r :: c => Mop op rl r (plug c tr)
  | Mach.Mload chunk addr rl r :: c => Mload chunk addr rl r (plug c tr)
  | Mach.Mstore chunk addr rl r :: c => Mstore chunk addr rl r (plug c tr)
  | Mach.Malloc :: c => Malloc (plug c tr)
  | Mach.Mcall sign id :: c => Mout 1%positive
  | Mach.Mlabel lbl :: c => Mout 1%positive
  | Mach.Mgoto lbl  :: c => Mout 1%positive
  | Mach.Mcond cond rl lbl :: c => Mout 1%positive
  | Mach.Mreturn :: c => Mout 1%positive
  end. 
(*
Lemma exec_instr_length:
forall FF ge sp parent c rs fr m c' rs' fr' m' t,
exec_nb_instr FF ge sp parent c rs fr m t c' rs' fr' m' -> 
List.length c = (1 + List.length c')%nat.
Proof.
  intros. inversion H;simpl;trivial. 
Qed. 

Lemma exec_nb_instrs_length:
forall FF ge sp parent c rs fr m c' rs' fr' m' t,
exec_nb_instrs FF ge sp parent c rs fr m t c' rs' fr' m' -> 
(List.length c' <= List.length c)%nat.
Proof. 
  intros. induction H. 
  trivial. 
  generalize (exec_instr_length  _ _ _ _ _ _ _ _ _ _ _ _ H).
  intro. omega.  
Qed.

Lemma no_move_aux:
forall ge sp parent c rs fr m c' rs' fr' m' t,
exec_nb_instrs ge sp parent c rs fr m t c' rs' fr' m' -> 
List.length c = List.length c' -> rs = rs' /\ fr = fr' /\ m = m'.
Proof.
  induction 1. 
  auto.
  intro. generalize (exec_instr_length _ _ _ _ _ _ _ _ _ _ _ _ H); intro.
  generalize (exec_nb_instrs_length _ _ _ _ _ _ _ _ _ _ _ _  H0); intro.
  assert (length c2 = length c3). omega.
  generalize (IHexec_nb_instrs H4); intro.
  elimtype False. omega. 
Qed.  

Theorem no_move:
forall ge sp parent c rs fr m rs' fr' m' t,
exec_nb_instrs ge sp parent c rs fr m t c rs' fr' m' -> 
rs = rs' /\ fr = fr' /\ m = m'.
Proof.
  intros. eapply no_move_aux; eauto. 
Qed.

Lemma simple_move:
  forall ge sp parent i c k rs fr m t c' rs' fr' m', 
  exec_nb_instr ge sp parent (i :: c ++ k) rs fr m t c' rs' fr' m' ->
  c' = c ++ k.
Proof. 
  destruct i; intros; inversion H; trivial. 
Qed.  

Parameter coerce : (Genv.t fundef) -> (Genv.t Mach.fundef).
 coerce1: 
  forall ge,
  forall sp op vl, eval_operation ge sp op vl = eval_operation (coerce ge) sp op vl.
 coerce2:
  forall ge,
  forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing (coerce ge) sp addr vl. 
*)

Lemma plugit:
  forall ge sp parent c tree rs fr m w rs' fr' m' t rs'' fr'' m'' l,
  lnbranchset c = true ->
  exec_nb_instrs fundef ge sp parent (c ++ w) rs fr m E0 w rs' fr' m' ->
  exec_instructions_tree ge tree sp parent rs' fr' m' t l rs'' fr'' m'' ->
  exec_instructions_tree ge (plug c tree) sp parent rs fr m t l rs'' fr'' m''.
Proof. 
  induction c; intros. 
  simpl. simpl in H0. generalize (no_move fundef _ _ _ _  _  _ _ _ _  _ _ H0). intuition. subst.  trivial. 
  destruct a. 
    simpl. rewrite <- app_comm_cons in H0. inversion H0.
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Mgetstack; eauto.

    simpl. rewrite <- app_comm_cons in H0. inversion H0.
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Msetstack; eauto.

  simpl. rewrite <- app_comm_cons in H0. inversion H0.
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Mgetparam; eauto.

   simpl. rewrite <- app_comm_cons in H0. inversion H0. 
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Mop; eauto.     

   simpl. rewrite <- app_comm_cons in H0. inversion H0.
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Mload; eauto. 

   simpl. rewrite <- app_comm_cons in H0. inversion H0.
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Mstore; eauto.

  simpl in H. inversion H.
  simpl in H. inversion H.
  simpl in H. inversion H.

    simpl. rewrite <- app_comm_cons in H0. inversion H0.
      elimtype False. eapply list_diff; eauto.
      subst. simpl in H. generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2); intros; subst.
      inversion H2; subst. 
      eapply exec_Malloc; eauto. 

  simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
      simpl in H. inversion H.
Qed. 

Lemma no_trace:
  forall ge tree sp parent rs fr m t lbl rs' fr' m',
  exec_instructions_tree ge tree sp parent rs fr m t lbl rs' fr' m' -> t = E0.
Proof. 
  induction tree; intros.
  inversion H; subst. 
  eapply IHtree; eauto.
  inversion H; subst. 
  eapply IHtree; eauto.
  inversion H; subst. 
  eapply IHtree; eauto.  
  inversion H; subst. 
  eapply IHtree; eauto.
  inversion H; subst. 
  eapply IHtree; eauto.
  inversion H; subst. 
  eapply IHtree; eauto.
  inversion H; subst. 
  eapply IHtree; eauto.
  inversion H; subst.
  eapply IHtree1; eauto. 
  eapply IHtree2; eauto. 
  inversion H; subst.
  trivial. 
Qed.   

Lemma unplug:
  forall ge sp parent c2 sub1' rs0 fr0 m0 t lbl'' rs'' fr'' m'' w, 
  exec_instructions_tree ge (plug c2 sub1') sp parent rs0 fr0 m0 t lbl''
    rs'' fr'' m'' ->
      lnbranchset c2 = true ->
  exists rsi : regset, exists fri : frame, exists mi : mem,
  exec_nb_instrs fundef ge sp parent (c2 ++ w) rs0 fr0 m0 E0 w rsi fri mi /\
  exec_instructions_tree ge sub1' sp parent rsi fri mi E0 lbl'' rs'' fr'' m''.
Proof. 
  induction c2; intros. 
  simpl in H. simpl. exists rs0; exists fr0; exists m0.
  split. 
    eapply exec_refl_bl; eauto. 
    generalize (no_trace _ _ _ _ _ _ _ _ _ _ _ _ H); intro. subst. 
    trivial.
 
  rewrite <- app_comm_cons. 
  destruct a; try (inversion H0).  
    simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H18 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Mgetstack; eauto.
    trivial.

  simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H18 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Msetstack; eauto.
    trivial.

  simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H18 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Mgetparam; eauto.
    trivial.

simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H18 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Mop; eauto. 
    trivial.  

simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H20 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Mload; eauto.
    trivial.

simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H20 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Mstore; eauto.
    trivial. 

simpl in H. inversion H; subst. 
    generalize (IHc2 _ _ _ _ _ _ _ _ _ w H6 H2); intro.
    destruct H1 as [rsi [fri [mi [D E]]]]. 
    exists rsi; exists fri; exists mi. 
    split. 
    eapply exec_trans_bl; eauto. 
    eapply Valcommon.exec_Malloc; eauto.
    trivial.
Qed.   
  
Lemma rew1gen:
  forall c1 f1 i f,
  nbranchset i = true ->
  abstract_sequence f c1 = Some f1 ->
  abstract_sequence f (c1 ++ i :: nil) =
  Some f1;; i. 
Proof.
  induction c1; intros. 
  simpl. simpl in H0. injection H0 ; intros; subst.  destruct i; trivial; try inversion H. 
  destruct a; try (
  simpl in H0;
  generalize (IHc1 _ _ _ H H0); intro; rewrite <- H1; rewrite <- app_comm_cons;
  simpl;  trivial);try (simpl in H0; inversion H0).  
Qed. 

Definition get_constraint (i : Mach.instruction) (f : forest) :=
  match i with
  | (Mach.Mgetstack _ _ dst) as i => 
      Some ((Const (Rmap.get (Reg dst) (update f i))(Reg dst)) )
  | (Mach.Msetstack _ _ _ ) as i => 
      Some ((Const (Rmap.get Stack (update f i))(Stack))) 
  | (Mach.Mgetparam _ _ dst) as i => 
      Some ((Const (Rmap.get (Reg dst) (update f i))(Reg dst))) 
  | (Mach.Mop _ _ dst) as i => 
      Some ((Const (Rmap.get (Reg dst) (update f i))(Reg dst))) 
  | (Mach.Mload _ _ _ dst) as i => 
      Some ((Const (Rmap.get (Reg dst) (update f i))(Reg dst))) 
  | (Mach.Mstore _ _ _ _) as i => 
      Some ((Const (Rmap.get Mem (update f i))(Mem))) 
  | Mach.Malloc as i => 
      Some ((BiConst (Rmap.get Mem (update f i)) Mem (Rmap.get (Reg Conventions.loc_alloc_result) (update f i))(Reg Conventions.loc_alloc_result))) 
(*
(BiConst (Emalloc1 f # (Reg Conventions.loc_alloc_argument) f # Mem) Mem
     (Emalloc2 f # (Reg Conventions.loc_alloc_argument) f # Mem)
     (Reg Conventions.loc_alloc_result))
*)
(*
 ((BiConst (Rmap.get Mem (update f i)) Mem (Rmap.get (Reg Conventions.loc_alloc_result) (update f i))(Reg Conventions.loc_alloc_result))) 
*)
  | _ => None
 end. 

Lemma rew2_gen:
  forall c1 f1 i f s1 cons,
  nbranchset i = true ->
  abstract_sequence f c1 = Some f1 ->
  get_constraint i f1 = Some cons ->
  constset.equal (compute_constraints_me c1 f) s1 = true ->
  constset.equal (compute_constraints_me (c1 ++ i :: nil) f) 
     (constset.add cons s1) = true.
Proof. 
  induction c1; intros. 
  simpl in H0. injection H0; intros; subst.
  destruct i; try (
  simpl; 
  simpl in H1; inversion H1; subst; simpl in H2;
  rewrite Rmap.gss;
  rewrite constprop.add_union_singleton;
  rewrite constprop.add_union_singleton;
  eapply constset.equal_1;
  eapply constprop.union_equal_2; eauto;
  eapply constset.equal_2; eauto).

  destruct a. 

  (* getstack *)

  simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2.
  case_eq (constset.mem (Const (Egetstack i0 t f # Stack) (Reg m)) (compute_constraints_me c1
             f # (Reg m) <- (Egetstack i0 t f # Stack))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  remember (Const (Egetstack i0 t f # Stack) (Reg m)) as e1. 
  remember (f # (Reg m) <- (Egetstack i0 t f # Stack)) as f0.
  generalize (IHc1 f1 i f0 s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss. 
  rewrite <- Heqe1. rewrite <- Heqf0. 
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (Const (Egetstack i0 t f # Stack) (Reg m)) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  remember (Const (Egetstack i0 t f # Stack) (Reg m)) as e1. 
  remember (f # (Reg m) <- (Egetstack i0 t f # Stack)) as f0. 
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3.   

  (* setstack *) 

  simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2.
  case_eq (constset.mem (Const (Esetstack f # Stack f # (Reg m) i0 t) Stack) (compute_constraints_me c1
            f # Stack <- (Esetstack f # Stack f # (Reg m) i0 t))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  remember (Const (Esetstack f # Stack f # (Reg m) i0 t) Stack) as e1. 
  remember (f # Stack <- (Esetstack f # Stack f # (Reg m) i0 t)) as f0.
  generalize (IHc1 f1 i f0 s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss. 
  rewrite <- Heqe1. rewrite <- Heqf0. 
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (Const (Esetstack f # Stack f # (Reg m) i0 t) Stack) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  remember (Const (Esetstack f # Stack f # (Reg m) i0 t) Stack) as e1. 
  remember (f # Stack <- (Esetstack f # Stack f # (Reg m) i0 t)) as f0.
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3.   

  (* getparam *)

  simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2.
  case_eq (constset.mem (Const (Egetparam i0 t) (Reg m)) (compute_constraints_me c1
           f # (Reg m) <- (Egetparam i0 t))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  remember (Const (Egetparam i0 t) (Reg m)) as e1. 
  remember (f # (Reg m) <- (Egetparam i0 t)) as f0.
  generalize (IHc1 f1 i f0 s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss. 
  rewrite <- Heqe1. rewrite <- Heqf0. 
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (Const (Egetparam i0 t) (Reg m)) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  remember (Const (Egetparam i0 t) (Reg m)) as e1. 
  remember (f # (Reg m) <- (Egetparam i0 t)) as f0.
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3.     

  (* op *)

  simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2. 
  case_eq (constset.mem (Const (Eop o (list_translation l f)) (Reg m)) (compute_constraints_me c1
           f # (Reg m) <- (Eop o (list_translation l f)))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  remember (Const (Eop o (list_translation l f)) (Reg m)) as e1. 
  remember (f # (Reg m) <- (Eop o (list_translation l f))) as f0.
  generalize (IHc1 f1 i f0 s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss. 
  rewrite <- Heqe1. rewrite <- Heqf0. 
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (Const (Eop o (list_translation l f)) (Reg m)) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  remember (Const (Eop o (list_translation l f)) (Reg m)) as e1. 
  remember (f # (Reg m) <- (Eop o (list_translation l f))) as f0.
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3.     

  (* load *)

    simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2. 
  case_eq (constset.mem (Const (Eload m a (list_translation l f) f # Mem) (Reg m0)) (compute_constraints_me c1
           f # (Reg m0) <- (Eload m a (list_translation l f) f # Mem))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  remember (Const (Eload m a (list_translation l f) f # Mem)) as e1. 
  remember (f # (Reg m0) <- (Eload m a (list_translation l f) f # Mem)) as f0.
  generalize (IHc1 f1 i f0 s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss. 
  rewrite <- Heqe1. rewrite <- Heqf0. 
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (Const (Eload m a (list_translation l f) f # Mem) (Reg m0)) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  remember (Const (Eload m a (list_translation l f) f # Mem)) as e1. 
  remember (f # (Reg m0) <- (Eload m a (list_translation l f) f # Mem)) as f0.
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3.     

  (* store *)

    simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2. 
  case_eq (constset.mem (Const (Estore f # Mem m a (list_translation l f) f # (Reg m0)) Mem) (compute_constraints_me c1
           f # Mem <-
             (Estore f # Mem m a (list_translation l f) f # (Reg m0)))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  remember (Const (Estore f # Mem m a (list_translation l f) f # (Reg m0)) Mem) as e1. 
  remember (f # Mem <- (Estore f # Mem m a (list_translation l f) f # (Reg m0))) as f0.
  generalize (IHc1 f1 i f0 s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss. 
  rewrite <- Heqe1. rewrite <- Heqf0. 
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (Const (Estore f # Mem m a (list_translation l f) f # (Reg m0)) Mem) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  remember (Const (Estore f # Mem m a (list_translation l f) f # (Reg m0)) Mem) as e1. 
  remember (f # Mem <- (Estore f # Mem m a (list_translation l f) f # (Reg m0))) as f0.
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3.      

  simpl in H0; inversion H0. 

  (* alloc *)

  simpl in H0. simpl in H2.
  rewrite Rmap.gss in H2.
  case_eq (constset.mem (BiConst
             (Emalloc2 f # (Reg Conventions.loc_alloc_argument) f # Mem) Mem
             ((f # (Reg Conventions.loc_alloc_result) <-
               (Emalloc1 f # (Reg Conventions.loc_alloc_argument) f # Mem))
              # Mem <-
              (Emalloc2 f # (Reg Conventions.loc_alloc_argument) f # Mem))
             # (Reg Conventions.loc_alloc_result)
             (Reg Conventions.loc_alloc_result)) (compute_constraints_me c1
          f # (Reg Conventions.loc_alloc_result) <-
              (Emalloc1 f # (Reg Conventions.loc_alloc_argument) f # Mem)
             # Mem <-
             (Emalloc2 f # (Reg Conventions.loc_alloc_argument) f # Mem))).
  
  intro. 
  generalize (constset.mem_2 H3); intro.
  rewrite (constprop.add_equal H4) in H2.       
  generalize (IHc1 f1 i _ s1 cons H H0 H1 H2); intro.
  generalize (constset.equal_2 H5); intro. 
  rewrite  <- app_comm_cons. simpl . rewrite Rmap.gss.     
  rewrite constprop.add_equal. 
    eapply constset.mem_2.   
    eapply constset_prop; eauto. 
    eapply constset.equal_1. trivial.  
        
  intro. 
  generalize (constset.equal_2 H2). intro.
  generalize (constprop.Equal_remove (BiConst
             (Emalloc2 f # (Reg Conventions.loc_alloc_argument) f # Mem) Mem
             ((f # (Reg Conventions.loc_alloc_result) <-
               (Emalloc1 f # (Reg Conventions.loc_alloc_argument) f # Mem))
              # Mem <-
              (Emalloc2 f # (Reg Conventions.loc_alloc_argument) f # Mem))
             # (Reg Conventions.loc_alloc_result)
             (Reg Conventions.loc_alloc_result)) H4). intro.
  rewrite constprop.remove_add in H5. 
  generalize (constset.equal_1 H5); intro. 
  generalize (IHc1 _ _ _ _ _ H H0 H1 H6); intro.
  rewrite <- app_comm_cons.  simpl. trivial.  
  rewrite Rmap.gss.
  rewrite <- H4. rewrite <- H4 in H7. 
  rewrite constprop.add_add.
  generalize (constset.equal_2 H7); intro. rewrite H8. 
  rewrite constprop.remove_add. intro.
    generalize (constset.mem_1 H9); intro. 
    rewrite H10 in H3. inversion H3. 
  eapply constset.equal_1. unfold constset.Equal. 
  intro. split; trivial. 
  intro. 
   generalize (constset.mem_1 H6); intro. 
    rewrite  H7 in H3. inversion H3. 

  simpl in H0; inversion H0. 
  simpl in H0; inversion H0. 
  simpl in H0; inversion H0. 
  simpl in H0; inversion H0.     
Qed. 

Lemma gen_exec: 
  forall FF ge sp parent i rs fr m w rs' fr' m',
  exec_nb_instr FF ge sp parent (i :: w) rs fr m E0 w rs' fr' m' ->
  forall w, exec_nb_instr FF ge sp parent (i :: w) rs fr m E0 w rs' fr' m'.
Proof. 
  intros. 
  inversion H; subst. 
  eapply Valcommon.exec_Mgetstack; eauto.
  eapply Valcommon.exec_Msetstack; eauto.
  eapply Valcommon.exec_Mgetparam; eauto.
  eapply Valcommon.exec_Mop; eauto.
  eapply Valcommon.exec_Mload; eauto.
  eapply Valcommon.exec_Mstore; eauto.
  eapply Valcommon.exec_Malloc; eauto.
Qed.  

Lemma rew3_gen: 
  forall fundef ge sp parent c1 i w rs fr m rs' fr' m' w' rs'' fr'' m'',
  exec_nb_instrs fundef ge sp parent (c1 ++ w) rs fr m E0 w rs' fr' m' ->
  exec_nb_instr fundef ge sp parent (i :: w') rs' fr' m' E0 w' rs'' fr'' m'' ->
  exec_nb_instrs fundef ge sp parent (c1 ++ i :: w) rs fr m E0 w rs'' fr'' m''.
Proof. 
  induction c1; intros. 

  simpl. simpl in H. 
  generalize (no_move fundef _ _ _ _ _ _ _ _ _ _ _ H); intro.
  intuition. subst.  
  generalize (gen_exec fundef _ _ _ _ _ _ _ _ _ _ _ H0 w); intro.
  eapply Valcommon.exec_trans_bl; eauto.
  eapply Valcommon.exec_refl_bl; eauto.

  destruct a; try (  
  rewrite <- app_comm_cons in H;  inversion H; [
  elimtype False; eapply list_diff; eauto |
  subst;
  assert (c2 = c1 ++ w); [ eapply simple_move; eauto |
  subst;
  generalize (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ H2 H0); intro;
  rewrite <- app_comm_cons;
  eapply exec_trans_bl; eauto;
  eapply gen_exec; eauto]]).
Qed. 

Lemma test_aux2:
  forall FF ge sp parent c s1 s2 rs fr m k rs' fr' m',
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' ->
    c = s1 ++ s2 ->
  exists rs'', exists fr'', exists m'',
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 (s2 ++ k) rs'' fr'' m'' /\
  exec_nb_instrs FF ge sp parent (s2 ++ k) rs'' fr'' m'' E0 k rs' fr' m'.
Proof. 
    induction c; intros. 
  simpl in H. 
  generalize (no_move FF _ _ _ _ _ _ _ _ _ _ _ H); intro. intuition subst. 
  assert (s2 = nil). clear H. induction s1. simpl in H0. congruence. 
    rewrite <- app_comm_cons in H0. congruence. 
  subst. simpl. exists rs'; exists fr'; exists m'. split;  eapply exec_refl_bl; eauto. 
  
  rewrite <- app_comm_cons in *|-. 
  rewrite <- app_comm_cons. 
  inversion H. elimtype False. eapply list_diff; eauto. 
  subst. 
  generalize (simple_move FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1). intro. subst. 
  case_eq s1; intro. subst. simpl in H0. rewrite <- H0. 
  exists rs; exists fr; exists m. rewrite app_comm_cons. 
  split. eapply exec_refl_bl; eauto. rewrite <- app_comm_cons. trivial.  
  intros. subst. 
  assert ((i :: l) ++ s2 = i :: l ++ s2). rewrite app_comm_cons. trivial. 
  rewrite H3 in H0. 
  assert (c = l ++ s2). congruence. 
  generalize (IHc _ _ _ _ _ _ _ _ _ H2 H4). intro. 
  destruct H5 as [rs'' [fr'' [m'' A]]]. 
  exists rs''; exists fr''; exists m''.
  destruct A. 
  split. eapply exec_trans_bl; eauto.
  trivial. 
Qed. 
 
Lemma br_prop:
  forall c i,
  nbranchset i = true ->
  lnbranchset c = true ->
  lnbranchset (c ++ i :: nil) = true.
Proof. 
  induction c; intros. 
  simpl. destruct i; trivial. 
  rewrite <- app_comm_cons. 
  destruct a; simpl; simpl in H0; try (eapply IHc; eauto); try (inversion H0). 
Qed. 

Definition put (i : Mach.instruction) (sub : instructions_tree) : option instructions_tree :=
  match i with
  | Mach.Mgetstack i t m => Some (Mgetstack i t m sub)
  | Mach.Msetstack m i t => Some (Msetstack m i t sub)
  | Mach.Mgetparam i t m => Some (Mgetparam i t m sub)
  | Mach.Mop a b c => Some (Mop a b c sub)
  | Mach.Mload a b c d => Some (Mload a b c d sub)
  | Mach.Mstore a b c d => Some (Mstore a b c d sub)
  | Mach.Malloc => Some (Malloc sub)
  | _ => None
  end.

Lemma rew4_gen:
  forall ge sp parent i c t' sub rs fr m t lbl rs' fr' m',
  nbranchset i = true ->
  lnbranchset c = true ->
  exec_instructions_tree ge (plug (c ++ i :: nil) sub) sp parent rs fr m t lbl rs' fr' m' ->
  put i sub = Some t' ->
  exec_instructions_tree ge (plug c t')  sp parent rs fr m t lbl rs' fr' m'.
Proof. 
  intros.
  assert (lnbranchset (c ++ i :: nil) = true). 
    eapply br_prop; eauto. revert H3; intro LN.
  generalize (unplug _ _ _ _ _ _ _ _ _ _ _ _ _ nil H1 LN); intro.
  destruct H3 as [rsi [fri [mi [D E]]]]. 
  generalize (test_aux2 fundef _ _ _ _ c (i :: nil) _ _ _ _ _ _ _ D  (refl_equal (c ++ i :: nil))); intro.
  destruct H3 as [rsi' [fri' [mi' [F G]]]]. 
  rewrite <- app_comm_cons in F. rewrite  app_ass in F.
  eapply plugit; eauto. 
  inversion G; subst.
  rewrite <- app_comm_cons in H3. 
  generalize (simple_move fundef _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3); intro.
  simpl in H5. subst. 
  generalize (no_move fundef _ _ _ _ _ _ _ _ _ _ _  H4); intro.
  intuition subst.    
  generalize (no_trace _ _ _ _ _ _ _ _ _ _ _ _ H1); intro; subst.
  inversion H3; subst;
  simpl in H2; inversion H2; subst. 
  eapply exec_Mgetstack; eauto.
  eapply exec_Msetstack; eauto. 
  eapply exec_Mgetparam; eauto.
  eapply exec_Mop; eauto. 
  eapply exec_Mload; eauto.
  eapply exec_Mstore; eauto.  
  eapply exec_Malloc; eauto. 
Qed. 
  
Lemma direction:
  forall FF ge tge sp parent l f1 f2 rs fr m rs1 fr1 m1 rs2 fr2 m2 l' c b,
    (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
  sem FF ge sp parent rs fr m f1 rs1 fr1 m1 ->
  sem FF tge sp parent rs fr m f2 rs2 fr2 m2 ->
  listGet l f1 = listGet l' f2 ->
  eval_condition c rs1 ## l = Some b ->
  eval_condition c rs2 ## l' = Some b.
Proof.
  intros until 1. revert H. intro ENV1. intro ENV2. intros.   
  case_eq c; intros; subst.  

  (* ccomp *)
  assert (exists r1 : mreg, exists r2, l = r1 :: r2 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    destruct l. 
    simpl in H2. destruct (rs1 m0); inversion H2.
    exists m0. exists m3. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2; destruct (rs1 m3); inversion H2.
  destruct H3 as [r1 [r2 D]].
  subst. 
  assert (exists r1' : mreg, exists r2', l' = r1' :: r2' :: nil).
    destruct l'. 
    simpl in H1. inversion H1. 
    destruct l'. simpl in H1. inversion H1.
    exists m0; exists m3. 
    destruct l'. trivial. 
    simpl in H1. inversion H1. 
  destruct H3 as [r1' [r2' E]].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H5; subst. 
  inversion H0; subst. inversion H9; subst. 
  clear H5 H6 H7 H9 H10 H11. 
  generalize (H8 r1); intro. generalize (H8 r2); intro. 
  generalize (H12 r1'); intro. generalize (H12 r2'); intro.
  clear H8 H12.
  rewrite <- H3 in H9.
  rewrite <- H4 in H7.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto. 
  assert (rs1 r2 = rs2 r2'). 
    eapply fonct_value; eauto. 
  assert (rs1 ## (r1 :: r2 :: nil) = rs2 ## (r1' :: r2' :: nil)). 
  simpl. rewrite H8. rewrite H10. trivial.
  rewrite <- H11. trivial. 

  (* ccompu *)
  assert (exists r1 : mreg, exists r2, l = r1 :: r2 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    destruct l. 
    simpl in H2. destruct (rs1 m0); inversion H2.
    exists m0. exists m3. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2; destruct (rs1 m3); inversion H2.  
  destruct H3 as [r1 [r2 D]].
  subst. 
  assert (exists r1' : mreg, exists r2', l' = r1' :: r2' :: nil).
    destruct l'. 
    simpl in H1. inversion H1. 
    destruct l'. simpl in H1. inversion H1.
    exists m0; exists m3. 
    destruct l'. trivial. 
    simpl in H1. inversion H1. 
  destruct H3 as [r1' [r2' E]].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H5; subst. 
  inversion H0; subst. inversion H9; subst. 
  clear H5 H6 H7 H9 H10 H11. 
  generalize (H8 r1); intro. generalize (H8 r2); intro. 
  generalize (H12 r1'); intro. generalize (H12 r2'); intro.
  clear H8 H12.
  rewrite <- H3 in H9.
  rewrite <- H4 in H7.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto. 
  assert (rs1 r2 = rs2 r2'). 
    eapply fonct_value; eauto. 
  assert (rs1 ## (r1 :: r2 :: nil) = rs2 ## (r1' :: r2' :: nil)). 
  simpl. rewrite H8. rewrite H10. trivial.
  rewrite <- H11. trivial. 

  (* ccompimm *)
  assert (exists r1 : mreg, l = r1 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    exists m0. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2.
  destruct H3 as [r1 D].
  assert (exists r1' : mreg, l' = r1' :: nil).
    destruct l'. 
    simpl in H1. subst.  inversion H1. 
    exists m0. 
    destruct l'. trivial. 
    simpl in H1. subst.  inversion H1. 
  destruct H3 as [r1' E].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H4; subst. 
  inversion H0; subst. inversion H8; subst. 
  clear H4 H5 H6 H8 H9 H10. 
  generalize (H7 r1); intro.  
  generalize (H11 r1'); intro. 
  clear H7 H11.
  rewrite <- H3 in H5.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto.  
  assert (rs1 ## (r1 :: nil) = rs2 ## (r1' :: nil)). 
  simpl. rewrite H6. trivial. 
  rewrite <- H7. trivial. 

(* ccompuimm *)

  assert (exists r1 : mreg, l = r1 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    exists m0. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2.
  destruct H3 as [r1 D].
  assert (exists r1' : mreg, l' = r1' :: nil).
    destruct l'. 
    simpl in H1. subst.  inversion H1. 
    exists m0. 
    destruct l'. trivial. 
    simpl in H1. subst.  inversion H1. 
  destruct H3 as [r1' E].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H4; subst. 
  inversion H0; subst. inversion H8; subst. 
  clear H4 H5 H6 H8 H9 H10. 
  generalize (H7 r1); intro.  
  generalize (H11 r1'); intro. 
  clear H7 H11.
  rewrite <- H3 in H5.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto.  
  assert (rs1 ## (r1 :: nil) = rs2 ## (r1' :: nil)). 
  simpl. rewrite H6. trivial. 
  rewrite <- H7. trivial. 

(*ccompf *)

  assert (exists r1 : mreg, exists r2, l = r1 :: r2 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    destruct l. 
    simpl in H2. destruct (rs1 m0); inversion H2.
    exists m0. exists m3. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2; destruct (rs1 m3); inversion H2.
  destruct H3 as [r1 [r2 D]].
  subst. 
  assert (exists r1' : mreg, exists r2', l' = r1' :: r2' :: nil).
    destruct l'. 
    simpl in H1. inversion H1. 
    destruct l'. simpl in H1. inversion H1.
    exists m0; exists m3. 
    destruct l'. trivial. 
    simpl in H1. inversion H1. 
  destruct H3 as [r1' [r2' E]].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H5; subst. 
  inversion H0; subst. inversion H9; subst. 
  clear H5 H6 H7 H9 H10 H11. 
  generalize (H8 r1); intro. generalize (H8 r2); intro. 
  generalize (H12 r1'); intro. generalize (H12 r2'); intro.
  clear H8 H12.
  rewrite <- H3 in H9.
  rewrite <- H4 in H7.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto. 
  assert (rs1 r2 = rs2 r2'). 
    eapply fonct_value; eauto. 
  assert (rs1 ## (r1 :: r2 :: nil) = rs2 ## (r1' :: r2' :: nil)). 
  simpl. rewrite H8. rewrite H10. trivial.
  rewrite <- H11. trivial. 

  (* cnotcompf *)
  assert (exists r1 : mreg, exists r2, l = r1 :: r2 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    destruct l. 
    simpl in H2. destruct (rs1 m0); inversion H2.
    exists m0. exists m3. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2; destruct (rs1 m3); inversion H2.  
  destruct H3 as [r1 [r2 D]].
  subst. 
  assert (exists r1' : mreg, exists r2', l' = r1' :: r2' :: nil).
    destruct l'. 
    simpl in H1. inversion H1. 
    destruct l'. simpl in H1. inversion H1.
    exists m0; exists m3. 
    destruct l'. trivial. 
    simpl in H1. inversion H1. 
  destruct H3 as [r1' [r2' E]].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H5; subst. 
  inversion H0; subst. inversion H9; subst. 
  clear H5 H6 H7 H9 H10 H11. 
  generalize (H8 r1); intro. generalize (H8 r2); intro. 
  generalize (H12 r1'); intro. generalize (H12 r2'); intro.
  clear H8 H12.
  rewrite <- H3 in H9.
  rewrite <- H4 in H7.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto. 
  assert (rs1 r2 = rs2 r2'). 
    eapply fonct_value; eauto. 
  assert (rs1 ## (r1 :: r2 :: nil) = rs2 ## (r1' :: r2' :: nil)). 
  simpl. rewrite H8. rewrite H10. trivial.
  rewrite <- H11. trivial. 

  (* cmaskzero *)
  assert (exists r1 : mreg, l = r1 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    exists m0. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2.
  destruct H3 as [r1 D].
  assert (exists r1' : mreg, l' = r1' :: nil).
    destruct l'. 
    simpl in H1. subst.  inversion H1. 
    exists m0. 
    destruct l'. trivial. 
    simpl in H1. subst.  inversion H1. 
  destruct H3 as [r1' E].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H4; subst. 
  inversion H0; subst. inversion H8; subst. 
  clear H4 H5 H6 H8 H9 H10. 
  generalize (H7 r1); intro.  
  generalize (H11 r1'); intro. 
  clear H7 H11.
  rewrite <- H3 in H5.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto.  
  assert (rs1 ## (r1 :: nil) = rs2 ## (r1' :: nil)). 
  simpl. rewrite H6. trivial. 
  rewrite <- H7. trivial. 

(* cmasknotzero *)

  assert (exists r1 : mreg, l = r1 :: nil).
    destruct l. 
    simpl in H2. inversion H2. 
    exists m0. 
    destruct l. trivial. 
    simpl in H2. 
    destruct (rs1 m0); inversion H2.
  destruct H3 as [r1 D].
  assert (exists r1' : mreg, l' = r1' :: nil).
    destruct l'. 
    simpl in H1. subst.  inversion H1. 
    exists m0. 
    destruct l'. trivial. 
    simpl in H1. subst.  inversion H1. 
  destruct H3 as [r1' E].
  subst. 
  simpl in H1. 
  injection H1; intros. 
  inversion H; subst. inversion H4; subst. 
  inversion H0; subst. inversion H8; subst. 
  clear H4 H5 H6 H8 H9 H10. 
  generalize (H7 r1); intro.  
  generalize (H11 r1'); intro. 
  clear H7 H11.
  rewrite <- H3 in H5.
  assert (rs1 r1 = rs2 r1'). 
    eapply fonct_value; eauto.  
  assert (rs1 ## (r1 :: nil) = rs2 ## (r1' :: nil)). 
  simpl. rewrite H6. trivial. 
  rewrite <- H7. trivial. 
Qed.

Lemma listCheckProp:
  forall l f1 e,
  listCheck (listGet l f1) e = true ->
  (listGet l f1) = e.
Proof. 
  induction l; intros. 
  simpl. simpl in H. case_eq e; intros. 
  rewrite H0 in H. trivial.  rewrite H0 in H. inversion H. 
  simpl. simpl in H. 
  case_eq e; intros. rewrite H0 in H. inversion H.
  rewrite H0 in H. 
  generalize (essai _ _ H); intro. 
  destruct H1. 
  assert (f1 # (Reg a) = e0). eapply beq_expression_correct; eauto. 
  subst.    
  assert (listGet l f1 = e1). eapply IHl;eauto. 
  subst. trivial. 
Qed. 

Lemma wd_semantics_gen: 
  forall ge tge sp parent d f1 f2 s1 s2  ,
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
  validate_trees d f1 f2 s1 s2 = true ->
  forall t1 t2 c1 c2 rs fr m t lbl rs' fr' m'  rs0 fr0 m0 w,
  d = (t1,t2) ->
  abstract_sequence empty c1 = Some f1 ->
  abstract_sequence empty c2 = Some f2 ->
  constset.equal (compute_constraints_me c1 empty) s1 = true ->
  constset.equal (compute_constraints_me c2 empty) s2 = true ->
  exec_nb_instrs fundef ge sp parent (c1 ++ w) rs0 fr0 m0  E0 w rs fr m ->
  exec_instructions_tree ge t1 sp parent rs fr m t lbl rs' fr' m' ->
  lnbranchset c2 = true ->
  exec_instructions_tree tge (plug c2 t2) sp parent rs0 fr0 m0 t lbl rs' fr' m'.  
Proof. 
  intros ge tge sp parent d f1 f2 s1 s2 ENV1 ENV2. intro.  
  (*assert (forall (sp : val) (op : operation) (vl : list val), eval_operation ge sp op vl = eval_operation tge sp op vl).
    intros. 
    generalize (coerce1 ge sp0 op vl); intro.
    generalize (coerce1 tge sp0 op vl); intro.
    generalize (ENV1 sp0 op vl); intro. 
    congruence. 
  assert (forall (sp : val) (addr : addressing) (vl : list val), eval_addressing (coerce ge) sp addr vl = eval_addressing (coerce tge) sp addr vl).
    intros. 
    generalize (coerce2 ge sp0 addr vl); intro.
    generalize (coerce2 tge sp0 addr vl); intro.
    generalize (ENV2 sp0 addr vl); intro. 
    congruence. revert H0 H1; intros EV1 EV2. *)
  functional induction (validate_trees d f1 f2 s1 s2); intros.
    
  (* (out,out) *)

  clear e0. injection H0; intros; subst.   
  generalize (essai _ _ H); intro. 
  assert (nbic c1 c2 = true). 
    unfold nbic. 
    assert (compare c1 c2 = true). 
    unfold compare. destruct H8.  rewrite H1. rewrite H2. trivial. 
    assert (veriphi c1 c2 = true). unfold veriphi. 
    destruct H8. 
      generalize (constset.equal_2 H3); intro.
      generalize (constset.equal_2 H4); intro. 
      rewrite <- H11 in H10. rewrite <- H12 in H10. 
      rewrite H10.  trivial. 
    rewrite H9. rewrite H10. simpl. trivial. 
 (* assert (forall (sp : val) (op : operation) (vl : list val), eval_operation ge sp op vl = eval_operation (coerce tge) sp op vl).
    intros. 
    generalize (coerce1 ge sp0 op vl); intro.
    generalize (coerce1 tge sp0 op vl); intro.
    generalize (ENV1 sp0 op vl); intro. 
    congruence. 
  assert (forall (sp : val) (addr : addressing) (vl : list val), eval_addressing (coerce ge) sp addr vl = eval_addressing (coerce tge) sp addr vl).
    intros. 
    generalize (coerce2 ge sp0 addr vl); intro.
    generalize (coerce2 tge sp0 addr vl); intro.
    generalize (ENV2 sp0 addr vl); intro. 
    congruence. *)
  generalize (nbic_imply_equivalence fundef _ _ _ _ _ _ _ _ _ _ w _ _ _ H9 ENV1 ENV2 H5); intro.   
  inversion H6; subst. 
  eapply plugit; eauto. 
  eapply exec_Mout. 
 
  (* cas trivial *)
  inversion H.
  
  (* cond cond *)
  generalize (essai _ _ H); intro. clear e0. destruct H8.
  injection H0; intros; subst. clear H0.  
  inversion H6; subst. 
  
  (* premier cas *)
  generalize (IHb H8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (refl_equal (sub1,sub1'))
                    H1 H2 H3 H4 H5 H25 H7). 
  intro.                   
  assert (exists rsi, exists fri, exists mi,
             exec_nb_instrs fundef tge sp parent (c2 ++ w) rs0 fr0 m0 E0 w rsi fri mi /\
             exec_instructions_tree tge sub1' sp parent rsi fri mi E0 lbl rs' fr' m').
             eapply unplug; eauto. 
  destruct H10 as [rsi [fri [mi [D E]]]].            
  eapply plugit; eauto. 
  eapply exec_Mcond_true; eauto. 
  assert (sem fundef ge sp parent rs0 fr0 m0 f1 rs fr m).
    eapply eval_sym_correct_aux_spec; eauto.
  assert (sem fundef tge sp parent rs0 fr0 m0 f2 rsi fri mi).
    eapply eval_sym_correct_aux_spec; eauto.
  assert (listGet l f1 = listGet l' f2). 
    eapply listCheckProp; eauto. 
    eapply direction; eauto.  
  generalize (no_trace _ _ _ _ _ _ _ _ _ _ _ _ H0); intro. subst. 
  trivial. 

  (* second cas, symetriaue de premier *)
  generalize (IHb0 H9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (refl_equal (sub2,sub2'))
                    H1 H2 H3 H4 H5 H25 H7). 
  intro.                   
  assert (exists rsi, exists fri, exists mi,
             exec_nb_instrs fundef tge sp parent (c2 ++ w) rs0 fr0 m0 E0 w rsi fri mi /\
             exec_instructions_tree tge sub2' sp parent rsi fri mi E0 lbl rs' fr' m').
             eapply unplug; eauto. 
  destruct H10 as [rsi [fri [mi [D E]]]].            
  eapply plugit; eauto. 
  eapply exec_Mcond_false; eauto.
  assert (sem fundef ge sp parent rs0 fr0 m0 f1 rs fr m).
    eapply eval_sym_correct_aux_spec; eauto.
  assert (sem fundef tge sp parent rs0 fr0 m0 f2 rsi fri mi).
    eapply eval_sym_correct_aux_spec; eauto.
  assert (listGet l f1 = listGet l' f2). 
    eapply listCheckProp; eauto.
  eapply direction; eauto. 
  generalize (no_trace _ _ _ _ _ _ _ _ _ _ _ _ H0); intro. subst. 
  trivial.   
  
  (* 2 cas triviaux *)
  inversion H.
  inversion H. 
  
  (* descente a gauche *)
 
  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.  
  assert (nbranchset (Mach.Mgetstack i t m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.   
  eapply Valcommon.exec_Mgetstack; eauto. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.                 
  assert (nbranchset (Mach.Msetstack m i t) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.   
  eapply Valcommon.exec_Msetstack; eauto. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.  
  assert (nbranchset (Mach.Mgetparam i t m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.   
  eapply Valcommon.exec_Mgetparam; eauto. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.  
  assert (nbranchset (Mach.Mop op rl m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.   
  eapply Valcommon.exec_Mop; eauto. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.  
  assert (nbranchset (Mach.Mload chk addr rl m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.     
  eapply Valcommon.exec_Mload; eauto. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.  
  assert (nbranchset (Mach.Mstore chk addr rl m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.    
  eapply Valcommon.exec_Mstore; eauto. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.  
  inversion H6; subst.  
  assert (nbranchset (Mach.Malloc) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply H8; eauto. 
  eapply rew2_gen; eauto. 
  simpl. rewrite Rmap.gss. 
  rewrite Rmap.gso; try congruence. rewrite Rmap.gss. trivial. 
  rewrite app_ass. rewrite <- app_comm_cons. simpl. 
  eapply rew3_gen with (w' := (@nil Mach.instruction)); eauto.  
  eapply Valcommon.exec_Malloc; eauto. 

  (* descente a droite *)     

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Mgetstack i t m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial. 
  
  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Msetstack m i t) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Mgetparam i t m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Mop op rl m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Mload chk addr rl m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Mstore chk addr rl m) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial. 

  generalize (IHb H); intro. clear IHb.
  injection H0; intros; subst.
  assert (nbranchset (Mach.Malloc) = true). trivial. 
  generalize (rew1gen _ _ _ _ H9 H1); intro.
  eapply rew4_gen; eauto. 
  eapply H8; eauto.
  eapply rew1gen; eauto. 
  eapply rew2_gen; eauto. simpl. rewrite Rmap.gss. trivial. 
  rewrite Rmap.gso; try congruence. rewrite Rmap.gss. trivial. 
  eapply br_prop; eauto. simpl; trivial.  
 
  (* 2 cas triviaux *)
  inversion H.
  inversion H. 
Qed.   
  


Theorem wd_semantics: 
  forall ge tge sp parent t1 t2 rs fr m t lbl rs' fr' m',
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->   
  validate_trees (t1,t2) empty empty constset.empty constset.empty = true ->
  exec_instructions_tree ge t1 sp parent rs fr m t lbl rs' fr' m' ->
  exec_instructions_tree tge t2 sp parent rs fr m t lbl rs' fr' m'.
Proof. 
  intros. 
  assert (t2 = plug nil t2). simpl. trivial. 
  rewrite H3.
  assert (abstract_sequence empty nil = Some empty). 
    simpl. trivial. 
  assert (compute_constraints_me nil empty = constset.empty). 
    simpl. trivial. 
  assert (exec_nb_instrs fundef ge sp parent (nil ++ nil) rs fr m E0 nil rs fr m).
    eapply exec_refl_bl. 
  eapply wd_semantics_gen; eauto. 
Qed.   


