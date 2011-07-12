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

(** a semantics of non-branching sequences *)

Inductive exec_nb_instr (FF : Set) :
      Genv.t FF ->  val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_Mgetstack:
      forall ge sp parent ofs ty dst c rs fr m v,
      get_slot fr ty (Int.signed ofs) v ->
      exec_nb_instr FF ge sp parent
                 (Mgetstack ofs ty dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Msetstack:
     forall ge sp parent src ofs ty c rs fr m fr',
      set_slot fr ty (Int.signed ofs) (rs src) fr' ->
      exec_nb_instr FF ge sp parent
                 (Msetstack src ofs ty :: c) rs fr m
              E0 c rs fr' m
  | exec_Mgetparam:
      forall ge sp parent ofs ty dst c rs fr m v,
      get_slot parent ty (Int.signed ofs) v ->
      exec_nb_instr FF ge sp parent
                 (Mgetparam ofs ty dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Mop:
      forall ge sp parent op args res c rs fr m v,
      eval_operation ge sp op rs##args = Some v ->
      exec_nb_instr FF ge sp parent
                 (Mop op args res :: c) rs fr m
              E0 c (rs#res <- v) fr m
  | exec_Mload:
      forall ge sp parent chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_nb_instr FF ge sp parent
                 (Mload chunk addr args dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Mstore:
      forall ge sp parent chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      exec_nb_instr FF ge sp parent
                 (Mstore chunk addr args src :: c) rs fr m
              E0 c rs fr m'
  | exec_Malloc:
      forall ge sp parent c rs fr m sz m' blk,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_nb_instr FF ge sp parent
                 (Malloc :: c) rs fr m
              E0 c (rs#Conventions.loc_alloc_result <- 
                                              (Vptr blk Int.zero)) fr m'.

Inductive exec_nb_instrs (FF : Set) :
      Genv.t FF -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_refl_bl:
      forall ge sp parent c rs fr m,
      exec_nb_instrs FF ge sp parent  c rs fr m  E0 c rs fr m
  | exec_trans_bl:
      forall ge sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 c3 rs3 fr3 m3,
      exec_nb_instr FF ge sp parent c1 rs1 fr1 m1  E0 c2 rs2 fr2 m2 ->
      exec_nb_instrs FF ge sp parent c2 rs2 fr2 m2  E0 c3 rs3 fr3 m3 ->
      exec_nb_instrs FF ge sp parent c1 rs1 fr1 m1  E0 c3 rs3 fr3 m3.

(** Proof of computational equivalence *)

Require Import BasicLib. 

Lemma abstract_seq_correct_aux:
forall FF ge sp parent i c exps rs fr m rs0 fr0 m0 rs' fr' m' t,
nbranchset i = true ->
exec_nb_instr FF ge sp parent (i :: c) rs fr m t c rs' fr' m' ->
sem FF ge sp parent rs0 fr0 m0 exps rs fr m ->
sem FF ge sp parent rs0 fr0 m0 (update exps i) rs' fr' m'.
Proof. 
  intros. inversion H1. subst. inversion H2. subst. 
   
   destruct i; simpl; eapply Sem; eauto;inversion H0; try inversion H.

  (* getstack *)
  eapply Sregset; eauto. 
  intro. 
  generalize (resource_eq (Reg m1) (Reg x)); intro.
  destruct H22. injection e; intro.  rewrite e; rewrite H22. 
  rewrite map2. rewrite map3. eapply Sgetstack; eauto. 
  rewrite H19; auto. 
  generalize (tri1 _ _ n). intro. 
  rewrite map5; auto. rewrite genmap1;auto. 

  rewrite genmap1;auto. rewrite <- H19; auto. 
  congruence. 
  rewrite genmap1;auto. rewrite <- H20;auto. 
  congruence. 

  (* setstack *)

  eapply Sregset; eauto. 
  intro. rewrite genmap1. rewrite <- H18. auto. 
  congruence. 
  rewrite map2. 
  eapply Ssetstack;eauto. auto. rewrite  H18. auto.  
  generalize (H5 m1). intro; auto. 
  rewrite genmap1;auto. rewrite <- H20; auto. 
  congruence. 

  (* etparam *)
    
  eapply Sregset; eauto. intro. 
  generalize (resource_eq (Reg m1) (Reg x)); intro.
  destruct H22. injection e; intro. rewrite e; rewrite H22. 
  rewrite map2. rewrite map3. eapply Sgetparam; eauto. 
  generalize (tri1 _ _ n). intro. 
  rewrite map5; auto. rewrite genmap1; auto. 
  rewrite genmap1; auto. rewrite <- H19; auto. 
  congruence. 
  rewrite genmap1; auto. rewrite <- H20; auto. 
  congruence. 

  (* op *)

  eapply Sregset; eauto. intro. 
  generalize (resource_eq (Reg m1) (Reg x)); intro.
  destruct H22. injection e. intro. rewrite e; rewrite H22. 
  rewrite map2. rewrite map3. eapply Sop; eauto. 
  eapply gen_list_base; eauto. 

  generalize (tri1 _ _ n). intro. 
  rewrite genmap1; auto. rewrite map5; auto. 
  rewrite genmap1; auto. rewrite <- H19. auto. congruence.
  rewrite genmap1; auto. rewrite <- H20. auto. congruence. 

  (* load *)

  eapply Sregset; eauto. intro. 
  generalize (resource_eq (Reg m2) (Reg x)); intro.  
  destruct H24. injection e;intro. rewrite e; rewrite H24. 
  rewrite map2. rewrite map3. eapply Sload; eauto. 
  eapply gen_list_base; eauto. rewrite H21. auto.   
  
  generalize (tri1 _ _ n). intro. rewrite genmap1; auto. 
  rewrite map5; auto. 
  rewrite genmap1; auto. rewrite <- H20. auto. congruence.
  rewrite genmap1; auto. rewrite <- H21. auto. congruence. 

  (* store *)

  eapply Sregset; eauto. 
  intro. 
rewrite genmap1; auto. rewrite <- H19; auto. congruence. 
    rewrite genmap1; auto. rewrite <- H20. auto. congruence.
  rewrite map2. eapply Sstore; eauto. rewrite <- H19. 
  generalize (H5 m2). intro. auto. 
  eapply gen_list_base; eauto. rewrite  H19; eauto. 

  (* alloc1 *)
  eapply Sregset; eauto. intro. 
  rewrite genmap1;auto;try congruence. 
  generalize (resource_eq (Reg Conventions.loc_alloc_result) (Reg x)). intros.
  destruct H20. injection e; intro. rewrite H20. rewrite map2.
  rewrite map3. eapply Smalloc1;eauto. rewrite <- H7. 
  generalize (H5 Conventions.loc_alloc_argument). intro. unfold Rmap.get. 
  trivial. 

  rewrite genmap1; auto; try congruence. rewrite map5; eauto. 
  eapply tri1; eauto. 

  repeat (rewrite genmap1; auto; try congruence). 

  rewrite map2. eapply Smalloc2; eauto. 
  generalize (H5 Conventions.loc_alloc_argument). intro. unfold Rmap.get. 
  rewrite <- H7. trivial. 
Qed.

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
  generalize (exec_instr_length FF _ _ _  c1 _ _ _  c2 _ _ _ _ H).
  intro. omega.  
Qed.

Lemma no_move_aux:
forall FF ge sp parent c rs fr m c' rs' fr' m' t,
exec_nb_instrs FF ge sp parent c rs fr m t c' rs' fr' m' -> 
List.length c = List.length c' -> rs = rs' /\ fr = fr' /\ m = m'.
Proof.
  induction 1. 
  auto.
(*  intro. elimtype False. generalize (exec_instr_length _ _ _ _ _ _ _ _ _ _ _ _ _ H). omega.*)
  intro. generalize (exec_instr_length FF _ _ _ _ _ _ _ _ _ _ _ _ H); intro.
  generalize (exec_nb_instrs_length FF _ _ _ _ _ _ _ _ _  _ _ _ H0); intro.
  assert (length c2 = length c3). omega.
  generalize (IHexec_nb_instrs H4); intro.
  elimtype False. omega. 
Qed.  
  
Theorem no_move:
forall FF ge sp parent c rs fr m rs' fr' m' t,
exec_nb_instrs FF ge sp parent c rs fr m t c rs' fr' m' -> 
rs = rs' /\ fr = fr' /\ m = m'.
Proof.
  intros. eapply no_move_aux; eauto. 
Qed.

Lemma simple_move:
  forall FF ge sp parent i c k rs fr m t c' rs' fr' m', 
  exec_nb_instr FF ge sp parent (i :: c ++ k) rs fr m t c' rs' fr' m' ->
  c' = c ++ k.
Proof. 
  destruct i; intros; inversion H; trivial. 
Qed.  
(*
Lemma nb_to_usual:
  forall FF ge f sp parent i c' rs fr m t rs' fr' m',
  exec_nb_instr FF ge sp parent (i :: c') rs fr m t c' rs' fr' m' ->
  exec_instr ge f sp parent (i :: c') rs fr m t c' rs' fr' m'.
Proof. 
  intros. destruct i; inversion H. 
  eapply Machabstr.exec_Mgetstack; eauto. 
  eapply Machabstr.exec_Msetstack; eauto. 
  eapply Machabstr.exec_Mgetparam; eauto. 
  eapply Machabstr.exec_Mop; eauto. 
  eapply Machabstr.exec_Mload; eauto. 
  eapply Machabstr.exec_Mstore; eauto. 
  eapply Machabstr.exec_Malloc; eauto. 
Qed. 
  *)
Lemma nb_branch_well:
  forall FF ge sp parent i c rs fr m rs' fr' m' t,
  exec_nb_instr FF ge sp parent (i :: c) rs fr m t c rs' fr' m' ->
  nbranchset i = true.
Proof. 
  intros. 
  destruct i; trivial; try 
  (inversion H;  inversion H0).  
Qed. 

Lemma nb_branchs_well:
  forall FF ge sp parent c rs fr m k rs' fr' m' t,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m t k rs' fr' m' ->
  lnbranchset c = true.
Proof.  
  induction c; intros. trivial. 
  rewrite <- app_comm_cons in H. 
  destruct a; try (inversion H;
  [
  elimtype False; eapply list_diff; eauto |
  assert (c2 = c ++ k); [eapply simple_move; eauto | subst;eapply IHc; eauto]
  ]); try (inversion H; [elimtype False; eapply list_diff; eauto|inversion H0]). 
Qed.   

Lemma abstract_succeed2:
  forall FF ge sp parent c rs fr m k rs' fr' m' fo t,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m t k rs' fr' m' ->
  exists x, abstract_sequence fo c = Some x.
Proof. 
  intros. eapply abstract_succeed; eauto. 
  eapply nb_branchs_well; eauto. 
Qed. 

Lemma eval_sym_correct_aux:
  forall FF ge sp parent c rs fr m t k rs' fr' m' fo rs0 fr0 m0 exps,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m t k rs' fr' m' ->
  sem FF ge sp parent rs0 fr0 m0 exps rs fr m ->
  abstract_sequence exps c = Some fo ->
  sem FF ge sp parent rs0 fr0 m0 fo rs' fr' m'.
Proof. 
  induction c; intros. 
  simpl in H. generalize (no_move FF _ _ _ _ _  _ _ _ _ _ _ H). 
  intuition subst. simpl in H1. injection H1. intuition subst. 
  trivial. 
  
  rewrite <- app_comm_cons in H. inversion H. elimtype False. 
  eapply list_diff; eauto. 
  generalize (simple_move FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2). intro. 
  rewrite H16 in H3. 
  rewrite H16 in H2. 
  generalize (nb_branch_well FF _ _ _ _ _ _ _ _ _ _ _ _ H2). intro. 
  generalize (abstract_seq_correct_aux FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  H17 H2 H0).
  intro. 
  eapply IHc; eauto. 
  destruct a;  try inversion H17; subst; trivial.
Qed.   
  


Lemma eval_sym_end_aux:
  forall FF ge sp parent c rs fr m t k rs' fr' m' ff,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m t k rs' fr' m' ->
  exists fo, abstract_sequence ff c = Some fo.
Proof. 
  induction c; intros. 
  exists ff. simpl. trivial. 
  rewrite <- app_comm_cons in H. 
  inversion H. 
  elimtype False. eapply list_diff; eauto. 
  subst. generalize (simple_move FF _ _  _ _ _ _ _ _ _ _ _ _ _ _ H0). 
  intro. subst. 
  generalize (IHc _ _ _ _ _ _ _ _ (update ff a) H1). intro. 
  destruct H2. 
  exists x. 
  destruct a; trivial; try inversion H0.   
Qed.   

Lemma eval_sym_end:
  forall FF ge sp parent c rs fr m t k rs' fr' m',
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m t k rs' fr' m' ->
  exists fo, abstract_sequence empty c = Some fo. 
Proof.  
  intros. 
  eapply eval_sym_end_aux; eauto. 
Qed. 

Lemma eval_sym_correct_aux_spec:
  forall FF ge sp parent c rs fr m t k rs' fr' m' fo,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m t k rs' fr' m' ->
  abstract_sequence empty c = Some fo ->
  sem FF ge sp parent rs fr m fo rs' fr' m'.
Proof. 
  intros. eapply eval_sym_correct_aux; eauto. 
  eapply empty_no_move; eauto. 
Qed. 
 
Lemma compare_fundamental_property :
  forall FF ge tge sp parent c1 c2 rs fr m k rs' fr' m' k' rs'' fr'' m'' t,
  compare c1 c2 = true -> 
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
  exec_nb_instrs FF ge sp parent (c1 ++ k) rs fr m t k rs' fr' m'-> 
  exec_nb_instrs FF tge sp parent (c2 ++ k') rs fr m t k' rs'' fr'' m'' ->
  rs' = rs'' /\ fr' = fr'' /\ m' = m''.
Proof. 
  intros until 1. intros ENV1 ENV2. intros.  
  unfold compare in H. 
  generalize (abstract_succeed2 FF _ _ _ _ _ _ _ _ _ _ _  empty _  H0). 
  generalize (abstract_succeed2 FF _ _ _ _ _ _ _ _ _ _ _  empty _  H1). 
  intros. 
  destruct H2. destruct H3. rewrite H2 in H. rewrite H3 in H. 
  generalize (eval_sym_correct_aux_spec FF _ _ _ _ _ _ _ _ _ _ _ _ _  H0 H3). 
  generalize (eval_sym_correct_aux_spec FF tge _ _ _ _ _ _ _ _ _ _ _ _  H1 H2).
  intros. 
  inversion H4; subst. inversion H6; subst. 
  inversion H5; subst. inversion H10; subst. 
  clear H4 H5 H6 H10. 
  generalize (check_correct_bis x0 x H). intro. 
  generalize (H4 Stack). intro; subst. 
  generalize (H4 Mem). intro; subst. 
  assert (forall r, rs' r = rs'' r). 
    intro.  
    generalize (H9 r). generalize (H13 r). generalize (H4 (Reg r)).  
    intros. rewrite <- H10 in H15. 
    generalize (fonct_value FF _ _ _ _ _ _ _ _ _  _ ENV1 ENV2 H14 H15). 
    intro. trivial. 
  rewrite H5 in H11. rewrite H6 in H12. 
  generalize (fonct_frame FF _ _ _ _ _ _ _ _ _  _ ENV1 ENV2 H11 H7). 
  generalize (fonct_mem FF _ _ _ _ _ _ _ _ _  _ ENV1 ENV2 H12 H8). 
  intros; subst. 
  intuition. 
  generalize (Regmap.exten rs' rs'' H10). trivial. 
Qed.   

(** Proof of well defined semantics *)

Lemma sem_to_exec_aux:
  forall FF ge sp parent f i w rs0 fr0 m0 rs fr m rs' fr' m',
  nbranchset i = true ->
  sem FF ge sp parent rs0 fr0 m0 f rs fr m ->
  sem FF ge sp parent rs0 fr0 m0 (update f i) rs' fr' m' ->
  exec_nb_instr FF ge sp parent (i :: w) rs fr m E0 w rs' fr' m'.
Proof. 
  intros. 
  destruct i; inversion H. 

  (* Mgetstack *)
  simpl in H1. 
  inversion H0; subst. 
  inversion H1; subst. 
  rewrite genmap1 in H6; try congruence. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H6). intro; subst. 
  rewrite genmap1 in H7; try congruence. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H7). intro; subst. 
  inversion H5; subst. 
  generalize (gen_one_changed_reg FF _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H8). intro.
  generalize (Regmap.exten _ _ H9). intro. rewrite H10. clear H10. 
  generalize (H8 m1). intro. inversion H10; subst.
  rewrite map2 in H11. injection H11; intros; subst. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H12). intro; subst.   
  eapply exec_Mgetstack; eauto. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H18; congruence. 
  rewrite map2 in H11; congruence. 
  
  (* Msetstack *)
  simpl in H1. 
  inversion H0; subst. inversion H1; subst. 
  rewrite genmap1 in H7; try congruence. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H7). intro; subst. 
  inversion H5; subst. 
  generalize (gen_regset_unchanged_Stack FF _ _ _ _ _ _ _ _ _ _ _ _ H0 H8). intro. 
  generalize (Regmap.exten _ _ H9). intro; subst. 
  rewrite map2 in H6. inversion H6; subst. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H21). intro; subst. 
  generalize (H8 m1). intro. rewrite genmap1 in H10; try congruence. 
  generalize (s_fonct_value FF _ _ _ _ _ _ _ _ _ H10 H22). intro; subst. 
  eapply exec_Msetstack; eauto. 

  (* Mgetparam *)
  simpl in H1. 
  inversion H0; subst. inversion H1; subst. 
  rewrite genmap1 in H6; try congruence. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H6); intro; subst. 
  rewrite genmap1 in H7; try congruence. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H7); intro; subst. 
  inversion H5; subst. 
  generalize (gen_one_changed_reg FF _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H8). intro.
  generalize (Regmap.exten _ _ H9). intro. rewrite H10. clear H10.   
  generalize (H8 m1). intro. inversion H10; subst.
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11. injection H11; intros; subst. 
  eapply exec_Mgetparam; eauto. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H18; congruence.   
  rewrite map2 in H11; congruence. 

  (* Mop *)
  simpl in H1. 
  inversion H0; subst. inversion H1; subst. 
  rewrite genmap1 in H6; try congruence. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H6); intro; subst. 
  rewrite genmap1 in H7; try congruence. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H7); intro; subst. 
  inversion H5; subst. 
  generalize (gen_one_changed_reg FF _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H8). intro.
  generalize (Regmap.exten _ _ H9). intro. rewrite H10. clear H10.     
  generalize (H8 m1). intro. inversion H10; subst.
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11. injection H11; intros; subst. 
  inversion H2; subst. 
  generalize (gen_list_base FF _ _ _ l _ _ _ _ _ H13). intro.  
  generalize (gen_list_translation_det FF _ _ _ _ _ _ _ _ _ _ H12 H14). intro. subst.   
  eapply exec_Mop; eauto. 
  rewrite map2 in H18; congruence. 
  rewrite map2 in H11; congruence. 

  (* Mload *)
  simpl in H1. 
  inversion H0; subst. inversion H1; subst. 
  rewrite genmap1 in H6; try congruence. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H6); intro; subst. 
  rewrite genmap1 in H7; try congruence. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H7); intro; subst. 
  inversion H5; subst. 
  generalize (gen_one_changed_reg FF _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H8). intro.
  generalize (Regmap.exten _ _ H9). intro. rewrite H10. clear H10.   
  generalize (H8 m2). intro. inversion H10; subst.
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H11. injection H11; intros; subst. 
  inversion H2; subst. 
  generalize (gen_list_base FF _ _ _ l _ _ _ _ _ H15). intro.  
  generalize (gen_list_translation_det FF _ _ _ _ _ _ _ _ _ _ H13 H16). intro. subst.     
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H12 H4). intro; subst. 
  eapply exec_Mload; eauto. 
  rewrite map2 in H11; congruence. 
  rewrite map2 in H18; congruence. 
  rewrite map2 in H11; congruence.

  (* Mstore *)    
  simpl in H1. 
  inversion H0; subst. inversion H1; subst. 
  rewrite genmap1 in H6; try congruence. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H6). intro; subst. 
  inversion H5; subst. 
  generalize (gen_regset_unchanged_Mem FF _ _ _ _ _ _ _ _ _ _ _ _ H0 H8). intro. 
  generalize (Regmap.exten _ _ H9). intro; subst. 
  rewrite map2 in H7. inversion H7; subst. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H21). intro; subst. 
  generalize (H8 m2). intro. rewrite genmap1 in H10; try congruence. 
  generalize (s_fonct_value FF _ _ _ _ _ _ _ _ _ H10 H23). intro; subst. 
  inversion H2; subst. 
  generalize (gen_list_base FF _ _ _ l _ _ _ _ _ H11). intro.  
  generalize (gen_list_translation_det FF _ _ _ _ _ _ _ _ _ _ H12 H24). intro. subst.       
  eapply exec_Mstore; eauto. 

  (* Malloc *)
  simpl in H1. 
  inversion H0; subst. inversion H1; subst. 
  rewrite genmap1 in H6; try congruence. 
  rewrite genmap1 in H6; try congruence. 
  generalize (s_fonct_frame FF _ _ _ _ _ _ _ _ _ H3 H6). intro; subst. 
  rewrite map2 in H7. 
  
  inversion H7; subst. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H17). intro; subst. 
  inversion H2; subst. generalize (H8 (Conventions.loc_alloc_argument)).
  intro. generalize (s_fonct_value FF _ _ _ _ _ _ _ _ _ H9 H10). intro; subst. 

  inversion H5; subst. 
  
  cut (rs' = Regmap.set Conventions.loc_alloc_result (Vptr blk Int.zero) rs). 
  intro; subst. 

  eapply exec_Malloc; eauto. 
  (* unfold Rmap.get in H12. *)
  
  cut (forall x, rs' x = Regmap.set Conventions.loc_alloc_result (Vptr blk Int.zero) rs x). 
  intro. 
  generalize (Regmap.exten _ _ H13). intro. trivial. 

  intro. generalize (mreg_eq x Conventions.loc_alloc_result). 
  intro. destruct H13. 
  subst. generalize (H12 Conventions.loc_alloc_result). intro. 
  rewrite Rmap.gso in H13; try congruence. 
  rewrite Rmap.gss in H13. 
  inversion H13; subst. rewrite map3. 
  generalize (s_fonct_mem FF _ _ _ _ _ _ _ _ _ H4 H26). intro; subst. 
  generalize (s_fonct_value FF _ _ _ _ _ _ _ _ _ H25 H9). intro; subst. 
  rewrite H11 in H14. injection H14. intro; subst. rewrite H27 in H19. 
  injection H19; intros; subst; trivial. 
  
  generalize (H12 x). intros. rewrite genmap1 in H13; try congruence. 
  rewrite genmap1 in H13; try congruence. 
  generalize (H8 x). intro. 
  generalize (s_fonct_value FF _ _ _ _ _ _ _ _ _ H13 H14). intros. 
  rewrite map5; try congruence. 
Qed. 


 

Lemma sem_to_exec:
  forall FF ge sp parent i w rs fr m rs' fr' m',
  nbranchset i = true ->
  sem FF ge sp parent rs fr m (update empty i) rs' fr' m' ->
  exec_nb_instr FF ge sp parent (i :: w) rs fr m E0 w rs' fr' m'. 
Proof. 
  intros. 
  eapply sem_to_exec_aux; eauto. 
  eapply empty_no_move; eauto. 
Qed.


Lemma test_aux2:
  forall FF ge sp parent c s1 s2 rs fr m k rs' fr' m',
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' ->
    c = s1 ++ s2 ->
  exists rs'', exists fr'', exists m'',
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 (s2 ++ k) rs'' fr'' m''.
Proof.  
  induction c; intros. 
  simpl in H. 
  generalize (no_move FF _ _ _ _ _ _ _ _ _ _ _ H); intro. intuition subst. 
  assert (s2 = nil). clear H. induction s1. simpl in H0. congruence. 
    rewrite <- app_comm_cons in H0. congruence. 
  subst. simpl. exists rs'; exists fr'; exists m'. eapply exec_refl_bl; eauto. 
  
  rewrite <- app_comm_cons in *|-. 
  rewrite <- app_comm_cons. 
  inversion H. elimtype False. eapply list_diff; eauto. 
  subst. 
  generalize (simple_move FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1). intro. subst. 
  case_eq s1; intro. subst. simpl in H0. rewrite <- H0. 
  exists rs; exists fr; exists m. rewrite app_comm_cons. 
  eapply exec_refl_bl; eauto. 
  intros. subst. 
  assert ((i :: l) ++ s2 = i :: l ++ s2). rewrite app_comm_cons. trivial. 
  rewrite H3 in H0. 
  assert (c = l ++ s2). congruence. 
  generalize (IHc _ _ _ _ _ _ _ _ _ H2 H4). intro. 
  destruct H5 as [rs'' [fr'' [m'' A]]]. 
  exists rs''; exists fr''; exists m''. eapply exec_trans_bl; eauto. 
Qed. 
  
Lemma list_util:
  forall (l : list instruction),
  l <> nil -> exists l', exists e, l = l' ++ e :: nil. 
Proof. 
  induction l; intros. 
  congruence. 
  case_eq l; intros; subst. 
  exists (@nil instruction) ; exists a. simpl. trivial. 
  assert (i :: l0 <> nil). 
    congruence. 
  generalize (IHl H0). intro. 
  destruct H1 as [l' [e A]]. 
  rewrite A. 
  exists (a :: l'); exists e. simpl. trivial. 
Qed. 

Lemma abstr_comp : 
  forall l i f x x0,
  abstract_sequence f (l ++ i :: nil) = Some x ->
  abstract_sequence f l = Some x0 ->
  x = update x0 i.
Proof. 
  induction l; intros. 
  simpl in *|-. injection H0. intro; subst. 
  destruct i ; simpl in *|- ; simpl ; trivial ; try congruence. 
  rewrite <- app_comm_cons in H. 
  simpl in *|-; destruct a. 

  generalize (IHl i (update f (Mgetstack i0 t m)) _ _ H H0); intro; trivial. 
  generalize (IHl i (update f (Msetstack m i0 t)) _ _ H H0); intro; trivial.
  generalize (IHl i (update f (Mgetparam i0 t m)) _ _ H H0); intro; trivial.
  generalize (IHl i (update f (Mop o l0 m)) _ _ H H0); intro; trivial.
  generalize (IHl i (update f (Mload m a l0 m0)) _ _ H H0); intro; trivial.
  generalize (IHl i (update f (Mstore m a l0 m0)) _ _ H H0); intro; trivial.
  inversion H. 
  generalize (IHl i (update f (Malloc)) _ _ H H0); intro; trivial.  
  inversion H. 
  inversion H. 
  inversion H. 
  inversion H. 
Qed. 

Lemma list_diff3:
  forall l (i : instruction),
  l ++ i :: nil = nil -> False.
Proof. 
  induction l; intros; simpl; inversion H. 
Qed.  


Lemma abstr_comp2 :
  forall l i f x,
  abstract_sequence f l = Some x ->
  compute_one_constraint (l ++ i :: nil) f = 
  compute_one_constraint (i :: nil) x.
Proof. 
  induction l; intros. 
  simpl in H. injection H; intro; subst. 
  destruct i; simpl; trivial. 
  
  destruct a; simpl in H; 
  try (generalize (IHl i _ _ H); intro; rewrite <- H0; rewrite <- app_comm_cons; 
  case_eq (l ++ i :: nil); intros; [elimtype False; eapply list_diff3; eauto |
  trivial]); try inversion H.     
Qed. 

Lemma lnbranchset_prop:
  forall l i,
  lnbranchset (l ++ i :: nil) = true -> lnbranchset l = true.
Proof. 
  induction l; intros. 
  trivial. 
  rewrite <- app_comm_cons in H. 
  destruct a; simpl in H; try (generalize (IHl i H); intro; simpl ; trivial); 
  try (inversion H). 
Qed.   
  


Lemma test_aux_v : 
  forall FF ge sp parent c e r rs fr m rs' fr' m' k,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' -> 
  constset.mem (Const e (Reg r)) (compute_constraints_me c empty) = true ->
  exists v, sem_value FF ge sp parent rs fr m e v.
Proof.
  intros. 

  (* il exists une sous liste amenant a cette contrainte *)
  generalize (test_aux c e r empty H0); intro; destruct H1 as [s1 [s2 [A B]]]. 
  (* cette sous liste est semantiquement bien definie *)
  generalize (test_aux2 FF _ _ _ _ _ _ _ _ _ _ _ _ _  H A); intro; destruct H1 as [rs'' [fr'' [m'' C]]]. 
  rewrite A in *|- . rewrite <- ass_app in *|-. 
  (* sa version abstraite est donc semantiquement bien definie *)
  generalize (eval_sym_end FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro; destruct H1. 
  generalize (eval_sym_correct_aux_spec FF _ _ _ _ _ _ _ _ _ _ _ _ _ C H1); intro. 

  case_eq s1; intros. subst. simpl in B. 
  unfold constraintdt.eq in B. simpl in B. elimtype False. trivial.  subst. 

  assert (i :: l <> nil); try congruence. 
  generalize (list_util (i :: l) H3); intro; destruct H4 as [l1 [i1 A]]. 
  rewrite A in * |-. 
 
  generalize (nb_branchs_well  FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro. 
  assert (lnbranchset l1 = true). eapply lnbranchset_prop; eauto.  
  generalize (abstract_succeed _ empty  H5); intro; destruct H6. 
  
  assert (x = update x0 i1). 
    eapply abstr_comp; eauto.  
  rewrite (abstr_comp2 l1 i1 empty x0 H6) in B.   

  destruct i1; simpl in B;   try (generalize (consteq_1 _ _ _ _ B); intro CON; 
  injection CON; intros;subst); 
  try (
  inversion H2;subst ; inversion H7; subst; 
  generalize (H10 m0); intro; exists (rs'' m0);
  simpl in H11; unfold Rmap.get; trivial ); try (generalize (consteq_1 _ _ _ _ B); intro CON; discriminate CON);
  try (
  inversion H2;subst ; inversion H7; subst; 
  generalize (H10 m1); intro; exists (rs'' m1);
  simpl in H11; unfold Rmap.get; trivial); try inversion B.  
Qed. 

Lemma test_aux_fr : 
  forall FF ge sp parent c e rs fr m rs' fr' m' k,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' -> 
  constset.mem (Const e Stack) (compute_constraints_me c empty) = true ->
  exists ffr, sem_frame FF ge sp parent rs fr m e ffr.
Proof.
  intros. 

  (* il exists une sous liste amenant a cette contrainte *)
  generalize (test_aux_bis c e empty H0); intro; destruct H1 as [s1 [s2 [A B]]]. 
  (* cette sous liste est semantiquement bien definie *)
  generalize (test_aux2 FF _ _ _ _ _ _ _ _ _ _ _ _ _  H A); intro; destruct H1 as [rs'' [fr'' [m'' C]]]. 
  rewrite A in *|- . rewrite <- ass_app in *|-. 
  (* sa version abstraite est donc semantiquement bien definie *)
  generalize (eval_sym_end FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro; destruct H1. 
  generalize (eval_sym_correct_aux_spec FF _ _ _ _ _ _ _ _ _ _ _ _ _ C H1); intro. 

  case_eq s1; intros. subst. simpl in B. 
  unfold constraintdt.eq in B. simpl in B. elimtype False. trivial.  subst. 

  assert (i :: l <> nil); try congruence. 
  generalize (list_util (i :: l) H3); intro; destruct H4 as [l1 [i1 A]]. 
  rewrite A in * |-. 
 
  generalize (nb_branchs_well FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro. 
  assert (lnbranchset l1 = true). eapply lnbranchset_prop; eauto.  
  generalize (abstract_succeed _ empty  H5); intro; destruct H6. 
  
  assert (x = update x0 i1). 
    eapply abstr_comp; eauto.  
  rewrite (abstr_comp2 l1 i1 empty x0 H6) in B.   

  destruct i1; simpl in B;   try (generalize (consteq_1 _ _ _ _ B); intro CON; 
  injection CON; intros;subst); 
  try inversion B.  


  inversion H2;subst.   exists (fr'').
  simpl in H8. trivial.  
Qed. 

Lemma test_aux_m : 
  forall FF ge sp parent c e rs fr m rs' fr' m' k,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' -> 
  constset.mem (Const e Mem) (compute_constraints_me c empty) = true ->
  exists mm, sem_mem FF ge sp parent rs fr m e mm.
Proof.
  intros. 

  (* il exists une sous liste amenant a cette contrainte *)
  generalize (test_aux_bis2 c e empty H0); intro; destruct H1 as [s1 [s2 [A B]]]. 
  (* cette sous liste est semantiquement bien definie *)
  generalize (test_aux2 FF _ _ _ _ _ _ _ _ _ _ _ _ _  H A); intro; destruct H1 as [rs'' [fr'' [m'' C]]]. 
  rewrite A in *|- . rewrite <- ass_app in *|-. 
  (* sa version abstraite est donc semantiquement bien definie *)
  generalize (eval_sym_end FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro; destruct H1. 
  generalize (eval_sym_correct_aux_spec FF _ _ _ _ _ _ _ _ _ _ _ _ _ C H1); intro. 

  case_eq s1; intros. subst. simpl in B. 
  unfold constraintdt.eq in B. simpl in B. elimtype False. trivial.  subst. 

  assert (i :: l <> nil); try congruence. 
  generalize (list_util (i :: l) H3); intro; destruct H4 as [l1 [i1 A]]. 
  rewrite A in * |-. 
 
  generalize (nb_branchs_well FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro. 
  assert (lnbranchset l1 = true). eapply lnbranchset_prop; eauto.  
  generalize (abstract_succeed _ empty  H5); intro; destruct H6. 
  
  assert (x = update x0 i1). 
    eapply abstr_comp; eauto.  
  rewrite (abstr_comp2 l1 i1 empty x0 H6) in B.   

  destruct i1; simpl in B;   try (generalize (consteq_1 _ _ _ _ B); intro CON; 
  injection CON; intros;subst); 
 try inversion B.  

  inversion H2;subst.   exists (m'').
  simpl in H9. trivial.  

Qed. 

Lemma test_aux_bi : 
  forall FF ge sp parent c e1 r e2 rs fr m rs' fr' m' k,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' -> 
  constset.mem (BiConst e1 Mem e2 (Reg r)) (compute_constraints_me c empty) = true ->
  (exists v, sem_value FF ge sp parent rs fr m e2 v) /\ 
  (exists mm, sem_mem FF ge sp parent rs fr m e1 mm).
Proof.
  intros. 

  (* il exists une sous liste amenant a cette contrainte *)
  generalize (test_aux_bis3 c e1 r e2 empty H0); intro; destruct H1 as [s1 [s2 [A B]]]. 
  (* cette sous liste est semantiquement bien definie *)
  generalize (test_aux2 FF _ _ _ _ _ _ _ _ _ _ _ _ _  H A); intro; destruct H1 as [rs'' [fr'' [m'' C]]]. 
  rewrite A in *|- . rewrite <- ass_app in *|-. 
  (* sa version abstraite est donc semantiquement bien definie *)
  generalize (eval_sym_end FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro; destruct H1. 
  generalize (eval_sym_correct_aux_spec FF _ _ _ _ _ _ _ _ _ _ _ _ _ C H1); intro. 

  case_eq s1; intros. subst. simpl in B. 
  unfold constraintdt.eq in B. simpl in B. elimtype False. trivial.  subst. 

  assert (i :: l <> nil); try congruence. 
  generalize (list_util (i :: l) H3); intro; destruct H4 as [l1 [i1 A]]. 
  rewrite A in * |-. 
 
  generalize (nb_branchs_well FF _ _ _ _ _ _ _ _ _ _ _ _ C); intro. 
  assert (lnbranchset l1 = true). eapply lnbranchset_prop; eauto.  
  generalize (abstract_succeed _ empty  H5); intro; destruct H6. 
  
  assert (x = update x0 i1). 
    eapply abstr_comp; eauto.  
  rewrite (abstr_comp2 l1 i1 empty x0 H6) in B.   

  destruct i1; simpl in B;   try (generalize (consteq_1 _ _ _ _ B); intro CON; 
  injection CON; intros;subst); 
   try inversion B.  

  split. 
  inversion H2; subst. inversion H8; subst. 
  generalize (H7 Conventions.loc_alloc_result). intro. 
  exists (rs'' Conventions.loc_alloc_result). 
  generalize (consteq_2 _ _ _ _ _ _ _ _ B). 
  intro. injection H12; intros; subst. 
  clear H12 B H0. simpl in H11. (*
  unfold Rmap.get. unfold Rmap.get in H11.*)  
  trivial. 
  
  inversion H2; subst. inversion H8; subst. 
  exists m''. 
  generalize (consteq_2 _ _ _ _ _ _ _ _ B). 
  intro. injection H11; intros; subst. simpl in H10.  
  
  rewrite map2 in H10. 
  rewrite Rmap.gss. 
trivial. 
Qed.   


 

Definition constsat (FF : Set) (ge : Genv.t FF) (sp : val) (parent : frame) 
                            (rs : regset) (fr : frame) (m : mem) (cons : constraint) : Prop:= 
  forall e r e1 r1 e2 r2,
  (cons = Const e r -> 
  (exists v, sem_value FF ge sp parent rs fr m e v) \/
  (exists ffr, sem_frame FF ge sp parent rs fr m e ffr) \/
  (exists mm, sem_mem FF ge sp parent rs fr m e mm)) /\
  (cons = BiConst e1 r1 e2 r2 -> 
  (exists v, sem_value FF ge sp parent rs fr m e2 v) /\
  (exists mm, sem_mem FF ge sp parent rs fr m e1 mm)) .


Lemma coolie:
  forall c e1 r1 e2 r2 tf cons,
  cons = BiConst e1 r1 e2 r2 ->
  constset.mem cons (compute_constraints_me c tf) = true ->
  (exists r, r2 = Reg r) /\ r1 = Mem. 
Proof. 
  induction c; intros. 
  simpl in H0. inversion H0. 
  destruct a; simpl in H0. 

  case_eq (constraint_eq (cons) (Const
             (Rmap.get (Reg m)
                tf # (Reg m) <- (Egetstack i t (Rmap.get Stack tf))) 
             (Reg m)) ); intros. 
  subst. inversion H1. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 
             
  case_eq (constraint_eq (cons) (Const
             (Rmap.get Stack
                tf # Stack <-
                (Esetstack (Rmap.get Stack tf) (Rmap.get (Reg m) tf) i t))
             Stack) ); intros. 
  subst. inversion H1. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 

  case_eq (constraint_eq (cons) (Const (Rmap.get (Reg m) tf # (Reg m) <- (Egetparam i t)) (Reg m)) ); intros. 
  subst. inversion H1. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 

  case_eq (constraint_eq (cons) (Const
             (Rmap.get (Reg m)
                tf # (Reg m) <- (Eop o (list_translation l tf))) (Reg m)) ); intros. 
  subst. inversion H1. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 

  case_eq (constraint_eq (cons) (Const
             (Rmap.get (Reg m0)
                tf # (Reg m0) <-
                (Eload m a (list_translation l tf) (Rmap.get Mem tf)))
             (Reg m0)) ); intros. 
  subst. inversion H1. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 

  case_eq (constraint_eq (cons) (Const
             (Rmap.get Mem
                tf # Mem <-
                (Estore (Rmap.get Mem tf) m a (list_translation l tf)
                   (Rmap.get (Reg m0) tf))) Mem) ); intros. 
  subst. inversion H1. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 

  inversion H0. 

  case_eq (constraint_eq (cons) (BiConst
             (Rmap.get Mem
                (tf # (Reg Conventions.loc_alloc_result) <-
                 (Emalloc1 (Rmap.get (Reg Conventions.loc_alloc_argument) tf)
                    (Rmap.get Mem tf))) # Mem <-
                (Emalloc2 (Rmap.get (Reg Conventions.loc_alloc_argument) tf)
                   (Rmap.get Mem tf))) Mem
             (Rmap.get (Reg Conventions.loc_alloc_result)
                (tf # (Reg Conventions.loc_alloc_result) <-
                 (Emalloc1 (Rmap.get (Reg Conventions.loc_alloc_argument) tf)
                    (Rmap.get Mem tf))) # Mem <-
                (Emalloc2 (Rmap.get (Reg Conventions.loc_alloc_argument) tf)
                   (Rmap.get Mem tf))) (Reg Conventions.loc_alloc_result)) ); intros. 
  subst. generalize (cpe_3 _ _ H1). intro. generalize (consteq_2 _ _ _ _ _ _ _ _ H). 
  intro. injection H2; intros; subst. split; trivial. exists Conventions.loc_alloc_result. 
  trivial. 
  generalize (mem_prop _ _ _ H1 H0); intro. 
  generalize (IHc _ _ _ _ _ _ H H2). trivial. 

  inversion H0. 
  inversion H0. 
  inversion H0. 
  inversion H0. 
Qed. 



Lemma one:
  forall FF ge sp parent c cons rs fr m rs' fr' m' k,
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' -> 
  constset.mem cons (compute_constraints_me c empty) = true ->
  constsat FF ge sp parent rs fr m cons.
Proof. 
  intros. 
  unfold constsat. 
  case_eq cons; intros. 
  case_eq r; intros. 
  split. intro. left. subst. injection H3; intros; subst. eapply test_aux_v; eauto. 
          intro. inversion H3. 
  split. intro. right. right. subst. injection H3; intros; subst. eapply test_aux_m; eauto.
          intro. inversion H3. 
  split. intro. right. left. subst. injection H3; intros; subst. eapply test_aux_fr; eauto. 
          intro. inversion H3. 
  split. intro. inversion H2. 
  intro. 
  generalize (coolie _ _ _ _ _ _ _ H1 H0); intro. destruct H3. destruct H3. 
  subst. injection H2; intros; subst. eapply test_aux_bi; eauto. 
  
  split. intro. inversion H2. 
          intro. inversion H2. 
Qed. 









Lemma two: 
  forall c1 c2,
  veriphi c1 c2 = true -> forall cons, 
  constset.mem cons (compute_constraints_me c2 empty) = true ->
  constset.mem cons (compute_constraints_me c1 empty) = true.
Proof. 
  intros. 
  unfold veriphi in H. 
  case_eq (constset.subset (compute_constraints_me c2 empty)
          (compute_constraints_me c1 empty)); intros. 
  (*generalize (nodupcc c2 empty). intro. 
  generalize (nodupcc c1 empty). intro. *)
  generalize (constset.subset_2 H1). intro. 
  generalize (constset.mem_2 H0). intro. 
  eapply constset.mem_1. 
  unfold constset.Subset in H2 ; intuition. 
  
  rewrite H1 in H. clear H1. 
  case_eq (constset.equal (compute_constraints_me c1 empty)
          (compute_constraints_me c2 empty)); intros. 
  (* generalize (nodupcc c2 empty). intro. 
  generalize (nodupcc c1 empty). intro. *)
  generalize (constset.mem_2 H0). intro. 
  generalize (constset.equal_2 H1). intro. 
  eapply constset.mem_1. 
  unfold constset.Equal in H3. 
  generalize (H3 cons). intro. destruct H4. generalize (H5 H2). 
  intuition. 

  rewrite H1 in H. inversion H. 
Qed. 
  
Lemma three: (* hypothetiaue les nevironnements ne sont pas les memes *)
  forall FF ge sp parent rs fr m c tc,
  veriphi c tc = true -> 
  (forall cons, constset.mem cons (compute_constraints_me c empty) = true ->
  constsat FF ge sp parent rs fr m cons) ->
  forall cons, constset.mem cons (compute_constraints_me tc empty) = true ->
  constsat FF ge sp parent rs fr m cons.
Proof. 
  intros. 
  generalize (two _ _ H); intro. 
  generalize (H2 cons H1); intro. 
  generalize (H0 cons H3); intro. 
  intuition. 
Qed.   

Lemma four_aux: (* utilise ? *)
  forall FF ge sp parent rs fr m cons w,
  constset.mem cons (compute_constraints_me nil empty) = true ->
  constsat FF ge sp parent rs fr m cons ->
  exists rs', exists fr', exists m',
  exec_nb_instrs FF ge sp parent (nil ++ w) rs fr m E0 w rs' fr' m'.
Proof. 
  intros. simpl in H. inversion H. 
Qed. 

Lemma sub4:
  forall x S S',
  constset.Subset S S' -> constset.Subset (constset.add x S) (constset.add x S').
Proof. 
  intros. 
  generalize (constprop.subset_add_2 x H). intro. 
  generalize (constset.add_1 S' ). intro. 
  generalize (H1 x x). intro. 
  assert (constset.E.eq x x). eapply constraintdt.eq_refl; eauto. 
  generalize (H2 H3). intro. 
  eapply constprop.subset_add_3; eauto.
Qed. 

Lemma constset_sub:
  forall l i tf,
constset.subset (compute_constraints_me l tf) 
           (compute_constraints_me (l ++ i :: nil) tf) = true.
Proof. 

  induction l; intros;  eapply constset.subset_1; eauto.
  
  destruct i; simpl; trivial; eapply constprop.subset_empty; eauto. 
  rewrite <- app_comm_cons. 
  generalize (IHl i (update tf a)). intro. 
  eapply constset.subset_2; eauto. 
  generalize (constset.subset_2 H). intro. clear H. 
  eapply constset.subset_1. 
  
  destruct a; simpl; try eapply sub4; eauto. 
  eapply constprop.subset_empty; eauto. 
  eapply constprop.subset_empty; eauto. 
  eapply constprop.subset_empty; eauto. 
  eapply constprop.subset_empty; eauto. 
  eapply constprop.subset_empty; eauto. 
Qed. 
  
Lemma constset_prop:
  forall l cons tf i,
  constset.mem cons (compute_constraints_me l tf) = true ->
  constset.mem cons (compute_constraints_me (l ++ i :: nil) tf) = true.
Proof. 
  intros. 
  generalize (constset_sub l i tf). intro. 
  generalize (constset.mem_2 H). intro. 
  generalize (constset.subset_2 H0). intro. 
  eapply constset.mem_1; eauto. 
Qed.   

Lemma back_trans_sat:
  forall FF l ge sp parent rs fr m i tf,  
  (forall cons, constset.mem cons (compute_constraints_me (l ++ i :: nil) tf) = true
  -> constsat FF ge sp parent rs fr m cons) ->
  (forall cons, constset.mem cons (compute_constraints_me l tf) = true ->
    constsat FF ge sp parent rs fr m cons). 
Proof. 
  intros. 
  generalize (constset_prop _ _ _ i H0). intro. 
  generalize (H cons H1). intro; trivial. 
Qed. 

Definition four (l : list instruction) : Prop :=
  lnbranchset l = true ->
  forall FF ge sp parent rs fr m w,
  (forall cons, constset.mem cons (compute_constraints_me l empty) = true ->
  constsat FF ge sp parent rs fr m cons) ->
  exists rs', exists fr', exists m',
  exec_nb_instrs FF ge sp parent (l ++ w) rs fr m E0 w rs' fr' m'.

Lemma four_test1: 
  four(nil). 
Proof. 
  unfold four. intros. exists rs; exists fr; exists m. simpl. 
  eapply exec_refl_bl; eauto. 
Qed. 

Lemma coc_step:
  forall l i tf,
  nbranchset i = true -> l <> nil ->
  compute_one_constraint (i :: l) tf = compute_one_constraint l (update tf i).
Proof. 
  intros. 
  destruct i; try inversion H; simpl; trivial; 
  case_eq l; intros; subst; simpl; simpl in *|-; try congruence. 
Qed. 

Lemma compute_comp:
  forall l i tf,
  nbranchset i = true ->
  lnbranchset l = true ->
  constset.mem (compute_one_constraint (l ++ i :: nil) tf) 
                   (compute_constraints_me (l ++ i :: nil) tf) = true.
Proof. 
  induction l; intros. 
  destruct i; simpl; try inversion H; trivial; try (
    eapply constset.mem_1; eauto;
    rewrite <- constprop.singleton_equal_add; 
    eapply constset.singleton_2; eauto). 
 
  generalize (IHl i (update tf a) H); intro. 
  assert (nbranchset a = true). destruct a; simpl; trivial. 
  assert (l ++ i :: nil <> nil). induction l; simpl ; congruence. 
  generalize (coc_step _ _ tf H2 H3). intro. 
  rewrite <- app_comm_cons. rewrite H4. 
  assert (lnbranchset l = true). destruct a; try inversion H2; simpl in H0; trivial. 
  generalize (H1 H5). intro. 
  eapply constset.mem_1. 
  eapply constprop.in_subset; eauto. eapply constset.mem_2; eauto. 
  destruct a; simpl; inversion H2; unfold constset.Subset; intros; 
  eapply constset.add_2; eauto. 
Qed. 

Lemma list_prop:
  forall (m : list instruction) n, 
  length m <> length n -> m <> n.
Proof. 
  induction m; intros. destruct n. simpl in H. congruence. 
                                congruence. 
   destruct n. congruence. 
   simpl in H. assert (length m <> length n). auto. 
   generalize (IHm _ H0). intro. congruence. 
Qed. 

Lemma list_prop2:
  forall (m : list instruction) n, 
  le (length n) (length (m ++ n)).
Proof. 
  induction m; intros. simpl. omega. 
  rewrite <- app_comm_cons. 
  simpl. generalize (IHm n); intro. omega. 
Qed.  
  
Lemma list_diff4:
  forall c (i : instruction) k,
  c ++ i :: k = k -> False.
Proof. 
  intros. 
  assert (length (i :: k) <> length k). simpl. omega. 
  assert (le (length (i :: k)) (length (c ++ i :: k))). eapply list_prop2; eauto. 
  assert (le (length k) (length (i :: k))). simpl. omega.
  assert (length (c ++ i :: k) <> length k). omega. 
  assert (length (c ++ i :: k) = length (k)). rewrite H. trivial. 
  congruence. 
Qed.   


Lemma inverted_exec_tree:
  forall FF ge sp parent c i k rs fr m rs' fr' m' rs'' fr'' m'',
  exec_nb_instrs FF ge sp parent (c ++ i :: nil ++ k) rs fr m E0 (i :: nil ++ k) rs' fr' m' ->
  exec_nb_instr FF ge sp parent (i :: nil ++ k) rs' fr' m' E0 k rs'' fr'' m'' ->
  exec_nb_instrs FF ge sp parent (c ++ i :: nil ++ k) rs fr m E0 k rs'' fr'' m''.
Proof. 
  induction c; intros. 
  simpl . simpl in H0. simpl in H. 
  
  generalize (no_move FF _ _ _ _ _ _ _  _ _ _ _ H). intuition subst.  
  eapply exec_trans_bl; eauto. eapply exec_refl_bl; eauto.  
  rewrite <- app_comm_cons in H. inversion H. elimtype False. 
  eapply list_diff4; eauto. 
    
  subst. 
  generalize (simple_move FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1). intro. 
  subst. 
  generalize (IHc _ _ _ _ _ _ _ _ _ _ _ H2 H0). intro. 
  rewrite <- app_comm_cons. eapply exec_trans_bl; eauto. 
Qed. 
  
Lemma lnb_prop:
  forall l i,
  lnbranchset (l ++ i :: nil) = true -> lnbranchset l = true /\ nbranchset i = true.
Proof. 
  induction l; intros. split ; trivial. 
  rewrite <- app_comm_cons in H. 
  assert (lnbranchset (l ++ i :: nil) = true). 
    destruct a; simpl in H; inversion H; trivial. 
  generalize (IHl i H0); intro. destruct H1. 
  split; trivial. 
  destruct a; simpl; trivial; simpl in H; try inversion H. 
Qed. 

Lemma four_test2_aux:
  forall l i, four(l) -> four (l ++ i :: nil).
Proof. 
  intros. 
  unfold four in H; unfold four. 
  intro EEE1. intros.   
  generalize (back_trans_sat FF _ _ _ _ _ _ _ _ _ H0). intros. 
  generalize (lnb_prop l i EEE1). intro. destruct H2.   
  assert (EEE2 : lnbranchset l = true). trivial. 
  assert (EEE3 : nbranchset i = true). trivial. 
  clear H2 H3. 
  
  generalize (H EEE2 FF _ _ _ _ _ _  (i :: w) H1). intro. 
  destruct H2 as [rs' [fr' [m' A]]]. 
  generalize (H0 (compute_one_constraint (l ++ i :: nil) empty)). intro. 
  assert (constset.mem (compute_one_constraint (l ++ i :: nil) empty)
       (compute_constraints_me (l ++ i :: nil) empty) = true ).
       eapply compute_comp; eauto. 
     

  rewrite H3 in H2. generalize (H2 (refl_equal true)). intro.  
  clear H2 H3. 
  generalize (eval_sym_end FF _ _ _ _ _ _ _ _ _ _ _ _ A). intro. destruct H2. 
  generalize (eval_sym_correct_aux_spec FF _ _ _ _ _ _ _ _ _ _ _ _ _ A H2). intro. 
  unfold constsat in H4. 


  destruct i. 

  (* Mgetstack *)

  generalize (H4 ((update x (Mgetstack i t m0)) #  (Reg m0)) (Reg m0) 
                           (x # Mem) Mem (x # Mem) Mem); intro. 
  destruct H5. 
  assert (compute_one_constraint (l ++ Mgetstack i t m0 :: nil) empty =
     Const ((update x (Mgetstack i t m0)) #  (Reg m0)) (Reg m0)). 
     generalize (abstr_comp2 _ (Mgetstack i t m0) _ _ H2). trivial. 
  generalize (H5 H7); intro. 
  destruct H8. destruct H8. 
  (* cas ok *)  exists (Regmap.set m0 x0 rs'). exists fr'. exists m'. 
                    rewrite app_ass. rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    inversion H9; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto. 
                    eapply Sem; eauto. 
                    eapply Sregset; eauto. intro. 
                    case_eq (mreg_eq x1 m0). 
                      intros.  rewrite e. rewrite map3. 
                      trivial. 
                      intros. rewrite map5; trivial. simpl. 
                      rewrite genmap1; try congruence. 
                      generalize (H12 x1). intro. trivial. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  destruct H8. destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 
  destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 
  
  (* Msetstack *)

  generalize (H4 ((update x (Msetstack m0 i t)) # (Stack)) (Stack) 
                           (x # Mem) Mem (x # Mem) Mem); intro. 
  destruct H5. 
  assert (compute_one_constraint (l ++ Msetstack m0 i t :: nil) empty =
     Const ((update x (Msetstack m0 i t)) # (Stack)) (Stack)). 
     generalize (abstr_comp2 _ (Msetstack m0 i t) _ _ H2). trivial.  
  generalize (H5 H7); intro. 
  destruct H8; destruct H8; simpl in H8; rewrite map2 in H8; inversion H8. 
  (* cas ok *) exists rs'. exists x0. exists m'. 
                    rewrite app_ass; rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto.  
                    eapply Sem; eauto. 
                    eapply Sregset; eauto. 
  simpl. intro. rewrite Rmap.gso. trivial. inversion H10; subst. 
  generalize (H13 x1); intro. trivial. congruence. 
                     simpl. rewrite Rmap.gss. trivial. 
    simpl. rewrite Rmap.gso. trivial. congruence. 


  destruct H8; simpl in H8. unfold Rmap.get in H8. inversion H8. 

  (* Mgetparam *)

  generalize (H4 ((update x (Mgetparam i t m0)) # (Reg m0)) (Reg m0) 
                           (x # Mem) Mem (x # Mem) Mem); intro. 
  destruct H5. 
  assert (compute_one_constraint (l ++ Mgetparam i t m0 :: nil) empty =
     Const ((update x (Mgetparam i t m0)) #  (Reg m0)) (Reg m0)). 
     generalize (abstr_comp2 _ (Mgetparam i t m0) _ _ H2). trivial. 
  generalize (H5 H7); intro. 
  destruct H8. destruct H8. 
  (* cas ok *) exists (Regmap.set m0 x0 rs'). exists fr'. exists m'. 
                    rewrite app_ass. rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    inversion H9; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto. 
                    eapply Sem; eauto. 
                    eapply Sregset; eauto. intro. 
                    case_eq (mreg_eq x1 m0). 
                      intros.  rewrite e. rewrite map3. 
                      trivial. 
                      intros. rewrite map5; trivial. simpl. 
                      rewrite genmap1; try congruence. 
                      generalize (H12 x1). intro. trivial. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  destruct H8. destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 
  destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 

  (* Mop *)

  generalize (H4 ((update x (Mop o l0 m0)) # (Reg m0)) (Reg m0) 
                           (x # Mem) Mem (x # Mem) Mem); intro. 
  destruct H5. 
  assert (compute_one_constraint (l ++ Mop o l0 m0 :: nil) empty =
     Const ((update x (Mop o l0 m0)) #  (Reg m0)) (Reg m0)). 
     generalize (abstr_comp2 _ (Mop o l0 m0) _ _ H2). trivial. 
  generalize (H5 H7); intro. 
  destruct H8. destruct H8. 
  (* cas ok *) exists (Regmap.set m0 x0 rs'). exists fr'. exists m'. 
                    rewrite app_ass. rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    inversion H9; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto. 
                    eapply Sem; eauto. 
                    eapply Sregset; eauto. intro. 
                    case_eq (mreg_eq x1 m0). 
                      intros.  rewrite e. rewrite map3. 
                      trivial. 
                      intros. rewrite map5; trivial. simpl. 
                      rewrite genmap1; try congruence. 
                      generalize (H12 x1). intro. trivial. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  destruct H8. destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 
  destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 

  (* Mload *)

  generalize (H4 ((update x (Mload m0 a l0 m1)) # (Reg m1)) (Reg m1) 
                           (x # Mem) Mem (x # Mem) Mem); intro. 
  destruct H5. 
  assert (compute_one_constraint (l ++ Mload m0 a l0 m1 :: nil) empty =
     Const ((update x (Mload m0 a l0 m1)) #  (Reg m1)) (Reg m1)). 
     generalize (abstr_comp2 _ (Mload m0 a l0 m1) _ _ H2). trivial. 
  generalize (H5 H7); intro. 
  destruct H8. destruct H8. 
  (* cas ok *) exists (Regmap.set m1 x0 rs'). exists fr'. exists m'. 
                    rewrite app_ass. rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    inversion H9; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto. 
                    eapply Sem; eauto. 
                    eapply Sregset; eauto. intro. 
                    case_eq (mreg_eq x1 m1). 
                      intros.  rewrite e. rewrite map3. 
                      trivial. 
                      intros. rewrite map5; trivial. simpl. 
                      rewrite genmap1; try congruence. 
                      generalize (H12 x1). intro. trivial. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  simpl. rewrite Rmap.gso. trivial. congruence. 
  destruct H8. destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 
  destruct H8. simpl in H8. rewrite map2 in H8. inversion H8. 

  (* Mstore *)

  generalize (H4 ((update x (Mstore m0 a l0 m1)) # (Mem)) (Mem) 
                           (x # Mem) Mem (x # Mem) Mem); intro. 
  destruct H5. 
  assert (compute_one_constraint (l ++ Mstore m0 a l0 m1 :: nil) empty =
     Const ((update x (Mstore m0 a l0 m1)) # (Mem)) (Mem)). 
     generalize (abstr_comp2 _ (Mstore m0 a l0 m1) _ _ H2). trivial.  
  generalize (H5 H7); intro. 
  destruct H8; destruct H8; simpl in H8; rewrite map2 in H8; inversion H8. 
  destruct H8; simpl in H8.  inversion H8. 
  (* cas ok *) exists rs'. exists fr'. exists x0. 
                    rewrite app_ass; rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto.  
                    eapply Sem; eauto.   
                    eapply Sregset; eauto. 
                    intro. simpl. rewrite Rmap.gso.  
                    inversion H10; subst. generalize (H13 x1). trivial. 
                    congruence. 
                      simpl. rewrite Rmap.gso. trivial. congruence. 
                   simpl. rewrite Rmap.gss. trivial. 

  inversion EEE3.   

  (* Malloc *)

  generalize (H4 (x # Mem) (Mem) ((update x (Malloc)) #  Mem) (Mem) ((update x (Malloc)) #  (Reg Conventions.loc_alloc_result)) (Reg Conventions.loc_alloc_result)).
  intro. 
  assert (compute_one_constraint (l ++ Malloc :: nil) empty =
     BiConst ((update x (Malloc)) #  (Mem)) Mem ((update x (Malloc)) #  (Reg Conventions.loc_alloc_result)) (Reg Conventions.loc_alloc_result)). 
    generalize (abstr_comp2 _ (Malloc) _ _ H2). trivial.  
  destruct H5. 
  generalize (H7 H6). intro. 
  destruct H8. destruct H8. destruct H9. 
  exists (Regmap.set Conventions.loc_alloc_result x0 rs'). 
  exists fr'. exists x1. 
           rewrite app_ass; rewrite <- app_comm_cons. 
                    inversion H3; subst. 
                    eapply inverted_exec_tree; eauto. 
                    eapply sem_to_exec_aux; eauto.  
                    eapply Sem; eauto. 
                    eapply Sregset; eauto. 
                    intro. 
                    case_eq (mreg_eq x2 (Conventions.loc_alloc_result)). 
                      intros.  rewrite e. rewrite map3. 
                      trivial. 
                      intros. rewrite map5; trivial. simpl. 
                      rewrite genmap1; try congruence. 
                      inversion H10; subst. 
                      generalize (H14 x2). intro. 
                      rewrite Rmap.gso. trivial. congruence. 
  simpl. rewrite Rmap.gso. rewrite Rmap.gso. trivial. 
  congruence. congruence. 
                                    
  (* autre *)                  

  inversion EEE3. 
  inversion EEE3. 
  inversion EEE3. 
  inversion EEE3. 

Qed. 
 
Lemma four_test2:
  forall i l, four(l) -> four (l ++ i :: nil).
Proof. 
  intros. eapply four_test2_aux. trivial. 
Qed. 

Theorem constsatwd_v1:
  forall l, four l. 
Proof. 
  intros. 
  apply (rev_ind four four_test1 four_test2). 
Qed. 

Lemma fonct_env:
  forall FF ge tge sp parent rs fr m f, 
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  forall v fv mv,
  (sem_value FF ge sp parent rs fr m f v -> sem_value FF tge sp parent rs fr m f v) /\
  (sem_frame FF ge sp parent rs fr m f fv -> sem_frame FF tge sp parent rs fr m f fv) /\
  (sem_mem FF ge sp parent rs fr m f mv -> sem_mem FF tge sp parent rs fr m f mv).
Proof. 
 
  intros FF ge tge sp parent rs fr m f ENV1 ENV2. 
  
   apply expression_ind2 with
    
    (P := fun (e1: expression) => 
    forall v fv mv,
    (sem_value FF ge sp parent rs fr m e1 v -> sem_value FF tge sp parent rs fr m e1 v) /\ 
    (sem_frame FF ge sp parent rs fr m e1 fv -> sem_frame FF tge sp parent rs fr m e1 fv) /\ 
    (sem_mem FF ge sp parent rs fr m e1 mv -> sem_mem FF tge sp parent rs fr m e1 mv))
    
    (P0 := fun (e1: expression_list) => 
    forall lv, sem_val_list FF ge sp parent rs fr m e1 lv -> sem_val_list FF tge sp parent rs fr m e1 lv 
    ); intros; intuition; try (inversion H; eauto with *); try (inversion H0); try (inversion H1); 
    try (inversion H2).   

    eapply Sop; eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 

   eapply Sload; eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 
   generalize (H0 sp fr m'). intros. intuition. 
   generalize (H lv H14). intuition. rewrite <- ENV2. intuition. 

   eapply Sstore; eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 
   generalize (H sp fr m'). intros. intuition. 
   generalize (H1 v0 fr m). intros. intuition. 
   generalize (H0 lv H17). intuition. rewrite <- ENV2. intuition. 

  eapply Sgetstack;eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 
    generalize (H sp fr' m). intros. intuition. 
  
  eapply Ssetstack; eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 
  generalize (H sp fr' m). intros. intuition. 
  generalize (H0 v0 fr m). intros. intuition. 

  eapply Smalloc1; eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 
  generalize (H (Vint sz) fr m). intros. intuition. 
  generalize (H0 sp fr m1). intros. intuition. 

  eapply Smalloc2; eauto; try (rewrite <- ENV1; trivial); try (rewrite <- ENV1; trivial). 
  generalize (H (Vint sz) fr m). intros. intuition. 
  generalize (H0 sp fr m1). intros. intuition. 

  eapply Scons; eauto. 
    generalize (H v fr m). intro. intuition. 

Qed.


Lemma constsat_env_ind:
  forall FF ge tge sp parent rs fr m cons,
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->  
  constsat FF ge sp parent rs fr m cons ->
  constsat FF tge sp parent rs fr m cons.
Proof. 
  intros. 
  unfold constsat in H1. unfold constsat. intros. 
  generalize (H1 e r e1 r1 e2 r2); intros. destruct H2. 
  split; intros; try generalize (H2 H4); try (generalize (H3 H4)); intro; clear H1 H2 H3.  
  destruct H5. left.   
  2:destruct H1; [right;left|right;right]. 
  
  destruct H1. exists x. 
  generalize (fonct_env FF _ _ sp parent rs fr m e H H0 x fr m); intro. 
  destruct H2 as [A [B C]]. generalize (A H1); intuition. 
  
  destruct H1. exists x. 
  generalize (fonct_env FF _ _ sp parent rs fr m e H H0 sp x m); intro. 
  destruct H2 as [A [B C]]. generalize (B H1); intuition. 
 
  destruct H1. exists x. 
  generalize (fonct_env FF _ _ sp parent rs fr m e H H0 sp fr x); intro. 
  destruct H2 as [A [B C]]. generalize (C H1); intuition. 

  destruct H5. split. 
  destruct H1. exists x. 
  generalize (fonct_env FF _ _ sp parent rs fr m e2 H H0 x fr m); intro. 
  destruct H3 as [A [B C]]. generalize (A H1); intuition. 

  destruct H2. exists x. 
  generalize (fonct_env FF _ _ sp parent rs fr m e1 H H0 sp fr x); intro. 
  destruct H3 as [A [B C]]. generalize (C H2); intuition. 

Qed. 

Theorem veriphi_existenz:
  forall FF ge tge sp parent c tc rs fr m k tk rs' fr' m', 
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  veriphi c tc = true -> 
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' ->
  lnbranchset tc = true ->
  exists rs'', exists fr'', exists m'',
  exec_nb_instrs FF tge sp parent (tc ++ tk) rs fr m E0 tk rs'' fr'' m''.
Proof. 
  intros. 
  eapply (constsatwd_v1 tc); eauto. intros. 
  eapply three; eauto. intros. 
  eapply constsat_env_ind; eauto. 
  eapply one; eauto. 
Qed. 

Definition nbic (c tc : code) : bool :=
  andb (compare c tc) (veriphi c tc). 

Lemma aaaprop:
  forall c tf x,
  abstract_sequence tf c = Some x -> lnbranchset c = true.
Proof. 
  induction c; intros. trivial. 
  assert (nbranchset a = true). destruct a; try inversion H; trivial. 
  assert (abstract_sequence tf (a :: c) = abstract_sequence (update tf a) c).
    destruct a; try inversion H0; trivial. 
    rewrite H1 in H. 
    generalize (IHc (update tf a) x H); intro; trivial. 
    clear IHc H H1. 
    simpl. destruct a; try inversion H0; trivial. 
Qed. 

Lemma comp_imp_nb:
  forall c tc, 
  compare c tc = true -> lnbranchset tc = true.
Proof. 
  intros. unfold compare in H. 
  case_eq (abstract_sequence empty tc); intros. 
  eapply aaaprop; eauto. 
  rewrite H0 in H. case_eq (abstract_sequence empty c); intros; rewrite H1 in H; inversion H. 
Qed. 

Lemma comp_imp_nb2:
  forall c tc, 
  compare c tc = true -> lnbranchset c = true.
Proof. 
  intros. unfold compare in H. 
  case_eq (abstract_sequence empty c); intros. 
  eapply aaaprop; eauto. 
  rewrite H0 in H. inversion H. 
Qed. 

Lemma comp_imp_nb3:
  forall c tc,
  compare c tc = true ->
  exists f,
  abstract_sequence empty c = Some f. 
Proof. 
  intros. unfold compare in H. 
  case_eq (abstract_sequence empty c); intros.
  rewrite H0 in H. exists f; trivial.
  rewrite H0 in H. inversion H. 
Qed.   

Lemma comp_imp_nb4:
  forall c tc,
  compare c tc = true ->
  exists f,
  abstract_sequence empty tc = Some f. 
Proof. 
  intros. unfold compare in H. 
  case_eq (abstract_sequence empty c); intros.
  rewrite H0 in H.
  case_eq (abstract_sequence empty tc); intros.
  rewrite H1 in H.  exists f0. trivial. 
  rewrite H1 in H. inversion H. 
  rewrite H0 in H. inversion H. 
Qed.   

Theorem nbic_imply_equivalence:
  forall FF ge tge sp parent c tc rs fr m k tk rs' fr' m',  
  nbic c tc = true ->
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) -> 
  exec_nb_instrs FF ge sp parent (c ++ k) rs fr m E0 k rs' fr' m' ->
  exec_nb_instrs FF tge sp parent (tc ++ tk) rs fr m E0 tk rs' fr' m'.
Proof. 
  intros until 1. intro ENV1. intro ENV2. intro. 
  unfold nbic in H. 
  generalize (essai _ _ H). intro. destruct H1. 
  generalize (comp_imp_nb _ _ H1). intro. 
  generalize (veriphi_existenz FF _ _ _  _ _ _ _ _ _ _ tk _ _  _   ENV1 ENV2 H2 H0 H3). intro. clear H3. 
  destruct H4 as [rs'' [fr'' [m'' HYP]]]. 
  
  generalize (compare_fundamental_property FF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _   H1 ENV1 ENV2 H0 HYP). 
  intuition subst. trivial. 
Qed. 

(** essai d un nouveau lemme plus simple : plus a jour*)
(*

 
Lemma simple_injection:
  forall ge f sp parent a c2 rs fr m rs2 fr2 m2,
  exec_nb_instr ge f sp parent (a :: c2) rs fr m E0 c2 rs2 fr2 m2 ->
  sem ge sp parent rs fr m (update empty a) rs2 fr2 m2.
Proof.  
  intros. 
  assert (nbranchset a = true). 
    inversion H; trivial.
  assert (exec_instr ge f sp parent (a :: c2) rs fr m E0 c2 rs2 fr2 m2). 
    destruct a; inversion H; try inversion H0; subst.
  eapply Machabstr.exec_Mgetstack; eauto.
  eapply Machabstr.exec_Msetstack; eauto.
  eapply Machabstr.exec_Mgetparam; eauto. 
  eapply Machabstr.exec_Mop; eauto. 
  eapply Machabstr.exec_Mload; eauto. 
  eapply Machabstr.exec_Mstore; eauto. 
  eapply Machabstr.exec_Malloc; eauto. 
 
  clear H. 
  eapply abstract_seq_correct_aux; eauto. 
  eapply empty_no_move; eauto. 
Qed. 

Lemma aprouver:
  forall ge (f : function) sp parent c i rs fr m,
  lnbranchset (i :: c) = true -> (
  (forall e, constset.mem e (compute_constraints_me (i :: c) empty) = true ->
             constsat ge sp parent rs fr m e) <->
  exists rsi, exists fri, exists mi, 
  sem ge sp parent rs fr m (update empty i) rsi fri mi /\
  (forall e, constset.mem e (compute_constraints_me c empty) = true ->
             constsat ge sp parent rsi fri mi e)).
Proof. 
  intros. 
  split; intros.

  (* => *)   
  generalize  constsatwd_v1. intro. unfold four in H0. 
  generalize (H1 (i :: c)); intro. 
  assert (lnbranchset (i :: c) = true). trivial. 
  generalize (H2 H3); intro.
  generalize (H4 _ f _ _ _ _ _ nil H0). intro. 
  destruct H5 as [rs' [fr' [m' HYP]]]. rewrite <- app_comm_cons in HYP. 
  inversion HYP; subst.
  generalize (simple_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5). intro; subst.  
  exists rs2; exists fr2; exists m2. split.
  eapply simple_injection; eauto.
  intros.  eapply one; eauto.

  (* <= *)
  destruct H0 as [rsi [fri [mi [E F]]]]. 
  generalize constsatwd_v1. intro. unfold four in H0. 
  generalize (H0 c); intro. 
  assert (lnbranchset c = true). 
    inversion H. destruct i; try inversion H4; trivial.  
  generalize (H2 H3); intro. 
  generalize (H4 _ f _ _ _ _ _ nil F); intro. 
  destruct H5 as [rs' [fr' [m' HYP]]]. 
  eapply one; eauto. rewrite <- app_comm_cons. 
  eapply exec_trans_bl; eauto.
  eapply sem_to_exec; eauto. destruct i; trivial. 
Qed. 
 
Lemma corr1:
   forall ge (f : function) sp parent c i rs fr m,
   lnbranchset (i :: c) = true ->
  (forall e, constset.mem e (compute_constraints_me (i :: c) empty) = true ->
             constsat ge sp parent rs fr m e) ->
  exists rsi, exists fri, exists mi, 
  sem ge sp parent rs fr m (update empty i) rsi fri mi /\
  (forall e, constset.mem e (compute_constraints_me c empty) = true ->
             constsat ge sp parent rsi fri mi e).
Proof. 
  intros. generalize (aprouver ge f sp parent c i rs fr m H).  
  intro. destruct H1. 
  generalize (H1 H0). intuition.
Qed. 

Lemma corr2: 
   forall ge (f : function) sp parent c i rs fr m,
   lnbranchset (i :: c) = true ->
  (exists rsi, exists fri, exists mi, 
  sem ge sp parent rs fr m (update empty i) rsi fri mi /\
  (forall e, constset.mem e (compute_constraints_me c empty) = true ->
             constsat ge sp parent rsi fri mi e)) ->
  (forall e, constset.mem e (compute_constraints_me (i :: c) empty) = true ->
             constsat ge sp parent rs fr m e). 
Proof. 
  intros. generalize (aprouver ge f sp parent c i rs fr m H). intro. 
  destruct H2. generalize (H3 H0). intuition.   
Qed. 

Lemma value_inversion:
  forall ge sp parent rs fr m x (rs' : regset),
  sem_value ge sp parent rs fr m empty # (Reg x) (rs' x) ->
  rs x = rs' x. 
Proof. 
(* la preuve marche tout a fait mais c ets tellement lent que ca me gene 
  intros.
  destruct x; inversion H; subst; trivial.  
Qed. 
*)


Lemma alpha_comp:
  forall ge sp parent sigma i rs0 fr0 m0 rs fr m rs' fr' m',
  sem ge sp parent rs0 fr0 m0 sigma rs fr m ->
  sem ge sp parent rs fr m (update empty i) rs' fr' m' ->
  sem ge sp parent rs0 fr0 m0 (update sigma i) rs' fr' m'.
Proof. 
  intros. 
  destruct i.

  (* getstack *)
 
  simpl in H0. simpl. 
  eapply Sem; eauto.

  eapply Sregset; eauto. intro.  
  generalize (mreg_eq m1 x); intro. destruct H1. 

  subst. rewrite Rmap.gss. inversion H0; subst. inversion H1; subst. 
  generalize (H4 x); intro. rewrite Rmap.gss in H5. 
  inversion H5; subst. eapply Sgetstack; eauto. 
  inversion H16; subst. inversion H; subst. trivial. 

  rewrite Rmap.gso; try congruence. inversion H0; subst. 
  inversion H1; subst. 
  inversion H; subst. inversion H5; subst.  
  generalize (H4 x); intro. generalize (H8 x); intro. 
  rewrite Rmap.gso in H9; try congruence.
  assert (rs x = rs' x).  eapply value_inversion; eauto. 
  rewrite <- H11 in H9. rewrite <- H11. trivial. 

  rewrite Rmap.gso; try congruence. inversion H0; subst. 
  rewrite Rmap.gso in H2; try congruence. 
  inversion H2; subst. inversion H; subst. trivial.

  rewrite Rmap.gso; try congruence. inversion H0; subst. 
  rewrite Rmap.gso in H3; try congruence. 
  inversion H3; subst. inversion H; subst. trivial.

  apply 
  apply 
  apply 
  apply 
  apply 

  (* call *) 
  simpl in H0. simpl.
  inversion H0; subst. inversion H1; subst.
  inversion H2; subst. inversion H3; subst. 
  eapply Sem; eauto. 
  eapply Sregset; eauto.  intro. 
  generalize (H4 x); intro. 
  assert (rs x = rs' x). eapply value_inversion; eauto. 
  inversion H; subst. inversion H7; subst. generalize (H10 x); intro. 
  rewrite H6 in H11. trivial. 
  
  inversion H; subst; trivial. 
  inversion H; subst; trivial. 
 
  apply 
  apply 
  apply 
  apply 
  apply 
    
Qed.    



Lemma allInOne:
  forall ge f sp parent c w sigma fo rs0 fr0 m0 rs fr m,
  lnbranchset c = true ->
  abstract_sequence sigma c = Some fo ->
  sem ge sp parent rs0 fr0 m0 sigma rs fr m ->
  forall rs' fr' m',
  exec_nb_instrs ge f sp parent (c ++ w) rs fr m E0 w rs' fr' m' 
  <->  
  sem ge sp parent rs0 fr0 m0 fo rs' fr' m' /\
  (forall e, constset.mem e (compute_constraints_me c empty) = true ->
               constsat ge sp parent rs fr m e).
Proof. 
  induction c; intros. 

  (* c = nil *)
  split; intros.
 
    simpl in H0. injection H0; intros; subst. clear H0. 
    simpl in H2. 
    generalize (no_move _ _ _ _ _ _ _ _ _ _ _ _ H2); intro. 
    destruct H0 as [E [F G]]. subst. 
    split; trivial.   
    simpl; intros. inversion H0. 
  
    simpl in H0. injection H0; intros; subst. clear H0. 
    simpl. destruct H2. 
    generalize (s_fonct_sem _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1); intro. 
    destruct H3. destruct H4. subst.
    eapply exec_refl_bl; eauto. 
  
  (* c = i :: l *)
  assert (abstract_sequence sigma (a :: c) = abstract_sequence (update sigma a) c). 
    destruct a; try inversion H; simpl in H0; trivial. 
  rewrite H2 in H0. 
  assert (lnbranchset c = true).
    destruct a; try inversion H; simpl in H; trivial. 
    
  split; intros. 
  
  rewrite <- app_comm_cons in H4. 
  inversion H4. 
  elimtype False. eapply list_diff; eauto.
  subst. 
  assert (sem ge sp parent rs fr m (update empty a) rs2 fr2 m2).
     generalize (simple_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5). intro; subst.  
  eapply simple_injection; eauto.   
  assert (sem ge sp parent rs0 fr0 m0 (update sigma a) rs2 fr2 m2). 
    eapply alpha_comp; eauto. 
  generalize (IHc w _ _ _ _ _ _ _ _ H3 H0 H8). intro MAIN.    
  generalize (MAIN rs' fr' m'). intro. 
  destruct H9.   
  assert (exec_nb_instrs ge f sp parent (c ++ w) rs2 fr2 m2 E0 w rs' fr' m'). 
    generalize (simple_move _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5). intro; subst. 
    trivial. 
  generalize (H9 H11); intro. 
  destruct H12. split; trivial. 
  intros. eapply corr2; eauto. (* la prop fondamentale *)

  destruct H4.
  generalize (corr1 _ f _ _ _ _ _ _ _ H H5). intro. 
  destruct H6 as [rsi [fri [mi [E F]]]]. 
  assert (sem ge sp parent rs0 fr0 m0 (update sigma a) rsi fri mi). 
    eapply alpha_comp; eauto. 
  generalize (IHc w _ _ _ _ _ _ _ _ H3 H0 H6); intro.
  generalize (H7 rs' fr' m'); intro. 
  destruct H8. 
  assert (sem ge sp parent rs0 fr0 m0 fo rs' fr' m' /\
     (forall e : constset.elt,
      constset.mem e (compute_constraints_me c empty) = true ->
      constsat ge sp parent rsi fri mi e)). 
    split; trivial. 
  generalize (H9 H10); intro. 
  rewrite <- app_comm_cons.
  eapply exec_trans_bl; eauto.
  eapply sem_to_exec; eauto. 
  destruct a; trivial; try inversion H. 
Qed.   

Theorem doubleEq:
  forall ge f sp parent c w fo rs fr m rs' fr' m',
  lnbranchset c = true -> 
  abstract_sequence empty c = Some fo -> (
  exec_nb_instrs ge f sp parent (c ++ w) rs fr m E0 w rs' fr' m' 
  <->  
  sem ge sp parent rs fr m fo rs' fr' m' /\
  (forall e, constset.mem e (compute_constraints_me c empty) = true ->
               constsat ge sp parent rs fr m e)).
Proof. 
  intros. 
  eapply allInOne; eauto.
  eapply empty_no_move; eauto. 
Qed.   

Theorem ohMy:
  forall ge tge f tf sp parent c tc rs fr m k tk rs' fr' m',  
  nbic c tc = true ->
  exec_nb_instrs ge f sp parent (c ++ k) rs fr m E0 k rs' fr' m' ->
  exec_nb_instrs tge tf sp parent (tc ++ tk) rs fr m E0 tk rs' fr' m'.
Proof. 
  intros.
  unfold nbic in H. 
  generalize (essai _ _ H). intro. destruct H1. 
  generalize (comp_imp_nb _ _ H1). intro.
  generalize (comp_imp_nb2 _ _ H1). intro.
  generalize (comp_imp_nb3 _ _ H1). intro.
  destruct H5. 
  generalize (doubleEq ge f sp parent _ k _ rs fr m rs' fr' m' H4 H5). intro. 
  destruct H6. clear H7. 
  generalize (H6 H0); intro. clear H6. destruct H7.

    generalize (comp_imp_nb4 _ _ H1). intro.
    destruct H8. 
    unfold compare in H1. rewrite H5 in H1. rewrite H8 in H1. 
    assert (x = x0). (* vrai mais chiant, a voire *)
      apply 
    subst. 
    generalize (three _ _ _ _ _ _ _ _ H2 H7). intro. 
  generalize (doubleEq tge tf sp parent _ tk _ rs fr m rs' fr' m' H3 H8). intro.     
  destruct H10. 
  assert (sem tge sp parent rs fr m x0 rs' fr' m' /\
      (forall e : constset.elt,
       constset.mem e (compute_constraints_me tc empty) = true ->
       constsat tge sp parent rs fr m e)). 
  apply  (* ok, c est juste l apparition de lenv *)
  generalize (H11 H12). intro; trivial.  
Qed. 

(** essai sur la composition *)
(*
Notation "a ;;; b" := (abstract_sequence a b) (at level 1). 

Lemma decomposeSemExtended:
  forall ge fu sp parent b a rs fr m rsi fri mi rs' fr' m' f  w,
  sem ge sp parent rs fr m a rsi fri mi ->
  a ;;; b = Some f -> 
  sem ge sp parent rs fr m f rs' fr' m' ->
  exec_nb_instrs ge fu sp parent (b ++ w) rsi fri mi E0 w rs' fr' m'.
Proof. 
  induction b; intros.
 
  simpl in H0. injection H0; intros; subst. 
  assert (rsi = rs' /\ fri = fr' /\ mi = m'). eapply font_sem; eauto. 
  destruct H2. destruct H3. subst. simpl. eapply exec_refl_bl. 

  destruct a. 
  
  (* getstack *)
  simpl in *|-.
  assert (exists rsk, exists frk, exists mk, 
             sem ge sp parent rs fr m  a0 # (Reg m0) <- (Egetstack i t a0 # Stack) rsk frk mk). 
             apply  (* gros morceau *)
  destruct H2 as [rsk [frk [mk A]]]. 
  generalize (IHb _ _ _ _ _ _ _ _ _ _ _ w A H0 H1). intro.
  rewrite <- app_comm_cons. 
  eapply exec_trans_bl; eauto. 
  inversion A; subst. inversion H3; subst. generalize (H6 m0); intro. 
  rewrite Rmap.gss in H7 .inversion H7; subst. 
  eapply exec_Mgetstack; eauto. 
*)  
 
*)




