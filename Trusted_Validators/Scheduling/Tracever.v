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
Require Import ExtValcommon. 

Definition compare t1 t2 := validate_trees (t1, t2) empty empty constset.empty constset.empty. 

(** definition of the tranformation over cfgs *)

Definition verify (l : label) (c tc : cfg_body) : bool :=
  match c!l, tc!l with
  | Some Mreturn, Some Mreturn => true
  | Some (Mtree t), Some (Mtree ttt) => compare t ttt
  | Some (Mcall s1 r1 l1), Some (Mcall s2 r2 l2) => 
      if signature_eq s1 s2 
      then if mreg_plus_ident_eq r1 r2
      then if peq l1 l2 then true
      else false
      else false
      else false
  | _,_ => false
  end. 

Definition check_cfg (c tc : cfg) : bool :=
   let keys := PTree.xkeys c.(cfg_code) xH in
   let b := if peq c.(cfg_head) tc.(cfg_head) then true else false in
   let b' := List.fold_left (fun acc => fun k => (verify k c.(cfg_code) tc.(cfg_code)) && acc ) keys true in 
   b && b'.  

Lemma same_h:
  forall c1 c2,
  check_cfg c1 c2 = true -> c1.(cfg_head) = c2.(cfg_head).
Proof. 
  intros. 
  unfold check_cfg in H. 
  generalize (essai _ _ H); intro. destruct H0. 
  case_eq (peq (cfg_head c1) (cfg_head c2)); intros. 
    trivial. 
    rewrite H2 in H. simpl in H. inversion H. 
Qed. 
  
Lemma list_prop:
  forall l k (a : positive),
  In k (a :: l) -> a <> k -> In k l.
Proof. 
  induction l; intros.
  inversion H. congruence. trivial. 
  unfold In in H. destruct H. congruence.
  destruct H. subst.  unfold In; left; trivial.
  assert (In k l = (fix In (a : positive) (l : list positive) {struct l} : Prop :=
       match l with
       | nil => False
       | b :: m => b = a \/ In a m
       end) k l). 
       unfold In. trivial. 
  rewrite <- H1 in H. eapply in_cons; eauto. 
Qed.  

Lemma fold_false:
  forall l f,
  fold_left
      (fun (acc : bool) (k : label) =>
       f k && acc) l false = true -> False. 
Proof. 
  induction l; intros. 
  simpl in H. inversion H. 
  simpl in H. 
  assert (f a && false = false).  
    case_eq (f a); intros. 
    simpl. trivial. 
    simpl. trivial. 
  rewrite H0 in H. 
  eapply IHl; eauto. 
Qed.   
  
Lemma fold_prop:
  forall l c1 c2 k,
  List.fold_left (fun acc => fun k => (verify k c1.(cfg_code) c2.(cfg_code)) && acc ) l true = true ->
  In k l -> verify k c1.(cfg_code) c2.(cfg_code) = true.
Proof. 
  induction l; intros. 
    inversion H0. 
    case_eq (peq k a); intros.
    rewrite e. simpl in H. 
      case_eq (verify a (cfg_code c1) (cfg_code c2)); intros. 
      trivial. 
      rewrite H2 in H. simpl in H.  
        generalize (fold_false l (fun k => verify k (cfg_code c1) (cfg_code c2)) H); intro. 
        intuition. 
      simpl in H. 
      assert (In k l).
        eapply list_prop; eauto. 
      eapply IHl; eauto. 
      case_eq (verify a (cfg_code c1) (cfg_code c2)); intros. 
      rewrite H3 in H. simpl in H. auto. 
      rewrite H3 in H. simpl in H. elimtype False. 
      generalize (fold_false l (fun k => verify k (cfg_code c1) (cfg_code c2)) H); intro. 
      intuition. 
Qed.     
    
Lemma same_l:
  forall c1 c2,
  check_cfg c1 c2 = true -> 
  forall l, In l (PTree.xkeys (cfg_code c1) xH) ->verify l (cfg_code c1) (cfg_code c2) = true.
Proof. 
  intros. 
  unfold check_cfg in H. 
  generalize (essai _ _ H); intro. destruct H1. 
  eapply fold_prop; eauto. 
Qed. 

Lemma isIn:
  forall c1 l i,
  (cfg_code c1) ! l = Some i ->  
  In l (PTree.xkeys (cfg_code c1) xH).
Proof. 
  intros.
  generalize (PTree.elements_correct _ _ H); intro. 
  unfold PTree.xkeys. unfold PTree.elements in H0. 
  generalize (in_map (@fst positive instruction) (PTree.xelements (cfg_code c1) 1) (l,i) H0); intro.
  simpl in H1. trivial. 
Qed. 

Lemma checkandsome:
  forall c1 c2 l i,
  check_cfg c1 c2 = true ->
  (cfg_code c1) ! l = Some i ->  
  verify l (cfg_code c1) (cfg_code c2) = true.
Proof. 
  intros.
  generalize (isIn _ _ _ H0); intro. 
  eapply same_l; eauto. 
Qed.

Lemma verifcall:
  forall c1 c2 l s1 r1 l1, 
  (cfg_code c1) ! l = Some (Mcall s1 r1 l1) ->  
  verify l (cfg_code c1) (cfg_code c2) = true ->
  (cfg_code c2) ! l = Some (Mcall s1 r1 l1).
Proof. 
  intros. 
  unfold verify in H0. 
  rewrite H in H0. 
  case_eq ((cfg_code c2) ! l); intros. 
    rewrite H1 in H0.
    case_eq i; intros; subst.
    inversion H0.
    case_eq (signature_eq s1 s); intros. 
    rewrite H2 in H0. 
    case_eq (mreg_plus_ident_eq r1 s0); intros. 
    rewrite H3 in H0. 
    case_eq (peq l1 l0); intros. 
    clear H2 H3 H4. subst. trivial. 
    rewrite H4 in H0. inversion H0. 
    rewrite H3 in H0. inversion H0. 
    rewrite H2 in H0. inversion H0. 
    inversion H0. 
    rewrite H1 in H0. inversion H0. 
Qed.

Lemma veriftree:
  forall c1 c2 l t, 
  (cfg_code c1) ! l = Some (Mtree t) ->       
  verify l (cfg_code c1) (cfg_code c2) = true -> exists t',
  (cfg_code c2) ! l = Some (Mtree t') /\ compare t t' = true.
Proof. 
  intros.   
  unfold verify in H0. 
  rewrite H in H0. 
  case_eq ((cfg_code c2) ! l); intros. 
    rewrite H1 in H0. 
      case_eq i; intros; subst.
      exists i0. split; trivial. 
    inversion H0. inversion H0. 
    rewrite H1 in H0.  inversion H0. 
Qed. 
  
Lemma verifreturn:
  forall c1 c2 l, 
  (cfg_code c1) ! l = Some Mreturn ->       
  verify l (cfg_code c1) (cfg_code c2) = true ->
  (cfg_code c2) ! l = Some Mreturn.
Proof. 
  intros.   
  unfold verify in H0. 
  rewrite H in H0. 
  case_eq ((cfg_code c2) ! l); intros. 
    rewrite H1 in H0. 
      case_eq i; intros; subst.
      inversion H0. inversion H0.  trivial. 
    rewrite H1 in H0.  inversion H0. 
Qed. 

Definition check_function f tf :  bool :=
  (if signature_eq f.(fn_sig) tf.(fn_sig) then true else false) &&
  (if zeq f.(fn_stacksize) tf.(fn_stacksize) then true else false) &&
  (if zeq f.(fn_framesize) tf.(fn_framesize) then true else false) &&
  check_cfg f.(fn_body) tf.(fn_body).

Definition check_external_function f tf : bool :=
  (if peq f.(ef_id) tf.(ef_id) then true else false) &&
  (if signature_eq f.(ef_sig) tf.(ef_sig) then true else false).

Definition check_fundef f tf : bool :=
  match f, tf with 
  | Internal f, Internal tf => check_function f tf
  | External f, External tf => check_external_function f tf
  | _,_ => false
  end. 
  
Definition check_idfundef f tf : bool :=
  match f, tf with
  | (idf,f) , (idtf,tf) => (if peq idf idtf then true else false) && check_fundef f tf
  end. 

Fixpoint check_funct_list lf ltf {struct lf} : bool :=
  match lf, ltf with
  | f :: lf', tf :: ltf' => check_idfundef f tf && check_funct_list lf' ltf'
  | nil, nil => true
  | _ , _ => false
  end. 

Fixpoint check_init_data (id1 id2 : init_data) {struct id1} : bool :=
  match id1 , id2 with
  | Init_int8 i , Init_int8 i' => if Int.eq_dec i i' then true else false
  | Init_int16 i , Init_int16 i' => if Int.eq_dec i i' then true else false
  | Init_int32 i , Init_int32 i' => if Int.eq_dec i i' then true else false
  | Init_float32 f , Init_float32 f' => if Float.eq_dec f f' then true else false
  | Init_float64 f , Init_float64 f' => if Float.eq_dec f f' then true else false
  | Init_space p , Init_space p' => if zeq p p' then true else false
  | Init_pointer li , Init_pointer li' => 
      let fix check_init_data_list (l1 l2 : list init_data) {struct l1} : bool :=
         match l1, l2 with
         | nil , nil => true
         | i1 :: l1 , i2 :: l2 => check_init_data i1 i2  && check_init_data_list l1 l2
         | _ , _ => false
         end in
         check_init_data_list li li'
  | _ , _ => false
  end.

Fixpoint check_init_data_list (l1 l2 : list init_data) {struct l1} : bool :=
  match l1 , l2 with
  | nil , nil => true
  | i1 :: l1 , i2 :: l2 => check_init_data i1 i2 && check_init_data_list l1 l2 
  | _ , _ => false
  end. 

Definition check_unit (uf utf : unit) : bool := true. 

Definition check_var vf vtf : bool :=
  match vf , vtf with
  | (idf,lf,uf), (idtf,ltf,utf) => (if peq idf idtf then true else false) &&
                                        check_init_data_list lf ltf &&
                                        check_unit uf utf
  end. 
                                        

Fixpoint check_vars lf ltf {struct lf} : bool :=
  match lf, ltf with
  | vf :: lf , vtf :: ltf => check_var vf vtf && check_vars lf ltf
  | nil , nil => true 
  | _ , _ =>  false
  end. 

Definition check_program p tp : bool :=  
  check_funct_list p.(prog_funct) tp.(prog_funct) &&
  (if peq p.(prog_main) tp.(prog_main) then true else false) &&
  check_vars p.(prog_vars) tp.(prog_vars). 
  
(** preuve de correction *)
 
(** lemmes utiles *)

Axiom find_symbol_preserved:
  forall p tp,
  check_program p tp = true ->
  forall i,
  @Genv.find_symbol fundef (Genv.globalenv p) i  = @Genv.find_symbol fundef (Genv.globalenv tp) i. 

Axiom funct_same:
  forall p tp,
  check_program p tp = true ->
  forall v f,
  @Genv.find_funct fundef (Genv.globalenv p) v = Some f ->
  exists tf, @Genv.find_funct fundef (Genv.globalenv tp) v = Some tf /\ check_fundef f tf = true.

Axiom funct_ptr_same:
  forall p tp,
  check_program p tp = true ->
  forall v f,
  @Genv.find_funct_ptr fundef (Genv.globalenv p) v = Some f ->
  exists tf, @Genv.find_funct_ptr fundef (Genv.globalenv tp) v = Some tf /\ check_fundef f tf = true.

Axiom init_mem_same:
  forall p tp,
  check_program p tp = true ->
  @Genv.init_mem fundef unit p = @Genv.init_mem fundef unit tp. 

Lemma env_doesnt_matter1:
  forall p tp,
  check_program p tp = true ->
  forall sp op vl,
  @eval_operation fundef (Genv.globalenv p) sp op vl = 
  @eval_operation fundef (Genv.globalenv tp) sp op vl.
Proof. 
  intros. 
  unfold eval_operation; destruct op; trivial.
  rewrite (find_symbol_preserved p tp H i). trivial.  
Qed. 

Lemma env_doesnt_matter2:
  forall p tp,
  check_program p tp = true ->
  forall sp addr vl,
  @eval_addressing fundef (Genv.globalenv p) sp addr vl = 
  @eval_addressing fundef (Genv.globalenv tp) sp addr vl.
Proof. 
  intros. 
  unfold eval_addressing; destruct addr; trivial.
  rewrite (find_symbol_preserved p tp H i). trivial.  
   rewrite (find_symbol_preserved p tp H i). trivial.   
Qed. 


Lemma find_function_prop:
  forall p tp,
  check_program p tp = true ->
  forall l rs f parent m t rs'  ,
  find_function (Genv.globalenv p) l rs = Some (External f) ->
  exec_function (Genv.globalenv p) (External f) parent rs m t rs' m -> 
  exists tf,
  find_function (Genv.globalenv tp) l rs = Some (External tf) /\ 
  check_fundef (External f) (External tf) = true.
Proof. 
  intros. 
  destruct l. 
  generalize (funct_same _ _ H _ _ H0); intro.
  destruct H2 as [tf [A B]]. 
  simpl in B. 
  case_eq tf; intros. 
  rewrite H2 in B. congruence. 
  rewrite H2 in B. 
  exists e. intuition trivial. simpl. subst. trivial.
  simpl in H0. 
  case_eq (@Genv.find_symbol fundef (Genv.globalenv p) i); intros.
  rewrite H2 in H0. 
  generalize (funct_ptr_same _ _ H _ _ H0); intro.
  destruct H3 as [tf [A B]]. 
  simpl in B. 
  case_eq tf; intros. 
  rewrite H3 in B. congruence. 
  rewrite H3 in B. 
  exists e. intuition trivial. simpl.  
  rewrite (find_symbol_preserved p tp H) in H2. 
  rewrite H2. subst. trivial.  
  rewrite H2 in H0. congruence. 
Qed. 

Lemma find_function_prop_int:
  forall p tp,
  check_program p tp = true ->
  forall l rs f,
  find_function (Genv.globalenv p) l rs = Some (Internal f) ->
  exists tf,
  find_function (Genv.globalenv tp) l rs = Some (Internal tf) /\ 
  check_fundef (Internal f) (Internal tf) = true.
Proof. 
  intros. 
  destruct l. 
  simpl in H0. 
  generalize (funct_same _ _ H _ _ H0); intro.
  destruct H1 as [tf [A B]]. 
  simpl in B. 
  case_eq tf; intros. 
    rewrite H1 in B. 
    exists f0. simpl. subst. intuition trivial. 
    rewrite H1 in B. congruence. 
  simpl in H0. 
  case_eq (@Genv.find_symbol fundef (Genv.globalenv p) i); intros.
  rewrite H1 in H0. 
  generalize (funct_ptr_same _ _ H _ _ H0); intro.
  destruct H2 as [tf [A B]].
  simpl in B. 
  case_eq tf; intros. 
    rewrite H2 in B. exists f0. simpl. 
    rewrite (find_symbol_preserved p tp H) in H1.
    rewrite H1. subst. intuition  trivial. 
  rewrite H2 in B. congruence. 
  rewrite H1 in H0. 
  congruence. 
Qed. 

Lemma checksome:
  forall lbl c tc i, 
  verify lbl c tc = true ->
  c ! lbl = Some i ->
  exists i', tc ! lbl = Some i'.
Proof. 
  intros. 
  unfold verify in H. 
  destruct c! lbl; destruct tc ! lbl. 
  exists i1; trivial. 
  destruct i0; congruence. 
  inversion H. 
  inversion H. 
Qed. 

Lemma false_fold:
  forall b,
  b && false = false.
Proof. 
  intros. destruct b; simpl; congruence.
Qed.  

(** la preuve centrale *)

Lemma transf_fundef_correct: 
  forall f parent p tp rs m t rs' m',
  check_program p tp = true->
  exec_function (Genv.globalenv p) f parent rs m t rs' m' ->
  forall tf,
  check_fundef f tf =true ->
  exec_function (Genv.globalenv tp) tf parent rs m t rs' m'. 
Proof.  
  intros f parent p tp rs m t rs' m'. intro. intro.   
  generalize (env_doesnt_matter1 _ _ H); intro ENV1. 
  generalize (env_doesnt_matter2 _ _ H); intro ENV2. 

  eapply exec_function_ind5 with

  ( ge := (Genv.globalenv p))

  (P := fun c sp parent instr rs fr m t lbl' rs' fr' m' =>
           forall tc lbl tinstr, 
           check_cfg c tc = true ->
           (cfg_code c)!lbl = Some instr ->
           ((cfg_code tc)!lbl = Some tinstr ->
           exec_instruction (Genv.globalenv tp) tc sp parent tinstr rs fr m t lbl' rs' fr' m'))
  
  (P0 := fun (c : cfg) sp parent lbl rs fr m t lbl' rs' fr' m' =>
            forall tc,
            check_cfg c tc = true ->
            exec_instrs (Genv.globalenv tp) tc sp parent lbl rs fr m t lbl' rs' fr' m')

  (P1 := fun (f : function) parent link ra rs m t rs' m' =>
             forall tf,
             check_function f tf = true ->
             exec_function_body (Genv.globalenv tp) tf parent link ra rs m t rs' m')

  (P2 := fun (f : fundef) parent rs m t rs' m' =>
            forall tf,
            check_fundef f tf = true ->
            exec_function (Genv.globalenv tp) tf parent rs m t rs' m'); intros.  

  (* call *)

  case_eq f'; intros; subst.
 generalize (find_function_prop_int _  _ H  _ _ _ H1). intro F.  destruct F. destruct H7 as [H7 CF].      
  generalize (checkandsome _ _ _ _ H4 H5); intro.  
  generalize (verifcall _ _ _ _ _ _ H5 H8); intro.
  rewrite H6 in H9. inversion H9; subst.

  eapply exec_Mcall; eauto. (*
  eapply H3; eauto.
  eapply transf_funct_ok; eauto. *) 
  
  inversion H2; subst.  
  generalize (find_function_prop _ _ H _ _ _ _ _ _ _ H1 H2); intro.
  destruct H7 as [tf [A C]]. 
  generalize (checkandsome _ _ _ _ H4 H5); intro.  
  generalize (verifcall _ _ _ _ _ _ H5 H7); intro.      
  rewrite H6 in H10. inversion H10; subst. 
  eapply exec_Mcall; eauto. 

  (* tree *)

  generalize (checkandsome _ _ _ _ H2 H3); intro.  
  generalize (veriftree _ _ _ _  H3 H5); intro. destruct H6. destruct H6. 
  rewrite H4 in H6. inversion H6; subst. 
  eapply exec_Mtree; eauto. 
  eapply wd_semantics; eauto.
  unfold compare in H7. trivial. 

  (* refl *)

  eapply exec_refl; eauto. 

  (* add *)

  generalize (checkandsome _ _ _ _  H6 H1); intro.
  generalize (checksome _ _ _ _ H7 H1); intro. destruct H8.  
  eapply exec_add; eauto. 

  (* function_body *)

  unfold check_function in H7.
  case_eq (check_cfg (fn_body f0) (fn_body tf)); intros.
  assert ((fn_sig f0) = (fn_sig tf)). 
    case_eq (signature_eq (fn_sig f0) (fn_sig tf) ); intros. 
    trivial. rewrite H9 in H7. simpl in H7. congruence. 
  assert ((fn_stacksize f0) = (fn_stacksize tf)). 
    case_eq (zeq (fn_stacksize f0) (fn_stacksize tf)); intros. 
    trivial. rewrite H10 in H7. rewrite false_fold in H7. simpl in H7. congruence.   
  assert ((fn_framesize f0) = (fn_framesize tf)). 
    case_eq (zeq (fn_framesize f0) (fn_framesize tf)); intros. 
    trivial. rewrite H11 in H7. rewrite false_fold in H7. simpl in H7. congruence.  
  subst. 
  rewrite H8 in H7. 
  eapply exec_funct_body; eauto. 
  rewrite <- H10; eauto.
  unfold init_frame. unfold init_frame in H2. rewrite <- H11; eauto.  
  assert ((cfg_head (fn_body f0)) = (cfg_head (fn_body tf))). 
    generalize (same_h _ _ H8); intro. trivial. 
  rewrite <- H12. rewrite <- H11.   
  eapply H5; eauto. 
  generalize (H5 (fn_body tf) H8); intro. 
  generalize (checkandsome _ _ _ _ H8 H6); intro.    
  generalize (verifreturn _ _ _ H6 H13); intro. 
  simpl. trivial. 
  rewrite H8 in H7. rewrite false_fold in H7. congruence. 

  (* internal function *)

  unfold check_fundef in H3. 
  case_eq tf; intros.
    rewrite H4 in H3. 
    injection H3; intros; subst. 
  eapply exec_funct_internal; eauto. 
  rewrite H4 in H3. inversion H3. 
  
  (* external function *)
  
  unfold check_fundef in H4. 
  case_eq tf; intros. subst. inversion H4. 
  subst. 
  unfold check_external_function in H4. 
  assert ((ef_id ef) = (ef_id e)). 
    case_eq (peq (ef_id ef) (ef_id e)); intros. 
    trivial. rewrite H3 in H4. simpl in H4. congruence. 
  assert ((ef_sig ef) = (ef_sig e)). 
    case_eq (signature_eq (ef_sig ef) (ef_sig e)); intros. 
    trivial. 
    rewrite H5 in H4. rewrite false_fold in H4. congruence. 
  rewrite H5.
  inversion H1.
  rewrite H5 in H6. rewrite H5 in H7. rewrite H3 in H10. subst.
  rewrite H3. 
  eapply exec_funct_external; eauto. 
  eapply event_match_intro; eauto. 
  rewrite <- H5. trivial.  
  
  (* fin *)
  trivial.  
Qed. 

Theorem check_correct :
  forall p tp t r, 
  check_program p tp = true ->
  exec_program p t r ->
  exec_program tp t r.
Proof. 
  intros. inversion H. revert H2. intro BACK.  
  unfold exec_program in H0. 
  destruct H0 as [b [f [rs [m [A [B [C D]]]]]]].
  unfold check_program in H. 
  assert (exists f', @Genv.find_funct_ptr fundef (Genv.globalenv tp) b = Some f' /\ 
  exec_function (Genv.globalenv tp) f' empty_frame (Regmap.init Vundef)
      (Genv.init_mem tp) t rs m). 
    generalize (funct_ptr_same _ _ BACK _ _ B); intro. 
    destruct H0 as [tf [E F]]. exists tf. intuition trivial. eapply transf_fundef_correct; eauto.
     rewrite (init_mem_same _ _ BACK) in C. trivial. 
  destruct H0 as [f' [E F]]. 
  exists b; exists f'; exists rs; exists m.
  repeat (generalize (essai _ _ H); clear H; intro H; destruct H).
  assert (prog_main p = prog_main tp). 
    case_eq (peq (prog_main p) (prog_main tp)); intros. 
    trivial. 
    rewrite H2 in H1. congruence. 
  intuition trivial. 
  generalize (find_symbol_preserved p tp BACK (prog_main tp)). intro.
  unfold fundef in H3. unfold fundef. 
  rewrite <- H3. rewrite <- H2. trivial . 
Qed.   
  

