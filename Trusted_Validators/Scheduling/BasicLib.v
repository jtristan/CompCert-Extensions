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
(** The model of the machine *)

Inductive resource : Set := 
| Reg : mreg -> resource
| Mem : resource
| Stack : resource.

Lemma dec_and_refl:
  forall A : Set, forall (dec : forall (r1 : A) (r2 : A), {r1 = r2} + {r1 <> r2}),  forall r, 
  (if dec r r then true else false) = true. 
Proof. 
  intros. case_eq (dec r r); intros. trivial. congruence. 
Qed.   

(** A bunch of decidable equality lemmas *)

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

Lemma resource_eq : forall (r1 r2 : resource), {r1 = r2} + {r1 <> r2}.
Proof.
decide equality. apply mreg_eq.
Defined.

Lemma comparison_eq: forall (x y : comparison), {x = y} + {x <> y}.
Proof.
decide equality.
Defined.

Lemma condition_eq: forall (x y : condition), {x = y} + {x <> y}.
Proof.
generalize comparison_eq; intro.
generalize Int.eq_dec; intro.
decide equality.
Defined.

Lemma operation_eq: forall (x y : operation), {x = y} + {x <> y}.
Proof.
generalize Int.eq_dec; intro.
generalize Float.eq_dec; intro.
generalize ident_eq; intro.
generalize condition_eq; intro.
decide equality.
Defined.

Lemma addressing_eq : forall (x y : addressing), {x = y} + {x <> y}.
Proof.
generalize Int.eq_dec; intro.
generalize ident_eq; intro.
decide equality.
Defined.

Lemma memory_chunk_eq : forall (x y : memory_chunk), {x = y} + {x <> y}.
Proof.
decide equality.
Defined.

Lemma typ_eq : forall (x y : typ), {x = y} + {x <> y}.
Proof.
decide equality.
Defined.

Lemma list_typ_eq: forall (x y : list typ), {x = y} + {x <> y}.
Proof.
generalize typ_eq; intro.
decide equality.
Defined.

Lemma option_typ_eq : forall (x y : option typ), {x = y} + {x <> y}.
Proof.
generalize typ_eq; intro.
decide equality.
Defined.

Lemma signature_eq: forall (x y : signature), {x = y} + {x <> y}.
Proof.
generalize list_typ_eq; intro.
generalize option_typ_eq; intro.
decide equality.
Defined.

Lemma list_operation_eq : forall (x y : list operation), {x = y} + {x <> y}.
Proof.
generalize operation_eq; intro.
decide equality.
Defined.

Lemma list_mreg_eq : forall (x y : list mreg), {x = y} + {x <> y}.
Proof.
generalize mreg_eq; intro.
decide equality.
Defined.

Lemma mreg_plus_ident_eq : forall (x y : mreg + ident), {x = y} + {x <> y}. 
Proof.
generalize mreg_eq; intro.
generalize ident_eq; intro.
decide equality.
Defined.

Lemma instruction_eq: forall (x y : instruction), {x = y} + {x <> y}.
Proof.
generalize mreg_eq; intro.
generalize typ_eq; intro.
generalize Int.eq_dec; intro.
generalize memory_chunk_eq; intro.
generalize addressing_eq; intro.
generalize operation_eq; intro.
generalize condition_eq; intro.
generalize signature_eq; intro.
generalize list_operation_eq; intro.
generalize list_mreg_eq; intro.
generalize ident_eq; intro.
generalize mreg_plus_ident_eq; intro.
decide equality.
Defined.


(** Syntax of computation terms*)

Inductive expression: Set :=
| Ebase : resource -> expression
| Eop : operation -> expression_list -> expression
| Eload : memory_chunk -> addressing -> expression_list -> expression -> expression
| Estore : expression -> memory_chunk -> addressing -> expression_list -> expression -> expression
| Egetstack : int -> typ -> expression -> expression
| Esetstack : expression -> expression -> int -> typ -> expression
| Egetparam : int -> typ -> expression
| Emalloc1 : expression -> expression -> expression
| Emalloc2 : expression -> expression -> expression
with expression_list: Set :=
| Enil: expression_list
| Econs: expression -> expression_list -> expression_list.


Scheme expression_ind3:= Minimality for expression Sort Prop
    with expression_list_ind3:= Minimality for expression_list Sort Prop.

Module R_indexed.
  Definition t := resource.
  Definition index (rs: resource) : positive :=
    match rs with
    | Reg r => xO (IndexedMreg.index r)
    | Mem => 1%positive
    | Stack => 3%positive
    end.

Lemma index_inj:  forall (x y: t), index x = index y -> x = y.
Proof. 
  destruct x; destruct y; intro; try (simpl in H; congruence). 
  simpl in H. injection H. intro. 
  generalize (Locations.IndexedMreg.index_inj _ _ H0). intro. congruence. 
Qed. 
  
Definition eq := resource_eq.
End R_indexed.

Module Rmap  := IMap(R_indexed).

Definition forest : Set := Rmap.t (expression).

Notation "a # b" := (Rmap.get b a) (at level 1).
Notation "a # b <- c" := (Rmap.set b c a) (at level 1, b at next level).

(** Semantics of computations terms*)

Inductive sem_value (A : Set):
    Genv.t A -> val -> frame -> regset -> frame -> mem -> expression -> val -> Prop :=
  | Sgetstack: 
          forall ge sp parent rs fr m stack_exp ty ofs v fr', 
          sem_frame A ge sp parent rs fr m stack_exp fr' ->
          get_slot fr' ty (Int.signed ofs) v ->
          sem_value A ge sp parent rs fr m (Egetstack ofs ty stack_exp) v

  | Sgetparam:
          forall ge sp parent rs fr m ty ofs v,
          get_slot parent ty (Int.signed ofs) v ->
          sem_value A ge sp parent rs fr m (Egetparam ofs ty) v

  | Sload:
          forall ge sp parent rs fr m mem_exp addr chunk args a v m' lv ,
          sem_mem A ge sp parent rs fr m mem_exp m' ->
          sem_val_list A ge sp parent rs fr m args lv ->
          eval_addressing ge sp addr lv = Some a ->
          Mem.loadv chunk m' a = Some v ->
          sem_value A ge sp parent rs fr m (Eload chunk addr args mem_exp) v

  | Sop: 
          forall ge sp parent rs fr m op args v lv,
          sem_val_list A ge sp parent rs fr m args lv ->
          eval_operation ge sp op lv = Some v ->
          sem_value A ge sp parent rs fr m (Eop op args) v

  | Sbase_reg:
          forall ge sp parent rs fr m r,
          sem_value A ge sp parent rs fr m (Ebase (Reg r)) (rs r)

  | Smalloc1:
          forall ge sp parent rs fr m sz m' blk m0 val_exp mem_exp,
          sem_value A ge sp parent rs fr m val_exp (Vint sz) ->
          sem_mem A ge sp parent rs fr m mem_exp m0 ->
          Mem.alloc m0 0 (Int.signed sz) = (m', blk) ->
          sem_value A ge sp parent rs fr m (Emalloc1 val_exp mem_exp) (Vptr blk Int.zero)

with sem_frame (A : Set):
    Genv.t A -> val -> frame -> regset -> frame -> mem -> expression -> frame -> Prop :=
  | Ssetstack:
          forall ge sp parent rs fr m stack_exp val_exp ty ofs fr' v fr'',
          sem_frame A ge sp parent rs fr m stack_exp fr' ->
          sem_value A ge sp parent rs fr m val_exp v ->
          set_slot fr' ty (Int.signed ofs) v fr'' ->
          sem_frame A ge sp parent rs fr m (Esetstack stack_exp val_exp ofs ty) fr''

  | Sbase_frame:
          forall ge sp parent rs fr m,
          sem_frame A ge sp parent rs fr m (Ebase Stack) fr

with sem_mem (A : Set) :
    Genv.t A -> val -> frame -> regset -> frame -> mem -> expression -> mem -> Prop :=
  | Sstore:
          forall ge sp parent rs fr m mem_exp val_exp m'' addr v a m' chunk args lv,
          sem_mem A ge sp parent rs fr m mem_exp m' ->
          sem_value A ge sp parent rs fr m val_exp v ->
          sem_val_list A ge sp parent rs fr m args lv ->
          eval_addressing ge sp addr lv = Some a ->
          Mem.storev chunk m' a v = Some m'' ->
          sem_mem A ge sp parent rs fr m (Estore mem_exp chunk addr args val_exp) m''
  | Sbase_mem:
          forall ge sp parent rs fr m,
          sem_mem A ge sp parent rs fr m (Ebase Mem) m

    | Smalloc2:
          forall ge sp parent rs fr m sz m' blk m0 val_exp mem_exp,
          sem_value A ge sp parent rs fr m val_exp (Vint sz) ->
          sem_mem A ge sp parent rs fr m mem_exp m0 ->
          Mem.alloc m0 0 (Int.signed sz) = (m', blk) ->
          sem_mem A ge sp parent rs fr m (Emalloc2 val_exp mem_exp) m'

with sem_val_list (A : Set) :
   Genv.t A -> val -> frame -> regset -> frame -> mem -> expression_list -> list val -> Prop :=
  | Snil:
          forall ge sp parent rs fr m,
          sem_val_list A ge sp parent rs fr m (Enil) nil
          
  |Scons:
          forall ge sp parent rs fr m e v l lv,
          sem_value A ge sp parent rs fr m e v ->
          sem_val_list A ge sp parent rs fr m l lv ->
          sem_val_list A ge sp parent rs fr m (Econs e l) (cons v lv).

Scheme sem_value_ind2:= Minimality for sem_value Sort Prop
    with sem_frame_ind2:= Minimality for sem_frame Sort Prop
    with sem_mem_ind2:= Minimality for sem_mem Sort Prop
    with sem_val_list_ind2:= Minimality for sem_val_list Sort Prop.

Hint Resolve Sgetstack : vali.
Hint Resolve Sgetparam : vali.
Hint Resolve Sload : vali.
Hint Resolve Sop : vali.
Hint Resolve Sbase_reg : vali.
Hint Resolve Ssetstack : vali.
Hint Resolve Sbase_frame : vali.
Hint Resolve Sstore : vali.
Hint Resolve Sbase_mem : vali.
Hint Resolve Snil : vali.
Hint Resolve Scons : vali.
Hint Resolve Smalloc1 : vali.
Hint Resolve Smalloc2 : vali. 

Inductive sem_regset (A : Set) :
   Genv.t A -> val -> frame -> regset -> frame -> mem -> forest -> regset -> Prop :=
  | Sregset:
        forall ge sp parent rs fr m f rs',
        (forall x, sem_value A ge sp parent rs fr m (f # (Reg x)) (rs' (x))) ->
        sem_regset A ge sp parent rs fr m f rs'.
 
Inductive sem (A : Set) : 
   Genv.t A -> val -> frame -> regset -> frame -> mem -> forest -> regset -> frame -> mem -> Prop :=  
  | Sem:
        forall ge sp parent rs fr m f rs' fr' m',
        sem_regset A ge sp parent rs fr m f rs' ->
        sem_frame A ge sp parent rs fr m (f # Stack) fr' ->
        sem_mem A ge sp parent rs fr m (f # Mem) m' ->
        sem A ge sp parent rs fr m f rs' fr' m'.

(** Basic operations over computations terms *)

Fixpoint beq_expression (e1 e2: expression) {struct e1}: bool :=
  match e1, e2 with 
  (* | Eimp , Eimp => false *)
  | Ebase r1, Ebase r2 => if resource_eq r1 r2 then true else false
  | Eop op1 el1, Eop op2 el2 =>
      if operation_eq op1 op2 then beq_expression_list el1 el2 else false
  | Eload chk1 addr1 el1 e1, Eload chk2 addr2 el2 e2 =>
      if memory_chunk_eq chk1 chk2 
      then if addressing_eq addr1 addr2 
      then if beq_expression_list el1 el2 
      then beq_expression e1 e2 else false else false else false
  | Estore m1 chk1 addr1 el1 e1, Estore m2 chk2 addr2 el2 e2=>
      if memory_chunk_eq chk1 chk2
      then if addressing_eq addr1 addr2
      then if beq_expression_list el1 el2 
      then if beq_expression m1 m2 
      then beq_expression e1 e2 else false else false else false else false
  | Egetstack i1 t1 e1, Egetstack i2 t2 e2 =>
      if Int.eq_dec i1 i2
      then if typ_eq t1 t2
      then if beq_expression e1 e2
      then true
      else false
      else false
      else false
  | Esetstack f1 e1 i1 t1, Esetstack f2 e2 i2 t2 =>
      if Int.eq_dec i1 i2
      then if typ_eq t1 t2
      then if beq_expression e1 e2 
      then if beq_expression f1 f2 then true
      else false else false else false else false
  | Egetparam i1 t1, Egetparam i2 t2 =>
      if Int.eq_dec i1 i2
      then if typ_eq t1 t2 then true
      else false else false
  | Emalloc1 v1 m1, Emalloc1 v2 m2 =>
      if beq_expression v1 v2 then beq_expression m1 m2 else false
  | Emalloc2 v1 m1, Emalloc2 v2 m2 =>
      if beq_expression v1 v2 then beq_expression m1 m2 else false
| _, _ => false
  end
with beq_expression_list (el1 el2: expression_list) {struct el1}: bool :=
  match el1, el2 with
  | Enil, Enil => true
  | Econs e1 t1, Econs e2 t2 => beq_expression e1 e2 && beq_expression_list t1 t2
  | _, _ => false
  end.

Scheme expression_ind2:= Induction for expression Sort Prop
    with expression_list_ind2:= Induction for expression_list Sort Prop.

Lemma beq_expression_correct:
  forall e1 e2, beq_expression e1 e2 = true -> e1 = e2.
Proof.
  intro e1.  
  apply expression_ind2 with
    (P := fun (e1: expression) => forall e2, beq_expression e1 e2 = true -> e1 = e2)
    (P0 := fun (e1: expression_list) => forall e2, beq_expression_list e1 e2 = true -> e1 = e2).
  (* Eimp *)
  (* intro e2. destruct e2; simpl; try congruence. *)
  (* Ebase *)
  intros r e2. destruct e2; simpl; try congruence.
  case (resource_eq r r0); try congruence.
  (* Eop *)
  intros o e HR e2. destruct e2; simpl; try congruence. 
  case (operation_eq o o0); intros. generalize (HR _ H). congruence.
  congruence.
  (* Eload *)
  intros m a e HR e3 HR3. destruct e2 ; simpl ; try congruence.
  case (memory_chunk_eq m m0). 
  case (addressing_eq a a0). 
  caseEq (beq_expression_list e e0). 
  caseEq (beq_expression e3 e2).
  intros. 
  generalize (HR e0 H0). generalize (HR3 e2 H). intros. 
  subst. trivial. 
  intros; discriminate. 
  intros; discriminate. 
  intros; discriminate. 
  intros; discriminate. 
  (* Estore *)
  intros e3 HR2 m a e HR e4 HR4 e2.
  destruct e2; simpl; try congruence.
  case (memory_chunk_eq m m0). case (addressing_eq a a0).
  (*case (beq_expression_list e e0). case (beq_expression e3 e2). *)
  intros. 
  caseEq (beq_expression_list e e0). intro. rewrite H0 in H. 
  caseEq (beq_expression e3 e2_1). intro. rewrite H1 in H. 
  generalize (HR2 e2_1 H1). intro. generalize (HR e0 H0). 
  generalize (HR4 e2_2 H).
  congruence.
  intro. rewrite H1 in H. discriminate. 
  intro. rewrite H0 in H. discriminate. 
  intros; congruence.
  intros; congruence.
  (* Egetstack *)
  intros i t e HR e2.
  destruct e2; simpl; try congruence.
  case (Int.eq_dec i i0); case (typ_eq t t0); 
  caseEq (beq_expression e e2); try congruence.
  intros. generalize (HR e2 H). intro. subst; trivial. 
  (* Esetstack *)
  intros ne nHR e HR i t e2.
  destruct e2; simpl; try congruence. 
  case (Int.eq_dec i i0); case (typ_eq t t0); try congruence.
  caseEq (beq_expression e e2_2); try congruence. 
  caseEq (beq_expression ne e2_1). 
  intros. generalize (HR e2_2 H0). generalize (nHR e2_1 H). congruence.
  intros; discriminate. 
  (* Egetparam *)
  intros i t e2.
  destruct e2; simpl; try congruence.
  case (Int.eq_dec i i0); case (typ_eq t t0); try congruence.
  (* Emalloc *)
  intros. 
  destruct e2; simpl; try inversion H1. 
  caseEq (beq_expression e e2_1); caseEq (beq_expression e0 e2_2); intros. 
  generalize (H e2_1 H4). generalize (H0 e2_2 H2). intros; subst; trivial. 
  rewrite H4 in H3. rewrite H2 in H3. inversion H3. 
  rewrite H4 in H3 . inversion H3. 
  rewrite H4 in H3. inversion H3. 
  (* Emalloc2 *)
  intros. 
  destruct e2; simpl; try inversion H1. 
  caseEq (beq_expression e e2_1); caseEq (beq_expression e0 e2_2); intros. 
  generalize (H e2_1 H4). generalize (H0 e2_2 H2). intros; subst; trivial. 
  rewrite H4 in H3. rewrite H2 in H3. inversion H3. 
  rewrite H4 in H3 . inversion H3. 
  rewrite H4 in H3. inversion H3.   
  (* Enil *)
  intro e2.
  intro.
  injection H.
  case e2; intros; try congruence; trivial.
  (* Econs *)
  intros e HR1 e0 HR2 e2.
  destruct e2; simpl; try congruence.
  caseEq (beq_expression e e2); caseEq (beq_expression_list e0 e3); simpl; try congruence.
  intros. clear H1. generalize (HR1 e2 H0). generalize (HR2 e3 H).
  congruence.
Defined.  
  
Hint Resolve beq_expression_correct.

Definition check (fa fb : forest) :=
beq_expression (fa # (Reg R3)) (fb # (Reg R3))  && 
beq_expression (fa # (Reg R4)) (fb # (Reg R4)) && 
beq_expression (fa # (Reg R5)) (fb # (Reg R5)) && 
beq_expression (fa # (Reg R6)) (fb # (Reg R6)) && 
beq_expression (fa # (Reg R7)) (fb # (Reg R7)) && 
beq_expression (fa # (Reg R8)) (fb # (Reg R8)) && 
beq_expression (fa # (Reg R9)) (fb # (Reg R9)) && 
beq_expression (fa # (Reg R10)) (fb # (Reg R10)) &&  
beq_expression (fa # (Reg R13)) (fb # (Reg R13)) && 
beq_expression (fa # (Reg R14)) (fb # (Reg R14)) && 
beq_expression (fa # (Reg R15)) (fb # (Reg R15)) && 
beq_expression (fa # (Reg R16)) (fb # (Reg R16)) && 
beq_expression (fa # (Reg R17)) (fb # (Reg R17)) && 
beq_expression (fa # (Reg R18)) (fb # (Reg R18)) && 
beq_expression (fa # (Reg R19)) (fb # (Reg R19)) && 
beq_expression (fa # (Reg R20)) (fb # (Reg R20)) && 
beq_expression (fa # (Reg R21)) (fb # (Reg R21)) && 
beq_expression (fa # (Reg R22)) (fb # (Reg R22)) && 
beq_expression (fa # (Reg R23)) (fb # (Reg R23)) && 
beq_expression (fa # (Reg R24)) (fb # (Reg R24)) && 
beq_expression (fa # (Reg R25)) (fb # (Reg R25)) && 
beq_expression (fa # (Reg R26)) (fb # (Reg R26)) && 
beq_expression (fa # (Reg R27)) (fb # (Reg R27)) && 
beq_expression (fa # (Reg R28)) (fb # (Reg R28)) && 
beq_expression (fa # (Reg R29)) (fb # (Reg R29)) && 
beq_expression (fa # (Reg R30)) (fb # (Reg R30)) && 
beq_expression (fa # (Reg R31)) (fb # (Reg R31)) &&
beq_expression (fa # (Reg F1)) (fb # (Reg F1)) && 
beq_expression (fa # (Reg F2)) (fb # (Reg F2)) && 
beq_expression (fa # (Reg F3)) (fb # (Reg F3)) && 
beq_expression (fa # (Reg F4)) (fb # (Reg F4)) && 
beq_expression (fa # (Reg F5)) (fb # (Reg F5)) && 
beq_expression (fa # (Reg F6)) (fb # (Reg F6)) && 
beq_expression (fa # (Reg F7)) (fb # (Reg F7)) && 
beq_expression (fa # (Reg F8)) (fb # (Reg F8)) && 
beq_expression (fa # (Reg F9)) (fb # (Reg F9)) && 
beq_expression (fa # (Reg F10)) (fb # (Reg F10)) && 
beq_expression (fa # (Reg F14)) (fb # (Reg F14)) && 
beq_expression (fa # (Reg F15)) (fb # (Reg F15)) && 
beq_expression (fa # (Reg F16)) (fb # (Reg F16)) && 
beq_expression (fa # (Reg F17)) (fb # (Reg F17)) && 
beq_expression (fa # (Reg F18)) (fb # (Reg F18)) && 
beq_expression (fa # (Reg F19)) (fb # (Reg F19)) && 
beq_expression (fa # (Reg F20)) (fb # (Reg F20)) && 
beq_expression (fa # (Reg F21)) (fb # (Reg F21)) && 
beq_expression (fa # (Reg F22)) (fb # (Reg F22)) && 
beq_expression (fa # (Reg F23)) (fb # (Reg F23)) && 
beq_expression (fa # (Reg F24)) (fb # (Reg F24)) && 
beq_expression (fa # (Reg F25)) (fb # (Reg F25)) && 
beq_expression (fa # (Reg F26)) (fb # (Reg F26)) && 
beq_expression (fa # (Reg F27)) (fb # (Reg F27)) && 
beq_expression (fa # (Reg F28)) (fb # (Reg F28)) && 
beq_expression (fa # (Reg F29)) (fb # (Reg F29)) && 
beq_expression (fa # (Reg F30)) (fb # (Reg F30)) && 
beq_expression (fa # (Reg F31)) (fb # (Reg F31)) && 
beq_expression (fa # (Reg IT1)) (fb # (Reg IT1)) &&
beq_expression (fa # (Reg IT2)) (fb # (Reg IT2)) && 
beq_expression (fa # (Reg IT3)) (fb # (Reg IT3)) &&
beq_expression (fa # (Reg FT1)) (fb # (Reg FT1)) && 
beq_expression (fa # (Reg FT2)) (fb # (Reg FT2)) &&
beq_expression (fa # (Reg FT3)) (fb # (Reg FT3)) && 
beq_expression (fa # Mem) (fb # Mem) &&
beq_expression (fa # Stack) (fb # Stack).

Lemma essai: forall (a b : bool), a && b = true -> a = true /\ b = true.
intros a b.
case a; case b; auto.
Qed.

Lemma check_correct: forall (fa fb : forest) (x : resource), 
check fa fb = true -> fa # x = fb # x.
Proof.
   intros fa fb.
   unfold check.
   intros x HYP.
repeat match goal with | H : ?a && ?b = true |- _ =>
generalize (essai _ _ H); clear H;
let H1 := fresh "H" in
let H2 := fresh "H" in 
intros [H1 H2] end.
destruct x. destruct m; auto.
auto.
auto.
Qed.

Lemma check_correct_bis: forall (fa fb : forest),
  check fa fb = true -> forall x, fa # x = fb # x. 
Proof. 
  intros. eapply check_correct; eauto. 
Qed. 

(*Notation "a # b <- c" := (Rmap.set b c a) (at level 1, b at next level).*)

(** The empty abstract state *)
 
Definition empty : forest :=
  (Rmap.init  (Ebase (Reg R3)))
  # (Reg   R3 ) <- (Ebase (Reg R3) ) # (Reg   R4 ) <- (Ebase (Reg R4) ) # (Reg   R5 ) <- (Ebase (Reg R5))
  # (Reg   R6 ) <- (Ebase (Reg R6) ) # (Reg   R7 ) <- (Ebase (Reg R7) ) # (Reg   R8 ) <- (Ebase (Reg R8))
  # (Reg   R9 ) <- (Ebase (Reg R9) ) # (Reg   R10 ) <- (Ebase (Reg R10) ) 
  # (Reg   R13 ) <- (Ebase (Reg R13) ) # (Reg   R14 ) <- (Ebase (Reg R14) ) # (Reg   R15 ) <- (Ebase (Reg R15))
  # (Reg   R16 ) <- (Ebase (Reg R16) ) # (Reg   R17 ) <- (Ebase (Reg R17) ) # (Reg   R18 ) <- (Ebase (Reg R18))
  # (Reg   R19 ) <- (Ebase (Reg R19) ) # (Reg   R20 ) <- (Ebase (Reg R20) ) # (Reg   R21 ) <- (Ebase (Reg R21))
  # (Reg   R22 ) <- (Ebase (Reg R22) ) # (Reg   R23 ) <- (Ebase (Reg R23) ) # (Reg   R24 ) <- (Ebase (Reg R24))
  # (Reg   R25 ) <- (Ebase (Reg R25) ) # (Reg   R26 ) <- (Ebase (Reg R26) ) # (Reg   R27 ) <- (Ebase (Reg R27))
  # (Reg   R28 ) <- (Ebase (Reg R28) ) # (Reg   R29 ) <- (Ebase (Reg R29) ) # (Reg   R30 ) <- (Ebase (Reg R30))
  # (Reg   R31 ) <- (Ebase (Reg R31) ) # (Reg   F1 ) <- (Ebase (Reg F1) ) # (Reg   F2 ) <- (Ebase (Reg F2))
  # (Reg   F3 ) <- (Ebase (Reg F3) ) # (Reg   F4 ) <- (Ebase (Reg F4) ) # (Reg   F5 ) <- (Ebase (Reg F5))
  # (Reg   F6 ) <- (Ebase (Reg F6) ) # (Reg   F7 ) <- (Ebase (Reg F7) ) # (Reg   F8 ) <- (Ebase (Reg F8))
  # (Reg   F9 ) <- (Ebase (Reg F9) ) # (Reg   F10 ) <- (Ebase (Reg F10) ) # (Reg   F14 ) <- (Ebase (Reg F14))
  # (Reg   F15 ) <- (Ebase (Reg F15) ) # (Reg   F16 ) <- (Ebase (Reg F16) ) # (Reg   F17 ) <- (Ebase (Reg F17))
  # (Reg   F18 ) <- (Ebase (Reg R3) ) # (Reg   F18 ) <- (Ebase (Reg F18) ) # (Reg   F19 ) <- (Ebase (Reg F19))
  # (Reg   F20 ) <- (Ebase (Reg F20) ) # (Reg   F21 ) <- (Ebase (Reg F21) ) # (Reg   F22 ) <- (Ebase (Reg F22))
  # (Reg   F23 ) <- (Ebase (Reg F23) ) # (Reg   F24 ) <- (Ebase (Reg F24) ) # (Reg   F25 ) <- (Ebase (Reg F25))
  # (Reg   F26 ) <- (Ebase (Reg F26) ) # (Reg   F27 ) <- (Ebase (Reg F27) ) # (Reg   F28 ) <- (Ebase (Reg F28))
  # (Reg   F29 ) <- (Ebase (Reg F29) ) # (Reg   F30 ) <- (Ebase (Reg F30) ) # (Reg   F31 ) <- (Ebase (Reg F31))
  # (Reg   IT1 ) <- (Ebase (Reg IT1) ) # (Reg   IT2 ) <- (Ebase (Reg IT2) ) # (Reg   IT3 ) <- (Ebase (Reg IT3))
  # (Reg   FT1 ) <- (Ebase (Reg FT1) ) # (Reg   FT2 ) <- (Ebase (Reg FT2) ) # (Reg   FT3 ) <- (Ebase (Reg FT3))
  # Stack <- (Ebase Stack ) # Mem <- (Ebase Mem). 

Lemma get_empty:
  forall r, empty#r = Ebase r.
Proof.
  destruct r. unfold Rmap.get; destruct m; simpl; try reflexivity.
  reflexivity. reflexivity. 
Qed.

Lemma map0:
  forall r, 
  empty # r = Ebase r.
Proof. 
  intros. eapply get_empty. 
Qed.

Lemma map1:
  forall w dst dst',
  dst <> dst' ->
  (empty # dst <- w) # dst' = Ebase dst'. 
Proof. 
  intros. 
  rewrite Rmap.gso. eapply map0. auto. 
Qed. 

Lemma genmap1:
  forall (f : forest) w dst dst',
  dst <> dst' ->
  (f # dst <- w) # dst' = f # dst'. 
Proof. 
  intros. 
  rewrite Rmap.gso. reflexivity. auto. 
Qed. 

Lemma map2:
  forall (v : expression) x rs,
  (rs # x <- v) # x = v.
Proof. 
  intros. 
  rewrite Rmap.gss. trivial. 
Qed.

Lemma map3:
  forall (v : val) (x : mreg) rs,
  Regmap.set x v rs x  = v.
Proof.  
  intros.  
unfold Regmap.set. 
  caseEq (RegEq.eq x x);intros; intuition. 
  generalize (n (refl_equal x)). intro. intuition. 
Qed. 

Lemma map4:
  forall x,
  Rmap.get x empty = Ebase x.
Proof. 
  intros. eapply get_empty.  
Qed.

Lemma map5:
  forall x y (v : val) rs,
  x <> y ->
  Regmap.set y v rs x = rs x.
Proof. 
  intros. unfold Regmap.set. 
  caseEq (RegEq.eq x y). intros. 
  intuition. intros. trivial. 
Qed.

Lemma tri1:
  forall x y,
  Reg x <> Reg y -> x <> y.
Proof. 
  intros. intuition. 
  rewrite H0 in H. generalize (H (refl_equal (Reg y))). 
  intuition. 
Qed.

Hint Rewrite -> map0 : vali.
Hint Rewrite -> map1 : vali.
Hint Rewrite -> map2 : vali.
Hint Rewrite -> map3 : vali.
Hint Rewrite -> map4 : vali.
Hint Rewrite -> map5 : vali.

(** Lemma of functionnality of the computations terns semantics *)

Lemma fonct:
  forall FF ge tge sp parent rs fr m f, 
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  forall v v' fv fv' mv mv',
  (sem_value FF ge sp parent rs fr m f v /\ sem_value FF tge sp parent rs fr m f v' -> v = v') /\
  (sem_frame FF ge sp parent rs fr m f fv /\ sem_frame FF tge sp parent rs fr m f fv' -> fv = fv') /\
  (sem_mem FF ge sp parent rs fr m f mv /\ sem_mem FF tge sp parent rs fr m f mv' -> mv = mv').
Proof. 
 
  intros FF ge tge sp parent rs fr m f ENV1 ENV2. 
  
   apply expression_ind2 with
    
    (P := fun (e1: expression) => 
    forall v v' fv fv' mv mv',
    (sem_value FF ge sp parent rs fr m e1 v /\ sem_value FF tge sp parent rs fr m e1 v' -> v = v') /\ 
    (sem_frame FF ge sp parent rs fr m e1 fv /\ sem_frame FF tge sp parent rs fr m e1 fv' -> fv = fv') /\ 
    (sem_mem FF ge sp parent rs fr m e1 mv /\ sem_mem FF tge sp parent rs fr m e1 mv' -> mv = mv'))
    
    (P0 := fun (e1: expression_list) => 
    forall lv lv', sem_val_list FF ge sp parent rs fr m e1 lv -> sem_val_list FF tge sp parent rs fr m e1 lv' -> lv = lv'
    ); intros; intuition. 

  inversion H0. inversion H0. inversion H0. 
  inversion H0; inversion H1; subst; congruence. 
  inversion H0; inversion H1; subst; congruence. 
  inversion H0; inversion H1; subst; congruence.  

  inversion H1; inversion H2; subst. generalize (H lv lv0 H10 H21). intro. 
  generalize (ENV1 sp o lv). intro. congruence. 
  inversion H1. inversion H1. 

  inversion H2; inversion H3; subst. generalize (H lv lv0 H15 H30). intro. subst. 
  generalize (H0 v v' fv fv' m' m'0). intros. intuition. 
  generalize (ENV2 sp a lv0). intro. congruence. 

  inversion H2. inversion H2. 

  inversion H3. inversion H3. 
  inversion H3; inversion H4; subst. 
  generalize (H0 lv lv0 H18 H35). intro. 
  generalize (H1 v0 v1 fv fv' mv mv'). 
  generalize (H v v' fv fv' m' m'0). intros. intuition. 
  generalize (ENV2 sp a lv). intro. congruence. 

  inversion H1; inversion H2; subst. generalize (H v v' fr' fr'0 mv mv'). 
  intuition. subst. inversion H25; inversion H13; subst. congruence.   
  inversion H1. inversion H1. 

  inversion H2. 
  inversion H2; inversion H3; subst. 
  generalize (H v v' fr' fr'0 mv mv'). intuition. 
  generalize (H0 v0 v1 fv fv' mv mv'). intuition. subst. 
  inversion H30; inversion H16. 
  assert (A = A0). eapply proof_irrelevance; eauto. 
  assert (B = B0). eapply proof_irrelevance; eauto. 
  assert (C = C0). eapply proof_irrelevance; eauto. congruence.
  inversion H2. 
  
  inversion H0; inversion H1; subst. 
  inversion H10; inversion H20; subst. congruence.  


  inversion H0. inversion H0. 

  inversion H2; subst. inversion H3; subst. 
  generalize (H (Vint sz) (Vint sz0) fv fv' mv mv'). 
  generalize (H0 sp sp fv fv' m1 m2). intuition. subst. 
  injection H7. intro; subst. 
  rewrite H17 in H14. injection H14. intros; subst; trivial. 
  inversion H2. inversion H2. inversion H2. inversion H2. 

  inversion H2; subst. inversion H3; subst. 
  generalize (H (Vint sz) (Vint sz0) fv fv' mv mv'). 
  generalize (H0 sp sp fv fv' m1 m2). intuition. subst. 
  injection H7. intro; subst. 
  rewrite H17 in H14. injection H14. intros; subst; trivial.  

  inversion H; inversion H0; subst. trivial. 
  inversion H1; inversion H2; subst. generalize (H v v0 fr fr m m ). 
  intuition. generalize (H0 lv0 lv1 H13 H24). intros. congruence. 
Qed.

Lemma fonct_value:
  forall FF ge tge sp parent rs fr m f v v',
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  sem_value FF ge sp parent rs fr m f v ->
  sem_value FF tge sp parent rs fr m f v' ->
  v = v'.
Proof. 
  intros. 
  generalize (fonct FF ge tge sp parent rs fr m f H H0 v v' fr fr m m). 
  intuition trivial. 
Qed.

Lemma s_fonct_value:
  forall FF ge sp parent rs fr m f v v',
  sem_value FF ge sp parent rs fr m f v ->
  sem_value FF ge sp parent rs fr m f v' ->
  v = v'.
Proof. 
  intros. 
  eapply fonct_value; eauto. intros; trivial. 
  intros; trivial. 
Qed.

Lemma fonct_frame:
  forall FF ge tge sp parent rs fr m f v v',
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  sem_frame FF ge sp parent rs fr m f v ->
  sem_frame FF tge sp parent rs fr m f v' ->
  v = v'.
Proof.
  intros. 
  generalize (fonct FF ge tge sp parent rs fr m f H H0 sp sp v v' m m). 
  intuition trivial. 
Qed.  

Lemma s_fonct_frame:
  forall FF ge sp parent rs fr m f v v',
  sem_frame FF ge sp parent rs fr m f v ->
  sem_frame FF ge sp parent rs fr m f v' ->
  v = v'.
Proof. 
  intros. eapply fonct_frame; eauto. intros; trivial. intros; trivial. 
Qed.

Lemma fonct_mem:
  forall FF ge tge sp parent rs fr m f v v',
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  sem_mem FF ge sp parent rs fr m f v ->
  sem_mem FF tge sp parent rs fr m f v' ->
  v = v'.
Proof. 
  intros. 
  generalize (fonct FF ge tge sp parent rs fr m f H H0 sp sp fr fr v v'). 
  intuition trivial.   
Qed.

Lemma s_fonct_mem:
  forall FF ge sp parent rs fr m f v v',
  sem_mem FF ge sp parent rs fr m f v ->
  sem_mem FF ge sp parent rs fr m f v' ->
  v = v'.
Proof. 
  intros. eapply fonct_mem; eauto. intros; trivial. intros; trivial. 
Qed.

Lemma fonct_regset:
  forall FF ge tge sp parent rs fr m f v v',
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  sem_regset FF ge sp parent rs fr m f v ->
  sem_regset FF tge sp parent rs fr m f v' ->
  v = v'.
Proof. 
  intros. 
  inversion H1; subst. inversion H2; subst. 
  assert (forall x, v x = v' x). intro. 
  generalize (H3 x); intro. generalize (H4 x); intro. 
  eapply fonct_value; eauto. 
  apply (Regmap.exten v v' H5). 
Qed. 


Hint Resolve fonct_value : vali.
Hint Resolve fonct_frame : vali.
Hint Resolve fonct_mem : vali.
Hint Resolve fonct_regset : vali.


Lemma font_sem:
  forall FF ge tge sp parent f rs fr m rs' fr' m' rs'' fr'' m'',
  (forall sp op vl, eval_operation ge sp op vl = eval_operation tge sp op vl) ->
  (forall sp addr vl, eval_addressing ge sp addr vl = eval_addressing tge sp addr vl) ->
  sem FF ge sp parent rs fr m f rs' fr' m' ->
  sem FF tge sp parent rs fr m f rs'' fr'' m'' ->
  rs' = rs'' /\ fr' = fr'' /\ m' = m''.
Proof.
  intros. 
  inversion H1; subst. inversion H2; subst. 
  intuition (eauto with vali).
Qed. 

Lemma s_fonct_sem:
  forall FF ge sp parent f rs fr m rs' fr' m' rs'' fr'' m'',
  sem FF ge sp parent rs fr m f rs' fr' m' ->
  sem FF ge sp parent rs fr m f rs'' fr'' m'' ->
  rs' = rs'' /\ fr' = fr'' /\ m' = m''. 
Proof.  
  intros. eapply font_sem; eauto. intros; trivial. intros; trivial. 
Qed. 

Fixpoint list_translation (l : list mreg) (f : forest) {struct l} : expression_list :=
match l with
| nil => Enil
| cons i l => Econs (Rmap.get (Reg i) f) (list_translation l f)
end.

(** Injection from sequence of instructions to computations terms *)

Definition update (f : forest) (i : instruction) : forest := 
match i with
    | Mgetstack i0 t r => 
        Rmap.set (Reg r) (Egetstack i0 t (Rmap.get Stack f)) f 
    | Msetstack r i0 t => 
        Rmap.set Stack (Esetstack (Rmap.get Stack f) (Rmap.get (Reg r) f) i0 t) f
    | Mgetparam i0 t r => 
        Rmap.set (Reg r) (Egetparam i0 t) f
    | Mop op rl r => 
        Rmap.set (Reg r) (Eop op (list_translation rl f)) f
    | Mload chunk addr rl r => 
        Rmap.set (Reg r) (Eload chunk addr (list_translation rl f) (Rmap.get Mem f)) f
    | Mstore chunk addr rl r => 
        Rmap.set Mem (Estore (Rmap.get Mem f) chunk addr (list_translation rl f) (Rmap.get (Reg r) f))  f
    | Malloc =>
        Rmap.set Mem (Emalloc2 (Rmap.get (Reg Conventions.loc_alloc_argument) f) (Rmap.get (Mem) f)) 
        (Rmap.set (Reg (Conventions.loc_alloc_result)) (Emalloc1 (Rmap.get (Reg Conventions.loc_alloc_argument) f) (Rmap.get (Mem) f)) f)
    | Mcall sign id => f
    | Mlabel lbl => f
    | Mgoto lbl  => f 
    | Mcond cond rl lbl => f
    | Mreturn => f
end.

Definition nbranchset (i : instruction) : bool :=
match i with
| Msetstack a b c => true
| Mgetstack a b c => true
| Mgetparam a b c => true
| Mop a b c => true
| Mload a b c d => true
| Mstore a b c d => true 
| Malloc => true
| _ => false
end.

Fixpoint abstract_sequence (f : forest) (c : code) {struct c} : option forest :=
  match c with
  | nil => Some f
  | cons (Mgoto lbl) l => None
  | cons (Mcall sig n) l => None
  | cons (Mlabel lbl) l => None
  | cons (Mcond cmp rl lbl) l => None
  | cons (Mreturn) l => None
  | i :: l => abstract_sequence (update f i) l
  end.

Fixpoint lnbranchset (l : list instruction) : bool :=
match l with
| Msetstack a b c ::  k => lnbranchset k
| Mgetstack a b c :: k => lnbranchset k
| Mgetparam a b c :: k => lnbranchset k
| Mop a b c :: k => lnbranchset k
| Mload a b c d :: k => lnbranchset k
| Mstore a b c d :: k => lnbranchset k
| Malloc :: k => lnbranchset k
| nil => true
| _ => false
end.

Definition compare (c1 : code) (c2 : code) : bool :=
  match abstract_sequence empty c1 with
  | None => false
  | Some a1 => match abstract_sequence empty c2 with
                        | None => false
                        | Some a2 => check a1 a2
                        end
  end. 

Lemma abstract_succeed:
  forall c f,
  lnbranchset c = true -> exists x, abstract_sequence f c = Some x.
Proof. 
  induction c; intros. 
  simpl. exists f. trivial. 
    assert (lnbranchset c = true). 
    simpl in H. destruct a; try congruence; trivial. 
  generalize (IHc (update f a) H0). intro. destruct H1. exists x. 
  rewrite <- H1. 
  destruct a; trivial; try inversion H. 
Qed.  

Lemma gen_list_base:
  forall FF ge sp parent l rs rs0 fr0 m0 exps,
  (forall x, sem_value FF ge sp parent rs0 fr0 m0 (exps # (Reg x)) (rs x)) ->
  sem_val_list FF ge sp parent rs0 fr0 m0 (list_translation l exps) rs ## l.
Proof. 
  induction l. 
  intros. simpl. eauto with vali. 
  intros. simpl. eapply Scons; eauto. 
Qed.  

(** A bunch of trivial lemmas on lists *)

Lemma list_size:
forall l1 l2 : list instruction,
l1 = l2 -> length l1 = length l2. 
Proof. 
  intros. rewrite H. trivial. 
Qed. 

Lemma list_plus_size:
forall l1 l2 : list instruction,
length (l1 ++ l2) = (length l1 + length l2)%nat. 
Proof. 
  intros. induction l1. 
  simpl. trivial. 
  simpl. rewrite IHl1. trivial. 
Qed. 

Lemma list_diff:
forall  (l2 l : list instruction) (a : instruction),
a :: l2 ++ l = l -> False. 
Proof. 
  intros. generalize (list_size (a :: l2 ++ l) l H). 
  intro. simpl in H0. rewrite list_plus_size in H0. 
  omega.    
Qed. 

Lemma list_diff2:
forall  (l : list instruction) (a : instruction),
a :: l = l -> False. 
Proof. 
  intros. generalize (list_size (a :: l) l H). 
  intro. simpl in H0. 
  omega.    
Qed.    

Lemma empty_no_move:
  forall FF ge sp parent rs fr m,
  sem FF ge sp parent rs fr m empty rs fr m.
Proof. 
  intros. 
  eapply Sem; eauto. 
  eapply Sregset; eauto. intro. 
  rewrite get_empty. auto with vali. 
  auto with vali. 
  auto with vali. 
Qed. 

Fixpoint is_in (i : instruction) (c : code) {struct c} : bool :=
   match c with 
     | nil => false
     | a :: l => if instruction_eq i a then true else is_in i l
     end.

(** More lemmas about computations terms *)

Lemma one_schanged_reg:
forall FF ge sp parent rs rs' fr m y w,
(forall x : mreg,     
      sem_value FF ge sp parent rs fr m (empty # (Reg y) <- w # (Reg x)) (rs' x)) ->
(forall x, rs' x= (Regmap.set y (rs' y) rs) x).
Proof. 
  intros. generalize (mreg_eq x y). intro. 
  generalize (H x). intro. destruct H0. 
  subst. rewrite map3. trivial.  
  rewrite map5. rewrite map1 in H1. inversion H1. trivial. 
  intuition congruence. intuition congruence. 
Qed.
 
Lemma gen_one_changed_reg:
  forall FF ge sp parent rs0 fr0 m0 rs fr m rs' y w exps,
  sem FF ge sp parent rs0 fr0 m0 exps rs fr m -> 
  (forall x,
     sem_value FF ge sp parent rs0 fr0 m0
       (exps # (Reg y) <- w # (Reg x))
       (rs' x)) ->
  (forall x, rs' x= (Regmap.set y (rs' y) rs) x).
Proof. 
  intros. generalize (mreg_eq x y). intro. 
  generalize (H0 x). intro. destruct H1. 
  subst. rewrite map3. trivial. 
  rewrite map5;auto. rewrite genmap1 in H2; try (congruence). 
  inversion H; subst. inversion H1; subst. 
  generalize (H5 x); intro.
  eapply s_fonct_value; eauto. 
Qed.
  

Lemma regset_unchanged_Stack:
forall FF ge sp parent rs fr m rs' w, 
(forall x : mreg,
     sem_value FF ge sp parent rs fr m (empty # Stack <- w # (Reg x)) (rs' x)) ->
(forall x : mreg, rs x = rs' x).
Proof.
  intros. 
  generalize (H x). intro. 
  rewrite Rmap.gso in H0. rewrite get_empty in H0.  
  inversion H0; subst. trivial. congruence. 
Qed.

Lemma gen_regset_unchanged_Stack:
  forall FF ge sp parent rs fr m rs0 fr0 m0 rs' w f, 
  sem FF ge sp parent rs0 fr0 m0 f rs fr m -> 
  (forall x : mreg,
  sem_value FF ge sp parent rs0 fr0 m0 (f # Stack <- w # (Reg x)) (rs' x)) ->
  (forall x : mreg, rs x = rs' x).
Proof. 
  intros. 
  generalize (H0 x). intro. rewrite genmap1 in H1; try congruence. 
  inversion H; subst. inversion H2; subst.
  eapply s_fonct_value; eauto. 
Qed.

Lemma regset_unchanged_Mem:
forall FF ge sp parent rs fr m rs' w, 
(forall x : mreg,
     sem_value FF ge sp parent rs fr m (empty # Mem <- w # (Reg x)) (rs' x)) ->
(forall x : mreg, rs x = rs' x).
Proof.
  intros. 
  generalize (H x). intro. 
  rewrite Rmap.gso in H0. 
  rewrite get_empty in H0. 
inversion H0; subst. trivial. congruence. 
Qed.

Lemma gen_regset_unchanged_Mem:
  forall FF ge sp parent rs fr m rs0 fr0 m0 rs' w f, 
  sem FF ge sp parent rs0 fr0 m0 f rs fr m -> 
  (forall x : mreg,
  sem_value FF ge sp parent rs0 fr0 m0 (f # Mem <- w # (Reg x)) (rs' x)) ->
  (forall x : mreg, rs x = rs' x).
Proof.
  intros. 
  generalize (H0 x). intro. rewrite genmap1 in H1; try congruence. 
  inversion H; subst. inversion H2; subst.
  eapply s_fonct_value; eauto. 
Qed.

Lemma list_translation_base:
  forall FF args ge sp parent rs fr m,
  sem_val_list FF ge sp parent rs fr m (list_translation args empty) rs##args.
Proof. 
  induction args. 
  intros. simpl. eauto with vali. 
  intros. simpl. eapply Scons; eauto. rewrite map4. eauto with vali. 
Qed. 
 
Lemma gen_list_translation_det:
  forall FF ge sp parent rs fr m l l1 l2 f,
  sem_val_list FF ge sp parent rs fr m (list_translation l f) l1 ->
  sem_val_list FF ge sp parent rs fr m (list_translation l f) l2 ->
  l1 = l2. 
  induction l.
  intros. simpl in H. simpl in H0. inversion H; subst. inversion H0; subst. 
  trivial. 
  intros. inversion H; subst. inversion H0; subst. 
  generalize (IHl lv lv0 _ H11 H13). intro. 
  assert (v = v0); try (eauto with vali). 
  subst. eapply s_fonct_value; eauto. subst.  trivial. 
Qed.

Lemma to_exten:
forall FF ge sp parent  rs fr m  rs',
 (forall x : mreg,
     sem_value FF ge sp parent rs fr m (empty # (Reg x)) (rs' x)) ->
     (forall x, rs x = rs' x).
Proof.
  intros. generalize (H x).
  intro. 
  rewrite get_empty in H0.  
  inversion H0; subst. trivial. 
Qed.

(** Implememtation of constraints *)

Require Import FSetWeak. 

Inductive constraint : Set :=
  | Const : expression -> resource -> constraint
  | BiConst : expression -> resource -> expression -> resource -> constraint
  | NilConst : constraint.


Definition constraint_eq (c c' : constraint) : bool :=
  match c, c' with
  | Const e r, Const e' r' => if resource_eq r r' then beq_expression e e' else false
  | BiConst e1 r1 e2 r2, BiConst e1' r1' e2' r2' => andb
     (if resource_eq r1 r1' then beq_expression e1 e1' else false)
     (if resource_eq r2 r2' then beq_expression e2 e2' else false)
  | NilConst, NilConst => true
  | _,_ => false
  end.

Definition constraint_dec (c c' : constraint) : 
        {constraint_eq c c' = true} + {constraint_eq c c' = false}:=
  Sumbool.sumbool_of_bool (constraint_eq c c'). 

(*  Module constraintdt : DecidableType with Definition t := constraint.  *)

Module constraintdt. 
Definition t := constraint. 
Definition eq c c':= Is_true (constraint_eq c c'). 

Lemma constraint_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  intros. unfold eq. case_eq (constraint_eq x y); intros. 
  left. simpl. trivial. 
  right. simpl. congruence. 
Defined.  


Axiom eq_refl : forall x, eq x x.
Axiom eq_sym : forall x y, eq x y -> eq y x. 
Axiom eq_trans : forall x y z, eq x y -> eq y z -> eq x z. 

Definition eq_dec := constraint_dec. 
(* Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }. *)

End constraintdt. 

 

Module constset := Make(constraintdt). 
(* ancienenemnt Raw *)
 
(** Computation of constraints from a sequence of instructions *)

Fixpoint compute_one_constraint (c : code) (f : forest) {struct c} : constraintdt.t :=
  match c with
  | nil => NilConst
  | (Mgetstack _ _ dst) as i :: nil => 
      (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) 
  | (Msetstack _ _ _ ) as i :: nil => 
      (Const (Rmap.get Stack (update f i))(Stack)) 
  | (Mgetparam _ _ dst) as i :: nil => 
      (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) 
  | (Mop _ _ dst) as i :: nil => 
      (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) 
  | (Mload _ _ _ dst) as i :: nil => 
      (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) 
  | (Mstore _ _ _ _) as i :: nil => 
      (Const (Rmap.get Mem (update f i))(Mem)) 
  | Malloc as i :: nil => 
      (BiConst (Rmap.get Mem (update f i)) Mem (Rmap.get (Reg Conventions.loc_alloc_result) (update f i))(Reg Conventions.loc_alloc_result)) 
  | i :: k => compute_one_constraint k (update f i)
 end. 


Fixpoint compute_constraints (c pc : code) (f : forest) {struct c} : constset.t :=
  match c with
  | nil => constset.empty
  | (Mgetstack _ _ dst) as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i)) 
  | (Msetstack _ _ _ ) as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i)) 
  | (Mgetparam _ _ dst) as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i)) 
  | (Mop _ _ dst) as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i)) 
  | (Mload _ _ _ dst) as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i)) 
  | (Mstore _ _ _ _) as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i)) 
  | Malloc as i :: k => 
      constset.add (compute_one_constraint (pc ++ i :: nil) empty) (compute_constraints k (pc ++ i :: nil) (update f i))
  | _ => constset.empty (* Oh my god... *)
 end. 

Fixpoint compute_constraints_me (c : code) (f : forest) {struct c} : constset.t :=
  match c with
  | nil => constset.empty
  | (Mgetstack _ _ dst) as i :: k => 
      constset.add (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) (compute_constraints_me k (update f i)) 
  | (Msetstack _ _ _ ) as i :: k => 
      constset.add (Const (Rmap.get Stack (update f i))(Stack)) (compute_constraints_me k (update f i)) 
  | (Mgetparam _ _ dst) as i :: k => 
      constset.add (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) (compute_constraints_me k (update f i)) 
  | (Mop _ _ dst) as i :: k => 
      constset.add (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) (compute_constraints_me k (update f i)) 
  | (Mload _ _ _ dst) as i :: k => 
      constset.add (Const (Rmap.get (Reg dst) (update f i))(Reg dst)) (compute_constraints_me k (update f i)) 
  | (Mstore _ _ _ _) as i :: k => 
      constset.add (Const (Rmap.get Mem (update f i))(Mem)) (compute_constraints_me k (update f i)) 
  | Malloc as i :: k => 
      constset.add (BiConst (Rmap.get Mem (update f i)) Mem (Rmap.get (Reg Conventions.loc_alloc_result) (update f i))(Reg Conventions.loc_alloc_result)) (compute_constraints_me k (update f i))
  | _ => constset.empty (* Oh my god... *)
 end. 


(* les deux derniers cas de la definition aui precede montre a quel point il faut que j'utilise le style monadique *)

Definition veriphi (c1 c2 : code) :=
  let s1 := compute_constraints_me c1 empty in
  let s2 := compute_constraints_me c2 empty in
  if constset.subset s2 s1 then true else if constset.equal s1 s2 then true else false. 


(** A bunch of lemmas on constraints *)

Lemma cpe:
  forall a b,
  constraint_eq a b = true <-> constraintdt.eq a b.
Proof. 
  intros; split; intro. 
  unfold constraintdt.eq. rewrite H. simpl. trivial. 
  unfold constraintdt.eq in H. unfold Is_true in H. 
  case_eq (constraint_eq a b); intro. trivial. 
  rewrite H0 in H. elimtype False. trivial. 
Qed. 
 
Lemma cpe_3:
  forall a b,
  constraint_eq a b = true -> constraintdt.eq a b. 
Proof. 
  intros. unfold constraintdt.eq. rewrite H. simpl. trivial. 
Qed. 

Lemma cpe_4:
  forall a b,
  constraint_eq a b = false -> ~ constraintdt.eq a b. 
Proof. 
  intros. unfold constraintdt.eq. rewrite H. simpl. congruence. 
Qed. 

Lemma consteq_1:
  forall e e' r r',
  constraintdt.eq (Const e r) (Const e' r') -> 
  (Const e r) = (Const e' r').
Proof. 
  intros. 
  unfold constraintdt.eq in H. 
  case_eq (constraint_eq (Const e r) (Const e' r')); intros. 
  unfold constraint_eq in H0. 
  case_eq (resource_eq r r'); intros. rewrite H1 in H0. 
  case_eq (beq_expression e e'); intros. 
  generalize (beq_expression_correct _ _ H2). intro. 
  rewrite e0. rewrite H3. trivial. 
  rewrite H2 in H0. inversion H0. 
  rewrite H1 in H0. inversion H0. 
  rewrite H0 in H. simpl in H. elimtype False. trivial. 
Qed. 

Lemma consteq_2:
  forall e1 e1' r1 r1' e2 r2 e'2 r'2,
  constraintdt.eq (BiConst e1 r1 e2 r2) (BiConst e1' r1' e'2 r'2) -> 
  (BiConst e1 r1 e2 r2) = (BiConst e1' r1' e'2 r'2).
Proof. 
  intros. 
  unfold constraintdt.eq in H. 
  case_eq (constraint_eq (BiConst e1 r1 e2 r2) (BiConst e1' r1' e'2 r'2)); intros. 
  unfold constraint_eq in H0. 
  case_eq (resource_eq r1 r1'); intros. rewrite H1 in H0. 
  case_eq (beq_expression e1 e1'); intros. rewrite H2 in H0. 
  case_eq (resource_eq r2 r'2); intros. rewrite H3 in H0. 
  case_eq (beq_expression e2 e'2); intros. rewrite H4 in H0. 
  generalize (beq_expression_correct _ _ H2); intro. 
  generalize (beq_expression_correct _ _ H4); intro. 
  rewrite e; rewrite e0; rewrite H5; rewrite H6. trivial. 
  rewrite H4 in H0. simpl in H0. inversion H0. 
  rewrite H3 in H0. simpl in H0. inversion H0. 
  rewrite H2 in H0. simpl in H0. inversion H0. 
  rewrite H1 in H0. simpl in H0. inversion H0. 
  rewrite H0 in H. inversion H. 
Qed. 

Lemma constraint_eq_sym:
  forall e e',
  constraint_eq e e' = constraint_eq e' e.
Proof. 
  intros. 
  generalize (constraintdt.eq_sym e e'). intro. 
  generalize (constraintdt.eq_sym e' e). intro. 
  unfold constraintdt.eq in H. 
  unfold constraintdt.eq in H0. 
  case_eq (constraint_eq e e'); intros.  
  rewrite H1 in H. simpl in H. 
  assert (True); trivial. generalize (H H2). intro. 
  generalize (H0 H3); intro; trivial. 
    case_eq (constraint_eq e' e); intros; try inversion H3; trivial. 
     rewrite H5 in H. simpl in H. intuition. 
  
  rewrite H1 in H0. 
  case_eq (constraint_eq e' e); intros. rewrite H2 in H0. simpl in H0. 
  intuition. trivial. 

Qed. 
  


Require FSetWeakProperties.

Module constprop := FSetWeakProperties.Properties(constset).



Lemma mem_prop:
  forall s e e',
  constraint_eq e e' = false -> 
  constset.mem e (constset.add e' s) = true -> 
  constset .mem e s = true.
Proof. 
  intros. 
  generalize (constset.mem_2 H0). intro. 
  rewrite constraint_eq_sym in H. 
  generalize (cpe_4 e' e H); intro. 
  apply constset.mem_1. 
  rewrite constprop.add_union_singleton in H1. 
  generalize (constset.union_1 H1); intro. 
  destruct H3. 
  generalize (constset.singleton_1 H3); intro. 
  elimtype False. intuition. 
  trivial.
Qed. 

Lemma test_aux: 
  forall c e r tf,
  constset.mem (Const e (Reg r)) (compute_constraints_me c tf) = true ->
  exists s1, exists s2, 
  c = s1 ++ s2 /\ 
  constraintdt.eq (Const e (Reg r)) (compute_one_constraint s1 tf). 
Proof.   
  induction c; intros. 
  (* nil *)
  exists ( @nil instruction ) ; exists ( @nil instruction). 
  split. trivial. inversion H. 
  (* a :: c *)
  destruct a; simpl in H.  

  (* Egetstack *) 
  
  case_eq (constraint_eq (Const e (Reg r)) (Const
            (Rmap.get (Reg m)
               tf # (Reg m) <- (Egetstack i t (Rmap.get Stack tf))) (Reg m)) ); intros.
  exists (Mgetstack i t m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetstack i t m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Msetstack *)

  case_eq (constraint_eq (Const e (Reg r)) (Const
            (Rmap.get Stack
                tf # Stack <-
            (Esetstack (Rmap.get Stack tf) (Rmap.get (Reg m) tf) i t)) Stack)); intros.
  exists (Msetstack m i t :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Msetstack m i t :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.   

  (* Mgetparam *)

  case_eq (constraint_eq (Const e (Reg r)) (Const (Rmap.get (Reg m) tf # (Reg m) <- (Egetparam i t)) (Reg m)) ); intros.
  exists (Mgetparam i t m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetparam i t m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 
 
  (* Mop *)

  case_eq (constraint_eq (Const e (Reg r)) (Const
            (Rmap.get (Reg m) tf # (Reg m) <- (Eop o (list_translation l tf)))
            (Reg m)) ); intros.
  exists (Mop o l m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mop o l m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mload *)

  case_eq (constraint_eq (Const e (Reg r)) (Const
            (Rmap.get (Reg m0)
               tf # (Reg m0) <-
               (Eload m a (list_translation l tf) (Rmap.get Mem tf)))
            (Reg m0)) ); intros.
  exists (Mload m a l m0 :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2.  
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mload m a l m0 :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mstore *)  

  case_eq (constraint_eq (Const e (Reg r)) (Const
            (Rmap.get Mem
               tf # Mem <-
               (Estore (Rmap.get Mem tf) m a (list_translation l tf)
                  (Rmap.get (Reg m0) tf))) Mem) ); intros.
  exists (Mstore m a l m0 :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mstore m a l m0 :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.   

  (* autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 
  
  (* Malloc *)

  case_eq (constraint_eq (Const e (Reg r)) (BiConst
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
  exists (Malloc :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Malloc :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.     

  (*  autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 

Qed.

Lemma test_aux_bis: 
  forall c e tf,
  constset.mem (Const e Stack) (compute_constraints_me c tf) = true ->
  exists s1, exists s2, 
  c = s1 ++ s2 /\ 
  constraintdt.eq (Const e Stack) (compute_one_constraint s1 tf). 
Proof.   
  induction c; intros. 
  (* nil *)
  exists ( @nil instruction ) ; exists ( @nil instruction). 
  split. trivial. inversion H. 
  (* a :: c *)
  destruct a; simpl in H.  

  (* Egetstack *) 
  
  case_eq (constraint_eq (Const e Stack) (Const
            (Rmap.get (Reg m)
               tf # (Reg m) <- (Egetstack i t (Rmap.get Stack tf))) (Reg m)) ); intros.
  generalize (cpe_3 _ _ H0); intro. 
  generalize (consteq_1 _ _ _ _ H1); intro; elimtype False; congruence. 
  unfold Rmap.get in *|-. (*; rewrite map2 in *|-. *)
  generalize (mem_prop _ _ _ H0 H); intro. 
  generalize (IHc _ _ H1); intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetstack i t m :: s3); exists s4. 
  split; subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Msetstack *)

  case_eq (constraint_eq (Const e Stack) (Const
            (Rmap.get Stack
               tf # Stack <-
               (Esetstack (Rmap.get Stack tf) (Rmap.get (Reg m) tf) i t))
            Stack) ); intros.
  generalize (cpe_3 _ _ H0); intro. 
  generalize (consteq_1 _ _ _ _ H1); intro. injection H2; intro; subst. 
  exists (Msetstack m i t :: nil). exists (c). 
  split. rewrite <- app_comm_cons. trivial. 
  trivial. 

  unfold Rmap.get in *|-. (*; rewrite map2 in *|-. *)
  generalize (mem_prop _ _ _ H0 H); intro. 
  generalize (IHc _ _ H1); intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Msetstack m i t :: s3); exists s4. 
  split; subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mgetparam *)

  case_eq (constraint_eq (Const e Stack) (Const (Rmap.get (Reg m) tf # (Reg m) <- (Egetparam i t)) (Reg m)) ); intros.
  generalize (cpe_3 _ _ H0); intro. 
  generalize (consteq_1 _ _ _ _ H1); intro; elimtype False; congruence. 
  unfold Rmap.get in *|-. (*; rewrite map2 in *|-. *)
  generalize (mem_prop _ _ _ H0 H); intro. 
  generalize (IHc _ _ H1); intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetparam i t m :: s3); exists s4. 
  split; subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mop *)

  case_eq (constraint_eq (Const e Stack) (Const
            (Rmap.get (Reg m) tf # (Reg m) <- (Eop o (list_translation l tf)))
            (Reg m)) ); intros.
  generalize (cpe_3 _ _ H0); intro. 
  generalize (consteq_1 _ _ _ _ H1); intro; elimtype False; congruence. 
  unfold Rmap.get in *|-. (*; rewrite map2 in *|-. *)
  generalize (mem_prop _ _ _ H0 H); intro. 
  generalize (IHc _ _ H1); intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mop o l m :: s3); exists s4. 
  split; subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mload *)

  case_eq (constraint_eq (Const e Stack) (Const
            (Rmap.get (Reg m0)
               tf # (Reg m0) <-
               (Eload m a (list_translation l tf) (Rmap.get Mem tf)))
            (Reg m0)) ); intros.
  generalize (cpe_3 _ _ H0); intro. 
  generalize (consteq_1 _ _ _ _ H1); intro; elimtype False; congruence. 
  unfold Rmap.get in *|-. (*; rewrite map2 in *|-. *)
  generalize (mem_prop _ _ _ H0 H); intro. 
  generalize (IHc _ _ H1); intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mload m a l m0 :: s3); exists s4. 
  split; subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mstore *)

  case_eq (constraint_eq (Const e Stack) (Const
            (Rmap.get Mem
               tf # Mem <-
               (Estore (Rmap.get Mem tf) m a (list_translation l tf)
                  (Rmap.get (Reg m0) tf))) Mem) ); intros.
  generalize (cpe_3 _ _ H0); intro. 
  generalize (consteq_1 _ _ _ _ H1); intro; elimtype False; congruence. 
  unfold Rmap.get in *|-. (*; rewrite map2 in *|-. *)
  generalize (mem_prop _ _ _ H0 H); intro. 
  generalize (IHc _ _ H1); intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mstore m a l m0 :: s3); exists s4. 
  split; subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 

  (* Malloc *)

  case_eq (constraint_eq (Const e Stack) (BiConst
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
  exists (Malloc :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Malloc :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* autre *)
  generalize (constset.mem_2 H); intro; inversion H0. 
  generalize (constset.mem_2 H); intro; inversion H0. 
  generalize (constset.mem_2 H); intro; inversion H0. 
  generalize (constset.mem_2 H); intro; inversion H0. 
Qed.   

Lemma test_aux_bis2: 
  forall c e tf,
  constset.mem (Const e Mem) (compute_constraints_me c tf) = true ->
  exists s1, exists s2, 
  c = s1 ++ s2 /\ 
  constraintdt.eq (Const e Mem) (compute_one_constraint s1 tf). 
Proof.   
  induction c; intros. 
  (* nil *)
  exists ( @nil instruction ) ; exists ( @nil instruction). 
  split. trivial. inversion H. 
  (* a :: c *)
  destruct a; simpl in H.  

  (* Egetstack *) 
  
  case_eq (constraint_eq (Const e Mem) (Const
            (Rmap.get (Reg m)
               tf # (Reg m) <- (Egetstack i t (Rmap.get Stack tf))) (Reg m)) ); intros.
  exists (Mgetstack i t m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2.  
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetstack i t m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Msetstack *)

  case_eq (constraint_eq (Const e Mem) (Const
            (Rmap.get Stack
                tf # Stack <-
            (Esetstack (Rmap.get Stack tf) (Rmap.get (Reg m) tf) i t)) Stack)); intros.
  exists (Msetstack m i t :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Msetstack m i t :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.   

  (* Mgetparam *)

  case_eq (constraint_eq (Const e Mem) (Const (Rmap.get (Reg m) tf # (Reg m) <- (Egetparam i t)) (Reg m)) ); intros.
  exists (Mgetparam i t m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetparam i t m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 
 
  (* Mop *)

  case_eq (constraint_eq (Const e Mem) (Const
            (Rmap.get (Reg m) tf # (Reg m) <- (Eop o (list_translation l tf)))
            (Reg m)) ); intros.
  exists (Mop o l m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mop o l m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mload *)

  case_eq (constraint_eq (Const e Mem) (Const
            (Rmap.get (Reg m0)
               tf # (Reg m0) <-
               (Eload m a (list_translation l tf) (Rmap.get Mem tf)))
            (Reg m0)) ); intros.
  exists (Mload m a l m0 :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mload m a l m0 :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mstore *)  

  case_eq (constraint_eq (Const e Mem) (Const
            (Rmap.get Mem
               tf # Mem <-
               (Estore (Rmap.get Mem tf) m a (list_translation l tf)
                  (Rmap.get (Reg m0) tf))) Mem) ); intros.
  exists (Mstore m a l m0 :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mstore m a l m0 :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.   

  (* autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 
  
  (* Malloc *)

  case_eq (constraint_eq (Const e Mem) (BiConst
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
  exists (Malloc :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _  H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Malloc :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.     

  (*  autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 

Qed.

Lemma test_aux_bis3: 
  forall c e1 r e2  tf,
  constset.mem (BiConst e1 Mem e2 (Reg r)) (compute_constraints_me c tf) = true ->
  exists s1, exists s2, 
  c = s1 ++ s2 /\ 
  constraintdt.eq (BiConst e1 Mem e2 (Reg r)) (compute_one_constraint s1 tf). 
Proof.   
  induction c; intros. 
  (* nil *)
  exists ( @nil instruction ) ; exists ( @nil instruction). 
  split. trivial. inversion H. 
  (* a :: c *)
  destruct a; simpl in H.  

  (* Egetstack *) 
  
  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (Const
            (Rmap.get (Reg m)
               tf # (Reg m) <- (Egetstack i t (Rmap.get Stack tf))) (Reg m)) ); intros.
  exists (Mgetstack i t m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetstack i t m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Msetstack *)

  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (Const
            (Rmap.get Stack
                tf # Stack <-
            (Esetstack (Rmap.get Stack tf) (Rmap.get (Reg m) tf) i t)) Stack)); intros.
  exists (Msetstack m i t :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2.  
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Msetstack m i t :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.   

  (* Mgetparam *)

  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (Const (Rmap.get (Reg m) tf # (Reg m) <- (Egetparam i t)) (Reg m)) ); intros.
  exists (Mgetparam i t m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mgetparam i t m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 
 
  (* Mop *)

  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (Const
            (Rmap.get (Reg m) tf # (Reg m) <- (Eop o (list_translation l tf)))
            (Reg m)) ); intros.
  exists (Mop o l m :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mop o l m :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mload *)

  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (Const
            (Rmap.get (Reg m0)
               tf # (Reg m0) <-
               (Eload m a (list_translation l tf) (Rmap.get Mem tf)))
            (Reg m0)) ); intros.
  exists (Mload m a l m0 :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mload m a l m0 :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial. 

  (* Mstore *)  

  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (Const
            (Rmap.get Mem
               tf # Mem <-
               (Estore (Rmap.get Mem tf) m a (list_translation l tf)
                  (Rmap.get (Reg m0) tf))) Mem) ); intros.
  exists (Mstore m a l m0 :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl. rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Mstore m a l m0 :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.   

  (* autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 
  
  (* Malloc *)

  case_eq (constraint_eq (BiConst e1 Mem e2 (Reg r)) (BiConst
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
  exists (Malloc :: nil). exists (c). 
  split. rewrite <- app_comm_cons. simpl. trivial. 
  simpl.  rewrite map2. 
  rewrite map2 in H0. eapply cpe_3; eauto. 
  generalize (mem_prop _ _ _ H0 H). intro. 
  generalize (IHc _ _ _ _ H1). intro. 
  destruct H2 as [s3 [s4 [A B]]]. 
  exists (Malloc :: s3). exists s4. 
  split. subst. rewrite <- app_comm_cons. trivial. 
  case_eq s3; intros; subst. 
  simpl in B. unfold constraintdt.eq in B. simpl in B. 
  elimtype False. trivial. 
  trivial.     

  (*  autre *)

  generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 
generalize (constset.mem_2 H); intro; inversion H0. 

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

(** Definition of composition and properties *)

Fixpoint composeExpression (f : forest) (t : expression)  {struct t} : expression :=
  match t with 
  | Ebase r => f # r 
  | Eop o el => Eop o (composeList f el)
  | Eload mc a el e => Eload mc a (composeList f el) (composeExpression f e)
  | Estore e1 mc a el e2 => Estore (composeExpression f e1) mc a (composeList f el) (composeExpression f e2)
  | Egetstack i t e => Egetstack i t (composeExpression f e)
  | Esetstack e1 e2 i t => Esetstack (composeExpression f e1) (composeExpression f e2) i t
  | Egetparam i t => Egetparam i t
  | Emalloc1 e1 e2 => Emalloc1 (composeExpression f e1) (composeExpression f e2)
  | Emalloc2 e1 e2 => Emalloc2 (composeExpression f e1) (composeExpression f e2)
  end

with composeList (f : forest) (tl : expression_list) {struct tl} : expression_list :=
  match tl with
  | Enil => Enil
  | Econs e el => Econs (composeExpression f e) (composeList f el)
  end.

Notation "a ;; b" := (update a b) (at level 1). 



(*
Lemma decomposeSem:
  forall ge sp parent a b rs fr m rs' fr' m',
  sem ge sp parent rs fr m (a ;; b) rs'' fr'' m'' ->
  exists rsi, exists fri, exists mi, 
  sem ge sp parent rs fr m a rsi fri mi /\
  sem ge sp parent rsi fri mi (empty ;; b) rs' fr' m'.

  induction b.  

  intros. inversion H; subst. 
  simpl in H1. rewrite Rmap.gso in H1; try congruence. 
  simpl in H2. rewrite Rmap.gso in H2; try congruence.
  exists (Regmap.set m sp rs'); exists fr'; exists m'. 
  split. 
  eapply Sem; eauto.  (* faux *) 
  simpl. rewrite get_empty. 
  eapply Sem; eauto. 
  rewrite Rmap.gso; try congruence. rewrite get_empty. eapply Sbase_frame.
  rewrite Rmap.gso; try congruence. rewrite get_empty. eapply Sbase_mem.

*)
(*

Lemma decomposeSem:
  forall ge sp parent a b rs fr m rsi fri mi rs' fr' m',
  sem ge sp parent rs fr m a rsi fri mi ->
  sem ge sp parent rs fr m (a ;; b) rs' fr' m' ->
  sem ge sp parent rsi fri mi (empty ;; b) rs' fr' m'.
Proof. 
  induction b; intros.

  (* getstack *) 
  simpl. rewrite get_empty.
  simpl in H0. inversion H0; subst.
  eapply Sem; eauto.

    inversion H1; subst. eapply Sregset; eauto. intros. 
    generalize (mreg_eq x m); intro. destruct H5.
 
      subst. generalize (H4 m); intro. 
      rewrite Rmap.gss in H5. rewrite Rmap.gss. 
      inversion H; subst. inversion H6; subst. 
      generalize (H9 m); intro. inversion H5; subst. 
      assert (fr'0 = fri). eapply fonct_frame; eauto. subst. 
      eapply Sgetstack; eauto. eapply Sbase_frame; eauto.

      rewrite Rmap.gso; try congruence. rewrite get_empty. 
      generalize (H4 x); intro.  rewrite Rmap.gso in H5; try congruence.
      inversion H; subst. inversion H6; subst. generalize (H9 x); intro. 
      assert (rsi x = rs' x). eapply fonct_value; eauto. 
      rewrite <- H11. eapply Sbase_reg.    

    rewrite Rmap.gso in H2; try congruence.
    rewrite Rmap.gso; try congruence. rewrite get_empty. 
    inversion H; subst. 
    assert (fri = fr'). eapply fonct_frame; eauto. subst. 
    eapply Sbase_frame. 

    rewrite Rmap.gso in H3; try congruence.
    rewrite Rmap.gso; try congruence. rewrite get_empty. 
    inversion H; subst. 
    assert (mi = m'). eapply fonct_mem; eauto. subst. 
    eapply Sbase_mem.

  (* suite *)
 
  apply 
  apply 
  apply 
  apply 
  apply 

  (* call *)  
 
  simpl. simpl in H0. 
  assert (rsi = rs' /\ fri = fr' /\ mi = m'). eapply font_sem; eauto.
  destruct H1. destruct H2. subst. eapply empty_no_move.

  apply 
  apply  
  apply 
  apply 
Qed. 

   *)
    


