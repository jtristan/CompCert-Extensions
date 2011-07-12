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
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import FSets.
Require Import FSetWeakInterface. 
Require Import FSetWeakList.  
Require Import FSetWeakFacts. 
Require Import FSetWeakProperties. 
Require Import DecidableType. 
Require Import Setoid. 
Require Import RTL. 
 
Inductive operation : Set :=
  | Ointconst: int -> operation         (**r [rd] is set to the given integer constant *)
  | Ofloatconst: float -> operation     (**r [rd] is set to the given float constant *)
  | Oaddrsymbol: ident -> int -> operation (**r [rd] is set to the the address of the symbol plus the offset *)
  | Oaddrstack: int -> operation        (**r [rd] is set to the stack pointer plus the given offset *)
(*c Integer arithmetic: *)
  | Ocast8signed: operation             (**r [rd] is 8-bit sign extension of [r1] *)
  | Ocast8unsigned: operation           (**r [rd] is 8-bit zero extension of [r1] *)
  | Ocast16signed: operation            (**r [rd] is 16-bit sign extension of [r1] *)
  | Ocast16unsigned: operation          (**r [rd] is 16-bit zero extension of [r1] *)
  | Oadd: operation                     (**r [rd = r1 + r2] *)
  | Oaddimm: int -> operation           (**r [rd = r1 + n] *)
  | Osub: operation                     (**r [rd = r1 - r2] *)
  | Osubimm: int -> operation           (**r [rd = n - r1] *)
  | Omul: operation                     (**r [rd = r1 * r2] *)
  | Omulimm: int -> operation           (**r [rd = r1 * n] *)
  | Odiv: operation                     (**r [rd = r1 / r2] (signed) *)
  | Odivu: operation                    (**r [rd = r1 / r2] (unsigned) *)
  | Oand: operation                     (**r [rd = r1 & r2] *)
  | Oandimm: int -> operation           (**r [rd = r1 & n] *)
  | Oor: operation                      (**r [rd = r1 | r2] *)
  | Oorimm: int -> operation            (**r [rd = r1 | n] *)
  | Oxor: operation                     (**r [rd = r1 ^ r2] *)
  | Oxorimm: int -> operation           (**r [rd = r1 ^ n] *)
  | Onand: operation                    (**r [rd = ~(r1 & r2)] *)
  | Onor: operation                     (**r [rd = ~(r1 | r2)] *)
  | Onxor: operation                    (**r [rd = ~(r1 ^ r2)] *)
  | Oshl: operation                     (**r [rd = r1 << r2] *)
  | Oshr: operation                     (**r [rd = r1 >> r2] (signed) *)
  | Oshrimm: int -> operation           (**r [rd = r1 >> n] (signed) *)
  | Oshrximm: int -> operation          (**r [rd = r1 / 2^n] (signed) *)
  | Oshru: operation                    (**r [rd = r1 >> r2] (unsigned) *)
  | Orolm: int -> int -> operation      (**r rotate left and mask *)
(*c Floating-point arithmetic: *)
  | Onegf: operation                    (**r [rd = - r1] *)
  | Oabsf: operation                    (**r [rd = abs(r1)] *)
  | Oaddf: operation                    (**r [rd = r1 + r2] *)
  | Osubf: operation                    (**r [rd = r1 - r2] *)
  | Omulf: operation                    (**r [rd = r1 * r2] *)
  | Odivf: operation                    (**r [rd = r1 / r2] *)
  | Omuladdf: operation                 (**r [rd = r1 * r2 + r3] *)
  | Omulsubf: operation                 (**r [rd = r1 * r2 - r3] *)
  | Osingleoffloat: operation           (**r [rd] is [r1] truncated to single-precision float *)
(*c Conversions between int and float: *)
  | Ointoffloat: operation              (**r [rd = signed_int_of_float(r1)] *)
  | Ointuoffloat: operation             (**r [rd = unsigned_int_of_float(r1)] *)
  | Ofloatofint: operation              (**r [rd = float_of_signed_int(r1)] *)
  | Ofloatofintu: operation.             (**r [rd = float_of_unsigned_int(r1)] *) 

Inductive instruction : Set :=
  | Imove : reg -> reg -> instruction
  | Iop: operation -> list reg -> reg -> instruction
  | Iload: memory_chunk -> addressing -> list reg -> reg -> instruction
  | Istore: memory_chunk -> addressing -> list reg -> reg -> instruction. 

Record state : Set := mkst {
  stack: list stackframe;
  c: code;            
  sp: val;                    
  rs: regset;             
  mm: Mem.mem
}.               

Definition observables := list reg. 

Inductive state_eq : observables -> state -> state -> Prop :=
  | Steq_intro: 
    forall o s s', (forall x, In x o -> s.(rs) # x = s'.(rs) # x) -> s.(mm) = s'.(mm) -> 
	s.(stack) = s'.(stack) -> s.(sp) = s'.(sp) ->
	state_eq o s s'. 

Lemma steq_relf:
  forall o s, state_eq o s s. 
Proof.
  intros. 
  eapply Steq_intro; eauto. 
Qed. 

Lemma steq_sym:
  forall o s s', state_eq o s s' -> state_eq o s' s.
Proof. 
  intros. 
  inversion H; subst. 
  eapply Steq_intro; eauto.
  intros. 
  symmetry. eapply H0; eauto.
Qed. 

Lemma steq_trans:
  forall o s1 s2 s3, state_eq o s1 s2 -> state_eq o s2 s3 -> state_eq o s1 s3. 
Proof.
  intros. 
  inversion H; subst. 
  inversion H0; subst. 
  eapply Steq_intro; eauto; try congruence. 
  intros. 
  generalize (H1 _ H9); intro. 
  generalize (H5 _ H9); intro. 
  congruence. 
Qed.  
  
Parameter oo : operation -> option Op.operation. 

Definition eval_operation
    (F: Set) (genv: Genv.t F) (sp: val)
    (op: operation) (vl: list val) : option val :=
  match oo (op) with 
  | None => None
  | Some op => Op.eval_operation genv sp op vl Mem.empty
  end. 

Inductive lsteps : genv -> list instruction -> state -> state -> Prop :=
  | exec_start:
     forall ge s,
     lsteps ge nil s s
  | exec_Imove:
      forall ge l l' stack c sp rs m arg res s s' s'',
      l = (Imove arg res) :: l' ->
      s = mkst stack c sp rs m ->
      s' = mkst stack c sp (rs#res <- (rs#arg)) m ->
      lsteps ge l' s' s'' ->
      lsteps ge l s s'' 
  | exec_Iop:
      forall ge l l' stack c sp rs m op args res v s s' s'',
      l = (Iop op args res) :: l' ->
      eval_operation _ ge sp op rs##args = Some v ->
      s = mkst stack c sp rs m ->
      s' = mkst stack c sp (rs#res <- v) m ->
      lsteps ge l' s' s'' ->
      lsteps ge l s s'' 
  | exec_Iload:
      forall ge l l' stack c sp rs m chunk addr args dst a v s s' s'',
      l = (Iload chunk addr args dst) :: l' ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      s = mkst stack c sp rs m ->
      s' = mkst stack c sp (rs#dst <- v) m ->
      lsteps ge l' s' s'' ->
      lsteps ge l s s''
  | exec_Istore:
      forall ge l l' stack c sp rs m chunk addr args src a m' s s' s'',
      l = (Istore chunk addr args src) :: l' ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      s = mkst stack c sp rs m ->
      s' = mkst stack c sp rs m' ->
      lsteps ge l' s' s'' ->
      lsteps ge l s s''.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type Eval.

Variable t : Set. 
Variable delta : t -> t -> t.
Notation "a ^^ b" := (delta a b) (at level 0).
Variable I : t. 
Variable evaluate : list instruction -> t. 

(* Equivalence forte *)

Variable eq : t -> t -> Prop. 
Notation "a ~ b" := (eq a b) (at level 1). 
Hypothesis eq_refl : forall t, t ~ t.
Hypothesis eq_sym : forall t t', t ~ t' -> t' ~ t. 
Hypothesis eq_trans : forall t t' t'', t ~ t' -> t' ~ t'' -> t ~ t''. 
Add Relation t eq reflexivity proved by (@eq_refl) symmetry proved by (@eq_sym) transitivity proved by (@eq_trans) as sym_eq. 

Hypothesis delta_assoc : forall t t' t'', t ^^ (t' ^^ t'') ~ (t ^^ t') ^^ t''.   
Hypothesis delta_compatible_right : forall t t' t'', t ~ t' -> t'' ^^ t ~  t'' ^^ t'.
Hypothesis delta_compatible_left : forall t t' t'', t ~ t' -> t ^^ t'' ~  t' ^^ t''.

Hypothesis init_neutral_left : forall t, I ^^ t ~ t. 
Hypothesis init_neutral_right : forall t, t ^^ I ~ t. 

Hypothesis kernel : (evaluate nil) ~ I. 
Hypothesis decomposition : forall l l', (evaluate (l ++ l')) ~ ((evaluate l) ^^ (evaluate l')). 

(* Equivalence observable *)

Variable weq : observables -> t -> t -> Prop.
Notation "o : a \ b" := (weq o a b) (at level 1). 

Hypothesis weq_reflexivity: forall o s, o : s \ s. 
Hypothesis weq_symmetry: forall o s s', o : s \ s' -> o : s' \ s.
Hypothesis weq_transitivity: forall o s1 s2 s3, o : s1 \ s2 -> o : s2 \ s3 -> o : s1 \ s3.

Hypothesis strong_rewrite_left : forall t t', t ~ t' -> forall o s, o : t \ s -> o : t' \ s.
Hypothesis strong_rewrite_right : forall t t', t ~ t' -> forall o s, o : s \ t -> o : s \ t'.
Hypothesis obs_rewrite_left : forall o t t' t'', o : t \ t' -> o : t \ t'' -> o : t \ t'. 

Variable dec : observables -> t -> t -> bool. 
Hypothesis dec_correct : forall o t t', dec o t t' = true -> weq o t t'.  

Variable domain : t -> observables -> Prop. 
Hypothesis domain_composable: forall o a b, domain a o -> domain b o -> domain (a ^^ b) o. 
Hypothesis domain_rewritable: forall o a b, weq o a b -> domain a o -> domain b o. 

Variable domain_dec : t -> observables -> bool. 
Hypothesis domain_dec_correct : forall o t, domain_dec t o = true -> domain t o. 

Hypothesis correct : forall o l l', 
   o : (evaluate l) \ (evaluate l') -> domain (evaluate l') o ->
   forall ge s t s', state_eq o s t -> 
   lsteps ge l s s' -> 
   exists t', lsteps ge l' t t' /\ state_eq o s' t'. 

(* Partie 3 : Observation de registres, traitement du controle *)
 
Variable elt : Set.

Variable dec_elt : elt -> elt -> bool.
Hypothesis dec_elt_correct : forall e e', dec_elt e e' = true -> e = e'. 

Variable get : t -> reg -> elt.
Variable only : elt -> reg -> bool. 
Variable delta_mini : elt -> elt -> option elt. 

Hypothesis get_compatibility: forall t t' r, t ~ t' -> get t r = get t' r.
Hypothesis get_decomposition : 
  forall a b r, 
  only (get b r) r = true ->
  delta_mini (get a r) (get b r) = Some (get (a ^^ b) r). 

Hint Resolve eq_refl eq_sym eq_trans delta_assoc delta_compatible_right delta_compatible_left init_neutral_left init_neutral_right kernel
	decomposition dec_correct strong_rewrite_left strong_rewrite_right correct get_compatibility get_decomposition. 

End Eval. 

 






 

      