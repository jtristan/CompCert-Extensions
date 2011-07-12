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

Variable eq : t -> t -> Prop. 
Notation "a ~ b" := (eq a b) (at level 1). 
Hypothesis eq_refl : forall t, t ~ t.
Hypothesis eq_sym : forall t t', t ~ t' -> t' ~ t. 
Hypothesis eq_trans : forall t t' t'', t ~ t' -> t' ~ t'' -> t ~ t''. 
Add Relation t eq reflexivity proved by (@eq_refl) symmetry proved by (@eq_sym) transitivity proved by (@eq_trans) as sym_eq. 

Variable delta : t -> t -> t.
Notation "a ^^ b" := (delta a b) (at level 0).
Hypothesis delta_assoc : forall t t' t'', t ^^ (t' ^^ t'') ~ (t ^^ t') ^^ t''.   
Hypothesis delta_compatible_right : forall t t' t'', t ~ t' -> t'' ^^ t ~  t'' ^^ t'.
Hypothesis delta_compatible_left : forall t t' t'', t ~ t' -> t ^^ t'' ~  t' ^^ t''.

Variable I : t. 
Hypothesis init_neutral_left : forall t, I ^^ t ~ t. 
Hypothesis init_neutral_right : forall t, t ^^ I ~ t. 

Variable evaluate : list instruction -> t. 
Hypothesis kernel : (evaluate nil) ~ I. 
Hypothesis decomposition : forall l l', (evaluate (l ++ l')) ~ ((evaluate l) ^^ (evaluate l')). 

Variable dec : t -> t -> bool. 
Hypothesis dec_correct : forall t t', dec t t' = true -> t ~ t'.

Hypothesis correct : forall l l', (evaluate l) ~ (evaluate l') -> forall ge s s', (lsteps ge l s s' <-> lsteps ge l' s s'). 
 
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
	decomposition dec_correct correct get_compatibility get_decomposition. 

End Eval. 

 






 

      