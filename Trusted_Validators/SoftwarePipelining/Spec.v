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
Require Import Base. 

Set Implicit Arguments.
Unset Strict Implicit. 

Module Type Eval.

(** *Section 6.3 *)

(** Sets *)
Variable t elt : Set. 

(** Functions *)
Variable alpha : list instruction -> t. 
Variable epsilon : t. 
Variable bang : t -> reg -> elt. Notation "a ! b" := (bang a b) (at level 1). 

(** Predicates *)
Variable eq : t -> t -> Prop. Notation "a ~ b" := (eq a b) (at level 1). 
Variable weq : observables -> t -> t -> Prop. Notation "o : a \ b" := (weq o a b) (at level 1). 
Variable domain : t -> observables -> Prop. 

(** Properties *)
Hypothesis eq_refl : forall t, t ~ t.
Hypothesis eq_sym : forall t t', t ~ t' -> t' ~ t. 
Hypothesis eq_trans : forall t t' t'', t ~ t' -> t' ~ t'' -> t ~ t''. 
Hypothesis weq_reflexivity: forall o s, o : s \ s. 
Hypothesis weq_symmetry: forall o s s', o : s \ s' -> o : s' \ s.
Hypothesis weq_transitivity: forall o s1 s2 s3, o : s1 \ s2 -> o : s2 \ s3 -> o : s1 \ s3.
Hypothesis strong_rewrite_left : forall t t', t ~ t' -> forall o s, o : t \ s -> o : t' \ s.
Hypothesis strong_rewrite_right : forall t t', t ~ t' -> forall o s, o : s \ t -> o : s \ t'.
Hypothesis domain_rewritable: forall o a b, weq o a b -> domain a o -> domain b o.
Hypothesis get_compatibility: forall t t' r, t ~ t' -> t ! r = t' ! r.

(** Section 6.5 *)

(** Function *)
Variable composition : t -> t -> t. Notation "a ^^ b" := (composition a b) (at level 0).
Variable substitution : elt -> elt -> option elt. Notation "a [ b ]" := (substitution a b) (at level 0). 

(** Properties *)
Hypothesis delta_assoc : forall t t' t'', t ^^ (t' ^^ t'') ~ (t ^^ t') ^^ t''.   
Hypothesis delta_compatible_right : forall t t' t'', t ~ t' -> t'' ^^ t ~  t'' ^^ t'.
Hypothesis delta_compatible_left : forall t t' t'', t ~ t' -> t ^^ t'' ~  t' ^^ t''.
Hypothesis init_neutral_left : forall t, epsilon ^^ t ~ t. 
Hypothesis init_neutral_right : forall t, t ^^ epsilon ~ t. 
Hypothesis kernel : (alpha nil) ~ epsilon. 
Hypothesis decomposition : forall l l', (alpha (l ++ l')) ~ ((alpha l) ^^ (alpha l')). 
Hypothesis weak_rewrite_right : forall o t t' t'', o : t' \  t'' -> o : (t ^^ t') \ (t ^^ t'').   
Hypothesis weak_rewrite_left : forall o t t' t'', domain t'' o -> o : t \ t' -> o : (t ^^ t'') \ (t' ^^ t''). 
Hypothesis domain_composable: forall o a b, domain a o -> domain b o -> domain (a ^^ b) o. 

Variable only : elt -> reg -> bool. 

Hypothesis get_decomposition : 
  forall a b r, 
  only (b ! r) r = true ->
  (a ! r) [ (b ! r) ] = Some ((a ^^ b) ! r). 

Hypothesis obs_rewrite_left : forall o t t' t'', o : t \ t' -> o : t \ t'' -> o : t \ t'. 

End Eval. 
