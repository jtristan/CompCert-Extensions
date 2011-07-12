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


(** Label Cleaning : removing of untargetted labels *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Mach. 
Require Import Machabstr. 

Require Import Machtyper. 

Fixpoint is_targetted  (lbl : label) (c : code) {struct c} : bool :=
  match c with
  | Msetstack _ _ _ ::  k => is_targetted lbl k
  | Mgetstack _ _ _ :: k => is_targetted lbl k
  | Mgetparam _ _ _ :: k => is_targetted lbl k
  | Mop _ _ _ :: k => is_targetted lbl k
  | Mload _ _ _ _ :: k => is_targetted lbl k
  | Mstore _ _ _ _ :: k => is_targetted lbl k
  | Malloc :: k => is_targetted lbl k
  | Mcond _ _ lbl' :: k => if peq lbl lbl' then true else is_targetted lbl k
  | Mcall _ _ :: k => is_targetted lbl k
  | Mgoto lbl' :: k => if peq lbl lbl' then true else is_targetted lbl k
  | Mreturn :: k => is_targetted lbl k
  | Mlabel _ :: k => is_targetted lbl k
  | nil => false
end.  
  
Fixpoint remove_labels (c : code) (fn : code) {struct c} : code :=
  match c with
  | (Msetstack _ _ _) as i ::  k => i :: remove_labels k fn
  | (Mgetstack _ _ _) as i :: k => i :: remove_labels k fn
  | (Mgetparam _ _ _) as i :: k => i :: remove_labels k fn
  | (Mop _ _ _) as i :: k => i :: remove_labels k fn
  | (Mload _ _ _ _) as i :: k => i :: remove_labels k fn
  | (Mstore _ _ _ _) as i :: k => i :: remove_labels k fn
  | (Malloc) as i :: k => i :: remove_labels k fn
  | (Mcond _ _ _) as i :: k => i :: remove_labels k fn
  | (Mcall _ _) as i :: k => i :: remove_labels k fn
  | (Mgoto _) as i :: k => i :: remove_labels k fn
  | (Mreturn) as i :: k => i :: remove_labels k fn
  | (Mlabel lbl) as i :: k => if is_targetted lbl fn
                                         then i :: remove_labels k fn
                                         else remove_labels k fn
  | nil => nil
end.

Definition clean_function (f : function) : function  := 
  mkfunction (fn_sig f) (remove_labels (fn_code f) (fn_code f) ) (fn_stacksize f) (fn_framesize f).

Definition clean_fundef (f: fundef) : fundef :=
  transf_fundef clean_function f.

Definition clean_program (p: program) : program :=
  transform_program clean_fundef p.


