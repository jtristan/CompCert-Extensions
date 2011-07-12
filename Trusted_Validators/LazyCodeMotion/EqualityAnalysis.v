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
Require Import Lattice.
Require Import Kildall.
Require Import DecidableType. 
Require Import FSetWeakInterface. 
Require Import FSetWeakFacts. 
Require Import FSetWeakProperties. 
Require Import FSetWeakList. 
Require Import Errors. 
Require Import Utilities. 

Module D := LPMap Approx.  

Definition transp (a : approx) (res : reg) : approx :=
  match a with
  | Novalue => Novalue 
  | Unknown => Unknown
  | Op op lr => if mem res lr then Unknown else Op op lr
  | Load chk addr lr => if mem res lr then Unknown else Load chk addr lr
  end.

Definition transp_mem (a : approx) : approx :=
  match a with
  | Novalue => Novalue 
  | Unknown => Unknown
  | Op op lr => match op with | Ocmp _ => Unknown | _ => Op op lr end (* l instruction Ocmp lit la memoire *)
  | Load chk addr lr => Unknown
  end.

Definition transfer (f: function) (pc: node) (before: D.t) :=
  match f.(fn_code)!pc with
  | None => before
  | Some i =>
      match i with
      | Inop s =>
          before
      | Iop op args res s =>
          let a := if mem res args then Unknown else Op op args in
          let transparent := D.map (fun i a => transp a res) before in
          D.set res a transparent
      | Iload chunk addr args dst s =>
          let a := if mem dst args then Unknown else Load chunk addr args in
          let transparent := D.map (fun i a => transp a dst) before in
          D.set dst a transparent
      | Istore chunk addr args src s =>
          D.map (fun i a => transp_mem a) before
      | Icall sig ros args res s => 
          let before := D.map (fun i a => transp a res) before in
          let transparent := D.map (fun i a => transp_mem a) before in
          D.set res Unknown transparent
      | Itailcall sig ros args =>
          before
      | Ialloc arg res s =>
          let before := D.map (fun i a => transp a res) before in
          let transparent := D.map (fun i a => transp_mem a) before in
          D.set res Unknown transparent
      | Icond cond args ifso ifnot =>
          before
      | Ireturn optarg =>
          before
      end
  end.

Module DS := Dataflow_Solver(D)(NodeSetForward).

Definition analyze (f: RTL.function): PMap.t D.t :=
  match DS.fixpoint (successors f) f.(fn_nextpc) (transfer f) 
                    ((f.(fn_entrypoint), D.top) :: nil) with
  | None => PMap.init D.top
  | Some res => res
  end.