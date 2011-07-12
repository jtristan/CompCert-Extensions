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

Inductive info : Set :=
  | Found
  | NotFound
  | Visited
  | Dunno.

Definition args_of (a : approx) : list reg :=
  match a with
  | Op _ l => l
  | Load _ _ l => l
  | _ => nil
  end.  

Definition sensible (a : approx) (r : reg) : bool :=
  let args := args_of a in
  mem r args. 

Definition memory_sensible (a : approx) : bool :=
  match a with
  | Load _ _ _ => true
  | Op o l => match o with Ocmp _ => true | _ => false end
  | _ => false
  end. 

Section ANT. 

Variable cfg : RTL.code. 
Variable a : approx. 

Definition info_map : Set := PTree.t info. 

Fixpoint ant_checker (pc : node) (st : info_map) (cmpt : nat) {struct cmpt} : (info_map * bool) :=
  match cmpt with 
  | O => (st,false)
  | S n =>
      match st!pc with
      | Some (Found) =>  (st,true)
      | Some (NotFound) => (st,false)
      | Some (Visited) => (st,false)
      | Some (Dunno) => 
          match cfg!pc with
          | Some (Ireturn _) => let st := (PTree.set pc NotFound st) in (st,false)
          | Some (Itailcall _ _ _) => let st := (PTree.set pc NotFound st) in (st,false)
          | Some (Icond _ _ s1 s2) =>
                     let st := (PTree.set pc Visited st) in
                     let (st',b1) := ant_checker s1 st n in
                     let (st'',b2) := ant_checker s2 st' n in
                     if b1 && b2 then let st''' := (PTree.set pc Found st'') in (st''',true) 
                                         else let st''' := (PTree.set pc NotFound st'') in (st''',false)
         | Some (Inop s) => 
                     let st := (PTree.set pc Visited st) in
                     let (st',b) := ant_checker s st n in
                     if b then let st'' := (PTree.set pc Found st') in (st'',true)
                           else let st'' := (PTree.set pc NotFound st') in (st'',false)
         | Some (Icall _ _ _ r s) => 
                     let st := (PTree.set pc NotFound st) in (st,false)
         | Some (Ialloc _ r s) => 
                     if memory_sensible a then let st := (PTree.set pc NotFound st) in (st,false)
                     else
                     if sensible a r then let st := (PTree.set pc NotFound st) in (st,false)
                     else
                     let st := (PTree.set pc Visited st) in
                     let (st',b) := ant_checker s st n in
                     if b then let st'' := (PTree.set pc Found st') in (st'',true)
                           else let st'' := (PTree.set pc NotFound st') in (st'',false)
         | Some (Istore _ _ _ _ s) => 
                     if memory_sensible a then let st := (PTree.set pc NotFound st) in (st,false)
                     else
                     let st := (PTree.set pc Visited st) in
                     let (st',b) := ant_checker s st n in
                     if b then let st'' := (PTree.set pc Found st') in (st'',true)
                           else let st'' := (PTree.set pc NotFound st') in (st'',false)
         | Some (Iop op args r s) => 
                     if sensible a r then let st := (PTree.set pc NotFound st) in (st,false)
                     else
                     if Approx.beq a (Op op args) then let st := (PTree.set pc Found st) in (st,true)
                         else
                         let st := (PTree.set pc Visited st) in
                         let (st',b) := ant_checker s st n in
                         if b then let st'' := (PTree.set pc Found st') in (st'',true)
                               else let st'' := (PTree.set pc NotFound st') in (st'',false)
         | Some (Iload chk addr args r s) =>
                     if sensible a r then let st := (PTree.set pc NotFound st) in (st,false)
                     else
                     if Approx.beq a (Load chk addr args) then let st := (PTree.set pc Found st) in (st,true)
                         else
                         let st := (PTree.set pc Visited st) in
                         let (st',b) := ant_checker s st n in
                         if b then let st'' := (PTree.set pc Found st') in (st'',true)
                               else let st'' := (PTree.set pc NotFound st') in (st'',false)
         | None => (st,false)
         end
      | None => (st,false)
      end 
   end. 
  
End ANT.