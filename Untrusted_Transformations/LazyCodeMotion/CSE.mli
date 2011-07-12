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


open AST
open BinPos
open Coqlib
open Datatypes
open Floats
open Integers
open CList
open Maps
open Op
open RTL
open Registers
open Specif

type valnum = positive

type rhs =
  | Op of operation * valnum list
  | Load of memory_chunk * addressing * valnum list

val rhs_rect :
  (operation -> valnum list -> 'a1) -> (memory_chunk -> addressing -> valnum
  list -> 'a1) -> rhs -> 'a1

val rhs_rec :
  (operation -> valnum list -> 'a1) -> (memory_chunk -> addressing -> valnum
  list -> 'a1) -> rhs -> 'a1

val eq_valnum : valnum -> valnum -> bool

val eq_list_valnum : valnum list -> valnum list -> bool

val eq_rhs : rhs -> rhs -> bool

type numbering = { num_next : valnum; num_eqs : (valnum, rhs) prod list;
                   num_reg : valnum Maps.PTree.t }

val numbering_rect :
  (valnum -> (valnum, rhs) prod list -> valnum Maps.PTree.t -> 'a1) ->
  numbering -> 'a1

val numbering_rec :
  (valnum -> (valnum, rhs) prod list -> valnum Maps.PTree.t -> 'a1) ->
  numbering -> 'a1

val num_next : numbering -> valnum

val num_eqs : numbering -> (valnum, rhs) prod list

val num_reg : numbering -> valnum Maps.PTree.t

val empty_numbering : numbering

val valnum_reg : numbering -> reg -> (numbering, valnum) prod

val valnum_regs : numbering -> reg list -> (numbering, valnum list) prod

val find_valnum_rhs : rhs -> (valnum, rhs) prod list -> valnum option

val add_rhs : numbering -> reg -> rhs -> numbering

val add_op : numbering -> reg -> operation -> reg list -> numbering

val add_load :
  numbering -> reg -> memory_chunk -> addressing -> reg list -> numbering

val add_unknown : numbering -> reg -> numbering

val kill_load_eqs : (valnum, rhs) prod list -> (valnum, rhs) prod list

val kill_loads : numbering -> numbering

val reg_valnum : numbering -> valnum -> reg option

val find_rhs : numbering -> rhs -> reg option

val find_op : numbering -> operation -> reg list -> reg option

val find_load :
  numbering -> memory_chunk -> addressing -> reg list -> reg option

module Numbering : 
 sig 
  type t = numbering
  
  val top : numbering
 end

module Solver : 
 sig 
  module L : 
   sig 
    type t = Numbering.t
    
    val top : t
   end
  
  val fixpoint :
    (positive -> positive list) -> positive -> (positive -> L.t -> L.t) ->
    positive -> L.t Maps.PMap.t option
 end

val transfer : coq_function -> node -> numbering -> numbering

val analyze : coq_function -> numbering Maps.PMap.t

val is_trivial_op : operation -> bool

val transf_instr : numbering -> instruction -> instruction

val transf_code : numbering Maps.PMap.t -> code -> code

val transf_function : coq_function -> code
(*
val transf_fundef : fundef -> fundef

val transf_program : program -> program
*)
