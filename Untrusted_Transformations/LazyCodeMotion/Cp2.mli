open AST
open BinInt
open BinPos
open Bool
open Datatypes
open Floats
open Integers
open CList
open Maps
open Op
open RTL
open Registers
open Specif

type approx =
  | Novalue
  | Unknown
  | I of int
  | F of float
  | S of ident * int

val approx_rect :
  'a1 -> 'a1 -> (int -> 'a1) -> (float -> 'a1) -> (ident -> int -> 'a1) ->
  approx -> 'a1

val approx_rec :
  'a1 -> 'a1 -> (int -> 'a1) -> (float -> 'a1) -> (ident -> int -> 'a1) ->
  approx -> 'a1

module Approx : 
 sig 
  type t = approx
  
  val eq_dec : t -> t -> bool
  
  val beq : t -> t -> bool
  
  val bot : approx
  
  val top : approx
  
  val lub : t -> t -> t
 end

module D : 
 sig 
  type t_ =
    | Bot_except of Approx.t Maps.PTree.t
    | Top_except of Approx.t Maps.PTree.t
  
  val t__rect :
    (Approx.t Maps.PTree.t -> 'a1) -> (Approx.t Maps.PTree.t -> 'a1) -> t_ ->
    'a1
  
  val t__rec :
    (Approx.t Maps.PTree.t -> 'a1) -> (Approx.t Maps.PTree.t -> 'a1) -> t_ ->
    'a1
  
  type t = t_
  
  val get : positive -> t -> Approx.t
  
  val set : positive -> Approx.t -> t -> t
  
  val beq : t -> t -> bool
  
  val bot : t_
  
  val top : t_
  
  val lub : t -> t -> t
  
  val map : (positive -> Approx.t -> Approx.t) -> t -> t
 end

type eval_static_condition_cases =
  | Coq_eval_static_condition_case1 of comparison * int * int
  | Coq_eval_static_condition_case2 of comparison * int * int
  | Coq_eval_static_condition_case3 of comparison * int * int
  | Coq_eval_static_condition_case4 of comparison * int * int
  | Coq_eval_static_condition_case5 of comparison * float * float
  | Coq_eval_static_condition_case6 of comparison * float * float
  | Coq_eval_static_condition_case7 of int * int
  | Coq_eval_static_condition_case8 of int * int
  | Coq_eval_static_condition_default of condition * approx list

val eval_static_condition_cases_rect :
  (comparison -> int -> int -> 'a1) -> (comparison -> int -> int -> 'a1) ->
  (comparison -> int -> int -> 'a1) -> (comparison -> int -> int -> 'a1) ->
  (comparison -> float -> float -> 'a1) -> (comparison -> float -> float ->
  'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (condition -> approx
  list -> 'a1) -> condition -> approx list -> eval_static_condition_cases ->
  'a1

val eval_static_condition_cases_rec :
  (comparison -> int -> int -> 'a1) -> (comparison -> int -> int -> 'a1) ->
  (comparison -> int -> int -> 'a1) -> (comparison -> int -> int -> 'a1) ->
  (comparison -> float -> float -> 'a1) -> (comparison -> float -> float ->
  'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (condition -> approx
  list -> 'a1) -> condition -> approx list -> eval_static_condition_cases ->
  'a1

val eval_static_condition_match :
  condition -> approx list -> eval_static_condition_cases

val eval_static_condition : condition -> approx list -> bool option

type eval_static_operation_cases =
  | Coq_eval_static_operation_case1 of approx
  | Coq_eval_static_operation_case2 of int
  | Coq_eval_static_operation_case3 of float
  | Coq_eval_static_operation_case4 of ident * int
  | Coq_eval_static_operation_case6 of int
  | Coq_eval_static_operation_case7 of int
  | Coq_eval_static_operation_case8 of int * int
  | Coq_eval_static_operation_case9 of ident * int * int
  | Coq_eval_static_operation_case11 of int * int
  | Coq_eval_static_operation_case12 of int * ident * int
  | Coq_eval_static_operation_case13 of int * int
  | Coq_eval_static_operation_case14 of ident * int * int
  | Coq_eval_static_operation_case15 of int * int
  | Coq_eval_static_operation_case16 of int * int
  | Coq_eval_static_operation_case17 of int * int
  | Coq_eval_static_operation_case18 of int * int
  | Coq_eval_static_operation_case19 of int * int
  | Coq_eval_static_operation_case20 of int * int
  | Coq_eval_static_operation_case21 of int * int
  | Coq_eval_static_operation_case22 of int * int
  | Coq_eval_static_operation_case23 of int * int
  | Coq_eval_static_operation_case24 of int * int
  | Coq_eval_static_operation_case25 of int * int
  | Coq_eval_static_operation_case26 of int * int
  | Coq_eval_static_operation_case27 of int * int
  | Coq_eval_static_operation_case28 of int * int
  | Coq_eval_static_operation_case29 of int * int
  | Coq_eval_static_operation_case30 of int * int
  | Coq_eval_static_operation_case31 of int * int
  | Coq_eval_static_operation_case32 of int * int
  | Coq_eval_static_operation_case33 of int * int
  | Coq_eval_static_operation_case34 of int * int * int
  | Coq_eval_static_operation_case35 of float
  | Coq_eval_static_operation_case36 of float
  | Coq_eval_static_operation_case37 of float * float
  | Coq_eval_static_operation_case38 of float * float
  | Coq_eval_static_operation_case39 of float * float
  | Coq_eval_static_operation_case40 of float * float
  | Coq_eval_static_operation_case41 of float * float * float
  | Coq_eval_static_operation_case42 of float * float * float
  | Coq_eval_static_operation_case43 of float
  | Coq_eval_static_operation_case44 of float
  | Coq_eval_static_operation_case45 of int
  | Coq_eval_static_operation_case46 of int
  | Coq_eval_static_operation_case47 of condition * approx list
  | Coq_eval_static_operation_case48 of int
  | Coq_eval_static_operation_case49 of int
  | Coq_eval_static_operation_default of operation * approx list

val eval_static_operation_cases_rect :
  (approx -> 'a1) -> (int -> 'a1) -> (float -> 'a1) -> (ident -> int -> 'a1)
  -> (int -> 'a1) -> (int -> 'a1) -> (int -> int -> 'a1) -> (ident -> int ->
  int -> 'a1) -> (int -> int -> 'a1) -> (int -> ident -> int -> 'a1) -> (int
  -> int -> 'a1) -> (ident -> int -> int -> 'a1) -> (int -> int -> 'a1) ->
  (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int
  -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int
  -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int ->
  'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1)
  -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) ->
  (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int -> 'a1) ->
  (float -> 'a1) -> (float -> 'a1) -> (float -> float -> 'a1) -> (float ->
  float -> 'a1) -> (float -> float -> 'a1) -> (float -> float -> 'a1) ->
  (float -> float -> float -> 'a1) -> (float -> float -> float -> 'a1) ->
  (float -> 'a1) -> (float -> 'a1) -> (int -> 'a1) -> (int -> 'a1) ->
  (condition -> approx list -> 'a1) -> (int -> 'a1) -> (int -> 'a1) ->
  (operation -> approx list -> 'a1) -> operation -> approx list ->
  eval_static_operation_cases -> 'a1

val eval_static_operation_cases_rec :
  (approx -> 'a1) -> (int -> 'a1) -> (float -> 'a1) -> (ident -> int -> 'a1)
  -> (int -> 'a1) -> (int -> 'a1) -> (int -> int -> 'a1) -> (ident -> int ->
  int -> 'a1) -> (int -> int -> 'a1) -> (int -> ident -> int -> 'a1) -> (int
  -> int -> 'a1) -> (ident -> int -> int -> 'a1) -> (int -> int -> 'a1) ->
  (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int
  -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int
  -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int ->
  'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1)
  -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) ->
  (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int -> 'a1) ->
  (float -> 'a1) -> (float -> 'a1) -> (float -> float -> 'a1) -> (float ->
  float -> 'a1) -> (float -> float -> 'a1) -> (float -> float -> 'a1) ->
  (float -> float -> float -> 'a1) -> (float -> float -> float -> 'a1) ->
  (float -> 'a1) -> (float -> 'a1) -> (int -> 'a1) -> (int -> 'a1) ->
  (condition -> approx list -> 'a1) -> (int -> 'a1) -> (int -> 'a1) ->
  (operation -> approx list -> 'a1) -> operation -> approx list ->
  eval_static_operation_cases -> 'a1

val eval_static_operation_match :
  operation -> approx list -> eval_static_operation_cases

val eval_static_operation : operation -> approx list -> approx

val approx_regs : reg list -> D.t -> Approx.t list

val transfer : coq_function -> node -> D.t -> D.t

module DS : 
 sig 
  module L : 
   sig 
    type t = D.t
    
    val beq : t -> t -> bool
    
    val bot : t
    
    val lub : t -> t -> t
   end
  
  val fixpoint :
    (positive -> positive list) -> positive -> (positive -> L.t -> L.t) ->
    (positive, L.t) prod list -> L.t Maps.PMap.t option
 end

val analyze : coq_function -> D.t Maps.PMap.t

val intval : D.t -> reg -> int option

type cond_strength_reduction_cases =
  | Coq_csr_case1 of comparison * reg * reg
  | Coq_csr_case2 of comparison * reg * reg
  | Coq_csr_default of condition * reg list

val cond_strength_reduction_cases_rect :
  (comparison -> reg -> reg -> 'a1) -> (comparison -> reg -> reg -> 'a1) ->
  (condition -> reg list -> 'a1) -> condition -> reg list ->
  cond_strength_reduction_cases -> 'a1

val cond_strength_reduction_cases_rec :
  (comparison -> reg -> reg -> 'a1) -> (comparison -> reg -> reg -> 'a1) ->
  (condition -> reg list -> 'a1) -> condition -> reg list ->
  cond_strength_reduction_cases -> 'a1

val cond_strength_reduction_match :
  condition -> reg list -> cond_strength_reduction_cases

val cond_strength_reduction :
  D.t -> condition -> reg list -> (condition, reg list) prod

val make_addimm : int -> reg -> (operation, reg list) prod

val make_shlimm : int -> reg -> (operation, reg list) prod

val make_shrimm : int -> reg -> (operation, reg list) prod

val make_shruimm : int -> reg -> (operation, reg list) prod

val make_mulimm : int -> reg -> (operation, reg list) prod

val make_andimm : int -> reg -> (operation, reg list) prod

val make_orimm : int -> reg -> (operation, reg list) prod

val make_xorimm : int -> reg -> (operation, reg list) prod

type op_strength_reduction_cases =
  | Coq_op_strength_reduction_case1 of reg * reg
  | Coq_op_strength_reduction_case2 of reg * reg
  | Coq_op_strength_reduction_case3 of reg * reg
  | Coq_op_strength_reduction_case4 of reg * reg
  | Coq_op_strength_reduction_case5 of reg * reg
  | Coq_op_strength_reduction_case6 of reg * reg
  | Coq_op_strength_reduction_case7 of reg * reg
  | Coq_op_strength_reduction_case8 of reg * reg
  | Coq_op_strength_reduction_case9 of reg * reg
  | Coq_op_strength_reduction_case10 of reg * reg
  | Coq_op_strength_reduction_case11 of reg * reg
  | Coq_op_strength_reduction_case12 of condition * reg list
  | Coq_op_strength_reduction_default of operation * reg list

val op_strength_reduction_cases_rect :
  (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg
  -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg
  -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg ->
  'a1) -> (reg -> reg -> 'a1) -> (condition -> reg list -> 'a1) -> (operation
  -> reg list -> 'a1) -> operation -> reg list -> op_strength_reduction_cases
  -> 'a1

val op_strength_reduction_cases_rec :
  (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg
  -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg
  -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg -> 'a1) -> (reg -> reg ->
  'a1) -> (reg -> reg -> 'a1) -> (condition -> reg list -> 'a1) -> (operation
  -> reg list -> 'a1) -> operation -> reg list -> op_strength_reduction_cases
  -> 'a1

val op_strength_reduction_match :
  operation -> reg list -> op_strength_reduction_cases

val op_strength_reduction :
  D.t -> operation -> reg list -> (operation, reg list) prod

type addr_strength_reduction_cases =
  | Coq_addr_strength_reduction_case1 of reg * reg
  | Coq_addr_strength_reduction_case2 of ident * int * reg
  | Coq_addr_strength_reduction_case3 of int * reg
  | Coq_addr_strength_reduction_default of addressing * reg list

val addr_strength_reduction_cases_rect :
  (reg -> reg -> 'a1) -> (ident -> int -> reg -> 'a1) -> (int -> reg -> 'a1)
  -> (addressing -> reg list -> 'a1) -> addressing -> reg list ->
  addr_strength_reduction_cases -> 'a1

val addr_strength_reduction_cases_rec :
  (reg -> reg -> 'a1) -> (ident -> int -> reg -> 'a1) -> (int -> reg -> 'a1)
  -> (addressing -> reg list -> 'a1) -> addressing -> reg list ->
  addr_strength_reduction_cases -> 'a1

val addr_strength_reduction_match :
  addressing -> reg list -> addr_strength_reduction_cases

val addr_strength_reduction :
  D.t -> addressing -> reg list -> (addressing, reg list) prod

val transf_ros : D.t -> (reg, ident) sum -> (reg, ident) sum

val transf_instr : D.t -> instruction -> instruction

val transf_code : D.t Maps.PMap.t -> code -> code

val transf_function : coq_function -> code
(*
val transf_fundef : fundef -> fundef

val transf_program : program -> program
*)
