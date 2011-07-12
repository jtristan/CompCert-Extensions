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



val transf_code : RTL.coq_function -> RTL.code
val transf_function : RTL.coq_function -> RTL.coq_function
val transf_fundef :
  RTL.coq_function AST.fundef -> RTL.coq_function AST.fundef
val transf_program :
  (RTL.coq_function AST.fundef, 'a) AST.program ->
  (RTL.coq_function AST.fundef, 'a) AST.program
