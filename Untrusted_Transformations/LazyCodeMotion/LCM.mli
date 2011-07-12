
val transf_code : RTL.coq_function -> RTL.code
val transf_function : RTL.coq_function -> RTL.coq_function
val transf_fundef :
  RTL.coq_function AST.fundef -> RTL.coq_function AST.fundef
val transf_program :
  (RTL.coq_function AST.fundef, 'a) AST.program ->
  (RTL.coq_function AST.fundef, 'a) AST.program
