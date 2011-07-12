open Basic
open IMS

val mve : G.t -> int NI.t -> int -> 
  (G.V.t option) array * G.V.t list * G.V.t list * int * int * (reg * reg) list * (reg * reg) list
