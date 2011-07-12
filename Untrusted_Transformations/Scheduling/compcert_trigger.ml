

(* Chaque optimisation a un entier i, trigerred i indique si elle
   est enclenchee ou non *)

let triggered i =
  let v = try Unix.getenv "COMPCERTRUNPARAM" with Not_found -> "0" in
  let v = String.concat "" ["0"; v] in
  let v = int_of_string v in 
  let v = Int32.of_int v in
  let v = Int32.shift_right_logical v i in
  let v = Int32.logand v Int32.one in
  v = Int32.one
  

