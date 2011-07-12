

(* Chaque optimisation a un entier i, trigerred i indique si elle
   est enclenchee ou non *)

let triggered i =
  let s = try Unix.getenv "COMPCERTRUNPARAM" with Not_found -> "0" in
  String.get s (i - 1) = '1' 

(*
let triggered i =
  let v = try Unix.getenv "COMPCERTRUNPARAM" with Not_found -> "0" in
  let v = String.concat "" ["0"; v] in
  let v = int_of_string v in 
  let v = Int32.of_int v in
  let v = Int32.shift_right_logical v i in
  let v = Int32.logand v Int32.one in
  v = Int32.one
*)  

(* fonction d evaluation du temps d execution *)

let time msg f arg =
  let rec loop t0 count =
    let res = f arg in
    let t1 = (Unix.times()).Unix.tms_utime in
    if t1 -. t0 >= 1.0 then begin
      Printf.printf "%s: %f\n" msg ((t1 -. t0) /. float count);
      res
    end else
      loop t0 (count + 1)
  in loop (Unix.times()).Unix.tms_utime 1
