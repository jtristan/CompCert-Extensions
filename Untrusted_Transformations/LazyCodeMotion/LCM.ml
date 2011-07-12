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
open Analysis
open BinPos
open Datatypes
open CList
open Maps
open Op
open RTL
open Registers

let debug = false

(** val used_reg : instruction -> reg list **)

let used_reg = function
  | Inop s -> Coq_nil
  | Iop (op, lr, r, s) -> Coq_cons (r, Coq_nil)
  | Iload (mc, ad, lr, r, s) -> Coq_cons (r, Coq_nil)
  | Istore (mc, ad, lr, r, s) -> Coq_cons (r, Coq_nil)
  | Icall (si, ri, lr, r, s) -> Coq_cons (r, Coq_nil)
  | Itailcall (si, ri, lr) -> Coq_nil
  | Ialloc (r1, r2, s) -> Coq_cons (r2, Coq_nil)
  | Icond (c, lr, s1, s2) -> Coq_nil
  | Ireturn or0 -> Coq_nil

(** val max : positive -> positive -> positive **)

let max x y =
  match coq_Pcompare x y Eq with
    | Eq -> x
    | Lt -> y
    | Gt -> x

(** val rewrite_instr : instruction -> reg -> instruction **)

let rewrite_instr i t0 =
  match i with
    | Inop n -> i
    | Iop (op, lr, r, s) -> Iop (Omove, (Coq_cons (t0, Coq_nil)), r, s)
    | Iload (mc, ad, lr, r, s) -> Iop (Omove, (Coq_cons (t0, Coq_nil)), r, s)
    | Istore (m, a, l, r, n) -> i
    | Icall (s, s0, l, r, n) -> i
    | Itailcall (s, s0, l) -> i
    | Ialloc (r, r0, n) -> i
    | Icond (c, l, n, n0) -> i
    | Ireturn o -> i

(** val new_def : instruction -> reg -> instruction **)
(*
let new_def i t0 opt_point =
  match i with
    | Inop n -> i
    | Iop (op, lr, r, s) -> Iop (op, lr, t0, opt_point)
    | Iload (mc, ad, lr, r, s) -> Iload (mc, ad, lr, t0, opt_point)
    | Istore (m, a, l, r, n) -> i
    | Icall (s, s0, l, r, n) -> i
    | Itailcall (s, s0, l) -> i
    | Ialloc (r, r0, n) -> i
    | Icond (c, l, n, n0) -> i
    | Ireturn o -> i
*)

let new_def i t0 opt_point =
  match i with
    | Op (op, lr) -> Iop (op, lr, t0, opt_point)
    | Load (mc, ad, lr) -> Iload (mc, ad, lr, t0, opt_point)
	

let relink g hijacked hijacker =
  let cmp = fun node -> if node = hijacked then hijacker else node in
  let relink_one = function
    | Inop n -> Inop (cmp n)
    | Iop (op, lr, r, s) -> Iop (op, lr, r, cmp s)
    | Iload (mc, ad, lr, r, s) -> Iload (mc, ad, lr, r, cmp s)
    | Istore (m, a, l, r, n) -> Istore (m, a, l, r, cmp n)
    | Icall (s, s0, l, r, n) -> Icall (s, s0, l, r, cmp n)
    | Itailcall (s, s0, l) -> Itailcall (s, s0, l)
    | Ialloc (r, r0, n) -> Ialloc (r, r0, cmp n)
    | Icond (c, l, n, n0) -> Icond (c, l, cmp n, cmp n0)
    | Ireturn o -> Ireturn o in     
    
  Maps.PTree.map (fun n i -> relink_one i) g

let print_pos p =
  print_int (Int32.to_int (Camlcoq.camlint_of_positive p))
(** val apply_optimal : coq_function -> (node -> Analysis.Es.t) -> expression
                        -> node -> reg -> coq_function **)

let horrible_hack_old_entrypoint = ref (Obj.magic 1)
let horrible_hack_new_entrypoint = ref (Obj.magic 1)

let apply_optimal func oPT expr n t0 =
  
  let g = func.fn_code in
  (match Analysis.Es.mem expr (oPT n) with
     | true -> if debug then (Printf.printf "oui | "; flush stdout);
         let m = func.fn_nextpc in
	 if debug then (print_pos m; Analysis.print_expr expr);
	 if n = ! horrible_hack_old_entrypoint then horrible_hack_new_entrypoint := m;
         (match Maps.PTree.get n g with
            | Some i -> { fn_sig = func.fn_sig; fn_params = func.fn_params;
                fn_stacksize = func.fn_stacksize; fn_code =
                (Maps.PTree.set m (new_def expr t0 n) (* (new_def i t0 n) *)
                  (relink g n m)); fn_entrypoint =
                func.fn_entrypoint; fn_nextpc = (coq_Psucc m) }
            | None -> func)
     | false -> if debug then (Printf.printf "non | "; flush stdout); func)

(** val apply_redondant : coq_function -> (node -> Analysis.Es.t) -> code ->
                          expression -> node -> reg -> code **)

let apply_redondant rEDN g expr n t0 =
  
  match Analysis.Es.mem expr (rEDN n) with
    | true -> if debug then (Printf.printf "oui | "; flush stdout);
        (match Maps.PTree.get n g with
           | Some i -> Maps.PTree.set n (rewrite_instr i t0) g
           | None -> g)
    | false -> if debug then (Printf.printf "non | "; flush stdout); g

(** val transf_code : RTL.coq_function -> RTL.code **)

let transf_code func =
  Printf.printf "Lazy code motion : ";
  if Compcert_trigger.triggered 1 = false
  then (Printf.printf "off\n"; fn_code func)
  else 
    begin
      Printf.printf "on\n";


  if debug then (Printf.printf "Lazy code motion \n"; flush stdout);

  horrible_hack_old_entrypoint := func.fn_entrypoint;
  horrible_hack_new_entrypoint := func.fn_entrypoint;

  let Coq_pair (oPTaux, rEDNaux) = analysis func in

  let reg = ref (Coq_xH,false) in

  let fresh_register () =
    let (t,b) = !reg in
    if b 
    then (reg := (coq_Psucc t,b); t)
    else   
      let t =
	coq_Psucc
	  (fold_left (fun pot r -> max pot r)
             (app func.fn_params
		(Maps.PTree.fold (fun l p i -> app l (used_reg i)) func.fn_code
		   Coq_nil)) Coq_xH) in
      reg := (coq_Psucc t,true); t in
  
  let res =
  fold_left (fun fu expr ->
	       if debug then (
	       print_newline ();
    Printf.printf "Nouvelle expression : "; 
    Analysis.print_expr expr; print_newline ());	
    let freg = fresh_register () in
    let fu0 =
      if debug then (Printf.printf "Optimalite : ");
      Maps.PTree.fold (fun fu0 n i ->
			 if debug then (
			 print_int (Int32.to_int (Camlcoq.camlint_of_positive n)); 
			 Printf.printf " :: ");
        apply_optimal fu0 (fun n0 ->
          match Maps.PTree.get n0 oPTaux with
            | Some x -> x
            | None -> Analysis.Es.empty) expr n freg) func.fn_code
        fu
    in
    if debug then (
    print_newline ();
    Printf.printf "Redondance : ");
    let ggggg = 
      (Maps.PTree.fold (fun g n i ->
			  if debug then (
		print_int (Int32.to_int (Camlcoq.camlint_of_positive n)); 
			 Printf.printf " :: ");	
      apply_redondant (fun n0 ->
        match Maps.PTree.get n0 rEDNaux with
          | Some x -> x
          | None -> Analysis.Es.empty) g expr n freg) func.fn_code
      fu0.fn_code) in 

    

    { fn_sig = fu0.fn_sig; 
      fn_params = fu0.fn_params; 
      fn_stacksize = fu0.fn_stacksize; 
      fn_code = ggggg; 
      fn_entrypoint = !horrible_hack_new_entrypoint;
      fn_nextpc = fu0.fn_nextpc }) 
    
    (Analysis.Es.elements (universe func)) func in
  if debug then (
  Analysis.print_cfg (func.fn_code) (func.fn_entrypoint);
  Analysis.print_cfg (res.fn_code) (res.fn_entrypoint));
  if (not (func.fn_entrypoint = res.fn_entrypoint)) then failwith "decalage entrypoint STOP\n"; 
  res.fn_code
    end

(** val transf_function : coq_function -> coq_function **)

let transf_function func =
  if debug then (Printf.printf "Lazy code motion \n"; flush stdout);

  horrible_hack_old_entrypoint := func.fn_entrypoint;
  horrible_hack_new_entrypoint := func.fn_entrypoint;

  let Coq_pair (oPTaux, rEDNaux) = analysis func in

  let reg = ref (Coq_xH,false) in

  let fresh_register () =
    let (t,b) = !reg in
    if b 
    then (reg := (coq_Psucc t,b); t)
    else   
      let t =
	coq_Psucc
	  (fold_left (fun pot r -> max pot r)
             (app func.fn_params
		(Maps.PTree.fold (fun l p i -> app l (used_reg i)) func.fn_code
		   Coq_nil)) Coq_xH) in
      reg := (coq_Psucc t,true); t in
  
  let res =
  fold_left (fun fu expr ->
	       if debug then (
	       print_newline ();
    Printf.printf "Nouvelle expression : "; 
    Analysis.print_expr expr; print_newline ());	
    let freg = fresh_register () in
    let fu0 =
      if debug then (Printf.printf "Optimalite : ");
      Maps.PTree.fold (fun fu0 n i ->
			 if debug then (
			 print_int (Int32.to_int (Camlcoq.camlint_of_positive n)); 
			 Printf.printf " :: ");
        apply_optimal fu0 (fun n0 ->
          match Maps.PTree.get n0 oPTaux with
            | Some x -> x
            | None -> Analysis.Es.empty) expr n freg) func.fn_code
        fu
    in
    if debug then (
    print_newline ();
    Printf.printf "Redondance : ");
    let ggggg = 
      (Maps.PTree.fold (fun g n i ->
			  if debug then (
		print_int (Int32.to_int (Camlcoq.camlint_of_positive n)); 
			 Printf.printf " :: ");	
      apply_redondant (fun n0 ->
        match Maps.PTree.get n0 rEDNaux with
          | Some x -> x
          | None -> Analysis.Es.empty) g expr n freg) func.fn_code
      fu0.fn_code) in 

    

    { fn_sig = fu0.fn_sig; 
      fn_params = fu0.fn_params; 
      fn_stacksize = fu0.fn_stacksize; 
      fn_code = ggggg; 
      fn_entrypoint = !horrible_hack_new_entrypoint;
      fn_nextpc = fu0.fn_nextpc }) 
    
    (Analysis.Es.elements (universe func)) func in
  if debug then (
  Analysis.print_cfg (func.fn_code) (func.fn_entrypoint);
  Analysis.print_cfg (res.fn_code) (res.fn_entrypoint));
  
  res

(** val transf_fundef : fundef -> fundef **)

let transf_fundef = function
  | Internal f -> Internal (transf_function f)
  | External ef -> External ef

(** val transf_program : program -> program **)

let transf_program p =
  transform_program transf_fundef p
  

