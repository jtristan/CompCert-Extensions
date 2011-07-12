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
open CList
open Maps
open Op
open RTL
open Registers
open Setoid
open Specif

let debug = false

type __ = Obj.t

type expression =
  | Op of operation * reg list
  | Load of memory_chunk * addressing * reg list

let print_pos p =
  Printf.printf "%i " (Int32.to_int (Camlcoq.camlint_of_positive p))

let print_op o =
  match o with
  | Omove -> Printf.printf "move"
  | Ointconst i -> Printf.printf "intconst %i" (Int32.to_int (Camlcoq.camlint_of_z i))
  | Ofloatconst _ -> Printf.printf "floatconst"
  | Oaddrsymbol (id,i) -> Printf.printf "addrsymbol (%i,%i)" (Int32.to_int (Camlcoq.camlint_of_positive id)) (Int32.to_int (Camlcoq.camlint_of_z i)) 
  | Oaddrstack _ -> Printf.printf "addrstack"
  | Ocast8signed -> Printf.printf "cast8signed"
  | Ocast8unsigned -> Printf.printf "cast8unsigned"
  | Ocast16signed -> Printf.printf "cast16signed"
  | Ocast16unsigned -> Printf.printf "cast16unsigned"
  | Oadd -> Printf.printf "add"
  | Oaddimm _ -> Printf.printf "addimm"
  | Osub -> Printf.printf "sub"
  | Osubimm _ -> Printf.printf "subimm"
  | Omul -> Printf.printf "mul"
  | Omulimm _ -> Printf.printf "mulimm"
  | Odiv -> Printf.printf "div"
  | Odivu -> Printf.printf "divu"
  | Oand -> Printf.printf "and"
  | Oandimm _ -> Printf.printf "andimm"
  | Oor -> Printf.printf "or"
  | Oorimm _ -> Printf.printf "orimm"
  | Oxor -> Printf.printf "xor"
  | Oxorimm _ -> Printf.printf "xorimm"
  | Onand -> Printf.printf "nand"
  | Onor -> Printf.printf "nor"
  | Onxor -> Printf.printf "nxor"
  | Oshl -> Printf.printf "shl"
  | Oshr -> Printf.printf "shr"
  | Oshrimm _ -> Printf.printf "shrimm"
  | Oshrximm _ -> Printf.printf "shrximm"
  | Oshru -> Printf.printf "shru"
  | Orolm _ -> Printf.printf "rolm"
  | Onegf -> Printf.printf "negf"
  | Oabsf -> Printf.printf "absf"
  | Oaddf -> Printf.printf "addf"
  | Osubf -> Printf.printf "subf"
  | Omulf -> Printf.printf "mulf"
  | Odivf -> Printf.printf "divf"
  | Omuladdf -> Printf.printf "muladdf"
  | Omulsubf -> Printf.printf "mulsubf"
  | Osingleoffloat -> Printf.printf "singleoffloat"
  | Ointoffloat -> Printf.printf "intoffloat"
  | Ofloatofint -> Printf.printf "floatofint"
  | Ofloatofintu -> Printf.printf "floattointu"
  | Ocmp _ -> Printf.printf "cmp"
 
let print_reg_list l = 
  let l = Camlcoq.camllist_of_coqlist l in
  List.iter (fun p -> Printf.printf " "; print_pos p) l  

let print_expr e =
  match e with
    | Op (op,rl) -> print_op op; print_reg_list rl
    | Load (mc,a,rl) -> Printf.printf "Load"

let print_instr i =
  match i with
  | Inop n -> Printf.printf "nop -> %i" (Int32.to_int (Camlcoq.camlint_of_positive n))
  | Iop (o, rl, r, n) -> print_pos r; Printf.printf " := " ;print_op o; print_reg_list rl ; Printf.printf " -> "; print_pos n 
  | Iload (_,_,_,_,n) -> Printf.printf "load -> %i" (Int32.to_int (Camlcoq.camlint_of_positive n))
  | Istore (_,_,_,_,n) -> Printf.printf "store -> %i" (Int32.to_int (Camlcoq.camlint_of_positive n))
  | Icall (_,_,_,_,n)  -> Printf.printf "call -> %i" (Int32.to_int (Camlcoq.camlint_of_positive n))
  | Itailcall _ -> Printf.printf "tailcall"
  | Ialloc (_,_,n) -> Printf.printf "alloc -> %i" (Int32.to_int (Camlcoq.camlint_of_positive n))
  | Icond (_,_,n1,n2) -> Printf.printf "cond -> %i, %i" (Int32.to_int (Camlcoq.camlint_of_positive n1)) (Int32.to_int (Camlcoq.camlint_of_positive n2))
  | Ireturn _ -> Printf.printf "return"

let print_cfg_raw c e =
  Printf.printf "entrypoint : %i\n" (Int32.to_int (Camlcoq.camlint_of_positive e));
  ignore (Maps.PTree.map (fun n i -> print_pos n; print_string " :: "; print_instr i; print_newline()) c) 


let print_cfg_unfolded c e = 
  let cop = fun n -> (Int32.to_int (Camlcoq.camlint_of_positive n)) in  
  let rec pretty_printf_aux m l =
    print_newline ();
    if List.mem m l then print_newline ()
    else
      print_pos m; print_string " :: ";
      match Maps.PTree.get m c with
	| Some (Inop n) -> Printf.printf "nop -> %i" (cop n); pretty_printf_aux n (m :: l)
	| Some (Iop (o, rl, r, n)) -> print_pos r; Printf.printf " := " ;print_op o; print_reg_list rl ; Printf.printf " -> "; print_pos n; pretty_printf_aux n (m :: l) 
	| Some (Iload (_,_,_,_,n)) -> Printf.printf "load -> %i" (cop n); pretty_printf_aux n (m :: l)
	| Some (Istore (_,_,_,_,n)) -> Printf.printf "store -> %i" (cop n); pretty_printf_aux n (m :: l)
	| Some (Icall (_,_,_,_,n))  -> Printf.printf "call -> %i" (cop n); pretty_printf_aux n (m :: l)
	| Some (Itailcall _) -> Printf.printf "tailcall"; print_newline ()
	| Some (Ialloc (_,_,n)) -> Printf.printf "alloc -> %i" (cop n); pretty_printf_aux n (m :: l)
	| Some (Icond (_,_,n1,n2)) -> Printf.printf "cond -> %i, %i" (cop n1) (cop n2); print_newline ();pretty_printf_aux n1 (m :: l); print_newline (); pretty_printf_aux n2 (m :: l)
	| Some (Ireturn _) -> Printf.printf "return"; print_newline ()
	| None -> failwith "On essaie d imprimer un noeud qui n existe pas"
  in
  pretty_printf_aux e []

let print_cfg c e =
  Printf.printf "\nLe cfg :\n";
  print_cfg_raw c e;
  (* Printf.printf "\nSa version depliee : \n";
  print_cfg_unfolded c e *)

module Expression = 
 struct 
  type t = expression
  let eq_dec = fun t1 t2 -> t1 = t2
 end

module Expressions = FSetWeakList.Make(Expression)
module Es = Expressions

type dSet =
  | Exp of Es.t
  | Uni

(* debug code *)
let print_dSet_aux = function 
  | Exp s -> 
      if s = Es.empty then print_string "empty" 
      else List.iter print_expr (Camlcoq.camllist_of_coqlist s);
  | Uni -> print_string "uni"
let print_dSet c = 
  ignore (Maps.PMap.map (fun s -> (print_string " :: "; print_dSet_aux s; print_newline())) c) 
let print_dSet_2 c =
  ignore (Maps.PTree.map (fun n s -> (print_pos n ; print_string " :: "; print_dSet_aux s; print_newline())) c) 

(* fin *)

let dSetUnion d1 d2 =
  match d1, d2 with
    | Exp s1, Exp s2 -> Exp (Es.union s1 s2)
    | _ , _ -> Uni

let dSetIntersection d1 d2 =
  match d1, d2 with
    | Exp s1, Exp s2 -> Exp (Es.inter s1 s2)
    | Exp s1, Uni -> Exp s1
    | Uni, Exp s2 -> Exp s2
    | Uni, Uni -> Uni

let beq d1 d2 =
  match d1, d2 with
    | Exp s1, Exp s2 -> Es.equal s1 s2
    | Exp s1, Uni -> false
    | Uni, Exp s2 -> false
    | Uni, Uni -> true

let dBot = Exp Es.empty
let dTop = Uni

module LFSet = 
 struct 
  type t = dSet
  let beq x x0 = beq x x0
  let bot = dBot
  let lub x x0 = dSetUnion x x0
 end

module GFSet = 
 struct 
  type t = dSet
  let beq x x0 = beq x x0
  let bot = dTop
  let lub x x0 = dSetIntersection x x0
 end

module Forward_lfp = KildallGen.Dataflow_Solver(LFSet)(Kildall.NodeSetForward)
module Forward_gfp = KildallGen.Dataflow_Solver(GFSet)(Kildall.NodeSetForward)
module Backward_gfp = KildallGen.Backward_Dataflow_Solver(GFSet)(Kildall.NodeSetBackward)

let (++) = fun d1 d2 -> dSetUnion d1 d2

let ( ** ) = fun d1 d2 -> dSetIntersection d1 d2

let rec mem elt0 = function
  | Coq_nil -> false
  | Coq_cons (x, l0) ->
      (match peq x elt0 with
         | true -> true
         | false -> mem elt0 l0)

let defined func n =
  match Maps.PTree.get n func.fn_code with
    | Some i ->
        (match i with
           | Inop s -> Es.empty
           | Iop (op, lr, r, s) -> Es.singleton (Op (op, lr))
           | Iload (mc, ad, lr, r, s) -> Es.singleton (Load (mc, ad, lr))
           | Istore (mc, ad, lr, r, s) -> Es.empty
           | Icall (si, ri, lr, r, s) -> Es.empty
           | Itailcall (si, ri, lr) -> Es.empty
           | Ialloc (r1, r2, s) -> Es.empty
           | Icond (c, lr, s1, s2) -> Es.empty
           | Ireturn or0 -> Es.empty)
    | None -> Es.empty

let universe func =
  Maps.PTree.fold (fun s n a -> Es.union s (defined func n)) func.fn_code
    Es.empty

let co universe0 = function
  | Exp s -> Exp (Es.diff universe0 s)
  | Uni -> Exp Es.empty   

let exitpoint = function
  | Inop s -> false
  | Iop (op, lr, r, s) -> false
  | Iload (mc, ad, lr, r, s) -> false
  | Istore (mc, ad, lr, r, s) -> false
  | Icall (si, ri, lr, r, s) -> false
  | Itailcall (si, ri, lr) -> true
  | Ialloc (r1, r2, s) -> false
  | Icond (c, lr, s1, s2) -> false
  | Ireturn or0 -> true

let occur r = function
  | Op (op, lr) -> mem r lr
  | Load (mc, ad, lr) -> mem r lr

let occur_mem = function
  | Op (op, lr) -> false
  | Load (mc, ad, lr) -> true

let trans r universe0 =
  Es.filter (fun elt0 ->
    match occur r elt0 with
      | true -> false
      | false -> true) universe0

let trans_mem universe0 =
  Es.filter (fun elt0 ->
    match occur_mem elt0 with
      | true -> false
      | false -> true) universe0

let coq_TRANSloc_aux i universe0 =
  match i with
    | Inop s -> Uni
    | Iop (op, lr, r, s) -> Exp (trans r universe0)
    | Iload (mc, ad, lr, r, s) -> Exp (trans r universe0)
    | Istore (mc, ad, lr, r, s) -> Exp (trans_mem universe0)
    | Icall (si, ri, lr, r, s) -> Exp
        (Es.inter (trans r universe0) (trans_mem universe0))
    | Itailcall (si, ri, lr) -> Uni
    | Ialloc (r1, r2, s) -> Exp
        (Es.inter (trans r2 universe0) (trans_mem universe0))
    | Icond (c, lr, s1, s2) -> Uni
    | Ireturn ori -> Uni

let coq_TRANSloc g universe0 =
  let m = Maps.PTree.map (fun n i -> coq_TRANSloc_aux i universe0) g in
   if debug then print_string "transparency : \n";
  if debug then (print_dSet_2 m);   
  m   

let coq_ANTloc_aux = function
  | Inop s -> Exp Es.empty
  | Iop (op, lr, r, s) -> Exp
      (match mem r lr with
         | true -> Es.empty
         | false -> Es.singleton (Op (op, lr)))
  | Iload (mc, ad, lr, r, s) -> Exp
      (match mem r lr with
         | true -> Es.empty
         | false -> Es.singleton (Load (mc, ad, lr)))
  | Istore (mc, ad, lr, r, s) -> Exp Es.empty
  | Icall (si, ri, lr, r, s) -> Exp Es.empty
  | Itailcall (si, ri, lr) -> Exp Es.empty
  | Ialloc (r1, r2, s) -> Exp Es.empty
  | Icond (c, lr, s1, s2) -> Exp Es.empty
  | Ireturn ori -> Exp Es.empty

let coq_ANTloc g =
  let m = Maps.PTree.map (fun n i -> coq_ANTloc_aux i) g in
   if debug then print_string "local anticipabolity : \n";
  if debug then (print_dSet_2 m);  
  m

let unop msg = function Some x -> x | None -> failwith msg
let unop_kildall = unop "L analyse a echouee" 
let unop_get = unop "Le get a echoue"

(* Analyse d'anticipabilite *)

let coq_ANT g universe0 successors0 topnode exitpoints aNTloc tRANSloc =

  (* transfert *)
  let transf_ANT = fun n after ->
    (unop_get (Maps.PTree.get n aNTloc)) ++ ((unop_get (Maps.PTree.get n tRANSloc)) ** after) in

  (* join *)
  let join_ANT = fun n old new0 -> GFSet.lub old new0 in

  (* demarrage *)
  let start_ANT = let rec map0 = function
        | Coq_nil -> Coq_nil
        | Coq_cons (a, t0) -> Coq_cons ((Coq_pair (a, (Exp Es.empty))),
            (map0 t0))
      in map0 exitpoints in

  (* resolution *)
  let analysis = unop_kildall (Backward_gfp.fixpoint successors0 topnode transf_ANT join_ANT
     start_ANT) in
  if debug then print_string "anticipability : \n";
  if debug then (print_dSet analysis);
  (analysis, transf_ANT)

(* Analyse earliestness *)

let coq_EARL g universe0 successors0 topnode entrypoint aNTloc tRANSloc aNT =

  (* transfert *)
  let transf_EARL = fun n before ->
    (co universe0 (unop_get (Maps.PTree.get n tRANSloc))) ++ ((co universe0 (aNT n)) ** before) in

  (* join *)
  let join_EARL = fun n old new0 -> LFSet.lub old new0 in

  (* demarrage *)
  let start_EARL = Coq_cons ((Coq_pair (entrypoint, (Exp universe0))),
     Coq_nil) in

  (* resolution *)
  let analysis = unop_kildall (Forward_lfp.fixpoint successors0 topnode transf_EARL join_EARL start_EARL) in
  if debug then print_string "earliestness : \n";
  if debug then (print_dSet analysis);
  (analysis, transf_EARL)

(* Analyse de delayement *)
let coq_DELAY g universe0 successors0 topnode entrypoint aNTloc tRANSloc aNT eARL =

  (* transfert *)
  let transf_DELAY = fun n before ->
    (co universe0 (unop_get (Maps.PTree.get n aNTloc))) ** before in

  (* join *)
  let join_DELAY = fun n old new0 ->
     ((aNT n) ** (eARL n)) ++ (GFSet.lub old new0) in
    
  (* demarrage *)
  let start_DELAY = Coq_cons ((Coq_pair (entrypoint,
     ((aNT entrypoint) ** (eARL entrypoint)))), Coq_nil) in  

  (* resolution *)

  let analysis = unop_kildall (Forward_gfp.fixpoint successors0 topnode transf_DELAY join_DELAY start_DELAY) in
  if debug then print_string "delay : \n";
  if debug then (print_dSet analysis);  
  (analysis, transf_DELAY)


(* Analyse d isolement *)
let coq_ISOL g universe0 successors0 topnode exitpoints aNTloc tRANSloc lATE =

  (* transfert *)
  let transf_ISOL = fun n after ->
    (lATE n) ++ ((co universe0 (unop_get (Maps.PTree.get n aNTloc))) ** after) 
  in

  (* join *)
  let join_ISOL = fun n old new0 -> GFSet.lub old new0 in

  (* demarrage *)
  let start_ISOL = let rec map0 = function
        | Coq_nil -> Coq_nil
        | Coq_cons (a, t0) -> Coq_cons ((Coq_pair (a, (Exp universe0))),
            (map0 t0))
      in map0 exitpoints in

  (* resolution *)
  let analysis = unop_kildall (Backward_gfp.fixpoint successors0 topnode transf_ISOL join_ISOL start_ISOL) in
    if debug then print_string "isolated : \n";
  if debug then (print_dSet analysis); 
  (analysis, transf_ISOL)

(* Analyse globale *)

let analysis func =
  let successors0 = successors func in
  let exitpoints =
    Maps.PTree.fold (fun s n a ->
		       if exitpoint a then Coq_cons (n, s) else s)
       func.fn_code Coq_nil
  in
  if debug then Printf.printf "Il y a %i poitns de sortie\n" (List.length (Camlcoq.camllist_of_coqlist exitpoints));
  

  let topnode = func.fn_nextpc in
  let universe0 = universe func in
  let aNTloc = coq_ANTloc func.fn_code in
  let tRANSloc = coq_TRANSloc func.fn_code universe0 in

  let (aNTanalysis, transf_ANT) =
    coq_ANT func.fn_code universe0 successors0 topnode exitpoints aNTloc
      tRANSloc
  in
  let aNTout = fun n -> Maps.PMap.get n aNTanalysis in
  let aNT = fun n -> (transf_ANT n (aNTout n)) in

  let (eARLanalysis, transf_EARL) =
    coq_EARL func.fn_code universe0 successors0 topnode func.fn_entrypoint
      aNTloc tRANSloc aNT in
  let eARL = fun n -> Maps.PMap.get n eARLanalysis in

  let (dELAYanalysis, transf_DELAY) =
    coq_DELAY func.fn_code universe0 successors0 topnode func.fn_entrypoint
      aNTloc tRANSloc aNT eARL in
  let dELAY = fun n -> Maps.PMap.get n dELAYanalysis in

  let lATE = fun n ->
    (dELAY n) **
      ((unop_get (Maps.PTree.get n aNTloc)) ++
        (co universe0 (fold_left (fun s n0 ->  s ** (dELAY n0)) 
          (successors0 n) (Exp universe0)))) in

  let (iSOLanalysis, transf_ISOL) =
    coq_ISOL func.fn_code universe0 successors0 topnode exitpoints aNTloc
      tRANSloc lATE in
  let iSOL = fun n -> Maps.PMap.get n iSOLanalysis in

  Coq_pair
  ((Maps.PTree.fold (fun o n i ->
     Maps.PTree.set n
       (match (lATE n) ** (co universe0 (iSOL n)) with
          | Exp s -> s
          | Uni -> universe0)
           (Obj.magic o)) func.fn_code Maps.PTree.empty),
  (Maps.PTree.fold (fun o n i ->
    Maps.PTree.set n
      (match (unop_get (Maps.PTree.get n aNTloc)) **
               (co universe0 ((lATE n) ** (iSOL n))) with
         
                        | Exp s -> s
                        | Uni -> universe0)
		    (Obj.magic o)) func.fn_code Maps.PTree.empty))

