open Mach
open Two_level_repr
open Maps
open PTree
open Camlcoq
open Int32
open BinPos
open LabelSync

let rec convert1 = function
    CList.Coq_nil -> []
  | CList.Coq_cons (elt,l) -> elt :: convert1 l 

let rec convert2 = function
    [] -> CList.Coq_nil 
  | elt :: l -> CList.Coq_cons (elt,convert2 l)

let print_binpos b = print_int (Int32.to_int (Camlcoq.camlint_of_positive b))

let print_mach i =
  match i with 
    | Mach.Mgetstack _  -> print_string " Mgetstack "
    | Mach.Msetstack _ -> print_string " Msetstack "
    | Mach.Mgetparam _ -> print_string " Mgetparam "
    | Mach.Mop _ -> print_string " Mop "
    | Mach.Mload _ -> print_string " Mload "
    | Mach.Mstore _ -> print_string " Mstore "
    | Mach.Mcall _ -> print_string " Mcall "
    | Mach.Mlabel lbl -> print_string " Mlabel "; print_binpos lbl
    | Mach.Mgoto lbl -> print_string " Mgoto "; print_binpos lbl
    | Mach.Mcond (_,_,lbl) -> print_string " Mcond "; print_binpos lbl
    | Mach.Mreturn  -> print_string " Mreturn "
    | Mach.Malloc  -> print_string " Malloc "

let print_code func = List.iter (fun i ->  print_mach i; print_newline ()) (convert1 func)



(**************************************************************)
(**************************************************************)
(* transformation code Mach lineaire -> graphe a 2 niveaux    *)
(**************************************************************)
(**************************************************************)

let trans = Camlcoq.positive_of_camlint
(*
let identify code =

  let rec identify_aux code count =
    match code with
      | i :: l -> (trans (Int32.of_int count), i) :: identify_aux l (count + 1)
      | [] -> [] in 
  
  identify_aux code 1
*)
let unop = function Datatypes.Some x -> x | _ -> failwith "unop abusif"

let find_label lbl func = 
  match Mach.find_label lbl (convert2 func) with
  | Datatypes.Some l -> Datatypes.Some (convert1 l)
  | Datatypes.None -> Datatypes.None

let is_targetted lbl func =
  (* print_string "in is_targetted" ; print_newline (); *)
  let rec is_targetted_aux code =
    match code with
    | Mach.Mgoto lbl' :: l -> if lbl = lbl' then true else is_targetted_aux l
    | Mach.Mcond (_,_,lbl') :: l -> if lbl = lbl' then true else is_targetted_aux l
    | i :: l -> is_targetted_aux l
    | [] -> false

  in
  (* print_string "out is_targetted"; print_newline (); *)
  is_targetted_aux func

let path lbl func code =
  (* print_string "in path"; print_newline (); *)
  let max_depth = List.length func in 
  print_int max_depth ;
  let rec path_aux code n =
    match n with
    | 0 -> false
    | _ -> (
      match code with
      | Mach.Mgoto lbl' :: l -> if lbl = lbl' then true else path_aux (unop (find_label lbl' func)) (n - 1) 
      | Mach.Mcond (_,_,lbl') :: l -> if lbl = lbl' then true else path_aux l (n - 1) || path_aux (unop (find_label lbl' func)) (n - 1)
      | Mach.Mreturn :: l -> false
      | i :: l -> path_aux l (n - 1)
      | [] -> failwith "reached the end of the code and didn t encounter a return !")

  in 
  (* print_code (convert2 func) ; print_newline ();
  (* print_string "on recherche un chemin vers : "; print_binpos lbl ;
  print_string "le calcule donne : " ; 
  if (path_aux code max_depth) then print_string "true" else print_string "false"; *)
  print_newline (); *)
  let b = path_aux code max_depth in
  (* print_string "out path"; print_newline (); *)
  b

let mem_path lbl func code =
  let max_depth = List.length func in 
 
  let rec path_aux code n mem =
    if (List.mem code mem) then false else (
    let mem = code :: mem in
    match n with
    | 0 -> false
    | _ -> (
      match code with
      | Mach.Mgoto lbl' :: l -> if lbl = lbl' then true else path_aux (unop (find_label lbl' func)) (n - 1) mem
      | Mach.Mcond (_,_,lbl') :: l -> if lbl = lbl' then true else path_aux l (n - 1) mem || path_aux (unop (find_label lbl' func)) (n - 1) mem
      | Mach.Mreturn :: l -> false
      | i :: l -> path_aux l (n - 1) mem
      | [] -> failwith "reached the end of the code and didn t encounter a return !"))

  in 
 
  let b = path_aux code max_depth [] in b 

let backedges func =

  let rec backedges_aux code =
   (* print_string "coucou"; *)
    match code with
      | Mach.Mlabel lbl :: l -> if (is_targetted lbl func && mem_path lbl func l) then lbl :: backedges_aux l else backedges_aux l
      | _ :: l -> (* print_string "couac" ; *) backedges_aux l
      | [] -> []

  in
  (* print_string "out backedges"; print_newline (); *)
  backedges_aux func

let get_head func =
  match func with
    | Mlabel lbl :: l -> lbl
    | _ -> failwith "the code isn t well formed, it should begin with a label"

let keys func backedges =

  let rec keys_aux code =
    match code with
    | [] -> []
    | Mach.Mlabel lbl :: Mach.Mcall _ :: Mach.Mlabel lbl' :: l -> lbl :: lbl' :: keys_aux l
    | Mach.Mlabel lbl :: Mach.Mreturn :: l -> lbl :: keys_aux l
    | Mach.Mlabel lbl :: l -> if List.mem lbl backedges then lbl :: keys_aux l else keys_aux l
    | i :: l -> keys_aux l

  in
  get_head func :: keys_aux func 
(*   
let rec get_id corr lbl =
  match corr with
    | (lbl',node) :: l -> if lbl = lbl' then node else get_id l lbl
    | [] -> failwith "get_id label not found"
*)

let rec mem lbl = function
  | CList.Coq_nil -> false
  | CList.Coq_cons (lbl', l0) ->
      if lbl = lbl' then true else mem lbl l0
        
let rec skip_control s func c = function
  | Datatypes.O -> Datatypes.None
  | Datatypes.S n ->
      (match c with
         | CList.Coq_nil -> Datatypes.None
         | CList.Coq_cons (i, c') ->
             (match i with
                | Mach.Mgetstack (i0, t, m) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Msetstack (m, i0, t) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Mgetparam (i0, t, m) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Mop (o, l, m) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Mload (m, a, l, m0) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Mstore (m, a, l, m0) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Mcall (s0, s1) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Malloc -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mlabel lbl ->
                    (match mem lbl s with
                       | true -> Datatypes.Some (CList.Coq_cons ((Mlabel lbl), c'))
                       | false -> skip_control s func c' n)
                | Mgoto lbl ->
                    (match Mach.find_label lbl func with
                       | Datatypes.Some c'' ->
                           (match mem lbl s with
                              | true -> Datatypes.Some (CList.Coq_cons ((Mgoto lbl), c'))
                              | false -> skip_control s func c'' n)
                       | Datatypes.None -> Datatypes.None)
                | Mach.Mcond (c0, l, l0) -> Datatypes.Some (CList.Coq_cons (i, c'))
                | Mach.Mreturn -> Datatypes.Some (CList.Coq_cons (i, c'))))

let build_tree func code keys =
  (* print_string "entree dans build tree "; print_newline ();
  print_code (convert2 func); *)
  let max_depth = CList.length (convert2 func) in  

  let rec build_tree_aux code = 
  match skip_control (convert2 keys) (convert2 func) (convert2 code) max_depth with
    | Datatypes.Some c -> ( (* print_string "coucou"; print_newline (); *)
	match (convert1 c) with
	  | i :: l -> (* print_mach i; *) (
	      match i with
		| Mach.Mgetstack (i0, t, m) -> Two_level_repr.Mgetstack (i0,t,m,build_tree_aux l)
		| Mach.Msetstack (m, i0, t) -> Two_level_repr.Msetstack (m, i0, t,build_tree_aux l)
		| Mach.Mgetparam (i0, t, m) -> Two_level_repr.Mgetparam (i0, t, m,build_tree_aux l)
		| Mach.Mop (a, b, c) -> Two_level_repr.Mop (a, b, c,build_tree_aux l)
		| Mach.Mload (a, b, c, d) -> Two_level_repr.Mload (a, b, c, d,build_tree_aux l)
		| Mach.Mstore (a, b, c, d) -> Two_level_repr.Mstore (a, b, c, d,build_tree_aux l)
		| Mach.Mcall (s, s0) -> failwith "the code isnt well formed, encountered a call while building a tree "
		| Mach.Malloc -> Two_level_repr.Malloc (build_tree_aux l)
		| Mach.Mlabel l -> Two_level_repr.Mout l 
		| Mach.Mgoto l -> Two_level_repr.Mout l 
		| Mach.Mcond (c, li, l0) -> 
		     if List.mem l0 keys 
		    then Two_level_repr.Mcond (c, li,Two_level_repr.Mout l0,build_tree_aux l) 
		    else Two_level_repr.Mcond (c, li,build_tree_aux (unop (find_label l0 func)),build_tree_aux l)
		| Mach.Mreturn -> failwith "the code isnt well formed, encountered a return while building a tree " )
	  | [] -> failwith "while building a tree the code has been completely consummed without encouterering a return" )
    | Datatypes.None -> failwith "the keys have not been computed correctly"

  in
  Two_level_repr.Mtree (build_tree_aux code)

let build_call code =
  match code with
    | Mach.Mcall (sigg,ros) :: Mlabel lbl :: l -> Two_level_repr.Mcall (sigg,ros,lbl)  
    | _ -> failwith "the code isn t well formed, should have got a call followed by a label" 

let build_return code =
  match code with 
    | Mach.Mreturn :: l -> Two_level_repr.Mreturn 
    | _ -> failwith "the code isn t well formed, should have got a return"

let build code func keys =
  match code with
    | [] -> failwith "trying to build something upon the empty code"
    | Mach.Mcall _ :: l -> build_call code
    | Mach.Mreturn :: l -> build_return code
    | _ -> build_tree func code keys 

let rec get_suffix func id = 
  match func with 
    | Mlabel lbl :: l -> if lbl = id then l else get_suffix l id
    | i :: l -> get_suffix l id
    | [] -> failwith "couldn t find an id in the code"

let build_graph ids_to_treat func =
  List.fold_left (fun m -> fun id -> Maps.PTree.set id (build (get_suffix func id) func ids_to_treat) m) Maps.PTree.empty ids_to_treat
  
    (* experimentation *)
(*
let rec is_cond lbl code =
  match code with
    | Mach.Mcond (_,_,lbl') :: l -> if lbl = lbl' then true else is_cond lbl l 
    | i :: l -> is_cond lbl l 
    | _ -> false

let rec patch code ptch n =
 match code with
   | Mach.Mlabel lbl :: l -> if List.mem lbl ptch then Mlabel lbl :: Mlabel n :: patch l ptch (coq_Psucc n) else Mlabel lbl :: patch l ptch n  
   | i :: l -> i :: patch l ptch n
   | [] -> []

let sync_more func =
  let be = backedges func in
  let le = List.filter (fun k -> is_cond k func) be in
    (patch func le (coq_Psucc (LabelSync.get_max (LabelSync.get_labels (convert2 func)))),le)
  *)

let build_repr func =
  (*print_string "elaboration\n";
  print_newline (); *)
  let func = convert1 func in
    (* print_string "calcul des backedges ..."; print_newline (); *)
  let backedges = backedges func in
   (* print_string " OK"; print_newline ();
    List.iter (fun i -> print_binpos i ; print_string ";") backedges;
     print_string "calcul des cles ..."; print_newline (); *)
  let keys = keys func backedges in
   (*  print_string " OK"; print_newline ();
     List.iter (fun i -> print_binpos i ; print_string ";") keys;
     print_string "calcul du graphe ..."; print_newline (); *)
  let cfg = build_graph keys func in
   (*  print_string " OK"; print_newline ();
  print_string "fini"; print_newline (); *)
  Datatypes.Some {Two_level_repr.cfg_code = cfg ; Two_level_repr.cfg_head = get_head func}
    


