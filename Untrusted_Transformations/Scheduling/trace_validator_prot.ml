open Mach
open Two_level_repr
open Valcommon
open Maps
open Datatypes

let rec conv = function
    [] -> CList.Coq_nil 
  | elt :: l -> CList.Coq_cons (elt,conv l)

let print_binpos b = print_int (Int32.to_int (Camlcoq.camlint_of_positive b))

let print_instruction i =
  match i with 
    | Mgetstack (_,_,_,b) -> print_string " getsack"; print_binpos b
    | Msetstack (_,_,_,b) -> print_string " setstack"; print_binpos b
    | Mgetparam (_,_,_,b) -> print_string " getparam"; print_binpos b
    | Mop (_,_,_,b) -> print_string " op"; print_binpos b
    | Mload (_,_,_,_,b) -> print_string " load"; print_binpos b
    | Mstore (_,_,_,_,b) -> print_string " store"; print_binpos b
    | Malloc b -> print_string " alloc"; print_binpos b
    | Mcond (_,_,b1,b2) -> print_string " cond"; print_binpos b1; print_string " "; print_binpos b2
    | Mout lbl -> print_string " out"; print_binpos lbl

let print_cfdb cfd =
  Maps.PTree.map (fun b -> fun i ->( print_string "(" ; print_binpos b ; 
		 print_string ","; print_instruction i; print_string ")"; i)) cfd 

let print_cfd cfd = 
  print_cfdb cfd.cfd_code;
  print_binpos cfd.cfd_head

(**** validation de deux dags ****)

let focus c pc =
  { cfd_code = c.cfd_code; cfd_head = pc; cfd_nextpc = c.cfd_nextpc }

let check_control c1 c2 buf1 buf2 : 
                         bool * (cfd * cfd * cfd * cfd) option =     
  match (PTree.get (c1.cfd_head) c1.cfd_code), 
    (PTree.get (c2.cfd_head) c2.cfd_code)  with
  | Some (Mcond (cond1, args1, pc1', pc1'')), Some (Mcond (cond2, args2, pc2', pc2'')) ->
          if cond1 = cond2 then
          if args1 = args2 then
          (true, Some (focus c1 pc1',focus c2 pc2',focus c1 pc1'', focus c2 pc2''))
          else (false, None) else (false,None)
  | Some (Mout lbl1), Some (Mout lbl2) -> if lbl1 = lbl2 then (nbic buf1 buf2,None) else (false, None)
  | _, _ -> (false, None)
 

let rec next_branch c buf =
  match PTree.get c.cfd_head c.cfd_code with
    | Some (Mgetstack (i, t, m, pc)) -> next_branch (focus c pc) (buf @ (Mach.Mgetstack (i, t, m)) :: [])
    | Some (Msetstack (m, i, t, pc)) -> next_branch (focus c pc) (buf @ (Mach.Msetstack (m, i, t)) :: [])
    | Some (Mgetparam (i, t, m, pc)) -> next_branch (focus c pc) (buf @ (Mach.Mgetparam (i, t, m)) :: [])    
    | Some (Mop (o, lm, m, pc)) -> next_branch (focus c pc) (buf @ (Mach.Mop (o, lm, m)) :: [])
    | Some (Mload (chk, addr, args, r, pc)) -> next_branch (focus c pc) (buf @ (Mach.Mload (chk, addr, args, r)) :: [])
    | Some (Mstore (chk, addr, args, r, pc)) -> next_branch (focus c pc) (buf @ (Mach.Mstore (chk, addr, args, r)) :: [])
    | Some (Malloc pc) -> next_branch (focus c pc) (buf @ (Mach.Malloc) :: [])
    | Some (Mcond _) -> (c,buf)
    | Some (Mout _) -> (c,buf)
    | None -> (print_binpos c.cfd_head; print_newline (); failwith "hum...")
    
let rec compare d1 d2 buf1 buf2 =
  let (d1',buf1') = next_branch d1 buf1
  and (d2',buf2') = next_branch d2 buf2 in
  match check_control d1' d2' (conv buf1') (conv buf2') with
    | true, None -> true
    | true, Some (c1'', c2'', c1''', c2''') ->
	compare c1'' c2'' buf1' buf2' && compare c1''' c2''' buf1' buf2' 
    | false, _ -> false

let validate_dags (di : cfd) (dt : cfd) : bool = 
  print_string "validate_dags"; print_newline();
  print_cfd di;
  print_cfd dt;
  print_string "comparaison"; print_newline();
  compare di dt [] []
  
(**** validation de deux cfgs *****)

let compgendags r1 r2 =
  match r1, r2 with
    | Mlabel c1, Mlabel c2 -> validate_dags c1 c2 
    | Mreturn, Mreturn -> true
    | Mcall (s1, ros1, c1), Mcall (s2, ros2, c2) ->
	s1 = s2 && ros1 = ros2 && validate_dags c1 c2
    | _ -> false

let validate_cfgs (ci : cfg) (ct : cfg) : bool =
  print_string "\nvalidation... \n";
  print_newline ();
  let get glue lbl = 
    match PTree.get lbl (ct.cfg_code) with
      | Some c -> compgendags glue c 
      | None -> false in    
  print_string "c est parti"; print_newline ();
  let b = 
  PTree.fold (fun b -> fun lbl -> fun glue -> b && get glue lbl) ci.cfg_code true
  && ci.cfg_head = ct.cfg_head in
  if b then print_string "\nTRUE\n" else print_string "\nFALSE\n" ;
  b
