open Mach
open Compcert_trigger

(* on aura surement besoi nde converstir des listes caml en coq et vice versa *)

let rec to_caml = function
    CList.Coq_nil -> []
  | CList.Coq_cons (elt,l) -> elt :: to_caml l 

let rec to_coq = function
    [] -> CList.Coq_nil 
  | elt :: l -> CList.Coq_cons (elt,to_coq l)

type resource = Reg of Locations.mreg | Mem 
open Locations
let all = [Mem
  ; Reg R3
  ; Reg R4
  ;Reg R5
  ;Reg R6
  ;Reg R7
  ;Reg R8
  ;Reg R9
  ;Reg R10
  ;Reg R13
  ;Reg R14
  ;Reg R15
  ;Reg R16
  ;Reg R17
  ;Reg R18
  ;Reg R19
  ;Reg R20
  ;Reg R21
  ;Reg R22
  ;Reg R23
  ;Reg R24
  ;Reg R25
  ;Reg R26
  ;Reg R27
  ;Reg R28
  ;Reg R29
  ;Reg R30
  ;Reg R31
  ;Reg F1
  ;Reg F2
  ;Reg F3
  ;Reg F4
  ;Reg F5
  ;Reg F6
  ;Reg F7
  ;Reg F8
  ;Reg F9
  ;Reg F10
  ;Reg F14
  ;Reg F15
  ;Reg F16
  ;Reg F17
  ;Reg F18
  ;Reg F19
  ;Reg F20
  ;Reg F21
  ;Reg F22
  ;Reg F23
  ;Reg F24
  ;Reg F25
  ;Reg F26
  ;Reg F27
  ;Reg F28
  ;Reg F29
  ;Reg F30
  ;Reg F31
  ;Reg IT1
  ;Reg IT2
  ;Reg IT3
  ;Reg FT1
  ;Reg FT2
  ;Reg FT3]


let print_mach i =
  match i with 
    | Mgetstack _  -> print_string "Mgetstack "
    | Msetstack _ -> print_string "Msetstack "
    | Mgetparam _ -> print_string "Mgetparam "
    | Mop _ -> print_string "Mop "
    | Mload _ -> print_string "Mload "
    | Mstore _ -> print_string "Mstore "
    | Mcall _ -> print_string "Mcall "
    | Mlabel _ -> print_string "Mlabel "
    | Mgoto _ -> print_string "Mgoto "
    | Mcond _ -> print_string "Mcond "
    | Mreturn  -> print_string "Mreturn "
    | Malloc  -> print_string "Malloc "

let print_code = List.iter print_mach

(* [reads_writes instruction] donne la liste de resources slues et des resource
   ecrites par [instruction]*)
let reads_writes instruction = 
  
  let to_resource rl = List.map (fun e -> Reg e) (to_caml rl) in

  match instruction with
    | Mgetstack (i, t, r) -> [Mem],[Reg r] 
    | Msetstack (r, i, t) -> [Reg r],[Mem]
    | Mgetparam (i, t, r) -> [Mem],[Reg r] 
    | Mop (op, rl, r) -> (to_resource rl),[Reg r]
    | Mload (chk, addr, rl, r) -> Mem::(to_resource rl),[Reg r]
    | Mstore (chk, addr, rl, r) -> (Reg r)::(to_resource rl),[Mem]
    | Mcall (sign, rid) -> all,all 
    | Mlabel lbl -> [],[]
    | Mgoto lbl -> [],[]
    | Mcond (cond, rl, lbl) -> (to_resource rl),[]
    | Mreturn -> [],[]
    | Malloc -> all,all

(* [latency instruction] renvoie une estimation de la latence de [instruction] *)
let latency instruction = 

  match instruction with 
    | Mgetstack _ -> 3 
    | Msetstack _ -> 3
    | Mgetparam _ -> 3 
    | Mop _ -> 1
    | Mload _ -> 3
    | Mstore _ -> 3
    | Mcall _ -> 1 
    | Mlabel _ -> 1
    | Mgoto _ -> 1
    | Mcond _ -> 1
    | Mreturn -> 1
    | Malloc -> 1

(* [chop_code code] decoupe [code] en blocs de base et elimine les labels 
   inutiles *)
let chop_code code =

  let rec chop_code_after_breaks current_block found_blocks lbls = function
    | Mgoto lbl as i :: code -> chop_code_after_breaks [] ((i :: current_block) :: found_blocks) (lbl :: lbls) code 
    | Mcond (_, _, lbl) as i :: code -> chop_code_after_breaks [] ((i :: current_block) :: found_blocks) (lbl :: lbls) code 
    | Mreturn as i :: code -> chop_code_after_breaks [] ((i :: current_block) :: found_blocks) lbls code 
    | i :: code ->  chop_code_after_breaks (i :: current_block) found_blocks lbls code
    | [] -> found_blocks , lbls 
	
  and chop_code_after_labels labels current_block found_blocks = function
    | Mlabel label as i :: code -> 
	if List.mem label labels 
	then chop_code_after_labels labels [] ((i :: current_block) :: found_blocks) code
	else chop_code_after_labels labels (i :: current_block) found_blocks code
    | i :: code  -> chop_code_after_labels labels (i :: current_block) found_blocks code
    | [] -> List.rev (if List.length current_block = 0 
		      then found_blocks
		      else current_block :: found_blocks) in 
  (*
  let delete_useless_labels labels = 
    List.filter (fun e -> 
		   match e with 
		       Mlabel l -> List.mem l labels 
		     | _ -> true) in 
  *)
  let (choped,labels) = chop_code_after_breaks [] [] [] code in
  let choped = List.map (chop_code_after_labels [] (*labels*) [] []) choped in
  let choped = List.concat choped in
  (* let choped = List.map (delete_useless_labels labels) choped in *)
  List.rev choped 

(* Algorithme d'ordonnacement par liste *)

(* DGraph est le module d'implemntation de la structure de donnee
   centrale : le graphe de dependance (qui en fait est un DAG) *)
module DGraph = Graph.Make ( 
  struct 
    type t = Mach.instruction 
    let print_content t = Printf.printf "developpement en cours !\n%!"
  end)
  
(* [compute_dependency_graph block] associe a un bloc d'instructions
   le graphe de dépendance entre ces instructions *)
let compute_dependency_graph block = 
  
  let last_to_write = Hashtbl.create 10 
  and last_to_read = Hashtbl.create 10 
  and graph = DGraph.empty_graph () in
  let lbl = ref None in
  
  
  let set_last reg = 
    if Hashtbl.mem last_to_write reg then
      Hashtbl.replace last_to_write reg
    else Hashtbl.add last_to_write reg
  and get_last reg = 
    if Hashtbl.mem last_to_write reg then
      Some (Hashtbl.find last_to_write reg)
    else None in
  let set_last_tr reg node = 
    if Hashtbl.mem last_to_read reg then
      let l = Hashtbl.find last_to_read reg in
      if List.mem node l then ()
      else 
	Hashtbl.replace last_to_read reg (node :: l)
    else Hashtbl.add last_to_read reg [node] 
  and get_last_tr reg = 
    if Hashtbl.mem last_to_read reg then
      Hashtbl.find last_to_read reg
    else [] 
  and reset_last_tr reg =    (* new new new *)
    if Hashtbl.mem last_to_read reg then
      Hashtbl.replace last_to_read reg []
    else () in
  
  let rec iter_block graph = function 
      
      [] -> graph
    | instr :: block ->
	let reads,writes = reads_writes instr in
	let (node,graph) = DGraph.add_node graph instr in
	
	(match instr with 
	     Mach.Mlabel _ -> lbl := Some node;
	   | _ -> ());
	
	(* RAW *) 
	
	let graph = 
	  List.fold_left (fun graph reg -> match get_last reg with
			      Some instr2 -> DGraph.add_arrow graph instr2 node
			    | None -> graph) 
	    graph reads in
	
        (* WAW *)
	
	let graph = 
	  List.fold_left (fun graph reg -> match get_last reg with
			      Some instr2 -> DGraph.add_arrow graph instr2 node
			    | None -> graph) 
	    graph writes in
	
	(* WAR *)
	
	let graph = 
	  List.fold_left (
	    fun graph reg -> 
	      let l = get_last_tr reg in 
	      List.fold_left (
		fun graph -> fun e -> 
		  DGraph.add_arrow graph e node
	      ) graph l
	  ) graph writes in
	
	(* update the last_to_write registration *)
	
	List.iter (fun reg -> set_last reg node) writes;
	List.iter (fun reg -> set_last_tr reg node) reads;
	List.iter (fun reg -> reset_last_tr reg) writes;
	
	(* special cases : branches and labels *)
	(* we make the hypothesis that a branch is always unique and last in the block *)
	
	(* branches *)
	
	let graph =
	  match instr with
	    | Mach.Mgoto _ | Mach.Mcond _ | Mach.Mreturn  ->
		let all_nodes = DGraph.all_nodes graph in
		let all_nodes = List.filter (fun e -> not (e = node)) all_nodes in
		List.fold_left (fun g e -> DGraph.add_arrow g e node) graph all_nodes  
	    | _ -> graph in
	
	iter_block graph block 
  in 
  
  
  let graph = iter_block graph block in 
  
  (* labels *)
  (* we make the assumption that there is at most one label *)
  
  let graph =
    match !lbl with
	Some node -> 
	  let all_nodes = DGraph.all_nodes graph in
	  let all_nodes = List.filter (fun e -> not (e = node)) all_nodes in
	  List.fold_left (fun g e -> DGraph.add_arrow g node e) graph all_nodes  
      | None -> graph in
  
  graph   
    
    
(* l'algortihe de list scheduling a proprement parler *)
    
let compute_priority = fun x -> x
 
let choose graph l = let l = List.rev l in (List.tl l,List.hd l)  

let simulate graph =
    
  let cycle = 1 
  and graph_cpy = DGraph.copy graph
  and ready = DGraph.get_roots graph
  and active = [] 
  and launched = []
  and schedule = Hashtbl.create 10 in
  
  let invert invschedule =
    let schedule = Hashtbl.create (Hashtbl.length invschedule) in
    let f a b sched = Hashtbl.add sched b a; sched in 
    Hashtbl.fold f invschedule schedule in
      
  let rec process graph ready active cycle launched =
    
    if List.length ready != 0 || List.length active != 0 then (
	
      let launched,ready,active = 
	if List.length ready != 0 
	then 
	  let remain,op = choose graph ready in 
	  Hashtbl.add schedule op cycle;
	  op :: launched,remain,op::active  
	else launched,ready,active 
	  
      and cycle = cycle + 1 in
	  
      let processed node = 
	Hashtbl.find schedule node + latency (DGraph.get_datum graph node) < cycle in
      
      let still_active = List.filter (fun e -> not (processed e)) active 
      and finished = List.filter processed active in
      let graph = List.fold_left (fun g n -> DGraph.del_node g n) graph finished in 
      let new_ready = DGraph.get_roots graph in
      let new_ready = List.filter (fun e -> not (List.mem e launched)) new_ready in
      let new_ready = List.filter (fun e -> not (List.mem e ready)) new_ready in
	  
      process graph (new_ready @ ready) still_active cycle launched
    ) in
  
  process graph ready active cycle launched;
  
  let schedule = invert schedule in
  
  let rec insert a b = function
      (a',_) as e :: l -> 
	if a' < a 
	then e :: insert a b l
	else (a,b) :: e :: l
    | [] -> [(a,b)] in

  let schedule = Hashtbl.fold insert schedule [] in
  let l = List.map snd schedule in
  List.map (DGraph.get_datum graph_cpy) l
  
let schedule il = 
  let dg = compute_dependency_graph il in
  let deco_dg = compute_priority dg in
  let new_block = simulate deco_dg in
  new_block

(* experimentation *)

let sched_pres func =

  let rec sched_aux code buf =
    match code with
      | [] -> schedule buf
      | Mlabel lbl as i :: l -> schedule buf @ i :: sched_aux l []
      | Mcond _ as i :: l -> schedule buf @ i :: sched_aux l []
      | Mgoto _ as i :: l -> schedule buf @ i :: sched_aux l []
      | Mreturn as i :: l ->  schedule buf @ i :: sched_aux l []
      | Mcall _ as i :: l ->  schedule buf @ i :: sched_aux l []
      | i :: l -> sched_aux l (buf @ i :: [])

  in
    sched_aux func []

let schedule_code func =
  if triggered 0 then 
  (let func = to_caml func in
  let funcy = sched_pres func in
  Datatypes.Some ((to_coq funcy):Mach.code))
  else Datatypes.Some func
(*  Printf.printf "Block_scheduler in\n%!";
  let func = to_caml func in
  let funcy = sched_pres func in
    if (funcy = func) then print_string "trivial" else print_string "not trivial";
    Printf.printf "Block_scheduler out\n%!";
    Datatypes.Some ((to_coq funcy):Mach.code)
*)


(* un faux scheduler pour les tests *)

let sched_pres_rev func =

  let rec sched_aux code buf =
    match code with
      | [] -> schedule buf
      | Mlabel lbl as i :: l -> (List.rev (schedule buf)) @ i :: sched_aux l []
      | Mcond _ as i :: l -> (List.rev (schedule buf)) @ i :: sched_aux l []
      | Mgoto _ as i :: l -> (List.rev (schedule buf)) @ i :: sched_aux l []
      | Mreturn as i :: l ->  (List.rev (schedule buf)) @ i :: sched_aux l []
      | Mcall _ as i :: l ->  (List.rev (schedule buf)) @ i :: sched_aux l []
      | i :: l -> sched_aux l (buf @ i :: [])

  in
    sched_aux func []

let shcedule_wrong func = 
  Printf.printf "Faux Block_scheduler in\n%!";
  let func = to_caml func in
  let funcy = sched_pres_rev func in
    if (funcy = func) then print_string "trivial" else print_string "not trivial";
    Printf.printf "Faux Block_scheduler out\n%!";
    Datatypes.Some ((to_coq funcy):Mach.code)

(* generalisation a la fonction *)
(*
let schedule_code func =
  Printf.printf "Block_scheduler in\n%!";
  let func = to_caml func in
  print_code func ; print_string "coucou\n%!";
  let blocks = chop_code func in
  let scheduled_block_set  = List.map schedule blocks in
  let func = List.flatten scheduled_block_set in
    print_code func;
  Printf.printf "Block_scheduler out\n%!";
  Datatypes.Some ((to_coq func):Mach.code)
*)
(*
let schedule_code func = Datatypes.Some func
*)
