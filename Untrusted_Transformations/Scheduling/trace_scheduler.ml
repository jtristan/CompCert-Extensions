
let schedule_code code = 
  match Block_scheduler.schedule_code code with
    | Datatypes.Some tc -> tc
    | Datatypes.None -> failwith "echec ordonnacement"
 

(* Premiere partie : calcul du graphe de dependance *)
(*
module DGraph = Graph.Make ( 
  struct 
    type t = Mach.instruction 
    let print_content = fun x -> ()
  end)
  
let schedule_to_code graph schedule =
    
  let invert invschedule =
    let schedule = Hashtbl.create (Hashtbl.length invschedule) in
    let f a b sched = Hashtbl.add sched b a; sched in 
    Hashtbl.fold f invschedule schedule in

  let schedule = invert schedule in
  
  let rec insert a b = function
      (a',_) as e :: l -> 
	if a' < a 
	then e :: insert a b l
	else (a,b) :: e :: l
    | [] -> [(a,b)] in
  
  let schedule = Hashtbl.fold insert schedule [] in
  
    let l = List.map snd schedule in
    List.map (DGraph.get_datum graph) l
      

  let compute_trace_sched_dependency_graph block =
    
    let last_to_write = Hashtbl.create 10 
    and last_to_read = Hashtbl.create 10 
    and last_if = ref None 
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
    and reset_last_tr reg =    
      if Hashtbl.mem last_to_read reg then
	Hashtbl.replace last_to_read reg []
      else () 
    and set_last_if node = 
      last_if := Some node
    and get_last_if () = !last_if

    in
      
    let rec iter_block graph = function 
	[] -> graph
      | instr :: block ->
	  let reads,writes = Ppcutils.reads_writes instr in
	  let (node,graph) = DGraph.add_node graph instr in
	  
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
	  
	  (* trace if dependency *)
	  
	  let graph = match get_last_if () with 
	      Some instr2 -> DGraph.add_arrow graph instr2 node
	    | None -> graph in

	  (* update the last_to_write registration *)
	  
	  List.iter (fun reg -> set_last reg node) writes;
	  List.iter (fun reg -> set_last_tr reg node) reads;
	  List.iter (fun reg -> reset_last_tr reg) writes;
	  if (match instr with PPC.Pbt _ | PPC.Pbf _ -> true | _ -> false)
	  then set_last_if node;
	  
	  iter_block graph block 
    in 
    
    
    let graph = iter_block graph block in 
            
(*     Printf.printf "______________________________\n"; *)
(*     Printf.printf "taille du bloc : %i, taille de dg : %i\n%!" (List.length block) (DGraph.size graph); *)
(*     DGraph.print_graph graph; *)
(*     Printf.printf "______________________________\n";     *)

      graph

(* deuxieme partie : ordonnancement d une trace *)

  let compute_priority = fun x -> x
 
  let choose graph l = let l = List.rev l in (List.tl l,List.hd l)  

  let simulate graph =
    
    let cycle = 1 
    and graph_cpy = LibScheduling.DGraph.copy graph
    and ready = LibScheduling.DGraph.get_roots graph
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
	  Hashtbl.find schedule node + Ppcutils.latency (LibScheduling.DGraph.get_datum graph node) < cycle in
	
	let still_active = List.filter (fun e -> not (processed e)) active
	and finished = List.filter processed active in
	let graph = List.fold_left (fun g n -> LibScheduling.DGraph.del_node g n) graph finished in 
	let new_ready = LibScheduling.DGraph.get_roots graph in
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
	List.map (LibScheduling.DGraph.get_datum graph_cpy) l
  
  let schedule_bis il= 
    let dg = LibScheduling.compute_trace_sched_dependency_graph il in
    let deco_dg = compute_priority dg in
    let new_block = simulate deco_dg in
      new_block


(* troisieme partie : bookkeeping *)

  module A = Array
  
  (* stubs is the placeholder for all the stubs we are generating *)

  let stubs = ref []

  let move_join_points link tab1 tab2 = 
    let size = A.length tab1 in
    for i = 0 to size - 1 do
      match A.get tab1 i with
	  PPC.Plabel lbl -> 
	    let join = i and
		join' = ref (link i) in
	      for j = 0 to join - 1 do
		if link j < !join' 
		then ()
		else 
		  let content = A.get tab2 !join' in
		  let () = for k = !join' to link j - 1 do
		    A.set tab2 k (A.get tab2 (k + 1))
		  done in
		  let () = A.set tab2 (link j) content in 
		  let () = join' := (link j) in ()
	      done
	| _ -> ()
    done
      


  let split_bookkeeping link tab1 tab2 =
    let size = A.length tab1 in
    
      (* for each split, we look at every instruction that may have gone 
	 below. If it is the case, we place a copy of this instruciton in a
	 stub. Finally the stub gets relabelized *)



      for i = 0 to size - 1 do
	match A.get tab1 i with
	    PPC.Pbt (c,lbl) ->
	      let stub = ref [] in
	      	for j = 0 to i - 1 do
		  if link j < link i then ()
		  else match A.get tab1 j with 
		      PPC.Plabel _ -> ()
		    | _ -> stub := (A.get tab1 j) :: !stub
		done;
	      (*Printf.fprintf stdout "split - bt \n";*)
		if List.length !stub = 0 then () else
		let stub = (PPC.Pb lbl) :: !stub in
		let stub = List.rev stub in
		let label = Ppcutils.fresh_label () in
		let stub = (PPC.Plabel label) :: stub in
		  stubs := stub :: !stubs;
		  A.set tab2 (link i) (PPC.Pbt (c,label))
	  | PPC.Pbf (c,lbl) ->
	      let stub = ref [] in
	      for j = 0 to i - 1 do
		if link j < link i then ()
		else match A.get tab1 j with 
		    PPC.Plabel _ -> ()
		  | _ ->stub := (A.get tab1 j) :: !stub
	      done;
	      (*Printf.fprintf stdout "split - bf \n";*)
	      if List.length !stub = 0 then () else
		let stub = (PPC.Pb lbl) :: !stub in
		let stub = List.rev stub in
		let label = Ppcutils.fresh_label () in
		let stub = (PPC.Plabel label) :: stub in
		stubs := stub :: !stubs;
		A.set tab2 (link i) (PPC.Pbf (c,label))
	  | PPC.Pb lbl -> 
	      let stub = ref [] in
	      	for j = 0 to i - 1 do
		  if link j < link i then ()
		  else match A.get tab1 j with 
		      PPC.Plabel _ -> ()
		    | _ ->stub := (A.get tab1 j) :: !stub
		done;
	      (*Printf.fprintf stdout "split - b \n";*)
		if List.length !stub = 0 then () else
		let stub = (PPC.Pb lbl) :: !stub in
		let stub = List.rev stub in
		let label = Ppcutils.fresh_label () in
		let stub = (PPC.Plabel label) :: stub in
		  stubs := stub :: !stubs;
		  A.set tab2 (link i) (PPC.Pb label)
	  | PPC.Pbctr -> 
	      let stub = ref [] in
	      	for j = 0 to i - 1 do
		  if link j < link i then ()
		  else match A.get tab1 j with 
		      PPC.Plabel _ -> ()
		    | _ ->stub := (A.get tab1 j) :: !stub
		done;
		(*Printf.fprintf stdout "split - bctr \n";*)
		if List.length !stub = 0 then () else
		let stub = (PPC.Pbctr) :: !stub in
		let stub = List.rev stub in
		let label = Ppcutils.fresh_label () in
		let stub = (PPC.Plabel label) :: stub in
		  stubs := stub :: !stubs;
		  A.set tab2 (link i) (PPC.Pb label)
	  | _ -> ()
      done	



  let get_real_label label =
    let f = fun l -> match List.hd l with PPC.Plabel lbl -> lbl = label | _ -> false in
    let stub = List.find f !stubs in
      (*Printf.printf "le stub de split : \n";*)
      (*Ppcutils.print_code stub;*)
    let stub = List.rev stub in
      match List.hd stub with
	  PPC.Pb lbl -> lbl
	| _ -> failwith "didn t find label ! \n"

  let join_bookkeeping link tab1 tab2 = 
    let size = A.length tab1 in
      
      for i = 0 to size - 1 do
	match A.get tab1 i with
	    PPC.Plabel l ->
	      let stub = ref [] in
	      	for j = i + 1 to size -1 do
		  if link j = link i then failwith "probleme";
		  if link j > link i then ()
		  else 
		    match A.get tab2 (link j) with
			PPC.Pbt (c,lbl) ->
			  let stub' = ref [] in
			  for k = i to j - 1 do
			    if link k < link j then ()
			    else match A.get tab1 k with
				PPC.Plabel _ -> () 
			      | _ -> if link k > link i then
				    stub' := (A.get tab2 (link k)) :: !stub'
			  done;
			  (*Printf.fprintf stdout "!!!!!spec - bt \n";*)
			  if List.length !stub' = 0 then () else
			    let label = Ppcutils.fresh_label () in
			    let lab = get_real_label lbl in
			    let stub' = (PPC.Pb lab) :: !stub' in
			    let stub' = List.rev stub' in
			    let stub' = (PPC.Plabel label) :: stub' in
			    stubs := stub' :: !stubs;
			    stub := (PPC.Pbt (c,label)) :: !stub
		      | PPC.Pbf (c,lbl) ->
			  let stub' = ref [] in
			  for k = i to j - 1 do
			    if link k < link j then ()
			    else match A.get tab1 k with
				PPC.Plabel _ -> () 
			      | _ ->if link k > link i then
				  stub' := (A.get tab1 k) :: !stub'
			  done;
			    (*Printf.fprintf stdout "!!!!!spec - bf \n";*)
			  if List.length !stub' = 0 then () else
			    let label = Ppcutils.fresh_label () in
			    let lab = get_real_label lbl in
			    let stub' = (PPC.Pb lab) :: !stub' in
			    let stub' = List.rev stub' in
			    let stub' = (PPC.Plabel label) :: stub' in
			    stubs := stub' :: !stubs;
			    stub := (PPC.Pbf (c,label)) :: !stub
		      | PPC.Pb lbl ->
			  let stub' = ref [] in
			  for k = i to j - 1 do
			    if link k < link j then ()
			    else match A.get tab1 k with
				PPC.Plabel _ -> () 
			      | _ -> if link k > link i then
				  stub' := (A.get tab1 k) :: !stub'
			  done;
			    (*Printf.fprintf stdout "!!!!!spec - b \n";*)
			    if List.length !stub' = 0 then () else
			    let label = Ppcutils.fresh_label () in
			    let lab = get_real_label lbl in
			    let stub' = (PPC.Pb lab) :: !stub' in
			    let stub' = List.rev stub' in
			    let stub' = (PPC.Plabel label) :: stub' in
			      (*Printf.printf "le nouveau : \n";*)
			      (*Ppcutils.print_code stub';*)
			      stubs := stub' :: !stubs;
			      stub := (PPC.Pb label) :: !stub
		      | PPC.Pbctr ->
			  let stub' = ref [] in
			    for k = i to j - 1 do
			      if link k < link j then ()
			      else match A.get tab1 k with
				  PPC.Plabel _ -> () 
				| _ ->if link k > link i then
				    stub' := (A.get tab1 k) :: !stub'
			    done;
			    (*Printf.fprintf stdout "!!!!!spec - bctr \n";*)
			    if List.length !stub' = 0 then () else
			    let label = Ppcutils.fresh_label () in
			    let stub' = (PPC.Pbctr) :: !stub' in
			    let stub' = List.rev stub' in
			    let stub' = (PPC.Plabel label) :: stub' in
			      stubs := stub' :: !stubs;
			      stub := (PPC.Pb label) :: !stub
		      | instr -> stub := instr :: !stub 
		done;
		(*Printf.fprintf stdout "join -  \n";*)
		if List.length !stub = 0 then () else
		let label = Ppcutils.fresh_label () in
		let stub = (PPC.Pb label) :: !stub in
		let stub = List.rev stub in
		let stub = (PPC.Plabel l) :: stub in
		  (* Printf.printf "le stub de join : \n"; *)
(* 		  Printf.printf "----------"; *)
(* 		  Ppcutils.print_code stub; *)
(* 		  Printf.printf "----------"; *)
		  stubs := stub :: !stubs;
		  A.set tab2 (link i) (PPC.Plabel label)
	  | _ -> ()
      done

  let pack trace = 
(*     match List.hd trace with *)
(* 	PPC.Plabel l -> List.flatten !stubs @ trace *)
(*       | _ -> *) 
	  if not (List.length !stubs = 0) 
	  then
	    let label = Ppcutils.fresh_label () in
	    [PPC.Pb label] @ List.flatten !stubs @ [PPC.Plabel label] @ trace
	  else
	    trace
	      
  let link tab1 tab2 =
    let size = A.length tab1 in
    let link = A.create size 0 in
    let used = A.create size false in
    let placed = ref false in
      Array.iteri (fun pos -> fun e ->
		     placed := false ;
		     for i = 0 to size - 1 do
		       if A.get tab2 i = e && not (A.get used i) && not !placed
		       then (
			 A.set link pos i ;
			 A.set used i true ;
			 placed := true
		       ) 
		     done
		  ) tab1;
      link

(* fonction finale : prend une trace et en retourne une ordonnancee *)

  let schedule il = 
    
    (* Printf.printf "New block received : \n%!"; *)
(*     Ppcutils.print_code il; *)

    stubs := [];
    let sched = ListScheduling.schedule_bis il in
    

    (*   Printf.printf "a reparer : \n"; *)
(*       Ppcutils.print_code sched; *)

    let size = List.length il in
    let tab1 = A.of_list il and
	tab2 = A.of_list sched in
    let link = link tab1 tab2 in
      
    let link = A.get link in 

(*       Printf.fprintf stdout "\nDEBUT\n"; *)
     (*  Printf.printf "------------------------------------------------\n"; *)
(*       Printf.printf "la trace : \n";  *)
(*       Ppcutils.print_code il;  *)
      
(*       Printf.fprintf stdout "\nmove\n"; *)



      move_join_points link tab1 tab2 ; 



(*       Printf.printf "apres le move du join : \n"; *)
(*       Ppcutils.print_code (A.to_list tab2); *)
      
      
(*       List.iter (fun e -> match e with PPC.Plabel lbl -> Printf.fprintf stdout "label : %d - " (Int32.to_int (Camlcoq.camlint_of_positive lbl)) | _ -> ()) (A.to_list tab2); *)
(*       Printf.fprintf stdout "taille : %i\n" (List.length !stubs); *)
(*       List.iter (fun e -> match e with PPC.Plabel lbl -> Printf.fprintf stdout "label : %d - " (Int32.to_int (Camlcoq.camlint_of_positive lbl)) | _ -> ()) (List.flatten !stubs); *)
(*       Printf.fprintf stdout "\n - split - \n"; *)
      
      split_bookkeeping link tab1 tab2 ; 
    

  
(*       List.iter (fun e -> match e with PPC.Plabel lbl -> Printf.fprintf stdout "label : %d - " (Int32.to_int (Camlcoq.camlint_of_positive lbl)) | _ -> ()) (A.to_list tab2); *)
(*       Printf.fprintf stdout "taille : %i\n" (List.length !stubs); *)
(*       List.iter (fun e -> match e with PPC.Plabel lbl -> Printf.fprintf stdout "label : %d - " (Int32.to_int (Camlcoq.camlint_of_positive lbl)) | _ -> ()) (List.flatten !stubs);  *)
(*       Printf.fprintf stdout "\n - join - \n"; *)
      
      join_bookkeeping link tab1 tab2 ; 
      


(*       List.iter (fun e -> match e with PPC.Plabel lbl -> Printf.fprintf stdout "label : %d - " (Int32.to_int (Camlcoq.camlint_of_positive lbl)) | _ -> ()) (A.to_list tab2); *)
(*       Printf.fprintf stdout " taille : %i\n" (List.length !stubs);  *)
(*       List.iter (fun e -> match e with PPC.Plabel lbl -> Printf.fprintf stdout "label : %d - " (Int32.to_int (Camlcoq.camlint_of_positive lbl)) | _ -> ()) (List.flatten !stubs); *)
(*       Printf.fprintf stdout "\nFIN\n"; *)
      
      let trace = A.to_list tab2 in
      let trace = pack trace in
	
(* 	Printf.printf "la trace obtenue : \n"; *)
(* 	Ppcutils.print_code trace; *)
(* 	Printf.printf "------------------------------------------------\n"; *)

(*       Printf.printf "---------------------------------------"; *)
(*       Ppcutils.print_code il; *)
(*       Printf.printf "---------------------------------------"; *)
(*       Ppcutils.print_code trace; *)
(*       Printf.printf "---------------------------------------"; *)

	trace
      
*)
