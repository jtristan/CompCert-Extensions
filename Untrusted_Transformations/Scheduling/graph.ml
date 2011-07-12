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


module type GraphContent =
sig
  type t
  val print_content : t -> unit
end

module type S =
sig
  
  (* type info *) 
  type node 
  type datum 
  type 'a t
  exception Graph of string
    
  val empty_graph : unit -> 'a t
  val add_node : 'a t -> datum -> node * 'a t
  val add_arrow : 'a t -> node -> node -> 'a t
  val del_node : 'a t -> node -> 'a t
  val get_roots : 'a t -> node list
  val trans_sons : 'a t -> node -> node list
  val set_information : 'a t -> node -> 'a -> 'a t
  val get_information : 'a t -> node -> 'a option 
  val print_graph : 'a t -> unit
  val size : 'a t -> int
  val get_datum : 'a t -> node -> datum
  val copy : 'a t -> 'a t
  val iter : 'a t -> (node -> unit) -> unit (* returned type is not coherent ! *)
  val all_nodes : 'a t -> node list
  val fold : ('a t -> node -> 'a t) -> 'a t -> 'a t
  val node_sons : 'a t -> node -> node list
  val print_node : node -> unit
  val predecessors : 'a t -> node -> node list  
  val get_cycles : 'a t -> node list list
  val dominator_tree : 'a t -> datum -> node option array
  val back_edges : 'a t -> datum -> (node * node) list    
  val del_arrow : 'a t -> node * node -> 'a t  
  val print_graph2 : 'a t -> unit
  val find : 'a t -> datum -> node list

end

module Make (GC : GraphContent) : S with type datum = GC.t  =
struct

  open Hashtbl
    
  type datum = GC.t
      (* type info *)  
  type node = int
  
  (* The graph is implmented using the followinf structure.
     It is a Hashtable from integers to a 4-uple containing :
     - a datum, i.e. the piece of data that the node contains
     - a node list, i.e. the successors of this node
     - an int, the number of predecessors (here for efficiency reasons)
     - an option that let the user put a piece of information easily 
     Note the arrows structure that record every arrow (here for efficiency reasons) *)
  

  (* this is a nasty hack ! i do not delete arrows on del_node because 
     del_node and arrows corresponf to two distincts use of this graph
     HUGH *)

  (* requiring two graphs in the same time does not longer make sense, 
     HUGH, HUGH, HUGH ! *) 
	 

  let arrows = ref []
    
  type 'a t = (node,datum * node list * int * 'a option) Hashtbl.t
  exception Graph of string
    
  let node_pool = ref (-1)
    
  let fresh_node () = incr node_pool; !node_pool
    
  let empty_graph () = node_pool := -1 ; arrows := [] ; Hashtbl.create 10 
    
  let add_node graph datum = 
    let id = fresh_node () in 
    add graph id (datum,[],0,None); (id,graph)
      
  let node_datum graph node =
    match (find graph node) with
	(datum,_,_,_) -> datum
	    
  let node_sons graph node =
    if mem graph node 
    then match (find graph node) with
	(_,l,_,_) -> l
    else []
    
  let node_deps graph node = 
    if mem graph node 
    then match (find graph node) with
	(_,_,i,_) -> i
    else 0
      
  let node_info graph node =
    if mem graph node 
    then match (find graph node) with
	(_,_,_,info) -> info
    else None
      
  (* test if already exist an arrow is useless *)
      
  let update1 graph node e =
    if List.mem node (node_sons graph node) then (Printf.fprintf stdout "problem  %!";graph)
    else (
      let l = node_sons graph node in
      let l = if List.mem e l then l else e :: l in
      replace graph node (node_datum graph node,l,node_deps graph node,node_info graph node);
      graph)
      
  let update2 graph node f =
    replace graph node (node_datum graph node,node_sons graph node,f (node_deps graph node),node_info graph node);
    graph
      
  let update3 graph node info =
    replace graph node (node_datum graph node,node_sons graph node,node_deps graph node,Some info);
    graph
      
  let add_arrow graph source target =
    if mem graph source && mem graph target
    then 
      let l = node_sons graph source in
      if List.mem target l 
      then graph
      else
	let () = arrows := (source,target) :: !arrows in
	let graph = update1 graph source target in
	let graph = update2 graph target (fun i -> i + 1) in 
	graph
    else graph
      
  let del_node graph node = (* seems incorrect !, every arrow involving node should be deleted *)
    if mem graph node 
    then 
      let graph = List.fold_left (fun g -> fun n -> update2 g n (fun x -> x - 1)) graph (node_sons graph node) in
      (remove graph node ; graph)
    else graph
      
  let del_arrow graph (source,target) = (* new, quicly implemented *)
    let (datum,node_list,num,op) = find graph source in
    let new_list = List.filter (fun e -> not (e = target)) node_list in
    replace graph source (datum,new_list,num,op);
    arrows := List.filter (fun x -> not (x = (source,target))) !arrows;
    graph
	

  let get_roots graph =
    fold (fun node -> fun (_,_,i,_) -> fun l -> if i = 0 then node :: l else l) graph []
      
      
  let print_graph graph = 
    print_string "\n\nGRAPH DUMP :\n\n";
    let print a (datum,nl,i,_) = 
      print_string "\n*****\n";
      GC.print_content datum ; 
      print_int a; print_string " ";
      print_string " --> ";
      List.iter (fun e -> (print_string " ; ";print_int e)) nl ;
      Printf.fprintf stdout "   [%i]" i
    in 
    iter print graph;
    print_string "\n\nEND OF GRAPH DUMP :\n\n";
    flush stdout
      
  (*
    let trans_sons graph node =
    if mem graph node 
    then let rec transitivity graph = function
    [] -> [] 
    | i :: [] -> [i] 
    | l -> List.concat 
    (List.map (fun n -> transitivity graph (node_sons graph n)) l) in
    transitivity graph (node_sons graph node)
    else []
  *)  
      
  let trans_sons graph node =
    let l = ref [] 
    and visited = ref [] in
    if mem graph node 
    then 
      let rec trans node =
	let sons = node_sons graph node in
	if List.length sons = 0 then l := (node :: !l)
	else
	  let sons = List.filter (fun e -> not (List.mem e !visited)) sons in
	  visited := (node :: !visited); 
	  List.iter trans sons in
      trans node; !l
    else []
      
  let set_information = update3
    
  let get_information = node_info
    
    
  let size = length
    
  let get_datum = node_datum 
    
  let copy = copy

  let iter graph f = (iter (fun a _ -> f a) graph)
      
  let all_nodes graph = fold (fun a b l -> a :: l) graph []
    
  let all_arrows = !arrows

  let fold f graph = List.fold_left f graph (all_nodes graph)
    
  let print_node = print_int 

  let predecessors graph node = 
    let f = fun a b l -> 
      let succs = node_sons graph a in
      if List.mem node succs 
      then a :: l else l in
	
    Hashtbl.fold f graph []
      
  let get_cycles graph = 
    
    let rec deep_first_search_cycles visited node =
      let b = ref false in
      if List.mem node visited 
      then 
	let f = fun l elt -> 
	  if !b 
	  then l 
	  else 
	    if elt = node 
	    then (b := true ; l)
	    else elt :: l in
	[List.fold_left f [] visited]
      else List.flatten (List.map (deep_first_search_cycles (node :: visited)) (node_sons graph node)) in
	
    List.flatten (List.map (deep_first_search_cycles []) (all_nodes graph))
	  
  module Doms = Set.Make (struct type t = int let compare = compare end)


  let find cfg datum =
   Hashtbl.fold (fun a (b,_,_,_) l -> if b = datum then (a :: l) else l) cfg []
 
  exception No_single_root

  let root datum cfg = 
    let possible_roots_1 = get_roots cfg in
    let possible_roots_2 = find cfg datum in
    let possible_roots = List.filter (fun e -> List.mem e possible_roots_2) possible_roots_1 in
    if List.length possible_roots = 1 
    then List.hd possible_roots
    else raise No_single_root

  let dominators cfg datum = 
    
    let root = root datum cfg in
    let size = size cfg in
    let all_nodes = List.fold_left (fun s e -> Doms.add e s) Doms.empty (all_nodes cfg) in
    let dom = Array.create size all_nodes in
    (*Printf.printf "size : %i, root : %i" size root;*)
    Array.set dom root (Doms.add root Doms.empty);
    let domref = Array.create size (Doms.empty) in 
    
    while not (List.fold_left2 (fun b s1 s2 -> b && Doms.equal s1 s2) true (Array.to_list dom) (Array.to_list domref)) do 
      Array.blit dom 0 domref 0 size;
      for i = 0 to size - 1 do
	Array.set dom i (List.fold_left (fun s e -> Doms.union (Doms.add i Doms.empty) (Doms.inter s (Array.get dom e))) (Array.get dom i) (predecessors cfg i))
      done
    done;
    dom
      

  let dominator_tree cfg datum =
    
    let doms = dominators cfg datum in
    (*Printf.printf "coucou\n";
    Array.iteri (fun i elt -> (Printf.printf "\n%i " i ; Doms.iter (Printf.printf "%i ") elt)) doms;
    *)
    let size = size cfg in
    let idoms = Array.create size None in
    Array.iteri (fun i s -> Array.set doms i (Doms.remove i s)) doms;
    let root = root datum cfg in
    let i = ref 0 in
    while (!i < size) do
      if Doms.cardinal (Array.get doms !i) = 1 
      then let elt = Doms.choose (Array.get doms !i) in
      Array.set idoms !i (Some elt);
      (*Array.iteri (fun i b -> Printf.printf "(%i,%i) " i (match b with Some k -> k | None -> -1)) idoms;
      print_newline ();*)
      Array.set doms !i (Doms.empty);
      Array.iteri (fun i s -> if (Doms.cardinal s > 1) then Array.set doms i (Doms.remove elt s)) doms; 
      i := 0
      else incr i;
    done;
    idoms

  let print_graph2 cfg =
    Printf.printf "root : %i\n" (List.hd (get_roots cfg));
    Printf.printf "nodes : ";
    List.iter (Printf.printf "%i ") (all_nodes cfg);
    Printf.printf "\narrows : ";
    List.iter (fun (a,b) -> Printf.printf "(%i,%i) " a b) !arrows;
    print_newline ()

  let back_edges cfg datum =
    let dominators = dominators cfg datum in
    let all_nodes = all_nodes cfg in
    let dominator_tree = dominator_tree cfg datum in
    (*
    Printf.printf "\ninformations :\n";
    Array.iteri (fun i e -> Printf.printf "(%i,%i) " i (match e with Some k -> k | None -> -1)) dominator_tree;
    print_newline ();
    print_graph2 cfg;
    *)
    let root = root datum cfg in
    let size = size cfg in
    let rec filter (src,tgt) =
      match Array.get dominator_tree src with
	  None -> false
	| Some daddy -> if daddy = tgt then true else filter (daddy,tgt) in
    let back_edges = List.filter filter !arrows in
    (*Printf.printf "back_edegs rouves :\n";
    List.iter (fun (a,b) -> Printf.printf "(%i,%i) " a b) back_edges ;
    print_newline ();*)
    back_edges

end
