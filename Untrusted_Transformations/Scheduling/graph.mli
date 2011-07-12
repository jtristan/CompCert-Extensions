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


(** Graph implementation used both for cfgs and dep graphs*)

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

    (** returns an empty graph *)
    val empty_graph : unit -> 'a t
    
    (** add a node to the graph *)
    val add_node : 'a t -> datum -> node * 'a t
    
    (** add an arrow to the graph *)
    val add_arrow : 'a t -> node -> node -> 'a t
    
    (** delete a node ??? *)
    val del_node : 'a t -> node -> 'a t
    
    (** returns the list of roots of a fraph, i.e. the ones without predecessors*)
    val get_roots : 'a t -> node list
    
    (** returns all the transitiv successors of a node *)
    val trans_sons : 'a t -> node -> node list
    
    (** associate a piece of information to a node *)
    val set_information : 'a t -> node -> 'a -> 'a t
    
    (** returns the information associated to a node *)
    val get_information : 'a t -> node -> 'a option 
    
    (** pretty printing of the graph *)
    val print_graph : 'a t -> unit
    
    (** returns the cardinal of a graph *)
    val size : 'a t -> int
    
    (** return the content of a node *)
    val get_datum : 'a t -> node -> datum
    
    (** returns a copy of the graph *)
    val copy : 'a t -> 'a t
    
    (** iteration over the graph nodes *)
    val iter : 'a t -> (node -> unit) -> unit (* returned type is not coherent ! *)
    
    (** returns the list of all the nodes in the graph *)
    val all_nodes : 'a t -> node list

    (** restrected folding over graph *)
    val fold : ('a t -> node -> 'a t) -> 'a t -> 'a t
    
    (** returns the list of successors of a node *)
    val node_sons : 'a t -> node -> node list
    
    (** debuggung utility *)
    val print_node : node -> unit
    
    (** returns the list of predecessors of a node *)
    val predecessors : 'a t -> node -> node list

    (** returns all the cycles (may be redundant *)
    val get_cycles : 'a t -> node list list

    (** returns the dominator tree  *)
    val dominator_tree : 'a t -> datum -> node option array

    (** returns the list of all the back edges targets *)
    val back_edges : 'a t -> datum -> ( node * node )list
    
    (** deletes teh given arrow from the graph *)
    val del_arrow : 'a t -> node * node -> 'a t

    (** raw printing of the graph *)
    val print_graph2 : 'a t -> unit 

    (** find all the nodes holding the given datum *)
    val find : 'a t -> datum -> node list

  end

module Make (GC : GraphContent) : S with type datum = GC.t  
