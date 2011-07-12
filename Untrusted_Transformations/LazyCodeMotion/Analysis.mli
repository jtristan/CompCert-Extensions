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


type __ = Obj.t
type expression =
    Op of Op.operation * Registers.reg CList.list
  | Load of AST.memory_chunk * Op.addressing * Registers.reg CList.list

val print_expr : expression -> unit
val print_cfg : RTL.code -> BinPos.positive -> unit
val print_op : Op.operation -> unit
val print_reg_list : BinPos.positive CList.list -> unit
val print_pos : Registers.reg -> unit

module Expression : sig type t = expression val eq_dec : 'a -> 'a -> bool end
module Expressions :
  sig
    module Raw :
      sig
        module E : sig type t = Expression.t val eq_dec : t -> t -> bool end
        type elt = Expression.t
        type t = elt CList.list
        val empty : t
        val is_empty : t -> bool
        val mem : elt -> t -> bool
        val add : elt -> t -> t
        val singleton : elt -> t
        val remove : elt -> t -> t
        val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
        val union : t -> t -> t
        val diff : t -> t -> t
        val inter : t -> t -> t
        val subset : t -> t -> bool
        val equal : t -> t -> bool
        val filter : (elt -> bool) -> t -> t
        val for_all : (elt -> bool) -> t -> bool
        val exists_ : (elt -> bool) -> t -> bool
        val partition : (elt -> bool) -> t -> (t, t) Datatypes.prod
        val cardinal : t -> Datatypes.nat
        val elements : t -> elt CList.list
        val choose : t -> elt Datatypes.option
      end
    module E : sig type t = Expression.t val eq_dec : t -> t -> bool end
    type slist = Raw.t
    val slist_rect : (Raw.t -> FSetWeakList.__ -> 'a) -> slist -> 'a
    val slist_rec : (Raw.t -> FSetWeakList.__ -> 'a) -> slist -> 'a
    val this : slist -> Raw.t
    type t = slist
    type elt = E.t
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val remove : elt -> t -> t
    val singleton : elt -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val empty : t
    val is_empty : t -> bool
    val elements : t -> elt CList.list
    val choose : t -> elt Datatypes.option
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val cardinal : t -> Datatypes.nat
    val filter : (elt -> bool) -> t -> t
    val for_all : (elt -> bool) -> t -> bool
    val exists_ : (elt -> bool) -> t -> bool
    val partition : (elt -> bool) -> t -> (t, t) Datatypes.prod
  end
module Es :
  sig
    module Raw :
      sig
        module E : sig type t = Expression.t val eq_dec : t -> t -> bool end
        type elt = Expression.t
        type t = elt CList.list
        val empty : t
        val is_empty : t -> bool
        val mem : elt -> t -> bool
        val add : elt -> t -> t
        val singleton : elt -> t
        val remove : elt -> t -> t
        val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
        val union : t -> t -> t
        val diff : t -> t -> t
        val inter : t -> t -> t
        val subset : t -> t -> bool
        val equal : t -> t -> bool
        val filter : (elt -> bool) -> t -> t
        val for_all : (elt -> bool) -> t -> bool
        val exists_ : (elt -> bool) -> t -> bool
        val partition : (elt -> bool) -> t -> (t, t) Datatypes.prod
        val cardinal : t -> Datatypes.nat
        val elements : t -> elt CList.list
        val choose : t -> elt Datatypes.option
      end
    module E : sig type t = Expression.t val eq_dec : t -> t -> bool end
    type slist = Raw.t
    val slist_rect : (Raw.t -> FSetWeakList.__ -> 'a) -> slist -> 'a
    val slist_rec : (Raw.t -> FSetWeakList.__ -> 'a) -> slist -> 'a
    val this : slist -> Raw.t
    type t = slist
    type elt = E.t
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val remove : elt -> t -> t
    val singleton : elt -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val empty : t
    val is_empty : t -> bool
    val elements : t -> elt CList.list
    val choose : t -> elt Datatypes.option
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val cardinal : t -> Datatypes.nat
    val filter : (elt -> bool) -> t -> t
    val for_all : (elt -> bool) -> t -> bool
    val exists_ : (elt -> bool) -> t -> bool
    val partition : (elt -> bool) -> t -> (t, t) Datatypes.prod
  end
type dSet = Exp of Es.t | Uni
val dSetUnion : dSet -> dSet -> dSet
val dSetIntersection : dSet -> dSet -> dSet
val beq : dSet -> dSet -> bool
val dBot : dSet
val dTop : dSet
module LFSet :
  sig
    type t = dSet
    val beq : dSet -> dSet -> bool
    val bot : dSet
    val lub : dSet -> dSet -> dSet
  end
module GFSet :
  sig
    type t = dSet
    val beq : dSet -> dSet -> bool
    val bot : dSet
    val lub : dSet -> dSet -> dSet
  end
module Forward_lfp :
  sig
    module L :
      sig
        type t = LFSet.t
        val beq : t -> t -> bool
        val bot : t
        val lub : t -> t -> t
      end
    val fixpoint :
      (BinPos.positive -> BinPos.positive CList.list) ->
      BinPos.positive ->
      (BinPos.positive -> L.t -> 'a) ->
      (BinPos.positive -> L.t -> 'a -> L.t) ->
      (BinPos.positive, L.t) Datatypes.prod CList.list ->
      L.t Maps.PMap.t Datatypes.option
  end
module Forward_gfp :
  sig
    module L :
      sig
        type t = GFSet.t
        val beq : t -> t -> bool
        val bot : t
        val lub : t -> t -> t
      end
    val fixpoint :
      (BinPos.positive -> BinPos.positive CList.list) ->
      BinPos.positive ->
      (BinPos.positive -> L.t -> 'a) ->
      (BinPos.positive -> L.t -> 'a -> L.t) ->
      (BinPos.positive, L.t) Datatypes.prod CList.list ->
      L.t Maps.PMap.t Datatypes.option
  end
module Backward_gfp :
  sig
    module L :
      sig
        type t = LFSet.t
        val beq : t -> t -> bool
        val bot : t
        val lub : t -> t -> t
      end
    module DS :
      sig
        module L :
          sig
            type t = L.t
            val beq : t -> t -> bool
            val bot : t
            val lub : t -> t -> t
          end
        val fixpoint :
          (BinPos.positive -> BinPos.positive CList.list) ->
          BinPos.positive ->
          (BinPos.positive -> L.t -> 'a) ->
          (BinPos.positive -> L.t -> 'a -> L.t) ->
          (BinPos.positive, L.t) Datatypes.prod CList.list ->
          L.t Maps.PMap.t Datatypes.option
      end
    val fixpoint :
      (BinPos.positive -> BinPos.positive CList.list) ->
      BinPos.positive ->
      (BinPos.positive -> DS.L.t -> 'a) ->
      (BinPos.positive -> DS.L.t -> 'a -> DS.L.t) ->
      (BinPos.positive, DS.L.t) Datatypes.prod CList.list ->
      DS.L.t Maps.PMap.t Datatypes.option
  end

val universe : RTL.coq_function -> Es.t
val analysis :
  RTL.coq_function -> (Es.t Maps.PTree.t, Es.t Maps.PTree.t) Datatypes.prod
