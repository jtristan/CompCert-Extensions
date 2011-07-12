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
open Floats
open Integers
open CList
open Maps
open Op
open RTL
open Registers
open Specif

let debug = false

type valnum = positive

type rhs =
  | Op of operation * valnum list
  | Load of memory_chunk * addressing * valnum list

(** val rhs_rect : (operation -> valnum list -> 'a1) -> (memory_chunk ->
                   addressing -> valnum list -> 'a1) -> rhs -> 'a1 **)

let rhs_rect f f0 = function
  | Op (x, x0) -> f x x0
  | Load (x, x0, x1) -> f0 x x0 x1

(** val rhs_rec : (operation -> valnum list -> 'a1) -> (memory_chunk ->
                  addressing -> valnum list -> 'a1) -> rhs -> 'a1 **)

let rhs_rec f f0 = function
  | Op (x, x0) -> f x x0
  | Load (x, x0, x1) -> f0 x x0 x1

(** val eq_valnum : valnum -> valnum -> bool **)

let eq_valnum x y =
  peq x y

(** val eq_list_valnum : valnum list -> valnum list -> bool **)

let rec eq_list_valnum l y =
  match l with
    | Coq_nil ->
        (match y with
           | Coq_nil -> true
           | Coq_cons (v, l0) -> false)
    | Coq_cons (a, l0) ->
        (match y with
           | Coq_nil -> false
           | Coq_cons (v, l1) ->
               (match eq_valnum a v with
                  | true -> eq_list_valnum l0 l1
                  | false -> false))

(** val eq_rhs : rhs -> rhs -> bool **)

let eq_rhs = fun (x: rhs) (y: rhs) -> x = y

type numbering = { num_next : valnum; num_eqs : (valnum, rhs) prod list;
                   num_reg : valnum Maps.PTree.t }

(** val numbering_rect : (valnum -> (valnum, rhs) prod list -> valnum
                         Maps.PTree.t -> 'a1) -> numbering -> 'a1 **)

let numbering_rect f n =
  let { num_next = x; num_eqs = x0; num_reg = x1 } = n in f x x0 x1

(** val numbering_rec : (valnum -> (valnum, rhs) prod list -> valnum
                        Maps.PTree.t -> 'a1) -> numbering -> 'a1 **)

let numbering_rec f n =
  let { num_next = x; num_eqs = x0; num_reg = x1 } = n in f x x0 x1

(** val num_next : numbering -> valnum **)

let num_next x = x.num_next

(** val num_eqs : numbering -> (valnum, rhs) prod list **)

let num_eqs x = x.num_eqs

(** val num_reg : numbering -> valnum Maps.PTree.t **)

let num_reg x = x.num_reg

(** val empty_numbering : numbering **)

let empty_numbering =
  { num_next = Coq_xH; num_eqs = Coq_nil; num_reg = Maps.PTree.empty }

(** val valnum_reg : numbering -> reg -> (numbering, valnum) prod **)

let valnum_reg n r =
  match Maps.PTree.get r n.num_reg with
    | Some v -> Coq_pair (n, v)
    | None -> Coq_pair ({ num_next = (coq_Psucc n.num_next); num_eqs =
        n.num_eqs; num_reg = (Maps.PTree.set r n.num_next n.num_reg) },
        n.num_next)

(** val valnum_regs : numbering -> reg list -> (numbering, valnum list) prod **)

let rec valnum_regs n = function
  | Coq_nil -> Coq_pair (n, Coq_nil)
  | Coq_cons (r1, rs) ->
      let Coq_pair (n1, v1) = valnum_reg n r1 in
      let Coq_pair (ns, vs) = valnum_regs n1 rs in
      Coq_pair (ns, (Coq_cons (v1, vs)))

(** val find_valnum_rhs : rhs -> (valnum, rhs) prod list -> valnum option **)

let rec find_valnum_rhs r = function
  | Coq_nil -> None
  | Coq_cons (p, eqs1) ->
      let Coq_pair (v, r') = p in
      (match eq_rhs r r' with
         | true -> Some v
         | false -> find_valnum_rhs r eqs1)

(** val add_rhs : numbering -> reg -> rhs -> numbering **)

let add_rhs n rd rh =
  match find_valnum_rhs rh n.num_eqs with
    | Some vres -> { num_next = n.num_next; num_eqs = n.num_eqs; num_reg =
        (Maps.PTree.set rd vres n.num_reg) }
    | None -> { num_next = (coq_Psucc n.num_next); num_eqs = (Coq_cons
        ((Coq_pair (n.num_next, rh)), n.num_eqs)); num_reg =
        (Maps.PTree.set rd n.num_next n.num_reg) }

(** val add_op : numbering -> reg -> operation -> reg list -> numbering **)

let add_op n rd op rs =
  match op with
    | Omove ->
        (match rs with
           | Coq_nil ->
               let Coq_pair (n1, vs) = valnum_regs n rs in
               add_rhs n1 rd (Op (op, vs))
           | Coq_cons (arg, l) ->
               (match l with
                  | Coq_nil ->
                      let Coq_pair (n1, v) = valnum_reg n arg in
                      { num_next = n1.num_next; num_eqs = n1.num_eqs;
                      num_reg = (Maps.PTree.set rd v n1.num_reg) }
                  | Coq_cons (a, l0) ->
                      let Coq_pair (n1, vs) = valnum_regs n rs in
                      add_rhs n1 rd (Op (op, vs))))
    | Ointconst i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ofloatconst f ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oaddrsymbol (i, i0) ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oaddrstack i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ocast8signed ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ocast8unsigned ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ocast16signed ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ocast16unsigned ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oadd ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oaddimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Osub ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Osubimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Omul ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Omulimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Odiv ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Odivu ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oand ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oandimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oor ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oorimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oxor ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oxorimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Onand ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Onor ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Onxor ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oshl ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oshr ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oshrimm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oshrximm i ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oshru ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Orolm (i, i0) ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Onegf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oabsf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Oaddf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Osubf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Omulf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Odivf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Omuladdf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Omulsubf ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Osingleoffloat ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ointoffloat ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ofloatofint ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ofloatofintu ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))
    | Ocmp c ->
        let Coq_pair (n1, vs) = valnum_regs n rs in
        add_rhs n1 rd (Op (op, vs))

(** val add_load : numbering -> reg -> memory_chunk -> addressing -> reg list
                   -> numbering **)

let add_load n rd chunk addr rs =
  let Coq_pair (n1, vs) = valnum_regs n rs in
  add_rhs n1 rd (Load (chunk, addr, vs))

(** val add_unknown : numbering -> reg -> numbering **)

let add_unknown n rd =
  { num_next = (coq_Psucc n.num_next); num_eqs = n.num_eqs; num_reg =
    (Maps.PTree.set rd n.num_next n.num_reg) }

(** val kill_load_eqs : (valnum, rhs) prod list -> (valnum, rhs) prod list **)

let rec kill_load_eqs = function
  | Coq_nil -> Coq_nil
  | Coq_cons (v_rh, rem) ->
      let Coq_pair (v, r) = v_rh in
      (match r with
         | Op (o, l) -> Coq_cons (v_rh, (kill_load_eqs rem))
         | Load (m, a, l) -> kill_load_eqs rem)

(** val kill_loads : numbering -> numbering **)

let kill_loads n =
  { num_next = n.num_next; num_eqs = (kill_load_eqs n.num_eqs); num_reg =
    n.num_reg }

(** val reg_valnum : numbering -> valnum -> reg option **)

let reg_valnum n vn =
  Maps.PTree.fold (fun res r v ->
    match peq v vn with
      | true -> Some r
      | false -> res) n.num_reg None

(** val find_rhs : numbering -> rhs -> reg option **)

let find_rhs n rh =
  match find_valnum_rhs rh n.num_eqs with
    | Some vres -> reg_valnum n vres
    | None -> None

(** val find_op : numbering -> operation -> reg list -> reg option **)

let find_op n op rs =
  let Coq_pair (n1, vl) = valnum_regs n rs in find_rhs n1 (Op (op, vl))

(** val find_load : numbering -> memory_chunk -> addressing -> reg list ->
                    reg option **)

let find_load n chunk addr rs =
  let Coq_pair (n1, vl) = valnum_regs n rs in
  find_rhs n1 (Load (chunk, addr, vl))

module Numbering = 
 struct 
  type t = numbering
  
  (** val top : numbering **)
  
  let top =
    empty_numbering
 end

module Solver = Kildall.BBlock_solver(Numbering)

(** val transfer : coq_function -> node -> numbering -> numbering **)

let transfer f pc before =
  match Maps.PTree.get pc f.fn_code with
    | Some i ->
        (match i with
           | Inop s -> before
           | Iop (op, args, res, s) -> add_op before res op args
           | Iload (chunk, addr, args, dst, s) ->
               add_load before dst chunk addr args
           | Istore (chunk, addr, args, src, s) -> kill_loads before
           | Icall (sig0, ros, args, res, s) -> empty_numbering
           | Itailcall (sig0, ros, args) -> empty_numbering
           | Ialloc (arg, res, s) -> add_unknown before res
           | Icond (cond, args, ifso, ifnot) -> before
           | Ireturn optarg -> before)
    | None -> before

(** val analyze : coq_function -> numbering Maps.PMap.t **)

let analyze f =
  match Solver.fixpoint (successors f) f.fn_nextpc 
          (transfer f) f.fn_entrypoint with
    | Some res -> res
    | None -> Maps.PMap.init empty_numbering

(** val is_trivial_op : operation -> bool **)

let is_trivial_op = function
  | Omove -> true
  | Ointconst i -> true
  | Ofloatconst f -> false
  | Oaddrsymbol (i, i0) -> true
  | Oaddrstack i -> true
  | Ocast8signed -> false
  | Ocast8unsigned -> false
  | Ocast16signed -> false
  | Ocast16unsigned -> false
  | Oadd -> false
  | Oaddimm i -> false
  | Osub -> false
  | Osubimm i -> false
  | Omul -> false
  | Omulimm i -> false
  | Odiv -> false
  | Odivu -> false
  | Oand -> false
  | Oandimm i -> false
  | Oor -> false
  | Oorimm i -> false
  | Oxor -> false
  | Oxorimm i -> false
  | Onand -> false
  | Onor -> false
  | Onxor -> false
  | Oshl -> false
  | Oshr -> false
  | Oshrimm i -> false
  | Oshrximm i -> false
  | Oshru -> false
  | Orolm (i, i0) -> false
  | Onegf -> false
  | Oabsf -> false
  | Oaddf -> false
  | Osubf -> false
  | Omulf -> false
  | Odivf -> false
  | Omuladdf -> false
  | Omulsubf -> false
  | Osingleoffloat -> false
  | Ointoffloat -> false
  | Ofloatofint -> false
  | Ofloatofintu -> false
  | Ocmp c -> false

(** val transf_instr : numbering -> instruction -> instruction **)

let transf_instr n instr = match instr with
  | Inop n0 -> instr
  | Iop (op, args, res, s) ->
      (match is_trivial_op op with
         | true -> instr
         | false ->
             (match find_op n op args with
                | Some r -> Iop (Omove, (Coq_cons (r, Coq_nil)), res, s)
                | None -> instr))
  | Iload (chunk, addr, args, dst, s) -> instr
      (* (match find_load n chunk addr args with
         | Some r -> Iop (Omove, (Coq_cons (r, Coq_nil)), dst, s)
         | None -> instr) *)
  | Istore (m, a, l, r, n0) -> instr
  | Icall (s, s0, l, r, n0) -> instr
  | Itailcall (s, s0, l) -> instr
  | Ialloc (r, r0, n0) -> instr
  | Icond (c, l, n0, n1) -> instr
  | Ireturn o -> instr

(** val transf_code : numbering Maps.PMap.t -> code -> code **)

let transf_code approxs instrs =
  Maps.PTree.map (fun pc instr ->
    transf_instr (Maps.PMap.get pc approxs) instr) instrs

(** val transf_function : coq_function -> coq_function **)

let transf_function f =
  Printf.printf "Extended value numbering : ";
  if Compcert_trigger.triggered 3 = false
  then (Printf.printf "off\n"; fn_code f)
  else 
    begin
      Printf.printf "on\n";

  let g = transf_code (analyze f) f.fn_code in
  if debug then 
    (
      Analysis.print_cfg (f.fn_code) (f.fn_entrypoint);
      Analysis.print_cfg g (f.fn_entrypoint)
    ) ; 
  g
    end
(*
let transf_function f =
  { fn_sig = f.fn_sig; fn_params = f.fn_params; fn_stacksize =
    f.fn_stacksize; fn_code = (transf_code (analyze f) f.fn_code);
    fn_entrypoint = f.fn_entrypoint; fn_nextpc = f.fn_nextpc }
*)
(** val transf_fundef : fundef -> fundef **)

let transf_fundef = function
  | Internal f0 -> Internal (transf_function f0)
  | External ef -> External ef

(** val transf_program : program -> program **)

let transf_program p =
  transform_program transf_fundef p

