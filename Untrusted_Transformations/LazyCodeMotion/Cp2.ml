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
open BinInt
open BinPos
open Bool
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

type approx =
  | Novalue
  | Unknown
  | I of int
  | F of float
  | S of ident * int

(** val approx_rect : 'a1 -> 'a1 -> (int -> 'a1) -> (float -> 'a1) -> (ident
                      -> int -> 'a1) -> approx -> 'a1 **)

let approx_rect f f0 f1 f2 f3 = function
  | Novalue -> f
  | Unknown -> f0
  | I x -> f1 x
  | F x -> f2 x
  | S (x, x0) -> f3 x x0

(** val approx_rec : 'a1 -> 'a1 -> (int -> 'a1) -> (float -> 'a1) -> (ident
                     -> int -> 'a1) -> approx -> 'a1 **)

let approx_rec f f0 f1 f2 f3 = function
  | Novalue -> f
  | Unknown -> f0
  | I x -> f1 x
  | F x -> f2 x
  | S (x, x0) -> f3 x x0

module Approx = 
 struct 
  type t = approx
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    match x with
      | Novalue ->
          (match y with
             | Novalue -> true
             | Unknown -> false
             | I i -> false
             | F f -> false
             | S (i, i0) -> false)
      | Unknown ->
          (match y with
             | Novalue -> false
             | Unknown -> true
             | I i -> false
             | F f -> false
             | S (i, i0) -> false)
      | I x0 ->
          (match y with
             | Novalue -> false
             | Unknown -> false
             | I i0 -> Integers.Int.eq_dec x0 i0
             | F f -> false
             | S (i0, i1) -> false)
      | F x0 ->
          (match y with
             | Novalue -> false
             | Unknown -> false
             | I i -> false
             | F f0 -> Floats.Float.eq_dec x0 f0
             | S (i, i0) -> false)
      | S (x0, x1) ->
          (match y with
             | Novalue -> false
             | Unknown -> false
             | I i1 -> false
             | F f -> false
             | S (i1, i2) ->
                 (match ident_eq x0 i1 with
                    | true -> Integers.Int.eq_dec x1 i2
                    | false -> false))
  
  (** val beq : t -> t -> bool **)
  
  let beq x y =
    match eq_dec x y with
      | true -> true
      | false -> false
  
  (** val bot : approx **)
  
  let bot =
    Novalue
  
  (** val top : approx **)
  
  let top =
    Unknown
  
  (** val lub : t -> t -> t **)
  
  let lub x y =
    match eq_dec x y with
      | true -> x
      | false ->
          (match x with
             | Novalue -> y
             | Unknown ->
                 (match y with
                    | Novalue -> x
                    | Unknown -> Unknown
                    | I i -> Unknown
                    | F f -> Unknown
                    | S (i, i0) -> Unknown)
             | I i ->
                 (match y with
                    | Novalue -> x
                    | Unknown -> Unknown
                    | I i0 -> Unknown
                    | F f -> Unknown
                    | S (i0, i1) -> Unknown)
             | F f ->
                 (match y with
                    | Novalue -> x
                    | Unknown -> Unknown
                    | I i -> Unknown
                    | F f0 -> Unknown
                    | S (i, i0) -> Unknown)
             | S (i, i0) ->
                 (match y with
                    | Novalue -> x
                    | Unknown -> Unknown
                    | I i1 -> Unknown
                    | F f -> Unknown
                    | S (i1, i2) -> Unknown))
 end

module D = Lattice.LPMap(Approx)

type eval_static_condition_cases =
  | Coq_eval_static_condition_case1 of comparison * int * int
  | Coq_eval_static_condition_case2 of comparison * int * int
  | Coq_eval_static_condition_case3 of comparison * int * int
  | Coq_eval_static_condition_case4 of comparison * int * int
  | Coq_eval_static_condition_case5 of comparison * float * float
  | Coq_eval_static_condition_case6 of comparison * float * float
  | Coq_eval_static_condition_case7 of int * int
  | Coq_eval_static_condition_case8 of int * int
  | Coq_eval_static_condition_default of condition * approx list

(** val eval_static_condition_cases_rect : (comparison -> int -> int -> 'a1)
                                           -> (comparison -> int -> int ->
                                           'a1) -> (comparison -> int -> int
                                           -> 'a1) -> (comparison -> int ->
                                           int -> 'a1) -> (comparison ->
                                           float -> float -> 'a1) ->
                                           (comparison -> float -> float ->
                                           'a1) -> (int -> int -> 'a1) ->
                                           (int -> int -> 'a1) -> (condition
                                           -> approx list -> 'a1) ->
                                           condition -> approx list ->
                                           eval_static_condition_cases -> 'a1 **)

let eval_static_condition_cases_rect f f0 f1 f2 f3 f4 f5 f6 f7 cond vl = function
  | Coq_eval_static_condition_case1 (x, x0, x1) -> f x x0 x1
  | Coq_eval_static_condition_case2 (x, x0, x1) -> f0 x x0 x1
  | Coq_eval_static_condition_case3 (x, x0, x1) -> f1 x x0 x1
  | Coq_eval_static_condition_case4 (x, x0, x1) -> f2 x x0 x1
  | Coq_eval_static_condition_case5 (x, x0, x1) -> f3 x x0 x1
  | Coq_eval_static_condition_case6 (x, x0, x1) -> f4 x x0 x1
  | Coq_eval_static_condition_case7 (x, x0) -> f5 x x0
  | Coq_eval_static_condition_case8 (x, x0) -> f6 x x0
  | Coq_eval_static_condition_default (x, x0) -> f7 x x0

(** val eval_static_condition_cases_rec : (comparison -> int -> int -> 'a1)
                                          -> (comparison -> int -> int ->
                                          'a1) -> (comparison -> int -> int
                                          -> 'a1) -> (comparison -> int ->
                                          int -> 'a1) -> (comparison -> float
                                          -> float -> 'a1) -> (comparison ->
                                          float -> float -> 'a1) -> (int ->
                                          int -> 'a1) -> (int -> int -> 'a1)
                                          -> (condition -> approx list ->
                                          'a1) -> condition -> approx list ->
                                          eval_static_condition_cases -> 'a1 **)

let eval_static_condition_cases_rec f f0 f1 f2 f3 f4 f5 f6 f7 cond vl = function
  | Coq_eval_static_condition_case1 (x, x0, x1) -> f x x0 x1
  | Coq_eval_static_condition_case2 (x, x0, x1) -> f0 x x0 x1
  | Coq_eval_static_condition_case3 (x, x0, x1) -> f1 x x0 x1
  | Coq_eval_static_condition_case4 (x, x0, x1) -> f2 x x0 x1
  | Coq_eval_static_condition_case5 (x, x0, x1) -> f3 x x0 x1
  | Coq_eval_static_condition_case6 (x, x0, x1) -> f4 x x0 x1
  | Coq_eval_static_condition_case7 (x, x0) -> f5 x x0
  | Coq_eval_static_condition_case8 (x, x0) -> f6 x x0
  | Coq_eval_static_condition_default (x, x0) -> f7 x x0

(** val eval_static_condition_match : condition -> approx list ->
                                      eval_static_condition_cases **)

let eval_static_condition_match cond vl =
  match cond with
    | Ccomp c ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Ccomp c),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Ccomp c),
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Ccomp c),
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_default
                             ((Ccomp c), (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_condition_default ((Ccomp
                                    c), (Coq_cons ((I n1), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_condition_default ((Ccomp
                                    c), (Coq_cons ((I n1), (Coq_cons
                                    (Unknown, l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_condition_case1
                                           (c, n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_condition_default
                                           ((Ccomp c), (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_condition_default
                                    ((Ccomp c), (Coq_cons ((I n1), (Coq_cons
                                    ((F f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_condition_default ((Ccomp
                                    c), (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_condition_default ((Ccomp c),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_condition_default ((Ccomp
                      c), (Coq_cons ((S (i, i0)), l)))))
    | Ccompu c ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Ccompu c),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Ccompu c),
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Ccompu c),
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_default
                             ((Ccompu c), (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_condition_default
                                    ((Ccompu c), (Coq_cons ((I n1), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_condition_default
                                    ((Ccompu c), (Coq_cons ((I n1), (Coq_cons
                                    (Unknown, l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_condition_case2
                                           (c, n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_condition_default
                                           ((Ccompu c), (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_condition_default
                                    ((Ccompu c), (Coq_cons ((I n1), (Coq_cons
                                    ((F f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_condition_default
                                    ((Ccompu c), (Coq_cons ((I n1), (Coq_cons
                                    ((S (i, i0)), l0)))))))
                  | F f -> Coq_eval_static_condition_default ((Ccompu c),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_condition_default ((Ccompu
                      c), (Coq_cons ((S (i, i0)), l)))))
    | Ccompimm (c, n) ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Ccompimm (c, n)),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Ccompimm
                      (c, n)), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Ccompimm
                      (c, n)), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_case3 (c, n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_condition_default ((Ccompimm (c,
                             n)), (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_condition_default ((Ccompimm (c,
                      n)), (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_condition_default ((Ccompimm
                      (c, n)), (Coq_cons ((S (i, i0)), l)))))
    | Ccompuimm (c, n) ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Ccompuimm (c,
               n)), Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Ccompuimm
                      (c, n)), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Ccompuimm
                      (c, n)), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_case4 (c, n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_condition_default ((Ccompuimm
                             (c, n)), (Coq_cons ((I n1), (Coq_cons (a0,
                             l0))))))
                  | F f -> Coq_eval_static_condition_default ((Ccompuimm (c,
                      n)), (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_condition_default
                      ((Ccompuimm (c, n)), (Coq_cons ((S (i, i0)), l)))))
    | Ccompf c ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Ccompf c),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Ccompf c),
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Ccompf c),
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_condition_default ((Ccompf c),
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_default
                             ((Ccompf c), (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_condition_default
                                    ((Ccompf c), (Coq_cons ((F n1), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_condition_default
                                    ((Ccompf c), (Coq_cons ((F n1), (Coq_cons
                                    (Unknown, l0)))))
                                | I i -> Coq_eval_static_condition_default
                                    ((Ccompf c), (Coq_cons ((F n1), (Coq_cons
                                    ((I i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_condition_case5
                                           (c, n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_condition_default
                                           ((Ccompf c), (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), (Coq_cons (a1,
                                           l1))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_condition_default
                                    ((Ccompf c), (Coq_cons ((F n1), (Coq_cons
                                    ((S (i, i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_condition_default ((Ccompf
                      c), (Coq_cons ((S (i, i0)), l)))))
    | Cnotcompf c ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Cnotcompf c),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Cnotcompf
                      c), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Cnotcompf
                      c), (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_condition_default ((Cnotcompf c),
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_default
                             ((Cnotcompf c), (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_condition_default
                                    ((Cnotcompf c), (Coq_cons ((F n1),
                                    (Coq_cons (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_condition_default
                                    ((Cnotcompf c), (Coq_cons ((F n1),
                                    (Coq_cons (Unknown, l0)))))
                                | I i -> Coq_eval_static_condition_default
                                    ((Cnotcompf c), (Coq_cons ((F n1),
                                    (Coq_cons ((I i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_condition_case6
                                           (c, n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_condition_default
                                           ((Cnotcompf c), (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), (Coq_cons (a1,
                                           l1))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_condition_default
                                    ((Cnotcompf c), (Coq_cons ((F n1),
                                    (Coq_cons ((S (i, i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_condition_default
                      ((Cnotcompf c), (Coq_cons ((S (i, i0)), l)))))
    | Cmaskzero n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Cmaskzero n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default ((Cmaskzero
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default ((Cmaskzero
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_case7 (n, n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_condition_default ((Cmaskzero
                             n), (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_condition_default ((Cmaskzero n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_condition_default
                      ((Cmaskzero n), (Coq_cons ((S (i, i0)), l)))))
    | Cmasknotzero n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_condition_default ((Cmasknotzero n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_condition_default
                      ((Cmasknotzero n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_condition_default
                      ((Cmasknotzero n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_condition_case8 (n, n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_condition_default ((Cmasknotzero
                             n), (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_condition_default ((Cmasknotzero
                      n), (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_condition_default
                      ((Cmasknotzero n), (Coq_cons ((S (i, i0)), l)))))

(** val eval_static_condition : condition -> approx list -> bool option **)

let eval_static_condition cond vl =
  match eval_static_condition_match cond vl with
    | Coq_eval_static_condition_case1 (c, n1, n2) -> Some
        (Integers.Int.cmp c n1 n2)
    | Coq_eval_static_condition_case2 (c, n1, n2) -> Some
        (Integers.Int.cmpu c n1 n2)
    | Coq_eval_static_condition_case3 (c, n, n1) -> Some
        (Integers.Int.cmp c n1 n)
    | Coq_eval_static_condition_case4 (c, n, n1) -> Some
        (Integers.Int.cmpu c n1 n)
    | Coq_eval_static_condition_case5 (c, n1, n2) -> Some
        (Floats.Float.cmp c n1 n2)
    | Coq_eval_static_condition_case6 (c, n1, n2) -> Some
        (negb (Floats.Float.cmp c n1 n2))
    | Coq_eval_static_condition_case7 (n, n1) -> Some
        (Integers.Int.eq (Integers.Int.coq_and n1 n) Integers.Int.zero)
    | Coq_eval_static_condition_case8 (n, n1) -> Some
        (negb
          (Integers.Int.eq (Integers.Int.coq_and n1 n) Integers.Int.zero))
    | Coq_eval_static_condition_default (cond0, vl0) -> None

type eval_static_operation_cases =
  | Coq_eval_static_operation_case1 of approx
  | Coq_eval_static_operation_case2 of int
  | Coq_eval_static_operation_case3 of float
  | Coq_eval_static_operation_case4 of ident * int
  | Coq_eval_static_operation_case6 of int
  | Coq_eval_static_operation_case7 of int
  | Coq_eval_static_operation_case8 of int * int
  | Coq_eval_static_operation_case9 of ident * int * int
  | Coq_eval_static_operation_case11 of int * int
  | Coq_eval_static_operation_case12 of int * ident * int
  | Coq_eval_static_operation_case13 of int * int
  | Coq_eval_static_operation_case14 of ident * int * int
  | Coq_eval_static_operation_case15 of int * int
  | Coq_eval_static_operation_case16 of int * int
  | Coq_eval_static_operation_case17 of int * int
  | Coq_eval_static_operation_case18 of int * int
  | Coq_eval_static_operation_case19 of int * int
  | Coq_eval_static_operation_case20 of int * int
  | Coq_eval_static_operation_case21 of int * int
  | Coq_eval_static_operation_case22 of int * int
  | Coq_eval_static_operation_case23 of int * int
  | Coq_eval_static_operation_case24 of int * int
  | Coq_eval_static_operation_case25 of int * int
  | Coq_eval_static_operation_case26 of int * int
  | Coq_eval_static_operation_case27 of int * int
  | Coq_eval_static_operation_case28 of int * int
  | Coq_eval_static_operation_case29 of int * int
  | Coq_eval_static_operation_case30 of int * int
  | Coq_eval_static_operation_case31 of int * int
  | Coq_eval_static_operation_case32 of int * int
  | Coq_eval_static_operation_case33 of int * int
  | Coq_eval_static_operation_case34 of int * int * int
  | Coq_eval_static_operation_case35 of float
  | Coq_eval_static_operation_case36 of float
  | Coq_eval_static_operation_case37 of float * float
  | Coq_eval_static_operation_case38 of float * float
  | Coq_eval_static_operation_case39 of float * float
  | Coq_eval_static_operation_case40 of float * float
  | Coq_eval_static_operation_case41 of float * float * float
  | Coq_eval_static_operation_case42 of float * float * float
  | Coq_eval_static_operation_case43 of float
  | Coq_eval_static_operation_case44 of float
  | Coq_eval_static_operation_case45 of int
  | Coq_eval_static_operation_case46 of int
  | Coq_eval_static_operation_case47 of condition * approx list
  | Coq_eval_static_operation_case48 of int
  | Coq_eval_static_operation_case49 of int
  | Coq_eval_static_operation_default of operation * approx list

(** val eval_static_operation_cases_rect : (approx -> 'a1) -> (int -> 'a1) ->
                                           (float -> 'a1) -> (ident -> int ->
                                           'a1) -> (int -> 'a1) -> (int ->
                                           'a1) -> (int -> int -> 'a1) ->
                                           (ident -> int -> int -> 'a1) ->
                                           (int -> int -> 'a1) -> (int ->
                                           ident -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (ident -> int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> 'a1) -> (int ->
                                           int -> 'a1) -> (int -> int -> 'a1)
                                           -> (int -> int -> int -> 'a1) ->
                                           (float -> 'a1) -> (float -> 'a1)
                                           -> (float -> float -> 'a1) ->
                                           (float -> float -> 'a1) -> (float
                                           -> float -> 'a1) -> (float ->
                                           float -> 'a1) -> (float -> float
                                           -> float -> 'a1) -> (float ->
                                           float -> float -> 'a1) -> (float
                                           -> 'a1) -> (float -> 'a1) -> (int
                                           -> 'a1) -> (int -> 'a1) ->
                                           (condition -> approx list -> 'a1)
                                           -> (int -> 'a1) -> (int -> 'a1) ->
                                           (operation -> approx list -> 'a1)
                                           -> operation -> approx list ->
                                           eval_static_operation_cases -> 'a1 **)

let eval_static_operation_cases_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 op vl = function
  | Coq_eval_static_operation_case1 x -> f x
  | Coq_eval_static_operation_case2 x -> f0 x
  | Coq_eval_static_operation_case3 x -> f1 x
  | Coq_eval_static_operation_case4 (x, x0) -> f2 x x0
  | Coq_eval_static_operation_case6 x -> f3 x
  | Coq_eval_static_operation_case7 x -> f4 x
  | Coq_eval_static_operation_case8 (x, x0) -> f5 x x0
  | Coq_eval_static_operation_case9 (x, x0, x1) -> f6 x x0 x1
  | Coq_eval_static_operation_case11 (x, x0) -> f7 x x0
  | Coq_eval_static_operation_case12 (x, x0, x1) -> f8 x x0 x1
  | Coq_eval_static_operation_case13 (x, x0) -> f9 x x0
  | Coq_eval_static_operation_case14 (x, x0, x1) -> f10 x x0 x1
  | Coq_eval_static_operation_case15 (x, x0) -> f11 x x0
  | Coq_eval_static_operation_case16 (x, x0) -> f12 x x0
  | Coq_eval_static_operation_case17 (x, x0) -> f13 x x0
  | Coq_eval_static_operation_case18 (x, x0) -> f14 x x0
  | Coq_eval_static_operation_case19 (x, x0) -> f15 x x0
  | Coq_eval_static_operation_case20 (x, x0) -> f16 x x0
  | Coq_eval_static_operation_case21 (x, x0) -> f17 x x0
  | Coq_eval_static_operation_case22 (x, x0) -> f18 x x0
  | Coq_eval_static_operation_case23 (x, x0) -> f19 x x0
  | Coq_eval_static_operation_case24 (x, x0) -> f20 x x0
  | Coq_eval_static_operation_case25 (x, x0) -> f21 x x0
  | Coq_eval_static_operation_case26 (x, x0) -> f22 x x0
  | Coq_eval_static_operation_case27 (x, x0) -> f23 x x0
  | Coq_eval_static_operation_case28 (x, x0) -> f24 x x0
  | Coq_eval_static_operation_case29 (x, x0) -> f25 x x0
  | Coq_eval_static_operation_case30 (x, x0) -> f26 x x0
  | Coq_eval_static_operation_case31 (x, x0) -> f27 x x0
  | Coq_eval_static_operation_case32 (x, x0) -> f28 x x0
  | Coq_eval_static_operation_case33 (x, x0) -> f29 x x0
  | Coq_eval_static_operation_case34 (x, x0, x1) -> f30 x x0 x1
  | Coq_eval_static_operation_case35 x -> f31 x
  | Coq_eval_static_operation_case36 x -> f32 x
  | Coq_eval_static_operation_case37 (x, x0) -> f33 x x0
  | Coq_eval_static_operation_case38 (x, x0) -> f34 x x0
  | Coq_eval_static_operation_case39 (x, x0) -> f35 x x0
  | Coq_eval_static_operation_case40 (x, x0) -> f36 x x0
  | Coq_eval_static_operation_case41 (x, x0, x1) -> f37 x x0 x1
  | Coq_eval_static_operation_case42 (x, x0, x1) -> f38 x x0 x1
  | Coq_eval_static_operation_case43 x -> f39 x
  | Coq_eval_static_operation_case44 x -> f40 x
  | Coq_eval_static_operation_case45 x -> f41 x
  | Coq_eval_static_operation_case46 x -> f42 x
  | Coq_eval_static_operation_case47 (x, x0) -> f43 x x0
  | Coq_eval_static_operation_case48 x -> f44 x
  | Coq_eval_static_operation_case49 x -> f45 x
  | Coq_eval_static_operation_default (x, x0) -> f46 x x0

(** val eval_static_operation_cases_rec : (approx -> 'a1) -> (int -> 'a1) ->
                                          (float -> 'a1) -> (ident -> int ->
                                          'a1) -> (int -> 'a1) -> (int ->
                                          'a1) -> (int -> int -> 'a1) ->
                                          (ident -> int -> int -> 'a1) ->
                                          (int -> int -> 'a1) -> (int ->
                                          ident -> int -> 'a1) -> (int -> int
                                          -> 'a1) -> (ident -> int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> 'a1) -> (int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> 'a1) -> (int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> 'a1) -> (int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> 'a1) -> (int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> 'a1) -> (int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> 'a1) -> (int -> int ->
                                          'a1) -> (int -> int -> 'a1) -> (int
                                          -> int -> int -> 'a1) -> (float ->
                                          'a1) -> (float -> 'a1) -> (float ->
                                          float -> 'a1) -> (float -> float ->
                                          'a1) -> (float -> float -> 'a1) ->
                                          (float -> float -> 'a1) -> (float
                                          -> float -> float -> 'a1) -> (float
                                          -> float -> float -> 'a1) -> (float
                                          -> 'a1) -> (float -> 'a1) -> (int
                                          -> 'a1) -> (int -> 'a1) ->
                                          (condition -> approx list -> 'a1)
                                          -> (int -> 'a1) -> (int -> 'a1) ->
                                          (operation -> approx list -> 'a1)
                                          -> operation -> approx list ->
                                          eval_static_operation_cases -> 'a1 **)

let eval_static_operation_cases_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 op vl = function
  | Coq_eval_static_operation_case1 x -> f x
  | Coq_eval_static_operation_case2 x -> f0 x
  | Coq_eval_static_operation_case3 x -> f1 x
  | Coq_eval_static_operation_case4 (x, x0) -> f2 x x0
  | Coq_eval_static_operation_case6 x -> f3 x
  | Coq_eval_static_operation_case7 x -> f4 x
  | Coq_eval_static_operation_case8 (x, x0) -> f5 x x0
  | Coq_eval_static_operation_case9 (x, x0, x1) -> f6 x x0 x1
  | Coq_eval_static_operation_case11 (x, x0) -> f7 x x0
  | Coq_eval_static_operation_case12 (x, x0, x1) -> f8 x x0 x1
  | Coq_eval_static_operation_case13 (x, x0) -> f9 x x0
  | Coq_eval_static_operation_case14 (x, x0, x1) -> f10 x x0 x1
  | Coq_eval_static_operation_case15 (x, x0) -> f11 x x0
  | Coq_eval_static_operation_case16 (x, x0) -> f12 x x0
  | Coq_eval_static_operation_case17 (x, x0) -> f13 x x0
  | Coq_eval_static_operation_case18 (x, x0) -> f14 x x0
  | Coq_eval_static_operation_case19 (x, x0) -> f15 x x0
  | Coq_eval_static_operation_case20 (x, x0) -> f16 x x0
  | Coq_eval_static_operation_case21 (x, x0) -> f17 x x0
  | Coq_eval_static_operation_case22 (x, x0) -> f18 x x0
  | Coq_eval_static_operation_case23 (x, x0) -> f19 x x0
  | Coq_eval_static_operation_case24 (x, x0) -> f20 x x0
  | Coq_eval_static_operation_case25 (x, x0) -> f21 x x0
  | Coq_eval_static_operation_case26 (x, x0) -> f22 x x0
  | Coq_eval_static_operation_case27 (x, x0) -> f23 x x0
  | Coq_eval_static_operation_case28 (x, x0) -> f24 x x0
  | Coq_eval_static_operation_case29 (x, x0) -> f25 x x0
  | Coq_eval_static_operation_case30 (x, x0) -> f26 x x0
  | Coq_eval_static_operation_case31 (x, x0) -> f27 x x0
  | Coq_eval_static_operation_case32 (x, x0) -> f28 x x0
  | Coq_eval_static_operation_case33 (x, x0) -> f29 x x0
  | Coq_eval_static_operation_case34 (x, x0, x1) -> f30 x x0 x1
  | Coq_eval_static_operation_case35 x -> f31 x
  | Coq_eval_static_operation_case36 x -> f32 x
  | Coq_eval_static_operation_case37 (x, x0) -> f33 x x0
  | Coq_eval_static_operation_case38 (x, x0) -> f34 x x0
  | Coq_eval_static_operation_case39 (x, x0) -> f35 x x0
  | Coq_eval_static_operation_case40 (x, x0) -> f36 x x0
  | Coq_eval_static_operation_case41 (x, x0, x1) -> f37 x x0 x1
  | Coq_eval_static_operation_case42 (x, x0, x1) -> f38 x x0 x1
  | Coq_eval_static_operation_case43 x -> f39 x
  | Coq_eval_static_operation_case44 x -> f40 x
  | Coq_eval_static_operation_case45 x -> f41 x
  | Coq_eval_static_operation_case46 x -> f42 x
  | Coq_eval_static_operation_case47 (x, x0) -> f43 x x0
  | Coq_eval_static_operation_case48 x -> f44 x
  | Coq_eval_static_operation_case49 x -> f45 x
  | Coq_eval_static_operation_default (x, x0) -> f46 x x0

(** val eval_static_operation_match : operation -> approx list ->
                                      eval_static_operation_cases **)

let eval_static_operation_match op vl =
  match op with
    | Omove ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Omove, Coq_nil)
           | Coq_cons (v1, l) ->
               (match l with
                  | Coq_nil -> Coq_eval_static_operation_case1 v1
                  | Coq_cons (a, l0) -> Coq_eval_static_operation_default
                      (Omove, (Coq_cons (v1, (Coq_cons (a, l0)))))))
    | Ointconst n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_case2 n
           | Coq_cons (a, l) -> Coq_eval_static_operation_default ((Ointconst
               n), (Coq_cons (a, l))))
    | Ofloatconst n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_case3 n
           | Coq_cons (a, l) -> Coq_eval_static_operation_default
               ((Ofloatconst n), (Coq_cons (a, l))))
    | Oaddrsymbol (s, n) ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_case4 (s, n)
           | Coq_cons (a, l) -> Coq_eval_static_operation_default
               ((Oaddrsymbol (s, n)), (Coq_cons (a, l))))
    | Oaddrstack i -> Coq_eval_static_operation_default ((Oaddrstack i), vl)
    | Ocast8signed ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ocast8signed,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ocast8signed, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ocast8signed, (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case6 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default (Ocast8signed,
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default (Ocast8signed,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ocast8signed, (Coq_cons ((S (i, i0)), l)))))
    | Ocast8unsigned ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ocast8unsigned,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ocast8unsigned, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ocast8unsigned, (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case48 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default
                             (Ocast8unsigned, (Coq_cons ((I n1), (Coq_cons
                             (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default (Ocast8unsigned,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ocast8unsigned, (Coq_cons ((S (i, i0)), l)))))
    | Ocast16signed ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ocast16signed,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ocast16signed, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ocast16signed, (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case7 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default
                             (Ocast16signed, (Coq_cons ((I n1), (Coq_cons
                             (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default (Ocast16signed,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ocast16signed, (Coq_cons ((S (i, i0)), l)))))
    | Ocast16unsigned ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ocast16unsigned,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ocast16unsigned, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ocast16unsigned, (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case49 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default
                             (Ocast16unsigned, (Coq_cons ((I n1), (Coq_cons
                             (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default
                      (Ocast16unsigned, (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ocast16unsigned, (Coq_cons ((S (i, i0)), l)))))
    | Oadd ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oadd, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oadd,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oadd,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oadd, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oadd,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oadd,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case8
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oadd, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oadd, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oadd,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oadd, (Coq_cons
                      ((F f), l)))
                  | S (s1, n1) ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oadd, (Coq_cons ((S (s1, n1)), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oadd,
                                    (Coq_cons ((S (s1, n1)), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oadd,
                                    (Coq_cons ((S (s1, n1)), (Coq_cons
                                    (Unknown, l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case9
                                           (s1, n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oadd, (Coq_cons ((S (s1, n1)),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oadd, (Coq_cons ((S (s1, n1)), (Coq_cons
                                    ((F f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oadd,
                                    (Coq_cons ((S (s1, n1)), (Coq_cons ((S
                                    (i, i0)), l0)))))))))
    | Oaddimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Oaddimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Oaddimm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Oaddimm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case11 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oaddimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Oaddimm n),
                      (Coq_cons ((F f), l)))
                  | S (s1, n1) ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case12 (n,
                             s1, n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oaddimm n),
                             (Coq_cons ((S (s1, n1)), (Coq_cons (a0, l0))))))))
    | Osub ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Osub, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Osub,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Osub,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Osub, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Osub,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Osub,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case13
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Osub, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Osub, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Osub,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Osub, (Coq_cons
                      ((F f), l)))
                  | S (s1, n1) ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Osub, (Coq_cons ((S (s1, n1)), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Osub,
                                    (Coq_cons ((S (s1, n1)), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Osub,
                                    (Coq_cons ((S (s1, n1)), (Coq_cons
                                    (Unknown, l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case14
                                           (s1, n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Osub, (Coq_cons ((S (s1, n1)),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Osub, (Coq_cons ((S (s1, n1)), (Coq_cons
                                    ((F f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Osub,
                                    (Coq_cons ((S (s1, n1)), (Coq_cons ((S
                                    (i, i0)), l0)))))))))
    | Osubimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Osubimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Osubimm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Osubimm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case15 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Osubimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Osubimm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Osubimm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Omul ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Omul, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Omul,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Omul,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Omul, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Omul,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Omul,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case16
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Omul, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Omul, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Omul,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Omul, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Omul,
                      (Coq_cons ((S (i, i0)), l)))))
    | Omulimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Omulimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Omulimm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Omulimm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case17 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Omulimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Omulimm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Omulimm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Odiv ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Odiv, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Odiv,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Odiv,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Odiv, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Odiv,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Odiv,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case18
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Odiv, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Odiv, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Odiv,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Odiv, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Odiv,
                      (Coq_cons ((S (i, i0)), l)))))
    | Odivu ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Odivu, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Odivu,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Odivu,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Odivu, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Odivu,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Odivu,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case19
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Odivu, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Odivu, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Odivu,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Odivu,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Odivu,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oand ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oand, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oand,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oand,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oand, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oand,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oand,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case20
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oand, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oand, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oand,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oand, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oand,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oandimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Oandimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Oandimm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Oandimm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case21 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oandimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Oandimm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Oandimm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Oor ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oor, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oor,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oor,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default (Oor,
                             (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oor,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oor,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case22
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oor, (Coq_cons ((I n1), (Coq_cons
                                           ((I n2), (Coq_cons (a1, l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oor, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oor,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oor, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oor,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oorimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Oorimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Oorimm n),
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Oorimm n),
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case23 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oorimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Oorimm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Oorimm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Oxor ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oxor, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oxor,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oxor,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oxor, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oxor,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oxor,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case24
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oxor, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oxor, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oxor,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oxor, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oxor,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oxorimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Oxorimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Oxorimm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Oxorimm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case25 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oxorimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Oxorimm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Oxorimm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Onand ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Onand, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Onand,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Onand,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Onand, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Onand,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Onand,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case26
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Onand, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Onand, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Onand,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Onand,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Onand,
                      (Coq_cons ((S (i, i0)), l)))))
    | Onor ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Onor, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Onor,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Onor,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Onor, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Onor,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Onor,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case27
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Onor, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Onor, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Onor,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Onor, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Onor,
                      (Coq_cons ((S (i, i0)), l)))))
    | Onxor ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Onxor, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Onxor,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Onxor,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Onxor, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Onxor,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Onxor,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case28
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Onxor, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Onxor, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Onxor,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Onxor,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Onxor,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oshl ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oshl, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oshl,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oshl,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oshl, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oshl,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oshl,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case29
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oshl, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oshl, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oshl,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oshl, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oshl,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oshr ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oshr, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oshr,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oshr,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oshr, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oshr,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oshr,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case30
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oshr, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oshr, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oshr,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oshr, (Coq_cons
                      ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oshr,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oshrimm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Oshrimm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Oshrimm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Oshrimm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case31 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oshrimm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Oshrimm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Oshrimm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Oshrximm n ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Oshrximm n),
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Oshrximm
                      n), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Oshrximm
                      n), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case32 (n,
                             n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Oshrximm n),
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Oshrximm n),
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Oshrximm
                      n), (Coq_cons ((S (i, i0)), l)))))
    | Oshru ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oshru, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oshru,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oshru,
                      (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oshru, (Coq_cons ((I n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oshru,
                                    (Coq_cons ((I n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oshru,
                                    (Coq_cons ((I n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case33
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oshru, (Coq_cons ((I n1),
                                           (Coq_cons ((I n2), (Coq_cons (a1,
                                           l1))))))))
                                | F f -> Coq_eval_static_operation_default
                                    (Oshru, (Coq_cons ((I n1), (Coq_cons ((F
                                    f), l0)))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oshru,
                                    (Coq_cons ((I n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | F f -> Coq_eval_static_operation_default (Oshru,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oshru,
                      (Coq_cons ((S (i, i0)), l)))))
    | Orolm (amount, mask) ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default ((Orolm (amount,
               mask)), Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default ((Orolm
                      (amount, mask)), (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default ((Orolm
                      (amount, mask)), (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case34
                             (amount, mask, n1)
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default ((Orolm
                             (amount, mask)), (Coq_cons ((I n1), (Coq_cons
                             (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default ((Orolm (amount,
                      mask)), (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default ((Orolm
                      (amount, mask)), (Coq_cons ((S (i, i0)), l)))))
    | Onegf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Onegf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Onegf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Onegf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Onegf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case35 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default (Onegf,
                             (Coq_cons ((F n1), (Coq_cons (a0, l0))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Onegf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oabsf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oabsf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oabsf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oabsf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Oabsf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case36 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default (Oabsf,
                             (Coq_cons ((F n1), (Coq_cons (a0, l0))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oabsf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Oaddf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Oaddf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Oaddf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Oaddf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Oaddf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Oaddf, (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Oaddf,
                                    (Coq_cons ((F n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Oaddf,
                                    (Coq_cons ((F n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I i -> Coq_eval_static_operation_default
                                    (Oaddf, (Coq_cons ((F n1), (Coq_cons ((I
                                    i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case37
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Oaddf, (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), (Coq_cons (a1,
                                           l1))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Oaddf,
                                    (Coq_cons ((F n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Oaddf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Osubf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Osubf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Osubf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Osubf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Osubf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Osubf, (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Osubf,
                                    (Coq_cons ((F n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Osubf,
                                    (Coq_cons ((F n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I i -> Coq_eval_static_operation_default
                                    (Osubf, (Coq_cons ((F n1), (Coq_cons ((I
                                    i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case38
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Osubf, (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), (Coq_cons (a1,
                                           l1))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Osubf,
                                    (Coq_cons ((F n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Osubf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Omulf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Omulf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Omulf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Omulf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Omulf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Omulf, (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Omulf,
                                    (Coq_cons ((F n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Omulf,
                                    (Coq_cons ((F n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I i -> Coq_eval_static_operation_default
                                    (Omulf, (Coq_cons ((F n1), (Coq_cons ((I
                                    i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case39
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Omulf, (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), (Coq_cons (a1,
                                           l1))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Omulf,
                                    (Coq_cons ((F n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Omulf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Odivf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Odivf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Odivf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Odivf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Odivf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Odivf, (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default (Odivf,
                                    (Coq_cons ((F n1), (Coq_cons (Novalue,
                                    l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default (Odivf,
                                    (Coq_cons ((F n1), (Coq_cons (Unknown,
                                    l0)))))
                                | I i -> Coq_eval_static_operation_default
                                    (Odivf, (Coq_cons ((F n1), (Coq_cons ((I
                                    i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_case40
                                           (n1, n2)
                                       | Coq_cons (
                                           a1, l1) ->
                                           Coq_eval_static_operation_default
                                           (Odivf, (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), (Coq_cons (a1,
                                           l1))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default (Odivf,
                                    (Coq_cons ((F n1), (Coq_cons ((S (i,
                                    i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Odivf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Omuladdf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Omuladdf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Omuladdf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Omuladdf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Omuladdf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Omuladdf, (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default
                                    (Omuladdf, (Coq_cons ((F n1), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default
                                    (Omuladdf, (Coq_cons ((F n1), (Coq_cons
                                    (Unknown, l0)))))
                                | I i -> Coq_eval_static_operation_default
                                    (Omuladdf, (Coq_cons ((F n1), (Coq_cons
                                    ((I i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_default
                                           (Omuladdf, (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), Coq_nil)))))
                                       | Coq_cons (
                                           a1, l1) ->
                                           (match a1 with
                                              | Novalue ->
                                                  Coq_eval_static_operation_default
                                                  (Omuladdf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons (Novalue,
                                                  l1)))))))
                                              | Unknown ->
                                                  Coq_eval_static_operation_default
                                                  (Omuladdf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons (Unknown,
                                                  l1)))))))
                                              | I i ->
                                                  Coq_eval_static_operation_default
                                                  (Omuladdf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons ((I i), l1)))))))
                                              | F n3 ->
                                                  (
                                                  match l1 with
                                                    | 
                                                  Coq_nil ->
                                                  Coq_eval_static_operation_case41
                                                  (n1, n2, n3)
                                                    | 
                                                  Coq_cons (
                                                  a2, l2) ->
                                                  Coq_eval_static_operation_default
                                                  (Omuladdf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons ((F n3),
                                                  (Coq_cons (a2, l2))))))))))
                                              | S (
                                                  i, i0) ->
                                                  Coq_eval_static_operation_default
                                                  (Omuladdf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons ((S (i, i0)),
                                                  l1)))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default
                                    (Omuladdf, (Coq_cons ((F n1), (Coq_cons
                                    ((S (i, i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Omuladdf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Omulsubf ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Omulsubf, Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default (Omulsubf,
                      (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default (Omulsubf,
                      (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Omulsubf,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_default
                             (Omulsubf, (Coq_cons ((F n1), Coq_nil)))
                         | Coq_cons (a0, l0) ->
                             (match a0 with
                                | Novalue ->
                                    Coq_eval_static_operation_default
                                    (Omulsubf, (Coq_cons ((F n1), (Coq_cons
                                    (Novalue, l0)))))
                                | Unknown ->
                                    Coq_eval_static_operation_default
                                    (Omulsubf, (Coq_cons ((F n1), (Coq_cons
                                    (Unknown, l0)))))
                                | I i -> Coq_eval_static_operation_default
                                    (Omulsubf, (Coq_cons ((F n1), (Coq_cons
                                    ((I i), l0)))))
                                | F n2 ->
                                    (match l0 with
                                       | Coq_nil ->
                                           Coq_eval_static_operation_default
                                           (Omulsubf, (Coq_cons ((F n1),
                                           (Coq_cons ((F n2), Coq_nil)))))
                                       | Coq_cons (
                                           a1, l1) ->
                                           (match a1 with
                                              | Novalue ->
                                                  Coq_eval_static_operation_default
                                                  (Omulsubf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons (Novalue,
                                                  l1)))))))
                                              | Unknown ->
                                                  Coq_eval_static_operation_default
                                                  (Omulsubf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons (Unknown,
                                                  l1)))))))
                                              | I i ->
                                                  Coq_eval_static_operation_default
                                                  (Omulsubf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons ((I i), l1)))))))
                                              | F n3 ->
                                                  (
                                                  match l1 with
                                                    | 
                                                  Coq_nil ->
                                                  Coq_eval_static_operation_case42
                                                  (n1, n2, n3)
                                                    | 
                                                  Coq_cons (
                                                  a2, l2) ->
                                                  Coq_eval_static_operation_default
                                                  (Omulsubf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons ((F n3),
                                                  (Coq_cons (a2, l2))))))))))
                                              | S (
                                                  i, i0) ->
                                                  Coq_eval_static_operation_default
                                                  (Omulsubf, (Coq_cons ((F
                                                  n1), (Coq_cons ((F n2),
                                                  (Coq_cons ((S (i, i0)),
                                                  l1)))))))))
                                | S (i, i0) ->
                                    Coq_eval_static_operation_default
                                    (Omulsubf, (Coq_cons ((F n1), (Coq_cons
                                    ((S (i, i0)), l0)))))))
                  | S (i, i0) -> Coq_eval_static_operation_default (Omulsubf,
                      (Coq_cons ((S (i, i0)), l)))))
    | Osingleoffloat ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Osingleoffloat,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Osingleoffloat, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Osingleoffloat, (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Osingleoffloat,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case43 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default
                             (Osingleoffloat, (Coq_cons ((F n1), (Coq_cons
                             (a0, l0))))))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Osingleoffloat, (Coq_cons ((S (i, i0)), l)))))
    | Ointoffloat ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ointoffloat,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ointoffloat, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ointoffloat, (Coq_cons (Unknown, l)))
                  | I i -> Coq_eval_static_operation_default (Ointoffloat,
                      (Coq_cons ((I i), l)))
                  | F n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case44 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default (Ointoffloat,
                             (Coq_cons ((F n1), (Coq_cons (a0, l0))))))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ointoffloat, (Coq_cons ((S (i, i0)), l)))))
    | Ofloatofint ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ofloatofint,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ofloatofint, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ofloatofint, (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case45 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default (Ofloatofint,
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default (Ofloatofint,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ofloatofint, (Coq_cons ((S (i, i0)), l)))))
    | Ofloatofintu ->
        (match vl with
           | Coq_nil -> Coq_eval_static_operation_default (Ofloatofintu,
               Coq_nil)
           | Coq_cons (a, l) ->
               (match a with
                  | Novalue -> Coq_eval_static_operation_default
                      (Ofloatofintu, (Coq_cons (Novalue, l)))
                  | Unknown -> Coq_eval_static_operation_default
                      (Ofloatofintu, (Coq_cons (Unknown, l)))
                  | I n1 ->
                      (match l with
                         | Coq_nil -> Coq_eval_static_operation_case46 n1
                         | Coq_cons (a0, l0) ->
                             Coq_eval_static_operation_default (Ofloatofintu,
                             (Coq_cons ((I n1), (Coq_cons (a0, l0))))))
                  | F f -> Coq_eval_static_operation_default (Ofloatofintu,
                      (Coq_cons ((F f), l)))
                  | S (i, i0) -> Coq_eval_static_operation_default
                      (Ofloatofintu, (Coq_cons ((S (i, i0)), l)))))
    | Ocmp c -> Coq_eval_static_operation_case47 (c, vl)

(** val eval_static_operation : operation -> approx list -> approx **)

let eval_static_operation op vl =
  match eval_static_operation_match op vl with
    | Coq_eval_static_operation_case1 v1 -> v1
    | Coq_eval_static_operation_case2 n -> I n
    | Coq_eval_static_operation_case3 n -> F n
    | Coq_eval_static_operation_case4 (s, n) -> S (s, n)
    | Coq_eval_static_operation_case6 n1 -> I (Integers.Int.cast8signed n1)
    | Coq_eval_static_operation_case7 n1 -> I (Integers.Int.cast16signed n1)
    | Coq_eval_static_operation_case8 (n1, n2) -> I (Integers.Int.add n1 n2)
    | Coq_eval_static_operation_case9 (s1, n1, n2) -> S (s1,
        (Integers.Int.add n1 n2))
    | Coq_eval_static_operation_case11 (n, n1) -> I (Integers.Int.add n1 n)
    | Coq_eval_static_operation_case12 (n, s1, n1) -> S (s1,
        (Integers.Int.add n1 n))
    | Coq_eval_static_operation_case13 (n1, n2) -> I (Integers.Int.sub n1 n2)
    | Coq_eval_static_operation_case14 (s1, n1, n2) -> S (s1,
        (Integers.Int.sub n1 n2))
    | Coq_eval_static_operation_case15 (n, n1) -> I (Integers.Int.sub n n1)
    | Coq_eval_static_operation_case16 (n1, n2) -> I (Integers.Int.mul n1 n2)
    | Coq_eval_static_operation_case17 (n, n1) -> I (Integers.Int.mul n1 n)
    | Coq_eval_static_operation_case18 (n1, n2) ->
        (match Integers.Int.eq n2 Integers.Int.zero with
           | true -> Unknown
           | false -> I (Integers.Int.divs n1 n2))
    | Coq_eval_static_operation_case19 (n1, n2) ->
        (match Integers.Int.eq n2 Integers.Int.zero with
           | true -> Unknown
           | false -> I (Integers.Int.divu n1 n2))
    | Coq_eval_static_operation_case20 (n1, n2) -> I
        (Integers.Int.coq_and n1 n2)
    | Coq_eval_static_operation_case21 (n, n1) -> I
        (Integers.Int.coq_and n1 n)
    | Coq_eval_static_operation_case22 (n1, n2) -> I
        (Integers.Int.coq_or n1 n2)
    | Coq_eval_static_operation_case23 (n, n1) -> I
        (Integers.Int.coq_or n1 n)
    | Coq_eval_static_operation_case24 (n1, n2) -> I (Integers.Int.xor n1 n2)
    | Coq_eval_static_operation_case25 (n, n1) -> I (Integers.Int.xor n1 n)
    | Coq_eval_static_operation_case26 (n1, n2) -> I
        (Integers.Int.xor (Integers.Int.coq_and n1 n2) Integers.Int.mone)
    | Coq_eval_static_operation_case27 (n1, n2) -> I
        (Integers.Int.xor (Integers.Int.coq_or n1 n2) Integers.Int.mone)
    | Coq_eval_static_operation_case28 (n1, n2) -> I
        (Integers.Int.xor (Integers.Int.xor n1 n2) Integers.Int.mone)
    | Coq_eval_static_operation_case29 (n1, n2) ->
        (match Integers.Int.ltu n2
                 (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   (Coq_xO Coq_xH))))))) with
           | true -> I (Integers.Int.shl n1 n2)
           | false -> Unknown)
    | Coq_eval_static_operation_case30 (n1, n2) ->
        (match Integers.Int.ltu n2
                 (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   (Coq_xO Coq_xH))))))) with
           | true -> I (Integers.Int.shr n1 n2)
           | false -> Unknown)
    | Coq_eval_static_operation_case31 (n, n1) ->
        (match Integers.Int.ltu n
                 (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   (Coq_xO Coq_xH))))))) with
           | true -> I (Integers.Int.shr n1 n)
           | false -> Unknown)
    | Coq_eval_static_operation_case32 (n, n1) ->
        (match Integers.Int.ltu n
                 (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   (Coq_xO Coq_xH))))))) with
           | true -> I (Integers.Int.shrx n1 n)
           | false -> Unknown)
    | Coq_eval_static_operation_case33 (n1, n2) ->
        (match Integers.Int.ltu n2
                 (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
                   (Coq_xO Coq_xH))))))) with
           | true -> I (Integers.Int.shru n1 n2)
           | false -> Unknown)
    | Coq_eval_static_operation_case34 (amount, mask, n1) -> I
        (Integers.Int.rolm n1 amount mask)
    | Coq_eval_static_operation_case35 n1 -> F (Floats.Float.neg n1)
    | Coq_eval_static_operation_case36 n1 -> F (Floats.Float.abs n1)
    | Coq_eval_static_operation_case37 (n1, n2) -> F (Floats.Float.add n1 n2)
    | Coq_eval_static_operation_case38 (n1, n2) -> F (Floats.Float.sub n1 n2)
    | Coq_eval_static_operation_case39 (n1, n2) -> F (Floats.Float.mul n1 n2)
    | Coq_eval_static_operation_case40 (n1, n2) -> F (Floats.Float.div n1 n2)
    | Coq_eval_static_operation_case41 (n1, n2, n3) -> F
        (Floats.Float.add (Floats.Float.mul n1 n2) n3)
    | Coq_eval_static_operation_case42 (n1, n2, n3) -> F
        (Floats.Float.sub (Floats.Float.mul n1 n2) n3)
    | Coq_eval_static_operation_case43 n1 -> F
        (Floats.Float.singleoffloat n1)
    | Coq_eval_static_operation_case44 n1 -> I (Floats.Float.intoffloat n1)
    | Coq_eval_static_operation_case45 n1 -> F (Floats.Float.floatofint n1)
    | Coq_eval_static_operation_case46 n1 -> F (Floats.Float.floatofintu n1)
    | Coq_eval_static_operation_case47 (c, vl0) ->
        (match eval_static_condition c vl0 with
           | Some b -> I
               (match b with
                  | true -> Integers.Int.one
                  | false -> Integers.Int.zero)
           | None -> Unknown)
    | Coq_eval_static_operation_case48 n1 -> I
        (Integers.Int.cast8unsigned n1)
    | Coq_eval_static_operation_case49 n1 -> I
        (Integers.Int.cast16unsigned n1)
    | Coq_eval_static_operation_default (op0, vl0) -> Unknown

(** val approx_regs : reg list -> D.t -> Approx.t list **)

let rec approx_regs rl approx0 =
  match rl with
    | Coq_nil -> Coq_nil
    | Coq_cons (a, t0) -> Coq_cons ((D.get a approx0),
        (approx_regs t0 approx0))

(** val transfer : coq_function -> node -> D.t -> D.t **)

let transfer f pc before =
  match Maps.PTree.get pc f.fn_code with
    | Some i ->
        (match i with
           | Inop s -> before
           | Iop (op, args, res, s) ->
               D.set res
                 (eval_static_operation op
                   (let rec map0 = function
                      | Coq_nil -> Coq_nil
                      | Coq_cons (a, t0) -> Coq_cons (
                          (D.get a before), (map0 t0))
                    in map0 args)) before
           | Iload (chunk, addr, args, dst, s) -> D.set dst Unknown before
           | Istore (chunk, addr, args, src, s) -> before
           | Icall (sig0, ros, args, res, s) -> D.set res Unknown before
           | Itailcall (sig0, ros, args) -> before
           | Ialloc (arg, res, s) -> D.set res Unknown before
           | Icond (cond, args, ifso, ifnot) -> before
           | Ireturn optarg -> before)
    | None -> before

module DS = Kildall.Dataflow_Solver(D)(Kildall.NodeSetForward)

(** val analyze : coq_function -> D.t Maps.PMap.t **)

let analyze f =
  match DS.fixpoint (successors f) f.fn_nextpc (transfer f) (Coq_cons
          ((Coq_pair (f.fn_entrypoint, D.top)), Coq_nil)) with
    | Some res -> res
    | None -> Maps.PMap.init D.top

(** val intval : D.t -> reg -> int option **)

let intval approx0 r =
  match D.get r approx0 with
    | Novalue -> None
    | Unknown -> None
    | I n -> Some n
    | F f -> None
    | S (i, i0) -> None

type cond_strength_reduction_cases =
  | Coq_csr_case1 of comparison * reg * reg
  | Coq_csr_case2 of comparison * reg * reg
  | Coq_csr_default of condition * reg list

(** val cond_strength_reduction_cases_rect : (comparison -> reg -> reg ->
                                             'a1) -> (comparison -> reg ->
                                             reg -> 'a1) -> (condition -> reg
                                             list -> 'a1) -> condition -> reg
                                             list ->
                                             cond_strength_reduction_cases ->
                                             'a1 **)

let cond_strength_reduction_cases_rect f f0 f1 c l = function
  | Coq_csr_case1 (x, x0, x1) -> f x x0 x1
  | Coq_csr_case2 (x, x0, x1) -> f0 x x0 x1
  | Coq_csr_default (x, x0) -> f1 x x0

(** val cond_strength_reduction_cases_rec : (comparison -> reg -> reg -> 'a1)
                                            -> (comparison -> reg -> reg ->
                                            'a1) -> (condition -> reg list ->
                                            'a1) -> condition -> reg list ->
                                            cond_strength_reduction_cases ->
                                            'a1 **)

let cond_strength_reduction_cases_rec f f0 f1 c l = function
  | Coq_csr_case1 (x, x0, x1) -> f x x0 x1
  | Coq_csr_case2 (x, x0, x1) -> f0 x x0 x1
  | Coq_csr_default (x, x0) -> f1 x x0

(** val cond_strength_reduction_match : condition -> reg list ->
                                        cond_strength_reduction_cases **)

let cond_strength_reduction_match cond rl =
  match cond with
    | Ccomp c ->
        (match rl with
           | Coq_nil -> Coq_csr_default ((Ccomp c), Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_csr_default ((Ccomp c), (Coq_cons (r1,
                      Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_csr_case1 (c, r1, r2)
                         | Coq_cons (r, l1) -> Coq_csr_default ((Ccomp c),
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Ccompu c ->
        (match rl with
           | Coq_nil -> Coq_csr_default ((Ccompu c), Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_csr_default ((Ccompu c), (Coq_cons (r1,
                      Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_csr_case2 (c, r1, r2)
                         | Coq_cons (r, l1) -> Coq_csr_default ((Ccompu c),
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Ccompimm (c, i) -> Coq_csr_default ((Ccompimm (c, i)), rl)
    | Ccompuimm (c, i) -> Coq_csr_default ((Ccompuimm (c, i)), rl)
    | Ccompf c -> Coq_csr_default ((Ccompf c), rl)
    | Cnotcompf c -> Coq_csr_default ((Cnotcompf c), rl)
    | Cmaskzero i -> Coq_csr_default ((Cmaskzero i), rl)
    | Cmasknotzero i -> Coq_csr_default ((Cmasknotzero i), rl)

(** val cond_strength_reduction : D.t -> condition -> reg list -> (condition,
                                  reg list) prod **)

let cond_strength_reduction approx0 cond args =
  match cond_strength_reduction_match cond args with
    | Coq_csr_case1 (c, r1, r2) ->
        (match intval approx0 r1 with
           | Some n -> Coq_pair ((Ccompimm ((swap_comparison c), n)),
               (Coq_cons (r2, Coq_nil)))
           | None ->
               (match intval approx0 r2 with
                  | Some n -> Coq_pair ((Ccompimm (c, n)), (Coq_cons (r1,
                      Coq_nil)))
                  | None -> Coq_pair (cond, args)))
    | Coq_csr_case2 (c, r1, r2) ->
        (match intval approx0 r1 with
           | Some n -> Coq_pair ((Ccompuimm ((swap_comparison c), n)),
               (Coq_cons (r2, Coq_nil)))
           | None ->
               (match intval approx0 r2 with
                  | Some n -> Coq_pair ((Ccompuimm (c, n)), (Coq_cons (r1,
                      Coq_nil)))
                  | None -> Coq_pair (cond, args)))
    | Coq_csr_default (cond0, args0) -> Coq_pair (cond0, args0)

(** val make_addimm : int -> reg -> (operation, reg list) prod **)

let make_addimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
    | false -> Coq_pair ((Oaddimm n), (Coq_cons (r, Coq_nil)))

(** val make_shlimm : int -> reg -> (operation, reg list) prod **)

let make_shlimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
    | false -> Coq_pair ((Orolm (n, (Integers.Int.shl Integers.Int.mone n))),
        (Coq_cons (r, Coq_nil)))

(** val make_shrimm : int -> reg -> (operation, reg list) prod **)

let make_shrimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
    | false -> Coq_pair ((Oshrimm n), (Coq_cons (r, Coq_nil)))

(** val make_shruimm : int -> reg -> (operation, reg list) prod **)

let make_shruimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
    | false -> Coq_pair ((Orolm
        ((Integers.Int.sub
           (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
             Coq_xH))))))) n), (Integers.Int.shru Integers.Int.mone n))),
        (Coq_cons (r, Coq_nil)))

(** val make_mulimm : int -> reg -> (operation, reg list) prod **)

let make_mulimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair ((Ointconst Integers.Int.zero), Coq_nil)
    | false ->
        (match Integers.Int.eq n Integers.Int.one with
           | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
           | false ->
               (match Integers.Int.is_power2 n with
                  | Some l -> make_shlimm l r
                  | None -> Coq_pair ((Omulimm n), (Coq_cons (r, Coq_nil)))))

(** val make_andimm : int -> reg -> (operation, reg list) prod **)

let make_andimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair ((Ointconst Integers.Int.zero), Coq_nil)
    | false ->
        (match Integers.Int.eq n Integers.Int.mone with
           | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
           | false -> Coq_pair ((Oandimm n), (Coq_cons (r, Coq_nil))))

(** val make_orimm : int -> reg -> (operation, reg list) prod **)

let make_orimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
    | false ->
        (match Integers.Int.eq n Integers.Int.mone with
           | true -> Coq_pair ((Ointconst Integers.Int.mone), Coq_nil)
           | false -> Coq_pair ((Oorimm n), (Coq_cons (r, Coq_nil))))

(** val make_xorimm : int -> reg -> (operation, reg list) prod **)

let make_xorimm n r =
  match Integers.Int.eq n Integers.Int.zero with
    | true -> Coq_pair (Omove, (Coq_cons (r, Coq_nil)))
    | false -> Coq_pair ((Oxorimm n), (Coq_cons (r, Coq_nil)))

type op_strength_reduction_cases =
  | Coq_op_strength_reduction_case1 of reg * reg
  | Coq_op_strength_reduction_case2 of reg * reg
  | Coq_op_strength_reduction_case3 of reg * reg
  | Coq_op_strength_reduction_case4 of reg * reg
  | Coq_op_strength_reduction_case5 of reg * reg
  | Coq_op_strength_reduction_case6 of reg * reg
  | Coq_op_strength_reduction_case7 of reg * reg
  | Coq_op_strength_reduction_case8 of reg * reg
  | Coq_op_strength_reduction_case9 of reg * reg
  | Coq_op_strength_reduction_case10 of reg * reg
  | Coq_op_strength_reduction_case11 of reg * reg
  | Coq_op_strength_reduction_case12 of condition * reg list
  | Coq_op_strength_reduction_default of operation * reg list

(** val op_strength_reduction_cases_rect : (reg -> reg -> 'a1) -> (reg -> reg
                                           -> 'a1) -> (reg -> reg -> 'a1) ->
                                           (reg -> reg -> 'a1) -> (reg -> reg
                                           -> 'a1) -> (reg -> reg -> 'a1) ->
                                           (reg -> reg -> 'a1) -> (reg -> reg
                                           -> 'a1) -> (reg -> reg -> 'a1) ->
                                           (reg -> reg -> 'a1) -> (reg -> reg
                                           -> 'a1) -> (condition -> reg list
                                           -> 'a1) -> (operation -> reg list
                                           -> 'a1) -> operation -> reg list
                                           -> op_strength_reduction_cases ->
                                           'a1 **)

let op_strength_reduction_cases_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o l = function
  | Coq_op_strength_reduction_case1 (x, x0) -> f x x0
  | Coq_op_strength_reduction_case2 (x, x0) -> f0 x x0
  | Coq_op_strength_reduction_case3 (x, x0) -> f1 x x0
  | Coq_op_strength_reduction_case4 (x, x0) -> f2 x x0
  | Coq_op_strength_reduction_case5 (x, x0) -> f3 x x0
  | Coq_op_strength_reduction_case6 (x, x0) -> f4 x x0
  | Coq_op_strength_reduction_case7 (x, x0) -> f5 x x0
  | Coq_op_strength_reduction_case8 (x, x0) -> f6 x x0
  | Coq_op_strength_reduction_case9 (x, x0) -> f7 x x0
  | Coq_op_strength_reduction_case10 (x, x0) -> f8 x x0
  | Coq_op_strength_reduction_case11 (x, x0) -> f9 x x0
  | Coq_op_strength_reduction_case12 (x, x0) -> f10 x x0
  | Coq_op_strength_reduction_default (x, x0) -> f11 x x0

(** val op_strength_reduction_cases_rec : (reg -> reg -> 'a1) -> (reg -> reg
                                          -> 'a1) -> (reg -> reg -> 'a1) ->
                                          (reg -> reg -> 'a1) -> (reg -> reg
                                          -> 'a1) -> (reg -> reg -> 'a1) ->
                                          (reg -> reg -> 'a1) -> (reg -> reg
                                          -> 'a1) -> (reg -> reg -> 'a1) ->
                                          (reg -> reg -> 'a1) -> (reg -> reg
                                          -> 'a1) -> (condition -> reg list
                                          -> 'a1) -> (operation -> reg list
                                          -> 'a1) -> operation -> reg list ->
                                          op_strength_reduction_cases -> 'a1 **)

let op_strength_reduction_cases_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 o l = function
  | Coq_op_strength_reduction_case1 (x, x0) -> f x x0
  | Coq_op_strength_reduction_case2 (x, x0) -> f0 x x0
  | Coq_op_strength_reduction_case3 (x, x0) -> f1 x x0
  | Coq_op_strength_reduction_case4 (x, x0) -> f2 x x0
  | Coq_op_strength_reduction_case5 (x, x0) -> f3 x x0
  | Coq_op_strength_reduction_case6 (x, x0) -> f4 x x0
  | Coq_op_strength_reduction_case7 (x, x0) -> f5 x x0
  | Coq_op_strength_reduction_case8 (x, x0) -> f6 x x0
  | Coq_op_strength_reduction_case9 (x, x0) -> f7 x x0
  | Coq_op_strength_reduction_case10 (x, x0) -> f8 x x0
  | Coq_op_strength_reduction_case11 (x, x0) -> f9 x x0
  | Coq_op_strength_reduction_case12 (x, x0) -> f10 x x0
  | Coq_op_strength_reduction_default (x, x0) -> f11 x x0

(** val op_strength_reduction_match : operation -> reg list ->
                                      op_strength_reduction_cases **)

let op_strength_reduction_match op args =
  match op with
    | Omove -> Coq_op_strength_reduction_default (Omove, args)
    | Ointconst i -> Coq_op_strength_reduction_default ((Ointconst i), args)
    | Ofloatconst f -> Coq_op_strength_reduction_default ((Ofloatconst f),
        args)
    | Oaddrsymbol (i, i0) -> Coq_op_strength_reduction_default ((Oaddrsymbol
        (i, i0)), args)
    | Oaddrstack i -> Coq_op_strength_reduction_default ((Oaddrstack i),
        args)
    | Ocast8signed -> Coq_op_strength_reduction_default (Ocast8signed, args)
    | Ocast8unsigned -> Coq_op_strength_reduction_default (Ocast8unsigned,
        args)
    | Ocast16signed -> Coq_op_strength_reduction_default (Ocast16signed,
        args)
    | Ocast16unsigned -> Coq_op_strength_reduction_default (Ocast16unsigned,
        args)
    | Oadd ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oadd, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oadd,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case1 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oadd,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oaddimm i -> Coq_op_strength_reduction_default ((Oaddimm i), args)
    | Osub ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Osub, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Osub,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case2 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Osub,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Osubimm i -> Coq_op_strength_reduction_default ((Osubimm i), args)
    | Omul ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Omul, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Omul,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case3 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Omul,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Omulimm i -> Coq_op_strength_reduction_default ((Omulimm i), args)
    | Odiv ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Odiv, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Odiv,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case4 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Odiv,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Odivu ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Odivu, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Odivu,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case5 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Odivu,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oand ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oand, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oand,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case6 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oand,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oandimm i -> Coq_op_strength_reduction_default ((Oandimm i), args)
    | Oor ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oor, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oor,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case7 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oor,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oorimm i -> Coq_op_strength_reduction_default ((Oorimm i), args)
    | Oxor ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oxor, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oxor,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case8 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oxor,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oxorimm i -> Coq_op_strength_reduction_default ((Oxorimm i), args)
    | Onand -> Coq_op_strength_reduction_default (Onand, args)
    | Onor -> Coq_op_strength_reduction_default (Onor, args)
    | Onxor -> Coq_op_strength_reduction_default (Onxor, args)
    | Oshl ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oshl, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oshl,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case9 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oshl,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oshr ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oshr, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oshr,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case10 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oshr,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Oshrimm i -> Coq_op_strength_reduction_default ((Oshrimm i), args)
    | Oshrximm i -> Coq_op_strength_reduction_default ((Oshrximm i), args)
    | Oshru ->
        (match args with
           | Coq_nil -> Coq_op_strength_reduction_default (Oshru, Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_op_strength_reduction_default (Oshru,
                      (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_op_strength_reduction_case11 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_op_strength_reduction_default (Oshru,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Orolm (i, i0) -> Coq_op_strength_reduction_default ((Orolm (i, i0)),
        args)
    | Onegf -> Coq_op_strength_reduction_default (Onegf, args)
    | Oabsf -> Coq_op_strength_reduction_default (Oabsf, args)
    | Oaddf -> Coq_op_strength_reduction_default (Oaddf, args)
    | Osubf -> Coq_op_strength_reduction_default (Osubf, args)
    | Omulf -> Coq_op_strength_reduction_default (Omulf, args)
    | Odivf -> Coq_op_strength_reduction_default (Odivf, args)
    | Omuladdf -> Coq_op_strength_reduction_default (Omuladdf, args)
    | Omulsubf -> Coq_op_strength_reduction_default (Omulsubf, args)
    | Osingleoffloat -> Coq_op_strength_reduction_default (Osingleoffloat,
        args)
    | Ointoffloat -> Coq_op_strength_reduction_default (Ointoffloat, args)
    | Ofloatofint -> Coq_op_strength_reduction_default (Ofloatofint, args)
    | Ofloatofintu -> Coq_op_strength_reduction_default (Ofloatofintu, args)
    | Ocmp c -> Coq_op_strength_reduction_case12 (c, args)

(** val op_strength_reduction : D.t -> operation -> reg list -> (operation,
                                reg list) prod **)

let op_strength_reduction approx0 op args =
  match op_strength_reduction_match op args with
    | Coq_op_strength_reduction_case1 (r1, r2) ->
        (match intval approx0 r1 with
           | Some n -> make_addimm n r2
           | None ->
               (match intval approx0 r2 with
                  | Some n -> make_addimm n r1
                  | None -> Coq_pair (op, args)))
    | Coq_op_strength_reduction_case2 (r1, r2) ->
        (match intval approx0 r1 with
           | Some n -> Coq_pair ((Osubimm n), (Coq_cons (r2, Coq_nil)))
           | None ->
               (match intval approx0 r2 with
                  | Some n -> make_addimm (Integers.Int.neg n) r1
                  | None -> Coq_pair (op, args)))
    | Coq_op_strength_reduction_case3 (r1, r2) ->
        (match intval approx0 r1 with
           | Some n -> make_mulimm n r2
           | None ->
               (match intval approx0 r2 with
                  | Some n -> make_mulimm n r1
                  | None -> Coq_pair (op, args)))
    | Coq_op_strength_reduction_case4 (r1, r2) ->
        (match intval approx0 r2 with
           | Some n ->
               (match Integers.Int.is_power2 n with
                  | Some l -> Coq_pair ((Oshrximm l), (Coq_cons (r1,
                      Coq_nil)))
                  | None -> Coq_pair (op, args))
           | None -> Coq_pair (op, args))
    | Coq_op_strength_reduction_case5 (r1, r2) ->
        (match intval approx0 r2 with
           | Some n ->
               (match Integers.Int.is_power2 n with
                  | Some l -> make_shruimm l r1
                  | None -> Coq_pair (op, args))
           | None -> Coq_pair (op, args))
    | Coq_op_strength_reduction_case6 (r1, r2) ->
        (match intval approx0 r1 with
           | Some n ->
               (match Integers.Int.eq n Integers.Int.zero with
                  | true -> Coq_pair ((Ointconst Integers.Int.zero), Coq_nil)
                  | false ->
                      (match Integers.Int.eq n Integers.Int.mone with
                         | true -> Coq_pair (Omove, (Coq_cons (r2, Coq_nil)))
                         | false -> Coq_pair ((Oandimm n), (Coq_cons (r2,
                             Coq_nil)))))
           | None ->
               (match intval approx0 r2 with
                  | Some n ->
                      (match Integers.Int.eq n Integers.Int.zero with
                         | true -> Coq_pair ((Ointconst Integers.Int.zero),
                             Coq_nil)
                         | false ->
                             (match Integers.Int.eq n Integers.Int.mone with
                                | true -> Coq_pair (Omove, (Coq_cons (r1,
                                    Coq_nil)))
                                | false -> Coq_pair ((Oandimm n), (Coq_cons
                                    (r1, Coq_nil)))))
                  | None -> Coq_pair (op, args)))
    | Coq_op_strength_reduction_case7 (r1, r2) ->
        (match intval approx0 r1 with
           | Some n ->
               (match Integers.Int.eq n Integers.Int.zero with
                  | true -> Coq_pair (Omove, (Coq_cons (r2, Coq_nil)))
                  | false ->
                      (match Integers.Int.eq n Integers.Int.mone with
                         | true -> Coq_pair ((Ointconst Integers.Int.mone),
                             Coq_nil)
                         | false -> Coq_pair ((Oorimm n), (Coq_cons (r2,
                             Coq_nil)))))
           | None ->
               (match intval approx0 r2 with
                  | Some n ->
                      (match Integers.Int.eq n Integers.Int.zero with
                         | true -> Coq_pair (Omove, (Coq_cons (r1, Coq_nil)))
                         | false ->
                             (match Integers.Int.eq n Integers.Int.mone with
                                | true -> Coq_pair ((Ointconst
                                    Integers.Int.mone), Coq_nil)
                                | false -> Coq_pair ((Oorimm n), (Coq_cons
                                    (r1, Coq_nil)))))
                  | None -> Coq_pair (op, args)))
    | Coq_op_strength_reduction_case8 (r1, r2) ->
        (match intval approx0 r1 with
           | Some n -> make_xorimm n r2
           | None ->
               (match intval approx0 r2 with
                  | Some n -> make_xorimm n r1
                  | None -> Coq_pair (op, args)))
    | Coq_op_strength_reduction_case9 (r1, r2) ->
        (match intval approx0 r2 with
           | Some n ->
               (match Integers.Int.ltu n
                        (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO
                          (Coq_xO (Coq_xO Coq_xH))))))) with
                  | true -> make_shlimm n r1
                  | false -> Coq_pair (op, args))
           | None -> Coq_pair (op, args))
    | Coq_op_strength_reduction_case10 (r1, r2) ->
        (match intval approx0 r2 with
           | Some n ->
               (match Integers.Int.ltu n
                        (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO
                          (Coq_xO (Coq_xO Coq_xH))))))) with
                  | true -> make_shrimm n r1
                  | false -> Coq_pair (op, args))
           | None -> Coq_pair (op, args))
    | Coq_op_strength_reduction_case11 (r1, r2) ->
        (match intval approx0 r2 with
           | Some n ->
               (match Integers.Int.ltu n
                        (Integers.Int.repr (Zpos (Coq_xO (Coq_xO (Coq_xO
                          (Coq_xO (Coq_xO Coq_xH))))))) with
                  | true -> make_shruimm n r1
                  | false -> Coq_pair (op, args))
           | None -> Coq_pair (op, args))
    | Coq_op_strength_reduction_case12 (c, args0) ->
        let Coq_pair (c', args') = cond_strength_reduction approx0 c args0 in
        Coq_pair ((Ocmp c'), args')
    | Coq_op_strength_reduction_default (op0, args0) -> Coq_pair (op0, args0)

type addr_strength_reduction_cases =
  | Coq_addr_strength_reduction_case1 of reg * reg
  | Coq_addr_strength_reduction_case2 of ident * int * reg
  | Coq_addr_strength_reduction_case3 of int * reg
  | Coq_addr_strength_reduction_default of addressing * reg list

(** val addr_strength_reduction_cases_rect : (reg -> reg -> 'a1) -> (ident ->
                                             int -> reg -> 'a1) -> (int ->
                                             reg -> 'a1) -> (addressing ->
                                             reg list -> 'a1) -> addressing
                                             -> reg list ->
                                             addr_strength_reduction_cases ->
                                             'a1 **)

let addr_strength_reduction_cases_rect f f0 f1 f2 addr args = function
  | Coq_addr_strength_reduction_case1 (x, x0) -> f x x0
  | Coq_addr_strength_reduction_case2 (x, x0, x1) -> f0 x x0 x1
  | Coq_addr_strength_reduction_case3 (x, x0) -> f1 x x0
  | Coq_addr_strength_reduction_default (x, x0) -> f2 x x0

(** val addr_strength_reduction_cases_rec : (reg -> reg -> 'a1) -> (ident ->
                                            int -> reg -> 'a1) -> (int -> reg
                                            -> 'a1) -> (addressing -> reg
                                            list -> 'a1) -> addressing -> reg
                                            list ->
                                            addr_strength_reduction_cases ->
                                            'a1 **)

let addr_strength_reduction_cases_rec f f0 f1 f2 addr args = function
  | Coq_addr_strength_reduction_case1 (x, x0) -> f x x0
  | Coq_addr_strength_reduction_case2 (x, x0, x1) -> f0 x x0 x1
  | Coq_addr_strength_reduction_case3 (x, x0) -> f1 x x0
  | Coq_addr_strength_reduction_default (x, x0) -> f2 x x0

(** val addr_strength_reduction_match : addressing -> reg list ->
                                        addr_strength_reduction_cases **)

let addr_strength_reduction_match addr args =
  match addr with
    | Aindexed n ->
        (match args with
           | Coq_nil -> Coq_addr_strength_reduction_default ((Aindexed n),
               Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_addr_strength_reduction_case3 (n, r1)
                  | Coq_cons (r, l0) -> Coq_addr_strength_reduction_default
                      ((Aindexed n), (Coq_cons (r1, (Coq_cons (r, l0)))))))
    | Aindexed2 ->
        (match args with
           | Coq_nil -> Coq_addr_strength_reduction_default (Aindexed2,
               Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_addr_strength_reduction_default
                      (Aindexed2, (Coq_cons (r1, Coq_nil)))
                  | Coq_cons (r2, l0) ->
                      (match l0 with
                         | Coq_nil -> Coq_addr_strength_reduction_case1 (r1,
                             r2)
                         | Coq_cons (r, l1) ->
                             Coq_addr_strength_reduction_default (Aindexed2,
                             (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r,
                             l1))))))))))
    | Aglobal (i, i0) -> Coq_addr_strength_reduction_default ((Aglobal (i,
        i0)), args)
    | Abased (symb, ofs) ->
        (match args with
           | Coq_nil -> Coq_addr_strength_reduction_default ((Abased (symb,
               ofs)), Coq_nil)
           | Coq_cons (r1, l) ->
               (match l with
                  | Coq_nil -> Coq_addr_strength_reduction_case2 (symb, ofs,
                      r1)
                  | Coq_cons (r, l0) -> Coq_addr_strength_reduction_default
                      ((Abased (symb, ofs)), (Coq_cons (r1, (Coq_cons (r,
                      l0)))))))
    | Ainstack i -> Coq_addr_strength_reduction_default ((Ainstack i), args)

(** val addr_strength_reduction : D.t -> addressing -> reg list ->
                                  (addressing, reg list) prod **)

let addr_strength_reduction approx0 addr args =
  match addr_strength_reduction_match addr args with
    | Coq_addr_strength_reduction_case1 (r1, r2) ->
        (match D.get r1 approx0 with
           | Novalue ->
               (match D.get r2 approx0 with
                  | Novalue -> Coq_pair (addr, args)
                  | Unknown -> Coq_pair (addr, args)
                  | I n2 -> Coq_pair ((Aindexed n2), (Coq_cons (r1,
                      Coq_nil)))
                  | F f -> Coq_pair (addr, args)
                  | S (symb, n2) -> Coq_pair ((Abased (symb, n2)), (Coq_cons
                      (r1, Coq_nil))))
           | Unknown ->
               (match D.get r2 approx0 with
                  | Novalue -> Coq_pair (addr, args)
                  | Unknown -> Coq_pair (addr, args)
                  | I n2 -> Coq_pair ((Aindexed n2), (Coq_cons (r1,
                      Coq_nil)))
                  | F f -> Coq_pair (addr, args)
                  | S (symb, n2) -> Coq_pair ((Abased (symb, n2)), (Coq_cons
                      (r1, Coq_nil))))
           | I n1 ->
               (match D.get r2 approx0 with
                  | Novalue -> Coq_pair ((Aindexed n1), (Coq_cons (r2,
                      Coq_nil)))
                  | Unknown -> Coq_pair ((Aindexed n1), (Coq_cons (r2,
                      Coq_nil)))
                  | I n2 -> Coq_pair ((Aindexed n1), (Coq_cons (r2,
                      Coq_nil)))
                  | F f -> Coq_pair ((Aindexed n1), (Coq_cons (r2, Coq_nil)))
                  | S (symb, n2) -> Coq_pair ((Aglobal (symb,
                      (Integers.Int.add n1 n2))), Coq_nil))
           | F f ->
               (match D.get r2 approx0 with
                  | Novalue -> Coq_pair (addr, args)
                  | Unknown -> Coq_pair (addr, args)
                  | I n2 -> Coq_pair ((Aindexed n2), (Coq_cons (r1,
                      Coq_nil)))
                  | F f0 -> Coq_pair (addr, args)
                  | S (symb, n2) -> Coq_pair ((Abased (symb, n2)), (Coq_cons
                      (r1, Coq_nil))))
           | S (symb, n1) ->
               (match D.get r2 approx0 with
                  | Novalue -> Coq_pair ((Abased (symb, n1)), (Coq_cons (r2,
                      Coq_nil)))
                  | Unknown -> Coq_pair ((Abased (symb, n1)), (Coq_cons (r2,
                      Coq_nil)))
                  | I n2 -> Coq_pair ((Aglobal (symb,
                      (Integers.Int.add n1 n2))), Coq_nil)
                  | F f -> Coq_pair ((Abased (symb, n1)), (Coq_cons (r2,
                      Coq_nil)))
                  | S (symb0, n2) -> Coq_pair ((Abased (symb, n1)), (Coq_cons
                      (r2, Coq_nil)))))
    | Coq_addr_strength_reduction_case2 (symb, ofs, r1) ->
        (match intval approx0 r1 with
           | Some n -> Coq_pair ((Aglobal (symb, (Integers.Int.add ofs n))),
               Coq_nil)
           | None -> Coq_pair (addr, args))
    | Coq_addr_strength_reduction_case3 (n, r1) ->
        (match D.get r1 approx0 with
           | Novalue -> Coq_pair (addr, args)
           | Unknown -> Coq_pair (addr, args)
           | I i -> Coq_pair (addr, args)
           | F f -> Coq_pair (addr, args)
           | S (symb, ofs) -> Coq_pair ((Aglobal (symb,
               (Integers.Int.add ofs n))), Coq_nil))
    | Coq_addr_strength_reduction_default (addr0, args0) -> Coq_pair (addr0,
        args0)

(** val transf_ros : D.t -> (reg, ident) sum -> (reg, ident) sum **)

let transf_ros approx0 ros = match ros with
  | Coq_inl r ->
      (match D.get r approx0 with
         | Novalue -> ros
         | Unknown -> ros
         | I i -> ros
         | F f -> ros
         | S (symb, ofs) ->
             (match Integers.Int.eq ofs Integers.Int.zero with
                | true -> Coq_inr symb
                | false -> ros))
  | Coq_inr s -> ros

(** val transf_instr : D.t -> instruction -> instruction **)

let transf_instr approx0 instr = match instr with
  | Inop n -> instr
  | Iop (op, args, res, s) ->
      (match eval_static_operation op
               (let rec map0 = function
                  | Coq_nil -> Coq_nil
                  | Coq_cons (a, t0) -> Coq_cons ((D.get a approx0),
                      (map0 t0))
                in map0 args) with
         | Novalue ->
             let Coq_pair (op', args') =
               op_strength_reduction approx0 op args
             in
             Iop (op', args', res, s)
         | Unknown ->
             let Coq_pair (op', args') =
               op_strength_reduction approx0 op args
             in
             Iop (op', args', res, s)
         | I n -> Iop ((Ointconst n), Coq_nil, res, s)
         | F n -> Iop ((Ofloatconst n), Coq_nil, res, s)
         | S (symb, ofs) -> Iop ((Oaddrsymbol (symb, ofs)), Coq_nil, res, s))
  | Iload (chunk, addr, args, dst, s) -> instr
  | Istore (chunk, addr, args, src, s) -> instr
  | Icall (sig0, ros, args, res, s) -> instr
  | Itailcall (sig0, ros, args) -> instr
  | Ialloc (arg, res, s) -> instr
  | Icond (cond, args, s1, s2) -> instr
  | Ireturn o -> instr

(** val transf_code : D.t Maps.PMap.t -> code -> code **)

let transf_code approxs instrs =
  Maps.PTree.map (fun pc instr ->
    transf_instr (Maps.PMap.get pc approxs) instr) instrs

(** val transf_function : coq_function -> coq_function **)

let transf_function f =
  Printf.printf "Constant propagation : ";
  if Compcert_trigger.triggered 2 = false
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
let transf_function' f =
  { fn_sig = f.fn_sig; fn_params = f.fn_params; fn_stacksize =
    f.fn_stacksize; fn_code = (transf_code (analyze f) f.fn_code);
    fn_entrypoint = f.fn_entrypoint; fn_nextpc = f.fn_nextpc }

(** val transf_fundef : fundef -> fundef **)

let transf_fundef = function
  | Internal f -> Internal (transf_function' f)
  | External ef -> External ef

(** val transf_program : program -> program **)

let transf_program p =
  transform_program transf_fundef p
*)
