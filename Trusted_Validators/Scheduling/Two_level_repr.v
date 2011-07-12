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


Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Mach.
Require Import Locations.
Require Import Maps.
Require Import Floats.
Require Import Machabstr.
Require Import Stackingproof.
Require Import Values.
Require Import Globalenvs.
Require Import Mem.
Require Import Events.

Inductive instructions_tree: Set :=
  | Mgetstack: int -> typ -> mreg -> instructions_tree -> instructions_tree
  | Msetstack: mreg -> int -> typ -> instructions_tree -> instructions_tree
  | Mgetparam: int -> typ -> mreg -> instructions_tree -> instructions_tree
  | Mop: operation -> list mreg -> mreg -> instructions_tree -> instructions_tree
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instructions_tree -> instructions_tree
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instructions_tree -> instructions_tree
  | Malloc: instructions_tree -> instructions_tree
  | Mcond: condition -> list mreg -> instructions_tree -> instructions_tree -> instructions_tree
  | Mout : label -> instructions_tree.

Inductive instruction : Set :=
  | Mtree: instructions_tree -> instruction
  | Mcall: signature -> mreg + ident -> label -> instruction	
  | Mreturn: instruction. 

Definition cfg_body : Set := PTree.t instruction. 

Record cfg : Set := mkcfg {
  cfg_code : cfg_body;
  cfg_head : label
}.

Record function: Set := mkfunction
  { fn_sig: signature;
    fn_body: cfg;
    fn_stacksize: Z;
    fn_framesize: Z }.

Definition fundef := AST.fundef function.

Definition genv := Genv.t fundef.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

Definition find_function (ge : genv) (ros: mreg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs r)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Definition init_frame (f: function) :=
  empty_block (- f.(fn_framesize)) 0.

Inductive exec_instructions_tree:
      genv -> instructions_tree -> val -> frame ->
      regset -> frame -> mem -> trace -> label ->
      regset -> frame -> mem -> Prop :=

  | exec_Mgetstack:
      forall ge subtree sp parent ofs ty dst rs fr m t rs' fr' m' v lbl,
      get_slot fr ty (Int.signed ofs) v ->
      exec_instructions_tree ge subtree sp parent (rs#dst <- v)  fr m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mgetstack ofs ty dst subtree) sp parent rs fr m t lbl rs' fr' m'

  | exec_Msetstack:
     forall ge subtree sp parent src ofs ty  rs fr m t fr0 rs' fr' m' lbl,
     set_slot fr ty (Int.signed ofs) (rs src) fr0 ->
      exec_instructions_tree ge subtree sp parent rs fr0 m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Msetstack src ofs ty subtree) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mgetparam:
      forall ge subtree sp parent ofs ty dst  rs fr m t rs' fr' m' v lbl,
      get_slot parent ty (Int.signed ofs) v ->
      exec_instructions_tree ge subtree sp parent (rs#dst <- v) fr m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mgetparam ofs ty dst subtree) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mop:
      forall ge subtree sp parent op args res  rs fr m t rs' fr' m' v lbl,
      eval_operation ge sp op rs##args = Some v ->
      exec_instructions_tree ge subtree sp parent (rs#res <- v) fr m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mop op args res subtree) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mload:
      forall ge subtree sp parent chunk addr args dst  rs fr m a t rs' fr' m' v lbl,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instructions_tree ge subtree sp parent (rs#dst <- v) fr m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mload chunk addr args dst subtree) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mstore:
      forall ge subtree sp parent chunk addr args src rs fr m m0 t rs' fr' m' a lbl,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m0 ->
      exec_instructions_tree ge subtree sp parent rs fr m0 t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mstore chunk addr args src subtree) sp parent rs fr m t lbl rs' fr' m'
 
  | exec_Malloc:
      forall ge subtree sp parent rs fr m sz m0 blk t rs' fr' m' lbl,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m0, blk) ->
      exec_instructions_tree ge subtree sp parent (rs#Conventions.loc_alloc_result <- 
                                              (Vptr blk Int.zero)) fr m0 t lbl rs' fr' m' ->
      exec_instructions_tree ge (Malloc subtree) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mcond_true:
      forall ge subtree1 subtree2 sp parent cond args rs fr m t rs' fr' m' lbl,
      eval_condition cond rs##args = Some true ->
      exec_instructions_tree ge subtree1 sp parent rs fr m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mcond cond args subtree1 subtree2) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mcond_false:
      forall ge subtree1 subtree2 sp parent cond args  rs fr m t rs' fr' m' lbl,
      eval_condition cond rs##args = Some false ->
      exec_instructions_tree ge subtree2 sp parent rs fr m t lbl rs' fr' m' ->
      exec_instructions_tree ge (Mcond cond args subtree1 subtree2) sp parent rs fr m t lbl rs' fr' m'

  | exec_Mout:
      forall ge sp parent rs fr m lbl,
      exec_instructions_tree ge (Mout lbl) sp parent rs fr m E0 lbl rs fr m.

Section Sem. 

Variable ge : genv. 

Inductive exec_instruction:
      cfg -> val -> frame -> instruction ->
      regset -> frame -> mem -> trace -> label ->
      regset -> frame -> mem -> Prop :=
 | exec_Mcall:
      forall cfg sp parent sig ros rs fr m f' t lbl rs' m',
       find_function ge ros rs = Some f' ->
      exec_function f' fr rs m t rs' m' ->
      exec_instruction cfg sp parent (Mcall sig ros lbl) rs fr m t lbl rs' fr m'
  | exec_Mtree:
      forall cfg sp parent tree rs fr m t lbl rs' fr' m',
      exec_instructions_tree ge tree sp parent rs fr m t lbl rs' fr' m' ->
      exec_instruction cfg sp parent (Mtree tree) rs fr m t lbl rs' fr' m'
(*****
with exec_instr : 
     cfg -> val -> frame ->
     label -> regset -> frame -> mem -> trace ->
     label -> regset -> frame -> mem -> Prop :=
  | exec_Instr_intro:
      forall cfg sp parent lab instr rs fr m t lbl rs' m',
      cfg.(cfg_code)!lab = Some instr->
     exec_instruction cfg sp parent instr rs fr m t lbl rs' fr m' ->
     exec_instr cfg sp parent lab rs fr m t lbl rs' fr m'
******)
(*****
  | exec_Mcall:
      forall cfg sp parent lab sig ros rs fr m f' t lbl rs' m',
      cfg.(cfg_code)!lab = Some (Mcall sig ros lbl) ->
      find_function ge ros rs = Some f' ->
      exec_function f' fr rs m t rs' m' ->
      exec_instr cfg sp parent lab rs fr m t lbl rs' fr m'
  | exec_Mtree:
      forall cfg sp parent lab tree rs fr m t lbl rs' fr' m',
      cfg.(cfg_code)!lab = Some (Mtree tree) ->
      exec_instructions_tree ge tree sp parent rs fr m t lbl rs' fr' m' ->
      exec_instr cfg sp parent lab rs fr m t lbl rs' fr' m'
***)

with exec_instrs:
    cfg -> val -> frame ->
    label -> regset -> frame -> mem -> trace ->
    label -> regset -> frame -> mem -> Prop :=
  | exec_refl: 
     forall cfg sp parent (lbl:label) (rs : regset) (fr :frame ) (m : mem) lbl rs fr m,
     exec_instrs cfg sp parent lbl rs fr m E0 lbl rs fr m 
  | exec_add:
     forall cfg sp parent instr lbl rs fr m t lbl' rs' fr' m' t0 lbl'' rs'' fr'' m'',
     cfg.(cfg_code)!lbl = Some instr->
     exec_instruction cfg sp parent instr rs fr m t lbl' rs' fr' m' ->
     exec_instrs cfg sp parent lbl' rs' fr' m' t0 lbl'' rs'' fr'' m'' ->
     exec_instrs cfg sp parent lbl rs fr m (t ** t0) lbl'' rs'' fr'' m''

with exec_function_body:
      function -> frame -> val -> val ->
      regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_body:
      forall f parent link ra rs m t rs' m1 m2 stk fr1 fr2 fr3 lw,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      set_slot (init_frame f) Tint 0 link fr1 ->
      set_slot fr1 Tint 12 ra fr2 ->
      exec_instrs f.(fn_body) (Vptr stk (Int.repr (-f.(fn_framesize)))) parent
                   (f.(fn_body)).(cfg_head) rs fr2 m1
                t lw rs' fr3 m2 ->
      (f.(fn_body)).(cfg_code)!lw = Some Mreturn ->
      exec_function_body f parent link ra rs m t rs' (Mem.free m2 stk)

with exec_function:
      fundef -> frame -> regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_internal:
      forall f parent rs m t rs' m',
      (forall link ra, 
         Val.has_type link Tint ->
         Val.has_type ra Tint ->
         exec_function_body f parent link ra rs m t rs' m') ->
      exec_function (Internal f) parent rs m t rs' m'
  | exec_funct_external:
      forall ef parent args res rs1 rs2 m t,
      event_match ef args t res ->
      extcall_arguments rs1 parent ef.(ef_sig) args ->
      rs2 = (rs1#(Conventions.loc_result ef.(ef_sig)) <- res) ->
      exec_function (External ef) parent rs1 m t rs2 m.

Scheme exec_instruction_ind5 := Minimality for exec_instruction Sort Prop
  with exec_instrs_ind5 := Minimality for exec_instrs Sort Prop  
  with exec_function_body_ind5 := Minimality for exec_function_body Sort Prop
  with exec_function_ind5 := Minimality for exec_function Sort Prop.

End Sem.  

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  exec_function ge f empty_frame (Regmap.init Vundef) m0 t rs m /\
  rs R3 = r.





