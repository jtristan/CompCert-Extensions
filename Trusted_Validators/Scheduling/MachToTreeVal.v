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
Require Import Two_level_repr.
Require Import Valcommon.
Require Import BasicLib. 

 

Parameter elaborate : Mach.code -> option Two_level_repr.cfg.


Section Val. 

Variable f : Mach.function. 
Variable cfg : Two_level_repr.function. 

Notation "a && b" := (andb a b). 

(** validation pour un arbre d instructions *)

Inductive validTreeProp (s : list label) : code -> instructions_tree -> Prop := 

  | labelControl: forall lbl t l,
    ~ In lbl s -> 
    validTreeProp s l t ->
    validTreeProp s (Mlabel lbl :: l) t 
    
  | gotoControl: forall lbl l t l',
    ~ In lbl s -> 
    validTreeProp s l' t  -> find_label lbl (fn_code f) = Some l' ->
   validTreeProp s (Mgoto lbl :: l) t 

  | getStackSync: forall i t m l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Mgetstack i t m :: l) (Two_level_repr.Mgetstack i t m sub)

  | setStackSync: forall i t m l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Msetstack m i t :: l) (Two_level_repr.Msetstack m i t sub)

  | getParamSync: forall i t m l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Mgetparam i t m :: l) (Two_level_repr.Mgetparam i t m sub)

  | opSync: forall op lr m l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Mop op lr m :: l) (Two_level_repr.Mop op lr m sub)

  | loadSync: forall chk addr m lr l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Mload chk addr m lr :: l) (Two_level_repr.Mload chk addr m lr sub)

  | storeSync: forall chk addr lr m l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Mstore chk addr m lr :: l) (Two_level_repr.Mstore chk addr m lr sub)

  | allocSync: forall l sub,
    validTreeProp s l sub ->
    validTreeProp s (Mach.Malloc :: l) (Two_level_repr.Malloc sub)

  | condSync: forall lbl cond rl l l' sub2 sub1,
    ~ In lbl s ->
    find_label lbl (fn_code f) = Some l' -> 
    validTreeProp s l sub2 ->
    validTreeProp s l' sub1 -> 
    validTreeProp s (Mach.Mcond cond rl lbl :: l) (Two_level_repr.Mcond cond rl sub1 sub2)

  | gotoSync: forall lbl l,
    In lbl s ->
    validTreeProp s (Mach.Mgoto lbl :: l) (Two_level_repr.Mout lbl)
 
  | outSync: forall lbl l,
    In lbl s -> 
    validTreeProp s (Mach.Mlabel lbl :: l) (Two_level_repr.Mout lbl)

  | condBack: forall lbl cond rl l sub2,
    In lbl s ->
    validTreeProp s l sub2 ->
    validTreeProp s (Mach.Mcond cond rl lbl :: l) (Two_level_repr.Mcond cond rl (Two_level_repr.Mout lbl) sub2).

Inductive validCallProp (s : list label) : code -> instruction -> Prop :=
  | validCall: 
     forall sig ros l lbl,
     In lbl s -> 
     validTreeProp s l (Two_level_repr.Mout lbl) ->
     validCallProp s (Mach.Mcall sig ros :: l) (Mcall sig ros lbl).

Inductive validReturnProp : code -> instruction -> Prop :=
  | validReturn:
     forall l, 
     validReturnProp (Mach.Mreturn :: l) Mreturn.  

Inductive validProp (s : list label) : code -> instruction -> Prop :=
  | vTree: forall c t, validTreeProp s c t -> validProp s c (Mtree t)
  | vCall: forall c t, validCallProp s c t -> validProp s c t
  | vRet: forall c t, validReturnProp c t -> validProp s c t. 

Fixpoint mem (lbl : label) (l : list label) {struct l} : bool :=
  match l with
  | nil => false
  | lbl' :: l => if peq lbl lbl' then true else (mem lbl l)
  end. 
 

Fixpoint label_unicity (c : code) (l : list label) {struct c} : bool :=
  match c with
  | nil => true
  | Mlabel lbl :: w => if  mem lbl l then false else label_unicity w (lbl :: l)
  | i :: w => label_unicity w l
  end. 
 

Fixpoint wf_instructions_tree (t : instructions_tree) (keys : list label) (head : label) {struct t} :=
  match t with 
  | Mout lbl => mem lbl keys && if peq lbl head then false else true
  | Mgetstack _ _ _ s => wf_instructions_tree s keys head
  | Msetstack _ _ _ s => wf_instructions_tree s keys head
  | Mgetparam _ _ _ s => wf_instructions_tree s keys head
  | Mop _ _ _ s => wf_instructions_tree s keys head
  | Mload _ _ _ _ s => wf_instructions_tree s keys head
  | Mstore _ _ _ _ s => wf_instructions_tree s keys head
  | Malloc s => wf_instructions_tree s keys head
  | Mcond _ _ s1 s2 => wf_instructions_tree s1 keys head && wf_instructions_tree s2 keys head
  end. 

Definition wf_instruction (i : instruction) (keys : list label) (head : label) : bool :=
  match i with
  | Mtree t => wf_instructions_tree t keys head
  | Mcall _ _ lbl => mem lbl keys && if peq lbl head then false else true 
  | Mreturn => true
  end. 

Fixpoint remove (l : list label) (lbl : label) {struct l} : list label :=
  match l with 
  | nil => nil
  | i :: l' => if peq i lbl then remove l' lbl else i :: remove l' lbl
  end. 

Definition wf_cfg :=
  let keys := PTree.xkeys (cfg_code (fn_body cfg)) 1 in
  let b' := 
    List.fold_left (fun acc => fun k => 
             (match (cfg_code (fn_body cfg))!k with 
                 | Some i => wf_instruction i keys (cfg_head (fn_body cfg))
                 | None => false end 
                 && acc)) keys true in 
  b'.  

Fixpoint get_labels (c : code) {struct c} : list label :=
  match c with
  | nil => nil
  | Mlabel lbl :: l => lbl :: (get_labels l)
  | i :: l => get_labels l
  end. 

Fixpoint check_target_aux (c : code) (ens : list label) {struct c} : bool :=
  match c with 
  | nil => true
  | Mgoto lbl :: l => mem lbl ens && check_target_aux l ens
  | Mach.Mcond cond args lbl :: l => mem lbl ens && check_target_aux l ens
  | i :: l => check_target_aux l ens
  end. 

Definition check_target : bool :=
  check_target_aux (fn_code f) (get_labels (fn_code f)). 


Fixpoint skip_control (s : list label) (func c : code) (counter : nat) {struct counter} : option code :=
  match counter with
  | Datatypes.O => None
  | Datatypes.S n => match c with
                | Mlabel lbl :: c' => if mem lbl s then Some (Mlabel lbl :: c') else skip_control s func c' n 
                | Mgoto lbl :: c' => 
                           match find_label lbl func with
                           | Some c'' => if mem lbl s then Some (Mgoto lbl :: c') else skip_control s func c'' n 
                           | None => None
                           end
                | i :: c' => Some (i :: c')
                | _ => None
                end
  end.


Definition test_out (sub : instructions_tree) (lbl : label) : bool :=
  match sub with
  | Two_level_repr.Mout lbl'  => if peq lbl lbl' then true else false
  | _ => false
  end. 

Fixpoint validTreeBase (s : list label) (cur : code) (t : instructions_tree) {struct t} : bool :=
  match (skip_control s (fn_code f) cur (length (fn_code f))), t with
  | Some (Mach.Mgetstack i t m :: l), Two_level_repr.Mgetstack i' t' m' sub => 
             (if Int.eq_dec i i' then true else false) && (if typ_eq t t' then true else false) && (if mreg_eq m m' then true else false) && 
             validTreeBase s l sub
  | Some (Mach.Msetstack m i t :: l), Two_level_repr.Msetstack m' i' t' sub => 
             (if Int.eq_dec i i' then true else false) && (if typ_eq t t' then true else false) && (if mreg_eq m m' then true else false) && 
             validTreeBase s l sub
  | Some (Mach.Mgetparam i t m :: l), Two_level_repr.Mgetparam i' t' m' sub => 
             (if Int.eq_dec i i' then true else false) && (if typ_eq t t' then true else false) && (if mreg_eq m m' then true else false) && 
             validTreeBase s l sub
  | Some (Mach.Mop op lr m :: l), Two_level_repr.Mop op' lr' m' sub => 
             (if operation_eq op op' then true else false) && (if list_mreg_eq lr lr' then true else false) && (if mreg_eq m m' then true else false) && 
             validTreeBase s l sub
  | Some (Mach.Mload chk addr lr m :: l), Two_level_repr.Mload chk' addr' lr' m' sub => 
             (if addressing_eq addr addr' then true else false) && (if memory_chunk_eq chk chk' then true else false) && (if list_mreg_eq lr lr' then true else false) && (if mreg_eq m m' then true else false) && 
             validTreeBase s l sub
  | Some (Mach.Mstore chk addr lr m :: l), Two_level_repr.Mstore chk' addr' lr' m' sub => 
             (if addressing_eq addr addr' then true else false) && (if memory_chunk_eq chk chk' then true else false) && (if list_mreg_eq lr lr' then true else false) && (if mreg_eq m m' then true else false) && 
             validTreeBase s l sub
  | Some (Mach.Malloc :: l), Two_level_repr.Malloc sub =>  
             validTreeBase s l sub
  | Some (Mach.Mcond cond rl lbl :: l), Two_level_repr.Mcond cond' rl' sub1 sub2 =>
             (if condition_eq cond cond' then true else false) && (if list_mreg_eq rl rl' then true else false) && (validTreeBase s l sub2) &&
             if (mem lbl s) then ( test_out sub1 lbl)
                                   else (match find_label lbl (fn_code f) with
                                   | Some l' => (validTreeBase s l' sub1) 
                                   | None => false
                                   end)
  | Some (Mach.Mlabel lbl :: l), Two_level_repr.Mout lbl' => peq lbl lbl'
  | Some (Mach.Mgoto lbl :: l), Two_level_repr.Mout lbl' => peq lbl lbl'
  | _, _ => false
  end.
(*
 | Some (Mach.Mcond cond rl lbl :: l), Two_level_repr.Mcond cond' rl' (Two_level_repr.Mout lbl') sub2 =>
              (if condition_eq cond cond' then true else false) && (if list_mreg_eq rl rl' then true else false) &&
              (validTreeBase s l sub2) && (if peq lbl lbl' then true else false)
*)
  
Definition validTreeIn (s : list label) (lbl : label) (t : instructions_tree) : bool :=
  match find_label lbl (fn_code f) with
  | Some l' => validTreeBase s l' t 
  | None => false
  end. 

(** validation pour un label *)

(* cette definition de valid label suppose que l on a pas de controle faible
  pour ce qui correspond aux calls ou aux returns et em simplifie donc la definition.
  Il est necessaire de s assurer qu il est possible de transformer le code de la sorte *)

Definition validLabel (s : list label) (lbl : label) : bool :=
  match (cfg_code (fn_body cfg))!lbl with
  | Some (Two_level_repr.Mtree t) => validTreeIn s lbl t                     
  | Some (Two_level_repr.Mcall sig ros lblt) => 
            match find_label lbl (fn_code f) with
            | Some l' => match l' with
                | Mach.Mcall sig' ros' :: Mach.Mlabel lbl' :: l'' =>
                                     signature_eq sig sig' &&
                                     mreg_plus_ident_eq ros ros' &&
                                     peq lblt lbl'
                | _ => false
                end
            | None => false
            end
  | Some (Two_level_repr.Mreturn) =>
              match find_label lbl (fn_code f) with
              | Some l' => match l' with
                 | Mach.Mreturn :: l => true
                 | _ => false
                 end
               | None => false
               end
  | None => false
  end.

Definition validCFG : bool :=
   let keys := (remove (PTree.xkeys (cfg_code (fn_body cfg)) xH)
          (cfg_head (fn_body cfg))) in
   let b' := List.fold_left (fun acc => fun k => (validLabel keys k) && acc) keys true in 
   b'.  



End Val. 

Definition transf_function (f : Mach.function) : option Two_level_repr.function :=
  match elaborate (Mach.fn_code f) with
  | Some tf => 
       let tf := Two_level_repr.mkfunction f.(Mach.fn_sig) tf f.(Mach.fn_stacksize) f.(Mach.fn_framesize) in
	let keys := remove (PTree.xkeys (cfg_code (fn_body tf)) 1) (cfg_head (fn_body tf)) in
       if validCFG f tf 
          && label_unicity (fn_code f) nil 
          && wf_cfg tf 
          && (negb (mem (cfg_head (fn_body tf)) keys))
          && match (cfg_code (fn_body tf)) ! (cfg_head (fn_body tf)) with | Some i => true | None => false end
          && validLabel f tf keys (cfg_head (fn_body tf)) 
          && match head (tail (fn_code f)) with | Some (Mach.Mreturn) => false | Some (Mach.Mcall _ _) => false | _ => true end 
          && match head (fn_code f) with | Some (Mlabel lbl) => if peq lbl (cfg_head (fn_body tf)) then true else false | _ => false end
          && match (cfg_code (fn_body tf)) ! (cfg_head (fn_body tf)) with | Some Mreturn => false | _ => true end
          && check_target f
          then Some tf else None
  | None => None
  end.

Definition transf_fundef (f: Mach.fundef) : option Two_level_repr.fundef :=
match f with
  | Internal f => 
       match transf_function f with
       | None => None
       | Some f => Some (Internal f)
       end
  | External f => Some (External f)
  end.

Definition transf_program (p: Mach.program) : option Two_level_repr.program :=
  transform_partial_program transf_fundef p.












 

