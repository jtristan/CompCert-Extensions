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


(* Valigator *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import DecidableType. 
Require Import FSetWeakInterface. 
Require Import FSetWeakFacts. 
Require Import FSetWeakProperties. 
Require Import FSetWeakList. 
Require Import Errors. 
Require Import Utilities. 
Require Import EqualityAnalysis. 
Require Import AnticipabilityChecker. 
Require Import Unification. 

Unset Extraction Optimize.
Unset Extraction AutoInline. 

Module Valigator (E : UnificationEngine). 

Module M := UE (E). 
Definition unification := M.unification. 

(*
Definition ill_defined (op : operation) : bool :=
  match op with
  | Oaddrsymbol _ _ => true
  | Osub => true
  | Odiv => true
  | Odivu => true
  | Oshl => true
  | Oshr => true
  | Oshrimm n => negb (Int.ltu n (Int.repr 32))   
  | Oshrximm n => negb (Int.ltu n (Int.repr 32))
  | Oshru => true
  | _ => false
  end.

Definition well_formed_op (op : operation)  (args : list reg) : bool :=
  match op, args with
  | Omove, v1::nil => true
  | Ointconst n, nil => true
  | Ofloatconst n, nil => true
  | Oaddrsymbol s ofs, nil => true
  | Oaddrstack ofs, nil => true
  | Ocast8signed, v1 :: nil => true
  | Ocast8unsigned, v1 :: nil => true
  | Ocast16signed, v1 :: nil => true
  | Ocast16unsigned, v1 :: nil => true
  | Oadd, n1 :: n2 :: nil => true
  | Oaddimm n, n1 :: nil => true
  | Osub, n1 :: n2 :: nil => true
  | Osubimm n, n1 :: nil => true
  | Omul, n1 :: n2 :: nil => true
  | Omulimm n, n1 :: nil => true
  | Odiv, n1 :: n2 :: nil => true
  | Odivu, n1 :: n2 :: nil => true
  | Oand, n1 :: n2 :: nil => true
  | Oandimm n, n1 :: nil => true
  | Oor, n1 :: n2 :: nil => true
  | Oorimm n, n1 :: nil => true
  | Oxor, n1 :: n2 :: nil => true
  | Oxorimm n, n1 :: nil => true
  | Onand, n1 :: n2 :: nil => true
  | Onor, n1 :: n2 :: nil => true
  | Onxor, n1 :: n2 :: nil => true
  | Oshl, n1 :: n2 :: nil =>true
  | Oshr, n1 :: n2 :: nil =>true
  | Oshrimm n, n1 :: nil =>true
  | Oshrximm n, n1 :: nil =>true
  | Oshru, n1 :: n2 :: nil =>true
  | Orolm amount mask, n1 :: nil => true
  | Onegf, f1 :: nil =>true
  | Oabsf, f1 :: nil => true
  | Oaddf, f1 :: f2 :: nil => true
  | Osubf, f1 :: f2 :: nil => true
  | Omulf, f1 :: f2 :: nil => true
  | Odivf, f1 :: f2 :: nil => true
  | Omuladdf, f1 :: f2 :: f3 :: nil =>true
  | Omulsubf, f1 :: f2 :: f3 :: nil =>  true
  | Osingleoffloat, v1 :: nil =>  true
  | Ointoffloat, f1 :: nil =>  true
  | Ofloatofint, n1 :: nil =>    true
  | Ofloatofintu, n1 :: nil =>   true
  | Ocmp c, _ =>true
  | _,_ => false
end. 
*)


Definition ill_defined (i : instruction) : bool := 
   match i with
  | Iop (Ointconst n) nil _ _ => false
  | Iop (Ofloatconst n) nil _ _ => false
  | _ => true
  end.

Definition anticipable (cfg cfg' : RTL.code) (pc n : node) : bool :=
  let init_map := PTree.fold (fun st p _ => PTree.set p Dunno st) cfg (PTree.empty info) in
  match cfg'!n with
  | Some (Inop s) => false
  | Some (Iop op args res s) => 
       if (ill_defined (Iop op args res s)) then snd (ant_checker cfg (Op op args) pc init_map (count_nodes cfg)) else true
  | Some (Iload chunk addr args dst s) =>  snd (ant_checker cfg (Load chunk addr args) pc init_map (count_nodes cfg))
  | Some (Istore chunk addr args src s) => false
  | Some (Icall sig ros args res s) => false
  | Some (Itailcall sig ros args) => false
  | Some (Ialloc arg res s) => false
  | Some (Icond cond args ifso ifnot) => false
  | Some (Ireturn optarg) => false
  | None => false
  end.
 
(** *Checking the paths through stubs *)

(* ins = is_non_standard *)
Fixpoint crawl_aux (f tf : RTL.function) (base n : node) target (succs : node -> list node) (csr : list node) (count : nat) {struct count} : bool :=
  match count with
  | S m => 
    if peq n target then true 
    else (if is_non_standard csr tf.(fn_code)!n  
         then  
         match succs n with
         | cons s nil =>anticipable f.(fn_code) tf.(fn_code) base n &&  crawl_aux f tf base s target succs csr m
         | _ => false
         end 
         else false) 
  | O => false
  end. 

Definition crawl (f tf : RTL.function) (link : node -> node) csr
                           (n : node)  : bool :=
  let s := successors f in
  let s' := successors tf in
  let succs := s n in
  let targets := List.map link succs in
  let succs' := s' (link n) in
  match succs , succs', targets with
  | nil , nil, nil => true
  | cons i nil, cons a nil, cons b nil => 
               crawl_aux f tf i a b s' csr (count_nodes tf.(fn_code))
  | cons i (cons j nil), cons a (cons a' nil), cons b (cons b' nil) => 
               crawl_aux f tf i a b s' csr (count_nodes tf.(fn_code)) 
               && 
               crawl_aux f tf j a' b' s' csr (count_nodes tf.(fn_code))
  | _, _, _ => false
  end.
(** *Unification of control-flow graphs *)

Definition check_point (f tf : RTL.function) (n : node) (info info' : PMap.t D.t) (link : node -> node) csr : bool :=
  match f.(fn_code)!n, tf.(fn_code)!(link n) with
  | Some i, Some j => unification f tf (info!!n) (info'!!(link n)) i j && crawl f tf link csr n
  | _, _ => false
  end. 

Definition validate_graphs (f tf : RTL.function) (link : node -> node) : bool :=
  let info := analyze f in
  let info' := analyze tf in
  let csr := compute_standard_regs (f.(fn_code)) in

  let b_rec := PTree.fold (fun res n i => check_point f tf n info info' link csr && res) f.(fn_code) true in 
  let b_intro := peq tf.(fn_entrypoint) (link f.(fn_entrypoint)) in
  b_rec && b_intro.

Definition validate (f tf : RTL.function) : bool := validate_graphs f tf (fun x => x).  

Definition Pmax (m n : positive) : positive :=
  if plt m n then n else m. 

Definition compute_nextpc (g : code) : positive :=
  Psucc (PTree.fold (fun max pos _ => Pmax max pos) g xH) . 

Lemma leq:
  forall l n max,
  (fold_left (fun a (p : positive * instruction) => Pmax a (fst p)) l n) = max ->
  n = max \/ Plt n max.
Proof. 
  induction l; intros.
  simpl in H. left; trivial. 
  assert (a :: l = cons a nil ++ l) by trivial. 
  rewrite H0 in H. rewrite fold_left_app in H.
  simpl in H.
  generalize (IHl (Pmax n (fst a)) _ H); intro.
    destruct H1. 
    rewrite <- H1. 
    unfold Pmax. case_eq (plt n (fst a)); intros. 
    right; trivial. 
    left; trivial. 
   unfold Pmax in H1. 
   case_eq (plt n (fst a)); intros.
   rewrite H2 in H1. right. eapply Plt_trans; eauto. 
   rewrite H2 in H1. right; trivial. 
Qed.   

Lemma Plt_prop: forall pc n, ~ Plt n pc -> Plt pc n \/ pc = n.
Proof. 
  intros. 
  case_eq (plt pc n); intros. 
  left; trivial. 
  right. unfold Plt in *|-. clear H0.
  generalize (Zle_or_lt (Zpos n) (Zpos pc)); intro.
  destruct H0. 
  generalize (Zle_lt_or_eq _ _ H0); intro.
  destruct H1. congruence. 
  congruence. 
  congruence.
Qed.  

Lemma compute_nextpc_correct_aux2:
  forall l pc n i,
  In (pc,i) l -> 
  Plt pc (Psucc ((fold_left (fun a p => Pmax a (@fst positive instruction p)) l n))).
Proof. 
  induction l; intros. 
  inversion H. 
  simpl. simpl in H.  destruct H. 
  subst. simpl. 
     assert ((fold_left
        (fun (a : positive) (p : positive * instruction) => Pmax a (fst p)) l
        (Pmax n pc)) = (fold_left
        (fun (a : positive) (p : positive * instruction) => Pmax a (fst p)) l
        (Pmax n pc))) by trivial. 
     generalize (leq l (Pmax n pc) (fold_left
        (fun (a : positive) (p : positive * instruction) => Pmax a (fst p)) l
        (Pmax n pc)) H); intro.
     destruct H0.
          rewrite <- H0. unfold Pmax. case_eq (plt n pc); intros. eapply Plt_succ; eauto. 
                   assert (Plt pc n \/ pc = n). eapply Plt_prop; eauto. 
                      destruct H2. eapply Plt_trans_succ; eauto. subst. eapply Plt_succ; eauto. 
          unfold Pmax in H0. unfold Pmax.  case_eq (plt n pc); intros. 
          rewrite H1 in H0. eapply Plt_trans_succ; eauto.
          rewrite H1 in H0.       
          assert (Plt pc n \/ pc = n). eapply Plt_prop; eauto.  
          destruct H2. 
          generalize (Plt_trans _ _ _ H2 H0); intro. eapply Plt_trans_succ; eauto.
          subst. eapply Plt_trans_succ; eauto. 
  eapply IHl; eauto. 
Qed. 

Lemma compute_nextpc_correct :
  forall g pc, 
  Plt pc (compute_nextpc g) \/ g!pc = None.
Proof. 
  intros. 
  unfold compute_nextpc.
  rewrite PTree.fold_spec .
  case_eq (g!pc); intros. 
  generalize (PTree.elements_correct g _ H); intro.
  generalize (compute_nextpc_correct_aux2 _ _ 1%positive _ H0); intro.
  left. trivial. 
  right; trivial. 
Qed.    

Definition transf_function (f : function) : res function :=
  let tg := E.transformation f in
  let tf :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    tg
    f.(fn_entrypoint)
    (compute_nextpc tg) 
    (compute_nextpc_correct tg) 
  in 
  if validate f tf then OK tf else Error (E.em). 

Definition transf_fundef (fd: fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.

End Valigator. 
