open Mach
open Two_level_repr
open Maps
open PTree
open Camlcoq
open Int32
open BinPos
open LabelSync
open Linear_to_2level
open Datatypes
open Compcert_trigger

(* replace c l1 l2 remplace dans le code c 
   les goto et cond vers l1 par des goto et cond vers l2 *)

let rec replace code lbl lbl' =
  match code with
  | [] -> []
  | (Mach.Mcond (a,b,lab)) as i :: l ->
    (if lab = lbl then Mach.Mcond (a,b,lbl') else i) :: replace l lbl lbl' 
  | (Mach.Mgoto lab) as i :: l -> 
    (if lab = lbl then Mach.Mgoto lbl' else i) :: replace l lbl lbl' 
  | i :: l -> i :: replace l lbl lbl'

(* fresh_label c renvoie un label n apparaissant pas dans c *)

let max p1 p2 =
  let c = BinPos.coq_Pcompare p1 p2 Datatypes.Lt in
  match c with
  | Datatypes.Lt -> p2
  | _ -> p1 

let fresh_label code = 

  let rec fresh_label_aux code =
    match code with 
    | [] -> trans (Int32.of_int 1)
    | Mach.Mlabel lbl :: l -> max lbl (fresh_label_aux l)
    | i :: l -> fresh_label_aux l 
  in
  coq_Psucc (fresh_label_aux code) 

(* stub c l p insere le patch p dans le code en derivant le controle *)

let stub code lbl patch =
  let fl = fresh_label code in
  let code = replace code lbl fl in 
  let patch = (Mach.Mlabel fl) :: patch @ [Mach.Mgoto lbl] in
  let code = code @ patch in
  code 

(* sched_point c k detecte les branchements autour dequels on peu ordonnancer *)

let rec sched_point code keys opt_inst=
 (*  print_newline ();  print_newline ();
  print_code (convert2 code); print_newline ();  print_newline ();*)
  match code with 
  | [] -> []
  | Mach.Mlabel lbl :: l -> (if (not (mem lbl keys)) then ((*print_string "coucou"; *) [(lbl, Some (List.hd l),[])]) else []) @ sched_point l keys None 
  | Mach.Mcond (_,rl,lbl) :: l -> (*print_binpos lbl ;*) (if (not (mem lbl keys)) then [(lbl,opt_inst,(convert1 rl))] else []) @ sched_point l keys None 
  | i :: l -> sched_point l keys (Some i)

let switchable i rl =
  match i with
  | None -> false
  | Some i -> ( 
  let (_,writes) = Block_scheduler.reads_writes i in
  let b = List.fold_left (fun bi -> fun r -> (not (List.mem r rl)) && bi) true writes in
  (* if b then print_string "Un saut peut avoir lieu"; print_mach i; 
  print_newline (); *)
  b) 

let non_branching i =
  match i with
  | Some (Mach.Mgetstack _) -> true
  | Some (Mach.Msetstack _) -> true
  | Some (Mach.Mgetparam _) -> true
  | Some (Mach.Mop _) -> true
  | Some (Mach.Mload _) -> true
  | Some (Mach.Mstore _) -> true
  | Some (Mach.Malloc) -> true
  | _ -> false

let removable code rl lbl i =

let rec removable_aux code rl lbl i b =
  match code with
  | Mach.Mcond (_,rl',lbl') :: l -> (if (lbl = lbl' && rl = rl' && b) then 1 else 0) + removable_aux l rl lbl i false  
  | j :: l -> if (j = i) then removable_aux l rl lbl i true else removable_aux l rl lbl i b 
  | [] -> 0

  in
  match i with
  | Some i -> removable_aux code rl lbl i false = 1
  | None -> false

(* mauvais nom : soit switcher !!! *)
(*
let remove code rl lbl i = 

  let rec remove_aux code rl lbl i b =
  match code with
  | (Mach.Mcond (_,rl',lbl')) as c :: l -> if (lbl = lbl' && rl = rl' && b) then c :: i :: remove_aux l rl lbl i false else 
                                         (if b then i :: c :: remove_aux l rl lbl i false else c :: remove_aux l rl lbl i false)  
  | j :: l -> if (j = i) then remove_aux l rl lbl i true else j :: remove_aux l rl lbl i false (* tres faux *)
  | [] -> []

  in
  match i with
  | Some i -> remove_aux code rl lbl i false 
  | None -> failwith "pop pop pop"
*)

let is_the_cond i rl lbl = 
  match i with
    | Mach.Mcond (_,rl',lbl') -> rl = rl' && lbl = lbl'
    | _ -> false

let rec remove code rl lbl i =
  match code with
    | j :: l when Datatypes.Some j = i && is_the_cond (List.hd l) rl lbl -> (List.hd l) :: j :: remove (List.tl l) rl lbl i    
    | j :: l -> j :: remove l rl lbl i
    | [] -> []

(* attention : ici on fait l hypothese qu un label est unique *)
let rec remove_join code lbl = 
  match code with 
    | (Mach.Mlabel lbl') as i :: l -> if lbl = lbl' then List.hd l :: i :: (List.tl l) else i :: remove_join l lbl
    | i :: l -> i :: remove_join l lbl
    | [] -> [] 

let conv l = List.map (fun r -> Block_scheduler.Reg r) l

(* List.empty permet de savoir si on a affaire a un join ou un exit *)
let modify code keys =
  let points = sched_point code keys None in
  (* if points = [] then print_string "NO POINTS" 
  else print_string "POINTS : "; print_int (List.length (convert1 keys)); 
  print_newline (); *)
  List.fold_left (fun c -> fun (p,i,ls) -> 
    if (not (ls = []) && non_branching i && switchable i (conv ls) && removable c (convert2 ls) p i) 
    then stub (remove c (convert2 ls) p i) p [unop i] 
    else ( 
         if (ls = [] && non_branching i) 
	 then stub (remove_join c p) p [unop i]
	 else c )) code points

let schedule func = 
  if triggered 1 then (
  (* print_string "Welcome to trace shceduling, the code looks like this :";
  print_newline ();
  print_code func; *)
  let func = convert1 func in
  (* print_string "calcul des backedges... "; print_newline ();*)
  let backedges = backedges func in 
  (*print_string "OK"; print_newline ();*)
  (* List.iter (fun i -> print_string " "; print_binpos i) (backedges);*)
  (*print_newline ();*)
  let keys = convert2 (keys func backedges) in
  (*List.iter (fun i -> print_string " "; print_binpos i) (convert1 keys);*)
  let func' = modify func keys in
  (*if (not (func = func')) then print_string "stubs Not trivial";
  print_string "trace shceduling finished, the code looks like this :";
  print_newline ();
  print_code (convert2 func') ;*)
  (* Datatypes.Some (convert2 func') *)
  Block_scheduler.schedule_code (convert2 func'))
  else Datatypes.Some func 
