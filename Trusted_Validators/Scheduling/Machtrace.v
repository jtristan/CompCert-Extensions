(** Alternate semantics for the Mach intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.
Require Import Machabstr.
 
Module A. 

Section RELSEM.

Variable ge: genv.

Inductive exec_instr:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace -> instruction ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_Mlabel:
      forall f sp parent lbl c rs fr m,
      exec_instr f sp parent
                 (Mlabel lbl :: c) rs fr m
              E0 (Mlabel lbl) c rs fr m
  | exec_Mgetstack:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot fr ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetstack ofs ty dst :: c) rs fr m
              E0 (Mgetstack ofs ty dst) c (rs#dst <- v) fr m
  | exec_Msetstack:
     forall f sp parent src ofs ty c rs fr m fr',
      set_slot fr ty (Int.signed ofs) (rs src) fr' ->
      exec_instr f sp parent
                 (Msetstack src ofs ty :: c) rs fr m
              E0 (Msetstack src ofs ty) c rs fr' m
  | exec_Mgetparam:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot parent ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetparam ofs ty dst :: c) rs fr m
              E0 (Mgetparam ofs ty dst) c (rs#dst <- v) fr m
  | exec_Mop:
      forall f sp parent op args res c rs fr m v,
      eval_operation ge sp op rs##args = Some v ->
      exec_instr f sp parent
                 (Mop op args res :: c) rs fr m
              E0 (Mop op args res) c (rs#res <- v) fr m
  | exec_Mload:
      forall f sp parent chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instr f sp parent
                 (Mload chunk addr args dst :: c) rs fr m
              E0 (Mload chunk addr args dst) c (rs#dst <- v) fr m
  | exec_Mstore:
      forall f sp parent chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      exec_instr f sp parent
                 (Mstore chunk addr args src :: c) rs fr m
              E0 (Mstore chunk addr args src) c rs fr m'
  | exec_Mcall:
      forall f sp parent sig ros c rs fr m t f' rs' m',
      find_function ge ros rs = Some f' ->
      exec_function f' fr rs m t rs' m' ->
      exec_instr f sp parent
                 (Mcall sig ros :: c) rs fr m
               t (Mcall sig ros) c rs' fr m'
  | exec_Malloc:
      forall f sp parent c rs fr m sz m' blk,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_instr f sp parent
                 (Malloc :: c) rs fr m
              E0 (Malloc) c (rs#Conventions.loc_alloc_result <- 
                                              (Vptr blk Int.zero)) fr m'
  | exec_Mgoto:
      forall f sp parent lbl c rs fr m c',
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp parent
                 (Mgoto lbl :: c) rs fr m
              E0 (Mgoto lbl) c' rs fr m
  | exec_Mcond_true:
      forall f sp parent cond args lbl c rs fr m c',
      eval_condition cond rs##args = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp parent
                 (Mcond cond args lbl :: c) rs fr m
              E0 (Mcond cond args lbl) c' rs fr m
  | exec_Mcond_false:
      forall f sp parent cond args lbl c rs fr m,
      eval_condition cond rs##args = Some false ->
      exec_instr f sp parent
                 (Mcond cond args lbl :: c) rs fr m
              E0 (Mcond cond args lbl) c rs fr m

with exec_instrs:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace -> list instruction ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_refl:
      forall f sp parent c rs fr m,
      exec_instrs f sp parent  c rs fr m E0 nil c rs fr m
  | exec_one:
      forall f sp parent c rs fr m t i c' rs' fr' m',
      exec_instr f sp parent  c rs fr m t i c' rs' fr' m' ->
      exec_instrs f sp parent  c rs fr m t (cons i nil) c' rs' fr' m'
  | exec_trans:
      forall f sp parent c1 rs1 fr1 m1 t1 l1 c2 rs2 fr2 m2 t2 l2 c3 rs3 fr3 m3 t3 l3,
      exec_instrs f sp parent  c1 rs1 fr1 m1 t1 l1 c2 rs2 fr2 m2 ->
      exec_instrs f sp parent  c2 rs2 fr2 m2 t2 l2 c3 rs3 fr3 m3 ->
      t3 = t1 ** t2 -> l3 = l1 ++ l2 ->
      exec_instrs f sp parent  c1 rs1 fr1 m1 t3 l3 c3 rs3 fr3 m3

with exec_function_body:
      function -> frame -> val -> val ->
      regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_body:
      forall f parent link ra rs m t l rs' m1 m2 stk fr1 fr2 fr3 c,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      set_slot (init_frame f) Tint 0 link fr1 ->
      set_slot fr1 Tint 12 ra fr2 ->
      exec_instrs f (Vptr stk (Int.repr (-f.(fn_framesize)))) parent
                  f.(fn_code) rs fr2 m1
                t l (Mreturn :: c) rs' fr3 m2 ->
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

Scheme exec_instr_ind4 := Minimality for exec_instr Sort Prop
  with exec_instrs_ind4 := Minimality for exec_instrs Sort Prop
  with exec_function_body_ind4 := Minimality for exec_function_body Sort Prop
  with exec_function_ind4 := Minimality for exec_function Sort Prop.

End RELSEM.

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  exec_function ge f empty_frame (Regmap.init Vundef) m0 t rs m /\
  rs R3 = r.

Lemma eq_sem_1_aux:
  forall ge f parent rs m t rs' m',
  exec_function ge f parent rs m t rs' m' ->
  Machabstr.exec_function ge f parent rs m t rs' m'.
Proof.
  intro. 
  
  generalize (exec_function_ind4 ge 
     (fun f sp parent c rs fr m t (i : instruction) c' rs' fr' m' =>
      Machabstr.exec_instr ge f sp parent c rs fr m t c' rs' fr' m')
     (fun f sp parent c rs fr m t (l : list instruction) c' rs' fr' m' =>
      Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m')
     (fun f parent link ra rs m t rs' m' =>
       Machabstr.exec_function_body ge f parent link ra rs m t rs' m')
     (fun f parent rs m t rs' m' =>
      Machabstr.exec_function ge f parent rs m t rs' m')
     ); intro.

  apply H; clear H; intros. 

  eapply Machabstr.exec_Mlabel; eauto. 
  eapply Machabstr.exec_Mgetstack; eauto. 
  eapply Machabstr.exec_Msetstack; eauto. 
  eapply Machabstr.exec_Mgetparam; eauto. 
  eapply Machabstr.exec_Mop; eauto. 
  eapply Machabstr.exec_Mload; eauto. 
  eapply Machabstr.exec_Mstore; eauto. 
  eapply Machabstr.exec_Mcall; eauto. 
  eapply Machabstr.exec_Malloc; eauto.
  eapply Machabstr.exec_Mgoto; eauto.
  eapply Machabstr.exec_Mcond_true; eauto.
  eapply Machabstr.exec_Mcond_false; eauto.
  eapply Machabstr.exec_refl; eauto. 
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_funct_body; eauto. 
  eapply Machabstr.exec_funct_internal; eauto.    
  eapply Machabstr.exec_funct_external; eauto. 
Qed. 


Lemma eq_sem_2_aux:
  forall ge f parent rs m t rs' m',
  Machabstr.exec_function ge f parent rs m t rs' m' ->
  exec_function ge f parent rs m t rs' m'.
Proof. 
  intro. 

  generalize (Machabstr.exec_function_ind4 ge
  (fun f sp parent c rs fr m t c' rs' fr' m' =>
  exists i, exec_instr ge f sp parent c rs fr m t i c' rs' fr' m')
  (fun f sp parent c rs fr m t c' rs' fr' m' =>
  exists l, exec_instrs ge f sp parent c rs fr m t l c' rs' fr' m')
  (fun f parent link ra rs m t rs' m' =>
  exec_function_body ge f parent link ra rs m t rs' m')
  (fun f parent rs m t rs' m' =>
   exec_function ge f parent rs m t rs' m')
  ); intro.

  apply H; clear H; intros. 
   
  exists (Mlabel lbl). eapply exec_Mlabel; eauto. 
  exists (Mgetstack ofs ty dst). eapply exec_Mgetstack; eauto. 
  exists (Msetstack src ofs ty). eapply exec_Msetstack; eauto. 
  exists (Mgetparam ofs ty dst). eapply exec_Mgetparam; eauto. 
  exists (Mop op args res). eapply exec_Mop; eauto. 
  exists (Mload chunk addr args dst). eapply exec_Mload; eauto. 
  exists (Mstore chunk addr args src). eapply exec_Mstore; eauto. 
  exists (Mcall sig ros). eapply exec_Mcall; eauto. 
  exists (Malloc). eapply exec_Malloc; eauto.
  exists (Mgoto lbl). eapply exec_Mgoto; eauto.
  exists (Mcond cond args lbl). eapply exec_Mcond_true; eauto.
  exists (Mcond cond args lbl). eapply exec_Mcond_false; eauto.
  exists (@nil instruction). eapply exec_refl; eauto. 
  destruct H0. exists (cons x nil). eapply exec_one; eauto. 
  destruct H0. destruct H2. exists (x ++ x0). eapply exec_trans; eauto. 
  destruct H3. eapply exec_funct_body; eauto. 
  eapply exec_funct_internal; eauto. 
  eapply exec_funct_external; eauto. 
Qed. 
 
Theorem eq_sem_1:
  forall p t r,
  exec_program p t r -> Machabstr.exec_program p t r. 
Proof. 
  unfold exec_program. unfold Machabstr.exec_program. 
  intros. destruct H as [b [f [rs [m [A [B [C D]]]]]]].
  exists b; exists f; exists rs; exists m; intuition trivial. 
  eapply eq_sem_1_aux; eauto. 
Qed. 

Theorem eq_sem_2:
  forall p t r,
  Machabstr.exec_program p t r -> exec_program p t r. 
Proof. 
  unfold exec_program. unfold Machabstr.exec_program. 
  intros. destruct H as [b [f [rs [m [A [B [C D]]]]]]].
  exists b; exists f; exists rs; exists m; intuition trivial. 
  eapply eq_sem_2_aux; eauto. 
Qed.  

Lemma exists_trace:
  forall ge f sp parent c rs fr m t c' rs' fr' m',
  Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m' ->
  exists l, exec_instrs ge f sp parent c rs fr m t l c' rs' fr' m'.
Proof. 
  intro. 

  generalize (Machabstr.exec_instrs_ind4 ge
  (fun f sp parent c rs fr m t c' rs' fr' m' =>
  exists i, exec_instr ge f sp parent c rs fr m t i c' rs' fr' m')
  (fun f sp parent c rs fr m t c' rs' fr' m' =>
  exists l, exec_instrs ge f sp parent c rs fr m t l c' rs' fr' m')
  (fun f parent link ra rs m t rs' m' =>
  exec_function_body ge f parent link ra rs m t rs' m')
  (fun f parent rs m t rs' m' =>
   exec_function ge f parent rs m t rs' m')
  ); intro.

  apply H; clear H; intros. 
   
  exists (Mlabel lbl). eapply exec_Mlabel; eauto. 
  exists (Mgetstack ofs ty dst). eapply exec_Mgetstack; eauto. 
  exists (Msetstack src ofs ty). eapply exec_Msetstack; eauto. 
  exists (Mgetparam ofs ty dst). eapply exec_Mgetparam; eauto. 
  exists (Mop op args res). eapply exec_Mop; eauto. 
  exists (Mload chunk addr args dst). eapply exec_Mload; eauto. 
  exists (Mstore chunk addr args src). eapply exec_Mstore; eauto. 
  exists (Mcall sig ros). eapply exec_Mcall; eauto. 
  exists (Malloc). eapply exec_Malloc; eauto.
  exists (Mgoto lbl). eapply exec_Mgoto; eauto.
  exists (Mcond cond args lbl). eapply exec_Mcond_true; eauto.
  exists (Mcond cond args lbl). eapply exec_Mcond_false; eauto.
  exists (@nil instruction). eapply exec_refl; eauto. 
  destruct H0. exists (cons x nil). eapply exec_one; eauto. 
  destruct H0. destruct H2. exists (x ++ x0). eapply exec_trans; eauto. 
  destruct H3. eapply exec_funct_body; eauto. 
  eapply exec_funct_internal; eauto. 
  eapply exec_funct_external; eauto. 
Qed.

Lemma erase_trace:
  forall ge f sp parent c rs fr m t l c' rs' fr' m',
  exec_instrs ge f sp parent c rs fr m t l c' rs' fr' m' ->
  Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m'.
Proof. 
  intro. 
  
  generalize (exec_instrs_ind4 ge 
     (fun f sp parent c rs fr m t (i : instruction) c' rs' fr' m' =>
      Machabstr.exec_instr ge f sp parent c rs fr m t c' rs' fr' m')
     (fun f sp parent c rs fr m t (l : list instruction) c' rs' fr' m' =>
      Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m')
     (fun f parent link ra rs m t rs' m' =>
       Machabstr.exec_function_body ge f parent link ra rs m t rs' m')
     (fun f parent rs m t rs' m' =>
      Machabstr.exec_function ge f parent rs m t rs' m')
     ); intro.

  apply H; clear H; intros. 

  eapply Machabstr.exec_Mlabel; eauto. 
  eapply Machabstr.exec_Mgetstack; eauto. 
  eapply Machabstr.exec_Msetstack; eauto. 
  eapply Machabstr.exec_Mgetparam; eauto. 
  eapply Machabstr.exec_Mop; eauto. 
  eapply Machabstr.exec_Mload; eauto. 
  eapply Machabstr.exec_Mstore; eauto. 
  eapply Machabstr.exec_Mcall; eauto. 
  eapply Machabstr.exec_Malloc; eauto.
  eapply Machabstr.exec_Mgoto; eauto.
  eapply Machabstr.exec_Mcond_true; eauto.
  eapply Machabstr.exec_Mcond_false; eauto.
  eapply Machabstr.exec_refl; eauto. 
  eapply Machabstr.exec_one; eauto. 
  eapply Machabstr.exec_trans; eauto. 
  eapply Machabstr.exec_funct_body; eauto. 
  eapply Machabstr.exec_funct_internal; eauto.    
  eapply Machabstr.exec_funct_external; eauto. 
Qed. 

End A. 
 

(*
Require Import MachToTreeVal. 
Require Import BasicLib. 
                         
Inductive Flow_aux : function -> list label -> label -> code -> list instruction -> Prop :=
  | getstack: forall i t m f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Mgetstack i t m :: c) (Mgetstack i t m :: l')
  | setstack: forall i t m f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Msetstack m i t :: c) (Msetstack m i t :: l')
  | getparam: forall i t m f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Mgetparam i t m :: c) (Mgetparam i t m :: l')
  | op : forall op args res f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Mop op args res :: c) (Mop op args res :: l')  
  | load : forall chunk addr args dst f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Mload chunk addr args dst :: c) (Mload chunk addr args dst :: l')  
  | store : forall chunk addr args src f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Mstore chunk addr args src :: c) (Mstore chunk addr args src :: l')  
  | alloc : forall f keys l_end c l',
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Malloc :: c) (Malloc :: l') 
  | lab : forall lbl f keys l_end c l',
         mem lbl keys = false ->
         Flow_aux f keys l_end c l' ->
         Flow_aux f keys l_end (Mlabel lbl :: c) (Mlabel lbl :: l') 
  | key : forall f keys l_end c,
         Flow_aux f keys l_end (Mlabel l_end :: c) nil
  | cond0: forall cond args lbl f keys l_end c c' l',
	 Flow_aux f keys l_end c l' -> 
         find_label lbl (fn_code f) = Some c' -> 
         Flow_aux f keys l_end c' l' -> 
	 Flow_aux f keys l_end (Mcond cond args lbl  :: c) (Mcond cond args lbl :: l')
  | cond1 : forall cond args lbl f keys l_end c c' l',
         Flow_aux f keys l_end c l' ->
         find_label lbl (fn_code f) = Some c' -> 
         ~ (Flow_aux f keys l_end c' l') -> 
         Flow_aux f keys l_end (Mcond cond args lbl  :: c) (Mcond cond args lbl :: l')
  | cond2 : forall cond args lbl f c c' keys l_end l',
         find_label lbl (fn_code f) = Some c' -> 
         Flow_aux f keys l_end c' l' -> 
         ~ (Flow_aux f keys l_end c l') ->
         Flow_aux f keys l_end (Mcond cond args lbl  :: c) (Mcond cond args lbl :: l')
  | goto : forall lbl f keys l_end c c' l',
         find_label lbl (fn_code f) = Some c' ->
         Flow_aux f keys l_end c' l' ->
         Flow_aux f keys l_end (Mgoto lbl  :: c) (Mgoto lbl :: l').    

Inductive Flow  : function -> list label -> label -> label -> list instruction -> Prop :=
  | Boot: forall f keys l_in l_out trace c lbl,
         find_label lbl (fn_code f) = Some c ->
         Flow_aux f keys l_out c trace ->
         Flow f keys l_in l_out trace.
*)
(** ce qui suit est probablement inutile *)
(*


Fixpoint flow_aux (f : function) (keys : list label) (l_end : label) 
                              (c : code) (trace : list instruction) {struct trace} : bool :=
  match trace, head c with
  | Mlabel lbl :: l', Some i => if mem lbl keys 
                                             then false
                                             else (instruction_eq (Mlabel lbl) i && flow_aux f keys l_end (tail c) l')
  | Mgoto lbl :: l', Some i => match find_label lbl (fn_code f) with 
                                             | Some c' => instruction_eq (Mgoto lbl) i &&  flow_aux f keys l_end c' l'
                                             | None => false
                                             end
  | Mcond cond rl lbl :: l', Some i => instruction_eq (Mcond cond rl lbl) i &&
                                                         (orb (flow_aux f keys l_end (tail c) l') 
                                                         (match find_label lbl (fn_code f) with
                                                         | Some c' => flow_aux f keys l_end c' l' 
                                                         | None => false
                                                         end))
  | instr :: l', Some i => instruction_eq instr i && flow_aux f keys l_end (tail c) l'
  | nil, Some (Mlabel lbl) => peq l_end lbl 
  | _,_ => false
  end.

Definition flow (f : function) (keys : list label) (l_in l_out : label) (trace : list instruction) : bool :=
  match find_label l_in (fn_code f) with
  | Some c => flow_aux f keys l_out c trace 
  | None => false
  end. 

Section DECIDABLE_EQUALITY.

Variable A: Set.
Variable dec_eq: forall (x y: A), {x=y} + {x<>y}.
Variable B: Set.

Lemma dec_eq_true:
  forall (x: A) (ifso ifnot: B),
  (if dec_eq x x then ifso else ifnot) = ifso.
Proof.
  intros. destruct (dec_eq x x). auto. congruence.
Qed.

Lemma dec_eq_false:
  forall (x y: A) (ifso ifnot: B),
  x <> y -> (if dec_eq x y then ifso else ifnot) = ifnot.
Proof.
  intros. destruct (dec_eq x y). congruence. auto.
Qed.

Lemma dec_eq_sym:
  forall (x y: A) (ifso ifnot: B),
  (if dec_eq x y then ifso else ifnot) =
  (if dec_eq y x then ifso else ifnot).
Proof.
  intros. destruct (dec_eq x y). 
  subst y. rewrite dec_eq_true. auto.
  rewrite dec_eq_false; auto.
Qed.

Lemma dec_eq_left:
  forall (x : A),
  dec_eq x x = left (x <> x) (refl_equal x).
Proof. 
  intro. destruct (dec_eq x x). 
  assert (e = refl_equal x). apply proof_irrelevance.
  subst; trivial. 
  congruence. 
Qed. 

Lemma dec_imp_leibniz:
  forall (x y : A), 
  (if dec_eq x y then true else false) = true ->  x = y.
Proof. 
  intros. 
  case_eq (dec_eq x y); intros. 
  trivial. 
  rewrite H0 in H. inversion H. 
Qed. 

End DECIDABLE_EQUALITY.

Hint Resolve dec_eq_true. 
Hint Resolve dec_eq_false.
Hint Resolve dec_eq_left. 
Hint Resolve dec_imp_leibniz.  

Lemma corrcomp_aux:
  forall f keys l_end c l,
  Flow_aux f keys l_end c l -> flow_aux f keys l_end c l = true.
Proof. 
   
  generalize (Flow_aux_ind 
                     (fun f keys l_end c trace =>
                     flow_aux f keys l_end c trace = true)
                     ); intro. 

  apply H; clear H; intros. 

  simpl. rewrite H0. 
  assert (Int.eq_dec i i = left (i <> i) (refl_equal i)). eauto.   
  assert (typ_eq t t = left (t <> t) (refl_equal t)). eauto.   
  assert (mreg_eq m m = left (m <> m) (refl_equal m)). eauto.  
  rewrite H1.  rewrite H2. rewrite H3. simpl. trivial. 

  apply 
  apply 
  apply 
  apply 
  apply 
  apply 
  apply 
  
  simpl. assert (peq l_end l_end = left (l_end <> l_end) (refl_equal l_end)). eauto. 
  rewrite H. simpl; trivial. 
  

  simpl. 
    assert (condition_eq cond cond = left (cond <> cond) (refl_equal cond)). eauto.    
    assert (list_mreg_eq args args = left (args <> args) (refl_equal args)). eauto. 
    assert (ident_eq lbl lbl = left (lbl <> lbl) (refl_equal lbl)). eauto. 
  rewrite H0. rewrite H1. rewrite H2. rewrite H3. simpl. trivial. 
   
  simpl. 
    assert (condition_eq cond cond = left (cond <> cond) (refl_equal cond)). eauto.    
    assert (list_mreg_eq args args = left (args <> args) (refl_equal args)). eauto. 
    assert (ident_eq lbl lbl = left (lbl <> lbl) (refl_equal lbl)). eauto. 
  rewrite H. rewrite H1. rewrite H2. rewrite H3. rewrite H4. simpl. trivial. 

  simpl. 
    assert (ident_eq lbl lbl = left (lbl <> lbl) (refl_equal lbl)). eauto.  
    rewrite H. rewrite H1. rewrite H2. simpl. trivial.   
Qed. 

Lemma compcorr_aux:
  forall f keys l_end l c,
  flow_aux f keys l_end c l = true -> Flow_aux f keys l_end c l.
Proof. 
  induction l; intros. 
  simpl in H. case_eq (head c); intros. rewrite H0 in H. 
  destruct i; inversion H. clear H2.
  assert (l = l_end). 
  subst. 
  assert (c = (Mlabel l_end) :: tail c). apply 
  rewrite H1. apply key.
  rewrite H0 in H. congruence. 

  destruct a.
  unfold flow_aux in H. 
  case_eq (head c); intros. rewrite H0 in H. 
  generalize (essai _ _ H); intro. destruct H1. clear H. 
  generalize (IHl _ H2); intro. clear H2. 
  assert (c = i0 :: tail c). 
  rewrite H2. 
  assert (i0 = Mgetstack i t m). apply 
  rewrite H3.  
  eapply getstack;eauto.


*)  

  




