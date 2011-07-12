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


(** A block semantics and its properties *)

Section RELSEM.

Variable ge: genv.

Inductive exec_instr:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_Mgetstack:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot fr ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetstack ofs ty dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Msetstack:
     forall f sp parent src ofs ty c rs fr m fr',
      set_slot fr ty (Int.signed ofs) (rs src) fr' ->
      exec_instr f sp parent
                 (Msetstack src ofs ty :: c) rs fr m
              E0 c rs fr' m
  | exec_Mgetparam:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot parent ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetparam ofs ty dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Mop:
      forall f sp parent op args res c rs fr m v,
      eval_operation ge sp op rs##args = Some v ->
      exec_instr f sp parent
                 (Mop op args res :: c) rs fr m
              E0 c (rs#res <- v) fr m
  | exec_Mload:
      forall f sp parent chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instr f sp parent
                 (Mload chunk addr args dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Mstore:
      forall f sp parent chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      exec_instr f sp parent
                 (Mstore chunk addr args src :: c) rs fr m
              E0 c rs fr m'
  | exec_Malloc:
      forall f sp parent c rs fr m sz m' blk,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_instr f sp parent
                 (Malloc :: c) rs fr m
              E0 c (rs#Conventions.loc_alloc_result <- 
                                              (Vptr blk Int.zero)) fr m'

with exec_block_end:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_Mlabel:
      forall f sp parent lbl c rs fr m,
      exec_block_end f sp parent
                 (Mlabel lbl :: c) rs fr m
              E0 c rs fr m
  | exec_Mgoto:
      forall f sp parent lbl c rs fr m c',
      find_label lbl f.(fn_code) = Some c' ->
      exec_block_end f sp parent
                 (Mgoto lbl :: c) rs fr m
              E0 c' rs fr m
  | exec_Mcond_true:
      forall f sp parent cond args lbl c rs fr m c',
      eval_condition cond rs##args = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      exec_block_end f sp parent
                 (Mcond cond args lbl :: c) rs fr m
              E0 c' rs fr m
  | exec_Mcond_false:
      forall f sp parent cond args lbl c rs fr m,
      eval_condition cond rs##args = Some false ->
      exec_block_end f sp parent
                 (Mcond cond args lbl :: c) rs fr m
              E0 c rs fr m
  | exec_Mcall:
      forall f sp parent sig ros c rs fr m t f' rs' m',
      find_function ge ros rs = Some f' ->
      exec_function f' fr rs m t rs' m' ->
      exec_block_end f sp parent
                 (Mcall sig ros :: c) rs fr m
               t c rs' fr m'


with exec_block_body:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_refl_bl:
      forall f sp parent c rs fr m,
      exec_block_body f sp parent  c rs fr m  E0 c rs fr m
  | exec_one_bl:
      forall f sp parent c rs fr m t c' rs' fr' m',
      exec_instr f sp parent  c rs fr m  t c' rs' fr' m' ->
      exec_block_body f sp parent  c rs fr m  t c' rs' fr' m'
  | exec_trans_bl:
      forall f sp parent c1 rs1 fr1 m1 t1 c2 rs2 fr2 m2 t2 c3 rs3 fr3 m3 t3,
      exec_block_body f sp parent  c1 rs1 fr1 m1  t1 c2 rs2 fr2 m2 ->
      exec_block_body f sp parent  c2 rs2 fr2 m2  t2 c3 rs3 fr3 m3 ->
      t3 = t1 ** t2 ->
      exec_block_body f sp parent  c1 rs1 fr1 m1  t3 c3 rs3 fr3 m3

with exec_instrs:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
| exec_one_block:
      forall f sp parent c rs fr m t c' rs' fr' m',
      exec_block_body f sp parent c rs fr m t c' rs' fr' m' ->
      exec_instrs f sp parent c rs fr m t c' rs' fr' m' 
| exec_add_block:
      forall f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 c3 rs3 fr3 m3 c4 rs4 fr4 m4
          t1 t2 t3 t4,
      exec_block_body f sp parent c1 rs1 fr1 m1 t1 c2 rs2 fr2 m2 ->
      exec_block_end f sp parent c2 rs2 fr2 m2 t2 c3 rs3 fr3 m3 ->
      exec_instrs f sp parent c3 rs3 fr3 m3 t3 c4 rs4 fr4 m4 ->
      t4 = t1 ** t2 ** t3 ->
      exec_instrs f sp parent c1 rs1 fr1 m1 t4 c4 rs4 fr4 m4

with exec_function_body:
      function -> frame -> val -> val ->
      regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_body:
      forall f parent link ra rs m t rs' m1 m2 stk fr1 fr2 fr3 c,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      set_slot (init_frame f) Tint 0 link fr1 ->
      set_slot fr1 Tint 12 ra fr2 ->
      exec_instrs f (Vptr stk (Int.repr (-f.(fn_framesize)))) parent
                  f.(fn_code) rs fr2 m1
                t (Mreturn :: c) rs' fr3 m2 ->
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

Scheme exec_instr_ind7 := Minimality for exec_instr Sort Prop
  with exec_block_end_ind7 := Minimality for exec_block_end Sort Prop  
  with exec_block_body_ind7 := Minimality for exec_block_body Sort Prop
  with exec_instrs_ind7 := Minimality for exec_instrs Sort Prop
  with exec_function_body_ind7 := Minimality for exec_function_body Sort Prop
  with exec_function_ind7 := Minimality for exec_function Sort Prop.

End RELSEM.
      
Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  exec_function ge f empty_frame (Regmap.init Vundef) m0 t rs m /\
  rs R3 = r.

Lemma exec_function_corr1:
  forall ge f parent rs m t rs' m',
  Machabstr.exec_function ge f parent rs m t rs' m' ->
  exec_function ge f parent rs m t rs' m'. 
Proof.
  intros. 
  apply (exec_function_ind4 ge

(fun f sp parent c rs fr m t c' rs' fr' m' =>
    Machabstr.exec_instr ge f sp parent c rs fr m t c' rs' fr' m' ->
    exec_instr ge f sp parent c rs fr m t c' rs' fr' m' 
    \/ exec_block_end ge f sp parent c rs fr m t c' rs' fr' m')

(fun f sp parent c rs fr m t c' rs' fr' m' =>
    Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m' ->
   exec_block_body ge f sp parent c rs fr m t c' rs' fr' m' \/
   exec_instrs ge f sp parent c rs fr m t c' rs' fr' m')

(fun f parent link ra rs m t rs' m' =>
    Machabstr.exec_function_body ge f parent link ra rs m t rs' m' ->
    exec_function_body ge f parent link ra rs m t rs' m')
   
(fun f fr rs m t rs' m' => Machabstr.exec_function ge f fr rs m t rs' m' -> 
                                    exec_function ge f fr rs m t rs' m' )

);intros;trivial. 

  right; apply exec_Mlabel; auto.
  left; apply exec_Mgetstack;auto.
  left; apply exec_Msetstack;auto.
  left; apply exec_Mgetparam; auto.
  left; apply exec_Mop;auto.
  left; eapply exec_Mload;eauto. 
  left; eapply exec_Mstore;eauto.
  right; eapply exec_Mcall;eauto.
  left; eapply exec_Malloc;eauto.
  right; apply exec_Mgoto;auto.
  right; apply exec_Mcond_true;auto.
  right; apply exec_Mcond_false;auto.

  left. apply exec_refl_bl. 
  
  generalize (H1 H0).
  clear H1. intro HYP.
  inversion H0;subst;destruct HYP.

  inversion H1.

  right. generalize (exec_refl_bl ge f0 sp parent0 (Mlabel lbl :: c') rs'0 fr' m'0). 
  intro LEFT. generalize (exec_refl_bl ge f0 sp parent0 c' rs'0 fr' m'0). 
  intro RIGHT. eapply exec_add_block;eauto. 
  apply exec_one_block; eauto. traceEq. 
     
  left. eapply exec_one_bl;eauto. 
  inversion H3.

  left. eapply exec_one_bl;eauto. 
  inversion H3.
  
  left. eapply exec_one_bl;eauto. 
  inversion H3.

  left. eapply exec_one_bl;eauto. 
  inversion H3. 

  left. eapply exec_one_bl;eauto. 
  inversion H4.

  left. eapply exec_one_bl;eauto. 
  inversion H4.

  left. eapply exec_one_bl;eauto. 
  right. generalize (exec_refl_bl ge f0 sp parent0 (Mcall sig ros  :: c') rs0 fr' m0). 
  intro LEFT. generalize (exec_refl_bl ge f0 sp parent0 c' rs'0 fr' m'0). 
  intro RIGHT. eapply exec_add_block;eauto. apply exec_one_block;eauto. traceEq.

  left. eapply exec_one_bl;eauto. 
  inversion H4.

  inversion H3. 
  right. generalize (exec_refl_bl ge f0 sp parent0 (Mgoto lbl  :: c0) rs'0 fr' m'0). 
  intro LEFT. generalize (exec_refl_bl ge f0 sp parent0 c' rs'0 fr' m'0). 
  intro RIGHT. eapply exec_add_block;eauto. apply exec_one_block;eauto. traceEq. 

  inversion H4.
  right. generalize (exec_refl_bl ge f0 sp parent0 (Mcond cond args lbl  :: c0) rs'0 fr' m'0). 
  intro LEFT. generalize (exec_refl_bl ge f0 sp parent0 c' rs'0 fr' m'0). 
  intro RIGHT. eapply exec_add_block;eauto. apply exec_one_block;eauto. traceEq.

  inversion H3.
  right. generalize (exec_refl_bl ge f0 sp parent0 (Mcond cond args lbl  :: c') rs'0 fr' m'0). 
  intro LEFT. generalize (exec_refl_bl ge f0 sp parent0 c' rs'0 fr' m'0). 
  intro RIGHT. eapply exec_add_block;eauto. apply exec_one_block;eauto. traceEq. 

  generalize (H1 H0). generalize (H3 H2). 
  clear H0 H1 H2 H3. intros. 
  destruct H0; destruct H1.

  (* 1er cas *)
  left. eapply exec_trans_bl; eauto.

  (* 2nd cas *)
  clear H5. subst. induction H1. left. eapply exec_trans_bl;eauto.    
  generalize (IHexec_instrs H0). intro. destruct H5. 
  right. eapply exec_add_block;eauto. eapply exec_one_block;eauto. traceEq. 
  right. eapply exec_add_block;eauto. traceEq. 

  (* 3eme cas *)
  inversion H0; subst. left. eapply exec_trans_bl;eauto. 
  right. generalize (exec_trans_bl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
                           (t1 ** t0) H1 H2 (refl_equal (t1 ** t0))). intro. 
  eapply exec_add_block;eauto. traceEq. 

  (* dernier cas *)
  clear H5. subst. induction H1. induction H0. left. eapply exec_trans_bl;eauto. 
  right. generalize (exec_trans_bl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (t0 ** t1) H1 H0 (refl_equal (t0 ** t1))).
  intro. eapply exec_add_block;eauto. traceEq. 
  generalize (IHexec_instrs H0); intro. destruct H5. 
  right. eapply exec_add_block; eauto. eapply exec_one_block;eauto. traceEq. 
  right. eapply exec_add_block;eauto. traceEq. 
  
  eapply exec_funct_body; eauto.
  2: eapply exec_funct_internal; eauto.
  generalize (H4 H3). intro. 
  destruct H6; eauto. 
  apply exec_one_block;auto.
  eapply exec_funct_external; eauto.
Qed.

Theorem eq1:
  forall p t r,
  Machabstr.exec_program p t r -> exec_program p t r.
Proof.
  intros.
  unfold exec_program in H. destruct H as [b [f [rs [m [A [B [C D]]]]]]].
  exists b; exists f; exists rs; exists m. 
  split; trivial. split; trivial. split; trivial. 
  apply exec_function_corr1; auto.
Qed.


Lemma exec_function_corr2:
  forall ge f fr rs m t rs' m',
  exec_function ge f fr rs m t rs' m' ->
  Machabstr.exec_function ge f fr rs m t rs' m'.
Proof.
  intros ge f fr rs m t rs' m'. intro.
    apply (exec_function_ind7 ge 

(fun f sp parent c rs fr m t c' rs' fr' m' => 
   exec_instr ge f sp parent c rs fr m t c' rs' fr' m' ->
   Machabstr.exec_instr ge f sp parent c rs fr m t c' rs' fr' m') 

(fun f sp parent c rs fr m t c' rs' fr' m' => 
   exec_block_end ge f sp parent c rs fr m t c' rs' fr' m' ->
   Machabstr.exec_instr ge f sp parent c rs fr m t c' rs' fr' m') 

(fun f sp parent c rs fr m t c' rs' fr' m' => 
   exec_block_body ge f sp parent c rs fr m t c' rs' fr' m' ->
   Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m') 

(fun f sp parent c rs fr m t c' rs' fr' m' => 
   exec_instrs ge f sp parent c rs fr m t c' rs' fr' m' ->
   Machabstr.exec_instrs ge f sp parent c rs fr m t c' rs' fr' m')

(fun f parent link ra rs m t rs' m' =>
    exec_function_body ge f parent link ra rs m t rs' m' ->
    Machabstr.exec_function_body ge f parent link ra rs m t rs' m')
   
(fun f fr rs m t rs' m' => exec_function ge f fr rs m t rs' m' -> 
                                    Machabstr.exec_function ge f fr rs m t rs' m' ));intros.

apply Machabstr.exec_Mgetstack; auto. 
apply Machabstr.exec_Msetstack; auto.
apply Machabstr.exec_Mgetparam; auto.
apply Machabstr.exec_Mop;auto.
eapply Machabstr.exec_Mload;eauto.
eapply Machabstr.exec_Mstore;eauto. 
eapply Machabstr.exec_Malloc;eauto. 

eapply Machabstr.exec_Mlabel; eauto. 
apply Machabstr.exec_Mgoto;auto.
apply Machabstr.exec_Mcond_true;auto.
apply Machabstr.exec_Mcond_false; auto.
eapply Machabstr.exec_Mcall;eauto. 

apply Machabstr.exec_refl. 
apply Machabstr.exec_one. apply H1; auto.
eapply Machabstr.exec_trans. eapply H1; eauto. eapply H3; eauto. trivial.

apply H1; auto. 
eapply exec_trans; eauto. eapply exec_trans;eauto. 
generalize (H3 H2). intro. apply exec_one ; auto. 

eapply Machabstr.exec_funct_body;eauto.

eapply Machabstr.exec_funct_internal; eauto.
eapply Machabstr.exec_funct_external; eauto.

trivial.
trivial.
Qed.

Theorem eq2:
  forall p t r,
  exec_program p t r -> Machabstr.exec_program p t r.
Proof.
  intros.
  unfold exec_program in H. destruct H as [b [f [rs [m [A [B [C D ]]]]]]].
  exists b; exists f; exists rs; exists m. 
  split. trivial. split; trivial. split; trivial.  
  apply exec_function_corr2; auto.
Qed.  