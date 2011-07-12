 
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.
Require Import Errors. 

Parameter transformation : function -> code. 
 
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
  let tg := transformation f in
  let tf :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    tg
    f.(fn_entrypoint)
    (compute_nextpc tg) 
    (compute_nextpc_correct tg) 
  in OK tf. 

Definition transf_fundef (fd: fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.

Axiom semantics_preservation:
  forall (p tp : program) (beh: Smallstep.program_behavior), 
  transf_program p = OK tp ->	
  exec_program p beh -> exec_program tp beh.
 
