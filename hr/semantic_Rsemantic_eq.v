(** * Equivalence between equational reasoning of Riesz Spaces and Riesz Spaces restricted to negative normal form *)
Require Import Rpos.
Require Import RL.hr.Rterm.
Require Import RL.hr.term.
Require Import RL.hr.Rsemantic.
Require Import RL.hr.semantic.

Require Import Reals.
Require Import Lra.
Require Import Lia.


Local Open Scope R_scope.

(** ** Definitions *)
(** Function that takes a regular term and returns the NNF of the term *)
Fixpoint NNF (A : Rterm) : term.
  destruct A as [x | | A B |  r A | A B | A B].
  (* A = var x *)
  - now apply (HR_var x).
  (* A = zero *)
  - now apply HR_zero.
  (* A = A + B *)
  - now apply ((NNF A) +S (NNF B)).
  (* A = r * A *)
  - case_eq (0 <? r) ; intros Hr.
    (* 0 < r *)
    + now apply ((existT _ r Hr) *S (NNF A)).
    + case_eq (0 <? -r) ; intros Hr'.
      (* r < 0 *)
      * now apply ((existT _ (-r) Hr') *S (-S (NNF A))).
      (* r = 0 *)
      * now apply HR_zero.
  (* A = A \/ B *)
  - now apply ((NNF A) \/S (NNF B)).
  (* A = A /\ B *)
  - now apply ((NNF A) /\S (NNF B)).
Defined.

(** Function that takes a context and returns the NNF of the context *)
Fixpoint CNNF (C : Rcontext) : context.
  destruct C as [ | A | x | | C1 C2 | C1 C2 | C1 C2 | r C ].
  - now apply HR_hole.
  - now apply (HR_TC (NNF A)).
  - now apply (HR_varC x).
  - now apply HR_zeroC.
  - now apply (HR_minC (CNNF C1) (CNNF C2)).
  - now apply (HR_maxC (CNNF C1) (CNNF C2)).
  - now apply (HR_plusC (CNNF C1) (CNNF C2)).
  - case_eq (0 <? r) ; intros Hr.
    + now apply (HR_mulC (existT _ r Hr) (CNNF C)).
    + case_eq (0 <? -r) ; intros Hr'.
      * now apply (HR_mulC (existT _ (-r) Hr') (minusC (CNNF C))).
      * now apply HR_zeroC.
Defined.

(** The embedding of terms in NNF into regular terms *)
Fixpoint toRterm A :=
  match A with
  | HR_var x =>  R_var x
  | HR_covar x => -R (R_var x)
  | HR_zero => R_zero
  | HR_plus A B => R_plus (toRterm A) (toRterm B)
  | HR_mul (existT _ r _) A => R_mul r (toRterm A)
  | HR_max A B => R_max (toRterm A) (toRterm B)
  | HR_min A B => R_min (toRterm A) (toRterm B)
  end.

(** The embedding of context in NNF into regular context *)
Fixpoint toRcontext C :=
  match C with
  | HR_hole => R_hole
  | HR_cohole => R_mulC (-1) R_hole
  | HR_varC x => R_varC x
  | HR_covarC x => R_mulC (-1) (R_varC x)
  | HR_TC A => R_TC (toRterm A)
  | HR_zeroC => R_zeroC
  | HR_plusC C1 C2 => R_plusC (toRcontext C1) (toRcontext C2)
  | HR_mulC (existT _ r _) C => R_mulC r (toRcontext C)
  | HR_maxC C1 C2 => R_maxC (toRcontext C1) (toRcontext C2)
  | HR_minC C1 C2 => R_minC (toRcontext C1) (toRcontext C2)
  end.

(** * Soundness of the translation, i.e. NNF (toRterm A) = A and toRterm (NNF A) = A  *)
Lemma aux_dep_if_true : forall (b : bool) (t : b = true -> term) (f : b = false -> term) (H : true = b),
       (if b as b' return b = b' -> term
        then t
        else f) eq_refl
       = t (eq_sym H).
Proof.
  destruct H; reflexivity.
Defined.

Lemma aux_dep_if_false : forall (b : bool) (t : b = true -> term) (f : b = false -> term) (H : false = b),
       (if b as b' return b = b' -> term
        then t
        else f) eq_refl
       = f (eq_sym H).
Proof.
  destruct H; reflexivity.
Defined.

Lemma R_eq_minus : forall A, (toRterm (-S A)) =R= (-R (toRterm A)).
Proof with auto with Rsem_solver.
  induction A as [ x | x | | A IHA B IHB | [r Hr] A IHA | A IHA B IHB | A IHA B IHB];simpl; try rewrite IHA; try rewrite IHB...
Qed.

Lemma toRterm_NNF : forall A, toRterm (NNF A) =R= A.
Proof with auto with Rsem_solver.
  induction A; try (simpl; rewrite IHA1 ; rewrite IHA2); try (simpl; rewrite IHA)...
  - case_eq (0 <? r) ; intros Hr; [ | case_eq (0 <? -r) ; intros Hnr]; simpl.
    + rewrite aux_dep_if_true with _ _ _  (eq_sym Hr)...
      simpl; rewrite IHA.
      reflexivity.        
    + rewrite aux_dep_if_false...
      rewrite aux_dep_if_true with _ _ _  (eq_sym Hnr)...
      simpl; rewrite R_eq_minus; rewrite IHA.
      rewrite R_mul_assoc.
      replace (-r * -1) with r by lra...
    + rewrite aux_dep_if_false...
      rewrite aux_dep_if_false...
      replace r with 0.
      * simpl.
        symmetry.
        replace 0 with (0 + 0) by lra.
        rewrite R_mul_distri_coeff.
        replace 0 with (-1 * 0) at 2 by lra.
        rewrite <-(R_mul_assoc)...
      * unfold f in Hr; unfold f in Hnr.
        apply R_blt_nlt in Hr.
        apply R_blt_nlt in Hnr.
        lra.
Qed.

Lemma NNF_toRterm : forall A, NNF (toRterm A) === A.
Proof with auto with MGA_solver.
  induction A; simpl; try (rewrite IHA1 ; rewrite IHA2); try rewrite IHA...
  - rewrite aux_dep_if_false.
    2:{ symmetry; apply R_blt_nlt; lra. }
    erewrite aux_dep_if_true.
    Unshelve.
    2:{ symmetry; apply R_blt_lt; lra. }
    replace (existT (fun r : R => (0 <? r) = true) (- -1) _) with One...
    apply Rpos_eq.
    simpl; lra.
  - destruct r as [r Hr].
    simpl.
    erewrite aux_dep_if_true.
    Unshelve.
    2:{ rewrite Hr... }
    replace ( existT (fun r0 : R => (0 <? r0) = true) r _) with (existT (fun r0 : R => (0 <? r0) = true) r Hr)...
    apply Rpos_eq...
Qed.    

(** ** Semantic to Rsemantic, i.e. proof that A === B -> toRterm A =R= toRterm B *)

Lemma R_eq_term_context : forall C T, (toRterm (evalContext C T)) =R= (evalRcontext (toRcontext C) (toRterm T)).
Proof with auto with Rsem_solver.
  induction C as [ | | B | x | x | | C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2 | [r Hr] C IHC ]; intros A; simpl ; try (constructor; assumption); try rewrite IHC1; try rewrite IHC2; try rewrite IHC...
  - apply R_eq_minus.
Qed.

Lemma R_eq_term_subs : forall A B n, (toRterm (subs A n B)) =R= (Rsubs (toRterm A) n (toRterm B)).
Proof with auto with Rsem_solver.
  induction A as [ x | x | | A1 IHA1 A2 IHA2 | [r Hr] A IHA | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2 ]; intros B; simpl; try (constructor; assumption); intros n; try rewrite IHA1; try rewrite IHA2; try rewrite IHA...
  - case (n =? x); apply R_refl.
  - case (n =? x)...
    + apply R_eq_minus.
Qed.
      
Fixpoint R_subs_gen (A : Rterm) (v : nat -> Rterm) : Rterm :=
  match A with
  | R_zero => R_zero
  | R_var n => v n
  | R_plus A B => R_plus (R_subs_gen A v) (R_subs_gen B v)
  | R_mul r A => R_mul r (R_subs_gen A v)
  | R_max A B => R_max (R_subs_gen A v) (R_subs_gen B v)
  | R_min A B => R_min (R_subs_gen A v) (R_subs_gen B v)
  end.

Lemma R_subs_gen_sub : forall A v n t, R_subs_gen (Rsubs A n t) v = R_subs_gen A (fun x => if n =? x then (R_subs_gen t v) else v x).
Proof.
  induction A ; intros v n' t; simpl; try (specialize (IHA1 v n' t)); try (specialize (IHA2 v n' t)); try (specialize (IHA v n' t)); try (rewrite IHA1); try (rewrite IHA2); try (rewrite IHA); try reflexivity.
  - case (n' =? n); reflexivity.
Qed.

Lemma R_subs_gen_cong : forall A B v, R_eqMALG A B -> R_eqMALG (R_subs_gen A v) (R_subs_gen B v).
Proof.
  intros A B v Heq; revert v; induction Heq ; intros v; try (constructor; assumption).
  - apply R_trans with (R_subs_gen t2 v); [apply IHHeq1 | apply IHHeq2].
  - induction c; simpl; try apply R_refl.
    + apply IHHeq.
    + apply R_trans with (R_min (R_subs_gen (evalRcontext c1 t2) v) (R_subs_gen (evalRcontext c2 t1) v)).
      * apply (R_ctxt (R_minC R_hole (R_TC (R_subs_gen (evalRcontext c2 t1) v)))).
        apply IHc1.
      * apply (R_ctxt (R_minC (R_TC (R_subs_gen (evalRcontext c1 t2) v)) R_hole)).
        apply IHc2.
    + apply R_trans with (R_max (R_subs_gen (evalRcontext c1 t2) v) (R_subs_gen (evalRcontext c2 t1) v)).
      * apply (R_ctxt (R_maxC R_hole (R_TC (R_subs_gen (evalRcontext c2 t1) v)))).
        apply IHc1.
      * apply (R_ctxt (R_maxC (R_TC (R_subs_gen (evalRcontext c1 t2) v)) R_hole)).
        apply IHc2.
    + apply R_trans with (R_plus (R_subs_gen (evalRcontext c1 t2) v) (R_subs_gen (evalRcontext c2 t1) v)).
      * apply (R_ctxt (R_plusC R_hole (R_TC (R_subs_gen (evalRcontext c2 t1) v)))).
        apply IHc1.
      * apply (R_ctxt (R_plusC (R_TC (R_subs_gen (evalRcontext c1 t2) v)) R_hole)).
        apply IHc2.
    + apply (R_ctxt (R_mulC r R_hole)).
      apply IHc.
  - apply R_sym; apply IHHeq.
  - rewrite 2?R_subs_gen_sub.
    apply IHHeq.
Qed.

Lemma R_subs_to_gen : forall A n t, Rsubs A n t = R_subs_gen A (fun x => if n =? x then t else R_var x).
Proof.
  induction A ; intros n' t; simpl; try (rewrite IHA1; rewrite IHA2); try rewrite IHA; try reflexivity.
Qed.
      
Lemma semantic_to_Rsemantic : forall A B, A === B -> (toRterm A) =R= (toRterm B).
Proof with try assumption.
  intros A B Heq.
  induction Heq; simpl; try (constructor; assumption);
    try (destruct x as [x Hx]; destruct y as [y Hy]; simpl; constructor; assumption);
    try (destruct x as [x Hx]; simpl; constructor; assumption).
  - apply R_trans with (toRterm t2)...
  - apply R_trans with (evalRcontext (toRcontext c) (toRterm t1)); [apply R_eq_term_context | ].
    apply R_trans with (evalRcontext (toRcontext c) (toRterm t2)) ; [ | apply R_sym ; apply R_eq_term_context].
    apply R_ctxt...
  - apply R_trans with (Rsubs (toRterm t1) n (toRterm t)); [apply R_eq_term_subs | ].
    apply R_trans with (Rsubs (toRterm t2) n (toRterm t)); [ | apply R_sym; apply R_eq_term_subs ].
    rewrite 2?R_subs_to_gen.
    apply R_subs_gen_cong.
    apply IHHeq.
  - rewrite R_eq_minus; apply R_opp_plus.
  - destruct a as [a Ha]; destruct b as [b Hb]; simpl in *.
    change (a - b) with (a + (- b)).
    rewrite R_mul_distri_coeff.
    rewrite R_eq_minus.  
    replace (- b) with (b * (- 1)) by nra.
    auto with Rsem_solver.
  - destruct r as [x Hx]; simpl; apply R_compa_mul_ax.
    apply Rlt_le.
    revert Hx; unfold R_lt_dec; case_eq (Rlt_dec 0 x); intros; now simpl.
Qed.

    
(** ** Rsemantic to Semantic, i.e. A =R= B -> NNF A === NNF B *)
    
Lemma eq_term_subs : forall A B n, (NNF (Rsubs A n B)) === (subs (NNF A) n (NNF B)).
Proof with auto with MGA_solver.
  induction A as [ x | | A1 IHA1 A2 IHA2 | r A IHA | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2 ]; intros B; try (simpl; constructor; assumption); intros n; try (simpl; rewrite IHA1 ; rewrite IHA2; auto with MGA_solver; fail)...
  - simpl; case (n =? x)...
  - unfold Rsubs; fold Rsubs.
    case_eq (0 <? r) ; intros Hr; [ | case_eq (0 <? -r) ; intros Hnr]; simpl.
    + rewrite aux_dep_if_true with _ _ _ (eq_sym Hr).
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hr).
      rewrite IHA.
      simpl...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnr).
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnr).
      intros; simpl; rewrite IHA.
      rewrite eq_subs_minus...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
Qed.
      
Fixpoint subs_gen (A : term) (v : nat -> term) : term :=
  match A with
  | HR_zero => HR_zero
  | HR_var n => v n
  | HR_covar n => -S (v n)
  | HR_plus A B => HR_plus (subs_gen A v) (subs_gen B v)
  | HR_mul r A => HR_mul r (subs_gen A v)
  | HR_max A B => HR_max (subs_gen A v) (subs_gen B v)
  | HR_min A B => HR_min (subs_gen A v) (subs_gen B v)
  end.

Lemma eq_subs_gen_minus : forall A v, subs_gen (-S A) v === -S (subs_gen A v).
Proof with auto with MGA_solver.
  induction A ; intros v; try (simpl; constructor; assumption); simpl; try (rewrite IHA1; rewrite IHA2; auto with MGA_solver; fail)...
Qed.

Lemma subs_gen_sub : forall A v n t, subs_gen (subs A n t) v === subs_gen A (fun x => if n =? x then (subs_gen t v) else v x).
Proof.
  induction A ; intros v n' t; simpl; try (specialize (IHA1 v n' t)); try (specialize (IHA2 v n' t)); try (specialize (IHA v n' t)); try (rewrite IHA1); try (rewrite IHA2); try (rewrite IHA); try reflexivity.
  - case (n' =? n); reflexivity.
  - case (n' =? n); [ rewrite eq_subs_gen_minus | ]; reflexivity.
Qed.

Lemma subs_gen_cong : forall A B v, A === B -> (subs_gen A v) === (subs_gen B v).
Proof with auto with MGA_solver.
  intros A B v Heq; revert v; induction Heq ; intros v; simpl; try rewrite IHHeq; try (constructor; now assumption).
  - transitivity (subs_gen t2 v); [ apply IHHeq1 | apply IHHeq2].
  - induction c; simpl; try rewrite IHc1; try rewrite IHc2; try rewrite IHc...
    rewrite 2?eq_subs_gen_minus.
    rewrite IHHeq...
  - rewrite 2?subs_gen_sub.
    apply IHHeq.
  - rewrite eq_subs_gen_minus...
  - rewrite eq_subs_gen_minus...
Qed.

Lemma subs_to_gen : forall A n t, subs A n t = subs_gen A (fun x => if n =? x then t else HR_var x).
Proof.
  induction A ; intros n' t; simpl; try (rewrite IHA1; rewrite IHA2); try rewrite IHA; try reflexivity.
  case (n' =? n); reflexivity.
Qed.

Lemma Rsemantic_to_semantic : forall A B, A =R= B -> (NNF A) === (NNF B).
Proof with auto with MGA_solver.
  intros A B Heq.
  induction Heq; try (simpl; now auto with MGA_solver).
  - transitivity (NNF t2)...
  - induction c; try (simpl; rewrite IHc1; rewrite IHc2; auto with MGA_solver);try (simpl; rewrite IHc1; auto with MGA_solver)...
    case_eq (0 <? r) ; intros Hr ; [ | case_eq (0 <? (-r)) ; intros Hnr]; simpl.
    + rewrite aux_dep_if_true with _ _ _ (eq_sym Hr)...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hr)...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnr)... 
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnr)...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...      
  - rewrite 2?eq_term_subs.
    rewrite 2!(subs_to_gen).
    apply subs_gen_cong...
  - simpl.
    rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt; lra].
    erewrite aux_dep_if_true.
    Unshelve.
    2: symmetry; apply R_blt_lt; lra.
    replace (existT (fun r : R => (0 <? r) = true) (- -1) _) with One.
    2:{ apply Rpos_eq;simpl; lra. }
    rewrite mul_1...
  - simpl.
    erewrite aux_dep_if_true.
    Unshelve.
    2: symmetry; apply R_blt_lt; lra.
    replace (existT (fun r : R => (0 <? r) = true) 1 _) with One...
    apply Rpos_eq;simpl; lra.
  -  case_eq (0 <? x) ; intros Hx ; [ | case_eq (0 <? -x) ; intros Hnx]; (case_eq (0 <? y) ; intros Hy; [ | case_eq (0 <?  - y) ; intros Hny]); simpl.
     + rewrite aux_dep_if_true with _ _ _ (eq_sym Hx).
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hy).
       erewrite aux_dep_if_true.
       Unshelve.
       2:apply R_blt_lt in Hx; apply R_blt_lt in Hy; symmetry; apply R_blt_lt...
       2:{ apply Rmult_lt_0_compat... }
       rewrite mul_assoc.
       apply mul_left.
       apply Rpos_eq...
     + rewrite aux_dep_if_true with _ _ _ (eq_sym Hx).
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hny).
       rewrite aux_dep_if_false.
       2:{ symmetry.
           apply R_blt_lt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt.
           nra. }
       erewrite aux_dep_if_true.
       Unshelve.
       2:{ symmetry.
           apply R_blt_lt in Hx; apply R_blt_lt in Hny; apply R_blt_lt.
           nra. }
       rewrite mul_assoc.
       apply mul_left.
       apply Rpos_eq; simpl; nra.
     + rewrite aux_dep_if_true with _ _ _ (eq_sym Hx).
       rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hx; apply R_blt_nlt in Hny; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx).
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hy).
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hx; apply R_blt_lt in Hy; apply R_blt_nlt; nra].
       erewrite aux_dep_if_true.
       Unshelve.
       2: symmetry; apply R_blt_lt in Hnx; apply R_blt_lt in Hy; apply R_blt_lt; nra.
       rewrite mul_minus; rewrite mul_assoc; apply mul_left; apply Rpos_eq; simpl; nra.
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx)...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hny).
       erewrite aux_dep_if_true.
       Unshelve.
       2: symmetry; apply R_blt_lt in Hnx; apply R_blt_lt in Hny; apply R_blt_lt; nra.
       rewrite <-(mul_minus).
       rewrite minus_minus.
       rewrite mul_assoc; apply mul_left; apply Rpos_eq; simpl; nra.
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx).
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hnx; apply R_blt_nlt in Hy; apply R_blt_nlt in Hny; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hnx; apply R_blt_nlt in Hy; apply R_blt_nlt in Hny; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_lt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_lt in Hy; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra]...
  - case_eq (0 <? x) ; intros Hx; [ | case_eq (0 <? - x) ; intros Hnx]; simpl.
    + rewrite aux_dep_if_true with _ _ _ (eq_sym Hx)...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hx)...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hx)...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx)...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx)...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx)...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
  - case_eq (0 <? x + y); [intros Hxy | intros Hxy; (case_eq (0 <? -(x + y)) ; [intros Hnxy | intros Hnxy])];  (case_eq (0 <? x); [intros Hx | intros Hx; (case_eq (0 <? -x) ; [intros Hnx | intros Hnx])]);  (case_eq (0 <? y); [intros Hy | intros Hy; (case_eq (0 <? -y) ; [intros Hny | intros Hny])]);
      try (exfalso;
           try (apply R_blt_lt in Hx);
           try (apply R_blt_nlt in Hx);
           try (apply R_blt_lt in Hnx);
           try (apply R_blt_nlt in Hnx);
           try (apply R_blt_lt in Hy);
           try (apply R_blt_nlt in Hy);
           try (apply R_blt_lt in Hny);
           try (apply R_blt_nlt in Hny);
           try (apply R_blt_lt in Hxy);
           try (apply R_blt_nlt in Hxy);
           try (apply R_blt_lt in Hnxy);
           try (apply R_blt_nlt in Hnyx);
           nra); unfold NNF; fold (NNF t);
        try (rewrite aux_dep_if_true with _ _ _ (eq_sym Hxy));
        try (rewrite aux_dep_if_false with _ _ _ (eq_sym Hxy));
        try (rewrite aux_dep_if_true with _ _ _ (eq_sym Hnxy));
        try (rewrite aux_dep_if_false with _ _ _ (eq_sym Hnxy));
        try (rewrite aux_dep_if_true with _ _ _ (eq_sym Hx));
        try (rewrite aux_dep_if_false with _ _ _ (eq_sym Hx));
        try (rewrite aux_dep_if_true with _ _ _ (eq_sym Hnx));
        try (rewrite aux_dep_if_false with _ _ _ (eq_sym Hnx));
        try (rewrite aux_dep_if_true with _ _ _ (eq_sym Hy));
        try (rewrite aux_dep_if_false with _ _ _ (eq_sym Hy));
        try (rewrite aux_dep_if_true with _ _ _ (eq_sym Hny));
        try (rewrite aux_dep_if_false with _ _ _ (eq_sym Hny))...
    + rewrite <-mul_distri_coeff.
      apply mul_left; apply Rpos_eq; simpl; nra.
    + assert (projT1 (existT (fun r : R => (0 <? r) = true) (- y) (eq_sym (eq_sym Hny))) < projT1 (existT (fun r : R => (0 <? r) = true) x (eq_sym (eq_sym Hx)))) as Hlt by (simpl; apply R_blt_lt in Hxy; apply R_blt_lt in Hx; apply R_blt_lt in Hny; nra).
      rewrite (minus_ax _ _ _ Hlt).
      apply mul_left; apply Rpos_eq; unfold minus_pos; simpl;  nra.
    + assert (y = 0) as Heq by (apply R_blt_nlt in Hy; apply R_blt_nlt in Hny; lra).
      rewrite neutral_plus.
      apply mul_left; apply Rpos_eq; simpl; nra.
    + assert (projT1 (existT (fun r : R => (0 <? r) = true) (- x) (eq_sym (eq_sym Hnx))) < projT1 (existT (fun r : R => (0 <? r) = true) y (eq_sym (eq_sym Hy)))) as Hlt by (simpl; apply R_blt_lt in Hxy; apply R_blt_lt in Hy; apply R_blt_lt in Hnx; nra).
      rewrite commu_plus.
      rewrite (minus_ax _ _ _ Hlt).
      apply mul_left; apply Rpos_eq; unfold minus_pos; simpl;  nra.
    + assert (x = 0) as Heq by (apply R_blt_nlt in Hx; apply R_blt_nlt in Hnx; lra).
      rewrite commu_plus; rewrite neutral_plus.
      apply mul_left; apply Rpos_eq; simpl; nra.
    + assert (projT1 (existT (fun r : R => (0 <? r) = true) x (eq_sym (eq_sym Hx))) < projT1 (existT (fun r : R => (0 <? r) = true) (-y) (eq_sym (eq_sym Hny)))) as Hlt by (simpl; apply R_blt_lt in Hnxy; apply R_blt_lt in Hny; apply R_blt_lt in Hx; nra).
      rewrite commu_plus; rewrite <-(minus_minus (NNF t)) at 3.
      rewrite (minus_ax _ _ _ Hlt).
      apply mul_left; apply Rpos_eq; simpl; nra.
    + assert (projT1 (existT (fun r : R => (0 <? r) = true) y (eq_sym (eq_sym Hy))) < projT1 (existT (fun r : R => (0 <? r) = true) (-x) (eq_sym (eq_sym Hnx)))) as Hlt by (simpl; apply R_blt_lt in Hnxy; apply R_blt_lt in Hy; apply R_blt_lt in Hnx; nra).
      rewrite <-(minus_minus (NNF t)) at 3.
      rewrite (minus_ax _ _ _ Hlt).
      apply mul_left; apply Rpos_eq; simpl; nra.
    + rewrite <-mul_distri_coeff.
      apply mul_left; apply Rpos_eq; simpl; nra.
    + assert (y = 0) as Heq by (apply R_blt_nlt in Hy; apply R_blt_nlt in Hny; lra).
      rewrite neutral_plus.
      apply mul_left; apply Rpos_eq; simpl; nra.
    + assert (x = 0) as Heq by (apply R_blt_nlt in Hx; apply R_blt_nlt in Hnx; lra).
      rewrite commu_plus; rewrite neutral_plus.
      apply mul_left; apply Rpos_eq; simpl; nra.
    + replace (existT (fun r : R => (0 <? r) = true) (- y) (eq_sym (eq_sym Hny))) with (existT (fun r : R => (0 <? r) = true) x (eq_sym (eq_sym Hx))) by (apply R_blt_nlt in Hxy; apply R_blt_nlt in Hnxy;apply Rpos_eq;simpl; lra).
      rewrite opp_plus...
    + rewrite commu_plus.
      replace (existT (fun r : R => (0 <? r) = true) (- x) (eq_sym (eq_sym Hnx))) with (existT (fun r : R => (0 <? r) = true) y (eq_sym (eq_sym Hy))) by (apply R_blt_nlt in Hxy; apply R_blt_nlt in Hnxy;apply Rpos_eq;simpl; lra).
      rewrite opp_plus...
    + exfalso; apply R_blt_nlt in Hnxy; apply R_blt_lt in Hnx; apply R_blt_lt in Hny; nra.
    + exfalso; apply R_blt_nlt in Hnxy; apply R_blt_lt in Hnx; apply R_blt_nlt in Hny; apply R_blt_nlt in Hy; nra.
    + exfalso; apply R_blt_nlt in Hnxy; apply R_blt_lt in Hny; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; nra.
  - case_eq (0 <? r); [intros Hr | intros Hr]; unfold NNF; fold (NNF t).
    + rewrite aux_dep_if_true with _ _ _ (eq_sym Hr)...
    + rewrite aux_dep_if_false with _ _ _ (eq_sym Hr).
      rewrite aux_dep_if_false ; [ | apply R_blt_nlt in Hr; symmetry; apply R_blt_nlt; nra]...
Qed.
      
       
       
           
   
  
