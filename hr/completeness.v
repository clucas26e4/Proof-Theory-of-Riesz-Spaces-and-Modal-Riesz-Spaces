(** * Implementation of Section 3.5 *)
Require Import RL.QArithSternBrocot.sqrt2.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.hr.term.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.
Require Import RL.hr.semantic.
Require Import RL.hr.interpretation.
Require Import RL.hr.lambda_prop_tools.
Require Import RL.hr.tech_lemmas.
Require Import RL.hr.tactics.
Require Import RL.hr.soundness.

Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** ** First formulation : A = B implies |- 1.A,1.-B and |- 1.B, 1.-A are derivable *)
(** Proof of Lemma 3.28 *)
Lemma completeness_1 : forall A B r, A === B -> HR_M_can (((r, -S B) :: (r, A) :: nil) :: nil)
with completeness_2 : forall A B r, A === B -> HR_M_can (((r, -S A) :: (r, B) :: nil) :: nil).
Proof with try assumption; try reflexivity.
  - intros A B r Heq; destruct Heq.
    + change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
      apply hrr_ID_gen...
      apply hrr_INIT.
    + apply hrr_can with t2 (r :: nil) (r :: nil)...
      apply hrr_ex_seq with (((r, -S t2) :: (r, t1) :: nil) ++ ((r, -S t3) :: (r, t2) :: nil)); [ Permutation_Type_solve | ].
      apply hrr_M; try reflexivity; [ apply (completeness_1 _ _ _ Heq1) | apply (completeness_1 _ _ _ Heq2)].
    + revert r; induction c; (try rename r into r0); intros r.
      * apply completeness_1.
        apply Heq.
      * eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_2.
        simpl; rewrite minus_minus; apply Heq.
      * simpl; change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * simpl.
        change ((r, HR_covar n) :: (r, HR_var n) :: nil) with ((vec (r :: nil) (HR_covar n)) ++ (vec (r :: nil) (HR_var n)) ++ nil).
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        apply hrr_ex_seq with ((vec (r :: nil) (HR_covar n)) ++ (vec (r :: nil) (HR_var n)) ++ nil) ; [Permutation_Type_solve | ].
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        change ((r, HR_zero) :: (r, HR_zero) :: nil) with ((vec (r:: r:: nil) HR_zero) ++ nil).
        apply hrr_Z.
        apply hrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold HR_minus; fold HR_minus.
        apply hrr_ex_seq with ((vec (r :: nil) (evalContext c1 t1 /\S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ nil) ; [ Permutation_Type_solve | ].
        apply hrr_min.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c1 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           apply hrr_W.
           apply IHc1.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c2 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hrr_W.
           eapply hrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext.
        unfold HR_minus; fold HR_minus.
        change ((r, -S evalContext c1 t2 /\S -S evalContext c2 t2)
                  :: (r, evalContext c1 t1 \/S evalContext c2 t1) :: nil) with
            ((vec (r ::nil) (-S evalContext c1 t2 /\S -S evalContext c2 t2)) ++ (vec (r ::nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ nil).
        apply hrr_min.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           apply hrr_W.
           eapply hrr_ex_seq ; [ | apply IHc1].
           Permutation_Type_solve.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c2 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hrr_W.
           eapply hrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext; unfold HR_minus; fold HR_minus.
        change ((r, (-S evalContext c1 t2) -S (evalContext c2 t2))
                  :: (r, evalContext c1 t1 +S evalContext c2 t1) :: nil)
          with ((vec (r :: nil) ((-S evalContext c1 t2) -S (evalContext c2 t2))) ++ (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1)) ++ nil).
        apply hrr_plus.
        apply hrr_ex_seq with (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1) ++
                               vec (r :: nil) (-S evalContext c1 t2) ++
                               vec (r :: nil) (-S evalContext c2 t2) ++ nil) ; [ Permutation_Type_solve | ].
        apply hrr_plus.
        apply hrr_ex_seq with (((r, -S evalContext c1 t2) :: (r, evalContext c1 t1) :: nil) ++ ((r, -S evalContext c2 t2) :: (r, evalContext c2 t1) :: nil)) ; [ Permutation_Type_solve | ].
        apply hrr_M; try reflexivity; [ apply IHc1 | apply IHc2].
      * unfold evalContext; fold evalContext; unfold HR_minus; fold HR_minus.
        change ((r, r0 *S (-S evalContext c t2)) :: (r, r0 *S evalContext c t1) :: nil) with ((vec (r :: nil) (r0 *S (-S evalContext c t2))) ++ (vec (r :: nil) (r0 *S evalContext c t1)) ++ nil).
        apply hrr_mul.
        apply hrr_ex_seq with (vec (r :: nil) (r0 *S evalContext c t1) ++ vec (mul_vec r0 (r :: nil)) (-S evalContext c t2) ++  nil) ; [ Permutation_Type_solve | ].
        apply hrr_mul.
        simpl.
        eapply hrr_ex_seq; [ | apply IHc].
        Permutation_Type_solve.
    + apply (completeness_2 _ _ _ Heq).
    + replace (((r, -S subs t2 n t) :: (r, subs t1 n t) :: nil) :: nil) with (subs_hseq (((r, -S t2) :: (r, t1) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_1; apply Heq.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can. do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_M_can; do_HR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      pattern t at 1; rewrite <-(minus_minus t).
      rewrite<- ? app_assoc; apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      apply hrr_ex_seq with ((vec ((time_pos (minus_pos Hlt) r) ::(time_pos b r) :: nil) (-S t)) ++ (vec ((time_pos a r) :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hrr_ID_gen ; [ | apply hrr_INIT ].
      simpl; destruct a; destruct b; destruct r; unfold minus_pos.
      simpl; nra.
    + pattern t at 2; rewrite <- minus_minus.
      apply hrr_ex_seq with ((vec (r :: nil) (One *S (-S (-S t)))) ++ (vec (r :: nil) (-S t)) ++ nil); [ Permutation_Type_solve | ].
      apply hrr_mul.
      apply hrr_ID_gen; [ destruct r; simpl; nra | apply hrr_INIT].
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      apply hrr_ex_seq with ((vec ((time_pos x r) :: (time_pos y r) :: nil) (-S t)) ++ (vec (time_pos (plus_pos x y) r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hrr_ID_gen; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      simpl; nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; apply hrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t2 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | apply hrr_W ; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | apply hrr_W]].
        pattern t3 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_M_can; do_HR_logical.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W.
        rewrite <- app_assoc.
        apply hrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        rewrite <-app_assoc; apply hrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        rewrite <-app_assoc; apply hrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_INIT.
      * simpl.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
        apply hrr_W.
        apply hrr_INIT.
  - intros A B r Heq; destruct Heq.
    + unfold HR_M_can; HR_to_vec.
      apply hrr_ID_gen...
      apply hrr_INIT.
    + apply hrr_can with t2 (r :: nil) (r :: nil)...
      apply hrr_ex_seq with (((r, -S t1) :: (r, t2) :: nil) ++ ((r, -S t2) :: (r, t3) :: nil)); [ Permutation_Type_solve | ].
      apply hrr_M; try reflexivity; [ apply (completeness_2 _ _ _ Heq1) | apply (completeness_2 _ _ _ Heq2)].
    + revert r;induction c; try (rename r into r0); intros r.
      * apply completeness_2.
        apply Heq.
      * eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_1.
        simpl; rewrite minus_minus; apply Heq.
      * unfold HR_M_can; simpl; HR_to_vec.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * simpl; unfold HR_M_can; HR_to_vec.
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        apply hrr_ex_seq with ((vec (r :: nil) (HR_covar n)) ++ (vec (r :: nil) (HR_var n)) ++ nil) ; [Permutation_Type_solve | ].
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        unfold HR_M_can; do_HR_logical.
        apply hrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold HR_minus; fold HR_minus.
        unfold HR_M_can; do_HR_logical.
        -- apply hrr_W.
           apply IHc1.
        -- eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W; apply IHc2.
      * unfold evalContext; fold evalContext.
        unfold HR_minus; fold HR_minus.
        unfold HR_M_can; do_HR_logical.
        -- apply hrr_W.
           simpl; eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc1.
        -- eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
           eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc2.
      * simpl. unfold HR_M_can; do_HR_logical.
        apply hrr_ex_seq with (((r, -S evalContext c1 t1) :: (r, evalContext c1 t2) :: nil) ++ ((r, -S evalContext c2 t1) :: (r, evalContext c2 t2) :: nil)) ; [ Permutation_Type_solve | ].
        apply hrr_M; try reflexivity; [apply IHc1 | apply IHc2].
      * simpl; unfold HR_M_can; do_HR_logical.
        apply IHc.
    + apply (completeness_1 _ _ _ Heq).
    + replace (((r, -S subs t1 n t) :: (r, subs t2 n t) :: nil) :: nil) with (subs_hseq (((r, -S t1) :: (r, t2) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_2; apply Heq.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      rewrite minus_minus.
      rewrite<- ? app_assoc; apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      rewrite minus_minus.
      apply hrr_ex_seq with ((vec (time_pos a r :: nil) (-S t)) ++ (vec (time_pos (minus_pos Hlt) r :: time_pos b r :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hrr_ID_gen ; [ | apply hrr_INIT ].
      destruct r; destruct a; destruct b; unfold minus_pos.
      simpl; nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen; [ | apply hrr_INIT].
      destruct r; simpl; nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      apply hrr_ex_seq with ((vec (time_pos (plus_pos x y) r :: nil) (-S t)) ++ (vec (time_pos x r :: time_pos y r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hrr_ID_gen; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      simpl; nra.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | apply hrr_W ; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | apply hrr_W]].
        pattern t2 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; apply hrr_W.
        pattern t3 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; apply hrr_W.
        apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) t1) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hrr_ID_gen...
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ex_seq with ((vec (r :: nil) (-S t2)) ++ (vec (r :: nil) t2) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hrr_ID_gen...
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_minus; fold HR_minus.
      unfold HR_M_can; do_HR_logical.
      simpl.
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply hrr_INIT.
Qed.

(** ** Second formulation *)
(** We use the can rule and the M rule to go from a proof |- 1.[G] to a proof of G *)
Lemma HR_sem_seq P : forall G T D,
    HR P (((One, sem_seq T) :: D) :: G) ->
    HR (hr_frag_add_CAN (hr_frag_add_M P)) ((T ++ D) :: G).
Proof.
  intros G T; revert P G; induction T; intros P G D pi.
  - simpl in *.
    apply hrr_Z_can_inv with (One :: nil).
    apply HR_le_frag with P; [ | apply pi].
    apply add_M_le_frag.
  - destruct a as (a , A).
    simpl in *.
    apply hrr_ex_seq with (T ++ (a , A) :: D); [ Permutation_Type_solve | ].
    apply (IHT (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M P))))).
    replace a with (time_pos a One) by (destruct a; unfold One; apply Rpos_eq; simpl; nra).
    apply hrr_ex_seq with ((vec (mul_vec a (One :: nil)) A) ++ (vec (One :: nil) (sem_seq T)) ++ D) ; [ Permutation_Type_solve | ].
    apply hrr_mul_can_inv.
    apply hrr_plus_can_inv.
    apply pi.
Qed.

Lemma HR_sem_hseq P : forall G H,
    H <> nil ->
    HR P (((One, sem_hseq H) :: nil) :: G) ->
    HR (hr_frag_add_CAN (hr_frag_add_M P)) (H ++ G).
Proof with try assumption; try reflexivity.
  intros G H Hnnil; revert P G.
  induction H; [ now auto | ].
  rename a into T.
  intros P G pi.
  destruct H as [ | T2 H ].
  - simpl in *.
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HR_sem_seq...
  - unfold sem_hseq in pi; fold (sem_hseq (T2 :: H)) in pi.
    change ((One, sem_seq T \/S sem_hseq (T2 :: H)) :: nil) with ((vec (One :: nil) (sem_seq T \/S sem_hseq (T2 :: H))) ++ nil) in pi.
    apply hrr_max_can_inv in pi.
    apply hrr_ex_hseq with ((T2 :: H) ++ (T :: G)); [ Permutation_Type_solve | ].
    apply HR_le_frag with (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M P)))))).
    { destruct P; repeat split; Bool.destr_bool. }
    refine (IHlist _ (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M P)))) (T :: G) _) ; [ now auto | ].
    apply hrr_ex_hseq with (T :: ((One , sem_hseq (T2 :: H)) :: nil) :: G) ; [ Permutation_Type_solve | ].
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HR_sem_seq.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply pi.
Qed.

(** Proof of the completeness of the system of HR - hr_complete return a T free proof of G *)
Lemma hr_complete : forall G,
    G <> nil ->
    HR_zero <== sem_hseq G ->
    HR_M_can G.
Proof with try assumption.
  intros G Hnnil Hleq.
  assert (pi := completeness_1 _ _ One Hleq).
  replace G with (G ++ nil) by now rewrite app_nil_r.
  apply (@HR_sem_hseq hr_frag_M_can)...
  change ((One , sem_hseq G) :: nil) with ((vec (One :: nil) (sem_hseq G)) ++ nil).
  apply (@hrr_min_can_inv_r hr_frag_M_can) with HR_zero.
  apply (@hrr_Z_can_inv hr_frag_M_can) with (One :: nil)...
Qed.

(** Proof of Lemma 3.31 *)

(** Proof of Lemma 3.32 *)
Lemma int_lambda_prop :
  forall G,
    hseq_is_atomic G ->
    HR_M G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => (0 < x)%nat) L) *
            (forall n, sum_weight_with_coeff n G (map (fun x => INR x) L) = 0))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with (1%nat :: nil).
    repeat split; try reflexivity.
    + apply Exists_inf_cons_hd.
      lia.
    + intros n.
      simpl; nra.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [Hex Hsum]]].
    split with (0%nat :: L).
    repeat split; auto.
    + simpl; rewrite Hlen; reflexivity.
    + intros n.
      simpl.
      rewrite (Hsum n).
      nra.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply Forall_inf_cons ;[ | apply Forall_inf_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with (((n + n0)%nat) :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        lia.
      * inversion X1; subst; auto.
        apply Exists_inf_cons_hd; lia.
    + intros n1.
      simpl.
      specialize (Hsum n1).
      simpl in Hsum.
      rewrite plus_INR.
      nra.
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply Forall_inf_cons; try assumption.
      apply seq_atomic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (n :: n :: L).
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n1.
      specialize (Hsum n1).
      simpl in *.
      rewrite sum_weight_seq_var_app in Hsum.
      rewrite sum_weight_seq_covar_app in Hsum.
      nra.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [Hex1 Hsum1]]].
    { apply Forall_inf_cons ; [ apply seq_atomic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct n.
    { split with (0%nat :: L1).
      repeat split; auto.
      intros n; specialize (Hsum1 n).
      simpl in *; nra. }
    destruct IHpi2 as [L2 [Hlen2 [Hex2 Hsum2]]].
    { apply Forall_inf_cons ; [ apply seq_atomic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct n0.
    { split with (0%nat :: L2).
      repeat split; auto.
      intros n0; specialize (Hsum2 n0).
      simpl in *; nra. }
    split with (((S n) * (S n0))%nat :: add_nat_list (map (Nat.mul (S n0)) L1) (map (Nat.mul (S n)) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite add_nat_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_inf_cons_hd.
      lia.
    + intros n1; specialize (Hsum1 n1); specialize (Hsum2 n1); simpl in Hsum1, Hsum2.
      simpl.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      rewrite sum_weight_with_coeff_add_nat_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      change (fun m : nat => (m + n0 * m)%nat) with (Nat.mul (S n0)).
      change (fun m : nat => (m + n * m)%nat) with (Nat.mul (S n)).
      change (fun x : nat => INR x) with INR in *.
      rewrite 2 sum_weight_with_coeff_mul_nat_list.
      change (match (n0 + n * S n0)%nat with
              | 0%nat => 1
              | S _ => INR (n0 + n * S n0) + 1
              end)
        with (INR ((S n) * (S n0))).
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)) in Hsum1.
      change (match n0 with
              | 0%nat => 1
              | S _ => INR n0 + 1
              end) with (INR (S n0)) in Hsum2.
      rewrite mult_INR.
      nra.
  - inversion f.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply Forall_inf_cons; try assumption.
      eapply seq_atomic_app_inv_r; eapply seq_atomic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    intros n0; specialize (Hsum n0).
    destruct L; try now inversion Hlen.
    simpl; rewrite ? sum_weight_seq_app.
    case_eq (n0 =? n); intros H.
    + apply Nat.eqb_eq in H; subst.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite sum_weight_seq_covar_vec_covar_eq;rewrite sum_weight_seq_var_vec_var_eq.
      rewrite sum_weight_seq_var_vec_neq; [ | now auto ]; rewrite sum_weight_seq_covar_vec_neq; [ | now auto].
      simpl in Hsum.
      nra.
    + apply Nat.eqb_neq in H.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
      simpl in Hsum.
      nra.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { inversion Ha; subst.
      apply Forall_inf_cons ; [ | apply Forall_inf_cons ]; assumption. }
    destruct L ; [ | destruct L]; try now inversion Hlen.
    split with ((n + n0)%nat :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        lia.
      * inversion X; subst; auto.
        apply Exists_inf_cons_hd; lia.
    + intros n1.
      simpl.
      specialize (Hsum n1).
      simpl in Hsum.
      rewrite plus_INR.
      nra.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct IHpi as [L [Hlen [Hex Hsum]]].
    { inversion Ha; subst.
      apply Forall_inf_cons; try assumption.
      apply seq_atomic_perm with T2; [ Permutation_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    intro n1; specialize (Hsum n1).
    simpl in *.
    rewrite <- (sum_weight_seq_var_perm _ _ _ p); rewrite <- (sum_weight_seq_covar_perm _ _ _ p); apply Hsum.
  - destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply hseq_atomic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_with_coeff_perm_r G H (map (fun x => INR x) L) p) as [L' [Hperm' H']].
    { rewrite map_length.
      apply Hlen. }
    destruct (Permutation_Type_map_inv _ _ (Permutation_Type_sym Hperm')) as [L'' Heq Hperm''].
    split with L''.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      apply Permutation_Type_length in Hperm''.
      lia.
    + apply Exists_inf_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- Heq.
      rewrite <- (H' n); apply Hsum.
  - inversion f.
Qed.
         
Lemma int_lambda_prop_inv :
  forall G,
    hseq_is_atomic G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => (0 < x)%nat) L) *
            (forall n, sum_weight_with_coeff n G (map (fun x => INR x) L) = 0))} ->
    HR_M G.
Proof.
  enough (forall G H,
             hseq_is_atomic G ->
             hseq_is_atomic H ->
             { L &
               prod (length L = length G)
                    ((Exists_inf (fun x => (0 < x)%nat) L) *
                     (forall n, (sum_weight_var n H - sum_weight_covar n H) + sum_weight_with_coeff n G (map (fun x => INR x) L) = 0))} + HR_M H ->
             HR_M (H ++  G)).
  { intros G Hat [L [Hlen [Hex Hsum]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_inf_nil.
    - left.
      split with L.
      repeat split; auto.
      intros n; specialize (Hsum n); simpl in *; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [ [L [Hlen [Hex Hsum]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_inf_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type (map (fun x => INR x) L) (map (fun x => INR x) (r :: La ++ Lb))) as Hperm by (rewrite HeqL ; Permutation_Type_solve).
    destruct (sum_weight_with_coeff_perm_l G _ _ Hperm) as [G' [HpermG Hsum']].
    { rewrite map_length; lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hrr_ex_hseq with (T :: H ++ G') ; [ Permutation_Type_solve | ].
    apply lt_INR in Hp.
    change (INR 0) with 0 in Hp.
    apply (Permutation_Type_Forall_inf HpermG) in HatG.
    inversion HatG; clear x l H1 H2.
    destruct r.
    { exfalso.
      simpl in Hp; nra. }
    apply R_blt_lt in Hp.
    apply hrr_C_copy with r.
    change (copy_seq (S r) T :: H ++ G') with ((copy_seq (S r) T :: H) ++ G').
    apply IHn.
    + rewrite (Permutation_Type_length HpermG) in Heqn; simpl in Heqn.
      apply eq_add_S; apply Heqn.
    + apply X0.
    + apply Forall_inf_cons; try assumption.
      apply copy_seq_atomic; assumption.
    + destruct (Forall_inf_Exists_inf_dec (fun x => x = 0%nat)) with (La ++ Lb).
      { intro x; destruct x; [ left | right]; lia. }
      * right.
        apply atomic_proof_all_eq.
        -- apply copy_seq_atomic; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           change (match r with
                   | 0%nat => 1
                   | S _ => INR r + 1
                   end) with (INR (S r)) in *.
           rewrite (sum_weight_with_coeff_all_0 _ (map (fun x => INR x) (La ++ Lb))) in Hsum'.
           ++ rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app; rewrite sum_weight_seq_var_copy; rewrite sum_weight_seq_covar_copy; simpl.
              rewrite S_INR in Hsum'.
              nra.
           ++ remember (La ++ Lb); clear - f.
              induction l; simpl in *; auto.
              inversion f; subst.
              apply Forall_inf_cons; auto.
      * left.
        split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite app_length; rewrite app_length in Hlen; simpl in *.
           lia.
        -- clear - e.
           induction La.
           ++ induction Lb; try now inversion e.
              inversion e; subst.
              ** apply Exists_inf_cons_hd.
                 lia.
              ** apply Exists_inf_cons_tl.
                 apply IHLb; try assumption.
           ++ simpl in *.
              inversion e; subst.
              ** apply Exists_inf_cons_hd.
                 lia.
              ** apply Exists_inf_cons_tl.
                 now apply IHLa.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app; rewrite sum_weight_seq_var_copy; rewrite sum_weight_seq_covar_copy; simpl.
           change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)) in *.
           rewrite S_INR in Hsum'; nra.
  - eapply hrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hrr_W_gen.
    apply pi.
Qed.

Lemma HR_M_not_complete : { G : _ & HR_zero <== sem_hseq G & (HR_M G -> False) }.
Proof.
  assert (0 <? sqrt 2 = true) as H by (apply R_blt_lt; apply Rlt_sqrt2_0).
  set (sq2 := (existT (fun x => 0 <? x = true) (sqrt 2) H)).
  split with (((One, HR_var 0) :: nil) :: ((sq2, HR_covar 0) :: nil):: nil).
  - apply hr_sound with hr_frag_full.
    apply hrr_T with sq2; try reflexivity.
    apply hrr_S.
    apply hrr_ex_seq with (vec (sq2 :: nil) (HR_covar 0) ++ vec (time_pos sq2 One :: nil) (HR_var 0) ++ nil).
    + unfold seq_mul.
      replace (time_pos sq2 One) with sq2 by (unfold sq2; unfold One; apply Rpos_eq; simpl; nra).
      simpl.
      apply Permutation_Type_swap.
    + apply hrr_ID ; [ | apply hrr_INIT].
      simpl.
      nra.
  - intros pi.
    apply int_lambda_prop in pi as [L [Hlen [Hex Hsum]]].
    + specialize (Hsum 0)%nat.
      simpl in Hlen.
      destruct L; [ | destruct L ; [ | destruct L]]; inversion Hlen.
      simpl in *.
      replace (INR n * (1 + 0 - 0)) with (INR n) in Hsum by nra.
      replace (0 - (sqrt 2 + 0)) with (- sqrt 2) in Hsum by nra.
      replace (INR n0 * - sqrt 2 + 0) with (- INR n0 * sqrt 2) in Hsum by nra.
      assert (INR (n * n) = INR (2 * n0 * n0)).
      { rewrite ? mult_INR.
        change (INR 2) with 2.
        replace 2 with (sqrt 2 * sqrt 2) by (apply sqrt_def; nra).
        nra. }
      apply INR_inj in H0.
      destruct n0; destruct n; try lia.
      { inversion Hex; [ lia | ].
        inversion X; [ lia | ].
        inversion X0. }
      apply sqrt2_not_rational with (S n) (S n0); auto.
      lia.
    + repeat apply Forall_inf_cons; try apply Forall_inf_nil; apply I.
Qed.
      
