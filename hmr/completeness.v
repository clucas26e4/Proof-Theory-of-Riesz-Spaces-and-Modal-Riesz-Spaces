(** * Implementation of Section 4.4 *)
Require Import RL.QArithSternBrocot.sqrt2.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.semantic.
Require Import RL.hmr.interpretation.
Require Import RL.hmr.tactics.
Require Import RL.hmr.tech_lemmas.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.soundness.

Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** ** First formulation : A = B implies |- 1.A,1.-B and |- 1.B, 1.-A are derivable *)
(** Proof of Lemma 4.20 *)
Lemma completeness_1 : forall A B r, A === B -> HMR_M_can (((r, -S B) :: (r, A) :: nil) :: nil)
with completeness_2 : forall A B r, A === B -> HMR_M_can (((r, -S A) :: (r, B) :: nil) :: nil).
Proof with try assumption; try reflexivity.
  - intros A B r Heq; destruct Heq.
    + change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + apply hmrr_can with t2 (r :: nil) (r :: nil)...
      apply hmrr_ex_seq with (((r, -S t2) :: (r, t1) :: nil) ++ ((r, -S t3) :: (r, t2) :: nil)); [ Permutation_Type_solve | ].
      apply hmrr_M; try reflexivity; [ apply (completeness_1 _ _ _ Heq1) | apply (completeness_1 _ _ _ Heq2)].
    + revert r; induction c; (try rename r into r0); intros r.
      * apply completeness_1.
        apply Heq.
      * eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_2.
        simpl; rewrite minus_minus; apply Heq.
      * simpl; change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * simpl.
        change ((r, HMR_covar n) :: (r, HMR_var n) :: nil) with ((vec (r :: nil) (HMR_covar n)) ++ (vec (r :: nil) (HMR_var n)) ++ nil).
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        apply hmrr_ex_seq with ((vec (r :: nil) (HMR_covar n)) ++ (vec (r :: nil) (HMR_var n)) ++ nil) ; [Permutation_Type_solve | ].
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        change ((r, HMR_zero) :: (r, HMR_zero) :: nil) with ((vec (r:: r:: nil) HMR_zero) ++ nil).
        apply hmrr_Z.
        apply hmrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        apply hmrr_ex_seq with ((vec (r :: nil) (evalContext c1 t1 /\S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ nil) ; [ Permutation_Type_solve | ].
        apply hmrr_min.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c1 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           apply hmrr_W.
           apply IHc1.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c2 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hmrr_W.
           eapply hmrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        change ((r, -S evalContext c1 t2 /\S -S evalContext c2 t2)
                  :: (r, evalContext c1 t1 \/S evalContext c2 t1) :: nil) with
            ((vec (r ::nil) (-S evalContext c1 t2 /\S -S evalContext c2 t2)) ++ (vec (r ::nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ nil).
        apply hmrr_min.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           apply hmrr_W.
           eapply hmrr_ex_seq ; [ | apply IHc1].
           Permutation_Type_solve.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c2 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hmrr_W.
           eapply hmrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext; unfold HMR_minus; fold HMR_minus.
        change ((r, (-S evalContext c1 t2) -S (evalContext c2 t2))
                  :: (r, evalContext c1 t1 +S evalContext c2 t1) :: nil)
          with ((vec (r :: nil) ((-S evalContext c1 t2) -S (evalContext c2 t2))) ++ (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1)) ++ nil).
        apply hmrr_plus.
        apply hmrr_ex_seq with (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1) ++
                               vec (r :: nil) (-S evalContext c1 t2) ++
                               vec (r :: nil) (-S evalContext c2 t2) ++ nil) ; [ Permutation_Type_solve | ].
        apply hmrr_plus.
        apply hmrr_ex_seq with (((r, -S evalContext c1 t2) :: (r, evalContext c1 t1) :: nil) ++ ((r, -S evalContext c2 t2) :: (r, evalContext c2 t1) :: nil)) ; [ Permutation_Type_solve | ].
        apply hmrr_M; try reflexivity; [ apply IHc1 | apply IHc2].
      * unfold evalContext; fold evalContext; unfold HMR_minus; fold HMR_minus.
        change ((r, r0 *S (-S evalContext c t2)) :: (r, r0 *S evalContext c t1) :: nil) with ((vec (r :: nil) (r0 *S (-S evalContext c t2))) ++ (vec (r :: nil) (r0 *S evalContext c t1)) ++ nil).
        apply hmrr_mul.
        apply hmrr_ex_seq with (vec (r :: nil) (r0 *S evalContext c t1) ++ vec (mul_vec r0 (r :: nil)) (-S evalContext c t2) ++  nil) ; [ Permutation_Type_solve | ].
        apply hmrr_mul.
        simpl.
        eapply hmrr_ex_seq; [ | apply IHc].
        Permutation_Type_solve.
      * simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * eapply hmrr_ex_seq;  [ apply Permutation_Type_swap | ].
        simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * simpl in *.
        change ((r, <S> (-S evalContext c t2)) :: (r, <S> evalContext c t1) :: nil) with (seq_diamond ((r , (-S evalContext c t2)) :: (r , evalContext c t1) :: nil)).
        apply hmrr_diamond_no_one.
        apply IHc.
    + apply (completeness_2 _ _ _ Heq).
    + replace (((r, -S subs t2 n t) :: (r, subs t1 n t) :: nil) :: nil) with (subs_hseq (((r, -S t2) :: (r, t1) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_1; apply Heq.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can. do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_M_can; do_HMR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      pattern t at 1; rewrite <-(minus_minus t).
      rewrite<- ? app_assoc; apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      apply hmrr_ex_seq with ((vec ((time_pos (minus_pos Hlt) r) ::(time_pos b r) :: nil) (-S t)) ++ (vec ((time_pos a r) :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_ID_gen ; [ | apply hmrr_INIT ].
      simpl; destruct a; destruct b; destruct r; unfold minus_pos.
      simpl; nra.
    + pattern t at 2; rewrite <- minus_minus.
      apply hmrr_ex_seq with ((vec (r :: nil) (One *S (-S (-S t)))) ++ (vec (r :: nil) (-S t)) ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_mul.
      apply hmrr_ID_gen; [ destruct r; simpl; nra | apply hmrr_INIT].
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      apply hmrr_ex_seq with ((vec ((time_pos x r) :: (time_pos y r) :: nil) (-S t)) ++ (vec (time_pos (plus_pos x y) r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; apply hmrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t2 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | apply hmrr_W ; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | apply hmrr_W]].
        pattern t3 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W.
        rewrite <- app_assoc.
        apply hmrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        rewrite <-app_assoc; apply hmrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        rewrite <-app_assoc; apply hmrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_INIT.
      * simpl.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
        apply hmrr_W.
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      change (vec (r :: nil) (<S> (-S t1)) ++ vec (r :: nil) (<S> (-S t2)) ++ vec (r :: nil) (<S> (t1 +S t2)) ++ nil)
        with
          (seq_diamond (vec (r :: nil) (-S t1) ++ vec (r :: nil) (-S t2) ++ vec (r :: nil) (t1 +S t2) ++ nil)).
      apply hmrr_diamond_no_one.
      do_HMR_logical.
      apply hmrr_ex_seq with (vec (r :: nil) (-S t2) ++ vec (r :: nil) t2 ++ vec (r :: nil) (-S t1) ++ vec (r :: nil) t1 ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      change (vec (mul_vec r0 (r :: nil)) (<S> (-S t)) ++ vec (r :: nil) (<S> (r0 *S t)) ++ nil)
        with
          (seq_diamond (vec (mul_vec r0 (r :: nil)) (-S t) ++ vec (r :: nil) (r0 *S t) ++ nil)).
      apply hmrr_diamond_no_one.
      do_HMR_logical.
      pattern t at 1.
      rewrite <- minus_minus.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * change (<S> HMR_one) with (-S (<S> HMR_coone)).
        apply hmrr_ID_gen; try reflexivity.
        apply hmrr_INIT.
      * rewrite app_nil_r.
        change (vec (r :: nil) HMR_one ++ vec (r :: nil) (<S> HMR_coone))
          with
            (vec nil HMR_coone ++ vec (r :: nil) HMR_one ++ seq_diamond (vec (r :: nil) (HMR_coone))).
        apply hmrr_diamond.
        { destruct r as [r Hr]; simpl; apply R_blt_lt in Hr; nra. }
        change HMR_one with (-S HMR_coone).
        rewrite app_nil_l; rewrite <- (app_nil_r (vec (r :: nil) HMR_coone)).
        apply hmrr_ID_gen; try reflexivity.
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical ; try apply hmrr_INIT.
      change (vec (r :: nil) (<S> pos t) ++ nil) with (seq_diamond (vec (r :: nil) (pos t) ++ nil)).
      apply hmrr_diamond_no_one.
      do_HMR_logical; simpl.
      eapply hmrr_ex_hseq;  [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical ; try apply hmrr_INIT.
      change (vec (r :: nil) HMR_one ++ nil)
        with (vec nil HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
      apply hmrr_one; try apply hmrr_INIT.
      destruct r as [r Hr]; simpl.
      apply R_blt_lt in Hr; nra.
  - intros A B r Heq; destruct Heq.
    + unfold HMR_M_can; HMR_to_vec.
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + apply hmrr_can with t2 (r :: nil) (r :: nil)...
      apply hmrr_ex_seq with (((r, -S t1) :: (r, t2) :: nil) ++ ((r, -S t2) :: (r, t3) :: nil)); [ Permutation_Type_solve | ].
      apply hmrr_M; try reflexivity; [ apply (completeness_2 _ _ _ Heq1) | apply (completeness_2 _ _ _ Heq2)].
    + revert r;induction c; try (rename r into r0); intros r.
      * apply completeness_2.
        apply Heq.
      * eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_1.
        simpl; rewrite minus_minus; apply Heq.
      * unfold HMR_M_can; simpl; HMR_to_vec.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * simpl; unfold HMR_M_can; HMR_to_vec.
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        apply hmrr_ex_seq with ((vec (r :: nil) (HMR_covar n)) ++ (vec (r :: nil) (HMR_var n)) ++ nil) ; [Permutation_Type_solve | ].
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        unfold HMR_M_can; do_HMR_logical.
        apply hmrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        unfold HMR_M_can; do_HMR_logical.
        -- apply hmrr_W.
           apply IHc1.
        -- eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W; apply IHc2.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        unfold HMR_M_can; do_HMR_logical.
        -- apply hmrr_W.
           simpl; eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc1.
        -- eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
           eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc2.
      * simpl. unfold HMR_M_can; do_HMR_logical.
        apply hmrr_ex_seq with (((r, -S evalContext c1 t1) :: (r, evalContext c1 t2) :: nil) ++ ((r, -S evalContext c2 t1) :: (r, evalContext c2 t2) :: nil)) ; [ Permutation_Type_solve | ].
        apply hmrr_M; try reflexivity; [apply IHc1 | apply IHc2].
      * simpl; unfold HMR_M_can; do_HMR_logical.
        apply IHc.
      * simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * eapply hmrr_ex_seq;  [ apply Permutation_Type_swap | ].
        simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * simpl in *.
        change ((r, <S> (-S evalContext c t1)) :: (r, <S> evalContext c t2) :: nil) with (seq_diamond ((r , (-S evalContext c t1)) :: (r , evalContext c t2) :: nil)).
        apply hmrr_diamond_no_one.
        apply IHc.
    + apply (completeness_1 _ _ _ Heq).
    + replace (((r, -S subs t1 n t) :: (r, subs t2 n t) :: nil) :: nil) with (subs_hseq (((r, -S t1) :: (r, t2) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_2; apply Heq.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      rewrite minus_minus.
      rewrite<- ? app_assoc; apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      rewrite minus_minus.
      apply hmrr_ex_seq with ((vec (time_pos a r :: nil) (-S t)) ++ (vec (time_pos (minus_pos Hlt) r :: time_pos b r :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_ID_gen ; [ | apply hmrr_INIT ].
      destruct r; destruct a; destruct b; unfold minus_pos.
      simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen; [ | apply hmrr_INIT].
      destruct r; simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      apply hmrr_ex_seq with ((vec (time_pos (plus_pos x y) r :: nil) (-S t)) ++ (vec (time_pos x r :: time_pos y r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | apply hmrr_W ; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | apply hmrr_W]].
        pattern t2 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; apply hmrr_W.
        pattern t3 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; apply hmrr_W.
        apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) t1) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hmrr_ID_gen...
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ex_seq with ((vec (r :: nil) (-S t2)) ++ (vec (r :: nil) t2) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hmrr_ID_gen...
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      simpl.
      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with (seq_diamond (vec (r :: nil) ((-S t1) -S t2) ++ vec (r :: nil) t1 ++ vec (r :: nil) t2 ++ nil)) ; [ Permutation_Type_solve | ].
      apply hmrr_diamond_no_one.
      apply hmrr_plus.
      apply hmrr_ex_seq with (vec (r :: nil) (-S t2) ++ vec (r :: nil) t2 ++ vec (r :: nil) (-S t1) ++ vec (r :: nil) t1 ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with (seq_diamond (vec (r :: nil) (r0 *S (-S t)) ++ vec (mul_vec r0 (r :: nil)) t ++ nil)); [Permutation_Type_solve | ].
      apply hmrr_diamond_no_one; apply hmrr_mul.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_W.
      change (vec (r :: nil) (<S> HMR_coone) ++ vec (r :: nil) (<S> HMR_one) ++ nil)
        with (seq_diamond (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil)).
      apply hmrr_diamond_no_one.
      apply hmrr_one; simpl; try nra.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      simpl.
      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W; apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      simpl.
      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_INIT.
Qed.

(** ** Second formulation *)
(** We use the can rule and the M rule to go from a proof |- 1.G to a proof of G *)
Lemma HMR_sem_seq P : forall G T D,
    HMR P (((One, sem_seq T) :: D) :: G) ->
    HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((T ++ D) :: G).
Proof.
  intros G T; revert P G; induction T; intros P G D pi.
  - simpl in *.
    apply hmrr_Z_can_inv with (One :: nil).
    apply HMR_le_frag with P; [ | apply pi].
    apply add_M_le_frag.
  - destruct a as (a , A).
    simpl in *.
    apply hmrr_ex_seq with (T ++ (a , A) :: D); [ Permutation_Type_solve | ].
    apply (IHT (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M P))))).
    replace a with (time_pos a One) by (destruct a; unfold One; apply Rpos_eq; simpl; nra).
    apply hmrr_ex_seq with ((vec (mul_vec a (One :: nil)) A) ++ (vec (One :: nil) (sem_seq T)) ++ D) ; [ Permutation_Type_solve | ].
    apply hmrr_mul_can_inv.
    apply hmrr_plus_can_inv.
    apply pi.
Qed.

Lemma HMR_sem_hseq P : forall G H,
    H <> nil ->
    HMR P (((One, sem_hseq H) :: nil) :: G) ->
    HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) (H ++ G).
Proof with try assumption; try reflexivity.
  intros G H Hnnil; revert P G.
  induction H; [ now auto | ].
  rename a into T.
  intros P G pi.
  destruct H as [ | T2 H ].
  - simpl in *.
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HMR_sem_seq...
  - unfold sem_hseq in pi; fold (sem_hseq (T2 :: H)) in pi.
    change ((One, sem_seq T \/S sem_hseq (T2 :: H)) :: nil) with ((vec (One :: nil) (sem_seq T \/S sem_hseq (T2 :: H))) ++ nil) in pi.
    apply hmrr_max_can_inv in pi.
    apply hmrr_ex_hseq with ((T2 :: H) ++ (T :: G)); [ Permutation_Type_solve | ].
    apply HMR_le_frag with (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M P)))))).
    { destruct P; repeat split; Bool.destr_bool. }
    refine (IHlist _ (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M P)))) (T :: G) _) ; [ now auto | ].
    apply hmrr_ex_hseq with (T :: ((One , sem_hseq (T2 :: H)) :: nil) :: G) ; [ Permutation_Type_solve | ].
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HMR_sem_seq.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply pi.
Qed.

(** Proof of the completeness of the system of HMR - hmr_complete return a T free proof of G *)
Lemma hmr_complete : forall G,
    G <> nil ->
    HMR_zero <== sem_hseq G ->
    HMR_M_can G.
Proof with try assumption.
  intros G Hnnil Hleq.
  assert (pi := completeness_1 _ _ One Hleq).
  replace G with (G ++ nil) by now rewrite app_nil_r.
  apply (@HMR_sem_hseq hmr_frag_M_can)...
  change ((One , sem_hseq G) :: nil) with ((vec (One :: nil) (sem_hseq G)) ++ nil).
  apply (@hmrr_min_can_inv_r hmr_frag_M_can) with HMR_zero.
  apply (@hmrr_Z_can_inv hmr_frag_M_can) with (One :: nil)...
Qed.

(** Proof of Lemma 4.23 *)

(** Proof of Lemma 4.24 *)
Lemma int_lambda_prop :
  forall G,
    hseq_is_basic G ->
    HMR_M G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> 0%nat) L) *
            (forall n, sum_weight_with_coeff n G (map nat_oRpos L) = 0) *
            (0 <= sum_weight_with_coeff_one G (map nat_oRpos L)) *
            (HMR_M ((concat_with_coeff_copy (only_diamond_hseq G) L) :: nil)))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with (1%nat :: nil).
    repeat split; try reflexivity.
    + apply Exists_inf_cons_hd.
      intros H; inversion H.
    + intros n.
      simpl; nra.
    + simpl; nra.
    + apply hmrr_INIT.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with (0%nat :: L).
    repeat split; auto.
    + simpl; rewrite Hlen; reflexivity.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons ;[ | apply Forall_inf_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with ((n + n0)%nat :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        destruct n; destruct n0; intros H; inversion H.
        apply H0; reflexivity.
      * inversion X1; subst; auto.
        apply Exists_inf_cons_hd.
        destruct n0 ; [ exfalso; apply H0; reflexivity | ].
        destruct n; intros H; inversion H.
    + intros n1.
      specialize (Hsum n1).
      simpl; simpl in Hsum.
      destruct n; destruct n0; simpl in *; try rewrite Nat.add_0_r; try nra.
      rewrite Nat.add_succ_r.
      rewrite <- S_INR.
      replace ((S(S (n + n0)))%nat) with (((S n) + (S n0))%nat) by lia.
      rewrite plus_INR.
      simpl; nra.
    + simpl; simpl in Hone.
      destruct n; destruct n0; simpl in *; try rewrite Nat.add_0_r; try nra.
      rewrite Nat.add_succ_r.
      rewrite <- S_INR.
      replace ((S(S (n + n0)))%nat) with (((S n) + (S n0))%nat) by lia.
      rewrite plus_INR.
      simpl; nra.
    + simpl in Hind |- *.
      rewrite ? copy_seq_plus; simpl.
      eapply hmrr_ex_seq ; [ | apply Hind].
      Permutation_Type_solve.      
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      apply seq_basic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (n :: n :: L).
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n1.
      specialize (Hsum n1).
      simpl; simpl in Hsum.
      destruct n;
        unfold nat_oRpos in *; fold nat_oRpos in *;
          unfold INRpos in *; unfold projT1 in *; rewrite ? S_INR in *;
            try rewrite sum_weight_seq_var_app in Hsum;
            try rewrite sum_weight_seq_covar_app in Hsum;
            try nra.
    + simpl; simpl in Hone.
      destruct n;
        unfold nat_oRpos in *; fold nat_oRpos in *;
          unfold INRpos in *; unfold projT1 in *; rewrite ? S_INR in *;
            try rewrite sum_weight_seq_one_app in Hone;
            try rewrite sum_weight_seq_coone_app in Hone;
            try nra.
    + simpl in Hind |- *.
      rewrite only_diamond_seq_app in Hind.
      eapply hmrr_ex_seq ; [ | apply Hind].
      rewrite app_assoc.
      apply Permutation_Type_app ; [ | reflexivity].
      apply copy_seq_app.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [[[Hex1 Hsum1] Hone1] Hind1]]].
    { apply Forall_inf_cons ; [ apply seq_basic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct n.
    { split with (0%nat :: L1).
      repeat split; auto. }
    destruct IHpi2 as [L2 [Hlen2 [[[Hex2 Hsum2] Hone2] Hind2]]].
    { apply Forall_inf_cons ; [ apply seq_basic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct n0.
    { split with (0%nat :: L2).
      repeat split; auto. }
    split with ((S n * S n0)%nat :: add_nat_list (map (Nat.mul (S n0)) L1) (map (Nat.mul (S n)) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite add_nat_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_inf_cons_hd.
      intros H; inversion H.
    + intros n'; specialize (Hsum1 n'); specialize (Hsum2 n'); simpl in Hsum1, Hsum2.
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)) in Hsum1.
      change (match n0 with
              | 0%nat => 1
              | S _ => INR n0 + 1
              end) with (INR (S n0)) in Hsum2.
      simpl.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      rewrite sum_weight_with_coeff_add_nat_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      change (match (n0 + n * S n0)%nat with
              | 0%nat => 1
              | S _ => INR (n0 + n * S n0) + 1
              end) with (INR ((S n) * (S n0))).
      change (fun m : nat => (m + n0 * m)%nat) with (Nat.mul (S n0)).
      change (fun m : nat => (m + n * m)%nat) with (Nat.mul (S n)).
      rewrite mult_INR.
      rewrite 2 sum_weight_with_coeff_mul_nat_list.
      nra.
    + simpl in Hone1, Hone2.
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)) in Hone1.
      change (match n0 with
              | 0%nat => 1
              | S _ => INR n0 + 1
              end) with (INR (S n0)) in Hone2.
      simpl.
      rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app.
      rewrite sum_weight_with_coeff_one_add_nat_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      change (match (n0 + n * S n0)%nat with
              | 0%nat => 1
              | S _ => INR (n0 + n * S n0) + 1
              end) with (INR ((S n) * (S n0))).
      change (fun m : nat => (m + n0 * m)%nat) with (Nat.mul (S n0)).
      change (fun m : nat => (m + n * m)%nat) with (Nat.mul (S n)).
      rewrite mult_INR.
      rewrite 2 sum_weight_with_coeff_one_mul_nat_list.
      assert (0 < INR (S n)) by apply INR_S_n_pos.
      assert (0 < INR (S n0)) by apply INR_S_n_pos.
      nra.
    + simpl only_diamond_hseq; simpl concat_with_coeff_copy in *.
      change (copy_seq (n0 + n * S n0) (only_diamond_seq (T1 ++ T2)) ++ only_diamond_seq (T1 ++ T2))
             with (copy_seq ((S n) * (S n0)) (only_diamond_seq (T1 ++ T2))).
      rewrite only_diamond_seq_app.
      eapply hmrr_ex_seq ; [ apply Permutation_Type_app ; [ symmetry; apply copy_seq_app | reflexivity] | ].
      rewrite <- (copy_seq_twice (only_diamond_seq T2)).
      replace ((S n * S n0)%nat) with ((S n0 * S n)%nat) by lia.
      rewrite <- copy_seq_twice.
      apply hmrr_ex_seq with ((concat_with_coeff_copy (only_diamond_hseq G) (add_nat_list (map (Nat.mul (S n0)) L1) (map (Nat.mul (S n)) L2))) ++ (copy_seq (S n0) (copy_seq (S n) (only_diamond_seq T1)) ++ copy_seq (S n) (copy_seq (S n0) (only_diamond_seq T2)))) ; [ Permutation_Type_solve | ].
      eapply hmrr_ex_seq ; [ apply Permutation_Type_app ; [ symmetry; apply concat_with_coeff_copy_add_nat_list_perm | reflexivity] | ].
      { rewrite ? map_length; simpl in *; lia. }
      eapply hmrr_ex_seq ; [ apply Permutation_Type_app ; [ apply Permutation_Type_app; symmetry; apply concat_with_coeff_copy_mul_nat_list | reflexivity]  | ].
      apply hmrr_ex_seq with (copy_seq (S n) (copy_seq (S n0) (only_diamond_seq T2) ++ (concat_with_coeff_copy (only_diamond_hseq G) L2)) ++ copy_seq (S n0) (copy_seq (S n) (only_diamond_seq T1) ++ (concat_with_coeff_copy (only_diamond_hseq G) L1))).
      { etransitivity ; [ apply Permutation_Type_app ; apply copy_seq_app  | ].
        Permutation_Type_solve. }
      change hmr_frag_M with (hmr_frag_add_M hmr_frag_M).
      apply hmrr_M; [ reflexivity | | ];
        apply hmrr_C_copy_inv; assumption.
  - inversion f.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n0; specialize (Hsum n0).
      destruct L; try now inversion Hlen.
      simpl; rewrite ? sum_weight_seq_app.
      case_eq (n0 =? n); intros H.
      * apply Nat.eqb_eq in H; subst.
        rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
        rewrite sum_weight_seq_covar_vec_covar_eq;rewrite sum_weight_seq_var_vec_var_eq.
        rewrite sum_weight_seq_var_vec_neq; [ | now auto ]; rewrite sum_weight_seq_covar_vec_neq; [ | now auto].
        destruct n1; simpl in *; nra.
      * apply Nat.eqb_neq in H.
        rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
        rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
        destruct n1; simpl in *; nra.
    + destruct L; try now inversion Hlen.
      simpl; rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite ? sum_weight_seq_one_vec_neq; try now auto.
      rewrite ? sum_weight_seq_coone_vec_neq; try now auto.
      destruct n0; simpl in *; nra.
    + destruct L; try now inversion Hlen.
      simpl.
      rewrite ? only_diamond_seq_app.
      rewrite only_diamond_seq_vec_var; rewrite only_diamond_seq_vec_covar.
      apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
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
      specialize (Hsum n1).
      destruct n; destruct n0; simpl in *; try rewrite Nat.add_0_r; try nra.
      rewrite Nat.add_succ_r.
      rewrite <- S_INR.
      replace ((S(S (n + n0)))%nat) with (((S n) + (S n0))%nat) by lia.
      rewrite plus_INR.
      simpl; nra.
    + destruct n; destruct n0; simpl in *; try rewrite Nat.add_0_r; try nra.
      rewrite Nat.add_succ_r.
      rewrite <- S_INR.
      replace ((S(S (n + n0)))%nat) with (((S n) + (S n0))%nat) by lia.
      rewrite plus_INR.
      simpl; nra.
    + simpl in Hind |- *.
      rewrite copy_seq_plus.
      rewrite <- app_assoc; apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n0; specialize (Hsum n0).
      destruct L; try now inversion Hlen.
      simpl; rewrite ? sum_weight_seq_app.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
      destruct n; simpl in *; nra.
    + destruct L; try now inversion Hlen.
      simpl; rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite ? sum_weight_seq_one_vec_one_eq; rewrite ? sum_weight_seq_coone_vec_coone_eq.
      rewrite ? sum_weight_seq_one_vec_neq; try now auto.
      rewrite ? sum_weight_seq_coone_vec_neq; try now auto.
      destruct n; simpl in *; try nra.
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)) in *.
      assert (INR_pos := INR_S_n_pos n).
      nra.
    + destruct L; try now inversion Hlen.
      simpl.
      rewrite ? only_diamond_seq_app.
      rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_vec_coone.
      apply hmrr_ex_seq with (copy_seq n (vec s HMR_coone) ++ copy_seq n (vec r HMR_one) ++ copy_seq n (only_diamond_seq T) ++ concat_with_coeff_copy (only_diamond_hseq G) L).
      { rewrite 2 app_assoc; apply Permutation_Type_app; [ | reflexivity].
        rewrite <- app_assoc.
        etransitivity ; [ | symmetry; apply copy_seq_app ].
        apply Permutation_Type_app ; [ reflexivity | ].
        symmetry; apply copy_seq_app. }
      simpl in Hind.
      remember (copy_seq n (only_diamond_seq T)) as D.
      clear - r0 Hind.
      induction n; try apply Hind.
      eapply hmrr_ex_seq ; [ | apply hmrr_one ; [ apply r0 | apply IHn]].
      simpl; Permutation_Type_solve.
  - split with (1%nat :: nil).
    repeat split; auto.
    + intros n.
      simpl.
      rewrite ? sum_weight_seq_var_app; rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_var_vec_neq; try now auto.
      rewrite ? sum_weight_seq_covar_vec_neq; try now auto.
      rewrite sum_weight_seq_var_seq_diamond; rewrite sum_weight_seq_covar_seq_diamond.
      nra.
    + simpl.
      rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite sum_weight_seq_one_vec_one_eq; rewrite sum_weight_seq_coone_vec_coone_eq.
      rewrite ? sum_weight_seq_one_vec_neq; try now auto.
      rewrite ? sum_weight_seq_coone_vec_neq; try now auto.
      rewrite sum_weight_seq_one_seq_diamond; rewrite sum_weight_seq_coone_seq_diamond.
      nra.
    + simpl.
      rewrite app_nil_r; rewrite ? only_diamond_seq_app.
      rewrite only_diamond_seq_vec_coone; rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_only_diamond.
      apply pi.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_inf_cons; try assumption.
      apply seq_basic_perm with T2; [ Permutation_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    + intro n1; specialize (Hsum n1).
      simpl in *.
      rewrite <- (sum_weight_seq_var_perm _ _ _ p); rewrite <- (sum_weight_seq_covar_perm _ _ _ p); apply Hsum.
    + simpl in *.
      rewrite <- (sum_weight_seq_one_perm _ _ p); rewrite <- (sum_weight_seq_coone_perm _ _ p); apply Hone.
    + simpl in Hind |- *.
      eapply hmrr_ex_seq; [ | apply Hind].
      apply Permutation_Type_app ; [ | reflexivity ].
      apply copy_seq_perm; apply only_diamond_seq_perm.
      apply p.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply hseq_basic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_with_coeff_perm_r_int G H L p) as [L' [Hperm' [[Hsum' Hone'] Hpc]]].
    { apply Hlen. }
    split with L'.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      lia.
    + apply Exists_inf_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- (Hsum' n); apply Hsum.
    + rewrite <- Hone'; apply Hone.
    + eapply hmrr_ex_seq ; [ apply Hpc | ].
      apply Hind.
  - inversion f.
Qed.

Lemma int_lambda_prop_inv :
  forall G,
    hseq_is_basic G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> 0%nat) L) *
            (forall n, sum_weight_with_coeff n G (map nat_oRpos L) = 0) *
            (0 <= sum_weight_with_coeff_one G (map nat_oRpos L)) *
            (HMR_M ((concat_with_coeff_copy (only_diamond_hseq G) L) :: nil)))} ->
    HMR_M G.
Proof.
  enough (forall G H,
             hseq_is_basic G ->
             hseq_is_basic H ->
             { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> 0%nat) L) *
            (forall n, (sum_weight_var n H - sum_weight_covar n H) + sum_weight_with_coeff n G (map nat_oRpos L) = 0) *
            (0 <= (sum_weight_one H - sum_weight_coone H) + sum_weight_with_coeff_one G (map nat_oRpos L)) *
            (HMR_M ((flat_map only_diamond_seq H ++ concat_with_coeff_copy (only_diamond_hseq G) L) :: nil)))} + HMR_M H ->
             HMR_M (H ++  G)).
  { intros G Hat [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_inf_nil.
    - left.
      split with L.
      repeat split; auto.
      + intros n; specialize (Hsum n); simpl in *; nra.
      + simpl in *; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [ [L [Hlen [[[Hex Hsum] Hone] Hind]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_inf_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type L (r :: La ++ Lb)) as Hperm by (rewrite HeqL ; Permutation_Type_solve).
    destruct (sum_weight_with_coeff_perm_l_int G _ _ Hperm) as [G' [HpermG [[Hsum' Hone'] Hpc]]].
    { lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hmrr_ex_hseq with (T :: H ++ G') ; [ Permutation_Type_solve | ].
    apply (Permutation_Type_Forall_inf HpermG) in HatG.
    inversion HatG; clear x l H1 H2.
    destruct r.
    { exfalso.
      apply Hp; reflexivity. }
    apply hmrr_C_copy with r.
    change (copy_seq (S r) T :: H ++ G') with ((copy_seq (S r) T :: H) ++ G').
    apply IHn.
    + rewrite (Permutation_Type_length HpermG) in Heqn; simpl in Heqn.
      apply eq_add_S; apply Heqn.
    + apply X0.
    + apply Forall_inf_cons; try assumption.
      apply copy_seq_basic; apply X.
    + destruct (Forall_inf_Exists_inf_dec (fun x => x = 0%nat)) with (La ++ Lb).
      { intro x; destruct x; [ left | right]; lia. }
      * right.
        apply basic_proof_all_eq.
        -- apply copy_seq_basic; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           change (match r with
                   | 0%nat => 1
                   | S _ => INR r + 1
                   end) with (INR (S r)) in *.
           rewrite (sum_weight_with_coeff_all_0 _ (map nat_oRpos (La ++ Lb))) in Hsum'.
           ++ rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app; rewrite sum_weight_seq_var_copy; rewrite sum_weight_seq_covar_copy; simpl.
              rewrite S_INR in Hsum'.
              nra.
           ++ remember (La ++ Lb); clear - f.
              induction l; simpl in *; auto.
              inversion f; subst.
              apply Forall_inf_cons; auto.
        -- simpl in *.
           change (match r with
                   | 0%nat => 1
                   | S _ => INR r + 1
                   end) with (INR (S r)) in *.
           rewrite (sum_weight_with_coeff_one_all_0 _ (map nat_oRpos (La ++ Lb))) in Hone'.
           ++ rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app; rewrite sum_weight_seq_one_copy; rewrite sum_weight_seq_coone_copy; simpl.
              rewrite S_INR in Hone'.
              nra.
           ++ remember (La ++ Lb); clear - f.
              induction l; simpl in *; auto.
              inversion f; subst.
              apply Forall_inf_cons; auto.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           simpl.
           etransitivity ; [ | apply Permutation_Type_app_swap].
           apply Permutation_Type_app ; [ reflexivity | ].
           rewrite concat_with_coeff_copy_only_diamond.
           apply only_diamond_seq_perm.
           simpl in Hpc.
           rewrite (concat_with_coeff_copy_all_0  G') in Hpc; [rewrite app_nil_r in Hpc; apply Hpc | ].
           apply f.
      * left.
        split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite app_length; rewrite app_length in Hlen; simpl in *.
           lia.
        -- apply e.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app; rewrite sum_weight_seq_var_copy; rewrite sum_weight_seq_covar_copy; simpl.
           change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)) in *.
           rewrite S_INR in Hsum'; nra.
        -- simpl in *.
           rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app; rewrite sum_weight_seq_one_copy; rewrite sum_weight_seq_coone_copy; simpl.
           change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)) in *.
           rewrite S_INR in Hone'; nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind ].
           simpl in Hpc |- *.
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           etransitivity ; [ | apply Permutation_Type_app_swap].
           rewrite app_assoc.
           apply Permutation_Type_app; [ | reflexivity].
           rewrite ? concat_with_coeff_copy_only_diamond.
           rewrite <- only_diamond_seq_app; apply only_diamond_seq_perm.
           Permutation_Type_solve.
  - eapply hmrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hmrr_W_gen.
    apply pi.
Qed.


Lemma HMR_M_not_complete : { G : _ & HMR_zero <== sem_hseq G & (HMR_M G -> False) }.
Proof.
  assert (0 <? sqrt 2 = true) as H by (apply R_blt_lt; apply Rlt_sqrt2_0).
  set (sq2 := (existT (fun x => 0 <? x = true) (sqrt 2) H)).
  split with (((One, HMR_var 0) :: nil) :: ((sq2, HMR_covar 0) :: nil):: nil).
  - apply hmr_sound with hmr_frag_full.
    apply hmrr_T with sq2; try reflexivity.
    apply hmrr_S.
    apply hmrr_ex_seq with (vec (sq2 :: nil) (HMR_covar 0) ++ vec (time_pos sq2 One :: nil) (HMR_var 0) ++ nil).
    + unfold seq_mul.
      replace (time_pos sq2 One) with sq2 by (unfold sq2; unfold One; apply Rpos_eq; simpl; nra).
      simpl.
      apply Permutation_Type_swap.
    + apply hmrr_ID ; [ | apply hmrr_INIT].
      simpl.
      nra.
  - intros pi.
    apply int_lambda_prop in pi as [L [Hlen [[[Hex Hsum] Hone] Hstep]]].
    + specialize (Hsum 0)%nat.
      simpl in Hlen.
      clear Hone Hstep.
      destruct L; [ | destruct L ; [ | destruct L]]; inversion Hlen.
      destruct n0; destruct n; try lia.
      * inversion Hex; [ lia | ].
        inversion X; [ lia | ].
        inversion X0.
      * simpl in *.
        change (match n with
                | 0%nat => 1
                | S _ => INR n + 1
                end)
          with (INR (S n)) in Hsum.
        replace (INR (S n) * (1 + 0 - 0) + 0) with (INR (S n)) in Hsum by lra.
        change 0 with (INR 0) in Hsum; apply INR_inj in Hsum; inversion Hsum.
      * simpl in *.
        change (match n0 with
                | 0%nat => 1
                | S _ => INR n0 + 1
                end)
          with (INR (S n0)) in Hsum.
        replace (INR (S n0) * (0 - (sqrt 2 + 0)) + 0) with (- INR (S n0) * sqrt 2) in Hsum by lra.
        enough (INR ((S n0) * (S n0) * 2) = 0).
        { change 0 with (INR 0) in H0.
          apply INR_inj in H0.
          lia. }
        rewrite ? mult_INR.
        change (INR 2) with 2.
        replace 2 with (sqrt 2 * sqrt 2) by (apply sqrt_def; nra).
        nra.
      * simpl in *.
        change (match n with
                | 0%nat => 1
                | S _ => INR n + 1
                end)
          with (INR (S n)) in Hsum.
        change (match n0 with
                | 0%nat => 1
                | S _ => INR n0 + 1
                end)
          with (INR (S n0)) in Hsum.
        replace (INR (S n) * (1 + 0 - 0)) with (INR (S n)) in Hsum by nra.
        replace (0 - (sqrt 2 + 0)) with (- sqrt 2) in Hsum by nra.
        replace (INR (S n0) * - sqrt 2 + 0) with (- INR (S n0) * sqrt 2) in Hsum by nra.
        assert (INR ((S n) * (S n)) = INR (2 * (S n0) * (S n0))).
        { rewrite ? mult_INR.
          change (INR 2) with 2.
          replace 2 with (sqrt 2 * sqrt 2) by (apply sqrt_def; nra).
          nra. }
        apply INR_inj in H0.
        apply sqrt2_not_rational with (S n) (S n0); auto.
        lia.
    + repeat apply Forall_inf_cons; try apply Forall_inf_nil; apply I.
Qed.
