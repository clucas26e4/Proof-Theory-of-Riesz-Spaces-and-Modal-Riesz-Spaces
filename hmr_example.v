Require Import RL.Utilities.Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.interpretation.
Require Import RL.hmr.completeness.
Require Import RL.hmr.soundness.
Require Import RL.hmr.can_elim.

Require Import List.

Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

(** F is a Riesz space term. *)
Definition F := (((plus_pos One One) *S HMR_var 0) +S ((plus_pos One One) *S HMR_covar 1)) \/S (HMR_var 1 +S HMR_covar 0).

(** A proof that F is positive using equational reasonning. The proof uses some lemmas defined in soundness, but the derived tree is actually quite big. *)
Lemma F_is_pos : HMR_zero <== F.
Proof.
  unfold F.
  rewrite <- mul_distri_term.
  rewrite leq_pos_max_mul_l_inv; auto.
  rewrite commu_plus.
  apply zero_leq_abs.
Qed.

(** A proof that the sequent |- 1.F is derivable using the soundness of the HMR and the positivity of F. *)
Lemma F_is_provable_from_soundness : HMR_full (((One, F) :: nil) :: nil).
Proof.
  apply HMR_le_frag with hmr_frag_M_can; [ repeat split; auto | ].
  apply hmr_complete; [intros  H; inversion H | ].
  simpl; rewrite mul_1; rewrite neutral_plus.
  apply F_is_pos.
Qed.

(** An other derivation for the sequent |- 1.F *)
Lemma F_is_provable : HMR_full (((One, F) :: nil) :: nil).
Proof.
  change ((One, F) :: nil) with (vec (One :: nil) F ++ nil).
  unfold F.
  apply hmrr_max.
  eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  apply hmrr_plus.
  apply hmrr_mul.
  rewrite app_assoc.
  eapply hmrr_ex_seq ; [ apply Permutation_Type_app ; [ apply Permutation_Type_app_swap | reflexivity ] | ].
  rewrite <- app_assoc.
  apply hmrr_mul.
  eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  apply hmrr_plus.
  apply hmrr_T with (plus_pos One One); [reflexivity | ].
  apply hmrr_S.
  rewrite ? seq_mul_app.
  rewrite ? seq_mul_vec_mul_vec.
  apply hmrr_ex_seq with (vec (time_pos (plus_pos One One) One :: nil) (HMR_covar 0) ++ vec (time_pos (plus_pos One One) One :: nil) (HMR_var 0) ++ vec (time_pos (plus_pos One One) One :: nil) (HMR_covar 1) ++ vec (time_pos (plus_pos One One) One :: nil) (HMR_var 1) ++ nil).
  { simpl.
    Permutation_Type_solve. }
  apply hmrr_ID ; [ reflexivity | ].
  apply hmrr_ID ; [ reflexivity | ].
  apply hmrr_INIT.
Qed.
  
(** We can use the soundness of HMR to have a proof that F is positive. *)
Lemma F_is_pos_from_soundness : HMR_zero <== F.
Proof.
  apply leq_cong_r with (sem_hseq (((One, F) :: nil) :: nil)).
  { simpl.
    rewrite mul_1; rewrite neutral_plus; reflexivity. }
  apply hmr_sound with hmr_frag_full.
  apply F_is_provable.
Qed.

(** Finally, we can have a CAN-free proof of |- 1.F with the can elimination theorem. *)
Lemma F_is_provable_without_CAN : HMR_T_M (((One, F) :: nil) :: nil).
Proof.
  apply hmrr_can_elim.
  apply F_is_provable.
Qed.
