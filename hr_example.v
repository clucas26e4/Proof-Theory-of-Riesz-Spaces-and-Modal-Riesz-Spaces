Require Import RL.Utilities.Rpos.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.
Require Import RL.hr.interpretation.
Require Import RL.hr.completeness.
Require Import RL.hr.soundness.
Require Import RL.hr.can_elim.

Require Import List.

Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

(** F is a Riesz space term. *)
Definition F := (((plus_pos One One) *S HR_var 0) +S ((plus_pos One One) *S HR_covar 1)) \/S (HR_var 1 +S HR_covar 0).

(** A proof that F is positive using equational reasonning. The proof uses some lemmas defined in soundness, but the derived tree is actually quite big. *)
Lemma F_is_pos : HR_zero <== F.
Proof.
  unfold F.
  rewrite <- mul_distri_term.
  rewrite leq_pos_max_mul_l_inv; auto.
  rewrite commu_plus.
  apply zero_leq_abs.
Qed.

(** A proof that the sequent |- 1.F is derivable using the soundness of the HR and the positivity of F. *)
Lemma F_is_provable_from_soundness : HR_full (((One, F) :: nil) :: nil).
Proof.
  apply HR_le_frag with hr_frag_M_can; [ repeat split; auto | ].
  apply hr_complete; [intros  H; inversion H | ].
  simpl; rewrite mul_1; rewrite neutral_plus.
  apply F_is_pos.
Qed.

(** An other derivation for the sequent |- 1.F *)
Lemma F_is_provable : HR_full (((One, F) :: nil) :: nil).
Proof.
  change ((One, F) :: nil) with (vec (One :: nil) F ++ nil).
  unfold F.
  apply hrr_max.
  eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  apply hrr_plus.
  apply hrr_mul.
  rewrite app_assoc.
  eapply hrr_ex_seq ; [ apply Permutation_Type_app ; [ apply Permutation_Type_app_swap | reflexivity ] | ].
  rewrite <- app_assoc.
  apply hrr_mul.
  eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  apply hrr_plus.
  apply hrr_T with (plus_pos One One); [reflexivity | ].
  apply hrr_S.
  rewrite ? seq_mul_app.
  rewrite ? seq_mul_vec_mul_vec.
  apply hrr_ex_seq with (vec (time_pos (plus_pos One One) One :: nil) (HR_covar 0) ++ vec (time_pos (plus_pos One One) One :: nil) (HR_var 0) ++ vec (time_pos (plus_pos One One) One :: nil) (HR_covar 1) ++ vec (time_pos (plus_pos One One) One :: nil) (HR_var 1) ++ nil).
  { simpl.
    Permutation_Type_solve. }
  apply hrr_ID ; [ reflexivity | ].
  apply hrr_ID ; [ reflexivity | ].
  apply hrr_INIT.
Qed.
  
(** We can use the soundness of HR to have a proof that F is positive. *)
Lemma F_is_pos_from_soundness : HR_zero <== F.
Proof.
  apply leq_cong_r with (sem_hseq (((One, F) :: nil) :: nil)).
  { simpl.
    rewrite mul_1; rewrite neutral_plus; reflexivity. }
  apply hr_sound with hr_frag_full.
  apply F_is_provable.
Qed.

(** Finally, we can have a CAN-free proof of |- 1.F with the can elimination theorem. *)
Lemma F_is_provable_without_CAN : HR_T_M (((One, F) :: nil) :: nil).
Proof.
  apply hrr_can_elim.
  apply F_is_provable.
Qed.
