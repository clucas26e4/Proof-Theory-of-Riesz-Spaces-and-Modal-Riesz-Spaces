(** * Summary of the main results as in Section 4.1 *)
Require Import RL.Utilities.Rpos.
Require Import RL.hmr.Rterm.
Require Import RL.hmr.term.
Require Import RL.hmr.Rsemantic.
Require Import RL.hmr.semantic.
Require Import RL.hmr.semantic_Rsemantic_eq.
Require Import RL.hmr.hseq.
Require Import RL.hmr.completeness.
Require Import RL.hmr.soundness.
Require Import RL.hmr.interpretation.
Require Import RL.hmr.hmr.
Require Import RL.hmr.invertibility.
Require Import RL.hmr.M_elim.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.decidability.

Require Import Reals.
Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.

(** Theorem 4.3 *)
Lemma HMR_soundness P : forall G,
    HMR P G ->
    R_zero <R= toRterm (sem_hseq G).
Proof.
  intros G pi.
  change (R_zero /\R (toRterm (sem_hseq G))) with (toRterm (HMR_zero /\S sem_hseq G)).
  change (R_zero) with (toRterm HMR_zero).
  apply semantic_to_Rsemantic.
  apply hmr_sound with P.
  apply pi.
Qed.

(** Theorem 4.4 *)
Lemma HMR_completeness : forall G,
    G <> nil ->
    R_zero <R= toRterm (sem_hseq G) ->
    HMR_M_can G.
Proof.
  intros G Hnnil H.
  apply hmr_complete; [ apply Hnnil | ].
  transitivity (NNF (R_zero /\R toRterm (sem_hseq G))).
  - simpl.
    rewrite NNF_toRterm.
    reflexivity.
  - change HMR_zero with (NNF (R_zero)).
    apply Rsemantic_to_semantic.
    apply H.
Qed.

(** Theorem 4.6 *)
Lemma HMR_plus_inv : forall G T A B r, HMR_T_M ((vec r (A +S B) ++ T) :: G) -> HMR_T_M ((vec r A ++ vec r B ++ T) :: G).
Proof.
  apply hmrr_plus_inv.
Qed.

Lemma HMR_Z_inv : forall G T r, HMR_T_M ((vec r HMR_zero ++ T) :: G) -> HMR_T_M (T :: G).
Proof.
  apply hmrr_Z_inv.
Qed.
  
Lemma HMR_mul_inv : forall G T A r0 r, HMR_T_M ((vec r (r0 *S A) ++ T) :: G) -> HMR_T_M ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  apply hmrr_mul_inv.
Qed.

Lemma HMR_max_inv : forall G T A B r, HMR_T_M ((vec r (A \/S B) ++ T) :: G) -> HMR_T_M ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  apply hmrr_max_inv.
Qed.

Lemma HMR_min_inv_l : forall G T A  B r, HMR_T_M ((vec r (A /\S B) ++ T) :: G) -> HMR_T_M ((vec r A ++ T) :: G).
Proof.
  apply hmrr_min_inv_l.
Qed.

Lemma HMR_min_inv_r : forall G T A  B r, HMR_T_M ((vec r (A /\S B) ++ T) :: G) -> HMR_T_M ((vec r B ++ T) :: G).
Proof.
  apply hmrr_min_inv_r.
Qed.

(** Theorem 4.9 *)
Lemma HMR_M_elim : forall G, HMR_T_M G -> HMR_T G.
Proof.
  apply hmrr_M_elim.
Qed.

(** Theorem 4.10 *)
Lemma HMR_can_elim : forall G, HMR_full G -> HMR_T_M G.
Proof.
  apply hmrr_can_elim.
Qed.

(** Theorem 4.11 *)
Lemma HMR_is_decidable : forall G,
    (HMR_full G) + (HMR_full G -> False).
Proof.
  apply HMR_decidable.
Qed.
