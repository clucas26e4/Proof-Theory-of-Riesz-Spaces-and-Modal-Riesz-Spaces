(** * Implementation of Section 3.3 *)
Require Import Rpos.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.

Require Import CMorphisms.
Require Import List.
Require Import Lra.

Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** Implementation of Lemma 3.20 *)
Lemma hrr_ID_gen P : forall G T A r s, sum_vec r = sum_vec s -> HR P (T :: G) -> HR P ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  intros G T A; revert G T.
  induction A;intros G T r0 s Heq pi; unfold minus; fold minus.
  - apply hrr_ID; assumption.
  - apply hrr_ex_seq with (vec r0 (HR_covar n) ++ vec s (HR_var n) ++ T); [ Permutation_Type_solve | ].
    apply hrr_ID; try symmetry; assumption.
  - apply hrr_Z; apply hrr_Z; apply pi.
  - apply hrr_plus.
    apply hrr_ex_seq with (vec r0 (A1 +S A2) ++ vec s (-S A1) ++ vec s (-S A2) ++ T); [ Permutation_Type_solve | ].
    apply hrr_plus.
    eapply hrr_ex_seq.
    2:{ eapply IHA1; [ apply Heq | ].
        eapply hrr_ex_seq.
        2:{ eapply IHA2; [ apply Heq | apply pi ]. }
        Permutation_Type_solve. }
    Permutation_Type_solve.
  - apply hrr_mul.
    eapply hrr_ex_seq with (vec r0 (r *S A) ++ vec (mul_vec r s) (-S A) ++ T) ; [ Permutation_Type_solve | ].
    apply hrr_mul.
    apply hrr_ex_seq with (vec (mul_vec r s) (-S A) ++ vec (mul_vec r r0) A ++ T); [ Permutation_Type_solve | ].
    apply IHA ; [ | apply pi].
    rewrite ? sum_mul_vec.
    destruct r as [r Hr].
    simpl.
    apply R_blt_lt in Hr.
    nra.
  - apply hrr_min.
    + apply hrr_ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A1) ++ T); [Permutation_Type_solve | ].
      apply hrr_max.
      apply hrr_W.
      eapply hrr_ex_seq; [ | apply IHA1; [ apply Heq | apply pi] ].
      Permutation_Type_solve.
    + apply hrr_ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A2) ++ T); [Permutation_Type_solve | ].
      apply hrr_max.
      apply hrr_ex_hseq with ((vec r0 A1 ++ vec s (-S A2) ++ T) :: (vec r0 A2 ++ vec s (-S A2) ++ T) :: G) ; [ Permutation_Type_solve | ]. 
      apply hrr_W.
      eapply hrr_ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      Permutation_Type_solve.
  - apply hrr_ex_seq with (vec r0 (A1 /\S A2) ++ vec s (-S A1 \/S -S A2) ++ T); [ Permutation_Type_solve | ].
    apply hrr_min.
    + apply hrr_ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A1) ++ T); [Permutation_Type_solve | ].
      apply hrr_max.
      apply hrr_W.
      apply IHA1; [ apply Heq | apply pi].
    + apply hrr_ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A2) ++ T); [Permutation_Type_solve | ].
      apply hrr_max.
      apply hrr_ex_hseq with ((vec s (-S A1) ++ vec r0 A2 ++ T) :: (vec s (-S A2) ++ vec r0 A2 ++ T) :: G) ; [ Permutation_Type_solve | ]. 
      apply hrr_W.
      eapply hrr_ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      Permutation_Type_solve.
Qed.

(** Implementation of Lemma 3.21 *)
Lemma subs_proof P : forall G n t,
    HR P G ->
    HR P (subs_hseq G n t).
Proof with try assumption; try reflexivity.
  intros G n t pi.
  induction pi;unfold subs_hseq in *; fold subs_hseq in *; try rewrite ? subs_seq_vec in *; try rewrite subs_seq_app in *; unfold subs in *; fold subs in *; try now constructor.
  - replace (subs_seq (seq_mul r T) n t) with (seq_mul r (subs_seq T n t)) in IHpi by (clear; induction T; try destruct a; simpl; try rewrite IHT; try reflexivity).
    apply hrr_T with r...
  - case (n =? n0).
    + apply hrr_ID_gen...
    + apply hrr_ID...
  - eapply hrr_ex_seq; [ apply subs_seq_ex ; apply p | ]...
  - eapply hrr_ex_hseq; [ apply subs_hseq_ex; apply p | ]...
  - rewrite eq_subs_minus in IHpi.
    apply hrr_can with (subs A n t) r s...
Qed.    

(** Implementation of Lemma 3.22 *)
Lemma hrr_plus_can_inv P : forall G T A B r, HR P ((vec r (A +S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r A ++ vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A +S B) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) ++ (vec r (A +S B) ++ T)); [ Permutation_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P) ; [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hrr_ex_hseq with (G ++ ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) :: nil)); [ Permutation_Type_solve | ].
  apply hrr_W_gen.
  unfold minus; fold (-S A); fold (-S B).
  apply hrr_plus.
  apply hrr_ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B); [ Permutation_Type_solve | ].
  apply hrr_ID_gen; try reflexivity.
  replace (vec r (-S B) ++ vec r B) with (vec r (-S B) ++ vec r B ++ nil) by (now rewrite app_nil_r).
  apply hrr_ID_gen; [ reflexivity | apply hrr_INIT ].
Qed.

Lemma hrr_Z_can_inv P : forall G T r, HR P ((vec r HR_zero ++ T) :: G) -> HR (hr_frag_add_CAN P) (T :: G).
Proof.
  intros G T r pi.
  apply hrr_can with HR_zero r r; try reflexivity.
  apply hrr_Z.
  apply HR_le_frag with P; try assumption.
  apply add_CAN_le_frag.
Qed.
  
Lemma hrr_mul_can_inv P : forall G T A r0 r, HR P ((vec r (r0 *S A) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  intros G T A r0 r pi.
  apply hrr_can with (r0 *S A) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) ++ (vec r (r0 *S A) ++ T)); [ Permutation_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hrr_ex_hseq with (G ++ ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) :: nil)); [ Permutation_Type_solve | ].
  apply hrr_W_gen.
  unfold HR_minus; fold HR_minus.
  apply hrr_mul.
  replace (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A) with (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A ++ nil) by (now rewrite app_nil_r).
  apply hrr_ID_gen; [ reflexivity | ].
  apply hrr_INIT.
Qed.

Lemma hrr_max_can_inv P : forall G T A B r, HR P ((vec r (A \/S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A \/S B) r r; try reflexivity.
  apply hrr_ex_seq with ( (vec r (-S (A \/S B)) ++ vec r B) ++ (vec r (A \/S B) ++ T)); [Permutation_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hrr_ex_hseq with ((vec r A ++ T) :: (vec r (-S (A \/S B)) ++ vec r B) :: G); [ apply Permutation_Type_swap | ].
  apply hrr_can with (A \/S B) r r ; try reflexivity.
  apply hrr_ex_seq with ( (vec r (-S (A \/S B)) ++ vec r A) ++ (vec r (A \/S B) ++ T)); [Permutation_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hrr_min.
  - apply hrr_ex_hseq with (( (vec r (-S A /\S -S B) ++ vec r B) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ Permutation_Type_solve | ].
    apply hrr_W_gen.
    replace (vec r (-S A) ++ vec r A) with (vec r (-S A) ++ vec r A ++ nil) by (now rewrite app_nil_r).
    apply hrr_ID_gen; [reflexivity | apply hrr_INIT].
  - eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_min.
    + apply hrr_S.
      apply hrr_ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B ++ nil) ; [ Permutation_Type_solve | ].
      apply hrr_ID_gen; [ reflexivity | apply hrr_ID_gen ; [ reflexivity | ] ].
      apply hrr_ex_hseq with (G ++ (nil :: nil)); [ Permutation_Type_solve | ].
      apply hrr_W_gen; apply hrr_INIT.
    + rewrite <-(app_nil_r (vec r B)).
      apply hrr_ID_gen; [ reflexivity | ].
      eapply hrr_ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ (nil :: nil)); [ | apply hrr_W_gen; apply hrr_INIT ].
      Permutation_Type_solve.
Qed.

Lemma hrr_min_can_inv_l P : forall G T A  B r, HR P ((vec r (A /\S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A /\S B) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (A /\S B)) ++ vec r A) ++ (vec r (A /\S B) ++ T)); [ Permutation_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hrr_max.
  apply hrr_ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ Permutation_Type_solve | ].
  apply hrr_W_gen.
  rewrite <-(app_nil_r (vec r A)).
  apply hrr_ID_gen; [ reflexivity | apply hrr_INIT].
Qed.

Lemma hrr_min_can_inv_r P : forall G T A  B r, HR P ((vec r (A /\S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A /\S B) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (A /\S B)) ++ vec r B) ++ (vec r (A /\S B) ++ T)); [ Permutation_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hrr_max.
  apply hrr_ex_hseq with (((vec r (-S A) ++ vec r B) :: G) ++ ((vec r (-S B) ++ vec r B) :: nil)); [ Permutation_Type_solve | ].
  apply hrr_W_gen.
  rewrite <-(app_nil_r (vec r B)).
  apply hrr_ID_gen; [ reflexivity | apply hrr_INIT].
Qed.

(** Implementation of Lemma 3.24 *)
Lemma hrr_T_vec P : forall G T vr,
    vr <> nil ->
    HR P (seq_mul_vec vr T :: G) ->
    HR (hr_frag_add_T P) (T :: G).
Proof.
  intros G T vr; revert P G T; induction vr; intros P G T Hnnil pi.
  - exfalso; auto.
  - simpl in *.
    destruct vr.
    + apply hrr_T with a; try reflexivity.
      simpl in pi; rewrite app_nil_r in pi.
      apply HR_le_frag with P; try assumption.
      apply add_T_le_frag.
    + apply hrr_C.
      apply hrr_T with a; try reflexivity.
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      refine (IHvr P (seq_mul a T :: G) T _ _) ; [ now auto | ].
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_S.
      apply pi.
Qed.

(** Implementation of Lemma 3.25 *)
Lemma hrr_T_vec_inv P : forall G T vr,
    HR P (T :: G) ->
    HR (hr_frag_add_T (hr_frag_add_M P)) (seq_mul_vec vr T :: G).
Proof with try assumption.
  intros G T vr; revert G T; induction vr; intros G T pi.
  - apply hrr_ex_hseq with (G ++ (nil :: nil)) ; [ Permutation_Type_solve | ].
    apply hrr_W_gen.
    apply hrr_INIT.
  - simpl.
    apply hrr_M; try reflexivity.
    + apply hrr_T with (inv_pos a); try reflexivity.
      rewrite seq_mul_twice.
      replace (time_pos (inv_pos a) a) with One by (apply Rpos_eq; destruct a; simpl;apply R_blt_lt in e;apply Rinv_l_sym; nra).
      rewrite seq_mul_One.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_T_le_frag ].
    + apply IHvr.
      apply pi.
Qed.

(** Implementation of Corollary 3.26 *)
Lemma mix_A_B : forall G T A B vr vs,
    HR_T_M (((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HR_T_M (((vec vs B) ++ (vec vr B) ++ T) :: G) ->
    HR_T_M (((vec vs B) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs piA piB.
  destruct vr as [| r vr]; [ | destruct vs as [ | s vs ]]; try assumption.
  apply hrr_C.
  change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M).
  apply hrr_T_vec with (r :: vr) ; [now auto | ].
  eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M).
  apply hrr_T_vec with (s :: vs) ; [ now auto | ].
  apply hrr_S.
  apply hrr_ex_seq with ((seq_mul_vec (r :: vr) ((vec (s :: vs) A) ++ (vec (r :: vr) A) ++ T)) ++ (seq_mul_vec (s :: vs) ((vec (s :: vs) B) ++ (vec (r :: vr) B) ++ T))).
  2:{ apply hrr_M; try reflexivity.
      - change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M).
        apply hrr_T_vec_inv.
        apply piA.
      - change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M).
        apply hrr_T_vec_inv.
        apply piB. }
  transitivity ((seq_mul_vec (r :: vr) (vec (s :: vs) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B ++ vec (r :: vr) B ++ T)).
  - apply Permutation_Type_app; try reflexivity.
    transitivity (seq_mul_vec (r :: vr) (vec (s :: vs) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A ++ T)).
    + apply seq_mul_vec_app_r.
    + apply Permutation_Type_app; try reflexivity.
      apply seq_mul_vec_app_r.
  - transitivity ((seq_mul_vec (r :: vr) (vec (s :: vs) A) ++
                               seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++
                                                                                                   ( seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B) ++ seq_mul_vec (s :: vs) T)).
    + apply Permutation_Type_app; try reflexivity.
      transitivity (seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B ++ T)).
      * apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        apply seq_mul_vec_app_r.
    + transitivity ((seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (s :: vs) T) ++ seq_mul_vec (r :: vr) (vec (s :: vs) B ++ vec (r :: vr) A ++ T)).
      * transitivity ((seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (s :: vs) T) ++ (seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ (seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T))).
        -- transitivity ((seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B) ++ seq_mul_vec (s :: vs) T).
           ++ do 2 (apply Permutation_Type_app; try reflexivity).
              apply seq_mul_vec_vec.
           ++ transitivity ((seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) T).
              ** do 3 (apply Permutation_Type_app; try reflexivity).
                 apply seq_mul_vec_vec.
              ** remember (seq_mul_vec (s :: vs) (vec (r :: vr) A)) as srA.
                 remember (seq_mul_vec (r :: vr) (vec (r :: vr) A)) as rrA.
                 remember (seq_mul_vec (s :: vs) (vec (s :: vs) B)) as ssB.
                 remember (seq_mul_vec (r :: vr) (vec (s :: vs) B)) as rsB.
                 Permutation_Type_solve.                 
        -- apply Permutation_Type_app; try reflexivity.
           transitivity (seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A ++ T)).
           ++ apply Permutation_Type_app; try reflexivity.
              symmetry; apply seq_mul_vec_app_r.
           ++ symmetry; apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        transitivity (seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A ++ T)).
        -- apply Permutation_Type_app; try reflexivity.
           symmetry; apply seq_mul_vec_app_r.
        -- symmetry; apply seq_mul_vec_app_r.
Qed.

(** Implementation of Corollary 3.27 *)
Lemma C_A_B : forall G T A B vr vs,
    HR_T_M (((vec vs B) ++ (vec vr A) ++ T) ::((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HR_T_M (((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs pi.
  destruct vr as [ | r vr]; [ | destruct vs as [ | s vs]].
  - simpl in *.
    apply hrr_C.
    apply pi.
  - simpl in *.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_C.
    eapply hrr_ex_hseq ; [ | apply pi].
    apply Permutation_Type_skip.
    apply Permutation_Type_swap.
  - remember (s :: vs) as vs'; remember (r :: vr) as vr'.
    apply hrr_C.
    change hr_frag_T_M with (hr_frag_add_T hr_frag_T_M).
    apply hrr_T_vec with vs' ; [ rewrite Heqvs'; now auto | ].
    apply hrr_ex_hseq with ((vec vs' A ++ vec vr' A ++ T) :: (vec vs' B ++ vec vr' B ++ T) :: (seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)) :: G).
    { etransitivity ; [ | apply Permutation_Type_swap ].
      etransitivity; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply hrr_C.
    change hr_frag_T_M with (hr_frag_add_T hr_frag_T_M).
    apply hrr_T_vec with vr'; [ rewrite Heqvr' ; now auto | ].
    eapply hrr_ex_hseq.
    { apply Permutation_Type_skip.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply hrr_S.
    apply hrr_ex_seq with (seq_mul_vec (vr' ++ vs') (vec vs' B ++ vec vr' A ++ T)).
    2:{ change hr_frag_T_M with (hr_frag_add_T (hr_frag_add_M hr_frag_T_M)).
        apply hrr_T_vec_inv.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply pi]. }
    rewrite seq_mul_vec_app_l.
    symmetry.
    transitivity ((seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)).
    + apply Permutation_Type_app; try reflexivity.
      transitivity (seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A ++ T)).
      * apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        apply seq_mul_vec_app_r.
    + transitivity ((seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ ( seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B) ++ seq_mul_vec vs' T)).
      * apply Permutation_Type_app; try reflexivity.
        transitivity (seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B ++ T)).
        -- apply seq_mul_vec_app_r.
        -- apply Permutation_Type_app; try reflexivity.
           apply seq_mul_vec_app_r.
      * transitivity ((seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B ++ vec vr' A ++ T)).
        -- transitivity ((seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ (seq_mul_vec vs' (vec vs' B) ++ (seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vs' T))).
           ++ transitivity ((seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B) ++ seq_mul_vec vs' T).
              ** do 2 (apply Permutation_Type_app; try reflexivity).
                 apply seq_mul_vec_vec.
              ** transitivity ((seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vs' T).
                 --- do 3 (apply Permutation_Type_app; try reflexivity).
                     apply seq_mul_vec_vec.
                 --- remember (seq_mul_vec vs' (vec vr' A)) as srA.
                     remember (seq_mul_vec vr' (vec vr' A)) as rrA.
                     remember (seq_mul_vec vs' (vec vs' B)) as ssB.
                     remember (seq_mul_vec vr' (vec vs' B)) as rsB.
                     Permutation_Type_solve.                 
           ++ apply Permutation_Type_app; try reflexivity.
              transitivity (seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' A ++ T)).
              ** apply Permutation_Type_app; try reflexivity.
                 symmetry; apply seq_mul_vec_app_r.
              ** symmetry; apply seq_mul_vec_app_r.
        -- apply Permutation_Type_app; try reflexivity.
           transitivity (seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A ++ T)).
           ++ apply Permutation_Type_app; try reflexivity.
              symmetry; apply seq_mul_vec_app_r.
           ++ symmetry; apply seq_mul_vec_app_r.
Qed.
