(** * Implementation of Section 4.6 *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.tech_lemmas.
Require Import RL.hmr.preproof.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

(** Proof of Lemma 4.35 *)
Lemma hmrr_mul_vec : forall L (pi : HMR_T (map (fun x => snd x) L)),
    { pi' : HMR_T (map (fun x => seq_mul_vec (fst x) (snd x)) L) & (modal_depth_proof pi' <= modal_depth_proof pi)}.
Proof.
  intros L pi.
  remember (map (fun x => snd x) L) as G.
  revert L HeqG; induction pi; intros L HeqG.
  - destruct L; [ | destruct L]; try now inversion HeqG.
    destruct p as [r T]; destruct T; try now inversion HeqG.
    esplit.
    Unshelve.
    2:{ simpl; rewrite seq_mul_vec_nil_r; apply hmrr_INIT. }
    unfold HMR_T; unfold map; rewrite (modal_depth_proof_eq_rect_r _ _ (fun l : list (Rpos * term) => l :: nil)).
    reflexivity.
  - destruct L; try now inversion HeqG.
    simpl in HeqG; inversion HeqG.
    destruct (IHpi _ H1) as [pi' Hpi'].
    split with (hmrr_W _ _ _ pi').
    apply Hpi'.
  - destruct L; simpl in HeqG; inversion HeqG; subst.
    destruct (IHpi (p :: p :: L) eq_refl) as [pi' Hpi'].
    split with (hmrr_C _ _ _ pi').
    simpl; apply Hpi'.
  - destruct L; [ | destruct L]; try destruct p as [r1 T1']; try destruct p0 as [r2 T2']; inversion HeqG; subst.
    destruct r1 ; [ | destruct r2].
    + simpl.
      esplit with (hmrr_ex_hseq _ ((seq_mul_vec r2 T2' :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) ++ (nil :: nil)) _ _ (hmrr_W_gen _ _ _ (hmrr_INIT _))).
      Unshelve.
      2: Permutation_Type_solve.
      simpl.
      rewrite modal_depth_proof_W_gen.
      apply Peano.le_0_n.
    + simpl.
      esplit with (hmrr_ex_hseq _ ((seq_mul_vec (r :: r1) T1' :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) ++ (nil :: nil)) _ _ (hmrr_W_gen _ _ _ (hmrr_INIT _))).
      Unshelve.
      2: Permutation_Type_solve.
      simpl.
      rewrite modal_depth_proof_W_gen.
      apply Peano.le_0_n.
    + destruct (IHpi ((vec_mul_vec (r :: r1) (r0 :: r2) , T1' ++ T2') :: L) eq_refl) as [pi' Hpi'].
      assert (r0 :: r2 <> nil) as Hnnilr2 by now auto.
      assert (r :: r1 <> nil) as Hnnilr1 by now auto.
      assert (Permutation_Type (seq_mul_vec (vec_mul_vec (r :: r1) (r0 :: r2)) (T1' ++ T2')) ((seq_mul_vec (r0 :: r2) (seq_mul r T1' ++ seq_mul_vec r1 T1') ++ seq_mul_vec (r :: r1) (seq_mul r0 T2' ++ seq_mul_vec r2 T2')))) as Hperm'.
      { etransitivity; [ symmetry; apply seq_mul_vec_twice | ].
        etransitivity ; [ apply seq_mul_vec_perm_r; apply (seq_mul_vec_app_r _ _ (r0 :: r2)) | ].
        etransitivity ; [ apply seq_mul_vec_app_r | ].
        etransitivity ; [ apply Permutation_Type_app ; [ apply seq_mul_vec_twice_comm | reflexivity ] | ].
        Permutation_Type_solve. }
      esplit.
      Unshelve.
      2:{ unfold HMR_T; change hmr_frag_T with (hmr_frag_add_T hmr_frag_T).
          simpl.
          apply hmrr_T_vec with (r0 :: r2); try apply Hnnilr2.
          eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
          change hmr_frag_T with (hmr_frag_add_T hmr_frag_T).
          apply hmrr_T_vec with (r :: r1); try apply Hnnilr1.
          eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
          apply hmrr_S.
          eapply hmrr_ex_seq; [ apply Hperm' | ].
          apply pi'. }
      change hmr_frag_T with (hmr_frag_add_T hmr_frag_T) at 1.
      unfold map.
      rewrite modal_depth_proof_T_vec.
      unfold modal_depth_proof; fold (@modal_depth_proof hmr_frag_T).
      change hmr_frag_T with (hmr_frag_add_T hmr_frag_T) at 1.
      rewrite modal_depth_proof_T_vec.
      unfold modal_depth_proof; fold (@modal_depth_proof hmr_frag_T).
      apply Hpi'.
  - inversion f.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.    
    simpl.
    destruct (IHpi ((r1, seq_mul r T1) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply hmrr_T with r; try assumption.
        rewrite seq_mul_seq_mul_vec.
        apply pi'. }
    simpl.
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => l :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L)).
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.    
    simpl.
    destruct (IHpi ((r1, T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply hmrr_ex_seq with (vec (vec_mul_vec r1 s) (HMR_covar n) ++ vec (vec_mul_vec r1 r) (HMR_var n) ++ seq_mul_vec r1 T).
        { etransitivity ; [ | symmetry ; apply seq_mul_vec_app_r].
          etransitivity ; [ | symmetry; apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity ].
          apply Permutation_Type_app ; [ | apply Permutation_Type_app]; try rewrite seq_mul_vec_vec_mul_vec; reflexivity. }
        apply hmrr_ID.
        { rewrite ? sum_vec_vec_mul_vec.
          nra. }
        apply pi'. }
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi ((r1, T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        eapply hmrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
        rewrite seq_mul_vec_vec_mul_vec.
        apply hmrr_Z.
        apply pi'. }
    simpl.
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))).
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi ((r1, vec r A ++ vec r B ++ T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        eapply hmrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
        rewrite seq_mul_vec_vec_mul_vec.
        apply hmrr_plus.
        rewrite <- ? seq_mul_vec_vec_mul_vec.
        apply hmrr_ex_seq with (seq_mul_vec r1 (vec r A ++ vec r B ++ T)).
        { etransitivity ; [apply seq_mul_vec_app_r | ].
          apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity. }
        apply pi'. }
    simpl.
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))).
    simpl.
    rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((l ++ vec (vec_mul_vec r1 r) B ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))).
    rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((seq_mul_vec r1 (vec r A) ++ l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))).
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi ((r1, vec (mul_vec r0 r) A ++ T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        eapply hmrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
        rewrite seq_mul_vec_vec_mul_vec.
        apply hmrr_mul.
        rewrite <- vec_mul_vec_mul_vec_comm.
        rewrite <- ? seq_mul_vec_vec_mul_vec.
        eapply hmrr_ex_seq ; [ apply seq_mul_vec_app_r | ].
        apply pi'. }
    simpl.
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((vec l A ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi ((r1, vec r B ++ T) :: (r1, vec r A ++ T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        eapply hmrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
        rewrite seq_mul_vec_vec_mul_vec.
        apply hmrr_max.
        rewrite <- ? seq_mul_vec_vec_mul_vec.
        eapply hmrr_ex_seq ; [ apply seq_mul_vec_app_r | ].
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
        eapply hmrr_ex_seq ; [ apply seq_mul_vec_app_r | ].
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
        apply pi'. }
    simpl.
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: (vec (vec_mul_vec r1 r) A ++ seq_mul_vec r1 T):: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((seq_mul_vec r1 (vec r B) ++ seq_mul_vec r1 T) :: (l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    apply Hpi'.    
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi1 ((r1, vec r A ++ T) :: L) eq_refl) as [pi1' Hpi1'].
    destruct (IHpi2 ((r1, vec r B ++ T) :: L) eq_refl) as [pi2' Hpi2'].
    esplit.
    Unshelve.
    2:{ simpl.
        eapply hmrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
        rewrite seq_mul_vec_vec_mul_vec.
        apply hmrr_min;
          rewrite <- ? seq_mul_vec_vec_mul_vec;
          (eapply hmrr_ex_seq ; [ apply seq_mul_vec_app_r | ]);
          [ apply pi1'
          | apply pi2' ]. }
    simpl.
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    apply Nat.max_lub; rewrite (modal_depth_proof_eq_rect _ _ (fun l => ((l ++ seq_mul_vec r1 T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L))); simpl.
    + etransitivity ; [ apply Hpi1' | apply Nat.le_max_l; assumption].
    + etransitivity ; [ apply Hpi2' | apply Nat.le_max_r; assumption].
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi ((r1, T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        apply hmrr_ex_seq with (vec (vec_mul_vec r1 s) HMR_coone ++ vec (vec_mul_vec r1 r) HMR_one ++ seq_mul_vec r1 T).
        { rewrite <- ? seq_mul_vec_vec_mul_vec.
          etransitivity ; [ | etransitivity ; [ apply Permutation_Type_app; [ reflexivity |  symmetry; apply seq_mul_vec_app_r ]| symmetry; apply seq_mul_vec_app_r ]].
          reflexivity. }
        apply hmrr_one.
        { rewrite ? sum_vec_vec_mul_vec.
          assert ((0 <= sum_vec r1)%R) by apply (sum_vec_le_0).
          nra. }
        apply pi'. }
    apply Hpi'.
  - destruct L; [ | destruct L];  try destruct p as [r1 T1]; inversion HeqG; subst.
    destruct (IHpi ((r1, vec s HMR_coone ++ vec r HMR_one ++ T) :: nil) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        apply hmrr_ex_seq with (vec (vec_mul_vec r1 s) HMR_coone ++ vec (vec_mul_vec r1 r) HMR_one ++ seq_diamond (seq_mul_vec r1 T)).
        { rewrite <- ? seq_mul_vec_vec_mul_vec.
          etransitivity ; [ | etransitivity ; [ apply Permutation_Type_app; [ reflexivity |  symmetry; apply seq_mul_vec_app_r ]| symmetry; apply seq_mul_vec_app_r ]].
          rewrite seq_diamond_seq_mul_vec.
          reflexivity. }
        apply hmrr_diamond.
        { rewrite ? sum_vec_vec_mul_vec.
          assert ((0 <= sum_vec r1)%R) by apply (sum_vec_le_0).
          nra. }
        eapply hmrr_ex_seq ; [ | apply pi'].
        symmetry; simpl.
        rewrite <- ? seq_mul_vec_vec_mul_vec.
        etransitivity ; [ | etransitivity ; [ apply Permutation_Type_app; [ reflexivity |  symmetry; apply seq_mul_vec_app_r ]| symmetry; apply seq_mul_vec_app_r ]].
        reflexivity. }
    simpl; apply le_n_S; apply Hpi'.
  - destruct L; try destruct p0 as [r1 T1']; inversion HeqG; subst.
    destruct (IHpi ((r1 , T1) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ simpl.
        eapply hmrr_ex_seq ; [ apply seq_mul_vec_perm_r; apply p | ].
        apply pi'. }
    apply Hpi'.
  - subst.
    destruct (Permutation_Type_map_inv _ _ p) as [L' Heq Hperm].
    destruct (IHpi L' Heq) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:eapply hmrr_ex_hseq ; [ apply Permutation_Type_map ; symmetry; apply Hperm | ]; apply pi'.
    apply Hpi'.
  - inversion f.
Qed.

(** Define the property satisfied by the leaves of the preproof after the step 1 *)
Definition good_leaf_step_1 H D n :=
  fun G => {' (T', r , s ,t) : _ &
                               prod
                                 (G =  (vec t HMR_coone ++ vec s HMR_one ++ seq_mul_vec r D ++ seq_diamond T') :: H)
                                 (((sum_vec t <= sum_vec s)%R) *
                                  ({ pi : HMR_T ((vec t HMR_coone ++ vec s HMR_one ++ T') :: nil) & modal_depth_proof pi < n}))}.

Lemma good_leaf_le : forall H D n1 n2 G,
    n1 <= n2 ->
    good_leaf_step_1 H D n1 G ->
    good_leaf_step_1 H D n2 G.
Proof.
  intros H D n1 n2 G Hle GL.
  destruct GL as [[[[T r] s] t] [G' [Hsum [pi Hpi]]]].
  split with (T,r,s,t).
  repeat split; try assumption.
  split with pi.
  apply Nat.lt_le_trans with n1; assumption.
Qed.

(** Proof of Lemma 4.34 *)
Lemma hmrr_M_step_1 : forall L H D (pi : HMR_T (map (fun x => snd x) L)),
    HMR_T (D :: H) ->
    {' pi' : preHMR (map (fun x => snd x ++ seq_mul_vec (fst x) D) L ++ H) & Forall_inf (good_leaf_step_1 H D (modal_depth_proof pi)) (leaves pi')}.
Proof.
  intros L H D pi pi2.
  remember (map (fun x => snd x) L) as G.
  revert L HeqG.
  induction pi; intros L HeqG.
  - destruct L; try (destruct p as [r1 T1]; destruct T1); inversion HeqG; simpl.
    destruct L; inversion H1; simpl.
    esplit.
    Unshelve.
    2:{ apply HMR_to_preHMR.
        assert {L & prod
                      (H = map (fun x => snd x) L)
                      (H = map (fun x => seq_mul_vec (fst x) (snd x)) L)} as [L [Heq1 Heq2]].
        { clear; induction H.
          - split with nil; split; reflexivity.
          - destruct IHlist as [L [H1 H2]].
            split with (((One :: nil), a) :: L).
            simpl; split ; [ rewrite H1; reflexivity |  rewrite H2].
            rewrite app_nil_r; rewrite seq_mul_One.
            reflexivity. }
        rewrite Heq2.
        change (seq_mul_vec r1 D :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L)
          with
            (map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) ((r1 , D) :: L)).
        apply hmrr_mul_vec.
        simpl; rewrite <- Heq1.
        apply pi2. }
    rewrite HMR_to_preHMR_no_leaf.
    apply Forall_inf_nil.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi L eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:apply prehmrr_W; apply pi'.
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, T1) :: (r1, T1) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:apply prehmrr_C; apply pi'.
    apply Hpi'.
  - destruct L; [ | destruct L]; try destruct p as [r1 T1']; try destruct p0 as [r2 T2']; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1 ++ r2, T1' ++ T2') :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_S.
        apply prehmrr_ex_seq with ((T1' ++ T2') ++ seq_mul_vec (r1 ++ r2) D).
        { rewrite seq_mul_vec_app_l.
          Permutation_Type_solve. }
        apply pi'. }
    simpl.
    apply Hpi'.
  - inversion f.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((mul_vec r r1, seq_mul r T1) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_T with r.
        apply prehmrr_ex_seq with (seq_mul r T1 ++ seq_mul_vec (mul_vec r r1) D) ; [ rewrite seq_mul_app; rewrite seq_mul_seq_mul_vec_2; reflexivity | ].
        apply pi'. }
    simpl; apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec s (HMR_covar n) ++ vec r (HMR_var n) ++ T ++ seq_mul_vec r1 D) ; [ rewrite <- ? app_assoc; reflexivity | apply prehmrr_ID; try assumption]. }
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec r HMR_zero ++ T ++ seq_mul_vec r1 D) ; [ rewrite <- ? app_assoc; reflexivity | apply prehmrr_Z; apply pi']. }
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, vec r A ++ vec r B ++ T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec r (A +S B) ++ T ++ seq_mul_vec r1 D) ; [ rewrite <- ? app_assoc; reflexivity | apply prehmrr_plus].
        eapply prehmrr_ex_seq ; [ | apply pi'].
        Permutation_Type_solve. }
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, vec (mul_vec r0 r) A ++ T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec r (r0 *S A) ++ T ++ seq_mul_vec r1 D) ; [ rewrite <- ? app_assoc; reflexivity | apply prehmrr_mul].
        eapply prehmrr_ex_seq ; [ | apply pi'].
        Permutation_Type_solve. }
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, vec r B ++ T) :: (r1, vec r A ++ T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec r (A \/S B) ++ T ++ seq_mul_vec r1 D) ; [ rewrite <- ? app_assoc; reflexivity | ].
        apply prehmrr_max.
        eapply prehmrr_ex_hseq; [ apply Permutation_Type_swap | ].
        apply prehmrr_ex_seq with ((vec r A ++ T) ++ seq_mul_vec r1 D) ; [ Permutation_Type_solve | ].
        eapply prehmrr_ex_hseq; [ apply Permutation_Type_swap | ].
        eapply prehmrr_ex_seq; [ | apply pi'].
        Permutation_Type_solve. }
    apply Hpi'.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi1 ((r1, vec r A ++ T) :: L) eq_refl) as [pi1' Hpi1'].
    destruct (IHpi2 ((r1, vec r B ++ T) :: L) eq_refl) as [pi2' Hpi2'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec r (A /\S B) ++ T ++ seq_mul_vec r1 D) ; [ Permutation_Type_solve |].
        apply prehmrr_min; eapply prehmrr_ex_hseq ; [ | apply pi1' | | apply pi2']; Permutation_Type_solve. }
    simpl.
    apply Forall_inf_app.
    + apply Forall_inf_arrow with (good_leaf_step_1 H D (modal_depth_proof pi1)); try assumption.
      intros a GL.
      apply good_leaf_le with (modal_depth_proof pi1); try assumption.
      apply Nat.le_max_l.
    + apply Forall_inf_arrow with (good_leaf_step_1 H D (modal_depth_proof pi3)); try assumption.
      intros a GL.
      apply good_leaf_le with (modal_depth_proof pi3); try assumption.
      apply Nat.le_max_r.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, T) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ apply prehmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ T ++ seq_mul_vec r1 D) ; [ rewrite <- ? app_assoc; reflexivity | apply prehmrr_one; try assumption]. }
    apply Hpi'.
  - destruct L ; [ | destruct L]; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    assert ({pi' : preHMR ((vec s HMR_coone ++ vec r HMR_one ++ seq_mul_vec r1 D ++ seq_diamond T) :: H) &
                   Forall_inf (good_leaf_step_1 H D (S (modal_depth_proof pi))) (leaves pi')}) as [pi' Hpi'].
    { split with (prehmrr_leaf _).
      apply Forall_inf_cons ; [ | apply Forall_inf_nil].
      split with (T, r1, r, s).
      repeat split; try assumption; try reflexivity.
      split with pi.
      auto. }
    esplit.
    Unshelve.
    2:{ eapply prehmrr_ex_seq ; [ | apply pi'].
        Permutation_Type_solve. }
    apply Hpi'.
  - destruct L; try destruct p0 as [r1 T1']; inversion HeqG; subst; simpl.
    destruct (IHpi ((r1, T1) :: L) eq_refl) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ eapply prehmrr_ex_seq ; [ apply Permutation_Type_app ; [ apply p | reflexivity] | ].
        apply pi'. }
    apply Hpi'.
  - subst.
    destruct (Permutation_Type_map_inv  _ _ p) as [L' Heq Hperm].
    destruct (IHpi L' Heq) as [pi' Hpi'].
    esplit.
    Unshelve.
    2:{ eapply prehmrr_ex_hseq ; [ apply Permutation_Type_app ; [ apply Permutation_Type_map ; symmetry; apply Hperm | reflexivity ] | ].
        apply pi'. }
    apply Hpi'.
  - inversion f.
Qed.

(** Generalized version of Theorem 4.9 *)
Lemma hmrr_M_gen : forall L H D (pi : HMR_T (map (fun x => snd x) L)),
    HMR_T (D :: H) ->
    HMR_T (map (fun x => snd x ++ seq_mul_vec (fst x) D) L ++ H).
Proof.
  intros L H D pi1 pi2.
  remember (modal_depth_proof pi1) as n.
  revert L H D pi1 pi2 Heqn.
  change (forall (L : list (list Rpos * sequent)) (H : list sequent) (D : sequent)
                 (pi1 : HMR_T (map (fun x : list Rpos * sequent => snd x) L)),
             HMR_T (D :: H) ->
             n = modal_depth_proof pi1 ->
             HMR_T (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H))
    with ((fun n0 => 
            forall (L : list (list Rpos * sequent)) (H : list sequent) (D : sequent)
                   (pi1 : HMR_T (map (fun x : list Rpos * sequent => snd x) L)),
              HMR_T (D :: H) ->
              n0 = modal_depth_proof pi1 ->
              HMR_T (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)) n).
  apply lt_wf_rect.
  intros n0 Hn L H D pi1 pi2 Heq.
  clear n.
  destruct (hmrr_M_step_1 _ _ _ pi1 pi2) as [pi1' Hpi1'].
  apply finish_preproof with pi1'.
  apply forall_Forall_inf.
  intros G Hin.
  destruct (Forall_inf_forall Hpi1' _ Hin) as [[[[T1 r] s] t] [HeqG [Hle [piG Hind]]]].
  subst.
  apply hmrr_ex_seq with (seq_mul_vec r D ++ seq_mul_vec (One :: nil) (vec t HMR_coone ++ vec s HMR_one ++ seq_diamond T1)).
  { simpl; rewrite seq_mul_One; Permutation_Type_solve. }
  assert (HMR_T (seq_mul_vec r D :: H)) as pi2'.
  { assert {L & prod
                  (H = map (fun x => snd x) L)
                  (H = map (fun x => seq_mul_vec (fst x) (snd x)) L)} as [L' [Heq1 Heq2]].
    { clear; induction H.
      - split with nil; split; reflexivity.
      - destruct IHlist as [L [H1 H2]].
        split with (((One :: nil), a) :: L).
        simpl; split ; [ rewrite H1; reflexivity |  rewrite H2].
        rewrite app_nil_r; rewrite seq_mul_One.
        reflexivity. }
    rewrite Heq2.
    change (seq_mul_vec r D :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L')
      with
        (map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) ((r , D) :: L')).
    apply hmrr_mul_vec.
    simpl; rewrite <- Heq1.
    apply pi2. }
  assert {L' & prod
                 (H = map (fun x => snd x) L')
                 (H = map (fun x => snd x ++ seq_mul_vec (fst x) (vec t HMR_coone ++ vec s HMR_one ++ seq_diamond T1)) L')} as [L' [Heq1 Heq2]].
  { clear; induction H.
    - split with nil; split; reflexivity.
    - destruct IHlist as [L [H1 H2]].
      split with ((nil, a) :: L).
      simpl; split ; [ rewrite H1; reflexivity |  rewrite H2].
      rewrite app_nil_r; reflexivity. }
  rewrite Heq2; rewrite Heq1 in pi2'.
  destruct (hmrr_M_step_1 ((One::nil, seq_mul_vec r D) :: L') nil (vec t HMR_coone ++ vec s HMR_one ++ seq_diamond T1) pi2' (hmrr_diamond _ _ _ _ Hle piG)) as [pi' Hleaves].
  rewrite <- app_nil_r.
  apply finish_preproof with pi'.
  apply forall_Forall_inf.
  intros G' Hin'.
  destruct (Forall_inf_forall Hleaves _ Hin') as [[[[D1 r'] s'] t'] [HeqG' [Hle' [piG' Hind']]]].
  subst.
  apply hmrr_ex_seq with (vec (t' ++ vec_mul_vec r' t) HMR_coone ++ vec (s' ++ vec_mul_vec r' s) HMR_one ++ seq_diamond (seq_mul_vec r' T1 ++ D1)).
  { rewrite ? vec_app.
    rewrite ? seq_diamond_app.
    rewrite <- ? seq_mul_vec_vec_mul_vec.
    etransitivity.
    2:{ apply Permutation_Type_app ; [ reflexivity | ].
        apply Permutation_Type_app ; [ reflexivity | ].
        apply Permutation_Type_app ; [ | reflexivity].
        etransitivity ; [ | symmetry; apply seq_mul_vec_app_r ].
        apply Permutation_Type_app ; [ reflexivity | symmetry; apply seq_mul_vec_app_r]. }
    rewrite seq_diamond_seq_mul_vec.
    Permutation_Type_solve. }    
  apply hmrr_diamond.
  { rewrite ? sum_vec_app.
    rewrite ? sum_vec_vec_mul_vec.
    assert ((0 <= sum_vec r')%R) by apply sum_vec_le_0.
    nra. }
  apply hmrr_ex_seq with (seq_mul_vec r' (vec t HMR_coone ++ vec s HMR_one ++ T1) ++ seq_mul_vec (One :: nil) (vec t' HMR_coone ++ vec s' HMR_one ++ D1)).
  { simpl; rewrite seq_mul_One.
    rewrite app_nil_r.
    etransitivity.
    { apply Permutation_Type_app ; [ | reflexivity ].
      etransitivity ; [ apply seq_mul_vec_app_r | ].
      apply Permutation_Type_app; [ reflexivity | apply seq_mul_vec_app_r]. }
    rewrite ? vec_app.
    rewrite <- ? seq_mul_vec_vec_mul_vec.
    Permutation_Type_solve. }
  change  ((seq_mul_vec r' (vec t HMR_coone ++ vec s HMR_one ++ T1) ++ seq_mul_vec (One :: nil) (vec t' HMR_coone ++ vec s' HMR_one ++ D1)) :: nil)
    with
      (map (fun x => snd x ++ seq_mul_vec (fst x) (vec t' HMR_coone ++ vec s' HMR_one ++ D1)) ((One :: nil, seq_mul_vec r' (vec t HMR_coone ++ vec s HMR_one ++ T1)) :: nil)).
  assert { pi'' :  HMR_T (map (fun x : list Rpos * sequent => snd x) ((One :: nil,seq_mul_vec r' (vec t HMR_coone ++ vec s HMR_one ++ T1)) :: nil)) & modal_depth_proof pi'' < modal_depth_proof pi1} as [pi'' Hdiam''].
  { change (map (fun x : list Rpos * sequent => snd x)
                ((One :: nil, seq_mul_vec r' (vec t HMR_coone ++ vec s HMR_one ++ T1)) :: nil))
      with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r' ,vec t HMR_coone ++ vec s HMR_one ++ T1) :: nil)).
    change ((vec t HMR_coone ++ vec s HMR_one ++ T1) :: nil) with (map (fun x => snd x) ((r' ,vec t HMR_coone ++ vec s HMR_one ++ T1) :: nil)) in piG.
    destruct (hmrr_mul_vec ((r', vec t HMR_coone ++ vec s HMR_one ++ T1) :: nil) piG) as [pi'' Hdiam''].
    split with pi''.
    apply Nat.le_lt_trans with (modal_depth_proof piG); assumption. }
  rewrite <- app_nil_r.
  apply Hn with (modal_depth_proof pi'') pi''; try assumption; try reflexivity.
Qed.

(** Proof of Theorem 4.9 *)
Lemma hmrr_M_elim : forall G,
    HMR_T_M G ->
    HMR_T G.
Proof.
  intros G pi; induction pi; try now constructor.
  - assert {L & prod
                  (G = map (fun x => snd x) L)
                  (G = map (fun x => snd x ++ seq_mul_vec (fst x) T2) L)} as [L [Heq1 Heq2]].
    { clear; induction G.
      - split with nil; split; reflexivity.
      - destruct IHG as [L [H1 H2]].
        split with ((nil, a) :: L).
        simpl; split ; [ rewrite H1; reflexivity |  rewrite H2].
        rewrite app_nil_r; reflexivity. }
    apply hmrr_ex_hseq with (G ++ ((T1 ++ T2) :: nil)); [ Permutation_Type_solve | ].
    apply hmrr_C_gen.
    apply hmrr_ex_hseq with (((T1 ++ T2) :: G) ++ G); [ Permutation_Type_solve | ].
    pattern G at 1; rewrite Heq2.
    replace ((T1 ++ T2)
               :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) T2) L)
      with (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) T2) ((One :: nil , T1) :: L)) by (simpl; rewrite app_nil_r; now rewrite seq_mul_One).
    apply hmrr_M_gen; try assumption.
    simpl.
    rewrite <- Heq1; apply IHpi1.
  - now apply hmrr_T with r.
  - now apply hmrr_ex_seq with T1.
  - now apply hmrr_ex_hseq with G.
Qed.
