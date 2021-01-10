(** * Implementation of Section 4.8 *)
Require Import Rpos.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import riesz_logic_List_more.
Require Import RL.hmr.hmr.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.p_hseq.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.invertibility.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.M_elim.
Require Import RL.hmr.tech_lemmas.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Program.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Import EqNotations.

Local Open Scope R_scope.

(** ** Lambda property *)
Lemma hmrr_fuse :
  forall G T A r1 r2,
    HMR_T_M (((r1, A) :: (r2 , A) :: T) :: G) ->
    HMR_T_M (((plus_pos r1 r2, A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can_elim.
  unfold HMR_full.
  change hmr_frag_full with (hmr_frag_add_CAN hmr_frag_full).
  apply hmrr_can_fuse.
  apply HMR_le_frag with hmr_frag_T_M; try assumption.
  repeat split.
Qed.

Lemma hmrr_unfuse :
  forall G T A r1 r2,
    HMR_T_M (((plus_pos r1 r2, A) :: T) :: G) ->
    HMR_T_M (((r1, A) :: (r2 , A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can_elim.
  unfold HMR_full.
  change hmr_frag_full with (hmr_frag_add_CAN hmr_frag_full).
  apply hmrr_can_unfuse.
  apply HMR_le_frag with hmr_frag_T_M; try assumption.
  repeat split.
Qed.

Lemma hmrr_unfuse_gen :
  forall G T D r1 r2,
    HMR_T_M ((hseq.seq_mul (plus_pos r1 r2) D ++ T) :: G) ->
    HMR_T_M ((hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ T) :: G).
Proof.
  intros G T D r1 r2.
  revert T; induction D; intros T pi; try assumption.
  - destruct a as [a A]; simpl in *.
    apply hmrr_ex_seq with ((time_pos r1 a, A) :: (time_pos r2 a, A) :: hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ T); [ Permutation_Type_solve | ].
    apply hmrr_unfuse.
    replace (plus_pos (time_pos r1 a) (time_pos r2 a)) with (time_pos (plus_pos r1 r2) a) by (destruct r1; destruct r2; destruct a; apply Rpos_eq; simpl; nra).
    apply hmrr_ex_seq with (hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ (time_pos (plus_pos r1 r2) a, A) :: T) ; [ Permutation_Type_solve | ].
    apply IHD.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
Qed.

Lemma hmrr_fuse_gen :
  forall G T D r1 r2,
    HMR_T_M ((hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ T) :: G) ->
    HMR_T_M ((hseq.seq_mul (plus_pos r1 r2) D ++ T) :: G).
Proof.
  intros G T D r1 r2.
  revert T; induction D; intros T pi; try assumption.
  - destruct a as [a A]; simpl in *.
    replace (time_pos (plus_pos r1 r2) a) with (plus_pos (time_pos r1 a) (time_pos r2 a)) by (destruct r1; destruct r2; destruct a; apply Rpos_eq; simpl; nra).
    apply hmrr_fuse.
    apply hmrr_ex_seq with (hseq.seq_mul (plus_pos r1 r2) D ++ (time_pos r1 a, A) :: (time_pos r2 a, A) :: T) ; [ Permutation_Type_solve | ].
    apply IHD.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
Qed.

(* begin hide *)
Lemma concat_with_coeff_mul_oadd_Rpos_list_fuse : forall G T H L1 L2,
    length L1 = length L2 ->
    HMR_T_M ((concat_with_coeff_mul G L1 ++ concat_with_coeff_mul G L2 ++ T) :: H) ->
    HMR_T_M ((concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ T) :: H).
Proof.
  intros G T H L1; revert G T H; induction L1; intros G T H L2 Hlen pi; [ destruct L2; inversion Hlen; destruct G; apply pi | ].
  destruct L2; inversion Hlen.
  destruct G; [ apply pi | ].
  destruct a; destruct o; simpl in *.
  - rewrite<- app_assoc; apply hmrr_fuse_gen.
    apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (hseq.seq_mul r s ++ hseq.seq_mul r0 s ++ T)) ; [ Permutation_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (hseq.seq_mul r s ++ T)) ; [ Permutation_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (hseq.seq_mul r s ++ T)) ; [ Permutation_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply IHL1; try assumption.
Qed.
(* end hide *)

Lemma lambda_prop :
  forall G,
    hseq_is_basic G ->
    HMR_T_M G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> None) L) *
            (forall n, sum_weight_with_coeff n G L = 0) *
            (0 <= sum_weight_with_coeff_one G L) *
            (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with ((Some One) :: nil).
    repeat split; try reflexivity.
    + apply Exists_inf_cons_hd.
      intros H; inversion H.
    + intros n.
      simpl; nra.
    + simpl; nra.
    + apply hmrr_INIT.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with (None :: L).
    repeat split; auto.
    simpl; rewrite Hlen; reflexivity.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons ;[ | apply Forall_inf_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with ((oadd_Rpos o o0) :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        destruct o; [ | exfalso; apply H0; reflexivity].
        destruct o0; intros H; inversion H.
      * inversion X1; subst; auto.
        apply Exists_inf_cons_hd.
        destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intro H; inversion H.
    + intros n.
      specialize (Hsum n).
      destruct o; destruct o0; try destruct r; try destruct r0; simpl; simpl in Hsum; nra.
    + destruct o; destruct o0; try destruct r; try destruct r0; simpl; simpl in Hone; nra.
    + destruct o; destruct o0; simpl; simpl in Hind; try assumption.
      apply hmrr_fuse_gen.
      apply Hind.
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      apply seq_basic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (o :: o :: L).
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n.
      specialize (Hsum n).
      destruct o; auto.
      simpl in *.
      rewrite sum_weight_seq_var_app in Hsum.
      rewrite sum_weight_seq_covar_app in Hsum.
      nra.
    + destruct o; auto.
      simpl in *.
      rewrite sum_weight_seq_one_app in Hone.
      rewrite sum_weight_seq_coone_app in Hone.
      nra.
    + destruct o; try assumption.
      simpl in *.
      rewrite only_diamond_seq_app in Hind.
      rewrite hseq.seq_mul_app in Hind.
      rewrite app_assoc; apply Hind.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [[[Hex1 Hsum1] Hone1] Hind1]]].
    { apply Forall_inf_cons ; [ apply seq_basic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct o.
    2:{ split with (None :: L1).
        repeat split; auto. }
    destruct IHpi2 as [L2 [Hlen2 [[[Hex2 Hsum2] Hone2] Hind2]]].
    { apply Forall_inf_cons ; [ apply seq_basic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct o.
    2:{ split with (None :: L2).
        repeat split; auto. }
    split with ((Some (time_pos r r0)) :: oadd_Rpos_list (map (mul_Rpos_oRpos r0) L1) (map (mul_Rpos_oRpos r) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite oadd_Rpos_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_inf_cons_hd.
      intros H; inversion H.
    + intros n; specialize (Hsum1 n); specialize (Hsum2 n); simpl in Hsum1, Hsum2.
      simpl.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      rewrite sum_weight_with_coeff_oadd_Rpos_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_with_coeff_omul_Rpos_list.
      destruct r; destruct r0; simpl in *; nra.
    + simpl; simpl in Hone1, Hone2.
      rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app.
      rewrite sum_weight_with_coeff_one_oadd_Rpos_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_with_coeff_one_omul_Rpos_list.
      destruct r as [r Hr]; destruct r0 as [r0 Hr0]; simpl in *.
      clear - Hr Hr0 Hone1 Hone2.
      apply R_blt_lt in Hr; apply R_blt_lt in Hr0.
      nra.
    + simpl in Hind1, Hind2 |- *.
      rewrite only_diamond_seq_app; rewrite hseq.seq_mul_app.
      rewrite <- (seq_mul_twice (only_diamond_seq T2)).
      replace (time_pos r r0) with (time_pos r0 r) by (destruct r0; destruct r; apply Rpos_eq; simpl; nra).
      rewrite <- seq_mul_twice.
      apply hmrr_ex_seq with ((concat_with_coeff_mul (only_diamond_hseq G) (oadd_Rpos_list (map (mul_Rpos_oRpos r0) L1) (map (mul_Rpos_oRpos r) L2))) ++ (hseq.seq_mul r0 (hseq.seq_mul r (only_diamond_seq T1)) ++ hseq.seq_mul r (hseq.seq_mul r0 (only_diamond_seq T2)))) ; [ Permutation_Type_solve | ].
      apply concat_with_coeff_mul_oadd_Rpos_list_fuse ; [ simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia | ].
      rewrite 2 concat_with_coeff_mul_omul_Rpos_list.
      apply hmrr_ex_seq with (hseq.seq_mul r (hseq.seq_mul r0 (only_diamond_seq T2) ++ (concat_with_coeff_mul (only_diamond_hseq G) L2)) ++ hseq.seq_mul r0 (hseq.seq_mul r (only_diamond_seq T1) ++ (concat_with_coeff_mul (only_diamond_hseq G) L1))) ; [ rewrite ? hseq.seq_mul_app; Permutation_Type_solve | ].
      apply hmrr_M; [ reflexivity | | ];
        eapply hmrr_T; try reflexivity;
          rewrite hseq.seq_mul_twice; rewrite inv_pos_l; rewrite hseq.seq_mul_One; assumption.      
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      apply seq_basic_mul; apply X. }
    destruct L; try now inversion Hlen.
    destruct o.
    2:{ split with (None :: L).
        repeat split; auto. }
    split with (Some (time_pos r0 r) :: L).
    repeat split; auto.
    + apply Exists_inf_cons_hd; intros H; inversion H.
    + destruct r; destruct r0; simpl in *; intros n; specialize (Hsum n);rewrite sum_weight_seq_var_mul in Hsum; rewrite sum_weight_seq_covar_mul in Hsum; simpl in *.
      nra.
    + destruct r; destruct r0; simpl in *; rewrite sum_weight_seq_one_mul in Hone; rewrite sum_weight_seq_coone_mul in Hone.
      simpl in *; nra.
    + simpl in *.
      rewrite<- hseq.seq_mul_twice; rewrite only_diamond_seq_mul.
      apply Hind.
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
        simpl in Hsum.
        destruct o; nra.
      * apply Nat.eqb_neq in H.
        rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
        rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
        destruct o; simpl in Hsum; auto.
        nra.
    + destruct L; try now inversion Hlen.
      simpl in *; rewrite ? sum_weight_seq_app.
      simpl in *; rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      destruct o; auto.
      rewrite ? sum_weight_seq_coone_vec_neq; try now (intros H; inversion H).
      rewrite ? sum_weight_seq_one_vec_neq; try now (intros H; inversion H).
      nra.
    + unfold only_diamond_hseq; fold only_diamond_hseq.
      rewrite 2 only_diamond_seq_app.
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
    split with (oadd_Rpos o o0 :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intros H; inversion H.
      * inversion X; subst; auto.
        apply Exists_inf_cons_hd; 
          destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intros H; inversion H.
    + intros n.
      simpl.
      specialize (Hsum n).
      destruct o; destruct o0; try destruct r; try destruct r0; simpl in *; nra.
    + destruct o; destruct o0; try destruct r; try destruct r0; simpl in *; nra.
    + destruct o; destruct o0; try apply Hind.
      simpl in *.
      apply hmrr_fuse_gen; apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_inf_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n; specialize (Hsum n).
      destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite ? sum_weight_seq_var_app; rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_var_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_covar_vec_neq; try (intros H; now inversion H).
      nra.
    + destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite ? sum_weight_seq_one_vec_one_eq; rewrite ? sum_weight_seq_coone_vec_coone_eq.
      rewrite ? sum_weight_seq_one_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_coone_vec_neq; try (intros H; now inversion H).
      apply (Rmult_le_compat_l (projT1 r1)) in r0.
      2:{ destruct r1 as [r1 Hr1]; simpl.
          clear - Hr1; apply R_blt_lt in Hr1.
          nra. }
      nra.
    + destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite 2 only_diamond_seq_app; rewrite 2 hseq.seq_mul_app.
      rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_vec_coone.
      rewrite 2 hseq.seq_mul_vec_mul_vec.
      rewrite<- ? app_assoc.
      apply hmrr_one; try assumption.
      rewrite 2 hseq.mul_vec_sum_vec.
      clear - r0.
      destruct r1 as [r1 Hr1]; simpl; apply R_blt_lt in Hr1; nra.
  - split with (Some One :: nil).
    repeat split; auto.
    + apply Exists_inf_cons_hd; intros H; inversion H.
    + intros n.
      simpl.
      rewrite ? sum_weight_seq_var_app; rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_var_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_covar_vec_neq; try (intros H; now inversion H).
      rewrite sum_weight_seq_var_seq_diamond; rewrite sum_weight_seq_covar_seq_diamond; nra.
    + simpl.
      rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite sum_weight_seq_one_vec_one_eq; rewrite sum_weight_seq_coone_vec_coone_eq.
      rewrite ? sum_weight_seq_one_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_coone_vec_neq; try (intros H; now inversion H).
      rewrite sum_weight_seq_one_seq_diamond; rewrite sum_weight_seq_coone_seq_diamond; nra.
    + simpl.
      rewrite hseq.seq_mul_One.
      rewrite ? only_diamond_seq_app.
      rewrite only_diamond_seq_vec_coone; rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_only_diamond.
      rewrite app_nil_r; apply pi.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_inf_cons; try assumption.
      apply seq_basic_perm with T2; [ Permutation_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    + intro n; specialize (Hsum n).
      destruct o; simpl in *; auto.
      rewrite <- (sum_weight_seq_var_perm _ _ _ p); rewrite <- (sum_weight_seq_covar_perm _ _ _ p); apply Hsum.
    + destruct o; simpl in *; auto.
      rewrite <- (sum_weight_seq_one_perm _ _ p); rewrite <- (sum_weight_seq_coone_perm _ _ p); apply Hone.
    + destruct o; simpl in *; auto.
      eapply hmrr_ex_seq; [ | apply Hind].
      apply Permutation_Type_app; try reflexivity.
      apply hseq.seq_mul_perm.
      apply only_diamond_seq_perm.
      apply p.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply hseq_basic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_with_coeff_perm_r G H L p Hlen) as [L' [Hperm' [[Hsum' Hone'] Hperm'']]].
    split with L'.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      etransitivity ; [ | apply p].
      etransitivity ; [ | apply Hlen].
      symmetry; apply Hperm'.
    + apply Exists_inf_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- (Hsum' n); apply Hsum.
    + rewrite <- Hone'; apply Hone.
    + eapply hmrr_ex_seq ; [ | apply Hind].
      apply Hperm''.
  - inversion f.
Qed.

Lemma lambda_prop_inv :
  forall G,
    hseq_is_basic G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> None) L) *
            (forall n, sum_weight_with_coeff n G L = 0) *
            (0 <= sum_weight_with_coeff_one G L) *
            (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))} ->
    HMR_T_M G.
Proof.
  enough (forall G H,
             hseq_is_basic G ->
             hseq_is_basic H ->
             { L &
               prod (length L = length G)
                    ((Exists_inf (fun x => x <> None) L) *
                     (forall n, (sum_weight_var n H - sum_weight_covar n H) + sum_weight_with_coeff n G L = 0) *
                     (0 <= (sum_weight_one H - sum_weight_coone H) + sum_weight_with_coeff_one G L) *
                     (HMR_T_M ((flat_map only_diamond_seq H ++ concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))} + HMR_T_M H ->
             HMR_T_M (H ++  G)).
  { intros G Hat [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_inf_nil.
    - left.
      split with L.
      repeat split; auto.
      + intros n; simpl; specialize (Hsum n); nra.
      + simpl; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [[L [Hlen [[[Hex Hsum] Hone] Hind]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_inf_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type L (r :: La ++ Lb)) as Hperm by (rewrite HeqL ; Permutation_Type_solve).
    destruct (sum_weight_with_coeff_perm_l G _ _ Hperm) as [G' [HpermG [[Hsum' Hone'] Hpc]]].
    { lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hmrr_ex_hseq with (T :: H ++ G') ; [ Permutation_Type_solve | ].
    destruct r ; [ | exfalso; apply Hp; reflexivity].
    apply hmrr_T with r; try reflexivity.
    change (hseq.seq_mul r T :: H ++ G')
      with
        ((hseq.seq_mul r T :: H) ++ G').
    assert (hseq_is_basic (T :: G')) as HatG'.
    { apply Forall_inf_Permutation_Type with G; try assumption. }
    apply IHn.
    + apply Permutation_Type_length in HpermG.
      rewrite HpermG in Heqn; simpl in Heqn; inversion Heqn; auto.
    + inversion HatG'; auto.
    + apply Forall_inf_cons; auto.
      apply seq_basic_mul; now inversion HatG'.
    + destruct (Forall_inf_Exists_inf_dec (fun x : option Rpos => x = None)) with (La ++ Lb).
      { intros x.
        destruct x ; [ right; intros H'; inversion H' | left; reflexivity]. }
      * right.
        apply basic_proof_all_eq.
        -- apply seq_basic_mul.
           apply hseq_basic_perm with _ (T :: G') in HatG; try assumption.
           inversion HatG; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite (sum_weight_with_coeff_all_0 _ (La ++ Lb)) in Hsum'; try assumption.
           rewrite sum_weight_seq_var_mul; rewrite sum_weight_seq_covar_mul; simpl.
           nra.
        -- simpl in *.
           rewrite (sum_weight_with_coeff_one_all_0 _ (La ++ Lb)) in Hone'; try assumption.
           rewrite sum_weight_seq_one_mul; rewrite sum_weight_seq_coone_mul; simpl.
           nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           rewrite HeqL.
           simpl.
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           apply Permutation_Type_app; [ | reflexivity].
           rewrite concat_with_coeff_mul_only_diamond.
           apply only_diamond_seq_perm.
           rewrite HeqL in Hpc; etransitivity ; [ apply Hpc | ].
           simpl.
           rewrite concat_with_coeff_mul_all_0; try assumption.
           rewrite app_nil_r; reflexivity.
      * left; split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite ? app_length.
           rewrite ? app_length in Hlen; simpl in Hlen.
           lia.
        -- apply e.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_seq_var_mul; rewrite sum_weight_seq_covar_mul; simpl.
           nra.
        -- simpl in *.
           rewrite sum_weight_seq_one_mul; rewrite sum_weight_seq_coone_mul; simpl.
           nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           rewrite HeqL.
           simpl.
           etransitivity ; [ | apply Permutation_Type_app_swap ].
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           rewrite app_assoc.
           apply Permutation_Type_app; [ | reflexivity].
           rewrite 2 concat_with_coeff_mul_only_diamond.
           rewrite <- only_diamond_seq_app.
           apply only_diamond_seq_perm.
           rewrite HeqL in Hpc; etransitivity ; [ apply Hpc | ].
           simpl.
           apply Permutation_Type_app_swap.
  - eapply hmrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hmrr_W_gen.
    apply pi.
Qed.

(** ** Decidablity *)
(* begin hide *)
(* Preliminary work necessary for the decidability result *)
Fixpoint pos_indexes (L : list (option Rpos)) :=
  match L with
  | nil => nil
  | (Some r :: L) => 0%nat :: map S (pos_indexes L)
  | (None :: L) => map S (pos_indexes L)
  end.

Lemma In_inf_pos_indexes:
  forall i L,
    In_inf i (pos_indexes L) ->
    (i < length L)%nat.
Proof.
  intros i L; revert i; induction L; intros i Hin; try now inversion Hin.
  destruct a; simpl in Hin; try (inversion Hin; subst).
  - simpl; lia.
  - simpl; destruct i.
    + exfalso; apply not_0_In_inf_map_S in X; apply X.
    + apply In_inf_map_S_inv in X.
      specialize (IHL i X).
      lia.
  - simpl; destruct i.
    + exfalso; apply not_0_In_inf_map_S in Hin; apply Hin.
    + apply In_inf_map_S_inv in Hin.
      specialize (IHL i Hin).
      lia.
Qed.

Lemma pos_indexes_nth : forall L i,
    In_inf i (pos_indexes L) ->
    {r & nth i L None = Some r}.
Proof.
  induction L; intros i Hin; try now exfalso.
  destruct a.
  - destruct i.
    + split with r; auto.
    + simpl; apply IHL.
      apply In_inf_map_S_inv.
      inversion Hin; [ exfalso; inversion H | ].
      apply X.
  - destruct i.
    + exfalso.
      apply not_0_In_inf_map_S with (pos_indexes L).
      apply Hin.
    + apply IHL; apply In_inf_map_S_inv; apply Hin.
Qed.

Lemma pos_indexes_Forall_inf : forall L,
    Forall_inf (fun n : nat => (n < length L)%nat) (pos_indexes L).
Proof.
  induction L; [ apply Forall_inf_nil | ].
  simpl.
  destruct a.
  - apply Forall_inf_cons.
    + lia.
    + apply Forall_inf_lt_map_S.
      apply IHL.
  - apply Forall_inf_lt_map_S; apply IHL.
Qed.

Lemma pos_indexes_not_In_inf : forall L i,
    (i < length L)%nat ->
    (In_inf i (pos_indexes L) -> False) ->
    (nth i L None = None).
Proof.
  induction L; intros i Hlen H; try now inversion Hlen.
  simpl in H.
  destruct a.
  - destruct i; [ exfalso; apply H; left; lia | ].
    simpl.
    apply IHL; [ simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    right.
    apply in_inf_map.
    apply Hin.
  - destruct i; [ auto | ].
    simpl.
    apply IHL; [simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    apply in_inf_map; apply Hin.
Qed.

Lemma pos_indexes_order : forall L,
    forall i j : nat,
      (j < length (pos_indexes L))%nat ->
      (i < j)%nat -> (nth i (pos_indexes L) 0 < nth j (pos_indexes L) 0)%nat.
Proof.
  induction L; intros i j Hlen Hlt ; [ now inversion Hlen | ].
  simpl.
  destruct a.
  - simpl in Hlen.
    destruct j; [inversion Hlt | ].
    destruct i; simpl.
    + rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
      rewrite map_nth.
      lia.
    + rewrite nth_indep with _ _ _ _ 1%nat ; [ | lia].
      rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
      rewrite ? map_nth.
      apply lt_n_S.
      rewrite map_length in Hlen.
      apply IHL; lia.
  - simpl in Hlen.
    rewrite nth_indep with _ _ _ _ 1%nat ; [ | lia].
    rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
    rewrite ? map_nth.
    apply lt_n_S.
    rewrite map_length in Hlen.
    apply IHL; lia.
Qed.

Lemma pos_indexes_cond : forall L v,
    (forall i j : nat,
      (j < length v)%nat ->
      (i < j)%nat -> (nth i v 0 < nth j v 0)%nat) ->
    (forall i,
        (i < length v)%nat ->
        (nth i v 0 < length L)%nat) ->
    (forall i,
        In_inf i v ->
        nth i L None <> None) ->
    (forall i,
        (i < length L)% nat ->
        nth i L None <> None ->
        In_inf i v) ->
    v = pos_indexes L.
Proof.
  induction L; intros v H1 H2 H3 H4.
  - destruct v; auto.
    exfalso.
    apply (H3 n); [ left; auto |] .
    destruct n; auto.
  - destruct a.
    + simpl.
      destruct v.
      { exfalso.
        apply in_inf_nil with _ 0%nat.
        apply H4; simpl; try lia.
        intros H; inversion H. }
      destruct n.
      2:{ exfalso.
          apply (all_neq_not_In_inf (S n :: v) 0%nat).
          - apply forall_Forall_inf.
            intros x Hin.
            apply not_eq_sym.
            apply Nat.lt_neq.
            apply In_inf_nth with _ _ _ 0%nat in Hin as [j Hlenj Heqj].
            rewrite <- Heqj.
            destruct j; try (simpl; lia).
            apply Nat.lt_trans with (S n); try lia.
            change (S n) with (nth 0%nat (S n :: v) 0%nat) at 1.
            apply H1; simpl in *; try lia.
          - apply H4; simpl in *; try lia.
            intros H; inversion H. }
      destruct all_neq_0_map_S with v.
      * apply forall_Forall_inf.
        intros x Hin.
        apply not_eq_sym.
        apply Nat.lt_neq.
        apply In_inf_nth with _ _ _ 0%nat in Hin as [j Hlenj Heqj].
        rewrite <- Heqj.
        change (nth j v 0)%nat with (nth (S j) (0 :: v) 0)%nat.
        change 0%nat with (nth 0 (0 :: v) 0)%nat.
        apply H1; simpl in *; lia.
      * rewrite e.
        rewrite (IHL x); auto.
        -- intros i j Hltj Hltij.
           apply lt_S_n.
           rewrite <- map_nth.
           rewrite <- (map_nth _ _ _ j).
           rewrite nth_indep with _ _ _ _ 0%nat ; [ | rewrite map_length; lia].
           rewrite nth_indep with _ _ j _ 0%nat ; [ | rewrite map_length; lia].
           rewrite <- e.
           change (nth i v 0)%nat with (nth (S i) (0 :: v) 0)%nat.
           change (nth j v 0)%nat with (nth (S j) (0 :: v) 0)%nat.
           rewrite <- (map_length S) in Hltj.
           rewrite <- e in Hltj.
           apply H1; simpl in *; try lia.
        -- intros i Hlti.
           apply lt_S_n.
           rewrite <- map_nth.
           rewrite nth_indep with _ _ _ _ 0%nat ; [ | rewrite map_length; lia].
           rewrite <- e.
           change (nth i v 0)%nat with (nth (S i) (0 :: v) 0)%nat.
           rewrite <- (map_length S) in Hlti.
           rewrite <- e in Hlti.
           apply H2; simpl in *; try lia.
        -- intros i Hin.
           apply In_inf_map_S in Hin.
           rewrite <- e in Hin.
           change (nth i L None) with (nth (S i) (Some r :: L) None).
           apply H3.
           right; auto.
        -- intros i Hlti Hneq.
           change (nth i L None) with (nth (S i) (Some r :: L) None) in Hneq.
           apply lt_n_S in Hlti.
           specialize (H4 (S i) Hlti Hneq).
           rewrite e in H4.
           inversion H4; [ inversion H |].
           apply In_inf_map_S_inv in X.
           apply X.
    + destruct all_neq_0_map_S with v.
      * apply forall_Forall_inf.
        intros x Hin.
        apply not_eq_sym.
        intros H.
        subst.
        specialize (H3 _ Hin); simpl in H3.
        contradiction.
      * simpl.
        rewrite e.
        rewrite (IHL x); auto.
        -- intros i j Hltj Hltij.
           apply lt_S_n.
           rewrite <- map_nth.
           rewrite <- (map_nth _ _ _ j).
           rewrite nth_indep with _ _ _ _ 0%nat ; [ | rewrite map_length; lia].
           rewrite nth_indep with _ _ j _ 0%nat ; [ | rewrite map_length; lia].
           rewrite <- e.
           change (nth i v 0)%nat with (nth (S i) (0 :: v) 0)%nat.
           change (nth j v 0)%nat with (nth (S j) (0 :: v) 0)%nat.
           rewrite <- (map_length S) in Hltj.
           rewrite <- e in Hltj.
           apply H1; simpl in *; try lia.
        -- intros i Hlti.
           apply lt_S_n.
           rewrite <- map_nth.
           rewrite nth_indep with _ _ _ _ 0%nat ; [ | rewrite map_length; lia].
           rewrite <- e.
           change (nth i v 0)%nat with (nth (S i) (0 :: v) 0)%nat.
           rewrite <- (map_length S) in Hlti.
           rewrite <- e in Hlti.
           apply H2; simpl in *; try lia.
        -- intros i Hin.
           apply In_inf_map_S in Hin.
           rewrite <- e in Hin.
           change (nth i L None) with (nth (S i) (None :: L) None).
           apply H3.
           auto.
        -- intros i Hlti Hneq.
           change (nth i L None) with (nth (S i) (None :: L) None) in Hneq.
           apply lt_n_S in Hlti.
           specialize (H4 (S i) Hlti Hneq).
           rewrite e in H4.
           apply In_inf_map_S_inv in H4.
           apply H4.
Qed.    

(* get a real number x and convert |x| to oRpos *)
Definition R_to_oRpos x :=
  match R_order_dec x with
              | R_is_gt _ H => Some (existT (fun x => 0 <? x = true) x H)
              | R_is_lt _ H => Some (existT (fun x => 0 <? x = true) (- x) H)
              | R_is_null _ _ => None
  end.

Definition eval_to_oRpos val f := R_to_oRpos (FOL_R_term_sem val f).

Definition oRpos_to_R (o : option Rpos) :=
  match o with
  | None => 0
  | Some r => projT1 r
  end.

Lemma R_to_oRpos_oRpos_to_R :
  forall o,
    R_to_oRpos (oRpos_to_R o) = o.
Proof.
  destruct o; unfold R_to_oRpos; simpl;
    [ | case (R_order_dec 0); intros e; simpl; try reflexivity; exfalso; apply R_blt_lt in e; lra].
  destruct r as [r Hr]; simpl.
  case (R_order_dec r); intros e;
    try (replace e with Hr by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec); reflexivity);
    exfalso; apply R_blt_lt in Hr; try apply R_blt_lt in e; lra.
Qed.

Lemma oRpos_to_R_to_Rpos : forall r (Hr : 0 <? projT1 r = true),
    existT _ (oRpos_to_R (Some r)) Hr = r.
Proof.
  intros [r Hr] H.
  apply Rpos_eq; reflexivity.
Qed.

Lemma map_oRpos_to_R_all_pos:
  forall L val i, Forall_inf (fun x => 0 <= FOL_R_term_sem (upd_val_vec val (seq i (length L)) (map oRpos_to_R L)) x) (map FOL_R_var (seq i (length L))).
Proof.
  induction L; intros val i; [ apply Forall_inf_nil | ].
  simpl.
  apply Forall_inf_cons; [ | apply IHL].
  rewrite FOL_R_term_sem_upd_val_vec_not_in.
  2:{ apply not_In_inf_seq; lia. }
  rewrite upd_val_eq.
  clear.
  destruct a; simpl; try (destruct r as [r Hr]; simpl; apply R_blt_lt in Hr); lra.
Qed.

Lemma eval_to_oRpos_eq :
  forall val vr k,
    map (eval_to_oRpos (upd_val_vec val (seq k (length vr)) vr)) (map FOL_R_var (seq k (length vr))) = map R_to_oRpos vr.
Proof.
  intros val vr; revert val; induction vr; intros val k; auto.
  simpl.
  rewrite (IHvr _ (S k)).
  unfold eval_to_oRpos.
  rewrite FOL_R_term_sem_upd_val_vec_not_in.
  2:{ apply not_In_inf_seq; lia. }
  unfold upd_val.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma eval_p_seq_upd_val_vec_nth :
  forall val G L k,
    length G = length L ->
    (max_var_weight_p_hseq G < k)%nat ->
    eval_p_sequent (upd_val_vec val (seq k (length L)) (map oRpos_to_R L)) (flat_map (fun i => seq_mul (FOL_R_var (k + i)) (nth i G nil)) (pos_indexes L)) = concat_with_coeff_mul (map (eval_p_sequent val) G) L.
Proof.
  intros val G; revert val; induction G; intros val [ | o L] k Hlen Hlt; auto; try now inversion Hlen.
  destruct o.
  - simpl pos_indexes; simpl map.
    rewrite (cons_is_app 0%nat); rewrite flat_map_app.
    rewrite eval_p_sequent_app.
    simpl (flat_map _ (0%nat :: nil)).
    rewrite app_nil_r.
    simpl upd_val_vec.
    rewrite flat_map_concat_map.
    rewrite map_map.
    rewrite <- flat_map_concat_map.
    replace (flat_map (fun x : nat => seq_mul (FOL_R_var (k + S x)) (nth (S x) (a :: G) nil)) (pos_indexes L)) with (flat_map (fun x : nat => seq_mul (FOL_R_var ((S k) + x)) (nth x G nil)) (pos_indexes L)).
    2:{ apply flat_map_ext.
        intros a'.
        simpl.
        replace (S (k + a')) with (k + S a')%nat by lia.
        reflexivity. }
    simpl in Hlt.
    rewrite IHG; [ | simpl in Hlen; lia | lia].
    simpl.
    rewrite eval_p_sequent_upd_val_vec_lt.
    2:{ apply forall_Forall_inf.
        intros x Hin.
        replace (k + 0)%nat with k by lia.
        assert (k < x)%nat.
        { apply In_inf_seq_le_start in Hin.
          lia. }
        destruct a; [ simpl; lia | ].
        rewrite max_var_weight_p_seq_seq_mul; simpl max_var_FOL_R_term; try lia.
        intros H'; inversion H'. }
    rewrite eval_p_hseq_upd_val_lt; try lia.
    replace (eval_p_sequent (upd_val val k (projT1 r)) (seq_mul (FOL_R_var (k + 0)) a))
      with (hseq.seq_mul r (eval_p_sequent val a)); auto.
    apply Nat.max_lub_lt_iff in Hlt as [Hlt _].
    clear - Hlt.
    revert Hlt; induction a; intros Hlt; auto.
    destruct a as [a A].
    simpl in *.
    replace (k + 0)%nat with k by lia.
    rewrite upd_val_eq.
    rewrite upd_val_term_lt; try lia.
    sem_is_pos_decomp val a;
      assert {H & R_order_dec (projT1 r * FOL_R_term_sem val a) = H} as [H HeqH] by (split with (R_order_dec (projT1 r * FOL_R_term_sem val a)); reflexivity); destruct H as [H | H | H];
        rewrite ? HeqH; revert H HeqH; intros era Hera ea Hea; auto;
          try (exfalso;
               clear - era ea;
               destruct r as [r Hr]; simpl in *; apply R_blt_lt in Hr;
               try (apply R_blt_lt in era);
               try (apply R_blt_lt in ea);
               nra);
          simpl; try rewrite IHa; try lia;
            try (replace (k + 0)%nat with k by lia); auto.
    + replace (time_pos r (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) ea))
        with (existT (fun x : R => (0 <? x) = true) (projT1 r * FOL_R_term_sem val a) era); auto.
      apply Rpos_eq; destruct r; simpl; lra.
    + replace (time_pos r (existT (fun x : R => (0 <? x) = true) (- FOL_R_term_sem val a) ea))
        with (existT (fun x : R => (0 <? x) = true) (- (projT1 r * FOL_R_term_sem val a)) era); auto.
      apply Rpos_eq; destruct r; simpl; lra.
  - simpl pos_indexes.
    simpl concat_with_coeff_mul.
    simpl upd_val_vec.
    rewrite flat_map_concat_map.
    rewrite map_map.
    rewrite <- flat_map_concat_map.
    replace (flat_map (fun x : nat => seq_mul (FOL_R_var (k + S x)) (nth (S x) (a :: G) nil)) (pos_indexes L)) with (flat_map (fun x : nat => seq_mul (FOL_R_var ((S k) + x)) (nth x G nil)) (pos_indexes L)).
    2:{ apply flat_map_ext.
        intros a'.
        simpl.
        replace (S (k + a')) with (k + S a')%nat by lia.
        reflexivity. }
    rewrite IHG; simpl in*; try lia.
    rewrite eval_p_hseq_upd_val_lt; try lia.
    reflexivity.    
Qed.

Fixpoint p_sum_weight_var_with_coeff n G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_var n T) +R p_sum_weight_var_with_coeff n G L
  end.

Lemma p_sum_weight_var_with_coeff_lt_max_var : forall n G L val,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) = 0.
Proof.
  intros n; induction G; intros L val Hlt; destruct L; auto.
  simpl in *.
  simpl; try rewrite sum_weight_p_seq_var_lt_max_var; try lia;
    rewrite IHG; try lia;
      lra.
Qed.

Lemma p_sum_weight_var_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_var_with_coeff n (G1 ++ G2) L = p_sum_weight_var_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_var_with_coeff_app2 : forall val n G1 G2 L1 L2,
    (length L1 = length G1) ->
    FOL_R_pred_sem val (p_sum_weight_var_with_coeff n (G1 ++ G2) (L1 ++ L2) =R p_sum_weight_var_with_coeff n G1 L1 +R p_sum_weight_var_with_coeff n G2 L2).
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_var_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_var_with_coeff n G (L1 ++ L2) = p_sum_weight_var_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint p_sum_weight_covar_with_coeff n G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_covar n T) +R p_sum_weight_covar_with_coeff n G L
  end.

Lemma p_sum_weight_covar_with_coeff_lt_max_covar : forall n G L val,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L) = 0.
Proof.
  intros n; induction G; intros L val Hlt; destruct L; auto.
  simpl in *.
  simpl; try rewrite sum_weight_p_seq_covar_lt_max_var; try lia;
    rewrite IHG; try lia;
      lra.
Qed.

Lemma p_sum_weight_covar_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_covar_with_coeff n (G1 ++ G2) L = p_sum_weight_covar_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_covar_with_coeff_app2 : forall val n G1 G2 L1 L2,
    (length L1 = length G1) ->
    FOL_R_pred_sem val (p_sum_weight_covar_with_coeff n (G1 ++ G2) (L1 ++ L2) =R p_sum_weight_covar_with_coeff n G1 L1 +R p_sum_weight_covar_with_coeff n G2 L2).
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_covar_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_covar_with_coeff n G (L1 ++ L2) = p_sum_weight_covar_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint p_sum_weight_one_with_coeff G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_one T) +R p_sum_weight_one_with_coeff G L
  end.

Lemma p_sum_weight_one_with_coeff_app1 : forall G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_one_with_coeff (G1 ++ G2) L = p_sum_weight_one_with_coeff G1 L.
Proof.
  induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_one_with_coeff_app2 : forall val G1 G2 L1 L2,
    (length L1 = length G1) ->
    FOL_R_pred_sem val (p_sum_weight_one_with_coeff (G1 ++ G2) (L1 ++ L2) =R p_sum_weight_one_with_coeff G1 L1 +R p_sum_weight_one_with_coeff G2 L2).
Proof.
  induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_one_with_coeff_app3 : forall G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_one_with_coeff G (L1 ++ L2) = p_sum_weight_one_with_coeff G L1.
Proof.
  induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint p_sum_weight_coone_with_coeff G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_coone T) +R p_sum_weight_coone_with_coeff G L
  end.

Lemma p_sum_weight_coone_with_coeff_app1 : forall G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_coone_with_coeff (G1 ++ G2) L = p_sum_weight_coone_with_coeff G1 L.
Proof.
  induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_coone_with_coeff_app2 : forall val G1 G2 L1 L2,
    (length L1 = length G1) ->
    FOL_R_pred_sem val (p_sum_weight_coone_with_coeff (G1 ++ G2) (L1 ++ L2) =R p_sum_weight_coone_with_coeff G1 L1 +R p_sum_weight_coone_with_coeff G2 L2).
Proof.
  induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_coone_with_coeff_app3 : forall G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_coone_with_coeff G (L1 ++ L2) = p_sum_weight_coone_with_coeff G L1.
Proof.
  induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Lemma eval_to_oRpos_to_R_eq : forall L val i,
    Forall_inf (fun x => 0 <= FOL_R_term_sem (upd_val_vec val (seq i (length L)) (map oRpos_to_R L)) x) (map FOL_R_var (seq i (length L))) ->
    map (eval_to_oRpos (upd_val_vec val (seq i (length L)) (map oRpos_to_R L))) (map FOL_R_var (seq i (length L))) = L.
Proof.
  induction L; intros val i Hall.
  - reflexivity.
  - inversion Hall; subst.
    simpl.
    rewrite IHL; auto.
    unfold eval_to_oRpos.
    rewrite FOL_R_term_sem_upd_val_vec_not_in.
    2:{ apply not_In_inf_seq; lia. }
    clear - H0.
    simpl in H0.
    rewrite upd_val_vec_not_in in H0.
    2:{ apply not_In_inf_seq; lia. }
    rewrite upd_val_eq in H0 |-*.
    case_eq (R_order_dec (oRpos_to_R a));
      intros e He;
      [ | exfalso; clear - H0 e; apply R_blt_lt in e | ]; try lra.
    + destruct a;
        simpl in H0;
        [ | exfalso; clear - e; apply R_blt_lt in e; simpl in e; lra].
      rewrite R_to_oRpos_oRpos_to_R; reflexivity.
    + rewrite R_to_oRpos_oRpos_to_R; reflexivity.
Qed.

Fixpoint p_concat_with_coeff_mul G L :=
  match G, L with
  | _, nil => nil
  | nil, _ => nil
  | T :: G , r :: L => seq_mul r T ++ p_concat_with_coeff_mul G L
  end.

Lemma p_concat_with_coeff_mul_only_diamond : forall G L,
    p_concat_with_coeff_mul (only_diamond_p_hseq G) L = only_diamond_p_seq (p_concat_with_coeff_mul G L).
Proof.
  induction G; intros L; destruct L; auto.
  simpl; rewrite IHG; auto.
  rewrite only_diamond_p_seq_app.
  rewrite only_diamond_p_seq_mul; reflexivity.
Qed.

Lemma FOL_R_term_sem_eval_p_sequent : forall val n T,
    FOL_R_term_sem val (sum_weight_p_seq_var n T) - FOL_R_term_sem val (sum_weight_p_seq_covar n T) = sum_weight_seq_var n (eval_p_sequent val T) - sum_weight_seq_covar n (eval_p_sequent val T) .
Proof.
  intros val n; induction T; simpl; try reflexivity.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl;
    destruct A; simpl; try case (n =? n0); simpl; try rewrite IHT; try lra.
Qed.

Lemma FOL_R_term_sem_eval_p_hseq : forall val n G L,
    Forall_inf (fun x => 0 <= FOL_R_term_sem val x) L ->
    FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) - FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L) = sum_weight_var_with_coeff n (map (eval_p_sequent val) G) (map (eval_to_oRpos val) L) - sum_weight_covar_with_coeff n (map (eval_p_sequent val) G) (map (eval_to_oRpos val) L).
Proof.
  intros val n; induction G; intros L Hall; destruct Hall; simpl; try reflexivity.
  specialize (IHG l Hall).
  unfold eval_to_oRpos; unfold R_to_oRpos.
  sem_is_pos_decomp val x; intros e' He'; simpl ; [ | exfalso; clear - r e'; apply R_blt_lt in e' |  ]; try lra.
  - transitivity
      (FOL_R_term_sem val x * (FOL_R_term_sem val (sum_weight_p_seq_var n a) - FOL_R_term_sem val (sum_weight_p_seq_covar n a)) +
       (FOL_R_term_sem val (p_sum_weight_var_with_coeff n G l) - FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G l))); try lra.
    rewrite IHG; rewrite FOL_R_term_sem_eval_p_sequent.
    unfold eval_to_oRpos; unfold R_to_oRpos.
    lra.
  - rewrite e'.
    unfold eval_to_oRpos in IHG; unfold R_to_oRpos in IHG.
    lra.
Qed.

Lemma FOL_R_term_sem_eval_p_sequent_one : forall val T,
    FOL_R_term_sem val (sum_weight_p_seq_one T) - FOL_R_term_sem val (sum_weight_p_seq_coone T) = sum_weight_seq_one (eval_p_sequent val T) - sum_weight_seq_coone (eval_p_sequent val T) .
Proof.
  intros val; induction T; simpl; try reflexivity.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl;
    destruct A;  simpl; try rewrite IHT; try lra.
Qed.

Lemma FOL_R_term_sem_eval_p_hseq_one : forall val G L,
    Forall_inf (fun x => 0 <= FOL_R_term_sem val x) L ->
    FOL_R_term_sem val (p_sum_weight_one_with_coeff G L) - FOL_R_term_sem val (p_sum_weight_coone_with_coeff G L) = sum_weight_one_with_coeff (map (eval_p_sequent val) G) (map (eval_to_oRpos val) L) - sum_weight_coone_with_coeff (map (eval_p_sequent val) G) (map (eval_to_oRpos val) L).
Proof.
  intros val; induction G; intros L Hall; destruct Hall; simpl; try reflexivity.
  specialize (IHG l Hall).
  unfold eval_to_oRpos; unfold R_to_oRpos.
  sem_is_pos_decomp val x; intros e' He'; simpl ; [ | exfalso; clear - r e'; apply R_blt_lt in e' |  ]; try lra.
  - transitivity
      (FOL_R_term_sem val x * (FOL_R_term_sem val (sum_weight_p_seq_one a) - FOL_R_term_sem val (sum_weight_p_seq_coone a)) +
       (FOL_R_term_sem val (p_sum_weight_one_with_coeff G l) - FOL_R_term_sem val (p_sum_weight_coone_with_coeff G l))); try lra.
    rewrite IHG; rewrite FOL_R_term_sem_eval_p_sequent_one.
    unfold eval_to_oRpos; unfold R_to_oRpos.
    lra.
  - rewrite e'.
    unfold eval_to_oRpos in IHG; unfold R_to_oRpos in IHG.
    lra.
Qed.

Lemma FOL_R_term_sem_upd_val_vec_lt : forall val a vx vr,
    Forall_inf (fun x => max_var_FOL_R_term a < x)%nat vx ->
    FOL_R_term_sem (upd_val_vec val vx vr) a = FOL_R_term_sem val a.
Proof.
  intros val; induction a; intros vx vr Hall.
  - simpl.
    apply upd_val_vec_not_in.
    intros Hin.
    apply (Forall_inf_forall Hall) in Hin.
    simpl in Hin; lia.
  - reflexivity.
  - simpl; rewrite IHa1; [ rewrite IHa2 | ]; try reflexivity; refine (Forall_inf_arrow _ _ Hall);
      intros a Hlt; simpl in Hlt; lia.
  - simpl; rewrite IHa1; [ rewrite IHa2 | ]; try reflexivity; refine (Forall_inf_arrow _ _ Hall);
      intros a Hlt; simpl in Hlt; lia.
Qed.

Lemma eval_p_hseq_upd_val_vec_lt : forall val G vx vr,
    Forall_inf (fun x => max_var_weight_p_hseq G < x)%nat vx ->
    map (eval_p_sequent (upd_val_vec val vx vr)) G = map (eval_p_sequent val) G.
Proof.
  intros val; induction G; intros vx vr Hall; simpl; try reflexivity.
  rewrite eval_p_sequent_upd_val_vec_lt ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  rewrite IHG ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  reflexivity.
Qed.

Lemma sum_weight_with_coeff_eval_eq : forall val n G L,
    sum_weight_var_with_coeff n (map (eval_p_sequent val) G) L - sum_weight_covar_with_coeff n (map (eval_p_sequent val) G) L = FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) (map oRpos_to_R L)) (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))) - FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) (map oRpos_to_R L)) (p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))).
Proof.
  intros val n G L.
  rewrite FOL_R_term_sem_eval_p_hseq; auto.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_to_oRpos_to_R_eq.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_p_hseq_upd_val_vec_lt; try reflexivity.
  apply forall_Forall_inf.
  intros x Hin.
  case_eq (max_var_weight_p_hseq G <? x)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H]; auto.
  exfalso.
  apply not_In_inf_seq with (S (max_var_weight_p_hseq G)) (length L) x; try lia.
  apply Hin.
Qed.

Lemma sum_weight_with_coeff_one_eval_eq : forall val G L,
    sum_weight_one_with_coeff (map (eval_p_sequent val) G) L - sum_weight_coone_with_coeff (map (eval_p_sequent val) G) L = FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) (map oRpos_to_R L)) (p_sum_weight_one_with_coeff G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))) - FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) (map oRpos_to_R L)) (p_sum_weight_coone_with_coeff G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))).
Proof.
  intros val G L.
  rewrite FOL_R_term_sem_eval_p_hseq_one; auto.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_to_oRpos_to_R_eq.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_p_hseq_upd_val_vec_lt; try reflexivity.
  apply forall_Forall_inf.
  intros x Hin.
  case_eq (max_var_weight_p_hseq G <? x)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H]; auto.
  exfalso.
  apply not_In_inf_seq with (S (max_var_weight_p_hseq G)) (length L) x; try lia.
  apply Hin.
Qed.

(* Put non basic formula first, i.e., G in the form H | |- T, r.A with A non basic. *)

Fixpoint p_seq_fst_non_basic_term (T : p_sequent) : (FOL_R_term * term) :=
  match T with
  | nil => (FOL_R_cst 0, HMR_var 0)
  | (a, A) :: T => if (0 <? HMR_complexity_term A)%nat
                   then (a , A)
                   else (p_seq_fst_non_basic_term T)
  end.

Lemma p_seq_fst_non_basic_term_correct :
  forall T,
    (p_seq_is_basic T -> False) ->
    (is_basic (snd (p_seq_fst_non_basic_term T)) -> False).
Proof.
  induction T; intros Hnbs Hbt; [ apply Hnbs; apply Forall_inf_nil | ].
  destruct a as [a A]; simpl in *.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H1; rewrite H1 in Hbt;
    (apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1).
  - apply is_basic_complexity_0 in Hbt.
    simpl in Hbt.
    lia.
  - apply IHT; auto.
    intros H2.
    apply Hnbs.
    apply Forall_inf_cons; auto.
    apply is_basic_complexity_0_inv.
    lia.
Qed.

Lemma p_seq_fst_non_basic_term_well_defined :
  forall val T,
    (0 < HMR_complexity_p_seq T)%nat ->
    p_seq_well_defined val T ->
    (0 <? FOL_R_term_sem val (fst (p_seq_fst_non_basic_term T))) = true.
Proof.
  intros val; induction T; intros Hlt; [ simpl in Hlt; exfalso; try lia | ].
  intros Hwd.
  destruct a as [a A].
  simpl.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H; auto; inversion Hwd; subst; auto.
  apply IHT; auto.
  apply Nat.ltb_nlt in H.
  simpl in *.
  lia.
Qed.  

Fixpoint p_seq_without_fst_non_basic_term (T : p_sequent) : p_sequent :=
  match T with
  | nil => nil
  | (a, A) :: T => if (0 <? HMR_complexity_term A)%nat
                   then T
                   else (a , A) :: (p_seq_without_fst_non_basic_term T)
  end.

Lemma p_seq_put_non_basic_fst : forall T,
    (p_seq_is_basic T -> False) ->
    Permutation_Type T (p_seq_fst_non_basic_term T :: p_seq_without_fst_non_basic_term T).
Proof.
  induction T; intros Hnb; [ exfalso; apply Hnb; apply Forall_inf_nil | ].
  destruct a as [a A]; simpl.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H1;
    apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1; auto.
  assert (p_seq_is_basic T -> False).
  { intros H; apply Hnb; apply Forall_inf_cons; auto.
    apply is_basic_complexity_0_inv.
    lia. }
  specialize (IHT H).
  transitivity ((a , A) :: p_seq_fst_non_basic_term T :: p_seq_without_fst_non_basic_term T);
    Permutation_Type_solve.
Qed.

Lemma p_seq_without_fst_non_basic_term_well_defined :
  forall val T,
    p_seq_well_defined val T ->
    p_seq_well_defined val (p_seq_without_fst_non_basic_term T).
Proof.
  intros val; induction T; intros Hwd; [apply Forall_inf_nil |].
  destruct a as [a A]; inversion Hwd; subst.
  simpl.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H; try apply Forall_inf_cons; try apply IHT; auto.
Qed.

Fixpoint p_hseq_p_seq_max_complexity (G : p_hypersequent) : p_sequent :=
  match G with
  | nil => nil
  | T :: G => if (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq T)
              then T
              else p_hseq_p_seq_max_complexity G
  end.

Lemma p_hseq_p_seq_max_complexity_well_defined :
  forall val G,
    p_hseq_well_defined val G ->
    p_seq_well_defined val (p_hseq_p_seq_max_complexity G).
Proof.
  intros val; induction G; intros Hwd; [ apply Forall_inf_nil | ].
  inversion Hwd; specialize (IHG X0); subst.
  simpl; case (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); auto.
Qed.

Lemma p_hseq_p_seq_max_complexity_correct :
  forall G,
    HMR_complexity_p_seq (p_hseq_p_seq_max_complexity G) = fst (HMR_complexity_p_hseq G).
Proof.
  induction G; auto.
  simpl.
  case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H1;
    case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); intros H2;
      case_eq (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
        simpl;
        apply Nat.leb_le in H1 + apply Nat.leb_nle in H1;
        apply Nat.eqb_eq in H2 + apply Nat.eqb_neq in H2;
        apply Nat.ltb_lt in H3 + apply Nat.ltb_nlt in H3;
        try lia.
Qed.

Fixpoint p_hseq_without_max_complexity (G : p_hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => if (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq T)
              then G
              else T :: p_hseq_without_max_complexity G
  end.

Lemma p_hseq_without_max_complexity_well_defined :
  forall val G,
    p_hseq_well_defined val G ->
    p_hseq_well_defined val (p_hseq_without_max_complexity G).
Proof.
  intros val; induction G; intros Hwd; [apply Forall_inf_nil | ].
  inversion Hwd; subst; specialize (IHG X0).
  simpl; case (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); try apply Forall_inf_cons; auto.
Qed.

Lemma p_hseq_put_max_complexity_fst : forall G,
    G <> nil ->
    Permutation_Type G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G).
Proof.
  induction G; intros Hnnil; [ exfalso; auto | ].
  simpl.
  case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H1;
    apply Nat.leb_le in H1 + apply Nat.leb_nle in H1; auto.
  destruct G.
  { exfalso; simpl in H1; lia. }
  assert (p :: G <> nil) as Hnnil'.
  { intros H; inversion H. }
  specialize (IHG Hnnil').
  transitivity (a :: p_hseq_p_seq_max_complexity (p :: G) :: p_hseq_without_max_complexity (p :: G)); Permutation_Type_solve.
Qed.

Definition p_hseq_put_non_basic_fst G :=
  ((p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)) :: p_hseq_without_max_complexity G).

Lemma p_hseq_put_non_basic_fst_modal_complexity :
  forall G,
    (p_hseq_is_basic G -> False) ->
    modal_complexity_p_hseq (p_hseq_put_non_basic_fst G) = modal_complexity_p_hseq G.
Proof.
  intros G Hnb.
  unfold p_hseq_put_non_basic_fst.
  rewrite modal_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_basic_fst.
      intros H.
      apply Hnb.
      apply p_hseq_is_basic_complexity_0_inv.
      rewrite <- p_hseq_p_seq_max_complexity_correct.
      apply p_seq_is_basic_complexity_0.
      apply H. }
  rewrite modal_complexity_perm with _ G; auto.
  symmetry; apply p_hseq_put_max_complexity_fst.
  intros H; apply Hnb; rewrite H.
  apply Forall_inf_nil.
Qed.

Lemma p_hseq_put_non_basic_fst_HMR_complexity :
  forall G,
    (p_hseq_is_basic G -> False) ->
    HMR_complexity_p_hseq (p_hseq_put_non_basic_fst G) = HMR_complexity_p_hseq G.
Proof.
  intros G Hnb.
  apply same_modal_complexity_HMR_complexity.
  apply p_hseq_put_non_basic_fst_modal_complexity; auto.
Qed.

Lemma p_hseq_put_non_basic_fst_correct :
  forall G a A T H,
    (p_hseq_is_basic G -> False) ->
    p_hseq_put_non_basic_fst G = ((a, A) :: T) :: H ->
    is_basic A -> False.
Proof.
  intros G a A T H Hnb Heq Hb.
  unfold p_hseq_put_non_basic_fst in Heq.
  inversion Heq; subst.
  apply p_seq_fst_non_basic_term_correct with (p_hseq_p_seq_max_complexity G).
  - intros Hb'.
    apply Hnb.
    apply p_hseq_is_basic_complexity_0_inv.
    apply p_seq_is_basic_complexity_0 in Hb'.
    rewrite p_hseq_p_seq_max_complexity_correct in Hb'.
    apply Hb'.
  - rewrite H1.
    apply Hb.
Qed.

Lemma p_hseq_put_non_basic_fst_well_defined :
  forall val G,
    (0 < fst (HMR_complexity_p_hseq G))%nat ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val (p_hseq_put_non_basic_fst G).
Proof.
  intros val G Hn0 Hwd.
  apply Forall_inf_cons; (destruct G; [ exfalso; simpl in *; lia | ]).
  - apply Forall_inf_cons.
    + apply p_seq_fst_non_basic_term_well_defined; [ | apply p_hseq_p_seq_max_complexity_well_defined; auto].
      rewrite p_hseq_p_seq_max_complexity_correct.
      apply Hn0.
    + apply p_seq_without_fst_non_basic_term_well_defined.
      apply p_hseq_p_seq_max_complexity_well_defined.
      apply Hwd.
  - apply p_hseq_without_max_complexity_well_defined; apply Hwd.
Qed.
  
Definition apply_logical_rule_on_p_hypersequent G : (p_hypersequent + (p_hypersequent * p_hypersequent)) :=
  match G with
  | nil => inl nil
  | T :: G => match T with
              | nil => inl (nil :: G)
              | (a, A) :: T => match A with
                               | A1 +S A2 => inl (((a, A1) :: (a, A2) :: T) :: G)
                               | A1 /\S A2 => inr ((((a, A1) :: T) :: G) , (((a, A2) :: T) :: G))
                               | A1 \/S A2 => inl (((a, A2) :: T) :: ( (a, A1) :: T) :: G)
                               | r0 *S A => inl (((FOL_R_cst (projT1 r0) *R a, A) :: T) :: G)
                               | HMR_zero => inl (T :: G)
                               | _ => inl (((a, A) :: T) :: G)
                               end
              end
  end.

Lemma apply_logical_rule_on_p_hypersequent_inl_well_defined :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val G1.
Proof.
  intros val G G1 Heq Hwd.
  destruct G ; [inversion Heq; apply Forall_inf_nil | ].
  destruct l; [inversion Heq; apply Hwd | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto;
    inversion Hwd; subst;
      inversion X; subst; simpl in *;
        (apply Forall_inf_cons; [ | try apply Forall_inf_cons]); auto;
          apply Forall_inf_cons; auto.
  apply R_blt_lt; apply R_blt_lt in H0.
  destruct r as [r Hr].
  clear - H0 Hr.
  simpl; apply R_blt_lt in Hr.
  nra.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_l_well_defined :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1, G2) ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val G1.
Proof.
  intros val G G1 G2 Heq Hwd.
  destruct G ; [inversion Heq | ].
  destruct l; [inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; subst.
  inversion X; subst.
  apply Forall_inf_cons ; [ apply Forall_inf_cons | ]; auto.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_r_well_defined :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1, G2) ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val G2.
Proof.
  intros val G G1 G2 Heq Hwd.
  destruct G ; [inversion Heq | ].
  destruct l; [inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; subst.
  inversion X; subst.
  apply Forall_inf_cons ; [ apply Forall_inf_cons | ]; auto.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inl_HMR :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) G1).
Proof.
  intros val G G1 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ nil pi); auto | ].
  destruct l; [ inversion Heq; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  - inversion Hwd; inversion X; subst.
    simpl in pi.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    rewrite He in pi.
    simpl.
    apply hmrr_Z_inv with ((existT _ (FOL_R_term_sem val a) e) :: nil).
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    rewrite He in pi.
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r, A1) :: (r, A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) A1 ++ hseq.vec (r :: nil) A2 ++ eval_p_sequent val l).
    apply hmrr_plus_inv.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    case (R_order_dec (projT1 r * FOL_R_term_sem val a)); intros e';
      try (exfalso; destruct r as [r Hr]; clear - e e' H2;
           simpl in *;
           apply R_blt_lt in Hr; apply R_blt_lt in e; try (apply R_blt_lt in e');
           nra).
    rewrite He in pi.
    replace ((existT (fun x : R => (0 <? x) = true) (projT1 r * FOL_R_term_sem val a) e', A)
              :: eval_p_sequent val l) with
        (hseq.vec (hseq.mul_vec r ((existT (fun x => (0 <? x) = true) (FOL_R_term_sem val a) e) :: nil)) A ++ eval_p_sequent val l).
    2:{ simpl.
        replace (time_pos r (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e))
          with (existT (fun x : R => (0 <? x) = true) (projT1 r * FOL_R_term_sem val a) e') by (destruct r; apply Rpos_eq; clear; simpl; nra); auto. }
    apply hmrr_mul_inv.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    rewrite He in pi.
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r, A1) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) A1 ++ eval_p_sequent val l).
    change ((r, A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) A2 ++ eval_p_sequent val l).
    apply hmrr_max_inv.
    apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inl_HMR_inv :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G1) ->
    HMR_T_M (map (eval_p_sequent val) G).
Proof.
  intros val G G1 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ _ pi); inversion Heq; auto | ].
  destruct l; [ inversion Heq; subst; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r, HMR_zero) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) HMR_zero ++ eval_p_sequent val l).
    apply hmrr_Z.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    rewrite He in pi.
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r, A1 +S A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) (A1 +S A2) ++ eval_p_sequent val l).
    apply hmrr_plus.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    case_eq (R_order_dec (projT1 r * FOL_R_term_sem val a)); intros e' He';
      try (exfalso; destruct r as [r Hr]; clear - e e' H2;
           simpl in *;
           apply R_blt_lt in Hr; apply R_blt_lt in e; try (apply R_blt_lt in e');
           nra).
    rewrite He' in pi.
    replace ((existT (fun x : R => (0 <? x) = true) (projT1 r * FOL_R_term_sem val a) e', A)
              :: eval_p_sequent val l) with
        (hseq.vec (hseq.mul_vec r ((existT (fun x => (0 <? x) = true) (FOL_R_term_sem val a) e) :: nil)) A ++ eval_p_sequent val l) in pi.
    2:{ simpl.
        replace (time_pos r (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e))
          with (existT (fun x : R => (0 <? x) = true) (projT1 r * FOL_R_term_sem val a) e') by (destruct r; apply Rpos_eq; clear; simpl; nra); auto. }
    revert pi;set (r' := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r', r *S A) :: eval_p_sequent val l)
      with (hseq.vec (r' :: nil) (r *S A) ++ eval_p_sequent val l).    
    apply hmrr_mul.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    rewrite He in pi.
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r, A1 \/S A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) (A1 \/S A2) ++ eval_p_sequent val l).
    apply hmrr_max.
    apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_l_HMR :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) G1).
Proof.
  intros val G G1 G2 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ nil pi); auto | ].
  destruct l; [ inversion Heq; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; inversion X; subst.
  simpl in pi |- *.
  sem_is_pos_decomp val a; intros e He;
    try (exfalso; clear - e H2;
         try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
  rewrite He in pi.
  revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
  change ((r, A1) :: eval_p_sequent val l) with
      (hseq.vec (r :: nil) A1 ++ eval_p_sequent val l).
  apply hmrr_min_inv_l with A2.
  apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_r_HMR :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) G2).
Proof.
  intros val G G1 G2 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ nil pi); auto | ].
  destruct l; [ inversion Heq; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; inversion X; subst.
  simpl in pi |- *.
  sem_is_pos_decomp val a; intros e He;
    try (exfalso; clear - e H2;
         try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
  rewrite He in pi.
  revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
  change ((r, A2) :: eval_p_sequent val l) with
      (hseq.vec (r :: nil) A2 ++ eval_p_sequent val l).
  apply hmrr_min_inv_r with A1.
  apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_HMR_inv :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G1) ->
    HMR_T_M (map (eval_p_sequent val) G2) ->
    HMR_T_M (map (eval_p_sequent val) G).
Proof.
  intros val G G1 G2 Heq Hwd pi1 pi2.
  destruct G; [ exfalso; inversion Heq | ].
  destruct l; [ inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; inversion X; subst.
  simpl in pi1,pi2 |- *.
  sem_is_pos_decomp val a; intros e He;
    try (exfalso; clear - e H2;
         try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
  rewrite He in pi1; rewrite He in pi2.
  revert pi1 pi2;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi1 pi2.
  change ((r, A1 /\S A2) :: eval_p_sequent val l) with
      (hseq.vec (r :: nil) (A1 /\S A2) ++ eval_p_sequent val l).
  apply hmrr_min; auto.
Qed.
    
Lemma apply_logical_rule_on_p_hypersequent_correct_inl :
  forall G G1 n,
    snd (fst (modal_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl G1 ->
    modal_complexity_p_hseq G1 <3 modal_complexity_p_hseq G.
Proof.
  intros G G1 n H1 H2.
  unfold modal_complexity_p_hseq in H1.
  simpl in H1.
  remember (p_hseq_put_non_basic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_basic_fst_HMR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_basic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_basic A -> False).
  { apply p_hseq_put_non_basic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_basic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, HMR_zero) :: l) with (vec (a :: nil) HMR_zero ++ l).
    apply hmrr_Z_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, A1 +S A2) :: l) with (vec (a :: nil) (A1 +S A2) ++ l).
    change ((a, A1) :: (a, A2) :: l) with (vec (a :: nil) A1 ++ vec (a :: nil) A2 ++ l).
    apply hmrr_plus_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, r *S A) :: l) with (vec (a :: nil) (r *S A) ++ l).
    change ((FOL_R_cst (projT1 r) *R a, A) :: l) with (vec (mul_vec (FOL_R_cst (projT1 r)) (a :: nil)) A ++ l).
    apply hmrr_mul_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, A1 \/S A2) :: l) with (vec (a :: nil) (A1 \/S A2) ++ l).
    change ((a, A1) :: l) with (vec (a :: nil) A1 ++ l).
    change ((a, A2) :: l) with (vec (a :: nil) A2 ++ l).
    apply hmrr_max_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_correct_inr_l :
  forall G G1 G2 n,
    snd (fst (modal_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1 , G2) ->
    modal_complexity_p_hseq G1 <3 modal_complexity_p_hseq G.
Proof.
  intros G G1 G2 n H1 H2.
  unfold modal_complexity_p_hseq in H1.
  simpl in H1.
  remember (p_hseq_put_non_basic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_basic_fst_HMR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_basic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_basic A -> False).
  { apply p_hseq_put_non_basic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_basic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
  2:{ intros Hnb.
      apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  rewrite <- HeqH.
  change ((a, A1 /\S A2) :: l) with (vec (a :: nil) (A1 /\S A2) ++ l).
  change ((a, A1) :: l) with (vec (a :: nil) A1 ++ l).
  apply hmrr_min_r_decrease_modal_complexity ; [ intros H'; inversion H' | ].
  simpl vec; simpl app.
  rewrite HeqH.
  unfold p_hseq_put_non_basic_fst in *.
  rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  rewrite complexity_p_hseq_perm with _ G.
  2:{ symmetry; apply p_hseq_put_max_complexity_fst.
      intros Heq; rewrite Heq in H1; inversion H1. }
  rewrite <-p_hseq_p_seq_max_complexity_correct.
  rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  inversion HeqH; subst; reflexivity.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_correct_inr_r :
  forall G G1 G2 n,
    snd (fst (modal_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1 , G2) ->
    modal_complexity_p_hseq G2 <3 modal_complexity_p_hseq G.
Proof.
  intros G G1 G2 n H1 H2.
  unfold modal_complexity_p_hseq in H1.
  simpl in H1.
  remember (p_hseq_put_non_basic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_basic_fst_HMR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_basic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_basic A -> False).
  { apply p_hseq_put_non_basic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_basic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
  2:{ intros Hnb.
      apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  rewrite <- HeqH.
  change ((a, A1 /\S A2) :: l) with (vec (a :: nil) (A1 /\S A2) ++ l).
  change ((a, A2) :: l) with (vec (a :: nil) A2 ++ l).
  apply hmrr_min_l_decrease_modal_complexity ; [ intros H'; inversion H' | ].
  simpl vec; simpl app.
  rewrite HeqH.
  unfold p_hseq_put_non_basic_fst in *.
  rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  rewrite complexity_p_hseq_perm with _ G.
  2:{ symmetry; apply p_hseq_put_max_complexity_fst.
      intros Heq; rewrite Heq in H1; inversion H1. }
  rewrite <-p_hseq_p_seq_max_complexity_correct.
  rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  inversion HeqH; subst; reflexivity.
Qed.

(* end hide *)

(** return the conjunction /\(beta_{k + i} = 0) for all i \in v *)
Fixpoint FOL_R_all_zero k (v : list nat) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and
                (FOL_R_atoms ((FOL_R_var (k + n)) =R (FOL_R_cst 0)))
                (FOL_R_all_zero k v)
  end.

Lemma cond_FOL_R_all_zero_formula_sem : forall k v val,
    (forall n, In_inf n v -> val (k + n)%nat = 0) ->
    FOL_R_formula_sem val (FOL_R_all_zero k v).
Proof.
  intros k; induction v; intros val H; [apply I | ].
  split.
  - apply H.
    apply in_inf_eq.
  - apply IHv.
    intros n Hin.
    apply H.
    apply in_inf_cons; apply Hin.
Qed.
    
Lemma cond_FOL_R_all_zero_formula_sem_inv : forall k v val,
    FOL_R_formula_sem val (FOL_R_all_zero k v) ->
    forall n, In_inf n v -> val (k + n)%nat = 0.
Proof.
  intros k; induction v; intros val Hf n Hin; inversion Hin; subst.
  - destruct Hf as [Heq _]; apply Heq.
  - destruct Hf as [_ Hf].
    apply IHv; assumption.
Qed.

(** return the conjunction /\(0\leq\beta_{k + i} /\ \beta_{k + i} = 0) for all in \in v *)
Fixpoint FOL_R_all_gtz k (v : list nat ) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and (FOL_R_and
                           (FOL_R_atoms ((FOL_R_var (k + n)) <>R (FOL_R_cst 0)))
                           (FOL_R_atoms ((FOL_R_cst 0) <=R(FOL_R_var (k + n)))))
                        (FOL_R_all_gtz k v)
  end.

Lemma cond_FOL_R_all_gtz_formula_sem : forall k v val,
    (forall n, In_inf n v -> 0 < val (k + n)%nat) ->
    FOL_R_formula_sem val (FOL_R_all_gtz k v).
Proof.
  intros k; induction v; intros val H; [apply I | ].
  split.
  - specialize (H a (in_inf_eq a v)).
    split; simpl; lra.
  - apply IHv.
    intros n Hin.
    apply H.
    apply in_inf_cons; apply Hin.
Qed.
    
Lemma cond_FOL_R_all_gtz_formula_sem_inv : forall k v val,
    FOL_R_formula_sem val (FOL_R_all_gtz k v) ->
    forall n, In_inf n v -> 0 < val (k + n)%nat.
Proof.
  intros k; induction v; intros val Hf n Hin; inversion Hin; subst.
  - destruct Hf as [[Hneq Hle] _].
    simpl in *; lra.
  - destruct Hf as [_ Hf].
    apply IHv; assumption.
Qed.

(** return the conjunction /\(\sum_i^m \beta_{(max_var_weight G) + i} \sum\vec R_{i,j} = \sum_i^m \beta_{(max_var_weight G) + i} \sum\vec S_{i,j} *)
Fixpoint FOL_R_all_atoms_eq G k :=
  match k with
  | 0%nat => FOL_R_atoms ((p_sum_weight_var_with_coeff 0%nat G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) =R(p_sum_weight_covar_with_coeff 0%nat G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))))
  | S k => FOL_R_and
             (FOL_R_atoms ((p_sum_weight_var_with_coeff (S k) G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) =R (p_sum_weight_covar_with_coeff (S k) G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))))))
             (FOL_R_all_atoms_eq G k)
  end.


Lemma cond_FOL_R_all_atoms_eq_formula_sem : forall G k val,
    (forall n, (n <= k)%nat -> FOL_R_pred_sem val (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) =R p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))))) ->
    FOL_R_formula_sem val (FOL_R_all_atoms_eq G k).
Proof.
  intros G; induction k; intros val H.
  - simpl.
    specialize (H 0%nat (Nat.le_refl 0%nat)).
    apply H.
  - simpl.
    split.
    + specialize (H (S k) (Nat.le_refl (S k))).
      apply H.
    + apply IHk.
      intros n Hle.
      apply H.
      lia.
Qed.
    
Lemma cond_FOL_R_all_atoms_eq_formula_sem_inv : forall G k val,
    FOL_R_formula_sem val (FOL_R_all_atoms_eq G k) ->
    forall n, (n <= k)%nat -> FOL_R_pred_sem val (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) =R p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))).
Proof.
  intros G; induction k; intros val Hf n Hle.
  - simpl in Hf.
    destruct n; inversion Hle.
    apply Hf.
  - destruct Hf as [Hf1 Hf2].
    case_eq (n =? S k)%nat; intros Heq.
    + simpl in Hf1 |- *.
      apply Nat.eqb_eq in Heq; rewrite Heq.
      apply Hf1.
    + apply IHk ; try assumption.
      apply Nat.eqb_neq in Heq.
      lia.
Qed.

(** return the formula (\sum_i^m \beta_{(max_var_weight G) + i} \sum\vec R_{i,j} = \sum_i^m \beta_{(max_var_weight G) + i} \sum\vec S_{i,j} *)
Definition FOL_R_coone_le_one G := FOL_R_atoms ((p_sum_weight_coone_with_coeff G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) <=R (p_sum_weight_one_with_coeff G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))))).

(** return the formula corresponding to \phi_{G,v} *)
Definition FOL_R_phi G v :=
  FOL_R_and (FOL_R_all_zero (S (max_var_weight_p_hseq G)) (complementary v (length G)))
            (FOL_R_and (FOL_R_all_gtz (S (max_var_weight_p_hseq G)) v)
                       (FOL_R_and (FOL_R_all_atoms_eq G (max_var_p_hseq G))
                                  (FOL_R_coone_le_one G))).
    
(** return the whole formula *)

(* begin hide *)
(* auxiliary functions used to help Coq understands they terminate *)
Fixpoint FOL_R_basic_case_aux (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = n) (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) : FOL_R_formula
with HMR_dec_formula_aux (G : p_hypersequent) (x: nat) (Heqx : snd (fst (modal_complexity_p_hseq G)) = x) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) (acc : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) : FOL_R_formula.
  - destruct acc as [acc].
    destruct V as [ | v V].
    + apply FOL_R_false.
    +  destruct n.
       * refine (FOL_R_or
                   (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v))
                   (FOL_R_basic_case_aux G V
                                         0%nat
                                         Heqn
                                         (acc _
                                              (lt_nat4_last
                                                 _
                                                 _
                                                 _
                                                 (Nat.lt_succ_diag_r _))))).
       * refine (FOL_R_or
                   (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G))
                               (FOL_R_and (FOL_R_phi G v)
                                          (HMR_dec_formula_aux (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil)
                                                               _
                                                               (eq_refl _)
                                                               _
                                                               (eq_refl _)
                                                               (acc _ (lt_nat3_to_lt_nat4
                                                                         _
                                                                         _
                                                                         _
                                                                         _
                                                                         (modal_complexity_only_diamond_p_seq _ _ _ _ Heqn))))))
                   (FOL_R_basic_case_aux G V
                                         (S n)
                                         Heqn
                                         (acc _
                                              (lt_nat4_last
                                                 _
                                                 _
                                                 _
                                                 (Nat.lt_succ_diag_r _))))).
  - destruct acc as [acc].
    destruct x.
    + refine (FOL_R_basic_case_aux G (map (@rev nat) (make_subsets (length G)))
                                   _
                                   (eq_refl _)
                                   (acc _
                                        (lt_nat4_last
                                           _
                                           _
                                           _
                                           (eq_rect _ (fun x => (x < S (length (make_subsets (length G))))%nat) (Nat.lt_succ_diag_r _) _ (eq_sym (map_length _ _)))))).
    + destruct p.
      * refine (HMR_dec_formula_aux p
                                _
                                eq_refl
                                _
                                eq_refl
                                (acc _
                                     (lt_nat3_to_lt_nat4 _ _ _ _
                                                         (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp)))).
      * destruct p.
        refine (FOL_R_and
                  (HMR_dec_formula_aux p
                                   _
                                   (eq_refl _)
                                   _
                                   (eq_refl _)
                                   (acc _
                                        (lt_nat3_to_lt_nat4 _ _ _ _
                                                            (apply_logical_rule_on_p_hypersequent_correct_inr_l G p p0 x Heqx Heqp))))
                  (HMR_dec_formula_aux p0
                                    _
                                   eq_refl
                                   _
                                   eq_refl
                                   (acc _
                                        (lt_nat3_to_lt_nat4 _ _ _ _
                                                            (apply_logical_rule_on_p_hypersequent_correct_inr_r G p p0 x Heqx Heqp))))).
Defined.    

Lemma FOL_R_basic_case_aux_sem_indep_acc val (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = n) (acc1 acc2 : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
    FOL_R_formula_sem val (FOL_R_basic_case_aux G V n Heqn acc1) ->
    FOL_R_formula_sem val (FOL_R_basic_case_aux G V n Heqn acc2)
with HMR_dec_formula_aux_sem_indep_acc val (G : p_hypersequent) (x: nat) (Heqx : snd (fst (modal_complexity_p_hseq G)) = x) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) (acc1 acc2 : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
         FOL_R_formula_sem val (HMR_dec_formula_aux G x Heqx p Heqp acc1) ->
         FOL_R_formula_sem val (HMR_dec_formula_aux G x Heqx p Heqp acc2).
Proof.
  - destruct acc1 as [acc1]; destruct acc2 as [acc2].
    destruct V; destruct n; intros Hf; try destruct Hf as [Hf | Hf].
    + inversion Hf.
    + inversion Hf.
    + simpl.
      left.
      apply Hf.
    + simpl.
      right.
      refine (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf).
    + left.
      apply cond_FOL_R_exists_vec_formula_sem.
      apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [v [Hlen [Hf1 Hf2]]].
      split with v.
      split; [ |  split]; auto.
      refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf2).
    + simpl.
      right.
      refine (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf).
  - destruct acc1 as [acc1]; destruct acc2 as [acc2]; intros Hf.
    destruct x.
    + simpl.
      refine (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf).
    + destruct p.
      * refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf).
      * destruct p.
        destruct Hf as [Hf1 Hf2].
        split.
        -- refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf1).
        -- refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf2).
Qed.

Lemma FOL_R_basic_case_aux_sem_indep_n :
  forall val (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = n) m (Heqm : max_diamond_p_hseq G = m) (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)),
  FOL_R_formula_sem val (FOL_R_basic_case_aux G V n Heqn acc) ->
  FOL_R_formula_sem val (FOL_R_basic_case_aux G V m Heqm acc).
Proof.
  intros val G V.
  induction V; intros n Heqn m Heqm acc;
    destruct acc as [acc]; auto.
  destruct n; destruct m; try (exfalso; lia); intros [Hf | Hf].
  + left.
    apply Hf.
  + right.
    apply (IHV _ Heqn _ Heqm); apply Hf.
  + left.
    apply cond_FOL_R_exists_vec_formula_sem.
    apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [v [Hlen [Hf1 Hf2]]].
    split with v.
    split; [ |  split]; auto.
    apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
  + right.
    apply (IHV _ Heqn _ Heqm); apply Hf.
Qed.

Lemma HMR_dec_formula_aux_sem_indep_n : forall val G (n: nat) (Heqn : snd (fst (modal_complexity_p_hseq G)) = n) m (Heqm : snd (fst (modal_complexity_p_hseq G)) = m) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) acc,
    FOL_R_formula_sem val (HMR_dec_formula_aux G n Heqn p Heqp acc) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G m Heqm p Heqp acc).
Proof.
  intros val G.
  assert ({x & x = modal_complexity_p_hseq G}) as [x Heqx] by (split with (modal_complexity_p_hseq G); reflexivity).
  revert G Heqx.
  apply (lt_nat3_wf_rect x); clear x.
  intros x H G Heqx [ | n] Heqn [ | m] Heqm [G1 | [G1 G2]] Heqp [acc] Hf;
    try destruct Hf as [Hf1 Hf2]; try (exfalso; lia).
  - apply Hf.
  - apply Hf.
  - unfold HMR_dec_formula_aux in *; fold HMR_dec_formula_aux in *.
    refine (H (modal_complexity_p_hseq G1) _ G1 eq_refl _ eq_refl _ eq_refl _ eq_refl _ _).
    { rewrite Heqx.
      apply apply_logical_rule_on_p_hypersequent_correct_inl with n; auto. }
    refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
  - split.
    + unfold HMR_dec_formula_aux in *; fold HMR_dec_formula_aux in *.
      refine (H (modal_complexity_p_hseq G1) _ G1 eq_refl _ eq_refl _ eq_refl _ eq_refl _ _).
      { rewrite Heqx.
        apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 n; auto. }
      refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1).
    + unfold HMR_dec_formula_aux in *; fold HMR_dec_formula_aux in *.
      refine (H (modal_complexity_p_hseq G2) _ G2 eq_refl _ eq_refl _ eq_refl _ eq_refl _ _).
      { rewrite Heqx.
        apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 n; auto. }
      refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
Qed.

Lemma HMR_dec_formula_aux_sem_indep_Heqp : forall val G (n: nat) (Heqn : snd (fst (modal_complexity_p_hseq G)) = n) p (Heqp1 Heqp2 : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) acc,
    FOL_R_formula_sem val (HMR_dec_formula_aux G n Heqn p Heqp1 acc) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G n Heqn p Heqp2 acc).
Proof.
  intros val G [ | n] Heqn [G1 | [G1 G2]] Heqp1 Heqp2 [acc] Hf;
    try destruct Hf as [Hf1 Hf2]; try (exfalso; lia).
  - apply Hf.
  - apply Hf.
  - unfold HMR_dec_formula_aux in *; fold HMR_dec_formula_aux in *.
    apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
  - split.
    + unfold HMR_dec_formula_aux in *; fold HMR_dec_formula_aux in *.
      apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1).
    + unfold HMR_dec_formula_aux in *; fold HMR_dec_formula_aux in *.
      apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
Qed.

Lemma HMR_dec_formula_aux_sem_indep_p : forall val G (n: nat) (Heqn : snd (fst (modal_complexity_p_hseq G)) = n) p1 (Heqp1 : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p1) p2 (Heqp2 : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p2) acc,
    FOL_R_formula_sem val (HMR_dec_formula_aux G n Heqn p1 Heqp1 acc) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G n Heqn p2 Heqp2 acc).
Proof.
  intros val G [ | n] Heqn [G1 | [G1 G2]] Heqp1 [G'1 | [G'1 G'2]] Heqp2 [acc] Hf;
    try destruct Hf as [Hf1 Hf2]; try (exfalso; rewrite Heqp1 in Heqp2; now inversion Heqp2).
  - apply Hf.
  - apply Hf.
  - assert (G1 = G'1) as H.
    { clear - Heqp1 Heqp2; rewrite Heqp1 in Heqp2; now inversion Heqp2. }
    subst.
    apply (HMR_dec_formula_aux_sem_indep_Heqp _ _ _ _ _ _ _ _ Hf).
  - assert (G1 = G'1) as H1.
    { clear - Heqp1 Heqp2; rewrite Heqp1 in Heqp2; now inversion Heqp2. }
    assert (G2 = G'2) as H2.
    { clear - Heqp1 Heqp2; rewrite Heqp1 in Heqp2; now inversion Heqp2. }
    subst.
    split.
    + apply (HMR_dec_formula_aux_sem_indep_Heqp _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1)).
    + apply (HMR_dec_formula_aux_sem_indep_Heqp _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2)).
Qed.

Lemma cond_FOL_R_basic_case_aux_no_diamond :
  forall val (G : p_hypersequent) (V : list (list nat)) (Heqn : max_diamond_p_hseq G = 0%nat) (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)),
    {v & prod (In_inf v V) (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v)))} ->
    FOL_R_formula_sem val (FOL_R_basic_case_aux G V 0%nat Heqn acc).
Proof.
  intros val G V.
  induction V as [ | v V]; intros Heqn acc [v0 [Hin Hf]];
    destruct acc as [acc].
  - inversion Hin.
  - inversion Hin; subst.
    + simpl.
      left.
      apply Hf.
    + simpl; right.
      apply IHV.
      split with v0.
      split; auto.
Qed.

Lemma cond_FOL_R_basic_case_aux_diamond :
  forall val (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = S n) (acc : Acc lt_nat4 (modal_complexity_p_hseq G, length V)),
    { v & { acc' &  prod (In_inf v V)
                         (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G))
                                                             (FOL_R_and
                                                                (FOL_R_phi G v)
                                                                (HMR_dec_formula_aux (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil) _ eq_refl _ eq_refl acc'))))} } ->
    FOL_R_formula_sem val (FOL_R_basic_case_aux G V (S n) Heqn acc).
Proof.
  intros val G V.
  induction V; intros n Heqn [acc] [v [acc' [Hin Hf]]].
  - inversion Hin.
  - inversion Hin; subst.
    + left.
      apply cond_FOL_R_exists_vec_formula_sem.
      apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [v' [Hlen [Hf1 Hf2]]].
      split with v'.
      split; [ |  split]; auto.
      apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
    + right.
      apply IHV.
      split with v.
      split with acc'.
      repeat split; auto.
Qed.

Lemma cond_FOL_R_basic_case_aux_no_diamond_inv :
  forall val (G : p_hypersequent) (V : list (list nat)) (Heqn : max_diamond_p_hseq G = 0%nat) (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)),
    FOL_R_formula_sem val (FOL_R_basic_case_aux G V 0%nat Heqn acc) ->
    {v & prod (In_inf v V) (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v)))}.
Proof.
  intros val G V.
  induction V as [ | v V]; intros Heqn acc Hf;
    destruct acc as [acc].
  - inversion Hf.
  - inversion Hf.
    + split with v.
      repeat split; auto.
      left.
      reflexivity.
    + destruct (IHV _ _ X) as [v0 [Hin Hf']].
      split with v0.
      repeat split; auto.
      now right.
Qed.

Lemma cond_FOL_R_basic_case_aux_diamond_inv :
  forall val (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = S n) (acc : Acc lt_nat4 (modal_complexity_p_hseq G, length V)),
    FOL_R_formula_sem val (FOL_R_basic_case_aux G V (S n) Heqn acc) ->
    { v & { acc' &  prod (In_inf v V)
                         (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G))
                                                             (FOL_R_and
                                                                (FOL_R_phi G v)
                                                                (HMR_dec_formula_aux (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil) _ eq_refl _ eq_refl acc'))))} }.
Proof.
  intros val G V.
  induction V; intros n Heqn [acc] Hf.
  - inversion Hf.
  - inversion Hf.
    + split with a.
      split with (wf_lt_nat4 _).
      apply cond_FOL_R_exists_vec_formula_sem_inv in X as [v [Hin [Hf1 Hf2]]].
      repeat split.
      * left; reflexivity.
      * apply cond_FOL_R_exists_vec_formula_sem.
        split with v; split; [ | split]; auto.
        apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
    + destruct (IHV _ _ _ X) as [v0 [acc' [Hin Hf']]].
      split with v0.
      split with acc'.
      repeat split; auto.
      now right.
Qed.

Lemma cond_HMR_dec_formula_aux_basic :
  forall val G (Heqx : snd (fst (modal_complexity_p_hseq G)) = 0%nat) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) acc1 acc2,
    FOL_R_formula_sem val (FOL_R_basic_case_aux G (map (@rev nat) (make_subsets (length G))) _ eq_refl acc2) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G 0%nat Heqx p Heqp acc1).
Proof.
  intros val G Heqx p Heqp acc1 acc2 Hf.
  destruct acc1 as [acc1].
  simpl.
  apply (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HMR_dec_formula_aux_inl :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl G1) acc1 acc2,
    FOL_R_formula_sem val (HMR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G _ Heqx _ Heqp acc1).
Proof.
  intros val G n heqx G1 Heqp acc1 acc2 Hf.
  destruct acc1 as [acc1].
  apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HMR_dec_formula_aux_inr :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1, G2)) acc1 acc2 acc3,
    FOL_R_formula_sem val (HMR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G2 _ eq_refl _ eq_refl acc3) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G _ Heqx _ Heqp acc1).
Proof.
  intros val G n heqx G1 G2 Heqp acc1 acc2 acc3 Hf1 Hf2.
  destruct acc1 as [acc1].
  split;
    [ apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1)
    | apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2) ].
Qed.

Lemma cond_HMR_dec_formula_aux_basic_inv :
  forall val G (Heqx : snd (fst (modal_complexity_p_hseq G)) = 0%nat) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) acc1 acc2,
    FOL_R_formula_sem val (HMR_dec_formula_aux G 0%nat Heqx p Heqp acc1) ->
    FOL_R_formula_sem val (FOL_R_basic_case_aux G (map (@rev nat) (make_subsets (length G))) _ eq_refl acc2).
Proof.
  intros val G Heqx p Heqp acc1 acc2 Hf.
  destruct acc1 as [acc1].
  simpl.
  apply (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HMR_dec_formula_aux_inl_inv :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl G1) acc1 acc2,
    FOL_R_formula_sem val (HMR_dec_formula_aux G _ Heqx _ Heqp acc1) ->
    FOL_R_formula_sem val (HMR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2).
Proof.
  intros val G n heqx G1 Heqp acc1 acc2 Hf.
  destruct acc1 as [acc1].
  simpl in Hf.
  refine (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HMR_dec_formula_aux_inr_inv :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1, G2)) acc1 acc2 acc3,
    FOL_R_formula_sem val (HMR_dec_formula_aux G _ Heqx _ Heqp acc1) ->
    (FOL_R_formula_sem val (HMR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2) *
     FOL_R_formula_sem val (HMR_dec_formula_aux G2 _ eq_refl _ eq_refl acc3)).
Proof.
  intros val G n heqx G1 G2 Heqp acc1 acc2 acc3 Hf.
  destruct acc1 as [acc1].
  destruct Hf as [Hf1 Hf2].
  split;
    [ apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1)
    | apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2) ].
Qed.

(* end hide *)

Definition FOL_R_basic_case G V := FOL_R_basic_case_aux G V _ eq_refl (wf_lt_nat4 _).

Definition HMR_dec_formula G := HMR_dec_formula_aux G _ eq_refl _ eq_refl (wf_lt_nat4 _).

Lemma cond_FOL_R_basic_case_no_diamond :
  forall val (G : p_hypersequent) (V : list (list nat)) (Heqn : max_diamond_p_hseq G = 0%nat),
    {v & prod (In_inf v V) (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v)))} ->
    FOL_R_formula_sem val (FOL_R_basic_case G V).
Proof.
  intros val G V Heqn H.
  apply (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ _ _ (FOL_R_basic_case_aux_sem_indep_n _ _ _ _ Heqn _ _ _ (cond_FOL_R_basic_case_aux_no_diamond _ _ _ Heqn (wf_lt_nat4 _) H))).
Qed.

Lemma cond_FOL_R_basic_case_diamond :
  forall val (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = S n),
    { v & prod (In_inf v V)
               (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G))
                                                  (FOL_R_and
                                                     (FOL_R_phi G v)
                                                     (HMR_dec_formula (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil))))) }->
    FOL_R_formula_sem val (FOL_R_basic_case G V).
Proof.
  intros val G V n Heqn [v [Hin Hf]].
  refine (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ _ _ (FOL_R_basic_case_aux_sem_indep_n _ _ _ _ Heqn _ _ _ (cond_FOL_R_basic_case_aux_diamond _ _ _ _ Heqn (wf_lt_nat4 _) _))).
  split with v.
  split with (wf_lt_nat4 _).
  split; auto.
Qed.

Lemma cond_FOL_R_basic_case_no_diamond_inv :
  forall val (G : p_hypersequent) (V : list (list nat)) (Heqn : max_diamond_p_hseq G = 0%nat),
    FOL_R_formula_sem val (FOL_R_basic_case G V) ->
    {v & prod (In_inf v V) (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v)))}.
Proof.
  intros val G V Heqn Hf.
  apply (cond_FOL_R_basic_case_aux_no_diamond_inv _ _ _ Heqn (wf_lt_nat4 _)).
  apply (FOL_R_basic_case_aux_sem_indep_n _ _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_FOL_R_basic_case_diamond_inv :
  forall val (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = S n),
    FOL_R_formula_sem val (FOL_R_basic_case G V) ->
    { v & prod (In_inf v V)
               (FOL_R_formula_sem val (exists_vec (seq (S (max_var_weight_p_hseq G)) (length G))
                                                  (FOL_R_and
                                                     (FOL_R_phi G v)
                                                     (HMR_dec_formula (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil))))) }.
Proof.
  intros val G V n Heqn Hf.
  destruct (cond_FOL_R_basic_case_aux_diamond_inv val _ V _ Heqn (wf_lt_nat4 _)) as [v [acc [Hin Hf']]].
  { apply (FOL_R_basic_case_aux_sem_indep_n _ _ _ _ _ _ _ _ Hf). }
  split with v.
  repeat split; auto.
  apply cond_FOL_R_exists_vec_formula_sem_inv in Hf' as [v' [Hin' [Hf1 Hf2]]].
  apply cond_FOL_R_exists_vec_formula_sem.
  split with v'; split ; [ | split]; auto.
  apply (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
Qed.

Lemma cond_HMR_dec_formula_basic :
  forall val G (Heqx : snd (fst (modal_complexity_p_hseq G)) = 0%nat),
    FOL_R_formula_sem val (FOL_R_basic_case G (map (@rev nat) (make_subsets (length G)))) ->
    FOL_R_formula_sem val (HMR_dec_formula G).
Proof.
  intros val G Heqn Hf.
  unfold HMR_dec_formula.
  refine (HMR_dec_formula_aux_sem_indep_n _ _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ (cond_HMR_dec_formula_aux_basic val G Heqn _ eq_refl _ _ Hf))).
  apply wf_lt_nat4.
Qed.

Lemma cond_HMR_dec_formula_inl :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl G1),
    FOL_R_formula_sem val (HMR_dec_formula G1) ->
    FOL_R_formula_sem val (HMR_dec_formula G).
Proof.
  intros val G n Heqx G1 Heqp Hf.
  unfold HMR_dec_formula in *.
  apply HMR_dec_formula_aux_sem_indep_n with (S n) Heqx.
  refine (HMR_dec_formula_aux_sem_indep_p _ _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ (cond_HMR_dec_formula_aux_inl _ _ _ _ _ _ _ _ Hf))); auto.
  apply wf_lt_nat4.
Qed.

Lemma cond_HMR_dec_formula_inr :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1, G2)),
    FOL_R_formula_sem val (HMR_dec_formula G1) ->
    FOL_R_formula_sem val (HMR_dec_formula G2) ->
    FOL_R_formula_sem val (HMR_dec_formula G).
Proof.
  intros val G n Heqx G1 G2 Heqp Hf1 Hf2.
  unfold HMR_dec_formula in *.
  apply HMR_dec_formula_aux_sem_indep_n with (S n) Heqx.
  refine (HMR_dec_formula_aux_sem_indep_p _ _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ (cond_HMR_dec_formula_aux_inr _ _ _ _ _ _ _ _ _ _ Hf1 Hf2))); auto.
  apply wf_lt_nat4.
Qed.

Lemma cond_HMR_dec_formula_basic_inv :
  forall val G (Heqx : snd (fst (modal_complexity_p_hseq G)) = 0%nat),
    FOL_R_formula_sem val (HMR_dec_formula G) ->
    FOL_R_formula_sem val (FOL_R_basic_case G (map (@rev nat) (make_subsets (length G)))).
Proof.
  intros val G Heqx Hf.
  unfold HMR_dec_formula in Hf.
  apply HMR_dec_formula_aux_sem_indep_n with _ _ _ _ _ Heqx _ _ _ in Hf.
  remember (wf_lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))).
  destruct a.
  refine (FOL_R_basic_case_aux_sem_indep_acc _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HMR_dec_formula_inl_inv :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl G1),
    FOL_R_formula_sem val (HMR_dec_formula G) ->
    FOL_R_formula_sem val (HMR_dec_formula G1).
Proof.
  intros val G n Heqx G1 Heqp Hf.
  unfold HMR_dec_formula in *.
  apply HMR_dec_formula_aux_sem_indep_n with _ _ _ _ (S n) Heqx _ _ _ in Hf.
  apply HMR_dec_formula_aux_sem_indep_p with _ _ _ _ _ _ _ Heqp _ in Hf.
  refine (cond_HMR_dec_formula_aux_inl_inv _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf)); auto.
  apply wf_lt_nat4.
Qed.

Lemma cond_HMR_dec_formula_inr_inv :
  forall val G n (Heqx : snd (fst (modal_complexity_p_hseq G)) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1, G2)),
    FOL_R_formula_sem val (HMR_dec_formula G) ->
    (FOL_R_formula_sem val (HMR_dec_formula G1) *
     FOL_R_formula_sem val (HMR_dec_formula G2)).
Proof.
  intros val G n Heqx G1 G2 Heqp Hf.
  unfold HMR_dec_formula in *.
  apply HMR_dec_formula_aux_sem_indep_n with _ _ _ _ (S n) Heqx _ _ _ in Hf.
  apply HMR_dec_formula_aux_sem_indep_p with _ _ _ _ _ _ _ Heqp _ in Hf.
  refine (cond_HMR_dec_formula_aux_inr_inv _ _ _ _ _ _ _ _ _ _ (HMR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf)).
  apply wf_lt_nat4.
Qed.

Lemma FOL_R_basic_case_1
      val
      (G : p_hypersequent)
      (Hwd : p_hseq_well_defined val G)
      (Hb : p_hseq_is_basic G)
      (pi : HMR_T (map (eval_p_sequent val) G))
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G, 0%nat)) :
  FOL_R_formula_sem val (FOL_R_basic_case G (map (@rev nat) (make_subsets (length G))))
with HMR_dec_formula_1
       val
       (G : p_hypersequent)
       (Hwd : p_hseq_well_defined val G)
       (pi : HMR_T (map (eval_p_sequent val) G))
       (acc : Acc lt_nat4 (modal_complexity_p_hseq G, 1%nat)) :
       FOL_R_formula_sem val (HMR_dec_formula G).
Proof.
  - destruct acc as [acc].
    remember (max_diamond_p_hseq G); symmetry in Heqn.
    destruct n;
      (apply HMR_le_frag with _ hmr_frag_T_M _ in pi; 
       [ | repeat split; auto]);
      destruct (lambda_prop _ (p_hseq_basic_hseq_basic _ _ Hb) pi) as [L [Hlen [[[Hex Hsum] Hone] Hstep]]].
    + apply cond_FOL_R_basic_case_no_diamond; auto.
      split with (pos_indexes L).
      split.
      { rewrite <- (rev_involutive (pos_indexes L)).
        apply in_inf_map.
        apply cond_is_in_make_subsets.
        - clear - Hex.
          apply rev_not_nil.
          induction L; [inversion Hex | ].
          inversion Hex; subst.
          + destruct a ; [ | exfalso; now apply H0 ].
            intros H; inversion H.
          + destruct a; [ intros H; inversion H | ].
            simpl.
            intros H'; apply map_eq_nil in H'.
            apply IHL; assumption.
        - intros i.
          case_eq (i <? length (rev (pos_indexes L)))%nat.
          + intros Hlt; apply Nat.ltb_lt in Hlt.
            apply Forall_inf_nth; try assumption.
            rewrite map_length in Hlen.
            rewrite <- Hlen.
            apply Forall_inf_rev.
            apply pos_indexes_Forall_inf.
          + intros Hlt; apply Nat.ltb_nlt in Hlt; rewrite nth_overflow; destruct G; simpl; try lia.
            apply HMR_not_empty in pi.
            exfalso; auto.            
        - intros i j Hlen' Hlt'.
          apply rev_reverse_order_lt; try lia.
          apply pos_indexes_order. }
      apply cond_FOL_R_exists_vec_formula_sem.
      split with (map oRpos_to_R L).
      split; [ rewrite map_length in Hlen; rewrite map_length; rewrite seq_length; symmetry; apply Hlen | ].
      repeat split.
      * apply cond_FOL_R_all_zero_formula_sem.
        intros n Hin.
        rewrite map_length in Hlen; rewrite <- Hlen.
        rewrite <- (map_length oRpos_to_R L).
        rewrite upd_val_vec_eq.
        rewrite nth_indep with _ _ _ _ (oRpos_to_R None).
        2:{ rewrite map_length; rewrite Hlen; apply (In_inf_complementary_lt _ _ _ Hin). }
        rewrite map_nth.
        rewrite pos_indexes_not_In_inf; auto.
        { rewrite Hlen; apply (In_inf_complementary_lt _ _ _ Hin). }
        intros Hin'.
        apply In_inf_complementary2 with (pos_indexes L) (length G) n; auto.
      * apply cond_FOL_R_all_gtz_formula_sem.
        intros n Hin.
        change (list (prod Rpos term)) with sequent.
        rewrite map_length in Hlen; rewrite <- Hlen.
        rewrite <- (map_length oRpos_to_R L).
        rewrite upd_val_vec_eq.
        assert (n < length L)%nat as Hlt.
        { apply (@Forall_inf_forall _ (fun x => x < length L)%nat) with (pos_indexes L); [ apply pos_indexes_Forall_inf | ].
          apply Hin. }
        rewrite nth_indep with _ _ _ _ (oRpos_to_R None); auto.
        2:{ rewrite map_length; apply Hlt. }
        rewrite map_nth.
        destruct (pos_indexes_nth L n) as [[r Hr] Heq].
        { apply Hin. }
        rewrite Heq; simpl.
        clear - Hr; apply R_blt_lt in Hr; apply Hr.
      * apply cond_FOL_R_all_atoms_eq_formula_sem.
        intros n Hlen'.
        rewrite map_length in Hlen; rewrite <- Hlen.
        simpl.
        specialize (Hsum n).
        rewrite sum_weight_with_coeff_eq_var_covar in Hsum.
        rewrite (sum_weight_with_coeff_eval_eq val n G L) in Hsum.
        lra.
      * rewrite map_length in Hlen.
        simpl.
        rewrite sum_weight_with_coeff_eq_one_coone in Hone.
        rewrite (sum_weight_with_coeff_one_eval_eq val G L) in Hone.
        rewrite <- Hlen.
        lra.
    + apply cond_FOL_R_basic_case_diamond with n; auto.
      split with (pos_indexes L).
      split.
      { rewrite <- (rev_involutive (pos_indexes L)).
        apply in_inf_map.
        apply cond_is_in_make_subsets.
        - apply rev_not_nil.
          clear - Hex.
          induction L; [inversion Hex | ].
          inversion Hex; subst.
          + destruct a ; [ | exfalso; now apply H0 ].
            intros H; inversion H.
          + destruct a; [ intros H; inversion H | ].
            simpl.
            intros H'; apply map_eq_nil in H'.
            apply IHL; assumption.
        - intros i.
          apply rev_nth_all_lt.
          clear i.
          intros i.
          case_eq (i <? length (pos_indexes L))%nat.
          + intros Hlt; apply Nat.ltb_lt in Hlt.
            apply Forall_inf_nth; try assumption.
            rewrite map_length in Hlen.
            rewrite <- Hlen.
            apply pos_indexes_Forall_inf.
          + intros Hlt; apply Nat.ltb_nlt in Hlt; rewrite nth_overflow; destruct G; simpl; try lia.
            apply HMR_not_empty in pi.
            exfalso; auto.            
        - intros i j Hlen' Hlt'.
          apply rev_reverse_order_lt; try lia.
          apply pos_indexes_order. }
      apply cond_FOL_R_exists_vec_formula_sem.
      split with (map oRpos_to_R L).
      split; [ rewrite map_length in Hlen; rewrite map_length; rewrite seq_length; symmetry; apply Hlen | ].
      split.
      * repeat split.
        -- apply cond_FOL_R_all_zero_formula_sem.
           intros m Hin.
           rewrite map_length in Hlen; rewrite <- Hlen.
           rewrite <- (map_length oRpos_to_R L).
           rewrite upd_val_vec_eq.
           rewrite nth_indep with _ _ _ _ (oRpos_to_R None).
           2:{ rewrite map_length; rewrite Hlen; apply (In_inf_complementary_lt _ _ _ Hin). }
           rewrite map_nth.
           rewrite pos_indexes_not_In_inf; auto.
           { rewrite Hlen; apply (In_inf_complementary_lt _ _ _ Hin). }
           intros Hin'.
           apply In_inf_complementary2 with (pos_indexes L) (length G) m; auto.
        -- apply cond_FOL_R_all_gtz_formula_sem.
           intros m Hin.
           change (list (prod Rpos term)) with sequent.
           rewrite map_length in Hlen; rewrite <- Hlen.
           rewrite <- (map_length oRpos_to_R L).
           rewrite upd_val_vec_eq.
           assert (m < length L)%nat as Hlt.
           { apply (@Forall_inf_forall _ (fun x => x < length L)%nat) with (pos_indexes L); [ apply pos_indexes_Forall_inf | ].
             apply Hin. }
           rewrite nth_indep with _ _ _ _ (oRpos_to_R None); auto.
           2:{ rewrite map_length; apply Hlt. }
           rewrite map_nth.
           destruct (pos_indexes_nth L m) as [[r Hr] Heq].
           { apply Hin. }
           rewrite Heq; simpl.
           clear - Hr; apply R_blt_lt in Hr; apply Hr.
        -- apply cond_FOL_R_all_atoms_eq_formula_sem.
           intros m Hlen'.
           rewrite map_length in Hlen; rewrite <- Hlen.
           simpl.
           specialize (Hsum m).
           rewrite sum_weight_with_coeff_eq_var_covar in Hsum.
           rewrite (sum_weight_with_coeff_eval_eq val m G L) in Hsum.
           lra.
        -- simpl.
           rewrite map_length in Hlen; rewrite <- Hlen.
           rewrite sum_weight_with_coeff_eq_one_coone in Hone.
           rewrite (sum_weight_with_coeff_one_eval_eq val G L) in Hone.
           lra.
      * refine (HMR_dec_formula_1 (upd_val_vec val (seq  _ _) _) _ _ _ _).
        -- rewrite flat_map_concat_map.
           apply Forall_inf_cons ; [ | apply Forall_inf_nil].
           apply forall_Forall_inf.
           intros A HinA.
           apply In_inf_concat in HinA as [l [Hin1 Hin2]].
           apply in_inf_map_inv in Hin1 as [i Heq Hin3].
           rewrite <- Heq in Hin2.
           apply In_inf_seq_mul in Hin2 as [[b B] [HeqB HinB]].
           rewrite HeqB.
           simpl.
           rewrite map_length in Hlen.
           rewrite <- Hlen.
           rewrite <- map_length with _ _ oRpos_to_R _.
           change (S (max_var_weight_p_hseq G + i)) with ((S (max_var_weight_p_hseq G)) + i)%nat.
           rewrite upd_val_vec_eq.
           rewrite FOL_R_term_sem_upd_val_vec_lt.
           2:{ apply forall_Forall_inf.
               intros x Hinx.
               apply Nat.lt_le_trans with (S (max_var_weight_p_hseq G)).
               - apply Nat.le_lt_trans with (max_var_weight_p_seq (only_diamond_p_seq (nth i G nil))).
                 + apply max_var_FOL_R_term_In_inf_p_seq with B; auto.
                 + apply Nat.le_lt_trans with (max_var_weight_p_seq (nth i G nil)) ; [ apply max_var_weight_p_seq_only_diamond | ].
                   apply Nat.le_lt_trans with (max_var_weight_p_hseq G) ; [ | lia ].
                   apply max_var_weight_p_seq_In_inf_p_hseq.
                   apply nth_In_inf.
                   rewrite <- Hlen.
                   apply In_inf_pos_indexes; auto.
               - apply (In_inf_seq_le_start _ _ _ Hinx). }
           apply R_blt_lt.
           apply Rmult_lt_0_compat.
           ++ rewrite nth_indep with _ _ _ _ (oRpos_to_R None).
              2:{ rewrite map_length.
                  apply In_inf_pos_indexes; auto. }
              rewrite map_nth.
              destruct (pos_indexes_nth _ _ Hin3) as [[r Hr] Heqr].
              rewrite Heqr; simpl.
              clear - Hr; apply R_blt_lt in Hr; apply Hr.
           ++ change b with (fst (b , B)).
              apply R_blt_lt.
              refine (@Forall_inf_forall _ (fun x => (0 <? FOL_R_term_sem val (fst x)) = true) (only_diamond_p_seq (nth i G nil)) _ (b, B) _); auto.
              apply p_seq_well_defined_only_diamond.
              refine (@Forall_inf_forall _ (p_seq_well_defined val) G _ (nth i G nil) _); auto.
              apply nth_In_inf.
              rewrite <- Hlen.
              apply In_inf_pos_indexes; auto. 
        -- replace (fun i : nat => seq_mul (FOL_R_var i) (only_diamond_p_seq (nth i G nil)))
             with (fun i : nat => seq_mul (FOL_R_var i) (nth i (only_diamond_p_hseq G) nil)).
           2:{ apply functional_extensionality.
               intros x.
               rewrite <- (map_nth only_diamond_p_seq); reflexivity. }
           simpl; rewrite map_length in Hlen; rewrite <- Hlen.
           replace (flat_map
                      (fun i : nat =>
                         seq_mul (FOL_R_var (S (max_var_weight_p_hseq G + i)))
                                 (only_diamond_p_seq (nth i G nil))) (pos_indexes L))
             with (flat_map
                     (fun i : nat =>
                        seq_mul (FOL_R_var ((S (max_var_weight_p_hseq G)) + i))
                                ((nth i (only_diamond_p_hseq G) nil))) (pos_indexes L)).
           2:{ apply flat_map_ext.
               intros a.
               rewrite <- (map_nth _ G nil).
               reflexivity. }
           rewrite eval_p_seq_upd_val_vec_nth.
           ++ apply hmrr_M_elim; rewrite  <- only_diamond_eval_p_hseq; apply Hstep.
           ++ change (only_diamond_p_hseq G) with (map only_diamond_p_seq G).
              rewrite map_length.
              symmetry; apply Hlen.
           ++ apply Nat.le_lt_trans with (max_var_weight_p_hseq G); try lia.
              rewrite max_var_weight_p_hseq_only_diamond.
              apply Nat.le_refl.
        -- apply acc.
           apply fst_lt4.
           rewrite Heqn.
           rewrite flat_map_concat_map.
           simpl.
           rewrite Nat.max_0_r.
           apply max_diamond_p_seq_concat.
           apply forall_Forall_inf.
           intros x Hinx.
           apply in_inf_map_inv in Hinx as [i Heq Hini].
           rewrite <- Heq.
           rewrite max_diamond_seq_mul.
           rewrite <- Heqn.
           rewrite <- map_nth.
           apply Nat.le_lt_trans with (max_diamond_p_hseq (map only_diamond_p_seq G)).
           ++ apply max_diamond_nth.
           ++ apply max_diamond_only_diamond_p_hseq_lt.
              lia.
  - destruct acc as [acc].
    remember (snd (fst (modal_complexity_p_hseq G))).
    destruct n;
      [ |
        remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G)) ].
    + apply cond_HMR_dec_formula_basic; auto.
      refine (FOL_R_basic_case_1 val G Hwd _ pi _).
      { apply p_hseq_is_basic_complexity_0_inv; auto. }
      apply acc.
      apply fth_lt4.
      lia.
    + destruct s as [G1 | [G1 G2] ].
      * apply (cond_HMR_dec_formula_inl val G n (eq_sym Heqn) G1 (eq_sym Heqs)).
        refine (HMR_dec_formula_1 val G1 _ _ _).
        -- eapply apply_logical_rule_on_p_hypersequent_inl_well_defined; [ symmetry; apply Heqs | ].
           apply p_hseq_put_non_basic_fst_well_defined; auto.
           simpl in Heqn; rewrite <- Heqn; lia.
        -- apply hmrr_M_elim.
           eapply apply_logical_rule_on_p_hypersequent_inl_HMR; [ symmetry; apply Heqs | | ].
           ++ apply p_hseq_put_non_basic_fst_well_defined; auto.
              simpl in Heqn; rewrite <- Heqn; lia.
           ++ unfold p_hseq_put_non_basic_fst.
              rewrite map_cons.
              apply hmrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
              { apply Permutation_Type_eval_p_sequent.
                apply p_seq_put_non_basic_fst.
                intros H.
                apply p_seq_is_basic_complexity_0 in H.
                rewrite p_hseq_p_seq_max_complexity_correct in H.
                simpl in *; lia. }
              apply hmrr_ex_hseq with (map (eval_p_sequent val) G); auto ; [ | eapply HMR_le_frag ; [ | apply pi]; repeat split; auto ].
              rewrite <- map_cons.
              apply Permutation_Type_map.
              apply p_hseq_put_max_complexity_fst.
              intros H; rewrite H in Heqn; inversion Heqn.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           apply (apply_logical_rule_on_p_hypersequent_correct_inl G G1 n (eq_sym Heqn) (eq_sym Heqs)).
      * apply (cond_HMR_dec_formula_inr val G n (eq_sym Heqn) G1 G2 (eq_sym Heqs)).
        -- refine (HMR_dec_formula_1 val G1 _ _ _).
           ++ eapply apply_logical_rule_on_p_hypersequent_inr_l_well_defined; [ symmetry; apply Heqs | ].
              apply p_hseq_put_non_basic_fst_well_defined; auto.
              simpl in Heqn; rewrite <- Heqn; lia.
           ++ apply hmrr_M_elim.
              eapply apply_logical_rule_on_p_hypersequent_inr_l_HMR; [ symmetry; apply Heqs | | ].
              ** apply p_hseq_put_non_basic_fst_well_defined; auto.
                 simpl in Heqn; rewrite <- Heqn; lia.
              ** unfold p_hseq_put_non_basic_fst.
                 rewrite map_cons.
                 apply hmrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
                 { apply Permutation_Type_eval_p_sequent.
                   apply p_seq_put_non_basic_fst.
                   intros H.
                   apply p_seq_is_basic_complexity_0 in H.
                   rewrite p_hseq_p_seq_max_complexity_correct in H.
                   simpl in *; lia. }
                 apply hmrr_ex_hseq with (map (eval_p_sequent val) G); auto ; [ | eapply HMR_le_frag ; [ | apply pi]; repeat split; auto ].
                 rewrite <- map_cons.
                 apply Permutation_Type_map.
                 apply p_hseq_put_max_complexity_fst.
                 intros H; rewrite H in Heqn; inversion Heqn.
           ++ apply acc.
              apply lt_nat3_to_lt_nat4.
              apply (apply_logical_rule_on_p_hypersequent_correct_inr_l G G1 G2 n (eq_sym Heqn) (eq_sym Heqs)).
        -- refine (HMR_dec_formula_1 val G2 _ _ _).
           ++ eapply apply_logical_rule_on_p_hypersequent_inr_r_well_defined; [ symmetry; apply Heqs | ].
              apply p_hseq_put_non_basic_fst_well_defined; auto.
              simpl in Heqn; rewrite <- Heqn; lia.
           ++ apply hmrr_M_elim.
              eapply apply_logical_rule_on_p_hypersequent_inr_r_HMR; [ symmetry; apply Heqs | | ].
              ** apply p_hseq_put_non_basic_fst_well_defined; auto.
                 simpl in Heqn; rewrite <- Heqn; lia.
              ** unfold p_hseq_put_non_basic_fst.
                 rewrite map_cons.
                 apply hmrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
                 { apply Permutation_Type_eval_p_sequent.
                   apply p_seq_put_non_basic_fst.
                   intros H.
                   apply p_seq_is_basic_complexity_0 in H.
                   rewrite p_hseq_p_seq_max_complexity_correct in H.
                   simpl in *; lia. }
                 apply hmrr_ex_hseq with (map (eval_p_sequent val) G); auto ; [ | eapply HMR_le_frag ; [ | apply pi]; repeat split; auto ].
                 rewrite <- map_cons.
                 apply Permutation_Type_map.
                 apply p_hseq_put_max_complexity_fst.
                 intros H; rewrite H in Heqn; inversion Heqn.
           ++ apply acc.
              apply lt_nat3_to_lt_nat4.
              apply (apply_logical_rule_on_p_hypersequent_correct_inr_r G G1 G2 n (eq_sym Heqn) (eq_sym Heqs)).
Qed.

Lemma FOL_R_basic_case_2
      val
      (G : p_hypersequent)
      (Hwd : p_hseq_well_defined val G)
      (Hb : p_hseq_is_basic G)
      (Hf : FOL_R_formula_sem val (FOL_R_basic_case G (map (@rev nat) (make_subsets (length G)))))
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G, 0%nat)) :
  HMR_T (map (eval_p_sequent val) G)
with HMR_dec_formula_2
       val
       (G : p_hypersequent)
       (Hwd : p_hseq_well_defined val G)
       (Hf : FOL_R_formula_sem val (HMR_dec_formula G))
       (acc : Acc lt_nat4 (modal_complexity_p_hseq G, 1%nat)) :
       HMR_T (map (eval_p_sequent val) G).
Proof.
  - destruct acc as [acc].
    remember (max_diamond_p_hseq G).
    destruct n.
    + apply cond_FOL_R_basic_case_no_diamond_inv in Hf; auto.
      destruct Hf as [vx [Hinvx Hf]].
      apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [vr [Hlen [Hf1 [Hf2 [Hf3 Hf4]]]]].
      apply hmrr_M_elim.
      apply lambda_prop_inv ; [apply p_hseq_basic_hseq_basic; auto | ].
      split with (map (fun x => eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_var x)) (seq (S (max_var_weight_p_hseq G)) (length G))).
      repeat split.
      * rewrite ? map_length.
        rewrite seq_length; auto.
      * apply in_inf_map_inv in Hinvx as [vxr Heq Hin].
        apply cond_is_in_make_subsets_inv in Hin as [[Hnnil Hle] Hlt].
        destruct vxr ; [ exfalso; apply Hnnil; auto | ].
        apply nth_Exists_inf with n None.
        -- rewrite map_length.
           rewrite seq_length.
           apply (Hle 0)%nat.
        -- rewrite nth_indep with _ _ _ _ ((fun x => eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_var x)) 0%nat).
           2:{ rewrite map_length.
               rewrite seq_length.
               apply (Hle 0)%nat. }
           rewrite (map_nth (fun x => eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_var x))).
           apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ n in Hf2.
           2:{ rewrite <- Heq.
               apply in_inf_rev.
               left; auto. }
           unfold eval_to_oRpos.
           simpl.
           rewrite seq_nth.
           2:{ apply (Hle 0)%nat. }
           unfold R_to_oRpos.
           case (R_order_dec
                      (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr
                                   (S (max_var_weight_p_hseq G) + n)));
             intros e; try (exfalso; try apply R_blt_lt in e; lra).
           intros H; inversion H.
      * intros n.
        case_eq (n <=? max_var_p_hseq G)%nat; intros Hle.
        -- apply cond_FOL_R_all_atoms_eq_formula_sem_inv with _ _ _ n in Hf3 ; [ | apply Nat.leb_le in Hle; auto].
           replace (map
                     (fun x : nat =>
                        eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)
                                      (FOL_R_var x)) (seq (S (max_var_weight_p_hseq G)) (length G))) with
               (map (eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) by (now rewrite map_map).
           simpl in Hf3.
           apply Rminus_diag_eq in Hf3.
           rewrite FOL_R_term_sem_eval_p_hseq in Hf3.
           2:{ apply forall_Forall_inf.
               intros x Hinx.
               apply in_inf_map_inv in Hinx as [i Heqi Hini].
               apply In_inf_nth with _ _ _ 0%nat in Hini as [k Hltk Heqk].
               rewrite <- Heqi; rewrite <- Heqk.
               rewrite seq_length in Hlen.
               rewrite Hlen.
               rewrite seq_nth.
               2:{ rewrite <- Hlen.
                   rewrite seq_length in Hltk.
                   apply Hltk. }
               simpl.
               rewrite <- Nat.add_succ_l.
               rewrite (upd_val_vec_eq vr val k (S (max_var_weight_p_hseq G))).
               destruct (in_inf_dec Nat.eq_dec k vx); auto.
               - apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ k in Hf2; auto.
                 rewrite Hlen in Hf2.
                 rewrite upd_val_vec_eq in Hf2.
                 lra.
               - apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ k in Hf1.
                 2:{ apply In_inf_complementary2_inv; auto.
                     rewrite seq_length in Hltk.
                     apply Hltk. }
                 rewrite Hlen in Hf1.
                 rewrite upd_val_vec_eq in Hf1.
                 lra. }
           rewrite sum_weight_with_coeff_eq_var_covar.
           replace (map (eval_p_sequent (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) G) with (map (eval_p_sequent val) G) in Hf3; auto.
           symmetry; apply eval_p_hseq_upd_val_vec_lt.
           apply forall_Forall_inf.
           intros x Hinx.
           apply In_inf_seq_le_start in Hinx.
           lia.
        -- apply Nat.leb_nle in Hle.
           clear - Hle.
           rewrite sum_weight_with_coeff_eq_var_covar.
           assert (H := max_var_hseq_le_p_hseq val G).
           rewrite sum_weight_var_with_coeff_lt_max_var; [ | lia ].
           rewrite sum_weight_covar_with_coeff_lt_max_var; [ | lia ].
           lra.
      * replace (map
                   (fun x : nat =>
                      eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)
                                    (FOL_R_var x)) (seq (S (max_var_weight_p_hseq G)) (length G))) with
            (map (eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) by (now rewrite map_map).
        simpl in Hf4.
        apply Rminus_diag_le in Hf4.
        rewrite FOL_R_term_sem_eval_p_hseq_one in Hf4.
        2:{ apply forall_Forall_inf.
            intros x Hinx.
            apply in_inf_map_inv in Hinx as [i Heqi Hini].
            apply In_inf_nth with _ _ _ 0%nat in Hini as [k Hltk Heqk].
            rewrite <- Heqi; rewrite <- Heqk.
            rewrite seq_length in Hlen.
            rewrite Hlen.
            rewrite seq_nth.
            2:{ rewrite <- Hlen.
                rewrite seq_length in Hltk.
                apply Hltk. }
            simpl.
            rewrite <- Nat.add_succ_l.
            rewrite (upd_val_vec_eq vr val k (S (max_var_weight_p_hseq G))).
            destruct (in_inf_dec Nat.eq_dec k vx); auto.
            - apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ k in Hf2; auto.
              rewrite Hlen in Hf2.
              rewrite upd_val_vec_eq in Hf2.
              lra.
            - apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ k in Hf1.
              2:{ apply In_inf_complementary2_inv; auto.
                  rewrite seq_length in Hltk.
                  apply Hltk. }
              rewrite Hlen in Hf1.
              rewrite upd_val_vec_eq in Hf1.
              lra. }
        rewrite sum_weight_with_coeff_eq_one_coone.
        replace (map (eval_p_sequent (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) G) with (map (eval_p_sequent val) G) in Hf4; auto.
        symmetry; apply eval_p_hseq_upd_val_vec_lt.
        apply forall_Forall_inf.
        intros x Hinx.
        apply In_inf_seq_le_start in Hinx.
        lia.
      * set (val' := (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)).
        set (L := (map (fun x : nat => eval_to_oRpos val' (FOL_R_var x))
                       (seq (S (max_var_weight_p_hseq G)) (length G)))).
        set (T := flat_map (fun i : nat =>
                              seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i))
                                      (only_diamond_p_seq (nth i G nil))) (pos_indexes L)).
        remember T; clear - Heqn Hf1 Hf2 Hf3 Hf4 Hlen.
        destruct (concat_with_coeff_mul_only_diamond_decomp_no_diamond (map (eval_p_sequent val) G) L) as [[r s] [Hperm Heq]].
        { assert (H := max_diamond_eval_p_hseq val G).
          lia. }
        rewrite concat_with_coeff_mul_only_diamond.
        apply hmrr_ex_seq with (hseq.vec s HMR_coone ++ hseq.vec r HMR_one ++ nil); [ Permutation_Type_solve | ].
        apply hmrr_one ; [ | apply hmrr_INIT].
        replace (map
                     (fun x : nat =>
                        eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)
                                      (FOL_R_var x)) (seq (S (max_var_weight_p_hseq G)) (length G))) with
               (map (eval_to_oRpos (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) by (now rewrite map_map).
        simpl in Hf4.
        apply Rminus_diag_le in Hf4.
        rewrite FOL_R_term_sem_eval_p_hseq_one in Hf4.
        2:{ apply forall_Forall_inf.
            intros x Hinx.
            apply in_inf_map_inv in Hinx as [i Heqi Hini].
            apply In_inf_nth with _ _ _ 0%nat in Hini as [k Hltk Heqk].
            rewrite <- Heqi; rewrite <- Heqk.
            rewrite seq_length in Hlen.
            rewrite Hlen.
            rewrite seq_nth.
            2:{ rewrite <- Hlen.
                rewrite seq_length in Hltk.
                apply Hltk. }
            simpl.
            rewrite <- Nat.add_succ_l.
            rewrite (upd_val_vec_eq vr val k (S (max_var_weight_p_hseq G))).
            destruct (in_inf_dec Nat.eq_dec k vx); auto.
            - apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ k in Hf2; auto.
              rewrite Hlen in Hf2.
              rewrite upd_val_vec_eq in Hf2.
              lra.
            - apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ k in Hf1.
              2:{ apply In_inf_complementary2_inv; auto.
                  rewrite seq_length in Hltk.
                  apply Hltk. }
              rewrite Hlen in Hf1.
              rewrite upd_val_vec_eq in Hf1.
              lra. }
        rewrite sum_weight_with_coeff_eq_one_coone in Heq.
        replace (map (eval_p_sequent (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) G) with (map (eval_p_sequent val) G) in Hf4.
        2:{ symmetry; apply eval_p_hseq_upd_val_vec_lt.
            apply forall_Forall_inf.
            intros x Hinx.
            apply In_inf_seq_le_start in Hinx.
            lia. }
        unfold L in Heq; unfold val' in Heq.
        rewrite map_map in Hf4.
        lra.
    + apply cond_FOL_R_basic_case_diamond_inv with _ _ _ n in Hf; auto.
      destruct Hf as [vx [Hinvx Hf]].
      apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [vr [Hlen [[Hf1 [Hf2 [Hf3 Hf4]]] Hf5]]].
      apply hmrr_M_elim.
      apply lambda_prop_inv ; [apply p_hseq_basic_hseq_basic; auto | ].
      split with (map R_to_oRpos vr).
      repeat split.
      * rewrite ? map_length.
        rewrite seq_length in Hlen; auto.
      * apply in_inf_map_inv in Hinvx as [vxr Heq Hin].
        apply cond_is_in_make_subsets_inv in Hin as [[Hnnil Hle] Hlt].
        destruct vxr ; [ exfalso; apply Hnnil; auto | ].
        apply nth_Exists_inf with n0 None.
        -- rewrite map_length.
           rewrite seq_length in Hlen.
           rewrite <- Hlen.
           apply (Hle 0)%nat.
        -- rewrite nth_indep with _ _ _ _ (R_to_oRpos 0).
           2:{ rewrite map_length.
               rewrite seq_length in Hlen.
               rewrite <- Hlen.
               apply (Hle 0)%nat. }
           rewrite map_nth.
           apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ n0 in Hf2.
           2:{ rewrite <- Heq.
               apply in_inf_rev.
               left; auto. }
           unfold R_to_oRpos.
           rewrite seq_length in Hlen; rewrite Hlen in Hf2.
           rewrite upd_val_vec_eq in Hf2.
           rewrite nth_indep with _ _ _ _ 0 in Hf2.
           2:{ rewrite <- Hlen.
               apply (Hle 0)%nat. }
           case (R_order_dec (nth n0 vr 0));
             intros e; try (exfalso; try apply R_blt_lt in e; lra).
           intros H; inversion H.
      * intros n0.
        case_eq (n0 <=? max_var_p_hseq G)%nat; intros Hle.
        -- apply cond_FOL_R_all_atoms_eq_formula_sem_inv with _ _ _ n0 in Hf3 ; [ | apply Nat.leb_le in Hle; auto].
           simpl in Hf3.
           apply Rminus_diag_eq in Hf3.
           rewrite FOL_R_term_sem_eval_p_hseq in Hf3.
           2:{ apply forall_Forall_inf.
               intros x Hinx.
               apply in_inf_map_inv in Hinx as [i Heqi Hini].
               apply In_inf_nth with _ _ _ 0%nat in Hini as [k Hltk Heqk].
               rewrite <- Heqi; rewrite <- Heqk.
               rewrite seq_length in Hlen.
               rewrite Hlen.
               rewrite seq_nth.
               2:{ rewrite <- Hlen.
                   rewrite seq_length in Hltk.
                   apply Hltk. }
               simpl.
               rewrite <- Nat.add_succ_l.
               rewrite (upd_val_vec_eq vr val k (S (max_var_weight_p_hseq G))).
               destruct (in_inf_dec Nat.eq_dec k vx); auto.
               - apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ k in Hf2; auto.
                 rewrite Hlen in Hf2.
                 rewrite upd_val_vec_eq in Hf2.
                 lra.
               - apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ k in Hf1.
                 2:{ apply In_inf_complementary2_inv; auto.
                     rewrite seq_length in Hltk.
                     apply Hltk. }
                 rewrite Hlen in Hf1.
                 rewrite upd_val_vec_eq in Hf1.
                 lra. }
           rewrite sum_weight_with_coeff_eq_var_covar.
           replace (map (eval_p_sequent (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) G) with (map (eval_p_sequent val) G) in Hf3; auto.
           2:{ symmetry; apply eval_p_hseq_upd_val_vec_lt.
               apply forall_Forall_inf.
               intros x Hin.
               apply In_inf_seq_le_start in Hin.
               lia. }
           rewrite seq_length in Hlen.
           rewrite Hlen in Hf3.
           rewrite eval_to_oRpos_eq in Hf3.
           apply Hf3.
        -- apply Nat.leb_nle in Hle.
           clear - Hle.
           rewrite sum_weight_with_coeff_eq_var_covar.
           assert (H := max_var_hseq_le_p_hseq val G).
           rewrite sum_weight_var_with_coeff_lt_max_var; [ | lia ].
           rewrite sum_weight_covar_with_coeff_lt_max_var; [ | lia ].
           lra.
      * simpl in Hf4.
        apply Rminus_diag_le in Hf4.
        rewrite FOL_R_term_sem_eval_p_hseq_one in Hf4.
        2:{ apply forall_Forall_inf.
            intros x Hinx.
            apply in_inf_map_inv in Hinx as [i Heqi Hini].
            apply In_inf_nth with _ _ _ 0%nat in Hini as [k Hltk Heqk].
            rewrite <- Heqi; rewrite <- Heqk.
            rewrite seq_length in Hlen.
            rewrite Hlen.
            rewrite seq_nth.
            2:{ rewrite <- Hlen.
                rewrite seq_length in Hltk.
                apply Hltk. }
            simpl.
            rewrite <- Nat.add_succ_l.
            rewrite (upd_val_vec_eq vr val k (S (max_var_weight_p_hseq G))).
            destruct (in_inf_dec Nat.eq_dec k vx); auto.
            - apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ k in Hf2; auto.
              rewrite Hlen in Hf2.
              rewrite upd_val_vec_eq in Hf2.
              lra.
            - apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ k in Hf1.
              2:{ apply In_inf_complementary2_inv; auto.
                  rewrite seq_length in Hltk.
                  apply Hltk. }
              rewrite Hlen in Hf1.
              rewrite upd_val_vec_eq in Hf1.
              lra. }
        rewrite sum_weight_with_coeff_eq_one_coone.
        replace (map (eval_p_sequent (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)) G) with (map (eval_p_sequent val) G) in Hf4; auto.
        2:{ symmetry; apply eval_p_hseq_upd_val_vec_lt.
            apply forall_Forall_inf.
            intros x Hin.
            apply In_inf_seq_le_start in Hin.
            lia. }
        rewrite seq_length in Hlen.
        rewrite Hlen in Hf4.
        rewrite eval_to_oRpos_eq in Hf4.
        apply Hf4.
      * set (val' := (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr)).
        revert Hf4;
          set (T := flat_map (fun i : nat =>
                              seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i))
                                      (only_diamond_p_seq (nth i G nil))) vx); intros Hf4.
        specialize (HMR_dec_formula_2 val' (T :: nil)).
        assert (p_hseq_well_defined val' (T :: nil)) as Hwd'.
        { unfold val'; unfold T.
          rewrite flat_map_concat_map.
          apply Forall_inf_cons ; [ | apply Forall_inf_nil].
          apply forall_Forall_inf.
          intros A HinA.
          apply In_inf_concat in HinA as [l [Hin1 Hin2]].
          apply in_inf_map_inv in Hin1 as [i Heq Hin3].
          assert (i < length G)%nat as Hlti.
          { apply in_inf_map_inv in Hinvx as [vx' Heq' Hinvx'].
            apply cond_is_in_make_subsets_inv in Hinvx' as [[_ H1] _].
            rewrite <- Heq' in Hin3.
            apply in_inf_rev_inv in Hin3.
            apply In_inf_nth with _ _ _ 0%nat in Hin3 as [i' Hleni Heqi].
            rewrite <- Heqi.
            apply H1. }
          rewrite <- Heq in Hin2.
          apply In_inf_seq_mul in Hin2 as [[b B] [HeqB HinB]].
          rewrite HeqB.
          simpl.
          rewrite seq_length in Hlen.
          rewrite Hlen.
          change (S (max_var_weight_p_hseq G + i)) with ((S (max_var_weight_p_hseq G)) + i)%nat.
          rewrite upd_val_vec_eq.
          rewrite FOL_R_term_sem_upd_val_vec_lt.
          2:{ apply forall_Forall_inf.
              intros x Hinx.
              apply Nat.lt_le_trans with (S (max_var_weight_p_hseq G)).
              - apply Nat.le_lt_trans with (max_var_weight_p_seq (only_diamond_p_seq (nth i G nil))).
                + apply max_var_FOL_R_term_In_inf_p_seq with B; auto.
                + apply Nat.le_lt_trans with (max_var_weight_p_seq (nth i G nil)) ; [ apply max_var_weight_p_seq_only_diamond | ].
                  apply Nat.le_lt_trans with (max_var_weight_p_hseq G) ; [ | lia ].
                  apply max_var_weight_p_seq_In_inf_p_hseq.
                  apply nth_In_inf.
                  apply Hlti.
              - apply (In_inf_seq_le_start _ _ _ Hinx). }
          apply R_blt_lt.
          apply Rmult_lt_0_compat.
          ++ apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ i in Hf2; auto.
             rewrite Hlen in Hf2; rewrite (upd_val_vec_eq vr val i) in Hf2.
             apply Hf2.
          ++ change b with (fst (b , B)).
             apply R_blt_lt.
             refine (@Forall_inf_forall _ (fun x => (0 <? FOL_R_term_sem val (fst x)) = true) (only_diamond_p_seq (nth i G nil)) _ (b, B) _); auto.
             apply p_seq_well_defined_only_diamond.
             refine (@Forall_inf_forall _ (p_seq_well_defined val) G _ (nth i G nil) _); auto.
             apply nth_In_inf.
             apply Hlti. }
        specialize (HMR_dec_formula_2 Hwd' Hf5).
        unfold val' in HMR_dec_formula_2; unfold T in HMR_dec_formula_2.
        replace (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil)))
             with (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (nth i (only_diamond_p_hseq G) nil)) in HMR_dec_formula_2.
        2:{ apply functional_extensionality.
            intros x.
            rewrite <- (map_nth only_diamond_p_seq); reflexivity. }
        simpl in HMR_dec_formula_2.
        replace vx with (pos_indexes (map R_to_oRpos vr)) in HMR_dec_formula_2.
        2:{ symmetry; apply pos_indexes_cond.
            - intros i j Hltj Hltij.
              apply in_inf_map_inv in Hinvx as [vxr Heqvxr Hinvxr].
              apply cond_is_in_make_subsets_inv in Hinvxr as [Hnil H].
              rewrite <- Heqvxr.
              apply rev_reverse_order; try rewrite Heqvxr; try lia.
              intros i' j' Hltj' Hltij'.
              apply H; auto.
            - intros i Hlti.
              rewrite map_length.
              rewrite <- Hlen.
              rewrite seq_length.
              apply in_inf_map_inv in Hinvx as [vxr Heqvxr Hinvxr].
              apply cond_is_in_make_subsets_inv in Hinvxr as [[Hnil H] H'].
              rewrite <- Heqvxr.
              rewrite rev_nth; try (rewrite <- Heqvxr in Hlti; rewrite rev_length in Hlti; lia).
              apply H.
            - intros i Hin.
              apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ i in Hf2; auto.
              apply in_inf_map_inv in Hinvx as [vxr Heqvxr Hinvxr].
              apply cond_is_in_make_subsets_inv in Hinvxr as [[Hnil H'] H].
              rewrite seq_length in Hlen; rewrite Hlen in Hf2.
              rewrite upd_val_vec_eq in Hf2.
              replace (@None Rpos) with (R_to_oRpos 0) at 1.
              2:{ unfold R_to_oRpos.
                  case R_order_dec; intro e; try (exfalso; simpl in *; apply R_blt_lt in e; lra); auto. }
              rewrite map_nth.
              unfold R_to_oRpos.
              rewrite nth_indep with _ _ _ _ 0 in Hf2.
              2:{ rewrite <- Heqvxr in Hin.
                  apply in_inf_rev_inv in Hin.
                  apply In_inf_nth with _ _ _ 0%nat in Hin as [k Hltk Heqk].
                  rewrite <- Heqk.
                  rewrite <- Hlen.
                  apply H'. }
              case (R_order_dec (nth i vr 0)); intros e; try (intro Heq; now inversion Heq).
              exfalso.
              lra.
            - intros i Hlti Hneq.
              destruct (in_inf_dec Nat.eq_dec i vx); auto.
              exfalso.
              rewrite seq_length in Hlen.
              apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ i in Hf1.
              2:{ apply In_inf_complementary2_inv.
                  rewrite Hlen.
                  rewrite map_length in Hlti; apply Hlti.
                  apply f. }
              rewrite Hlen in Hf1.
              rewrite upd_val_vec_eq in Hf1.
              replace (@None Rpos) with (R_to_oRpos 0) in Hneq at 1.
              2:{ unfold R_to_oRpos.
                  case R_order_dec; intro e; try (exfalso; simpl in *; apply R_blt_lt in e; lra); auto. }
              rewrite map_nth in Hneq.
              rewrite nth_indep with _ _ _ _ 0 in Hf1.
              2:{ rewrite map_length in Hlti.
                  apply Hlti. }
              rewrite Hf1 in Hneq.
              apply Hneq.
              unfold R_to_oRpos.
              case (R_order_dec 0); intros e; try (exfalso; simpl in *; apply R_blt_lt in e; lra).
              reflexivity. }
        rewrite seq_length in Hlen.
        rewrite Hlen in HMR_dec_formula_2.
        pattern vr in HMR_dec_formula_2 at 3.
        replace vr with (map oRpos_to_R (map R_to_oRpos vr)) in HMR_dec_formula_2 .
        2:{ rewrite map_map.
            apply nth_ext with 0 0.
            { rewrite map_length; auto. }
            intros n0.
            case_eq (n0 <? length vr)%nat; intros Hltn0.
            2:{ apply Nat.ltb_nlt in Hltn0.
                rewrite nth_overflow; [|rewrite map_length; lia ].
                rewrite nth_overflow; try lia.
                reflexivity. }
            apply Nat.ltb_lt in Hltn0.
            rewrite nth_indep with _ _ _ _ (oRpos_to_R (R_to_oRpos 0)).
            2:{ rewrite map_length; lia. }
            rewrite (map_nth (fun x => oRpos_to_R (R_to_oRpos x))).
            destruct (in_inf_dec Nat.eq_dec n0 vx); auto.
            - apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ n0 in Hf2; auto.
              rewrite Hlen in Hf2.
              rewrite upd_val_vec_eq in Hf2.
              rewrite nth_indep with _ _ _ _ 0 in Hf2; auto.
              unfold R_to_oRpos.
              case (R_order_dec (nth n0 vr 0)); intros e;
                try (exfalso; simpl in *; try apply R_blt_lt in e; lra).
              reflexivity.
            - apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ n0 in Hf1.
              2:{ apply In_inf_complementary2_inv; auto.
                  rewrite Hlen.
                  apply Hltn0. }
              rewrite Hlen in Hf1.
              rewrite upd_val_vec_eq in Hf1.
              rewrite nth_indep with _ _ _ _ 0 in Hf1; auto.
              unfold R_to_oRpos.
              case (R_order_dec (nth n0 vr 0)); intros e;
                try (exfalso; simpl in *; try apply R_blt_lt in e; lra).
              rewrite e;
                reflexivity. }
        rewrite <- (map_length R_to_oRpos vr) in HMR_dec_formula_2.
        rewrite eval_p_seq_upd_val_vec_nth in HMR_dec_formula_2.
        2:{ change (only_diamond_p_hseq G) with (map only_diamond_p_seq G).
            rewrite 2 map_length; auto. }
        2:{ eapply Nat.le_lt_trans; [ apply max_var_weight_p_hseq_only_diamond | ].
            lia. }
        apply (HMR_le_frag (hmr_frag_T)) ; [ repeat split; auto | ].
        rewrite only_diamond_eval_p_hseq.
        apply HMR_dec_formula_2.
        apply acc.
        apply fst_lt4.
        simpl.
        rewrite (max_diamond_seq_mul_nth _ _ (S (max_var_weight_p_hseq G))).
        rewrite flat_map_concat_map.
        simpl.
        rewrite Nat.max_0_r.
        rewrite <- Heqn.
        apply max_diamond_p_seq_concat.
        apply forall_Forall_inf.
        intros x Hinx.
        apply in_inf_map_inv in Hinx as [i Heq Hini].
        rewrite <- Heq.
        apply Nat.le_lt_trans with (max_diamond_p_hseq (map only_diamond_p_seq G)).
        ++ apply max_diamond_nth.
        ++ rewrite Heqn.
           apply max_diamond_only_diamond_p_hseq_lt.
           lia.           
  - destruct acc as [acc].
    remember (snd (fst (modal_complexity_p_hseq G))).
    destruct n.
    { refine (FOL_R_basic_case_2 val G Hwd _ _ _).
      - apply p_hseq_is_basic_complexity_0_inv.
        simpl in Heqn; auto.
      - apply cond_HMR_dec_formula_basic_inv in Hf; auto.
      - apply acc.
        apply fth_lt4; lia. }
    apply hmrr_ex_hseq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G) :: map (eval_p_sequent val) (p_hseq_without_max_complexity G)).
    { rewrite <- map_cons.
      apply Permutation_Type_map.
      symmetry; apply p_hseq_put_max_complexity_fst.
      destruct G; [ inversion Heqn | intros H; inversion H]. }
    apply hmrr_ex_seq with (eval_p_sequent val (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G))).
    { apply Permutation_Type_eval_p_sequent.
      symmetry; apply p_seq_put_non_basic_fst.
      intros Hb; apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb.
      simpl in *; lia. }
    remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G)).
    destruct s as [G1 | [G1 G2]].
    + rewrite <- map_cons.
      apply hmrr_M_elim.
      refine (apply_logical_rule_on_p_hypersequent_inl_HMR_inv val _ G1 (eq_sym Heqs) _ _).
      * apply p_hseq_put_non_basic_fst_well_defined; auto.
        simpl in Heqn; lia.
      * apply (HMR_le_frag hmr_frag_T _); [ repeat split; auto | ].
        refine (HMR_dec_formula_2 val G1 _ _ _).
        -- apply apply_logical_rule_on_p_hypersequent_inl_well_defined with (p_hseq_put_non_basic_fst G); auto.
           apply p_hseq_put_non_basic_fst_well_defined; auto.
           simpl in Heqn; lia.
        -- apply (cond_HMR_dec_formula_inl_inv val G n (eq_sym Heqn) G1) in Hf; auto.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           apply apply_logical_rule_on_p_hypersequent_correct_inl with n; auto.
    + rewrite <- map_cons.
      apply hmrr_M_elim.
      refine (apply_logical_rule_on_p_hypersequent_inr_HMR_inv val _ G1 G2 (eq_sym Heqs) _ _ _).
      * apply p_hseq_put_non_basic_fst_well_defined; auto.
        simpl in Heqn; lia.
      * apply (HMR_le_frag hmr_frag_T _); [ repeat split; auto | ].
        refine (HMR_dec_formula_2 val G1 _ _ _).
        -- apply apply_logical_rule_on_p_hypersequent_inr_l_well_defined with (p_hseq_put_non_basic_fst G) G2; auto.
           apply p_hseq_put_non_basic_fst_well_defined; auto.
           simpl in Heqn; lia.
        -- apply (cond_HMR_dec_formula_inr_inv val G n (eq_sym Heqn) G1 G2) in Hf as [Hf1 _ ]; auto.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 n; auto.
      * apply (HMR_le_frag hmr_frag_T _); [ repeat split; auto | ].
        refine (HMR_dec_formula_2 val G2 _ _ _).
        -- apply apply_logical_rule_on_p_hypersequent_inr_r_well_defined with (p_hseq_put_non_basic_fst G) G1; auto.
           apply p_hseq_put_non_basic_fst_well_defined; auto.
           simpl in Heqn; lia.
        -- apply (cond_HMR_dec_formula_inr_inv val G n (eq_sym Heqn) G1 G2) in Hf as [_ Hf2]; auto.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 n; auto.
Qed.

(** there exists a formula \phi_G such that \phi_G(\vec r) has a proof if and only if G[\vec r /\vec x] has a proof *) 
Lemma HMR_FOL_R_equiv : forall G,
    { f & forall val, p_hseq_well_defined val G ->
                      prod
                        (HMR_full (map (eval_p_sequent val) G) -> FOL_R_formula_sem val f)
                        (FOL_R_formula_sem val f -> HMR_full (map (eval_p_sequent val) G)) }.
Proof.
  enough (forall G,
             { f & forall val, p_hseq_well_defined val G ->
                               prod
                                (HMR_T (map (eval_p_sequent val) G) -> FOL_R_formula_sem val f)
                                (FOL_R_formula_sem val f -> HMR_T (map (eval_p_sequent val) G)) }).
  { intros G.
    specialize (X G) as [f H].
    split with f.
    intros val H'.
    destruct (H val) as [H1 H2]; try assumption.
    split.
    - intros pi.
      apply H1.
      apply hmrr_M_elim.
      apply hmrr_can_elim.
      apply pi.
    - intros Hf.
      refine (HMR_le_frag _ _ _ _ (H2 Hf)).
      repeat split; auto. }
  intros G.
  split with (HMR_dec_formula G).
  intros val Hwd.
  split.
  - intros pi.
    apply HMR_dec_formula_1; auto.
    apply wf_lt_nat4.
  - intros Hf.
    apply HMR_dec_formula_2; auto.
    apply wf_lt_nat4.
Qed.

Lemma p_HMR_decidable : forall val G,
    p_hseq_well_defined val G ->
    (HMR_full (map (eval_p_sequent val) G)) + (HMR_full (map (eval_p_sequent val) G) -> False).
Proof.
  intros val G Hwd.
  destruct (HMR_FOL_R_equiv G) as [f [H1 H2]]; [ apply Hwd | ].
  destruct (FOL_R_decidable f) with val.
  - left.
    apply H2; apply f0.
  - right.
    intros pi; apply f0; apply H1; apply pi.
Qed.

(** Theorem 4.11 *)
Lemma HMR_decidable : forall G,
    (HMR_full G) + (HMR_full G -> False).
Proof.
  intros G.
  rewrite <- (eval_p_hypersequent_to_p_hypersequent) with (fun x => 0) _.
  apply p_HMR_decidable.
  apply to_p_hypersequent_well_defined.
Qed.
