Require Import Rpos.
Require Import riesz_logic_List_more.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.p_hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.invertibility.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.M_elim.
Require Import RL.hmr.decidability.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import Omega.
Require Import ZArith Psatz.
Require Import FunctionalExtensionality.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.
  
(** Necessary definition *)
Fixpoint complexity_A n :=
  match n with
  | 0 => HMR_var 0
  | S n => (<S> (complexity_A n)) \/S (<S> (complexity_A n))
  end.


(** Size of the formula return by the decidability algorithm *)

Definition H_shape i j k (T : p_sequent) :=
  {' (r, s) : _ & prod (Permutation_Type T (vec r (<S> (complexity_A i)) ++ vec s (complexity_A (S i))))
                       ((length r = j) *
                        (length s = k))}.

Lemma H_shape_complexity : forall i j k T,
    H_shape i j k T ->
    HMR_complexity_p_seq T = k.
Proof.
  intros i j k T Hshape.
  destruct Hshape as [[r s] [Hperm [H1 H2]]].
  rewrite complexity_p_seq_perm with _ (vec r (<S> complexity_A i) ++ vec s (complexity_A (S i))); auto.
  rewrite complexity_p_seq_app.
  rewrite 2 complexity_p_seq_vec; rewrite H2; rewrite H1.
  simpl.
  lia.
Qed.

Lemma p_seq_fst_non_basic_term_H_shape :
  forall i j k T,
    H_shape i j (S k) T ->
    {r & p_seq_fst_non_basic_term T = (r, complexity_A (S i))}.
Proof.
  intros i j k T Hshape; revert i j k Hshape; induction T; intros i j k Hshape.
  - destruct Hshape as [[r s] [Hperm [H1 H2]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; rewrite 2 vec_length in Hperm; simpl in *; lia.
  - destruct a as [a A].
    simpl p_seq_fst_non_basic_term.
    destruct Hshape as [[r s] [Hperm [H1 H2]]].
    assert (In_inf (a, A) (vec r (<S> complexity_A i) ++ vec s (complexity_A (S i)))).
    { apply Permutation_Type_in_inf with ((a, A) :: T); auto.
      left; reflexivity. }
    apply in_inf_app_or in X.
    destruct X.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (<S> complexity_A i)) with false.
      2:{ symmetry; apply Nat.ltb_nlt; simpl; lia. }
      apply in_inf_split in Hin as [[ra rb] Heqr].
      refine (IHT i (length (ra ++ rb)) k _).
      split with (ra ++ rb, s).
      repeat split.
      * rewrite Heqr in Hperm.
        rewrite vec_app in *.
        simpl in *.
        Permutation_Type_solve.
      * apply H2.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (complexity_A (S i))) with true.
      2:{ symmetry; apply Nat.ltb_lt; simpl; lia. }
      split with a; auto.
Qed.

Lemma p_seq_without_fst_non_basic_term_H_shape :
  forall i j k T,
    H_shape i j (S k) T ->
    H_shape i j k (p_seq_without_fst_non_basic_term T).
Proof.
  intros i j k T Hshape; revert i j k Hshape; induction T; intros i j k Hshape.
  - destruct Hshape as [[r s] [Hperm [H1 H2]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; rewrite 2 vec_length in Hperm; simpl in *; lia.
  - destruct a as [a A].
    simpl p_seq_fst_non_basic_term.
    destruct Hshape as [[r s] [Hperm [H1 H2]]].
    assert (In_inf (a, A) (vec r (<S> complexity_A i) ++ vec s (complexity_A (S i)))).
    { apply Permutation_Type_in_inf with ((a, A) :: T); auto.
      left; reflexivity. }
    apply in_inf_app_or in X.
    destruct X.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (<S> complexity_A i)) with false.
      2:{ symmetry; apply Nat.ltb_nlt; simpl; lia. }
      apply in_inf_split in Hin as [[ra rb] Heqr].
      assert (H_shape i (length (ra ++ rb)) (S k) T).
      { split with (ra ++ rb, s).
        repeat split.
        * rewrite Heqr in Hperm.
          rewrite vec_app in *.
          simpl in *.
          Permutation_Type_solve.
        * apply H2. }
      specialize (IHT i (length (ra ++ rb)) k X).
      destruct IHT as [[r' s'] [Hperm' [H1' H2']]].
      split with (a :: r', s').
      repeat split.
      * simpl in *.
        Permutation_Type_solve.
      * rewrite Heqr; rewrite app_length in *; simpl; lia.
      * apply H2'.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (complexity_A (S i))) with true.
      2:{ symmetry; apply Nat.ltb_lt; simpl; lia. }
      simpl.
      apply in_inf_split in Hin as [[sa sb] Heq].
      split with (r, sa ++ sb).
      repeat split.
      * rewrite Heq in Hperm; rewrite vec_app in *.
        simpl in *; Permutation_Type_solve.
      * rewrite Heq in H2; rewrite app_length in *.
        simpl in *; lia.
Qed.

Lemma Forall_inf_H_shape_complexity_not_nil : forall i j k G,
    G <> nil ->
    Forall_inf (H_shape i j k) G ->
    fst (HMR_complexity_p_hseq G) = k.
Proof.
  intros i j k G Hnnil Hall.
  induction G; [ exfalso; contradiction | ].
  inversion Hall; subst.
  destruct G.
  - simpl.
    rewrite H_shape_complexity with i j k _; auto.
    case_eq (k =? 0); intros H; auto.
    apply Nat.eqb_eq in H.
    simpl; lia.
  - clear Hnnil; assert (p :: G <> nil) as Hnnil.
    { intros H; inversion H. }
    specialize (IHG Hnnil X0).
    remember (p :: G); clear - IHG X.
    simpl.
    rewrite IHG.
    rewrite H_shape_complexity with i j k _; auto.
    rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma Forall_inf_H_shape_complexity_le : forall i j k G,
    Forall_inf (H_shape i j k) G ->
    fst (HMR_complexity_p_hseq G) <= k.
Proof.
  intros i j k G Hall.
  induction G; [ simpl; lia | ].
  inversion Hall; subst.
  specialize (IHG X0).
  simpl.
  apply H_shape_complexity in X.
  case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H); simpl; try lia.
  replace (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) with false; simpl; try lia.
  symmetry; apply Nat.ltb_nlt; lia.
Qed.
  
Definition H_shape_hseq i j k l (G : p_hypersequent) :=
  {' (G1, G2) : _ & prod (Permutation_Type G (G1 ++ G2))
                         ((length G2 = l) *
                          (Forall_inf (H_shape i (S j) k) G1) *
                          (Forall_inf (H_shape i j (S k)) G2))}.

Lemma H_shape_hseq_complexity_S_l : forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    fst (HMR_complexity_p_hseq G) = S k.
Proof.
  intros i j k l G Hshape.
  destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
  rewrite complexity_p_hseq_perm with _ (G1 ++ G2); auto.
  rewrite complexity_p_hseq_app.
  apply Forall_inf_H_shape_complexity_le in H2.
  apply Forall_inf_H_shape_complexity_not_nil in H3.
  2:{ intros H; subst; inversion H1. }
  lia.
Qed.

Lemma H_shape_hseq_complexity_le : forall i j k l G,
    H_shape_hseq i j k l G ->
    fst (HMR_complexity_p_hseq G) <= S k.
Proof.
  intros i j k l G Hshape.
  destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
  rewrite complexity_p_hseq_perm with _ (G1 ++ G2); auto.
  rewrite complexity_p_hseq_app.
  apply Forall_inf_H_shape_complexity_le in H2.
  apply Forall_inf_H_shape_complexity_le in H3.
  lia.
Qed.

Lemma p_hseq_without_max_complexity_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    H_shape_hseq i j k l (p_hseq_without_max_complexity G).
Proof.
  intros i j k l G Hshape.
  induction G.
  - destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; simpl in Hperm.
    exfalso; lia.
  - assert (Hc := H_shape_hseq_complexity_S_l i j k l (a :: G) Hshape).
    destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    simpl.
    case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * apply Forall_inf_forall with _ _ _ a in H2; auto.
        apply H_shape_complexity in H2.
        apply Nat.leb_le in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; lia.
      * apply in_inf_split in i0 as [[G2a G2b] Heq]; subst.
        split with (G1, (G2a ++ G2b)).
        repeat split.
        -- Permutation_Type_solve.
        -- rewrite app_length in *; simpl in H1; lia.
        -- apply H2.
        -- apply Forall_inf_app; [ apply Forall_inf_app_l in H3 | apply Forall_inf_app_r in H3; inversion H3]; assumption.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * assert (H_shape_hseq i j k (S l) G).
        { apply in_inf_split in i0 as [[G1a G1b] Heq]; subst.
          split with ((G1a ++ G1b), G2).
          repeat split.
          - Permutation_Type_solve.
          - apply H1.
          - apply Forall_inf_app; [ apply Forall_inf_app_l in H2 | apply Forall_inf_app_r in H2; inversion H2]; assumption.
          - apply H3. }
        specialize (IHG X).
        destruct IHG as [[G1' G2'] [Hperm' [ [H1' H2'] H3']]].
        split with (a :: G1', G2'); repeat split; try auto.
        -- Permutation_Type_solve.
        -- apply Forall_inf_cons; auto.
           apply Forall_inf_forall with _ _ _ a in H2; auto.
      * assert (H_shape_hseq i j k l G).
        { apply in_inf_split in i0 as [[G2a G2b] Heq]; subst.
          split with (G1, (G2a ++ G2b)).
          repeat split.
          - Permutation_Type_solve.
          - rewrite app_length in *; simpl in H1; lia.
          - apply H2.
          - apply Forall_inf_app; [ apply Forall_inf_app_l in H3 | apply Forall_inf_app_r in H3; inversion H3]; assumption. }
        apply Forall_inf_forall with _ _ _ a in H3; auto.
        apply H_shape_complexity in H3.
        apply Nat.leb_nle in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; try lia.
        apply H_shape_hseq_complexity_le in X.
        lia.
Qed.

Lemma p_hseq_p_seq_max_complexity_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    H_shape i j (S k) (p_hseq_p_seq_max_complexity G).
Proof.
  intros i j k l G Hshape.
  induction G.
  - destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; simpl in Hperm.
    exfalso; lia.
  - assert (Hc := H_shape_hseq_complexity_S_l i j k l (a :: G) Hshape).
    destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    simpl.
    case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * apply Forall_inf_forall with _ _ _ a in H2; auto.
        apply H_shape_complexity in H2.
        apply Nat.leb_le in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; lia.
      * apply Forall_inf_forall with _ _ _ a in H3; auto.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * apply IHG.
        apply in_inf_split in i0 as [[G1a G1b] Heq]; subst.
        split with ((G1a ++ G1b), G2).
        repeat split.
        -- Permutation_Type_solve.
        -- apply H1.
        -- apply Forall_inf_app; [ apply Forall_inf_app_l in H2 | apply Forall_inf_app_r in H2; inversion H2]; assumption.
        -- apply H3.
      * assert (H_shape_hseq i j k l G).
        { apply in_inf_split in i0 as [[G2a G2b] Heq]; subst.
          split with (G1, (G2a ++ G2b)).
          repeat split.
          - Permutation_Type_solve.
          - rewrite app_length in *; simpl in H1; lia.
          - apply H2.
          - apply Forall_inf_app; [ apply Forall_inf_app_l in H3 | apply Forall_inf_app_r in H3; inversion H3]; assumption. }
        apply Forall_inf_forall with _ _ _ a in H3; auto.
        apply H_shape_complexity in H3.
        apply Nat.leb_nle in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; try lia.
        apply H_shape_hseq_complexity_le in X.
        lia.
Qed.  

Lemma p_hseq_put_non_basic_fst_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    {' (r, T, H) & prod (p_hseq_put_non_basic_fst G = ((r, complexity_A (S i)) :: T) :: H)
                        ((H_shape i j k T) *
                         (H_shape_hseq i j k l H)) }.
Proof.
  intros i j k l G Hshape.
  unfold p_hseq_put_non_basic_fst.
  assert (Hshape_max_c := p_hseq_p_seq_max_complexity_H_shape i j k l G Hshape).
  assert (Hshape_wo_max_c := p_hseq_without_max_complexity_H_shape i j k l G Hshape).
  assert (Hshape_T := p_seq_without_fst_non_basic_term_H_shape i j k _ Hshape_max_c).
  destruct (p_seq_fst_non_basic_term_H_shape i j k _ Hshape_max_c) as [r A].
  split with (r, p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G), p_hseq_without_max_complexity G); repeat split; auto.
  rewrite A; reflexivity.
Qed.

Lemma apply_logical_rule_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    { H & prod (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl H)
               (H_shape_hseq i j k l H) }.
Proof.
  intros i j k l G Hshape.
  destruct (p_hseq_put_non_basic_fst_H_shape i j k l G Hshape) as [[[r T] H] [Heq [Hshape1 Hshape2]]].
  remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G)).
  destruct s.
  - remember (p_hseq_put_non_basic_fst G) as H'.
    clear HeqH'.
    split with p; split; [reflexivity |].
    destruct H'.
    + inversion Heq.
    + destruct l0.
      * inversion Heq.
      * destruct p0 as [a A].
        inversion Heq; subst.
        simpl in Heqs.
        inversion Heqs; subst.
        destruct Hshape2 as [[G1 G2] [Hperm [[H1 H2] H3]]].
        split with (((r, <S> complexity_A i) :: T) :: ((r, <S> complexity_A i) :: T) :: G1, G2).
        repeat split.
        -- Permutation_Type_solve.
        -- apply H1.
        -- destruct Hshape1 as [[r' s'] [Hperm' [H1' H2']]].
           repeat apply Forall_inf_cons.
           ++ split with (r :: r', s').
              repeat split.
              ** simpl; Permutation_Type_solve.
              ** simpl; lia.
              ** apply H2'.
           ++ split with (r :: r', s').
              repeat split.
              ** simpl; Permutation_Type_solve.
              ** simpl; lia.
              ** apply H2'.
           ++ apply H2.
        -- apply H3.
  - rewrite Heq in Heqs.
    inversion Heqs.
Qed.

Lemma H_shape_hseq_0 :
  forall i j k G,
    H_shape_hseq i j (S k) 0 G ->
    H_shape_hseq i (S j) k (length G) G.
Proof.
  intros i j k G Hshape.
  destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
  split with (nil, G1).
  destruct G2; [ | inversion H1].
  repeat split; auto.
  - Permutation_Type_solve.
  - apply Permutation_Type_length in Hperm.
    rewrite app_length in Hperm; simpl in Hperm; lia.
Qed.

Lemma nb_exists_FOL_R_basic_case_aux_indep_acc (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = n) (acc1 acc2 : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc1) =
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc2)
with nb_exists_HMR_dec_formula_aux_indep_acc (G : p_hypersequent) (x: nat) (Heqx : snd (fst (modal_complexity_p_hseq G)) = x) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) (acc1 acc2 : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
         nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc1) =
         nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc2).
Proof.
  - destruct acc1 as [acc1]; destruct acc2 as [acc2].
    destruct V; destruct n.
    + reflexivity.
    + reflexivity.
    + simpl.
      apply f_equal2_plus; [ reflexivity | ].
      refine (nb_exists_FOL_R_basic_case_aux_indep_acc _ _ _ _ (acc1 _ _) (acc2 _ _)).
    + simpl; rewrite ? nb_exists_FOL_R_exists_vec; simpl.
      repeat (apply f_equal2_plus; try reflexivity).
      * refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
      * refine (nb_exists_FOL_R_basic_case_aux_indep_acc _ _ _ _ (acc1 _ _) (acc2 _ _)).
  - destruct acc1 as [acc1]; destruct acc2 as [acc2].
    destruct x.
    + simpl.
      refine (nb_exists_FOL_R_basic_case_aux_indep_acc _ _ _ _ (acc1 _ _) (acc2 _ _)).
    + destruct p.
      * refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
      * destruct p.
        simpl; apply f_equal2_plus.
        -- refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
        -- refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
Qed.

Fixpoint nb_exists_FOL_R_basic_aux_sub 
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = S n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  forall v,
    In_inf v V ->
    nb_exists_FOL_R_formula (HMR_dec_formula_aux (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil)
                         _
                         (eq_refl _)
                         _
                         (eq_refl _)
                         (Acc_inv acc _
                                  (lt_nat3_to_lt_nat4
                                     _
                                     _
                                     _
                                     _
                                     (modal_complexity_only_diamond_p_seq _ _ _ _ Heqn)))) <= nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V (S n) Heqn acc).
Proof.
  intros v Hin.
  destruct acc as [acc].
  destruct V; inversion Hin; subst.
  - simpl; rewrite nb_exists_FOL_R_exists_vec.
    simpl; lia.
  - transitivity (nb_exists_FOL_R_formula
                    (FOL_R_basic_case_aux G V (S n) Heqn
                                          (acc
                                             (modal_complexity_p_hseq G,
                                              (fix length (l : list (list nat)) : nat :=
                                                 match l with
                                                 | nil => 0
                                                 | _ :: l' => S (length l')
                                                 end) V)
                                             (lt_nat4_last (modal_complexity_p_hseq G)
                                                           ((fix length (l : list (list nat)) : nat :=
                                                               match l with
                                                               | nil => 0
                                                               | _ :: l' => S (length l')
                                                               end) V)
                                                           (S
                                                              ((fix length (l : list (list nat)) : nat :=
                                                                  match l with
                                                                  | nil => 0
                                                                  | _ :: l' => S (length l')
                                                                  end) V))
                                                           (Nat.lt_succ_diag_r
                                                              ((fix length (l : list (list nat)) : nat :=
                                                                  match l with
                                                                  | nil => 0
                                                                  | _ :: l' => S (length l')
                                                                  end) V)))))); [ | simpl; lia].
    etransitivity.
    2:{ refine (nb_exists_FOL_R_basic_aux_sub G V n Heqn _ v X). }
    apply Nat.eq_le_incl.
    apply nb_exists_HMR_dec_formula_aux_indep_acc.
Qed.

Lemma H_shape_hseq_only_diamond :
  forall i j n G,
    G <> nil ->
    H_shape_hseq (S i) j 0 0 G ->
    H_shape_hseq i 0 (pred (length G * (S j))) 1 (flat_map (fun i0 : nat => seq_mul (FOL_R_var (n + i0)) (only_diamond_p_seq (nth i0 G nil))) (seq 0 (length G)) :: nil).
Proof.
  intros i j n G Hnnil Hshape.
  split with (nil , (flat_map
                       (fun i0 : nat =>
                          seq_mul (FOL_R_var (n + i0))
                                  (only_diamond_p_seq (nth i0 G nil))) (seq 0 (length G)) :: nil)).
  repeat split; auto.
  destruct Hshape as [[G1 G2] [Hperm [[H1 H2] _]]].
  destruct G2; [ clear H1 | exfalso; simpl in *; lia].
  rewrite app_nil_r in Hperm.
  apply Forall_inf_Permutation_Type with _ _ _ G in H2; [ | symmetry; apply Hperm].
  clear - H2 Hnnil.
  revert n.
  induction G; [ contradiction | ].
  intros n.
  destruct G.
  - simpl.
    rewrite app_nil_r.
    apply Forall_inf_cons; [ | apply Forall_inf_nil].
    inversion H2; subst.
    destruct X as [[r s] [Hperm [H3 H4]]].
    destruct s; [ | exfalso; simpl in*; lia].
    split with (nil, mul_vec (FOL_R_var (n + 0)) r).
    repeat split.
    + simpl.
      simpl in Hperm.
      rewrite app_nil_r in Hperm.
      destruct (Permutation_Type_vec_decomp _ _ _ Hperm) as [vs [Heqvr Hpermvr]].
      rewrite Heqvr.
      rewrite only_diamond_p_seq_vec_diamond.
      rewrite seq_mul_vec_eq_vec_mul_vec.
      apply Permutation_Type_vec.
      apply Permutation_Type_mul_vec.
      symmetry; apply Hpermvr.
    + rewrite mul_vec_length.
      lia.
  - assert (p :: G <> nil) by (intros H; inversion H).
    remember (p :: G) as G'.
    inversion H2.
    specialize (IHG H X0 (S n)).
    clear G HeqG' Hnnil H1 H3 X0 x l.
    simpl.
    rewrite <- seq_shift.
    rewrite flat_map_map.
    apply Forall_inf_cons; [ | apply Forall_inf_nil].
    inversion IHG; subst.
    clear X1.
    destruct X0 as [[r s] [Hperm [Hr Hs]]].
    destruct r; [ | exfalso; simpl in *; lia ].
    clear Hr.
    split with (nil, mul_vec (FOL_R_var (n + 0)) (map fst (only_diamond_p_seq a)) ++ s).
    repeat split.
    + simpl.
      rewrite vec_app.
      apply Permutation_Type_app.
      2:{ erewrite flat_map_ext; [apply Hperm |].
          intros x; simpl.
          replace (n + S x) with (S (n + x)) by lia.
          reflexivity. }
      destruct X as [[ra sa] [Hperma [Hra Hsa]]].
      destruct sa; [ | exfalso; simpl in *; lia].
      simpl in *.
      rewrite app_nil_r in Hperma.
      transitivity (vec (mul_vec (FOL_R_var (n + 0)) ra) (<S> complexity_A i \/S <S> complexity_A i)).
      * rewrite <- seq_mul_vec_eq_vec_mul_vec.
        apply seq_mul_perm.
        replace (vec ra (<S> complexity_A i \/S <S> complexity_A i)) with (only_diamond_p_seq (vec ra (<S> (<S> complexity_A i \/S <S> complexity_A i)))).
        2:{ apply only_diamond_p_seq_vec_diamond. }
        apply only_diamond_p_seq_perm.
        apply Hperma.
      * rewrite <- 2 seq_mul_vec_eq_vec_mul_vec.
        apply seq_mul_perm.
        apply Permutation_Type_vec.
        destruct (Permutation_Type_vec_decomp _ _ _ Hperma) as [vs [Heqvs Hpermvs]].
        rewrite Heqvs.
        rewrite only_diamond_p_seq_vec_diamond.
        rewrite Heqvs in Hperma.
        apply Permutation_Type_vec_inv in Hperma.
        etransitivity ; [symmetry; apply Hperma |].
        clear.
        induction vs; simpl; auto.
    + rewrite app_length; rewrite mul_vec_length.
      rewrite map_length.
      destruct X as [[ra sa] [Hperma [Hra Hsa]]].
      destruct sa; [ | exfalso; simpl in *; lia].
      simpl in Hperma.
      rewrite app_nil_r in Hperma.
      replace (length (only_diamond_p_seq a)) with (length (vec ra (<S> complexity_A i \/S <S> complexity_A i))).
      * rewrite vec_length.
        destruct G'; [ contradiction | ].
        simpl; simpl in Hs.
        lia.        
      * replace (vec ra (<S> complexity_A i \/S <S> complexity_A i)) with (only_diamond_p_seq (vec ra (<S> (<S> complexity_A i \/S <S> complexity_A i)))).
        2:{ apply only_diamond_p_seq_vec_diamond. }
        apply Permutation_Type_length.
        apply only_diamond_p_seq_perm.
        symmetry; apply Hperma.
Qed.

Lemma nb_exists_HMR_dec_formula_aux_complexity_basic
      (G : p_hypersequent)
      x
      (Heqx : snd (fst (modal_complexity_p_hseq G)) = x)
      p
      (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
  forall acc',
    x = 0 ->
    nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc) =
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux
                               G
                               (map (@rev nat) (make_subsets (length G)))
                               _
                               (eq_refl _)
                               acc').
Proof.
  intros acc' Heq0.
  destruct acc as [acc].
  destruct x; inversion Heq0.
  simpl.
  apply nb_exists_FOL_R_basic_case_aux_indep_acc.
Qed.

Lemma nb_exists_FOL_R_all_zero :
  forall k v,
    nb_exists_FOL_R_formula (FOL_R_all_zero k v) = 0.
Proof.
  intros k v.
  induction v; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_all_gtz :
  forall k v,
    nb_exists_FOL_R_formula (FOL_R_all_gtz k v) = 0.
Proof.
  intros k v.
  induction v; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_all_atoms_eq :
  forall G k,
    nb_exists_FOL_R_formula (FOL_R_all_atoms_eq G k) = 0.
Proof.
  intros G k.
  induction k; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_phi : forall G l, nb_exists_FOL_R_formula (FOL_R_phi G l) = 0.
Proof.
  intros G l; simpl.
  rewrite nb_exists_FOL_R_all_zero.
  rewrite nb_exists_FOL_R_all_gtz.
  rewrite nb_exists_FOL_R_all_atoms_eq.
  reflexivity.
Qed.

Fixpoint nb_exists_FOL_R_basic_case_aux_complexity_no_diamond
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  n = 0 ->
  nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc) = length G * length V.
Proof.
  intros H.
  destruct acc as [acc].
  destruct n; inversion H.
  destruct V.
  - simpl; lia.
  - simpl.
    rewrite nb_exists_FOL_R_exists_vec.
    rewrite (nb_exists_FOL_R_basic_case_aux_complexity_no_diamond G V
                                                                  0%nat
                                                                  Heqn
                                                                  (acc _
                                                                       (lt_nat4_last
                                                                          _
                                                                          _
                                                                     _
                                                                     (Nat.lt_succ_diag_r _)))); auto.
    rewrite seq_length.
    rewrite nb_exists_FOL_R_phi.
    symmetry.
    lia.
Qed.

Fixpoint nb_exists_FOL_R_basic_case_aux_complexity_le
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  length G * length V <= nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc).
Proof.
  destruct acc as [acc].
  destruct n.
  { rewrite nb_exists_FOL_R_basic_case_aux_complexity_no_diamond; auto. }
  destruct V.
  - simpl; lia.
  - simpl.
    rewrite nb_exists_FOL_R_exists_vec.
    specialize (nb_exists_FOL_R_basic_case_aux_complexity_le G V
                                                             (S n)
                                                             Heqn
                                                             (acc _
                                                                  (lt_nat4_last
                                                                     _
                                                                     _
                                                                     _
                                                                     (Nat.lt_succ_diag_r _)))); auto.
    rewrite seq_length.
    lia.
Qed.
                                                                           
Lemma FOL_R_basic_case_aux_complexity_case_0
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
    p_hseq_is_atomic G ->
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc) = length V * length G
with HMR_dec_formula_aux_complexity_case_0
       (G : p_hypersequent)
       (x: nat)
       (Heqx : snd (fst (modal_complexity_p_hseq G)) = x)
       p
       (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p)
       (acc : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
       p_hseq_is_atomic G ->
       nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc) = (pow2 (length G) -1)* length G.
Proof.
  - intros Hb.
    destruct acc as [acc].
    destruct n.
    2:{ exfalso.
        replace (max_diamond_p_hseq G) with 0 in Heqn; try lia.
        symmetry.
        apply p_hseq_is_atomic_max_diamond_0.
        apply Hb. }
    destruct V; [ reflexivity | ].
    simpl.
    rewrite nb_exists_FOL_R_exists_vec.
    rewrite seq_length.
    rewrite nb_exists_FOL_R_phi.
    specialize (FOL_R_basic_case_aux_complexity_case_0 G V
                                         0%nat
                                         Heqn
                                         (acc _
                                              (lt_nat4_last
                                                 _
                                                 _
                                                 _
                                                 (Nat.lt_succ_diag_r _)))
                                         Hb).
    rewrite FOL_R_basic_case_aux_complexity_case_0.
    lia.
  - intros Hb.
    destruct acc as [acc].
    destruct x.
    2:{ exfalso.
        simpl in Heqx.
        replace (fst (HMR_complexity_p_hseq G)) with 0%nat in Heqx; try lia.
        symmetry; apply p_hseq_is_basic_complexity_0.
        apply p_hseq_is_atomic_basic.
        apply Hb. }
    simpl.
    etransitivity; [ apply FOL_R_basic_case_aux_complexity_case_0 | ]; auto.
    rewrite map_length.
    rewrite make_subsets_length.
    unfold pow2; lia.
Qed.

Fixpoint FOL_R_basic_case_aux_complexity_case_1
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  forall j,
    G <> nil ->
    H_shape_hseq 0 j 0 0 G ->
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc) = length V * (length G + 1).
Proof.
  intros j Hnnil Hshape.
  destruct acc as [acc].
  destruct n.
  { clear - Heqn Hshape Hnnil.
    destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
    destruct G2; [ | exfalso; simpl in *; lia ].
    destruct G1.
    { apply Permutation_Type_length in Hperm.
      destruct G; inversion Hperm.
      contradiction. }
    exfalso.
    inversion H2; subst.
    destruct X as [[vr vs] [Hperm' [H4 H5]]].
    rewrite max_diamond_p_hseq_perm with _ (p :: G1) in Heqn by Permutation_Type_solve.
    simpl in Heqn.
    destruct vr; try now inversion H4.
    simpl in Hperm'.
    assert (In_inf (f , <S> (complexity_A 0)) p).
    { apply Permutation_Type_in_inf with ((f, <S> complexity_A 0 )
                                            :: vec vr (<S> complexity_A 0) ++
                                            vec vs
                                            (complexity_A 1)); [symmetry; apply Hperm' | ].
      left; reflexivity. }
    apply in_inf_split in X as [[pa pb] Heq].
    rewrite Heq in Heqn.
    rewrite max_diamond_p_seq_app in Heqn.
    change (max_diamond_p_seq ((f, <S> complexity_A 0) :: pb)) with (max (S (max_diamond_term (complexity_A 0))) (max_diamond_p_seq pb)) in Heqn.
    lia. }
  destruct V; [ reflexivity | ].
  simpl.
  rewrite nb_exists_FOL_R_exists_vec.
  rewrite seq_length.
  simpl; rewrite nb_exists_FOL_R_all_zero; rewrite nb_exists_FOL_R_all_gtz; rewrite nb_exists_FOL_R_all_atoms_eq.
  rewrite FOL_R_basic_case_aux_complexity_case_1 with _ _ _ _ _ j; auto.
  rewrite HMR_dec_formula_aux_complexity_case_0.
  2:{ erewrite flat_map_ext.
      2:{ intros a.
          rewrite <- (map_nth only_diamond_p_seq).
          change (S (max_var_weight_p_hseq G + a)) with ((S (max_var_weight_p_hseq G)) + a).
          reflexivity. }
      apply p_hseq_is_atomic_flat_map.
      clear - Hshape.
      destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
      destruct G2; inversion H1.
      clear - H2 Hperm; rewrite app_nil_r in Hperm.
      apply p_hseq_is_atomic_perm with (map only_diamond_p_seq G1).
      { apply Permutation_Type_map.
        symmetry; apply Hperm. }
      clear - H2.
      induction G1; [apply Forall_inf_nil | ].
      simpl; apply Forall_inf_cons; inversion H2; subst.
      2:{ apply IHG1; apply X0. }
      clear - X.
      destruct X as [[r s] [Hperm [H1 H2]]].
      destruct s; inversion H2.
      simpl; rewrite app_nil_r in Hperm.
      apply p_seq_is_atomic_perm with (only_diamond_p_seq (vec r (<S> complexity_A 0))).
      { apply only_diamond_p_seq_perm.
        symmetry; apply Hperm. }
      rewrite only_diamond_p_seq_vec_diamond.
      clear.
      induction r; simpl; constructor; try assumption.
      apply I. }
  simpl.
  lia.
Qed.
    
Lemma FOL_R_basic_case_aux_complexity
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  forall i j,
    In_inf (seq 0 (length G)) V ->
    H_shape_hseq i j 0 0 G ->
    pow2 (1 + j) <= length G ->
    tetra_2 (1 + i) (1 + j) <= nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc)
with HMR_dec_formula_aux_complexity
       (G : p_hypersequent)
       (x: nat)
       (Heqx : snd (fst (modal_complexity_p_hseq G)) = x)
       p
       (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p)
       (acc : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
       forall i j k l,
         G <> nil ->
         H_shape_hseq i j k l G ->
         pow2 (1 + j) <= length G + l ->
         tetra_2 (1 + i) (1 + j + k) <= nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc).
Proof.
  - intros i j Hin Hshape Hlen.
    destruct acc as [acc].
    destruct n.
    + clear - Heqn Hshape Hlen.
      destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
      destruct G2; [ | exfalso; simpl in *; lia ].
      destruct G1.
      { apply Permutation_Type_length in Hperm.
        unfold pow2 in *; simpl in *.
        assert (H := le_1_pow2 j).
        lia. }
      exfalso.
      inversion H2; subst.
      destruct X as [[vr vs] [Hperm' [H4 H5]]].
      rewrite max_diamond_p_hseq_perm with _ (p :: G1) in Heqn by Permutation_Type_solve.
      simpl in Heqn.
      destruct vr; try now inversion H4.
      simpl in Hperm'.
      assert (In_inf (f , <S> (complexity_A i)) p).
      { apply Permutation_Type_in_inf with ((f, <S> complexity_A i )
                                              :: vec vr (<S> complexity_A i) ++
                                              vec vs
                                              (complexity_A (S i))); [symmetry; apply Hperm' | ].
        left; reflexivity. }
      apply in_inf_split in X as [[pa pb] Heq].
      rewrite Heq in Heqn.
      rewrite max_diamond_p_seq_app in Heqn.
      change (max_diamond_p_seq ((f, <S> complexity_A i) :: pb)) with (max (S (max_diamond_term (complexity_A i))) (max_diamond_p_seq pb)) in Heqn.
      lia. 
    + destruct i.
      { rewrite FOL_R_basic_case_aux_complexity_case_1 with _ _ _ _ _ j.
        - simpl.
          destruct V; try now inversion Hin.
          simpl.
          destruct G; simpl in *; lia.
        - destruct G; [ inversion Heqn | clear; intros H; inversion H].
        - apply Hshape. }
      etransitivity.
      2:{ apply nb_exists_FOL_R_basic_aux_sub.
          apply Hin. }
      etransitivity.
      2:{ apply (HMR_dec_formula_aux_complexity _ _ _ _ _ _ i 0 (pred (length G * (S j))) 1).
          - intros H; inversion H.
          - apply H_shape_hseq_only_diamond.
            + destruct G; inversion Heqn.
              intros H; inversion H.
            + apply Hshape.
          - unfold pow2; simpl. lia. }
      simpl.
      transitivity (tetra_2 (S i) (pow2 (S j))).
      * rewrite  tetra_2_pow2.
        reflexivity.
      * simpl.
        apply pow2_le_mono.
        apply tetra_2_le_mono.
        destruct G; simpl in*; try lia.
  - intros i j k l Hnnil Hshape Hlen.
    destruct acc as [acc].
    destruct x.
    + simpl.
      replace k with 0 in *.
      2:{ clear - Hnnil Hshape Heqx.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          rewrite modal_complexity_perm with _ (G1 ++ G2) in Heqx; auto.
          simpl in Heqx.
          rewrite complexity_p_hseq_app in Heqx.
          destruct G1; [ destruct G2 | ].
          - simpl in Hperm.
            symmetry in Hperm; apply Permutation_Type_nil in Hperm.
            contradiction.
          - inversion H3; subst.
            destruct X as [[vr vs] [Hperm1 [Heq1 Heq2]]].
            destruct vs; [ exfalso; simpl in *; inversion Heq2 | ].
            simpl in Hperm1.
            assert (In_inf (f, complexity_A (S i)) p).
            { symmetry in Hperm1.
              apply (Permutation_Type_in_inf _ Hperm1).
              apply in_inf_or_app.
              right; left; reflexivity. }
            apply in_inf_split in X as [[p1 p2] Heq].
            rewrite Heq in Heqx.
            rewrite complexity_p_hseq_cons in Heqx.
            rewrite complexity_p_seq_app in Heqx.
            simpl in Heqx.
            lia.
          - inversion H2; subst.
            destruct X as [[vr vs] [Hperm1 [Heq1 Heq2]]].
            destruct k; auto.
            destruct vs; [ exfalso; simpl in *; inversion Heq2 | ].
            simpl in Hperm1.
            assert (In_inf (f, complexity_A (S i)) p).
            { symmetry in Hperm1.
              apply (Permutation_Type_in_inf _ Hperm1).
              apply in_inf_or_app.
              right; left; reflexivity. }
            apply in_inf_split in X as [[p1 p2] Heq].
            rewrite Heq in Heqx.
            rewrite complexity_p_hseq_cons in Heqx.
            rewrite complexity_p_seq_app in Heqx.
            simpl in Heqx.
            lia. }
      replace l with 0 in *.
      2:{ clear - Hnnil Hshape Heqx.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          rewrite modal_complexity_perm with _ (G1 ++ G2) in Heqx; auto.
          simpl in Heqx.
          rewrite complexity_p_hseq_app in Heqx.
          destruct G2.
          - apply H1.
          - inversion H3; subst.
            destruct X as [[vr vs] [Hperm1 [Heq1 Heq2]]].
            destruct vs; [ exfalso; simpl in *; inversion Heq2 | ].
            simpl in Hperm1.
            assert (In_inf (f, complexity_A (S i)) p).
            { symmetry in Hperm1.
              apply (Permutation_Type_in_inf _ Hperm1).
              apply in_inf_or_app.
              right; left; reflexivity. }
            apply in_inf_split in X as [[p1 p2] Heq].
            rewrite Heq in Heqx.
            rewrite complexity_p_hseq_cons in Heqx.
            rewrite complexity_p_seq_app in Heqx.
            simpl in Heqx.
            lia. }
      etransitivity.
      2:{ refine (FOL_R_basic_case_aux_complexity _ _ _ _ _ _ _ _ Hshape _).
          - rewrite <- (rev_involutive (seq _ _)).
            apply in_inf_map.
            apply cond_is_in_make_subsets.
            + apply rev_not_nil.
              destruct G; [contradiction | ].
              intros H'; inversion H'.
            + clear - Hnnil.
              apply rev_nth_all_lt.
              intros i.
              case_eq (i <? length G); intros H; (apply Nat.ltb_lt in H + apply Nat.ltb_nlt in H).
              * rewrite seq_nth; lia.
              * rewrite nth_overflow; [ | rewrite seq_length; lia].
                destruct G; [ contradiction | simpl; lia].
            + clear - Hnnil.
              intros i j H1 H2.
              apply rev_reverse_order_lt; try assumption.
              clear.
              intros i j H1 H2.
              rewrite seq_length in H1.
              rewrite ? seq_nth; lia.
          - lia. }
      simpl.
      apply pow2_le_mono.
      apply tetra_2_le_mono.
      unfold pow2; simpl; lia.
    + destruct l.
      * destruct k.
        { exfalso.
          clear - Hnnil Hshape Heqx.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          rewrite modal_complexity_perm with _ (G1 ++ G2) in Heqx; auto.
          simpl in Heqx.
          rewrite complexity_p_hseq_app in Heqx.
          destruct G2; [ | simpl in H1; exfalso; lia].
          simpl in *.
          assert (fst (HMR_complexity_p_hseq G1) = 0).
          { clear - H2.
            induction G1; auto.
            inversion H2; subst.
            specialize (IHG1 X0).
            destruct X as [[vr vs] [Hperm [Heq1 Heq2]]].
            destruct vs; [ | exfalso; simpl in *; lia].
            rewrite complexity_p_hseq_cons.
            rewrite (complexity_p_seq_perm _ _ Hperm).
            rewrite complexity_p_seq_app.
            rewrite ? complexity_p_seq_vec.
            simpl.
            lia. }
          lia. }          
        apply H_shape_hseq_0 in Hshape.
        assert {n & length G = S n} as [n Heqn].
        { destruct G; inversion Heqx.
          split with (length G).
          reflexivity. }
        rewrite Heqn in Hshape.
        destruct (p_hseq_put_non_basic_fst_H_shape i (S j) k n G Hshape) as [[[r T] H] [Heq [Hshape1 Hshape2]]].
        destruct p.
        2:{ exfalso.
            rewrite Heq in Heqp.
            inversion Heqp. }
        simpl.
        etransitivity.
        2:{ refine (HMR_dec_formula_aux_complexity p
                                                   _
                                                   eq_refl
                                                   _
                                                   eq_refl
                                                   (acc _
                                                        (lt_nat3_to_lt_nat4 _ _ _ _
                                                                            (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp)))
                                                   i (S j) k n
                                                   _
                                                   _
                                                   _); try lia.
            { intros H'.
              rewrite Heq in Heqp.
              rewrite H' in Heqp.
              inversion Heqp. }
            2:{ replace (length p) with (S (length G)).
                2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
                    - rewrite Heq in Heqp.
                      inversion Heqp.
                      reflexivity.
                    - rewrite <- Heq.
                      clear - Heqx.
                      unfold p_hseq_put_non_basic_fst.
                      simpl.
                      change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
                      apply Permutation_Type_length.
                      symmetry; apply p_hseq_put_max_complexity_fst.
                      intros H; subst; inversion Heqx. }                
                rewrite pow2_S; rewrite Heqn in *.
                rewrite pow2_S in *.
                lia. }
            destruct Hshape2 as [[G1 G2] [Hperm [[H1 H2] H3]]].
            split with (((r, <S> complexity_A i) :: T) :: ((r, <S> complexity_A i) :: T) :: G1, G2).
            rewrite Heq in Heqp.
            simpl in Heqp.
            inversion Heqp.
            repeat split.
            - Permutation_Type_solve.
            - apply H1.
            - destruct Hshape1 as [[r' s'] [Hperm' [H1' H2']]].
              repeat apply Forall_inf_cons.
              + split with (r :: r', s').
                repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + split with (r :: r', s').
              repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + apply H2.
            - apply H3. }
        replace (length p) with (S (length G)).
        2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
            - rewrite Heq in Heqp.
              inversion Heqp.
              reflexivity.
            - rewrite <- Heq.
              clear - Heqx.
              unfold p_hseq_put_non_basic_fst.
              simpl.
              change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
              apply Permutation_Type_length.
              symmetry; apply p_hseq_put_max_complexity_fst.
              intros H; subst; inversion Heqx. }
        apply pow2_le_mono.
        apply tetra_2_le_mono.
        lia.
      * destruct (p_hseq_put_non_basic_fst_H_shape i j k l G Hshape) as [[[r T] H] [Heq [Hshape1 Hshape2]]].
        destruct p.
        2:{ exfalso.
            rewrite Heq in Heqp.
            inversion Heqp. }
        simpl.
        etransitivity.
        2:{ refine (HMR_dec_formula_aux_complexity p
                                                   _
                                                   eq_refl
                                                   _
                                                   eq_refl
                                                   (acc _
                                                        (lt_nat3_to_lt_nat4 _ _ _ _
                                                                            (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp)))
                                                   i j k l
                                                   _
                                                   _
                                                   _); try lia.
            { intros H'.
              rewrite Heq in Heqp.
              rewrite H' in Heqp.
              inversion Heqp. }
            2:{ replace (length p) with (S (length G)).
                2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
                    - rewrite Heq in Heqp.
                      inversion Heqp.
                      reflexivity.
                    - rewrite <- Heq.
                      clear - Heqx.
                      unfold p_hseq_put_non_basic_fst.
                      simpl.
                      change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
                      apply Permutation_Type_length.
                      symmetry; apply p_hseq_put_max_complexity_fst.
                      intros H; subst; inversion Heqx. }
                lia. }
            destruct Hshape2 as [[G1 G2] [Hperm [[H1 H2] H3]]].
            split with (((r, <S> complexity_A i) :: T) :: ((r, <S> complexity_A i) :: T) :: G1, G2).
            rewrite Heq in Heqp.
            simpl in Heqp.
            inversion Heqp.
            repeat split.
            - Permutation_Type_solve.
            - apply H1.
            - destruct Hshape1 as [[r' s'] [Hperm' [H1' H2']]].
              repeat apply Forall_inf_cons.
              + split with (r :: r', s').
                repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + split with (r :: r', s').
              repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + apply H2.
            - apply H3. }
        replace (length p) with (S (length G)).
        2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
            - rewrite Heq in Heqp.
              inversion Heqp.
              reflexivity.
            - rewrite <- Heq.
              clear - Heqx.
              unfold p_hseq_put_non_basic_fst.
              simpl.
              change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
              apply Permutation_Type_length.
              symmetry; apply p_hseq_put_max_complexity_fst.
              intros H; subst; inversion Heqx. }
        apply pow2_le_mono.
        apply tetra_2_le_mono.
        lia.
Qed.

(** Implementation of Lemma 4.43 *)
Lemma decidability_non_elementary :
  forall i,
    tetra_2 i 1 <= nb_exists_FOL_R_formula (HMR_dec_formula (((FOL_R_cst 1, complexity_A i) :: nil) :: nil)).
Proof.
  intro i.
  destruct i.
  { unfold HMR_dec_formula.
    rewrite HMR_dec_formula_aux_complexity_case_0.
    - reflexivity.
    - apply Forall_inf_cons; [ apply Forall_inf_cons ; [ | apply Forall_inf_nil] | apply Forall_inf_nil].
      apply I. }
  change 1 with (1 + 0 + 0) at 1.
  apply HMR_dec_formula_aux_complexity with 1.
  - intros H; inversion H.
  - split with (nil, (((FOL_R_cst 1, complexity_A (S i)) :: nil) :: nil)).
    repeat split.
    + Permutation_Type_solve.
    + apply Forall_inf_nil.
    + apply Forall_inf_cons ; [ | apply Forall_inf_nil].
      split with (nil, (FOL_R_cst 1 :: nil)).
      repeat split.
      simpl.
      reflexivity.
  - unfold pow2; simpl; lia.
Qed.
