(** * Implementation of Section 4.7 *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.invertibility.
Require Import RL.hmr.M_elim.
Require Import RL.hmr.hmr_perm_lemmas.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** Proof of Lemma 4.39

L is the list (((r_i, s_i), (r'_i, s'_i)), T_i) *)      

Lemma hmrr_atomic_can_elim_gen : forall L n,
    Forall_inf (fun x => sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x))) = sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x)))) L ->
    HMR_T (map (fun x => (vec (fst (fst (fst x))) (HMR_covar n) ++ vec (snd (fst (fst x))) (HMR_var n) ++ snd x)) L) ->
    HMR_T (map (fun x => (vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)) L).
Proof.
  intros L n H.
  remember (map (fun x => (vec (fst (fst (fst x))) (HMR_covar n) ++ vec (snd (fst (fst x))) (HMR_var n) ++ snd x)) L) as G.
  assert (Allperm G (map (fun x => (vec (fst (fst (fst x))) (HMR_covar n) ++ vec (snd (fst (fst x))) (HMR_var n) ++ snd x)) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L H X; induction pi; intros L Hsum Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X; destruct p as [[[s1 r1] [s2 r2]] T1]; destruct s1; destruct r1; destruct T1; inversion X; simpl.
    apply hmrr_ID.
    { inversion Hsum; simpl in *.
      nra. }
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi.
    + inversion Hsum; assumption.
    + assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C; try assumption.
    change ((vec (fst (snd (fst p))) (HMR_covar n) ++ vec (snd (snd (fst p))) (HMR_var n) ++ snd p)
              :: (vec (fst (snd (fst p))) (HMR_covar n) ++ vec (snd (snd (fst p))) (HMR_var n) ++ snd p)
              :: map
              (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)
              L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)
           (p :: p :: L)).
    apply IHpi.
    + inversion Hsum.
      repeat (apply Forall_inf_cons); assumption.
    + simpl.
      do 2 (apply Forall2_inf_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[[p1 p2] [p3 p4]] p5];
      destruct p0 as [[[p1' p2'] [p3' p4']] p5'];
      simpl in *;
      remember ((((p1 ++ p1'), (p2 ++ p2')) , ((p3 ++ p3') , (p4 ++ p4'))), (p5 ++ p5')) as p'';
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (fst (snd (fst p''))) (HMR_covar n) ++ vec (snd (snd (fst p''))) (HMR_var n) ++snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; Permutation_Type_solve | ]);
      change ((vec (fst (snd (fst p''))) (HMR_covar n) ++ vec (snd (snd (fst p''))) (HMR_var n) ++snd p'') :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) (L))
        with (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) (p'' :: L));
      (apply IHpi ;
       [ subst;
           inversion Hsum; inversion X3;
           repeat (try apply Forall_inf_cons);
           try assumption;
           simpl in *;
           rewrite ? sum_vec_app;
           nra | ]);
      simpl; apply Forall2_inf_cons;
           [ rewrite Heqp'';simpl; rewrite ? vec_app ; Permutation_Type_solve |  assumption].
  - inversion f.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_T with r; try assumption.
    destruct p as ([[r1 r2] [s1 s2]] , T'); simpl in *.
    apply hmrr_ex_seq with (vec (mul_vec r s1) (HMR_covar n) ++ vec (mul_vec r s2) (HMR_var n) ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      reflexivity. }
    change ((vec (mul_vec r s1) (HMR_covar n) ++ vec (mul_vec r s2) (HMR_var n) ++ seq_mul r T') :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((((mul_vec r r1, mul_vec r r2) , (mul_vec r s1 , mul_vec r s2)), seq_mul r T') :: L)).
    apply IHpi.
    + subst; inversion Hsum; subst; simpl in *.
      apply Forall_inf_cons ; try assumption; simpl.
      rewrite ? mul_vec_sum_vec; nra.
    + simpl.
      apply Forall2_inf_cons; [ | try assumption].
      rewrite <- ? seq_mul_vec_mul_vec; rewrite <- ? seq_mul_app.
      apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    case_eq (n =? n0); [intros Heqn; apply Nat.eqb_eq in Heqn | intros Hneqn; apply Nat.eqb_neq in Hneqn].
    + subst.
      destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
      destruct (perm_decomp_vec_eq_2 T T1 r1 s1 r s (HMR_var n0) (HMR_covar n0)) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]]; [ now auto | apply X | ].
      apply hmrr_ex_seq with (vec (c2 ++ s1') (HMR_covar n0) ++ vec (c1 ++ r1') (HMR_var n0) ++ T').
      { rewrite ? vec_app.
        transitivity (vec s1' (HMR_covar n0) ++ vec r1' (HMR_var n0) ++ (vec c2 (HMR_covar n0) ++ vec c1 (HMR_var n0) ++ T')); try Permutation_Type_solve. }
      change ((vec (c2 ++ s1') (HMR_covar n0) ++ vec (c1 ++ r1') (HMR_var n0) ++ T')
                :: map
                (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (HMR_covar n0) ++ vec (snd (snd (fst x))) (HMR_var n0) ++ snd x)
                L)
        with
          (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (HMR_covar n0) ++ vec (snd (snd (fst x))) (HMR_var n0) ++ snd x)
               ((((a2,a1),(c2 ++ s1', c1 ++ r1')), T')::L)).
      apply IHpi.
      * inversion Hsum; simpl in*.
        apply Forall_inf_cons ; [ | try assumption].
        simpl; rewrite ? sum_vec_app.
        transitivity (sum_vec c2 + sum_vec s1 - (sum_vec c1 + sum_vec r1)); try nra.
        replace (sum_vec s1) with (sum_vec (a2 ++ b2)).
        2:{ apply sum_vec_perm; Permutation_Type_solve. }
        replace (sum_vec r1) with (sum_vec (a1 ++ b1)) by (apply sum_vec_perm; Permutation_Type_solve).
        rewrite ? sum_vec_app.
        replace (sum_vec r) with (sum_vec (b1 ++ c1)) in e by (apply sum_vec_perm; Permutation_Type_solve).
        replace (sum_vec s) with (sum_vec (b2 ++ c2)) in e by (apply sum_vec_perm; Permutation_Type_solve).
        rewrite ? sum_vec_app in e.
        nra.
      * simpl; apply Forall2_inf_cons; [ | try assumption].
        Permutation_Type_solve.
    + destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
      subst.
      destruct (perm_decomp_vec_neq_2_2 T T1 r s r1 s1 (HMR_covar n0) (HMR_var n0) (HMR_covar n) (HMR_var n)) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
      apply hmrr_ex_seq with (vec s (HMR_covar n0) ++ vec r (HMR_var n0) ++ vec s1' (HMR_covar n) ++ vec r1' (HMR_var n) ++ T').
      { Permutation_Type_solve. }
      apply hmrr_ID; try assumption.
      change ((vec s1' (HMR_covar n) ++ vec r1' (HMR_var n) ++ T')
                :: map
                (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)
                L)
        with
          (map
             (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)
             ((((s1,r1),(s1',r1')),T')::L)).
      apply IHpi.
      * inversion Hsum.
        apply Forall_inf_cons ; [ | try assumption].
        simpl in *; nra.
      * simpl; apply Forall2_inf_cons; [ | try assumption].
        Permutation_Type_solve.      
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (HMR_zero <> HMR_covar n) as Hnc by now auto.
    assert (HMR_zero <> HMR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r HMR_zero ++ vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc.
      repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity; [ apply Permutation_Type_app_comm | ].
      etransitivity ; [ | symmetry; apply H1'].
      apply Permutation_Type_app; Permutation_Type_solve. }
    apply hmrr_Z; try assumption.
    change ((vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> HMR_covar n) as Hnc by now auto.
    assert (A +S B <> HMR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A +S B) ++ vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r A ++ vec r B ++ Db); [ Permutation_Type_solve | ].
    change ((vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r A ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((r1, vec r A ++ vec r B ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (r0 *S A <> HMR_covar n) as Hnc by now auto.
    assert (r0 *S A <> HMR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (r0 *S A) ++ vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec (mul_vec r0 r) A ++ Db).
    { Permutation_Type_solve. }
    change ((vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec (mul_vec r0 r) A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((r1, vec (mul_vec r0 r) A ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    +  simpl.
       apply Forall2_inf_cons; [ | assumption].
       Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> HMR_covar n) as Hnc by now auto.
    assert (A \/S B <> HMR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A \/S B) ++ vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r A ++ Db).
    { Permutation_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r B ++  Db).
    { Permutation_Type_solve. }
    change ((vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r B ++ Db) :: (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((r1, vec r B ++ Db) :: (r1, vec r A ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      repeat (try apply Forall_inf_cons); simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | apply Forall2_inf_cons ; [ | assumption] ]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> HMR_covar n) as Hnc by now auto.
    assert (A /\S B <> HMR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A /\S B) ++ vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_min; try assumption.
    + apply hmrr_ex_seq with (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r A ++ Db).
      { Permutation_Type_solve. }
      change ((vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
        with
          (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((r1, vec r A ++ Db) :: L)).
      apply IHpi1.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | assumption]; Permutation_Type_solve.
    + apply hmrr_ex_seq with (vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r B ++ Db).
      { Permutation_Type_solve. }
      change ((vec (fst (snd r1)) (HMR_covar n) ++ vec (snd (snd r1)) (HMR_var n) ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L)
        with
          (map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | try assumption]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
    destruct (perm_decomp_vec_neq_2_2 T T1 r s r1 s1 HMR_coone HMR_one (HMR_covar n) (HMR_var n)) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ vec s1' (HMR_covar n) ++ vec r1' (HMR_var n) ++ T').
    { Permutation_Type_solve. }
    apply hmrr_one; try assumption.
    change ((vec s1' (HMR_covar n) ++ vec r1' (HMR_var n) ++ T')
              :: map
              (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                 vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)
              L)
      with
        (map
           (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
              vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x)
           ((((s1,r1),(s1',r1')),T')::L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons ; [ | try assumption].
      simpl in *; nra.
    + simpl; apply Forall2_inf_cons; [ | try assumption].
      Permutation_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
    destruct (perm_decomp_vec_neq_2_2 (seq_diamond T) T1 r s r1 s1 HMR_coone HMR_one (HMR_covar n) (HMR_var n)) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
    apply seq_diamond_perm_decomp in H1' as [D'' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    destruct r1.
    2:{ destruct Db'; inversion HDb'. }
    destruct s1.
    2:{ destruct Da'; inversion HDa'. }
    apply hmrr_ID.
    { inversion Hsum; simpl in *; subst.
      nra. }
    simpl in *.
    rewrite HDb' in H3'.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ seq_diamond Db') ; [ Permutation_Type_solve | ].
    apply hmrr_diamond; try assumption.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ T).
    { apply Permutation_Type_app; [ | apply Permutation_Type_app]; try reflexivity.
      apply seq_diamond_perm_inv.
      etransitivity ; [ | symmetry; apply H3'].
      apply Permutation_Type_app_inv_l with (vec r HMR_one).
      apply Permutation_Type_app_inv_l with (vec s HMR_coone).
      Permutation_Type_solve. }
    apply pi.
  - destruct L; inversion Hperm; subst.
    apply IHpi; try assumption.
    simpl; apply Forall2_inf_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2_inf (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi; [ | rewrite Heq in f; apply f].
    clear - Hperm1 Hsum.
    revert Hsum; induction Hperm1; intros Hsum.
    + apply Forall_inf_nil.
    + inversion Hsum; subst.
      apply Forall_inf_cons; [ | apply IHHperm1];try assumption.
    + inversion Hsum; inversion X; subst.
      apply Forall_inf_cons ; [ | apply Forall_inf_cons]; try assumption.
    + apply IHHperm1_2; apply IHHperm1_1; apply Hsum.
  - inversion f.
Qed.

(** Proof of Lemma 4.36 *)
Lemma hmrr_atomic_can_elim : forall G T n r s,
    sum_vec r = sum_vec s ->
    HMR_T ((vec s (HMR_covar n) ++ vec r (HMR_var n) ++ T) :: G) ->
    HMR_T (T :: G).
Proof.
  intros G T n r s Heq pi.
  assert ({ L & prod
                  ( G = map (fun x  => vec (fst (fst (fst x))) (HMR_covar n) ++ vec (snd (fst (fst x))) (HMR_var n) ++ snd x) L)
                  (( G =  map (fun x  => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L) *
                   (Forall_inf
                      (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x))) = sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x))))  L))}) as [L [H1 [H2 H3]]].
  { clear - G ; induction G.
    - split with nil; repeat split; try reflexivity.
      apply Forall_inf_nil.
    - destruct IHG as [ L [ H1 [H2 H3]] ].
      split with ((((nil,nil),(nil,nil)), a) :: L).
      repeat split; simpl; [rewrite H1 | rewrite H2 | ]; try reflexivity.
      apply Forall_inf_cons; try assumption.
      simpl; nra. }
  rewrite H2.
  change (T :: map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) L) with
      (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) (HMR_covar n) ++ vec (snd (snd (fst x))) (HMR_var n) ++ snd x) ( (((s , r) , (nil, nil)) , T) :: L)).
  apply hmrr_atomic_can_elim_gen.
  - simpl; apply Forall_inf_cons; try assumption; simpl; nra.
  - simpl; rewrite <- H1.
    apply pi.
Qed.

(** Proof of Lemma 4.40 *)
Lemma hmrr_one_can_elim_gen : forall L,
    Forall_inf (fun x => sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x))) <=  sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x)))) L ->
    HMR_T (map (fun x => (vec (fst (fst (fst x))) HMR_coone ++ vec (snd (fst (fst x))) HMR_one ++ snd x)) L) ->
    HMR_T (map (fun x => (vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)) L).
Proof.
  intros L H.
  remember (map (fun x => (vec (fst (fst (fst x))) HMR_coone ++ vec (snd (fst (fst x))) HMR_one ++ snd x)) L) as G.
  assert (Allperm G (map (fun x => (vec (fst (fst (fst x))) HMR_coone ++ vec (snd (fst (fst x))) HMR_one ++ snd x)) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L H X; induction pi; intros L Hsum Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X; destruct p as [[[s1 r1] [s2 r2]] T1]; destruct s1; destruct r1; destruct T1; inversion X; simpl.
    apply hmrr_one.
    { inversion Hsum; subst; simpl in *.
      nra. }
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi.
    + inversion Hsum; assumption.
    + assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C; try assumption.
    change ((vec (fst (snd (fst p))) HMR_coone ++ vec (snd (snd (fst p))) HMR_one ++ snd p)
              :: (vec (fst (snd (fst p))) HMR_coone ++ vec (snd (snd (fst p))) HMR_one ++ snd p)
              :: map
              (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)
              L)
      with
        (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)
           (p :: p :: L)).
    apply IHpi.
    + inversion Hsum.
      repeat (apply Forall_inf_cons); assumption.
    + simpl.
      do 2 (apply Forall2_inf_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[[p1 p2] [p3 p4]] p5];
      destruct p0 as [[[p1' p2'] [p3' p4']] p5'];
      simpl in *;
      remember ((((p1 ++ p1'), (p2 ++ p2')) , ((p3 ++ p3') , (p4 ++ p4'))), (p5 ++ p5')) as p'';
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (fst (snd (fst p''))) HMR_coone ++ vec (snd (snd (fst p''))) HMR_one ++snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; Permutation_Type_solve | ]);
      change ((vec (fst (snd (fst p''))) HMR_coone ++ vec (snd (snd (fst p''))) HMR_one ++snd p'') :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) (L))
        with (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) (p'' :: L));
      (apply IHpi ;
       [ subst;
           inversion Hsum; inversion X3;
           repeat (try apply Forall_inf_cons);
           try assumption;
           simpl in *;
           rewrite ? sum_vec_app;
           nra | ]);
      simpl; apply Forall2_inf_cons;
           [ rewrite Heqp'';simpl; rewrite ? vec_app ; Permutation_Type_solve |  assumption].
  - inversion f.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_T with r; try assumption.
    destruct p as ([[r1 r2] [s1 s2]] , T'); simpl in *.
    apply hmrr_ex_seq with (vec (mul_vec r s1) HMR_coone ++ vec (mul_vec r s2) HMR_one ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      reflexivity. }
    change ((vec (mul_vec r s1) HMR_coone ++ vec (mul_vec r s2) HMR_one ++ seq_mul r T') :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((((mul_vec r r1, mul_vec r r2) , (mul_vec r s1 , mul_vec r s2)), seq_mul r T') :: L)).
    apply IHpi.
    + subst; inversion Hsum; subst; simpl in *.
      apply Forall_inf_cons ; try assumption; simpl.
      rewrite ? mul_vec_sum_vec.
      destruct r as [r Hr]; simpl.
      clear - Hr H0; apply R_blt_lt in Hr.
      nra.
    + simpl.
      apply Forall2_inf_cons; [ | try assumption].
      rewrite <- ? seq_mul_vec_mul_vec; rewrite <- ? seq_mul_app.
      apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
    destruct (perm_decomp_vec_neq_2_2 T T1 r s r1 s1 (HMR_covar n) (HMR_var n) HMR_coone HMR_one) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
    apply hmrr_ex_seq with (vec s (HMR_covar n) ++ vec r (HMR_var n) ++ vec s1' HMR_coone ++ vec r1' HMR_one ++ T').
    { Permutation_Type_solve. }
    apply hmrr_ID; try assumption.
    change ((vec s1' HMR_coone ++ vec r1' HMR_one ++ T')
              :: map
              (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                 vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)
              L)
      with
        (map
           (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
              vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)
           ((((s1,r1),(s1',r1')),T')::L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons ; [ | try assumption].
      simpl in *; nra.
    + simpl; apply Forall2_inf_cons; [ | try assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (HMR_zero <> HMR_coone) as Hnc by now auto.
    assert (HMR_zero <> HMR_one) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r HMR_zero ++ vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc.
      repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity; [ apply Permutation_Type_app_comm | ].
      etransitivity ; [ | symmetry; apply H1'].
      apply Permutation_Type_app; Permutation_Type_solve. }
    apply hmrr_Z; try assumption.
    change ((vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ Db) :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> HMR_coone) as Hnc by now auto.
    assert (A +S B <> HMR_one) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A +S B) ++ vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r A ++ vec r B ++ Db); [ Permutation_Type_solve | ].
    change ((vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r A ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((r1, vec r A ++ vec r B ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (r0 *S A <> HMR_coone) as Hnc by now auto.
    assert (r0 *S A <> HMR_one) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (r0 *S A) ++ vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec (mul_vec r0 r) A ++ Db).
    { Permutation_Type_solve. }
    change ((vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec (mul_vec r0 r) A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((r1, vec (mul_vec r0 r) A ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    +  simpl.
       apply Forall2_inf_cons; [ | assumption].
       Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> HMR_coone) as Hnc by now auto.
    assert (A \/S B <> HMR_one) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A \/S B) ++ vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r A ++ Db).
    { Permutation_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r B ++  Db).
    { Permutation_Type_solve. }
    change ((vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r B ++ Db) :: (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((r1, vec r B ++ Db) :: (r1, vec r A ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      repeat (try apply Forall_inf_cons); simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | apply Forall2_inf_cons ; [ | assumption] ]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> HMR_coone) as Hnc by now auto.
    assert (A /\S B <> HMR_one) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A /\S B) ++ vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hmrr_min; try assumption.
    + apply hmrr_ex_seq with (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r A ++ Db).
      { Permutation_Type_solve. }
      change ((vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
        with
          (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((r1, vec r A ++ Db) :: L)).
      apply IHpi1.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | assumption]; Permutation_Type_solve.
    + apply hmrr_ex_seq with (vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r B ++ Db).
      { Permutation_Type_solve. }
      change ((vec (fst (snd r1)) HMR_coone ++ vec (snd (snd r1)) HMR_one ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L)
        with
          (map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | try assumption]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    subst.
    destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
    destruct (perm_decomp_vec_eq_2 T T1 r1 s1 r s HMR_one HMR_coone) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]]; [ now auto | apply X | ].
    apply hmrr_ex_seq with (vec (c2 ++ s1') HMR_coone ++ vec (c1 ++ r1') HMR_one ++ T').
    { rewrite ? vec_app.
      transitivity (vec s1' HMR_coone ++ vec r1' HMR_one ++ (vec c2 HMR_coone ++ vec c1 HMR_one ++ T')); try Permutation_Type_solve. }
    change ((vec (c2 ++ s1') HMR_coone ++ vec (c1 ++ r1') HMR_one ++ T')
              :: map
              (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                 vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)
              L)
      with
        (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x)
             ((((a2,a1),(c2 ++ s1', c1 ++ r1')), T')::L)).
    apply IHpi.
    + inversion Hsum; simpl in*.
      apply Forall_inf_cons ; [ | try assumption].
      simpl; rewrite ? sum_vec_app.
      apply Rle_trans with (sum_vec c2 + sum_vec s1 - (sum_vec c1 + sum_vec r1)); try nra.
      replace (sum_vec s1) with (sum_vec (a2 ++ b2)).
      2:{ apply sum_vec_perm; Permutation_Type_solve. }
      replace (sum_vec r1) with (sum_vec (a1 ++ b1)) by (apply sum_vec_perm; Permutation_Type_solve).
      rewrite ? sum_vec_app.
      replace (sum_vec r) with (sum_vec (b1 ++ c1)) in r0 by (apply sum_vec_perm; Permutation_Type_solve).
      replace (sum_vec s) with (sum_vec (b2 ++ c2)) in r0 by (apply sum_vec_perm; Permutation_Type_solve).
      rewrite ? sum_vec_app in r0.
      nra.
    + simpl; apply Forall2_inf_cons; [ | try assumption].
      Permutation_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
    destruct (perm_decomp_vec_eq_2 (seq_diamond T) T1 r1 s1 r s HMR_one HMR_coone) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]]; [ now auto | apply X | ].
    apply seq_diamond_perm_decomp in H5' as [T'' H5'].
    destruct a2 ; [ | destruct T''; inversion H5'].
    destruct a1 ; [ | destruct T''; inversion H5'].
    simpl in *.
    apply hmrr_ex_seq with (vec (s1' ++ c2) HMR_coone ++ vec (r1' ++ c1) HMR_one ++ seq_diamond T'').
    { rewrite <- H5'.
      rewrite ? vec_app.
      Permutation_Type_solve. }
    apply hmrr_diamond.
    { rewrite ? sum_vec_app.
      inversion Hsum; subst; simpl in *.
      apply Rplus_le_reg_r with (- sum_vec c1).
      apply Rplus_le_reg_r with (- sum_vec s1').
      replace (sum_vec s1' + sum_vec c2 + - sum_vec c1 + - sum_vec s1') with (sum_vec c2 - sum_vec c1) by nra.
      replace (sum_vec r1' + sum_vec c1 + - sum_vec c1 + - sum_vec s1') with (sum_vec r1' - sum_vec s1') by nra.
      apply Rle_trans with (sum_vec r1 - sum_vec s1) ; [ | nra ].
      rewrite (sum_vec_perm _ _ H1'); rewrite (sum_vec_perm _ _ H3').
      rewrite (sum_vec_perm _ _ H2') in r0; rewrite (sum_vec_perm _ _ H4') in r0.
      rewrite ? sum_vec_app in r0.
      nra. }
    apply hmrr_ex_seq with (vec s1' HMR_coone ++ vec r1' HMR_one ++ vec c2 HMR_coone ++ vec c1 HMR_one ++ T'').
    { rewrite ? vec_app.
      Permutation_Type_solve. }
    change ((vec s1' HMR_coone ++ vec r1' HMR_one ++ vec c2 HMR_coone ++ vec c1 HMR_one ++ T'') :: nil)
      with
        (map (fun x => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ((((s1, r1), (s1', r1')), vec c2 HMR_coone ++ vec c1 HMR_one ++ T'') :: nil)).
    apply IHpi.
    + apply Forall_inf_cons; [ | apply Forall_inf_nil ].
      inversion Hsum; apply H0.
    + apply Forall2_inf_cons ; [ | apply Forall2_inf_nil].
      simpl.
      transitivity (vec s1 HMR_coone ++ vec r1 HMR_one ++ vec c2 HMR_coone ++ vec c1 HMR_one ++ T).
      { etransitivity ; [ apply Permutation_Type_app ; [ | apply Permutation_Type_app]; try (apply vec_perm); try apply H2'; try apply H4'; try reflexivity | ].
        rewrite ? vec_app.
        rewrite <- ? app_assoc.
        apply Permutation_Type_app ; [ apply vec_perm; symmetry; apply H3' | ].
        rewrite ? app_assoc.
        apply Permutation_Type_app ; [ | reflexivity].
        apply Permutation_Type_app ; [ | reflexivity].
        etransitivity ; [ | apply Permutation_Type_app_comm]; apply Permutation_Type_app; try reflexivity.
        apply vec_perm.
        symmetry; apply H1'. }
      repeat (apply Permutation_Type_app; try reflexivity).
      apply seq_diamond_perm_inv.
      rewrite <- H5'.
      etransitivity; [ | symmetry; apply p].
      apply Permutation_Type_app_inv_l with (vec c1 HMR_one).
      apply Permutation_Type_app_inv_l with (vec c2 HMR_coone).
      etransitivity ; [ | apply H6'].
      apply Permutation_Type_app_inv_l with (vec r1 HMR_one).
      apply Permutation_Type_app_inv_l with (vec s1 HMR_coone).
      etransitivity; [ | apply X].
      etransitivity ; [ | symmetry; apply Permutation_Type_app ; [ | apply Permutation_Type_app]; try (apply vec_perm); try apply H2'; try apply H4'; try reflexivity ].
      rewrite ? vec_app.
      rewrite ? app_assoc.
      apply Permutation_Type_app ; [ | reflexivity].
      apply Permutation_Type_app ; [ | reflexivity].
      rewrite <- ? app_assoc.
      apply Permutation_Type_app ; [ apply vec_perm; apply H3' | ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      apply Permutation_Type_app ; [ reflexivity | ].
      apply vec_perm; apply H1'.    
  - destruct L; inversion Hperm; subst.
    apply IHpi; try assumption.
    simpl; apply Forall2_inf_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2_inf (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi; [ | rewrite Heq in f; apply f].
    clear - Hperm1 Hsum.
    revert Hsum; induction Hperm1; intros Hsum.
    + apply Forall_inf_nil.
    + inversion Hsum; subst.
      apply Forall_inf_cons; [ | apply IHHperm1];try assumption.
    + inversion Hsum; inversion X; subst.
      apply Forall_inf_cons ; [ | apply Forall_inf_cons]; try assumption.
    + apply IHHperm1_2; apply IHHperm1_1; apply Hsum.
  - inversion f.
Qed.

(** Proof of Lemma 4.37 *)
Lemma hmrr_one_can_elim : forall G T r s,
    sum_vec r = sum_vec s ->
    HMR_T ((vec s HMR_coone ++ vec r HMR_one ++ T) :: G) ->
    HMR_T (T :: G).
Proof.
  intros G T r s Heq pi.
  assert ({ L & prod
                  ( G = map (fun x  => vec (fst (fst (fst x))) HMR_coone ++ vec (snd (fst (fst x))) HMR_one ++ snd x) L)
                  (( G =  map (fun x  => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L) *
                   (Forall_inf
                      (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x))) <= sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x))))  L))}) as [L [H1 [H2 H3]]].
  { clear - G ; induction G.
    - split with nil; repeat split; try reflexivity.
      apply Forall_inf_nil.
    - destruct IHG as [ L [ H1 [H2 H3]] ].
      split with ((((nil,nil),(nil,nil)), a) :: L).
      repeat split; simpl; [rewrite H1 | rewrite H2 | ]; try reflexivity.
      apply Forall_inf_cons; try assumption.
      simpl; nra. }
  rewrite H2.
  change (T :: map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) L) with
      (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) HMR_coone ++ vec (snd (snd (fst x))) HMR_one ++ snd x) ( (((s , r) , (nil, nil)) , T) :: L)).
  apply hmrr_one_can_elim_gen.
  - simpl; apply Forall_inf_cons; try assumption; simpl; nra.
  - simpl; rewrite <- H1.
    apply pi.
Qed.

(** The diamond case in of the proof of Lemma 4.38 *)
Lemma hmrr_diamond_can_elim : forall L A,
    Forall_inf (fun x => sum_vec (snd (fst x)) = sum_vec (fst (fst x))) L ->
    (forall G T r s, sum_vec r = sum_vec s -> HMR_T ((vec s (-S A) ++ vec r A ++ T) :: G) -> HMR_T (T :: G)) ->
    HMR_T (map (fun x => (vec (fst (fst x)) (-S (<S> A)) ++ vec (snd (fst x)) (<S> A) ++ snd x)) L) ->
    HMR_T (map (fun x => snd x) L).
Proof.
  intros L A H Hsum pi.
  remember (map (fun x => vec (fst (fst x)) (-S (<S> A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L) as G.
  assert (Allperm G (map (fun x => vec (fst (fst x)) (-S (<S> A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; simpl; try now constructor).
  clear HeqG.
  revert L H Hsum X.
  induction pi; intros L Hsum IH Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X; destruct p as [[s1 r1] T1]; destruct s1; destruct r1; destruct T1; inversion X; simpl.
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi; inversion Hsum; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C; try assumption.
    change (snd p :: snd p
              :: map
              (fun x  => snd x)
              L)
      with
        (map (fun x  => snd x)
           (p :: p :: L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      repeat (apply Forall_inf_cons); assumption.
    + simpl.
      do 2 (apply Forall2_inf_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[p1 p2] p5];
      destruct p0 as [[p1' p2'] p5'];
      simpl in *;
      apply hmrr_S;
      change ((p5 ++ p5') :: map (fun x  => snd x) L)
        with (map (fun x  => snd x) (((p1 ++ p1', p2 ++ p2') , p5 ++ p5') :: L));
      (apply IHpi ; try assumption;
       [ subst;
           inversion Hsum; inversion X3;
           repeat (try apply Forall_inf_cons);
           try assumption;
           simpl in *;
           rewrite ? sum_vec_app;
           nra | ]);
      simpl; apply Forall2_inf_cons;
           [ simpl; rewrite ? vec_app ; Permutation_Type_solve |  assumption].
  - inversion f.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_T with r; try assumption.
    destruct p as ([s1 r1] , T'); simpl in *.
    change (seq_mul r T' :: map (fun x  => snd x) L)
      with
        (map (fun x  => snd x) (((mul_vec r s1, mul_vec r r1) , seq_mul r T') :: L)).
    apply IHpi; try assumption.
    + subst; inversion Hsum; subst; simpl in *.
      apply Forall_inf_cons ; try assumption; simpl.
      rewrite ? mul_vec_sum_vec; nra.
    + simpl.
      apply Forall2_inf_cons; [ | try assumption].
      rewrite <- ? seq_mul_vec_mul_vec; rewrite <- ? seq_mul_app.
      apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [[s1 r1] T1]; simpl in *.
    subst.
    destruct (perm_decomp_vec_neq_2_2 T T1 r s r1 s1 (HMR_covar n) (HMR_var n) (-S (<S> A)) (<S> A)) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
    apply hmrr_ex_seq with (vec s (HMR_covar n) ++ vec r (HMR_var n) ++ T').
    { Permutation_Type_solve. }
    apply hmrr_ID; try assumption.
    change (T' :: map (fun x => snd x) L)
      with
        (map (fun x => snd x) (((s1,r1),T')::L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      apply Forall_inf_cons ; [ | try assumption].
      simpl in *; nra.
    + simpl; apply Forall2_inf_cons; [ | try assumption].
      Permutation_Type_solve.      
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (HMR_zero <> -S (<S> A)) as Hnc by now auto.
    assert (HMR_zero <> <S> A) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r HMR_zero ++ Db) ; [ Permutation_Type_solve | ].
    apply hmrr_Z; try assumption.
    change (Db :: map (fun x  => snd x) L)
      with
        (map (fun x  => snd x) ((r1, Db) :: L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A0 +S B <> -S (<S> A)) as Hnc by now auto.
    assert (A0 +S B <> <S> A) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A0 +S B) ++ Db) ; [ Permutation_Type_solve | ].
    apply hmrr_plus.
    change ((vec r A0 ++ vec r B ++ Db) :: map (fun x  => snd x) L)
      with
        (map (fun x  => snd x) ((r1, vec r A0 ++ vec r B ++ Db) :: L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (r0 *S A0 <> -S (<S> A)) as Hnc by now auto.
    assert (r0 *S A0 <> <S> A) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ Db) ; [ Permutation_Type_solve | ].
    apply hmrr_mul; try assumption.
    change ((vec (mul_vec r0 r) A0 ++ Db) :: map (fun x  => snd x) L)
      with
        (map (fun x  => snd x) ((r1, vec (mul_vec r0 r) A0 ++ Db) :: L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    +  simpl.
       apply Forall2_inf_cons; [ | assumption].
       Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A0 \/S B <> -S (<S> A)) as Hnc by now auto.
    assert (A0 \/S B <> <S> A) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A0 \/S B) ++ Db) ; [ Permutation_Type_solve | ].
    apply hmrr_max; try assumption.
    change ((vec r B ++ Db) :: (vec r A0 ++ Db) :: map (fun x  => snd x) L)
      with
        (map (fun x  => snd x) ((r1, vec r B ++ Db) :: (r1, vec r A0 ++ Db) :: L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      repeat (try apply Forall_inf_cons); simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | apply Forall2_inf_cons ; [ | assumption] ]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A0 /\S B <> -S (<S> A)) as Hnc by now auto.
    assert (A0 /\S B <> <S> A) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec r (A0 /\S B) ++ Db); [ Permutation_Type_solve | ].
    apply hmrr_min; try assumption.
    + change ((vec r A0 ++ Db) :: map (fun x  => snd x) L)
        with
          (map (fun x  => snd x) ((r1, vec r A0 ++ Db) :: L)).
      apply IHpi1; try assumption.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | assumption]; Permutation_Type_solve.
    + change ((vec r B ++ Db) :: map (fun x  => snd x) L)
        with
          (map (fun x  => snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2; try assumption.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | try assumption]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct (perm_decomp_vec_neq_2_2 T T1 r s r1 s1 HMR_coone HMR_one (-S (<S> A)) (<S> A)) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ T').
    { Permutation_Type_solve. }
    apply hmrr_one; try assumption.
    change (T':: map (fun x => snd x) L)
      with
        (map (fun x  => snd x) (((s1,r1),T')::L)).
    apply IHpi; try assumption.
    + inversion Hsum.
      apply Forall_inf_cons ; [ | try assumption].
      simpl in *; nra.
    + simpl; apply Forall2_inf_cons; [ | try assumption].
      Permutation_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct (perm_decomp_vec_neq_2_2 (seq_diamond T) T1 r s r1 s1 HMR_coone HMR_one (-S (<S> A)) (<S> A)) as [[T' D'] [H1' [H2' H3']]]; try (intros H; inversion H; apply Hneqn; auto); try apply X.
    apply seq_diamond_perm_decomp in H1' as [D'' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_app_inv in HDb' as [[Db'' Dc'] [HD'' [HDb'' HDc']]]; subst.
    clear HDa' Da' HDb'' Db''.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ seq_diamond Dc').
    { etransitivity ; [ | symmetry; apply H2'].
      apply Permutation_Type_app ; [ reflexivity | ].
      apply Permutation_Type_app ; [ reflexivity | ].
      apply H3'. }
    apply hmrr_diamond; try assumption.
    apply IH with r1 s1; try (inversion Hsum; assumption).
    eapply hmrr_ex_seq ; [ | apply pi].
    transitivity (vec s HMR_coone ++ vec r HMR_one ++ vec s1 (-S A) ++ vec r1 A ++ Dc'); [ | Permutation_Type_solve ].
    apply Permutation_Type_app ; [ | apply Permutation_Type_app]; try reflexivity.
    apply seq_diamond_perm_inv.
    rewrite ? seq_diamond_app; rewrite <- ? vec_diamond.
    apply Permutation_Type_app_inv_l with (vec r HMR_one).
    apply Permutation_Type_app_inv_l with (vec s HMR_coone).
    etransitivity ; [ apply X | ].
    Permutation_Type_solve. 
  - destruct L; inversion Hperm; subst.
    apply IHpi; try assumption.
    simpl; apply Forall2_inf_cons; try assumption.
    transitivity T2; assumption.     
  - destruct (Permutation_Type_Forall2_inf (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi; try assumption; [ | rewrite Heq in f; apply f].
    clear - Hperm1 Hsum.
    revert Hsum; induction Hperm1; intros Hsum.
    + apply Forall_inf_nil.
    + inversion Hsum; subst.
      apply Forall_inf_cons; [ | apply IHHperm1];try assumption.
    + inversion Hsum; inversion X; subst.
      apply Forall_inf_cons ; [ | apply Forall_inf_cons]; try assumption.
    + apply IHHperm1_2; apply IHHperm1_1; apply Hsum.
  - inversion f.
Qed.

(** Proof of Lemma 4.38 *)
Lemma hmrr_can_2 : forall G T A r s,
    sum_vec r = sum_vec s ->
    HMR_T ((vec s (-S A) ++ vec r A ++ T) :: G) ->
    HMR_T (T :: G).
Proof.
  intros G T A; revert G T; induction A; intros G T r1 s1 Heq pi.
  - apply hmrr_atomic_can_elim with n r1 s1; try assumption.
  - apply hmrr_atomic_can_elim with n s1 r1; try nra.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_M_elim.
    apply hmrr_Z_inv with r1.
    apply hmrr_Z_inv with s1.
    apply HMR_le_frag with (hmr_frag_T); auto.
    repeat split.
  - apply (IHA1 G T r1 s1 Heq).
    apply (IHA2 G (vec s1 (-S A1) ++ vec r1 A1 ++ T) r1 s1 Heq).
    apply hmrr_M_elim.
    apply hmrr_ex_seq with (vec r1 A1 ++ vec r1 A2 ++ vec s1 (-S A2) ++ vec s1 (-S A1) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_plus_inv.
    apply hmrr_ex_seq with (vec s1 (-S A1) ++ vec s1 (-S A2) ++ vec r1 (A1 +S A2) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_plus_inv.
    apply HMR_le_frag with hmr_frag_T; try assumption.
    repeat split.
  - apply (IHA G T (mul_vec r r1) (mul_vec r s1)).
    { rewrite ? mul_vec_sum_vec; nra. }
    apply hmrr_M_elim.
    apply hmrr_mul_inv.
    apply hmrr_ex_seq with (vec (mul_vec r r1) A ++ vec s1 (r *S (-S A)) ++ T) ; [ Permutation_Type_solve | ].
    apply hmrr_mul_inv.
    apply HMR_le_frag with hmr_frag_T; try (repeat split).
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_C; try reflexivity.
    apply (IHA2 (T :: G) T r1 s1 Heq).
    eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply (IHA1 ((vec s1 (-S A2) ++ vec r1 A2 ++ T) :: G) T r1 s1 Heq).
    apply hmrr_M_elim.
    apply hmrr_min_inv_l with (-S A2).
    apply hmrr_ex_seq with (vec r1 A1 ++ vec s1 (-S (A1 \/S A2)) ++ T); [Permutation_Type_solve | ].
    eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply hmrr_min_inv_r with (-S A1).
    apply hmrr_ex_seq with (vec r1 A2 ++ vec s1 (-S (A1 \/S A2)) ++ T); [Permutation_Type_solve | ].
    apply hmrr_max_inv.
    apply HMR_le_frag with hmr_frag_T; try (repeat split).
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_C; try reflexivity.
    apply (IHA2 (T :: G) T r1 s1 Heq).
    eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply (IHA1 ((vec s1 (-S A2) ++ vec r1 A2 ++ T) :: G) T r1 s1 Heq).
    apply hmrr_M_elim.
    apply hmrr_ex_seq with (vec r1 A1 ++ vec s1 (-S A1) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_min_inv_l with A2.
    apply hmrr_ex_seq with (vec s1 (-S A1) ++ vec r1 (A1 /\S A2) ++ T); [Permutation_Type_solve | ].
    eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 A2 ++ vec s1 (-S A2) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_min_inv_r with A1.
    apply hmrr_ex_seq with (vec s1 (-S A2) ++ vec r1 (A1 /\S A2) ++ T); [Permutation_Type_solve | ].
    apply hmrr_max_inv.
    apply HMR_le_frag with hmr_frag_T; try (repeat split).
    apply pi.
  - apply hmrr_one_can_elim with r1 s1; try assumption.
  - apply hmrr_one_can_elim with s1 r1; try nra.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - assert ({ L & prod
                    ( G = map (fun x  => vec (fst (fst x)) (-S (<S> A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
                    (( G =  map (fun x  => snd x) L) *
                     (Forall_inf (fun x => sum_vec (snd (fst x)) = sum_vec (fst (fst x))) L))}) as [L [H1 [H2 H3]]].
    { clear - G ; induction G.
      - split with nil; repeat split; try reflexivity.
        apply Forall_inf_nil.
      - destruct IHG as [ L [ H1 [H2 H3]] ].
        split with (((nil,nil), a) :: L).
        repeat split; simpl; [rewrite H1 | rewrite H2 | ]; try reflexivity.
        apply Forall_inf_cons; try assumption.
        simpl; nra. }
    rewrite H2.
    change (T :: map (fun x : list Rpos * list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) => snd x) (((s1, r1), T) :: L)).
    apply hmrr_diamond_can_elim with A; try assumption.
    + apply Forall_inf_cons; [ | apply H3].
      apply Heq.
    + simpl.
      unfold HMR_minus in H1; fold HMR_minus in H1.
      rewrite <- H1; apply pi.
Qed.

Lemma hmrr_can_elim : forall G,
    HMR_full G ->
    HMR_T_M G.
Proof.
  intros G pi; induction pi; try now constructor.
  - now apply hmrr_T with r.
  - now apply hmrr_ex_seq with T1.
  - now apply hmrr_ex_hseq with G.
  - apply HMR_le_frag with hmr_frag_T; try repeat split.
    apply hmrr_can_2 with A r s; try assumption.
    apply hmrr_M_elim.
    apply IHpi.
Qed.
