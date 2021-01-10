(** * Implementation of Section 3.8 *)
Require Import Rpos.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.
Require Import RL.hr.invertibility.
Require Import RL.hr.M_elim.
Require Import RL.hr.hr_perm_lemmas.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** Proof of Lemma 3.43 
    
    L is the list (((r_i, s_i), (r'_i, s'_i)), T_i) *)
Lemma hrr_atomic_can_elim_gen : forall L n,
    Forall_inf (fun x => sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x))) = sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x)))) L ->
    HR_T (map (fun x => (vec (fst (fst (fst x))) (HR_covar n) ++ vec (snd (fst (fst x))) (HR_var n) ++ snd x)) L) ->
    HR_T (map (fun x => (vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x)) L).
Proof.
  intros L n H.
  remember (map (fun x => (vec (fst (fst (fst x))) (HR_covar n) ++ vec (snd (fst (fst x))) (HR_var n) ++ snd x)) L) as G.
  assert (Allperm G (map (fun x => (vec (fst (fst (fst x))) (HR_covar n) ++ vec (snd (fst (fst x))) (HR_var n) ++ snd x)) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L H X; induction pi; intros L Hsum Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X; destruct p as [[[s1 r1] [s2 r2]] T1]; destruct s1; destruct r1; destruct T1; inversion X; simpl.
    apply hrr_ID.
    { inversion Hsum; simpl in *.
      nra. }
    apply hrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_W.
    apply IHpi.
    + inversion Hsum; assumption.
    + assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_C; try assumption.
    change ((vec (fst (snd (fst p))) (HR_covar n) ++ vec (snd (snd (fst p))) (HR_var n) ++ snd p)
              :: (vec (fst (snd (fst p))) (HR_covar n) ++ vec (snd (snd (fst p))) (HR_var n) ++ snd p)
              :: map
              (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x)
              L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x)
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
      apply hrr_S;
      (apply hrr_ex_seq with (vec (fst (snd (fst p''))) (HR_covar n) ++ vec (snd (snd (fst p''))) (HR_var n) ++snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; Permutation_Type_solve | ]);
      change ((vec (fst (snd (fst p''))) (HR_covar n) ++ vec (snd (snd (fst p''))) (HR_var n) ++snd p'') :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) (L))
        with (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) (p'' :: L));
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
    apply hrr_T with r; try assumption.
    destruct p as ([[r1 r2] [s1 s2]] , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec r s1) (HR_covar n) ++ vec (mul_vec r s2) (HR_var n) ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      reflexivity. }
    change ((vec (mul_vec r s1) (HR_covar n) ++ vec (mul_vec r s2) (HR_var n) ++ seq_mul r T') :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((((mul_vec r r1, mul_vec r r2) , (mul_vec r s1 , mul_vec r s2)), seq_mul r T') :: L)).
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
      destruct (perm_decomp_vec_eq_2 T T1 r1 s1 r s (HR_var n0) (HR_covar n0)) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]]; [ now auto | apply X | ].
      apply hrr_ex_seq with (vec (c2 ++ s1') (HR_covar n0) ++ vec (c1 ++ r1') (HR_var n0) ++ T').
      { rewrite ? vec_app.
        transitivity (vec s1' (HR_covar n0) ++ vec r1' (HR_var n0) ++ (vec c2 (HR_covar n0) ++ vec c1 (HR_var n0) ++ T')); try Permutation_Type_solve. }
      change ((vec (c2 ++ s1') (HR_covar n0) ++ vec (c1 ++ r1') (HR_var n0) ++ T')
                :: map
                (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (HR_covar n0) ++ vec (snd (snd (fst x))) (HR_var n0) ++ snd x)
                L)
        with
          (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (HR_covar n0) ++ vec (snd (snd (fst x))) (HR_var n0) ++ snd x)
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
      destruct (perm_decomp_vec_neq_2 T T1 r s r1 s1 n0 n (not_eq_sym Hneqn) X) as [[T' D'] [H1' [H2' H3']]].
      apply hrr_ex_seq with (vec s (HR_covar n0) ++ vec r (HR_var n0) ++ vec s1' (HR_covar n) ++ vec r1' (HR_var n) ++ T').
      { Permutation_Type_solve. }
      apply hrr_ID; try assumption.
      change ((vec s1' (HR_covar n) ++ vec r1' (HR_var n) ++ T')
                :: map
                (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x)
                L)
        with
          (map
             (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x)
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
    assert (HR_zero <> HR_covar n) as Hnc by now auto.
    assert (HR_zero <> HR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r HR_zero ++ vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc.
      repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity; [ apply Permutation_Type_app_comm | ].
      etransitivity ; [ | symmetry; apply H1'].
      apply Permutation_Type_app; Permutation_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> HR_covar n) as Hnc by now auto.
    assert (A +S B <> HR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A +S B) ++ vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r A ++ vec r B ++ Db); [ Permutation_Type_solve | ].
    change ((vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r A ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((r1, vec r A ++ vec r B ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | assumption].
      Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (r0 *S A <> HR_covar n) as Hnc by now auto.
    assert (r0 *S A <> HR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A) ++ vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec (mul_vec r0 r) A ++ Db).
    { Permutation_Type_solve. }
    change ((vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec (mul_vec r0 r) A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((r1, vec (mul_vec r0 r) A ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      apply Forall_inf_cons; simpl in *; try assumption.
    +  simpl.
       apply Forall2_inf_cons; [ | assumption].
       Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> HR_covar n) as Hnc by now auto.
    assert (A \/S B <> HR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A \/S B) ++ vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r A ++ Db).
    { Permutation_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r B ++  Db).
    { Permutation_Type_solve. }
    change ((vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r B ++ Db) :: (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
      with
        (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((r1, vec r B ++ Db) :: (r1, vec r A ++ Db) :: L)).
    apply IHpi.
    + inversion Hsum.
      repeat (try apply Forall_inf_cons); simpl in *; try assumption.
    + simpl.
      apply Forall2_inf_cons; [ | apply Forall2_inf_cons ; [ | assumption] ]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> HR_covar n) as Hnc by now auto.
    assert (A /\S B <> HR_var n) as Hnv by now auto.
    apply Permutation_Type_sym in X.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A /\S B) ++ vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      Permutation_Type_solve. }
    apply hrr_min; try assumption.
    + apply hrr_ex_seq with (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r A ++ Db).
      { Permutation_Type_solve. }
      change ((vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
        with
          (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((r1, vec r A ++ Db) :: L)).
      apply IHpi1.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | assumption]; Permutation_Type_solve.
    + apply hrr_ex_seq with (vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r B ++ Db).
      { Permutation_Type_solve. }
      change ((vec (fst (snd r1)) (HR_covar n) ++ vec (snd (snd r1)) (HR_var n) ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L)
        with
          (map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      * inversion Hsum.
        repeat (try apply Forall_inf_cons); simpl in *; try assumption.
      * simpl.
        apply Forall2_inf_cons; [ | try assumption]; Permutation_Type_solve.
  - destruct L; inversion Hperm; subst.
    apply IHpi; try assumption.
    simpl; apply Forall2_inf_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2_inf (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
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

(** Proof of Lemma 3.41 *)
Lemma hrr_atomic_can_elim : forall G T n r s,
    sum_vec r = sum_vec s ->
    HR_T ((vec s (HR_covar n) ++ vec r (HR_var n) ++ T) :: G) ->
    HR_T (T :: G).
Proof.
  intros G T n r s Heq pi.
  assert ({ L & prod
                  ( G = map (fun x  => vec (fst (fst (fst x))) (HR_covar n) ++ vec (snd (fst (fst x))) (HR_var n) ++ snd x) L)
                  (( G =  map (fun x  => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L) *
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
  change (T :: map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) L) with
      (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) (HR_covar n) ++ vec (snd (snd (fst x))) (HR_var n) ++ snd x) ( (((s , r) , (nil, nil)) , T) :: L)).
  apply hrr_atomic_can_elim_gen.
  - simpl; apply Forall_inf_cons; try assumption; simpl; nra.
  - simpl; rewrite <- H1.
    apply pi.
Qed.

Lemma hrr_can_2 : forall G T A r s,
    sum_vec r = sum_vec s ->
    HR_T ((vec s (-S A) ++ vec r A ++ T) :: G) ->
    HR_T (T :: G).
Proof.
  intros G T A; revert G T; induction A; intros G T r' s' Heq pi.
  - apply hrr_atomic_can_elim with n r' s'; try assumption.
  - apply hrr_atomic_can_elim with n s' r'; try nra.
    eapply hrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hrr_M_elim.
    apply hrr_Z_inv with r'.
    apply hrr_Z_inv with s'.
    apply HR_le_frag with (hr_frag_T); auto.
    repeat split.
  - apply (IHA1 G T r' s' Heq).
    apply (IHA2 G (vec s' (-S A1) ++ vec r' A1 ++ T) r' s' Heq).
    apply hrr_M_elim.
    apply hrr_ex_seq with (vec r' A1 ++ vec r' A2 ++ vec s' (-S A2) ++ vec s' (-S A1) ++ T); [ Permutation_Type_solve | ].
    apply hrr_plus_inv.
    apply hrr_ex_seq with (vec s' (-S A1) ++ vec s' (-S A2) ++ vec r' (A1 +S A2) ++ T); [ Permutation_Type_solve | ].
    apply hrr_plus_inv.
    apply HR_le_frag with hr_frag_T; try assumption.
    repeat split.
  - apply (IHA G T (mul_vec r r') (mul_vec r s')).
    { rewrite ? mul_vec_sum_vec; nra. }
    apply hrr_M_elim.
    apply hrr_mul_inv.
    apply hrr_ex_seq with (vec (mul_vec r r') A ++ vec s' (r *S (-S A)) ++ T) ; [ Permutation_Type_solve | ].
    apply hrr_mul_inv.
    apply HR_le_frag with hr_frag_T; try (repeat split).
    eapply hrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hrr_C; try reflexivity.
    apply (IHA2 (T :: G) T r' s' Heq).
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply (IHA1 ((vec s' (-S A2) ++ vec r' A2 ++ T) :: G) T r' s' Heq).
    apply hrr_M_elim.
    apply hrr_min_inv_l with (-S A2).
    apply hrr_ex_seq with (vec r' A1 ++ vec s' (-S (A1 \/S A2)) ++ T); [Permutation_Type_solve | ].
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply hrr_min_inv_r with (-S A1).
    apply hrr_ex_seq with (vec r' A2 ++ vec s' (-S (A1 \/S A2)) ++ T); [Permutation_Type_solve | ].
    apply hrr_max_inv.
    apply HR_le_frag with hr_frag_T; try (repeat split).
    eapply hrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hrr_C; try reflexivity.
    apply (IHA2 (T :: G) T r' s' Heq).
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply (IHA1 ((vec s' (-S A2) ++ vec r' A2 ++ T) :: G) T r' s' Heq).
    apply hrr_M_elim.
    apply hrr_ex_seq with (vec r' A1 ++ vec s' (-S A1) ++ T); [ Permutation_Type_solve | ].
    apply hrr_min_inv_l with A2.
    apply hrr_ex_seq with (vec s' (-S A1) ++ vec r' (A1 /\S A2) ++ T); [Permutation_Type_solve | ].
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r' A2 ++ vec s' (-S A2) ++ T); [ Permutation_Type_solve | ].
    apply hrr_min_inv_r with A1.
    apply hrr_ex_seq with (vec s' (-S A2) ++ vec r' (A1 /\S A2) ++ T); [Permutation_Type_solve | ].
    apply hrr_max_inv.
    apply HR_le_frag with hr_frag_T; try (repeat split).
    apply pi.
Qed.

(** Proof of Theorem 3.13 *)
Lemma hrr_can_elim : forall G,
    HR_full G ->
    HR_T_M G.
Proof.
  intros G pi; induction pi; try now constructor.
  - now apply hrr_T with r.
  - now apply hrr_ex_seq with T1.
  - now apply hrr_ex_hseq with G.
  - apply HR_le_frag with hr_frag_T; try repeat split.
    apply hrr_can_2 with A r s; try assumption.
    apply hrr_M_elim.
    apply IHpi.
Qed.
