(** * Implementation of Section 3.7 *)
Require Import Rpos.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.
Require Import RL.hr.tech_lemmas.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

(** Proof of Lemma 3.40 *)
Lemma hrr_mul_vec : forall L,
    HR_T (map (fun x => snd x) L) ->
    HR_T (map (fun x => seq_mul_vec (fst x) (snd x)) L).
Proof.
  intros L pi.
  remember (map (fun x => snd x) L) as G.
  revert L HeqG; induction pi; intros L HeqG.
  - destruct L; [ | destruct L]; try now inversion HeqG.
    destruct p as [r T]; destruct T; try now inversion HeqG.
    simpl; rewrite seq_mul_vec_nil_r; apply hrr_INIT.
  - destruct L; try now inversion HeqG.
    simpl; apply hrr_W.
    apply IHpi.
    simpl in HeqG; inversion HeqG.
    reflexivity.
  - destruct L; try now inversion HeqG.
    simpl; apply hrr_C.
    change (seq_mul_vec (fst p) (snd p)
                    :: seq_mul_vec (fst p) (snd p) :: map (fun x => seq_mul_vec (fst x) (snd x)) L)
      with
        (map (fun x => seq_mul_vec (fst x) (snd x)) (p :: p :: L)).
    apply IHpi.
    simpl in HeqG; inversion HeqG.
    reflexivity.
  - destruct L; [ | destruct L]; try destruct p as [r1 T1']; try destruct p0 as [r2 T2']; inversion HeqG; subst.
    destruct r1 ; [ | destruct r2].
    + simpl.
      apply hrr_ex_hseq with ((seq_mul_vec r2 T2' :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) ++ (nil :: nil)); [ Permutation_Type_solve |] .
      apply hrr_W_gen.
      apply hrr_INIT.
    + simpl.
      apply hrr_ex_hseq with ((seq_mul_vec (r :: r1) T1' :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) ++ (nil :: nil)); [ Permutation_Type_solve |] .
      apply hrr_W_gen.
      apply hrr_INIT.
    + simpl.
      unfold HR_T; change hr_frag_T with (hr_frag_add_T hr_frag_T).
      apply hrr_T_vec with (r0 :: r2); try now auto.
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      change hr_frag_T with (hr_frag_add_T hr_frag_T).
      apply hrr_T_vec with (r :: r1); try now auto.
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_S.
      apply hrr_ex_seq with (seq_mul_vec (vec_mul_vec (r :: r1) (r0 :: r2)) (T1' ++ T2')).
      { etransitivity; [ symmetry; apply seq_mul_vec_twice | ].
        etransitivity ; [ apply seq_mul_vec_perm_r; apply (seq_mul_vec_app_r _ _ (r0 :: r2)) | ].
        etransitivity ; [ apply seq_mul_vec_app_r | ].
        etransitivity ; [ apply Permutation_Type_app ; [ apply seq_mul_vec_twice_comm | reflexivity ] | ].
        Permutation_Type_solve. }
      change (seq_mul_vec (vec_mul_vec (r :: r1) (r0 :: r2)) (T1' ++ T2') :: map (fun x => seq_mul_vec (fst x) (snd x)) L)
        with
          (map (fun x => seq_mul_vec (fst x) (snd x)) ((vec_mul_vec (r :: r1) (r0 :: r2) , T1' ++ T2') :: L)).
      apply IHpi; reflexivity.
  - inversion f.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.    
    simpl.
    apply hrr_T with r; try assumption.
    rewrite seq_mul_seq_mul_vec.
    change (seq_mul_vec r1 (seq_mul r T1) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L)
      with (map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) ((r1, seq_mul r T1) :: L)).
    apply IHpi.
    reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.    
    simpl.
    apply hrr_ex_seq with (vec (vec_mul_vec r1 s) (HR_covar n) ++ vec (vec_mul_vec r1 r) (HR_var n) ++ seq_mul_vec r1 T).
    { etransitivity ; [ | symmetry ; apply seq_mul_vec_app_r].
      etransitivity ; [ | symmetry; apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity ].
      apply Permutation_Type_app ; [ | apply Permutation_Type_app]; try rewrite seq_mul_vec_vec_mul_vec; reflexivity. }
    apply hrr_ID.
    { rewrite ? sum_vec_vec_mul_vec.
      nra. }
    change (seq_mul_vec r1 T :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, T) :: L)).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    simpl.
    eapply hrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
    rewrite seq_mul_vec_vec_mul_vec.
    apply hrr_Z.
    change (seq_mul_vec r1 T :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, T) :: L)).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    simpl.
    eapply hrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
    rewrite seq_mul_vec_vec_mul_vec.
    apply hrr_plus.
    rewrite <- ? seq_mul_vec_vec_mul_vec.
    apply hrr_ex_seq with (seq_mul_vec r1 (vec r A ++ vec r B ++ T)).
    { etransitivity ; [apply seq_mul_vec_app_r | ].
      apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity. }
    change (seq_mul_vec r1 (vec r A ++ vec r B ++ T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, vec r A ++ vec r B ++ T) :: L)).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    simpl.
    eapply hrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
    rewrite seq_mul_vec_vec_mul_vec.
    apply hrr_mul.
    rewrite <- vec_mul_vec_mul_vec_comm.
    rewrite <- ? seq_mul_vec_vec_mul_vec.
    eapply hrr_ex_seq ; [ apply seq_mul_vec_app_r | ].
    change (seq_mul_vec r1 (vec (mul_vec r0 r) A ++ T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, vec (mul_vec r0 r) A ++ T) :: L)).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    simpl.
    eapply hrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
    rewrite seq_mul_vec_vec_mul_vec.
    apply hrr_max.
    rewrite <- ? seq_mul_vec_vec_mul_vec.
    eapply hrr_ex_seq ; [ apply seq_mul_vec_app_r | ].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    eapply hrr_ex_seq ; [ apply seq_mul_vec_app_r | ].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    change (seq_mul_vec r1 (vec r B ++ T) :: seq_mul_vec r1 (vec r A ++ T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, vec r B ++ T) :: (r1, vec r A ++ T) :: L)).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst.
    simpl.
    eapply hrr_ex_seq ; [ symmetry; apply seq_mul_vec_app_r | ].
    rewrite seq_mul_vec_vec_mul_vec.
    apply hrr_min;
      rewrite <- ? seq_mul_vec_vec_mul_vec;
      (eapply hrr_ex_seq ; [ apply seq_mul_vec_app_r | ]);
      [ change (seq_mul_vec r1 (vec r A ++ T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, vec r A ++ T) :: L)) ; apply IHpi1
      | change (seq_mul_vec r1 (vec r B ++ T) :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L) with (map (fun x => seq_mul_vec (fst x) (snd x)) ((r1, vec r B ++ T) :: L)) ; apply IHpi2 ];
      reflexivity.
  - destruct L; try destruct p0 as [r1 T1']; inversion HeqG; subst.
    simpl.
    eapply hrr_ex_seq ; [ apply seq_mul_vec_perm_r; apply p | ].
    change (seq_mul_vec r1 T1 :: map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) L)
      with
        (map (fun x : list Rpos * sequent => seq_mul_vec (fst x) (snd x)) ((r1 , T1) :: L)).
    apply IHpi; reflexivity.
  - subst.
    apply Permutation_Type_map_inv in p as [L' Heq Hperm].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map ; symmetry; apply Hperm | ].
    apply IHpi.
    apply Heq.
  - inversion f.
Qed.

(** Proof of Lemma 3.39 *)
Lemma hrr_M_gen : forall L H D,
    HR_T (map (fun x => snd x) L) ->
    HR_T (D :: H) ->
    HR_T (map (fun x => snd x ++ seq_mul_vec (fst x) D) L ++ H).
Proof.
  intros L H D pi pi2.
  remember (map (fun x => snd x) L) as G.
  revert L HeqG.
  induction pi; intros L HeqG.
  - destruct L; try (destruct p as [r1 T1]; destruct T1); inversion HeqG; simpl.
    destruct L; inversion H1; simpl.
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
    apply hrr_mul_vec.
    simpl; rewrite <- Heq1.
    apply pi2.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    apply hrr_W.
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    apply hrr_C.
    change ((T1 ++ seq_mul_vec r1 D)
              :: (T1 ++ seq_mul_vec r1 D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, T1) :: (r1 , T1) :: L) ++ H).
    apply IHpi; reflexivity.
  - destruct L; [ | destruct L]; try destruct p as [r1 T1']; try destruct p0 as [r2 T2']; inversion HeqG; subst; simpl.
    apply hrr_S.
    apply hrr_ex_seq with ((T1' ++ T2') ++ seq_mul_vec (r1 ++ r2) D).
    { rewrite seq_mul_vec_app_l.
      Permutation_Type_solve. }
    change (((T1' ++ T2') ++ seq_mul_vec (r1 ++ r2) D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1 ++ r2, T1' ++ T2') :: L) ++ H).
    apply IHpi; reflexivity.
  - inversion f.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    apply hrr_T with r; try assumption.
    rewrite seq_mul_app; rewrite seq_mul_seq_mul_vec_2.
    change ((seq_mul r T1 ++ seq_mul_vec (mul_vec r r1) D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((mul_vec r r1, seq_mul r T1) :: L) ++ H).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    rewrite <- ? app_assoc; apply hrr_ID; try assumption.
    change ((T ++ seq_mul_vec r1 D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, T) :: L) ++ H).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    rewrite <- ? app_assoc; apply hrr_Z; try assumption.
    change ((T ++ seq_mul_vec r1 D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, T) :: L) ++ H).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    rewrite <- ? app_assoc; apply hrr_plus; try assumption.
    replace ((vec r A ++ vec r B ++ T ++ seq_mul_vec r1 D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, vec r A ++ vec r B ++ T) :: L) ++ H) by (simpl; rewrite <- ? app_assoc; reflexivity).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    rewrite <- ? app_assoc; apply hrr_mul; try assumption.
    replace ((vec (mul_vec r0 r) A ++ T ++ seq_mul_vec r1 D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, vec (mul_vec r0 r) A ++ T) :: L) ++ H) by (simpl; rewrite <- ? app_assoc; reflexivity).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    rewrite <- ? app_assoc; apply hrr_max; try assumption.
    replace ((vec r B ++ T ++ seq_mul_vec r1 D) :: (vec r A ++ T ++ seq_mul_vec r1 D)
              :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, vec r B ++ T) :: (r1, vec r A ++ T) :: L) ++ H) by (simpl; rewrite <- ? app_assoc; reflexivity).
    apply IHpi; reflexivity.
  - destruct L; try destruct p as [r1 T1]; inversion HeqG; subst; simpl.
    rewrite <- ? app_assoc; apply hrr_min; try assumption;
      [ replace ((vec r A ++ T ++ seq_mul_vec r1 D) :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
          with (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, vec r A ++ T) :: L) ++ H) by (simpl; rewrite <- ? app_assoc; reflexivity); apply IHpi1
       | replace ((vec r B ++ T ++ seq_mul_vec r1 D) :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
           with (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, vec r B ++ T) :: L) ++ H)  by (simpl; rewrite <- ? app_assoc; reflexivity); apply IHpi2];
      reflexivity.
  - destruct L; try destruct p0 as [r1 T1']; inversion HeqG; subst; simpl.
    eapply hrr_ex_seq ; [ apply Permutation_Type_app ; [ apply p | reflexivity] | ].
    change ((T1 ++ seq_mul_vec r1 D) :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) L ++ H)
      with (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) D) ((r1, T1) :: L) ++ H).
    apply IHpi; reflexivity.
  - subst.
    apply Permutation_Type_map_inv in p as [L' Heq Hperm].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_app ; [ apply Permutation_Type_map ; symmetry; apply Hperm | reflexivity ] | ].
    apply IHpi.
    apply Heq.
  - inversion f.
Qed.

(** Proof of Theorem 3.12 *)
Lemma hrr_M_elim : forall G,
    HR_T_M G ->
    HR_T G.
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
    apply hrr_ex_hseq with (G ++ ((T1 ++ T2) :: nil)); [ Permutation_Type_solve | ].
    change (hr_frag_T) with hr_frag_T; apply hrr_C_gen.
    apply hrr_ex_hseq with (((T1 ++ T2) :: G) ++ G); [ Permutation_Type_solve | ].
    pattern G at 1; rewrite Heq2.
    replace ((T1 ++ T2)
               :: map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) T2) L)
      with (map (fun x : list Rpos * list (Rpos * term) => snd x ++ seq_mul_vec (fst x) T2) ((One :: nil , T1) :: L)) by (simpl; rewrite app_nil_r; now rewrite seq_mul_One).
    apply hrr_M_gen; try assumption.
    simpl.
    rewrite <- Heq1; apply IHpi1.
  - now apply hrr_T with r.
  - now apply hrr_ex_seq with T1.
  - now apply hrr_ex_hseq with G.
Qed.
