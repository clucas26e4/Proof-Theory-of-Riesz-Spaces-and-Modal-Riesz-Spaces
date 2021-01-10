(** * Some useful tools to manipulate lists of lists instead of multisets of multisets (and so to deal with the exchange rules) *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Definition Allperm := (Forall2_inf (Permutation_Type (A:=Rpos * term))).

Lemma decomp_Permutation_Type_2 A : forall l l' (x y : A),
    Permutation_Type (x :: y :: l) l' ->
    {' (l1,l2,l3) : _ & {l' = l1 ++ x :: l2 ++ y :: l3} +
                        {l' = l1 ++ y :: l2 ++ x :: l3}}.
Proof.
  intros l l' x y Hperm.
  destruct (in_inf_split x l') as [[la lb] Heq].
  { apply Permutation_Type_in_inf with (x :: y :: l); [ apply Hperm | ].
    left; reflexivity. }
  case (in_inf_app_or la lb y).
  { apply Permutation_Type_in_inf with (y :: l) ; [ | left; reflexivity].
    apply Permutation_Type_cons_inv with x.
    rewrite Heq in Hperm; Permutation_Type_solve. }
  - intros Hin.
    apply in_inf_split in Hin as [[l1 l2] Heq' ].
    split with (l1 , l2 , lb).
    right; subst.
    rewrite <- ? app_assoc; reflexivity.
  - intros Hin.
    apply in_inf_split in Hin as [[l1 l2] Heq' ].
    split with (la , l1 , l2).
    left; subst; reflexivity.
Qed.
    
Lemma decomp_M_case : forall T1 T2 r D A,
    Permutation_Type (T1 ++ T2) (vec r A ++ D) ->
    {' (D1, D2, r1, r2) : _ &
                          prod (Permutation_Type r (r1 ++ r2))
                               ((Permutation_Type D (D1 ++ D2)) *
                                (Permutation_Type T1 (vec r1 A ++ D1)) *
                                (Permutation_Type T2 (vec r2 A ++ D2)))}.
Proof.
  intros T1 T2 r D A Hperm.
  revert T1 T2 D Hperm; induction r; intros T1 T2 D Hperm.
  - simpl in Hperm.
    split with (T1 , T2, nil, nil).
    simpl; repeat split; try Permutation_Type_solve.
  - simpl in Hperm.
    case (in_inf_app_or T1 T2 (a , A)).
    + apply Permutation_Type_in_inf with ((a, A) :: vec r A ++ D); try Permutation_Type_solve.
      left; reflexivity.
    + intros Hin.
      apply in_inf_split in Hin as [[l1 l2] Heq].
      destruct (IHr (l1 ++ l2) T2 D) as [[[[D1 D2] r1'] r2] [H1' [[H2 H3] H4]]].
      * apply Permutation_Type_cons_inv with (a, A).
        rewrite Heq in Hperm; Permutation_Type_solve.
      * split with (D1, D2, (a :: r1'), r2).
        rewrite Heq; simpl; repeat split; try Permutation_Type_solve.
    + intros Hin.
      apply in_inf_split in Hin as [[l1 l2] Heq].
      destruct (IHr T1 (l1 ++ l2) D) as [[[[D1 D2] r1'] r2] [H1' [[H2 H3] H4]]].
      * apply Permutation_Type_cons_inv with (a, A).
        rewrite Heq in Hperm; Permutation_Type_solve.
      * split with (D1, D2, r1', (a :: r2)).
        rewrite Heq; simpl; repeat split; try Permutation_Type_solve.
Qed.
    
Lemma decomp_M_case_2 : forall T1 T2 r s D A B,
    Permutation_Type (T1 ++ T2) (vec r A ++ vec s B ++ D) ->
    {' (D1, D2, r1, r2, s1, s2) : _ &
                          prod (Permutation_Type r (r1 ++ r2))
                               ((Permutation_Type s (s1 ++ s2)) *
                                (Permutation_Type D (D1 ++ D2)) *
                                (Permutation_Type T1 (vec r1 A ++ vec s1 B ++ D1)) *
                                (Permutation_Type T2 (vec r2 A ++ vec s2 B ++ D2)))}.
Proof.
  intros T1 T2 r s D A B Hperm.
  apply decomp_M_case in Hperm as [[[[D1 D2] r1] r2] [H1 [[H2 H3] H4]]].
  symmetry in H2.
  apply decomp_M_case in H2 as [[[[D1' D2'] s1] s2] [H1' [[H2' H3'] H4']]].
  split with (D1', D2', r1,r2,s1,s2).
  repeat split; try Permutation_Type_solve.
Qed.

Lemma perm_decomp_vec_neq_2 : forall T D r s t A B C,
    A <> B ->
    A <> C ->
    Permutation_Type (vec s B ++ vec t C ++ T) (vec r A ++ D) ->
    {' (Ta, Tb, Da, Db) : _ &
                          prod (Permutation_Type T (Ta ++ Tb))
                               ((Permutation_Type D (Da ++ Db)) *
                                (Permutation_Type (vec s B ++ vec t C) Da) *
                                (Permutation_Type (vec r A) Ta) *
                                (Permutation_Type Tb Db)) }.
Proof.
  intros T D r s t A B C Hnc Hnv Hperm.
  revert D r Hperm; induction s; [ induction t | ]; intros D r Hperm.
  - split with (vec r A , D, nil, D).
    repeat split; try assumption; try reflexivity.
  - simpl in *.
    assert (In_inf (a, C) D) as HinD.
    { destruct (in_inf_app_or (vec r A) D (a , C)).
      + apply Permutation_Type_in_inf with ((a, C) :: vec t C ++ T); try assumption.
        left; reflexivity.
      + exfalso.
        clear - i Hnv.
        induction r; inversion i.
        * inversion H.
          apply Hnv; apply H2.
        * apply IHr; apply X.
      + assumption. }
    destruct (Add_inf_inv _ _ HinD) as [D' Hadd].
    apply Permutation_Type_Add_inf in Hadd.
    destruct (IHt D' r) as [ [[[Ta Tb] Da ] Db] [H1 [[[H2 H3] H4] H5]]].
    { apply Permutation_Type_cons_inv with (a, C).
      etransitivity; [ apply Hperm | ].
      Permutation_Type_solve. }
    split with (Ta, Tb, ((a, C):: Da), Db).
    repeat split; try assumption; try reflexivity; try Permutation_Type_solve.
  - simpl in *.
    assert (In_inf (a, B) D) as HinD.
    { destruct (in_inf_app_or (vec r A) D (a , B)).
      + apply Permutation_Type_in_inf with ((a, B) :: vec s (B) ++ vec t C ++ T); try assumption.
        left; reflexivity.
      + exfalso.
        clear - i Hnc.
        induction r; inversion i.
        * inversion H.
          apply Hnc; apply H2.
        * apply IHr; apply X.
      + assumption. }
    destruct (Add_inf_inv _ _ HinD) as [D' Hadd].
    apply Permutation_Type_Add_inf in Hadd.
    destruct (IHs D' r) as [ [[[Ta Tb] Da ] Db] [H1 [[[H2 H3] H4] H5]]].
    { apply Permutation_Type_cons_inv with (a, B).
      Permutation_Type_solve. }
    split with (Ta, Tb, ((a, B):: Da), Db).
    repeat split; try assumption; try reflexivity; try Permutation_Type_solve.
Qed.



Lemma perm_decomp_vec_neq : forall T D r s A B,
    A <> B ->
    Permutation_Type (vec s B ++ T) (vec r A ++ D) ->
    {' (Ta, Tb, Da, Db) : _ &
                          prod (Permutation_Type T (Ta ++ Tb))
                               ((Permutation_Type D (Da ++ Db)) *
                                (Permutation_Type (vec s B) Da) *
                                (Permutation_Type (vec r A) Ta) *
                                (Permutation_Type Tb Db)) }.
Proof.
  intros T D r s A B Hneq Hperm.
  revert D r Hperm; induction s; intros D r Hperm.
  - split with (vec r A , D, nil, D).
    repeat split; try assumption; try reflexivity.
  - simpl in *.
    assert (In_inf (a, B) D) as HinD.
    { destruct (in_inf_app_or (vec r A) D (a , B)).
      + apply Permutation_Type_in_inf with ((a, B) :: vec s B ++ T); try assumption.
        left; reflexivity.
      + exfalso.
        clear - i Hneq.
        induction r; inversion i.
        * inversion H.
          apply Hneq; apply H2.
        * apply IHr; apply X.
      + assumption. }
    destruct (Add_inf_inv _ _ HinD) as [D' Hadd].
    apply Permutation_Type_Add_inf in Hadd.
    destruct (IHs D' r) as [ [[[Ta Tb] Da ] Db] [H1 [[[H2 H3] H4] H5]]].
    { apply Permutation_Type_cons_inv with (a, B).
      etransitivity; [ apply Hperm | ].
      Permutation_Type_solve. }
    split with (Ta, Tb, ((a, B):: Da), Db).
    repeat split; try assumption; try reflexivity; try Permutation_Type_solve.
Qed.

Lemma perm_decomp_vec_eq : forall T D r s A,
    Permutation_Type (vec s A ++ T) (vec r A ++ D) ->
    {' (a , b , c , T', D') : _ &
                     prod (Permutation_Type r  (a ++ b))
                          ((Permutation_Type s  (b ++ c)) *
                           (Permutation_Type T (vec a A ++ T')) *
                           (Permutation_Type D (vec c A ++ D')) *
                           (Permutation_Type T' D')) }.
Proof.
  intros T D r s A Hperm.
  revert D r Hperm; induction s; intros D r Hperm.
  + split with (r, nil, nil, D , D).
    repeat split; try Permutation_Type_solve.
  + simpl in Hperm.
    case (in_inf_app_or (vec r A) D (a , A)).
    * apply Permutation_Type_in_inf with ((a, A) :: vec s A ++ T); [apply Hperm | ].
      left; reflexivity.
    * intro Hin.
      assert { r' & Permutation_Type r (a :: r')}.
      { clear - Hin.
        induction r.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with r; simpl; reflexivity.
          + specialize (IHr Hin) as [r' Hperm].
            split with (a0 :: r').
            Permutation_Type_solve. }
      destruct X as [r' Hperm'].
      destruct (IHs D r') as [ [[[[a1 b1] c1] T'] D'] [H1 [[[H2 H3] H4] H5]]].
      { apply Permutation_Type_cons_inv with (a, A).
        transitivity (vec r A ++ D); try Permutation_Type_solve.
        change ((a, A) :: vec r' A ++ D) with (vec (a :: r') A ++ D).
        apply Permutation_Type_app; try reflexivity.
        apply vec_perm; apply Hperm'. }
      split with (a1 , a :: b1, c1, T' , D').
      repeat split; try Permutation_Type_solve.
    * intro Hin.
      destruct (Add_inf_inv _ _ Hin) as [D' Hadd].
      apply Permutation_Type_Add_inf in Hadd.
      destruct (IHs D' r) as [ [[[[a1 b1] c1] T'] D''] [H1 [[[H2 H3] H4] H5]]].
      { apply Permutation_Type_cons_inv with (a, A).
        Permutation_Type_solve. }
      split with (a1, b1, a :: c1 , T', D'').
      repeat split; try Permutation_Type_solve.
Qed.

Lemma perm_decomp_vec_eq_2 : forall T D r s r' s' A B,
    A <> B ->
    Permutation_Type (vec s' B ++ vec r' A ++ T) (vec s B ++ vec r A ++ D) ->
    {' (a1 , b1 , c1, a2 , b2, c2, T', D') : _ &
                     prod (Permutation_Type r  (a1 ++ b1))
                          ((Permutation_Type r'  (b1 ++ c1)) *
                           (Permutation_Type s  (a2 ++ b2)) *
                           (Permutation_Type s'  (b2 ++ c2)) *
                           (Permutation_Type T (vec a2 B ++ vec a1 A ++ T')) *
                           (Permutation_Type D (vec c2 B ++ vec c1 A ++ D')) *
                           (Permutation_Type T' D')) }.
Proof.
  intros T D r s r' s' A B Hneq Hperm.
  revert s r' r T D A B Hneq Hperm.
  induction s'; [ intros s ; induction s ; [ intros r'; induction r'; [ intros r; induction r | ] | ] | ].
  - intros T D A B Hneq Hperm.
    split with (nil, nil,nil,nil,nil,nil , T , D).
    repeat split; try Permutation_Type_solve.
  - intros T D A B Hneq Hperm.
    simpl in *.
    destruct (in_inf_split (a , A) T) as [[T1 T2] HeqT].
    { apply Permutation_Type_in_inf with ((a , A) :: vec r A ++ D); try Permutation_Type_solve.
      left; reflexivity. }
    subst.
    destruct (IHr (T1 ++ T2) D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
    { apply Permutation_Type_cons_inv with (a , A).
      Permutation_Type_solve. }
    split with ((a :: a1), b1,c1,a2,b2,c2, T' , D').
    repeat split; try Permutation_Type_solve.
  - intros r T D A B Hneq Hperm; simpl in *.
    case (in_inf_app_or (vec r A) D (a , A)).
    { apply Permutation_Type_in_inf with ((a , A) :: vec r' A ++ T); try Permutation_Type_solve.
      left; reflexivity. }
    + intros Hin.
      assert { r' & Permutation_Type r (a :: r')}.
      { clear - Hin.
        induction r.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with r; simpl; reflexivity.
          + specialize (IHr Hin) as [r' Hperm].
            split with (a0 :: r').
            Permutation_Type_solve. }
      destruct X as [vr Hperm'].
      destruct (IHr' vr T D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a , A).
        change ((a , A) :: vec vr A ++ D) with (vec (a :: vr) A ++ D).
        etransitivity ; [ apply Hperm | ].
        apply Permutation_Type_app; [ apply vec_perm | ]; Permutation_Type_solve. }
      split with (a1, a :: b1, c1, a2, b2, c2, T', D').
      repeat split; simpl; try Permutation_Type_solve.
    + intros Hin.
      apply in_inf_split in Hin as [[D1 D2] HeqD]; subst.
      destruct (IHr' r T (D1 ++ D2) A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a,  A).
        Permutation_Type_solve. }
      split with (a1, b1, a :: c1 , a2, b2, c2, T', D').
      simpl; repeat split; try Permutation_Type_solve.
  - intros r' r T D A B Hneq Hperm; simpl in *.
    assert (In_inf (a , B) T).
    { case (in_inf_app_or (vec r' A) T (a , B)); try (intro H; assumption).
      { apply Permutation_Type_in_inf with ((a, B) :: vec s B ++ vec r A ++ D); try Permutation_Type_solve.
        left; reflexivity. }
      intro H; exfalso; clear - H Hneq.
      induction r'; simpl in H; inversion H.
      + inversion H0; subst; now apply Hneq.
      + apply IHr'; try assumption. }
    apply in_inf_split in X as [[T1 T2] Heq]; subst.
    destruct (IHs r' r (T1 ++ T2) D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
    { apply Permutation_Type_cons_inv with (a , B).
      Permutation_Type_solve. }
    split with (a1, b1,c1,a :: a2,b2,c2, T' , D').
    repeat split; try Permutation_Type_solve.
  - intros s r' r T D A B Hneq Hperm; simpl in *.
    case (in_inf_app_or (vec s B) (vec r A ++ D) (a , B)).
    { apply Permutation_Type_in_inf with ((a, B) :: vec s' B ++ vec r' A ++ T); try Permutation_Type_solve.
      left; reflexivity. }
    + intros Hin.
      assert { s' & Permutation_Type s (a :: s')}.
      { clear - Hin.
        induction s.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with s; simpl; reflexivity.
          + specialize (IHs Hin) as [s' Hperm].
            split with (a0 :: s').
            Permutation_Type_solve. }
      destruct X as [vs Hperm'].
      destruct (IHs' vs r' r T D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a , B).
        change ((a , B) :: vec vs B ++ vec r A ++  D) with (vec (a :: vs) B ++ vec r A ++ D).
        etransitivity ; [ apply Hperm | ].
        apply Permutation_Type_app; [ apply vec_perm | ]; Permutation_Type_solve. }
      split with (a1, b1, c1, a2, a::b2, c2, T', D').
      repeat split; simpl; try Permutation_Type_solve.
    + intros H.
      assert (In_inf (a , B) D) as Hin; [ | clear H].
      { case (in_inf_app_or (vec r A) D (a , B)); [ apply H | | ]; try (intros H0; assumption).
        intro H0; exfalso; clear - H0 Hneq.
        induction r; simpl in H0; inversion H0.
        - inversion H; subst; now apply Hneq.
        - apply IHr; try assumption. }
      apply in_inf_split in Hin as [[D1 D2] HeqD]; subst.
      destruct (IHs' s r' r T (D1 ++ D2) A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a,  B).
        Permutation_Type_solve. }
      split with (a1, b1, c1 , a2, b2, a :: c2, T', D').
      simpl; repeat split; try Permutation_Type_solve.
Qed.

Lemma perm_decomp_vec_neq_2_2 : forall T1 T2 r s r' s' A B C D,
    A <> C ->
    A <> D ->
    B <> C ->
    B <> D ->
    Permutation_Type (vec s A ++ vec r B ++ T1) (vec s' C ++ vec r' D ++ T2) ->
    {' (T', D') : _ &
                          prod (Permutation_Type T1 (vec s' C ++ vec r' D ++ T'))
                               ((Permutation_Type T2 (vec s A ++ vec r B ++ D')) *
                                (Permutation_Type T' D'))}.
Proof.
  intros T1 T2 r s r' s'.
  revert s r' r T1 T2.
  induction s'; [ intros s ; induction s ; [ intros r' ; induction r' ; [ intros r; induction r | ] | ] | ].
  - intros T1 T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4 Hperm.
    split with (T1, T2).
    simpl in *; repeat split; Permutation_Type_solve.
  - intros T1 T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4 Hperm.
    simpl in *.
    destruct (in_inf_split (a , B) T2) as [[D1 D2] Heq].
    { apply Permutation_Type_in_inf with ((a, B) :: vec r B ++ T1); try Permutation_Type_solve.
      left; reflexivity. }
    subst.
    destruct (IHr T1 (D1 ++ D2) A B C D Hneq1 Hneq2 Hneq3 Hneq4) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , B).
      Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
  - intros r T1 T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4 Hperm.
    simpl in *.
    destruct (in_inf_split (a , D) T1) as [[T1' T2'] Heq].
    { case (in_inf_app_or (vec r B) T1 (a , D)) ; [ apply Permutation_Type_in_inf with ((a, D) :: vec r' D ++ T2); [ Permutation_Type_solve | left; reflexivity ] | | auto ].
      intros H; clear - H Hneq4.
      exfalso.
      induction r; simpl in H; inversion H.
      - inversion H0.
        apply Hneq4; apply H3.
      - apply IHr; apply X. }
    subst.
    destruct (IHr' r (T1' ++ T2') T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , D); Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
  - intros r' r T1 T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4 Hperm.
    simpl in *.
    destruct (in_inf_split (a , A) T2) as [[D1 D2] Heq].
    { case (in_inf_app_or (vec r' D) T2 (a , A)) ; [ apply Permutation_Type_in_inf with ((a, A) :: vec s A ++ vec r B ++ T1); [ Permutation_Type_solve | left; reflexivity ] | | auto ].
      intros H; clear - H Hneq2.
      exfalso.
      induction r'; simpl in H; inversion H.
      - inversion H0.
        apply Hneq2; symmetry; apply H3.
      - apply IHr'; apply X. }
    subst.
    destruct (IHs r' r T1 (D1 ++ D2) A B C D Hneq1 Hneq2 Hneq3 Hneq4) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , A); Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
  - intros s r' r T1 T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4 Hperm.
    simpl in *.
    destruct (in_inf_split (a , C) T1) as [[T1' T2'] Heq].
    { case (in_inf_app_or (vec s A) (vec r B ++ T1) (a , C)) ; [ apply Permutation_Type_in_inf with ((a, C) :: vec s' C ++ vec r' D ++ T2); [ Permutation_Type_solve | left; reflexivity ] | | ].
      - intros H; clear - H Hneq1.
        exfalso.
        induction s; simpl in H; inversion H.
        + inversion H0.
          apply Hneq1; apply H3.
        + apply IHs; apply X.
      - intro H0 ;case (in_inf_app_or (vec r B) T1 (a , C)) ; [ apply H0 | | auto ].
        intros H; clear - H Hneq3.
        exfalso.
        induction r; simpl in H; inversion H.
        + inversion H0; subst; apply Hneq3; reflexivity.
        + apply IHr; apply X. }
    subst.
    destruct (IHs' s r' r (T1' ++ T2') T2 A B C D Hneq1 Hneq2 Hneq3 Hneq4) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , C); Permutation_Type_solve. }
    split with (T', D').
    repeat split; try Permutation_Type_solve.
Qed.
