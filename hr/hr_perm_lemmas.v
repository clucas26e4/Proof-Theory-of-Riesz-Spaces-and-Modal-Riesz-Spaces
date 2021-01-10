(** * Some useful tools to manipulate lists of lists instead of multisets of multisets (and so to deal with the exchange rules) *)
Require Import Rpos.
Require Import RL.hr.term.
Require Import RL.hr.hseq.

Require Import CMorphisms.
Require Import Bool.

Require Import Lra.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Definition Allperm := (Forall2_inf (Permutation_Type (A:=Rpos * term))).
    
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

Lemma perm_decomp_vec_ID_case : forall T D n r s t A,
    A <> HR_covar n ->
    A <> HR_var n ->
    Permutation_Type (vec s (HR_covar n) ++ vec t (HR_var n) ++ T) (vec r A ++ D) ->
    {' (Ta, Tb, Da, Db) : _ &
                          prod (Permutation_Type T (Ta ++ Tb))
                               ((Permutation_Type D (Da ++ Db)) *
                                (Permutation_Type (vec s (HR_covar n) ++ vec t (HR_var n)) Da) *
                                (Permutation_Type (vec r A) Ta) *
                                (Permutation_Type Tb Db)) }.
Proof.
  intros T D n r s t A Hnc Hnv Hperm.
  revert D r Hperm; induction s; [ induction t | ]; intros D r Hperm.
  - split with (vec r A , D, nil, D).
    repeat split; try assumption; try reflexivity.
  - simpl in *.
    assert (In_inf (a, HR_var n) D) as HinD.
    { destruct (in_inf_app_or (vec r A) D (a , HR_var n)).
      + apply Permutation_Type_in_inf with ((a, HR_var n) :: vec t (HR_var n) ++ T); try assumption.
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
    { apply Permutation_Type_cons_inv with (a, HR_var n).
      etransitivity; [ apply Hperm | ].
      Permutation_Type_solve. }
    split with (Ta, Tb, ((a, HR_var n):: Da), Db).
    repeat split; try assumption; try reflexivity; try Permutation_Type_solve.
  - simpl in *.
    assert (In_inf (a, HR_covar n) D) as HinD.
    { destruct (in_inf_app_or (vec r A) D (a , HR_covar n)).
      + apply Permutation_Type_in_inf with ((a, HR_covar n) :: vec s (HR_covar n) ++ vec t (HR_var n) ++ T); try assumption.
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
    { apply Permutation_Type_cons_inv with (a, HR_covar n).
      Permutation_Type_solve. }
    split with (Ta, Tb, ((a, HR_covar n):: Da), Db).
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
