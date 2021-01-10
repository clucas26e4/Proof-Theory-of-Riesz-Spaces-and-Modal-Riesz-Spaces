(** * Tools and lemma used to prove Lemma 4.26 and 4.43 more easily *)
Require Import Rpos.
Require Import riesz_logic_List_more.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** Basic operation concerning Option Rpos (the None constructor corresponds to 0) *)
Definition oadd_Rpos o1 o2 :=
  match o1, o2 with
  | None, o2 => o2
  | o1, None => o1
  | Some r1, Some r2 => Some (plus_pos r1 r2)
  end.

Definition mul_Rpos_oRpos r o :=
  match o with
  | None => None
  | Some r1 => Some (time_pos r r1)
  end.

(** Conversion from nat to Option Rpos *)
Definition nat_oRpos n :=
  match n with
  | 0 => None
  | S n => Some (INRpos n)
  end.

                         
(** The sum of the weights of the atoms of G, where each sequent is multiply by a scalar *)
Fixpoint sum_weight_with_coeff n G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , (Some r) :: L => ((projT1 r) * (sum_weight_seq_var n T - sum_weight_seq_covar n T)) + sum_weight_with_coeff n G L
  | T :: G , None :: L => sum_weight_with_coeff n G L
  end.  
Fixpoint sum_weight_with_coeff_one G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , (Some r) :: L => ((projT1 r) * (sum_weight_seq_one T - sum_weight_seq_coone T)) + sum_weight_with_coeff_one G L
  | T :: G , None :: L => sum_weight_with_coeff_one G L
  end.

Lemma sum_weight_with_coeff_all_0 : forall G L n,
    Forall_inf (fun x => x = None) L ->
    sum_weight_with_coeff n G L = 0.
Proof.
  intros G L; revert G; induction L; intros G n Hall; destruct G; try reflexivity.
  inversion Hall; subst.
  simpl.
  rewrite IHL; try assumption; reflexivity.
Qed.

Lemma sum_weight_with_coeff_one_all_0 : forall G L,
    Forall_inf (fun x => x = None) L ->
    sum_weight_with_coeff_one G L = 0.
Proof.
  intros G L; revert G; induction L; intros G Hall; destruct G; try reflexivity.
  inversion Hall; subst.
  simpl.
  rewrite IHL; try assumption; reflexivity.
Qed.

(** The hypersequent obtained by multiplying (or copying) every sequent by the corresponding element of L and then using the S rule until only one sequent remain *)
Fixpoint concat_with_coeff_mul G L :=
  match G, L with
  | _, nil => nil
  | nil, _ => nil
  | T :: G , (Some r) :: L => seq_mul r T ++ concat_with_coeff_mul G L
  | T :: G , None :: L => concat_with_coeff_mul G L
  end.

Fixpoint concat_with_coeff_copy G L :=
  match G, L with
  | _, nil => nil
  | nil, _ => nil
  | T :: G , n :: L => copy_seq n T ++ concat_with_coeff_copy G L
  end.

Lemma sum_weight_with_coeff_perm_r : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           ((forall n, sum_weight_with_coeff n G L = sum_weight_with_coeff n H L') *
            (sum_weight_with_coeff_one G L = sum_weight_with_coeff_one H L') *
            (Permutation_Type (concat_with_coeff_mul (only_diamond_hseq G) L) (concat_with_coeff_mul (only_diamond_hseq H) L')))}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    repeat split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    split with (o :: L').
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + destruct o; simpl; Permutation_Type_solve.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (o0 :: o :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct o; destruct o0; simpl; nra.
    + destruct o; destruct o0; simpl; nra.
    + destruct o; destruct o0; simpl; Permutation_Type_solve.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    destruct (IHHperm2 L') as [L2' [Hperm2' [[Hsum2 Hone2] Hperm2'']]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L2'.
    repeat split; [ Permutation_Type_solve | | | ].
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + Permutation_Type_solve.
Qed.

Lemma sum_weight_with_coeff_perm_l : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           ((forall n, sum_weight_with_coeff n G L = sum_weight_with_coeff n H L') *
            (sum_weight_with_coeff_one G L = sum_weight_with_coeff_one H L') *
            (Permutation_Type (concat_with_coeff_mul G L) (concat_with_coeff_mul H L')))}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm'[[Hsum Hone] Hpc]]].
    split with (s :: H).
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + simpl.
      destruct x; Permutation_Type_solve.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct y; destruct x; simpl; nra.
    + destruct y; destruct x; simpl; nra.
    + destruct x; destruct y; simpl; Permutation_Type_solve.
  - destruct (IHHperm1 G Hlen) as [H [Hperm'[[Hsum Hone] Hpc]]].
    destruct (IHHperm2 H) as [H2 [Hperm2'[[Hsum2 Hone2] Hpc2]]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split.
    + Permutation_Type_solve.
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + etransitivity ; [ apply Hpc | apply Hpc2].
Qed.

Lemma sum_weight_with_coeff_perm_r_int : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           ((forall n, sum_weight_with_coeff n G (map nat_oRpos L) = sum_weight_with_coeff n H (map nat_oRpos L')) *
            (sum_weight_with_coeff_one G (map nat_oRpos L) = sum_weight_with_coeff_one H (map nat_oRpos L')) *
            (Permutation_Type (concat_with_coeff_copy (only_diamond_hseq G) L) (concat_with_coeff_copy (only_diamond_hseq H) L')))}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    repeat split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    split with (n :: L').
    repeat split; auto.
    + intros n'; simpl;rewrite (Hsum n'); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + Permutation_Type_solve.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (n0 :: n :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n'; destruct n; destruct n0; simpl in *; nra.
    + destruct n; destruct n0; simpl; nra.
    + destruct n; destruct n0; simpl; Permutation_Type_solve.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    destruct (IHHperm2 L') as [L2' [Hperm2' [[Hsum2 Hone2] Hperm2'']]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L2'.
    repeat split; [ Permutation_Type_solve | | | ].
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + Permutation_Type_solve.
Qed.

Lemma sum_weight_with_coeff_perm_l_int : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           ((forall n, sum_weight_with_coeff n G (map nat_oRpos L) = sum_weight_with_coeff n H (map nat_oRpos L')) *
            (sum_weight_with_coeff_one G (map nat_oRpos L) = sum_weight_with_coeff_one H (map nat_oRpos L')) *
            (Permutation_Type (concat_with_coeff_copy G L) (concat_with_coeff_copy H L')))}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm'[[Hsum Hone] Hpc]]].
    split with (s :: H).
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + simpl.
      destruct x; Permutation_Type_solve.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct y; destruct x; simpl; nra.
    + destruct y; destruct x; simpl; nra.
    + destruct x; destruct y; simpl; Permutation_Type_solve.
  - destruct (IHHperm1 G Hlen) as [H [Hperm'[[Hsum Hone] Hpc]]].
    destruct (IHHperm2 H) as [H2 [Hperm2'[[Hsum2 Hone2] Hpc2]]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split.
    + Permutation_Type_solve.
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + etransitivity ; [ apply Hpc | apply Hpc2].
Qed.

Lemma concat_with_coeff_mul_only_diamond : forall G L,
    concat_with_coeff_mul (only_diamond_hseq G) L = only_diamond_seq (concat_with_coeff_mul G L).
Proof.
  induction G; intros L; destruct L; auto.
  destruct o; simpl; rewrite IHG; auto.
  rewrite only_diamond_seq_app.
  rewrite only_diamond_seq_mul; reflexivity.
Qed.

Lemma concat_with_coeff_mul_all_0 : forall G L,
    Forall_inf (fun x => x = None) L ->
    concat_with_coeff_mul G L = nil.
Proof.
  intros G L; revert G; induction L; intros G Ha0; destruct G; simpl; auto.
  inversion Ha0; subst.
  apply IHL; assumption.
Qed.

(* TODO MOVE to hseq *)
Lemma only_diamond_seq_decomp :
  forall T,
    {' (r , s, D) : _ & prod
                       (Permutation_Type
                          (only_diamond_seq T)
                          (vec s HMR_coone ++ vec r HMR_one ++ D))
                       (sum_vec r - sum_vec s = sum_weight_seq_one T - sum_weight_seq_coone T)}.
Proof.
  induction T; [split with (nil, nil, nil); split; try reflexivity; lra | ].
  destruct IHT as [[[r s] D] [Hperm Heq]]; try (destruct a; simpl in * ;lia).
  destruct a as [a A].
  destruct A;
    try (esplit with (r, s, D); split; assumption);
    try (simpl max_diamond_term in Hnd; exfalso; lia);
    [ split with (a :: r , s, D) | split with (r , a :: s, D) | split with (r, s, (a,A) :: D)];
    simpl; split; try Permutation_Type_solve; try lra.
Qed.

Lemma only_diamond_seq_decomp_no_diamond :
  forall T,
    max_diamond_seq T = 0%nat ->
    {' (r , s) : _ & prod
                       (Permutation_Type
                          (only_diamond_seq T)
                          (vec s HMR_coone ++ vec r HMR_one))
                       (sum_vec r - sum_vec s = sum_weight_seq_one T - sum_weight_seq_coone T)}.
Proof.
  induction T; intros Hnd; [split with (nil, nil); split; try reflexivity; lra | ].
  simpl in Hnd.
  destruct IHT as [[r s] [Hperm Heq]]; try (destruct a; simpl in * ;lia).
  destruct a as [a A].
  destruct A;
    try (esplit with (r, s); split; assumption);
    try (simpl max_diamond_term in Hnd; exfalso; lia);
    [ split with (a :: r , s) | split with (r , a :: s)];
    simpl; split; try Permutation_Type_solve; try lra.
Qed.

Lemma concat_with_coeff_mul_only_diamond_decomp :
  forall G L,
    {' (r , s, T) : _ & prod
                       (Permutation_Type
                          (only_diamond_seq (concat_with_coeff_mul G L))
                          (vec s HMR_coone ++ vec r HMR_one ++ T))
                       (sum_vec r - sum_vec s = sum_weight_with_coeff_one G L) }.
Proof.
  induction G; intros [ | o L]; simpl; try (split with ((nil, nil), nil); split; try reflexivity; lra).
  destruct (IHG L) as [[[r s] T] [Hperm Heq]]; try lia.
  destruct o; simpl; [ | split with (r ,s, T); split; auto ].
  destruct (only_diamond_seq_decomp a) as [[[ra sa] Ta] [Hperma Heqa]].
  split with ((mul_vec r0 ra) ++ r, (mul_vec r0 sa) ++ s, seq_mul r0 Ta ++ T).
  rewrite ?vec_app; rewrite ? sum_vec_app.
  rewrite only_diamond_seq_app.
  rewrite <- ? seq_mul_vec_mul_vec.
  rewrite ? sum_mul_vec.
  split; try nra.
  rewrite <- only_diamond_seq_mul.
  apply seq_mul_perm with _ _ r0 in Hperma.
  rewrite ? seq_mul_app in Hperma.
  Permutation_Type_solve.
Qed.

Lemma concat_with_coeff_mul_only_diamond_decomp_no_diamond :
  forall G L,
    max_diamond_hseq G = 0%nat ->
    {' (r , s) : _ & prod
                       (Permutation_Type
                          (only_diamond_seq (concat_with_coeff_mul G L))
                          (vec s HMR_coone ++ vec r HMR_one))
                       (sum_vec r - sum_vec s = sum_weight_with_coeff_one G L) }.
Proof.
  induction G; intros [ | o L] Hnd; simpl; try (split with (nil, nil); split; try reflexivity; lra).
  destruct (IHG L) as [[r s] [Hperm Heq]]; try (simpl in Hnd ; lia).
  destruct o; simpl; [ | split with (r ,s); split; auto ].
  destruct (only_diamond_seq_decomp_no_diamond a) as [[ra sa] [Hperma Heqa]]; try (simpl in Hnd ; lia).
  split with ((mul_vec r0 ra) ++ r, (mul_vec r0 sa) ++ s).
  rewrite ?vec_app; rewrite ? sum_vec_app.
  rewrite only_diamond_seq_app.
  rewrite <- ? seq_mul_vec_mul_vec.
  rewrite ? sum_mul_vec.
  split; try nra.
  rewrite <- only_diamond_seq_mul.
  apply seq_mul_perm with _ _ r0 in Hperma.
  rewrite ? seq_mul_app in Hperma.
  Permutation_Type_solve.
Qed.
  
Lemma concat_with_coeff_copy_only_diamond : forall G L,
    concat_with_coeff_copy (only_diamond_hseq G) L = only_diamond_seq (concat_with_coeff_copy G L).
Proof.
  induction G; intros L; destruct L; auto.
  simpl; rewrite IHG; auto.
  rewrite ? only_diamond_seq_app.
  rewrite only_diamond_seq_copy; reflexivity.
Qed.

Lemma concat_with_coeff_copy_all_0 : forall G L,
    Forall_inf (fun x => x = 0%nat) L ->
    concat_with_coeff_copy G L = nil.
Proof.
  intros G L; revert G; induction L; intros G Ha0; destruct G; simpl; auto.
  inversion Ha0; subst.
  apply IHL; assumption.
Qed.

(** point-wise operation on list of (Option Rpos) or nat *)
Fixpoint oadd_Rpos_list L1 L2 :=
  match L1,L2 with
  | nil, _ => nil
  | _, nil => nil
  | o1 :: L1 , o2 :: L2 => (oadd_Rpos o1 o2) :: (oadd_Rpos_list L1 L2)
  end.

Fixpoint add_nat_list L1 L2 :=
  match L1,L2 with
  | nil, _ => nil
  | _, nil => nil
  | n1 :: L1 , n2 :: L2 => ((n1 + n2)%nat) :: (add_nat_list L1 L2)
  end.

Lemma oadd_Rpos_list_length : forall L1 L2,
    length L1 = length L2 ->
    length (oadd_Rpos_list L1 L2) = (length L1).
Proof.
  induction L1; intros L2; try reflexivity.
  intros Heq.
  destruct L2; inversion Heq.
  specialize (IHL1 L2 H0).
  destruct a; destruct o; simpl; rewrite IHL1; reflexivity.
Qed.

Lemma add_nat_list_length : forall L1 L2,
    length L1 = length L2 ->
    length (add_nat_list L1 L2) = (length L1).
Proof.
  induction L1; intros L2; try reflexivity.
  intros Heq.
  destruct L2; inversion Heq.
  specialize (IHL1 L2 H0).
  simpl; rewrite IHL1; reflexivity.
Qed.

Lemma sum_weight_with_coeff_oadd_Rpos_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff n G (oadd_Rpos_list L1 L2) = sum_weight_with_coeff n G L1 + sum_weight_with_coeff n G L2.
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  destruct a; destruct o; try destruct r; try destruct r0; simpl; nra.
Qed.

Lemma sum_weight_with_coeff_omul_Rpos_list : forall n G L1 r,
    sum_weight_with_coeff n G (map (mul_Rpos_oRpos r) L1) = (projT1 r) * sum_weight_with_coeff n G L1.
Proof.
  intros n G L1; revert G; induction L1; intros G r ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G r).
  destruct a; try destruct r; try destruct r0; simpl in *; nra.
Qed.

Lemma sum_weight_with_coeff_add_nat_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff n G (map nat_oRpos (add_nat_list L1 L2)) = sum_weight_with_coeff n G (map nat_oRpos L1) + sum_weight_with_coeff n G (map nat_oRpos L2).
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl add_nat_list.
  destruct a; destruct n0; simpl map; simpl sum_weight_with_coeff; try nra.
  - change (match (a + 0)%nat with
             | 0%nat => 1
             | S _ => INR (a + 0) + 1
            end) with (INR (S a + 0)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    rewrite Nat.add_0_r; nra.
  - change (match (a + S n0)%nat with
             | 0%nat => 1
             | S _ => INR (a + S n0) + 1
            end) with (INR (S a + S n0)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (match n0 with
            | 0%nat => 1
            | S _ => INR n0 + 1
            end) with (INR (S n0)).
    rewrite plus_INR; nra.
Qed.

Lemma sum_weight_with_coeff_mul_nat_list : forall n G L1 n',
    sum_weight_with_coeff n G (map nat_oRpos (map (Nat.mul (S n')) L1)) = (INR (S n')) * sum_weight_with_coeff n G (map nat_oRpos L1).
Proof.
  intros n G L1; revert G; induction L1; intros G n' ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G n').
  destruct a; simpl map.
  - rewrite Nat.mul_0_r; apply IHL1.
  - simpl sum_weight_with_coeff.
    change (match (a + n' * S a)%nat with
           | 0%nat => 1
           | S _ => INR (a + n' * S a) + 1
            end) with (INR (S n' * S a)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (fun m : nat => (m + n' * m)%nat) with (Nat.mul (S n')).
    rewrite mult_INR; nra.
Qed.

Lemma sum_weight_with_coeff_one_oadd_Rpos_list : forall G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff_one G (oadd_Rpos_list L1 L2) = sum_weight_with_coeff_one G L1 + sum_weight_with_coeff_one G L2.
Proof.
  intros G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  destruct a; destruct o; try destruct r; try destruct r0; simpl; nra.
Qed.

Lemma sum_weight_with_coeff_one_omul_Rpos_list : forall G L1 r,
    sum_weight_with_coeff_one G (map (mul_Rpos_oRpos r) L1) = (projT1 r) * sum_weight_with_coeff_one G L1.
Proof.
  intros G L1; revert G; induction L1; intros G r ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G r).
  destruct a; try destruct r; try destruct r0; simpl in *; nra.
Qed.

Lemma sum_weight_with_coeff_one_add_nat_list : forall G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff_one G (map nat_oRpos (add_nat_list L1 L2)) = sum_weight_with_coeff_one G (map nat_oRpos L1) + sum_weight_with_coeff_one G (map nat_oRpos L2).
Proof.
  intros G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl add_nat_list.
  destruct a; destruct n; simpl; try nra.
  - change (match (a + 0)%nat with
             | 0%nat => 1
             | S _ => INR (a + 0) + 1
            end) with (INR (S a + 0)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    rewrite Nat.add_0_r; nra.
  - change (match (a + S n)%nat with
             | 0%nat => 1
             | S _ => INR (a + S n) + 1
            end) with (INR (S a + S n)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (match n with
            | 0%nat => 1
            | S _ => INR n + 1
            end) with (INR (S n)).
    rewrite plus_INR; nra.
Qed.

Lemma sum_weight_with_coeff_one_mul_nat_list : forall G L1 n',
    sum_weight_with_coeff_one G (map nat_oRpos (map (Nat.mul (S n')) L1)) = (INR (S n')) * sum_weight_with_coeff_one G (map nat_oRpos L1).
Proof.
  intros G L1; revert G; induction L1; intros G n' ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G n').
  destruct a; simpl.
  - rewrite Nat.mul_0_r; apply IHL1.
  - change (match (a + n' * S a)%nat with
           | 0%nat => 1
           | S _ => INR (a + n' * S a) + 1
            end) with (INR (S n' * S a)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (fun m : nat => (m + n' * m)%nat) with (Nat.mul (S n')).
    change (match n' with
            | 0%nat => 1
            | S _ => INR n' + 1
            end) with (INR (S n')).
    rewrite mult_INR; nra.
Qed.

Lemma concat_with_coeff_mul_omul_Rpos_list : forall G L1 r,
    concat_with_coeff_mul G (map (mul_Rpos_oRpos r) L1) = seq_mul r (concat_with_coeff_mul G L1).
Proof.
  induction G; intros L1 r; [ destruct L1; try destruct o; reflexivity | ].
  destruct L1 ; [ reflexivity | ].
  specialize (IHG L1 r).
  destruct o; simpl; rewrite IHG; try reflexivity.
  rewrite <- seq_mul_twice; rewrite seq_mul_app.
  reflexivity.
Qed.

Lemma concat_with_coeff_copy_add_nat_list_perm : forall G L1 L2,
    length L1 = length L2 ->
    Permutation_Type (concat_with_coeff_copy G (add_nat_list L1 L2)) (concat_with_coeff_copy G L1 ++ concat_with_coeff_copy G L2).
Proof.
  intros G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; inversion Hlen ; [ destruct G; simpl; apply Permutation_Type_nil_nil | ].
  destruct G ; [ apply Permutation_Type_nil_nil | ].
  simpl add_nat_list; simpl concat_with_coeff_copy.
  transitivity ((copy_seq a s ++ copy_seq n s) ++ (concat_with_coeff_copy G L1 ++ concat_with_coeff_copy G L2)) ; [ | Permutation_Type_solve].
  apply Permutation_Type_app ; [ | apply IHL1]; try assumption.
  rewrite copy_seq_plus; reflexivity.
Qed.

Lemma concat_with_coeff_copy_mul_nat_list : forall G L1 n,
    Permutation_Type (concat_with_coeff_copy G (map (Nat.mul n) L1)) (copy_seq n (concat_with_coeff_copy G L1)).
Proof.
  induction G; intros L1 n.
  - destruct L1; simpl; rewrite copy_seq_nil; apply Permutation_Type_nil_nil.
  - destruct L1; simpl ; [ rewrite copy_seq_nil; apply Permutation_Type_nil_nil | ].
    etransitivity ; [ | symmetry; apply copy_seq_app].
    apply Permutation_Type_app ; [ | apply IHG].
    rewrite copy_seq_twice; reflexivity.
Qed.

(** Sufficient conditions for derivability of a basic hypersequent *)
Lemma basic_proof_all_eq P : forall H T,
    seq_is_basic T ->
    hseq_is_basic H -> 
    (forall n, sum_weight_var n (T :: H) = sum_weight_covar n (T :: H)) ->
    (sum_weight_coone (T :: H) <= sum_weight_one (T :: H)) ->
    HMR P ((flat_map only_diamond_seq (T :: H)) :: nil) ->
    HMR P (T :: H).
Proof.
  induction H; intros T.
  - intros Hb _; revert Hb.
    remember (length T).
    revert T Heqn.
    apply (lt_wf_rect n (fun n => forall T : sequent,
                             n = length T ->
                             seq_is_basic T ->
                             (forall n0 : nat, sum_weight_var n0 (T :: nil) = sum_weight_covar n0 (T :: nil)) ->
                             sum_weight_coone (T :: nil) <= sum_weight_one (T :: nil) ->
                             HMR P (flat_map only_diamond_seq (T :: nil) :: nil) ->
                             HMR P (T :: nil))).
    clear n.
    intros n IHn T Hlen Hat Hsum Hone Hstep.
    destruct (seq_basic_decomp_decr T Hat) as [[[[[n0 r] s] D] [Hr [[Hs Hperm] Hdlen]]] | Hnil].
    + eapply hmrr_ex_seq ; [ symmetry; apply Hperm | ].
      apply hmrr_ID.
      { rewrite Hr; rewrite Hs.
        specialize (Hsum n0); simpl in Hsum.
        nra. }
      apply IHn with (length D).
      * lia.
      * reflexivity.
      * apply seq_basic_perm with _ (vec s (HMR_covar n0) ++ vec r (HMR_var n0) ++ D) in Hat; try assumption.
        apply seq_basic_app_inv_r in Hat.
        apply seq_basic_app_inv_r in Hat.
        apply Hat.
      * intros n1.
        specialize (Hsum n0) as Hrs.
        specialize (Hsum n1).
        simpl in Hsum; rewrite (sum_weight_seq_var_perm _ _ _ Hperm) in Hsum; rewrite (sum_weight_seq_covar_perm _ _ _ Hperm) in Hsum.
        rewrite ? sum_weight_seq_var_app in Hsum; rewrite ? sum_weight_seq_covar_app in Hsum.
        simpl.
        rewrite (sum_weight_seq_covar_vec_neq _ (HMR_var n0)) in Hsum; [ | now auto].
        rewrite (sum_weight_seq_var_vec_neq _ (HMR_covar n0)) in Hsum; [ | now auto].
        case_eq (n0 =? n1); intros H01.
        -- apply Nat.eqb_eq in H01; subst.
           rewrite sum_weight_seq_covar_vec_covar_eq in Hsum; rewrite sum_weight_seq_var_vec_var_eq in Hsum.
           simpl in Hrs.
           nra.
        -- apply Nat.eqb_neq in H01.
           rewrite sum_weight_seq_covar_vec_neq in Hsum; [ | intros H'; inversion H'; now auto].
           rewrite sum_weight_seq_var_vec_neq in Hsum; [ | intros H'; inversion H'; now auto].
           nra.
      * simpl in Hone; rewrite (sum_weight_seq_one_perm _ _ Hperm) in Hone; rewrite (sum_weight_seq_coone_perm _ _ Hperm) in Hone.
        rewrite ? sum_weight_seq_one_app in Hone; rewrite ? sum_weight_seq_coone_app in Hone.
        simpl.
        rewrite ? sum_weight_seq_coone_vec_neq in Hone; try now auto.
        rewrite ? sum_weight_seq_one_vec_neq in Hone; try now auto.
        nra.
      * simpl; simpl in Hstep.
        eapply hmrr_ex_seq; [ | apply Hstep].
        rewrite 2 app_nil_r.
        replace (only_diamond_seq D) with (only_diamond_seq (vec s (HMR_covar n0) ++ vec r (HMR_var n0) ++ D)) by (rewrite ? only_diamond_seq_app; rewrite only_diamond_seq_vec_covar; now rewrite only_diamond_seq_vec_var).
        apply only_diamond_seq_perm; apply Hperm.
    + simpl in Hstep; rewrite app_nil_r in Hstep.
      destruct (seq_basic_no_atom T Hat Hnil) as [[[r s] D] Hperm].
      apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ seq_diamond D); [ apply Permutation_Type_sym; apply Hperm | ].
      apply hmrr_diamond.
      { simpl in Hone.
        rewrite (sum_weight_seq_coone_perm _ _ Hperm) in Hone; rewrite (sum_weight_seq_one_perm _ _ Hperm) in Hone.
        rewrite ? sum_weight_seq_coone_app in Hone; rewrite ? sum_weight_seq_one_app in Hone.
        rewrite sum_weight_seq_one_vec_one_eq in Hone; rewrite sum_weight_seq_coone_vec_coone_eq in Hone.
        rewrite sum_weight_seq_one_vec_neq in Hone; [ | now auto].
        rewrite sum_weight_seq_coone_vec_neq in Hone; [ | now auto].
        rewrite sum_weight_seq_one_seq_diamond in Hone; rewrite sum_weight_seq_coone_seq_diamond in Hone.
        nra. }
      replace (vec s HMR_coone ++ vec r HMR_one ++ D) with (only_diamond_seq (vec s HMR_coone ++ vec r HMR_one ++ seq_diamond D)) by (rewrite ? only_diamond_seq_app; rewrite only_diamond_seq_vec_coone; rewrite only_diamond_seq_vec_one; now rewrite only_diamond_seq_only_diamond).
      eapply hmrr_ex_seq ; [ | apply Hstep].
      apply only_diamond_seq_perm; apply Hperm.
  - intros HatT HatH Hsum Hone Hstep.
    apply hmrr_S.
    apply IHlist.
    + inversion HatH; subst.
      apply seq_basic_app; assumption.
    + inversion HatH; assumption.
    + intros n.
      specialize (Hsum n).
      simpl in *.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      nra.
    + simpl in *.
      rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app.
      nra.
    + simpl in *.
      rewrite only_diamond_seq_app; rewrite <- app_assoc.
      apply Hstep.
Qed.

(** ** sum_weight_(co)var_with_coeff and co(one) *)
Fixpoint sum_weight_var_with_coeff n G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , None :: L => sum_weight_var_with_coeff n G L
  | T :: G , (Some r) :: L => ((projT1 r) * sum_weight_seq_var n T) + sum_weight_var_with_coeff n G L
  end.

Lemma sum_weight_var_with_coeff_lt_max_var : forall n G L,
    (max_var_hseq G < n)%nat ->
    sum_weight_var_with_coeff n G L = 0.
Proof.
  intros n; induction G; intros L Hlt; destruct L; auto.
  simpl in *.
  rewrite sum_weight_seq_var_lt_max_var; try lia.
  rewrite IHG; try lia.
  destruct o;lra.
Qed.

Lemma sum_weight_var_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    sum_weight_var_with_coeff n (G1 ++ G2) L = sum_weight_var_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_var_with_coeff_app2 : forall n G1 G2 L1 L2,
    (length L1 = length G1) ->
    sum_weight_var_with_coeff n (G1 ++ G2) (L1 ++ L2) = sum_weight_var_with_coeff n G1 L1 + sum_weight_var_with_coeff n G2 L2.
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  destruct o ; lra.
Qed.

Lemma sum_weight_var_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_var_with_coeff n G (L1 ++ L2) = sum_weight_var_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint sum_weight_covar_with_coeff n G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , (Some r) :: L => ((projT1 r) * sum_weight_seq_covar n T) + sum_weight_covar_with_coeff n G L
  | T :: G , None :: L => sum_weight_covar_with_coeff n G L
  end.

Lemma sum_weight_covar_with_coeff_lt_max_var : forall n G L,
    (max_var_hseq G < n)%nat ->
    sum_weight_covar_with_coeff n G L = 0.
Proof.
  intros n; induction G; intros L Hlt; destruct L; auto.
  simpl in *.
  rewrite sum_weight_seq_covar_lt_max_var; try lia.
  rewrite IHG; try lia.
  destruct o; lra.
Qed.

Lemma sum_weight_covar_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    sum_weight_covar_with_coeff n (G1 ++ G2) L = sum_weight_covar_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_covar_with_coeff_app2 : forall n G1 G2 L1 L2,
    (length L1 = length G1) ->
    sum_weight_covar_with_coeff n (G1 ++ G2) (L1 ++ L2) = sum_weight_covar_with_coeff n G1 L1 + sum_weight_covar_with_coeff n G2 L2.
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  destruct o; lra.
Qed.

Lemma sum_weight_covar_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_covar_with_coeff n G (L1 ++ L2) = sum_weight_covar_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_with_coeff_eq_var_covar : forall n G L,
    sum_weight_with_coeff n G L = sum_weight_var_with_coeff n G L - sum_weight_covar_with_coeff n G L.
Proof.
  intros n; induction G; intros L; destruct L; simpl; try rewrite IHG; try destruct o; lra.
Qed.

Fixpoint sum_weight_one_with_coeff G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , None :: L => sum_weight_one_with_coeff G L
  | T :: G , (Some r) :: L => ((projT1 r) * sum_weight_seq_one T) + sum_weight_one_with_coeff G L
  end.

Lemma sum_weight_one_with_coeff_app1 : forall G1 G2 L,
    (length L <= length G1)%nat ->
    sum_weight_one_with_coeff (G1 ++ G2) L = sum_weight_one_with_coeff G1 L.
Proof.
  induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_one_with_coeff_app2 : forall G1 G2 L1 L2,
    (length L1 = length G1) ->
    sum_weight_one_with_coeff (G1 ++ G2) (L1 ++ L2) = sum_weight_one_with_coeff G1 L1 + sum_weight_one_with_coeff G2 L2.
Proof.
  induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  destruct o ; lra.
Qed.

Lemma sum_weight_one_with_coeff_app3 : forall G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_one_with_coeff G (L1 ++ L2) = sum_weight_one_with_coeff G L1.
Proof.
  induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint sum_weight_coone_with_coeff G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , (Some r) :: L => ((projT1 r) * sum_weight_seq_coone T) + sum_weight_coone_with_coeff G L
  | T :: G , None :: L => sum_weight_coone_with_coeff G L
  end.

Lemma sum_weight_coone_with_coeff_app1 : forall G1 G2 L,
    (length L <= length G1)%nat ->
    sum_weight_coone_with_coeff (G1 ++ G2) L = sum_weight_coone_with_coeff G1 L.
Proof.
  induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_coone_with_coeff_app2 : forall G1 G2 L1 L2,
    (length L1 = length G1) ->
    sum_weight_coone_with_coeff (G1 ++ G2) (L1 ++ L2) = sum_weight_coone_with_coeff G1 L1 + sum_weight_coone_with_coeff G2 L2.
Proof.
  induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  destruct o; lra.
Qed.

Lemma sum_weight_coone_with_coeff_app3 : forall G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_coone_with_coeff G (L1 ++ L2) = sum_weight_coone_with_coeff G L1.
Proof.
  induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_with_coeff_eq_one_coone : forall G L,
    sum_weight_with_coeff_one G L = sum_weight_one_with_coeff G L - sum_weight_coone_with_coeff G L.
Proof.
  induction G; intros L; destruct L; simpl; try rewrite IHG; try destruct o; lra.
Qed.
