(** * Implementation of Section 4.8 *)
Require Import Rpos.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import riesz_logic_List_more.
Require Import RL.hr.hr.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.p_hseq.
Require Import RL.hr.lambda_prop_tools.
Require Import RL.hr.invertibility.
Require Import RL.hr.can_elim.
Require Import RL.hr.M_elim.
Require Import RL.hr.tech_lemmas.

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

(** ** Decidablity *)
(* begin hide *)
(* Preliminary work necessary for the decidability result *)
Fixpoint pos_indexes (L : list R) :=
  match L with
  | nil => nil
  | r :: L => if (0 <? r) then 0%nat :: map S (pos_indexes L) else map S (pos_indexes L)
  end.

Lemma pos_indexes_nth : forall L i,
    In_inf i (pos_indexes L) ->
    0 < nth i L 0.
Proof.
  induction L; intros i Hin; simpl in Hin; try now exfalso.
  case_eq (0 <? a); intros H; rewrite H in Hin.
  - destruct i.
    + apply R_blt_lt in H; apply H.
    + simpl; apply IHL.
      apply In_inf_map_S_inv.
      inversion Hin; [ exfalso; inversion H0 | ].
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
  case_eq (0 <? a); intros _.
  - apply Forall_inf_cons.
    + lia.
    + apply Forall_inf_lt_map_S.
      apply IHL.
  - apply Forall_inf_lt_map_S; apply IHL.
Qed.

Lemma pos_indexes_not_In_inf : forall L i,
    (i < length L)%nat ->
    (In_inf i (pos_indexes L) -> False) ->
    (nth i L 0 <= 0).
Proof.
  induction L; intros i Hlen H; try now inversion Hlen.
  simpl in H.
  case_eq (0 <? a); intros Hlt; rewrite Hlt in H.
  - destruct i; [ exfalso; apply H; left; lia | ].
    simpl.
    apply IHL; [ simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    right.
    apply in_inf_map.
    apply Hin.
  - destruct i; [ simpl; apply R_blt_nlt in Hlt; lra | ].
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
  case_eq (0 <? a); intros H.
  - simpl in Hlen; rewrite H in Hlen.
    simpl in Hlen.
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
  - simpl in Hlen; rewrite H in Hlen.
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
        0 < nth i L 0) ->
    (forall i,
        (i < length L)% nat ->
        0 < nth i L 0 ->
        In_inf i v) ->
    v = pos_indexes L.
Proof.
  induction L; intros v H1 H2 H3 H4.
  - destruct v; auto.
    exfalso.
    assert (In_inf n (n :: v)) by (left; auto).
    specialize (H3 n X) .
    destruct n; auto; simpl in H3; lra.
  - case_eq (0 <? a); intros Hlt.
    + simpl.
      rewrite Hlt.
      destruct v.
      { exfalso.
        apply in_inf_nil with _ 0%nat.
        apply H4; simpl; try lia.
        apply R_blt_lt in Hlt.
        lra. }
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
            apply R_blt_lt in Hlt.
            lra. }
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
           change (nth i L 0) with (nth (S i) (a :: L) 0).
           apply H3.
           right; auto.
        -- intros i Hlti Hneq.
           change (nth i L 0) with (nth (S i) (a :: L) 0) in Hneq.
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
        apply R_blt_nlt in Hlt.
        lra.
      * simpl.
        rewrite e.
        rewrite (IHL x); auto.
        -- rewrite Hlt; auto.
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
           change (nth i L 0) with (nth (S i) (a :: L) 0).
           apply H3.
           auto.
        -- intros i Hlti Hneq.
           change (nth i L 0) with (nth (S i) (a :: L) 0) in Hneq.
           apply lt_n_S in Hlti.
           specialize (H4 (S i) Hlti Hneq).
           rewrite e in H4.
           apply In_inf_map_S_inv in H4.
           apply H4.
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
  rewrite sum_weight_p_seq_var_lt_max_var; try lia.
  rewrite IHG; try lia.
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
  rewrite sum_weight_p_seq_covar_lt_max_var; try lia.
  rewrite IHG; try lia.
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

Lemma FOL_R_term_sem_eval_p_sequent : forall val n T,
    FOL_R_term_sem val (sum_weight_p_seq_var n T) - FOL_R_term_sem val (sum_weight_p_seq_covar n T) = sum_weight_seq_var n (eval_p_sequent val T) - sum_weight_seq_covar n (eval_p_sequent val T) .
Proof.
  intros val n; induction T; simpl; try reflexivity.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl;
    destruct A; simpl; try case (n =? n0); simpl; try rewrite IHT; try lra.
Qed.

Lemma FOL_R_term_sem_eval_p_hseq : forall val n G L,
    FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) - FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L) = sum_weight_var_with_coeff n (map (eval_p_sequent val) G) (map (FOL_R_term_sem val) L) - sum_weight_covar_with_coeff n (map (eval_p_sequent val) G) (map (FOL_R_term_sem val) L).
Proof.
  intros val n; induction G; intros [ | r L]; simpl; try reflexivity.
  specialize (IHG L).
  transitivity
    (FOL_R_term_sem val r * (FOL_R_term_sem val (sum_weight_p_seq_var n a) - FOL_R_term_sem val (sum_weight_p_seq_covar n a)) +
     (FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) - FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L))); try lra.
  rewrite IHG; rewrite FOL_R_term_sem_eval_p_sequent.
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

Lemma eval_p_seq_upd_val_vec_lt : forall val T vx vr,
    Forall_inf (fun x => max_var_weight_p_seq T < x)%nat vx ->
    eval_p_sequent (upd_val_vec val vx vr) T = eval_p_sequent val T.
Proof.
  intros val; induction T; intros vx vr Hall; simpl; try reflexivity.
  destruct a as [a A].
  rewrite ? FOL_R_term_sem_upd_val_vec_lt ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  rewrite IHT ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  reflexivity.
Qed.
  
Lemma eval_p_hseq_upd_val_vec_lt : forall val G vx vr,
    Forall_inf (fun x => max_var_weight_p_hseq G < x)%nat vx ->
    map (eval_p_sequent (upd_val_vec val vx vr)) G = map (eval_p_sequent val) G.
Proof.
  intros val; induction G; intros vx vr Hall; simpl; try reflexivity.
  rewrite eval_p_seq_upd_val_vec_lt ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  rewrite IHG ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  reflexivity.
Qed.

Lemma sum_weight_with_coeff_eval_eq : forall val n G L,
    sum_weight_var_with_coeff n (map (eval_p_sequent val) G) L - sum_weight_covar_with_coeff n (map (eval_p_sequent val) G) L = FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) L) (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))) - FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) L) (p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))).
Proof.
  intros val n G L.
  rewrite FOL_R_term_sem_eval_p_hseq.
  rewrite map_val_seq_var.
  rewrite eval_p_hseq_upd_val_vec_lt; try reflexivity.
  apply forall_Forall_inf.
  intros x Hin.
  case_eq (max_var_weight_p_hseq G <? x)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H]; auto.
  exfalso.
  apply not_In_inf_seq with (S (max_var_weight_p_hseq G)) (length L) x; try lia.
  apply Hin.
Qed.

(* Put non basic formula first, i.e., G in the form H | |- T, r.A with A non basic. *)

Fixpoint p_seq_fst_non_atomic_term (T : p_sequent) : (FOL_R_term * term) :=
  match T with
  | nil => (FOL_R_cst 0, HR_var 0)
  | (a, A) :: T => if (0 <? HR_complexity_term A)%nat
                   then (a , A)
                   else (p_seq_fst_non_atomic_term T)
  end.

Lemma p_seq_fst_non_atomic_term_correct :
  forall T,
    (p_seq_is_atomic T -> False) ->
    (is_atom (snd (p_seq_fst_non_atomic_term T)) -> False).
Proof.
  induction T; intros Hnbs Hbt; [ apply Hnbs; apply Forall_inf_nil | ].
  destruct a as [a A]; simpl in *.
  case_eq (0 <? HR_complexity_term A)%nat; intros H1; rewrite H1 in Hbt;
    (apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1).
  - apply is_atom_complexity_0 in Hbt.
    simpl in Hbt.
    lia.
  - apply IHT; auto.
    intros H2.
    apply Hnbs.
    apply Forall_inf_cons; auto.
    apply is_atom_complexity_0_inv.
    lia.
Qed.

Lemma p_seq_fst_non_atomic_term_well_defined :
  forall val T,
    (0 < HR_complexity_p_seq T)%nat ->
    p_seq_well_defined val T ->
    (0 <? FOL_R_term_sem val (fst (p_seq_fst_non_atomic_term T))) = true.
Proof.
  intros val; induction T; intros Hlt; [ simpl in Hlt; exfalso; try lia | ].
  intros Hwd.
  destruct a as [a A].
  simpl.
  case_eq (0 <? HR_complexity_term A)%nat; intros H; auto; inversion Hwd; subst; auto.
  apply IHT; auto.
  apply Nat.ltb_nlt in H.
  simpl in *.
  lia.
Qed.  

Fixpoint p_seq_without_fst_non_atomic_term (T : p_sequent) : p_sequent :=
  match T with
  | nil => nil
  | (a, A) :: T => if (0 <? HR_complexity_term A)%nat
                   then T
                   else (a , A) :: (p_seq_without_fst_non_atomic_term T)
  end.

Lemma p_seq_put_non_atomic_fst : forall T,
    (p_seq_is_atomic T -> False) ->
    Permutation_Type T (p_seq_fst_non_atomic_term T :: p_seq_without_fst_non_atomic_term T).
Proof.
  induction T; intros Hnb; [ exfalso; apply Hnb; apply Forall_inf_nil | ].
  destruct a as [a A]; simpl.
  case_eq (0 <? HR_complexity_term A)%nat; intros H1;
    apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1; auto.
  assert (p_seq_is_atomic T -> False).
  { intros H; apply Hnb; apply Forall_inf_cons; auto.
    apply is_atom_complexity_0_inv.
    lia. }
  specialize (IHT H).
  transitivity ((a , A) :: p_seq_fst_non_atomic_term T :: p_seq_without_fst_non_atomic_term T);
    Permutation_Type_solve.
Qed.

Lemma p_seq_without_fst_non_atomic_term_well_defined :
  forall val T,
    p_seq_well_defined val T ->
    p_seq_well_defined val (p_seq_without_fst_non_atomic_term T).
Proof.
  intros val; induction T; intros Hwd; [apply Forall_inf_nil |].
  destruct a as [a A]; inversion Hwd; subst.
  simpl.
  case_eq (0 <? HR_complexity_term A)%nat; intros H; try apply Forall_inf_cons; try apply IHT; auto.
Qed.

Fixpoint p_hseq_p_seq_max_complexity (G : p_hypersequent) : p_sequent :=
  match G with
  | nil => nil
  | T :: G => if (fst (HR_complexity_p_hseq G) <=? HR_complexity_p_seq T)
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
  simpl; case (fst (HR_complexity_p_hseq G) <=? HR_complexity_p_seq a); auto.
Qed.

Lemma p_hseq_p_seq_max_complexity_correct :
  forall G,
    HR_complexity_p_seq (p_hseq_p_seq_max_complexity G) = fst (HR_complexity_p_hseq G).
Proof.
  induction G; auto.
  simpl.
  case_eq (fst (HR_complexity_p_hseq G) <=? HR_complexity_p_seq a); intros H1;
    case_eq (HR_complexity_p_seq a =? fst (HR_complexity_p_hseq G)); intros H2;
      case_eq (HR_complexity_p_seq a <? fst (HR_complexity_p_hseq G))%nat; intros H3;
        simpl;
        apply Nat.leb_le in H1 + apply Nat.leb_nle in H1;
        apply Nat.eqb_eq in H2 + apply Nat.eqb_neq in H2;
        apply Nat.ltb_lt in H3 + apply Nat.ltb_nlt in H3;
        try lia.
Qed.

Fixpoint p_hseq_without_max_complexity (G : p_hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => if (fst (HR_complexity_p_hseq G) <=? HR_complexity_p_seq T)
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
  simpl; case (fst (HR_complexity_p_hseq G) <=? HR_complexity_p_seq a); try apply Forall_inf_cons; auto.
Qed.

Lemma p_hseq_put_max_complexity_fst : forall G,
    G <> nil ->
    Permutation_Type G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G).
Proof.
  induction G; intros Hnnil; [ exfalso; auto | ].
  simpl.
  case_eq (fst (HR_complexity_p_hseq G) <=? HR_complexity_p_seq a); intros H1;
    apply Nat.leb_le in H1 + apply Nat.leb_nle in H1; auto.
  destruct G.
  { exfalso; simpl in H1; lia. }
  assert (p :: G <> nil) as Hnnil'.
  { intros H; inversion H. }
  specialize (IHG Hnnil').
  transitivity (a :: p_hseq_p_seq_max_complexity (p :: G) :: p_hseq_without_max_complexity (p :: G)); Permutation_Type_solve.
Qed.

Definition p_hseq_put_non_atomic_fst G :=
  ((p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)) :: p_hseq_without_max_complexity G).

Lemma p_hseq_put_non_atomic_fst_HR_complexity :
  forall G,
    (p_hseq_is_atomic G -> False) ->
    HR_complexity_p_hseq (p_hseq_put_non_atomic_fst G) = HR_complexity_p_hseq G.
Proof.
  intros G Hnb.
  unfold p_hseq_put_non_atomic_fst.
  rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
  2:{ symmetry; apply p_seq_put_non_atomic_fst.
      intros H.
      apply Hnb.
      apply p_hseq_is_atomic_complexity_0_inv.
      rewrite <- p_hseq_p_seq_max_complexity_correct.
      apply p_seq_is_atomic_complexity_0.
      apply H. }
  rewrite complexity_p_hseq_perm with _ G; auto.
  symmetry; apply p_hseq_put_max_complexity_fst.
  intros H; apply Hnb; rewrite H.
  apply Forall_inf_nil.
Qed.

Lemma p_hseq_put_non_atomic_fst_correct :
  forall G a A T H,
    (p_hseq_is_atomic G -> False) ->
    p_hseq_put_non_atomic_fst G = ((a, A) :: T) :: H ->
    is_atom A -> False.
Proof.
  intros G a A T H Hnb Heq Hb.
  unfold p_hseq_put_non_atomic_fst in Heq.
  inversion Heq; subst.
  apply p_seq_fst_non_atomic_term_correct with (p_hseq_p_seq_max_complexity G).
  - intros Hb'.
    apply Hnb.
    apply p_hseq_is_atomic_complexity_0_inv.
    apply p_seq_is_atomic_complexity_0 in Hb'.
    rewrite p_hseq_p_seq_max_complexity_correct in Hb'.
    apply Hb'.
  - rewrite H1.
    apply Hb.
Qed.

Lemma p_hseq_put_non_atomic_fst_well_defined :
  forall val G,
    (0 < fst (HR_complexity_p_hseq G))%nat ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val (p_hseq_put_non_atomic_fst G).
Proof.
  intros val G Hn0 Hwd.
  apply Forall_inf_cons; (destruct G; [ exfalso; simpl in *; lia | ]).
  - apply Forall_inf_cons.
    + apply p_seq_fst_non_atomic_term_well_defined; [ | apply p_hseq_p_seq_max_complexity_well_defined; auto].
      rewrite p_hseq_p_seq_max_complexity_correct.
      apply Hn0.
    + apply p_seq_without_fst_non_atomic_term_well_defined.
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
                               | HR_zero => inl (T :: G)
                               |  _ => inl (((a, A) :: T) :: G)
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

Lemma apply_logical_rule_on_p_hypersequent_inl_HR :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    HR_T_M (map (eval_p_sequent val) G) ->
    HR_T_M (map (eval_p_sequent val) G1).
Proof.
  intros val G G1 Heq Hwd pi.
  destruct G; [ exfalso; apply (HR_not_empty _ nil pi); auto | ].
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
    apply hrr_Z_inv with ((existT _ (FOL_R_term_sem val a) e) :: nil).
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
    apply hrr_plus_inv.
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
    apply hrr_mul_inv.
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
    apply hrr_max_inv.
    apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inl_HR_inv :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    HR_T_M (map (eval_p_sequent val) G1) ->
    HR_T_M (map (eval_p_sequent val) G).
Proof.
  intros val G G1 Heq Hwd pi.
  destruct G; [ exfalso; apply (HR_not_empty _ _ pi); inversion Heq; auto | ].
  destruct l; [ inversion Heq; subst; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); apply R_blt_lt in H2; simpl in *; lra).
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val a) e)); intros pi.
    change ((r, HR_zero) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) HR_zero ++ eval_p_sequent val l).
    apply hrr_Z.
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
    apply hrr_plus.
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
    apply hrr_mul.
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
    apply hrr_max.
    apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_l_HR :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HR_T_M (map (eval_p_sequent val) G) ->
    HR_T_M (map (eval_p_sequent val) G1).
Proof.
  intros val G G1 G2 Heq Hwd pi.
  destruct G; [ exfalso; apply (HR_not_empty _ nil pi); auto | ].
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
  apply hrr_min_inv_l with A2.
  apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_r_HR :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HR_T_M (map (eval_p_sequent val) G) ->
    HR_T_M (map (eval_p_sequent val) G2).
Proof.
  intros val G G1 G2 Heq Hwd pi.
  destruct G; [ exfalso; apply (HR_not_empty _ nil pi); auto | ].
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
  apply hrr_min_inv_r with A1.
  apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_HR_inv :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HR_T_M (map (eval_p_sequent val) G1) ->
    HR_T_M (map (eval_p_sequent val) G2) ->
    HR_T_M (map (eval_p_sequent val) G).
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
  apply hrr_min; auto.
Qed.
    
Lemma apply_logical_rule_on_p_hypersequent_correct_inl :
  forall G G1 n,
    (fst (HR_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inl G1 ->
    HR_complexity_p_hseq G1 <2 HR_complexity_p_hseq G.
Proof.
  intros G G1 n H1 H2.
  remember (p_hseq_put_non_atomic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_atomic_fst_HR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_atomic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_atom A -> False).
  { apply p_hseq_put_non_atomic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_atomic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  - rewrite <- (p_hseq_put_non_atomic_fst_HR_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, HR_zero) :: l) with (vec (a :: nil) HR_zero ++ l).
    apply hrr_Z_decrease_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_atomic_fst in *.
    rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
    2:{ symmetry; apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_atomic_fst_HR_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, A1 +S A2) :: l) with (vec (a :: nil) (A1 +S A2) ++ l).
    change ((a, A1) :: (a, A2) :: l) with (vec (a :: nil) A1 ++ vec (a :: nil) A2 ++ l).
    apply hrr_plus_decrease_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_atomic_fst in *.
    rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
    2:{ symmetry; apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_atomic_fst_HR_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, r *S A) :: l) with (vec (a :: nil) (r *S A) ++ l).
    change ((FOL_R_cst (projT1 r) *R a, A) :: l) with (vec (mul_vec (FOL_R_cst (projT1 r)) (a :: nil)) A ++ l).
    apply hrr_mul_decrease_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_atomic_fst in *.
    rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
    2:{ symmetry; apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_atomic_fst_HR_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, A1 \/S A2) :: l) with (vec (a :: nil) (A1 \/S A2) ++ l).
    change ((a, A1) :: l) with (vec (a :: nil) A1 ++ l).
    change ((a, A2) :: l) with (vec (a :: nil) A2 ++ l).
    apply hrr_max_decrease_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_atomic_fst in *.
    rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
    2:{ symmetry; apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_atomic_fst.
        intros Hb.
        apply p_seq_is_atomic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_correct_inr_l :
  forall G G1 G2 n,
    fst (HR_complexity_p_hseq G) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inr (G1 , G2) ->
    HR_complexity_p_hseq G1 <2 HR_complexity_p_hseq G.
Proof.
  intros G G1 G2 n H1 H2.
  remember (p_hseq_put_non_atomic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_atomic_fst_HR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_atomic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_atom A -> False).
  { apply p_hseq_put_non_atomic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_atomic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  rewrite <- (p_hseq_put_non_atomic_fst_HR_complexity G).
  2:{ intros Hnb.
      apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
  rewrite <- HeqH.
  change ((a, A1 /\S A2) :: l) with (vec (a :: nil) (A1 /\S A2) ++ l).
  change ((a, A1) :: l) with (vec (a :: nil) A1 ++ l).
  apply hrr_min_r_decrease_complexity ; [ intros H'; inversion H' | ].
  simpl vec; simpl app.
  rewrite HeqH.
  unfold p_hseq_put_non_atomic_fst in *.
  rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
  2:{ symmetry; apply p_seq_put_non_atomic_fst.
      intros Hb.
      apply p_seq_is_atomic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  rewrite complexity_p_hseq_perm with _ G.
  2:{ symmetry; apply p_hseq_put_max_complexity_fst.
      intros Heq; rewrite Heq in H1; inversion H1. }
  rewrite <-p_hseq_p_seq_max_complexity_correct.
  rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_atomic_fst.
      intros Hb.
      apply p_seq_is_atomic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  inversion HeqH; subst; reflexivity.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_correct_inr_r :
  forall G G1 G2 n,
    fst (HR_complexity_p_hseq G) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inr (G1 , G2) ->
    HR_complexity_p_hseq G2 <2 HR_complexity_p_hseq G.
Proof.
  intros G G1 G2 n H1 H2.
  remember (p_hseq_put_non_atomic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_atomic_fst_HR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_atomic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_atom A -> False).
  { apply p_hseq_put_non_atomic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_atomic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  rewrite <- (p_hseq_put_non_atomic_fst_HR_complexity G).
  2:{ intros Hnb.
      apply p_hseq_is_atomic_complexity_0 in Hnb; lia. }
  rewrite <- HeqH.
  change ((a, A1 /\S A2) :: l) with (vec (a :: nil) (A1 /\S A2) ++ l).
  change ((a, A2) :: l) with (vec (a :: nil) A2 ++ l).
  apply hrr_min_l_decrease_complexity ; [ intros H'; inversion H' | ].
  simpl vec; simpl app.
  rewrite HeqH.
  unfold p_hseq_put_non_atomic_fst in *.
  rewrite complexity_p_hseq_perm_fst_p_seq with _ (p_hseq_p_seq_max_complexity G) _.
  2:{ symmetry; apply p_seq_put_non_atomic_fst.
      intros Hb.
      apply p_seq_is_atomic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  rewrite complexity_p_hseq_perm with _ G.
  2:{ symmetry; apply p_hseq_put_max_complexity_fst.
      intros Heq; rewrite Heq in H1; inversion H1. }
  rewrite <-p_hseq_p_seq_max_complexity_correct.
  rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_atomic_fst.
      intros Hb.
      apply p_seq_is_atomic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  inversion HeqH; subst; reflexivity.
Qed.

(* end hide *)
(** return the conjunction /\(beta_{k + i} = 0) for all i \in v *)
Fixpoint FOL_R_all_zero k (v : list nat) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and
                (FOL_R_atoms (FOL_R_var (k + n) =R (FOL_R_cst 0)))
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
  | n :: v => FOL_R_and
                (FOL_R_and
                   (FOL_R_atoms ((FOL_R_var (k + n)) <>R (FOL_R_cst 0)))
                   (FOL_R_atoms ((FOL_R_cst 0) <=R (FOL_R_var (k + n)))))
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
Fixpoint FOL_R_all_atoms_eq G k:=
  match k with
  | 0%nat => FOL_R_atoms ((p_sum_weight_var_with_coeff 0%nat G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) =R (p_sum_weight_covar_with_coeff 0%nat G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))))
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

(** return the formula corresponding to \phi_{G,v} *)
Definition FOL_R_phi G v := FOL_R_and
                              (FOL_R_all_zero (S (max_var_weight_p_hseq G)) (complementary v (length G)))
                              (FOL_R_and
                                 (FOL_R_all_gtz (S (max_var_weight_p_hseq G)) v)
                                 (FOL_R_all_atoms_eq G (max_var_p_hseq G))).

(** return the formula corresponding to \exists \beta_1,....,\beta_n \phi_{G,v} *)
Definition FOL_R_exists_phi G v :=
  exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v).

Lemma cond_FOL_R_exists_phi_formula_sem : forall G v val,
    { vr & prod (length vr = length G) (FOL_R_formula_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_phi G v)) } ->
    FOL_R_formula_sem val (FOL_R_exists_phi G v).
Proof.
  intros G v val [vr [Hlen Hf]].
  apply cond_FOL_R_exists_vec_formula_sem.
  split with vr.
  split; auto.
  rewrite seq_length.
  rewrite Hlen; reflexivity.
Qed.  
    
Lemma cond_FOL_R_exists_phi_formula_sem_inv : forall G v val,
    FOL_R_formula_sem val (FOL_R_exists_phi G v) ->
    { vr & prod (length vr = length G) (FOL_R_formula_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_phi G v)) }.
Proof.
  intros G v val Hf.
  apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [vr [Hlen Hf]].
  split with vr.
  split; auto.
  rewrite seq_length in Hlen; rewrite Hlen; reflexivity.
Qed.

(** return the whole formula for the atomic case *)
Fixpoint FOL_R_atomic_case_aux G V :=
  match V with
  | nil => FOL_R_false
  | v :: V => FOL_R_or (FOL_R_exists_phi G v) (FOL_R_atomic_case_aux G V)
  end.

Lemma cond_FOL_R_atomic_case_aux_formula_sem : forall G V val,
    { v : _ & In_inf v V & FOL_R_formula_sem val (FOL_R_exists_phi G v)} ->
    FOL_R_formula_sem val (FOL_R_atomic_case_aux G V).
Proof.
  intros G; induction V; intros val [v Hin Hf]; inversion Hin; subst.
  - left.
    apply Hf.
  - right.
    apply IHV.
    split with v; assumption.
Qed.

Lemma cond_FOL_R_atomic_case_aux_formula_sem_inv : forall G V val,
    FOL_R_formula_sem val (FOL_R_atomic_case_aux G V) ->
    { v : _ & In_inf v V & FOL_R_formula_sem val (FOL_R_exists_phi G v)}.
Proof.
  intros G V; induction V; intros val Hf; inversion Hf.
  - split with a; auto.
    apply in_inf_eq.
  - destruct (IHV val X) as [v Hin Hf'].
    split with v; try assumption.
    now apply in_inf_cons.
Qed.

Definition FOL_R_atomic_case G  :=
  FOL_R_atomic_case_aux G (map (@rev nat) (make_subsets (length G))).


(* auxiliary functions used to help Coq understands they terminate *)
Fixpoint HR_dec_formula_aux (G : p_hypersequent) (x: nat) (Heqx : fst (HR_complexity_p_hseq G) = x) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p) (acc : Acc lt_nat2 (HR_complexity_p_hseq G)) : FOL_R_formula.
  - destruct acc as [acc].
    destruct x.
    + apply (FOL_R_atomic_case G).
    + destruct p.
      * refine (HR_dec_formula_aux p
                                _
                                eq_refl
                                _
                                eq_refl
                                (acc _
                                     (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp))).
      * destruct p.
        refine (FOL_R_and
                  (HR_dec_formula_aux p
                                   _
                                   (eq_refl _)
                                   _
                                   (eq_refl _)
                                   (acc _
                                        (apply_logical_rule_on_p_hypersequent_correct_inr_l G p p0 x Heqx Heqp)))
                  (HR_dec_formula_aux p0
                                    _
                                   eq_refl
                                   _
                                   eq_refl
                                   (acc _
                                        (apply_logical_rule_on_p_hypersequent_correct_inr_r G p p0 x Heqx Heqp)))).
Defined.    

Fixpoint HR_dec_formula_aux_sem_indep_acc val (G : p_hypersequent) (x: nat) (Heqx : fst (HR_complexity_p_hseq G) = x) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p) (acc1 acc2 : Acc lt_nat2 (HR_complexity_p_hseq G)) :
         FOL_R_formula_sem val (HR_dec_formula_aux G x Heqx p Heqp acc1) ->
         FOL_R_formula_sem val (HR_dec_formula_aux G x Heqx p Heqp acc2).
Proof.
  - destruct acc1 as [acc1]; destruct acc2 as [acc2]; intros Hf.
    destruct x; auto.
    destruct p.
    + refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf).
    + destruct p.
      destruct Hf as [Hf1 Hf2].
      split.
      * refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf1).
      * refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ (acc1 _ _) (acc2 _ _) Hf2).
Qed.

Lemma HR_dec_formula_aux_sem_indep_n : forall val G (n: nat) (Heqn : fst (HR_complexity_p_hseq G) = n) m (Heqm : fst (HR_complexity_p_hseq G) = m) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p) acc,
    FOL_R_formula_sem val (HR_dec_formula_aux G n Heqn p Heqp acc) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G m Heqm p Heqp acc).
Proof.
  intros val G.
  assert ({x & x = HR_complexity_p_hseq G}) as [x Heqx] by (split with (HR_complexity_p_hseq G); reflexivity).
  revert G Heqx.
  apply (lt_nat2_wf_rect x); clear x.
  intros x H G Heqx [ | n] Heqn [ | m] Heqm [G1 | [G1 G2]] Heqp [acc] Hf;
    try destruct Hf as [Hf1 Hf2]; try (exfalso; lia).
  - apply Hf.
  - apply Hf.
  - unfold HR_dec_formula_aux in *; fold HR_dec_formula_aux in *.
    refine (H (HR_complexity_p_hseq G1) _ G1 eq_refl _ eq_refl _ eq_refl _ eq_refl _ _).
    { rewrite Heqx.
      apply apply_logical_rule_on_p_hypersequent_correct_inl with n; auto. }
    refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
  - split.
    + unfold HR_dec_formula_aux in *; fold HR_dec_formula_aux in *.
      refine (H (HR_complexity_p_hseq G1) _ G1 eq_refl _ eq_refl _ eq_refl _ eq_refl _ _).
      { rewrite Heqx.
        apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 n; auto. }
      refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1).
    + unfold HR_dec_formula_aux in *; fold HR_dec_formula_aux in *.
      refine (H (HR_complexity_p_hseq G2) _ G2 eq_refl _ eq_refl _ eq_refl _ eq_refl _ _).
      { rewrite Heqx.
        apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 n; auto. }
      refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
Qed.

Lemma HR_dec_formula_aux_sem_indep_Heqp : forall val G (n: nat) (Heqn : fst (HR_complexity_p_hseq G) = n) p (Heqp1 Heqp2 : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p) acc,
    FOL_R_formula_sem val (HR_dec_formula_aux G n Heqn p Heqp1 acc) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G n Heqn p Heqp2 acc).
Proof.
  intros val G [ | n] Heqn [G1 | [G1 G2]] Heqp1 Heqp2 [acc] Hf;
    try destruct Hf as [Hf1 Hf2]; try (exfalso; lia).
  - apply Hf.
  - apply Hf.
  - unfold HR_dec_formula_aux in *; fold HR_dec_formula_aux in *.
    apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
  - split.
    + unfold HR_dec_formula_aux in *; fold HR_dec_formula_aux in *.
      apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1).
    + unfold HR_dec_formula_aux in *; fold HR_dec_formula_aux in *.
      apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2).
Qed.

Lemma HR_dec_formula_aux_sem_indep_p : forall val G (n: nat) (Heqn : fst (HR_complexity_p_hseq G) = n) p1 (Heqp1 : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p1) p2 (Heqp2 : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p2) acc,
    FOL_R_formula_sem val (HR_dec_formula_aux G n Heqn p1 Heqp1 acc) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G n Heqn p2 Heqp2 acc).
Proof.
  intros val G [ | n] Heqn [G1 | [G1 G2]] Heqp1 [G'1 | [G'1 G'2]] Heqp2 [acc] Hf;
    try destruct Hf as [Hf1 Hf2]; try (exfalso; rewrite Heqp1 in Heqp2; now inversion Heqp2).
  - apply Hf.
  - apply Hf.
  - assert (G1 = G'1) as H.
    { clear - Heqp1 Heqp2; rewrite Heqp1 in Heqp2; now inversion Heqp2. }
    subst.
    apply (HR_dec_formula_aux_sem_indep_Heqp _ _ _ _ _ _ _ _ Hf).
  - assert (G1 = G'1) as H1.
    { clear - Heqp1 Heqp2; rewrite Heqp1 in Heqp2; now inversion Heqp2. }
    assert (G2 = G'2) as H2.
    { clear - Heqp1 Heqp2; rewrite Heqp1 in Heqp2; now inversion Heqp2. }
    subst.
    split.
    + apply (HR_dec_formula_aux_sem_indep_Heqp _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1)).
    + apply (HR_dec_formula_aux_sem_indep_Heqp _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2)).
Qed.

Lemma cond_HR_dec_formula_aux_atomic :
  forall val G (Heqx : fst (HR_complexity_p_hseq G) = 0%nat) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p) acc,
    FOL_R_formula_sem val (FOL_R_atomic_case G) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G 0%nat Heqx p Heqp acc).
Proof.
  intros val G Heqx p Heqp acc Hf.
  destruct acc as [acc].
  simpl.
  apply Hf.
Qed.

Lemma cond_HR_dec_formula_aux_inl :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inl G1) acc1 acc2,
    FOL_R_formula_sem val (HR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G _ Heqx _ Heqp acc1).
Proof.
  intros val G n heqx G1 Heqp acc1 acc2 Hf.
  destruct acc1 as [acc1].
  apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HR_dec_formula_aux_inr :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inr (G1, G2)) acc1 acc2 acc3,
    FOL_R_formula_sem val (HR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G2 _ eq_refl _ eq_refl acc3) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G _ Heqx _ Heqp acc1).
Proof.
  intros val G n heqx G1 G2 Heqp acc1 acc2 acc3 Hf1 Hf2.
  destruct acc1 as [acc1].
  split;
    [ apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1)
    | apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2) ].
Qed.

Lemma cond_HR_dec_formula_aux_atomic_inv :
  forall val G (Heqx : fst (HR_complexity_p_hseq G) = 0%nat) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = p) acc1,
    FOL_R_formula_sem val (HR_dec_formula_aux G 0%nat Heqx p Heqp acc1) ->
    FOL_R_formula_sem val (FOL_R_atomic_case G).
Proof.
  intros val G Heqx p Heqp acc1 Hf.
  destruct acc1 as [acc1].
  simpl.
  apply Hf.
Qed.

Lemma cond_HR_dec_formula_aux_inl_inv :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inl G1) acc1 acc2,
    FOL_R_formula_sem val (HR_dec_formula_aux G _ Heqx _ Heqp acc1) ->
    FOL_R_formula_sem val (HR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2).
Proof.
  intros val G n heqx G1 Heqp acc1 acc2 Hf.
  destruct acc1 as [acc1].
  simpl in Hf.
  refine (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf).
Qed.

Lemma cond_HR_dec_formula_aux_inr_inv :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inr (G1, G2)) acc1 acc2 acc3,
    FOL_R_formula_sem val (HR_dec_formula_aux G _ Heqx _ Heqp acc1) ->
    (FOL_R_formula_sem val (HR_dec_formula_aux G1 _ eq_refl _ eq_refl acc2) *
     FOL_R_formula_sem val (HR_dec_formula_aux G2 _ eq_refl _ eq_refl acc3)).
Proof.
  intros val G n heqx G1 G2 Heqp acc1 acc2 acc3 Hf.
  destruct acc1 as [acc1].
  destruct Hf as [Hf1 Hf2].
  split;
    [ apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf1)
    | apply (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf2) ].
Qed.

(* end hide *)

Definition HR_dec_formula G := HR_dec_formula_aux G _ eq_refl _ eq_refl (wf_lt_nat2 _).

Lemma cond_HR_dec_formula_atomic :
  forall val G (Heqx : fst (HR_complexity_p_hseq G) = 0%nat),
    FOL_R_formula_sem val (FOL_R_atomic_case G) ->
    FOL_R_formula_sem val (HR_dec_formula G).
Proof.
  intros val G Heqn Hf.
  unfold HR_dec_formula.
  refine (HR_dec_formula_aux_sem_indep_n _ _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ (cond_HR_dec_formula_aux_atomic val G Heqn _ eq_refl _ Hf))).
  apply wf_lt_nat2.
Qed.

Lemma cond_HR_dec_formula_inl :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inl G1),
    FOL_R_formula_sem val (HR_dec_formula G1) ->
    FOL_R_formula_sem val (HR_dec_formula G).
Proof.
  intros val G n Heqx G1 Heqp Hf.
  unfold HR_dec_formula in *.
  apply HR_dec_formula_aux_sem_indep_n with (S n) Heqx.
  refine (HR_dec_formula_aux_sem_indep_p _ _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ (cond_HR_dec_formula_aux_inl _ _ _ _ _ _ _ _ Hf))); auto.
  apply wf_lt_nat2.
Qed.

Lemma cond_HR_dec_formula_inr :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inr (G1, G2)),
    FOL_R_formula_sem val (HR_dec_formula G1) ->
    FOL_R_formula_sem val (HR_dec_formula G2) ->
    FOL_R_formula_sem val (HR_dec_formula G).
Proof.
  intros val G n Heqx G1 G2 Heqp Hf1 Hf2.
  unfold HR_dec_formula in *.
  apply HR_dec_formula_aux_sem_indep_n with (S n) Heqx.
  refine (HR_dec_formula_aux_sem_indep_p _ _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ (cond_HR_dec_formula_aux_inr _ _ _ _ _ _ _ _ _ _ Hf1 Hf2))); auto.
  apply wf_lt_nat2.
Qed.

Lemma cond_HR_dec_formula_atomic_inv :
  forall val G (Heqx : fst (HR_complexity_p_hseq G) = 0%nat),
    FOL_R_formula_sem val (HR_dec_formula G) ->
    FOL_R_formula_sem val (FOL_R_atomic_case G).
Proof.
  intros val G Heqx Hf.
  unfold HR_dec_formula in Hf.
  apply HR_dec_formula_aux_sem_indep_n with _ _ _ _ _ Heqx _ _ _ in Hf.
  remember (wf_lt_nat2 (HR_complexity_p_hseq G)).
  destruct a.
  apply Hf.
Qed.

Lemma cond_HR_dec_formula_inl_inv :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inl G1),
    FOL_R_formula_sem val (HR_dec_formula G) ->
    FOL_R_formula_sem val (HR_dec_formula G1).
Proof.
  intros val G n Heqx G1 Heqp Hf.
  unfold HR_dec_formula in *.
  apply HR_dec_formula_aux_sem_indep_n with _ _ _ _ (S n) Heqx _ _ _ in Hf.
  apply HR_dec_formula_aux_sem_indep_p with _ _ _ _ _ _ _ Heqp _ in Hf.
  refine (cond_HR_dec_formula_aux_inl_inv _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf)); auto.
  apply wf_lt_nat2.
Qed.

Lemma cond_HR_dec_formula_inr_inv :
  forall val G n (Heqx : fst (HR_complexity_p_hseq G) = S n) G1 G2 (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G) = inr (G1, G2)),
    FOL_R_formula_sem val (HR_dec_formula G) ->
    (FOL_R_formula_sem val (HR_dec_formula G1) *
     FOL_R_formula_sem val (HR_dec_formula G2)).
Proof.
  intros val G n Heqx G1 G2 Heqp Hf.
  unfold HR_dec_formula in *.
  apply HR_dec_formula_aux_sem_indep_n with _ _ _ _ (S n) Heqx _ _ _ in Hf.
  apply HR_dec_formula_aux_sem_indep_p with _ _ _ _ _ _ _ Heqp _ in Hf.
  refine (cond_HR_dec_formula_aux_inr_inv _ _ _ _ _ _ _ _ _ _ (HR_dec_formula_aux_sem_indep_acc _ _ _ _ _ _ _ _ Hf)).
  apply wf_lt_nat2.
Qed.

Lemma FOL_R_atomic_case_1
      val
      (G : p_hypersequent)
      (Hwd : p_hseq_well_defined val G)
      (Hb : p_hseq_is_atomic G) :
  HR_T (map (eval_p_sequent val) G) ->
  FOL_R_formula_sem val (FOL_R_atomic_case G).
Proof.
  intros pi.
  unfold FOL_R_atomic_case.
  apply cond_FOL_R_atomic_case_aux_formula_sem.
  apply HR_le_frag with _ (hr_frag_T_M) _ in pi ; [ | repeat split; auto].
  assert (hseq_is_atomic (map (eval_p_sequent val) G)) as Hat.
  { apply p_hseq_atomic_hseq_atomic.
    apply Hb. }
  destruct (lambda_prop _ Hat pi) as [L [Hlen [[Hex Hall] Hsum]]].
  split with (pos_indexes L).
  { rewrite<- (rev_involutive (pos_indexes L)).
    apply in_inf_map.
    apply cond_is_in_make_subsets.
    - apply rev_not_nil.
      clear - Hex.
      induction L; [inversion Hex | ].
      inversion Hex; subst.
      + apply R_blt_lt in H0.
        simpl; rewrite H0.
        intros H; inversion H.
      + case_eq (0 <? a); intros H; [ simpl; rewrite H; intros H'; inversion H' | ].
        simpl; rewrite H.
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
        apply HR_not_empty in pi.
        exfalso; auto.            
    - intros i j Hlen' Hlt'.
      apply rev_reverse_order_lt; try lia.
      apply pos_indexes_order. }
  apply cond_FOL_R_exists_phi_formula_sem.
  split with L.
  split; [ rewrite map_length in Hlen; apply Hlen | ].
  repeat split.
  - apply cond_FOL_R_all_zero_formula_sem.
    intros n Hin.
    rewrite map_length in Hlen; rewrite <- Hlen.
    rewrite upd_val_vec_eq.
    enough (nth n L (val (S (max_var_weight_p_hseq G) + n)%nat) <= 0).
    { apply Forall_inf_nth with _ _ _ n (val ((S (max_var_weight_p_hseq G)) + n)%nat) in Hall; [ lra | ].
      apply In_inf_complementary_lt with (pos_indexes L).
      rewrite <- Hlen in Hin.
      apply Hin. }
    rewrite nth_indep with _ _ _ _ 0.
    2:{ apply In_inf_complementary_lt with (pos_indexes L).
        rewrite <- Hlen in Hin.
        apply Hin. }
    apply pos_indexes_not_In_inf.
    -- apply In_inf_complementary_lt with (pos_indexes L).
       rewrite <- Hlen in Hin.
       apply Hin.
    -- intros H'.
       apply In_inf_complementary in Hin; auto.
  - apply cond_FOL_R_all_gtz_formula_sem.
    intros n Hin.
    change (list (prod Rpos term)) with sequent.
    rewrite map_length in Hlen; rewrite <- Hlen.
    rewrite upd_val_vec_eq.
    assert (n < length L)%nat as Hlt.
    { apply (@Forall_inf_forall _ (fun x => x < length L)%nat) with (pos_indexes L); [ apply pos_indexes_Forall_inf | ].
      apply Hin. }
    rewrite nth_indep with _ _ _ _ 0; auto.
    apply pos_indexes_nth.
    apply Hin.        
  - apply cond_FOL_R_all_atoms_eq_formula_sem.
    intros n Hlen'.
    rewrite map_length in Hlen; rewrite <- Hlen.
    simpl.
    specialize (Hsum n).
    rewrite sum_weight_with_coeff_eq_var_covar in Hsum.
    rewrite (sum_weight_with_coeff_eval_eq val n G L) in Hsum.
    lra.
Qed.

Fixpoint HR_dec_formula_1
       val
       (G : p_hypersequent)
       (Hwd : p_hseq_well_defined val G)
       (acc : Acc lt_nat2 (HR_complexity_p_hseq G)) :
  HR_T (map (eval_p_sequent val) G) ->
  FOL_R_formula_sem val (HR_dec_formula G).
Proof.
  intros pi.
  destruct acc as [acc].
  remember (fst (HR_complexity_p_hseq G)).
  destruct n;
    [ |
      remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G)) ].
  - apply cond_HR_dec_formula_atomic; auto.
    apply FOL_R_atomic_case_1; auto.
    apply p_hseq_is_atomic_complexity_0_inv.
    auto.
  - destruct s as [G1 | [G1 G2] ].
    + apply (cond_HR_dec_formula_inl val G n (eq_sym Heqn) G1 (eq_sym Heqs)).
      refine (HR_dec_formula_1 val G1 _ _ _).
      * eapply apply_logical_rule_on_p_hypersequent_inl_well_defined; [ symmetry; apply Heqs | ].
        apply p_hseq_put_non_atomic_fst_well_defined; auto.
        simpl in Heqn; rewrite <- Heqn; lia.
      * apply acc.
        apply (apply_logical_rule_on_p_hypersequent_correct_inl G G1 n (eq_sym Heqn) (eq_sym Heqs)).
      * apply hrr_M_elim.
        eapply apply_logical_rule_on_p_hypersequent_inl_HR; [ symmetry; apply Heqs | | ].
        -- apply p_hseq_put_non_atomic_fst_well_defined; auto.
           simpl in Heqn; rewrite <- Heqn; lia.
        -- unfold p_hseq_put_non_atomic_fst.
           rewrite map_cons.
           apply hrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
           { apply Permutation_Type_eval_p_sequent.
             apply p_seq_put_non_atomic_fst.
             intros H.
             apply p_seq_is_atomic_complexity_0 in H.
             rewrite p_hseq_p_seq_max_complexity_correct in H.
             simpl in *; lia. }
           apply hrr_ex_hseq with (map (eval_p_sequent val) G); auto ; [ | eapply HR_le_frag ; [ | apply pi]; repeat split; auto ].
           rewrite <- map_cons.
           apply Permutation_Type_map.
           apply p_hseq_put_max_complexity_fst.
           intros H; rewrite H in Heqn; inversion Heqn.
    + apply (cond_HR_dec_formula_inr val G n (eq_sym Heqn) G1 G2 (eq_sym Heqs)).
      * refine (HR_dec_formula_1 val G1 _ _ _).
        -- eapply apply_logical_rule_on_p_hypersequent_inr_l_well_defined; [ symmetry; apply Heqs | ].
           apply p_hseq_put_non_atomic_fst_well_defined; auto.
           simpl in Heqn; rewrite <- Heqn; lia.
        -- apply acc.
           apply (apply_logical_rule_on_p_hypersequent_correct_inr_l G G1 G2 n (eq_sym Heqn) (eq_sym Heqs)).
        -- apply hrr_M_elim.
           eapply apply_logical_rule_on_p_hypersequent_inr_l_HR; [ symmetry; apply Heqs | | ].
           ++ apply p_hseq_put_non_atomic_fst_well_defined; auto.
              simpl in Heqn; rewrite <- Heqn; lia.
           ++ unfold p_hseq_put_non_atomic_fst.
              rewrite map_cons.
              apply hrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
              { apply Permutation_Type_eval_p_sequent.
                apply p_seq_put_non_atomic_fst.
                intros H.
                apply p_seq_is_atomic_complexity_0 in H.
                rewrite p_hseq_p_seq_max_complexity_correct in H.
                simpl in *; lia. }
              apply hrr_ex_hseq with (map (eval_p_sequent val) G); auto ; [ | eapply HR_le_frag ; [ | apply pi]; repeat split; auto ].
              rewrite <- map_cons.
              apply Permutation_Type_map.
              apply p_hseq_put_max_complexity_fst.
              intros H; rewrite H in Heqn; inversion Heqn.
      * refine (HR_dec_formula_1 val G2 _ _ _).
        -- eapply apply_logical_rule_on_p_hypersequent_inr_r_well_defined; [ symmetry; apply Heqs | ].
           apply p_hseq_put_non_atomic_fst_well_defined; auto.
           simpl in Heqn; rewrite <- Heqn; lia.
        -- apply acc.
           apply (apply_logical_rule_on_p_hypersequent_correct_inr_r G G1 G2 n (eq_sym Heqn) (eq_sym Heqs)).
        -- apply hrr_M_elim.
           eapply apply_logical_rule_on_p_hypersequent_inr_r_HR; [ symmetry; apply Heqs | | ].
           ++ apply p_hseq_put_non_atomic_fst_well_defined; auto.
              simpl in Heqn; rewrite <- Heqn; lia.
           ++ unfold p_hseq_put_non_atomic_fst.
              rewrite map_cons.
              apply hrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
              { apply Permutation_Type_eval_p_sequent.
                apply p_seq_put_non_atomic_fst.
                intros H.
                apply p_seq_is_atomic_complexity_0 in H.
                rewrite p_hseq_p_seq_max_complexity_correct in H.
                simpl in *; lia. }
              apply hrr_ex_hseq with (map (eval_p_sequent val) G); auto ; [ | eapply HR_le_frag ; [ | apply pi]; repeat split; auto ].
              rewrite <- map_cons.
              apply Permutation_Type_map.
              apply p_hseq_put_max_complexity_fst.
              intros H; rewrite H in Heqn; inversion Heqn.
Qed.

Lemma FOL_R_atomic_case_2
      val
      (G : p_hypersequent)
      (Hwd : p_hseq_well_defined val G)
      (Hb : p_hseq_is_atomic G) :
  FOL_R_formula_sem val (FOL_R_atomic_case G) ->
  HR_T_M (map (eval_p_sequent val) G).
Proof.
  intros Hf.
  unfold FOL_R_atomic_case in Hf.
  apply cond_FOL_R_atomic_case_aux_formula_sem_inv in Hf as [v Hin f].
  apply cond_FOL_R_exists_phi_formula_sem_inv in f as [vr [Hlen f]].
  destruct f as [f1 [f2 f3]].
  apply lambda_prop_inv.
  { apply p_hseq_atomic_hseq_atomic.
    apply Hb. }
  split with (map (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (seq (S (max_var_weight_p_hseq G)) (length G))).
  repeat split.
  * rewrite ? map_length.
    rewrite seq_length.
    reflexivity.
  * clear f1 f3.
    apply in_inf_map_inv in Hin as [vx Heq Hin].
    apply cond_is_in_make_subsets_inv in Hin as [[Hnnil Hle] Hlt].
    destruct vx ; [ exfalso; apply Hnnil; auto | ].
    apply nth_Exists_inf with n 0.
    { rewrite map_length; rewrite seq_length.
      apply (Hle 0%nat). }
    rewrite <- Hlen.
    rewrite map_upd_val_vec_eq.
    apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ n in f2.
    2:{ rewrite <- Heq.
        apply in_inf_rev.
        left; auto. }
    rewrite <- Hlen in f2.
    rewrite upd_val_vec_eq in f2.
    rewrite nth_indep with _ _ _ _ (val ((S (max_var_weight_p_hseq G)) + n)%nat) ; [ apply f2 | ].
    rewrite Hlen.
    apply (Hle 0%nat).
  * clear f3.
    rewrite <- Hlen.
    rewrite map_upd_val_vec_eq.
    apply nth_Forall_inf.
    intros i a' Hlt.
    destruct (complementary_partition v (length vr) i); auto.
    -- apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ i in f2; auto.
       rewrite <- Hlen in f2; rewrite upd_val_vec_eq in f2.
       rewrite nth_indep with _ _ _ _ 0; auto.
       apply Rlt_le.
       rewrite nth_indep with _ _ _ _ (val ((S (max_var_weight_p_hseq G)) + i)%nat) ; [ apply f2 | apply Hlt].
    -- rewrite Hlen in i0.
       apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ i in f1; auto.
       rewrite <- Hlen in f1.
       rewrite upd_val_vec_eq in f1.
       rewrite nth_indep with _ _ _ _ (val ((S (max_var_weight_p_hseq G)) + i)%nat); auto.
       lra.
  * clear f1 f2.
    intros n.
    case_eq (n <=? max_var_p_hseq G)%nat; intros Hle.
    -- apply cond_FOL_R_all_atoms_eq_formula_sem_inv with _ _ _ n in f3 ; [ | apply Nat.leb_le in Hle; auto].
       rewrite sum_weight_with_coeff_eq_var_covar.
       rewrite (sum_weight_with_coeff_eval_eq val n G _).
       simpl in f3 |- *.
       rewrite <- Hlen.
       rewrite map_upd_val_vec_eq.
       rewrite Hlen.
       lra.
    -- apply Nat.leb_nle in Hle.
       clear - Hle.
       rewrite sum_weight_with_coeff_eq_var_covar.
       assert (H := max_var_hseq_le_p_hseq val G).
       rewrite sum_weight_var_with_coeff_lt_max_var; [ | lia ].
       rewrite sum_weight_covar_with_coeff_lt_max_var; [ | lia ].
       lra.
Qed.
  
Fixpoint HR_dec_formula_2
         val
         (G : p_hypersequent)
         (Hwd : p_hseq_well_defined val G)
         (acc : Acc lt_nat2 (HR_complexity_p_hseq G)) :
  FOL_R_formula_sem val (HR_dec_formula G) ->
  HR_T_M (map (eval_p_sequent val) G).
Proof.
  intros Hf.
  destruct acc as [acc].
  remember (fst (HR_complexity_p_hseq G)).
  destruct n.
  { refine (FOL_R_atomic_case_2 val G Hwd _ _).
    - apply p_hseq_is_atomic_complexity_0_inv.
      simpl in Heqn; auto.
    - apply cond_HR_dec_formula_atomic_inv in Hf; auto. }
  apply hrr_ex_hseq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G) :: map (eval_p_sequent val) (p_hseq_without_max_complexity G)).
  { rewrite <- map_cons.
    apply Permutation_Type_map.
    symmetry; apply p_hseq_put_max_complexity_fst.
    destruct G; [ inversion Heqn | intros H; inversion H]. }
  apply hrr_ex_seq with (eval_p_sequent val (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G))).
  { apply Permutation_Type_eval_p_sequent.
    symmetry; apply p_seq_put_non_atomic_fst.
    intros Hb; apply p_seq_is_atomic_complexity_0 in Hb.
    rewrite p_hseq_p_seq_max_complexity_correct in Hb.
    simpl in *; lia. }
  remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G)).
  destruct s as [G1 | [G1 G2]].
  - rewrite <- map_cons.
    refine (apply_logical_rule_on_p_hypersequent_inl_HR_inv val _ G1 (eq_sym Heqs) _ _).
    + apply p_hseq_put_non_atomic_fst_well_defined; auto.
      simpl in Heqn; lia.
    + refine (HR_dec_formula_2 val G1 _ _ _).
      * apply apply_logical_rule_on_p_hypersequent_inl_well_defined with (p_hseq_put_non_atomic_fst G); auto.
           apply p_hseq_put_non_atomic_fst_well_defined; auto.
           simpl in Heqn; lia.
      * apply acc.
        apply apply_logical_rule_on_p_hypersequent_correct_inl with n; auto.
      * apply (cond_HR_dec_formula_inl_inv val G n (eq_sym Heqn) G1) in Hf; auto.
  - rewrite <- map_cons.
    refine (apply_logical_rule_on_p_hypersequent_inr_HR_inv val _ G1 G2 (eq_sym Heqs) _ _ _).
    + apply p_hseq_put_non_atomic_fst_well_defined; auto.
      simpl in Heqn; lia.
    + refine (HR_dec_formula_2 val G1 _ _ _).
      * apply apply_logical_rule_on_p_hypersequent_inr_l_well_defined with (p_hseq_put_non_atomic_fst G) G2; auto.
        apply p_hseq_put_non_atomic_fst_well_defined; auto.
        simpl in Heqn; lia.
      * apply acc.
        apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 n; auto.
      * apply (cond_HR_dec_formula_inr_inv val G n (eq_sym Heqn) G1 G2) in Hf as [Hf1 _ ]; auto.
    + refine (HR_dec_formula_2 val G2 _ _ _).
      * apply apply_logical_rule_on_p_hypersequent_inr_r_well_defined with (p_hseq_put_non_atomic_fst G) G1; auto.
        apply p_hseq_put_non_atomic_fst_well_defined; auto.
        simpl in Heqn; lia.
      * apply acc.
        apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 n; auto.
      * apply (cond_HR_dec_formula_inr_inv val G n (eq_sym Heqn) G1 G2) in Hf as [_ Hf2]; auto.
Qed.

(** there exists a formula \phi_G such that \phi_G(\vec r) has a proof if and only if G[\vec r /\vec x] has a proof *) 
Lemma HR_FOL_R_equiv : forall G,
    { f & forall val, p_hseq_well_defined val G ->
                      prod
                        (HR_full (map (eval_p_sequent val) G) -> FOL_R_formula_sem val f)
                        (FOL_R_formula_sem val f -> HR_full (map (eval_p_sequent val) G)) }.
Proof.
  enough (forall G,
             { f & forall val, p_hseq_well_defined val G ->
                               prod
                                (HR_T (map (eval_p_sequent val) G) -> FOL_R_formula_sem val f)
                                (FOL_R_formula_sem val f -> HR_T_M (map (eval_p_sequent val) G)) }).
  { intros G.
    specialize (X G) as [f H].
    split with f.
    intros val H'.
    destruct (H val) as [H1 H2]; try assumption.
    split.
    - intros pi.
      apply H1.
      apply hrr_M_elim.
      apply hrr_can_elim.
      apply pi.
    - intros Hf.
      refine (HR_le_frag _ _ _ _ (H2 Hf)).
      repeat split; auto. }
  intros G.
  split with (HR_dec_formula G).
  intros val Hwd.
  split.
  - intros pi.
    apply HR_dec_formula_1; auto.
    apply wf_lt_nat2.
  - intros Hf.
    apply HR_dec_formula_2; auto.
    apply wf_lt_nat2.
Qed.

Lemma p_HR_decidable : forall val G,
    p_hseq_well_defined val G ->
    (HR_full (map (eval_p_sequent val) G)) + (HR_full (map (eval_p_sequent val) G) -> False).
Proof.
  intros val G Hwd.
  destruct (HR_FOL_R_equiv G) as [f [H1 H2]]; [ apply Hwd | ].
  destruct (FOL_R_decidable f) with val.
  - left.
    apply H2; apply f0.
  - right.
    intros pi; apply f0; apply H1; apply pi.
Qed.

(** Theorem 4.11 *)
Lemma HR_decidable : forall G,
    (HR_full G) + (HR_full G -> False).
Proof.
  intros G.
  rewrite <- (eval_p_hypersequent_to_p_hypersequent) with (fun x => 0) _.
  apply p_HR_decidable.
  apply to_p_hypersequent_well_defined.
Qed.
