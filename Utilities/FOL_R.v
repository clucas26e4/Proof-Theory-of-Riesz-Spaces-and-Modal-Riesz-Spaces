(** Existential fragment of first order logic for the signature (R, +, ., <=, =) where . is an external multiplication by a real scalar *)

Require Import riesz_logic_List_more.

Require Export Reals.
Require Import Rpos.
Require Import Bool.
Require Import Lra.
Require Import FunctionalExtensionality.
Require Import Lia.

Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.List_more.

Local Open Scope R_scope.
(* begin hide *)
Definition upd_val (v : nat -> R) n r :=
  fun n' => if beq_nat n n' then r else v n'.

Fixpoint upd_val_vec (val : nat -> R) (vx : list nat) (vr : list R) :=
  match vx, vr with
  | nil , _ => val
  | _ , nil => val
  | x :: vx, r :: vr => upd_val_vec (upd_val val x r) vx vr
  end.

Lemma upd_val_vec_not_in : forall val L v x,
    (In_inf x v -> False) ->
    upd_val_vec val v L x = val x.
Proof.
  intros val L v; revert val L; induction v; intros val L x Hin.
  - reflexivity.
  - destruct L; [reflexivity | ].
    simpl.
    rewrite IHv.
    2:{ intros H; apply Hin; right; apply H. }
    case_eq (a =? x); intros H; unfold upd_val; rewrite H; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H].
    + exfalso.
      apply Hin; left; lia.
    + reflexivity.
Qed.
      
Lemma upd_val_vec_seq_add : forall L v n k1 k2 i,
    upd_val_vec v (seq (k1 + k2) n) L (k1 + k2 + i) = upd_val_vec (fun x => v (k1 + x)%nat) (seq k2 n) L (k2 + i).
Proof.
  intros L v n.
  revert L v; induction n; intros L v k1 k2 i.
  - simpl.
    replace (k1 + k2 + i)%nat with (k1 + (k2 + i))%nat by lia.
    reflexivity.
  - destruct L; simpl; [ replace (k1 + k2 + i)%nat with (k1 + (k2 + i))%nat by lia; reflexivity| ].
    destruct i.
    + rewrite ? upd_val_vec_not_in.
      * unfold upd_val.
        replace (k1 + k2 =? k1 + k2 + 0) with true by (symmetry; apply Nat.eqb_eq; lia).
        replace (k2 =? k2 + 0) with true by (symmetry; apply Nat.eqb_eq; lia).
        reflexivity.
      * apply not_In_inf_seq.
        lia.
      * apply not_In_inf_seq.
        lia.        
    + replace (S (k1 + k2)) with (k1 + S k2)%nat by lia.
      replace (k1 + k2 + S i)%nat with (k1 + (S k2) + i)%nat by lia.
      rewrite IHn.
      replace (k2 + S i)%nat with (S k2 + i)%nat by lia.
      replace (fun x : nat => upd_val v (k1 + k2) r (k1 + x)) with (upd_val (fun x : nat => v (k1 + x)%nat) k2 r) ; [ reflexivity | ].
      apply functional_extensionality.
      intros x.
      unfold upd_val.
      case_eq (k2 =? x) ; intros H.
      * replace (k1 + k2 =? k1 + x) with true; [ reflexivity | ].
        symmetry; apply Nat.eqb_eq; apply Nat.eqb_eq in H.
        lia.
      * replace (k1 + k2 =? k1 + x) with false; [ reflexivity | ].
        symmetry; apply Nat.eqb_neq; apply Nat.eqb_neq in H; lia.
Qed.

Lemma upd_val_vec_eq : forall L v n i,
    upd_val_vec v (seq i (length L)) L (i + n) = nth n L (v (i + n))%nat.
Proof.
  intros L v n i; revert L v n; induction i.
  - induction L; intros v n.
    + destruct n; simpl; try reflexivity.
    + destruct n.
      * simpl.
        rewrite upd_val_vec_not_in; try reflexivity.
        apply not_In_inf_seq; lia.
      * simpl.
        change (v (S n)) with ((fun x => v (S x)) n).
        rewrite <- IHL.
        replace (1%nat) with (1 + 0)%nat by lia.
        replace (S n) with (1 + 0 + n)%nat by lia.
        rewrite upd_val_vec_seq_add.
        simpl.
        replace (fun x : nat => upd_val v 0 a (S x)) with (fun x : nat => v (S x)) ; [reflexivity | ].
        apply functional_extensionality.
        intros x.
        unfold upd_val.
        replace (0 =? S x) with false by (symmetry; apply Nat.eqb_neq; lia).
        reflexivity.
  - intros L v n.
    replace (S i) with (1 + 0 + i)%nat by lia.
    rewrite upd_val_vec_seq_add.
    rewrite IHi.
    replace (1 + 0 + (i + n))%nat with (1 + 0 + i + n)%nat by lia.
    reflexivity.
Qed.

Lemma upd_val_eq : forall val i a,
             upd_val val i a i = a.
Proof.
  intros val i a; unfold upd_val.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma map_upd_val_vec_eq : forall v L i,
    map (upd_val_vec v (seq i (length L)) L) (seq i (length L)) = L.
Proof.
  intros v L i.
  apply nth_ext with 0 0.
  { rewrite map_length; rewrite seq_length.
    reflexivity. }
  intros n.
  intros Hlt.
  rewrite map_length in Hlt; rewrite seq_length in Hlt.
  rewrite nth_indep with _ _ _ _ (upd_val_vec v (seq i (length L)) L 0).
  2:{ rewrite map_length; rewrite seq_length.
      lia. }
  rewrite map_nth.
  rewrite seq_nth; [ | assumption].
  rewrite upd_val_vec_eq.
  rewrite nth_indep with _ _ _ _ 0 ; auto.
Qed.

(* end hide *)

Inductive FOL_R_term : Type :=
| FOL_R_var : nat -> FOL_R_term
| FOL_R_cst : R -> FOL_R_term
| FOL_R_mul : FOL_R_term -> FOL_R_term -> FOL_R_term
| FOL_R_add : FOL_R_term -> FOL_R_term -> FOL_R_term.

Notation "f1 *R f2" := (FOL_R_mul f1 f2) (at level 20, left associativity).
Notation "f1 +R f2" := (FOL_R_add f1 f2) (at level 15).

Fixpoint max_var_FOL_R_term t :=
  match t with
  | FOL_R_var n => n
  | FOL_R_cst r => 0%nat
  | FOL_R_mul t1 t2 => Nat.max (max_var_FOL_R_term t1) (max_var_FOL_R_term t2)
  | FOL_R_add t1 t2 => Nat.max (max_var_FOL_R_term t1) (max_var_FOL_R_term t2)
  end.                         

Fixpoint FOL_R_term_sem (v : nat -> R) t :=
  match t with
  | FOL_R_var n => v n
  | FOL_R_cst r => r
  | FOL_R_mul t1 t2 => (FOL_R_term_sem v t1) * (FOL_R_term_sem v t2)
  | FOL_R_add t1 t2 => (FOL_R_term_sem v t1) + (FOL_R_term_sem v t2)
  end.

(* begin hide *)
Lemma FOL_R_term_sem_upd_val_vec_not_in : forall val vx vr i,
    (In_inf i vx -> False) ->
    FOL_R_term_sem (upd_val_vec val vx vr) (FOL_R_var i) = val i.
Proof.
  intros val vx; revert val; induction vx; intros val vr i Hin; auto.
  destruct vr; auto.
  simpl in *.
  rewrite IHvx.
  2:{ intros H; apply Hin; now right. }
  unfold upd_val.
  case_eq (a =? i); intros; auto.
  exfalso; apply Hin.
  left.
  apply Nat.eqb_eq; apply H.
Qed.

Lemma map_val_seq_var : forall val L i,
    map (FOL_R_term_sem (upd_val_vec val (seq i (length L)) L)) (map FOL_R_var (seq i (length L))) = L.
Proof.
  intros val L i.
  apply nth_ext with 0 0 ; [ rewrite 2 map_length; now rewrite seq_length | ].
  intros n.
  intros H.
  rewrite ? map_length in H; rewrite seq_length in H.
  rewrite nth_indep with _ _ _ _ (FOL_R_term_sem (upd_val_vec val (seq i (length L)) L) (FOL_R_var 0%nat)).
  2:{ rewrite 2 map_length; rewrite seq_length; apply H. }
  rewrite map_nth.
  rewrite map_nth.
  rewrite seq_nth; auto.
  simpl.
  rewrite upd_val_vec_eq.
  apply nth_indep; assumption.
Qed.

Lemma upd_val_term_lt :
  forall val a x r,
    (max_var_FOL_R_term a < x)%nat ->
    FOL_R_term_sem (upd_val val x r) a = FOL_R_term_sem val a.
Proof.
  intros val; induction a; intros x r' Hlt; simpl in *; try rewrite IHa1; try rewrite IHa2; try reflexivity; try lia.
  unfold upd_val.
  replace (x =? n) with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

(* end hide *)

Inductive FOL_R_pred : Type :=
| FOL_R_eq : FOL_R_term -> FOL_R_term -> FOL_R_pred
| FOL_R_neq : FOL_R_term -> FOL_R_term -> FOL_R_pred
| FOL_R_le : FOL_R_term -> FOL_R_term -> FOL_R_pred.

Notation "f1 =R f2" := (FOL_R_eq f1 f2) (at level 50).
Notation "f1 <>R f2" := (FOL_R_neq f1 f2) (at level 50).
Notation "f1 <=R f2" := (FOL_R_le f1 f2) (at level 50).                                            

Definition FOL_R_pred_sem (v : nat -> R) p :=
  match p with
  | FOL_R_eq t1 t2 => (FOL_R_term_sem v t1) = (FOL_R_term_sem v t2)
  | FOL_R_neq t1 t2 => (FOL_R_term_sem v t1) <> (FOL_R_term_sem v t2)
  | FOL_R_le t1 t2 => (FOL_R_term_sem v t1) <= (FOL_R_term_sem v t2)
  end.

Inductive FOL_R_formula : Type :=
| FOL_R_true : FOL_R_formula
| FOL_R_false : FOL_R_formula
| FOL_R_atoms : FOL_R_pred -> FOL_R_formula
| FOL_R_and : FOL_R_formula -> FOL_R_formula -> FOL_R_formula
| FOL_R_or : FOL_R_formula -> FOL_R_formula -> FOL_R_formula
| FOL_R_exists : nat -> FOL_R_formula -> FOL_R_formula.

Fixpoint exists_vec (v : list nat) (f : FOL_R_formula) :=
  match v with
  | nil => f
  | n :: v => FOL_R_exists n (exists_vec v f)
  end.

Notation "f1 /\R f2" := (FOL_R_and f1 f2) (at level 40, left associativity).
Notation "f1 \/R f2" := (FOL_R_or f1 f2) (at level 45, left associativity).

Fixpoint FOL_R_formula_sem (v : nat -> R) f : Type :=
  match f with
  | FOL_R_true => True
  | FOL_R_false => False
  | FOL_R_atoms p => FOL_R_pred_sem v p
  | FOL_R_and f1 f2 => prod (FOL_R_formula_sem v f1) (FOL_R_formula_sem v f2)
  | FOL_R_or f1 f2 => sum (FOL_R_formula_sem v f1) (FOL_R_formula_sem v f2)
  | FOL_R_exists n f => { r & FOL_R_formula_sem (upd_val v n r) f}
  end.

Lemma cond_FOL_R_exists_vec_formula_sem : forall v f val,
    {vr & prod (length v = length vr) (FOL_R_formula_sem (upd_val_vec val v vr) f)} ->
    FOL_R_formula_sem val (exists_vec v f).
Proof.
  induction v; intros f val [vr [Hlen Hf]].
  - apply Hf.
  - destruct vr; [inversion Hlen | ].
    simpl in *.
    split with r.
    apply IHv.
    split with vr.
    repeat split; auto.
Qed.

Lemma cond_FOL_R_exists_vec_formula_sem_inv : forall v f val,
    FOL_R_formula_sem val (exists_vec v f) ->
    {vr & prod (length v = length vr) (FOL_R_formula_sem (upd_val_vec val v vr) f)}.
Proof.
  induction v; intros f val Hf.
  - split with nil; split; auto.
  - destruct Hf as [r Hf].
    destruct (IHv _ _ Hf) as [vr [Hlen Hf']].
    split with (r :: vr).
    repeat split; simpl in *; try lia.
    apply Hf'.
Qed.

Axiom FOL_R_decidable : forall f v, (FOL_R_formula_sem v f) + (FOL_R_formula_sem v f -> False).

Definition Permutation_Type_FOL_R_term val l1 l2 := Permutation_Type (map (FOL_R_term_sem val) l1) (map (FOL_R_term_sem val) l2).

(** Size of a formula *)

Fixpoint degree_FOL_R_term t :=
  match t with
  | FOL_R_var _ => 1%nat
  | FOL_R_cst _ => 0%nat
  | FOL_R_add t1 t2 => max (degree_FOL_R_term t1) (degree_FOL_R_term t2)
  | FOL_R_mul t1 t2 => ((degree_FOL_R_term t1) + (degree_FOL_R_term t2))%nat
  end.

Definition degree_FOL_R_pred p :=
  match p with
  | FOL_R_eq t1 t2 => max (degree_FOL_R_term t1) (degree_FOL_R_term t2)
  | FOL_R_neq t1 t2 => max (degree_FOL_R_term t1) (degree_FOL_R_term t2)
  | FOL_R_le t1 t2 => max (degree_FOL_R_term t1) (degree_FOL_R_term t2)
  end.

Fixpoint degree_FOL_R_formula f :=
  match f with
  | FOL_R_true => 0%nat
  | FOL_R_false => 0%nat
  | FOL_R_atoms p => degree_FOL_R_pred p
  | FOL_R_and f1 f2 => max (degree_FOL_R_formula f1) (degree_FOL_R_formula f2)
  | FOL_R_or f1 f2 => max (degree_FOL_R_formula f1) (degree_FOL_R_formula f2)
  | FOL_R_exists _ f => degree_FOL_R_formula f
  end.

Fixpoint nb_pol_FOL_R_formula f :=
  match f with
  | FOL_R_true => 0%nat
  | FOL_R_false => 0%nat
  | FOL_R_atoms p => 1%nat
  | FOL_R_and f1 f2 => ((nb_pol_FOL_R_formula f1) + (nb_pol_FOL_R_formula f2))%nat
  | FOL_R_or f1 f2 => ((nb_pol_FOL_R_formula f1) + (nb_pol_FOL_R_formula f2))%nat
  | FOL_R_exists _ f => nb_pol_FOL_R_formula f
  end.

Fixpoint nb_exists_FOL_R_formula f :=
  match f with
  | FOL_R_true => 0%nat
  | FOL_R_false => 0%nat
  | FOL_R_atoms p => 0%nat
  | FOL_R_and f1 f2 => ((nb_exists_FOL_R_formula f1) + (nb_exists_FOL_R_formula f2))%nat
  | FOL_R_or f1 f2 => ((nb_exists_FOL_R_formula f1) + (nb_exists_FOL_R_formula f2))%nat
  | FOL_R_exists _ f => (1 + nb_exists_FOL_R_formula f)%nat
  end.

Lemma degree_FOL_R_and : forall f1 f2,
    degree_FOL_R_formula (FOL_R_and f1 f2) = max (degree_FOL_R_formula f1) (degree_FOL_R_formula f2).
Proof.
  reflexivity.
Qed.

Lemma nb_exists_FOL_R_exists_vec : forall f v,
    nb_exists_FOL_R_formula (exists_vec v f) = (length v + nb_exists_FOL_R_formula f)%nat.
Proof.
  intros f; induction v; simpl; auto.
Qed.
