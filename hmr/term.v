Require Import Rpos.

Require Import RL.OLlibs.List_more.
(** * Definition of terms of Riesz spaces in Negative Normal Form (i.e. built over the signature (0,+,.) where . is the external multiplication by a positive real) *)
(** ** Term *)

Inductive term : Type :=
| HMR_var : nat -> term
| HMR_covar : nat -> term
| HMR_zero : term
| HMR_plus : term -> term -> term
| HMR_mul : Rpos -> term -> term
| HMR_max : term -> term -> term
| HMR_min : term -> term -> term
| HMR_one : term
| HMR_coone : term
| HMR_diamond : term -> term.

Fixpoint HMR_minus A :=
  match A with
  | HMR_var n => HMR_covar n
  | HMR_covar n => HMR_var n
  | HMR_zero => HMR_zero
  | HMR_plus A B => HMR_plus (HMR_minus A) (HMR_minus B)
  | HMR_mul r A => HMR_mul r (HMR_minus A)
  | HMR_max A B => HMR_min (HMR_minus A) (HMR_minus B)
  | HMR_min A B => HMR_max (HMR_minus A) (HMR_minus B)
  | HMR_one => HMR_coone
  | HMR_coone => HMR_one
  | HMR_diamond A => HMR_diamond (HMR_minus A)
  end.

(** Notations *)
Notation "A +S B" := (HMR_plus A B) (at level 20, left associativity).
Notation "A \/S B" := (HMR_max A B) (at level 40, left associativity).
Notation "A /\S B" := (HMR_min A B) (at level 45, left associativity).
Notation "-S A" := (HMR_minus A) (at level 15).
Notation "A -S B" := (HMR_plus A (HMR_minus B)) (at level 10, left associativity).
Notation "r *S A" := (HMR_mul r A) (at level 15).
Notation "<S> A" := (HMR_diamond A) (at level 15).

Fixpoint sum_term k A :=
  match k with
  | 0 => HMR_zero
  | 1 => A
  | S n => A +S (sum_term n A)
  end.

(** Complexity *)
Fixpoint HMR_complexity_term A :=
  match A with
  | HMR_var n => 0
  | HMR_covar n => 0
  | HMR_one => 0
  | HMR_coone => 0
  | <S> A => 0
  | HMR_zero => 1
  | HMR_plus A B => 1 + HMR_complexity_term A + HMR_complexity_term B
  | HMR_min A B => 1 + HMR_complexity_term A + HMR_complexity_term B
  | HMR_max A B => 1 + HMR_complexity_term A + HMR_complexity_term B
  | HMR_mul r A => 1 + HMR_complexity_term A
  end.

Fixpoint max_diamond_term A :=
  match A with
  | HMR_var n => 0
  | HMR_covar n => 0
  | HMR_one => 0
  | HMR_coone => 0
  | <S> A => 1 + max_diamond_term A
  | HMR_zero => 0
  | HMR_plus A B => Nat.max (max_diamond_term A) (max_diamond_term B)
  | HMR_min A B => Nat.max (max_diamond_term A) (max_diamond_term B)
  | HMR_max A B => Nat.max (max_diamond_term A) (max_diamond_term B)
  | HMR_mul r A => max_diamond_term A
  end.

Lemma max_diamond_minus :
  forall A, max_diamond_term A = max_diamond_term (-S A).
Proof.
  induction A; simpl; try rewrite IHA; try rewrite IHA1; try rewrite IHA2; reflexivity.
Qed.

Fixpoint max_var_term A :=
  match A with
  | HMR_var n => n
  | HMR_covar n => n
  | HMR_zero => 0%nat
  | HMR_one => 0%nat
  | HMR_coone => 0%nat
  | <S> A => max_var_term A
  | A +S B => Nat.max (max_var_term A) (max_var_term B)
  | r *S A => max_var_term A
  | A /\S B => Nat.max (max_var_term A) (max_var_term B)
  | A \/S B => Nat.max (max_var_term A) (max_var_term B)
  end.

(** Substitution *)
Fixpoint subs (t1 : term) (x : nat) (t2 : term) : term :=
  match t1 with
  | HMR_var y => if (beq_nat x y) then t2 else HMR_var y
  | HMR_covar y => if (beq_nat x y) then (HMR_minus t2) else HMR_covar y
  | HMR_zero => HMR_zero
  | HMR_plus t t' => HMR_plus (subs t x t2) (subs t' x t2)
  | HMR_min t t' => HMR_min (subs t x t2) (subs t' x t2)
  | HMR_max t t' => HMR_max (subs t x t2) (subs t' x t2)
  | HMR_mul y t => HMR_mul y (subs t x t2)
  | HMR_one => HMR_one
  | HMR_coone => HMR_coone
  | HMR_diamond t => HMR_diamond (subs t x t2)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'pos' A" := (A \/S HMR_zero) (at level 5).
Notation "'neg' A" := ((-S A) \/S HMR_zero) (at level 5).
Notation "'abs' A" := (A \/S (-S A)) (at level 5).

(** Definition of atoms *)
Definition is_atom A :=
  match A with
  | HMR_var _ => True
  | HMR_covar _ => True
  | _ => False
  end.

Definition is_basic A :=
  match A with
  | HMR_var _ => True
  | HMR_covar _ => True
  | HMR_one => True
  | HMR_coone => True
  | HMR_diamond A => True
  | _ => False
  end.

Lemma is_atom_complexity_0 : forall A,
    is_atom A -> HMR_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_basic_complexity_0 : forall A,
    is_basic A -> HMR_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_basic_complexity_0_inv : forall A,
    HMR_complexity_term A = 0 -> is_basic A.
Proof.
  induction A; intros Hc0; now inversion Hc0.
Qed.

Lemma term_eq_dec : forall (A B : term) , { A = B } + { A <> B}.
Proof.
  induction A; destruct B; try (right; intro H; now inversion H).
  - case_eq (n =? n0); intro H; [ apply Nat.eqb_eq in H; rewrite H; now left | apply Nat.eqb_neq in H; right; intro H2; inversion H2; apply H; assumption ].
  - case_eq (n =? n0); intro H; [ apply Nat.eqb_eq in H; rewrite H; now left | apply Nat.eqb_neq in H; right; intro H2; inversion H2; apply H; assumption ].
  - now left.
  - specialize (IHA1 B1); specialize (IHA2 B2).
    destruct IHA1 as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct IHA2 as [ Heq' | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    left; now subst.
  - specialize (IHA B).
    destruct IHA as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct r as [r Hr] ; destruct r0 as [r0 Hr0].
    case (Req_dec r r0); [intros Heqr; left; replace (existT (fun r1 : R => (0 <? r1)%R = true) r0 Hr0) with (existT (fun r1 : R => (0 <? r1)%R = true) r Hr) by (apply Rpos_eq; simpl; apply Heqr); now subst | intros Hneqr; right; intros H; inversion H; auto].
  - specialize (IHA1 B1); specialize (IHA2 B2).
    destruct IHA1 as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct IHA2 as [ Heq' | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    left; now subst.
  - specialize (IHA1 B1); specialize (IHA2 B2).
    destruct IHA1 as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct IHA2 as [ Heq' | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    left; now subst.
  - left; reflexivity.
  - left; reflexivity.
  - specialize (IHA B) as [ Heq | Hneq ] ; [ left; now subst | right ; intro H; inversion H; apply Hneq; assumption].
Qed.
