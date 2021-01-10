(** * Definition of terms of Riesz spaces in Negative Normal Form (i.e. built over the signature (0,+,.) where . is the external multiplication by a positive real)*)
Require Import Rpos.

(** ** Term *)
Require Import RL.OLlibs.List_more.

Inductive term : Type :=
| HR_var : nat -> term
| HR_covar : nat -> term
| HR_zero : term
| HR_plus : term -> term -> term
| HR_mul : Rpos -> term -> term
| HR_max : term -> term -> term
| HR_min : term -> term -> term.

Fixpoint HR_minus A : term:=
  match A with
  | HR_var n => HR_covar n
  | HR_covar n => HR_var n
  | HR_zero => HR_zero
  | HR_plus A B => HR_plus (HR_minus A) (HR_minus B)
  | HR_mul r A => HR_mul r (HR_minus A)
  | HR_max A B => HR_min (HR_minus A) (HR_minus B)
  | HR_min A B => HR_max (HR_minus A) (HR_minus B)
  end.

(** Notations *)
Notation "A +S B" := (HR_plus A B) (at level 20, left associativity).
Notation "A \/S B" := (HR_max A B) (at level 40, left associativity).
Notation "A /\S B" := (HR_min A B) (at level 45, left associativity).
Notation "-S A" := (HR_minus A) (at level 15).
Notation "A -S B" := (HR_plus A (HR_minus B)) (at level 10, left associativity).
Notation "r *S A" := (HR_mul r A) (at level 15).

Fixpoint sum_term k A :=
  match k with
  | 0 => HR_zero
  | 1 => A
  | S n => A +S (sum_term n A)
  end.

(** Complexity *)
Fixpoint HR_complexity_term A :=
  match A with
  | HR_var n => 0
  | HR_covar n => 0
  | HR_zero => 1
  | HR_plus A B => 1 + HR_complexity_term A + HR_complexity_term B
  | HR_min A B => 1 + HR_complexity_term A + HR_complexity_term B
  | HR_max A B => 1 + HR_complexity_term A + HR_complexity_term B
  | HR_mul r A => 1 + HR_complexity_term A
  end.                                                       

Fixpoint max_var_term A :=
  match A with
  | HR_var n => n
  | HR_covar n => n
  | HR_zero => 0%nat
  | A +S B => Nat.max (max_var_term A) (max_var_term B)
  | r *S A => max_var_term A
  | A /\S B => Nat.max (max_var_term A) (max_var_term B)
  | A \/S B => Nat.max (max_var_term A) (max_var_term B)
  end.

(** Substitution *)
Fixpoint subs (t1 : term) (x : nat) (t2 : term) : term :=
  match t1 with
  | HR_var y => if (beq_nat x y) then t2 else HR_var y
  | HR_covar y => if (beq_nat x y) then (HR_minus t2) else HR_covar y
  | HR_zero => HR_zero
  | HR_plus t t' => HR_plus (subs t x t2) (subs t' x t2)
  | HR_min t t' => HR_min (subs t x t2) (subs t' x t2)
  | HR_max t t' => HR_max (subs t x t2) (subs t' x t2)
  | HR_mul y t => HR_mul y (subs t x t2)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'pos' A" := (A \/S HR_zero) (at level 5).
Notation "'neg' A" := ((-S A) \/S HR_zero) (at level 5).
Notation "'abs' A" := (A \/S (-S A)) (at level 5).

(** Definition of the proposition stating if a formula is an atom *)
Definition is_atom A :=
  match A with
  | HR_var _ => True
  | HR_covar _ => True
  | _ => False
  end.

Lemma is_atom_complexity_0 : forall A,
    is_atom A -> HR_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_atom_complexity_0_inv : forall A,
    HR_complexity_term A = 0 -> is_atom A.
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
Qed.
