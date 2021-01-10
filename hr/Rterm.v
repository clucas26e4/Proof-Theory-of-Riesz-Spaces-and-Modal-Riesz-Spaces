(** * Definition of terms of Riesz spaces *)
Require Import Reals.

(** ** Term *)
Require Import RL.OLlibs.List_more.

Inductive Rterm : Type :=
| R_var : nat -> Rterm
| R_zero : Rterm
| R_plus : Rterm -> Rterm -> Rterm
| R_mul : R -> Rterm -> Rterm
| R_max : Rterm -> Rterm -> Rterm
| R_min : Rterm -> Rterm -> Rterm.

(** Notations *)

Notation "A +R B" := (R_plus A B) (at level 20, left associativity).
Notation "A \/R B" := (R_max A B) (at level 40, left associativity).
Notation "A /\R B" := (R_min A B) (at level 45, left associativity).
Notation "-R A" := (R_mul (-1) A) (at level 15).
Notation "A -R B" := (R_plus A (-R B)) (at level 10, left associativity).
Notation "r *R A" := (R_mul r A) (at level 15).

Fixpoint R_sum_term k A :=
  match k with
  | 0 => R_zero
  | 1 => A
  | S n => A +R (R_sum_term n A)
  end.

(** Substitution *)
Fixpoint Rsubs (t1 : Rterm) (x : nat) (t2 : Rterm) : Rterm :=
  match t1 with
  | R_var y => if (beq_nat x y) then t2 else R_var y
  | R_zero => R_zero
  | R_plus t t' => R_plus (Rsubs t x t2) (Rsubs t' x t2)
  | R_min t t' => R_min (Rsubs t x t2) (Rsubs t' x t2)
  | R_max t t' => R_max (Rsubs t x t2) (Rsubs t' x t2)
  | R_mul y t => R_mul y (Rsubs t x t2)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'R_pos' A" := (A \/R R_zero) (at level 5).
Notation "'R_neg' A" := ((-R A) \/R R_zero) (at level 5).
Notation "'R_abs' A" := (A \/R (-R A)) (at level 5).
