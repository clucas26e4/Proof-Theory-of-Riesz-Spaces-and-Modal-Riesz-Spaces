(** * Equational reasoning for Riesz Spaces *)
Require Import CMorphisms.
Require Import RL.hr.Rterm.

Require Import Reals.
Require Import Lra.

Local Open Scope R_scope.

(** ** Basic definitions needed for equational reasoning *)
(** Context *)
Inductive Rcontext : Type :=
| R_hole : Rcontext
| R_TC : Rterm -> Rcontext
| R_varC : nat -> Rcontext
| R_zeroC : Rcontext
| R_minC : Rcontext -> Rcontext -> Rcontext
| R_maxC : Rcontext -> Rcontext -> Rcontext
| R_plusC : Rcontext -> Rcontext -> Rcontext
| R_mulC : R -> Rcontext -> Rcontext.

Fixpoint evalRcontext (c : Rcontext) (t : Rterm) : Rterm :=
  match c with
  | R_hole => t
  | R_TC t' => t'
  | R_varC n => R_var n
  | R_zeroC => R_zero
  | R_minC c1 c2 => R_min (evalRcontext c1 t) (evalRcontext c2 t)
  | R_maxC c1 c2 => R_max (evalRcontext c1 t) (evalRcontext c2 t)
  | R_plusC c1 c2 => R_plus (evalRcontext c1 t) (evalRcontext c2 t)
  | R_mulC x c => R_mul x (evalRcontext c t)
  end.

(** ** Equational Reasoning *)
Inductive R_eqMALG : Rterm -> Rterm -> Type :=
(** equational rules *)
| R_refl t : R_eqMALG t t
| R_trans t1 t2 t3 : R_eqMALG t1 t2 -> R_eqMALG t2 t3 -> R_eqMALG t1 t3
| R_ctxt c t1 t2 : R_eqMALG t1 t2 -> R_eqMALG (evalRcontext c t1) (evalRcontext c t2)
| R_sym t1 t2 : R_eqMALG t1 t2 -> R_eqMALG t2 t1
| R_subs_r t1 t2 n t : R_eqMALG t1 t2 -> R_eqMALG (Rsubs t1 n t) (Rsubs t2 n t)
(** vector space axioms *)
| R_asso_plus t1 t2 t3 : R_eqMALG (t1 +R (t2 +R t3)) ((t1 +R t2) +R t3)
| R_commu_plus t1 t2 : R_eqMALG (t1 +R t2) (t2 +R t1)
| R_neutral_plus t : R_eqMALG (t +R R_zero) t
| R_opp_plus t : R_eqMALG (t -R t) R_zero
| R_mul_1 t  : R_eqMALG (1 *R t) t
| R_mul_assoc x y t : R_eqMALG (x *R (y *R t)) ((x * y) *R t)
| R_mul_distri_term x t1 t2 : R_eqMALG (x *R (t1 +R t2)) ((x *R t1) +R (x *R t2))
| R_mul_distri_coeff x y t : R_eqMALG ((x + y) *R t) ((x *R t) +R (y *R t))
(** lattice axioms *)
| R_asso_max t1 t2 t3 : R_eqMALG (R_max t1 (R_max t2 t3)) (R_max (R_max t1 t2) t3)
| R_commu_max t1 t2 : R_eqMALG (R_max t1 t2) (R_max t2 t1)
| R_abso_max t1 t2 : R_eqMALG (R_max t1 (R_min t1 t2)) t1
| R_asso_min t1 t2 t3 : R_eqMALG (R_min t1 (R_min t2 t3)) (R_min (R_min t1 t2) t3)
| R_commu_min t1 t2 : R_eqMALG (R_min t1 t2) (R_min t2 t1)
| R_abso_min t1 t2 : R_eqMALG (R_min t1 (R_max t1 t2)) t1
(** compability axiom *)
| R_compa_R_plus_ax t1 t2 t3 : R_eqMALG (R_min (R_plus (R_min t1 t2) t3) (R_plus t2 t3)) (R_plus (R_min t1 t2) t3)
| R_compa_mul_ax r t : 0 <= r -> R_eqMALG (R_min R_zero (R_mul r (R_max t R_zero))) R_zero.    

Notation "A =R= B" := (R_eqMALG A B) (at level 90, no associativity).
Notation "A <R= B" := (R_eqMALG (R_min A B) A) (at level 90, no associativity).

(** *** =R= is an equivalence relation **)

Instance R_eqMALG_Equivalence : Equivalence R_eqMALG | 10 := {
  Equivalence_Reflexive := R_refl ;
  Equivalence_Symmetric := R_sym ;
  Equivalence_Transitive := R_trans }.

(** *** Proofs of a equalities *)

Hint Constructors R_eqMALG : core.

Lemma cong_S : forall A B, A = B -> A =R= B.
Proof.
  intros A B eq.
  subst.
  reflexivity.
Qed.
Hint Resolve cong_S : core.

Lemma plus_left : forall A B C, A =R= C -> A +R B =R= C +R B.
Proof.
  intros A B C eq.
  apply (@R_ctxt (R_plusC R_hole (R_TC B))).
  apply eq.
Qed.

Lemma plus_right : forall A B C, B =R= C -> A +R B =R= A +R C.
Proof.
  intros A B C eq.
  apply (@R_ctxt (R_plusC (R_TC A) R_hole)).
  apply eq.
Qed.

Lemma plus_cong : forall A B C D, A =R= B -> C =R= D -> A +R C =R= B +R D.
Proof.
  intros A B C D eq1 eq2.
  transitivity (A +R D); [apply plus_right | apply plus_left]; assumption.
Qed.

Global Instance plus_cong_instance : Proper (R_eqMALG ==> R_eqMALG ==> R_eqMALG) R_plus | 10.
Proof. repeat intro; now apply plus_cong. Qed.

Lemma max_left : forall A B C, A =R= C -> A \/R B =R= C \/R B.
Proof.
  intros A B C eq.
  apply (@R_ctxt (R_maxC R_hole (R_TC B))).
  apply eq.
Qed.

Lemma max_right : forall A B C, B =R= C -> A \/R B =R= A \/R C.
Proof.
  intros A B C eq.
  apply (@R_ctxt (R_maxC (R_TC A) R_hole)).
  apply eq.
Qed.

Lemma max_cong : forall A B C D, A =R= B -> C =R= D -> A \/R C =R= B \/R D.
Proof.
  intros A B C D eq1 eq2.
  transitivity (A \/R D); [apply max_right | apply max_left]; assumption.
Qed.

Global Instance max_cong_instance : Proper (R_eqMALG ==> R_eqMALG ==> R_eqMALG) R_max | 10.
Proof. repeat intro; now apply max_cong. Qed.

Lemma min_left : forall A B C, A =R= C -> A /\R B =R= C /\R B.
Proof.
  intros A B C eq.
  apply (@R_ctxt (R_minC R_hole (R_TC B))).
  apply eq.
Qed.

Lemma min_right : forall A B C, B =R= C -> A /\R B =R= A /\R C.
Proof.
  intros A B C eq.
  apply (@R_ctxt (R_minC (R_TC A) R_hole)).
  apply eq.
Qed.

Lemma R_mul_left : forall x y A , x = y -> R_mul x A =R= R_mul y A.
Proof.
  intros x y A eq.
  rewrite eq.
  auto.
Qed.

Lemma min_cong : forall A B C D, A =R= B -> C =R= D -> A /\R C =R= B /\R D.
Proof.
  intros A B C D eq1 eq2.
  transitivity (A /\R D); [apply min_right | apply min_left]; assumption.
Qed.

Global Instance min_cong_instance : Proper (R_eqMALG ==> R_eqMALG ==> R_eqMALG) R_min | 10.
Proof. repeat intro; now apply min_cong. Qed.

Lemma R_mul_right : forall x A B , A =R= B -> R_mul x A =R= R_mul x B.
Proof.
  intros x A B eq.
  apply (@R_ctxt (R_mulC x R_hole)).
  apply eq.
Qed.

Global Instance R_mul_right_instance x : Proper (R_eqMALG ==> R_eqMALG) (R_mul x) | 10.
Proof. repeat intro; now apply R_mul_right. Qed.

Lemma minus_cong : forall A B , A =R= B -> -R A =R= -R B.
Proof.
  intros A B eq.
  apply (@R_ctxt (R_mulC (-1) R_hole)).
  assumption.
Qed.

Global Instance minus_cong_instance : Proper (R_eqMALG ==> R_eqMALG) (R_mul (-1)) | 10.
Proof. repeat intro; now apply minus_cong. Qed.

Hint Resolve plus_left plus_right max_left max_right min_left min_right minus_cong R_mul_left R_mul_right : core.

Lemma evalContext_cong : forall c t1 t2, t1 =R= t2 -> evalRcontext c t1 =R= evalRcontext c t2.
Proof.
  induction c; simpl; auto.
  all:intros t1 t2 eq; specialize (IHc1 t1 t2 eq); specialize (IHc2 t1 t2 eq); rewrite IHc1 ; now rewrite IHc2.
Qed.

Global Instance evalContext_cong_instance c : Proper (R_eqMALG ==> R_eqMALG) (evalRcontext c) | 10.
Proof. repeat intro; now apply evalContext_cong. Qed.

Lemma leq_compa_plus : forall A B C, (A /\R B) +R C <R= B +R C.
Proof.
  intros A B C.
  auto.
Qed.

Hint Resolve leq_compa_plus : Rsem_solver.

Lemma minus_distri : forall A B, -R (A +R B) =R= (-R A) +R (-R B).
Proof.
  intros A B.
  auto.
Qed.

Hint Resolve minus_distri : Rsem_solver.

Lemma minus_R_zero : R_zero =R= -R R_zero.
Proof.
  rewrite <- (R_neutral_plus ((-1) *R R_zero)).
  rewrite R_commu_plus.
  auto.
Qed.

Lemma minus_minus : forall A , -R (-R A) =R= A.
Proof with auto.
  intro A.
  rewrite<- R_neutral_plus.
  rewrite<- (R_opp_plus A).
  rewrite (R_commu_plus A (-R A)).
  rewrite R_asso_plus.
  rewrite (R_commu_plus (-R (-R A)) (-R A)).
  rewrite R_opp_plus.
  now rewrite R_commu_plus.
Qed.

Hint Resolve minus_R_zero : Rsem_solver.
Hint Resolve minus_minus : Rsem_solver.

Lemma leq_antisym : forall A B, A <R= B -> B <R= A -> A =R= B.
Proof with auto.
  intros A B eq1 eq2.
  apply R_trans with (B /\R A)...
  apply R_trans with (A /\R B)...
Qed.

Lemma leq_cong_l : forall A A' B, A =R= A' -> A' <R= B -> A <R= B.
Proof with auto.
  intros A A' B eq leq.
  apply R_trans with (A' /\R B)...
  apply R_trans with A'...
Qed.

Lemma leq_cong_r : forall A B B', B =R= B' -> A <R= B' -> A <R= B.
Proof with auto.
  intros A B B' eq leq.
  apply R_trans with (A /\R B')...
Qed.

Lemma leq_R_trans : forall A B C, A <R= B -> B <R= C -> A <R= C.
Proof with auto.
  intros A B C leq1 leq2.
  apply R_trans with ((A /\R B) /\R C)...
  apply R_trans with (A /\R (B /\R C))...
  apply R_trans with (A /\R B)...
Qed.

Lemma leq_plus : forall A B C, A <R= B -> (A +R C) <R= (B +R C).
Proof with auto.
  intros A B C leq.
  apply leq_cong_l with ((A /\R B) +R C)...
Qed.

Hint Resolve leq_plus : Rsem_solver.

Lemma min_max : forall A B , (A /\R B) =R= A -> (A \/R B) =R= B.
Proof with auto.
  intros A B eq.
  apply R_trans with ((A /\R B) \/R B)...
  apply R_trans with ((B /\R A) \/R B)...
  apply R_trans with (B \/R (B /\R A))...
Qed.

Lemma max_min : forall A B , (A \/R B) =R= A -> (A /\R B) =R= B.
Proof with auto.
  intros A B eq.
  apply R_trans with ((A \/R B) /\R B)...
  apply R_trans with ((B \/R A) /\R B)...
  apply R_trans with (B /\R (B \/R A))...
Qed.

Hint Resolve max_min min_max : Rsem_solver.

Lemma leq_refl_cong : forall A B, ((A /\R A) /\R B) =R= A /\R B.
Proof with auto with *.
  intros A B.
  apply R_trans with (A /\R (A /\R B))...
Qed.

Lemma leq_refl : forall A , A /\R A =R= A.
Proof with auto.
  intro A.
  apply R_trans with (A /\R (A /\R (A \/R A)))...
  apply R_trans with ((A /\R A) /\R (A \/R A))...
  apply R_trans with (A /\R (A \/R A)); auto using leq_refl_cong.
Qed.

Hint Resolve leq_refl : Rsem_solver.

Lemma leq_min : forall A B C, A <R= B -> A <R= C -> A <R= (B /\R C).
Proof with auto.
  intros A B C leq1 leq2.
  apply R_trans with ((A /\R B) /\R C)...
  apply R_trans with (A /\R C)...
Qed.

Lemma leq_max : forall A B , A <R= (A \/R B).
Proof with auto.
  intros A B.
  auto.
Qed.

Lemma min_leq : forall A B, (A /\R B) <R= A.
Proof with auto with *.
  intros A B.
  apply R_trans with (A /\R (A /\R B))...
Qed.

Lemma max_leq : forall A B C, A <R= C -> B <R= C -> (A \/R B) <R= C.
Proof with auto with *.
  intros A B C leq1 leq2.
  apply R_trans with (C /\R (A \/R B))...
  apply max_min.
  apply R_trans with ((A \/R B) \/R C)...
  apply R_trans with (A \/R (B \/R C))...
  apply R_trans with (A \/R C)...
Qed.

Hint Resolve leq_max min_leq min_leq max_leq : Rsem_solver.

Lemma leq_plus_left : forall A B C, A <R= B -R C -> A +R C <R= B.
Proof with auto with *.
  intros A B C leq.
  apply leq_cong_r with (B +R (-R C) +R C)...
  apply R_trans with (B +R ((-R C) +R C))...
  apply R_trans with (B +R (C -R C))...
  apply R_trans with (B +R R_zero)...
Qed.

Lemma leq_plus_right : forall A B C, A -R B <R= C -> A <R= C +R B.
Proof with auto with *.
  intros A B C leq.
  apply leq_cong_l with ( A -R B +R B)...
  apply R_trans with (A +R R_zero)...
  apply R_trans with (A +R (B -R B))...
  apply R_trans with (A +R ((-R B) +R B))...
Qed.

Lemma leq_minus_left : forall A B C, A <R= B +R C -> A -R C <R= B.
Proof with auto.
  intros A B C leq.
  apply leq_plus_left...
  apply R_trans with (A /\R (B +R C)); auto using minus_minus.
Qed.

Lemma leq_minus_right : forall A B C , A +R C <R= B -> A <R= B -R C.
Proof with auto.
  intros A B C leq.
  apply leq_plus_right.
  apply R_trans with ((A +R C) /\R B); auto using minus_minus.
  apply R_trans with (A +R C); auto using minus_minus.
Qed.
  
Lemma max_plus : forall A B C, ((A \/R B) +R C) =R= (A +R C) \/R (B +R C).
Proof with auto.
  intros A B C.
  apply leq_antisym.
  - apply leq_plus_left.
    apply max_leq.
    + apply leq_minus_right...
    + apply leq_minus_right...
      apply R_trans with ((B +R C) /\R ((B +R C) \/R (A +R C)))...
  - apply max_leq; auto using leq_plus.
    apply leq_plus_right.
    apply leq_cong_l with B.
      * apply R_trans with (B +R (C -R C))...
        apply R_trans with (B +R R_zero)...
      * apply leq_cong_r with (B \/R A)...
Qed.

Hint Resolve max_plus : Rsem_solver.

Lemma minus_reverse_leq : forall A B, B <R= A -> (-R A) <R= (-R B).
Proof with auto.
  intros A B leq.
  apply leq_cong_r with (-R B +R R_zero)...
  apply leq_cong_r with (R_zero -R B)...
  apply leq_minus_right.
  apply leq_cong_l with (B -R A)...
  apply leq_minus_left.
  apply leq_cong_r with (A +R R_zero)...
  apply leq_cong_r with A...
Qed.

Hint Resolve minus_reverse_leq : Rsem_solver.

Lemma minus_min_max : forall A B, -R (A /\R B) =R= (-R A) \/R (-R B).
Proof with auto with Rsem_solver.
  intros A B.
  apply leq_antisym.
  - apply leq_cong_r with (-R (-R ((-R A) \/R (-R B))))...
    apply minus_reverse_leq.
    apply leq_min.
    + apply leq_cong_r with (-R (-R A))...
    + apply leq_cong_r with (-R (-R B))...
      apply leq_cong_l with (-R (-R B \/R -R A))...
  - apply max_leq.
    + apply minus_reverse_leq...
    + apply leq_cong_r with (-R (B /\R A))...
Qed.

Lemma min_leq_max : forall A B, A /\R B <R= A \/R B.
Proof with auto with Rsem_solver.
  intros A B.
  apply leq_R_trans with A...
Qed.

Hint Resolve minus_min_max min_leq_max : Rsem_solver.

Lemma minus_inj : forall A B, -R A =R= -R B -> A =R= B.
Proof with auto with Rsem_solver.
  intros A B eq.
  apply R_trans with (-R (-R A))...
  apply R_trans with (-R (-R B))...
Qed.

Lemma leq_plus_cong : forall A B C D, A <R= B -> C <R= D -> A +R C <R= B +R D.
Proof with auto with Rsem_solver.
  intros A B C D leq1 leq2.
  apply leq_R_trans with (B +R C)...
  apply leq_cong_l with (C +R B)...
  apply leq_cong_r with (D +R B)...
Qed.

Hint Resolve leq_plus_cong : Rsem_solver.

Lemma cond_leq : forall A B, R_zero <R= (A -R B) -> B <R= A.
Proof with auto with Rsem_solver.
  intros A B Hleq.
  apply leq_cong_r with ((A -R B) +R B).
  { apply R_trans with (A +R R_zero)...
    apply R_trans with (A +R (B -R B))...
    apply R_trans with (A +R ((-R B) +R B))... }
  apply leq_cong_l with (R_zero +R B)...
  apply R_trans with (B +R R_zero)...
Qed.

Lemma cond_leq_inv : forall A B, B <R= A -> R_zero <R= (A -R B).
Proof with auto with Rsem_solver.
  intros A B Hleq.
  apply leq_cong_l with (B -R B)...
Qed.

Lemma eq_minus : forall A B, A =R= B -> A -R B =R= R_zero.
Proof with auto with Rsem_solver.
  intros A B eq.
  apply R_trans with (B -R B)...
Qed.

Hint Resolve eq_minus : Rsem_solver.

Lemma minus_eq : forall A B, A -R B =R= R_zero -> A =R= B.
Proof with auto with Rsem_solver.
  intros A B eq.
  apply R_trans with (A +R R_zero)...
  apply R_trans with (A +R (B -R B))...
  apply R_trans with (A +R ((-R B) +R B))...
  apply R_trans with (A -R B +R B)...
  apply R_trans with (R_zero +R B)...
  apply R_trans with (B +R R_zero)...
Qed.

Lemma R_minus_mul : forall r A, -R (r *R A) =R= r *R (-R A).
Proof with auto with Rsem_solver.
  intros r A.
  rewrite R_mul_assoc.
  replace (-1 * r) with (r * -1) by lra.
  rewrite R_mul_assoc.
  reflexivity.
Qed.

Hint Resolve R_minus_mul : Rsem_solver.
                     
Lemma R_mul_compa : forall r A B, (0 <= r) -> A <R= B -> (r *R A) <R= (r *R B).
Proof with auto with Rsem_solver.
  intros r A B Hleqr HleqAB.
  apply cond_leq.
  apply leq_cong_r with ((r *R ((B -R A) \/R R_zero))).
  { apply R_trans with ((r *R B) +R (r *R (-R A)))...
    apply R_trans with (r *R (B -R A))...
    apply R_mul_right.
    apply R_sym.
    apply R_trans with (R_zero \/R (B -R A))...
    apply min_max.
    apply cond_leq_inv...
  }
  apply R_compa_mul_ax...
Qed.

Hint Resolve R_mul_compa : Rsem_solver.

Lemma R_mul_0 :  forall r, r *R R_zero =R= R_zero.
Proof with auto with Rsem_solver.
  intro r.
  transitivity (r *R (R_zero +R R_zero))...
  transitivity (r *R R_zero +R r *R R_zero)...
  transitivity (r *R R_zero +R r *R (-R R_zero))...
  transitivity (r *R R_zero +R (-R (r *R R_zero)))...
Qed.

Hint Resolve R_mul_0 : Rsem_solver.  

Lemma no_div_R_zero : forall r A, r <> 0 -> r *R A =R= R_zero -> A =R= R_zero.
Proof with auto with Rsem_solver.
  intros r A Hr eq.
  transitivity (1 *R A)...
  transitivity ((/ r * r) *R A)...
  { apply R_mul_left.
    symmetry.
    apply Rinv_l... }
  apply R_trans with ((/ r) *R (r *R A))...
  apply R_trans with ((/ r) *R R_zero)...
Qed.

Lemma R_mul_distri_minus : forall k A B, (k *R A) -R (k *R B) =R= k *R (A -R B).
Proof with auto with Rsem_solver.
  intros k A B.
  apply R_trans with ((k *R A) +R (k *R (-R B)))...
Qed.  

Lemma minus_max_min : forall A B, -R (A \/R B) =R= (-R A) /\R (-R B).
Proof with auto with Rsem_solver.
  intros A B.
  apply R_trans with (-R (A \/R (-R (-R B))))...
  apply R_trans with (-R ((-R (-R A)) \/R (-R (-R B))))...
  apply R_trans with (-R (-R ((-R A) /\R (-R B))))...
Qed.

Hint Resolve R_mul_distri_minus minus_max_min : Rsem_solver.

Lemma R_zero_leq_pos : forall A , R_zero <R= R_pos A.
Proof with auto with Rsem_solver.
  intro A.
  apply leq_cong_r with (R_zero \/R A)...
Qed.

Lemma R_zero_leq_neg : forall A , R_zero <R= R_neg A.
Proof with auto with Rsem_solver.
  intro A.
  apply leq_cong_r with (R_zero \/R (-R A))...
Qed.

Hint Resolve R_zero_leq_pos R_zero_leq_neg : Rsem_solver.

Lemma eq_minus_right : forall A B C, A +R C =R= B -> A =R= B -R C.
Proof with auto with Rsem_solver.
  intros A B C eq.
  apply R_trans with (A +R R_zero)...
  apply R_trans with (A +R (C -R C))...
  apply R_trans with ((A +R C) -R C)...
Qed.

Lemma eq_plus_right : forall A B C, A -R C =R= B -> A =R= B +R C.
Proof with auto with Rsem_solver.
  intros A B C eq.
  apply R_trans with (A +R R_zero)...
  apply R_trans with (A +R (C -R C))...
  apply R_trans with (A +R ((-R C) +R C))...
  apply R_trans with ((A -R C) +R C)...
Qed.

Lemma decomp_pos_neg : forall A, A =R= (R_pos A) -R (R_neg A).
Proof with auto with Rsem_solver.
  intros A.
  apply eq_minus_right.
  apply R_trans with (A \/R (A -R A))...
  apply R_trans with ((A +R R_zero) \/R (A -R A))...
  apply R_trans with ((R_zero +R A) \/R (A -R A))...
  apply R_trans with ((A -R A) \/R (R_zero +R A))...
  apply R_trans with (((-R A) +R A) \/R (R_zero +R A))...
  apply R_trans with (R_neg A +R A)...
Qed.

Hint Resolve decomp_pos_neg : Rsem_solver.

Lemma pos_neg : forall A, R_pos A =R= A +R (R_neg A).
Proof.
  intros A.
  apply R_trans with ((R_pos A -R R_neg A) +R R_neg A); auto using eq_plus_right with Rsem_solver.
Qed.

Lemma neg_pos : forall A , R_neg A =R= (R_pos A) -R A.
Proof with auto with Rsem_solver.
  intros A.
  apply eq_minus_right...
  apply R_trans with (A +R R_neg A); auto using eq_plus_right with Rsem_solver.
Qed.

Hint Resolve pos_neg neg_pos : Rsem_solver.
  
Lemma min_plus : forall A B C, (A /\R B) +R C =R= (A +R C) /\R (B +R C).
Proof with auto with Rsem_solver.
  intros A B C.
  apply R_trans with (-R (-R ((A +R C) /\R (B +R C))))...
  apply R_trans with (-R ((-R (A +R C)) \/R (-R (B +R C))))...
  apply R_trans with (-R (((-R A) -R C) \/R ((-R (B +R C)))))...
  apply R_trans with (-R (((-R A) -R C) \/R (((-R B) -R C))))...
  apply R_trans with (-R (((-R A) \/R ((-R B))) -R C))...
  apply R_trans with ((-R (((-R A) \/R ((-R B))))) -R (-R C))...
  apply R_trans with ((-R (((-R A) \/R ((-R B))))) +R C)...
  apply R_trans with (((-R (-R A)) /\R ((-R (-R B)))) +R C)...
  apply R_trans with ((A /\R ((-R (-R B)))) +R C)...
Qed.

Hint Resolve min_plus : Rsem_solver.

Lemma min_pos_neg : forall A, (R_pos A) /\R (R_neg A) =R= R_zero.
Proof with auto with Rsem_solver.
  intros A.
  apply R_trans with ((A +R (R_neg A)) /\R (R_neg A))...
  apply R_trans with ((A +R (R_neg A)) /\R (R_neg A +R R_zero))...
  apply R_trans with ((A +R (R_neg A)) /\R (R_zero +R R_neg A))...
  apply R_trans with ((A /\R R_zero) +R R_neg A)...
  apply R_trans with ( (-R (-R (A /\R R_zero))) +R R_neg A)...
  apply R_trans with ( (-R ((-R A) \/R (-R R_zero))) +R R_neg A)...
  apply R_trans with ( (-R (R_neg A)) +R R_neg A)...
  apply R_trans with (R_neg A -R R_neg A)...
Qed.

Hint Resolve min_pos_neg : Rsem_solver.

Lemma cond_R_zero_leq_max : forall A B,
    (A \/R B) =R= (R_pos A \/R R_pos B) -> R_zero <R= A \/R B.
Proof with auto with Rsem_solver.
  intros A B eq.
  apply R_trans with ((A \/R B) /\R R_zero)...
  apply max_min.
  apply R_trans with ((A \/R B) \/R (R_zero \/R R_zero))...
  apply R_trans with (A \/R (B \/R (R_zero \/R R_zero)))...
  apply R_trans with (A \/R (R_pos B \/R R_zero))...
  apply R_trans with (A \/R (R_zero \/R R_pos B))...
  apply R_trans with (R_pos A \/R R_pos B)...
Qed.

Lemma cond_eq_pos : forall A B,
    R_zero <R= A \/R B -> (A \/R B) =R= (R_pos A \/R R_pos B).
Proof with auto with Rsem_solver.
  intros A B eq.
  apply R_trans with (A \/R (R_zero \/R R_pos B))...
  apply R_trans with (A \/R (R_pos B \/R R_zero))...
  apply R_trans with (A \/R (B \/R (R_zero \/R R_zero)))...
  apply R_trans with ((A \/R B) \/R (R_zero \/R R_zero))...
  apply R_trans with (A \/R B \/R R_zero)...
  apply R_trans with (R_zero \/R (A \/R B))...
Qed.

Lemma max_pos : forall A B, A \/R B =R= (R_pos (A -R B)) +R B.
Proof with auto with Rsem_solver.
  intros A B.
  apply R_trans with ((A +R R_zero) \/R B)...
  apply R_trans with ((A +R (B -R B)) \/R B)...
  apply R_trans with ((A +R ((-R B) +R B)) \/R B)...
  apply R_trans with ((A +R (-R B) +R B) \/R B)...
  apply R_trans with ((A +R (-R B) +R B) \/R (B +R R_zero))...
  apply R_trans with ((A +R (-R B) +R B) \/R (R_zero +R B))...
Qed.

Hint Resolve max_pos : Rsem_solver.

Lemma min_pos : forall A B, A /\R B =R= A -R (R_pos (A -R B)).
Proof with auto with Rsem_solver.
  intros A B.
  apply eq_minus_right.
  apply R_trans with ((R_pos (A -R B)) +R (A /\R B))...
  apply R_sym.
  apply eq_plus_right.
  apply R_trans with (A +R ((-R A) \/R (-R B)))...
  apply R_trans with (((-R A) \/R (-R B)) +R A)...
  apply R_trans with (((-R A) +R A) \/R ((-R B) +R A))...
  apply R_trans with ((A -R A) \/R ((-R B) +R A))...
  apply R_trans with (R_zero \/R ((-R B) +R A))...
  apply R_trans with (R_zero \/R (A -R B))...
Qed.

Hint Resolve min_pos : Rsem_solver.

Lemma min_max_plus : forall A B, (A \/R B) +R (A /\R B) =R= A +R B.
Proof with auto with Rsem_solver.
  intros A B.
  apply R_trans with (((R_pos (A -R B)) +R B) +R (A /\R B))...
  apply R_trans with (((R_pos (A -R B)) +R B) +R (A -R (R_pos (A -R B))))...
  apply R_trans with ((B +R (R_pos (A -R B))) +R (A -R (R_pos (A -R B))))...
  apply R_trans with (B +R ((R_pos (A -R B)) +R (A -R (R_pos (A -R B)))))...
  apply R_trans with (B +R ((R_pos (A -R B)) +R ((-R (R_pos (A -R B))) +R A)))...
  apply R_trans with (B +R ((R_pos (A -R B)) +R (-R (R_pos (A -R B))) +R A))...
  apply R_trans with (B +R (R_zero +R A))...
  apply R_trans with (B +R (A +R R_zero))...
  apply R_trans with (B +R A)...
Qed.

Hint Resolve min_max_plus : Rsem_solver.

Lemma max_distri_min : forall A B C, (A /\R B) \/R C =R= (A \/R C) /\R (B \/R C).
Proof with auto with Rsem_solver.
  intros A B C.
  remember ((A \/R C) /\R (B \/R C)) as m.
  apply leq_antisym.
  - apply leq_cong_r with (A \/R C /\R B \/R C)...
    apply leq_min.
    + apply max_leq.
      * apply leq_R_trans with A...
      * apply leq_cong_r with (C \/R A)...
    + apply max_leq...
      * apply leq_R_trans with B...
        apply leq_cong_l with (B /\R A)...
      * apply leq_cong_r with (C \/R B)...
  - apply leq_cong_r with ((A /\R B) -R ((-R C) +R ((A /\R B) /\R C)))...
    + apply R_trans with ((A /\R B) +R ((-R (-R C)) -R ((A /\R B) /\R C)))...
      apply R_trans with ((A /\R B) +R (C -R ((A /\R B) /\R C)))...
      apply R_trans with (((A /\R B) +R C) -R ((A /\R B) /\R C)); auto using eq_minus_right with Rsem_solver.
    + apply leq_minus_right...
      apply leq_min...
      * apply leq_cong_l with ((m +R ((A /\R B) /\R C)) -R C)...
        ** apply R_trans with (m +R (((A /\R B) /\R C) -R C))...
        ** apply leq_cong_r with ((A +R C) -R C); auto using eq_minus_right with Rsem_solver.
           apply leq_plus.
           apply leq_cong_r with ((A \/R C) +R (A /\R C))...
           apply leq_R_trans with (m +R (A /\R C))...
           *** apply leq_plus_cong...
               apply leq_cong_l with (A /\R (B /\R C))...
               apply leq_cong_l with (A /\R (C /\R B))...
               apply leq_cong_l with (A /\R C /\R B)...
           *** apply leq_plus_cong...
               apply leq_cong_l with (A \/R C /\R B \/R C)...
      * apply leq_cong_l with (m +R ((A /\R B /\R C) -R C))...
        apply leq_cong_l with ((m +R (A /\R B /\R C)) -R C)...
        apply leq_cong_r with (B +R R_zero)...
        apply leq_cong_r with (B +R (C -R C))...
        apply leq_cong_r with ((B +R C) -R C)...
        apply leq_plus...
        apply leq_cong_r with ((B \/R C) +R (B /\R C))...
        apply leq_plus_cong...
        apply leq_cong_l with (A \/R C /\R B \/R C)...
        ** apply leq_cong_l with (B \/R C /\R A \/R C)...
        ** apply leq_cong_l with (A /\R (B /\R C))...
           apply leq_cong_l with ((B /\R C) /\R A)...
Qed.

Hint Resolve max_distri_min : Rsem_solver.

Lemma min_distri_max : forall A B C, (A \/R B) /\R C =R= (A /\R C) \/R (B /\R C).
Proof with auto with Rsem_solver.
  intros A B C.
  apply R_trans with (-R (-R (A \/R B /\R C)))...
  apply R_trans with (-R ((-R (A \/R B) \/R (-R C))))...
  apply R_trans with (-R (((-R A) /\R (-R B)) \/R (-R C)))...
  apply R_trans with (-R (((-R A) \/R (-R C)) /\R ((-R B) \/R (-R C))))...
  apply R_trans with ((-R ((-R A) \/R (-R C))) \/R (-R ((-R B) \/R (-R C))))...
  apply R_trans with (((-R (-R A)) /\R (-R (-R C))) \/R (-R ((-R B) \/R (-R C))))...
  apply R_trans with (((-R (-R A)) /\R (-R (-R C))) \/R ((-R (-R B)) /\R (-R (-R C))))...
  apply R_trans with ((A /\R (-R (-R C))) \/R ((-R (-R B)) /\R (-R (-R C))))...
  apply R_trans with ((A /\R C) \/R ((-R (-R B)) /\R (-R (-R C))))...
  apply R_trans with ((A /\R C) \/R (B /\R (-R (-R C))))...
Qed.

Hint Resolve min_distri_max : Rsem_solver.

Lemma decomp_max_pos_neg : forall A B, A \/R B =R= ((R_pos A) \/R (R_pos B)) -R ((R_neg A) /\R (R_neg B)).
Proof with auto with Rsem_solver.
  intros A B.
  apply R_trans with (R_pos (A \/R B) -R (R_neg (A \/R B)))...
  apply R_trans with ((R_pos A \/R R_pos B) -R (R_neg (A \/R B))).
  - apply (@R_ctxt (R_plusC R_hole (R_mulC (-1) (R_TC (R_neg (A \/R B)))))).
    apply R_trans with (A \/R B \/R (R_zero \/R R_zero))...
    apply R_trans with (A \/R (B \/R R_pos R_zero))...
    apply R_trans with (A \/R (R_pos B \/R R_zero))...
    apply R_trans with (A \/R (R_zero \/R R_pos B))...
  - apply R_trans with ((R_pos A \/R R_pos B) -R (((-R A) /\R (-R B)) \/R R_zero))...
Qed.

Hint Resolve decomp_max_pos_neg : Rsem_solver.

Lemma cond_R_zero_leq_max_2 : forall A B, (R_neg A) /\R (R_neg B) =R= R_zero -> R_zero <R= A \/R B.
Proof with auto with Rsem_solver.
  intros A B eq.
  apply cond_R_zero_leq_max...
  apply R_trans with ((R_pos A \/R R_pos B) +R R_zero)...
  apply R_trans with ((R_pos A \/R R_pos B) -R R_zero)...
  apply R_trans with ((R_pos A \/R R_pos B) -R (R_neg A /\R R_neg B))...
Qed.

Lemma cond_min_R_neg_eq_R_zero : forall A B, R_zero <R= A \/R B -> (R_neg A) /\R (R_neg B) =R= R_zero.
Proof with auto with Rsem_solver.
  intros A B leq.
  apply R_trans with (((R_pos A) \/R (R_pos B)) -R (A \/R B)); auto using eq_minus_right, cond_eq_pos with Rsem_solver.
  apply eq_minus_right...
  apply R_trans with ((A \/R B) +R (R_neg A /\R R_neg B)); auto using eq_plus_right with Rsem_solver.
Qed.

Lemma R_zero_leq_abs : forall A, R_zero <R= R_abs A.
Proof with auto with Rsem_solver.
  intro A.
  apply cond_R_zero_leq_max_2.
  apply R_trans with ((R_neg A) /\R (R_pos A))...
  apply R_trans with ((R_pos A) /\R (R_neg A))...
Qed.

Hint Resolve R_zero_leq_abs : Rsem_solver.
