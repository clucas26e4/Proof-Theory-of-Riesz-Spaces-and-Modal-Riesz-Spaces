(** * Definition of the system HR *)
Require Import Rpos.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.

Require Import CMorphisms.
Require Import List.
Require Import Lra.

Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** ** Fragments of the system HR, i.e. whether we can use the T rule, the M rule or the CAN rule *)
Record hr_frag := mk_hr_frag {
                      hr_T : bool;
                      hr_M : bool;
                      hr_CAN : bool }.

Definition le_hr_frag P Q :=
  prod (Bool.le (hr_T P) (hr_T Q))
       (prod (Bool.le (hr_M P) (hr_M Q))
             (Bool.le (hr_CAN P) (hr_CAN Q))).

Lemma le_hr_frag_trans : forall P Q R,
  le_hr_frag P Q -> le_hr_frag Q R -> le_hr_frag P R.
Proof.
intros P Q R H1 H2.
destruct H1 as (Ht1 & Hm1 & Hcan1).
destruct H2 as (Ht2 & Hm2 & Hcan2).
repeat split; destruct P; destruct Q; destruct R; Bool.destr_bool.
Qed.

Instance le_hr_frag_po : PreOrder le_hr_frag.
Proof.
split.
- repeat split; destruct x; Bool.destr_bool.
- intros P Q R.
  apply le_hr_frag_trans.
Qed.

Definition hr_frag_add_T P := mk_hr_frag true (hr_M P) (hr_CAN P).
Definition hr_frag_rm_T P := mk_hr_frag false (hr_M P) (hr_CAN P).
Definition hr_frag_add_M P := mk_hr_frag (hr_T P) true (hr_CAN P).
Definition hr_frag_rm_M P := mk_hr_frag (hr_T P) false (hr_CAN P).
Definition hr_frag_add_CAN P := mk_hr_frag (hr_T P) (hr_M P) true.
Definition hr_frag_rm_CAN P := mk_hr_frag (hr_T P) (hr_M P) false.

Lemma add_T_le_frag : forall P, le_hr_frag P (hr_frag_add_T P).
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma add_M_le_frag : forall P, le_hr_frag P (hr_frag_add_M P).
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma add_CAN_le_frag : forall P, le_hr_frag P (hr_frag_add_CAN P).
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma rm_T_le_frag : forall P, le_hr_frag (hr_frag_rm_T P) P.
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma rm_M_le_frag : forall P, le_hr_frag (hr_frag_rm_M P) P.
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma rm_CAN_le_frag : forall P, le_hr_frag (hr_frag_rm_CAN P) P.
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.

(** only the following fragments are interesting for what we want to do *)
Definition hr_frag_M_can := (mk_hr_frag false true true).
Definition hr_frag_full := (mk_hr_frag true true true).
Definition hr_frag_T_M := (mk_hr_frag true true false).
Definition hr_frag_T := (mk_hr_frag true false false).
Definition hr_frag_M := (mk_hr_frag false true false).
Definition hr_frag_nothing := (mk_hr_frag false false false).

(** * Definition of hr *)
(** ** HR *)

Inductive HR P : hypersequent -> Type :=
| hrr_INIT : HR P (nil :: nil)
| hrr_W : forall G T, HR P G -> HR P (T :: G)
| hrr_C : forall G T, HR P (T :: T :: G) -> HR P (T :: G)
| hrr_S : forall G T1 T2, HR P ((T1 ++ T2) :: G) -> HR P (T1 :: T2 :: G)
| hrr_M {f : hr_M P = true} : forall G T1 T2, HR P (T1 :: G) -> HR P (T2 :: G) -> HR P ((T1 ++ T2) :: G)
| hrr_T {f : hr_T P = true} : forall G T r, HR P (seq_mul r T :: G) -> HR P (T :: G)
| hrr_ID : forall G T n r s, sum_vec r = sum_vec s -> HR P (T :: G) -> HR P ((vec s (HR_covar n) ++ vec r (HR_var n) ++ T) :: G)
| hrr_Z : forall G T r, HR P (T :: G) -> HR P ((vec r HR_zero ++ T) :: G)

| hrr_plus : forall G T A B r, HR P ((vec r A ++ vec r B ++ T) :: G) -> HR P ((vec r (A +S B) ++ T) :: G)
| hrr_mul : forall G T A r0 r, HR P ((vec (mul_vec r0 r) A ++ T) :: G) -> HR P ((vec r (r0 *S A) ++ T) :: G)
| hrr_max : forall G T A B r, HR P ((vec r B ++ T) :: (vec r A ++ T) :: G) -> HR P ((vec r (A \/S B) ++ T) :: G)
| hrr_min : forall G T A B r, HR P ((vec r A ++ T) :: G) -> HR P ((vec r B ++ T) :: G) -> HR P ((vec r (A /\S B) ++ T) :: G)
| hrr_ex_seq : forall G T1 T2, Permutation_Type T1 T2 -> HR P (T1 :: G) -> HR P (T2 :: G)
| hrr_ex_hseq : forall G H, Permutation_Type G H -> HR P G -> HR P H
| hrr_can {f : hr_CAN P = true} : forall G T A r s, sum_vec r = sum_vec s -> HR P ((vec s (-S A) ++ vec r A ++ T) :: G) -> HR P (T :: G).

(** HR with only can and M *)
Definition HR_M_can := HR hr_frag_M_can.
(** HR with every rule *)
Definition HR_full := HR hr_frag_full.
(** HR without the CAN rule *)
Definition HR_T_M := HR hr_frag_T_M.
(** HR with neither the CAN rule nor the M rule *)
Definition HR_T := HR hr_frag_T.
(** HR with only the M rule*)
Definition HR_M := HR hr_frag_M.
(** HR with neither the CAN rule nor the M rule nor the T rule*)
Definition HR_nothing := HR hr_frag_nothing.

(** ** Some basic properties for the system HR *)
Lemma HR_not_empty P : forall G, HR P G -> G <> nil.
Proof.
  intros G pi; induction pi; (try now auto).
  intros Heq; apply IHpi; apply Permutation_Type_nil.
  symmetry; now rewrite <- Heq.
Qed.

(** if we add some rules, we keep the derivability (for instance, a hypersequent provable without the T rule is provable with the T rule) *)
Lemma HR_le_frag : forall P Q,
    le_hr_frag P Q ->
    forall G, HR P G -> HR Q G.
Proof.
  intros P Q Hle G pi.
  induction pi;  destruct P as [HTP HMP HCANP]; destruct Q as [HTQ HMQ HCANQ]; destruct Hle as [HleT [HleM HleCAN]]; simpl in *; subst; try (now constructor).
  - apply hrr_T with r; assumption.
  - apply hrr_ex_seq with T1; assumption.
  - apply hrr_ex_hseq with G; assumption.
  - apply hrr_can with A r s; try assumption; try reflexivity.
Qed.

(** some others derivable rules *)
Lemma hrr_W_gen P : forall G H, HR P G -> HR P (H ++ G).
Proof.
  intros G H; revert G; induction H; intros G pi.
  - auto.
  - simpl; apply hrr_W; apply IHlist; apply pi.
Qed.

Lemma hrr_C_gen P : forall G H, HR P (H ++ H ++ G) -> HR P (H ++ G).
Proof.
  intros G H; revert P G; induction H as [ | T H]; intros P G pi.
  - apply pi.
  - simpl; apply hrr_C; try reflexivity.
    apply hrr_ex_hseq with (H ++ T :: T :: G); [ Permutation_Type_solve | ].
    apply IHH.
    eapply hrr_ex_hseq ; [ | apply pi].
    Permutation_Type_solve.
Qed.

Lemma hrr_C_copy P : forall G T n, HR P ((copy_seq (S n) T) :: G) -> HR P (T :: G).
Proof.
  intros G T n; revert G T; induction n; intros G T pi; simpl in *; try assumption.
  apply hrr_C.
  apply IHn.
  apply hrr_S.
  apply pi.
Qed.
