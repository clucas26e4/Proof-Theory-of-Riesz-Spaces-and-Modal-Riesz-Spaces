(** * Definition of the system HR *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** ** Fragments of the system HMR, i.e. whether we can use the T rule, the M rule or the CAN rule *)
Record hmr_frag := mk_hmr_frag {
                      hmr_T : bool;
                      hmr_M : bool;
                      hmr_CAN : bool }.

Definition le_hmr_frag P Q :=
  prod (Bool.le (hmr_T P) (hmr_T Q))
       (prod (Bool.le (hmr_M P) (hmr_M Q))
             (Bool.le (hmr_CAN P) (hmr_CAN Q))).

Lemma le_hmr_frag_trans : forall P Q R,
  le_hmr_frag P Q -> le_hmr_frag Q R -> le_hmr_frag P R.
Proof.
intros P Q R H1 H2.
destruct H1 as (Ht1 & Hm1 & Hcan1).
destruct H2 as (Ht2 & Hm2 & Hcan2).
repeat split; destruct P; destruct Q; destruct R; Bool.destr_bool.
Qed.

Instance le_hmr_frag_po : PreOrder le_hmr_frag.
Proof.
split.
- repeat split; destruct x; Bool.destr_bool.
- intros P Q R.
  apply le_hmr_frag_trans.
Qed.

Definition hmr_frag_add_T P := mk_hmr_frag true (hmr_M P) (hmr_CAN P).
Definition hmr_frag_rm_T P := mk_hmr_frag false (hmr_M P) (hmr_CAN P).
Definition hmr_frag_add_M P := mk_hmr_frag (hmr_T P) true (hmr_CAN P).
Definition hmr_frag_rm_M P := mk_hmr_frag (hmr_T P) false (hmr_CAN P).
Definition hmr_frag_add_CAN P := mk_hmr_frag (hmr_T P) (hmr_M P) true.
Definition hmr_frag_rm_CAN P := mk_hmr_frag (hmr_T P) (hmr_M P) false.
  
Lemma add_T_le_frag : forall P, le_hmr_frag P (hmr_frag_add_T P).
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma add_M_le_frag : forall P, le_hmr_frag P (hmr_frag_add_M P).
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma add_CAN_le_frag : forall P, le_hmr_frag P (hmr_frag_add_CAN P).
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma rm_T_le_frag : forall P, le_hmr_frag (hmr_frag_rm_T P) P.
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.
Lemma rm_M_le_frag : forall P, le_hmr_frag (hmr_frag_rm_M P) P.
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.

Lemma rm_CAN_le_frag : forall P, le_hmr_frag (hmr_frag_rm_CAN P) P.
Proof.
  intros P.
  repeat split; destruct P; Bool.destr_bool.
Qed.

(** only the following fragments are interesting for what we want to do *)
Definition hmr_frag_M_can := (mk_hmr_frag false true true).
Definition hmr_frag_full := (mk_hmr_frag true true true).
Definition hmr_frag_T_M := (mk_hmr_frag true true false).
Definition hmr_frag_T := (mk_hmr_frag true false false).
Definition hmr_frag_M := (mk_hmr_frag false true false).
Definition hmr_frag_nothing := (mk_hmr_frag false false false).


(** * Definition of HMR *)
(** ** HMR *)

Inductive HMR P : hypersequent -> Type :=
| hmrr_INIT : HMR P (nil :: nil)
| hmrr_W : forall G T, HMR P G -> HMR P (T :: G)
| hmrr_C : forall G T, HMR P (T :: T :: G) -> HMR P (T :: G)
| hmrr_S : forall G T1 T2, HMR P ((T1 ++ T2) :: G) -> HMR P (T1 :: T2 :: G)
| hmrr_M {f : hmr_M P = true} : forall G T1 T2, HMR P (T1 :: G) -> HMR P (T2 :: G) -> HMR P ((T1 ++ T2) :: G)
| hmrr_T {f : hmr_T P = true} : forall G T r, HMR P (seq_mul r T :: G) -> HMR P (T :: G)
| hmrr_ID : forall G T n r s, sum_vec r = sum_vec s -> HMR P (T :: G) -> HMR P ((vec s (HMR_covar n) ++ vec r (HMR_var n) ++ T) :: G)
| hmrr_Z : forall G T r, HMR P (T :: G) -> HMR P ((vec r HMR_zero ++ T) :: G)

| hmrr_plus : forall G T A B r, HMR P ((vec r A ++ vec r B ++ T) :: G) -> HMR P ((vec r (A +S B) ++ T) :: G)
| hmrr_mul : forall G T A r0 r, HMR P ((vec (mul_vec r0 r) A ++ T) :: G) -> HMR P ((vec r (r0 *S A) ++ T) :: G)
| hmrr_max : forall G T A B r, HMR P ((vec r B ++ T) :: (vec r A ++ T) :: G) -> HMR P ((vec r (A \/S B) ++ T) :: G)
| hmrr_min : forall G T A B r, HMR P ((vec r A ++ T) :: G) -> HMR P ((vec r B ++ T) :: G) -> HMR P ((vec r (A /\S B) ++ T) :: G)
| hmrr_one : forall G T r s, sum_vec s <= sum_vec r -> HMR P (T :: G) -> HMR P ((vec s HMR_coone ++ vec r HMR_one ++ T) :: G)
| hmrr_diamond : forall T r s, sum_vec s <= sum_vec r -> HMR P ((vec s HMR_coone ++ vec r HMR_one ++ T) :: nil) -> HMR P ((vec s HMR_coone ++ vec r HMR_one ++ seq_diamond T) :: nil)
| hmrr_ex_seq : forall G T1 T2, Permutation_Type T1 T2 -> HMR P (T1 :: G) -> HMR P (T2 :: G)
| hmrr_ex_hseq : forall G H, Permutation_Type G H -> HMR P G -> HMR P H
| hmrr_can {f : hmr_CAN P = true} : forall G T A r s, sum_vec r = sum_vec s -> HMR P ((vec s (-S A) ++ vec r A ++ T) :: G) -> HMR P (T :: G).

(** HMR with only can and M *)
Definition HMR_M_can := HMR hmr_frag_M_can.
(** HMR with every rule *)
Definition HMR_full := HMR hmr_frag_full.
(** HMR without the CAN rule *)
Definition HMR_T_M := HMR hmr_frag_T_M.
(** HMR with neither the CAN rule nor the M rule *)
Definition HMR_T := HMR hmr_frag_T.
(** HMR with only the M rule *)
Definition HMR_M := HMR hmr_frag_M.
(** HMR with no additionnal rule *)
Definition HMR_nothing := HMR hmr_frag_nothing.

(** Modal depth of the proof pi *)
Fixpoint modal_depth_proof {P} {G} (pi : HMR P G) :=
  match pi with
| hmrr_INIT _ => 0%nat
| hmrr_W _ G T pi => modal_depth_proof pi
| hmrr_C _ _ _ pi => modal_depth_proof pi
| hmrr_S _ _ _ _ pi => modal_depth_proof pi
| hmrr_M _ _ _ _ pi1 pi2 => Nat.max (modal_depth_proof pi1) (modal_depth_proof pi2)
| hmrr_T _ _ _ _ pi => modal_depth_proof pi
| hmrr_ID _ _ _ _ _ _ _ pi => modal_depth_proof pi
| hmrr_Z _ _ _ _ pi => modal_depth_proof pi
| hmrr_plus _ _ _ _ _ _ pi => modal_depth_proof pi
| hmrr_mul  _ _ _ _ _ _ pi => modal_depth_proof pi
| hmrr_max  _ _ _ _ _ _ pi => modal_depth_proof pi
| hmrr_min  _ _ _ _ _ _ pi1 pi2 => Nat.max (modal_depth_proof pi1) (modal_depth_proof pi2)
| hmrr_one  _ _ _ _ _ _ pi => modal_depth_proof pi
| hmrr_diamond  _ _ _ _ _ pi => S (modal_depth_proof pi)
| hmrr_ex_seq  _ _ _ _ _ pi => modal_depth_proof pi
| hmrr_ex_hseq _ _ _ _ pi => modal_depth_proof pi
| hmrr_can _ _ _ _ _ _ _ pi => modal_depth_proof pi
  end.

(** ** Some basic properties *)
(** The two following lemmas are technical results needed for Coq *)
Lemma modal_depth_proof_eq_rect_r P :
  forall A (f : A -> hypersequent) a a' (pi : HMR P (f a') ) (Heq : a = a'),
    modal_depth_proof (eq_rect_r (fun a => HMR P (f a)) pi Heq) = modal_depth_proof pi.
Proof.
  intros A f a a' pi Heq.
  destruct Heq.
  reflexivity.
Qed.

Lemma modal_depth_proof_eq_rect P :
  forall A (f : A -> hypersequent) a a' (pi : HMR P (f a)) (Heq : a = a'),
    modal_depth_proof (eq_rect a (fun a => HMR P (f a)) pi a' Heq) = modal_depth_proof pi.
Proof.
  intros A f a a' pi Heq.
  destruct Heq; reflexivity.
Qed.

Lemma HMR_not_empty P : forall G, HMR P G -> G <> nil.
Proof.
  intros G pi; induction pi; (try now auto).
  intros Heq; apply IHpi; apply Permutation_Type_nil.
  symmetry; now rewrite <- Heq.
Qed.

(** If we add some rules, we keep the derivability *)
Lemma HMR_le_frag : forall P Q,
    le_hmr_frag P Q ->
    forall G, HMR P G -> HMR Q G.
Proof.
  intros P Q Hle G pi.
  induction pi;  destruct P as [HTP HMP HCANP]; destruct Q as [HTQ HMQ HCANQ]; destruct Hle as [HleT [HleM HleCAN]]; simpl in *; subst; try (now constructor).
  - apply hmrr_T with r; assumption.
  - apply hmrr_ex_seq with T1; assumption.
  - apply hmrr_ex_hseq with G; assumption.
  - apply hmrr_can with A r s; try assumption; try reflexivity.
Defined.

Lemma modal_depth_proof_le_frag : forall P Q (Hle : le_hmr_frag P Q) G (pi : HMR P G),
    modal_depth_proof (HMR_le_frag P Q Hle G pi) = modal_depth_proof pi.
Proof.
  intros P Q Hle G pi.
  induction pi;  destruct P as [HTP HMP HCANP]; destruct Q as [HTQ HMQ HCANQ]; destruct Hle as [HleT [HleM HleCAN]]; simpl in *; subst; simpl; try rewrite <- IHpi; try rewrite <- IHpi1; try rewrite <- IHpi2; try reflexivity.
Qed.

(** Some other derivable rules (and how they change the modal depth of the proof) *)
Lemma hmrr_W_gen P : forall G H, HMR P G -> HMR P (H ++ G).
Proof.
  intros G H; revert G; induction H; intros G pi.
  - auto.
  - simpl; apply hmrr_W; apply IHlist; apply pi.
Defined.

Lemma modal_depth_proof_W_gen P :
  forall G H (pi : HMR P G),
    modal_depth_proof (hmrr_W_gen P G H pi) = modal_depth_proof pi.
Proof.
  intros G H; revert G; induction H; intros G pi; simpl.
  - reflexivity.
  - apply IHlist.
Qed.

Lemma hmrr_C_gen P : forall G H, HMR P (H ++ H ++ G) -> HMR P (H ++ G).
Proof.
  intros G H; revert G; induction H as [ | T H]; intros G pi.
  - apply pi.
  - simpl; apply hmrr_C.
    apply hmrr_ex_hseq with (H ++ T :: T :: G); [ Permutation_Type_solve | ].
    apply IHH.
    eapply hmrr_ex_hseq ; [ | apply pi].
    Permutation_Type_solve.
Defined.

Lemma modal_depth_proof_C_gen P :
  forall G H (pi : HMR P (H ++ H ++ G)),
    modal_depth_proof (hmrr_C_gen P G H pi) = modal_depth_proof pi.
Proof.
  intros G H; revert G; induction H; intros G pi; simpl.
  - reflexivity.
  - simpl; apply IHlist.
Qed.

Lemma hmrr_diamond_no_one P : forall T,
    HMR P (T :: nil) ->
    HMR P ((seq_diamond T) :: nil).
Proof.
  intros T pi.
  change (seq_diamond T) with (vec nil HMR_coone ++ vec nil HMR_one ++ seq_diamond T).
  apply hmrr_diamond; try assumption.
  simpl; nra.
Defined.

Lemma modal_depth_proof_diamond_no_one P :
  forall T (pi : HMR P (T :: nil)),
    modal_depth_proof (hmrr_diamond_no_one P T pi) = S (modal_depth_proof pi).
Proof.
  intros T pi; simpl.
  reflexivity.
Qed.

Lemma hmrr_C_copy P : forall G T n,
    HMR P (copy_seq (S n) T :: G) ->
    HMR P (T :: G).
Proof.
  intros G T n; revert G T; induction n; intros G T pi; simpl in *; try assumption.
  apply hmrr_C.
  apply IHn.
  apply hmrr_S.
  apply pi.
Qed.

Lemma hmrr_C_copy_inv P : forall G T n,
    HMR P (T :: G) ->
    HMR (hmr_frag_add_M P) (copy_seq n T :: G).
Proof.
  intros G T; induction n; intros pi.
  - simpl.
    apply hmrr_ex_hseq with (G ++ (nil :: nil)) ; [ Permutation_Type_solve | ].
    apply hmrr_W_gen; apply hmrr_INIT.
  - simpl.
    specialize (IHn pi).
    apply hmrr_M; try reflexivity; try assumption.
    apply HMR_le_frag with P; try assumption.
    destruct P; repeat split; Bool.destr_bool.
Qed.
