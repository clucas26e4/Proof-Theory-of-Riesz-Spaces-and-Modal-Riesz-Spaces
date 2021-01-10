Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.
(** * Definition of hmr *)
(** ** HMR *)

Inductive preHMR : hypersequent -> Type :=
| prehmrr_leaf : forall G, preHMR G
| prehmrr_INIT : preHMR (nil :: nil)
| prehmrr_W : forall G T, preHMR G -> preHMR (T :: G)
| prehmrr_C : forall G T, preHMR (T :: T :: G) -> preHMR (T :: G)
| prehmrr_S : forall G T1 T2, preHMR ((T1 ++ T2) :: G) -> preHMR (T1 :: T2 :: G)
| prehmrr_T : forall G T r, preHMR (seq_mul r T :: G) -> preHMR (T :: G)
| prehmrr_ID : forall G T n r s, sum_vec r = sum_vec s -> preHMR (T :: G) -> preHMR ((vec s (HMR_covar n) ++ vec r (HMR_var n) ++ T) :: G)
| prehmrr_Z : forall G T r, preHMR (T :: G) -> preHMR ((vec r HMR_zero ++ T) :: G)

| prehmrr_plus : forall G T A B r, preHMR ((vec r A ++ vec r B ++ T) :: G) -> preHMR ((vec r (A +S B) ++ T) :: G)
| prehmrr_mul : forall G T A r0 r, preHMR ((vec (mul_vec r0 r) A ++ T) :: G) -> preHMR ((vec r (r0 *S A) ++ T) :: G)
| prehmrr_max : forall G T A B r, preHMR ((vec r B ++ T) :: (vec r A ++ T) :: G) -> preHMR ((vec r (A \/S B) ++ T) :: G)
| prehmrr_min : forall G T A B r, preHMR ((vec r A ++ T) :: G) -> preHMR ((vec r B ++ T) :: G) -> preHMR ((vec r (A /\S B) ++ T) :: G)
| prehmrr_one : forall G T r s, sum_vec s <= sum_vec r -> preHMR (T :: G) -> preHMR ((vec s HMR_coone ++ vec r HMR_one ++ T) :: G)
| prehmrr_diamond : forall T r s, sum_vec s <= sum_vec r -> preHMR ((vec s HMR_coone ++ vec r HMR_one ++ T) :: nil) -> preHMR ((vec s HMR_coone ++ vec r HMR_one ++ seq_diamond T) :: nil)
| prehmrr_ex_seq : forall G T1 T2, Permutation_Type T1 T2 -> preHMR (T1 :: G) -> preHMR (T2 :: G)
| prehmrr_ex_hseq : forall G H, Permutation_Type G H -> preHMR G -> preHMR H.

Fixpoint leaves {G} (pi : preHMR G) :=
  match pi with
| prehmrr_leaf G => G :: nil
| prehmrr_INIT => nil
| prehmrr_W G T pi => leaves pi
| prehmrr_C _ _ pi => leaves pi
| prehmrr_S _ _ _ pi => leaves pi
| prehmrr_T _ _ _ pi => leaves pi
| prehmrr_ID _ _ _ _ _ _ pi => leaves pi
| prehmrr_Z _ _ _ pi => leaves pi
| prehmrr_plus _ _ _ _ _ pi => leaves pi
| prehmrr_mul  _ _ _ _ _ pi => leaves pi
| prehmrr_max  _ _ _ _ _ pi => leaves pi
| prehmrr_min  _ _ _ _ _ pi1 pi2 => leaves pi1 ++ leaves pi2
| prehmrr_one  _ _ _ _ _ pi => leaves pi
| prehmrr_diamond  _ _ _ _ pi => leaves pi
| prehmrr_ex_seq  _ _ _ _ pi => leaves pi
| prehmrr_ex_hseq _ _ _ pi => leaves pi
  end.

Lemma finish_preproof : forall G (pi : preHMR G),
    Forall_inf HMR_T (leaves pi) ->
    HMR_T G.
Proof.
  intros G pi; induction pi; intros Hall.
  - inversion Hall; assumption.
  - apply hmrr_INIT.
  - apply hmrr_W; apply IHpi; apply Hall.
  - apply hmrr_C; apply IHpi; apply Hall.
  - apply hmrr_S; apply IHpi; apply Hall.
  - apply hmrr_T with r; try reflexivity; apply IHpi; apply Hall.
  - apply hmrr_ID; try assumption; apply IHpi; apply Hall.
  - apply hmrr_Z; apply IHpi; apply Hall.
  - apply hmrr_plus; apply IHpi; apply Hall.
  - apply hmrr_mul; apply IHpi; apply Hall.
  - apply hmrr_max; apply IHpi; apply Hall.
  - simpl in Hall.
    apply hmrr_min; [apply IHpi1; eapply Forall_inf_app_l | apply IHpi2; eapply Forall_inf_app_r]; try eassumption.
  - apply hmrr_one; try assumption; apply IHpi; apply Hall.
  - apply hmrr_diamond; try assumption; apply IHpi; apply Hall.
  - eapply hmrr_ex_seq; [ | apply IHpi; apply Hall]; try assumption.
  - eapply hmrr_ex_hseq; [ | apply IHpi; apply Hall ] ; try assumption.
Defined.

Lemma HMR_to_preHMR : forall G,
    HMR_T G ->
    preHMR G.
Proof.
  intros G pi.
  induction pi.
  - apply prehmrr_INIT.
  - now apply prehmrr_W.
  - now apply prehmrr_C.
  - now apply prehmrr_S.
  - inversion f.
  - now apply prehmrr_T with r.
  - now apply prehmrr_ID.
  - now apply prehmrr_Z.
  - now apply prehmrr_plus.
  - now apply prehmrr_mul.
  - now apply prehmrr_max.
  - now apply prehmrr_min.
  - now apply prehmrr_one.
  - now apply prehmrr_diamond.
  - now apply prehmrr_ex_seq with T1.
  - now apply prehmrr_ex_hseq with G.
  - inversion f.
Defined.

Lemma HMR_to_preHMR_no_leaf :
  forall G (pi : HMR_T G),
    leaves (HMR_to_preHMR G pi) = nil.
Proof.
  intros G pi.
  induction pi; simpl; try rewrite IHpi; try rewrite IHpi1; try rewrite IHpi2; try reflexivity; try inversion f.
Qed.
