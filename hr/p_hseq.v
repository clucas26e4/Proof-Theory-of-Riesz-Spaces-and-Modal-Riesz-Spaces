Require Import Rpos.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.
Require Import RL.OLlibs.wf_prod.

Local Open Scope R_scope.

Ltac sem_is_pos_decomp val a :=
  let H := fresh "H" in
  let HeqH := fresh "HeqH" in
  assert {H & R_order_dec (FOL_R_term_sem val a) = H} as [H HeqH] by (split with (R_order_dec (FOL_R_term_sem val a)); reflexivity); destruct H as [H | H | H];
  rewrite ? HeqH; revert H HeqH.


(** * Definitions *)
                                                
Definition p_sequent : Set := list (FOL_R_term * term).

Definition p_seq_is_atomic (T : p_sequent) := Forall_inf (fun x => match x with (a , A) => is_atom A end) T.

Fixpoint eval_p_sequent (val : nat -> R) (T : p_sequent) : sequent :=
  match T with
  | nil => nil
  | (a , A) :: T => match R_order_dec (FOL_R_term_sem val a) with
                    | R_is_gt _ H => (existT (fun x => 0 <? x = true) (FOL_R_term_sem val a) H, A) :: (eval_p_sequent val T)
                    | R_is_lt _ H => (existT (fun x => 0 <? x = true) (-(FOL_R_term_sem val a)) H, -S A) :: (eval_p_sequent val T)
                    | R_is_null _ H => eval_p_sequent val T
                    end
  end.

Fixpoint to_p_sequent (T : sequent) : p_sequent :=
  match T with
  | nil => nil
  | (a, A) :: T => (FOL_R_cst (projT1 a), A) :: (to_p_sequent T)
  end.
  
Definition Permutation_Type_p_seq val (T1 T2 : p_sequent) := Permutation_Type (eval_p_sequent val T1) (eval_p_sequent val T2).

Definition p_hypersequent : Set := list p_sequent.

Definition p_hseq_is_atomic G := Forall_inf p_seq_is_atomic G.

Definition Permutation_Type_p_hseq val (G1 G2 : p_hypersequent) := Permutation_Type (map (eval_p_sequent val) G1) (map (eval_p_sequent val) G2).

Fixpoint to_p_hypersequent (G : hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => (to_p_sequent T) :: (to_p_hypersequent G)
  end. 

(** ** Complexity *)
Fixpoint HR_complexity_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (a, A) :: T => ((HR_complexity_term A) + (HR_complexity_p_seq T))%nat
  end.

Fixpoint HR_complexity_p_hseq G :=
  match G with
  | nil => (0%nat, 0%nat)
  | T :: G => if HR_complexity_p_seq T =? fst (HR_complexity_p_hseq G) then (fst (HR_complexity_p_hseq G), S (snd (HR_complexity_p_hseq G)))
              else if (HR_complexity_p_seq T <? fst (HR_complexity_p_hseq G))%nat then (fst (HR_complexity_p_hseq G) , snd (HR_complexity_p_hseq G))
                   else (HR_complexity_p_seq T, 1%nat)
  end.

(** ** Max variable appearing in a term of a hypersequent *)
Fixpoint max_var_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (r, A) :: T => Nat.max (max_var_term A) (max_var_p_seq T)
  end.

Fixpoint max_var_p_hseq G :=
  match G with
  | nil => 0%nat
  | T :: G => Nat.max (max_var_p_seq T) (max_var_p_hseq G)
  end.

(** ** Min variable appearing in a weight of a hypersequent *)
Fixpoint max_var_weight_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (r, A) :: T => Nat.max (max_var_FOL_R_term r) (max_var_weight_p_seq T)
  end.

Fixpoint max_var_weight_p_hseq (G : p_hypersequent) :=
  match G with
  | nil => 0%nat
  | T :: G => Nat.max (max_var_weight_p_seq T) (max_var_weight_p_hseq G)
  end.

(** ** Substitution *)
Fixpoint subs_p_seq (D : p_sequent) n t :=
  match D with
  | nil => nil
  | (r, A) :: D => (r , subs A n t) :: (subs_p_seq D n t)
  end.

(** ** Definitions and properties of \vec{r}.A *)

Fixpoint vec (l : list FOL_R_term) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

Fixpoint sum_vec (l : list FOL_R_term) :=
  match l with
  | nil => FOL_R_cst 0
  | r :: l => r +R (sum_vec l)
  end.

Fixpoint copy_p_seq n (T : p_sequent) :=
  match n with
  | 0 => nil
  | S n => (copy_p_seq n T) ++ T
  end.

Fixpoint mul_vec r (l : list FOL_R_term) :=
  match l with
  | nil => nil
  | r0 :: l => (FOL_R_mul r r0) :: (mul_vec r l)
  end.

Fixpoint vec_mul_vec l1 l2 :=
  match l1 with
  | nil => nil
  | r :: l1 => (mul_vec r l2) ++ (vec_mul_vec l1 l2)
  end.

(** ** Sum of the weights *)
Fixpoint sum_weight_p_seq_var n (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , HR_var n0) :: T) => if n =? n0 then r +R (sum_weight_p_seq_var n T) else sum_weight_p_seq_var n T
  | ( _ :: T) => sum_weight_p_seq_var n T
  end.
Fixpoint sum_weight_p_seq_covar n (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , HR_covar n0) :: T) => if n =? n0 then r +R (sum_weight_p_seq_covar n T) else sum_weight_p_seq_covar n T
  | ( _ :: T) => sum_weight_p_seq_covar n T
  end.
Fixpoint p_sum_weight_var n G :=
  match G with
  | nil => FOL_R_cst 0
  | T :: G => (sum_weight_p_seq_var n T) +R (p_sum_weight_var n G)
  end.
Fixpoint p_sum_weight_covar n G :=
  match G with
  | nil => FOL_R_cst 0
  | T :: G => (sum_weight_p_seq_covar n T) +R (p_sum_weight_covar n G)
  end.

(** ** well defined hypersequent with regard to a valuation (i.e. all the weights of the hypersequent are strictly positive with this valuation) *)
Definition p_seq_well_defined (val : nat -> R) (T : p_sequent) :=
  Forall_inf (fun x => (0 <? FOL_R_term_sem val (fst x)) = true) T.

Definition p_hseq_well_defined (val : nat -> R) G : Type :=
  Forall_inf (p_seq_well_defined val) G.

(** * Properties *)
(** ** vec *)
Lemma vec_app : forall vr1 vr2 A, vec (vr1 ++ vr2) A = vec vr1 A ++ vec vr2 A.
Proof.
  induction vr1; intros vr2 A; simpl; try rewrite IHvr1; try reflexivity.
Qed.

Lemma sum_vec_app : forall vr1 vr2 val, FOL_R_pred_sem val ((sum_vec (vr1 ++ vr2)) =R ((sum_vec vr1) +R (sum_vec vr2))).
Proof.
  induction vr1; intros vr2 val.
  - rewrite app_nil_l; simpl; nra.
  - simpl.
    rewrite IHvr1.
    destruct a; simpl; nra.
Qed.

Lemma mul_vec_sum_vec : forall r vr val, FOL_R_pred_sem val (sum_vec (mul_vec r vr) =R r *R (sum_vec vr)).
Proof.
  intro r; induction vr; intros val.
  - simpl; nra.
  - simpl.
    rewrite IHvr.
    simpl; nra.
Qed.

Lemma sum_vec_vec_mul_vec : forall vr vs val, FOL_R_pred_sem val (sum_vec (vec_mul_vec vr vs) =R (sum_vec vr) *R (sum_vec vs)).
Proof.
  induction vr; intros vs val.
  - simpl; nra.
  - unfold vec_mul_vec; fold vec_mul_vec.
    unfold sum_vec; fold sum_vec.
    simpl; rewrite sum_vec_app.
    simpl; rewrite mul_vec_sum_vec.
    rewrite IHvr.
    simpl; nra.
Qed.

Lemma vec_mul_vec_nil_r : forall vr, vec_mul_vec vr nil = nil.
Proof with try reflexivity.
  induction vr...
  simpl; rewrite IHvr...
Qed.

Lemma vec_mul_vec_cons_r : forall vr1 vr2 r val, Permutation_Type_FOL_R_term val (vec_mul_vec vr1 (r :: vr2)) (mul_vec r vr1 ++ vec_mul_vec vr1 vr2).
Proof.
  unfold Permutation_Type_FOL_R_term.
  induction vr1; intros vr2 r val; simpl; try reflexivity.
  replace (FOL_R_term_sem val a * FOL_R_term_sem val r) with (FOL_R_term_sem val r * FOL_R_term_sem val a) by (simpl; nra).
  apply Permutation_Type_skip.
  rewrite ? map_app; rewrite app_assoc.
  etransitivity ; [ | apply Permutation_Type_app ; [ apply Permutation_Type_app_comm | reflexivity ] ].
  rewrite <- app_assoc; apply Permutation_Type_app; try reflexivity.
  rewrite <- map_app; apply IHvr1.
Qed.

Lemma vec_mul_vec_comm : forall vr1 vr2 val, Permutation_Type_FOL_R_term val (vec_mul_vec vr1 vr2) (vec_mul_vec vr2 vr1).
Proof.
  unfold Permutation_Type_FOL_R_term.
  induction vr1; intros vr2 val.
  - simpl; rewrite vec_mul_vec_nil_r; reflexivity.
  - simpl.
    etransitivity ; [ | symmetry; apply vec_mul_vec_cons_r ].
    rewrite ? map_app; apply Permutation_Type_app; try reflexivity.
    apply IHvr1.
Qed.

Lemma mul_vec_app : forall vr vs r, mul_vec r (vr ++ vs) = mul_vec r vr ++ mul_vec r vs.
Proof.
  induction vr; intros vs r; simpl; try rewrite IHvr; try reflexivity.
Qed.

Lemma mul_vec_perm : forall vr vs r val, Permutation_Type_FOL_R_term val vr vs ->  Permutation_Type_FOL_R_term val (mul_vec r vr) (mul_vec r vs).
Proof.
  unfold Permutation_Type_FOL_R_term.
  intros vr vs r val Hperm.
  remember (map (FOL_R_term_sem val) vr) as lr; remember (map (FOL_R_term_sem val) vs) as ls.
  revert vr vs Heqlr Heqls; induction Hperm; intros vr vs Heqlr Heqls.
  - symmetry in Heqlr; apply map_eq_nil in Heqlr; symmetry in Heqls; apply map_eq_nil in Heqls; subst.
    reflexivity.
  - destruct vr; destruct vs; inversion Heqlr; inversion Heqls; subst.
    simpl; rewrite H2; apply Permutation_Type_skip.
    apply IHHperm; reflexivity.
  - destruct vr; [ | destruct vr]; (destruct vs; [ | destruct vs]); inversion Heqlr; inversion Heqls; subst.
    simpl; rewrite H3; rewrite H4.
    replace (map (FOL_R_term_sem val) (mul_vec r vs)) with (map (FOL_R_term_sem val) (mul_vec r vr)); [ apply Permutation_Type_swap | ].
    clear - H5.
    revert vs H5; induction vr; intros vs H5.
    + destruct vs; try now inversion H5.
    + destruct vs; inversion H5; subst.
      simpl; rewrite H0.
      now rewrite IHvr with vs.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.
Qed.

Lemma vec_perm : forall vr1 vr2 A val,
    Permutation_Type_FOL_R_term val vr1 vr2 -> Permutation_Type_p_seq val (vec vr1 A) (vec vr2 A).
Proof.
  unfold Permutation_Type_FOL_R_term; unfold Permutation_Type_p_seq.
  intros vr1 vr2 A val Hperm.
  remember (map (FOL_R_term_sem val) vr1) as l1; remember (map (FOL_R_term_sem val) vr2) as l2.
  revert vr1 vr2 Heql1 Heql2; induction Hperm; intros vr1 vr2 Heql1 Heql2.
  - destruct vr1; destruct vr2; inversion Heql1; now inversion Heql2.
  - destruct vr1; destruct vr2; inversion Heql1; inversion Heql2; subst.
    simpl; rewrite H2.
    sem_is_pos_decomp val f0; intros;
      try apply Permutation_Type_skip;
      now apply IHHperm.
  - destruct vr1; [ | destruct vr1]; (destruct vr2; [ | destruct vr2]); inversion Heql1; inversion Heql2; simpl; subst.
    rewrite H3; rewrite H4.
    replace (eval_p_sequent val (vec vr1 A)) with (eval_p_sequent val (vec vr2 A)) ; [ sem_is_pos_decomp val f1; sem_is_pos_decomp val f2 ;intros; now try apply Permutation_Type_swap | ].
    clear - H5.
    revert vr2 H5; induction vr1; intros vr2 H5; destruct vr2; inversion H5; subst; try reflexivity.
    simpl; rewrite H0; now rewrite IHvr1.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.
Qed.

Lemma sum_mul_vec : forall val l r, FOL_R_pred_sem val (sum_vec (mul_vec r l) =R FOL_R_mul r (sum_vec l)).
Proof.
  intros val; induction l; intros r.
  - simpl; nra.
  - specialize (IHl r).
    simpl in *.
    rewrite IHl.
    nra.
Qed.

Lemma sum_vec_perm : forall val vr vs,
    Permutation_Type vr vs ->
    FOL_R_pred_sem val (sum_vec vr =R sum_vec vs).
Proof.
  intros val vr vs Hperm; induction Hperm; simpl in *; nra.
Qed.

Lemma mul_vec_length : forall r vr,
    length (mul_vec r vr) = length vr.
Proof.
  intros r; induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

(** ** Sequent *)

Lemma eval_p_sequent_cons : forall val r H A T,
    (existT _ (FOL_R_term_sem val r) H, A) :: eval_p_sequent val T = eval_p_sequent val ((r, A) :: T).
Proof.
  intros val r H A T.
  simpl in *.
  sem_is_pos_decomp val r; intros e He;
    [ | exfalso; clear - H e; apply R_blt_lt in H; apply R_blt_lt in e; lra
      | exfalso; clear - H e; apply R_blt_lt in H; lra].
  replace H with e by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec).
  reflexivity.
Qed.

Lemma Permutation_Type_eval_p_sequent : forall val T D,
    Permutation_Type T D ->
    Permutation_Type (eval_p_sequent val T) (eval_p_sequent val D).
Proof.
  intros val T D Hperm; induction Hperm; auto.
  - destruct x as [a A]; simpl.
    sem_is_pos_decomp val a; intros e He; try apply Permutation_Type_skip; assumption.
  - destruct x as [a A]; destruct y as [b B]; simpl.
    sem_is_pos_decomp val a; sem_is_pos_decomp val b; intros eb Heb ea Hea; try reflexivity; try apply Permutation_Type_swap.
  - etransitivity; [ apply IHHperm1 | apply IHHperm2 ].
Qed.
                                    
Lemma Permutation_Type_perm_eval_inv : forall val l T,
    Permutation_Type l (eval_p_sequent val T) ->
    { D & l = eval_p_sequent val D}.
Proof.
  intros val l T Hperm.
  remember (eval_p_sequent val T).
  revert T Heqs; induction Hperm; intros T Heqs.
  - split with nil; reflexivity.
  - induction T; try now inversion Heqs.
    destruct a as [a A]; simpl in Heqs.
    revert Heqs; sem_is_pos_decomp val a; intros e He Heqs;
      inversion Heqs; subst.
    + specialize (IHHperm T eq_refl) as [D Heq].
      split with ((a , A) :: D); simpl; rewrite He; rewrite Heq; try reflexivity.
    + specialize (IHHperm T eq_refl) as [D Heq].
      split with ((a , A) :: D); simpl; rewrite He; rewrite Heq; try reflexivity.
    + apply IHT.
      apply Heqs.
  - remember (length T).
    revert T Heqs Heqn.
    induction n; intros T Heqs Heqn.
    { destruct T; inversion Heqs; inversion Heqn. }
    destruct T ; [ | destruct T]; try now inversion Heqn.
    + exfalso.
      destruct p as [a A].
      simpl in Heqs.
      sem_is_pos_decomp val a; intros e He; rewrite He in Heqs; inversion Heqs.
    + destruct p as [a A]; destruct p0 as [b B]; simpl in Heqs.
      sem_is_pos_decomp val a; intros ea Hea; rewrite Hea in Heqs;
        sem_is_pos_decomp val b; intros eb Heb; rewrite Heb in Heqs;
          try (inversion Heqs; subst;
               split with ((b , B) :: (a , A) :: T);
               simpl; rewrite Hea; rewrite Heb; reflexivity);
          try (apply (IHn ((a, A) :: T));
               [simpl; rewrite Hea; apply Heqs |
                simpl in *; lia]);
          try (apply (IHn ((b, B) :: T));
               [simpl; rewrite Heb; apply Heqs |
                simpl in *; lia]).
  - specialize (IHHperm2 T Heqs) as [D Heq].
    apply IHHperm1 with D.
    apply Heq.
Qed.

Fixpoint seq_mul (r : FOL_R_term) (T : p_sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (FOL_R_mul r a, A) :: (seq_mul r T)
  end.
  
Lemma seq_mul_app : forall T1 T2 r, seq_mul r (T1 ++ T2) = seq_mul r T1 ++ seq_mul r T2.
Proof.
  induction T1; intros T2 r; try reflexivity.
  destruct a as (a , A).
  simpl; rewrite IHT1.
  reflexivity.
Qed.

Fixpoint seq_mul_vec vr T :=
  match vr with
  | nil => nil
  | r :: vr => (seq_mul r T) ++ (seq_mul_vec vr T)
  end.

Lemma seq_mul_vec_nil_r : forall vr,
    seq_mul_vec vr nil = nil.
Proof.
  induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

Lemma seq_mul_vec_app_l : forall T vr1 vr2,
    seq_mul_vec (vr1 ++ vr2) T = seq_mul_vec vr1 T ++ seq_mul_vec vr2 T.
Proof.
  intros T; induction vr1; intros vr2; try reflexivity.
  simpl.
  rewrite IHvr1.
  rewrite app_assoc; reflexivity.
Qed.

(** ** sum_weight_p_seq_(co)var *)

Lemma sum_weight_p_seq_var_lt_max_var : forall val n T1,
    (max_var_p_seq T1 < n)%nat ->
    FOL_R_term_sem val (sum_weight_p_seq_var n T1) = 0.
Proof.
  intros val n; induction T1; intros Hlt; auto.
  destruct a as [a A].
  destruct A; simpl in *; try (apply IHT1; simpl ; lia).
  replace (n =? n0) with false by (symmetry; apply Nat.eqb_neq; lia).
  apply IHT1.
  lia.
Qed.

Lemma sum_weight_p_seq_covar_lt_max_var : forall val n T1,
    (max_var_p_seq T1 < n)%nat ->
    FOL_R_term_sem val (sum_weight_p_seq_covar n T1) = 0.
Proof.
  intros val n; induction T1; intros Hlt; auto.
  destruct a as [a A].
  destruct A; simpl in *; try (apply IHT1 ; lia).
  replace (n =? n0) with false by (symmetry; apply Nat.eqb_neq; lia).
  apply IHT1.
  lia.
Qed. 
    
Lemma sum_weight_p_seq_var_app : forall val n T1 T2,
    FOL_R_pred_sem val (sum_weight_p_seq_var n (T1 ++ T2) =R sum_weight_p_seq_var n T1 +R sum_weight_p_seq_var n T2).
Proof.
  intros val n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (n =? n0); simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_covar_app : forall val n T1 T2,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (T1 ++ T2) =R sum_weight_p_seq_covar n T1 +R sum_weight_p_seq_covar n T2).
Proof.
  intros val n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (n =? n0); simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_var_mul : forall val n T r,
    FOL_R_pred_sem val (sum_weight_p_seq_var n (seq_mul r T) =R r *R sum_weight_p_seq_var n T).
Proof.
  intros val n T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (n =? n0); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_covar_mul : forall val n T r,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (seq_mul r T) =R r *R sum_weight_p_seq_covar n T).
Proof.
  intros val n T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (n =? n0); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_var_vec_var_eq : forall val n r,
    FOL_R_pred_sem val (sum_weight_p_seq_var n (vec r (HR_var n)) =R sum_vec r).
Proof.
  intros val n; induction r; simpl in *; try (rewrite Nat.eqb_refl; simpl; rewrite IHr); reflexivity.
Qed.

Lemma sum_weight_p_seq_covar_vec_covar_eq : forall val n r,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (vec r (HR_covar n)) =R sum_vec r).
Proof.
  intros val n; induction r; simpl; try (rewrite Nat.eqb_refl; simpl; rewrite IHr); nra.
Qed.

Lemma sum_weight_p_seq_var_vec_neq : forall val n A r,
    HR_var n <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_var n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.

Lemma sum_weight_p_seq_covar_vec_neq : forall val n A r,
    HR_covar n <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_covar n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.

Lemma p_seq_non_atomic_perm :
  forall T,
    (p_seq_is_atomic T -> False) ->
    {' (A , D) : _ &
                 Permutation_Type T (A :: D) &
                 ~ (is_atom (snd A)) }.
Proof.
  induction T; intros Hnat; [exfalso; apply Hnat; apply Forall_inf_nil | ].
  destruct a as [a A].
  destruct A.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, HR_var n) :: D)); auto.
    Permutation_Type_solve.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, HR_covar n) :: D)); auto.
    Permutation_Type_solve.
  - split with ((a, HR_zero), T); auto.
  - split with ((a, A1 +S A2), T); auto.
  - split with ((a, r *S A), T); auto.
  - split with ((a, A1 \/S A2), T); auto.
  - split with ((a, A1 /\S A2), T); auto.
Qed.

Lemma p_seq_atomic_seq_atomic : forall val T,
    p_seq_is_atomic T ->
    seq_is_atomic (eval_p_sequent val T).
Proof.
  intros val T; induction T; intros Hall.
  - apply Forall_inf_nil.
  - destruct a as [a A].
    simpl in Hall |- *.
    inversion Hall; subst.
    sem_is_pos_decomp val a; intros; simpl; try apply Forall_inf_cons; try apply IHT; auto.
    destruct A; inversion X; auto.
Qed.

Lemma p_hseq_atomic_hseq_atomic : forall val G,
    p_hseq_is_atomic G ->
    hseq_is_atomic (map (eval_p_sequent val) G).
Proof.
  intros val; induction G; intros Hat; try apply Forall_inf_nil.
  simpl; inversion Hat; subst; apply Forall_inf_cons; [ apply p_seq_atomic_seq_atomic | apply IHG]; auto.
Qed.

(** Complexity related theorem *)

Lemma complexity_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    HR_complexity_p_seq T1 = HR_complexity_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; lia.
Qed.

Lemma complexity_p_hseq_perm : forall G1 G2,
    Permutation_Type G1 G2 ->
    HR_complexity_p_hseq G1 = HR_complexity_p_hseq G2.
Proof.
  intros G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - simpl.
    rewrite IHHperm.
    case (HR_complexity_p_seq x =? fst (HR_complexity_p_hseq l'));
      case (HR_complexity_p_seq x <? fst (HR_complexity_p_hseq l'))%nat; reflexivity.
  - simpl.
    case_eq (HR_complexity_p_seq x =? fst (HR_complexity_p_hseq l)); intros H1;
      case_eq (HR_complexity_p_seq y =? fst (HR_complexity_p_hseq l)); intros H2;
        case_eq (HR_complexity_p_seq x <? fst (HR_complexity_p_hseq l))%nat; intros H3;
          case_eq (HR_complexity_p_seq y <? fst (HR_complexity_p_hseq l))%nat; intros H4;
            case_eq (HR_complexity_p_seq x =? HR_complexity_p_seq y); intros H5;
              case_eq (HR_complexity_p_seq x <? HR_complexity_p_seq y)%nat; intros H6;
                case_eq (HR_complexity_p_seq y <? HR_complexity_p_seq x)%nat; intros H7;
                  repeat (simpl; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5; try (rewrite Nat.eqb_sym in H5; rewrite H5); try rewrite H6; try rewrite H7);
                  try reflexivity;
                  (apply Nat.eqb_eq in H1 + apply Nat.eqb_neq in H1);
                  (apply Nat.eqb_eq in H2 + apply Nat.eqb_neq in H2);
                  (apply Nat.ltb_lt in H3 + apply Nat.ltb_nlt in H3);
                  (apply Nat.ltb_lt in H4 + apply Nat.ltb_nlt in H4);
                  (apply Nat.eqb_eq in H5 + apply Nat.eqb_neq in H5);
                  (apply Nat.ltb_lt in H6 + apply Nat.ltb_nlt in H6);
                  (apply Nat.ltb_lt in H7 + apply Nat.ltb_nlt in H7);
                  try lia.
    rewrite H5; reflexivity.
  - transitivity (HR_complexity_p_hseq l'); assumption.
Qed.

Lemma complexity_p_hseq_perm_fst : forall G,
    G <> nil ->
    {' (T, H) : _ &
                Permutation_Type G (T :: H) &
                HR_complexity_p_seq T = fst (HR_complexity_p_hseq G) }.
  induction G; intros H; [ exfalso; apply H; reflexivity | clear H ].
  simpl.
  case_eq (HR_complexity_p_seq a =? fst (HR_complexity_p_hseq G)); intros H1.
  - split with (a, G); try reflexivity.
    apply Nat.eqb_eq in H1; rewrite H1; reflexivity.
  - case_eq (HR_complexity_p_seq a <? fst (HR_complexity_p_hseq G))%nat; intros H2.
    + destruct G; [ inversion H2 | ].
      destruct IHG as [[T H] Hperm Heq].
      { intros H; inversion H. }
      split with (T, (a :: H)).
      * transitivity (a :: T :: H); Permutation_Type_solve.
      * rewrite (complexity_p_hseq_perm _ _ Hperm).
        rewrite (complexity_p_hseq_perm _ _ Hperm) in Heq.
        rewrite Heq; reflexivity.
    + split with (a, G); reflexivity.
Qed.

Lemma complexity_p_hseq_perm_fst_p_seq : forall T1 T2 G,
    Permutation_Type T1 T2 ->
    HR_complexity_p_hseq (T1 :: G) = HR_complexity_p_hseq (T2 :: G).
Proof.
  intros T1 T2 G Hperm.
  simpl.
  rewrite (complexity_p_seq_perm _ _ Hperm).
  reflexivity.
Qed.

Lemma complexity_p_seq_app : forall T1 T2,
    HR_complexity_p_seq (T1 ++ T2) = (HR_complexity_p_seq T1 + HR_complexity_p_seq T2)%nat.
Proof.
  induction T1; intros T2; simpl; try rewrite IHT1; try destruct a; lia.
Qed.

Lemma complexity_p_seq_vec : forall r A,
    HR_complexity_p_seq (vec r A) = (length r * HR_complexity_term A)%nat.
Proof.
  induction r; intros A; simpl; try rewrite IHr; lia.
Qed.

Lemma p_seq_is_atomic_complexity_0 :
  forall T,
    p_seq_is_atomic T ->
    HR_complexity_p_seq T = 0%nat.
Proof.
  induction T; intros Hat;
    inversion Hat; simpl; try destruct a; try rewrite IHT; try rewrite is_atom_complexity_0;
      auto.
Qed.

Lemma p_seq_is_atomic_complexity_0_inv :
  forall T,
    HR_complexity_p_seq T = 0%nat ->
    p_seq_is_atomic T.
Proof.
  induction T; intros Heq; [ apply Forall_inf_nil |] .
  destruct a as [a A]; simpl in *.
  apply Forall_inf_cons ; [ apply is_atom_complexity_0_inv  | apply IHT]; lia.
Qed.

Lemma p_hseq_is_atomic_complexity_0 :
  forall G,
    p_hseq_is_atomic G ->
    fst (HR_complexity_p_hseq G) = 0%nat.
Proof.
  induction G; intros Hat; [ reflexivity | ].
  inversion Hat; subst; specialize (IHG X0).
  simpl.
  rewrite p_seq_is_atomic_complexity_0 ; [ | apply X].
  rewrite IHG; reflexivity.
Qed.

Lemma p_hseq_is_atomic_complexity_0_inv :
  forall G,
    fst (HR_complexity_p_hseq G) = 0%nat ->
    p_hseq_is_atomic G.
Proof.
  induction G; intros Heq; [ apply Forall_inf_nil | ].
  simpl in *.
  case_eq (HR_complexity_p_seq a =? fst (HR_complexity_p_hseq G)); intros H; rewrite H in Heq; simpl in Heq ; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H ].
  { apply Forall_inf_cons; [ apply p_seq_is_atomic_complexity_0_inv | apply IHG ]; lia. }
  exfalso.
  case_eq (HR_complexity_p_seq a <? fst (HR_complexity_p_hseq G))%nat; intros H2; rewrite H2 in Heq; [apply Nat.ltb_lt in H2 | apply Nat.ltb_nlt in H2]; simpl in *; lia.
Qed.

Lemma hrr_Z_decrease_complexity : forall G T r,
    r <> nil ->
    HR_complexity_p_seq (vec r HR_zero ++ T) = fst (HR_complexity_p_hseq ((vec r HR_zero ++ T) :: G)) ->
    HR_complexity_p_hseq (T :: G) <2 HR_complexity_p_hseq ((vec r HR_zero ++ T) :: G).
Proof.
  intros G T r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq T =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r HR_zero ++ T) =? fst (HR_complexity_p_hseq G)); intros H2.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H2.
    rewrite complexity_p_seq_app in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r HR_zero ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq T <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite complexity_p_seq_app in H2; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq T <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r HR_zero ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite complexity_p_seq_app in H4; lia.
    + apply fst_lt2.
      rewrite complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      simpl; lia.
Qed.
    
Lemma hrr_plus_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A +S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r A ++ vec r B ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r A ++ vec r B ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A +S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite 2 complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; simpl; lia.
Qed.

Lemma hrr_mul_decrease_complexity : forall G T A r0 r,
    r <> nil ->
    HR_complexity_p_seq (vec r (r0 *S A) ++ T) = fst (HR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros G T A r0 r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (r0 *S A) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    rewrite mul_vec_length in H1.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in H1.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in *; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; rewrite mul_vec_length in *; simpl; lia.
Qed.

Lemma hrr_min_r_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r A ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r A ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite ? complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; simpl; lia.
Qed.

Lemma hrr_min_l_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r B ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; simpl; lia.
Qed.

Lemma hrr_max_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A \/S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r A ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A \/S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + simpl.
      case_eq (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G)); intros H4.
      * apply fst_lt2.
        apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
        lia.
      * case_eq (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H5.
        -- apply fst_lt2.
           apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
           lia.
        -- apply fst_lt2.
           rewrite ? complexity_p_seq_app; rewrite ? complexity_p_seq_vec; destruct r; [ exfalso; apply Hnnil; reflexivity | ]; simpl; lia.        
  - replace (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_neq in H1; apply Nat.eqb_eq in H2.
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    simpl.
    replace (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G)) with false.
    2:{ symmetry.
        apply Nat.eqb_neq; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    replace (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    apply snd_lt2; lia.
  - simpl in Heq.
    rewrite H2 in Heq.
    assert ((HR_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat = false) as H3.
    { apply Nat.ltb_nlt; apply Nat.eqb_neq in H2.
      intros H; apply Nat.ltb_lt in H.
      rewrite H in Heq.
      simpl in Heq.
      apply H2; apply Heq. }
    rewrite H3; clear Heq.
    case_eq (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; simpl.
    + case (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G));
        [ | case (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat];
        apply fst_lt2; apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4;
          rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
            (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
    + case (HR_complexity_p_seq (vec r B ++ T) =? HR_complexity_p_seq (vec r A ++ T));
        [ | case (HR_complexity_p_seq (vec r B ++ T) <? HR_complexity_p_seq (vec r A ++ T))%nat];
      apply fst_lt2;
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
          (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
Qed.

(** ** max_(co)var *)

Lemma max_var_seq_le_p_seq : forall val T,
    (max_var_seq (eval_p_sequent val T) <= max_var_p_seq T)%nat.
Proof.
  intros val; induction T; simpl; auto.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl; try lia.
  clear - IHT.
  induction A; simpl; try lia.
Qed.

Lemma max_var_hseq_le_p_hseq : forall val G,
    (max_var_hseq (map (eval_p_sequent val) G) <= max_var_p_hseq G)%nat.
Proof.
  intros val; induction G; simpl; auto.
  assert (H := max_var_seq_le_p_seq val a).
  lia.
Qed.

Lemma max_var_p_hseq_perm : forall G H,
    Permutation_Type G H ->
    max_var_p_hseq G = max_var_p_hseq H.
Proof.
  intros G H Hperm.
  induction Hperm; simpl; lia.
Qed.

Lemma max_var_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    max_var_p_seq T1 = max_var_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl; try destruct x; try destruct y; try lia.
Qed.

(** ** well defined *)
Lemma p_seq_well_defined_perm : forall val T D,
    Permutation_Type T D ->
    p_seq_well_defined val T ->
    p_seq_well_defined val D.
Proof.
  intros val T D Hperm.
  induction Hperm; intros Hwd; inversion Hwd; subst; (try constructor); auto.
  - apply IHHperm; auto.
  - inversion X; auto.
  - inversion X; subst.
    apply Forall_inf_cons; auto.
Qed.

Lemma p_hseq_well_defined_perm : forall val G H,
    Permutation_Type G H ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val H.
Proof.
  intros val G H Hperm.
  induction Hperm; intros Hwd; inversion Hwd; subst; (try constructor); auto.
  - apply IHHperm; auto.
  - inversion X0; auto.
  - inversion X0; subst.
    apply Forall_inf_cons; auto.
Qed.

(** ** to_p_hypersequent *)

Lemma to_p_sequent_well_defined : forall val T,
    p_seq_well_defined val (to_p_sequent T).
Proof.
  intros val; induction T; [ apply Forall_inf_nil | ].
  destruct a as [[a Ha] A]; simpl.
  apply Forall_inf_cons; assumption.
Qed.

Lemma to_p_hypersequent_well_defined : forall val G,
    p_hseq_well_defined val (to_p_hypersequent G).
Proof.
  intros val; induction G; [ apply Forall_inf_nil | ].
  apply Forall_inf_cons; [ apply to_p_sequent_well_defined | assumption ].
Qed.

Lemma eval_p_sequent_to_p_sequent : forall val T,
    eval_p_sequent val (to_p_sequent T) = T.
Proof.
  intros val; induction T; try reflexivity.
  destruct a as [[a Ha] A]; simpl.
  assert {H & R_order_dec a = H} as [e He] by (split with (R_order_dec a); reflexivity); destruct e as [e | e | e];
    rewrite ? He;
    [ | exfalso; clear - e Ha; simpl in *; apply R_blt_lt in Ha; apply R_blt_lt in e; nra
      | exfalso; clear - e Ha; simpl in *; apply R_blt_lt in Ha; nra].
  replace e with Ha by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec).
  rewrite IHT; reflexivity.
Qed.

Lemma eval_p_hypersequent_to_p_hypersequent : forall val G,
    map (eval_p_sequent val) (to_p_hypersequent G) = G.
Proof.
  intros val; induction G; try reflexivity.
  simpl.
  rewrite eval_p_sequent_to_p_sequent; rewrite IHG.
  reflexivity.
Qed.
