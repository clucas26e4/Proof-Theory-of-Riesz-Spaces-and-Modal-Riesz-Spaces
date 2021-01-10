Require Import Rpos.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import riesz_logic_List_more.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import FunctionalExtensionality.

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
Definition p_seq_diamond (T : p_sequent) := map (fun x => (fst x, <S> (snd x))) T.

Definition p_seq_is_basic (T : p_sequent) := Forall_inf (fun x => match x with (a , A) => is_basic A end) T.

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

Definition p_hseq_is_basic G := Forall_inf p_seq_is_basic G.

Definition p_hseq_is_atomic G := Forall_inf p_seq_is_atomic G.

Definition Permutation_Type_p_hseq val (G1 G2 : p_hypersequent) := Permutation_Type (map (eval_p_sequent val) G1) (map (eval_p_sequent val) G2).

Fixpoint to_p_hypersequent (G : hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => (to_p_sequent T) :: (to_p_hypersequent G)
  end. 

(** ** Complexity *)
Fixpoint HMR_complexity_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (a, A) :: T => ((HMR_complexity_term A) + (HMR_complexity_p_seq T))%nat
  end.

Fixpoint max_diamond_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (a, A) :: T => Nat.max (max_diamond_term A) (max_diamond_p_seq T)
  end.

Fixpoint HMR_complexity_p_hseq G :=
  match G with
  | nil => (0%nat, 0%nat)
  | T :: G => if HMR_complexity_p_seq T =? fst (HMR_complexity_p_hseq G) then (fst (HMR_complexity_p_hseq G), S (snd (HMR_complexity_p_hseq G)))
              else if (HMR_complexity_p_seq T <? fst (HMR_complexity_p_hseq G))%nat then (fst (HMR_complexity_p_hseq G) , snd (HMR_complexity_p_hseq G))
                   else (HMR_complexity_p_seq T, 1%nat)
  end.

Fixpoint max_diamond_p_hseq G :=
  match G with
  | nil => 0%nat
  | T :: G => Nat.max (max_diamond_p_seq T) (max_diamond_p_hseq G)
  end.

Definition modal_complexity_p_hseq G := (max_diamond_p_hseq G, fst (HMR_complexity_p_hseq G), snd (HMR_complexity_p_hseq G)).

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

(** ** Man variable appearing in a weight of a hypersequent *)
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

Fixpoint seq_mul (r : FOL_R_term) (T : p_sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (FOL_R_mul r a, A) :: (seq_mul r T)
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
  | ((r , HMR_var n0) :: T) => if n =? n0 then r +R (sum_weight_p_seq_var n T) else sum_weight_p_seq_var n T
  | ( _ :: T) => sum_weight_p_seq_var n T
  end.
Fixpoint sum_weight_p_seq_covar n (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , HMR_covar n0) :: T) => if n =? n0 then r +R (sum_weight_p_seq_covar n T) else sum_weight_p_seq_covar n T
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

Fixpoint sum_weight_p_seq_one (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , HMR_one) :: T) => r +R (sum_weight_p_seq_one T)
  | ( _ :: T) => sum_weight_p_seq_one T
  end.
Fixpoint sum_weight_p_seq_coone (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , HMR_coone) :: T) => r +R (sum_weight_p_seq_coone T)
  | ( _ :: T) => sum_weight_p_seq_coone T
  end.
Fixpoint p_sum_weight_one G :=
  match G with
  | nil => FOL_R_cst 0
  | T :: G => (sum_weight_p_seq_one T) +R (p_sum_weight_one G)
  end.
Fixpoint p_sum_weight_coone G :=
  match G with
  | nil => FOL_R_cst 0
  | T :: G => (sum_weight_p_seq_coone T) +R (p_sum_weight_coone G)
  end.

(** keep only the diamonds formulas and (co)ones but remove the diamond operator *)
Fixpoint only_diamond_p_seq (T : p_sequent) :=
  match T with
  | nil => nil
  | (a , <S> A) :: T => (a , A) :: only_diamond_p_seq T
  | (a , HMR_one) :: T => (a , HMR_one) :: only_diamond_p_seq T
  | (a , HMR_coone) :: T => (a , HMR_coone) :: only_diamond_p_seq T
  | _ :: T => only_diamond_p_seq T
  end.

Fixpoint only_diamond_p_hseq G :=
  match G with
  | nil => nil
  | T :: G => only_diamond_p_seq T :: only_diamond_p_hseq G
  end.

(** ** well defined hypersequent with regard to a valuation (i.e. all the weights of the hypersequent are strictly positive with this valuation) *)
Definition p_seq_well_defined (val : nat -> R) (T : p_sequent) :=
  Forall_inf (fun x => (0 <? FOL_R_term_sem val (fst x)) = true) T.

Definition p_hseq_well_defined (val : nat -> R) G : Type :=
  Forall_inf (p_seq_well_defined val) G.

(** * Properties *)
(** ** vec *)
Lemma vec_inj : forall vr vs A,
    vec vr A = vec vs A ->
    vr = vs.
Proof.
  induction vr; intros [ | s vs] A Heq; inversion Heq; subst; auto.
  rewrite IHvr with vs A; auto.
Qed.

Lemma in_inf_vec_eq_term : forall vr r A B, In_inf (r, A) (vec vr B) -> prod (A = B) (In_inf r vr).
Proof.
  induction vr; intros r A B Hin; inversion Hin; subst.
  - inversion H; split; auto.
    left; reflexivity.
  - destruct IHvr with r A B; auto.
    split; auto.
    right; assumption.
Qed.

Lemma Permutation_Type_vec : forall vr vs A,
    Permutation_Type vr vs ->
    Permutation_Type (vec vr A) (vec vs A).
Proof.
  intros vr vs A Hperm; induction Hperm; simpl; Permutation_Type_solve.
Qed.

Lemma Permutation_Type_vec_decomp : forall T vr A,
    Permutation_Type T (vec vr A) ->
    { vs & prod (T = vec vs A) (Permutation_Type vr vs)}.
Proof.
  intros T vr A Hperm.
  remember (vec vr A) as D.
  revert vr A HeqD.
  induction Hperm; intros vr A HeqD.
  - split with nil; repeat split; auto.
    destruct vr; auto.
    inversion HeqD.
  - destruct vr; inversion HeqD; subst.
    specialize (IHHperm vr A) as [vs [Heq Hperm']]; auto.
    split with (f :: vs).
    repeat split.
    + rewrite Heq; reflexivity.
    + apply Permutation_Type_skip; auto.
  - destruct vr; inversion HeqD.
    destruct vr; inversion H1; subst.
    split with (f0 :: f :: vr).
    repeat split; auto.
    apply Permutation_Type_swap.
  - destruct (IHHperm2 vr A HeqD) as [vs [Heq' Hperm']].
    destruct (IHHperm1 vs A Heq') as [vs' [Heq'' Hperm'']].
    split with vs'; repeat split; auto.
    Permutation_Type_solve.
Qed.

Lemma Permutation_Type_vec_inv : forall vr vs A,
    Permutation_Type (vec vr A) (vec vs A) ->
    Permutation_Type vr vs.
Proof.
  intros vr vs A Hperm.
  remember (vec vr A); remember (vec vs A).
  revert vr vs A Heql Heql0.
  induction Hperm; intros vr vs A Heql Heql0.
  - destruct vr; destruct vs; auto; inversion Heql; inversion Heql0.
  - destruct vr; destruct vs; inversion Heql; inversion Heql0; subst.
    inversion H2.
    apply Permutation_Type_skip.
    apply IHHperm with A; auto.
  - destruct vr; destruct vs; inversion Heql; inversion Heql0; subst.
    destruct vr; destruct vs; inversion H1; inversion H3; subst.
    rewrite vec_inj with vr vs A; auto.
    apply Permutation_Type_swap.
  - subst.
    destruct (Permutation_Type_vec_decomp _ _ _ Hperm2) as [vr' [ Heq Hperm]].
    subst.
    specialize (IHHperm2 vr' vs A (eq_refl _) (eq_refl _)).
    specialize (IHHperm1 vr vr' A (eq_refl _) (eq_refl _)).
    Permutation_Type_solve.    
Qed.

Lemma seq_mul_vec_eq_vec_mul_vec : forall r vr A,
    seq_mul r (vec vr A) = vec (mul_vec r vr) A.
Proof.
  intros r vr A; induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

Lemma vec_length : forall vr A, length (vec vr A) = length vr.
Proof.
  induction vr; intros A; try specialize (IHvr A); simpl; lia.
Qed.

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

Lemma Permutation_Type_mul_vec : forall r vr vs,
  Permutation_Type vr vs ->
  Permutation_Type (mul_vec r vr) (mul_vec r vs).
Proof.
  intros r vr vs Hperm; induction Hperm; simpl; Permutation_Type_solve.
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

Lemma In_inf_seq_mul :
  forall A r T,
    In_inf A (seq_mul r T) ->
    {' (b , B) : _ & prod (A = ((r *R b) , B)) (In_inf (b, B) T)}.
Proof.
  intros [a A] r; induction T; try destruct a0 as [b B]; intros Hin; simpl in *; inversion Hin.
  - split with (b , B); split; auto.
  - destruct (IHT X) as [[b0 B0] [Heq Hin']].
    split with (b0, B0); split; auto.
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

Lemma seq_mul_app : forall T1 T2 r, seq_mul r (T1 ++ T2) = seq_mul r T1 ++ seq_mul r T2.
Proof.
  induction T1; intros T2 r; try reflexivity.
  destruct a as (a , A).
  simpl; rewrite IHT1.
  reflexivity.
Qed.

Lemma seq_mul_perm : forall T1 T2 r, Permutation_Type T1 T2 -> Permutation_Type (seq_mul r T1) (seq_mul r T2).
Proof.
  intros T1 T2 r Hperm; induction Hperm; try destruct x; try destruct y; simpl; Permutation_Type_solve.
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

(** ** Diamond properties *)
  
Lemma only_diamond_p_seq_app :
  forall T1 T2,
    only_diamond_p_seq (T1 ++ T2) = only_diamond_p_seq T1 ++ only_diamond_p_seq T2.
Proof.
  induction T1; intros T2; simpl; try (rewrite IHT1; destruct a; destruct t); reflexivity.
Qed.

Lemma only_diamond_p_seq_mul :
  forall T r,
    seq_mul r (only_diamond_p_seq T) = only_diamond_p_seq (seq_mul r T).
Proof.
  induction T; intros r; simpl; try (destruct a; destruct t; simpl; rewrite IHT); try reflexivity.
Qed.

Lemma only_diamond_p_seq_copy :
  forall T n,
    copy_p_seq n (only_diamond_p_seq T) = only_diamond_p_seq (copy_p_seq n T).
Proof.
  intros T; induction n; simpl; try rewrite only_diamond_p_seq_app; try rewrite IHn; reflexivity.
Qed.

Lemma only_diamond_p_seq_vec_var :
  forall n r,
    only_diamond_p_seq (vec r (HMR_var n)) = nil.
Proof.
  intros n; induction r; simpl; auto.
Qed.

Lemma only_diamond_p_seq_vec_covar :
  forall n r,
    only_diamond_p_seq (vec r (HMR_covar n)) = nil.
Proof.
  intros n; induction r; simpl; auto.
Qed.

Lemma only_diamond_p_seq_vec_one :
  forall r,
    only_diamond_p_seq (vec r HMR_one) = vec r HMR_one.
Proof.
  induction r; simpl; try rewrite IHr; reflexivity.
Qed.

Lemma only_diamond_p_seq_vec_coone :
  forall r,
    only_diamond_p_seq (vec r HMR_coone) = vec r HMR_coone.
Proof.
  induction r; simpl; try rewrite IHr; reflexivity.
Qed.
Lemma only_diamond_p_seq_vec_diamond :
  forall r B,
    only_diamond_p_seq (vec r (<S> B)) = vec r B.
Proof.
  intros r B; induction r; simpl; try rewrite IHr; reflexivity.
Qed.

Lemma only_diamond_p_seq_only_diamond :
  forall T,
    only_diamond_p_seq (p_seq_diamond T) = T.
Proof.
  induction T; try destruct a; simpl; try rewrite IHT; reflexivity.
Qed.

Lemma only_diamond_p_seq_perm :
  forall T1 T2,
    Permutation_Type T1 T2 ->
    Permutation_Type (only_diamond_p_seq T1) (only_diamond_p_seq T2).
Proof.
  intros T1 T2 Hperm.
  induction Hperm.
  - apply Permutation_Type_nil_nil.
  - destruct x; destruct t; simpl; try apply Permutation_Type_cons; try apply IHHperm; reflexivity.
  - destruct x; destruct y; destruct t; destruct t0; simpl; try apply Permutation_Type_swap; try apply Permutation_Type_cons; reflexivity.
  - apply Permutation_Type_trans with (only_diamond_p_seq l'); assumption.
Qed.

(** ** sum_weight_p_seq_(co)var and (co)one *)

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
    FOL_R_pred_sem val (sum_weight_p_seq_var n (vec r (HMR_var n)) =R sum_vec r).
Proof.
  intros val n; induction r; simpl in *; try (rewrite Nat.eqb_refl; simpl; rewrite IHr); reflexivity.
Qed.

Lemma sum_weight_p_seq_covar_vec_covar_eq : forall val n r,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (vec r (HMR_covar n)) =R sum_vec r).
Proof.
  intros val n; induction r; simpl; try (rewrite Nat.eqb_refl; simpl; rewrite IHr); nra.
Qed.

Lemma sum_weight_p_seq_var_vec_neq : forall val n A r,
    HMR_var n <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_var n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.

Lemma sum_weight_p_seq_covar_vec_neq : forall val n A r,
    HMR_covar n <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_covar n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.
    
Lemma sum_weight_p_seq_one_app : forall val T1 T2,
    FOL_R_pred_sem val (sum_weight_p_seq_one (T1 ++ T2) =R sum_weight_p_seq_one T1 +R sum_weight_p_seq_one T2).
Proof.
  intros val T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A;  simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_coone_app : forall val T1 T2,
    FOL_R_pred_sem val (sum_weight_p_seq_coone (T1 ++ T2) =R sum_weight_p_seq_coone T1 +R sum_weight_p_seq_coone T2).
Proof.
  intros val T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_one_mul : forall val T r,
    FOL_R_pred_sem val (sum_weight_p_seq_one (seq_mul r T) =R r *R sum_weight_p_seq_one T).
Proof.
  intros val T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_coone_mul : forall val T r,
    FOL_R_pred_sem val (sum_weight_p_seq_coone (seq_mul r T) =R r *R sum_weight_p_seq_coone T).
Proof.
  intros val T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_one_vec_one_eq : forall val r,
    FOL_R_pred_sem val (sum_weight_p_seq_one (vec r HMR_one) =R sum_vec r).
Proof.
  intros val; induction r; simpl in *; try (simpl; rewrite IHr); reflexivity.
Qed.

Lemma sum_weight_p_seq_coone_vec_coone_eq : forall val r,
    FOL_R_pred_sem val (sum_weight_p_seq_coone (vec r HMR_coone) =R sum_vec r).
Proof.
  intros val; induction r; simpl; try (simpl; rewrite IHr); nra.
Qed.

Lemma sum_weight_p_seq_one_vec_neq : forall val A r,
    HMR_one <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_one (vec r A)) = 0.
Proof.
  intros val A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; simpl; auto.
  contradiction.
Qed.

Lemma sum_weight_p_seq_coone_vec_neq : forall val A r,
    HMR_coone <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_coone (vec r A)) = 0.
Proof.
  intros val A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; auto.
  contradiction.
Qed.

Lemma p_seq_non_basic_perm :
  forall T,
    (p_seq_is_basic T -> False) ->
    {' (A , D) : _ &
                 Permutation_Type T (A :: D) &
                 ~ (is_basic (snd A)) }.
Proof.
  induction T; intros Hnat; [exfalso; apply Hnat; apply Forall_inf_nil | ].
  destruct a as [a A].
  destruct A.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, HMR_var n) :: D)); auto.
    Permutation_Type_solve.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, HMR_covar n) :: D)); auto.
    Permutation_Type_solve.
  - split with ((a, HMR_zero), T); auto.
  - split with ((a, A1 +S A2), T); auto.
  - split with ((a, r *S A), T); auto.
  - split with ((a, A1 \/S A2), T); auto.
  - split with ((a, A1 /\S A2), T); auto.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, HMR_one) :: D)); auto.
    Permutation_Type_solve.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, HMR_coone) :: D)); auto.
    Permutation_Type_solve.
  - destruct IHT as [[B D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (B, ((a, <S> A) :: D)); auto.
    Permutation_Type_solve.
Qed.

Lemma p_seq_basic_seq_basic : forall val T,
    p_seq_is_basic T ->
    seq_is_basic (eval_p_sequent val T).
Proof.
  intros val T; induction T; intros Hall.
  - apply Forall_inf_nil.
  - destruct a as [a A].
    simpl in Hall |- *.
    inversion Hall; subst.
    sem_is_pos_decomp val a; intros; simpl; try apply Forall_inf_cons; try apply IHT; auto.
    destruct A; inversion X; auto.
Qed.

Lemma p_hseq_basic_hseq_basic : forall val G,
    p_hseq_is_basic G ->
    hseq_is_basic (map (eval_p_sequent val) G).
Proof.
  intros val; induction G; intros Hat; try apply Forall_inf_nil.
  simpl; inversion Hat; subst; apply Forall_inf_cons; [ apply p_seq_basic_seq_basic | apply IHG]; auto.
Qed.

(** Complexity related theorem *)

Lemma complexity_p_hseq_cons : forall T G,
    fst (HMR_complexity_p_hseq (T :: G)) = max (HMR_complexity_p_seq T) (fst (HMR_complexity_p_hseq G)).
Proof.
  intros T G.
  simpl.
  case_eq (HMR_complexity_p_seq T =? fst (HMR_complexity_p_hseq G)); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H);
    case_eq (HMR_complexity_p_seq T <? fst (HMR_complexity_p_hseq G))%nat; intros H2; (apply Nat.ltb_lt in H2 + apply Nat.ltb_nlt in H2); simpl in *; lia.
Qed.  

Lemma complexity_p_hseq_app : forall G1 G2,
    fst (HMR_complexity_p_hseq (G1 ++ G2)) = max (fst (HMR_complexity_p_hseq G1)) (fst (HMR_complexity_p_hseq G2)).
Proof.
  induction G1; intros G2; try specialize (IHG1 G2); simpl; try lia.
  rewrite IHG1.
  case_eq (HMR_complexity_p_seq a =? Init.Nat.max (fst (HMR_complexity_p_hseq G1)) (fst (HMR_complexity_p_hseq G2))); intros H1; (apply Nat.eqb_eq in H1 + apply Nat.eqb_neq in H1);
    case_eq ((HMR_complexity_p_seq a <? Init.Nat.max (fst (HMR_complexity_p_hseq G1)) (fst (HMR_complexity_p_hseq G2)))%nat); intros H2; (apply Nat.ltb_lt in H2 + apply Nat.ltb_nlt in H2);
      case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G1)); intros H3; (apply Nat.eqb_eq in H3 + apply Nat.eqb_neq in H3);
        case_eq ((HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G1))%nat); intros H4; (apply Nat.ltb_lt in H4 + apply Nat.ltb_nlt in H4); simpl; lia.
Qed.

Lemma max_diamond_p_seq_app : forall T1 T2,
    max_diamond_p_seq (T1 ++ T2) = Nat.max (max_diamond_p_seq T1) (max_diamond_p_seq T2).
Proof.
  induction T1; intros T2; try destruct a; simpl; try (rewrite (IHT1 T2)); lia.
Qed.

Lemma max_diamond_p_hseq_app : forall G1 G2,
    max_diamond_p_hseq (G1 ++ G2) = Nat.max (max_diamond_p_hseq G1) (max_diamond_p_hseq G2).
Proof.
  induction G1; intros G2; simpl; try (rewrite (IHG1 G2)); lia.
Qed.

Lemma max_diamond_p_seq_vec : forall r A,
    r <> nil ->
    max_diamond_p_seq (vec r A) = max_diamond_term A.
Proof.
  induction r; intros A Hnnil; [exfalso; now apply Hnnil | ].
  simpl.
  destruct r; [ simpl; lia | ].
  rewrite (IHr A); [ lia | intros H; inversion H].
Qed.

Lemma max_diamond_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    max_diamond_p_seq T1 = max_diamond_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl;
    try destruct x as [a A]; try destruct y as [b B];
      try destruct A; try destruct B; lia.
Qed.

Lemma max_diamond_p_hseq_perm : forall G H,
    Permutation_Type G H ->
    max_diamond_p_hseq G = max_diamond_p_hseq H.
Proof.
  intros G H Hperm; induction Hperm; simpl;
    lia.
Qed.

Lemma max_diamond_p_seq_concat :
  forall L k,
    Forall_inf (fun x => max_diamond_p_seq x < S k)%nat L ->
    (max_diamond_p_seq (concat L) < S k)%nat.
Proof.
  induction L; intros k Hall; inversion Hall; subst; simpl in *; try lia.
  rewrite max_diamond_p_seq_app.
  specialize (IHL k X).
  lia.
Qed.

Lemma complexity_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    HMR_complexity_p_seq T1 = HMR_complexity_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; lia.
Qed.

Lemma complexity_p_hseq_perm : forall G1 G2,
    Permutation_Type G1 G2 ->
    HMR_complexity_p_hseq G1 = HMR_complexity_p_hseq G2.
Proof.
  intros G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - simpl.
    rewrite IHHperm.
    case (HMR_complexity_p_seq x =? fst (HMR_complexity_p_hseq l'));
      case (HMR_complexity_p_seq x <? fst (HMR_complexity_p_hseq l'))%nat; reflexivity.
  - simpl.
    case_eq (HMR_complexity_p_seq x =? fst (HMR_complexity_p_hseq l)); intros H1;
      case_eq (HMR_complexity_p_seq y =? fst (HMR_complexity_p_hseq l)); intros H2;
        case_eq (HMR_complexity_p_seq x <? fst (HMR_complexity_p_hseq l))%nat; intros H3;
          case_eq (HMR_complexity_p_seq y <? fst (HMR_complexity_p_hseq l))%nat; intros H4;
            case_eq (HMR_complexity_p_seq x =? HMR_complexity_p_seq y); intros H5;
              case_eq (HMR_complexity_p_seq x <? HMR_complexity_p_seq y)%nat; intros H6;
                case_eq (HMR_complexity_p_seq y <? HMR_complexity_p_seq x)%nat; intros H7;
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
  - transitivity (HMR_complexity_p_hseq l'); assumption.
Qed.

Lemma complexity_p_hseq_perm_fst : forall G,
    G <> nil ->
    {' (T, H) : _ &
                Permutation_Type G (T :: H) &
                HMR_complexity_p_seq T = fst (HMR_complexity_p_hseq G) }.
  induction G; intros H; [ exfalso; apply H; reflexivity | clear H ].
  simpl.
  case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); intros H1.
  - split with (a, G); try reflexivity.
    apply Nat.eqb_eq in H1; rewrite H1; reflexivity.
  - case_eq (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G))%nat; intros H2.
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
    HMR_complexity_p_hseq (T1 :: G) = HMR_complexity_p_hseq (T2 :: G).
Proof.
  intros T1 T2 G Hperm.
  simpl.
  rewrite (complexity_p_seq_perm _ _ Hperm).
  reflexivity.
Qed.

Lemma complexity_p_seq_app : forall T1 T2,
    HMR_complexity_p_seq (T1 ++ T2) = (HMR_complexity_p_seq T1 + HMR_complexity_p_seq T2)%nat.
Proof.
  induction T1; intros T2; simpl; try rewrite IHT1; try destruct a; lia.
Qed.

Lemma complexity_p_seq_vec : forall r A,
    HMR_complexity_p_seq (vec r A) = (length r * HMR_complexity_term A)%nat.
Proof.
  induction r; intros A; simpl; try rewrite IHr; lia.
Qed.

Lemma p_seq_is_atomic_max_diamond_0 : forall T,
    p_seq_is_atomic T ->
    max_diamond_p_seq T = 0%nat.
Proof.
  intros T; induction T; intros Hat; inversion Hat; subst; try reflexivity.
  destruct a as [a A].
  destruct A; try now inversion X; specialize (IHT X0).
Qed.

Lemma p_seq_is_atomic_basic : forall T,
    p_seq_is_atomic T ->
    p_seq_is_basic T.
Proof.
  induction T; intros Hat; inversion Hat; subst; constructor.
  - destruct a as [a A]; destruct A; inversion X; auto.
  - apply IHT.
    apply X0.
Qed.

Lemma p_seq_is_basic_complexity_0 :
  forall T,
    p_seq_is_basic T ->
    HMR_complexity_p_seq T = 0%nat.
Proof.
  induction T; intros Hat;
    inversion Hat; simpl; try destruct a; try rewrite IHT; try rewrite is_basic_complexity_0;
      auto.
Qed.

Lemma p_seq_is_basic_complexity_0_inv :
  forall T,
    HMR_complexity_p_seq T = 0%nat ->
    p_seq_is_basic T.
Proof.
  induction T; intros Heq; [ apply Forall_inf_nil |] .
  destruct a as [a A]; simpl in *.
  apply Forall_inf_cons ; [ apply is_basic_complexity_0_inv  | apply IHT]; lia.
Qed.

Lemma p_hseq_is_atomic_max_diamond_0 :
  forall G,
    p_hseq_is_atomic G ->
    max_diamond_p_hseq G = 0%nat.
Proof.
  induction G; intros Hat; inversion Hat; subst; simpl; try lia.
  specialize (IHG X0).
  assert (H := p_seq_is_atomic_max_diamond_0 _ X); lia.
Qed.

Lemma p_hseq_is_atomic_basic : forall G,
    p_hseq_is_atomic G ->
    p_hseq_is_basic G.
Proof.
  induction G; intros Hat; inversion Hat; subst; constructor.
  - apply p_seq_is_atomic_basic; assumption.
  - apply IHG; assumption.
Qed.

Lemma p_seq_is_atomic_app : forall T1 T2,
    p_seq_is_atomic T1 ->
    p_seq_is_atomic T2 ->
    p_seq_is_atomic (T1 ++ T2).
Proof.
  induction T1; intros T2 Hat1 Hat2; inversion Hat1; subst; auto.
  simpl; apply Forall_inf_cons; auto.
  apply IHT1; auto.
Qed.

Lemma p_seq_is_atomic_seq_mul : forall r T,
    p_seq_is_atomic T ->
    p_seq_is_atomic (seq_mul r T).
Proof.
  intros r; induction T; intros Hat; inversion Hat; subst; auto.
  destruct a as [a A]; simpl; apply Forall_inf_cons; auto.
  apply IHT.
  apply X0.
Qed.

Lemma p_hseq_is_atomic_flat_map :
  forall k G l,
    p_hseq_is_atomic G ->
    p_hseq_is_atomic (flat_map (fun i : nat => seq_mul (FOL_R_var (k + i)) (nth i G nil)) l :: nil).
Proof.
  intros k G l Hat; revert k; induction l; intros k; apply Forall_inf_cons; try apply Forall_inf_nil.
  simpl.
  apply p_seq_is_atomic_app.
  - apply p_seq_is_atomic_seq_mul.
    case_eq (a <? length G)%nat; intros H; (apply Nat.ltb_lt in H + apply Nat.ltb_nlt in H); [ | rewrite nth_overflow; try lia; apply Forall_inf_nil].
    apply Forall_inf_forall with G; auto.
    apply nth_In_inf; assumption.
  - specialize (IHl k).
    inversion IHl; assumption.
Qed.

Lemma p_seq_is_atomic_perm :
  forall T1 T2,
    Permutation_Type T1 T2 ->
    p_seq_is_atomic T1 ->
    p_seq_is_atomic T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; intros Hat1; try destruct x; try destruct y; repeat apply Forall_inf_cons; try inversion Hat1; try inversion X0; subst; auto.
  - apply IHHperm; apply Forall_inf_nil.
  - apply IHHperm.
    apply Forall_inf_cons; assumption.
Qed.

Lemma p_hseq_is_atomic_perm :
  forall G1 G2,
    Permutation_Type G1 G2 ->
    p_hseq_is_atomic G1 ->
    p_hseq_is_atomic G2.
Proof.
  intros G1 G2 Hperm; induction Hperm; intros Hat1; repeat apply Forall_inf_cons; try inversion Hat1; try inversion X0; subst; auto.
  - apply IHHperm; apply Forall_inf_nil.
  - apply IHHperm.
    apply Forall_inf_cons; assumption.
Qed.

Lemma p_hseq_is_basic_complexity_0 :
  forall G,
    p_hseq_is_basic G ->
    fst (HMR_complexity_p_hseq G) = 0%nat.
Proof.
  induction G; intros Hat; [ reflexivity | ].
  inversion Hat; subst; specialize (IHG X0).
  simpl.
  rewrite p_seq_is_basic_complexity_0 ; [ | apply X].
  rewrite IHG; reflexivity.
Qed.

Lemma p_hseq_is_basic_complexity_0_inv :
  forall G,
    fst (HMR_complexity_p_hseq G) = 0%nat ->
    p_hseq_is_basic G.
Proof.
  induction G; intros Heq; [ apply Forall_inf_nil | ].
  simpl in *.
  case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); intros H; rewrite H in Heq; simpl in Heq ; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H ].
  { apply Forall_inf_cons; [ apply p_seq_is_basic_complexity_0_inv | apply IHG ]; lia. }
  exfalso.
  case_eq (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G))%nat; intros H2; rewrite H2 in Heq; [apply Nat.ltb_lt in H2 | apply Nat.ltb_nlt in H2]; simpl in *; lia.
Qed.

Lemma HMR_complexity_perm_fst_seq : forall G T D,
    Permutation_Type T D ->
    HMR_complexity_p_hseq (T :: G) = HMR_complexity_p_hseq (D :: G).
Proof.
  intros G T D Hperm.
  simpl.
  rewrite complexity_p_seq_perm with _ D; auto.
Qed.

Lemma modal_complexity_perm :forall G H,
    Permutation_Type G H ->
    modal_complexity_p_hseq G = modal_complexity_p_hseq H.
Proof.
  intros G H Hperm.
  unfold modal_complexity_p_hseq.
  rewrite max_diamond_p_hseq_perm with _ H; [ | apply Hperm ].
  rewrite complexity_p_hseq_perm with _ H; auto.
Qed.

Lemma modal_complexity_perm_fst_seq : forall G T D,
    Permutation_Type T D ->
    modal_complexity_p_hseq (T :: G) = modal_complexity_p_hseq (D :: G).
Proof.
  intros G T D Hperm.
  unfold modal_complexity_p_hseq.
  simpl.
  rewrite complexity_p_seq_perm with _ D; auto.
  rewrite max_diamond_p_seq_perm with _ D; auto.
Qed.

Lemma same_modal_complexity_HMR_complexity : forall G H,
    modal_complexity_p_hseq G = modal_complexity_p_hseq H ->
    HMR_complexity_p_hseq G = HMR_complexity_p_hseq H.
Proof.
  intros G H Heq.
  unfold modal_complexity_p_hseq in Heq.
  remember (HMR_complexity_p_hseq G) as pG.
  remember (HMR_complexity_p_hseq H) as pH.
  destruct pG; destruct pH; simpl in *; inversion Heq; auto.
Qed.

Lemma max_diamond_seq_mul : forall T r,
    max_diamond_p_seq (seq_mul r T) = max_diamond_p_seq T.
Proof.
  induction T; intros r; simpl; try specialize (IHT r); try destruct a as [a A];simpl; try lia.
Qed.

Lemma max_diamond_seq_mul_nth :
  forall G v k,
    max_diamond_p_seq (flat_map (fun i : nat => seq_mul (FOL_R_var (k + i)) (nth i G nil)) v) = max_diamond_p_seq (flat_map (fun i : nat => nth i G nil) v).
Proof.
  intros G; induction v; intros k; auto.
  simpl in *.
  rewrite ? max_diamond_p_seq_app; rewrite IHv.
  rewrite max_diamond_seq_mul.
  reflexivity.
Qed.

Lemma complexity_seq_mul : forall T r,
    HMR_complexity_p_seq (seq_mul r T) = HMR_complexity_p_seq T.
Proof.
  induction T; intros r; simpl; try specialize (IHT r); try destruct a as [a A];simpl; try lia.
Qed.

Lemma complexity_seq_mul_nth :
  forall G v k,
    HMR_complexity_p_seq (flat_map (fun i : nat => seq_mul (FOL_R_var (k + i)) (nth i G nil)) v) = HMR_complexity_p_seq (flat_map (fun i : nat => nth i G nil) v).
Proof.
  intros G; induction v; intros k; auto.
  simpl in *.
  rewrite ? complexity_p_seq_app; rewrite IHv.
  rewrite complexity_seq_mul.
  reflexivity.
Qed.

Lemma max_diamond_nth : forall G i,
    (max_diamond_p_seq (nth i G nil) <= max_diamond_p_hseq G)%nat.
Proof.
  induction G; intros i; destruct i; simpl; try lia.
  specialize (IHG i).
  lia.
Qed.

Lemma max_diamond_flat_map : forall G l,
    (max_diamond_p_hseq (flat_map (fun x : nat => only_diamond_p_seq (nth x G nil)) l :: nil) <=
     max_diamond_p_hseq (only_diamond_p_hseq G))%nat.
Proof.
  intros G; induction l; simpl; try lia.
  rewrite max_diamond_p_seq_app.
  rewrite <- map_nth.
  simpl (only_diamond_p_seq nil).
  transitivity (Nat.max
                  (Nat.max (max_diamond_p_hseq (map only_diamond_p_seq G))
                           (max_diamond_p_seq (flat_map (fun x : nat => only_diamond_p_seq (nth x G nil)) l))) 0); [ apply Nat.max_le_compat_r; apply Nat.max_le_compat_r; apply max_diamond_nth | ].
  simpl in IHl.
  change (map only_diamond_p_seq G) with (only_diamond_p_hseq G).
  lia.
Qed.

Lemma max_diamond_only_diamond_p_seq_eq_0 : forall T,
    max_diamond_p_seq T = 0%nat ->
    max_diamond_p_seq (only_diamond_p_seq T) = 0%nat.
Proof.
  induction T; try destruct a as [a A]; try destruct A; simpl in *; try lia.
  change (match max_diamond_p_seq T with
          | 0%nat => S (max_diamond_term A)
          | S m' => S (Nat.max (max_diamond_term A) m')
          end) with (Nat.max (S (max_diamond_term A)) (max_diamond_p_seq T)).
  lia.
Qed.

Lemma max_diamond_only_diamond_p_seq_lt_0 : forall T,
    (0 < max_diamond_p_seq T)%nat ->
    (max_diamond_p_seq (only_diamond_p_seq T) < (max_diamond_p_seq T))%nat.
Proof.
  induction T; intros Hlt; try now inversion Hlt.
  case_eq (0 <? max_diamond_p_seq T)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H].
  - specialize (IHT H).
    destruct a as [a A]; destruct A; simpl in *;
      try lia.
    change (match max_diamond_p_seq T with
            | 0 => S (max_diamond_term A)
            | S m' => S (Nat.max (max_diamond_term A) m')
            end)%nat with (Nat.max (S (max_diamond_term A)) (max_diamond_p_seq T)) in *.
    lia.
  - destruct a as [a A]; simpl in *.
    destruct A; simpl in *;
      replace (max_diamond_p_seq T) with 0%nat by lia;
      replace (max_diamond_p_seq (only_diamond_p_seq T)) with 0%nat;
      try (symmetry; apply max_diamond_only_diamond_p_seq_eq_0; lia);
      try lia.
Qed.

Lemma max_diamond_only_diamond_p_hseq_eq_0 : forall G,
    max_diamond_p_hseq G = 0%nat ->
    max_diamond_p_hseq (only_diamond_p_hseq G) = 0%nat.
Proof.
  induction G; intros H; simpl in *; try lia.
  rewrite max_diamond_only_diamond_p_seq_eq_0; lia.
Qed.
  
Lemma max_diamond_only_diamond_p_hseq_lt : forall G,
    (0 < max_diamond_p_hseq G)%nat ->
    (max_diamond_p_hseq (only_diamond_p_hseq G) < max_diamond_p_hseq G)%nat.
Proof.
  induction G; intros Hlt; try now inversion Hlt.
  simpl in Hlt.
  simpl.
  case_eq (0 <? (max_diamond_p_seq a))%nat; intros H1; case_eq (0 <? (max_diamond_p_hseq G))%nat; intros H2;
    (apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1);
    (apply Nat.ltb_lt in H2 + apply Nat.ltb_nlt in H2);
    try (specialize (IHG H2));
    try assert (H3 := max_diamond_only_diamond_p_seq_lt_0 _ H1);
    try lia.
  - rewrite max_diamond_only_diamond_p_hseq_eq_0; lia.
  - rewrite max_diamond_only_diamond_p_seq_eq_0; lia.
Qed.

Lemma modal_complexity_only_diamond_p_seq :
  forall G v n k ,
    max_diamond_p_hseq G = S n ->
    (modal_complexity_p_hseq (flat_map (fun i : nat => seq_mul (FOL_R_var (k + i)) (only_diamond_p_seq (nth i G nil))) v :: nil) <3 modal_complexity_p_hseq G).
Proof.
  intros G v n k Heq.
  apply fst_lt3.
  apply Nat.le_lt_trans with (max_diamond_p_hseq (only_diamond_p_hseq G)).
  - simpl.
    replace (fun i => seq_mul (FOL_R_var (k + i)) (only_diamond_p_seq (nth i G nil))) with (fun i => seq_mul (FOL_R_var (k + i)) (nth i (map only_diamond_p_seq G) (only_diamond_p_seq nil))).
    2:{ apply functional_extensionality; intros x.
        rewrite map_nth; auto. }
    rewrite max_diamond_seq_mul_nth.
    replace (fun i => nth i (map only_diamond_p_seq G) nil) with (fun i => only_diamond_p_seq (nth i G nil)).
    2:{ apply functional_extensionality; intros x.
        change nil with (only_diamond_p_seq nil); rewrite map_nth; auto. }
    apply max_diamond_flat_map.
  - apply max_diamond_only_diamond_p_hseq_lt.
    lia.
Qed.

Lemma hmrr_Z_decrease_complexity : forall G T r,
    r <> nil ->
    HMR_complexity_p_seq (vec r HMR_zero ++ T) = fst (HMR_complexity_p_hseq ((vec r HMR_zero ++ T) :: G)) ->
    HMR_complexity_p_hseq (T :: G) <2 HMR_complexity_p_hseq ((vec r HMR_zero ++ T) :: G).
Proof.
  intros G T r Hnnil Heq.
  simpl.
  case_eq (HMR_complexity_p_seq T =? fst (HMR_complexity_p_hseq G)); intros H1; case_eq (HMR_complexity_p_seq (vec r HMR_zero ++ T) =? fst (HMR_complexity_p_hseq G)); intros H2.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H2.
    rewrite complexity_p_seq_app in H2.
    lia.
  - case_eq (HMR_complexity_p_seq (vec r HMR_zero ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HMR_complexity_p_seq T <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite complexity_p_seq_app in H2; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HMR_complexity_p_seq T <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HMR_complexity_p_seq (vec r HMR_zero ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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
    
Lemma hmrr_plus_decrease_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A +S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G)) ->
    HMR_complexity_p_hseq ((vec r A ++ vec r B ++ T) :: G) <2 HMR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HMR_complexity_p_seq (vec r A ++ vec r B ++ T) =? fst (HMR_complexity_p_hseq G)); intros H1; case_eq (HMR_complexity_p_seq (vec r (A +S B) ++ T) =? fst (HMR_complexity_p_hseq G)); intros H2; rewrite 2 complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HMR_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HMR_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HMR_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HMR_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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

Lemma hmrr_mul_decrease_complexity : forall G T A r0 r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (r0 *S A) ++ T) = fst (HMR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G)) ->
    HMR_complexity_p_hseq ((vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) :: G) <2 HMR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros G T A r0 r Hnnil Heq.
  simpl.
  case_eq (HMR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) =? fst (HMR_complexity_p_hseq G)); intros H1; case_eq (HMR_complexity_p_seq (vec r (r0 *S A) ++ T) =? fst (HMR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    rewrite mul_vec_length in H1.
    lia.
  - case_eq (HMR_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
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
  - case_eq (HMR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in *; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HMR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HMR_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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

Lemma hmrr_min_r_decrease_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HMR_complexity_p_hseq ((vec r A ++ T) :: G) <2 HMR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HMR_complexity_p_seq (vec r A ++ T) =? fst (HMR_complexity_p_hseq G)); intros H1; case_eq (HMR_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HMR_complexity_p_hseq G)); intros H2; rewrite ? complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HMR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HMR_complexity_p_seq (vec r A ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HMR_complexity_p_seq (vec r A ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HMR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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

Lemma hmrr_min_l_decrease_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HMR_complexity_p_hseq ((vec r B ++ T) :: G) <2 HMR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HMR_complexity_p_seq (vec r B ++ T) =? fst (HMR_complexity_p_hseq G)); intros H1; case_eq (HMR_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HMR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HMR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HMR_complexity_p_seq (vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HMR_complexity_p_seq (vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HMR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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

Lemma hmrr_max_decrease_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A \/S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G)) ->
    HMR_complexity_p_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) <2 HMR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HMR_complexity_p_seq (vec r A ++ T) =? fst (HMR_complexity_p_hseq G)); intros H1; case_eq (HMR_complexity_p_seq (vec r (A \/S B) ++ T) =? fst (HMR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HMR_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + simpl.
      case_eq (HMR_complexity_p_seq (vec r B ++ T) =? fst (HMR_complexity_p_hseq G)); intros H4.
      * apply fst_lt2.
        apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
        lia.
      * case_eq (HMR_complexity_p_seq (vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H5.
        -- apply fst_lt2.
           apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
           lia.
        -- apply fst_lt2.
           rewrite ? complexity_p_seq_app; rewrite ? complexity_p_seq_vec; destruct r; [ exfalso; apply Hnnil; reflexivity | ]; simpl; lia.        
  - replace (HMR_complexity_p_seq (vec r A ++ T) <? fst (HMR_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_neq in H1; apply Nat.eqb_eq in H2.
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    simpl.
    replace (HMR_complexity_p_seq (vec r B ++ T) =? fst (HMR_complexity_p_hseq G)) with false.
    2:{ symmetry.
        apply Nat.eqb_neq; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    replace (HMR_complexity_p_seq (vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    apply snd_lt2; lia.
  - simpl in Heq.
    rewrite H2 in Heq.
    assert ((HMR_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HMR_complexity_p_hseq G))%nat = false) as H3.
    { apply Nat.ltb_nlt; apply Nat.eqb_neq in H2.
      intros H; apply Nat.ltb_lt in H.
      rewrite H in Heq.
      simpl in Heq.
      apply H2; apply Heq. }
    rewrite H3; clear Heq.
    case_eq (HMR_complexity_p_seq (vec r A ++ T) <? fst (HMR_complexity_p_hseq G))%nat; intros H4; simpl.
    + case (HMR_complexity_p_seq (vec r B ++ T) =? fst (HMR_complexity_p_hseq G));
        [ | case (HMR_complexity_p_seq (vec r B ++ T) <? fst (HMR_complexity_p_hseq G))%nat];
        apply fst_lt2; apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4;
          rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
            (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
    + case (HMR_complexity_p_seq (vec r B ++ T) =? HMR_complexity_p_seq (vec r A ++ T));
        [ | case (HMR_complexity_p_seq (vec r B ++ T) <? HMR_complexity_p_seq (vec r A ++ T))%nat];
      apply fst_lt2;
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
          (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
Qed.

Lemma hmrr_Z_decrease_modal_complexity : forall G T r,
    r <> nil ->
    HMR_complexity_p_seq (vec r HMR_zero ++ T) = fst (HMR_complexity_p_hseq ((vec r HMR_zero ++ T) :: G)) ->
    modal_complexity_p_hseq (T :: G) <3 modal_complexity_p_hseq ((vec r HMR_zero ++ T) :: G).
Proof.
  intros G T r Hnnil Heq.
  unfold modal_complexity_p_hseq.
  replace (max_diamond_p_hseq ((vec r HMR_zero ++ T) :: G)) with (max_diamond_p_hseq (T :: G)).
  2:{ simpl; rewrite max_diamond_p_seq_app.
      rewrite max_diamond_p_seq_vec; auto. }
  apply lt_nat2_fst_eq_lt_nat3.
  apply hmrr_Z_decrease_complexity; auto.
Qed.
    
Lemma hmrr_plus_decrease_modal_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A +S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G)) ->
    modal_complexity_p_hseq ((vec r A ++ vec r B ++ T) :: G) <3 modal_complexity_p_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  unfold modal_complexity_p_hseq.
  replace (max_diamond_p_hseq ((vec r (A +S B) ++ T) :: G)) with (max_diamond_p_hseq ((vec r A ++ vec r B ++ T) :: G)).
  2:{ simpl; rewrite ? max_diamond_p_seq_app.
      rewrite ? max_diamond_p_seq_vec; simpl; auto.
      lia. }
  apply lt_nat2_fst_eq_lt_nat3.
  apply hmrr_plus_decrease_complexity; auto.
Qed.

Lemma hmrr_mul_decrease_modal_complexity : forall G T A r0 r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (r0 *S A) ++ T) = fst (HMR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G)) ->
    modal_complexity_p_hseq ((vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) :: G) <3 modal_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros G T A r0 r Hnnil Heq.
  unfold modal_complexity_p_hseq.
  replace (max_diamond_p_hseq ((vec r (r0 *S A) ++ T) :: G)) with (max_diamond_p_hseq ((vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) :: G)).
  2:{ simpl; rewrite ? max_diamond_p_seq_app.
      rewrite ? max_diamond_p_seq_vec; simpl; auto.
      intros H; destruct r; [ now apply Hnnil | inversion H]. }
  apply lt_nat2_fst_eq_lt_nat3.
  apply hmrr_mul_decrease_complexity; auto.
Qed.

Lemma hmrr_min_r_decrease_modal_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    modal_complexity_p_hseq ((vec r A ++ T) :: G) <3 modal_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  unfold modal_complexity_p_hseq.
  case_eq (max_diamond_p_hseq ((vec r A ++ T) :: G) =? max_diamond_p_hseq ((vec r (A /\S B) ++ T) :: G)).
  + intros HeqA; apply Nat.eqb_eq in HeqA.
    rewrite HeqA.
    apply lt_nat2_fst_eq_lt_nat3.
    apply hmrr_min_r_decrease_complexity; auto.
  + intros HeqA; apply Nat.eqb_neq in HeqA.
    apply fst_lt3.
    clear Heq.
    simpl in *.
    rewrite ? max_diamond_p_seq_app in *.
    rewrite ? max_diamond_p_seq_vec in *; auto.
    simpl in *.
    lia.
Qed.

Lemma hmrr_min_l_decrease_modal_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    modal_complexity_p_hseq ((vec r B ++ T) :: G) <3 modal_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  unfold modal_complexity_p_hseq.
  case_eq (max_diamond_p_hseq ((vec r B ++ T) :: G) =? max_diamond_p_hseq ((vec r (A /\S B) ++ T) :: G)).
  + intros HeqB; apply Nat.eqb_eq in HeqB.
    rewrite HeqB.
    apply lt_nat2_fst_eq_lt_nat3.
    apply hmrr_min_l_decrease_complexity; auto.
  + intros HeqB; apply Nat.eqb_neq in HeqB.
    apply fst_lt3.
    clear Heq.
    simpl in *.
    rewrite ? max_diamond_p_seq_app in *.
    rewrite ? max_diamond_p_seq_vec in *; auto.
    simpl in *.
    lia.
Qed.

Lemma hmrr_max_decrease_modal_complexity : forall G T A B r,
    r <> nil ->
    HMR_complexity_p_seq (vec r (A \/S B) ++ T) = fst (HMR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G)) ->
    modal_complexity_p_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) <3 modal_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  unfold modal_complexity_p_hseq.
  replace (max_diamond_p_hseq ((vec r (A \/S B) ++ T) :: G)) with (max_diamond_p_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G)).
  2:{ simpl; rewrite ? max_diamond_p_seq_app.
      rewrite ? max_diamond_p_seq_vec; simpl; auto.
      lia. }
  apply lt_nat2_fst_eq_lt_nat3.
  apply hmrr_max_decrease_complexity; auto.
Qed.

(** ** max_var *)

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

Lemma max_var_weight_p_seq_app:
  forall T1 T2,
    max_var_weight_p_seq (T1 ++ T2) = Nat.max
                                        (max_var_weight_p_seq T1)
                                        (max_var_weight_p_seq T2).
Proof.
  induction T1; intros T2; try specialize (IHT1 T2); try destruct a; simpl in *; try lia.
Qed.

Lemma max_var_weight_p_seq_only_diamond :
  forall T,
    (max_var_weight_p_seq (only_diamond_p_seq T) <= max_var_weight_p_seq T)%nat.
Proof.
  induction T; try destruct a as [a A]; try destruct A; simpl in *; lia.
Qed.

Lemma max_var_weight_p_hseq_only_diamond :
  forall G,
    (max_var_weight_p_hseq (only_diamond_p_hseq G) <= max_var_weight_p_hseq G)%nat.
Proof.
  induction G; simpl in *; try (assert (H := max_var_weight_p_seq_only_diamond a)); lia.
Qed.

Lemma max_var_FOL_R_term_In_inf_p_seq :
  forall a A T,
    In_inf (a, A) T ->
    (max_var_FOL_R_term a <= max_var_weight_p_seq T)%nat.
Proof.
  intros a A; induction T; intros Hin; try destruct a0 as [b B]; simpl in *; inversion Hin; try (inversion H; subst); try specialize (IHT X); lia.
Qed.

Lemma max_var_weight_p_seq_In_inf_p_hseq :
  forall T G,
    In_inf T G ->
    (max_var_weight_p_seq T <= max_var_weight_p_hseq G)%nat.
Proof.
  intros T; induction G; intros Hin; simpl in *; inversion Hin; subst; try specialize (IHG X); lia.
Qed.

Lemma max_var_weight_p_seq_concat :
  forall L k,
    L <> nil ->
    Forall_inf (fun x => max_var_weight_p_seq x < k)%nat L ->
    (max_var_weight_p_seq (concat L) < k)%nat.
Proof.
  induction L; intros k Hnnil Hall; inversion Hall; subst; simpl in *; [exfalso; apply Hnnil; reflexivity | ].
  rewrite max_var_weight_p_seq_app.
  destruct L; try (simpl; lia).
  apply Nat.max_lub_lt; auto.
  apply IHL; auto.
  intros H'; inversion H'.
Qed.

Lemma max_var_weight_p_seq_seq_mul :
  forall r T,
    T <> nil ->
    max_var_weight_p_seq (seq_mul r T) = Nat.max (max_var_FOL_R_term r) (max_var_weight_p_seq T).
Proof.
  intros r; induction T; intros Hnnil; [exfalso; apply Hnnil; reflexivity | ]; destruct a as [a A]; simpl.
  destruct T; [simpl; lia | ].
  assert (p :: T <> nil).
  { intros H; inversion H. }
  specialize (IHT H).
  lia.
Qed.

(** ** well defined *)
Lemma p_seq_well_defined_perm : forall val T D,
    Permutation_Type T D ->
    p_seq_well_defined val T ->
    p_seq_well_defined val D.
Proof.
  intros val T D Hperm Hall.
  apply (Forall_inf_Permutation_Type _ _ _ _ Hperm Hall).
Qed.

Lemma p_hseq_well_defined_perm : forall val G H,
    Permutation_Type G H ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val H.
Proof.
  intros val G H Hperm Hall.
  apply (Forall_inf_Permutation_Type _ _ _ _ Hperm Hall).
Qed.

Lemma p_seq_well_defined_seq_mul : forall val T r,
    0 < FOL_R_term_sem val r ->
    p_seq_well_defined val T ->
    p_seq_well_defined val (seq_mul r T).
Proof.
  intros val; induction T; intros r Hr Hwd; auto.
  inversion Hwd; subst.
  destruct a as [a A].
  apply Forall_inf_cons; [ | apply (IHT r Hr); apply X ].
  apply R_blt_lt; apply R_blt_lt in H0.
  simpl in *; nra.
Qed.

Lemma p_seq_well_defined_only_diamond :
  forall val T,
    p_seq_well_defined val T ->
    p_seq_well_defined val (only_diamond_p_seq T).
Proof.
  intros val T; induction T; intros Hwd; auto.
  inversion Hwd; subst.
  destruct a as [a A].
  destruct A; try (apply Forall_inf_cons; auto); apply IHT; apply X.
Qed.

Lemma well_defined_concat :forall val G,
    Forall_inf (p_seq_well_defined val) G ->
    p_seq_well_defined val (concat G).
Proof.
  intros val; induction G; intros Hall; inversion Hall as [ | x1 x2 Hwd Hall']; subst.
  - simpl.
    apply Forall_inf_nil.
  - simpl.
    apply Forall_inf_app; auto.
    apply IHG.
    apply Hall'.
Qed.

Lemma p_seq_well_defined_upd_val :
  forall val T x r,
    (max_var_weight_p_seq T < x)%nat ->
    p_seq_well_defined val T ->
    p_seq_well_defined (upd_val val x r) T.
Proof.
  intros val T x r; induction T; intros Hlt Hwd; [ apply Forall_inf_nil | ].
  destruct a as [a A].
  inversion Hwd; subst.
  simpl in *; apply Forall_inf_cons; [ | apply IHT; auto; lia].
  simpl.
  rewrite upd_val_term_lt; auto.
  lia.
Qed.

Lemma p_hseq_well_defined_upd_val:
  forall val G x r,
    (max_var_weight_p_hseq G < x)%nat ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined (upd_val val x r) G.
Proof.
  intros val G x r; induction G; intros Hlt Hwd; [ apply Forall_inf_nil | ].
  inversion Hwd; subst.
  simpl in *; apply Forall_inf_cons; [ | apply IHG; auto; lia].
  apply p_seq_well_defined_upd_val; auto.
  lia.
Qed.

Lemma p_seq_well_defined_upd_val_vec:
  forall val T vx vr,
    Forall_inf (fun x => (max_var_weight_p_seq T < x)%nat) vx ->
    p_seq_well_defined val T ->
    p_seq_well_defined (upd_val_vec val vx vr) T.
Proof.
  intros val T vx; revert val; induction vx; intros val vr Hall Hwd; auto.
  destruct vr; simpl; inversion Hall; subst; auto.
  apply IHvx; auto.
  apply p_seq_well_defined_upd_val; auto.
Qed.

Lemma p_hseq_well_defined_upd_val_vec :
  forall val G vx vr,
    Forall_inf (fun x => max_var_weight_p_hseq G < x)%nat vx ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined (upd_val_vec val vx vr) G.
Proof.
  intros val G vx; revert val; induction vx; intros val vr Hlt Hwd; auto.
  destruct vr; auto.
  simpl.
  inversion Hlt; subst.
  apply IHvx; auto.
  apply p_hseq_well_defined_upd_val; auto.
Qed.


(** ** to_p_hypersequent and eval_p_sequent *)

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

Lemma eval_p_sequent_upd_val_lt : forall val T x r,
    (max_var_weight_p_seq T < x)%nat ->
    eval_p_sequent (upd_val val x r) T = eval_p_sequent val T.
Proof.
  intros val; induction T; intros x r Hlt; simpl in *; auto.
  destruct a as [a A].
  rewrite upd_val_term_lt; try lia.
  rewrite IHT; try lia.
  reflexivity.
Qed.

Lemma eval_p_sequent_upd_val_vec_lt : forall val T vx vr,
    Forall_inf (fun x => (max_var_weight_p_seq T < x)%nat) vx ->
    eval_p_sequent (upd_val_vec val vx vr) T = eval_p_sequent val T.
Proof.
  intros val T vx; revert val; induction vx; intros val vr Hall; auto.
  inversion Hall; subst.
  destruct vr; auto.
  simpl; rewrite IHvx; auto.
  rewrite eval_p_sequent_upd_val_lt; auto.
Qed.

Lemma eval_p_hseq_upd_val_lt : forall val G x r,
    (max_var_weight_p_hseq G < x)%nat ->
    map (eval_p_sequent (upd_val val x r)) G = map (eval_p_sequent val) G.
Proof.
  intros val; induction G; intros x r Hlt; simpl in *; auto.
  simpl; rewrite eval_p_sequent_upd_val_lt; try lia.
  rewrite IHG; try lia.
  reflexivity.
Qed.

Lemma eval_p_hseq_upd_val_vec_lt : forall val G vx vr,
    Forall_inf (fun x => (max_var_weight_p_hseq G < x)%nat) vx ->
    map (eval_p_sequent (upd_val_vec val vx vr)) G = map (eval_p_sequent val) G.
Proof.
  intros val G vx; revert val; induction vx; intros val vr Hall; auto.
  inversion Hall; subst.
  destruct vr; auto.
  simpl; rewrite IHvx; auto.
  rewrite eval_p_hseq_upd_val_lt; auto.
Qed.
   
Lemma eval_p_sequent_app :
  forall val T1 T2,
    eval_p_sequent val (T1 ++ T2) = eval_p_sequent val T1 ++ eval_p_sequent val T2.
Proof.
  intros val; induction T1; intros T2; simpl; try destruct a as [a A];
    try sem_is_pos_decomp val a; intros; try rewrite IHT1; try rewrite app_assoc; reflexivity.
Qed.

Lemma only_diamond_eval_p_seq:
  forall val T,
    only_diamond_seq (eval_p_sequent val T) = eval_p_sequent val (only_diamond_p_seq T).
Proof.
  intros val; induction T; simpl; try destruct a as [a A]; auto.
  sem_is_pos_decomp val a; destruct A; simpl; sem_is_pos_decomp val a; intros; simpl; rewrite IHT; try (replace H with H0 by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec) ); try reflexivity;
    try (exfalso;
         clear - H H0;
         try apply R_blt_lt in H + apply R_blt_nlt in H;
         try apply R_blt_lt in H0 + apply R_blt_nlt in H0;
         lra).
Qed.

Lemma only_diamond_eval_p_hseq :
  forall val G,
    only_diamond_hseq (map (eval_p_sequent val) G) = map (eval_p_sequent val) (only_diamond_p_hseq G).
Proof.
  intros val; induction G; simpl; try rewrite IHG; auto.
  rewrite only_diamond_eval_p_seq; reflexivity.
Qed.

Lemma max_diamond_eval_p_seq :
  forall val T,
    (max_diamond_seq (eval_p_sequent val T) <= max_diamond_p_seq T)%nat.
Proof.
  intros val; induction T; simpl; try lia.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros;simpl; try lia.
  rewrite <- max_diamond_minus.
  lia.
Qed.

Lemma max_diamond_eval_p_hseq :
  forall val G,
    (max_diamond_hseq (map (eval_p_sequent val) G) <= max_diamond_p_hseq G)%nat.
Proof.
  intros val; induction G; simpl; try lia.
  assert (H := max_diamond_eval_p_seq val a).
  lia.
Qed.


