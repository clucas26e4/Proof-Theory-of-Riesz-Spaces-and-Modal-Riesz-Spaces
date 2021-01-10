(** * Implementation of Section 4.2 *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.hmr_perm_lemmas.

Require Import CMorphisms.
Require Import Lra.

Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** Diamond case in the proof of Lemma 4.12 *)
Lemma hmrr_ID_diamond P : forall L A,
    (forall T r s, sum_vec r = sum_vec s -> HMR P (T :: nil) -> HMR P ((vec s (-S A) ++ vec r A ++ T) :: nil)) ->
    Forall_inf (fun x => sum_vec (snd (fst x)) = sum_vec (fst (fst x))) L ->
    HMR P (map (fun x => snd x) L) ->
    HMR P (map (fun x => (vec (fst (fst x)) (-S (<S> A)) ++ vec (snd (fst x)) (<S> A) ++ snd x)) L).
Proof.
  intros L A H Hsum pi.
  remember (map (fun x : list Rpos * list Rpos * sequent => snd x) L) as G.
  assert (Allperm G (map (fun x => snd x) L)) by (rewrite <- HeqG; clear; induction G; simpl; try now constructor).
  clear HeqG.
  revert L H Hsum X.
  induction pi; intros L IH Hsum Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X; destruct p as [r T]; destruct T; inversion X.
    simpl.
    rewrite ? vec_diamond.
    change (@nil (Rpos * term)) with (seq_diamond nil).
    rewrite <- ? seq_diamond_app.
    apply hmrr_diamond_no_one.
    apply IH.
    + inversion Hsum; assumption.
    + apply hmrr_INIT.    
  - destruct L; inversion Hperm; subst.
    simpl; apply hmrr_W.
    apply IHpi; inversion Hsum; try assumption.
  - destruct L; inversion Hperm; subst.
    simpl; apply hmrr_C.
    change ((vec (fst (fst p)) (<S> (-S A)) ++ vec (snd (fst p)) (<S> A) ++ snd p)
              :: (vec (fst (fst p)) (<S> (-S A)) ++ vec (snd (fst p)) (<S> A) ++ snd p)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with (map (fun x : list Rpos * list Rpos * list (Rpos * term) => vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (p :: p :: L)).
    apply IHpi; inversion Hsum; subst; try assumption; do 2 try now constructor.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[s1 r1] T1']; destruct p0 as [[s2 r2] T2']; simpl in *.
    apply hmrr_S.
    apply hmrr_ex_seq with (vec (s1 ++ s2) (<S> (-S A)) ++ vec (r1 ++ r2) (<S> A) ++ (T1' ++ T2')).
    { rewrite ? vec_app.
      Permutation_Type_solve. }
    change ((vec (s1 ++ s2) (<S> (-S A)) ++ vec (r1 ++ r2) (<S> A) ++ T1' ++ T2')
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1 ++ s2, r1 ++ r2),T1' ++ T2')::L)).
    inversion Hsum; inversion X3; subst.
    apply IHpi; try assumption; simpl in *; try constructor; try assumption ; [ | now apply Permutation_Type_app].
    simpl.
    rewrite ? sum_vec_app; nra.    
  - destruct L; inversion Hperm; subst.
    destruct p as [[s r] T]; simpl in *.
    apply hmrr_ex_seq with ((vec s (<S> (-S A)) ++ vec r (<S> A) ++ T1) ++ T2) ; [ Permutation_Type_solve | ].
    inversion Hsum; subst.
    apply hmrr_M; try assumption.
    2:{ change (T2
                  :: map
                  (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                     vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
          with
            (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                    vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((nil,nil), T2) :: L)).
        apply IHpi2; simpl; try assumption; try constructor; try assumption; try reflexivity. }
    change ((vec s (<S> (-S A)) ++ vec r (<S> A) ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s,r), T1) :: L)).
    apply IHpi1; simpl; try assumption; try constructor; try assumption; reflexivity.    
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl.
    apply hmrr_T with r; try assumption.
    rewrite ? seq_mul_app.
    rewrite ? seq_mul_vec_mul_vec.
    change ((vec (mul_vec r s1) (<S> (-S A)) ++ vec (mul_vec r r1) (<S> A) ++ seq_mul r T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((mul_vec r s1, mul_vec r r1),seq_mul r T1)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption ; [ | apply seq_mul_perm; apply X].
    simpl in *.
    rewrite ? mul_vec_sum_vec; nra.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec s (HMR_covar n) ++ vec r (HMR_var n) ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_ID; try assumption.
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec r HMR_zero ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_Z.
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec r (A0 +S B) ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_plus.
    apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r A0 ++ vec r B ++ T); [ Permutation_Type_solve | ].          
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r A0 ++ vec r B ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),vec r A0 ++ vec r B ++ T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_mul.
    apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec (mul_vec r0 r) A0 ++ T); [ Permutation_Type_solve | ].          
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec (mul_vec r0 r) A0 ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),vec (mul_vec r0 r) A0 ++ T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec r (A0 \/S B) ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_max.
    apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r B ++ T); [ Permutation_Type_solve | ].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r A0 ++ T); [ Permutation_Type_solve | ].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r B ++ T) :: (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r A0 ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),vec r B ++ T)::((s1,r1),vec r A0 ++ T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try constructor; try assumption; try reflexivity.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec r (A0 /\S B) ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_min.
    + apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r A0 ++ T); [ Permutation_Type_solve | ].
      change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r A0 ++ T)
                :: map
                (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                   vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
        with
          (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                  vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),vec r A0 ++ T)::L)).
      apply IHpi1; try assumption; simpl; try constructor; try assumption; try reflexivity.
    + apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r B ++ T); [ Permutation_Type_solve | ].
      change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec r B ++ T)
                :: map
                (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                   vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
        with
          (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                  vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),vec r B ++ T)::L)).
      apply IHpi2; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_one; try assumption.       
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0.
    destruct p as [[s' r'] T']; simpl in *; subst.
    apply hmrr_ex_seq with (vec s HMR_coone ++ vec r HMR_one ++ seq_diamond (vec s' (-S A) ++ vec r' A ++ T)).
    { rewrite ? seq_diamond_app.
      rewrite ? vec_diamond.
      Permutation_Type_solve. }
    apply hmrr_diamond; try assumption.
    apply hmrr_ex_seq with (vec s' (-S A) ++ vec r' A ++ (vec s HMR_coone ++ vec r HMR_one ++ T)) ; [ Permutation_Type_solve | ].
    apply IH; try assumption.
    inversion Hsum; simpl in *; nra.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p0 as [[s1 r1] T]; simpl in *.
    apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T1) ; [ Permutation_Type_solve | ].
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                   vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1),T1)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
  - destruct (Permutation_Type_Forall2_inf (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi; rewrite Heq in f; try assumption; simpl; try constructor; try assumption.
    clear - Hperm1 Hsum.
    revert Hsum; induction Hperm1; intros Hsum.
    + apply Forall_inf_nil.
    + inversion Hsum; apply Forall_inf_cons; try assumption.
      apply IHHperm1; assumption.
    + inversion Hsum; inversion X; subst.
      apply Forall_inf_cons; try assumption; apply Forall_inf_cons; try assumption.
    + apply IHHperm1_2; apply IHHperm1_1; apply Hsum.
  - destruct L; inversion Hperm; inversion Hsum; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec s (-S A0) ++ vec r A0 ++ T); [ Permutation_Type_solve | ].
    change ((vec s1 (<S> (-S A)) ++ vec r1 (<S> A) ++ vec s (-S A0) ++ vec r A0 ++  T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with
        (map (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s1,r1), vec s (-S A0) ++ vec r A0 ++ T)::L)).
    apply IHpi; try assumption; simpl; try constructor; try assumption; try reflexivity.
Qed.    

(** Proof of Lemma 4.12 *)
Lemma hmrr_ID_gen P : forall G T A r s, sum_vec r = sum_vec s -> HMR P (T :: G) -> HMR P ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  intros G T A; revert G T.
  induction A;intros G T r0 s Heq pi; unfold HMR_minus; fold HMR_minus.
  - apply hmrr_ID; assumption.
  - apply hmrr_ex_seq with (vec r0 (HMR_covar n) ++ vec s (HMR_var n) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_ID; try symmetry; assumption.
  - apply hmrr_Z; apply hmrr_Z; apply pi.
  - apply hmrr_plus.
    apply hmrr_ex_seq with (vec r0 (A1 +S A2) ++ vec s (-S A1) ++ vec s (-S A2) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_plus.
    eapply hmrr_ex_seq.
    2:{ eapply IHA1; [ apply Heq | ].
        eapply hmrr_ex_seq.
        2:{ eapply IHA2; [ apply Heq | apply pi ]. }
        Permutation_Type_solve. }
    Permutation_Type_solve.
  - apply hmrr_mul.
    eapply hmrr_ex_seq with (vec r0 (r *S A) ++ vec (mul_vec r s) (-S A) ++ T) ; [ Permutation_Type_solve | ].
    apply hmrr_mul.
    apply hmrr_ex_seq with (vec (mul_vec r s) (-S A) ++ vec (mul_vec r r0) A ++ T); [ Permutation_Type_solve | ].
    apply IHA ; [ | apply pi].
    rewrite ? mul_vec_sum_vec.
    destruct r as [r Hmr].
    simpl.
    apply R_blt_lt in Hmr.
    nra.
  - apply hmrr_min.
    + apply hmrr_ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A1) ++ T); [Permutation_Type_solve | ].
      apply hmrr_max.
      apply hmrr_W.
      eapply hmrr_ex_seq; [ | apply IHA1; [ apply Heq | apply pi] ].
      Permutation_Type_solve.
    + apply hmrr_ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A2) ++ T); [Permutation_Type_solve | ].
      apply hmrr_max.
      apply hmrr_ex_hseq with ((vec r0 A1 ++ vec s (-S A2) ++ T) :: (vec r0 A2 ++ vec s (-S A2) ++ T) :: G) ; [ Permutation_Type_solve | ]. 
      apply hmrr_W.
      eapply hmrr_ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      Permutation_Type_solve.
  - apply hmrr_ex_seq with (vec r0 (A1 /\S A2) ++ vec s (-S A1 \/S -S A2) ++ T); [ Permutation_Type_solve | ].
    apply hmrr_min.
    + apply hmrr_ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A1) ++ T); [Permutation_Type_solve | ].
      apply hmrr_max.
      apply hmrr_W.
      apply IHA1; [ apply Heq | apply pi].
    + apply hmrr_ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A2) ++ T); [Permutation_Type_solve | ].
      apply hmrr_max.
      apply hmrr_ex_hseq with ((vec s (-S A1) ++ vec r0 A2 ++ T) :: (vec s (-S A2) ++ vec r0 A2 ++ T) :: G) ; [ Permutation_Type_solve | ]. 
      apply hmrr_W.
      eapply hmrr_ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      Permutation_Type_solve.
  - apply hmrr_one; try nra; try assumption.
  - apply hmrr_ex_seq with (vec r0 HMR_coone ++ vec s HMR_one ++ T) ; [ Permutation_Type_solve | ].
    apply hmrr_one; try nra; try assumption.
  - assert ({ L & prod
                  ( G = map (fun x => snd x) L)
                  (( G =  map (fun x => vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L) *
                   (Forall_inf (fun x => sum_vec (snd (fst x)) = sum_vec (fst (fst x))) L))}) as [L [H1 [H2 H3]]].
    { clear - G ; induction G.
      - split with nil; repeat split; try reflexivity.
        apply Forall_inf_nil.
      - destruct IHG as [ L [ H1 [H2 H3]] ].
        split with (((nil , nil), a) :: L).
        repeat split; simpl; [rewrite H1 | rewrite H2 | ]; try reflexivity.
        apply Forall_inf_cons; try assumption.
        simpl; reflexivity. }
    rewrite H2.
    change ((vec s (<S> (-S A)) ++ vec r0 (<S> A) ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) L)
      with (map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) (<S> (-S A)) ++ vec (snd (fst x)) (<S> A) ++ snd x) (((s,r0), T) :: L)).
    apply hmrr_ID_diamond.
    + intros T0 r s0 H pi0.
      apply IHA; assumption.
    + apply Forall_inf_cons; assumption.
    + simpl; rewrite <- H1.
      apply pi.
Qed.

(** Proof of Lemma 4.13 *)
Lemma subs_proof P : forall G n t,
    HMR P G ->
    HMR P (subs_hseq G n t).
Proof with try assumption; try reflexivity.
  intros G n t pi.
  induction pi;unfold subs_hseq in *; fold subs_hseq in *; try rewrite ? subs_seq_vec in *; try rewrite subs_seq_app in *; unfold subs in *; fold subs in *; try now constructor.
  - replace (subs_seq (seq_mul r T) n t) with (seq_mul r (subs_seq T n t)) in IHpi by (clear; induction T; try destruct a; simpl; try rewrite IHT; try reflexivity).
    apply hmrr_T with r...
  - case (n =? n0).
    + apply hmrr_ID_gen...
    + apply hmrr_ID...
  - rewrite subs_seq_diamond.
    apply hmrr_diamond; try assumption.
  - eapply hmrr_ex_seq; [ apply subs_seq_ex ; apply p | ]...
  - eapply hmrr_ex_hseq; [ apply subs_hseq_ex; apply p | ]...
  - rewrite eq_subs_minus in IHpi.
    apply hmrr_can with (subs A n t) r s...
Qed.    

(** Proof of Lemma 4.14 *)
Lemma hmrr_plus_can_inv P : forall G T A B r, HMR P ((vec r (A +S B) ++ T) :: G) -> HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((vec r A ++ vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hmrr_can with (A +S B) r r; try reflexivity.
  apply hmrr_ex_seq with ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) ++ (vec r (A +S B) ++ T)); [ Permutation_Type_solve | ].
  apply hmrr_M; try reflexivity.
  2:{ apply HMR_le_frag with P; try assumption.
      apply le_hmr_frag_trans with (hmr_frag_add_M P) ; [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hmrr_ex_hseq with (G ++ ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) :: nil)); [ Permutation_Type_solve | ].
  apply hmrr_W_gen.
  unfold minus; fold (-S A); fold (-S B).
  apply hmrr_plus.
  apply hmrr_ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B); [ Permutation_Type_solve | ].
  apply hmrr_ID_gen; try reflexivity.
  replace (vec r (-S B) ++ vec r B) with (vec r (-S B) ++ vec r B ++ nil) by (now rewrite app_nil_r).
  apply hmrr_ID_gen; [ reflexivity | apply hmrr_INIT ].
Qed.

Lemma hmrr_Z_can_inv P : forall G T r, HMR P ((vec r HMR_zero ++ T) :: G) -> HMR (hmr_frag_add_CAN P) (T :: G).
Proof.
  intros G T r pi.
  apply hmrr_can with HMR_zero r r; try reflexivity.
  apply hmrr_Z.
  apply HMR_le_frag with P; try assumption.
  apply add_CAN_le_frag.
Qed.
  
Lemma hmrr_mul_can_inv P : forall G T A r0 r, HMR P ((vec r (r0 *S A) ++ T) :: G) -> HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  intros G T A r0 r pi.
  apply hmrr_can with (r0 *S A) r r; try reflexivity.
  apply hmrr_ex_seq with ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) ++ (vec r (r0 *S A) ++ T)); [ Permutation_Type_solve | ].
  apply hmrr_M; try reflexivity.
  2:{ apply HMR_le_frag with P; try assumption.
      apply le_hmr_frag_trans with (hmr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hmrr_ex_hseq with (G ++ ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) :: nil)); [ Permutation_Type_solve | ].
  apply hmrr_W_gen.
  unfold HMR_minus; fold HMR_minus.
  apply hmrr_mul.
  replace (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A) with (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A ++ nil) by (now rewrite app_nil_r).
  apply hmrr_ID_gen ; [ reflexivity | ].
  apply hmrr_INIT.
Qed.

Lemma hmrr_max_can_inv P : forall G T A B r, HMR P ((vec r (A \/S B) ++ T) :: G) -> HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hmrr_can with (A \/S B) r r; try reflexivity.
  apply hmrr_ex_seq with ( (vec r (-S (A \/S B)) ++ vec r B) ++ (vec r (A \/S B) ++ T)); [Permutation_Type_solve | ].
  apply hmrr_M; try reflexivity.
  2:{ eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply HMR_le_frag with P; try assumption.
      destruct P; repeat split; Bool.destr_bool. }
  apply hmrr_ex_hseq with ((vec r A ++ T) :: (vec r (-S (A \/S B)) ++ vec r B) :: G); [ apply Permutation_Type_swap | ].
  apply hmrr_can with (A \/S B) r r ; try reflexivity.
  apply hmrr_ex_seq with ( (vec r (-S (A \/S B)) ++ vec r A) ++ (vec r (A \/S B) ++ T)); [Permutation_Type_solve | ].
  apply hmrr_M; try reflexivity.
  2:{ eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply HMR_le_frag with P; try assumption.
      destruct P; repeat split; Bool.destr_bool.  }
  unfold minus; fold minus.
  apply hmrr_min.
  - apply hmrr_ex_hseq with (( (vec r (-S A /\S -S B) ++ vec r B) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ Permutation_Type_solve | ].
    apply hmrr_W_gen.
    replace (vec r (-S A) ++ vec r A) with (vec r (-S A) ++ vec r A ++ nil) by (now rewrite app_nil_r).
    apply hmrr_ID_gen; [reflexivity | apply hmrr_INIT].
  - eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_min.
    + apply hmrr_S.
      apply hmrr_ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; [ reflexivity | apply hmrr_ID_gen ; [ reflexivity | ] ].
      apply hmrr_ex_hseq with (G ++ (nil :: nil)); [ Permutation_Type_solve | ].
      apply hmrr_W_gen; apply hmrr_INIT.
    + rewrite <-(app_nil_r (vec r B)).
      apply hmrr_ID_gen; [ reflexivity | ].
      eapply hmrr_ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ (nil :: nil)); [ | apply hmrr_W_gen; apply hmrr_INIT ].
      Permutation_Type_solve.
Qed.

Lemma hmrr_min_can_inv_l P : forall G T A  B r, HMR P ((vec r (A /\S B) ++ T) :: G) -> HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hmrr_can with (A /\S B) r r; try reflexivity.
  apply hmrr_ex_seq with ((vec r (-S (A /\S B)) ++ vec r A) ++ (vec r (A /\S B) ++ T)); [ Permutation_Type_solve | ].
  apply hmrr_M; try reflexivity.
  2:{ apply HMR_le_frag with P; try assumption.
      apply le_hmr_frag_trans with (hmr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hmrr_max.
  apply hmrr_ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ Permutation_Type_solve | ].
  apply hmrr_W_gen.
  rewrite <-(app_nil_r (vec r A)).
  apply hmrr_ID_gen; [ reflexivity | apply hmrr_INIT].
Qed.

Lemma hmrr_min_can_inv_r P : forall G T A  B r, HMR P ((vec r (A /\S B) ++ T) :: G) -> HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hmrr_can with (A /\S B) r r; try reflexivity.
  apply hmrr_ex_seq with ((vec r (-S (A /\S B)) ++ vec r B) ++ (vec r (A /\S B) ++ T)); [ Permutation_Type_solve | ].
  apply hmrr_M; try reflexivity.
  2:{ apply HMR_le_frag with P; try assumption.
      apply le_hmr_frag_trans with (hmr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hmrr_max.
  apply hmrr_ex_hseq with (((vec r (-S A) ++ vec r B) :: G) ++ ((vec r (-S B) ++ vec r B) :: nil)); [ Permutation_Type_solve | ].
  apply hmrr_W_gen.
  rewrite <-(app_nil_r (vec r B)).
  apply hmrr_ID_gen; [ reflexivity | apply hmrr_INIT].
Qed.

(** Proof of Lemma 4.16 *)
Lemma hmrr_T_vec P : forall G T vr,
    vr <> nil ->
    HMR P (seq_mul_vec vr T :: G) ->
    HMR (hmr_frag_add_T P) (T :: G).
Proof.
  intros G T vr; revert G T; induction vr; intros G T Hnnil pi.
  - exfalso; auto.
  - simpl in *.
    destruct vr.
    + apply hmrr_T with a; try reflexivity.
      simpl in pi; rewrite app_nil_r in pi.
      apply HMR_le_frag with P; try assumption.
      apply add_T_le_frag.
    + apply hmrr_C.
      apply hmrr_T with a; try reflexivity.
      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      refine (IHvr (seq_mul a T :: G) T _ _) ; [ now auto | ].
      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hmrr_S.
      apply pi.
Defined.

Lemma modal_depth_proof_T_vec P :
  forall G T vr (Hnnil : vr <> nil) (pi : HMR P (seq_mul_vec vr T :: G)),
    modal_depth_proof (hmrr_T_vec P G T vr Hnnil pi) = modal_depth_proof pi.
Proof.
  intros G T vr; revert G T; induction vr; intros G T Hnnil pi.
  - exfalso; auto.
  - simpl in pi.
    destruct vr.
    + simpl; rewrite modal_depth_proof_le_frag.
      apply (modal_depth_proof_eq_rect _ _ (fun l => l :: G)).
    + change (modal_depth_proof pi) with (modal_depth_proof (hmrr_ex_hseq _ _ _ (Permutation_Type_swap _ _ _) (hmrr_S _ _ _ _ pi))).
      change sequent with (list (Rpos * term)) at 2 3.
      erewrite <- (IHvr (seq_mul a T :: G) T _ (hmrr_ex_hseq _ _ _ (Permutation_Type_swap _ _ _) (hmrr_S _ _ _ _ pi))).
      Unshelve.
      2:{ now auto. }
      reflexivity.
Qed.

(** Proof of Lemma 4.17 *)
Lemma hmrr_T_vec_inv P : forall G T vr,
    HMR P (T :: G) ->
    HMR (hmr_frag_add_T (hmr_frag_add_M P)) (seq_mul_vec vr T :: G).
Proof with try assumption.
  intros G T vr; revert G T; induction vr; intros G T pi.
  - apply hmrr_ex_hseq with (G ++ (nil :: nil)) ; [ Permutation_Type_solve | ].
    apply hmrr_W_gen.
    apply hmrr_INIT.
  - simpl.
    apply hmrr_M; try reflexivity.
    + apply hmrr_T with (inv_pos a); try reflexivity.
      rewrite seq_mul_twice.
      replace (time_pos (inv_pos a) a) with One by (apply Rpos_eq; destruct a; simpl;apply R_blt_lt in e;apply Rinv_l_sym; nra).
      rewrite seq_mul_One.
      apply HMR_le_frag with P; try assumption.
      apply le_hmr_frag_trans with (hmr_frag_add_M P); [ apply add_M_le_frag | apply add_T_le_frag ].
    + apply IHvr.
      apply pi.
Defined.

Lemma modal_depth_proof_T_vec_inv P :
  forall G T vr (pi : HMR P (T :: G)),
    (modal_depth_proof (hmrr_T_vec_inv P G T vr pi) <= modal_depth_proof pi)%nat.
Proof.
  intros G T vr; revert G T; induction vr; intros G T pi.
  - simpl.
    rewrite modal_depth_proof_W_gen.
    simpl.
    apply Peano.le_0_n.
  - simpl.
    apply Nat.max_lub.
    2:{ apply IHvr. }
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => l :: G)).
    rewrite (modal_depth_proof_eq_rect _ _ (fun r => seq_mul r T :: G)).
    rewrite (modal_depth_proof_eq_rect_r _ _ (fun l => l :: G)).
    rewrite modal_depth_proof_le_frag.
    reflexivity.
Qed.        

(** Proof of Corollary 4.18 *)
Lemma mix_A_B : forall G T A B vr vs,
    HMR_T_M (((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HMR_T_M (((vec vs B) ++ (vec vr B) ++ T) :: G) ->
    HMR_T_M (((vec vs B) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs piA piB.
  destruct vr as [| r vr]; [ | destruct vs as [ | s vs ]]; try assumption.
  apply hmrr_C.
  change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
  apply hmrr_T_vec with (r :: vr) ; [now auto | ].
  eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
  apply hmrr_T_vec with (s :: vs) ; [ now auto | ].
  apply hmrr_S.
  apply hmrr_ex_seq with ((seq_mul_vec (r :: vr) ((vec (s :: vs) A) ++ (vec (r :: vr) A) ++ T)) ++ (seq_mul_vec (s :: vs) ((vec (s :: vs) B) ++ (vec (r :: vr) B) ++ T))).
  2:{ apply hmrr_M; try reflexivity.
      - change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
        apply hmrr_T_vec_inv.
        apply piA.
      - change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
        apply hmrr_T_vec_inv.
        apply piB. }
  transitivity ((seq_mul_vec (r :: vr) (vec (s :: vs) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B ++ vec (r :: vr) B ++ T)).
  - apply Permutation_Type_app; try reflexivity.
    transitivity (seq_mul_vec (r :: vr) (vec (s :: vs) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A ++ T)).
    + apply seq_mul_vec_app_r.
    + apply Permutation_Type_app; try reflexivity.
      apply seq_mul_vec_app_r.
  - transitivity ((seq_mul_vec (r :: vr) (vec (s :: vs) A) ++
                               seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++
                                                                                                   ( seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B) ++ seq_mul_vec (s :: vs) T)).
    + apply Permutation_Type_app; try reflexivity.
      transitivity (seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B ++ T)).
      * apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        apply seq_mul_vec_app_r.
    + transitivity ((seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (s :: vs) T) ++ seq_mul_vec (r :: vr) (vec (s :: vs) B ++ vec (r :: vr) A ++ T)).
      * transitivity ((seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (s :: vs) T) ++ (seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ (seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T))).
        -- transitivity ((seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B) ++ seq_mul_vec (s :: vs) T).
           ++ do 2 (apply Permutation_Type_app; try reflexivity).
              apply seq_mul_vec_vec.
           ++ transitivity ((seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) T).
              ** do 3 (apply Permutation_Type_app; try reflexivity).
                 apply seq_mul_vec_vec.
              ** remember (seq_mul_vec (s :: vs) (vec (r :: vr) A)) as srA.
                 remember (seq_mul_vec (r :: vr) (vec (r :: vr) A)) as rrA.
                 remember (seq_mul_vec (s :: vs) (vec (s :: vs) B)) as ssB.
                 remember (seq_mul_vec (r :: vr) (vec (s :: vs) B)) as rsB.
                 Permutation_Type_solve.                 
        -- apply Permutation_Type_app; try reflexivity.
           transitivity (seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A ++ T)).
           ++ apply Permutation_Type_app; try reflexivity.
              symmetry; apply seq_mul_vec_app_r.
           ++ symmetry; apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        transitivity (seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A ++ T)).
        -- apply Permutation_Type_app; try reflexivity.
           symmetry; apply seq_mul_vec_app_r.
        -- symmetry; apply seq_mul_vec_app_r.
Qed.

(** Proof of Lemma 4.19 *)
Lemma C_A_B : forall G T A B vr vs,
    HMR_T_M (((vec vs B) ++ (vec vr A) ++ T) ::((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HMR_T_M (((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs pi.
  destruct vr as [ | r vr]; [ | destruct vs as [ | s vs]].
  - simpl in *.
    apply hmrr_C.
    apply pi.
  - simpl in *.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_C.
    eapply hmrr_ex_hseq ; [ | apply pi].
    apply Permutation_Type_skip.
    apply Permutation_Type_swap.
  - remember (s :: vs) as vs'; remember (r :: vr) as vr'.
    apply hmrr_C.
    change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
    apply hmrr_T_vec with vs' ; [ rewrite Heqvs'; now auto | ].
    apply hmrr_ex_hseq with ((vec vs' A ++ vec vr' A ++ T) :: (vec vs' B ++ vec vr' B ++ T) :: (seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)) :: G).
    { etransitivity ; [ | apply Permutation_Type_swap ].
      etransitivity; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply hmrr_C.
    change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
    apply hmrr_T_vec with vr'; [ rewrite Heqvr' ; now auto | ].
    eapply hmrr_ex_hseq.
    { apply Permutation_Type_skip.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply hmrr_S.
    apply hmrr_ex_seq with (seq_mul_vec (vr' ++ vs') (vec vs' B ++ vec vr' A ++ T)).
    2:{ change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M).
        apply hmrr_T_vec_inv.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply pi]. }
    rewrite seq_mul_vec_app_l.
    symmetry.
    transitivity ((seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)).
    + apply Permutation_Type_app; try reflexivity.
      transitivity (seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A ++ T)).
      * apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        apply seq_mul_vec_app_r.
    + transitivity ((seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ ( seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B) ++ seq_mul_vec vs' T)).
      * apply Permutation_Type_app; try reflexivity.
        transitivity (seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B ++ T)).
        -- apply seq_mul_vec_app_r.
        -- apply Permutation_Type_app; try reflexivity.
           apply seq_mul_vec_app_r.
      * transitivity ((seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B ++ vec vr' A ++ T)).
        -- transitivity ((seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ (seq_mul_vec vs' (vec vs' B) ++ (seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vs' T))).
           ++ transitivity ((seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B) ++ seq_mul_vec vs' T).
              ** do 2 (apply Permutation_Type_app; try reflexivity).
                 apply seq_mul_vec_vec.
              ** transitivity ((seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vs' T).
                 --- do 3 (apply Permutation_Type_app; try reflexivity).
                     apply seq_mul_vec_vec.
                 --- remember (seq_mul_vec vs' (vec vr' A)) as srA.
                     remember (seq_mul_vec vr' (vec vr' A)) as rrA.
                     remember (seq_mul_vec vs' (vec vs' B)) as ssB.
                     remember (seq_mul_vec vr' (vec vs' B)) as rsB.
                     Permutation_Type_solve.                 
           ++ apply Permutation_Type_app; try reflexivity.
              transitivity (seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' A ++ T)).
              ** apply Permutation_Type_app; try reflexivity.
                 symmetry; apply seq_mul_vec_app_r.
              ** symmetry; apply seq_mul_vec_app_r.
        -- apply Permutation_Type_app; try reflexivity.
           transitivity (seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A ++ T)).
           ++ apply Permutation_Type_app; try reflexivity.
              symmetry; apply seq_mul_vec_app_r.
           ++ symmetry; apply seq_mul_vec_app_r.
Qed.

(** Additionnal rules that required hmrr_ID_gen *)
Lemma hmrr_can_fuse P :
  forall G T A r1 r2,
    HMR P (((r1, A) :: (r2 , A) :: T) :: G) ->
    HMR (hmr_frag_add_M (hmr_frag_add_CAN P)) (((plus_pos r1 r2, A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can with A (r1 :: r2 :: nil) (r1 :: r2 :: nil); auto.
  apply hmrr_ex_seq with (((vec (r1 :: r2 :: nil) (-S A) ++ vec (plus_pos r1 r2 :: nil) A)) ++ (vec (r1 :: r2 :: nil) A ++ T)) ; [Permutation_Type_solve | ] .
  apply hmrr_M; auto.
  - apply hmrr_ex_hseq with (G ++ (vec (r1 :: r2 :: nil) (-S A) ++ vec (plus_pos r1 r2 :: nil) A) :: nil); [ Permutation_Type_solve | ].
    apply hmrr_W_gen.
    rewrite <- (app_nil_r (vec (r1 :: r2 :: nil) (-S A) ++ vec (plus_pos r1 r2 :: nil) A)); rewrite<- app_assoc;apply hmrr_ID_gen ; [ | apply hmrr_INIT].
    destruct r1; destruct r2; simpl; nra.
  - simpl.
    apply HMR_le_frag with P; try assumption.
    destruct P; repeat split; Bool.destr_bool.
Qed.

Lemma hmrr_can_unfuse P :
  forall G T A r1 r2,
    HMR P (((plus_pos r1 r2, A) :: T) :: G) ->
    HMR (hmr_frag_add_M (hmr_frag_add_CAN P)) (((r1, A) :: (r2 , A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can with A (plus_pos r1 r2 :: nil) (plus_pos r1 r2 :: nil); auto.
  apply hmrr_ex_seq with (((vec (plus_pos r1 r2 :: nil) (-S A) ++ vec (r1 :: r2 :: nil) A)) ++ (vec (plus_pos r1 r2 :: nil) A ++ T)) ; [Permutation_Type_solve | ] .
  apply hmrr_M; auto.
  - apply hmrr_ex_hseq with (G ++ (vec (plus_pos r1 r2 :: nil) (-S A) ++ vec (r1 :: r2 :: nil) A) :: nil); [ Permutation_Type_solve | ].
    apply hmrr_W_gen.
    rewrite <- (app_nil_r (vec (plus_pos r1 r2 :: nil) (-S A) ++ vec (r1 :: r2 :: nil) A)); rewrite<- app_assoc;apply hmrr_ID_gen ; [ | apply hmrr_INIT].
    destruct r1; destruct r2; simpl; nra.
  - simpl.
    apply HMR_le_frag with P; try assumption.
    destruct P; repeat split; Bool.destr_bool.
Qed.
