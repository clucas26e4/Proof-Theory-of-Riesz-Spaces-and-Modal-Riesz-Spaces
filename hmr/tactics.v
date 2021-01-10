Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.

Require Import List.
Require Import Lra.

Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Ltac HMR_to_app_step :=
  match goal with
  | |- HMR _ (?T1 :: ?T2 :: ?G) => change (T1 :: T2 :: G) with ((T1 :: nil) ++ (T2 :: nil) ++ G)
  | |- HMR _ (?G1 ++ ?T1 :: ?T2 :: ?G) => change (T1 :: T2 :: G) with ((T1 :: nil) ++ (T2 :: nil) ++ G)
  end.

Ltac HMR_to_vec_step :=
  match goal with
  | |- HMR _ (((?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  | |- HMR _ ((_ ++ (?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  | |- HMR _ (_ ++ ((?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  | |- HMR _ (_ ++ (_ ++ (?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  end.

Ltac HMR_to_vec := repeat HMR_to_vec_step.

Ltac apply_HMR_plus :=
  match goal with
  | |- HMR _ (?G1 ++ (?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (A +S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_plus
  | |- HMR _ (?G1 ++ ((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with (((vec a  (A +S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_plus
  | |- HMR _ ((?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hmrr_plus
  | |- HMR _ (((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hmrr_plus
  | |- HMR _ (?G1 ++ ((?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (A +S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_plus
  | |- HMR _ (?G1 ++ (((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with (((vec a  (A +S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_plus
  | |- HMR _ (((?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_plus
  | |- HMR _ ((((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_plus
  end.

Ltac apply_HMR_max :=
  match goal with
  | |- HMR _ (?G1 ++ (?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (A \/S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_max
  | |- HMR _ (?G1 ++ ((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with (((vec a  (A \/S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_max
  | |- HMR _ ((?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hmrr_max
  | |- HMR _ (((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hmrr_max
  | |- HMR _ (?G1 ++ ((?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (A \/S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_max
  | |- HMR _ (?G1 ++ (((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with (((vec a  (A \/S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_max
  | |- HMR _ (((?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_max
  | |- HMR _ ((((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_max
  end.

Ltac apply_HMR_Z :=
  match goal with
  | |- HMR _ (?G1 ++ (?T1 ++ (vec ?a (HMR_zero)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (HMR_zero)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (HMR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_Z
  | |- HMR _ (?G1 ++ ((vec ?a (HMR_zero)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with (((vec a  (HMR_zero)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_Z
  | |- HMR _ ((?T1 ++ (vec ?a (HMR_zero)) ++ ?T2) :: ?G2) => apply hmrr_ex_seq with ((vec a (HMR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hmrr_Z
  | |- HMR _ (((vec ?a (HMR_zero)) ++ ?T2) :: ?G2) => apply hmrr_Z
  | |- HMR _ (?G1 ++ ((?T1 ++ (vec ?a (HMR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (HMR_zero)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (HMR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_Z
  | |- HMR _ (?G1 ++ (((vec ?a (HMR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with (((vec a  (HMR_zero)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_Z
  | |- HMR _ (((?T1 ++ (vec ?a (HMR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_seq with ((vec a (HMR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_Z
  | |- HMR _ ((((vec ?a (HMR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_Z
  end.

Ltac apply_HMR_mul :=
  match goal with
  | |- HMR _ (?G1 ++ (?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (r *S A)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_mul
  | |- HMR _ (?G1 ++ ((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with (((vec a  (r *S A)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_mul
  | |- HMR _ ((?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hmrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hmrr_mul
  | |- HMR _ (((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hmrr_mul
  | |- HMR _ (?G1 ++ ((?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (r *S A)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_mul
  | |- HMR _ (?G1 ++ (((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with (((vec a  (r *S A)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_mul
  | |- HMR _ (((?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_mul
  | |- HMR _ ((((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_mul
  end.

Ltac apply_HMR_min :=
  match goal with
  | |- HMR _ (?G1 ++ (?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (A /\S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_min
  | |- HMR _ (?G1 ++ ((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_hseq with (((vec a  (A /\S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_min
  | |- HMR _ ((?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hmrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hmrr_min
  | |- HMR _ (((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hmrr_min
  | |- HMR _ (?G1 ++ ((?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with ((T1 ++ (vec a  (A /\S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_min
  | |- HMR _ (?G1 ++ (((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_hseq with (((vec a  (A /\S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_min
  | |- HMR _ (((?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hmrr_min
  | |- HMR _ ((((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hmrr_min
  end.


Ltac try_apply_rule_plus := repeat HMR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HMR_plus ||
                           (rewrite app_assoc ; apply_HMR_plus) ||
                           (rewrite 2 app_assoc ; apply_HMR_plus) ||
                           (rewrite 3 app_assoc ; apply_HMR_plus) ||
                           (rewrite 4 app_assoc ; apply_HMR_plus) ||
                           (rewrite 5 app_assoc ; apply_HMR_plus) ||
                           (rewrite 6 app_assoc ; apply_HMR_plus) ||
                           (rewrite 7 app_assoc ; apply_HMR_plus) ).
Ltac try_apply_rule_mul := repeat HMR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HMR_mul ||
                           (rewrite app_assoc ; apply_HMR_mul) ||
                           (rewrite 2 app_assoc ; apply_HMR_mul) ||
                           (rewrite 3 app_assoc ; apply_HMR_mul) ||
                           (rewrite 4 app_assoc ; apply_HMR_mul) ||
                           (rewrite 5 app_assoc ; apply_HMR_mul) ||
                           (rewrite 6 app_assoc ; apply_HMR_mul) ||
                           (rewrite 7 app_assoc ; apply_HMR_mul) ).
Ltac try_apply_rule_Z := repeat HMR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HMR_Z ||
                           (rewrite app_assoc ; apply_HMR_Z) ||
                           (rewrite 2 app_assoc ; apply_HMR_Z) ||
                           (rewrite 3 app_assoc ; apply_HMR_Z) ||
                           (rewrite 4 app_assoc ; apply_HMR_Z) ||
                           (rewrite 5 app_assoc ; apply_HMR_Z) ||
                           (rewrite 6 app_assoc ; apply_HMR_Z) ||
                           (rewrite 7 app_assoc ; apply_HMR_Z) ).
Ltac try_apply_rule_min := repeat HMR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HMR_min ||
                           (rewrite app_assoc ; apply_HMR_min) ||
                           (rewrite 2 app_assoc ; apply_HMR_min) ||
                           (rewrite 3 app_assoc ; apply_HMR_min) ||
                           (rewrite 4 app_assoc ; apply_HMR_min) ||
                           (rewrite 5 app_assoc ; apply_HMR_min) ||
                           (rewrite 6 app_assoc ; apply_HMR_min) ||
                           (rewrite 7 app_assoc ; apply_HMR_min) ).
Ltac try_apply_rule_max := repeat HMR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HMR_max ||
                           (rewrite app_assoc ; apply_HMR_max) ||
                           (rewrite 2 app_assoc ; apply_HMR_max) ||
                           (rewrite 3 app_assoc ; apply_HMR_max) ||
                           (rewrite 4 app_assoc ; apply_HMR_max) ||
                           (rewrite 5 app_assoc ; apply_HMR_max) ||
                           (rewrite 6 app_assoc ; apply_HMR_max) ||
                           (rewrite 7 app_assoc ; apply_HMR_max) ).

Ltac progress_HMR_proof := try_apply_rule_plus || try_apply_rule_Z || try_apply_rule_mul || try_apply_rule_min || try_apply_rule_max.

Ltac do_HMR_logical := HMR_to_vec; repeat progress_HMR_proof.
