(** * Tactics used to apply all possible logical rules *)
Require Import Rpos.
Require Import RL.hr.term.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.

Require Import List.
Require Import Lra.

Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Ltac HR_to_app_step :=
  match goal with
  | |- HR _ (?T1 :: ?T2 :: ?G) => change (T1 :: T2 :: G) with ((T1 :: nil) ++ (T2 :: nil) ++ G)
  | |- HR _ (?G1 ++ ?T1 :: ?T2 :: ?G) => change (T1 :: T2 :: G) with ((T1 :: nil) ++ (T2 :: nil) ++ G)
  end.

Ltac HR_to_vec_step :=
  match goal with
  | |- HR _ (((?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  | |- HR _ ((_ ++ (?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  | |- HR _ (_ ++ ((?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  | |- HR _ (_ ++ (_ ++ (?a , ?A) :: ?T) :: _) => change ((a , A) :: T) with (vec (a :: nil) A ++ T)
  end.

Ltac HR_to_vec := repeat HR_to_vec_step.

Ltac apply_HR_plus :=
  match goal with
  | |- HR _ (?G1 ++ (?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with ((T1 ++ (vec a  (A +S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_plus
  | |- HR _ (?G1 ++ ((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with (((vec a  (A +S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_plus
  | |- HR _ ((?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hrr_plus
  | |- HR _ (((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) => apply hrr_plus
  | |- HR _ (?G1 ++ ((?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with ((T1 ++ (vec a  (A +S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_plus
  | |- HR _ (?G1 ++ (((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with (((vec a  (A +S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_plus
  | |- HR _ (((?T1 ++ (vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_seq with ((vec a (A +S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_plus
  | |- HR _ ((((vec ?a (?A +S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_plus
  end.

Ltac apply_HR_max :=
  match goal with
  | |- HR _ (?G1 ++ (?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with ((T1 ++ (vec a  (A \/S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_max
  | |- HR _ (?G1 ++ ((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with (((vec a  (A \/S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_max
  | |- HR _ ((?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hrr_max
  | |- HR _ (((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) => apply hrr_max
  | |- HR _ (?G1 ++ ((?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with ((T1 ++ (vec a  (A \/S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_max
  | |- HR _ (?G1 ++ (((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with (((vec a  (A \/S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_max
  | |- HR _ (((?T1 ++ (vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_seq with ((vec a (A \/S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_max
  | |- HR _ ((((vec ?a (?A \/S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_max
  end.

Ltac apply_HR_Z :=
  match goal with
  | |- HR _ (?G1 ++ (?T1 ++ (vec ?a (HR_zero)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with ((T1 ++ (vec a  (HR_zero)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (HR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_Z
  | |- HR _ (?G1 ++ ((vec ?a (HR_zero)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with (((vec a  (HR_zero)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_Z
  | |- HR _ ((?T1 ++ (vec ?a (HR_zero)) ++ ?T2) :: ?G2) => apply hrr_ex_seq with ((vec a (HR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hrr_Z
  | |- HR _ (((vec ?a (HR_zero)) ++ ?T2) :: ?G2) => apply hrr_Z
  | |- HR _ (?G1 ++ ((?T1 ++ (vec ?a (HR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with ((T1 ++ (vec a  (HR_zero)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (HR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_Z
  | |- HR _ (?G1 ++ (((vec ?a (HR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with (((vec a  (HR_zero)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_Z
  | |- HR _ (((?T1 ++ (vec ?a (HR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_seq with ((vec a (HR_zero)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_Z
  | |- HR _ ((((vec ?a (HR_zero)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_Z
  end.

Ltac apply_HR_mul :=
  match goal with
  | |- HR _ (?G1 ++ (?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with ((T1 ++ (vec a  (r *S A)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_mul
  | |- HR _ (?G1 ++ ((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with (((vec a  (r *S A)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_mul
  | |- HR _ ((?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hrr_mul
  | |- HR _ (((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) => apply hrr_mul
  | |- HR _ (?G1 ++ ((?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with ((T1 ++ (vec a  (r *S A)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_mul
  | |- HR _ (?G1 ++ (((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with (((vec a  (r *S A)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_mul
  | |- HR _ (((?T1 ++ (vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_seq with ((vec a (r *S A)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_mul
  | |- HR _ ((((vec ?a (?r *S ?A)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_mul
  end.

Ltac apply_HR_min :=
  match goal with
  | |- HR _ (?G1 ++ (?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with ((T1 ++ (vec a  (A /\S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_min
  | |- HR _ (?G1 ++ ((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_hseq with (((vec a  (A /\S B)) ++ T2) :: G1 ++ G2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_min
  | |- HR _ ((?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                            apply hrr_min
  | |- HR _ (((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) => apply hrr_min
  | |- HR _ (?G1 ++ ((?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with ((T1 ++ (vec a  (A /\S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_min
  | |- HR _ (?G1 ++ (((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_hseq with (((vec a  (A /\S B)) ++ T2) :: G1 ++ G2 ++ G3) ; [ Permutation_Type_solve | ];
                                                              apply hrr_min
  | |- HR _ (((?T1 ++ (vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_ex_seq with ((vec a (A /\S B)) ++ T1 ++ T2) ; [ Permutation_Type_solve | ];
                                                              apply hrr_min
  | |- HR _ ((((vec ?a (?A /\S ?B)) ++ ?T2) :: ?G2) ++ ?G3) => apply hrr_min
  end.


Ltac try_apply_rule_plus := repeat HR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HR_plus ||
                           (rewrite app_assoc ; apply_HR_plus) ||
                           (rewrite 2 app_assoc ; apply_HR_plus) ||
                           (rewrite 3 app_assoc ; apply_HR_plus) ||
                           (rewrite 4 app_assoc ; apply_HR_plus) ||
                           (rewrite 5 app_assoc ; apply_HR_plus) ||
                           (rewrite 6 app_assoc ; apply_HR_plus) ||
                           (rewrite 7 app_assoc ; apply_HR_plus) ).
Ltac try_apply_rule_mul := repeat HR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HR_mul ||
                           (rewrite app_assoc ; apply_HR_mul) ||
                           (rewrite 2 app_assoc ; apply_HR_mul) ||
                           (rewrite 3 app_assoc ; apply_HR_mul) ||
                           (rewrite 4 app_assoc ; apply_HR_mul) ||
                           (rewrite 5 app_assoc ; apply_HR_mul) ||
                           (rewrite 6 app_assoc ; apply_HR_mul) ||
                           (rewrite 7 app_assoc ; apply_HR_mul) ).
Ltac try_apply_rule_Z := repeat HR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HR_Z ||
                           (rewrite app_assoc ; apply_HR_Z) ||
                           (rewrite 2 app_assoc ; apply_HR_Z) ||
                           (rewrite 3 app_assoc ; apply_HR_Z) ||
                           (rewrite 4 app_assoc ; apply_HR_Z) ||
                           (rewrite 5 app_assoc ; apply_HR_Z) ||
                           (rewrite 6 app_assoc ; apply_HR_Z) ||
                           (rewrite 7 app_assoc ; apply_HR_Z) ).
Ltac try_apply_rule_min := repeat HR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HR_min ||
                           (rewrite app_assoc ; apply_HR_min) ||
                           (rewrite 2 app_assoc ; apply_HR_min) ||
                           (rewrite 3 app_assoc ; apply_HR_min) ||
                           (rewrite 4 app_assoc ; apply_HR_min) ||
                           (rewrite 5 app_assoc ; apply_HR_min) ||
                           (rewrite 6 app_assoc ; apply_HR_min) ||
                           (rewrite 7 app_assoc ; apply_HR_min) ).
Ltac try_apply_rule_max := repeat HR_to_app_step; 
                           rewrite <- ? app_assoc ;
                          (apply_HR_max ||
                           (rewrite app_assoc ; apply_HR_max) ||
                           (rewrite 2 app_assoc ; apply_HR_max) ||
                           (rewrite 3 app_assoc ; apply_HR_max) ||
                           (rewrite 4 app_assoc ; apply_HR_max) ||
                           (rewrite 5 app_assoc ; apply_HR_max) ||
                           (rewrite 6 app_assoc ; apply_HR_max) ||
                           (rewrite 7 app_assoc ; apply_HR_max) ).

Ltac progress_HR_proof := try_apply_rule_plus || try_apply_rule_Z || try_apply_rule_mul || try_apply_rule_min || try_apply_rule_max.

Ltac do_HR_logical := HR_to_vec; repeat progress_HR_proof.
