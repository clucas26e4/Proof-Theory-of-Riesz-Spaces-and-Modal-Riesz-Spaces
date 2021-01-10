Require Import PeanoNat.
Require Import Lia.
Require Import RL.Utilities.lt_nat_tuples.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_solve.

Lemma Exists_inf_split A : forall P (l : list A),
    Exists_inf P l ->
    {' (a, la, lb) : _ &
                     prod (P a)
                          (l = la ++ a :: lb)}.
Proof.
  intros P l Hex; induction Hex.
  - split with (x , nil, l); repeat split; try assumption; try reflexivity.
  - destruct IHHex as [[[a la] lb] [Hp Heq]].
    split with (a , x :: la, lb); repeat split; try assumption; rewrite Heq; reflexivity.
Qed.

Lemma Forall_inf_Permutation_Type A : forall P (l l' : list A),
    Permutation_Type l l' ->
    Forall_inf P l ->
    Forall_inf P l'.
Proof.
  intros P l l' Hperm.
  induction Hperm; intros Hall.
  - apply Forall_inf_nil.
  - inversion Hall; subst.
    apply Forall_inf_cons ; [ apply X | ].
    apply IHHperm; apply X0.
  - inversion Hall; inversion X0; subst.
    apply Forall_inf_cons;  [ | apply Forall_inf_cons]; assumption.
  - apply IHHperm2.
    apply IHHperm1.
    apply Hall.
Qed.

Lemma Exists_inf_Permutation_Type A : forall P (l l' : list A),
    Permutation_Type l l' ->
    Exists_inf P l ->
    Exists_inf P l'.
Proof.
  intros P l l' Hperm.
  induction Hperm; intros Hex.
  - inversion Hex.
  - inversion Hex; subst.
    + apply Exists_inf_cons_hd; assumption.
    + apply Exists_inf_cons_tl; apply IHHperm; apply X.
  - inversion Hex;  [ | inversion X]; subst.
    + apply Exists_inf_cons_tl; apply Exists_inf_cons_hd; apply X.
    + apply Exists_inf_cons_hd; apply X0.
    + apply Exists_inf_cons_tl; apply Exists_inf_cons_tl; apply X0.
  - apply IHHperm2; apply IHHperm1; apply Hex.
Qed.

Lemma decomp_Permutation_Type_2 A : forall l l' (x y : A),
    Permutation_Type (x :: y :: l) l' ->
    {' (l1,l2,l3) : _ & {l' = l1 ++ x :: l2 ++ y :: l3} +
                        {l' = l1 ++ y :: l2 ++ x :: l3}}.
Proof.
  intros l l' x y Hperm.
  destruct (in_inf_split x l') as [[la lb] Heq].
  { apply Permutation_Type_in_inf with (x :: y :: l); [ apply Hperm | ].
    left; reflexivity. }
  case (in_inf_app_or la lb y).
  { apply Permutation_Type_in_inf with (y :: l) ; [ | left; reflexivity].
    apply Permutation_Type_cons_inv with x.
    rewrite Heq in Hperm; Permutation_Type_solve. }
  - intros Hin.
    apply in_inf_split in Hin as [[l1 l2] Heq' ].
    split with (l1 , l2 , lb).
    right; subst.
    rewrite <- ? app_assoc; reflexivity.
  - intros Hin.
    apply in_inf_split in Hin as [[l1 l2] Heq' ].
    split with (la , l1 , l2).
    left; subst; reflexivity.
Qed.

Lemma In_inf_seq : forall i k n,
    (i < n)%nat ->
    In_inf (i + k)%nat (seq k n).
Proof.
  intros i k n; revert i k; induction n; intros i k Hlt; try (exfalso; now inversion Hlt).
  destruct i; simpl; [ left; auto | ].
  right.
  replace (S (i + k)) with (i + S k)%nat by lia.
  apply IHn ; lia.
Qed.

Lemma in_inf_rev_inv A : forall (l : list A) a,
    In_inf a (rev l) ->
    In_inf a l.
Proof.
  intros l a Hin.
  rewrite <- rev_involutive.
  apply in_inf_rev.
  apply Hin.
Qed.

Lemma In_inf_map_S : forall i l,
    In_inf i l ->
    In_inf (S i) (map S l).
Proof.
  intros i; induction l; intros Hin; inversion Hin; subst; simpl; auto.
Qed.

Lemma not_0_In_inf_map_S : forall l,
    In_inf 0%nat (map S l) ->
    False.
Proof.
  induction l; intros Hin; inversion Hin; subst; simpl; auto.
  inversion H.
Qed.

Lemma In_inf_map_S_inv : forall i l,
    In_inf (S i) (map S l) ->
    In_inf i l.
Proof.
  intros i; induction l; intros Hin; inversion Hin; subst; simpl; auto.
Qed.

Lemma Forall_inf_lt_map_S : forall L n,
    Forall_inf (fun x => x < n)%nat L ->
    Forall_inf (fun x => x < S n)%nat (map S L).
Proof.
  induction L; intros n Hall; [apply Forall_inf_nil | ].
  inversion Hall; subst.
  apply Forall_inf_cons; [ lia | apply IHL; apply X].
Qed.

Lemma not_In_inf_seq : forall k n i,
    (i < k)%nat ->
    In_inf i (seq k n) ->
    False.
Proof.
  intros k n; revert k; induction n; intros k i Hlt Hin; inversion Hin; subst.
  - lia.
  - apply IHn with (S k) i; try assumption.
    lia.
Qed.

Lemma In_inf_seq_lt : forall k n i,
    In_inf i (seq k n) ->
    (i < k + n)%nat.
Proof.
  intros k n; revert k; induction n;  intros k i Hin; inversion Hin.
  - subst; lia.
  - replace (k + S n)%nat with (S k + n)%nat by lia.
    apply IHn.
    apply X.
Qed.

Lemma In_inf_remove_not A : forall eq_dec (l : list A) a,
    In_inf a (remove eq_dec a l) ->
    False.
Proof.
  intros eq_dec; induction l; intros a' Hin; [ inversion Hin | ].
  case_eq (eq_dec a' a); intros H1 H2.
  - subst; rewrite remove_cons in Hin.
    apply IHl with a.
    apply Hin.
  - simpl in Hin.
    rewrite H2 in Hin.
    inversion Hin ; [ apply H1; auto | ].
    apply IHl with a'.
    apply X.
Qed.

Lemma In_inf_remove_In_inf A : forall eq_dec (l : list A) a1 a2,
    In_inf a1 (remove eq_dec a2 l) ->
    (a1 <> a2) * (In_inf a1 l).
Proof.
  intros eq_dec; induction l; intros a1 a2 Hin; [ inversion Hin | ].
  case_eq (eq_dec a2 a); intros H1 H2; simpl in Hin; rewrite H2 in Hin.
  - destruct (IHl a1 a2 Hin) as [Hneq Hin'].
    split; auto.
    right; apply Hin'.
  - inversion Hin; subst.
    + split; auto.
      left; auto.
    + destruct (IHl a1 a2 X) as [Hneq Hin'].
      split; auto.
      right; auto.
Qed.

Lemma In_inf_remove_In_inf_inv A : forall eq_dec (l : list A) a1 a2,
    (a1 <> a2) * (In_inf a1 l) ->
    In_inf a1 (remove eq_dec a2 l).
Proof.
  intros eq_dec; induction l; intros a1 a2 [Hneq Hin]; [ inversion Hin | ].
  inversion Hin.
  - subst.
    simpl.
    case (eq_dec a2 a1); intros H; try (subst; now exfalso).
    clear H.
    left; auto.
  - simpl.
    case (eq_dec a2 a); intros H ; [ | right ]; apply IHl; split; auto.    
Qed.

Lemma rev_reverse_order_gt : forall L,
    (forall i j : nat,
        (j < length L)%nat ->
        (i < j)%nat -> (nth i L 0 > nth j L 0)%nat) ->
    forall i j : nat,
      (i < length (rev L))%nat ->
      (i > j)%nat -> (nth i (rev L) 0 > nth j (rev L) 0)%nat.
Proof.
  intros L H i j Hlen Hgt.
  rewrite rev_length in Hlen.
  rewrite ? rev_nth; try lia.
  apply H; lia.
Qed.

Lemma rev_reverse_order_lt : forall L,
    (forall i j : nat,
        (j < length L)%nat ->
        (i < j)%nat -> (nth i L 0 < nth j L 0)%nat) ->
    forall i j : nat,
      (i < length (rev L))%nat ->
      (i > j)%nat -> (nth i (rev L) 0 < nth j (rev L) 0)%nat.
Proof.
  intros L H i j Hlen Hlt.
  rewrite rev_length in Hlen.
  rewrite ? rev_nth; try lia.
  apply H; lia.
Qed.

Lemma in_inf_map_cons A : forall (a : A) l L,
    In_inf l L ->
    In_inf (a :: l) (map (cons a) L).
Proof.
  intros a l; induction L; intros Hin ; [ inversion Hin | ].
  inversion Hin; subst.
  - simpl; left; reflexivity.
  - simpl; right; apply IHL.
    apply X.
Qed.

Lemma in_inf_map_cons_inv A : forall (a : A) l L,
    In_inf l (map (cons a) L) ->
    { l' & prod (l = a :: l') (In_inf l' L) }.
Proof.
  intros a l L; induction L; intros Hin; inversion Hin; subst.
  - split with a0.
    split; try reflexivity.
    left; reflexivity.
  - destruct (IHL X) as [l' [Heq Hin']].
    split with l'.
    repeat split; try assumption.
    right; apply Hin'.
Qed.

Lemma rev_not_nil A : forall (L : list A),
    L <> nil ->
    rev L <> nil.
Proof.
  destruct L; auto.
  simpl.
  intros _.
  intros H.
  assert (Permutation_Type (a :: rev L) nil); [ rewrite <- H; Permutation_Type_solve | ].
  symmetry in X; apply Permutation_Type_nil in X.
  inversion X.
Qed.

Lemma rev_nth_all_lt : forall l n,
    (forall i, nth i l 0 < n)%nat ->
    forall i, (nth i (rev l) 0 < n)%nat.
Proof.
  induction l; intros n H i.
  - destruct n; destruct i; auto.
  - simpl.
    case_eq (i <? (length (rev l)))%nat.
    + intros Hlt.
      rewrite app_nth1 ; [ | apply Nat.ltb_lt in Hlt; apply Hlt].
      apply IHl.
      intros i'.
      apply (H (S i')).
    + intros H'.
      rewrite app_nth2 ; [ | apply Nat.ltb_nlt in H'; lia].
      specialize (H 0%nat); simpl in H.
      remember (length (rev l)).
      clear - H H'.
      revert n0 H'.
      induction i; intros n0 H'.
      * simpl; apply H.
      *  destruct n0; [ destruct i; simpl; lia | ].
         change (S i - S n0)%nat with (i - n0)%nat.
         apply IHi.
         apply H'.
Qed.

Lemma Forall_inf_nth A : forall (P : A -> Type) (l : list A),
    Forall_inf P l ->
    forall (i : nat) (a : A), (i < length l)%nat -> P (nth i l a).
Proof.
  intros P; induction l; intros Hall i a' Hlen; [ exfalso; inversion Hlen | ].
  inversion Hall; subst.
  destruct i; [simpl; apply X | ].
  apply IHl; try assumption.
  simpl in Hlen; lia.
Qed.

Lemma nth_Forall_inf A : forall (P : A -> Type) (l : list A),
    (forall (i : nat) (a : A), (i < length l)%nat -> P (nth i l a)) ->
    Forall_inf P l.
Proof.
  intros P; induction l; intros H; [ apply Forall_inf_nil | ].
  apply Forall_inf_cons.
  - apply (H 0 a)%nat.
    simpl; lia.
  - apply IHl.
    intros i a' Hlen.
    apply (H (S i) a').
    simpl; lia.
Qed.

Lemma In_inf_concat {A} :
  forall L (x : A),
    In_inf x (concat L) ->
    {l & prod (In_inf l L) (In_inf x l)}.
Proof.
  induction L; intros x Hin; [ inversion Hin | ].
  simpl in Hin.
  apply in_inf_app_or in Hin.
  destruct Hin.
  - split with a; split; auto.
    left; reflexivity.
  - destruct (IHL x i) as [l [H1 H2]].
    split with l; split; auto.
    right; apply H1.
Qed.

Lemma In_inf_seq_le_start :
  forall i j k,
    In_inf i (seq j k) ->
    (j <= i)%nat.
Proof.
  intros i j k; revert j; induction k; intros j Hin; inversion Hin; subst; try (specialize (IHk (S j) X)); lia.
Qed.

Lemma rev_reverse_order : forall L,
    (forall i j : nat,
        (j < length L)%nat ->
        (i < j)%nat -> (nth j L 0 < nth i L 0)%nat) ->
    forall i j : nat,
      (j < length (rev L))%nat ->
      (i < j)%nat -> (nth i (rev L) 0 < nth j (rev L) 0)%nat.
Proof.
  intros L H i j Hlen Hgt.
  rewrite rev_length in Hlen.
  rewrite ? rev_nth; try lia.
  apply H; lia.
Qed.

Lemma all_neq_not_In_inf {A} : forall l (a : A),
    Forall_inf (fun x => x <> a) l ->
    In_inf a l -> False.
Proof.
  induction l; intros a0 Hall Hin; inversion Hin; inversion Hall; subst; try contradiction.
  apply IHl with a0; assumption.
Qed.

Lemma all_neq_0_map_S : forall l,
    Forall_inf (fun x => x <> 0%nat) l ->
    { l' & l = map S l' }.
Proof.
  induction l; intros Hall; inversion Hall; subst.
  - split with nil; auto.
  - destruct a ; [ contradiction | ].
    destruct IHl as [l' Heq]; auto.
    split with (a :: l'); subst; auto.
Qed.

Lemma NoDup_inf_rev {A} : forall (l : list A),
    NoDup_inf l ->
    NoDup_inf (rev l).
Proof.
  intros l.
  apply Permutation_Type_NoDup_inf.
  apply Permutation_Type_rev.
Qed.

Lemma NoDup_inf_nth {A} : forall l,
    (forall (a0 : A) i j, i < length l -> j < length l -> i <> j -> nth i l a0 <> nth j l a0) ->
    NoDup_inf l.
Proof.
  intros l; induction l; intros H; [ apply NoDup_inf_nil | ].
  apply NoDup_inf_cons.
  - intros Hin.
    apply (In_inf_nth _ _ a) in Hin as [n Hlen Heq].
    refine (H a 0 (S n) _ _ _ _); simpl; try lia.
    auto.
  - apply IHl.
    intros a0 i j Hlen1 Hlen2 Hneq.
    refine (H a0 (S i) (S j) _ _ _); simpl; lia.
Qed.
    
Lemma list_split_max : forall v,
    v <> nil ->
    {' (la, lb, k) : _ & prod (v = la ++ k :: lb)
                              ((Forall_inf (fun x => x <= k) la) *
                               (Forall_inf (fun x => x <= k) lb))}.
Proof.
  induction v ; [ contradiction | ].
  destruct v; intros _.
  - split with (nil, nil, a).
    repeat split; auto.
  - destruct IHv as [[[la lb] k] [Heq [H1 H2]]]; [ intros H; inversion H | ].
    case_eq (k <=? a); intros H.
    + split with (nil, n :: v, a).
      apply Nat.leb_le in H.
      repeat split; auto.
      rewrite Heq.
      apply Forall_inf_app; [ | apply Forall_inf_cons].
      * refine (Forall_inf_arrow _ _ H1).
        intros a0 H'; lia.
      * apply H.
      * refine (Forall_inf_arrow _ _ H2).
        intros a0 H'; lia.
    + split with (a :: la, lb, k).
      apply Nat.leb_nle in H.
      repeat split; try rewrite Heq; auto.
      apply Forall_inf_cons; auto.
      lia.
Qed.

Lemma Forall_inf_le_not_In_inf : forall l k,
    Forall_inf (fun x => x <= k) l ->
    (In_inf k l -> False) ->
    Forall_inf (fun x => x < k) l.
Proof.
  induction l; intros k Hall Hnin; inversion Hall; subst; auto.
  apply Forall_inf_cons.
  - assert (a <> k).
    { intros H; subst; apply Hnin; left; auto. }
    lia.
  - apply IHl; auto.
    intros Hin; apply Hnin; right; auto.
Qed.
    
Lemma NoDup_inf_lt_length : forall v n,
    Forall_inf (fun x => x < n) v ->
    NoDup_inf v ->
    length v <= n.
Proof.
  intros v; remember (length v).
  revert v Heqn.
  induction n; intros v Heqn k Hall Hndup; try lia.
  assert (v <> nil) as Hnnil.
  { destruct v; try now inversion Heqn; auto. }
  destruct (list_split_max v Hnnil) as [[[la lb] k'] [Heq [H1 H2]]].
  apply Permutation_Type_NoDup_inf with _ _ (k' :: la ++ lb) in Hndup; [ | rewrite Heq;Permutation_Type_solve ].
  inversion Hndup; subst.
  transitivity (S k').
  - apply le_n_S.
    refine (IHn (la ++ lb) _ k' _ _).
    + replace (length (la ++ lb)) with (pred (length (la ++ k' :: lb))) by (rewrite ? app_length; simpl; lia).
      rewrite <- Heqn; reflexivity.
    + apply Forall_inf_le_not_In_inf; [ apply Forall_inf_app | ]; auto.
    + apply X.
  - apply Forall_inf_elt in Hall.
    apply Hall.
Qed.
      
Lemma seq_NoDup_inf : forall i j,
    NoDup_inf (seq i j).
Proof.
  intros i j; revert i; induction j; intros i; simpl.
  - apply NoDup_inf_nil.
  - apply NoDup_inf_cons; auto.
    apply not_In_inf_seq; lia.
Qed.

Lemma remove_NoDup_inf {A} (Eq_dec : forall (a b : A), {a = b} + {a <> b}): forall (a : A) l,
    NoDup_inf l ->
    NoDup_inf (remove Eq_dec a l).
Proof.
  intros a; induction l; intros Hndup; inversion Hndup; subst; simpl; auto.
  case (Eq_dec a a0); intros H.
  - apply IHl; assumption.
  - apply NoDup_inf_cons; [ | apply IHl; assumption].
    intros H1.
    apply H0.
    apply (In_inf_remove_In_inf _ _ _ _ _ H1).
Qed.

(* return a list of all non empty subsets of [0..n] *)
Fixpoint make_subsets n :=
  match n with
  | 0%nat => nil
  | S n => (n :: nil) :: (map (cons n) (make_subsets n)) ++ make_subsets n
  end.

Lemma make_subsets_length : forall k,
    length (make_subsets k) = pred (2 ^ k).
Proof.
  induction k; simpl; try lia.
  rewrite app_length; rewrite map_length.
  rewrite IHk.
  assert (2 ^ k <> 0).
  { apply pow_not_0; lia. }
  lia.
Qed.  

Lemma cond_is_in_make_subsets : forall n l,
    l <> nil ->
    (forall i, nth i l 0 < n)%nat ->
    (forall i j, (j < length l)%nat -> (i < j)%nat -> (nth i l 0 > nth j l 0)%nat) ->
    In_inf l (make_subsets n).
Proof.
  induction n; intros l Hnnil Hle Hlt.
  - specialize (Hle 0%nat).
    exfalso; destruct l; inversion Hle.
  - destruct l; [exfalso; apply Hnnil; reflexivity | ].
    case_eq (n0 =? n); intros Heq.
    + apply Nat.eqb_eq in Heq; subst.
      destruct l.
      * left; reflexivity.
      * right.
        apply in_inf_or_app; left.
        apply in_inf_map_cons.
        apply IHn.
        -- intros H'; inversion H'.
        -- intros i.
           case_eq (i <? length (n0 :: l))%nat; intros H.
           ++ specialize (Hlt 0%nat (S i)).
              simpl in Hlt.
              change (match i with
                      | 0 => n0
                      | S m => nth m l 0
                      end)%nat with (nth i (n0 :: l) 0)%nat in Hlt.
              apply Nat.ltb_lt in H; simpl in H.
              lia.
           ++ apply Nat.ltb_nlt in H.
              rewrite nth_overflow ; destruct n; try lia.
              exfalso.
              specialize (Hlt 0 1)%nat.
              simpl in Hlt; lia.
        -- intros i j Hlen' Hlt'.
           assert (H' := Hlt (S i) (S j)).
           change (nth (S i) (S n :: n0 :: l) 0%nat) with (nth i (n0 :: l) 0%nat) in *.
           change (nth (S j) (S n :: n0 :: l) 0)%nat with (nth j (n0 :: l) 0%nat) in *.
           apply H'; simpl in *; lia.
    + right; apply in_inf_or_app; right.
      apply IHn.
      -- intros H'; inversion H'.
      -- intros i.
         destruct i; [ specialize (Hle 0%nat); apply Nat.eqb_neq in Heq; simpl in *; lia | ].
         case_eq (S i <? length (n0 :: l))%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H].
         ++ specialize (Hle i).
            specialize (Hlt i (S i)).
            lia.
         ++ rewrite nth_overflow; destruct n; try lia.
            destruct n0; inversion Heq.
            specialize (Hle 0)%nat.
            simpl in Hle; lia.
      -- intros i j Hlen' Hlt'.
         specialize (Hle j); specialize (Hlt i j).
         apply Hlt; lia.
Qed.

Lemma cond_is_in_make_subsets_inv : forall n l,
    In_inf l (make_subsets n) ->
    (l <> nil) * (forall i, nth i l 0 < n)%nat * (forall i j, (j < length l)%nat -> (i < j)%nat -> (nth i l 0 > nth j l 0)%nat).
Proof.
  induction n; intros l; [ intros Hin | intros [Heq | Hin]].
  - inversion Hin.
  - destruct l; [ | destruct l]; inversion Heq; subst.
    repeat split.
    + intros H; inversion H.
    + intros i; destruct i; [ | destruct i]; simpl; lia.
    + intros i j Hlen Hlt.
      destruct j ; [inversion Hlt | ].
      destruct j; try now inversion Hlen.
  - destruct (in_inf_app_or _ _ _ Hin).
    + destruct (in_inf_map_cons_inv _ _ _ _ i) as [l' [Heq Hin']]; subst.
      destruct (IHn l' Hin') as [[Hnnil Hlen] Hlt].
      clear i Hin.
      repeat split.
      * intros H; inversion H.
      * intros i.
        destruct i.
        -- simpl; lia.
        -- specialize (Hlen i).
           simpl.
           lia.
      * intros i j Hlen' Hlt'.
        destruct j; try now inversion Hlt'.
        change (nth (S j) (S n :: l') 0)%nat with (nth j l' 0)%nat.
        destruct i.
        -- simpl.
           specialize (Hlen j).
           lia.
        -- change (nth (S i) (S n :: l') 0)%nat with (nth i l' 0)%nat.
           apply Hlt; simpl in *; lia.
    + specialize (IHn l i).
      clear Hin i.
      destruct IHn as [[Hnil Hlen] Hlt].
      repeat split; auto.
      intro i; specialize (Hlen i); lia.
Qed.    
    
(* return the complementary list of v *)
Fixpoint complementary (v : list nat) n :=
  match v with
  | nil => seq 0%nat n
  | i :: v => remove (Nat.eq_dec) i (complementary v n)
  end.

Lemma In_inf_complementary : forall v n i,
    In_inf i v ->
    In_inf i (complementary v n) ->
    False.
Proof.
  induction v; intros n i Hin1 Hin2; [ inversion Hin1 | ].
  simpl in Hin2.
  case_eq (i =? a); intros H.
  - apply Nat.eqb_eq in H; subst.
    apply In_inf_remove_not in Hin2.
    apply Hin2.
  - inversion Hin1; [ apply Nat.eqb_neq in H; lia | ].
    apply IHv with n i; auto.
    apply In_inf_remove_In_inf in Hin2.
    apply Hin2.
Qed.

Lemma In_inf_complementary_inv : forall v n i,
    (i < n)%nat ->
    (In_inf i (complementary v n) -> False) ->
    In_inf i v.
Proof.
  induction v; intros n i Hlt H.
  - exfalso; apply H.
    replace i with (i + 0)%nat by lia.
    apply In_inf_seq.
    apply Hlt.
  - simpl in *.
    case_eq (a =? i); intros Heq.
    + left.
      apply Nat.eqb_eq in Heq; auto.
    + right.
      apply IHv with n; auto.
      intros Hin.
      apply H.
      apply In_inf_remove_In_inf_inv.
      apply Nat.eqb_neq in Heq; split; auto.    
Qed.

Lemma In_inf_complementary2 : forall v n i,
    In_inf i (complementary v n) ->
    In_inf i v ->
    False.
Proof.
  induction v; intros n i Hin1 Hin2; [ inversion Hin2 | ].
  simpl in Hin1.
  case_eq (i =? a); intros H.
  - apply Nat.eqb_eq in H; subst.
    apply In_inf_remove_not in Hin1.
    apply Hin1.
  - inversion Hin2; [ apply Nat.eqb_neq in H; lia | ].
    apply IHv with n i; auto.
    apply In_inf_remove_In_inf in Hin1.
    apply Hin1.
Qed.

Lemma In_inf_complementary2_inv : forall v n i,
    (i < n)%nat ->
    (In_inf i v -> False) ->
    In_inf i (complementary v n).
Proof.
  induction v; intros n i Hlt H.
  - replace i with (i + 0)%nat by lia.
    apply In_inf_seq.
    apply Hlt.
  - simpl in *.
    case_eq (a =? i); intros Heq.
    + exfalso; apply H; left; apply Nat.eqb_eq; apply Heq.
    + apply In_inf_remove_In_inf_inv.
      apply Nat.eqb_neq in Heq; split; auto.    
Qed.

Lemma complementary_partition : forall v n i,
    (i < n)%nat ->
    (In_inf i v) + (In_inf i (complementary v n)).
Proof.
  intros v n i Hlt.
  assert (Hin := in_inf_dec Nat.eq_dec i v).
  inversion Hin.
  - left; apply X.
  - right.
    apply In_inf_complementary2_inv; auto.
Qed.  
  
Lemma In_inf_complementary_lt : forall L n i,
    In_inf i (complementary L n) ->
    (i < n)%nat.
Proof.
  induction L; intros n i Hin.
  - simpl complementary in Hin.
    replace n with (0 + n)%nat by lia.
    apply In_inf_seq_lt.
    apply Hin.
  - simpl in Hin.
    apply In_inf_remove_In_inf in Hin as [Hneq Hin].
    apply IHL; auto.
Qed.
    
Lemma complementary_NoDup_inf : forall v n,
    NoDup_inf (complementary v n).
Proof.
  induction v; intros n; simpl.
  - apply seq_NoDup_inf.
  - apply remove_NoDup_inf.
    apply IHv.
Qed.

Lemma remove_length_not_In_inf {A} (Eq_dec : forall (a b : A), {a = b} + {a <> b}): forall (a : A) l,
    (In_inf a l -> False) ->
    length (remove Eq_dec a l) = length l.
Proof.
  intros a; induction l; intros Hnin; simpl; try reflexivity.
  case (Eq_dec a a0); intros H.
  - exfalso; subst.
    apply Hnin.
    left; reflexivity.
  - simpl; rewrite IHl; auto.
    intros Hin; apply Hnin; right; apply Hin.
Qed.

Lemma remove_length_In_inf_no_dup {A} (Eq_dec : forall (a b : A), {a = b} + {a <> b}): forall (a : A) l,
    In_inf a l ->
    NoDup_inf l ->
    length (remove Eq_dec a l) = pred (length l).
Proof.
  intros a l; induction l; intros Hin Hndup; try now inversion Hin.
  inversion Hin; subst.
  - rewrite remove_cons.
    simpl.
    inversion Hndup; subst.
    apply remove_length_not_In_inf.
    apply H0.
  - simpl.
    case (Eq_dec a a0); intros H.
    + apply remove_length_not_In_inf; inversion Hndup; subst; assumption.
    +  inversion Hndup; subst.
       simpl; rewrite IHl; try assumption.
       destruct l; simpl; try lia.
       inversion X.
Qed.    

Lemma complementary_length_lt_no_dup : forall v n,
    Forall_inf (fun x => x < n) v ->
    NoDup_inf v ->
    length (complementary v n) = n - (length v).
Proof.
  induction v; intros n Hall Hndup; simpl.
  - rewrite seq_length; lia.
  - inversion Hall; subst.
    inversion Hndup; subst.
    specialize (IHv n X X0).
    rewrite remove_length_In_inf_no_dup.
    + rewrite IHv.
      lia.
    + apply In_inf_complementary2_inv; assumption.
    + apply complementary_NoDup_inf.
Qed.
