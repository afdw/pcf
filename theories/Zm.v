From PCF Require Import Tools.

Definition Zm_in_bounds (μ : nat) (n : Z) :=
  (0 ≤ n < Z.of_nat μ)%Z.

Definition Zm_canonical (μ : nat) (n : Z) :=
  ∀ m : Z, Zm_in_bounds μ (n + m * Z.of_nat μ)%Z → m = 0%Z.

Record Zm μ := {
  Zm_n : Z;
  Zm_canonical_n : Zm_canonical μ Zm_n;
}.
Arguments Zm_n {μ}.
Arguments Zm_canonical_n {μ}.

Declare Scope Zm_scope.
Delimit Scope Zm_scope with Zm.
Bind Scope Zm_scope with Zm.

Notation "'mod'  n" := {| Zm_n := n |} (at level 35, only printing) : Zm_scope.

Lemma irrelevant_Zm {μ} :
  ∀ n m : Zm μ,
  Zm_n n = Zm_n m →
  n = m.
Proof.
  intros n m H. destruct n as [n canonical_n], m as [m canonical_m].
  simpl in H. destruct H. f_equal. apply proof_irrelevance.
Qed.

Lemma Zm_in_bounds_mod :
  ∀ μ n,
  μ ≠ 0 →
  Zm_in_bounds μ (n mod Z.of_nat μ)%Z.
Proof.
  intros μ n H_μ. apply Z_mod_lt; lia.
Qed.

Lemma Zm_in_bounds_impl_mod :
  ∀ μ n,
  Zm_in_bounds μ n →
  (n mod Z.of_nat μ)%Z = n.
Proof.
  intros μ n H. apply Zmod_small. auto.
Qed.

Lemma Zm_in_bounds_Zm {μ} :
  μ ≠ 0 →
  ∀ n : Zm μ, Zm_in_bounds μ (Zm_n n).
Proof.
  intros H_μ. destruct n as [n canonical_n]. simpl. unfold Zm_canonical in canonical_n.
  specialize (canonical_n (- (n / Z.of_nat μ))%Z). rewrite Z.mul_opp_l, Z.add_opp_r, <- Zmod_eq_full in canonical_n by lia.
  specialize (canonical_n (Zm_in_bounds_mod _ _ H_μ)). rewrite Z.eq_opp_l, Z.opp_0 in canonical_n.
  apply Z.div_small_iff in canonical_n as [canonical_n | canonical_n].
  - auto.
  - lia.
  - lia.
Qed.

Lemma eq_Zm {μ} :
  ∀ n m : Zm μ, n = m ↔ (Zm_n n mod Z.of_nat μ)%Z = (Zm_n m mod Z.of_nat μ)%Z.
Proof.
  intros n m. split.
  - intros <-. auto.
  - intros H. apply irrelevant_Zm. destruct (classic (μ = 0)) as [-> | H_μ].
    + rewrite ! Zmod_0_r in H. auto.
    + rewrite ! (Zm_in_bounds_impl_mod _ _ (Zm_in_bounds_Zm H_μ _)) in H. auto.
Qed.

#[program]
Definition Zm_of_Z {μ} (n : Z) : Zm μ := {|
  Zm_n := (n mod Z.of_nat μ)%Z;
|}.
Next Obligation.
  intros μ n m H_m. remember (n mod Z.of_nat μ + m * Z.of_nat μ)%Z as k eqn:H_k.
  pose (H'_k := H_k). rewrite <- (Zm_in_bounds_impl_mod μ) in H'_k by (subst k; auto).
  rewrite Z_mod_plus_full in H'_k. rewrite Zmod_mod in H'_k. rewrite H'_k in H_k; clear H'_k.
  rewrite Z.add_comm in H_k. apply (Zplus_eq_compat _ _ (- (n mod Z.of_nat μ))%Z (- (n mod Z.of_nat μ))%Z) in H_k.
  - rewrite <- Z.add_assoc in H_k. rewrite Z.add_opp_diag_r in H_k. rewrite Z.add_0_r in H_k.
    symmetry in H_k. apply Zmult_integral in H_k. unfold Zm_in_bounds in H_m. destruct H_k as [H_k | H_k]; lia.
  - reflexivity.
Qed.

Lemma idempotent_Zm_of_Z {μ} :
  ∀ n, @Zm_of_Z μ (@Zm_n μ (Zm_of_Z n)) = Zm_of_Z n.
Proof.
  intros n. apply irrelevant_Zm. simpl. rewrite Zmod_mod. auto.
Qed.

Lemma eq_Zm_of_Z {μ} :
  ∀ n m, @Zm_of_Z μ n = @Zm_of_Z μ m ↔ (n mod Z.of_nat μ)%Z = (m mod Z.of_nat μ)%Z.
Proof.
  intros n m. split.
  - ltac1:(intros [=H]). auto.
  - intros H. apply irrelevant_Zm. auto.
Qed.

Compute Zm_of_Z 7 : Zm 3.

Instance arbitrary_Zm {μ} : Arbitrary (Zm μ) := Zm_of_Z 0%Z.

Instance dec_eq_Zm {μ} : EqDec (Zm μ) eq.
Proof.
  intros n m. destruct (Z.eq_dec (Zm_n n) (Zm_n m)) as [H_n_m | H_n_m].
  - left. apply irrelevant_Zm. auto.
  - right. intros <-. auto.
Defined.

Definition Zm_le {μ} (n m : Zm μ) := (Zm_n n ≤ Zm_n m)%Z.

Lemma refl_Zm_le {μ} :
  ∀ n : Zm μ, Zm_le n n.
Proof.
  intros n. unfold Zm_le. reflexivity.
Qed.

Lemma trans_Zm_le {μ} :
  ∀ n m k : Zm μ, Zm_le n m → Zm_le m k → Zm_le n k.
Proof.
  intros n m k H_1 H_2. unfold Zm_le in *. apply transitivity with (Zm_n m); auto.
Qed.

Instance preorder_Zm_le {μ} : PreOrder (@Zm_le μ) :=
  {| PreOrder_Reflexive := refl_Zm_le; PreOrder_Transitive := trans_Zm_le |}.

Instance partial_order_Zm_le {μ} : PartialOrder eq (@Zm_le μ).
Proof.
  intros n m. unfold relation_conjunction, predicate_intersection, flip; simpl. split.
  - intros <-. split; reflexivity.
  - intros (H_1 & H_2). apply irrelevant_Zm. unfold Zm_le in H_1, H_2. lia.
Qed.

Instance total_Zm_le {μ} : Total (@Zm_le μ).
Proof.
  intros n m. unfold Zm_le. apply totality.
Qed.

Instance dec_le_Zm {μ} : DecLe (@Zm_le μ).
Proof.
  intros n m. unfold le, Zm_le. apply dec_le_Z.
Defined.

#[program]
Definition infinite_Zm : infinite (Zm 0) :=
  λ l, exist _ (Zm_of_Z (` (infinite_Z (List.map Zm_n l)))) _.
Next Obligation.
  intros l. remember (List.map Zm_n l) as l' eqn:H_l'. destruct (infinite_Z l') as (n & H_n); simpl.
  subst l'. induction l as [| m l' IH].
  - auto.
  - intros [-> | H_l'].
    + apply H_n. left. simpl. apply Zmod_0_r.
    + apply IH.
      * intros H. apply H_n. right. auto.
      * auto.
Qed.

Fixpoint Zm_all_aux {μ} n : list (Zm μ) :=
  match n with
  | 0 => []
  | S n' => Zm_of_Z (Z.of_nat n') :: Zm_all_aux n'
  end.

Definition Zm_all {μ} : list (Zm μ) := Zm_all_aux μ.

Lemma list_In_Zm_all {μ} :
  μ ≠ 0 →
  ∀ n : Zm μ, List.In n Zm_all.
Proof.
  intros H_μ n. unfold Zm_all. specialize (Zm_in_bounds_Zm H_μ n) as H_n. assert (H_m : μ ≤ μ) by lia. induction μ as [| m IH] in H_n at 1, H_m at 1 |- * at 3.
  - unfold Zm_in_bounds in H_n. lia.
  - simpl. destruct (classic (Zm_of_Z (Z.of_nat m) = n)) as [<- | H].
    + left. auto.
    + right. unfold Zm_in_bounds in H_n, IH. apply IH.
      * rewrite eq_Zm in H. simpl in H. rewrite Zmod_mod, Zmod_small in H by lia.
        rewrite (Zm_in_bounds_impl_mod _ _ (Zm_in_bounds_Zm H_μ _)) in H. lia.
      * lia.
Qed.

#[program]
Definition finite_Zm {μ} (H_μ : μ ≠ 0) : finite (Zm μ) :=
  exist _ Zm_all _.
Next Obligation.
  intros μ H_μ. simpl. apply list_In_Zm_all; auto.
Qed.

Instance dec_finite_Zm {μ} : DecFinite (Zm μ) :=
  match μ == 0 with
  | left H_μ => inr (rew <- [λ μ, infinite (Zm μ)] H_μ in infinite_Zm)
  | right H_μ => inl (finite_Zm H_μ)
  end.

Goal ∃ H, (1 ↦₀ Zm_of_Z 2, _ ↦₀ (Zm_of_Z 3 : Zm 5)) == (1 ↦₀ Zm_of_Z 2, _ ↦₀ Zm_of_Z 3) = left H.
Proof.
  eexists. reflexivity.
Qed.

Goal ∃ H, (1 ↦₀ Zm_of_Z 2, _ ↦₀ (Zm_of_Z 3 : Zm 0)) == (1 ↦₀ Zm_of_Z 2, _ ↦₀ Zm_of_Z 3) = left H.
Proof.
  eexists. reflexivity.
Qed.

Definition Zm_pred {μ} (n : Zm μ) : Zm μ := Zm_of_Z (Z.pred (Zm_n n)).

Definition Zm_succ {μ} (n : Zm μ) : Zm μ := Zm_of_Z (Z.succ (Zm_n n)).
