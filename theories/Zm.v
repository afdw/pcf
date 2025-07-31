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

Lemma Zm_eq_dec {μ} :
  ∀ n m : Zm μ, {n = m} + {n ≠ m}.
Proof.
  intros n m. destruct (Z.eq_dec (Zm_n n) (Zm_n m)) as [H_n_m | H_n_m].
  - left. apply irrelevant_Zm. auto.
  - right. intros <-. auto.
Qed.

Instance dec_eq_Zm {μ} : EqDec (Zm μ) eq := Zm_eq_dec.

Lemma Zm_in_bounds_impl_mod :
  ∀ μ n,
  Zm_in_bounds μ n →
  (n mod Z.of_nat μ)%Z = n.
Proof.
  intros μ n H. apply Zmod_small. auto.
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

Compute Zm_of_Z 7 : Zm 3.
