From PCF Require Import Tools.

Definition Zm_in_bounds (μ : nat) (n : Z) :=
  (0 ≤ n < Z.of_nat μ)%Z.

Definition Zm_canonical (μ : nat) (n : Z) :=
  ∀ m : Z, Zm_in_bounds μ (n + Z.of_nat μ * m)%Z → m = 0%Z.

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

Lemma injective_Zm_n {μ} :
  ∀ n m : Zm μ, Zm_n n = Zm_n m → n = m.
Proof.
  intros n m H. destruct n as [n canonical_n], m as [m canonical_m].
  simpl in H. destruct H. f_equal. apply proof_irrelevance.
Qed.

Lemma Zm_eq_dec {μ} :
  ∀ n m : Zm μ, {n = m} + {n ≠ m}.
Proof.
  intros n m. destruct (Z.eq_dec (Zm_n n) (Zm_n m)) as [H_n_m | H_n_m].
  - left. apply injective_Zm_n. auto.
  - right. intros <-. auto.
Qed.

Instance dec_eq_Zm {μ} : EqDec (Zm μ) eq := Zm_eq_dec.

#[program]
Definition Zm_of_Z {μ} (n : Z) : Zm μ := {|
  Zm_n := (n mod Z.of_nat μ)%Z;
|}.
Next Obligation.
  intros μ n. Locate "_ mod _". Search Z.modulo.
Admitted.

Lemma idempotent_Zm_of_Z {μ} :
  ∀ n, @Zm_of_Z μ (@Zm_n μ (Zm_of_Z n)) = Zm_of_Z n.
Proof.
Admitted.

Compute Zm_of_Z 7 : Zm 3.
