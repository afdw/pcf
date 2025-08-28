From PCF Require Import Tools.

Inductive type : Type :=
  | Base : type
  | Func : type → type → type.

Declare Scope types_scope.
Delimit Scope types_scope with types.
Bind Scope types_scope with type.
Open Scope types_scope.

Notation "'ι'" := Base : type_scope.
Notation "α  '⇒'  β" := (Func α β) (at level 60, right associativity) : type_scope.

Equations Derive NoConfusionHom for type.

Instance dec_eq_type : EqDec type eq.
Proof.
  rewrite dec_eq_def.
  intros α_1; induction α_1 as [| α'_1 IH_α' β'_1 IH_β']; intros α_2; destruct α_2 as [| α'_2 β'_2]; try (right; congruence).
  - left; reflexivity.
  - specialize (IH_α' α'_2); specialize (IH_β' β'_2).
    destruct IH_α' as [<- | IH_α'] > [destruct IH_β' as [<- | IH_β'] |]; constructor; congruence.
Defined.

Fixpoint construct_type (αs : list type) : type :=
  match αs with
  | [] => ι
  | α :: αs' => α ⇒ construct_type αs'
  end.

Fixpoint destruct_type (α : type) : list type :=
  match α with
  | ι => []
  | α' ⇒ β' => α' :: destruct_type β'
  end.

Lemma construct_type_destruct_type :
  ∀ α,
  construct_type (destruct_type α) = α.
Proof.
  intros α. induction α as [| α' IH_α' β' IH_β'].
  - auto.
  - simpl. rewrite IH_β'. auto.
Qed.

Lemma destruct_type_construct_type :
  ∀ αs,
  destruct_type (construct_type αs) = αs.
Proof.
  intros αs. induction αs as [| α αs' IH].
  - auto.
  - simpl. rewrite IH. auto.
Qed.

Definition renaming Γ Δ := ∀ (α : type), mem_index α Δ → mem_index α Γ.

Definition renaming_id Γ : renaming Γ Γ :=
  λ _ mi, mi.

Equations renaming_cons {Γ Δ} α (mi : mem_index α Γ) (σ : renaming Γ Δ) : renaming Γ (α :: Δ) :=
  | α, mi, σ, _, MIO => mi
  | α, mi, σ, _, MIS mi_1' => σ _ mi_1'.

Definition renaming_shift α Γ : renaming (α :: Γ) Γ :=
  λ _ mi, MIS mi.

Definition renaming_comp {Γ Δ Θ} (τ : renaming Δ Θ) (σ : renaming Γ Δ) : renaming Γ Θ :=
  λ _ mi, σ _ (τ _ mi).

Definition renaming_up {Γ Δ} α (σ : renaming Γ Δ) : renaming (α :: Γ) (α :: Δ) :=
  renaming_cons α MIO (renaming_comp σ (renaming_shift α Γ)).
