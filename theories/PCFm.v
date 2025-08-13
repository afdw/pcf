From PCF Require Import Tools.
From PCF Require Import Zm.
From PCF Require Import Types.

Unset Elimination Schemes.

Inductive termₘ μ : list type → type → Type :=
  | Oₘ : ∀ Γ, termₘ μ Γ ι
  | Pₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | Sₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | switchₘ : ∀ Γ, termₘ μ Γ ι → (Zm μ →₀ termₘ μ Γ ι) → termₘ μ Γ ι
  | fixₘ : ∀ Γ α, termₘ μ Γ ((α ⇒ α) ⇒ α)
  | Varₘ : ∀ Γ α, mem_index α Γ → termₘ μ Γ α
  | Appₘ : ∀ Γ α β, termₘ μ Γ (α ⇒ β) → termₘ μ Γ α → termₘ μ Γ β
  | Absₘ : ∀ Γ α β, termₘ μ (β :: Γ) α → termₘ μ Γ (β ⇒ α).
Arguments Oₘ {μ Γ}.
Arguments Pₘ {μ Γ}.
Arguments Sₘ {μ Γ}.
Arguments switchₘ {μ Γ}.
Arguments fixₘ {μ Γ}.
Arguments Varₘ {μ Γ}.
Arguments Appₘ {μ Γ α β}.
Arguments Absₘ {μ Γ α}.

Set Elimination Schemes.

Notation "s  '$ₘ'  t" := (Appₘ s t) (at level 40, left associativity).
Notation "'λₘ:'  α ','  s" := (Absₘ α s) (at level 35, s at level 200).

Definition termₘ_rect (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Type)
  (case_Oₘ : ∀ Γ, P Γ ι Oₘ)
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (s' : termₘ μ Γ ι), P Γ ι s' → ∀ f : Zm μ →₀ termₘ μ Γ ι, (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some t' => P Γ ι t' | None => True end → P Γ ι (switchₘ s' f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (s' : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) s' → ∀ t' : termₘ μ Γ α, P Γ α t' → P Γ β (s' $ₘ t'))
  (case_Absₘ : ∀ Γ α β (s' : termₘ μ (β :: Γ) α), P (β :: Γ) α s' → P Γ (β ⇒ α) (λₘ: β, s')) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @Oₘ _ Γ => case_Oₘ Γ
    | @Pₘ _ Γ => case_Pₘ Γ
    | @Sₘ _ Γ => case_Sₘ Γ
    | @switchₘ _ Γ s' f => case_switchₘ Γ s' (F Γ ι s') f (λ n, F Γ ι (f n)) (match stabilizing_fun_default f as t' return match t' with Some t' => P Γ ι t' | None => True end with Some t' => F Γ ι t' | None => I end)
    | @fixₘ _ Γ α => case_fixₘ Γ α
    | @Varₘ _ Γ α m => case_Varₘ Γ α m
    | @Appₘ _ Γ α β s' t' => case_Appₘ Γ α β s' (F Γ (α ⇒ β) s') t' (F Γ α t')
    | @Absₘ _ Γ α β s' => case_Absₘ Γ α β s' (F (β :: Γ) α s')
    end.

Definition termₘ_ind (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Prop)
  (case_Oₘ : ∀ Γ, P Γ ι Oₘ)
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (s' : termₘ μ Γ ι), P Γ ι s' → ∀ f : Zm μ →₀ termₘ μ Γ ι, (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some t' => P Γ ι t' | None => True end → P Γ ι (switchₘ s' f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (s' : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) s' → ∀ t' : termₘ μ Γ α, P Γ α t' → P Γ β (s' $ₘ t'))
  (case_Absₘ : ∀ Γ α β (s' : termₘ μ (β :: Γ) α), P (β :: Γ) α s' → P Γ (β ⇒ α) (λₘ: β, s')) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @Oₘ _ Γ => case_Oₘ Γ
    | @Pₘ _ Γ => case_Pₘ Γ
    | @Sₘ _ Γ => case_Sₘ Γ
    | @switchₘ _ Γ s' f => case_switchₘ Γ s' (F Γ ι s') f (λ n, F Γ ι (f n)) (match stabilizing_fun_default f as t' return match t' with Some t' => P Γ ι t' | None => True end with Some t' => F Γ ι t' | None => I end)
    | @fixₘ _ Γ α => case_fixₘ Γ α
    | @Varₘ _ Γ α m => case_Varₘ Γ α m
    | @Appₘ _ Γ α β s' t' => case_Appₘ Γ α β s' (F Γ (α ⇒ β) s') t' (F Γ α t')
    | @Absₘ _ Γ α β s' => case_Absₘ Γ α β s' (F (β :: Γ) α s')
    end.

Definition termₘ_rec (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Set) := termₘ_rect μ P.

Equations Derive NoConfusion for termₘ.

Instance dec_eq_termₘ {μ Γ α} : EqDec (termₘ μ Γ α) eq.
Proof.
  rewrite dec_eq_def.
  intros s_1; induction s_1 as [Γ_1 | Γ_1 | Γ_1 | Γ_1 s'_1 IH_s' f_1 IH_f IH_f_default | Γ_1 α_1 | Γ_1 α_1 mi_1 | Γ_1 α_1 β_1 s'_1 IH_s' t'_1 IH_t' | Γ_1 α_1 β_1 s'_1 IH_s']; intros s_2; ltac1:(dependent elimination s_2 as [@Oₘ Γ_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 s'_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
  - left; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
  - specialize (IH_s' s'_2). ltac1:(pose proof (IH'_f := λ n, IH_f n (f_2 n))); clear IH_f.
    assert (H_f_default : {stabilizing_fun_default f_1 = stabilizing_fun_default f_2} + {stabilizing_fun_default f_1 ≠ stabilizing_fun_default f_2}). {
      remember (stabilizing_fun_default f_1) as f_default_1 eqn:H_f_default_1; remember (stabilizing_fun_default f_2) as f_default_2 eqn:H_f_default_2. destruct f_default_1 as [t'_1 |], f_default_2 as [t'_2 |]; try (right; congruence).
      - specialize (IH_f_default t'_2). destruct IH_f_default; constructor; congruence.
      - left; reflexivity.
    }
    ltac1:(pose proof (H_f := dec_eq_stabilizing_fun_minimal f_1 f_2 IH'_f H_f_default)).
    destruct IH_s' as [<- | IH_s'] > [destruct H_f as [<- | H_f] |]; constructor; congruence.
  - left; reflexivity.
  - destruct (mi_1 == mi_2 : {_ = _} + {_ ≠ _}) as [-> | H_mi]; constructor; congruence.
  - destruct (α_1 == α_2) as [-> | H_α]; try (right; congruence). specialize (IH_s' s'_2). specialize (IH_t' t'_2).
    destruct IH_s' as [<- | IH_s'] > [destruct IH_t' as [<- | IH_t'] |].
    + left; reflexivity.
    + right. intros H. apply IH_t'. injection H as H. do 2 (apply inj_right_pair in H). auto.
    + right. intros H. apply IH_s'. injection H as H _. do 3 (apply inj_right_pair in H). auto.
  - specialize (IH_s' s'_2). destruct IH_s' as [<- | IH_s']; constructor; congruence.
Defined.

Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ Oₘ.
(* Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (λₘ: ι, Varₘ ι MIO). *)

Check λₘ: ι, switchₘ (Varₘ ι MIO) (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ Oₘ), Zm_of_Z 1 ↦₀ Oₘ, _ ↦₀ Sₘ $ₘ Oₘ).
