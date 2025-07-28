From PCF Require Import Tools.
From PCF Require Import Zm.
From PCF Require Import Types.

Unset Positivity Checking.

Axiom FinFun : Type → Type → Type.

Inductive termₘ μ : list type → type → Type :=
  | Oₘ : ∀ Γ, termₘ μ Γ ι
  | predₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | succₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | matchₘ : ∀ Γ, termₘ μ Γ ι → FinFun (Zm μ) (termₘ μ Γ ι) → termₘ μ Γ ι
  | fixₘ : ∀ Γ α, termₘ μ Γ ((α ⇒ α) ⇒ α)
  | Varₘ : ∀ Γ α, mem_index α Γ → termₘ μ Γ α
  | Appₘ : ∀ Γ α β, termₘ μ Γ (α ⇒ β) → termₘ μ Γ α → termₘ μ Γ β
  | Absₘ : ∀ Γ α β, termₘ μ (β :: Γ) α → termₘ μ Γ (β ⇒ α).
Arguments Oₘ {μ Γ}.
Arguments predₘ {μ Γ}.
Arguments succₘ {μ Γ}.
Arguments matchₘ {μ Γ}.
Arguments fixₘ {μ Γ}.
Arguments Varₘ {μ Γ}.
Arguments Appₘ {μ Γ α β}.
Arguments Absₘ {μ Γ α}.

Notation "s  '$ₘ'  t" := (Appₘ s t) (at level 40, left associativity).
Notation "'λₘ:'  α ','  s" := (Absₘ α s) (at level 35, s at level 200).

Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (succₘ $ₘ Varₘ ι MIO) $ₘ Oₘ.
(* Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (λₘ: ι, Varₘ ι MIO). *)
