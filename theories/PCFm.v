From PCF Require Import Tools.
From PCF Require Import Zm.
From PCF Require Import Types.

Unset Elimination Schemes.

Inductive termₘ μ : list type → type → Type :=
  | kₘ : ∀ Γ, Zm μ → termₘ μ Γ ι
  | Pₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | Sₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | switchₘ : ∀ Γ, termₘ μ Γ ι → (Zm μ →₀ termₘ μ Γ ι) → termₘ μ Γ ι
  | fixₘ : ∀ Γ α, termₘ μ Γ ((α ⇒ α) ⇒ α)
  | Varₘ : ∀ Γ α, mem_index α Γ → termₘ μ Γ α
  | Appₘ : ∀ Γ α β, termₘ μ Γ (α ⇒ β) → termₘ μ Γ α → termₘ μ Γ β
  | Absₘ : ∀ Γ α β, termₘ μ (β :: Γ) α → termₘ μ Γ (β ⇒ α).
Arguments kₘ {μ Γ}.
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
  (case_kₘ : ∀ Γ n, P Γ ι (kₘ n))
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (s' : termₘ μ Γ ι), P Γ ι s' → ∀ f : Zm μ →₀ termₘ μ Γ ι, (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some t' => P Γ ι t' | None => True end → P Γ ι (switchₘ s' f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (s' : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) s' → ∀ t' : termₘ μ Γ α, P Γ α t' → P Γ β (s' $ₘ t'))
  (case_Absₘ : ∀ Γ α β (s' : termₘ μ (β :: Γ) α), P (β :: Γ) α s' → P Γ (β ⇒ α) (λₘ: β, s')) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @kₘ _ Γ n => case_kₘ Γ n
    | @Pₘ _ Γ => case_Pₘ Γ
    | @Sₘ _ Γ => case_Sₘ Γ
    | @switchₘ _ Γ s' f => case_switchₘ Γ s' (F Γ ι s') f (λ n, F Γ ι (f n)) (match stabilizing_fun_default f as t' return match t' with Some t' => P Γ ι t' | None => True end with Some t' => F Γ ι t' | None => I end)
    | @fixₘ _ Γ α => case_fixₘ Γ α
    | @Varₘ _ Γ α mi => case_Varₘ Γ α mi
    | @Appₘ _ Γ α β s' t' => case_Appₘ Γ α β s' (F Γ (α ⇒ β) s') t' (F Γ α t')
    | @Absₘ _ Γ α β s' => case_Absₘ Γ α β s' (F (β :: Γ) α s')
    end.

Definition termₘ_ind (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Prop)
  (case_kₘ : ∀ Γ n, P Γ ι (kₘ n))
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (s' : termₘ μ Γ ι), P Γ ι s' → ∀ f : Zm μ →₀ termₘ μ Γ ι, (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some t' => P Γ ι t' | None => True end → P Γ ι (switchₘ s' f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (s' : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) s' → ∀ t' : termₘ μ Γ α, P Γ α t' → P Γ β (s' $ₘ t'))
  (case_Absₘ : ∀ Γ α β (s' : termₘ μ (β :: Γ) α), P (β :: Γ) α s' → P Γ (β ⇒ α) (λₘ: β, s')) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @kₘ _ Γ n => case_kₘ Γ n
    | @Pₘ _ Γ => case_Pₘ Γ
    | @Sₘ _ Γ => case_Sₘ Γ
    | @switchₘ _ Γ s' f => case_switchₘ Γ s' (F Γ ι s') f (λ n, F Γ ι (f n)) (match stabilizing_fun_default f as t' return match t' with Some t' => P Γ ι t' | None => True end with Some t' => F Γ ι t' | None => I end)
    | @fixₘ _ Γ α => case_fixₘ Γ α
    | @Varₘ _ Γ α mi => case_Varₘ Γ α mi
    | @Appₘ _ Γ α β s' t' => case_Appₘ Γ α β s' (F Γ (α ⇒ β) s') t' (F Γ α t')
    | @Absₘ _ Γ α β s' => case_Absₘ Γ α β s' (F (β :: Γ) α s')
    end.

Definition termₘ_rec (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Set) := termₘ_rect μ P.

Equations Derive Signature for termₘ.
Equations Derive NoConfusion for termₘ.

Instance dec_eq_termₘ {μ Γ α} : EqDec (termₘ μ Γ α) eq.
Proof.
  rewrite dec_eq_def.
  intros s_1; induction s_1 as [Γ_1 n_1 | Γ_1 | Γ_1 | Γ_1 s'_1 IH_s' f_1 IH_f IH_f_default | Γ_1 α_1 | Γ_1 α_1 mi_1 | Γ_1 α_1 β_1 s'_1 IH_s' t'_1 IH_t' | Γ_1 α_1 β_1 s'_1 IH_s']; intros s_2.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_2 n_2 | @switchₘ Γ_2 s'_2 f_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2]); try (right; congruence).
    destruct (n_1 == n_2) as [H_n | H_n]; constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_ n_2 | @switchₘ Γ_2 s'_2 f_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2]); try (right; congruence).
    specialize (IH_s' s'_2). ltac1:(pose proof (IH'_f := λ n, IH_f n (f_2 n))); clear IH_f.
    assert (H_f_default : {stabilizing_fun_default f_1 = stabilizing_fun_default f_2} + {stabilizing_fun_default f_1 ≠ stabilizing_fun_default f_2}). {
      remember (stabilizing_fun_default f_1) as f_default_1 eqn:H_f_default_1; remember (stabilizing_fun_default f_2) as f_default_2 eqn:H_f_default_2. destruct f_default_1 as [t'_1 |], f_default_2 as [t'_2 |]; try (right; congruence).
      - specialize (IH_f_default t'_2). destruct IH_f_default; constructor; congruence.
      - left; reflexivity.
    }
    ltac1:(pose proof (H_f := dec_eq_stabilizing_fun_minimal f_1 f_2 IH'_f H_f_default)).
    destruct IH_s' as [IH_s' | IH_s'] > [destruct H_f as [H_f | H_f] |]; constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_ n_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 s'_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    destruct (mi_1 == mi_2 : {_ = _} + {_ ≠ _}) as [-> | H_mi]; constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_ n_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 s'_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    destruct (α_1 == α_2) as [-> | H_α]; try (right; congruence). specialize (IH_s' s'_2). specialize (IH_t' t'_2).
    destruct IH_s' as [IH_s' | IH_s'] > [destruct IH_t' as [IH_t' | IH_t'] |].
    + left; congruence.
    + right. intros H. apply IH_t'. injection H as _ H. do 2 (apply inj_right_pair in H). auto.
    + right. intros H. apply IH_s'. injection H as H _. do 3 (apply inj_right_pair in H). auto.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    specialize (IH_s' s'_2). destruct IH_s' as [IH_s' | IH_s']; constructor; congruence.
Defined.

Inductive termₘ_direct_subterm {μ} : ∀ {Γ_1 α_1 Γ_2 α_2}, termₘ μ Γ_1 α_1 → termₘ μ Γ_2 α_2 → Prop :=
  | termₘ_direct_subterm_switchₘ_s' :
    ∀ {Γ} (s' : termₘ μ Γ ι) (f : Zm μ →₀ termₘ μ Γ ι),
    termₘ_direct_subterm s' (switchₘ s' f)
  | termₘ_direct_subterm_switchₘ_f :
    ∀ {Γ} (s' : termₘ μ Γ ι) (f : Zm μ →₀ termₘ μ Γ ι) n,
    termₘ_direct_subterm (f n) (switchₘ s' f)
  | termₘ_direct_subterm_Appₘ_s' :
    ∀ {Γ α β} (s' : termₘ μ Γ (α ⇒ β)) (t' : termₘ μ Γ α),
    termₘ_direct_subterm s' (s' $ₘ t')
  | termₘ_direct_subterm_Appₘ_t' :
    ∀ {Γ α β} (s' : termₘ μ Γ (α ⇒ β)) (t' : termₘ μ Γ α),
    termₘ_direct_subterm t' (s' $ₘ t')
  | termₘ_direct_subterm_Absₘ_s' :
    ∀ {Γ α} β (s' : termₘ μ (β :: Γ) α),
    termₘ_direct_subterm s' (λₘ: β, s').

Hint Resolve termₘ_direct_subterm_switchₘ_s' : subterm_relation.
Hint Resolve termₘ_direct_subterm_switchₘ_f : subterm_relation.
Hint Resolve termₘ_direct_subterm_Appₘ_s' : subterm_relation.
Hint Resolve termₘ_direct_subterm_Appₘ_t' : subterm_relation.
Hint Resolve termₘ_direct_subterm_Absₘ_s' : subterm_relation.

Definition termₘ_subterm {μ} :=
  Relation_Operators.clos_trans
    (sigma (λ index : sigma (λ _ : list type, type), termₘ μ (pr1 index) (pr2 index)))
    (λ s t, termₘ_direct_subterm (pr2 s) (pr2 t)).

Hint Unfold termₘ_subterm : subterm_relation.

Instance well_founded_termₘ_subterm {μ} : WellFounded (@termₘ_subterm μ).
Proof.
  apply Transitive_Closure.wf_clos_trans. intros [[Γ_1 α_1] s_1]; simpl in s_1.
  induction s_1 as [Γ_1 n_1 | Γ_1 | Γ_1 | Γ_1 s'_1 IH_s' f_1 IH_f IH_f_default | Γ_1 α_1 | Γ_1 α_1 mi_1 | Γ_1 α_1 β_1 s'_1 IH_s' t'_1 IH_t' | Γ_1 α_1 β_1 s'_1 IH_s']; apply Acc_intro; simpl; intros [[Γ_2 α_2] s_2] H; simpl in s_2 |- *; try (solve [ltac1:(dependent elimination s_2 as [@kₘ Γ_2 n_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 s'_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2_ β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); inversion H]); ltac1:(dependent elimination H); auto.
Defined.

Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ kₘ (Zm_of_Z 0%Z).
Fail Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (λₘ: ι, Varₘ ι MIO).

Check λₘ: ι, switchₘ (Varₘ ι MIO) (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z)).

Check eq_refl : ((λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ kₘ (Zm_of_Z 0%Z) == (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ kₘ (Zm_of_Z 0%Z)) = left _.

Check eq_refl : (kₘ (Zm_of_Z 0%Z) == Sₘ $ₘ kₘ (Zm_of_Z 0%Z)) = right _.

Goal ∃ H, ((λₘ: ι, switchₘ (Varₘ ι MIO) (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z))) : termₘ 3 [] _) == (λₘ: ι, switchₘ (Varₘ ι MIO) (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z))) = left H.
Proof.
  eexists. reflexivity.
Qed.

Compute ` (bool_of_sumbool (((λₘ: ι, switchₘ (Varₘ ι MIO) (Zm_of_Z 100 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 11 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z))) : termₘ 10 [] _) == (λₘ: ι, switchₘ (Varₘ ι MIO) (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 20%Z))))).

Definition substitutionₘ μ Γ Δ := ∀ (α : type), mem_index α Δ → termₘ μ Γ α.

Definition substitutionₘ_of_renaming {μ Γ Δ} (σ : renaming Γ Δ) : substitutionₘ μ Γ Δ :=
  λ _ mi, Varₘ _ (σ _ mi).

Definition substitutionₘ_id {μ Γ} : substitutionₘ μ Γ Γ :=
  substitutionₘ_of_renaming renaming_id.

Equations substitutionₘ_cons {μ Γ Δ} α (s : termₘ μ Γ α) (σ : substitutionₘ μ Γ Δ) : substitutionₘ μ Γ (α :: Δ) :=
  | α, mi, σ, _, MIO => mi
  | α, mi, σ, _, MIS mi' => σ _ mi'.

Definition substitutionₘ_shift {μ α Γ} : substitutionₘ μ (α :: Γ) Γ :=
  substitutionₘ_of_renaming renaming_shift.

Section renaming_inst_termₘ.
  Context {μ : nat}.

  Equations renaming_inst_termₘ {Γ Δ α} (σ : renaming Γ Δ) (s : termₘ μ Δ α) : termₘ μ Γ α by wf (signature_pack s) :=
    | σ, kₘ n => kₘ n
    | σ, Pₘ => Pₘ
    | σ, Sₘ => Sₘ
    | σ, switchₘ s' f => switchₘ (renaming_inst_termₘ σ s') (stabilizing_fun_map_minimal (λ a, renaming_inst_termₘ σ (f a)) f _)
    | σ, fixₘ α => fixₘ α
    | σ, Varₘ α mi => Varₘ α (σ α mi)
    | σ, Appₘ s' t' => Appₘ (renaming_inst_termₘ σ s') (renaming_inst_termₘ σ t')
    | σ, Absₘ β s' => Absₘ β (renaming_inst_termₘ (renaming_up σ) s').
  Next Obligation.
    intros Γ Δ σ s' f renaming_inst_termₘ a_1 a_2 H_f_a. simpl.
    generalize (renaming_inst_termₘ_obligations_obligation_2 Δ s' f a_1) as H_1, (renaming_inst_termₘ_obligations_obligation_2 Δ s' f a_2) as H_2; intros H_1 H_2.
    destruct H_f_a. f_equal; apply proof_irrelevance.
  Defined.
End renaming_inst_termₘ.

Lemma renaming_inst_termₘ_equation_4' {μ : nat} :
  ∀ (Γ Δ : list type) (σ : renaming Γ Δ) (s' : termₘ μ Δ ι) (f : Zm μ →₀ termₘ μ Δ ι),
  renaming_inst_termₘ σ (switchₘ s' f) =
  switchₘ (renaming_inst_termₘ σ s') (stabilizing_fun_map (renaming_inst_termₘ σ) f).
Proof.
  intros Γ Δ σ s' f. rewrite renaming_inst_termₘ_equation_4. unfold stabilizing_fun_map. do 2 f_equal.
  apply functional_extensionality_dep; intros; apply functional_extensionality_dep; intros; apply functional_extensionality_dep; intros; apply proof_irrelevance.
Qed.

Hint Rewrite @renaming_inst_termₘ_equation_1 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_2 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_3 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_4' : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_5 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_6 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_7 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_8 : renaming_inst_termₘ'.

Reserved Notation "s_1  ⟶ₘ  s_2" (at level 70).

Inductive termₘ_step {μ} : ∀ {Γ α}, termₘ μ Γ α → termₘ μ Γ α → Prop :=
  | termₘ_step_switchₘ_cong :
    ∀ {Γ} (s'_1 s'_2 : termₘ μ Γ ι) (f_1 f_2 : Zm μ →₀ termₘ μ Γ ι),
    s'_1 ⟶ₘ s'_2 →
    (∀ n, f_1 n ⟶ₘ f_2 n) →
    switchₘ s'_1 f_1 ⟶ₘ switchₘ s'_2 f_2
  | termₘ_step_Appₘ :
    ∀ {Γ α β} (s'_1 s'_2 : termₘ μ Γ (α ⇒ β)) (t'_1 t'_2 : termₘ μ Γ α),
    s'_1 ⟶ₘ s'_2 →
    t'_1 ⟶ₘ t'_2 →
    Appₘ s'_1 t'_1 ⟶ₘ Appₘ s'_2 t'_2
  | termₘ_step_Absₘ :
    ∀ {Γ α β} (s'_1 s'_2 : termₘ μ (β :: Γ) α),
    s'_1 ⟶ₘ s'_2 →
    Absₘ β s'_1 ⟶ₘ Absₘ β s'_2
  where "s_1 ⟶ₘ s_2" := (termₘ_step s_1 s_2).
