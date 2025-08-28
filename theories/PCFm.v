From PCF Require Import Tools.
From PCF Require Import Zm.
From PCF Require Import Types.

Unset Elimination Schemes.

Inductive termₘ μ : list type → type → Type :=
  | kₘ : ∀ Γ, Zm μ → termₘ μ Γ ι
  | Pₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | Sₘ : ∀ Γ, termₘ μ Γ (ι ⇒ ι)
  | switchₘ : ∀ Γ, (Zm μ →₀ termₘ μ Γ ι) → termₘ μ Γ (ι ⇒ ι)
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
Notation "'λₘ:'  α ','  s" := (Absₘ α s) (at level 60, s at level 60, right associativity).

Definition termₘ_rect (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Type)
  (case_kₘ : ∀ Γ n, P Γ ι (kₘ n))
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (f : Zm μ →₀ termₘ μ Γ ι), (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some t' => P Γ ι t' | None => True end → P Γ (ι ⇒ ι) (switchₘ f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (s' : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) s' → ∀ t' : termₘ μ Γ α, P Γ α t' → P Γ β (s' $ₘ t'))
  (case_Absₘ : ∀ Γ α β (s' : termₘ μ (β :: Γ) α), P (β :: Γ) α s' → P Γ (β ⇒ α) (λₘ: β, s')) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @kₘ _ Γ n => case_kₘ Γ n
    | @Pₘ _ Γ => case_Pₘ Γ
    | @Sₘ _ Γ => case_Sₘ Γ
    | @switchₘ _ Γ f => case_switchₘ Γ f (λ n, F Γ ι (f n)) (match stabilizing_fun_default f as t' return match t' with Some t' => P Γ ι t' | None => True end with Some t' => F Γ ι t' | None => I end)
    | @fixₘ _ Γ α => case_fixₘ Γ α
    | @Varₘ _ Γ α mi => case_Varₘ Γ α mi
    | @Appₘ _ Γ α β s' t' => case_Appₘ Γ α β s' (F Γ (α ⇒ β) s') t' (F Γ α t')
    | @Absₘ _ Γ α β s' => case_Absₘ Γ α β s' (F (β :: Γ) α s')
    end.

Definition termₘ_ind (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Prop)
  (case_kₘ : ∀ Γ n, P Γ ι (kₘ n))
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (f : Zm μ →₀ termₘ μ Γ ι), (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some t' => P Γ ι t' | None => True end → P Γ (ι ⇒ ι) (switchₘ f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (s' : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) s' → ∀ t' : termₘ μ Γ α, P Γ α t' → P Γ β (s' $ₘ t'))
  (case_Absₘ : ∀ Γ α β (s' : termₘ μ (β :: Γ) α), P (β :: Γ) α s' → P Γ (β ⇒ α) (λₘ: β, s')) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @kₘ _ Γ n => case_kₘ Γ n
    | @Pₘ _ Γ => case_Pₘ Γ
    | @Sₘ _ Γ => case_Sₘ Γ
    | @switchₘ _ Γ f => case_switchₘ Γ f (λ n, F Γ ι (f n)) (match stabilizing_fun_default f as t' return match t' with Some t' => P Γ ι t' | None => True end with Some t' => F Γ ι t' | None => I end)
    | @fixₘ _ Γ α => case_fixₘ Γ α
    | @Varₘ _ Γ α mi => case_Varₘ Γ α mi
    | @Appₘ _ Γ α β s' t' => case_Appₘ Γ α β s' (F Γ (α ⇒ β) s') t' (F Γ α t')
    | @Absₘ _ Γ α β s' => case_Absₘ Γ α β s' (F (β :: Γ) α s')
    end.

Definition termₘ_rec (μ : nat) (P : ∀ Γ α, termₘ μ Γ α → Set) := termₘ_rect μ P.

Equations Derive Signature for termₘ.
Equations Derive NoConfusion for termₘ.

Instance arbitrary_termₘ {μ Γ α} : Arbitrary (termₘ μ Γ α).
Proof.
  revert Γ; induction α as [| α' IH_α' β' IH_β']; intros Γ.
  - apply (kₘ (Zm_of_Z 0%Z)).
  - apply Absₘ. apply IH_β'.
Defined.

Instance dec_eq_termₘ {μ Γ α} : EqDec (termₘ μ Γ α) eq.
Proof.
  rewrite dec_eq_def.
  intros s_1; induction s_1 as [Γ_1 n_1 | Γ_1 | Γ_1 | Γ_1 f_1 IH_f IH_f_default | Γ_1 α_1 | Γ_1 α_1 mi_1 | Γ_1 α_1 β_1 s'_1 IH_s' t'_1 IH_t' | Γ_1 α_1 β_1 s'_1 IH_s']; intros s_2.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_2 n_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2]); try (right; congruence).
    destruct (n_1 == n_2) as [H_n | H_n]; constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    ltac1:(pose proof (IH'_f := λ n, IH_f n (f_2 n))); clear IH_f.
    assert (H_f_default : {stabilizing_fun_default f_1 = stabilizing_fun_default f_2} + {stabilizing_fun_default f_1 ≠ stabilizing_fun_default f_2}). {
      remember (stabilizing_fun_default f_1) as f_default_1 eqn:H_f_default_1; remember (stabilizing_fun_default f_2) as f_default_2 eqn:H_f_default_2. destruct f_default_1 as [t'_1 |], f_default_2 as [t'_2 |]; try (right; congruence).
      - specialize (IH_f_default t'_2). destruct IH_f_default; constructor; congruence.
      - left; reflexivity.
    }
    ltac1:(pose proof (H_f := dec_eq_stabilizing_fun_minimal f_1 f_2 IH'_f H_f_default)).
    destruct H_f as [H_f | H_f]; constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_2 n_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    destruct (mi_1 == mi_2 : {_ = _} + {_ ≠ _}) as [-> | H_mi]; constructor; congruence.
  - ltac1:(dependent elimination s_2 as [@kₘ Γ_2 n_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    destruct (α_1 == α_2) as [-> | H_α]; try (right; congruence). specialize (IH_s' s'_2). specialize (IH_t' t'_2).
    destruct IH_s' as [IH_s' | IH_s'] > [destruct IH_t' as [IH_t' | IH_t'] |].
    + left; congruence.
    + right. intros H. apply IH_t'. injection H as _ H. do 2 (apply inj_right_pair in H). auto.
    + right. intros H. apply IH_s'. injection H as H _. do 3 (apply inj_right_pair in H). auto.
  - ltac1:(dependent elimination s_2 as [@Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2 β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); try (right; congruence).
    specialize (IH_s' s'_2). destruct IH_s' as [IH_s' | IH_s']; constructor; congruence.
Defined.

Inductive termₘ_direct_subterm {μ} : ∀ {Γ_1 α_1 Γ_2 α_2}, termₘ μ Γ_1 α_1 → termₘ μ Γ_2 α_2 → Prop :=
  | termₘ_direct_subterm_switchₘ_f :
    ∀ {Γ} (f : Zm μ →₀ termₘ μ Γ ι) n,
    termₘ_direct_subterm (f n) (switchₘ f)
  | termₘ_direct_subterm_switchₘ_f_default :
    ∀ {Γ} (f : Zm μ →₀ termₘ μ Γ ι) (t' : termₘ μ Γ ι),
    stabilizing_fun_default f = Some t' →
    termₘ_direct_subterm t' (switchₘ f)
  | termₘ_direct_subterm_Appₘ_s' :
    ∀ {Γ α β} (s' : termₘ μ Γ (α ⇒ β)) (t' : termₘ μ Γ α),
    termₘ_direct_subterm s' (s' $ₘ t')
  | termₘ_direct_subterm_Appₘ_t' :
    ∀ {Γ α β} (s' : termₘ μ Γ (α ⇒ β)) (t' : termₘ μ Γ α),
    termₘ_direct_subterm t' (s' $ₘ t')
  | termₘ_direct_subterm_Absₘ_s' :
    ∀ {Γ α} β (s' : termₘ μ (β :: Γ) α),
    termₘ_direct_subterm s' (λₘ: β, s').

Hint Resolve termₘ_direct_subterm_switchₘ_f : subterm_relation.
Hint Resolve termₘ_direct_subterm_switchₘ_f_default : subterm_relation.
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
  induction s_1 as [Γ_1 n_1 | Γ_1 | Γ_1 | Γ_1 f_1 IH_f IH_f_default | Γ_1 α_1 | Γ_1 α_1 mi_1 | Γ_1 α_1 β_1 s'_1 IH_s' t'_1 IH_t' | Γ_1 α_1 β_1 s'_1 IH_s']; apply Acc_intro; simpl; intros [[Γ_2 α_2] s_2] H; simpl in s_2 |- *; try (solve [ltac1:(dependent elimination s_2 as [@kₘ Γ_2 n_2 | @Pₘ Γ_2 | @Sₘ Γ_2 | @switchₘ Γ_2 f_2 | @fixₘ Γ_2 α_2 | @Varₘ Γ_2 α_2 mi_2 | @Appₘ Γ_2 α_2_ β_2 s'_2 t'_2 | @Absₘ Γ_2 α_2 β_2 s'_2]); inversion H]); try (solve[ltac1:(dependent elimination H); auto]).
  ltac1:(dependent elimination H as [@termₘ_direct_subterm_switchₘ_f Γ_1 f_1 n | @termₘ_direct_subterm_switchₘ_f_default Γ_1 f_1 t'_1 H_t'_1]); auto. destruct (stabilizing_fun_default f_1) as [x |]; congruence.
Defined.

Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ kₘ (Zm_of_Z 0%Z).
Fail Check (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (λₘ: ι, Varₘ ι MIO).

Check λₘ: ι, switchₘ (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z)) $ₘ Varₘ ι MIO.

Check eq_refl : ((λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ kₘ (Zm_of_Z 0%Z) == (λₘ: ι, λₘ: ι, Varₘ ι (MIS MIO)) $ₘ (Sₘ $ₘ Varₘ ι MIO) $ₘ kₘ (Zm_of_Z 0%Z)) = left _.

Check eq_refl : (kₘ (Zm_of_Z 0%Z) == Sₘ $ₘ kₘ (Zm_of_Z 0%Z)) = right _.

Goal ∃ H, ((λₘ: ι, switchₘ (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z)) $ₘ Varₘ ι MIO) : termₘ 3 [] _) == (λₘ: ι, switchₘ (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z)) $ₘ Varₘ ι MIO) = left H.
Proof.
  eexists. reflexivity.
Qed.

Compute ` (bool_of_sumbool (((λₘ: ι, switchₘ (Zm_of_Z 100 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 11 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 0%Z)) $ₘ Varₘ ι MIO) : termₘ 10 [] _) == (λₘ: ι, switchₘ (Zm_of_Z 0 ↦₀ Sₘ $ₘ (Sₘ $ₘ kₘ (Zm_of_Z 0%Z)), Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 0%Z), _ ↦₀ Sₘ $ₘ kₘ (Zm_of_Z 20%Z)) $ₘ Varₘ ι MIO))).

Section rebuild_termₘ.
  Context {μ : nat}.

  Equations rebuild_termₘ {Γ α} (s : termₘ μ Γ α) : termₘ μ Γ α by wf (signature_pack s) :=
    | kₘ n => kₘ n
    | Pₘ => Pₘ
    | Sₘ => Sₘ
    | switchₘ f =>
      switchₘ
        (stabilizing_fun_rebuild_erased
          (stabilizing_fun_map_minimal
            (λ a, rebuild_termₘ (f a))
            (match stabilizing_fun_default f as f_default return stabilizing_fun_default f = f_default → option (termₘ μ Γ ι) with
            | Some t' => λ H_t', Some (rebuild_termₘ t')
            | None => λ _, None
            end eq_refl)
            f
            _)
        )
    | fixₘ α => fixₘ α
    | Varₘ α mi => Varₘ α mi
    | s' $ₘ t' => (rebuild_termₘ s') $ₘ (rebuild_termₘ t')
    | λₘ: β, s' => λₘ: β, rebuild_termₘ s'.
  Next Obligation.
    intros Γ f renaming_inst_termₘ a_1 a_2 H_f_a. simpl.
    generalize (rebuild_termₘ_obligations_obligation_1 Γ f a_1) as H_1, (rebuild_termₘ_obligations_obligation_1 Γ f a_2) as H_2; intros H_1 H_2.
    destruct H_f_a. f_equal; apply proof_irrelevance.
  Defined.
End rebuild_termₘ.

Definition substitutionₘ μ Γ Δ := ∀ (α : type), mem_index α Δ → termₘ μ Γ α.

Definition substitutionₘ_of_renaming {μ Γ Δ} (σ : renaming Γ Δ) : substitutionₘ μ Γ Δ :=
  λ _ mi, Varₘ _ (σ _ mi).

Definition substitutionₘ_id {μ} Γ : substitutionₘ μ Γ Γ :=
  substitutionₘ_of_renaming (renaming_id Γ).

Equations substitutionₘ_cons {μ Γ Δ} α (s : termₘ μ Γ α) (σ : substitutionₘ μ Γ Δ) : substitutionₘ μ Γ (α :: Δ) :=
  | α, mi, σ, _, MIO => mi
  | α, mi, σ, _, MIS mi' => σ _ mi'.

Definition substitutionₘ_shift {μ} α Γ : substitutionₘ μ (α :: Γ) Γ :=
  substitutionₘ_of_renaming (renaming_shift α Γ).

Section renaming_inst_termₘ.
  Context {μ : nat}.

  Equations renaming_inst_termₘ {Γ Δ α} (σ : renaming Γ Δ) (s : termₘ μ Δ α) : termₘ μ Γ α by wf (signature_pack s) :=
    | σ, kₘ n => kₘ n
    | σ, Pₘ => Pₘ
    | σ, Sₘ => Sₘ
    | σ, switchₘ f =>
      switchₘ
        (stabilizing_fun_map_minimal
          (λ a, renaming_inst_termₘ σ (f a))
          (match stabilizing_fun_default f as f_default return stabilizing_fun_default f = f_default → option (termₘ μ Γ ι) with
          | Some t' => λ H_t', Some (renaming_inst_termₘ σ t')
          | None => λ _, None
          end eq_refl)
          f
          _)
    | σ, fixₘ α => fixₘ α
    | σ, Varₘ α mi => Varₘ α (σ α mi)
    | σ, s' $ₘ t' => (renaming_inst_termₘ σ s') $ₘ (renaming_inst_termₘ σ t')
    | σ, λₘ: β, s' => λₘ: β, renaming_inst_termₘ (renaming_up β σ) s'.
  Next Obligation.
    intros Γ Δ σ f renaming_inst_termₘ a_1 a_2 H_f_a. simpl.
    generalize (renaming_inst_termₘ_obligations_obligation_1 Δ f a_1) as H_1, (renaming_inst_termₘ_obligations_obligation_1 Δ f a_2) as H_2; intros H_1 H_2.
    destruct H_f_a. f_equal; apply proof_irrelevance.
  Defined.
End renaming_inst_termₘ.

Lemma renaming_inst_termₘ_equation_4' {μ : nat} :
  ∀ Γ Δ (σ : renaming Γ Δ) (f : Zm μ →₀ termₘ μ Δ ι),
  renaming_inst_termₘ σ (switchₘ f) = switchₘ (stabilizing_fun_map (renaming_inst_termₘ σ) f).
Proof.
  intros Γ Δ σ f. rewrite renaming_inst_termₘ_equation_4. unfold stabilizing_fun_map. do 2 f_equal.
  - destruct (stabilizing_fun_default f); reflexivity.
  - apply functional_extensionality_dep; intros; apply functional_extensionality_dep; intros; apply functional_extensionality_dep; intros; apply proof_irrelevance.
Qed.

Hint Rewrite @renaming_inst_termₘ_equation_1 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_2 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_3 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_4' : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_5 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_6 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_7 : renaming_inst_termₘ'.
Hint Rewrite @renaming_inst_termₘ_equation_8 : renaming_inst_termₘ'.

Definition substitutionₘ_comp_renaming {μ Γ Δ Θ} (τ : substitutionₘ μ Δ Θ) (σ : renaming Γ Δ) : substitutionₘ μ Γ Θ :=
  λ _ mi, renaming_inst_termₘ σ (τ _ mi).

Definition substitutionₘ_up {μ Γ Δ} α (σ : substitutionₘ μ Γ Δ) : substitutionₘ μ (α :: Γ) (α :: Δ) :=
  substitutionₘ_cons α (Varₘ α MIO) (substitutionₘ_comp_renaming σ (renaming_shift α Γ)).

Section substitutionₘ_inst.
  Context {μ : nat}.

  Equations substitutionₘ_inst {Γ Δ α} (σ : substitutionₘ μ Γ Δ) (s : termₘ μ Δ α) : termₘ μ Γ α by wf (signature_pack s) :=
    | σ, kₘ n => kₘ n
    | σ, Pₘ => Pₘ
    | σ, Sₘ => Sₘ
    | σ, switchₘ f =>
      switchₘ
        (stabilizing_fun_map_minimal
          (λ a, substitutionₘ_inst σ (f a))
          (match stabilizing_fun_default f as f_default return stabilizing_fun_default f = f_default → option (termₘ μ Γ ι) with
          | Some t' => λ H_t', Some (substitutionₘ_inst σ t')
          | None => λ _, None
          end eq_refl)
          f
          _)
    | σ, fixₘ α => fixₘ α
    | σ, Varₘ α mi => σ α mi
    | σ, s' $ₘ t' => (substitutionₘ_inst σ s') $ₘ (substitutionₘ_inst σ t')
    | σ, λₘ: β, s' => λₘ: β, substitutionₘ_inst (substitutionₘ_up β σ) s'.
  Next Obligation.
    intros Γ Δ σ f substitutionₘ_inst a_1 a_2 H_f_a. simpl.
    generalize (substitutionₘ_inst_obligations_obligation_1 Δ f a_1) as H_1, (substitutionₘ_inst_obligations_obligation_1 Δ f a_2) as H_2; intros H_1 H_2.
    destruct H_f_a. f_equal; apply proof_irrelevance.
  Defined.
End substitutionₘ_inst.

Lemma substitutionₘ_inst_equation_4' {μ : nat} :
  ∀ Γ Δ (σ : substitutionₘ μ Γ Δ) (f : Zm μ →₀ termₘ μ Δ ι),
  substitutionₘ_inst σ (switchₘ f) = switchₘ  (stabilizing_fun_map (substitutionₘ_inst σ) f).
Proof.
  intros Γ Δ σ f. rewrite substitutionₘ_inst_equation_4. unfold stabilizing_fun_map. do 2 f_equal.
  - destruct (stabilizing_fun_default f); reflexivity.
  - apply functional_extensionality_dep; intros; apply functional_extensionality_dep; intros; apply functional_extensionality_dep; intros; apply proof_irrelevance.
Qed.

Hint Rewrite @substitutionₘ_inst_equation_1 : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_2 : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_3 : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_4' : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_5 : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_6 : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_7 : substitutionₘ_inst'.
Hint Rewrite @substitutionₘ_inst_equation_8 : substitutionₘ_inst'.

Definition substitutionₘ_comp {μ Γ Δ Θ} (τ : substitutionₘ μ Δ Θ) (σ : substitutionₘ μ Γ Δ) : substitutionₘ μ Γ Θ :=
  λ _ mi, substitutionₘ_inst σ (τ _ mi).

Lemma renaming_id_def_termₘ {μ} :
  ∀ Γ,
  @substitutionₘ_of_renaming μ _ _ (renaming_id Γ) = substitutionₘ_id Γ.
Proof.
  intros Γ. reflexivity.
Qed.

Lemma renaming_cons_def_termₘ {μ Γ Δ} :
  ∀ α (mi : mem_index α Γ) (σ : renaming Γ Δ),
  @substitutionₘ_of_renaming μ _ _ (renaming_cons α mi σ) = substitutionₘ_cons α (Varₘ α mi) (substitutionₘ_of_renaming σ).
Proof.
  intros α mi σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi_1.
  unfold substitutionₘ_of_renaming. ltac1:(dependent elimination mi_1 as [@MIO Γ' | @MIS γ Γ' mi_1']); ltac1:(simp renaming_cons substitutionₘ_cons); reflexivity.
Qed.

Lemma renaming_shift_def_termₘ {μ} :
  ∀ α Γ,
  @substitutionₘ_of_renaming μ _ _ (renaming_shift α Γ) = substitutionₘ_shift α Γ.
Proof.
  intros α Γ. reflexivity.
Qed.

Lemma renaming_comp_def_termₘ {μ Γ Δ Θ} :
  ∀ (τ : renaming Δ Θ) (σ : renaming Γ Δ),
  @substitutionₘ_of_renaming μ _ _ (renaming_comp τ σ) = substitutionₘ_comp_renaming (substitutionₘ_of_renaming τ) σ.
Proof.
  intros τ σ. reflexivity.
Qed.

Lemma renaming_up_def_termₘ {μ Γ Δ} :
  ∀ α (σ : renaming Γ Δ),
  @substitutionₘ_of_renaming μ _ _ (renaming_up α σ) = substitutionₘ_up α (substitutionₘ_of_renaming σ).
Proof.
  intros α σ. unfold renaming_up, substitutionₘ_up. rewrite renaming_cons_def_termₘ, renaming_comp_def_termₘ. reflexivity.
Qed.

Lemma renaming_inst_termₘ_def {μ Γ Δ α} :
  ∀ (σ : renaming Γ Δ) (s : termₘ μ Δ α),
  renaming_inst_termₘ σ s = substitutionₘ_inst (substitutionₘ_of_renaming σ) s.
Proof.
  intros σ s. revert Γ σ; induction s as [Δ n | Δ | Δ | Δ f IH_f IH_f_default | Δ α | Δ α mi | Δ α β s' IH_s' t' IH_t' | Δ α β s' IH_s']; intros Γ σ; ltac1:(simp renaming_inst_termₘ' substitutionₘ_inst'); try (congruence).
  - f_equal. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_f. reflexivity.
    + destruct (stabilizing_fun_default f) as [t' |].
      * simpl. rewrite IH_f_default. reflexivity.
      * reflexivity.
  - reflexivity.
  - rewrite IH_s'. rewrite renaming_up_def_termₘ. reflexivity.
Qed.

Lemma substitutionₘ_comp_renaming_def {μ Γ Δ Θ} :
  ∀ (τ : substitutionₘ μ Δ Θ) (σ : renaming Γ Δ),
  substitutionₘ_comp_renaming τ σ = substitutionₘ_comp τ (substitutionₘ_of_renaming σ).
Proof.
  intros τ σ. unfold substitutionₘ_comp_renaming, substitutionₘ_comp. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  rewrite renaming_inst_termₘ_def. reflexivity.
Qed.

Lemma substitutionₘ_up_def {μ Γ Δ} :
  ∀ α (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_up α σ = substitutionₘ_cons α (Varₘ α MIO) (substitutionₘ_comp σ (substitutionₘ_shift α Γ)).
Proof.
  intros α σ. unfold substitutionₘ_up. rewrite substitutionₘ_comp_renaming_def, renaming_shift_def_termₘ. reflexivity.
Qed.

Lemma substitutionₘ_up_substitutionₘ_of_renaming {μ Γ Δ} :
  ∀ α (σ : renaming Γ Δ),
  substitutionₘ_up α (@substitutionₘ_of_renaming μ _ _ σ) = substitutionₘ_of_renaming (renaming_cons α MIO (renaming_comp σ (renaming_shift α Γ))).
Proof.
  intros α σ. rewrite substitutionₘ_up_def, renaming_cons_def_termₘ, renaming_comp_def_termₘ, substitutionₘ_comp_renaming_def. unfold substitutionₘ_shift. reflexivity.
Qed.

Lemma substitutionₘ_inst_kₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ) n,
  substitutionₘ_inst σ (kₘ n) = kₘ n.
Proof.
  intros σ n. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_Pₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_inst σ Pₘ = Pₘ.
Proof.
  intros σ. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_Sₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_inst σ Sₘ = Sₘ.
Proof.
  intros σ. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_switchₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ) (f : Zm μ →₀ termₘ μ Δ ι),
  substitutionₘ_inst σ (switchₘ f) = switchₘ (stabilizing_fun_map (substitutionₘ_inst σ) f).
Proof.
  intros σ f. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_fixₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ) α,
  substitutionₘ_inst σ (fixₘ α) = fixₘ α.
Proof.
  intros σ α. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_Varₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ) α mi,
  substitutionₘ_inst σ (Varₘ α mi) = σ α mi.
Proof.
  intros σ α mi. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_appₘ {μ Γ Δ α β} :
  ∀ (σ : substitutionₘ μ Γ Δ) (s' : termₘ μ Δ (α ⇒ β)) (t' : termₘ μ Δ α),
  substitutionₘ_inst σ (s' $ₘ t') = (substitutionₘ_inst σ s') $ₘ (substitutionₘ_inst σ t').
Proof.
  intros σ s' t'. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_absₘ {μ Γ Δ α} :
  ∀ (σ : substitutionₘ μ Γ Δ) β (s' : termₘ μ (β :: Δ) α),
  substitutionₘ_inst σ (λₘ: β, s') = λₘ: β, substitutionₘ_inst (substitutionₘ_up β σ) s'.
Proof.
  intros σ β s'. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_cons_Varₘ_MIO {μ Γ Δ} :
  ∀ α (s : termₘ μ Γ α) (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_inst (substitutionₘ_cons α s σ) (Varₘ α MIO) = s.
Proof.
  intros α s σ. rewrite substitutionₘ_inst_Varₘ. ltac1:(simp substitutionₘ_cons). reflexivity.
Qed.

Lemma substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons {μ Γ Δ} :
  ∀ α (s : termₘ μ Γ α) (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_comp (substitutionₘ_shift α Δ) (substitutionₘ_cons α s σ) = σ.
Proof.
  intros α s σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp, substitutionₘ_shift, substitutionₘ_of_renaming, renaming_shift.
  rewrite substitutionₘ_inst_Varₘ. ltac1:(simp substitutionₘ_cons). reflexivity.
Qed.

Lemma substitutionₘ_comp_substitutionₘ_cons {μ Γ Δ Θ} :
  ∀ α (s : termₘ μ Δ α) (τ : substitutionₘ μ Δ Θ) (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_comp (substitutionₘ_cons α s τ) σ = substitutionₘ_cons α (substitutionₘ_inst σ s) (substitutionₘ_comp τ σ).
Proof.
  intros α s τ σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp. ltac1:(dependent elimination mi as [@MIO Θ' | @MIS γ Θ' mi']); ltac1:(simp substitutionₘ_cons); reflexivity.
Qed.

Lemma substitutionₘ_recombination {μ Γ Δ α} :
  ∀ (σ : substitutionₘ μ Γ (α :: Δ)),
  substitutionₘ_cons α (substitutionₘ_inst σ (Varₘ α MIO)) (substitutionₘ_comp (substitutionₘ_shift α Δ) σ) = σ.
Proof.
  intros σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp, substitutionₘ_shift, substitutionₘ_of_renaming, renaming_shift. ltac1:(dependent elimination mi as [@MIO Θ' | @MIS γ Θ' mi']); ltac1:(simp substitutionₘ_cons); rewrite substitutionₘ_inst_Varₘ; reflexivity.
Qed.

Lemma substitutionₘ_cons_Varₘ_MIO_substitutionₘ_shift {μ Γ α} :
  substitutionₘ_cons α (@Varₘ μ _ α MIO) (substitutionₘ_shift α Γ) = substitutionₘ_id (α :: Γ).
Proof.
  apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp, substitutionₘ_shift, substitutionₘ_id, substitutionₘ_of_renaming, renaming_shift, renaming_id. ltac1:(dependent elimination mi as [@MIO Γ' | @MIS γ Γ' mi']); ltac1:(simp substitutionₘ_cons); reflexivity.
Qed.

Lemma substitutionₘ_comp_substitutionₘ_id_left {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_comp (substitutionₘ_id Δ) σ = σ.
Proof.
  intros σ. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp, substitutionₘ_id, substitutionₘ_of_renaming, renaming_id. rewrite substitutionₘ_inst_Varₘ. reflexivity.
Qed.

Lemma substitutionₘ_comp_substitutionₘ_id_right {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_comp σ (substitutionₘ_id Γ) = σ.
Proof.
  intros σ. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp. generalize (σ α mi) as s; intros s; clear σ mi.
  induction s as [Γ n | Γ | Γ | Γ f IH_f IH_f_default | Γ α | Γ α mi | Γ α β s' IH_s' t' IH_t' | Γ α β s' IH_s'].
  - rewrite substitutionₘ_inst_kₘ. reflexivity.
  - rewrite substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite substitutionₘ_inst_switchₘ. f_equal. apply stabilizing_fun_map_id.
    + intros n. rewrite IH_f. reflexivity.
    + destruct (stabilizing_fun_default f) as [t' |].
      * simpl. rewrite IH_f_default. reflexivity.
      * reflexivity.
  - rewrite substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite substitutionₘ_inst_Varₘ. unfold substitutionₘ_id, substitutionₘ_of_renaming, renaming_id. reflexivity.
  - rewrite substitutionₘ_inst_appₘ. rewrite IH_s', IH_t'. reflexivity.
  - rewrite substitutionₘ_inst_absₘ. rewrite substitutionₘ_up_def, substitutionₘ_comp_substitutionₘ_id_left, substitutionₘ_cons_Varₘ_MIO_substitutionₘ_shift. rewrite IH_s'. reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_inst_substitutionₘ_of_renaming {μ Γ Δ Θ α} :
  ∀ (τ : renaming Δ Θ) (σ : substitutionₘ μ Γ Δ) (s : termₘ μ Θ α),
  substitutionₘ_inst σ (substitutionₘ_inst (substitutionₘ_of_renaming τ) s) = substitutionₘ_inst (substitutionₘ_comp (substitutionₘ_of_renaming τ) σ) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ n | Θ | Θ | Θ f IH_f IH_f_default | Θ α | Θ α mi | Θ α β s' IH_s' t' IH_t' | Θ α β s' IH_s']; intros Γ Δ τ σ.
  - rewrite ! substitutionₘ_inst_kₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_switchₘ. f_equal. rewrite stabilizing_fun_map_stabilizing_fun_map. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_f. reflexivity.
    + destruct (stabilizing_fun_default f) as [t' |].
      * simpl. rewrite IH_f_default. reflexivity.
      * reflexivity.
  - rewrite ! substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Varₘ. unfold substitutionₘ_comp. reflexivity.
  - rewrite ! substitutionₘ_inst_appₘ. rewrite IH_s', IH_t'. reflexivity.
  - rewrite ! substitutionₘ_inst_absₘ. rewrite (substitutionₘ_up_substitutionₘ_of_renaming β τ). rewrite IH_s'. do 2 f_equal.
    rewrite (substitutionₘ_up_def β (substitutionₘ_comp (substitutionₘ_of_renaming τ) σ)), renaming_cons_def_termₘ, substitutionₘ_comp_substitutionₘ_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    rewrite substitutionₘ_up_def. unfold substitutionₘ_comp at 1 3 4, renaming_comp, substitutionₘ_of_renaming. rewrite ! substitutionₘ_inst_Varₘ.
    specialize (substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons β (Varₘ β MIO) (substitutionₘ_comp σ (substitutionₘ_shift β Γ))) as H. specialize (equal_f (equal_f_dep H γ) (τ γ mi)) as H'.
    unfold substitutionₘ_comp at 1 3, substitutionₘ_shift, substitutionₘ_of_renaming at 2 in H'. rewrite substitutionₘ_inst_Varₘ in H'.
    unfold substitutionₘ_shift. rewrite H'. reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_of_renaming_substitutionₘ_inst {μ Γ Δ Θ α} :
  ∀ (τ : substitutionₘ μ Δ Θ) (σ : renaming Γ Δ) (s : termₘ μ Θ α),
  substitutionₘ_inst (substitutionₘ_of_renaming σ) (substitutionₘ_inst τ s) = substitutionₘ_inst (substitutionₘ_comp τ (substitutionₘ_of_renaming σ)) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ n | Θ | Θ | Θ f IH_f IH_f_default | Θ α | Θ α mi | Θ α β s' IH_s' t' IH_t' | Θ α β s' IH_s']; intros Γ Δ τ σ.
  - rewrite ! substitutionₘ_inst_kₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_switchₘ. f_equal. rewrite stabilizing_fun_map_stabilizing_fun_map. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_f. reflexivity.
    + destruct (stabilizing_fun_default f) as [t' |].
      * simpl. rewrite IH_f_default. reflexivity.
      * reflexivity.
  - rewrite ! substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Varₘ. unfold substitutionₘ_comp. reflexivity.
  - rewrite ! substitutionₘ_inst_appₘ. rewrite IH_s', IH_t'. reflexivity.
  - rewrite ! substitutionₘ_inst_absₘ. rewrite (substitutionₘ_up_substitutionₘ_of_renaming β σ). rewrite IH_s'. do 2 f_equal.
    rewrite ! substitutionₘ_up_def, renaming_cons_def_termₘ, substitutionₘ_comp_substitutionₘ_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    unfold substitutionₘ_comp, substitutionₘ_shift. rewrite ! substitutionₘ_inst_substitutionₘ_inst_substitutionₘ_of_renaming.
    specialize (@substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons μ _ _ β (Varₘ β MIO) (substitutionₘ_of_renaming (renaming_comp σ (renaming_shift β Γ)))) as H. unfold substitutionₘ_shift in H. rewrite H.
    rewrite renaming_comp_def_termₘ, substitutionₘ_comp_renaming_def. reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_inst {μ Γ Δ Θ α} :
  ∀ (τ : substitutionₘ μ Δ Θ) (σ : substitutionₘ μ Γ Δ) (s : termₘ μ Θ α),
  substitutionₘ_inst σ (substitutionₘ_inst τ s) = substitutionₘ_inst (substitutionₘ_comp τ σ) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ n | Θ | Θ | Θ f IH_f IH_f_default | Θ α | Θ α mi | Θ α β s' IH_s' t' IH_t' | Θ α β s' IH_s']; intros Γ Δ τ σ.
  - rewrite ! substitutionₘ_inst_kₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_switchₘ. f_equal. rewrite stabilizing_fun_map_stabilizing_fun_map. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_f. reflexivity.
    + destruct (stabilizing_fun_default f) as [t' |].
      * simpl. rewrite IH_f_default. reflexivity.
      * reflexivity.
  - rewrite ! substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Varₘ. unfold substitutionₘ_comp. reflexivity.
  - rewrite ! substitutionₘ_inst_appₘ. rewrite IH_s', IH_t'. reflexivity.
  - rewrite ! substitutionₘ_inst_absₘ. rewrite IH_s'. do 2 f_equal.
    rewrite (substitutionₘ_up_def β τ), (substitutionₘ_up_def β (substitutionₘ_comp τ σ)), substitutionₘ_comp_substitutionₘ_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    unfold substitutionₘ_comp, substitutionₘ_shift.
    rewrite substitutionₘ_inst_substitutionₘ_inst_substitutionₘ_of_renaming, substitutionₘ_inst_substitutionₘ_of_renaming_substitutionₘ_inst, substitutionₘ_up_def.
    specialize (@substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons μ _ _ β (Varₘ β MIO) (substitutionₘ_comp σ (substitutionₘ_shift β Γ))) as H. unfold substitutionₘ_shift in H |- *. rewrite H. reflexivity.
Qed.

Lemma associativity_rev_substitutionₘ_comp {μ Γ Δ Θ Λ} :
  ∀ (υ : substitutionₘ μ Θ Λ) (τ : substitutionₘ μ Δ Θ) (σ : substitutionₘ μ Γ Δ),
  substitutionₘ_comp (substitutionₘ_comp υ τ) σ = substitutionₘ_comp υ (substitutionₘ_comp τ σ).
Proof.
  intros υ τ σ. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  unfold substitutionₘ_comp at 1 2 3. rewrite substitutionₘ_inst_substitutionₘ_inst. reflexivity.
Qed.

Hint Rewrite @renaming_id_def_termₘ : substitutionₘ.
Hint Rewrite @renaming_cons_def_termₘ : substitutionₘ.
Hint Rewrite @renaming_shift_def_termₘ : substitutionₘ.
Hint Rewrite @renaming_comp_def_termₘ : substitutionₘ.
Hint Rewrite @renaming_up_def_termₘ : substitutionₘ.
Hint Rewrite @renaming_inst_termₘ_def : substitutionₘ.
Hint Rewrite @substitutionₘ_comp_renaming_def : substitutionₘ.
Hint Rewrite @substitutionₘ_up_def : substitutionₘ.
Hint Rewrite @substitutionₘ_up_substitutionₘ_of_renaming : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_kₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_Pₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_Sₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_switchₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_fixₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_appₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_absₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_substitutionₘ_cons_Varₘ_MIO : substitutionₘ.
Hint Rewrite @substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons : substitutionₘ.
Hint Rewrite @substitutionₘ_comp_substitutionₘ_cons : substitutionₘ.
Hint Rewrite @substitutionₘ_recombination : substitutionₘ.
Hint Rewrite @substitutionₘ_comp_substitutionₘ_id_left : substitutionₘ.
Hint Rewrite @substitutionₘ_cons_Varₘ_MIO_substitutionₘ_shift : substitutionₘ.
Hint Rewrite @substitutionₘ_comp_substitutionₘ_id_left : substitutionₘ.
Hint Rewrite @substitutionₘ_comp_substitutionₘ_id_right : substitutionₘ.
Hint Rewrite @associativity_rev_substitutionₘ_comp : substitutionₘ.

Reserved Notation "s_1  ⟶ₘ  s_2" (at level 70).

Inductive termₘ_step {μ} : ∀ {Γ α}, termₘ μ Γ α → termₘ μ Γ α → Type :=
  | termₘ_step_Pₘ :
    ∀ {Γ} n,
    (@Pₘ _ Γ) $ₘ (kₘ n) ⟶ₘ kₘ (Zm_pred n)
  | termₘ_step_Sₘ :
    ∀ {Γ} n,
    (@Sₘ _ Γ) $ₘ (kₘ n) ⟶ₘ kₘ (Zm_succ n)
  | termₘ_step_switchₘ_f :
    ∀ {Γ} (f : Zm μ →₀ termₘ μ Γ ι),
    ¬ stabilizing_fun_canonical f →
    switchₘ f ⟶ₘ switchₘ (stabilizing_fun_canonize f)
  | termₘ_step_switchₘ_f_n :
    ∀ {Γ} (f : Zm μ →₀ termₘ μ Γ ι) n (t' : termₘ μ Γ ι),
    stabilizing_fun_canonical f →
    f n ⟶ₘ t' →
    switchₘ f ⟶ₘ switchₘ (n ↦₀ t', f)
  | termₘ_step_switchₘ_f_default :
    ∀ {Γ} (f : Zm μ →₀ termₘ μ Γ ι) (t'_1 t'_2 : termₘ μ Γ ι),
    stabilizing_fun_canonical f →
    stabilizing_fun_default f = Some t'_1 →
    t'_1 ⟶ₘ t'_2 →
    switchₘ f ⟶ₘ switchₘ (_ ↦₀ t'_2, f)
  | termₘ_step_switchₘ :
    ∀ {Γ} n (f : Zm μ →₀ termₘ μ Γ ι),
    switchₘ f $ₘ kₘ n ⟶ₘ f n
  | termₘ_step_fixₘ :
    ∀ {Γ} α (s : termₘ μ Γ (α ⇒ α)),
    fixₘ α $ₘ s ⟶ₘ s $ₘ (fixₘ α $ₘ s)
  | termₘ_step_Appₘ_s' :
    ∀ {Γ α β} (s'_1 s'_2 : termₘ μ Γ (α ⇒ β)) (t' : termₘ μ Γ α),
    s'_1 ⟶ₘ s'_2 →
    s'_1 $ₘ t' ⟶ₘ s'_2 $ₘ t'
  | termₘ_step_Appₘ_t' :
    ∀ {Γ α β} (s' : termₘ μ Γ (α ⇒ β)) (t'_1 t'_2 : termₘ μ Γ α),
    t'_1 ⟶ₘ t'_2 →
    s' $ₘ t'_1 ⟶ₘ s' $ₘ t'_2
  | termₘ_step_Absₘ_s' :
    ∀ {Γ α} β (s'_1 s'_2 : termₘ μ (β :: Γ) α),
    s'_1 ⟶ₘ s'_2 →
    λₘ: β, s'_1 ⟶ₘ λₘ: β, s'_2
  | termₘ_step_Absₘ :
    ∀ {Γ α} β (s' : termₘ μ (β :: Γ) α) (t : termₘ μ Γ β),
    (λₘ: β, s') $ₘ t ⟶ₘ substitutionₘ_inst (substitutionₘ_cons β t (substitutionₘ_id Γ)) s'
  where "s_1 ⟶ₘ s_2" := (termₘ_step s_1 s_2).

Definition termₘ_red {μ Γ α} := t_closure_t (@termₘ_step μ Γ α).

Notation "s_1  ⟶⁺ₘ  s_2" := (termₘ_red s_1 s_2) (at level 70).

Inductive termₘ_normal {μ Γ} : ∀ {α}, termₘ μ Γ α → Type :=
  | termₘ_normal_of_termₘ_neutral :
    ∀ {α} (s : termₘ μ Γ α),
    termₘ_neutral s →
    termₘ_normal s
  | termₘ_normal_kₘ :
    ∀ n,
    termₘ_normal (kₘ n)
  | termₘ_normal_Pₘ :
    termₘ_normal Pₘ
  | termₘ_normal_Sₘ :
    termₘ_normal Sₘ
  | termₘ_normal_switchₘ :
    ∀ (f : Zm μ →₀ termₘ μ Γ ι),
    stabilizing_fun_canonical f →
    (∀ n, termₘ_normal (f n)) →
    termₘ_normal (switchₘ f)
  | termₘ_normal_fixₘ :
    ∀ α,
    termₘ_normal (fixₘ α)
  | termₘ_normal_Absₘ :
    ∀ {α} β (s' : termₘ μ (β :: Γ) α),
    termₘ_normal s' →
    termₘ_normal (λₘ: β, s')
with termₘ_neutral {μ Γ} : ∀ {α}, termₘ μ Γ α → Type :=
  | termₘ_neutral_Pₘ :
    ∀ (s : termₘ μ Γ ι),
    termₘ_neutral s →
    termₘ_neutral (Pₘ $ₘ s)
  | termₘ_neutral_Sₘ :
    ∀ (s : termₘ μ Γ ι),
    termₘ_neutral s →
    termₘ_neutral (Sₘ $ₘ s)
  | termₘ_neutral_switchₘ :
    ∀ (f : Zm μ →₀ termₘ μ Γ ι) (s : termₘ μ Γ ι),
    stabilizing_fun_canonical f →
    (∀ n, termₘ_normal (f n)) →
    termₘ_neutral s →
    termₘ_neutral (switchₘ f $ₘ s)
  | termₘ_neutral_Varₘ :
    ∀ {α} (mi : mem_index α Γ),
    termₘ_neutral (Varₘ α mi)
  | termₘ_neutral_Appₘ :
    ∀ {α β} (s' : termₘ μ Γ (α ⇒ β)) (t' : termₘ μ Γ α),
    termₘ_neutral s' →
    termₘ_normal t' →
    termₘ_neutral (s' $ₘ t').

Scheme termₘ_normal_mutind := Induction for termₘ_normal Sort Prop
with termₘ_neutral_mutind := Induction for termₘ_neutral Sort Prop.

Scheme termₘ_normal_mutrect := Induction for termₘ_normal Sort Type
with termₘ_neutral_mutrect := Induction for termₘ_neutral Sort Type.

Definition termₘ_normal_mutrec μ (P_normal : ∀ Γ α (s : termₘ μ Γ α), termₘ_normal s → Set) (P_neutral : ∀ Γ α (s : termₘ μ Γ α), termₘ_neutral s → Set) := termₘ_normal_mutrect μ P_normal P_neutral.
Definition termₘ_neutral_mutrec μ (P_normal : ∀ Γ α (s : termₘ μ Γ α), termₘ_normal s → Set) (P_neutral : ∀ Γ α (s : termₘ μ Γ α), termₘ_neutral s → Set) := termₘ_neutral_mutrect μ P_normal P_neutral.

Definition termₘ_progress {μ Γ α} (s : termₘ μ Γ α) : {t & s ⟶ₘ t} + termₘ_normal s.
Proof.
  induction s as [Γ n | Γ | Γ | Γ f_1 IH_f IH_f_default | Γ α | Γ α mi | Γ α β s'_1 IH_s' t'_1 IH_t' | Γ α β s'_1 IH_s'].
  - right. apply termₘ_normal_kₘ.
  - right. apply termₘ_normal_Pₘ.
  - right. apply termₘ_normal_Sₘ.
  - destruct (dec_stabilizing_fun_canonical f_1) as [canonical_f_1 | canonical_f_1].
    + assert (H_f : {n & {s'_2 & f_1 n ⟶ₘ s'_2}} + (∀ n, mem_index n (stabilizing_fun_keys f_1) → termₘ_normal (f_1 n))). {
        clear s'_1 IH_f_default IH_s' canonical_f_1. generalize (stabilizing_fun_keys f_1); intros f_keys. induction f_keys as [| n f_keys' IH_f_keys].
        - right. intros n H. inversion H.
        - destruct (IH_f n) as [H_f_n | H_f_n] > [| destruct IH_f_keys as [(m & IH_f_keys) | IH_f_keys]].
          + left. exists n. auto.
          + left. exists m. auto.
          + right. intros m mi. inversion mi; auto.
      }
      remember (stabilizing_fun_default f_1) as f_1_default eqn:H_f_1_default; symmetry in H_f_1_default.
      destruct H_f as [(n & s'_2 & H_f_n) | H_f_n] > [| destruct f_1_default as [t'_1 |] > [destruct IH_f_default as [(s'_2 & H_f_default) | H_f_default] |]].
      * left. exists (switchₘ (n ↦₀ s'_2, f_1)). apply termₘ_step_switchₘ_f_n; auto.
      * left. exists (switchₘ (_ ↦₀ s'_2, f_1)). apply termₘ_step_switchₘ_f_default with t'_1; auto.
      * right. apply termₘ_normal_switchₘ > [auto |]. intros n.
        unfold stabilizing_fun_canonical in canonical_f_1. rewrite H_f_1_default in canonical_f_1. destruct canonical_f_1 as (_ & _ & canonical_f_1).
        destruct (dec_eq_list_In n (stabilizing_fun_keys f_1)) as [mi | H_n].
        -- apply H_f_n, mi.
        -- specialize (canonical_f_1 n). destruct (f_1 n == t'_1) as [-> | H_f_1_n] > [| ltac1:(intuition auto)]. auto.
      * right. apply termₘ_normal_switchₘ > [auto |]. intros n.
        unfold stabilizing_fun_canonical in canonical_f_1. rewrite H_f_1_default in canonical_f_1. destruct canonical_f_1 as (_ & _ & canonical_f_1).
        destruct (dec_eq_list_In n (stabilizing_fun_keys f_1)) as [mi | H_n].
        -- apply H_f_n, mi.
        -- specialize (canonical_f_1 n). exfalso. auto.
    + left. exists (switchₘ (stabilizing_fun_canonize f_1)). apply termₘ_step_switchₘ_f; auto.
  - right. apply termₘ_normal_fixₘ.
  - right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Varₘ.
  - ltac1:(dependent elimination s'_1 as [@Pₘ Γ | @Sₘ Γ | @switchₘ Γ s'_f | @fixₘ Γ s'_α | @Varₘ Γ s'_α s'_mi | @Appₘ Γ s'_α s'_β s'_s' s'_t' | @Absₘ Γ s'_α s'_β s'_s']).
    + destruct IH_s' as [(s'_2 & H_s') | H_s'] > [| destruct IH_t' as [(t'_2 & H_t') | H_t']].
      * left. exists (s'_2 $ₘ t'_1). apply termₘ_step_Appₘ_s'; auto.
      * left. exists (Pₘ $ₘ t'_2). apply termₘ_step_Appₘ_t'; auto.
      * ltac1:(dependent elimination H_t' as [termₘ_normal_of_termₘ_neutral t'_1 H_t' | termₘ_normal_kₘ n]).
        -- right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Pₘ; auto.
        -- left. exists (kₘ (Zm_pred n)). apply termₘ_step_Pₘ.
    + destruct IH_s' as [(s'_2 & H_s') | H_s'] > [| destruct IH_t' as [(t'_2 & H_t') | H_t']].
      * left. exists (s'_2 $ₘ t'_1). apply termₘ_step_Appₘ_s'; auto.
      * left. exists (Sₘ $ₘ t'_2). apply termₘ_step_Appₘ_t'; auto.
      * ltac1:(dependent elimination H_t' as [termₘ_normal_of_termₘ_neutral t'_1 H_t' | termₘ_normal_kₘ n]).
        -- right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Sₘ; auto.
        -- left. exists (kₘ (Zm_succ n)). apply termₘ_step_Sₘ.
    + destruct IH_t' as [(t'_2 & H_t') | H_t'].
      * left. exists (switchₘ s'_f $ₘ t'_2). apply termₘ_step_Appₘ_t'; auto.
      * ltac1:(dependent elimination H_t' as [termₘ_normal_of_termₘ_neutral t'_1 H_t' | termₘ_normal_kₘ n]).
        -- destruct IH_s' as [(s'_2 & H_s') | H_s'].
           ++ left. exists (s'_2 $ₘ t'_1). apply termₘ_step_Appₘ_s'; auto.
           ++ ltac1:(dependent elimination H_s' as [termₘ_normal_switchₘ s'_f canonical_s'_f H_s'_f]).
              right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_switchₘ; auto.
        -- left. exists (s'_f n). apply termₘ_step_switchₘ.
    + left. exists (t'_1 $ₘ (fixₘ s'_α $ₘ t'_1)). apply termₘ_step_fixₘ.
    + destruct IH_s' as [(s'_2 & H_s') | H_s'] > [| destruct IH_t' as [(t'_2 & H_t') | H_t']].
      * left. exists (s'_2 $ₘ t'_1). apply termₘ_step_Appₘ_s'; auto.
      * left. exists (Varₘ (α ⇒ β) s'_mi $ₘ t'_2). apply termₘ_step_Appₘ_t'; auto.
      * ltac1:(dependent elimination H_s' as [termₘ_normal_of_termₘ_neutral _ H_s']).
        right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Appₘ; auto.
    + destruct IH_s' as [(s'_2 & H_s') | H_s'] > [| destruct IH_t' as [(t'_2 & H_t') | H_t']].
      * left. exists (s'_2 $ₘ t'_1). apply termₘ_step_Appₘ_s'; auto.
      * left. exists (s'_s' $ₘ s'_t' $ₘ t'_2). apply termₘ_step_Appₘ_t'; auto.
      * ltac1:(dependent elimination H_s' as [termₘ_normal_of_termₘ_neutral _ H_s']).
        right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Appₘ; auto.
    + left. exists (substitutionₘ_inst (substitutionₘ_cons s'_β t'_1 (substitutionₘ_id Γ)) s'_s'). apply termₘ_step_Absₘ.
  - destruct IH_s' as [(s'_2 & H_s') | H_s'].
    + left. exists (λₘ: β, s'_2). apply termₘ_step_Absₘ_s'; auto.
    + right. apply termₘ_normal_Absₘ; auto.
Defined.

Lemma not_termₘ_normal_and_termₘ_step {μ Γ α} :
  ∀ (s t : termₘ μ Γ α),
  termₘ_normal s →
  s ⟶ₘ t →
  False.
Proof.
  intros s t H_normal_s H_step. revert t H_step; apply (termₘ_normal_mutind μ (λ Γ α s H_normal_s, ∀ t, s ⟶ₘ t → False) (λ Γ α s H_neutral_s, ∀ t, s ⟶ₘ t → False)); try (apply H_normal_s); clear Γ α s H_normal_s.
  - intros Γ α s H_neutral_s IH_s t H_step. apply (IH_s t); auto.
  - intros Γ n t H_step. inversion H_step.
  - intros Γ t H_step. inversion H_step.
  - intros Γ t H_step. inversion H_step.
  - intros Γ s_f stabilizing_s_f H_normal_s_f_n IH_s_f_n t H_step.
    ltac1:(dependent elimination H_step as [@termₘ_step_switchₘ_f Γ s_f H_s_f | @termₘ_step_switchₘ_f_n Γ s_f n s_t' H_s_f H_step | @termₘ_step_switchₘ_f_default Γ s_f s_t'_1 s_t'_2 H_s_f H_t'_1 H_step]).
    + auto.
    + apply (IH_s_f_n n s_t'); auto.
    + unfold stabilizing_fun_canonical in H_s_f. rewrite H_t'_1 in H_s_f. simpl in H_s_f. destruct (@dec_finite (Zm μ)) as [finite_A | infinite_A].
      * apply dec_finite_Zm.
      * ltac1:(intuition auto).
      * destruct H_s_f as (_ & _ & H_s_f). destruct (infinite_A (stabilizing_fun_keys s_f)) as (n & H_n).
        specialize (H_s_f n). apply (IH_s_f_n n s_t'_2). ltac1:(replace (s_f n) with s_t'_1 by (apply NNPP; intuition auto)). auto.
  - intros Γ α t H_step. inversion H_step.
  - intros Γ α β s_s' H_normal_s_s' IH_s_s' t H_step.
    ltac1:(dependent elimination H_step as [@termₘ_step_Absₘ_s' Γ α β s_s' t_s' H_step]). apply (IH_s_s' t_s'); auto.
  - intros Γ s_s H_neutral_s_s IH_s_s t H_step.
    remember Pₘ as s_u eqn:H_s_u; ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_s' Γ _ _ s_u t_u s_s H_step | @termₘ_step_Appₘ_t' Γ _ _ s_u s_s t_s H_step]); subst s_u.
    + inversion H_step.
    + apply (IH_s_s t_s); auto.
  - intros Γ s_s H_neutral_s_s IH_s_s t H_step.
    remember Sₘ as s_u eqn:H_s_u; ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_s' Γ _ _ s_u t_u s_s H_step | @termₘ_step_Appₘ_t' Γ _ _ s_u s_s t_s H_step]); subst s_u.
    + inversion H_step.
    + apply (IH_s_s t_s); auto.
  - intros Γ s_f s_s stabilizing_f_n H_normal_s_f_n IH_s_f_n H_neutral_s_s IH_s_s t H_step.
    remember (switchₘ s_f) as s_u eqn:H_s_u; ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_s' Γ _ _ s_u t_u s_s H_step | @termₘ_step_Appₘ_t' Γ _ _ s_u s_s t_s H_step]); subst s_u.
    + ltac1:(dependent elimination H_step as [@termₘ_step_switchₘ_f Γ s_f H_s_f | @termₘ_step_switchₘ_f_n Γ s_f n s_t' H_s_f H_step | @termₘ_step_switchₘ_f_default Γ s_f s_t'_1 s_t'_2 H_s_f H_t'_1 H_step]).
      * auto.
      * apply (IH_s_f_n n s_t'); auto.
      * unfold stabilizing_fun_canonical in H_s_f. rewrite H_t'_1 in H_s_f. simpl in H_s_f. destruct (@dec_finite (Zm μ)) as [finite_A | infinite_A].
        -- apply dec_finite_Zm.
        -- ltac1:(intuition auto).
        -- destruct H_s_f as (_ & _ & H_s_f). destruct (infinite_A (stabilizing_fun_keys s_f)) as (n & H_n).
           specialize (H_s_f n). apply (IH_s_f_n n s_t'_2). ltac1:(replace (s_f n) with s_t'_1 by (apply NNPP; intuition auto)). auto.
    + apply (IH_s_s t_s); auto.
  - intros Γ α mi t H_step. inversion H_step.
  - intros Γ α β s_s' s_t' H_neutral_s_s' IH_s_s' H_normal_s_t' IH_s_t' t H_step.
    ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_s' Γ _ _ s_s' t_s' s_t' H_step | @termₘ_step_Appₘ_t' Γ _ _ s_s' s_t' t_t' H_step]).
    + apply (IH_s_s' t_s'); auto.
    + apply (IH_s_t' t_t'); auto.
Qed.

Fixpoint termₘ_reduce {μ Γ α} (n : nat) (s : termₘ μ Γ α) : option {t : termₘ μ Γ α & (s ⟶⁺ₘ t)}.
Proof.
  destruct n as [| n'].
  - apply None.
  - destruct (termₘ_progress s) as [(t & H_s) | H_s].
    + apply t_closure_t_step in H_s. destruct (termₘ_reduce _ _ _ n' t) as [(u & H_t) |].
      * apply Some. exists u. apply trans_t_closure_t with t; auto.
      * apply Some. exists t. auto.
    + apply None.
Defined.

Definition termₘ_reduce_list {μ Γ α} (n : nat) (s : termₘ μ Γ α) : list (termₘ μ Γ α) :=
  s ::
  match termₘ_reduce n s with
  | None => []
  | Some (existT _ _ H) => list_of_t_closure_t H
  end.

Definition example_plusₘ {μ Γ} : termₘ μ Γ (ι ⇒ ι ⇒ ι) :=
  fixₘ (ι ⇒ ι ⇒ ι) $ₘ (λₘ: ι ⇒ ι ⇒ ι, λₘ: ι, λₘ: ι,
    switchₘ (
      Zm_of_Z 0 ↦₀ Varₘ ι MIO,
      _ ↦₀ Sₘ $ₘ (Varₘ (ι ⇒ ι ⇒ ι) (MIS (MIS MIO)) $ₘ (Pₘ $ₘ Varₘ ι (MIS MIO)) $ₘ (Varₘ ι MIO))
    ) $ₘ Varₘ ι (MIS MIO)
  ).

Definition example_fibonacciₘ {μ Γ} : termₘ μ Γ (ι ⇒ ι) :=
  fixₘ (ι ⇒ ι) $ₘ (λₘ: ι ⇒ ι, λₘ: ι,
    switchₘ (
      Zm_of_Z 0 ↦₀ kₘ (Zm_of_Z 1),
      Zm_of_Z 1 ↦₀ kₘ (Zm_of_Z 1),
      _ ↦₀ example_plusₘ $ₘ (Varₘ (ι ⇒ ι) (MIS MIO) $ₘ (Pₘ $ₘ (Pₘ $ₘ (Varₘ ι MIO)))) $ₘ (Pₘ $ₘ (Varₘ ι MIO))
    ) $ₘ Varₘ ι MIO
  ).

Eval lazy in (List.map rebuild_termₘ (termₘ_reduce_list 5 (@example_fibonacciₘ 0 [] $ₘ (kₘ (Zm_of_Z 3))))).

Eval lazy in option_map (λ s, rebuild_termₘ (projT1 s)) (termₘ_reduce 2 (@example_fibonacciₘ 0 [] $ₘ (kₘ (Zm_of_Z 2)))).

(*
Set Printing Width 120.
Set Printing Depth 10000.
Eval lazy in (List.map rebuild_termₘ (termₘ_reduce_list 100 (@example_fibonacciₘ 0 [] $ₘ (kₘ (Zm_of_Z 3))))).
*)
