From PCF Require Import Tools.
From PCF Require Import Zm.
From PCF Require Import Types.

Unset Elimination Schemes.

Inductive termₘ μ Γ : type → Type :=
  | kₘ : Zm μ → termₘ μ Γ ι
  | Pₘ : termₘ μ Γ (ι ⇒ ι)
  | Sₘ : termₘ μ Γ (ι ⇒ ι)
  | switchₘ : (Zm μ →₀ termₘ μ Γ ι) → termₘ μ Γ (ι ⇒ ι)
  | fixₘ : ∀ α, termₘ μ Γ ((α ⇒ α) ⇒ α)
  | Varₘ : ∀ α, mem_index α Γ → termₘ μ Γ α
  | Appₘ : ∀ α β, termₘ μ Γ (α ⇒ β) → termₘ μ Γ α → termₘ μ Γ β
  | Absₘ : ∀ α β, termₘ μ (β :: Γ) α → termₘ μ Γ (β ⇒ α).
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

Definition termₘ_rect μ (P : ∀ Γ α, termₘ μ Γ α → Type)
  (case_kₘ : ∀ Γ n, P Γ ι (kₘ n))
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (f : Zm μ →₀ termₘ μ Γ ι), (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some f_d => P Γ ι f_d | None => True end → P Γ (ι ⇒ ι) (switchₘ f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (_1 : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) _1 → ∀ _2 : termₘ μ Γ α, P Γ α _2 → P Γ β (_1 $ₘ _2))
  (case_Absₘ : ∀ Γ α β (_1 : termₘ μ (β :: Γ) α), P (β :: Γ) α _1 → P Γ (β ⇒ α) (λₘ: β, _1)) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @kₘ _ _ s_n => case_kₘ Γ s_n
    | @Pₘ _ _ => case_Pₘ Γ
    | @Sₘ _ _ => case_Sₘ Γ
    | @switchₘ _ _ s_f => case_switchₘ Γ s_f (λ n, F Γ ι (s_f n)) (match stabilizing_fun_default s_f as f_default return match f_default with Some s_f_d => P Γ ι s_f_d | None => True end with Some s_f_d => F Γ ι s_f_d | None => I end)
    | @fixₘ _ _ s_α => case_fixₘ Γ s_α
    | @Varₘ _ _ s_α s_mi => case_Varₘ Γ s_α s_mi
    | @Appₘ _ _ s_α s_β s_1 s_2 => case_Appₘ Γ s_α s_β s_1 (F Γ (s_α ⇒ s_β) s_1) s_2 (F Γ s_α s_2)
    | @Absₘ _ _ s_α s_β s_1 => case_Absₘ Γ s_α s_β s_1 (F (s_β :: Γ) s_α s_1)
    end.

Definition termₘ_ind μ (P : ∀ Γ α, termₘ μ Γ α → Prop)
  (case_kₘ : ∀ Γ n, P Γ ι (kₘ n))
  (case_Pₘ : ∀ Γ, P Γ (ι ⇒ ι) Pₘ)
  (case_Sₘ : ∀ Γ, P Γ (ι ⇒ ι) Sₘ)
  (case_switchₘ : ∀ Γ (f : Zm μ →₀ termₘ μ Γ ι), (∀ n, P Γ ι (f n)) → match stabilizing_fun_default f with Some f_d => P Γ ι f_d | None => True end → P Γ (ι ⇒ ι) (switchₘ f))
  (case_fixₘ : ∀ Γ α, P Γ ((α ⇒ α) ⇒ α) (fixₘ α))
  (case_Varₘ : ∀ Γ α (mi : mem_index α Γ), P Γ α (Varₘ α mi))
  (case_Appₘ : ∀ Γ α β (_1 : termₘ μ Γ (α ⇒ β)), P Γ (α ⇒ β) _1 → ∀ _2 : termₘ μ Γ α, P Γ α _2 → P Γ β (_1 $ₘ _2))
  (case_Absₘ : ∀ Γ α β (_1 : termₘ μ (β :: Γ) α), P (β :: Γ) α _1 → P Γ (β ⇒ α) (λₘ: β, _1)) :=
  fix F Γ α (s : termₘ μ Γ α) : P Γ α s :=
    match s with
    | @kₘ _ _ s_n => case_kₘ Γ s_n
    | @Pₘ _ _ => case_Pₘ Γ
    | @Sₘ _ _ => case_Sₘ Γ
    | @switchₘ _ _ s_f => case_switchₘ Γ s_f (λ n, F Γ ι (s_f n)) (match stabilizing_fun_default s_f as f_default return match f_default with Some s_f_d => P Γ ι s_f_d | None => True end with Some s_f_d => F Γ ι s_f_d | None => I end)
    | @fixₘ _ _ s_α => case_fixₘ Γ s_α
    | @Varₘ _ _ s_α s_mi => case_Varₘ Γ s_α s_mi
    | @Appₘ _ _ s_α s_β s_1 s_2 => case_Appₘ Γ s_α s_β s_1 (F Γ (s_α ⇒ s_β) s_1) s_2 (F Γ s_α s_2)
    | @Absₘ _ _ s_α s_β s_1 => case_Absₘ Γ s_α s_β s_1 (F (s_β :: Γ) s_α s_1)
    end.

Definition termₘ_rec μ (P : ∀ Γ α, termₘ μ Γ α → Set) := termₘ_rect μ P.

(* Equations Derive Signature for termₘ. *)

Definition termₘ_sig μ (index : sigma (λ _ : list type, type)) :=
  termₘ μ (pr1 index) (pr2 index).

Definition termₘ_sig_pack μ Γ α (s : termₘ μ Γ α) : sigma (termₘ_sig μ) :=
  {| pr1 := {| pr1 := Γ; pr2 := α |}; pr2 := s |}.

Instance termₘ_Signature μ Γ α : Signature (termₘ μ Γ α) (sigma (λ _ : list type, type)) (termₘ_sig μ) :=
  termₘ_sig_pack μ Γ α.

Equations Derive NoConfusion for termₘ.

Instance arbitrary_termₘ {μ Γ α} : Arbitrary (termₘ μ Γ α).
Proof.
  revert Γ; induction α as [| α_1 IH_α_1 α_2 IH_α_2]; intros Γ.
  - apply (kₘ (Zm_of_Z 0%Z)).
  - apply Absₘ. apply IH_α_2.
Defined.

Instance dec_eq_termₘ {μ Γ α} : EqDec (termₘ μ Γ α) eq.
Proof.
  rewrite dec_eq_def.
  intros s; induction s as [Γ s_n | Γ | Γ | Γ s_f IH_f IH_f_default | Γ s_α | Γ s_α s_mi | Γ s_α s_β s_1 IH_1 s_2 IH_2 | Γ s_α s_β s_1 IH_1]; intros t.
  - ltac1:(dependent elimination t as [@kₘ _ _ t_n | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2]); try (right; congruence).
    destruct (s_n == t_n) as [H_n | H_n]; constructor; congruence.
  - ltac1:(dependent elimination t as [@Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ t_f | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ t_α t_β t_1]); constructor; congruence.
  - ltac1:(dependent elimination t as [@Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ t_f | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ t_α t_β t_1]); constructor; congruence.
  - ltac1:(dependent elimination t as [@Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ t_f | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ t_α t_β t_1]); try (right; congruence).
    ltac1:(pose proof (IH'_f := λ n, IH_f n (t_f n))); clear IH_f.
    assert (H_f_default : {stabilizing_fun_default s_f = stabilizing_fun_default t_f} + {stabilizing_fun_default s_f ≠ stabilizing_fun_default t_f}). {
      remember (stabilizing_fun_default s_f) as s_f_default eqn:H_s_f_default; remember (stabilizing_fun_default t_f) as t_f_default eqn:H_t_f_default. destruct s_f_default as [s_f_d |], t_f_default as [t_f_d |]; try (right; congruence).
      - specialize (IH_f_default t_f_d). destruct IH_f_default; constructor; congruence.
      - left; reflexivity.
    }
    ltac1:(pose proof (H_f := dec_eq_stabilizing_fun_minimal s_f t_f IH'_f H_f_default)).
    destruct H_f as [H_f | H_f]; constructor; congruence.
  - ltac1:(dependent elimination t as [@fixₘ _ _ t_α | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ α_2 β_2 s'_2]); constructor; congruence.
  - ltac1:(dependent elimination t as [@kₘ _ _ t_n | @Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ t_f | @fixₘ _ _ t_α | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ t_α t_β t_1]); try (right; congruence).
    destruct (s_mi == t_mi : {_ = _} + {_ ≠ _}) as [-> | H_mi]; constructor; congruence.
  - ltac1:(dependent elimination t as [@kₘ _ _ t_n | @Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ t_f | @fixₘ _ _ t_α | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ t_α t_β t_1]); try (right; congruence).
    destruct (s_α == t_α) as [-> | H_α]; try (right; congruence). specialize (IH_1 t_1); specialize (IH_2 t_2).
    destruct IH_1 as [IH_1 | IH_1] > [destruct IH_2 as [IH_2 | IH_2] |].
    + left; congruence.
    + right. intros H. apply IH_2. injection H as _ H. apply inj_right_pair in H. auto.
    + right. intros H. apply IH_1. injection H as H _. do 2 (apply inj_right_pair in H). auto.
  - ltac1:(dependent elimination t as [@Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ t_f | @fixₘ _ _ t_α | @Varₘ _ _ t_α t_mi | @Appₘ _ _ t_α t_β t_1 t_2 | @Absₘ _ _ t_α t_β t_1]); try (right; congruence).
    specialize (IH_1 t_1). destruct IH_1 as [IH_1 | IH_1]; constructor; congruence.
Defined.

Inductive termₘ_direct_subterm {μ} : ∀ {s_Γ s_α t_Γ t_α}, termₘ μ s_Γ s_α → termₘ μ t_Γ t_α → Prop :=
  | termₘ_direct_subterm_switchₘ_f :
    ∀ {t_Γ} (t_f : Zm μ →₀ termₘ μ t_Γ ι) n,
    termₘ_direct_subterm (t_f n) (switchₘ t_f)
  | termₘ_direct_subterm_switchₘ_f_d :
    ∀ {t_Γ} (t_f : Zm μ →₀ termₘ μ t_Γ ι) (t_f_d : termₘ μ t_Γ ι),
    stabilizing_fun_default t_f = Some t_f_d →
    termₘ_direct_subterm t_f_d (switchₘ t_f)
  | termₘ_direct_subterm_Appₘ_1 :
    ∀ {t_Γ t_α t_β} (t_1 : termₘ μ t_Γ (t_α ⇒ t_β)) (t_2 : termₘ μ t_Γ t_α),
    termₘ_direct_subterm t_1 (t_1 $ₘ t_2)
  | termₘ_direct_subterm_Appₘ_2 :
    ∀ {t_Γ t_α t_β} (t_1 : termₘ μ t_Γ (t_α ⇒ t_β)) (t_2 : termₘ μ t_Γ t_α),
    termₘ_direct_subterm t_2 (t_1 $ₘ t_2)
  | termₘ_direct_subterm_Absₘ_1 :
    ∀ {t_Γ t_α} t_β (t_2 : termₘ μ (t_β :: t_Γ) t_α),
    termₘ_direct_subterm t_2 (λₘ: t_β, t_2).

Hint Resolve termₘ_direct_subterm_switchₘ_f : subterm_relation.
Hint Resolve termₘ_direct_subterm_switchₘ_f_d : subterm_relation.
Hint Resolve termₘ_direct_subterm_Appₘ_1 : subterm_relation.
Hint Resolve termₘ_direct_subterm_Appₘ_2 : subterm_relation.
Hint Resolve termₘ_direct_subterm_Absₘ_1 : subterm_relation.

Definition termₘ_subterm {μ} :=
  Relation_Operators.clos_trans
    (sigma (λ index : sigma (λ _ : list type, type), termₘ μ (pr1 index) (pr2 index)))
    (λ s t, termₘ_direct_subterm (pr2 s) (pr2 t)).

Hint Unfold termₘ_subterm : subterm_relation.

Instance well_founded_termₘ_subterm {μ} : WellFounded (@termₘ_subterm μ).
Proof.
  apply Transitive_Closure.wf_clos_trans. intros [[t_Γ t_α] t]; simpl in t.
  induction t as [t_Γ t_n | t_Γ | t_Γ | t_Γ t_f IH_f IH_f_default | t_Γ t_α | t_Γ t_α t_mi | t_Γ t_α t_β t_1 IH_1 t_2 IH_2 | Γ t_α t_β t_1 IH_1]; apply Acc_intro; simpl; intros [[s_Γ s_α] s] H; simpl in s |- *;
  try (solve [ltac1:(dependent elimination s as [@kₘ _ _ s_n | @Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ s_f | @fixₘ _ _ s_α | @Varₘ _ _ s_α s_mi | @Appₘ _ _ s_α_ s_β s_1 s_2 | @Absₘ _ _ s_α s_β s_1]); inversion H]); try (solve [ltac1:(dependent elimination H); auto]).
  ltac1:(dependent elimination H as [@termₘ_direct_subterm_switchₘ_f t_Γ t_f n | @termₘ_direct_subterm_switchₘ_f_d _ t_Γ t_f t_f_d H_t_f_default]).
  - auto.
  - rewrite H_t_f_default in IH_f_default. auto.
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
    | switchₘ s_f =>
      switchₘ
        (stabilizing_fun_rebuild_erased
          (stabilizing_fun_map_minimal
            (λ n, rebuild_termₘ (s_f n))
            (match stabilizing_fun_default s_f as s_f_default return stabilizing_fun_default s_f = s_f_default → option (termₘ μ Γ ι) with
            | Some s_f_d => λ s_f_default, Some (rebuild_termₘ s_f_d)
            | None => λ _, None
            end eq_refl)
            s_f
            _)
        )
    | fixₘ s_α => fixₘ s_α
    | Varₘ s_α s_mi => Varₘ s_α s_mi
    | s_1 $ₘ s_2 => (rebuild_termₘ s_1) $ₘ (rebuild_termₘ s_2)
    | λₘ: s_β, s_1 => λₘ: s_β, rebuild_termₘ s_1.
  Next Obligation.
    intros Γ f rebuild_termₘ n_1 n_2 H_f_n. simpl.
    generalize (rebuild_termₘ_obligations_obligation_1 Γ f n_1) as H_1, (rebuild_termₘ_obligations_obligation_1 Γ f n_2) as H_2; intros H_1 H_2.
    destruct H_f_n. f_equal; apply proof_irrelevance.
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
    | σ, switchₘ s_f =>
      switchₘ
        (stabilizing_fun_map_minimal
          (λ n, renaming_inst_termₘ σ (s_f n))
          (match stabilizing_fun_default s_f as s_f_default return stabilizing_fun_default s_f = s_f_default → option (termₘ μ Γ ι) with
          | Some s_f_d => λ s_f_default, Some (renaming_inst_termₘ σ s_f_d)
          | None => λ _, None
          end eq_refl)
          s_f
          _)
    | σ, fixₘ s_α => fixₘ s_α
    | σ, Varₘ s_α s_mi => Varₘ s_α (σ s_α s_mi)
    | σ, s_1 $ₘ s_2 => (renaming_inst_termₘ σ s_1) $ₘ (renaming_inst_termₘ σ s_2)
    | σ, λₘ: s_β, s_1 => λₘ: s_β, renaming_inst_termₘ (renaming_up s_β σ) s_1.
  Next Obligation.
    intros Γ Δ σ f renaming_inst_termₘ n_1 n_2 H_f_n. simpl.
    generalize (renaming_inst_termₘ_obligations_obligation_1 Δ f n_1) as H_1, (renaming_inst_termₘ_obligations_obligation_1 Δ f n_2) as H_2; intros H_1 H_2.
    destruct H_f_n. f_equal; apply proof_irrelevance.
  Defined.
End renaming_inst_termₘ.

Lemma renaming_inst_termₘ_equation_4' {μ : nat} :
  ∀ Γ Δ (σ : renaming Γ Δ) (s_f : Zm μ →₀ termₘ μ Δ ι),
  renaming_inst_termₘ σ (switchₘ s_f) = switchₘ (stabilizing_fun_map (renaming_inst_termₘ σ) s_f).
Proof.
  intros Γ Δ σ s_f. rewrite renaming_inst_termₘ_equation_4. unfold stabilizing_fun_map. do 2 f_equal.
  - destruct (stabilizing_fun_default s_f); reflexivity.
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
    | σ, switchₘ s_f =>
      switchₘ
        (stabilizing_fun_map_minimal
          (λ n, substitutionₘ_inst σ (s_f n))
          (match stabilizing_fun_default s_f as s_f_default return stabilizing_fun_default s_f = s_f_default → option (termₘ μ Γ ι) with
          | Some s_f_d => λ s_f_default, Some (substitutionₘ_inst σ s_f_d)
          | None => λ _, None
          end eq_refl)
          s_f
          _)
    | σ, fixₘ s_α => fixₘ s_α
    | σ, Varₘ s_α s_mi => σ s_α s_mi
    | σ, s_1 $ₘ s_2 => (substitutionₘ_inst σ s_1) $ₘ (substitutionₘ_inst σ s_2)
    | σ, λₘ: s_β, s_1 => λₘ: s_β, substitutionₘ_inst (substitutionₘ_up s_β σ) s_1.
  Next Obligation.
    intros Γ Δ σ f substitutionₘ_inst a_1 a_2 H_f_a. simpl.
    generalize (substitutionₘ_inst_obligations_obligation_1 Δ f a_1) as H_1, (substitutionₘ_inst_obligations_obligation_1 Δ f a_2) as H_2; intros H_1 H_2.
    destruct H_f_a. f_equal; apply proof_irrelevance.
  Defined.
End substitutionₘ_inst.

Lemma substitutionₘ_inst_equation_4' {μ : nat} :
  ∀ Γ Δ (σ : substitutionₘ μ Γ Δ) (s_f : Zm μ →₀ termₘ μ Δ ι),
  substitutionₘ_inst σ (switchₘ s_f) = switchₘ  (stabilizing_fun_map (substitutionₘ_inst σ) s_f).
Proof.
  intros Γ Δ σ s_f. rewrite substitutionₘ_inst_equation_4. unfold stabilizing_fun_map. do 2 f_equal.
  - destruct (stabilizing_fun_default s_f); reflexivity.
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
  intros σ s. revert Γ σ; induction s as [Δ n | Δ | Δ | Δ s_f IH_s_f IH_s_f_default | Δ s_α | Δ s_α s_mi | Δ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Δ α β s_1 IH_s_1]; intros Γ σ; ltac1:(simp renaming_inst_termₘ' substitutionₘ_inst'); try (congruence).
  - f_equal. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_s_f. reflexivity.
    + destruct (stabilizing_fun_default s_f) as [s_f_d |].
      * simpl. rewrite IH_s_f_default. reflexivity.
      * reflexivity.
  - reflexivity.
  - rewrite IH_s_1. rewrite renaming_up_def_termₘ. reflexivity.
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
  ∀ (σ : substitutionₘ μ Γ Δ) s_n,
  substitutionₘ_inst σ (kₘ s_n) = kₘ s_n.
Proof.
  intros σ s_n. ltac1:(simp substitutionₘ_inst'). reflexivity.
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
  ∀ (σ : substitutionₘ μ Γ Δ) (s_f : Zm μ →₀ termₘ μ Δ ι),
  substitutionₘ_inst σ (switchₘ s_f) = switchₘ (stabilizing_fun_map (substitutionₘ_inst σ) s_f).
Proof.
  intros σ s_f. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_fixₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ) s_α,
  substitutionₘ_inst σ (fixₘ s_α) = fixₘ s_α.
Proof.
  intros σ s_α. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_Varₘ {μ Γ Δ} :
  ∀ (σ : substitutionₘ μ Γ Δ) s_α s_mi,
  substitutionₘ_inst σ (Varₘ s_α s_mi) = σ s_α s_mi.
Proof.
  intros σ s_α s_mi. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_Appₘ {μ Γ Δ s_α s_β} :
  ∀ (σ : substitutionₘ μ Γ Δ) (s_1 : termₘ μ Δ (s_α ⇒ s_β)) (s_2 : termₘ μ Δ s_α),
  substitutionₘ_inst σ (s_1 $ₘ s_2) = (substitutionₘ_inst σ s_1) $ₘ (substitutionₘ_inst σ s_2).
Proof.
  intros σ s_1 s_2. ltac1:(simp substitutionₘ_inst'). reflexivity.
Qed.

Lemma substitutionₘ_inst_Absₘ {μ Γ Δ s_α} :
  ∀ (σ : substitutionₘ μ Γ Δ) s_β (s_1 : termₘ μ (s_β :: Δ) s_α),
  substitutionₘ_inst σ (λₘ: s_β, s_1) = λₘ: s_β, substitutionₘ_inst (substitutionₘ_up s_β σ) s_1.
Proof.
  intros σ s_β s_1. ltac1:(simp substitutionₘ_inst'). reflexivity.
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
  induction s as [Γ s_n | Γ | Γ | Γ s_f IH_s_f IH_s_f_default | Γ s_α | Γ s_α s_mi | Γ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Γ s_α s_β s_1 IH_s_1].
  - rewrite substitutionₘ_inst_kₘ. reflexivity.
  - rewrite substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite substitutionₘ_inst_switchₘ. f_equal. apply stabilizing_fun_map_id.
    + intros n. rewrite IH_s_f. reflexivity.
    + destruct (stabilizing_fun_default s_f) as [s_f_d |].
      * simpl. rewrite IH_s_f_default. reflexivity.
      * reflexivity.
  - rewrite substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite substitutionₘ_inst_Varₘ. unfold substitutionₘ_id, substitutionₘ_of_renaming, renaming_id. reflexivity.
  - rewrite substitutionₘ_inst_Appₘ. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite substitutionₘ_inst_Absₘ. rewrite substitutionₘ_up_def, substitutionₘ_comp_substitutionₘ_id_left, substitutionₘ_cons_Varₘ_MIO_substitutionₘ_shift. rewrite IH_s_1. reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_inst_substitutionₘ_of_renaming {μ Γ Δ Θ α} :
  ∀ (τ : renaming Δ Θ) (σ : substitutionₘ μ Γ Δ) (s : termₘ μ Θ α),
  substitutionₘ_inst σ (substitutionₘ_inst (substitutionₘ_of_renaming τ) s) = substitutionₘ_inst (substitutionₘ_comp (substitutionₘ_of_renaming τ) σ) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ s_n | Θ | Θ | Θ s_f IH_s_f IH_s_f_default | Θ s_α | Θ s_α s_mi | Θ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Θ s_α s_β s_1 IH_s_1]; intros Γ Δ τ σ.
  - rewrite ! substitutionₘ_inst_kₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_switchₘ. f_equal. rewrite stabilizing_fun_map_stabilizing_fun_map. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_s_f. reflexivity.
    + destruct (stabilizing_fun_default s_f) as [s_f_d |].
      * simpl. rewrite IH_s_f_default. reflexivity.
      * reflexivity.
  - rewrite ! substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Varₘ. unfold substitutionₘ_comp. reflexivity.
  - rewrite ! substitutionₘ_inst_Appₘ. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite ! substitutionₘ_inst_Absₘ. rewrite (substitutionₘ_up_substitutionₘ_of_renaming s_β τ). rewrite IH_s_1. do 2 f_equal.
    rewrite (substitutionₘ_up_def s_β (substitutionₘ_comp (substitutionₘ_of_renaming τ) σ)), renaming_cons_def_termₘ, substitutionₘ_comp_substitutionₘ_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    rewrite substitutionₘ_up_def. unfold substitutionₘ_comp at 1 3 4, renaming_comp, substitutionₘ_of_renaming. rewrite ! substitutionₘ_inst_Varₘ.
    specialize (substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons s_β (Varₘ s_β MIO) (substitutionₘ_comp σ (substitutionₘ_shift s_β Γ))) as H. specialize (equal_f (equal_f_dep H γ) (τ γ mi)) as H'.
    unfold substitutionₘ_comp at 1 3, substitutionₘ_shift, substitutionₘ_of_renaming at 2 in H'. rewrite substitutionₘ_inst_Varₘ in H'.
    unfold substitutionₘ_shift. rewrite H'. reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_of_renaming_substitutionₘ_inst {μ Γ Δ Θ α} :
  ∀ (τ : substitutionₘ μ Δ Θ) (σ : renaming Γ Δ) (s : termₘ μ Θ α),
  substitutionₘ_inst (substitutionₘ_of_renaming σ) (substitutionₘ_inst τ s) = substitutionₘ_inst (substitutionₘ_comp τ (substitutionₘ_of_renaming σ)) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ s_n | Θ | Θ | Θ s_f IH_s_f IH_s_f_default | Θ s_α | Θ s_α s_mi | Θ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Θ s_α s_β s_1 IH_s_1]; intros Γ Δ τ σ.
  - rewrite ! substitutionₘ_inst_kₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_switchₘ. f_equal. rewrite stabilizing_fun_map_stabilizing_fun_map. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_s_f. reflexivity.
    + destruct (stabilizing_fun_default s_f) as [s_f_d |].
      * simpl. rewrite IH_s_f_default. reflexivity.
      * reflexivity.
  - rewrite ! substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Varₘ. unfold substitutionₘ_comp. reflexivity.
  - rewrite ! substitutionₘ_inst_Appₘ. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite ! substitutionₘ_inst_Absₘ. rewrite (substitutionₘ_up_substitutionₘ_of_renaming s_β σ). rewrite IH_s_1. do 2 f_equal.
    rewrite ! substitutionₘ_up_def, renaming_cons_def_termₘ, substitutionₘ_comp_substitutionₘ_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    unfold substitutionₘ_comp, substitutionₘ_shift. rewrite ! substitutionₘ_inst_substitutionₘ_inst_substitutionₘ_of_renaming.
    specialize (@substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons μ _ _ s_β (Varₘ s_β MIO) (substitutionₘ_of_renaming (renaming_comp σ (renaming_shift s_β Γ)))) as H. unfold substitutionₘ_shift in H. rewrite H.
    rewrite renaming_comp_def_termₘ, substitutionₘ_comp_renaming_def. reflexivity.
Qed.

Lemma substitutionₘ_inst_substitutionₘ_inst {μ Γ Δ Θ α} :
  ∀ (τ : substitutionₘ μ Δ Θ) (σ : substitutionₘ μ Γ Δ) (s : termₘ μ Θ α),
  substitutionₘ_inst σ (substitutionₘ_inst τ s) = substitutionₘ_inst (substitutionₘ_comp τ σ) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ s_n | Θ | Θ | Θ s_f IH_s_f IH_s_f_default | Θ s_α | Θ s_α s_mi | Θ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Θ s_α s_β s_1 IH_s_1]; intros Γ Δ τ σ.
  - rewrite ! substitutionₘ_inst_kₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Pₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Sₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_switchₘ. f_equal. rewrite stabilizing_fun_map_stabilizing_fun_map. apply eq_stabilizing_fun_map.
    + intros n. rewrite IH_s_f. reflexivity.
    + destruct (stabilizing_fun_default s_f) as [s_f_d |].
      * simpl. rewrite IH_s_f_default. reflexivity.
      * reflexivity.
  - rewrite ! substitutionₘ_inst_fixₘ. reflexivity.
  - rewrite ! substitutionₘ_inst_Varₘ. unfold substitutionₘ_comp. reflexivity.
  - rewrite ! substitutionₘ_inst_Appₘ. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite ! substitutionₘ_inst_Absₘ. rewrite IH_s_1. do 2 f_equal.
    rewrite (substitutionₘ_up_def s_β τ), (substitutionₘ_up_def s_β (substitutionₘ_comp τ σ)), substitutionₘ_comp_substitutionₘ_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    unfold substitutionₘ_comp, substitutionₘ_shift.
    rewrite substitutionₘ_inst_substitutionₘ_inst_substitutionₘ_of_renaming, substitutionₘ_inst_substitutionₘ_of_renaming_substitutionₘ_inst, substitutionₘ_up_def.
    specialize (@substitutionₘ_comp_substitutionₘ_shift_substitutionₘ_cons μ _ _ s_β (Varₘ s_β MIO) (substitutionₘ_comp σ (substitutionₘ_shift s_β Γ))) as H. unfold substitutionₘ_shift in H |- *. rewrite H. reflexivity.
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
Hint Rewrite @substitutionₘ_inst_Appₘ : substitutionₘ.
Hint Rewrite @substitutionₘ_inst_Absₘ : substitutionₘ.
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

Inductive termₘ_step {μ Γ} : ∀ {α}, termₘ μ Γ α → termₘ μ Γ α → Type :=
  | termₘ_step_Pₘ :
    ∀ s_n,
    (@Pₘ _ Γ) $ₘ (kₘ s_n) ⟶ₘ kₘ (Zm_pred s_n)
  | termₘ_step_Sₘ :
    ∀ s_n,
    (@Sₘ _ Γ) $ₘ (kₘ s_n) ⟶ₘ kₘ (Zm_succ s_n)
  | termₘ_step_switchₘ_f :
    ∀ (s_f : Zm μ →₀ termₘ μ Γ ι),
    ¬ stabilizing_fun_canonical s_f →
    switchₘ s_f ⟶ₘ switchₘ (stabilizing_fun_canonize s_f)
  | termₘ_step_switchₘ_f_n :
    ∀ (s_f : Zm μ →₀ termₘ μ Γ ι) n (t_f_n : termₘ μ Γ ι),
    stabilizing_fun_canonical s_f →
    s_f n ⟶ₘ t_f_n →
    switchₘ s_f ⟶ₘ switchₘ (n ↦₀ t_f_n, s_f)
  | termₘ_step_switchₘ_f_d :
    ∀ (s_f : Zm μ →₀ termₘ μ Γ ι) (s_f_d t_f_d : termₘ μ Γ ι),
    stabilizing_fun_canonical s_f →
    stabilizing_fun_default s_f = Some s_f_d →
    s_f_d ⟶ₘ t_f_d →
    switchₘ s_f ⟶ₘ switchₘ (_ ↦₀ t_f_d, s_f)
  | termₘ_step_switchₘ :
    ∀ (s_1_f : Zm μ →₀ termₘ μ Γ ι) s_2_n,
    switchₘ s_1_f $ₘ kₘ s_2_n ⟶ₘ s_1_f s_2_n
  | termₘ_step_fixₘ :
    ∀ s_1_α (s_2 : termₘ μ Γ (s_1_α ⇒ s_1_α)),
    fixₘ s_1_α $ₘ s_2 ⟶ₘ s_2 $ₘ (fixₘ s_1_α $ₘ s_2)
  | termₘ_step_Appₘ_1 :
    ∀ {s_α s_β} (s_1 t_1 : termₘ μ Γ (s_α ⇒ s_β)) (s_2 : termₘ μ Γ s_α),
    s_1 ⟶ₘ t_1 →
    s_1 $ₘ s_2 ⟶ₘ t_1 $ₘ s_2
  | termₘ_step_Appₘ_2 :
    ∀ {s_α s_β} (s_1 : termₘ μ Γ (s_α ⇒ s_β)) (s_2 t_2 : termₘ μ Γ s_α),
    s_2 ⟶ₘ t_2 →
    s_1 $ₘ s_2 ⟶ₘ s_1 $ₘ t_2
  | termₘ_step_Absₘ_1 :
    ∀ {s_α} s_β (s_1 t_1 : termₘ μ (s_β :: Γ) s_α),
    s_1 ⟶ₘ t_1 →
    λₘ: s_β, s_1 ⟶ₘ λₘ: s_β, t_1
  | termₘ_step_Absₘ :
    ∀ {s_α} s_β (s_1_1 : termₘ μ (s_β :: Γ) s_α) (s_2 : termₘ μ Γ s_β),
    (λₘ: s_β, s_1_1) $ₘ s_2 ⟶ₘ substitutionₘ_inst (substitutionₘ_cons s_β s_2 (substitutionₘ_id Γ)) s_1_1
  where "s ⟶ₘ t" := (termₘ_step s t).

Notation "s  ⟶+ₘ  t" := (t_closure_t termₘ_step s t) (at level 70).
Notation "s  ⟶*ₘ  t" := (rt_closure_t termₘ_step s t) (at level 70).

Inductive termₘ_normal {μ Γ} : ∀ {α}, termₘ μ Γ α → Type :=
  | termₘ_normal_of_termₘ_neutral :
    ∀ {α} (s : termₘ μ Γ α),
    termₘ_neutral s →
    termₘ_normal s
  | termₘ_normal_kₘ :
    ∀ s_n,
    termₘ_normal (kₘ s_n)
  | termₘ_normal_Pₘ :
    termₘ_normal Pₘ
  | termₘ_normal_Sₘ :
    termₘ_normal Sₘ
  | termₘ_normal_switchₘ :
    ∀ (s_f : Zm μ →₀ termₘ μ Γ ι),
    stabilizing_fun_canonical s_f →
    (∀ n, termₘ_normal (s_f n)) →
    termₘ_normal (switchₘ s_f)
  | termₘ_normal_fixₘ :
    ∀ s_α,
    termₘ_normal (fixₘ s_α)
  | termₘ_normal_Absₘ :
    ∀ {s_α} s_β (s_1 : termₘ μ (s_β :: Γ) s_α),
    termₘ_normal s_1 →
    termₘ_normal (λₘ: s_β, s_1)
with termₘ_neutral {μ Γ} : ∀ {α}, termₘ μ Γ α → Type :=
  | termₘ_neutral_Pₘ :
    ∀ (s_2 : termₘ μ Γ ι),
    termₘ_neutral s_2 →
    termₘ_neutral (Pₘ $ₘ s_2)
  | termₘ_neutral_Sₘ :
    ∀ (s_2 : termₘ μ Γ ι),
    termₘ_neutral s_2 →
    termₘ_neutral (Sₘ $ₘ s_2)
  | termₘ_neutral_switchₘ :
    ∀ (s_1_f : Zm μ →₀ termₘ μ Γ ι) (s_2 : termₘ μ Γ ι),
    stabilizing_fun_canonical s_1_f →
    (∀ n, termₘ_normal (s_1_f n)) →
    termₘ_neutral s_2 →
    termₘ_neutral (switchₘ s_1_f $ₘ s_2)
  | termₘ_neutral_Varₘ :
    ∀ {s_α} (s_mi : mem_index s_α Γ),
    termₘ_neutral (Varₘ s_α s_mi)
  | termₘ_neutral_Appₘ :
    ∀ {s_α s_β} (s_1 : termₘ μ Γ (s_α ⇒ s_β)) (s_2 : termₘ μ Γ s_α),
    termₘ_neutral s_1 →
    termₘ_normal s_2 →
    termₘ_neutral (s_1 $ₘ s_2).

Scheme termₘ_normal_mutind := Induction for termₘ_normal Sort Prop
with termₘ_neutral_mutind := Induction for termₘ_neutral Sort Prop.

Scheme termₘ_normal_mutrect := Induction for termₘ_normal Sort Type
with termₘ_neutral_mutrect := Induction for termₘ_neutral Sort Type.

Definition termₘ_normal_mutrec μ (P_normal : ∀ Γ α (s : termₘ μ Γ α), termₘ_normal s → Set) (P_neutral : ∀ Γ α (s : termₘ μ Γ α), termₘ_neutral s → Set) := termₘ_normal_mutrect μ P_normal P_neutral.
Definition termₘ_neutral_mutrec μ (P_normal : ∀ Γ α (s : termₘ μ Γ α), termₘ_normal s → Set) (P_neutral : ∀ Γ α (s : termₘ μ Γ α), termₘ_neutral s → Set) := termₘ_neutral_mutrect μ P_normal P_neutral.

Definition termₘ_progress {μ Γ α} (s : termₘ μ Γ α) : {t & s ⟶ₘ t} + termₘ_normal s.
Proof.
  induction s as [Γ s_n | Γ | Γ | Γ s_f IH_s_f IH_s_f_default | Γ s_α | Γ s_α s_mi | Γ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Γ s_α s_β s_1 IH_s_1].
  - right. apply termₘ_normal_kₘ.
  - right. apply termₘ_normal_Pₘ.
  - right. apply termₘ_normal_Sₘ.
  - destruct (dec_stabilizing_fun_canonical s_f) as [canonical_s_f | canonical_s_f].
    + assert (H_f : {n & {t_f_n & s_f n ⟶ₘ t_f_n}} + (∀ n, mem_index n (stabilizing_fun_keys s_f) → termₘ_normal (s_f n))). {
        clear IH_s_f_default canonical_s_f. generalize (stabilizing_fun_keys s_f); intros f_keys. induction f_keys as [| n f_keys' IH_s_f_keys].
        - right. intros n H. inversion H.
        - destruct (IH_s_f n) as [H_f_n | H_f_n] > [| destruct IH_s_f_keys as [(m & IH_s_f_keys) | IH_s_f_keys]].
          + left. exists n. auto.
          + left. exists m. auto.
          + right. intros m mi. inversion mi; auto.
      }
      remember (stabilizing_fun_default s_f) as s_f_default eqn:H_s_f_default; symmetry in H_s_f_default.
      destruct H_f as [(n & t_f_n & H_s_f_n) | H_s_f_n] > [| destruct s_f_default as [s_f_d |] > [destruct IH_s_f_default as [(t_f_d & H_s_f_d) | H_s_f_d] |]].
      * left. exists (switchₘ (n ↦₀ t_f_n, s_f)). apply termₘ_step_switchₘ_f_n; auto.
      * left. exists (switchₘ (_ ↦₀ t_f_d, s_f)). apply termₘ_step_switchₘ_f_d with s_f_d; auto.
      * right. apply termₘ_normal_switchₘ > [auto |]. intros n.
        unfold stabilizing_fun_canonical in canonical_s_f. rewrite H_s_f_default in canonical_s_f. destruct canonical_s_f as (_ & _ & canonical_s_f).
        destruct (dec_eq_list_In n (stabilizing_fun_keys s_f)) as [mi | H_n].
        -- apply H_s_f_n, mi.
        -- specialize (canonical_s_f n). destruct (s_f n == s_f_d); ltac1:(intuition congruence).
      * right. apply termₘ_normal_switchₘ > [auto |]. intros n.
        unfold stabilizing_fun_canonical in canonical_s_f. rewrite H_s_f_default in canonical_s_f. destruct canonical_s_f as (_ & _ & canonical_s_f).
        destruct (dec_eq_list_In n (stabilizing_fun_keys s_f)) as [mi | H_n].
        -- apply H_s_f_n, mi.
        -- specialize (canonical_s_f n). exfalso. auto.
    + left. exists (switchₘ (stabilizing_fun_canonize s_f)). apply termₘ_step_switchₘ_f; auto.
  - right. apply termₘ_normal_fixₘ.
  - right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Varₘ.
  - ltac1:(dependent elimination s_1 as [@Pₘ _ _ | @Sₘ _ _ | @switchₘ _ _ s_1_f | @fixₘ _ _ s_1_α | @Varₘ _ _ s_1_α s_1_mi | @Appₘ _ _ s_1_α s_1_β s_1_1 s_1_2 | @Absₘ _ _ s_1_α s_1_β s_1_1]).
    + destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1] > [| destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2]].
      * left. exists (t_1 $ₘ s_2). apply termₘ_step_Appₘ_1; auto.
      * left. exists (Pₘ $ₘ t_2). apply termₘ_step_Appₘ_2; auto.
      * ltac1:(dependent elimination H_s_2 as [termₘ_normal_of_termₘ_neutral s_2 H_s_2 | termₘ_normal_kₘ s_2_n]).
        -- right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Pₘ; auto.
        -- left. exists (kₘ (Zm_pred s_2_n)). apply termₘ_step_Pₘ.
    + destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1] > [| destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2]].
      * left. exists (t_1 $ₘ s_2). apply termₘ_step_Appₘ_1; auto.
      * left. exists (Sₘ $ₘ t_2). apply termₘ_step_Appₘ_2; auto.
      * ltac1:(dependent elimination H_s_2 as [termₘ_normal_of_termₘ_neutral s_2 H_s_2 | termₘ_normal_kₘ s_2_n]).
        -- right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Sₘ; auto.
        -- left. exists (kₘ (Zm_succ s_2_n)). apply termₘ_step_Sₘ.
    + destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2].
      * left. exists (switchₘ s_1_f $ₘ t_2). apply termₘ_step_Appₘ_2; auto.
      * ltac1:(dependent elimination H_s_2 as [termₘ_normal_of_termₘ_neutral s_2 H_s_2 | termₘ_normal_kₘ s_2_n]).
        -- destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1].
           ++ left. exists (t_1 $ₘ s_2). apply termₘ_step_Appₘ_1; auto.
           ++ ltac1:(dependent elimination H_s_1 as [termₘ_normal_switchₘ s_1_f canonical_s_1_f H_1_f_n]).
              right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_switchₘ; auto.
        -- left. exists (s_1_f s_2_n). apply termₘ_step_switchₘ.
    + left. exists (s_2 $ₘ (fixₘ s_1_α $ₘ s_2)). apply termₘ_step_fixₘ.
    + destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1] > [| destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2]].
      * left. exists (t_1 $ₘ s_2). apply termₘ_step_Appₘ_1; auto.
      * left. exists (Varₘ (s_α ⇒ s_β) s_1_mi $ₘ t_2). apply termₘ_step_Appₘ_2; auto.
      * ltac1:(dependent elimination H_s_1 as [termₘ_normal_of_termₘ_neutral s_1 H_s_1]).
        right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Appₘ; auto.
    + destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1] > [| destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2]].
      * left. exists (t_1 $ₘ s_2). apply termₘ_step_Appₘ_1; auto.
      * left. exists (s_1_1 $ₘ s_1_2 $ₘ t_2). apply termₘ_step_Appₘ_2; auto.
      * ltac1:(dependent elimination H_s_1 as [termₘ_normal_of_termₘ_neutral s_1 H_s_1]).
        right. apply termₘ_normal_of_termₘ_neutral, termₘ_neutral_Appₘ; auto.
    + left. exists (substitutionₘ_inst (substitutionₘ_cons s_1_β s_2 (substitutionₘ_id Γ)) s_1_1). apply termₘ_step_Absₘ.
  - destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1].
    + left. exists (λₘ: s_β, t_1). apply termₘ_step_Absₘ_1; auto.
    + right. apply termₘ_normal_Absₘ; auto.
Defined.

Lemma not_termₘ_normal_and_termₘ_step {μ Γ α} :
  ∀ (s t : termₘ μ Γ α),
  termₘ_normal s →
  s ⟶ₘ t →
  False.
Proof.
  intros s t H_normal H_step. revert t H_step; apply (termₘ_normal_mutind μ (λ Γ α s H_normal, ∀ t, s ⟶ₘ t → False) (λ Γ α s H_neutral, ∀ t, s ⟶ₘ t → False)); try (apply H_normal); clear Γ α s H_normal.
  - intros Γ α s H_neutral_s IH_s t H_step. apply (IH_s t); auto.
  - intros Γ s_n t H_step. inversion H_step.
  - intros Γ t H_step. inversion H_step.
  - intros Γ t H_step. inversion H_step.
  - intros Γ s_f stabilizing_s_f H_normal_f_n IH_f_n t H_step.
    ltac1:(dependent elimination H_step as [@termₘ_step_switchₘ_f _ _ s_f H_s_f | @termₘ_step_switchₘ_f_n _ _ s_f n t_f_n H_s_f H_step | @termₘ_step_switchₘ_f_d _ _ s_f s_f_d t_f_d H_s_f H_s_f_default H_step]).
    + auto.
    + apply (IH_f_n n t_f_n); auto.
    + unfold stabilizing_fun_canonical in H_s_f. rewrite H_s_f_default in H_s_f. destruct (@dec_finite (Zm μ)) as [finite_A | infinite_A].
      * apply dec_finite_Zm.
      * ltac1:(intuition auto).
      * destruct H_s_f as (_ & _ & H_s_f). destruct (infinite_A (stabilizing_fun_keys s_f)) as (n & H_n).
        specialize (H_s_f n). apply (IH_f_n n t_f_d). ltac1:(replace (s_f n) with s_f_d by (apply NNPP; intuition auto)). auto.
  - intros Γ s_α t H_step. inversion H_step.
  - intros Γ s_α s_β s_1 H_normal_s_1 IH_s_1 t H_step.
    ltac1:(dependent elimination H_step as [@termₘ_step_Absₘ_1 _ _ s_α s_β s_1 t_1 H_step]). apply (IH_s_1 t_1); auto.
  - intros Γ s_2 H_neutral_s_2 IH_s_2 t H_step.
    remember Pₘ as s_1 eqn:H_s_1; ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_1 _ _ _ _ s_1 t_1 s_2 H_step | @termₘ_step_Appₘ_2 _ _ _ _ s_1 s_2 t_2 H_step]); subst s_1.
    + inversion H_step.
    + apply (IH_s_2 t_2); auto.
  - intros Γ s_2 H_neutral_s_2 IH_s_2 t H_step.
    remember Sₘ as s_1 eqn:H_s_1; ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_1 _ _ _ _ s_1 t_1 s_2 H_step | @termₘ_step_Appₘ_2 _ _ _ _ s_1 s_2 t_2 H_step]); subst s_1.
    + inversion H_step.
    + apply (IH_s_2 t_2); auto.
  - intros Γ s_1_f s_2 stabilizing_s_1_f_n H_normal_s_1_f_n IH_s_1_f_n H_neutral_s_2 IH_s_2 t H_step.
    remember (switchₘ s_1_f) as s_1 eqn:H_s_1; ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_1 _ _ _ _ s_1 t_1 s_2 H_step | @termₘ_step_Appₘ_2 _ _ _ _ s_1 s_2 t_2 H_step]); subst s_1.
    + ltac1:(dependent elimination H_step as [@termₘ_step_switchₘ_f _ _ s_1_f H_s_1_f | @termₘ_step_switchₘ_f_n _ _ s_1_f n t_1_f_n H_s_1_f H_step | @termₘ_step_switchₘ_f_d _ _ s_1_f s_1_f_d t_1_f_d H_s_f H_s_1_f_default H_step]).
      * auto.
      * apply (IH_s_1_f_n n t_1_f_n); auto.
      * unfold stabilizing_fun_canonical in H_s_f. rewrite H_s_1_f_default in H_s_f. destruct (@dec_finite (Zm μ)) as [finite_A | infinite_A].
        -- apply dec_finite_Zm.
        -- ltac1:(intuition auto).
        -- destruct H_s_f as (_ & _ & H_s_f). destruct (infinite_A (stabilizing_fun_keys s_1_f)) as (n & H_n).
           specialize (H_s_f n). apply (IH_s_1_f_n n t_1_f_d). ltac1:(replace (s_1_f n) with s_1_f_d by (apply NNPP; intuition auto)). auto.
    + apply (IH_s_2 t_2); auto.
  - intros Γ s_α s_mi t H_step. inversion H_step.
  - intros Γ s_α s_β s_1 s_2 H_neutral_s_1 IH_s_1 H_normal_s_2 IH_s_2 t H_step.
    ltac1:(dependent elimination H_step as [@termₘ_step_Appₘ_1 _ _ _ _ s_1 t_1 s_2 H_step | @termₘ_step_Appₘ_2 _ _ _ _ s_1 s_2 t_2 H_step]).
    + apply (IH_s_1 t_1); auto.
    + apply (IH_s_2 t_2); auto.
Qed.

Fixpoint termₘ_reduce {μ Γ α} (n : nat) (s : termₘ μ Γ α) : {t : termₘ μ Γ α & s ⟶*ₘ t}.
Proof.
  destruct n as [| n'].
  - exists s. apply refl_rt_closure_t.
  - destruct (termₘ_progress s) as [(t & H_s) | H_s].
    + apply rt_closure_t_step in H_s. destruct (termₘ_reduce _ _ _ n' t) as (u & H_t).
      exists u. apply trans_rt_closure_t with t; auto.
    + exists s. apply refl_rt_closure_t.
Defined.

Definition termₘ_reduce_list {μ Γ α} (n : nat) (s : termₘ μ Γ α) : list (termₘ μ Γ α) :=
  let '(existT _ _ H) := termₘ_reduce n s in
  list_of_rt_closure_t H.

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

Eval lazy in List.map rebuild_termₘ (termₘ_reduce_list 5 (@example_fibonacciₘ 0 [] $ₘ (kₘ (Zm_of_Z 3)))).

Eval lazy in rebuild_termₘ (projT1 (termₘ_reduce 2 (@example_fibonacciₘ 0 [] $ₘ (kₘ (Zm_of_Z 2))))).

(*
Set Printing Width 120.
Set Printing Depth 10000.
Eval lazy in (List.map rebuild_termₘ (termₘ_reduce_list 100 (@example_fibonacciₘ 0 [] $ₘ (kₘ (Zm_of_Z 3))))).
*)
