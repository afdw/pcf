From PCF Require Import Tools.
From PCF Require Import Zm.
From PCF Require Import Types.
(* From PCF Require Import PCFm. *)

Inductive term₁ Γ : type → Type :=
  | k₁ : bool → term₁ Γ ι
  | And₁ : term₁ Γ (ι ⇒ ι ⇒ ι)
  | Var₁ : ∀ α, mem_index α Γ → term₁ Γ α
  | App₁ : ∀ α β, term₁ Γ (α ⇒ β) → term₁ Γ α → term₁ Γ β
  | Abs₁ : ∀ α β, term₁ (β :: Γ) α → term₁ Γ (β ⇒ α).
Arguments k₁ {Γ}.
Arguments And₁ {Γ}.
Arguments Var₁ {Γ}.
Arguments App₁ {Γ α β}.
Arguments Abs₁ {Γ α}.

Notation "s  '$₁'  t" := (App₁ s t) (at level 40, left associativity).
Notation "'λ₁:'  α ','  s" := (Abs₁ α s) (at level 60, s at level 60, right associativity).

(* Equations Derive Signature for term₁. *)

Definition term₁_sig (index : sigma (λ _ : list type, type)) :=
  term₁ (pr1 index) (pr2 index).

Definition term₁_sig_pack Γ α (term₁_var : term₁ Γ α) : sigma term₁_sig :=
  {| pr1 := {| pr1 := Γ; pr2 := α |}; pr2 := term₁_var |}.

Instance term₁_Signature Γ α : Signature (term₁ Γ α) (sigma (λ _ : list type, type)) term₁_sig :=
  term₁_sig_pack Γ α.

Equations Derive NoConfusion for term₁.

Instance arbitrary_term₁ {Γ α} : Arbitrary (term₁ Γ α).
Proof.
  revert Γ; induction α as [| α_1 IH_α_1 α_2 IH_α_2]; intros Γ.
  - apply (k₁ false).
  - apply Abs₁. apply IH_α_2.
Defined.

Instance dec_eq_term₁ {Γ α} : EqDec (term₁ Γ α) eq.
Proof.
  rewrite dec_eq_def.
  intros s; induction s as [Γ s_b | Γ | Γ s_α s_mi | Γ s_α s_β s_1 IH_1 s_2 IH_2 | Γ s_α s_β s_1 IH_1]; intros t.
  - ltac1:(dependent elimination t as [@k₁ _ t_b | @Var₁ _ t_α t_mi | @App₁ _ t_α t_β t_1 t_2]); try (right; congruence).
    destruct (s_b == t_b) as [H_n | H_n]; constructor; congruence.
  - ltac1:(dependent elimination t as [@And₁ _ | @Var₁ _ t_α t_mi | @App₁ _ t_α t_β t_1 t_2 | @Abs₁ _ t_α t_β t_1]); constructor; congruence.
  - ltac1:(dependent elimination t as [@k₁ _ t_b | @And₁ _ | @Var₁ _ t_α t_mi | @App₁ _ t_α t_β t_1 t_2 | @Abs₁ _ t_α t_β t_1]); try (right; congruence).
    destruct (s_mi == t_mi : {_ = _} + {_ ≠ _}) as [-> | H_mi]; constructor; congruence.
  - ltac1:(dependent elimination t as [@k₁ _ t_b | @And₁ _ | @Var₁ _ t_α t_mi | @App₁ _ t_α t_β t_1 t_2 | @Abs₁ _ t_α t_β t_1]); try (right; congruence).
    destruct (s_α == t_α) as [-> | H_α]; try (right; congruence). specialize (IH_1 t_1); specialize (IH_2 t_2).
    destruct IH_1 as [IH_1 | IH_1] > [destruct IH_2 as [IH_2 | IH_2] |].
    + left; congruence.
    + right. intros H. apply IH_2. injection H as _ H. apply inj_right_pair in H. auto.
    + right. intros H. apply IH_1. injection H as H _. do 2 (apply inj_right_pair in H). auto.
  - ltac1:(dependent elimination t as [@And₁ _ | @Var₁ _ t_α t_mi | @App₁ _ t_α t_β t_1 t_2 | @Abs₁ _ t_α t_β t_1]); try (right; congruence).
    specialize (IH_1 t_1). destruct IH_1 as [IH_1 | IH_1]; constructor; congruence.
Defined.


Inductive term₁_direct_subterm : ∀ {s_Γ s_α t_Γ t_α}, term₁ s_Γ s_α → term₁ t_Γ t_α → Prop :=
  | term₁_direct_subterm_App₁_1 :
    ∀ {t_Γ t_α t_β} (t_1 : term₁ t_Γ (t_α ⇒ t_β)) (t_2 : term₁ t_Γ t_α),
    term₁_direct_subterm t_1 (t_1 $₁ t_2)
  | term₁_direct_subterm_App₁_2 :
    ∀ {t_Γ t_α t_β} (t_1 : term₁ t_Γ (t_α ⇒ t_β)) (t_2 : term₁ t_Γ t_α),
    term₁_direct_subterm t_2 (t_1 $₁ t_2)
  | term₁_direct_subterm_Abs₁_1 :
    ∀ {t_Γ t_α} t_β (t_2 : term₁ (t_β :: t_Γ) t_α),
    term₁_direct_subterm t_2 (λ₁: t_β, t_2).

Hint Resolve term₁_direct_subterm_App₁_1 : subterm_relation.
Hint Resolve term₁_direct_subterm_App₁_2 : subterm_relation.
Hint Resolve term₁_direct_subterm_Abs₁_1 : subterm_relation.

Definition term₁_subterm :=
  Relation_Operators.clos_trans
    (sigma (λ index : sigma (λ _ : list type, type), term₁ (pr1 index) (pr2 index)))
    (λ s t, term₁_direct_subterm (pr2 s) (pr2 t)).

Hint Unfold term₁_subterm : subterm_relation.

Instance well_founded_term₁_subterm : WellFounded term₁_subterm.
Proof.
  apply Transitive_Closure.wf_clos_trans. intros [[t_Γ t_α] t]; simpl in t.
  induction t as [t_Γ t_b | t_Γ | t_Γ t_α t_mi | t_Γ t_α t_β t_1 IH_1 t_2 IH_2 | Γ t_α t_β t_1 IH_1]; apply Acc_intro; simpl; intros [[s_Γ s_α] s] H; simpl in s |- *;
  try (solve [ltac1:(dependent elimination s as [@k₁ _ s_b | @And₁ _ | @Var₁ _ s_α s_mi | @App₁ _ s_α_ s_β s_1 s_2 | @Abs₁ _ s_α s_β s_1]); inversion H]); try (solve [ltac1:(dependent elimination H); auto]).
Defined.

Equations rebuild_term₁ {Γ α} (s : term₁ Γ α) : term₁ Γ α by wf (signature_pack s) :=
  | k₁ b => k₁ b
  | And₁ => And₁
  | Var₁ s_α s_mi => Var₁ s_α s_mi
  | s_1 $₁ s_2 => (rebuild_term₁ s_1) $₁ (rebuild_term₁ s_2)
  | λ₁: s_β, s_1 => λ₁: s_β, rebuild_term₁ s_1.

Definition substitution₁ Γ Δ := ∀ (α : type), mem_index α Δ → term₁ Γ α.

Definition substitution₁_of_renaming {Γ Δ} (σ : renaming Γ Δ) : substitution₁ Γ Δ :=
  λ _ mi, Var₁ _ (σ _ mi).

Definition substitution₁_id Γ : substitution₁ Γ Γ :=
  substitution₁_of_renaming (renaming_id Γ).

Equations substitution₁_cons {Γ Δ} α (s : term₁ Γ α) (σ : substitution₁ Γ Δ) : substitution₁ Γ (α :: Δ) :=
  | α, mi, σ, _, MIO => mi
  | α, mi, σ, _, MIS mi' => σ _ mi'.

Definition substitution₁_shift α Γ : substitution₁ (α :: Γ) Γ :=
  substitution₁_of_renaming (renaming_shift α Γ).

Equations renaming_inst_term₁ {Γ Δ α} (σ : renaming Γ Δ) (s : term₁ Δ α) : term₁ Γ α by wf (signature_pack s) :=
  | σ, k₁ b => k₁ b
  | σ, And₁ => And₁
  | σ, Var₁ s_α s_mi => Var₁ s_α (σ s_α s_mi)
  | σ, s_1 $₁ s_2 => (renaming_inst_term₁ σ s_1) $₁ (renaming_inst_term₁ σ s_2)
  | σ, λ₁: s_β, s_1 => λ₁: s_β, renaming_inst_term₁ (renaming_up s_β σ) s_1.

Definition substitution₁_comp_renaming {Γ Δ Θ} (τ : substitution₁ Δ Θ) (σ : renaming Γ Δ) : substitution₁ Γ Θ :=
  λ _ mi, renaming_inst_term₁ σ (τ _ mi).

Definition substitution₁_up {Γ Δ} α (σ : substitution₁ Γ Δ) : substitution₁ (α :: Γ) (α :: Δ) :=
  substitution₁_cons α (Var₁ α MIO) (substitution₁_comp_renaming σ (renaming_shift α Γ)).

Equations substitution₁_inst {Γ Δ α} (σ : substitution₁ Γ Δ) (s : term₁ Δ α) : term₁ Γ α by wf (signature_pack s) :=
  | σ, k₁ b => k₁ b
  | σ, And₁ => And₁
  | σ, Var₁ s_α s_mi => σ s_α s_mi
  | σ, s_1 $₁ s_2 => (substitution₁_inst σ s_1) $₁ (substitution₁_inst σ s_2)
  | σ, λ₁: s_β, s_1 => λ₁: s_β, substitution₁_inst (substitution₁_up s_β σ) s_1.

Definition substitution₁_comp {Γ Δ Θ} (τ : substitution₁ Δ Θ) (σ : substitution₁ Γ Δ) : substitution₁ Γ Θ :=
  λ _ mi, substitution₁_inst σ (τ _ mi).

Lemma renaming_id_def_term₁ :
  ∀ Γ,
  @substitution₁_of_renaming _ _ (renaming_id Γ) = substitution₁_id Γ.
Proof.
  intros Γ. reflexivity.
Qed.

Lemma renaming_cons_def_term₁ {Γ Δ} :
  ∀ α (mi : mem_index α Γ) (σ : renaming Γ Δ),
  @substitution₁_of_renaming _ _ (renaming_cons α mi σ) = substitution₁_cons α (Var₁ α mi) (substitution₁_of_renaming σ).
Proof.
  intros α mi σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi_1.
  unfold substitution₁_of_renaming. ltac1:(dependent elimination mi_1 as [@MIO Γ' | @MIS γ Γ' mi_1']); ltac1:(simp renaming_cons substitution₁_cons); reflexivity.
Qed.

Lemma renaming_shift_def_term₁ :
  ∀ α Γ,
  @substitution₁_of_renaming _ _ (renaming_shift α Γ) = substitution₁_shift α Γ.
Proof.
  intros α Γ. reflexivity.
Qed.

Lemma renaming_comp_def_term₁ {Γ Δ Θ} :
  ∀ (τ : renaming Δ Θ) (σ : renaming Γ Δ),
  @substitution₁_of_renaming _ _ (renaming_comp τ σ) = substitution₁_comp_renaming (substitution₁_of_renaming τ) σ.
Proof.
  intros τ σ. reflexivity.
Qed.

Lemma renaming_up_def_term₁ {Γ Δ} :
  ∀ α (σ : renaming Γ Δ),
  @substitution₁_of_renaming _ _ (renaming_up α σ) = substitution₁_up α (substitution₁_of_renaming σ).
Proof.
  intros α σ. unfold renaming_up, substitution₁_up. rewrite renaming_cons_def_term₁, renaming_comp_def_term₁. reflexivity.
Qed.

Lemma renaming_inst_term₁_def {Γ Δ α} :
  ∀ (σ : renaming Γ Δ) (s : term₁ Δ α),
  renaming_inst_term₁ σ s = substitution₁_inst (substitution₁_of_renaming σ) s.
Proof.
  intros σ s. revert Γ σ; induction s as [Δ s_b | Δ | Δ s_α s_mi | Δ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Δ s_α s_β s_1 IH_s_1]; intros Γ σ; ltac1:(simp renaming_inst_term₁ substitution₁_inst); try (congruence).
  - reflexivity.
  - rewrite IH_s_1. rewrite renaming_up_def_term₁. reflexivity.
Qed.

Lemma substitution₁_comp_renaming_def {Γ Δ Θ} :
  ∀ (τ : substitution₁ Δ Θ) (σ : renaming Γ Δ),
  substitution₁_comp_renaming τ σ = substitution₁_comp τ (substitution₁_of_renaming σ).
Proof.
  intros τ σ. unfold substitution₁_comp_renaming, substitution₁_comp. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  rewrite renaming_inst_term₁_def. reflexivity.
Qed.

Lemma substitution₁_up_def {Γ Δ} :
  ∀ α (σ : substitution₁ Γ Δ),
  substitution₁_up α σ = substitution₁_cons α (Var₁ α MIO) (substitution₁_comp σ (substitution₁_shift α Γ)).
Proof.
  intros α σ. unfold substitution₁_up. rewrite substitution₁_comp_renaming_def, renaming_shift_def_term₁. reflexivity.
Qed.

Lemma substitution₁_up_substitution₁_of_renaming {Γ Δ} :
  ∀ α (σ : renaming Γ Δ),
  substitution₁_up α (@substitution₁_of_renaming _ _ σ) = substitution₁_of_renaming (renaming_cons α MIO (renaming_comp σ (renaming_shift α Γ))).
Proof.
  intros α σ. rewrite substitution₁_up_def, renaming_cons_def_term₁, renaming_comp_def_term₁, substitution₁_comp_renaming_def. unfold substitution₁_shift. reflexivity.
Qed.

Lemma substitution₁_inst_k₁ {Γ Δ} :
  ∀ (σ : substitution₁ Γ Δ) s_b,
  substitution₁_inst σ (k₁ s_b) = k₁ s_b.
Proof.
  intros σ s_b. ltac1:(simp substitution₁_inst). reflexivity.
Qed.

Lemma substitution₁_inst_And₁ {Γ Δ} :
  ∀ (σ : substitution₁ Γ Δ),
  substitution₁_inst σ And₁ = And₁.
Proof.
  intros σ. ltac1:(simp substitution₁_inst). reflexivity.
Qed.

Lemma substitution₁_inst_Var₁ {Γ Δ} :
  ∀ (σ : substitution₁ Γ Δ) s_α s_mi,
  substitution₁_inst σ (Var₁ s_α s_mi) = σ s_α s_mi.
Proof.
  intros σ s_α s_mi. ltac1:(simp substitution₁_inst). reflexivity.
Qed.

Lemma substitution₁_inst_App₁ {Γ Δ s_α s_β} :
  ∀ (σ : substitution₁ Γ Δ) (s_1 : term₁ Δ (s_α ⇒ s_β)) (s_2 : term₁ Δ s_α),
  substitution₁_inst σ (s_1 $₁ s_2) = (substitution₁_inst σ s_1) $₁ (substitution₁_inst σ s_2).
Proof.
  intros σ s_1 s_2. ltac1:(simp substitution₁_inst). reflexivity.
Qed.

Lemma substitution₁_inst_Abs₁ {Γ Δ s_α} :
  ∀ (σ : substitution₁ Γ Δ) s_β (s_1 : term₁ (s_β :: Δ) s_α),
  substitution₁_inst σ (λ₁: s_β, s_1) = λ₁: s_β, substitution₁_inst (substitution₁_up s_β σ) s_1.
Proof.
  intros σ s_β s_1. ltac1:(simp substitution₁_inst). reflexivity.
Qed.

Lemma substitution₁_inst_substitution₁_cons_Var₁_MIO {Γ Δ} :
  ∀ α (s : term₁ Γ α) (σ : substitution₁ Γ Δ),
  substitution₁_inst (substitution₁_cons α s σ) (Var₁ α MIO) = s.
Proof.
  intros α s σ. rewrite substitution₁_inst_Var₁. ltac1:(simp substitution₁_cons). reflexivity.
Qed.

Lemma substitution₁_comp_substitution₁_shift_substitution₁_cons {Γ Δ} :
  ∀ α (s : term₁ Γ α) (σ : substitution₁ Γ Δ),
  substitution₁_comp (substitution₁_shift α Δ) (substitution₁_cons α s σ) = σ.
Proof.
  intros α s σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitution₁_comp, substitution₁_shift, substitution₁_of_renaming, renaming_shift.
  rewrite substitution₁_inst_Var₁. ltac1:(simp substitution₁_cons). reflexivity.
Qed.

Lemma substitution₁_comp_substitution₁_cons {Γ Δ Θ} :
  ∀ α (s : term₁ Δ α) (τ : substitution₁ Δ Θ) (σ : substitution₁ Γ Δ),
  substitution₁_comp (substitution₁_cons α s τ) σ = substitution₁_cons α (substitution₁_inst σ s) (substitution₁_comp τ σ).
Proof.
  intros α s τ σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitution₁_comp. ltac1:(dependent elimination mi as [@MIO Θ' | @MIS γ Θ' mi']); ltac1:(simp substitution₁_cons); reflexivity.
Qed.

Lemma substitution₁_recombination {Γ Δ α} :
  ∀ (σ : substitution₁ Γ (α :: Δ)),
  substitution₁_cons α (substitution₁_inst σ (Var₁ α MIO)) (substitution₁_comp (substitution₁_shift α Δ) σ) = σ.
Proof.
  intros σ. apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitution₁_comp, substitution₁_shift, substitution₁_of_renaming, renaming_shift. ltac1:(dependent elimination mi as [@MIO Θ' | @MIS γ Θ' mi']); ltac1:(simp substitution₁_cons); rewrite substitution₁_inst_Var₁; reflexivity.
Qed.

Lemma substitution₁_cons_Var₁_MIO_substitution₁_shift {Γ α} :
  substitution₁_cons α (@Var₁ _ α MIO) (substitution₁_shift α Γ) = substitution₁_id (α :: Γ).
Proof.
  apply functional_extensionality_dep; intros β; apply functional_extensionality; intros mi.
  unfold substitution₁_comp, substitution₁_shift, substitution₁_id, substitution₁_of_renaming, renaming_shift, renaming_id. ltac1:(dependent elimination mi as [@MIO Γ' | @MIS γ Γ' mi']); ltac1:(simp substitution₁_cons); reflexivity.
Qed.

Lemma substitution₁_comp_substitution₁_id_left {Γ Δ} :
  ∀ (σ : substitution₁ Γ Δ),
  substitution₁_comp (substitution₁_id Δ) σ = σ.
Proof.
  intros σ. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  unfold substitution₁_comp, substitution₁_id, substitution₁_of_renaming, renaming_id. rewrite substitution₁_inst_Var₁. reflexivity.
Qed.

Lemma substitution₁_comp_substitution₁_id_right {Γ Δ} :
  ∀ (σ : substitution₁ Γ Δ),
  substitution₁_comp σ (substitution₁_id Γ) = σ.
Proof.
  intros σ. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  unfold substitution₁_comp. generalize (σ α mi) as s; intros s; clear σ mi.
  induction s as [Γ s_b | Γ | Γ s_α s_mi | Γ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Γ s_α s_β s_1 IH_s_1].
  - rewrite substitution₁_inst_k₁. reflexivity.
  - rewrite substitution₁_inst_And₁. reflexivity.
  - rewrite substitution₁_inst_Var₁. unfold substitution₁_id, substitution₁_of_renaming, renaming_id. reflexivity.
  - rewrite substitution₁_inst_App₁. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite substitution₁_inst_Abs₁. rewrite substitution₁_up_def, substitution₁_comp_substitution₁_id_left, substitution₁_cons_Var₁_MIO_substitution₁_shift. rewrite IH_s_1. reflexivity.
Qed.

Lemma substitution₁_inst_substitution₁_inst_substitution₁_of_renaming {Γ Δ Θ α} :
  ∀ (τ : renaming Δ Θ) (σ : substitution₁ Γ Δ) (s : term₁ Θ α),
  substitution₁_inst σ (substitution₁_inst (substitution₁_of_renaming τ) s) = substitution₁_inst (substitution₁_comp (substitution₁_of_renaming τ) σ) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ s_b | Θ | Θ s_α s_mi | Θ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Θ s_α s_β s_1 IH_s_1]; intros Γ Δ τ σ.
  - rewrite ! substitution₁_inst_k₁. reflexivity.
  - rewrite ! substitution₁_inst_And₁. reflexivity.
  - rewrite ! substitution₁_inst_Var₁. unfold substitution₁_comp. reflexivity.
  - rewrite ! substitution₁_inst_App₁. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite ! substitution₁_inst_Abs₁. rewrite (substitution₁_up_substitution₁_of_renaming s_β τ). rewrite IH_s_1. do 2 f_equal.
    rewrite (substitution₁_up_def s_β (substitution₁_comp (substitution₁_of_renaming τ) σ)), renaming_cons_def_term₁, substitution₁_comp_substitution₁_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    rewrite substitution₁_up_def. unfold substitution₁_comp at 1 3 4, renaming_comp, substitution₁_of_renaming. rewrite ! substitution₁_inst_Var₁.
    specialize (substitution₁_comp_substitution₁_shift_substitution₁_cons s_β (Var₁ s_β MIO) (substitution₁_comp σ (substitution₁_shift s_β Γ))) as H. specialize (equal_f (equal_f_dep H γ) (τ γ mi)) as H'.
    unfold substitution₁_comp at 1 3, substitution₁_shift, substitution₁_of_renaming at 2 in H'. rewrite substitution₁_inst_Var₁ in H'.
    unfold substitution₁_shift. rewrite H'. reflexivity.
Qed.

Lemma substitution₁_inst_substitution₁_of_renaming_substitution₁_inst {Γ Δ Θ α} :
  ∀ (τ : substitution₁ Δ Θ) (σ : renaming Γ Δ) (s : term₁ Θ α),
  substitution₁_inst (substitution₁_of_renaming σ) (substitution₁_inst τ s) = substitution₁_inst (substitution₁_comp τ (substitution₁_of_renaming σ)) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ s_b | Θ | Θ s_α s_mi | Θ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Θ s_α s_β s_1 IH_s_1]; intros Γ Δ τ σ.
  - rewrite ! substitution₁_inst_k₁. reflexivity.
  - rewrite ! substitution₁_inst_And₁. reflexivity.
  - rewrite ! substitution₁_inst_Var₁. unfold substitution₁_comp. reflexivity.
  - rewrite ! substitution₁_inst_App₁. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite ! substitution₁_inst_Abs₁. rewrite (substitution₁_up_substitution₁_of_renaming s_β σ). rewrite IH_s_1. do 2 f_equal.
    rewrite ! substitution₁_up_def, renaming_cons_def_term₁, substitution₁_comp_substitution₁_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    unfold substitution₁_comp, substitution₁_shift. rewrite ! substitution₁_inst_substitution₁_inst_substitution₁_of_renaming.
    specialize (@substitution₁_comp_substitution₁_shift_substitution₁_cons _ _ s_β (Var₁ s_β MIO) (substitution₁_of_renaming (renaming_comp σ (renaming_shift s_β Γ)))) as H. unfold substitution₁_shift in H. rewrite H.
    rewrite renaming_comp_def_term₁, substitution₁_comp_renaming_def. reflexivity.
Qed.

Lemma substitution₁_inst_substitution₁_inst {Γ Δ Θ α} :
  ∀ (τ : substitution₁ Δ Θ) (σ : substitution₁ Γ Δ) (s : term₁ Θ α),
  substitution₁_inst σ (substitution₁_inst τ s) = substitution₁_inst (substitution₁_comp τ σ) s.
Proof.
  intros τ σ s. revert Γ Δ τ σ; induction s as [Θ s_b | Θ | Θ s_α s_mi | Θ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Θ s_α s_β s_1 IH_s_1]; intros Γ Δ τ σ.
  - rewrite ! substitution₁_inst_k₁. reflexivity.
  - rewrite ! substitution₁_inst_And₁. reflexivity.
  - rewrite ! substitution₁_inst_Var₁. unfold substitution₁_comp. reflexivity.
  - rewrite ! substitution₁_inst_App₁. rewrite IH_s_1, IH_s_2. reflexivity.
  - rewrite ! substitution₁_inst_Abs₁. rewrite IH_s_1. do 2 f_equal.
    rewrite (substitution₁_up_def s_β τ), (substitution₁_up_def s_β (substitution₁_comp τ σ)), substitution₁_comp_substitution₁_cons. f_equal.
    apply functional_extensionality_dep; intros γ; apply functional_extensionality; intros mi.
    unfold substitution₁_comp, substitution₁_shift.
    rewrite substitution₁_inst_substitution₁_inst_substitution₁_of_renaming, substitution₁_inst_substitution₁_of_renaming_substitution₁_inst, substitution₁_up_def.
    specialize (@substitution₁_comp_substitution₁_shift_substitution₁_cons _ _ s_β (Var₁ s_β MIO) (substitution₁_comp σ (substitution₁_shift s_β Γ))) as H. unfold substitution₁_shift in H |- *. rewrite H. reflexivity.
Qed.

Lemma associativity_rev_substitution₁_comp {Γ Δ Θ Λ} :
  ∀ (υ : substitution₁ Θ Λ) (τ : substitution₁ Δ Θ) (σ : substitution₁ Γ Δ),
  substitution₁_comp (substitution₁_comp υ τ) σ = substitution₁_comp υ (substitution₁_comp τ σ).
Proof.
  intros υ τ σ. apply functional_extensionality_dep; intros α; apply functional_extensionality; intros mi.
  unfold substitution₁_comp at 1 2 3. rewrite substitution₁_inst_substitution₁_inst. reflexivity.
Qed.

Hint Rewrite @renaming_id_def_term₁ : substitution₁.
Hint Rewrite @renaming_cons_def_term₁ : substitution₁.
Hint Rewrite @renaming_shift_def_term₁ : substitution₁.
Hint Rewrite @renaming_comp_def_term₁ : substitution₁.
Hint Rewrite @renaming_up_def_term₁ : substitution₁.
Hint Rewrite @renaming_inst_term₁_def : substitution₁.
Hint Rewrite @substitution₁_comp_renaming_def : substitution₁.
Hint Rewrite @substitution₁_up_def : substitution₁.
Hint Rewrite @substitution₁_up_substitution₁_of_renaming : substitution₁.
Hint Rewrite @substitution₁_inst_k₁ : substitution₁.
Hint Rewrite @substitution₁_inst_And₁ : substitution₁.
Hint Rewrite @substitution₁_inst_App₁ : substitution₁.
Hint Rewrite @substitution₁_inst_Abs₁ : substitution₁.
Hint Rewrite @substitution₁_inst_substitution₁_cons_Var₁_MIO : substitution₁.
Hint Rewrite @substitution₁_comp_substitution₁_shift_substitution₁_cons : substitution₁.
Hint Rewrite @substitution₁_comp_substitution₁_cons : substitution₁.
Hint Rewrite @substitution₁_recombination : substitution₁.
Hint Rewrite @substitution₁_comp_substitution₁_id_left : substitution₁.
Hint Rewrite @substitution₁_cons_Var₁_MIO_substitution₁_shift : substitution₁.
Hint Rewrite @substitution₁_comp_substitution₁_id_left : substitution₁.
Hint Rewrite @substitution₁_comp_substitution₁_id_right : substitution₁.
Hint Rewrite @associativity_rev_substitution₁_comp : substitution₁.

Reserved Notation "s_1  ⟶₁  s_2" (at level 70).

Inductive term₁_step {Γ} : ∀ {α}, term₁ Γ α → term₁ Γ α → Type :=
  | term₁_step_And₁_true :
    ∀ s_2 : term₁ Γ ι,
    And₁ $₁ (k₁ true) $₁ s_2 ⟶₁ s_2
  | term₁_step_And₁_false :
    ∀ s_2 : term₁ Γ ι,
    And₁ $₁ (k₁ false) $₁ s_2 ⟶₁ k₁ false
  | term₁_step_App₁_1 :
    ∀ {s_α s_β} (s_1 t_1 : term₁ Γ (s_α ⇒ s_β)) (s_2 : term₁ Γ s_α),
    s_1 ⟶₁ t_1 →
    s_1 $₁ s_2 ⟶₁ t_1 $₁ s_2
  | term₁_step_App₁_2 :
    ∀ {s_α s_β} (s_1 : term₁ Γ (s_α ⇒ s_β)) (s_2 t_2 : term₁ Γ s_α),
    s_2 ⟶₁ t_2 →
    s_1 $₁ s_2 ⟶₁ s_1 $₁ t_2
  | term₁_step_Abs₁_1 :
    ∀ {s_α} s_β (s_1 t_1 : term₁ (s_β :: Γ) s_α),
    s_1 ⟶₁ t_1 →
    λ₁: s_β, s_1 ⟶₁ λ₁: s_β, t_1
  | term₁_step_Abs₁ :
    ∀ {s_α} s_β (s_1_1 : term₁ (s_β :: Γ) s_α) (s_2 : term₁ Γ s_β),
    (λ₁: s_β, s_1_1) $₁ s_2 ⟶₁ substitution₁_inst (substitution₁_cons s_β s_2 (substitution₁_id Γ)) s_1_1
  where "s ⟶₁ t" := (term₁_step s t).

Notation "s  ⟶+₁  t" := (t_closure_t term₁_step s t) (at level 70).
Notation "s  ⟶*₁  t" := (rt_closure_t term₁_step s t) (at level 70).

Inductive term₁_normal {Γ} : ∀ {α}, term₁ Γ α → Type :=
  | term₁_normal_of_term₁_neutral :
    ∀ {α} (s : term₁ Γ α),
    term₁_neutral s →
    term₁_normal s
  | term₁_normal_k₁ :
    ∀ s_b,
    term₁_normal (k₁ s_b)
  | term₁_normal_And₁ :
    term₁_normal And₁
  | term₁_normal_And₁_app₁ :
    ∀ (s_2 : term₁ Γ ι),
    term₁_normal s_2 →
    term₁_normal (And₁ $₁ s_2)
  | term₁_normal_Abs₁ :
    ∀ {s_α} s_β (s_1 : term₁ (s_β :: Γ) s_α),
    term₁_normal s_1 →
    term₁_normal (λ₁: s_β, s_1)
with term₁_neutral {Γ} : ∀ {α}, term₁ Γ α → Type :=
  | term₁_neutral_And₁ :
    ∀ (s_2 : term₁ Γ ι),
    term₁_neutral s_2 →
    term₁_neutral (And₁ $₁ s_2)
  | term₁_neutral_Var₁ :
    ∀ {s_α} (s_mi : mem_index s_α Γ),
    term₁_neutral (Var₁ s_α s_mi)
  | term₁_neutral_App₁ :
    ∀ {s_α s_β} (s_1 : term₁ Γ (s_α ⇒ s_β)) (s_2 : term₁ Γ s_α),
    term₁_neutral s_1 →
    term₁_normal s_2 →
    term₁_neutral (s_1 $₁ s_2).

Scheme term₁_normal_mutind := Induction for term₁_normal Sort Prop
with term₁_neutral_mutind := Induction for term₁_neutral Sort Prop.

Scheme term₁_normal_mutrect := Induction for term₁_normal Sort Type
with term₁_neutral_mutrect := Induction for term₁_neutral Sort Type.

Definition term₁_normal_mutrec (P_normal : ∀ Γ α (s : term₁ Γ α), term₁_normal s → Set) (P_neutral : ∀ Γ α (s : term₁ Γ α), term₁_neutral s → Set) := term₁_normal_mutrect P_normal P_neutral.
Definition term₁_neutral_mutrec (P_normal : ∀ Γ α (s : term₁ Γ α), term₁_normal s → Set) (P_neutral : ∀ Γ α (s : term₁ Γ α), term₁_neutral s → Set) := term₁_neutral_mutrect P_normal P_neutral.

Definition term₁_progress {Γ α} (s : term₁ Γ α) : {t & s ⟶₁ t} + term₁_normal s.
Proof.
  induction s as [Γ s_b | Γ | Γ s_α s_mi | Γ s_α s_β s_1 IH_s_1 s_2 IH_s_2 | Γ s_α s_β s_1 IH_s_1].
  - right. apply term₁_normal_k₁.
  - right. apply term₁_normal_And₁.
  - right. apply term₁_normal_of_term₁_neutral, term₁_neutral_Var₁.
  - ltac1:(dependent elimination s_1 as [@And₁ _ | @Var₁ _ s_1_α s_1_mi | @App₁ _ s_1_α s_1_β s_1_1 s_1_2 | @Abs₁ _ s_1_α s_1_β s_1_1]).
    + destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2].
      * left. exists (And₁ $₁ t_2). apply term₁_step_App₁_2; auto.
      * right. apply term₁_normal_And₁_app₁; auto.
    + destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1] > [| destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2]].
      * left. exists (t_1 $₁ s_2). apply term₁_step_App₁_1; auto.
      * left. exists (Var₁ (s_α ⇒ s_β) s_1_mi $₁ t_2). apply term₁_step_App₁_2; auto.
      * ltac1:(dependent elimination H_s_1 as [term₁_normal_of_term₁_neutral s_1 H_s_1]).
        right. apply term₁_normal_of_term₁_neutral, term₁_neutral_App₁; auto.
    + destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1].
      * left. exists (t_1 $₁ s_2). apply term₁_step_App₁_1; auto.
      * ltac1:(dependent elimination H_s_1 as [term₁_normal_of_term₁_neutral s_1 H_s_1 | term₁_normal_And₁_app₁ s_1_2 H_s_1_2]).
        -- destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2].
           ++ left. exists (s_1_1 $₁ s_1_2 $₁ t_2). apply term₁_step_App₁_2; auto.
           ++ right. apply term₁_normal_of_term₁_neutral, term₁_neutral_App₁; auto.
        -- ltac1:(dependent elimination H_s_1_2 as [term₁_normal_of_term₁_neutral s_1_2 H_s_1_2 | term₁_normal_k₁ s_1_2_b]).
           ++ destruct IH_s_2 as [(t_2 & H_s_2) | H_s_2].
              ** left. exists (And₁ $₁ s_1_2 $₁ t_2). apply term₁_step_App₁_2; auto.
              ** right. apply term₁_normal_of_term₁_neutral, term₁_neutral_App₁.
                 --- apply term₁_neutral_And₁; auto.
                 --- auto.
           ++ destruct s_1_2_b as [|].
              ** left. exists s_2. apply term₁_step_And₁_true.
              ** left. exists (k₁ false). apply term₁_step_And₁_false.
    + left. exists (substitution₁_inst (substitution₁_cons s_1_β s_2 (substitution₁_id Γ)) s_1_1). apply term₁_step_Abs₁.
  - destruct IH_s_1 as [(t_1 & H_s_1) | H_s_1].
    + left. exists (λ₁: s_β, t_1). apply term₁_step_Abs₁_1; auto.
    + right. apply term₁_normal_Abs₁; auto.
Defined.

Lemma not_term₁_normal_and_term₁_step {Γ α} :
  ∀ (s t : term₁ Γ α),
  term₁_normal s →
  s ⟶₁ t →
  False.
Proof.
  intros s t H_normal H_step. revert t H_step; apply (term₁_normal_mutind (λ Γ α s H_normal, ∀ t, s ⟶₁ t → False) (λ Γ α s H_neutral, ∀ t, s ⟶₁ t → False)); try (apply H_normal); clear Γ α s H_normal.
  - intros Γ α s H_neutral_s IH_s t H_step. apply (IH_s t); auto.
  - intros Γ s_b t H_step. inversion H_step.
  - intros Γ t H_step. inversion H_step.
  - intros Γ s_2 H_normal_s_2 IH_s_2 t H_step.
    ltac1:(dependent elimination H_step as [@term₁_step_App₁_2 _ _ _ s_1 s_2 t_2 H_step]). apply (IH_s_2 t_2); auto.
  - intros Γ s_α s_β s_1 H_normal_s_1 IH_s_1 t H_step.
    ltac1:(dependent elimination H_step as [@term₁_step_Abs₁_1 _ s_α s_β s_1 t_1 H_step]). apply (IH_s_1 t_1); auto.
  - intros Γ s_2 H_neutral_s_2 IH_s_2 t H_step.
    ltac1:(dependent elimination H_step as [@term₁_step_App₁_2 _ _ _ s_1 s_2 t_2 H_step]). apply (IH_s_2 t_2); auto.
  - intros Γ s_α s_mi t H_step. inversion H_step.
  - intros Γ s_α s_β s_1 s_2 H_neutral_s_1 IH_s_1 H_normal_s_2 IH_s_2 t H_step.
    ltac1:(dependent elimination H_step as [@term₁_step_And₁_true _ s_2 | @term₁_step_And₁_false _ s_2 | @term₁_step_App₁_1 _ _ _ s_1 t_1 s_2 H_step | @term₁_step_App₁_2 _ _ _ s_1 s_2 t_2 H_step]).
    + remember And₁ as s_1_1 eqn:H_s_1_1; ltac1:(dependent elimination H_neutral_s_1 as [@term₁_neutral_App₁ _ _ _ s_1_1 s_1_2 H_neutral_s_1_1 H_normal_s_1_2]); subst s_1_1. inversion H_neutral_s_1_1.
    + remember And₁ as s_1_1 eqn:H_s_1_1; ltac1:(dependent elimination H_neutral_s_1 as [@term₁_neutral_App₁ _ _ _ s_1_1 s_1_2 H_neutral_s_1_1 H_normal_s_1_2]); subst s_1_1. inversion H_neutral_s_1_1.
    + apply (IH_s_1 t_1); auto.
    + apply (IH_s_2 t_2); auto.
Qed.
