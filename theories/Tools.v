From Ltac2 Require Export Ltac2.
From Stdlib Require Export Unicode.Utf8.
From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Export Logic.PropExtensionality.
From Stdlib Require Arith.Arith.
From Stdlib Require Export ZArith.ZArith.
From Stdlib Require Export micromega.Lia.
From Stdlib Require Lists.List.
Export Stdlib.Lists.List.ListNotations.
From Corelib Require Export Program.Basics.
From Stdlib Require Export Classes.EquivDec.

#[global] Obligation Tactic := ().
Unset Program Cases.

Open Scope equiv_scope.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope nat_scope.

Disable Notation "_ ≤ _".
Disable Notation "_ ≥ _".

Notation "x ≤ y" := (le x y) : nat_scope.
Notation "x ≥ y" := (ge x y) : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y /\ y ≤ z) : nat_scope.
Notation "x ≤ y < z" := (x ≤ y /\ y < z) : nat_scope.
Notation "x < y ≤ z" := (x < y /\ y ≤ z) : nat_scope.

Notation "x ≤ y" := (Z.le x y) : Z_scope.
Notation "x ≥ y" := (Z.ge x y) : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y /\ y ≤ z)%Z : Z_scope.
Notation "x ≤ y < z" := (x ≤ y /\ y < z)%Z : Z_scope.
Notation "x < y ≤ z" := (x < y /\ y ≤ z)%Z : Z_scope.

Instance dec_eq_Z : EqDec Z eq := Z.eq_dec.

Inductive mem_index {A} (a : A) : list A → Type :=
  | MIO : ∀ l', mem_index a (a :: l')
  | MIS : ∀ b l', mem_index a l' → mem_index a (b :: l').
Arguments MIO {A a l'}.
Arguments MIS {A a b l'}.

Check MIS (MIS (MIS MIO)).

Definition stabilizing {A B} (f : A → B) :=
  ∃ l b, ∀ a, List.In a l ∨ f a = b.

Record stabilizing_fun A B := {
  stabilizing_fun_f :> A → B;
  stabilizing_fun_stabilizing_f : stabilizing stabilizing_fun_f;
}.
Arguments stabilizing_fun_f {A B}.
Arguments stabilizing_fun_stabilizing_f {A B}.

Notation "A  '→₀'  B" := (stabilizing_fun A B) (at level 99, right associativity) : type_scope.

Lemma injective_stabilizing_fun_f {A B} :
  ∀ f g : A →₀ B, stabilizing_fun_f f = stabilizing_fun_f g → f = g.
Proof.
  intros f g H. destruct f as [f stabilizing_f], g as [g stabilizing_g].
  simpl in H. destruct H. f_equal. apply proof_irrelevance.
Qed.

#[program]
Definition stabilizing_fun_const {A B} b : A →₀ B := {|
  stabilizing_fun_f := λ _, b;
|}.
Next Obligation.
  intros A B b. exists [], b. intros a. auto.
Qed.

#[program]
Definition stabilizing_fun_update {A B} `{equiv : Equivalence A eq} `{dec_equiv : @EqDec A eq equiv} (f : A →₀ B) a b := {|
  stabilizing_fun_f := λ a', if a' == a then b else f a';
|}.
Next Obligation.
  intros A B equiv dec_equiv f a b. destruct f as [f (l & b' & H_f)]. exists (a :: l), b'. intros a'. simpl. destruct (a' == a) as [H_a' | H_a'].
  - left. left. auto.
  - specialize (H_f a'). destruct H_f; auto.
Qed.

Declare Scope stabilizing_fun_scope.
Delimit Scope stabilizing_fun_scope with stabilizing_fun.
Bind Scope stabilizing_fun_scope with stabilizing_fun.
Open Scope stabilizing_fun_scope.

Notation "'_'  '↦₀'  b" := (stabilizing_fun_const b) (at level 70) : stabilizing_fun_scope.
Notation "a  '↦₀'  b ','  f" := (stabilizing_fun_update f a b) (at level 70, f at level 200) : stabilizing_fun_scope.
