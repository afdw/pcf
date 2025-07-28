From Ltac2 Require Export Ltac2.
From Stdlib Require Export Unicode.Utf8.
From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Export Logic.PropExtensionality.
From Stdlib Require Arith.Arith.
From Stdlib Require Export ZArith.ZArith.
From Stdlib Require Export micromega.Lia.
From Stdlib Require Lists.List.
Export Stdlib.Lists.List.ListNotations.
From Corelib Require Import Program.Basics.

#[global] Obligation Tactic := ().
Unset Program Cases.

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

(* Require Import List.
Print In. *)

Inductive mem_index {A} (a : A) : list A → Type :=
  | MIO : ∀ l', mem_index a (a :: l')
  | MIS : ∀ b l', mem_index a l' → mem_index a (b :: l').
Arguments MIO {A a l'}.
Arguments MIS {A a b l'}.

Check MIS (MIS (MIS MIO)).

(* Declare Scope typed_index_scope.
Delimit Scope typed_index_scope with typed_index.
Bind Scope typed_index_scope with typed_index.
Open Scope typed_index_scope.

Number Notation typed_index True True : typed_index_scope. *)
