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
