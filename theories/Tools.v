From Ltac2 Require Export Ltac2.
From Equations Require Export Equations.
From Equations Require Export TransparentEquations.
From Stdlib Require Export Unicode.Utf8.
From Stdlib Require Export Logic.Classical.
From Stdlib Require Export Logic.FunctionalExtensionality.
From Stdlib Require Export Logic.PropExtensionality.
From Stdlib Require Export Logic.IndefiniteDescription.
From Stdlib Require Arith.Arith.
From Stdlib Require Export ZArith.ZArith.
From Stdlib Require Export micromega.Lia.
Export Corelib.Init.Logic.EqNotations.
From Stdlib Require Lists.List.
Export Stdlib.Lists.List.ListNotations.
From Corelib Require Export Program.Basics.
(* From Corelib Require Export Program.Utils. *)
From Stdlib Require Export Classes.EquivDec.

#[global] Obligation Tactic := try (solve [ltac1:(Equations.CoreTactics.equations_simpl)]).
#[global] Unset Program Cases.
#[global] Unset Program Generalized Coercion.
#[global] Unset Implicit Arguments.

(* #[global] Set Typeclasses Iterative Deepening. *)
#[global] Set Typeclasses Depth 20.

#[global] Set Equations With UIP.
#[global] Set Equations Transparent.

Ltac2 Notation "lia" := ltac1:(lia).

Open Scope program_scope.
Open Scope equiv_scope.
Open Scope bool_scope.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope nat_scope.

Disable Notation "_ ≤ _".
Disable Notation "_ ≥ _".
(* Disable Notation "{ ( _ , _ ) : _ | _ }". *)

Notation "x ≤ y" := (le x y) : nat_scope.
Notation "x ≥ y" := (ge x y) : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : nat_scope.

Notation "x ≤ y" := (Z.le x y) : Z_scope.
Notation "x ≥ y" := (Z.ge x y) : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%Z : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%Z : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%Z : Z_scope.

(* Notation " ! " := (False_rect _ _) : program_scope. (* copied from Corelib.Program.Utils *) *)

Notation " ` t " := (proj1_sig t) (at level 10, t at next level) : program_scope. (* copied from Corelib.Program.Utils *)

Class Arbitrary (A : Type) : Type :=
  | arbitrary : A.

Instance arbitrary_nat : Arbitrary nat := 0.

Instance arbitrary_Z : Arbitrary Z := 0%Z.

Lemma dec_eq_def :
  ∀ A,
  EqDec A eq = ∀ x y : A, {x = y} + {x ≠ y}.
Proof.
  intros A. auto.
Defined.

Instance dec_eq_impl_equations_dec_eq {A} {dec_eq_A : EqDec A eq} : Classes.EqDec A | 100 := dec_eq_A.

Instance equations_dec_eq_impl_dec_eq {A} {dec_eq_A : Classes.EqDec A} : EqDec A eq | 100 := dec_eq_A.

Instance dec_eq_Z : EqDec Z eq := Z.eq_dec.

Class Total {A} (R : A → A → Prop) :=
  | totality : ∀ x y, R x y ∨ R y x.

Instance total_nat_le : Total Nat.le := Nat.le_ge_cases.

Instance total_Z_le : Total Z.le := Z.le_ge_cases.

Definition le {A} {R : A → A → Prop} {pre_order_R : PreOrder R} := R.

Declare Scope le_scope.
Delimit Scope le_scope with le.

Notation "x <= y" := (le x y) (at level 70, no associativity) : le_scope.
Notation "x ≤ y" := (le x y) (at level 70, no associativity) : le_scope.

Class DecLe {A} (R : A → A → Prop) {pre_order_R : PreOrder R} :=
  | dec_le : ∀ x y : A, {(x ≤ y)%le} + {¬ (x ≤ y)%le}.

Notation "x <=? y" := (dec_le x y) (at level 70, no associativity) : le_scope.
Notation "x ≤? y" := (dec_le x y) (at level 70, no associativity) : le_scope.

Instance dec_le_nat : DecLe Nat.le := le_dec.

Instance dec_le_Z : DecLe Z.le := Z_le_dec.

#[program]
Instance dec_le_impl_dec_eq {A} (R : A → A → Prop) {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} : EqDec A eq | 100 :=
  λ x y,
    match (x ≤? y)%le, (y ≤? x)%le with
    | left _, left _ => left _
    | left _, right _ => right _
    | right _, left _ => right _
    | right _, right _ => right _
    end.
Next Obligation.
  intros A R pre_order_R partial_order_R total_R dec_le_R x y H_x_y H_y_x. apply partial_order_equivalence. split; auto.
Qed.
Next Obligation.
  intros A R pre_order_R partial_order_R total_R dec_le_R x y H_x_y H_y_x. unfold equiv. intros <-. auto.
Qed.
Next Obligation.
  intros A R pre_order_R partial_order_R total_R dec_le_R x y H_x_y H_y_x. unfold equiv. intros <-. auto.
Qed.
Next Obligation.
  intros A R pre_order_R partial_order_R total_R dec_le_R x y H_x_y H_y_x. exfalso. destruct (totality x y); auto.
Qed.

Definition max {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {dec_le_R : DecLe R} (x y : A) :=
  if (x ≤? y)%le then y else x.

Lemma commutative_max {A} (R : A → A → Prop) {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ x y : A, max x y = max y x.
Proof.
  intros x y. unfold max. destruct (x ≤? y)%le as [H_x_y | H_x_y], (y ≤? x)%le as [H_y_x | H_y_x].
  - apply partial_order_equivalence. split; auto.
  - auto.
  - auto.
  - exfalso. destruct (totality x y); auto.
Qed.

Lemma le_max {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ x y z : A, (max x y ≤ z)%le ↔ ((x ≤ z)%le ∧ (y ≤ z)%le).
Proof.
  intros x y z. unfold max. split.
  - intros H. destruct (x ≤? y)%le as [H_x_y | H_x_y].
    + split.
      * apply transitivity with y; auto.
      * auto.
    + split.
      * auto.
      * destruct (totality y z) as [H_y_z | H_y_z].
        -- auto.
        -- exfalso. apply H_x_y. apply transitivity with z; auto.
  - intros (H_x_z & H_y_z). destruct (x ≤? y)%le as [H_x_y | H_x_y]; auto.
Qed.

Fixpoint list_max_opt {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {dec_le_R : DecLe R} (l : list A) :=
  match l with
  | [] => None
  | [x] => Some x
  | x :: l =>
    match list_max_opt l with
    | Some y => Some (max x y)
    | None => Some x
    end
  end.

Lemma list_max_opt_none {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {dec_le_R : DecLe R} :
  ∀ l : list A,
  list_max_opt l = None →
  l = [].
Proof.
  intros l H_l. destruct l as [| x l'].
  - auto.
  - simpl in H_l. destruct l' as [| y l''].
    + simpl in H_l. congruence.
    + destruct (list_max_opt (y :: l'')); congruence.
Qed.

Lemma le_list_max_opt {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ (l : list A) x,
  list_max_opt l = Some x →
  ∀ y, (x ≤ y)%le ↔ (∀ z, List.In z l → (z ≤ y)%le).
Proof.
  intros l x H_x y. revert x H_x. induction l as [| z l' IH]; intros x H_x.
  - simpl in H_x. congruence.
  - simpl in H_x. simpl. destruct l' as [| z' l''].
    + injection H_x as ->. simpl. split.
      * intros H. intros _ [<- | []]. auto.
      * intros H. apply H. left. auto.
    + remember (list_max_opt (z' :: l'')) as x_opt eqn:H_x_opt. destruct x_opt as [x' |].
      * injection H_x as <-. rewrite le_max. specialize (IH x' eq_refl). rewrite IH. split.
        -- intros (H_1 & H_2). intros z'' [<- |]; auto.
        -- intros H. split.
           ++ apply H. left. auto.
           ++ intros z'' H_z''. apply H. right. auto.
      * symmetry in H_x_opt. apply list_max_opt_none in H_x_opt. congruence.
Qed.

Definition finite A := { l | ∀ a : A, List.In a l }.

Definition infinite A := ∀ l, { a : A | ¬ List.In a l }.

Lemma inhabited_finite_or_inhabited_infinite :
  ∀ A, inhabited (finite A) ∨ inhabited (infinite A).
Proof.
  intros A. unfold finite, infinite. destruct (classic (∃ l, ∀ a : A, List.In a l)) as [(l & H) | H].
  - left. exists. exists l. auto.
  - right. exists. intros l. apply not_ex_all_not with _ _ l in H. apply not_all_ex_not in H.
    apply constructive_indefinite_description. auto.
Qed.

Lemma not_finite_and_infinite :
  ∀ A, finite A → infinite A → False.
Proof.
  intros A (l & H_1) H_2. specialize (H_2 l) as (a & H_2). specialize (H_1 a). auto.
Qed.

Lemma not_inhabited_finite_and_inhabited_infinite :
  ∀ A, inhabited (finite A) → inhabited (infinite A) → False.
Proof.
  intros A [H_1] [H_2]. apply (not_finite_and_infinite A); auto.
Qed.

Lemma not_inhabited_finite_equiv_not_inhabited_infinite :
  ∀ A, ¬ inhabited (finite A) ↔ inhabited (infinite A).
Proof.
  intros A. specialize (inhabited_finite_or_inhabited_infinite A). specialize (not_inhabited_finite_and_inhabited_infinite A).
  ltac1:(intuition auto).
Qed.

Class DecFinite A :=
  | dec_finite : finite A + infinite A.

#[program]
Definition infinite_nat : infinite nat :=
  λ l, exist _ (
    match @list_max_opt _ Nat.le _ _ l with
    | Some n => S n
    | None => 0
    end
  ) _.
Next Obligation.
  intros l. remember (@list_max_opt _ Nat.le _ _ l) as n eqn:H_n; symmetry in H_n. destruct n as [n |].
  - intros H. specialize (le_list_max_opt _ _ H_n) as H'_n. clear H_n. specialize (H'_n n) as (H'_n & _).
    specialize (H'_n (reflexivity _)). specialize (H'_n _ H). unfold le in H'_n. lia.
  - apply list_max_opt_none in H_n. subst l. auto.
Qed.

Instance dec_finite_nat : DecFinite nat := inr infinite_nat.

#[program]
Definition infinite_Z : infinite Z :=
  λ l, exist _ (
    match @list_max_opt _ Z.le _ _ l with
    | Some n => (n + 1)%Z
    | None => 0%Z
    end
  ) _.
Next Obligation.
  intros l. remember (@list_max_opt _ Z.le _ _ l) as n eqn:H_n; symmetry in H_n. destruct n as [n |].
  - intros H. specialize (le_list_max_opt _ _ H_n) as H'_n. clear H_n. specialize (H'_n n) as (H'_n & _).
    specialize (H'_n (reflexivity _)). specialize (H'_n _ H). unfold le in H'_n. lia.
  - apply list_max_opt_none in H_n. subst l. auto.
Qed.

Instance dec_finite_Z : DecFinite Z := inr infinite_Z.

Lemma option_map_option_map {A B C} :
  ∀ (g : B → C) (f : A → B) o,
  option_map g (option_map f o) = option_map (λ a, g (f a)) o.
Proof.
  intros g f o. destruct o; reflexivity.
Qed.

Lemma list_filter_list_filter {A} :
  ∀ g f (l : list A),
  List.filter g (List.filter f l) = List.filter (λ a, f a && g a) l.
Proof.
  intros g f l. induction l as [| a l' IH].
  - reflexivity.
  - simpl. destruct (f a); simpl; destruct (g a); simpl; congruence.
Qed.

Definition list_remove {A} {dec_eq_A : EqDec A eq} (x : A) l :=
  List.filter (λ y, negb (` (bool_of_sumbool (y == x)))) l.

Fixpoint list_sorted_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} (l : list A) :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as l') => (x ≤ y)%le ∧ ¬ (y ≤ x)%le ∧ list_sorted_nodup l'
  end.

Fixpoint list_insert_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {dec_le_R : DecLe R} (x : A) l :=
  match l with
  | [] => [x]
  | y :: l' =>
    if (x ≤? y)%le then
      if (y ≤? x)%le then
        y :: l'
      else
        x :: y :: l'
    else
      y :: (list_insert_nodup x l')
  end.

Definition list_sort_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {dec_le_R : DecLe R} (l : list A) :=
  List.fold_right list_insert_nodup [] l.

Lemma list_In_list_insert_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ (x : A) l y,
  List.In y (list_insert_nodup x l) ↔ List.In y l ∨ x = y.
Proof.
  intros x l y. induction l as [| z l' IH].
  - simpl. ltac1:(intuition auto).
  - simpl. destruct (x ≤? z)%le as [H_x_z | H_x_z].
    + destruct (z ≤? x)%le as [H_z_x | H_z_x].
      * assert (H : x = z). {
          apply partial_order_equivalence. split; auto.
        }
        subst z. simpl. ltac1:(intuition auto).
      * simpl. ltac1:(intuition auto).
    + simpl. rewrite IH. ltac1:(intuition auto).
Qed.

Lemma list_In_list_sort_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ (l : list A) x,
  List.In x (list_sort_nodup l) ↔ List.In x l.
Proof.
  intros l x. induction l as [| y l' IH].
  - simpl. reflexivity.
  - simpl. rewrite list_In_list_insert_nodup, IH. ltac1:(intuition auto).
Qed.

Lemma list_sorted_nodup_list_insert_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ (x : A) l,
  list_sorted_nodup l →
  list_sorted_nodup (list_insert_nodup x l).
Proof.
  intros x l H_l. induction l as [| y l' IH].
  - auto.
  - simpl in H_l |- *. destruct (x ≤? y)%le as [H_x_y | H_x_y].
    + destruct (y ≤? x)%le as [H_y_x | H_y_x].
      * simpl. auto.
      * simpl. repeat split; auto.
    + assert (H_y_x : (y ≤ x)%le). {
        destruct (totality y x) as [H | H].
        - auto.
        - exfalso. apply H_x_y. auto.
      }
      destruct l' as [| z l''].
      * simpl. repeat split; auto.
      * destruct H_l as (H_y_z & H_z_y & H_l'). specialize (IH H_l'). simpl in IH |- *. destruct (x ≤? z)%le as [H_x_z | H_x_z].
        -- destruct (z ≤? x)%le as [H_z_x | H_z_x].
           ++ split; auto.
           ++ remember (z :: l'') as l'; simpl; subst l'. repeat split; auto.
        -- repeat split; auto.
Qed.

Lemma list_sorted_nodup_list_sort_nodup {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ l : list A,
  list_sorted_nodup (list_sort_nodup l).
Proof.
  intros l. induction l as [| x l' IH].
  - simpl. auto.
  - simpl. apply list_sorted_nodup_list_insert_nodup. auto.
Qed.

Lemma list_sorted_nodup_impl_not_list_in {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} :
  ∀ (x : A) l,
  list_sorted_nodup (x :: l) →
  ∀ y,
  (y ≤ x)%le →
  ¬ (x ≤ y)%le →
  ¬ List.In y (x :: l).
Proof.
  intros x l. simpl. revert x. induction l as [| z l' IH]; intros x H_x_l y H_y_x H_x_y.
  - simpl. intros [<- | H_y]; auto.
  - destruct (H_x_l) as (H_x_z & H_z_x & H_z_l'). simpl in H_z_l' |- *. destruct l' as [| w l''].
    + intros [<- | [<- | H_y]]; auto.
    + destruct H_z_l' as (H_z_w & H_w_z & h_w_l''). intros [<- | [<- | H_y]].
      * auto.
      * auto.
      * assert (H_y_z : (y ≤ z)%le). {
          apply transitivity with x; auto.
        }
        assert (H_z_y : ¬ (z ≤ y)%le). {
          intros H_z_y.
          assert (H : z = y). {
            apply partial_order_equivalence. split; auto.
          }
          subst z. auto.
        }
        specialize (IH z ltac:(auto) y H_y_z H_z_y). apply IH. right. auto.
Qed.

Lemma list_sorted_nodup_impl_canonical {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} :
  ∀ (l_1 l_2 : list A),
  (∀ x, List.In x l_1 ↔ List.In x l_2) →
  list_sorted_nodup l_1 →
  list_sorted_nodup l_2 →
  l_1 = l_2.
Proof.
  intros l_1 l_2 H_in H_l_1 H_l_2. revert l_2 H_in H_l_2; induction l_1 as [| x_1 l_1' IH]; intros l_2 H_in H_l_2.
  - destruct l_2 as [| x_2 l_2'].
    + auto.
    + specialize (H_in x_2). simpl in H_in. ltac1:(intuition auto).
  - destruct l_2 as [| x_2 l_2'].
    + specialize (H_in x_1). simpl in H_in. ltac1:(intuition auto).
    + simpl in H_in, H_l_1, H_l_2. destruct l_1' as [| y_1 l_1''], l_2' as [| y_2 l_2''].
      * f_equal. specialize (H_in x_2). simpl in H_in. ltac1:(intuition auto).
      * simpl in H_in. specialize (H_in x_2) as H_1. specialize (H_in y_2) as H_2.
        assert (H : x_2 = y_2). {
          clear - H_1 H_2. apply proj2 in H_1. apply proj2 in H_2. ltac1:(intuition congruence).
        }
        subst y_2. assert (H : (x_2 ≤ x_2)%le) by reflexivity. clear - H_l_2 H; ltac1:(intuition auto).
      * simpl in H_in. specialize (H_in x_1) as H_1. specialize (H_in y_1) as H_2.
        assert (H : x_1 = y_1). {
          clear - H_1 H_2. apply proj1 in H_1. apply proj1 in H_2. ltac1:(intuition congruence).
        }
        subst y_1. assert (H : (x_1 ≤ x_1)%le) by reflexivity. clear - H_l_1 H; ltac1:(intuition auto).
      * destruct H_l_1 as (H_x_1_y_1 & H_y_1_x_1 & H_l_1'), H_l_2 as (H_x_2_y_2 & H_y_2_x_2 & H_l_2').
        assert (H_x_1_x_2 : x_1 = x_2). {
          destruct (classic (x_1 ≤ x_2)%le) as [H_x_1_x_2 | H_x_1_x_2], (classic (x_2 ≤ x_1)%le) as [H_x_2_x_1 | H_x_2_x_1].
          - apply partial_order_equivalence. split; auto.
          - assert (H : ¬ List.In x_1 (y_2 :: l_2'')). {
            apply list_sorted_nodup_impl_not_list_in.
            - auto.
            - apply transitivity with x_2; auto.
            - intros H_1. apply H_y_2_x_2. apply transitivity with x_1; auto.
          }
          specialize (H_in x_1). ltac1:(intuition auto).
          - assert (H : ¬ List.In x_2 (y_1 :: l_1'')). {
              apply list_sorted_nodup_impl_not_list_in.
              - auto.
              - apply transitivity with x_1; auto.
              - intros H_1. apply H_y_1_x_1. apply transitivity with x_2; auto.
            }
            specialize (H_in x_2). ltac1:(intuition auto).
          - exfalso. destruct (totality x_1 x_2); auto.
        }
        subst x_2.
        assert (H_1 : ¬ List.In x_1 (y_1 :: l_1'')). {
          apply list_sorted_nodup_impl_not_list_in; auto.
        }
        assert (H_2 : ¬ List.In x_1 (y_2 :: l_2'')). {
          apply list_sorted_nodup_impl_not_list_in; auto.
        }
        assert (H_in' : ∀ x, List.In x (y_1 :: l_1'') ↔ List.In x (y_2 :: l_2'')). {
          intros x. specialize (H_in x). destruct (classic (x_1 = x)) as [<- | H_x_1_x]; ltac1:(intuition auto).
        }
        specialize (IH H_l_1' _ H_in' H_l_2'). injection IH as <- IH. f_equal; f_equal; auto.
Qed.

Lemma list_sorted_nodup_list_filter {A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} :
  ∀ f (l : list A),
  list_sorted_nodup l →
  list_sorted_nodup (List.filter f l).
Proof.
  intros f l H_l. enough (H : list_sorted_nodup (List.filter f l) ∧ ∀ x l' y l_f', l = x :: l' → List.filter f l = y :: l_f' → (x ≤ y)%le).
  - ltac1:(intuition auto).
  - induction l as [| x l' IH].
    + simpl. ltac1:(intuition congruence).
    + simpl. destruct (f x); simpl in H_l |- *; destruct l' as [| y l''].
      * simpl. split.
        -- auto.
        -- intros ? ? ? ? H_1 H_2; injection H_1 as <- <-; injection H_2 as <- <-. reflexivity.
      * destruct H_l as (H_x_y & H_y_x & H_l'). specialize (IH H_l') as (IH_1 & IH_2). remember (List.filter f (y :: l'')) as l_f' eqn:H_l_f'. destruct l_f' as [| z l_f''].
        -- split.
           ++ auto.
           ++ intros ? ? ? ? H_1 H_2; injection H_1 as <- <-; injection H_2 as <- <-. reflexivity.
        -- specialize (IH_2 y l'' z l_f'' eq_refl eq_refl). split > [repeat split |].
           ++ apply transitivity with y; auto.
           ++ intros H_z_y. apply H_y_x. apply transitivity with z; auto.
           ++ auto.
           ++ intros ? ? ? ? H_1 H_2; injection H_1 as <- <-; injection H_2 as <- <-. reflexivity.
      * simpl. split.
        -- auto.
        -- congruence.
      * destruct H_l as (H_x_y & H_y_x & H_l'). specialize (IH H_l') as (IH_1 & IH_2). split.
        -- auto.
        -- intros ? ? z l_f'' H_1 H_2; injection H_1 as <- <-. specialize (IH_2 y l'' z l_f'' eq_refl H_2).
           apply transitivity with y; auto.
Qed.

Lemma list_In_list_remove {A} {dec_eq_A : EqDec A eq} :
  ∀ (x : A) l y,
  List.In y (list_remove x l) ↔ List.In y l ∧ y ≠ x.
Proof.
  intros x l y. unfold list_remove. rewrite List.filter_In. destruct (y == x) as [<- | H_y_x]; simpl.
  - ltac1:(intuition congruence).
  - ltac1:(intuition auto).
Qed.

Lemma list_sorted_nodup_list_remove {A} {dec_eq_A : EqDec A eq} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ (x : A) l,
  list_sorted_nodup l →
  list_sorted_nodup (list_remove x l).
Proof.
  intros x l H_l. apply list_sorted_nodup_list_filter. auto.
Qed.

Inductive mem_index {A} (a : A) : list A → Type :=
  | MIO : ∀ l', mem_index a (a :: l')
  | MIS : ∀ b l', mem_index a l' → mem_index a (b :: l').
Arguments MIO {A a l'}.
Arguments MIS {A a b l'}.

Instance dec_eq_mem_index {A} {dec_eq_A : EqDec A eq} (a : A) l : EqDec (mem_index a l) eq.
Proof.
  rewrite dec_eq_def.
  intros mi_1; induction mi_1 as [l'_1 | b_1 l'_1 mi'_1 IH]; intros mi_2; ltac1:(dependent elimination mi_2 as [@MIO l'_2 | @MIS b_2 l'_2 mi'_2]); try (right; congruence).
  - left; reflexivity.
  - specialize (IH mi'_2). destruct IH as [<- | IH].
    + left; reflexivity.
    + right. intros H. apply IH. injection H as H. apply inj_right_pair in H. auto.
Defined.

Check MIS (MIS (MIS MIO)).

Definition dec_eq_list_In {A} {dec_eq_A : EqDec A eq} (a : A) l : mem_index a l + (¬ List.In a l).
Proof.
  induction l as [| a' l' IH]; simpl.
  - right. auto.
  - destruct (a' == a) as [-> | H_a'].
    + left. apply MIO.
    + destruct IH as [mi | IH].
      * left. apply MIS, mi.
      * right. ltac1:(intuition auto).
Defined.

Definition stabilizing {A B} (f : A → B) keys :=
  ¬ inhabited A ∨ ∃ b, ∀ a, List.In a keys ∨ f a = b.

Record stabilizing_fun A B := {
  stabilizing_fun_f :> A → B;
  stabilizing_fun_keys : list A;
  stabilizing_fun_default : option B;
  stabilizing_fun_stabilizing_f : stabilizing stabilizing_fun_f stabilizing_fun_keys;
}.
Arguments stabilizing_fun_f {A B}.
Arguments stabilizing_fun_keys {A B}.
Arguments stabilizing_fun_default {A B}.
Arguments stabilizing_fun_stabilizing_f {A B}.

Notation "A  '→₀'  B" := (stabilizing_fun A B) (at level 99, right associativity) : type_scope.

Lemma irrelevant_stabilizing_fun {A B} :
  ∀ f g : A →₀ B,
  stabilizing_fun_f f = stabilizing_fun_f g →
  stabilizing_fun_keys f = stabilizing_fun_keys g →
  stabilizing_fun_default f = stabilizing_fun_default g →
  f = g.
Proof.
  intros f g H_f H_keys H_default. destruct f as [f f_keys f_default stabilizing_f], g as [g g_keys g_default stabilizing_g].
  simpl in H_f, H_keys, H_default. destruct H_f, H_keys, H_default. f_equal. apply proof_irrelevance.
Qed.

Definition dec_eq_stabilizing_fun_minimal {A B} {dec_finite_A : DecFinite A} {dec_eq_A : EqDec A eq} (f g : A →₀ B) (dec_eq_f : ∀ a, {f a = g a} + {f a ≠ g a}) (dec_eq_f_default : {stabilizing_fun_default f = stabilizing_fun_default g} + {stabilizing_fun_default f ≠ stabilizing_fun_default g}) : {f = g} + {f ≠ g}.
Proof.
  destruct f as [f f_keys f_default stabilizing_f], g as [g g_keys g_default stabilizing_g]; simpl in dec_eq_f, dec_eq_f_default.
  assert (dec_eq_list_map_f : ∀ l, {List.map f l = List.map g l} + {List.map f l ≠ List.map g l}). {
    intros l. induction l as [| a l' IH].
    - left. auto.
    - simpl. destruct IH as [IH | IH] > [destruct (dec_eq_f a) as [H_a | H_a] |]; constructor; congruence.
  }
  destruct (f_keys == g_keys) as [H_keys | H_keys], dec_eq_f_default as [H_default | H_default]; try (right; congruence).
  destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
  - pose (f_values := List.map f list_A); pose (g_values := List.map g list_A).
    destruct (dec_eq_list_map_f list_A) as [H_values | H_values].
    + left. destruct H_keys, H_default.
      assert (H_f : f = g). {
        apply functional_extensionality. intros a. specialize (H_list_A a).
        induction list_A as [| a' list_A' IH].
        - exfalso. auto.
        - injection H_values as H_a' H_values. destruct H_list_A as [-> | H_list_A].
          + auto.
          + auto.
      }
      apply irrelevant_stabilizing_fun; auto.
    + right. ltac1:(intros [=H_f]). apply H_values; clear H_list_A H_values. induction list_A as [| a list_A' IH].
      * reflexivity.
      * change (f_values = g_values). subst f_values g_values. simpl. f_equal.
        -- apply equal_f; auto.
        -- auto.
  - pose (f_values := List.map f f_keys); pose (g_values := List.map g f_keys).
    pose (b_f := f (` (infinite_A f_keys))). pose (b_g := g (` (infinite_A f_keys))).
    destruct (dec_eq_list_map_f f_keys) as [H_values | H_values] > [destruct (dec_eq_f (` (infinite_A f_keys))) as [H_b | H_b] |].
    + left. destruct H_keys, H_default. change (b_f = b_g) in H_b.
      assert (H_f : f = g). {
        apply functional_extensionality. intros a. clear dec_eq_list_map_f.
        revert f stabilizing_f f_values b_f g stabilizing_g g_values b_g dec_eq_f H_values H_b; induction f_keys as [| a' f_keys' IH]; intros f stabilizing_f f_values b_f g stabilizing_g g_values b_g dec_eq_f H_values H_b.
        - destruct stabilizing_f as [H_f | (b_stabilizing_f & H_b_stabilizing_f)] > [| destruct stabilizing_g as [H_g | (b_stabilizing_g & H_b_stabilizing_g)]].
          + exfalso. apply H_f. exists. auto.
          + exfalso. apply H_g. exists. auto.
          + ltac1:(replace b_stabilizing_f with (f (` (infinite_A []))) in *; revgoals). {
              destruct (infinite_A []) as (a' & H_a'). simpl. specialize (H_b_stabilizing_f a'). ltac1:(intuition congruence).
            }
            ltac1:(replace b_stabilizing_g with (g (` (infinite_A []))) in *; revgoals). {
              destruct (infinite_A []) as (a' & H_a'). simpl. specialize (H_b_stabilizing_g a'). ltac1:(intuition congruence).
            }
            specialize (H_b_stabilizing_f a) as [[] | H_b_stabilizing_f]; specialize (H_b_stabilizing_g a) as [[] | H_b_stabilizing_g]. rewrite H_b_stabilizing_f, H_b_stabilizing_g. auto.
        - destruct stabilizing_f as [H_f | (b_stabilizing_f & H_b_stabilizing_f)] > [| destruct stabilizing_g as [H_g | (b_stabilizing_g & H_b_stabilizing_g)]].
          + exfalso. apply H_f. exists. auto.
          + exfalso. apply H_g. exists. auto.
          + pose (f' := λ a, if @equiv_dec _ _ _ dec_eq_A a a' then b_f else f a).
            pose (g' := λ a, if @equiv_dec _ _ _ dec_eq_A a a' then b_f else g a).
            injection H_values as H_a' H_values.
            assert (H_values' : List.map f' f_keys' = List.map g' f_keys'). {
              clear IH b_stabilizing_f H_b_stabilizing_f b_stabilizing_g H_b_stabilizing_g. clear b_g H_b; ltac1:(clearbody b_f). induction f_keys' as [| a'' f_keys'' IH'].
              - auto.
              - injection H_values as H_a'' H_values'. simpl. f_equal.
                + subst f' g'; simpl. destruct (a'' == a'); auto.
                + apply IH'; auto.
            }
            assert (stabilizing_f' : stabilizing f' f_keys'). {
              right. exists b_stabilizing_f. intros a''. subst f'; simpl. destruct (a'' == a') as [-> | H_a''].
              - right. subst b_f. destruct (infinite_A (a' :: f_keys')) as (a'' & H_a''). simpl. specialize (H_b_stabilizing_f a''). ltac1:(intuition congruence).
              - specialize (H_b_stabilizing_f a''); simpl in H_b_stabilizing_f. ltac1:(intuition congruence).
            }
            assert (stabilizing_g' : stabilizing g' f_keys'). {
              right. exists b_stabilizing_g. intros a''. subst g'; simpl. destruct (a'' == a') as [-> | H_a''].
              - right. subst b_g. destruct (infinite_A (a' :: f_keys')) as (a'' & H_a''). simpl. specialize (H_b_stabilizing_g a''). rewrite H_b. ltac1:(intuition congruence).
              - specialize (H_b_stabilizing_g a''); simpl in H_b_stabilizing_g. ltac1:(intuition congruence).
            }
            assert (dec_eq_f' : ∀ a, {f' a = g' a} + {f' a ≠ g' a}). {
              intros a''. subst f' g'; simpl. destruct (a'' == a') as [-> | _].
              - left. auto.
              - apply dec_eq_f.
            }
            assert (H_b' : f' (` (infinite_A f_keys')) = g' (` (infinite_A f_keys'))). {
              subst f' g'; simpl. destruct (` (infinite_A f_keys') == a') as [_ | H_a''].
              - auto.
              - ltac1:(replace b_stabilizing_f with b_f in *; revgoals). {
                  destruct (infinite_A (a' :: f_keys')) as (a''' & H_a'''). simpl. specialize (H_b_stabilizing_f a'''). ltac1:(intuition congruence).
                }
                ltac1:(replace b_stabilizing_g with b_g in *; revgoals). {
                  destruct (infinite_A (a' :: f_keys')) as (a''' & H_a'''). simpl. specialize (H_b_stabilizing_g a'''). ltac1:(intuition congruence).
                }
                specialize (H_b_stabilizing_f (` (infinite_A f_keys'))); specialize (H_b_stabilizing_g (` (infinite_A f_keys'))). destruct (infinite_A f_keys') as (a''' & H_a'''). simpl in H_b_stabilizing_f, H_b_stabilizing_g, H_a'' |- *.
                ltac1:(intuition congruence).
            }
            specialize (IH f' stabilizing_f' g' stabilizing_g' dec_eq_f' H_values' H_b'). subst f' g'; simpl in IH.
            destruct (a == a') as [<- | _]; auto.
      }
      apply irrelevant_stabilizing_fun; auto.
    + right. ltac1:(intros [=H_f]). apply H_b. apply equal_f; auto.
    + right. destruct H_keys, H_default. ltac1:(intros [=H_f]). apply H_values; clear stabilizing_f stabilizing_g H_values. induction f_keys as [| a f_keys' IH].
      * reflexivity.
      * change (f_values = g_values). subst f_values g_values. simpl. f_equal.
        -- apply equal_f; auto.
        -- auto.
Defined.

Instance dec_eq_stabilizing_fun {A B} {dec_finite_A : DecFinite A} {dec_eq_A : EqDec A eq} {dec_eq_B : EqDec B eq} : EqDec (A →₀ B) eq.
Proof.
  rewrite dec_eq_def. intros f g. apply dec_eq_stabilizing_fun_minimal.
  - intros a. apply (f a == g a).
  - apply (stabilizing_fun_default f == stabilizing_fun_default g).
Defined.

Definition stabilizing_fun_canonical {A B} {R : A → A → Prop} {pre_order_R : PreOrder R} (f : A →₀ B) :=
  list_sorted_nodup (stabilizing_fun_keys f) ∧
  match stabilizing_fun_default f with
  | None => inhabited (finite A) ∧ ∀ a, List.In a (stabilizing_fun_keys f)
  | Some b => ¬ inhabited (finite A) ∧ ∀ a, f a ≠ b ↔ List.In a (stabilizing_fun_keys f)
  end.

#[program]
Definition stabilizing_fun_canonize {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} (f : A →₀ B) := {|
  stabilizing_fun_f := stabilizing_fun_f f;
  stabilizing_fun_keys :=
    match @dec_finite A _ with
    | inl finite_A => list_sort_nodup (` finite_A)
    | inr infinite_A =>
      list_sort_nodup (
        List.filter
          (λ a, negb (` (bool_of_sumbool (f a == f (` (infinite_A (stabilizing_fun_keys f)))))))
          (stabilizing_fun_keys f)
      )
    end;
  stabilizing_fun_default :=
    match @dec_finite A _ with
    | inl _ => None
    | inr infinite_A => Some (f (` (infinite_A (stabilizing_fun_keys f))))
    end;
|}.
Next Obligation.
  intros A B dec_finite_A R pre_order_R partial_order_R total_R dec_le_R dec_eq_B f. destruct f as [f f_keys f_default stabilizing_f].
  unfold stabilizing in stabilizing_f |- *. simpl. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
  - simpl. destruct (classic (inhabited A)) as [[a_any] | H_A].
    + right. exists (f a_any). intros a. left. rewrite list_In_list_sort_nodup. auto.
    + left. auto.
  - destruct stabilizing_f as [H_A | (b & H_b)].
    + left. auto.
    + ltac1:(replace (f (` (infinite_A f_keys))) with b; revgoals). {
        destruct (infinite_A f_keys) as (a' & H_a'). simpl. specialize (H_b a'). ltac1:(intuition congruence).
      }
      right. exists b. intros a. rewrite list_In_list_sort_nodup, List.filter_In. destruct (H_b a) as [H_a | <-].
      * destruct (f a == b) as [<- | H_f_a].
        -- right. auto.
        -- left. simpl. repeat split. auto.
      * right. auto.
Qed.

Lemma stabilizing_fun_canonical_stabilizing_fun_canonize {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} :
  ∀ f : A →₀ B,
  stabilizing_fun_canonical (stabilizing_fun_canonize f).
Proof.
  intros f. unfold stabilizing_fun_canonize, stabilizing_fun_canonical. destruct f as [f f_keys f_default stabilizing_f]. simpl. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
  - simpl. split > [| split].
    + apply list_sorted_nodup_list_sort_nodup.
    + exists. exists list_A. auto.
    + intros a. rewrite list_In_list_sort_nodup. auto.
  - simpl. split > [| split].
    + apply list_sorted_nodup_list_sort_nodup.
    + rewrite not_inhabited_finite_equiv_not_inhabited_infinite. exists. auto.
    + intros a. rewrite list_In_list_sort_nodup, List.filter_In. destruct stabilizing_f as [H_A | (b & H_b)].
      * exfalso. apply H_A. exists. auto.
      * ltac1:(replace (f (` (infinite_A f_keys))) with b; revgoals). {
          destruct (infinite_A f_keys) as (a' & H_a'). simpl. specialize (H_b a'). ltac1:(intuition congruence).
        }
        specialize (H_b a). destruct (f a == b) as [<- | H_f_a]; simpl; ltac1:(intuition (auto; congruence)).
Qed.

Lemma stabilizing_fun_canonical_impl_canonical {A B} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} :
  ∀ f g : A →₀ B,
  stabilizing_fun_f f = stabilizing_fun_f g →
  stabilizing_fun_canonical f →
  stabilizing_fun_canonical g →
  f = g.
Proof.
  intros f g H_f canonical_f canonical_g. unfold stabilizing_fun_canonical in canonical_f, canonical_g.
  destruct f as [f f_keys f_default stabilizing_f], g as [g g_keys g_default stabilizing_g]. simpl in H_f, canonical_f, canonical_g.
  assert (H_keys_default : f_keys = g_keys ∧ f_default = g_default). {
    destruct f_default as [f_b |], g_default as [g_b |].
    + destruct canonical_f as (H_f_keys & H_f_A & H_f_a), canonical_g as (H_g_keys & H_g_A & H_g_a).
      assert (H_b : f_b = g_b). {
        apply NNPP. intros H_f_b_g_b. apply H_f_A. exists. exists (f_keys ++ g_keys). intros a.
        specialize (H_f_a a). specialize (H_g_a a). apply equal_f with a in H_f.
        rewrite List.in_app_iff. destruct (classic (f a = f_b)) as [<- | H_f_b], (classic (g a = g_b)) as [<- | H_g_b].
        - exfalso. auto.
        - right. rewrite <- H_g_a. auto.
        - left. rewrite <- H_f_a. auto.
        - left. rewrite <- H_f_a. auto.
      }
      assert (H_keys : ∀ a, List.In a f_keys ↔ List.In a g_keys). {
        intros a. specialize (H_f_a a). specialize (H_g_a a). apply equal_f with a in H_f. rewrite <- H_f_a, <- H_g_a. ltac1:(intuition congruence).
      }
      split.
      * apply list_sorted_nodup_impl_canonical; auto.
      * f_equal. auto.
    + destruct canonical_f as (H_f_keys & H_f_A & H_f_a). exfalso. ltac1:(intuition auto).
    + destruct canonical_g as (H_g_keys & H_g_A & H_g_a). exfalso. ltac1:(intuition auto).
    + split.
      * destruct canonical_f as (H_f_keys & H_f_A & H_f_a), canonical_g as (H_g_keys & H_g_A & H_g_a).
        apply list_sorted_nodup_impl_canonical; ltac1:(intuition auto).
      * auto.
  }
  apply irrelevant_stabilizing_fun; simpl.
  - auto.
  - ltac1:(intuition auto).
  - ltac1:(intuition auto).
Qed.

Definition dec_stabilizing_fun_canonical {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} :
  ∀ f : A →₀ B,
  {stabilizing_fun_canonical f} + {¬ stabilizing_fun_canonical f}.
Proof.
  intros f. destruct (f == stabilizing_fun_canonize f) as [H_f | H_f].
  - left. rewrite H_f. apply stabilizing_fun_canonical_stabilizing_fun_canonize.
  - right. intros H. apply H_f. apply stabilizing_fun_canonical_impl_canonical.
    + auto.
    + auto.
    + apply stabilizing_fun_canonical_stabilizing_fun_canonize.
Defined.

#[program]
Definition stabilizing_fun_const {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} b : A →₀ B := {|
  stabilizing_fun_f := λ _, b;
  stabilizing_fun_keys :=
    match @dec_finite A _ with
    | inl finite_A => list_sort_nodup (` finite_A)
    | inr _ => []
    end;
  stabilizing_fun_default :=
    if @dec_finite A _ then
      None
    else
      Some b;
|}.
Next Obligation.
  intros A B dec_finite_A R pre_order_R partial_order_R total_R dec_le_R b. unfold stabilizing.
  destruct (@dec_finite A _) as [(list_A & H_list_A) | _].
  - simpl. right. exists b. intros a. rewrite list_In_list_sort_nodup. ltac1:(intuition auto).
  - simpl. right. exists b. right. auto.
Qed.

#[program]
Definition stabilizing_fun_update {A B} {dec_finite_A : DecFinite A} {dec_eq_A : EqDec A eq} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} (f : A →₀ B) a b : A →₀ B := {|
  stabilizing_fun_f := λ a', if a' == a then b else f a';
  stabilizing_fun_keys :=
    match @dec_finite A _ with
    | inl _ => list_insert_nodup a (stabilizing_fun_keys f)
    | inr infinite_A =>
      if b == f (` (infinite_A (stabilizing_fun_keys f))) then
        list_remove a (stabilizing_fun_keys f)
      else
        list_insert_nodup a (stabilizing_fun_keys f)
    end;
  stabilizing_fun_default := stabilizing_fun_default f;
|}.
Next Obligation.
  intros A B dec_finite_A dec_eq_A R pre_order_R partial_order_R total_R dec_le_R dec_eq_B f a b. destruct f as [f f_keys f_default stabilizing_f].
  simpl. unfold stabilizing in stabilizing_f |- *. destruct stabilizing_f as [H | (b_stabilizing & H_b_stabilizing)].
  - left. auto.
  - right. exists b_stabilizing. intros a'. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
    + rewrite list_In_list_insert_nodup. destruct (a' == a) as [-> | _].
      * left. right. auto.
      * specialize (H_b_stabilizing a'). ltac1:(intuition auto).
    + ltac1:(replace (f (` (infinite_A f_keys))) with b_stabilizing; revgoals). {
        destruct (infinite_A f_keys) as (a'' & H_a''). simpl. specialize (H_b_stabilizing a''). ltac1:(intuition congruence).
      }
      destruct (b == b_stabilizing) as [-> | H_b].
      * rewrite list_In_list_remove. specialize (H_b_stabilizing a'). destruct (a' == a) as [-> | H_a']; ltac1:(intuition auto).
      * rewrite list_In_list_insert_nodup. specialize (H_b_stabilizing a'). destruct (a' == a) as [-> | H_a']; ltac1:(intuition auto).
Qed.

#[program]
Definition stabilizing_fun_update_default {A B} {dec_finite_A : DecFinite A} {dec_eq_B : EqDec B eq} (f : A →₀ B) b : A →₀ B := {|
  stabilizing_fun_f := λ a,
    match @dec_finite A _ with
    | inl _ => f a
    | inr infinite_A =>
      if f a == f (` (infinite_A (stabilizing_fun_keys f))) then
        b
      else
        f a
    end;
  stabilizing_fun_keys :=
    match @dec_finite A _ with
    | inl _ => stabilizing_fun_keys f
    | inr infinite_A =>
      List.filter (λ a, ` (bool_of_sumbool (f a == f (` (infinite_A (stabilizing_fun_keys f))))) || negb (` (bool_of_sumbool (f a == b)))) (stabilizing_fun_keys f)
    end;
  stabilizing_fun_default :=
    match @dec_finite A _ with
    | inl _ => stabilizing_fun_default f
    | inr infinite_A =>
      if stabilizing_fun_default f == Some (f (` (infinite_A (stabilizing_fun_keys f)))) then
        Some b
      else
        stabilizing_fun_default f
    end
|}.
Next Obligation.
  intros A B dec_finite_A dec_eq_B f b. destruct f as [f f_keys f_default stabilizing_f].
  simpl. unfold stabilizing in stabilizing_f |- *. destruct stabilizing_f as [H | (b_stabilizing & H_b_stabilizing)].
  - left. auto.
  - right. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
    + exists b_stabilizing. auto.
    + exists b. intros a. rewrite List.filter_In.
      ltac1:(replace (f (` (infinite_A f_keys))) with b_stabilizing; revgoals). {
        destruct (infinite_A f_keys) as (a'' & H_a''). simpl. specialize (H_b_stabilizing a''). ltac1:(intuition congruence).
      }
      destruct (f a == b_stabilizing) as [H_1_f_a | H_1_f_a] > [| destruct (f a == b) as [H_2_f_a | H_2_f_a]]; simpl.
      * ltac1:(intuition auto).
      * ltac1:(intuition auto).
      * specialize (H_b_stabilizing a). ltac1:(intuition congruence).
Qed.

Axiom stabilizing_fun_const_erased : ∀ {A B} (b : B), A →₀ B.

Axiom stabilizing_fun_update_erased : ∀ {A B} (f : A →₀ B) (a : A) (b : B), A →₀ B.

Axiom stabilizing_fun_update_default_erased : ∀ {A B} (f : A →₀ B) (b : B), A →₀ B.

Declare Scope stabilizing_fun_scope.
Delimit Scope stabilizing_fun_scope with stabilizing_fun.
Bind Scope stabilizing_fun_scope with stabilizing_fun.
Open Scope stabilizing_fun_scope.

Notation "'_' '↦₀' b" := (stabilizing_fun_const b) (at level 10, b at level 69, format "'[' '_'  '↦₀'  b ']'") : stabilizing_fun_scope.
Notation "( '_' : A ) '↦₀' b" := (@stabilizing_fun_const A _ _ _ _ _ _ _ b) (at level 0, b at level 69, format "'[' '(' '_'  ':'  A ')'  '↦₀'  b ']'") : stabilizing_fun_scope.
Notation "a '↦₀' b ',' f" := (stabilizing_fun_update f a b) (at level 70, b at level 69, f at level 200, format "'[' a  '↦₀'  b ',' '/' f ']'") : stabilizing_fun_scope.
Notation "'_' '↦₀' b ',' f" := (stabilizing_fun_update_default f b) (at level 10, b at level 69, f at level 200, format "'[' '_'  '↦₀'  b ',' '/' f ']'") : stabilizing_fun_scope.

Notation "'_' '↦₀ₑ' b" := (stabilizing_fun_const_erased b) (at level 10, b at level 69, format "'[' '_'  '↦₀ₑ'  b ']'") : stabilizing_fun_scope.
Notation "( '_' : A ) '↦₀ₑ' b" := (@stabilizing_fun_const_erased A _ b) (at level 0, b at level 69, format "'[' '(' '_'  ':'  A ')'  '↦₀ₑ'  b ']'") : stabilizing_fun_scope.
Notation "a '↦₀ₑ' b ',' f" := (stabilizing_fun_update_erased f a b) (at level 70, b at level 69, f at level 200, format "'[' a  '↦₀ₑ'  b ',' '/' f ']'") : stabilizing_fun_scope.
Notation "'_' '↦₀ₑ' b ',' f" := (stabilizing_fun_update_default_erased f b) (at level 10, b at level 69, f at level 200, format "'[' '_'  '↦₀ₑ'  b ',' '/' f ']'") : stabilizing_fun_scope.

Lemma stabilizing_fun_canonical_stabilizing_fun_const {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} :
  ∀ b : B,
  stabilizing_fun_canonical ((_ : A) ↦₀ b).
Proof.
  intros b. unfold stabilizing_fun_canonical. simpl. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
  - simpl. split > [| split].
    + apply list_sorted_nodup_list_sort_nodup.
    + exists. exists list_A. auto.
    + intros a. rewrite list_In_list_sort_nodup. auto.
  - simpl. split > [| split].
    + auto.
    + rewrite not_inhabited_finite_equiv_not_inhabited_infinite. exists. auto.
    + ltac1: (intuition congruence).
Qed.

Lemma stabilizing_fun_canonical_stabilizing_fun_update {A B} {dec_finite_A : DecFinite A} {dec_eq_A : EqDec A eq} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} :
  ∀ (f : A →₀ B) a b,
  stabilizing_fun_canonical f →
  stabilizing_fun_canonical (a ↦₀ b, f).
Proof.
  intros f a b canonical_f. unfold stabilizing_fun_canonical in canonical_f |- *. destruct f as [f f_keys f_default stabilizing_f]. simpl in canonical_f |- *. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A], f_default as [b_default |], canonical_f as (H_f_keys & H_f_A & H_f_a).
  - exfalso. apply H_f_A. exists. exists list_A. auto.
  - split > [| split].
    + apply list_sorted_nodup_list_insert_nodup. auto.
    + exists. exists list_A. auto.
    + intros a'. rewrite list_In_list_insert_nodup. left. auto.
  - ltac1:(replace (f (` (infinite_A f_keys))) with b_default; revgoals). {
      destruct (infinite_A f_keys) as (a'' & H_a''). simpl. specialize (H_f_a a''). apply NNPP. ltac1:(intuition auto).
    }
    destruct (b == b_default) as [-> | H_b].
    + split > [| split].
      * apply list_sorted_nodup_list_remove. auto.
      * rewrite not_inhabited_finite_equiv_not_inhabited_infinite. exists. auto.
      * intros a'. rewrite list_In_list_remove. destruct (a' == a) as [H_a' | H_a'].
        -- ltac1:(intuition auto).
        -- specialize (H_f_a a'). ltac1:(intuition auto).
    + split > [| split].
      * apply list_sorted_nodup_list_insert_nodup. auto.
      * rewrite not_inhabited_finite_equiv_not_inhabited_infinite. exists. auto.
      * intros a'. rewrite list_In_list_insert_nodup. destruct (a' == a) as [H_a' | H_a'].
        -- ltac1:(intuition auto).
        -- specialize (H_f_a a'). ltac1:(intuition congruence).
  - exfalso. destruct H_f_A as [H_f_A]. apply (not_finite_and_infinite A); auto.
Qed.

Lemma stabilizing_fun_canonical_stabilizing_fun_update_default {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} :
  ∀ (f : A →₀ B) b,
  stabilizing_fun_canonical f →
  stabilizing_fun_canonical (_ ↦₀ b, f).
Proof.
  intros f b canonical_f. unfold stabilizing_fun_canonical in canonical_f |- *. destruct f as [f f_keys f_default stabilizing_f]. simpl in canonical_f |- *. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A], f_default as [b_default |], canonical_f as (H_f_keys & H_f_A & H_f_a).
  - exfalso. apply H_f_A. exists. exists list_A. auto.
  - ltac1:(intuition auto).
  - ltac1:(replace (f (` (infinite_A f_keys))) with b_default; revgoals). {
      destruct (infinite_A f_keys) as (a'' & H_a''). simpl. specialize (H_f_a a''). apply NNPP. ltac1:(intuition auto).
    }
    destruct (Some b_default == Some b_default) as [_ |] > [| congruence]. split > [| split].
    + apply list_sorted_nodup_list_filter. auto.
    + auto.
    + intros a. rewrite List.filter_In. specialize (H_f_a a). destruct (f a == b_default) as [H_1_f_a | H_1_f_a] > [| destruct (f a == b) as [H_2_f_a | H_2_f_a]]; simpl; ltac1:(intuition congruence).
  - exfalso. destruct H_f_A as [H_f_A]. apply (not_finite_and_infinite A); auto.
Qed.

#[program]
Definition stabilizing_fun_map_minimal {A B C} {dec_finite_A : DecFinite A} {dec_eq_B : EqDec B eq} {dec_eq_C : EqDec C eq} (g_f : A → C) (g_f_default : option C) (f : A →₀ B) (H_g_f : ∀ a_1 a_2, f a_1 = f a_2 → g_f a_1 = g_f a_2) : A →₀ C := {|
  stabilizing_fun_f := g_f;
  stabilizing_fun_keys :=
    match @dec_finite A _ with
    | inl _ => stabilizing_fun_keys f
    | inr infinite_A =>
      List.filter (λ a, ` (bool_of_sumbool (f a == f (` (infinite_A (stabilizing_fun_keys f))))) || negb (` (bool_of_sumbool (g_f a == g_f (` (infinite_A (stabilizing_fun_keys f))))))) (stabilizing_fun_keys f)
    end;
  stabilizing_fun_default := g_f_default;
|}.
Next Obligation.
  intros A B C dec_finite_A dev_eq_B dec_eq_C g_f g_f_default f H_g_f. destruct f as [f f_keys f_default stabilizing_f]. simpl in H_g_f |- *.
  unfold stabilizing in stabilizing_f |- *. destruct stabilizing_f as [H | (b_stabilizing & H_b_stabilizing)].
  - left. auto.
  - destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
    + destruct (classic (∃ a_stabilizing, f a_stabilizing = b_stabilizing)) as [(a_stabilizing & <-) | H_a_stabilizing].
      * right. exists (g_f a_stabilizing). intros a. specialize (H_b_stabilizing a); specialize (H_g_f a a_stabilizing). ltac1:(intuition congruence).
      * destruct list_A as [| a_any list_A'].
        -- left. intros [a]. simpl in H_list_A. auto.
        -- right. exists (g_f a_any). intros a. specialize (H_b_stabilizing a); specialize (H_g_f a a_any). apply not_ex_all_not with _ _ a in H_a_stabilizing. ltac1:(intuition congruence).
    + ltac1:(replace b_stabilizing with (f (` (infinite_A f_keys))) in H_b_stabilizing; revgoals). {
        destruct (infinite_A f_keys) as (a' & H_a'). simpl. specialize (H_b_stabilizing a'). ltac1:(intuition congruence).
      }
      right. exists (g_f (` (infinite_A f_keys))). intros a.
      rewrite List.filter_In. specialize (H_b_stabilizing a). specialize (H_g_f a (` (infinite_A f_keys))). destruct (f a == f (` (infinite_A f_keys))) as [H_f_a | H_f_a], (g_f a == g_f (` (infinite_A f_keys))) as [H_g_f_a | H_g_f_a]; simpl; ltac1:(intuition congruence).
Qed.

Definition stabilizing_fun_map {A B C} {dec_finite_A : DecFinite A} {dec_eq_B : EqDec B eq} {dec_eq_C : EqDec C eq} (g : B → C) (f : A →₀ B) : A →₀ C :=
  stabilizing_fun_map_minimal (λ a, g (f a)) (option_map g (stabilizing_fun_default f)) f (λ a_1 a_2 H, f_equal _ H).

Lemma stabilizing_fun_canonical_stabilizing_fun_map {A B C} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_eq_B : EqDec B eq} {dec_eq_C : EqDec C eq} :
  ∀ (g : B → C) (f : A →₀ B),
  stabilizing_fun_canonical f →
  stabilizing_fun_canonical (stabilizing_fun_map g f).
Proof.
  intros g f canonical_f. unfold stabilizing_fun_canonical in canonical_f |- *. destruct f as [f f_keys f_default stabilizing_f]. simpl in canonical_f |- *. destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A], f_default as [b_default |], canonical_f as (H_f_keys & H_f_A & H_f_a).
  - exfalso. apply H_f_A. exists. exists list_A. auto.
  - simpl. ltac1:(intuition auto).
  - simpl. split > [| split].
    + apply list_sorted_nodup_list_filter; auto.
    + auto.
    + intros a.
      ltac1:(replace (f (` (infinite_A f_keys))) with b_default; revgoals). {
        destruct (infinite_A f_keys) as (a' & H_a'). simpl. specialize (H_f_a a'). apply NNPP. ltac1:(intuition congruence).
      }
      rewrite List.filter_In. specialize (H_f_a a). destruct (f a == b_default) as [H_f_a' | H_f_a'], (g (f a) == g b_default) as [H_g_f_a | H_g_f_a]; simpl; ltac1:(intuition congruence).
  - exfalso. destruct H_f_A as [H_f_A]. apply (not_finite_and_infinite A); auto.
Qed.

Lemma stabilizing_fun_map_id {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_eq_B_1 : EqDec B eq} {dec_eq_B_2 : EqDec B eq} :
  ∀ (g : B → B) (f : A →₀ B),
  (∀ a, g (f a) = f a) →
  option_map g (stabilizing_fun_default f) = stabilizing_fun_default f →
  @stabilizing_fun_map _ _ _ _ dec_eq_B_1 dec_eq_B_2 g f = f.
Proof.
  intros g f H_g_f H_g_default.
  ltac1:(replace dec_eq_B_2 with dec_eq_B_1 in *; revgoals). {
    apply functional_extensionality_dep; intros b_1; apply functional_extensionality_dep; intros b_2. destruct (dec_eq_B_1 b_1 b_2), (dec_eq_B_2 b_1 b_2); try (congruence); f_equal; apply proof_irrelevance.
  }
  destruct f as [f f_keys f_default stabilizing_f]. simpl in H_g_f, H_g_default |- *. apply irrelevant_stabilizing_fun; simpl.
  - apply functional_extensionality; intros a. rewrite H_g_f. reflexivity.
  - destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
    + reflexivity.
    + rewrite <- List.filter_true. f_equal. apply functional_extensionality; intros a. rewrite ! H_g_f.  destruct (f a == f (` (infinite_A f_keys))); reflexivity.
  - rewrite H_g_default. reflexivity.
Qed.

Lemma stabilizing_fun_map_stabilizing_fun_map {A B C D} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_eq_B : EqDec B eq} {dec_eq_C : EqDec C eq} {dec_eq_D : EqDec D eq} :
  ∀ (h : C → D) (g : B → C) (f : A →₀ B),
  stabilizing_fun_map h (stabilizing_fun_map g f) = stabilizing_fun_map (λ b, (h (g b))) f.
Proof.
  intros h g f. destruct f as [f f_keys f_default stabilizing_f]. apply irrelevant_stabilizing_fun; simpl.
  - reflexivity.
  - destruct (@dec_finite A _) as [(list_A & H_list_A) | infinite_A].
    + reflexivity.
    + rewrite list_filter_list_filter. f_equal. apply functional_extensionality; intros a.
      unfold stabilizing in stabilizing_f, stabilizing_stabilizing_fun_map_g_f |- *. destruct stabilizing_f as [H | (b_stabilizing & H_b_stabilizing)].
      * exfalso. apply H. exists. auto.
      * ltac1:(replace (f (` (infinite_A f_keys))) with b_stabilizing; revgoals). {
          destruct (infinite_A f_keys) as (a' & H_a'). simpl. specialize (H_b_stabilizing a'). ltac1:(intuition congruence).
        }
        ltac1:(replace (g (f (` (infinite_A (List.filter (λ a, ` (bool_of_sumbool (f a == b_stabilizing)) || negb (` (bool_of_sumbool (g (f a) == g b_stabilizing)))) f_keys))))) with (g b_stabilizing); revgoals). {
          destruct (infinite_A (List.filter (λ a, ` (bool_of_sumbool (f a == b_stabilizing)) || negb (` (bool_of_sumbool (g (f a) == g b_stabilizing)))) f_keys)) as (a' & H_a'). simpl. rewrite List.filter_In in H_a'.
          specialize (H_b_stabilizing a') as [H_b_stabilizing | H_b_stabilizing]; destruct (f a' == b_stabilizing) as [H_f_a' | H_f_a'], (g (f a') == g b_stabilizing) as [H_g_f_a' | H_g_f_a']; simpl in H_a' |- *; ltac1:(intuition congruence).
        }
        destruct (f a == b_stabilizing) as [H_f_a | H_f_a], (g (f a) == g b_stabilizing) as [H_g_f_a | H_g_f_a], (h (g (f a)) == h (g b_stabilizing)) as [H_h_g_f_a | H_h_g_f_a]; simpl; congruence.
  - rewrite option_map_option_map. reflexivity.
Qed.

Lemma eq_stabilizing_fun_map {A B C} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_eq_B : EqDec B eq} {dec_eq_C : EqDec C eq} :
  ∀ (g_1 g_2 : B → C) (f : A →₀ B),
  (∀ a, g_1 (f a) = g_2 (f a)) →
  option_map g_1 (stabilizing_fun_default f) = option_map g_2 (stabilizing_fun_default f) →
  stabilizing_fun_map g_1 f = stabilizing_fun_map g_2 f.
Proof.
  intros g_1 g_2 f H_g_f H_g_default. destruct f as [f f_keys f_default stabilizing_f]. simpl in H_g_f, H_g_default |- *. apply irrelevant_stabilizing_fun; simpl.
  - apply functional_extensionality. auto.
  - destruct (@dec_finite A _) as [_ | infinite_A].
    + reflexivity.
    + f_equal. apply functional_extensionality; intros a. rewrite <- ! H_g_f. reflexivity.
  - rewrite <- H_g_default. reflexivity.
Qed.

Definition stabilizing_fun_rebuild {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} {arbitrary_B : Arbitrary B} (f : A →₀ B) :=
  List.fold_right
    (λ a g, a ↦₀ f a, g)
    (_ ↦₀
      match stabilizing_fun_default f with
      | Some b_default => b_default
      | None => arbitrary
      end)
    (stabilizing_fun_keys f).


Definition stabilizing_fun_rebuild_erased {A B} {dec_finite_A : DecFinite A} {R : A → A → Prop} {pre_order_R : PreOrder R} {partial_order_R : PartialOrder eq R} {total_R : Total R} {dec_le_R : DecLe R} {dec_eq_B : EqDec B eq} {arbitrary_B : Arbitrary B} (f : A →₀ B) :=
  List.fold_right
    (λ a g, a ↦₀ₑ f a, g)
    (_ ↦₀ₑ
      match stabilizing_fun_default f with
      | Some b_default => b_default
      | None => arbitrary
      end)
    (stabilizing_fun_keys f).

Inductive t_closure_t {A} (R : A → A → Type) : A → A → Type :=
  | t_closure_t_step :
    ∀ x y,
    R x y →
    t_closure_t R x y
  | trans_t_closure_t :
    ∀ x y z,
    t_closure_t R x y →
    t_closure_t R y z →
    t_closure_t R x z.
Arguments t_closure_t_step {A R}.
Arguments trans_t_closure_t {A R}.

Fixpoint list_of_t_closure_t {A} {R : A → A → Type} {x y} (H : t_closure_t R x y) : list A :=
  match H with
  | t_closure_t_step x y H => [y]
  | trans_t_closure_t x y z H_1 H_2 => list_of_t_closure_t H_1 ++ list_of_t_closure_t H_2
  end.

Inductive rts_closure_t {A} (R : A → A → Type) : A → A → Type :=
  | rts_closure_t_step :
    ∀ x y,
    R x y →
    rts_closure_t R x y
  | refl_rts_closure_t :
    ∀ x,
    rts_closure_t R x x
  | trans_rts_closure_t :
    ∀ x y z,
    rts_closure_t R x y →
    rts_closure_t R y z →
    rts_closure_t R x z
  | sym_rts_closure_t :
    ∀ x y,
    rts_closure_t R x y →
    rts_closure_t R y x.
Arguments rts_closure_t_step {A R}.
Arguments refl_rts_closure_t {A R}.
Arguments trans_rts_closure_t {A R}.
Arguments sym_rts_closure_t {A R}.

Fixpoint list_of_rts_closure_t {A} {R : A → A → Type} {x y} (H : rts_closure_t R x y) : list A :=
  match H with
  | rts_closure_t_step x y H => [y]
  | refl_rts_closure_t x => [x]
  | trans_rts_closure_t x y z H_1 H_2 => list_of_rts_closure_t H_1 ++ list_of_rts_closure_t H_2
  | sym_rts_closure_t x y H => list_of_rts_closure_t H
  end.
