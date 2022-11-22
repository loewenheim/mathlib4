import Mathlib.Tactic.Nontriviality
import Mathlib.Algebra.Order.Ring
import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Set.Basic

/-! ### Test `nontriviality` with inequality hypotheses -/


example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality
  rename_i inst; guard_hyp inst : Nontrivial R
  assumption

/-! ### Test `nontriviality` with equality or non-strict inequality goals -/


example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality
  rename_i inst; guard_hyp inst : Nontrivial R
  apply mul_comm

/-! ### Test deducing `nontriviality` by instance search -/

instance [OrderedRing R] : OrderedSemiring R := by refine' { ‹OrderedRing R› with .. } <;> sorry
theorem zero_le_one {R : Type} [OrderedSemiring R] : 0 ≤ (1 : R) := sorry
theorem zero_le_two {R : Type} [OrderedSemiring R] : 0 ≤ (2 : R) := sorry

example {R : Type} [OrderedRing R] : 0 ≤ (1 : R) := by
  nontriviality R
  rename_i inst; guard_hyp inst : Nontrivial R
  exact zero_le_one

example {R : Type} [OrderedRing R] : 0 ≤ (1 : R) := by
  nontriviality ℕ
  rename_i inst; guard_hyp inst : Nontrivial ℕ
  exact zero_le_one

example {R : Type} [OrderedRing R] : 0 ≤ (2 : R) := by
  fail_if_success nontriviality PUnit
  exact zero_le_two

example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 2 ∣ 4 := by
  nontriviality R
  rename_i inst; guard_hyp inst : Nontrivial R
  decide

/-! Test using `@[nontriviality]` lemmas in `nontriviality and custom `simp` lemmas -/


def EmptyOrUniv {α : Type _} (s : Set α) : Prop :=
  s = ∅ ∨ s = Set.univ

theorem Subsingleton.set_empty_or_univ {α} [Subsingleton α] (s : Set α) : s = ∅ ∨ s = Set.univ :=
  sorry

theorem Subsingleton.set_empty_or_univ' {α} [Subsingleton α] (s : Set α) : EmptyOrUniv s :=
  Subsingleton.set_empty_or_univ s

theorem Set.empty_union (a : Set α) : ∅ ∪ a = a := sorry

example {α : Type _} (s : Set α) (hs : s = ∅ ∪ Set.univ) : EmptyOrUniv s := by
  fail_if_success nontriviality α
  rw [Set.empty_union] at hs
  exact Or.inr hs

section

attribute [local nontriviality] Subsingleton.set_empty_or_univ

example {α : Type _} (s : Set α) (hs : s = ∅ ∪ Set.univ) : EmptyOrUniv s := by
  fail_if_success nontriviality α
  nontriviality α using Subsingleton.set_empty_or_univ'
  rw [Set.empty_union] at hs
  exact Or.inr hs

end

attribute [local nontriviality] Subsingleton.set_empty_or_univ'

example {α : Type _} (s : Set α) (hs : s = ∅ ∪ Set.univ) : EmptyOrUniv s := by
  nontriviality α
  rw [Set.empty_union] at hs
  exact Or.inr hs

/-! Test with nonatomic type argument -/


example (α : ℕ → Type) (a b : α 0) (h : a = b) : a = b := by
  nontriviality α 0 using Nat.zero_lt_one
  rename_i inst; guard_hyp inst : Nontrivial (α 0)
  exact h