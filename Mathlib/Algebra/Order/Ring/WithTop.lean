/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
! This file was ported from Lean 3 source module algebra.order.ring.with_top
! leanprover-community/mathlib commit 550b58538991c8977703fdeb7c9d51a5aa27df11
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Hom.Ring
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Ring.Canonical
import Std.Data.Option.Lemmas

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.canonicallyOrderedCommSemiring` and
`WithBot.commMonoidWithZero`.
-/

variable {α : Type _}

namespace WithTop

instance [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

variable [DecidableEq α]

instance : DecidableEq (WithTop α) := instDecidableEqOption

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithTop α) where
  zero := 0
  mul m n := if m = 0 ∨ n = 0 then 0 else m.bind fun a => n.bind fun b => ↑(a * b)
  zero_mul _ := if_pos <| Or.inl rfl
  mul_zero _ := if_pos <| Or.inr rfl

theorem mul_def {a b : WithTop α} :
    a * b = if a = 0 ∨ b = 0 then (0 : WithTop α) else a.bind fun a => b.bind fun b => ↑(a * b) :=
  rfl
#align with_top.mul_def WithTop.mul_def

-- Porting note: commented out @[simp] to placate the `simp can prove this` linter
-- @[simp]
theorem top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := by simp [mul_def]; rfl
#align with_top.top_mul_top WithTop.top_mul_top

@[simp]
theorem mul_top {a : WithTop α} (h : a ≠ 0) : a * ⊤ = ⊤ := by cases a <;> simp [mul_def, h] <;> rfl
#align with_top.mul_top WithTop.mul_top

@[simp]
theorem top_mul {a : WithTop α} (h : a ≠ 0) : ⊤ * a = ⊤ := by cases a <;> simp [mul_def, h] <;> rfl
#align with_top.top_mul WithTop.top_mul

end Mul

section MulZeroClass

variable [MulZeroClass α]

@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithTop α) = a * b := by
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · simp [hb]
    · simp [*, mul_def]
      rfl
#align with_top.coe_mul WithTop.coe_mul

theorem mul_coe {b : α} (hb : b ≠ 0) : ∀ {a : WithTop α},
    a * (b : WithTop α) = a.bind fun a : α => ↑(a * b)
  | none =>
    show (if (⊤ : WithTop α) = 0 ∨ (b : WithTop α) = 0 then 0 else ⊤ : WithTop α) = ⊤ by simp [hb]
  | Option.some a => by
    rw [some_eq_coe, ← coe_mul]
    rfl
#align with_top.mul_coe WithTop.mul_coe

@[simp]
theorem mul_eq_top_iff {a b : WithTop α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by
  match a with
  | none => match b with
    | none => simp [none_eq_top]
    | Option.some b => by_cases hb : b = 0 <;> simp [none_eq_top, some_eq_coe, hb]
  | Option.some a => match b with
    | none => by_cases ha : a = 0 <;> simp [none_eq_top, some_eq_coe, ha]
    | Option.some b => simp [some_eq_coe, ← coe_mul]
#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iff

theorem mul_lt_top [Preorder α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ := by
  lift a to α using ha
  lift b to α using hb
  simp only [← coe_mul, coe_lt_top]
#align with_top.mul_lt_top WithTop.mul_lt_top

@[simp]
theorem untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
  induction a using WithTop.recTopCoe; · rw [top_mul hb, untop'_top, zero_mul]
  induction b using WithTop.recTopCoe; · rw [mul_top ha, untop'_top, mul_zero]
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
#align with_top.untop'_zero_mul WithTop.untop'_zero_mul

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) :=
  { WithTop.instMulZeroClassWithTop with
    mul := (· * ·)
    one := 1, zero := 0
    one_mul := fun a =>
      match a with
      | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, one_mul],
    mul_one := fun a =>
      match a with
      | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, mul_one] }

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps (config := { fullyApplied := false })]
protected def MonoidWithZeroHom.withTopMap {R S : Type _} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases eq_or_ne y 0 with (rfl | hy)
      · simp
      induction' x using WithTop.recTopCoe with x
      · simp [hy, this]
      induction' y using WithTop.recTopCoe with y
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      · simp [← coe_mul, map_coe] }
#align monoid_with_zero_hom.with_top_map WithTop.MonoidWithZeroHom.withTopMap

instance noZeroDivisors [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithTop α) :=
  ⟨ by
    intro a b
    cases a <;> cases b <;> dsimp [mul_def] <;> split_ifs <;>
      simp_all [none_eq_top, some_eq_coe, mul_eq_zero]⟩

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithTop α) :=
  { WithTop.instMulZeroClassWithTop with
    mul := (· * ·)
    zero := 0
    mul_assoc := fun a b c => by
      rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
      rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
      rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
    -- Porting note: below needed to be rewritten due to changed `simp` behaviour for `coe`
      induction' a using WithTop.recTopCoe with a; · simp [hb, hc]
      induction' b using WithTop.recTopCoe with b; · simp [mul_top ha, top_mul hc]
      induction' c using WithTop.recTopCoe with c
      · rw [mul_top hb, mul_top ha]
        rw [← coe_zero, ne_eq, coe_eq_coe] at ha hb
        simp [ha, hb]
      simp only [← coe_mul, mul_assoc] }

instance monoidWithZero [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    MonoidWithZero (WithTop α) :=
  { WithTop.instMulZeroOneClassWithTop, WithTop.instSemigroupWithZeroWithTop with }

instance commMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) :=
  { WithTop.monoidWithZero with
    mul := (· * ·)
    zero := 0,
    mul_comm := fun a b => by simp only [or_comm, mul_def, Option.bind_comm a b, mul_comm] }

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c := by
  induction' c using WithTop.recTopCoe with c
  · by_cases ha : a = 0 <;> simp [ha]
  · by_cases hc : c = 0
    · simp [hc]
    simp [mul_coe hc]
    cases a <;> cases b
    repeat' first | rfl |exact congr_arg some (add_mul _ _ _)

/-- This instance requires `CanonicallyOrderedCommSemiring` as it is the smallest class
that derives from both `NonAssocNonUnitalSemiring` and `CanonicallyOrderedAddMonoid`, both
of which are required for distributivity. -/
instance commSemiring [Nontrivial α] : CommSemiring (WithTop α) :=
  { WithTop.addCommMonoidWithOne, WithTop.commMonoidWithZero with
    right_distrib := distrib'
    left_distrib := fun a b c => by
      rw [mul_comm, distrib', mul_comm b, mul_comm c] }

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddMonoid with
  eq_zero_or_eq_zero_of_mul_eq_zero := fun _ _ => eq_zero_or_eq_zero_of_mul_eq_zero}

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps (config := { fullyApplied := false })]
protected def RingHom.withTopMap {R S : Type _} [CanonicallyOrderedCommSemiring R] [DecidableEq R]
    [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  {MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with}
#align ring_hom.with_top_map WithTop.RingHom.withTopMap

end WithTop

namespace WithBot

instance [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

variable [DecidableEq α]

instance : DecidableEq (WithBot α) := instDecidableEqOption

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithBot α) :=
  WithTop.instMulZeroClassWithTop

theorem mul_def {a b : WithBot α} :
    a * b = if a = 0 ∨ b = 0 then (0 : WithBot α) else a.bind fun a => b.bind fun b => ↑(a * b) :=
  rfl
#align with_bot.mul_def WithBot.mul_def

@[simp]
theorem mul_bot {a : WithBot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
  WithTop.mul_top h
#align with_bot.mul_bot WithBot.mul_bot

@[simp]
theorem bot_mul {a : WithBot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
  WithTop.top_mul h
#align with_bot.bot_mul WithBot.bot_mul

@[simp]
theorem bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ :=
  WithTop.top_mul_top
#align with_bot.bot_mul_bot WithBot.bot_mul_bot

end Mul

section MulZeroClass

variable [MulZeroClass α]

@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithBot α) = a * b := by
  -- Porting note: Some lemmas seem to be no longer simp
  by_cases ha : a = 0
  · simp [coe_zero, ha]
  · by_cases hb : b = 0
    · simp [coe_zero, hb]
    · simp [*, coe_eq_zero, mul_def]
      rfl
#align with_bot.coe_mul WithBot.coe_mul

theorem mul_coe {b : α} (hb : b ≠ 0) {a : WithBot α} :
    a * (b : WithBot α) = a.bind fun a : α => ↑(a * b) :=
  WithTop.mul_coe hb
#align with_bot.mul_coe WithBot.mul_coe

@[simp]
theorem mul_eq_bot_iff {a b : WithBot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iff

theorem bot_lt_mul [Preorder α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b := by
  lift a to α using ne_bot_of_gt ha
  lift b to α using ne_bot_of_gt hb
  simp only [← coe_mul, bot_lt_coe]
#align with_bot.bot_lt_mul WithBot.bot_lt_mul

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  WithTop.instMulZeroOneClassWithTop

instance [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.noZeroDivisors

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithBot α) :=
  WithTop.instSemigroupWithZeroWithTop

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithBot α) :=
  WithTop.monoidWithZero

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  WithTop.commMonoidWithZero

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : CommSemiring (WithBot α) :=
  WithTop.commSemiring

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : PosMulMono (WithBot α) :=
  posMulMono_iff_covariant_pos.2
    ⟨by
      rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
      lift x to α using x0.ne_bot
      induction' a using WithBot.recBotCoe with a; · simp_rw [mul_bot x0.ne.symm, bot_le]
      induction' b using WithBot.recBotCoe with b; · exact absurd h (bot_lt_coe a).not_le
      simp only [← coe_mul, coe_le_coe] at *
      exact mul_le_mul_left' h x⟩

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : MulPosMono (WithBot α) :=
  posMulMono_iff_mulPosMono.mp inferInstance