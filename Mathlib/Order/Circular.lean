/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Set

/-!
# Circular order hierarchy

This file defines circular preorders, circular partial orders and circular orders.

## Hierarchy

* A ternary "betweenness" relation `Btw : α → α → α → Prop` forms a `circular_order` if it is
  - reflexive: `Btw a a a`
  - cyclic: `Btw a b c → Btw b c a`
  - antisymmetric: `Btw a b c → Btw c b a → a = b ∨ b = c ∨ c = a`
  - total: `Btw a b c ∨ Btw c b a`
  along with a strict betweenness relation `SBtw : α → α → α → Prop` which respects
  `SBtw a b c ↔ Btw a b c ∧ ¬ Btw c b a`, analogously to how `<` and `≤` are related, and is
  - transitive: `SBtw a b c → sbtw b d c → sbtw a d c`.
* A `circular_partial_order` drops totality.
* A `circular_preorder` further drops antisymmetry.

The intuition is that a circular order is a circle and `Btw a b c` means that going around
clockwise from `a` you reach `b` before `c` (`b` is between `a` and `c` is meaningless on an
unoriented circle). A circular partial order is several, potentially intersecting, circles. A
circular preorder is like a circular partial order, but several points can coexist.

Note that the relations between `circular_preorder`, `circular_partial_order` and `circular_order`
are subtler than between `preorder`, `partial_order`, `linear_order`. In particular, one cannot
simply extend the `Btw` of a `circular_partial_order` to make it a `circular_order`.

One can translate from usual orders to circular ones by "closing the necklace at infinity". See
`has_le.to_has_btw` and `has_lt.to_has_sBtw`. Going the other way involves "cutting the necklace" or
"rolling the necklace open".

## Examples

Some concrete circular orders one encounters in the wild are `zmod n` for `0 < n`, `circle`,
`real.angle`...

## Main definitions

* `set.cIcc`: Closed-closed circular interval.
* `set.cIoo`: Open-open circular interval.

## Notes

There's an unsolved diamond on `order_dual α` here. The instances `has_le α → has_btw αᵒᵈ` and
`has_lt α → has_sBtw αᵒᵈ` can each be inferred in two ways:
* `has_le α` → `has_btw α` → `has_btw αᵒᵈ` vs
  `has_le α` → `has_le αᵒᵈ` → `has_btw αᵒᵈ`
* `has_lt α` → `has_sBtw α` → `has_sBtw αᵒᵈ` vs
  `has_lt α` → `has_lt αᵒᵈ` → `has_sBtw αᵒᵈ`
The fields are propeq, but not defeq. It is temporarily fixed by turning the circularizing instances
into definitions.

## TODO

Antisymmetry is quite weak in the sense that there's no way to discriminate which two points are
equal. This prevents defining closed-open intervals `cIco` and `cIoc` in the neat `=`-less way. We
currently haven't defined them at all.

What is the correct generality of "rolling the necklace" open? At least, this works for `α × β` and
`β × α` where `α` is a circular order and `β` is a linear order.

What's next is to define circular groups and provide instances for `zmod n`, the usual circle group
`circle`, `real.angle`, and `roots_of_unity M`. What conditions do we need on `M` for this last one
to work?

We should have circular order homomorphisms. The typical example is
`days_to_month : days_of_the_year →c months_of_the_year` which relates the circular order of days
and the circular order of months. Is `α →c β` a good notation?

## References

* https://en.wikipedia.org/wiki/Cyclic_order
* https://en.wikipedia.org/wiki/Partial_cyclic_order

## Tags

circular order, cyclic order, circularly ordered set, cyclically ordered set
-/


/-- Syntax typeclass for a betweenness relation. -/
class HasBtw (α : Type _) where
  Btw : α → α → α → Prop
#align has_btw HasBtw

export HasBtw (Btw)

/-- Syntax typeclass for a strict betweenness relation. -/
class HasSBtw (α : Type _) where
  SBtw : α → α → α → Prop
#align has_sbtw HasSBtw

export HasSBtw (SBtw)

/-- A circular preorder is the analogue of a preorder where you can loop around. `≤` and `<` are
replaced by ternary relations `Btw` and `SBtw`. `Btw` is reflexive and cyclic. `SBtw` is transitive.
-/
class CircularPreorder (α : Type _) extends HasBtw α, HasSBtw α where
  btw_refl (a : α) : Btw a a a
  btw_cyclic_left {a b c : α} : Btw a b c → Btw b c a
  SBtw := fun a b c => Btw a b c ∧ ¬Btw c b a
  -- Porting note: `intros; rfl` used in lieu of `order_laws_tac` akin to the port of `PositiveCone`
  sBtw_iff_btw_not_btw {a b c : α} : SBtw a b c ↔ Btw a b c ∧ ¬Btw c b a := by intros; rfl
  sBtw_trans_left {a b c d : α} : SBtw a b c → SBtw b d c → SBtw a d c
#align circular_preorder CircularPreorder

export CircularPreorder (btw_refl btw_cyclic_left sBtw_trans_left)

/-- A circular partial order is the analogue of a partial order where you can loop around. `≤` and
`<` are replaced by ternary relations `Btw` and `SBtw`. `Btw` is reflexive, cyclic and
antisymmetric. `SBtw` is transitive. -/
class CircularPartialOrder (α : Type _) extends CircularPreorder α where
  btw_antisymm {a b c : α} : Btw a b c → Btw c b a → a = b ∨ b = c ∨ c = a
#align circular_partial_order CircularPartialOrder

export CircularPartialOrder (btw_antisymm)

/-- A circular order is the analogue of a linear order where you can loop around. `≤` and `<` are
replaced by ternary relations `Btw` and `SBtw`. `Btw` is reflexive, cyclic, antisymmetric and total.
`SBtw` is transitive. -/
class CircularOrder (α : Type _) extends CircularPartialOrder α where
  btw_total : ∀ a b c : α, Btw a b c ∨ Btw c b a
#align circular_order CircularOrder

export CircularOrder (btw_total)

/-! ### Circular preorders -/


section CircularPreorder

variable {α : Type _} [CircularPreorder α]

theorem btw_rfl {a : α} : Btw a a a :=
  btw_refl _
#align btw_rfl btw_rfl

-- TODO: `alias` creates a def instead of a lemma.
-- alias btw_cyclic_left        ← has_btw.btw.cyclic_left
theorem HasBtw.Btw.cyclic_left {a b c : α} (h : Btw a b c) : Btw b c a :=
  btw_cyclic_left h
#align has_btw.btw.cyclic_left HasBtw.Btw.cyclic_left

theorem btw_cyclic_right {a b c : α} (h : Btw a b c) : Btw c a b :=
  h.cyclic_left.cyclic_left
#align btw_cyclic_right btw_cyclic_right

alias btw_cyclic_right ← HasBtw.Btw.cyclic_right

/-- The order of the `↔` has been chosen so that `rw btw_cyclic` cycles to the right while
`rw ←btw_cyclic` cycles to the left (thus following the prepended arrow). -/
theorem btw_cyclic {a b c : α} : Btw a b c ↔ Btw c a b :=
  ⟨btw_cyclic_right, btw_cyclic_left⟩
#align btw_cyclic btw_cyclic

theorem sBtw_iff_btw_not_btw {a b c : α} : SBtw a b c ↔ Btw a b c ∧ ¬Btw c b a :=
  CircularPreorder.sBtw_iff_btw_not_btw
#align sbtw_iff_btw_not_btw sBtw_iff_btw_not_btw

theorem btw_of_sBtw {a b c : α} (h : SBtw a b c) : Btw a b c :=
  (sBtw_iff_btw_not_btw.1 h).1
#align btw_of_sbtw btw_of_sBtw

alias btw_of_sBtw ← HasSBtw.SBtw.btw

theorem not_btw_of_sBtw {a b c : α} (h : SBtw a b c) : ¬Btw c b a :=
  (sBtw_iff_btw_not_btw.1 h).2
#align not_btw_of_sbtw not_btw_of_sBtw

alias not_btw_of_sBtw ← HasSBtw.SBtw.not_btw

theorem not_sBtw_of_btw {a b c : α} (h : Btw a b c) : ¬SBtw c b a := fun h' => h'.not_btw h
#align not_sbtw_of_btw not_sBtw_of_btw

alias not_sBtw_of_btw ← HasBtw.Btw.not_sBtw

theorem sBtw_of_btw_not_btw {a b c : α} (habc : Btw a b c) (hcba : ¬Btw c b a) : SBtw a b c :=
  sBtw_iff_btw_not_btw.2 ⟨habc, hcba⟩
#align sbtw_of_btw_not_btw sBtw_of_btw_not_btw

alias sBtw_of_btw_not_btw ← HasBtw.Btw.sBtw_of_not_btw

theorem sBtw_cyclic_left {a b c : α} (h : SBtw a b c) : SBtw b c a :=
  h.btw.cyclic_left.sBtw_of_not_btw fun h' => h.not_btw h'.cyclic_left
#align sbtw_cyclic_left sBtw_cyclic_left

alias sBtw_cyclic_left ← HasSBtw.SBtw.cyclic_left

theorem sBtw_cyclic_right {a b c : α} (h : SBtw a b c) : SBtw c a b :=
  h.cyclic_left.cyclic_left
#align sbtw_cyclic_right sBtw_cyclic_right

alias sBtw_cyclic_right ← HasSBtw.SBtw.cyclic_right

/-- The order of the `↔` has been chosen so that `rw sBtw_cyclic` cycles to the right while
`rw ←sBtw_cyclic` cycles to the left (thus following the prepended arrow). -/
theorem sBtw_cyclic {a b c : α} : SBtw a b c ↔ SBtw c a b :=
  ⟨sBtw_cyclic_right, sBtw_cyclic_left⟩
#align sbtw_cyclic sBtw_cyclic

-- TODO: `alias` creates a def instead of a lemma.
-- alias btw_trans_left        ← has_btw.btw.trans_left
theorem HasSBtw.SBtw.trans_left {a b c d : α} (h : SBtw a b c) : SBtw b d c → SBtw a d c :=
  sBtw_trans_left h
#align has_sbtw.sbtw.trans_left HasSBtw.SBtw.trans_left

theorem sBtw_trans_right {a b c d : α} (hbc : SBtw a b c) (hcd : SBtw a c d) : SBtw a b d :=
  (hbc.cyclic_left.trans_left hcd.cyclic_left).cyclic_right
#align sbtw_trans_right sBtw_trans_right

alias sBtw_trans_right ← HasSBtw.SBtw.trans_right

theorem sBtw_asymm {a b c : α} (h : SBtw a b c) : ¬SBtw c b a :=
  h.btw.not_sBtw
#align sbtw_asymm sBtw_asymm

alias sBtw_asymm ← HasSBtw.SBtw.not_sBtw

theorem sBtw_irrefl_left_right {a b : α} : ¬SBtw a b a := fun h => h.not_btw h.btw
#align sbtw_irrefl_left_right sBtw_irrefl_left_right

theorem sBtw_irrefl_left {a b : α} : ¬SBtw a a b := fun h => sBtw_irrefl_left_right h.cyclic_left
#align sbtw_irrefl_left sBtw_irrefl_left

theorem sBtw_irrefl_right {a b : α} : ¬SBtw a b b := fun h => sBtw_irrefl_left_right h.cyclic_right
#align sbtw_irrefl_right sBtw_irrefl_right

theorem sBtw_irrefl (a : α) : ¬SBtw a a a :=
  sBtw_irrefl_left_right
#align sbtw_irrefl sBtw_irrefl

end CircularPreorder

/-! ### Circular partial orders -/


section CircularPartialOrder

variable {α : Type _} [CircularPartialOrder α]

-- TODO: `alias` creates a def instead of a lemma.
-- alias btw_antisymm        ← has_btw.btw.antisymm
theorem HasBtw.Btw.antisymm {a b c : α} (h : Btw a b c) : Btw c b a → a = b ∨ b = c ∨ c = a :=
  btw_antisymm h
#align has_btw.btw.antisymm HasBtw.Btw.antisymm

end CircularPartialOrder

/-! ### Circular orders -/


section CircularOrder

variable {α : Type _} [CircularOrder α]

theorem btw_refl_left_right (a b : α) : Btw a b a :=
  (or_self_iff _).1 (btw_total a b a)
#align btw_refl_left_right btw_refl_left_right

theorem btw_rfl_left_right {a b : α} : Btw a b a :=
  btw_refl_left_right _ _
#align btw_rfl_left_right btw_rfl_left_right

theorem btw_refl_left (a b : α) : Btw a a b :=
  btw_rfl_left_right.cyclic_right
#align btw_refl_left btw_refl_left

theorem btw_rfl_left {a b : α} : Btw a a b :=
  btw_refl_left _ _
#align btw_rfl_left btw_rfl_left

theorem btw_refl_right (a b : α) : Btw a b b :=
  btw_rfl_left_right.cyclic_left
#align btw_refl_right btw_refl_right

theorem btw_rfl_right {a b : α} : Btw a b b :=
  btw_refl_right _ _
#align btw_rfl_right btw_rfl_right

theorem sBtw_iff_not_btw {a b c : α} : SBtw a b c ↔ ¬Btw c b a := by
  rw [sBtw_iff_btw_not_btw]
  exact and_iff_right_of_imp (btw_total _ _ _).resolve_left
#align sbtw_iff_not_btw sBtw_iff_not_btw

theorem btw_iff_not_sBtw {a b c : α} : Btw a b c ↔ ¬SBtw c b a :=
  iff_not_comm.1 sBtw_iff_not_btw
#align btw_iff_not_sbtw btw_iff_not_sBtw

end CircularOrder

/-! ### Circular intervals -/


namespace Set

section CircularPreorder

variable {α : Type _} [CircularPreorder α]

/-- Closed-closed circular interval -/
def cIcc (a b : α) : Set α :=
  { x | Btw a x b }
#align set.cIcc Set.cIcc

/-- Open-open circular interval -/
def cIoo (a b : α) : Set α :=
  { x | SBtw a x b }
#align set.cIoo Set.cIoo

@[simp]
theorem mem_cIcc {a b x : α} : x ∈ cIcc a b ↔ Btw a x b :=
  Iff.rfl
#align set.mem_cIcc Set.mem_cIcc

@[simp]
theorem mem_cIoo {a b x : α} : x ∈ cIoo a b ↔ SBtw a x b :=
  Iff.rfl
#align set.mem_cIoo Set.mem_cIoo

end CircularPreorder

section CircularOrder

variable {α : Type _} [CircularOrder α]

theorem left_mem_cIcc (a b : α) : a ∈ cIcc a b :=
  btw_rfl_left
#align set.left_mem_cIcc Set.left_mem_cIcc

theorem right_mem_cIcc (a b : α) : b ∈ cIcc a b :=
  btw_rfl_right
#align set.right_mem_cIcc Set.right_mem_cIcc

theorem compl_cIcc {a b : α} : cIcc a bᶜ = cIoo b a := by
  ext
  rw [Set.mem_cIoo, sBtw_iff_not_btw]
  rfl
#align set.compl_cIcc Set.compl_cIcc

theorem compl_cIoo {a b : α} : cIoo a bᶜ = cIcc b a := by
  ext
  rw [Set.mem_cIcc, btw_iff_not_sBtw]
  rfl
#align set.compl_cIoo Set.compl_cIoo

end CircularOrder

end Set

/-! ### Circularizing instances -/


/-- The betweenness relation obtained from "looping around" `≤`.
See note [reducible non-instances]. -/
@[reducible]
def LE.toHasBtw (α : Type _) [LE α] :
    HasBtw α where Btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
#align has_le.to_has_btw LE.toHasBtw

/-- The strict betweenness relation obtained from "looping around" `<`.
See note [reducible non-instances]. -/
@[reducible]
def LT.toHasSBtw (α : Type _) [LT α] :
    HasSBtw α where SBtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
#align has_lt.to_has_sbtw LT.toHasSBtw

/-- The circular preorder obtained from "looping around" a preorder.
See note [reducible non-instances]. -/
@[reducible]
def Preorder.toCircularPreorder (α : Type _) [Preorder α] : CircularPreorder α where
  Btw a b c := a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b
  SBtw a b c := a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
  btw_refl a := Or.inl ⟨le_rfl, le_rfl⟩
  btw_cyclic_left h := by
    unfold Btw at h⊢
    simp at h⊢
    rwa [← or_assoc, or_comm]
  sBtw_trans_left {a} {b} {c} d := by
    rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hbd, hdc⟩ | ⟨hdc, hcb⟩ | ⟨hcb, hbd⟩)
    · exact Or.inl ⟨hab.trans hbd, hdc⟩
    · exact (hbc.not_lt hcb).elim
    · exact (hbc.not_lt hcb).elim
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact (hbc.not_lt hcb).elim
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact Or.inr (Or.inl ⟨hdc, hca⟩)
    · exact Or.inr (Or.inr ⟨hca, hab.trans hbd⟩)
  sBtw_iff_btw_not_btw {a} {b} {c} := by
    simp_rw [lt_iff_le_not_le]
    have := le_trans a b c
    have := le_trans b c a
    have := le_trans c a b
    admit -- Porting note: waiting on `tauto`
#align preorder.to_circular_preorder Preorder.toCircularPreorder

/-- The circular partial order obtained from "looping around" a partial order.
See note [reducible non-instances]. -/
@[reducible]
def PartialOrder.toCircularPartialOrder (α : Type _) [PartialOrder α] : CircularPartialOrder α :=
  { Preorder.toCircularPreorder α with
    btw_antisymm := @fun a b c => by
      rintro (⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩) (⟨hcb, hba⟩ | ⟨hba, hac⟩ | ⟨hac, hcb⟩)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inr (Or.inr <| hca.antisymm hac)
      · exact Or.inr (Or.inl <| hbc.antisymm hcb)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inl (hab.antisymm hba)
      · exact Or.inr (Or.inr <| hca.antisymm hac) }
#align partial_order.to_circular_partial_order PartialOrder.toCircularPartialOrder

/-- The circular order obtained from "looping around" a linear order.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrder.toCircularOrder (α : Type _) [LinearOrder α] : CircularOrder α :=
  { PartialOrder.toCircularPartialOrder α with
    btw_total := fun a b c => by
      cases' le_total a b with hab hba <;> cases' le_total b c with hbc hcb <;>
        cases' le_total c a with hca hac
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inl ⟨hab, hbc⟩)
      · exact Or.inl (Or.inr <| Or.inr ⟨hca, hab⟩)
      · exact Or.inr (Or.inr <| Or.inr ⟨hac, hcb⟩)
      · exact Or.inl (Or.inr <| Or.inl ⟨hbc, hca⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩)
      · exact Or.inr (Or.inl ⟨hcb, hba⟩)
      · exact Or.inr (Or.inr <| Or.inl ⟨hba, hac⟩) }
#align linear_order.to_circular_order LinearOrder.toCircularOrder

/-! ### Dual constructions -/

section OrderDual

instance (α : Type _) [HasBtw α] : HasBtw αᵒᵈ :=
  ⟨fun a b c : α => Btw c b a⟩

instance (α : Type _) [HasSBtw α] : HasSBtw αᵒᵈ :=
  ⟨fun a b c : α => SBtw c b a⟩

instance (α : Type _) [CircularPreorder α] : CircularPreorder αᵒᵈ :=
  { instHasBtwOrderDual α, instHasSBtwOrderDual α with
    btw_refl := @btw_refl α _
    btw_cyclic_left := btw_cyclic_right
    sBtw_trans_left := fun habc hbdc => hbdc.trans_right habc
    sBtw_iff_btw_not_btw := @fun a b c => @sBtw_iff_btw_not_btw α _ c b a }

instance (α : Type _) [CircularPartialOrder α] : CircularPartialOrder αᵒᵈ :=
  { instCircularPreorderOrderDual α with
    btw_antisymm := fun habc hcba => @btw_antisymm α _ _ _ _ hcba habc }

instance (α : Type _) [CircularOrder α] : CircularOrder αᵒᵈ :=
  { instCircularPartialOrderOrderDual α with btw_total := fun a b c => @btw_total α _ c b a }

end OrderDual
