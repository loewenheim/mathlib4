/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.sups
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.ScopedNS

/-!
# Set family operations

This file defines a few binary operations on `Finset α` for use in set family combinatorics.

## Main declarations

* `Finset.Sups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `Finset.Infs s t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `Finset.DisjSups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.

## Notation

We define the following notation in locale `FinsetFamily`:
* `s ⊻ t` for `Finset.Sups s t`
* `s ⊼ t` for `Finset.Infs s t`
* `s ○ t` for `Finset.DisjSups s t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/


open Function

variable {α : Type _} [DecidableEq α]

namespace Finset

section Sups

variable [SemilatticeSup α] (s s₁ s₂ t t₁ t₂ u : Finset α)

/-- The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
def Sups (s t : Finset α) : Finset α :=
  image₂ (· ⊔ ·) s t
#align finset.sups Finset.Sups

-- mathport name: finset.sups
scoped[FinsetFamily] infixl:74 " ⊻ " => Finset.Sups
--porting note: had to open FinsetFamily here and import ScopedNS tactic
open FinsetFamily

variable {s t} {a b c : α}

@[simp]
theorem memSups : c ∈ s ⊻ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊔ b = c := by simp [Sups]
#align finset.mem_sups Finset.memSups

variable (s t)

@[simp, norm_cast]
theorem coeSups : (s ⊻ t : Set α) = Set.image2 (· ⊔ ·) s t :=
  coe_image₂ _ _ _
#align finset.coe_sups Finset.coeSups

theorem cardSups_le : (s ⊻ t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_sups_le Finset.cardSups_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cardSups_iff :
    (s ⊻ t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊔ x.2 :=
  card_image₂_iff
#align finset.card_sups_iff Finset.cardSups_iff

variable {s s₁ s₂ t t₁ t₂ u}

theorem sup_memSups : a ∈ s → b ∈ t → a ⊔ b ∈ s ⊻ t :=
  mem_image₂_of_mem
#align finset.sup_mem_sups Finset.sup_memSups

theorem sups_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊻ t₁ ⊆ s₂ ⊻ t₂ :=
  image₂_subset
#align finset.sups_subset Finset.sups_subset

theorem sups_subset_left : t₁ ⊆ t₂ → s ⊻ t₁ ⊆ s ⊻ t₂ :=
  image₂_subset_left
#align finset.sups_subset_left Finset.sups_subset_left

theorem sups_subset_right : s₁ ⊆ s₂ → s₁ ⊻ t ⊆ s₂ ⊻ t :=
  image₂_subset_right
#align finset.sups_subset_right Finset.sups_subset_right

theorem image_subsetSups_left : b ∈ t → (· ⊔ b) '' s ⊆ s ⊻ t :=
  image_subset_image₂_left
#align finset.image_subset_sups_left Finset.image_subsetSups_left

theorem image_subsetSups_right : a ∈ s → (· ⊔ ·) a '' t ⊆ s ⊻ t :=
  image_subset_image₂_right
#align finset.image_subset_sups_right Finset.image_subsetSups_right

theorem forallSups_iff {p : α → Prop} : (∀ c ∈ s ⊻ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊔ b) :=
  forall_image₂_iff
#align finset.forall_sups_iff Finset.forallSups_iff

@[simp]
theorem sups_subset_iff : s ⊻ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊔ b ∈ u :=
  image₂_subset_iff
#align finset.sups_subset_iff Finset.sups_subset_iff

@[simp]
theorem sups_nonempty_iff : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.sups_nonempty_iff Finset.sups_nonempty_iff

theorem Nonempty.Sups : s.Nonempty → t.Nonempty → (s ⊻ t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.sups Finset.Nonempty.Sups

theorem Nonempty.ofSups_left : (s ⊻ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_sups_left Finset.Nonempty.ofSups_left

theorem Nonempty.ofSups_right : (s ⊻ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_sups_right Finset.Nonempty.ofSups_right

@[simp]
theorem sups_empty_left : ∅ ⊻ t = ∅ :=
  image₂_empty_left
#align finset.sups_empty_left Finset.sups_empty_left

@[simp]
theorem sups_empty_right : s ⊻ ∅ = ∅ :=
  image₂_empty_right
#align finset.sups_empty_right Finset.sups_empty_right

@[simp]
theorem sups_eq_empty_iff : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.sups_eq_empty_iff Finset.sups_eq_empty_iff

@[simp]
theorem sups_singleton_left : {a} ⊻ t = t.image (a ⊔ ·) :=
  image₂_singleton_left
#align finset.sups_singleton_left Finset.sups_singleton_left

@[simp]
theorem sups_singleton_right : s ⊻ {b} = s.image (· ⊔ b) :=
  image₂_singleton_right
#align finset.sups_singleton_right Finset.sups_singleton_right

theorem sups_singleton_left' : {a} ⊻ t = t.image ((· ⊔ ·) a) :=
  image₂_singleton_left'
#align finset.sups_singleton_left' Finset.sups_singleton_left'

theorem sups_singleton : ({a} ⊻ {b} : Finset α) = {a ⊔ b} :=
  image₂_singleton
#align finset.sups_singleton Finset.sups_singleton

theorem sups_union_left : (s₁ ∪ s₂) ⊻ t = s₁ ⊻ t ∪ s₂ ⊻ t :=
  image₂_union_left
#align finset.sups_union_left Finset.sups_union_left

theorem sups_union_right : s ⊻ (t₁ ∪ t₂) = s ⊻ t₁ ∪ s ⊻ t₂ :=
  image₂_union_right
#align finset.sups_union_right Finset.sups_union_right

theorem sups_inter_subset_left : (s₁ ∩ s₂) ⊻ t ⊆ s₁ ⊻ t ∩ s₂ ⊻ t :=
  image₂_inter_subset_left
#align finset.sups_inter_subset_left Finset.sups_inter_subset_left

theorem sups_inter_subset_right : s ⊻ (t₁ ∩ t₂) ⊆ s ⊻ t₁ ∩ s ⊻ t₂ :=
  image₂_inter_subset_right
#align finset.sups_inter_subset_right Finset.sups_inter_subset_right

theorem subsetSups {s t : Set α} :
    ↑u ⊆ Set.image2 (· ⊔ ·) s t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊻ t' :=
  subset_image₂
#align finset.subset_sups Finset.subsetSups

variable (s t u)

theorem bunionᵢ_image_sup_left : (s.bunionᵢ fun a => t.image <| (· ⊔ ·) a) = s ⊻ t :=
  bunionᵢ_image_left
#align finset.bUnion_image_sup_left Finset.bunionᵢ_image_sup_left

theorem bunionᵢ_image_sup_right : (t.bunionᵢ fun b => s.image fun a => a ⊔ b) = s ⊻ t :=
  bunionᵢ_image_right
#align finset.bUnion_image_sup_right Finset.bunionᵢ_image_sup_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_sup_product (s t : Finset α) : (s  ×ᶠ t).image (uncurry (· ⊔ ·)) = s ⊻ t :=
  image_uncurry_product _ _ _
#align finset.image_sup_product Finset.image_sup_product

theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) :=
  image₂_assoc fun _ _ _ => sup_assoc
#align finset.sups_assoc Finset.sups_assoc

theorem sups_comm : s ⊻ t = t ⊻ s :=
  image₂_comm fun _ _ => sup_comm
#align finset.sups_comm Finset.sups_comm

theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image₂_left_comm sup_left_comm
#align finset.sups_left_comm Finset.sups_left_comm

theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image₂_right_comm sup_right_comm
#align finset.sups_right_comm Finset.sups_right_comm

end Sups

section Infs

variable [SemilatticeInf α] (s s₁ s₂ t t₁ t₂ u : Finset α)

/-- The finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
def infs (s t : Finset α) : Finset α :=
  image₂ (· ⊓ ·) s t
#align finset.infs Finset.infs

-- mathport name: finset.infs
scoped[FinsetFamily] infixl:74 " ⊼ " => Finset.infs
open FinsetFamily

variable {s t} {a b c : α}

@[simp]
theorem mem_infs : c ∈ s ⊼ t ↔ ∃ a ∈ s, ∃ b ∈ t, a ⊓ b = c := by simp [infs]
#align finset.mem_infs Finset.mem_infs

variable (s t)

@[simp, norm_cast]
theorem coe_infs : (s ⊼ t : Set α) = Set.image2 (· ⊓ ·) s t :=
  coe_image₂ _ _ _
#align finset.coe_infs Finset.coe_infs

theorem card_infs_le : (s ⊼ t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_infs_le Finset.card_infs_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem card_infs_iff :
    (s ⊼ t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊓ x.2 :=
  card_image₂_iff
#align finset.card_infs_iff Finset.card_infs_iff

variable {s s₁ s₂ t t₁ t₂ u}

theorem inf_mem_infs : a ∈ s → b ∈ t → a ⊓ b ∈ s ⊼ t :=
  mem_image₂_of_mem
#align finset.inf_mem_infs Finset.inf_mem_infs

theorem infs_subset : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ ⊼ t₁ ⊆ s₂ ⊼ t₂ :=
  image₂_subset
#align finset.infs_subset Finset.infs_subset

theorem infs_subset_left : t₁ ⊆ t₂ → s ⊼ t₁ ⊆ s ⊼ t₂ :=
  image₂_subset_left
#align finset.infs_subset_left Finset.infs_subset_left

theorem infs_subset_right : s₁ ⊆ s₂ → s₁ ⊼ t ⊆ s₂ ⊼ t :=
  image₂_subset_right
#align finset.infs_subset_right Finset.infs_subset_right

theorem image_subset_infs_left : b ∈ t → (fun a => a ⊓ b) '' s ⊆ s ⊼ t :=
  image_subset_image₂_left
#align finset.image_subset_infs_left Finset.image_subset_infs_left

theorem image_subset_infs_right : a ∈ s → (· ⊓ ·) a '' t ⊆ s ⊼ t :=
  image_subset_image₂_right
#align finset.image_subset_infs_right Finset.image_subset_infs_right

theorem forall_infs_iff {p : α → Prop} : (∀ c ∈ s ⊼ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, p (a ⊓ b) :=
  forall_image₂_iff
#align finset.forall_infs_iff Finset.forall_infs_iff

@[simp]
theorem infs_subset_iff : s ⊼ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a ⊓ b ∈ u :=
  image₂_subset_iff
#align finset.infs_subset_iff Finset.infs_subset_iff

@[simp]
theorem infs_nonempty_iff : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.infs_nonempty_iff Finset.infs_nonempty_iff

theorem Nonempty.infs : s.Nonempty → t.Nonempty → (s ⊼ t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.infs Finset.Nonempty.infs

theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_infs_left Finset.Nonempty.of_infs_left

theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_infs_right Finset.Nonempty.of_infs_right

@[simp]
theorem infs_empty_left : ∅ ⊼ t = ∅ :=
  image₂_empty_left
#align finset.infs_empty_left Finset.infs_empty_left

@[simp]
theorem infs_empty_right : s ⊼ ∅ = ∅ :=
  image₂_empty_right
#align finset.infs_empty_right Finset.infs_empty_right

@[simp]
theorem infs_eq_empty_iff : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.infs_eq_empty_iff Finset.infs_eq_empty_iff

@[simp]
theorem infs_singleton_left : {a} ⊼ t = t.image fun b => a ⊓ b :=
  image₂_singleton_left
#align finset.infs_singleton_left Finset.infs_singleton_left

@[simp]
theorem infs_singleton_right : s ⊼ {b} = s.image fun a => a ⊓ b :=
  image₂_singleton_right
#align finset.infs_singleton_right Finset.infs_singleton_right

theorem infs_singleton_left' : {a} ⊼ t = t.image ((· ⊓ ·) a) :=
  image₂_singleton_left'
#align finset.infs_singleton_left' Finset.infs_singleton_left'

theorem infs_singleton : ({a} ⊼ {b} : Finset α) = {a ⊓ b} :=
  image₂_singleton
#align finset.infs_singleton Finset.infs_singleton

theorem infs_union_left : (s₁ ∪ s₂) ⊼ t = s₁ ⊼ t ∪ s₂ ⊼ t :=
  image₂_union_left
#align finset.infs_union_left Finset.infs_union_left

theorem infs_union_right : s ⊼ (t₁ ∪ t₂) = s ⊼ t₁ ∪ s ⊼ t₂ :=
  image₂_union_right
#align finset.infs_union_right Finset.infs_union_right

theorem infs_inter_subset_left : (s₁ ∩ s₂) ⊼ t ⊆ s₁ ⊼ t ∩ s₂ ⊼ t :=
  image₂_inter_subset_left
#align finset.infs_inter_subset_left Finset.infs_inter_subset_left

theorem infs_inter_subset_right : s ⊼ (t₁ ∩ t₂) ⊆ s ⊼ t₁ ∩ s ⊼ t₂ :=
  image₂_inter_subset_right
#align finset.infs_inter_subset_right Finset.infs_inter_subset_right

theorem subset_infs {s t : Set α} :
    ↑u ⊆ Set.image2 (· ⊓ ·) s t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' ⊼ t' :=
  subset_image₂
#align finset.subset_infs Finset.subset_infs

variable (s t u)

theorem bunionᵢ_image_inf_left : (s.bunionᵢ fun a => t.image <| (· ⊓ ·) a) = s ⊼ t :=
  bunionᵢ_image_left
#align finset.bUnion_image_inf_left Finset.bunionᵢ_image_inf_left

theorem bunionᵢ_image_inf_right : (t.bunionᵢ fun b => s.image fun a => a ⊓ b) = s ⊼ t :=
  bunionᵢ_image_right
#align finset.bUnion_image_inf_right Finset.bunionᵢ_image_inf_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_inf_product (s t : Finset α) : (s ×ᶠ t).image (uncurry (· ⊓ ·)) = s ⊼ t :=
  image_uncurry_product _ _ _
#align finset.image_inf_product Finset.image_inf_product

theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) :=
  image₂_assoc fun _ _ _ => inf_assoc
#align finset.infs_assoc Finset.infs_assoc

theorem infs_comm : s ⊼ t = t ⊼ s :=
  image₂_comm fun _ _ => inf_comm
#align finset.infs_comm Finset.infs_comm

theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image₂_left_comm inf_left_comm
#align finset.infs_left_comm Finset.infs_left_comm

theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image₂_right_comm inf_right_comm
#align finset.infs_right_comm Finset.infs_right_comm

end Infs

open FinsetFamily

section DisjSups

variable [SemilatticeSup α] [OrderBot α] [@DecidableRel α Disjoint] (s s₁ s₂ t t₁ t₂ u : Finset α)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a` and `b` are disjoint.
-/
def DisjSups : Finset α :=
  ((s ×ᶠ t).filter fun ab : α × α => Disjoint ab.1 ab.2).image fun ab => ab.1 ⊔ ab.2
#align finset.disj_sups Finset.DisjSups

-- mathport name: finset.disj_sups
scoped[FinsetFamily] infixl:74 " ○ " => Finset.DisjSups

variable {s t u} {a b c : α}

@[simp]
theorem memDisjSups : c ∈ s ○ t ↔ ∃ a ∈ s, ∃ b ∈ t, Disjoint a b ∧ a ⊔ b = c := by
  simp [DisjSups, and_assoc]
#align finset.mem_disj_sups Finset.memDisjSups

theorem disjSups_subsetSups : s ○ t ⊆ s ⊻ t :=
  by
  simp_rw [subset_iff, memSups, memDisjSups]
  exact fun c ⟨a, b, ha, hb, _, hc⟩ => ⟨a, b, ha, hb, hc⟩
#align finset.disj_sups_subset_sups Finset.disjSups_subsetSups

variable (s t)

theorem cardDisjSups_le : (s ○ t).card ≤ s.card * t.card :=
  (card_le_of_subset disjSups_subsetSups).trans <| cardSups_le _ _
#align finset.card_disj_sups_le Finset.cardDisjSups_le

variable {s s₁ s₂ t t₁ t₂ u}

theorem disjSups_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ○ t₁ ⊆ s₂ ○ t₂ :=
  image_subset_image <| filter_subset_filter _ <| product_subset_product hs ht
#align finset.disj_sups_subset Finset.disjSups_subset

theorem disjSups_subset_left (ht : t₁ ⊆ t₂) : s ○ t₁ ⊆ s ○ t₂ := by
  exact disjSups_subset _ _ _ _ Subset.rfl ht
#align finset.disj_sups_subset_left Finset.disjSups_subset_left

theorem disjSups_subset_right (hs : s₁ ⊆ s₂) : s₁ ○ t ⊆ s₂ ○ t :=
  disjSups_subset _ _ _ _ hs Subset.rfl
#align finset.disj_sups_subset_right Finset.disjSups_subset_right

theorem forallDisjSups_iff {p : α → Prop} :
    (∀ c ∈ s ○ t, p c) ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → p (a ⊔ b) :=
  by
  simp_rw [memDisjSups]
  refine' ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, _⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab
#align finset.forall_disj_sups_iff Finset.forallDisjSups_iff

@[simp]
theorem disjSups_subset_iff : s ○ t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, Disjoint a b → a ⊔ b ∈ u :=
  forallDisjSups_iff _ _
#align finset.disj_sups_subset_iff Finset.disjSups_subset_iff

theorem Nonempty.of_disjSups_left : (s ○ t).Nonempty → s.Nonempty :=
  by
  simp_rw [Finset.Nonempty, memDisjSups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩
#align finset.nonempty.of_disj_sups_left Finset.Nonempty.of_disjSups_left

theorem Nonempty.of_disj_sups_right : (s ○ t).Nonempty → t.Nonempty :=
  by
  simp_rw [Finset.Nonempty, memDisjSups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩
#align finset.nonempty.of_disj_sups_right Finset.Nonempty.of_disj_sups_right

@[simp]
theorem disjSups_empty_left : ∅ ○ t = ∅ := by simp [DisjSups]
#align finset.disj_sups_empty_left Finset.disjSups_empty_left

@[simp]
theorem disjSups_empty_right : s ○ ∅ = ∅ := by simp [DisjSups]
#align finset.disj_sups_empty_right Finset.disjSups_empty_right

theorem disjSups_singleton : ({a} ○ {b} : Finset α) = if Disjoint a b then {a ⊔ b} else ∅ := by
  split_ifs with h <;> simp [DisjSups, filter_singleton, h]
#align finset.disj_sups_singleton Finset.disjSups_singleton

theorem disjSups_union_left : (s₁ ∪ s₂) ○ t = s₁ ○ t ∪ s₂ ○ t := by
  simp [DisjSups, filter_union, image_union]
#align finset.disj_sups_union_left Finset.disjSups_union_left

theorem disjSups_union_right : s ○ (t₁ ∪ t₂) = s ○ t₁ ∪ s ○ t₂ := by
  simp [DisjSups, filter_union, image_union]
#align finset.disj_sups_union_right Finset.disjSups_union_right

theorem disjSups_inter_subset_left : (s₁ ∩ s₂) ○ t ⊆ s₁ ○ t ∩ s₂ ○ t := by
  simpa only [DisjSups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _
#align finset.disj_sups_inter_subset_left Finset.disjSups_inter_subset_left

theorem disjSups_inter_subset_right : s ○ (t₁ ∩ t₂) ⊆ s ○ t₁ ∩ s ○ t₂ := by
  simpa only [DisjSups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _
#align finset.disj_sups_inter_subset_right Finset.disjSups_inter_subset_right

variable (s t)

theorem disjSups_comm : s ○ t = t ○ s := by
  ext
  rw [memDisjSups, exists₂_comm]
  simp [sup_comm, disjoint_comm]
#align finset.disj_sups_comm Finset.disjSups_comm

end DisjSups

open FinsetFamily

section DistribLattice

variable [DistribLattice α] [OrderBot α] [@DecidableRel α Disjoint] (s t u : Finset α)

theorem disjSups_assoc : ∀ s t u : Finset α, s ○ t ○ u = s ○ (t ○ u) :=
  by
  refine' associative_of_commutative_of_le disjSups_comm _
  simp only [le_eq_subset, disjSups_subset_iff, memDisjSups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, sup_assoc.symm⟩
#align finset.disj_sups_assoc Finset.disjSups_assoc

theorem disjSups_left_comm : s ○ (t ○ u) = t ○ (s ○ u) := by
  simp_rw [← disjSups_assoc, disjSups_comm s]
#align finset.disj_sups_left_comm Finset.disjSups_left_comm

theorem disjSups_right_comm : s ○ t ○ u = s ○ u ○ t := by simp_rw [disjSups_assoc, disjSups_comm]
#align finset.disj_sups_right_comm Finset.disjSups_right_comm

end DistribLattice

end Finset
