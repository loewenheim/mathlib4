/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.multiset.sections
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Multiset.Bind

/-!
# Sections of a multiset
-/


namespace Multiset

variable {α : Type _}

section Sections

/-- The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is an member of the corresponding multiset.
-/

-- Porting note: `Sections` depends on `recOn` which is noncomputable.
-- This may be removed when `Multiset.recOn` becomes computable.
noncomputable def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]
#align multiset.sections Multiset.Sections

@[simp]
theorem sections_zero : Sections (0 : Multiset (Multiset α)) = {0} :=
  rfl
#align multiset.sections_zero Multiset.sections_zero

@[simp]
theorem sections_cons (s : Multiset (Multiset α)) (m : Multiset α) :
    Sections (m ::ₘ s) = m.bind fun a => (Sections s).map (Multiset.cons a) :=
  recOn_cons m s
#align multiset.sections_cons Multiset.sections_cons

theorem coe_sections :
    ∀ l : List (List α),
      Sections (l.map fun l : List α => (l : Multiset α) : Multiset (Multiset α)) =
        (l.sections.map fun l : List α => (l : Multiset α) : Multiset (Multiset α))
  | [] => rfl
  | a :: l => by
    simp
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l]
    simp [List.sections, (· ∘ ·), List.bind]
#align multiset.coe_sections Multiset.coe_sections

@[simp]
theorem sections_add (s t : Multiset (Multiset α)) :
    Sections (s + t) = (Sections s).bind fun m => (Sections t).map ((· + ·) m) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, bind_assoc, map_bind, bind_map]
#align multiset.sections_add Multiset.sections_add

theorem mem_sections {s : Multiset (Multiset α)} :
    ∀ {a}, a ∈ Sections s ↔ s.Rel (fun s a => a ∈ s) a := by
  induction s using Multiset.induction_on
  case h₁ => simp
  case h₂ a a' ih =>
    -- Porting note: Previous code contained:
    -- simp [ih, rel_cons_left, -exists_and_left, exists_and_distrib_left.symm, eq_comm]
    --
    -- `exists_and_distrib_left` in Lean 3 is equal to `exists_and_left` in Lean 4.
    -- Also, the code doesn't finish the proof.
    intro a
    constructor <;> intro h <;> simp at *
    . let ⟨b, hb₁, c, hb₂, hb₃⟩ := h
      rw [rel_cons_left]; exists b, c
      simp [hb₁, ih.mp hb₂, hb₃.symm]
    . rw [rel_cons_left] at h
      let ⟨b, c, hb, hr, hc⟩ := h
      exists b; apply And.intro hb
      exists c; simp [ih.mpr hr, hc.symm]

#align multiset.mem_sections Multiset.mem_sections

theorem card_sections {s : Multiset (Multiset α)} : card (Sections s) = prod (s.map card) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }))
#align multiset.card_sections Multiset.card_sections

theorem prod_map_sum [CommSemiring α] {s : Multiset (Multiset α)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih => by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
#align multiset.prod_map_sum Multiset.prod_map_sum

end Sections

end Multiset