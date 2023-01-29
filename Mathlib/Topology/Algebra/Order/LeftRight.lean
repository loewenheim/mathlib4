/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.order.left_right
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.ContinuousOn

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuous_within_at_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuous_within_at_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuous_at_iff_continuous_left_right`, `continuous_at_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/


open Set Filter

open TopologicalSpace

section PartialOrder

variable {α β : Type _} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

theorem continuousWithinAt_ioi_iff_ici {a : α} {f : α → β} :
    ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [← Ici_diff_left, continuousWithinAt_diff_self]
#align continuous_within_at_Ioi_iff_Ici continuousWithinAt_ioi_iff_ici

theorem continuousWithinAt_iio_iff_iic {a : α} {f : α → β} :
    ContinuousWithinAt f (Iio a) a ↔ ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_ioi_iff_ici αᵒᵈ _ ‹TopologicalSpace α› _ _ _ f
#align continuous_within_at_Iio_iff_Iic continuousWithinAt_iio_iff_iic

theorem nhds_left'_le_nhds_ne (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun y hy => ne_of_lt hy
#align nhds_left'_le_nhds_ne nhds_left'_le_nhds_ne

theorem nhds_right'_le_nhds_ne (a : α) : 𝓝[>] a ≤ 𝓝[≠] a :=
  nhdsWithin_mono a fun y hy => ne_of_gt hy
#align nhds_right'_le_nhds_ne nhds_right'_le_nhds_ne

end PartialOrder

section TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β]

theorem nhds_left_sup_nhds_right (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ici, nhdsWithin_univ]
#align nhds_left_sup_nhds_right nhds_left_sup_nhds_right

theorem nhds_left'_sup_nhds_right (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iio_union_Ici, nhdsWithin_univ]
#align nhds_left'_sup_nhds_right nhds_left'_sup_nhds_right

theorem nhds_left_sup_nhds_right' (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhdsWithin_union, Iic_union_Ioi, nhdsWithin_univ]
#align nhds_left_sup_nhds_right' nhds_left_sup_nhds_right'

theorem nhds_left'_sup_nhds_right' (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsWithin_union, Iio_union_Ioi]
#align nhds_left'_sup_nhds_right' nhds_left'_sup_nhds_right'

theorem continuousAt_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iic a) a ∧ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhds_left_sup_nhds_right]
#align continuous_at_iff_continuous_left_right continuousAt_iff_continuous_left_right

theorem continuousAt_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (Iio a) a ∧ ContinuousWithinAt f (Ioi a) a := by
  rw [continuousWithinAt_ioi_iff_ici, continuousWithinAt_iio_iff_iic,
    continuousAt_iff_continuous_left_right]
#align continuous_at_iff_continuous_left'_right' continuousAt_iff_continuous_left'_right'

end TopologicalSpace

