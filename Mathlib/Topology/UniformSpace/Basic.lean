/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
--import Mathlib.Order.Filter.SmallSets
--import Mathlib.Topology.SubsetProperties
--import Mathlib.Topology.NhdsSet
import Mathlib.Init.Set
--import Mathlib.Data.Set.Basic
/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `uniform_embedding.lean`)
* totally bounded sets (in `cauchy.lean`)
* totally bounded complete sets are compact (in `cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (prod.mk x) (𝓤 X)`

where `prod.mk x : X → X × X := (λ y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `set (X × X)`, the composition `V ○ W : set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `set (X × X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (α β : Type*) := α → β → Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (α × α)`
instead of `rel α α` because we really need sets to use the filter library, and elements
of filters on `α × α` have type `set (α × α)`.

The structure `uniform_space X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/


open Set

-- open Filter Classical

--open Classical TopologicalSpace Filter

--set_option eqn_compiler.zeta true

universe u

/-!
### Relations, seen as `set (α × α)`
-/


variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} {ι : Sort _}

/-- The identity relation, or the graph of the identity function -/
def idRel {α : Type _} :=
  { p : α × α | p.1 = p.2 }
#align id_rel idRel

@[simp]
theorem mem_id_rel {a b : α} : (a, b) ∈ @idRel α ↔ a = b :=
  Iff.rfl
#align mem_id_rel mem_id_rel

#exit -- need to port `subset_def` to get any further
@[simp]
theorem id_rel_subset {s : Set (α × α)} : idRel ⊆ s ↔ ∀ a, (a, a) ∈ s := by
  simp [subset_def] <;> exact forall_congr' fun a => by simp
#align id_rel_subset id_rel_subset

/-- The composition of relations -/
def compRel {α : Type u} (r₁ r₂ : Set (α × α)) :=
  { p : α × α | ∃ z : α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂ }
#align comp_rel compRel

-- mathport name: uniformity.comp_rel
scoped[uniformity] infixl:55 " ○ " => compRel

@[simp]
theorem mem_comp_rel {r₁ r₂ : Set (α × α)} {x y : α} : (x, y) ∈ r₁ ○ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ :=
  Iff.rfl
#align mem_comp_rel mem_comp_rel

@[simp]
theorem swap_id_rel : Prod.swap '' idRel = @idRel α :=
  Set.ext fun ⟨a, b⟩ => by simp [image_swap_eq_preimage_swap] <;> exact eq_comm
#align swap_id_rel swap_id_rel

theorem monotone_comp_rel [Preorder β] {f g : β → Set (α × α)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ○ g x := fun a b h p ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩
#align monotone_comp_rel monotone_comp_rel

@[mono]
theorem comp_rel_mono {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k := fun ⟨x, y⟩ ⟨z, h, h'⟩ =>
  ⟨z, h₁ h, h₂ h'⟩
#align comp_rel_mono comp_rel_mono

theorem prod_mk_mem_comp_rel {a b c : α} {s t : Set (α × α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) : (a, b) ∈ s ○ t :=
  ⟨c, h₁, h₂⟩
#align prod_mk_mem_comp_rel prod_mk_mem_comp_rel

@[simp]
theorem id_comp_rel {r : Set (α × α)} : idRel ○ r = r :=
  Set.ext fun ⟨a, b⟩ => by simp
#align id_comp_rel id_comp_rel

theorem comp_rel_assoc {r s t : Set (α × α)} : r ○ s ○ t = r ○ (s ○ t) := by
  ext p <;> cases p <;> simp only [mem_comp_rel] <;> tauto
#align comp_rel_assoc comp_rel_assoc
#exit

theorem left_subset_comp_rel {s t : Set (α × α)} (h : idRel ⊆ t) : s ⊆ s ○ t := fun ⟨x, y⟩ xy_in => ⟨y, xy_in, h <| rfl⟩
#align left_subset_comp_rel left_subset_comp_rel

theorem right_subset_comp_rel {s t : Set (α × α)} (h : idRel ⊆ s) : t ⊆ s ○ t := fun ⟨x, y⟩ xy_in =>
  ⟨x, h <| rfl, xy_in⟩
#align right_subset_comp_rel right_subset_comp_rel

theorem subset_comp_self {s : Set (α × α)} (h : idRel ⊆ s) : s ⊆ s ○ s :=
  left_subset_comp_rel h
#align subset_comp_self subset_comp_self

theorem subset_iterate_comp_rel {s t : Set (α × α)} (h : idRel ⊆ s) (n : ℕ) : t ⊆ ((· ○ ·) s^[n]) t := by
  induction' n with n ihn generalizing t
  exacts[subset.rfl, (right_subset_comp_rel h).trans ihn]
#align subset_iterate_comp_rel subset_iterate_comp_rel

/-- The relation is invariant under swapping factors. -/
def SymmetricRel (V : Set (α × α)) : Prop :=
  Prod.swap ⁻¹' V = V
#align symmetric_rel SymmetricRel

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrizeRel (V : Set (α × α)) : Set (α × α) :=
  V ∩ Prod.swap ⁻¹' V
#align symmetrize_rel symmetrizeRel

theorem symmetric_symmetrize_rel (V : Set (α × α)) : SymmetricRel (symmetrizeRel V) := by
  simp [SymmetricRel, symmetrizeRel, preimage_inter, inter_comm, ← preimage_comp]
#align symmetric_symmetrize_rel symmetric_symmetrize_rel

theorem symmetrize_rel_subset_self (V : Set (α × α)) : symmetrizeRel V ⊆ V :=
  sep_subset _ _
#align symmetrize_rel_subset_self symmetrize_rel_subset_self

@[mono]
theorem symmetrize_mono {V W : Set (α × α)} (h : V ⊆ W) : symmetrizeRel V ⊆ symmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h
#align symmetrize_mono symmetrize_mono

theorem SymmetricRel.mk_mem_comm {V : Set (α × α)} (hV : SymmetricRel V) {x y : α} : (x, y) ∈ V ↔ (y, x) ∈ V :=
  Set.ext_iff.1 hV (y, x)
#align symmetric_rel.mk_mem_comm SymmetricRel.mk_mem_comm

theorem SymmetricRel.eq {U : Set (α × α)} (hU : SymmetricRel U) : Prod.swap ⁻¹' U = U :=
  hU
#align symmetric_rel.eq SymmetricRel.eq

theorem SymmetricRel.inter {U V : Set (α × α)} (hU : SymmetricRel U) (hV : SymmetricRel V) : SymmetricRel (U ∩ V) := by
  rw [SymmetricRel, preimage_inter, hU.eq, hV.eq]
#align symmetric_rel.inter SymmetricRel.inter

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure UniformSpace.Core (α : Type u) where
  uniformity : Filter (α × α)
  refl : 𝓟 idRel ≤ uniformity
  symm : Tendsto Prod.swap uniformity uniformity
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
#align uniform_space.core UniformSpace.Core

/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : ∀ r ∈ U, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ U, Prod.swap ⁻¹' r ∈ U) (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) : UniformSpace.Core α :=
  ⟨U, fun r ru => id_rel_subset.2 (refl _ ru), symm, by
    intro r ru
    rw [mem_lift'_sets]
    exact comp _ ru
    apply monotone_comp_rel <;> exact monotone_id⟩
#align uniform_space.core.mk' UniformSpace.Core.mk'

/-- Defining an `uniform_space.core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α)) (refl : ∀ r ∈ B, ∀ (x), (x, x) ∈ r)
    (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ Prod.swap ⁻¹' r) (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.HasBasis.ge_iff.mpr fun r ru => id_rel_subset.2 <| refl _ ru
  symm := (B.HasBasis.tendsto_iff B.HasBasis).mpr symm
  comp := (HasBasis.le_basis_iff (B.HasBasis.lift' (monotone_comp_rel monotone_id monotone_id)) B.HasBasis).mpr comp
#align uniform_space.core.mk_of_basis UniformSpace.Core.mkOfBasis

/-- A uniform space generates a topological space -/
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) : TopologicalSpace α where
  IsOpen s := ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ u.uniformity
  is_open_univ := by simp <;> intro <;> exact univ_mem
  is_open_inter := fun s t hs ht x ⟨xs, xt⟩ => by
    filter_upwards [hs x xs, ht x xt] <;> simp (config := { contextual := true })
  is_open_sUnion := fun s hs x ⟨t, ts, xt⟩ => by filter_upwards [hs t ts x xt] with p ph h using⟨t, ts, ph h⟩
#align uniform_space.core.to_topological_space UniformSpace.Core.toTopologicalSpace

theorem UniformSpace.core_eq : ∀ {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
  | ⟨u₁, _, _, _⟩, ⟨u₂, _, _, _⟩, h => by
    congr
    exact h
#align uniform_space.core_eq UniformSpace.core_eq

-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class UniformSpace (α : Type u) extends TopologicalSpace α, UniformSpace.Core α where
  is_open_uniformity : ∀ s, IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ uniformity
#align uniform_space UniformSpace

/-- Alternative constructor for `uniform_space α` when a topology is already given. -/
@[match_pattern]
def UniformSpace.mk' {α} (t : TopologicalSpace α) (c : UniformSpace.Core α)
    (is_open_uniformity : ∀ s : Set α, t.IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ c.uniformity) :
    UniformSpace α :=
  ⟨c, is_open_uniformity⟩
#align uniform_space.mk' UniformSpace.mk'

/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace α where
  toCore := u
  toTopologicalSpace := u.toTopologicalSpace
  is_open_uniformity a := Iff.rfl
#align uniform_space.of_core UniformSpace.ofCore

/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
    (h : t = u.toTopologicalSpace) : UniformSpace α where
  toCore := u
  toTopologicalSpace := t
  is_open_uniformity a := h.symm ▸ Iff.rfl
#align uniform_space.of_core_eq UniformSpace.ofCoreEq

theorem UniformSpace.to_core_to_topological_space (u : UniformSpace α) :
    u.toCore.toTopologicalSpace = u.toTopologicalSpace :=
  topological_space_eq <| funext fun s => by rw [UniformSpace.Core.toTopologicalSpace, UniformSpace.is_open_uniformity]
#align uniform_space.to_core_to_topological_space UniformSpace.to_core_to_topological_space

@[ext.1]
theorem uniform_space_eq : ∀ {u₁ u₂ : UniformSpace α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
  | UniformSpace.mk' t₁ u₁ o₁, UniformSpace.mk' t₂ u₂ o₂, h => by
    have : u₁ = u₂ := UniformSpace.core_eq h
    have : t₁ = t₂ := topological_space_eq <| funext fun s => by rw [o₁, o₂] <;> simp [this]
    simp [*]
#align uniform_space_eq uniform_space_eq

theorem UniformSpace.of_core_eq_to_core (u : UniformSpace α) (t : TopologicalSpace α)
    (h : t = u.toCore.toTopologicalSpace) : UniformSpace.ofCoreEq u.toCore t h = u :=
  uniform_space_eq rfl
#align uniform_space.of_core_eq_to_core UniformSpace.of_core_eq_to_core

/-- Replace topology in a `uniform_space` instance with a propositionally (but possibly not
definitionally) equal one. -/
@[reducible]
def UniformSpace.replaceTopology {α : Type _} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : UniformSpace α :=
  UniformSpace.ofCoreEq u.toCore i <| h.trans u.to_core_to_topological_space.symm
#align uniform_space.replace_topology UniformSpace.replaceTopology

theorem UniformSpace.replace_topology_eq {α : Type _} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  u.of_core_eq_to_core _ _
#align uniform_space.replace_topology_eq UniformSpace.replace_topology_eq

section UniformSpace

variable [UniformSpace α]

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  (@UniformSpace.toCore α _).uniformity
#align uniformity uniformity

-- mathport name: uniformity
scoped[uniformity] notation "𝓤" => uniformity

theorem is_open_uniformity {s : Set α} : IsOpen s ↔ ∀ x ∈ s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α :=
  UniformSpace.is_open_uniformity s
#align is_open_uniformity is_open_uniformity

theorem refl_le_uniformity : 𝓟 idRel ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).refl
#align refl_le_uniformity refl_le_uniformity

instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) := by
  inhabit α
  refine' (principal_ne_bot_iff.2 _).mono refl_le_uniformity
  exact ⟨(default, default), rfl⟩
#align uniformity.ne_bot uniformity.neBot

theorem refl_mem_uniformity {x : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) : (x, x) ∈ s :=
  refl_le_uniformity h rfl
#align refl_mem_uniformity refl_mem_uniformity

theorem mem_uniformity_of_eq {x y : α} {s : Set (α × α)} (h : s ∈ 𝓤 α) (hx : x = y) : (x, y) ∈ s :=
  hx ▸ refl_mem_uniformity h
#align mem_uniformity_of_eq mem_uniformity_of_eq

theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) ≤ 𝓤 _ :=
  (@UniformSpace.toCore α _).symm
#align symm_le_uniformity symm_le_uniformity

theorem comp_le_uniformity : ((𝓤 α).lift' fun s : Set (α × α) => s ○ s) ≤ 𝓤 α :=
  (@UniformSpace.toCore α _).comp
#align comp_le_uniformity comp_le_uniformity

theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity
#align tendsto_swap_uniformity tendsto_swap_uniformity

theorem comp_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
  have : s ∈ (𝓤 α).lift' fun t : Set (α × α) => t ○ t := comp_le_uniformity hs
  (mem_lift'_sets <| monotone_comp_rel monotone_id monotone_id).mp this
#align comp_mem_uniformity_sets comp_mem_uniformity_sets

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions). -/
theorem eventually_uniformity_iterate_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) (n : ℕ) :
    ∀ᶠ t in (𝓤 α).smallSets, ((· ○ ·) t^[n]) t ⊆ s := by
  suffices : ∀ᶠ t in (𝓤 α).smallSets, t ⊆ s ∧ ((· ○ ·) t^[n]) t ⊆ s
  exact (eventually_and.1 this).2
  induction' n with n ihn generalizing s
  · simpa

  rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
  refine' (ihn htU).mono fun U hU => _
  rw [Function.iterate_succ_apply']
  exact ⟨hU.1.trans <| (subset_comp_self <| refl_le_uniformity htU).trans hts, (comp_rel_mono hU.1 hU.2).trans hts⟩
#align eventually_uniformity_iterate_comp_subset eventually_uniformity_iterate_comp_subset

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
theorem eventually_uniformity_comp_subset {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1
#align eventually_uniformity_comp_subset eventually_uniformity_comp_subset

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is transitive. -/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β → α}
    (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α)) (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) l (𝓤 α)) :
    Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α) := by
  refine' le_trans (le_lift'.2 fun s hs => mem_map.2 _) comp_le_uniformity
  filter_upwards [h₁₂ hs, h₂₃ hs] with x hx₁₂ hx₂₃ using⟨_, hx₁₂, hx₂₃⟩
#align filter.tendsto.uniformity_trans Filter.Tendsto.uniformity_trans

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is symmetric -/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β → α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h
#align filter.tendsto.uniformity_symm Filter.Tendsto.uniformity_symm

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is reflexive. -/
theorem tendsto_diag_uniformity (f : β → α) (l : Filter β) : Tendsto (fun x => (f x, f x)) l (𝓤 α) := fun s hs =>
  mem_map.2 <| univ_mem' fun x => refl_mem_uniformity hs
#align tendsto_diag_uniformity tendsto_diag_uniformity

theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ => a) f
#align tendsto_const_uniformity tendsto_const_uniformity

theorem symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, (∀ a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
  have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
  ⟨s ∩ preimage Prod.swap s, inter_mem hs this, fun a b ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, inter_subset_left _ _⟩
#align symm_of_uniformity symm_of_uniformity

theorem comp_symm_of_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, (∀ {a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
  let ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', ht'₁, Subset.trans (monotone_comp_rel monotone_id monotone_id ht'₂) ht₂⟩
#align comp_symm_of_uniformity comp_symm_of_uniformity

theorem uniformity_le_symm : 𝓤 α ≤ @Prod.swap α α <$> 𝓤 α := by
  rw [map_swap_eq_comap_swap] <;> exact map_le_iff_le_comap.1 tendsto_swap_uniformity
#align uniformity_le_symm uniformity_le_symm

theorem uniformity_eq_symm : 𝓤 α = @Prod.swap α α <$> 𝓤 α :=
  le_antisymm uniformity_le_symm symm_le_uniformity
#align uniformity_eq_symm uniformity_eq_symm

@[simp]
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective
#align comap_swap_uniformity comap_swap_uniformity

theorem symmetrize_mem_uniformity {V : Set (α × α)} (h : V ∈ 𝓤 α) : symmetrizeRel V ∈ 𝓤 α := by
  apply (𝓤 α).inter_sets h
  rw [← image_swap_eq_preimage_swap, uniformity_eq_symm]
  exact image_mem_map h
#align symmetrize_mem_uniformity symmetrize_mem_uniformity

/-- Symmetric entourages form a basis of `𝓤 α` -/
theorem UniformSpace.has_basis_symmetric : (𝓤 α).HasBasis (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) id :=
  has_basis_self.2 fun t t_in =>
    ⟨symmetrizeRel t, symmetrize_mem_uniformity t_in, symmetric_symmetrize_rel t, symmetrize_rel_subset_self t⟩
#align uniform_space.has_basis_symmetric UniformSpace.has_basis_symmetric

theorem uniformity_lift_le_swap {g : Set (α × α) → Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
  calc
    (𝓤 α).lift g ≤ (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g := lift_mono uniformity_le_symm le_rfl
    _ ≤ _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap] <;> exact h

#align uniformity_lift_le_swap uniformity_lift_le_swap

theorem uniformity_lift_le_comp {f : Set (α × α) → Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) ≤ (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : Set (α × α) => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      exact monotone_comp_rel monotone_id monotone_id
      exact h
    _ ≤ (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

#align uniformity_lift_le_comp uniformity_lift_le_comp

theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : Set (α × α) => s ○ (s ○ s)) ≤ 𝓤 α :=
  calc
    ((𝓤 α).lift' fun d => d ○ (d ○ d)) = (𝓤 α).lift fun s => (𝓤 α).lift' fun t : Set (α × α) => s ○ (t ○ t) := by
      rw [lift_lift'_same_eq_lift']
      exact fun x => monotone_comp_rel monotone_const <| monotone_comp_rel monotone_id monotone_id
      exact fun x => monotone_comp_rel monotone_id monotone_const
    _ ≤ (𝓤 α).lift fun s => (𝓤 α).lift' fun t : Set (α × α) => s ○ t :=
      lift_mono' fun s hs =>
        @uniformity_lift_le_comp α _ _ (𝓟 ∘ (· ○ ·) s) <|
          monotone_principal.comp (monotone_comp_rel monotone_const monotone_id)
    _ = (𝓤 α).lift' fun s : Set (α × α) => s ○ s :=
      lift_lift'_same_eq_lift' (fun s => monotone_comp_rel monotone_const monotone_id) fun s =>
        monotone_comp_rel monotone_id monotone_const
    _ ≤ 𝓤 α := comp_le_uniformity

#align comp_le_uniformity3 comp_le_uniformity3

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs
  use symmetrizeRel w, symmetrize_mem_uniformity w_in, symmetric_symmetrize_rel w
  have : symmetrizeRel w ⊆ w := symmetrize_rel_subset_self w
  calc
    symmetrizeRel w ○ symmetrizeRel w ⊆ w ○ w := by mono
    _ ⊆ s := w_sub

#align comp_symm_mem_uniformity_sets comp_symm_mem_uniformity_sets

theorem subset_comp_self_of_mem_uniformity {s : Set (α × α)} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
  subset_comp_self (refl_le_uniformity h)
#align subset_comp_self_of_mem_uniformity subset_comp_self_of_mem_uniformity

theorem comp_comp_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, SymmetricRel t ∧ t ○ t ○ t ⊆ s := by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, w_symm, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t ⊆ t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t ⊆ w ○ t := by mono
    _ ⊆ w ○ (t ○ t) := by mono
    _ ⊆ w ○ w := by mono
    _ ⊆ s := w_sub

#align comp_comp_symm_mem_uniformity_sets comp_comp_symm_mem_uniformity_sets

/-!
### Balls in uniform spaces
-/


/-- The ball around `(x : β)` with respect to `(V : set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def UniformSpace.ball (x : β) (V : Set (β × β)) : Set β :=
  Prod.mk x ⁻¹' V
#align uniform_space.ball UniformSpace.ball

open UniformSpace (ball)

theorem UniformSpace.mem_ball_self (x : α) {V : Set (α × α)} (hV : V ∈ 𝓤 α) : x ∈ ball x V :=
  refl_mem_uniformity hV
#align uniform_space.mem_ball_self UniformSpace.mem_ball_self

/-- The triangle inequality for `uniform_space.ball` -/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W) :=
  prod_mk_mem_comp_rel h h'
#align mem_ball_comp mem_ball_comp

theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
    ball x W ⊆ ball y V := fun z z_in => h' (mem_ball_comp h z_in)
#align ball_subset_of_comp_subset ball_subset_of_comp_subset

theorem ball_mono {V W : Set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
  preimage_mono h
#align ball_mono ball_mono

theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
  preimage_inter
#align ball_inter ball_inter

theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
  ball_mono (inter_subset_left V W) x
#align ball_inter_left ball_inter_left

theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
  ball_mono (inter_subset_right V W) x
#align ball_inter_right ball_inter_right

theorem mem_ball_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x y} : x ∈ ball y V ↔ y ∈ ball x V :=
  show (x, y) ∈ Prod.swap ⁻¹' V ↔ (x, y) ∈ V by
    unfold SymmetricRel at hV
    rw [hV]
#align mem_ball_symmetry mem_ball_symmetry

theorem ball_eq_of_symmetry {V : Set (β × β)} (hV : SymmetricRel V) {x} : ball x V = { y | (y, x) ∈ V } := by
  ext y
  rw [mem_ball_symmetry hV]
  exact Iff.rfl
#align ball_eq_of_symmetry ball_eq_of_symmetry

theorem mem_comp_of_mem_ball {V W : Set (β × β)} {x y z : β} (hV : SymmetricRel V) (hx : x ∈ ball z V)
    (hy : y ∈ ball z W) : (x, y) ∈ V ○ W := by
  rw [mem_ball_symmetry hV] at hx
  exact ⟨z, hx, hy⟩
#align mem_comp_of_mem_ball mem_comp_of_mem_ball

theorem UniformSpace.is_open_ball (x : α) {V : Set (α × α)} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.Preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.is_open_ball UniformSpace.is_open_ball

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_comp_comp {V W M : Set (β × β)} (hW' : SymmetricRel W) {p : β × β} :
    p ∈ V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W ∩ M).Nonempty := by
  cases' p with x y
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry hW']⟩, hwz⟩

  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rwa [mem_ball_symmetry hW'] at z_in
    use z, w <;> tauto

#align mem_comp_comp mem_comp_comp

/-!
### Neighborhoods in uniform spaces
-/


theorem mem_nhds_uniformity_iff_right {x : α} {s : Set α} : s ∈ 𝓝 x ↔ { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α := by
  refine' ⟨_, fun hs => _⟩
  · simp only [mem_nhds_iff, is_open_uniformity, and_imp, exists_imp]
    intro t ts ht xt
    filter_upwards [ht x xt] using fun y h eq => ts (h Eq)

  · refine' mem_nhds_iff.mpr ⟨{ x | { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α }, _, _, hs⟩
    · exact fun y hy => refl_mem_uniformity hy rfl

    · refine' is_open_uniformity.mpr fun y hy => _
      rcases comp_mem_uniformity_sets hy with ⟨t, ht, tr⟩
      filter_upwards [ht]
      rintro ⟨a, b⟩ hp' rfl
      filter_upwards [ht]
      rintro ⟨a', b'⟩ hp'' rfl
      exact @tr (a, b') ⟨a', hp', hp''⟩ rfl


#align mem_nhds_uniformity_iff_right mem_nhds_uniformity_iff_right

theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} : s ∈ 𝓝 x ↔ { p : α × α | p.2 = x → p.1 ∈ s } ∈ 𝓤 α := by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  rfl
#align mem_nhds_uniformity_iff_left mem_nhds_uniformity_iff_left

theorem nhds_eq_comap_uniformity_aux {α : Type u} {x : α} {s : Set α} {F : Filter (α × α)} :
    { p : α × α | p.fst = x → p.snd ∈ s } ∈ F ↔ s ∈ comap (Prod.mk x) F := by
  rw [mem_comap] <;>
    exact
      Iff.intro (fun hs => ⟨_, hs, fun x hx => hx rfl⟩) fun ⟨t, h, ht⟩ =>
        (F.sets_of_superset h) fun ⟨p₁, p₂⟩ hp (h : p₁ = x) => ht <| by simp [h.symm, hp]
#align nhds_eq_comap_uniformity_aux nhds_eq_comap_uniformity_aux

theorem nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x) := by
  ext s
  rw [mem_nhds_uniformity_iff_right]
  exact nhds_eq_comap_uniformity_aux
#align nhds_eq_comap_uniformity nhds_eq_comap_uniformity

/-- See also `is_open_iff_open_ball_subset`. -/
theorem is_open_iff_ball_subset {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  simp_rw [is_open_iff_mem_nhds, nhds_eq_comap_uniformity]
  exact Iff.rfl
#align is_open_iff_ball_subset is_open_iff_ball_subset

theorem nhds_basis_uniformity' {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) {x : α} :
    (𝓝 x).HasBasis p fun i => ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)
#align nhds_basis_uniformity' nhds_basis_uniformity'

theorem nhds_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) {x : α} :
    (𝓝 x).HasBasis p fun i => { y | (y, x) ∈ s i } := by
  replace h := h.comap Prod.swap
  rw [← map_swap_eq_comap_swap, ← uniformity_eq_symm] at h
  exact nhds_basis_uniformity' h
#align nhds_basis_uniformity nhds_basis_uniformity

theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s := by
  rw [nhds_eq_comap_uniformity, mem_comap]
  exact Iff.rfl
#align uniform_space.mem_nhds_iff UniformSpace.mem_nhds_iff

theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : Set (α × α)⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x := by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, subset.refl _⟩
#align uniform_space.ball_mem_nhds UniformSpace.ball_mem_nhds

theorem UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, SymmetricRel V ∧ ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use symmetrizeRel V, symmetrize_mem_uniformity V_in, symmetric_symmetrize_rel V
    exact subset.trans (ball_mono (symmetrize_rel_subset_self V) x) V_sub

  · rintro ⟨V, V_in, V_symm, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

#align uniform_space.mem_nhds_iff_symm UniformSpace.mem_nhds_iff_symm

theorem UniformSpace.has_basis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : Set (α × α) => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc']⟩
#align uniform_space.has_basis_nhds UniformSpace.has_basis_nhds

open UniformSpace

theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (s ∩ ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (has_basis_nhds x), Set.Nonempty]
#align uniform_space.mem_closure_iff_symm_ball UniformSpace.mem_closure_iff_symm_ball

theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} : x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).Nonempty :=
  by simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]
#align uniform_space.mem_closure_iff_ball UniformSpace.mem_closure_iff_ball

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem UniformSpace.has_basis_nhds_prod (x y : α) :
    (HasBasis (𝓝 (x, y)) fun s => s ∈ 𝓤 α ∧ SymmetricRel s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (has_basis_nhds x).prod_same_index (has_basis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, U_symm.inter V_symm⟩, ball_inter_left x U V, ball_inter_right y U V⟩
#align uniform_space.has_basis_nhds_prod UniformSpace.has_basis_nhds_prod

theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_binfi
#align nhds_eq_uniformity nhds_eq_uniformity

theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) ∈ s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_binfi
#align nhds_eq_uniformity' nhds_eq_uniformity'

theorem mem_nhds_left (x : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { y : α | (x, y) ∈ s } ∈ 𝓝 x :=
  ball_mem_nhds x h
#align mem_nhds_left mem_nhds_left

theorem mem_nhds_right (y : α) {s : Set (α × α)} (h : s ∈ 𝓤 α) : { x : α | (x, y) ∈ s } ∈ 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)
#align mem_nhds_right mem_nhds_right

theorem IsCompact.nhds_set_basis_uniformity {p : ι → Prop} {s : ι → Set (α × α)} (hU : (𝓤 α).HasBasis p s) {K : Set α}
    (hK : IsCompact K) : (𝓝ˢ K).HasBasis p fun i => ⋃ x ∈ K, ball x (s i) := by
  refine' ⟨fun U => _⟩
  simp only [mem_nhds_set_iff_forall, (nhds_basis_uniformity' hU).mem_iff, Union₂_subset_iff]
  refine' ⟨fun H => _, fun ⟨i, hpi, hi⟩ x hx => ⟨i, hpi, hi x hx⟩⟩
  replace H : ∀ x ∈ K, ∃ i : { i // p i }, ball x (s i ○ s i) ⊆ U
  · intro x hx
    rcases H x hx with ⟨i, hpi, hi⟩
    rcases comp_mem_uniformity_sets (hU.mem_of_mem hpi) with ⟨t, ht_mem, ht⟩
    rcases hU.mem_iff.1 ht_mem with ⟨j, hpj, hj⟩
    exact ⟨⟨j, hpj⟩, subset.trans (ball_mono ((comp_rel_mono hj hj).trans ht) _) hi⟩

  have : Nonempty { a // p a } := nonempty_subtype.2 hU.ex_mem
  choose! I hI using H
  rcases hK.elim_nhds_subcover (fun x => ball x <| s (I x)) fun x hx => ball_mem_nhds _ <| hU.mem_of_mem (I x).2 with
    ⟨t, htK, ht⟩
  obtain ⟨i, hpi, hi⟩ : ∃ (i : _)(hpi : p i), s i ⊆ ⋂ x ∈ t, s (I x)
  exact hU.mem_iff.1 ((bInter_finset_mem t).2 fun x hx => hU.mem_of_mem (I x).2)
  rw [subset_Inter₂_iff] at hi
  refine' ⟨i, hpi, fun x hx => _⟩
  rcases mem_Union₂.1 (ht hx) with ⟨z, hzt : z ∈ t, hzx : x ∈ ball z (s (I z))⟩
  calc
    ball x (s i) ⊆ ball z (s (I z) ○ s (I z)) := fun y hy => ⟨x, hzx, hi z hzt hy⟩
    _ ⊆ U := hI z (htK z hzt)

#align is_compact.nhds_set_basis_uniformity IsCompact.nhds_set_basis_uniformity

theorem Disjoint.exists_uniform_thickening {A B : Set α} (hA : IsCompact A) (hB : IsClosed B) (h : Disjoint A B) :
    ∃ V ∈ 𝓤 α, Disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) := by
  have : Bᶜ ∈ 𝓝ˢ A := hB.is_open_compl.mem_nhds_set.mpr h.le_compl_right
  rw [(hA.nhds_set_basis_uniformity (Filter.basis_sets _)).mem_iff] at this
  rcases this with ⟨U, hU, hUAB⟩
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
  refine' ⟨V, hV, set.disjoint_left.mpr fun x => _⟩
  simp only [mem_Union₂]
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
  rw [mem_ball_symmetry hVsymm] at hxa hxb
  exact hUAB (mem_Union₂_of_mem ha <| hVU <| mem_comp_of_mem_ball hVsymm hxa hxb) hb
#align disjoint.exists_uniform_thickening Disjoint.exists_uniform_thickening

theorem Disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → Set (α × α)} (hU : (𝓤 α).HasBasis p s)
    {A B : Set α} (hA : IsCompact A) (hB : IsClosed B) (h : Disjoint A B) :
    ∃ i, p i ∧ Disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) := by
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩
  exact ⟨i, hi, hVAB.mono (Union₂_mono fun a _ => ball_mono hiV a) (Union₂_mono fun b _ => ball_mono hiV b)⟩
#align disjoint.exists_uniform_thickening_of_basis Disjoint.exists_uniform_thickening_of_basis

theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α) := fun s => mem_nhds_right a
#align tendsto_right_nhds_uniformity tendsto_right_nhds_uniformity

theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α) := fun s => mem_nhds_left a
#align tendsto_left_nhds_uniformity tendsto_left_nhds_uniformity

theorem lift_nhds_left {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g { y | (x, y) ∈ s } :=
  Eq.trans
    (by
      rw [nhds_eq_uniformity]
      exact Filter.lift_assoc <| monotone_principal.comp <| monotone_preimage.comp monotone_preimage)
    (congr_arg _ <| funext fun s => Filter.lift_principal hg)
#align lift_nhds_left lift_nhds_left

theorem lift_nhds_right {x : α} {g : Set α → Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g { y | (y, x) ∈ s } :=
  calc
    (𝓝 x).lift g = (𝓤 α).lift fun s : Set (α × α) => g { y | (x, y) ∈ s } := lift_nhds_left hg
    _ = (@Prod.swap α α <$> 𝓤 α).lift fun s : Set (α × α) => g { y | (x, y) ∈ s } := by rw [← uniformity_eq_symm]
    _ = (𝓤 α).lift fun s : Set (α × α) => g { y | (x, y) ∈ image Prod.swap s } :=
      map_lift_eq2 <| hg.comp monotone_preimage
    _ = _ := by simp [image_swap_eq_preimage_swap]

#align lift_nhds_right lift_nhds_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ᶠ 𝓝 b =
      (𝓤 α).lift fun s : Set (α × α) =>
        (𝓤 α).lift' fun t : Set (α × α) => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ t } :=
  by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  · rfl

  · exact monotone_preimage

  · exact monotone_preimage

#align nhds_nhds_eq_uniformity_uniformity_prod nhds_nhds_eq_uniformity_uniformity_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) = (𝓤 α).lift' fun s : Set (α × α) => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · intro s
    exact monotone_const.set_prod monotone_preimage

  · intro t
    exact monotone_preimage.set_prod monotone_const

#align nhds_eq_uniformity_prod nhds_eq_uniformity_prod

/- ./././Mathport/Syntax/Translate/Basic.lean:611:2: warning: expanding binder collection (t «expr ⊆ » cl_d) -/
theorem nhdset_of_mem_uniformity {d : Set (α × α)} (s : Set (α × α)) (hd : d ∈ 𝓤 α) :
    ∃ t : Set (α × α), IsOpen t ∧ s ⊆ t ∧ t ⊆ { p | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d } :=
  let cl_d := { p : α × α | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d }
  have : ∀ p ∈ s, ∃ (t : _)(_ : t ⊆ cl_d), IsOpen t ∧ p ∈ t := fun ⟨x, y⟩ hp =>
    mem_nhds_iff.mp <|
      show cl_d ∈ 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        exact monotone_preimage.set_prod monotone_preimage
  have : ∃ t : ∀ (p : α × α) (h : p ∈ s), Set (α × α), ∀ p, ∀ h : p ∈ s, t p h ⊆ cl_d ∧ IsOpen (t p h) ∧ p ∈ t p h := by
    simp [Classical.skolem] at this <;> simp <;> assumption
  match this with
  | ⟨t, ht⟩ =>
    ⟨(⋃ p : α × α, ⋃ h : p ∈ s, t p h : Set (α × α)),
      is_open_Union fun p : α × α => is_open_Union fun hp => (ht p hp).right.left, fun ⟨a, b⟩ hp => by
      simp <;> exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
      Union_subset fun p => Union_subset fun hp => (ht p hp).left⟩
#align nhdset_of_mem_uniformity nhdset_of_mem_uniformity

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball w_symm u_in v_in)
#align nhds_le_uniformity nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
theorem supr_nhds_le_uniformity : (⨆ x : α, 𝓝 (x, x)) ≤ 𝓤 α :=
  supr_le nhds_le_uniformity
#align supr_nhds_le_uniformity supr_nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_set_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhds_set_diagonal α).trans_le supr_nhds_le_uniformity
#align nhds_set_diagonal_le_uniformity nhds_set_diagonal_le_uniformity

/-!
### Closure and interior in uniform spaces
-/


theorem closure_eq_uniformity (s : Set <| α × α) : closure s = ⋂ V ∈ { V | V ∈ 𝓤 α ∧ SymmetricRel V }, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp (config := { contextual := true }) only [mem_closure_iff_nhds_basis (UniformSpace.has_basis_nhds_prod x y),
    mem_Inter, mem_set_of_eq, and_imp, mem_comp_comp, exists_prop, ← mem_inter_iff, inter_comm, Set.Nonempty]
#align closure_eq_uniformity closure_eq_uniformity

theorem uniformity_has_basis_closed : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsClosed V) id := by
  refine' Filter.has_basis_self.2 fun t h => _
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine' ⟨closure w, mem_of_superset w_in subset_closure, isClosedClosure, _⟩
  refine' subset.trans _ r
  rw [closure_eq_uniformity]
  apply Inter_subset_of_subset
  apply Inter_subset
  exact ⟨w_in, w_symm⟩
#align uniformity_has_basis_closed uniformity_has_basis_closed

theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_has_basis_closed.lift'_closure_eq_self fun _ => And.right
#align uniformity_eq_uniformity_closure uniformity_eq_uniformity_closure

theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → Set (α × α)} (h : (𝓤 α).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure
#align filter.has_basis.uniformity_closure Filter.HasBasis.uniformity_closure

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_has_basis_closure : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure
#align uniformity_has_basis_closure uniformity_has_basis_closure

theorem closure_eq_inter_uniformity {t : Set (α × α)} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (hV : V ∈ 𝓤 α ∧ SymmetricRel V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <|
        UniformSpace.has_basis_symmetric.bInter_mem fun V₁ V₂ hV => comp_rel_mono (comp_rel_mono hV Subset.rfl) hV
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp only [comp_rel_assoc]

#align closure_eq_inter_uniformity closure_eq_inter_uniformity

theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_infi fun d =>
      le_infi fun hd => by
        let ⟨s, hs, hs_comp⟩ :=
          (mem_lift'_sets <| monotone_comp_rel monotone_id <| monotone_comp_rel monotone_id monotone_id).mp
            (comp_le_uniformity3 hd)
        let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
        have : s ⊆ interior d :=
          calc
            s ⊆ t := hst
            _ ⊆ interior d :=
              ht.subset_interior_iff.mpr fun x (hx : x ∈ t) =>
                let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
                hs_comp ⟨x, h₁, y, h₂, h₃⟩

        have : interior d ∈ 𝓤 α := by filter_upwards [hs] using this
        simp [this])
    fun s hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset
#align uniformity_eq_uniformity_interior uniformity_eq_uniformity_interior

theorem interior_mem_uniformity {s : Set (α × α)} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior] <;> exact mem_lift' hs
#align interior_mem_uniformity interior_mem_uniformity

theorem mem_uniformity_is_closed {s : Set (α × α)} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_has_basis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩
#align mem_uniformity_is_closed mem_uniformity_is_closed

theorem is_open_iff_open_ball_subset {s : Set α} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, IsOpen V ∧ ball x V ⊆ s := by
  rw [is_open_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact ⟨interior V, interior_mem_uniformity hV, is_open_interior, (ball_mono interior_subset x).trans hV'⟩

  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩

#align is_open_iff_open_ball_subset is_open_iff_open_ball_subset

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem Dense.bUnion_uniformity_ball {s : Set α} {U : Set (α × α)} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    (⋃ x ∈ s, ball x U) = univ := by
  refine' Union₂_eq_univ_iff.2 fun y => _
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩
#align dense.bUnion_uniformity_ball Dense.bUnion_uniformity_ball

/-!
### Uniformity bases
-/


/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
theorem uniformity_has_basis_open : HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V) id :=
  has_basis_self.2 fun s hs => ⟨interior s, interior_mem_uniformity hs, is_open_interior, interior_subset⟩
#align uniformity_has_basis_open uniformity_has_basis_open

theorem Filter.HasBasis.mem_uniformity_iff {p : β → Prop} {s : β → Set (α × α)} (h : (𝓤 α).HasBasis p s)
    {t : Set (α × α)} : t ∈ 𝓤 α ↔ ∃ (i : _)(hi : p i), ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
  h.mem_iff.trans <| by simp only [Prod.forall, subset_def]
#align filter.has_basis.mem_uniformity_iff Filter.HasBasis.mem_uniformity_iff

/-- Open elements `s : set (α × α)` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
theorem uniformity_has_basis_open_symmetric :
    HasBasis (𝓤 α) (fun V : Set (α × α) => V ∈ 𝓤 α ∧ IsOpen V ∧ SymmetricRel V) id := by
  simp only [← and_assoc']
  refine' uniformity_has_basis_open.restrict fun s hs => ⟨symmetrizeRel s, _⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.Preimage continuous_swap)⟩, symmetric_symmetrize_rel s,
      symmetrize_rel_subset_self s⟩
#align uniformity_has_basis_open_symmetric uniformity_has_basis_open_symmetric

theorem comp_open_symm_mem_uniformity_sets {s : Set (α × α)} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SymmetricRel t ∧ t ○ t ⊆ s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_has_basis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (comp_rel_mono hu₄ hu₄).trans ht₂⟩
#align comp_open_symm_mem_uniformity_sets comp_open_symm_mem_uniformity_sets

section

variable (α)

theorem UniformSpace.has_seq_basis [is_countably_generated <| 𝓤 α] :
    ∃ V : ℕ → Set (α × α), HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SymmetricRel (V n) :=
  let ⟨U, hsym, hbasis⟩ := UniformSpace.has_basis_symmetric.exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩
#align uniform_space.has_seq_basis UniformSpace.has_seq_basis

end

theorem Filter.HasBasis.bInter_bUnion_ball {p : ι → Prop} {U : ι → Set (α × α)} (h : HasBasis (𝓤 α) p U) (s : Set α) :
    (⋂ (i) (hi : p i), ⋃ x ∈ s, ball x (U i)) = closure s := by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]
#align filter.has_basis.bInter_bUnion_ball Filter.HasBasis.bInter_bUnion_ball

/-! ### Uniform continuity -/


/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def UniformContinuous [UniformSpace β] (f : α → β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)
#align uniform_continuous UniformContinuous

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A function `f : α → β` is *uniformly continuous* on `s : set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def UniformContinuousOn [UniformSpace β] (f : α → β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ principal (s ×ˢ s)) (𝓤 β)
#align uniform_continuous_on UniformContinuousOn

theorem uniform_continuous_def [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  Iff.rfl
#align uniform_continuous_def uniform_continuous_def

theorem uniform_continuous_iff_eventually [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ x : α × α in 𝓤 α, (f x.1, f x.2) ∈ r :=
  Iff.rfl
#align uniform_continuous_iff_eventually uniform_continuous_iff_eventually

theorem uniform_continuous_on_univ [UniformSpace β] {f : α → β} : UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]
#align uniform_continuous_on_univ uniform_continuous_on_univ

theorem uniform_continuous_of_const [UniformSpace β] {c : α → β} (h : ∀ a b, c a = c b) : UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' idRel = univ := eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this, univ_mem]) refl_le_uniformity
#align uniform_continuous_of_const uniform_continuous_of_const

theorem uniform_continuous_id : UniformContinuous (@id α) := by simp [UniformContinuous] <;> exact tendsto_id
#align uniform_continuous_id uniform_continuous_id

theorem uniform_continuous_const [UniformSpace β] {b : β} : UniformContinuous fun a : α => b :=
  uniform_continuous_of_const fun _ _ => rfl
#align uniform_continuous_const uniform_continuous_const

theorem UniformContinuous.comp [UniformSpace β] [UniformSpace γ] {g : β → γ} {f : α → β} (hg : UniformContinuous g)
    (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf
#align uniform_continuous.comp UniformContinuous.comp

theorem Filter.HasBasis.uniform_continuous_iff [UniformSpace β] {p : γ → Prop} {s : γ → Set (α × α)}
    (ha : (𝓤 α).HasBasis p s) {q : δ → Prop} {t : δ → Set (β × β)} (hb : (𝓤 β).HasBasis q t) {f : α → β} :
    UniformContinuous f ↔ ∀ (i) (hi : q i), ∃ (j : _)(hj : p j), ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
  (ha.tendsto_iff hb).trans <| by simp only [Prod.forall]
#align filter.has_basis.uniform_continuous_iff Filter.HasBasis.uniform_continuous_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Basic.lean:611:2: warning: expanding binder collection (x y «expr ∈ » S) -/
theorem Filter.HasBasis.uniform_continuous_on_iff [UniformSpace β] {p : γ → Prop} {s : γ → Set (α × α)}
    (ha : (𝓤 α).HasBasis p s) {q : δ → Prop} {t : δ → Set (β × β)} (hb : (𝓤 β).HasBasis q t) {f : α → β} {S : Set α} :
    UniformContinuousOn f S ↔
      ∀ (i) (hi : q i), ∃ (j : _)(hj : p j), ∀ (x y) (_ : x ∈ S) (_ : y ∈ S), (x, y) ∈ s j → (f x, f y) ∈ t i :=
  ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans <| by
    simp_rw [Prod.forall, Set.inter_comm (s _), ball_mem_comm, mem_inter_iff, mem_prod, and_imp]
#align filter.has_basis.uniform_continuous_on_iff Filter.HasBasis.uniform_continuous_on_iff

end UniformSpace

open uniformity

section Constructions

instance : PartialOrder (UniformSpace α) where
  le t s := t.uniformity ≤ s.uniformity
  le_antisymm t s h₁ h₂ := uniform_space_eq <| le_antisymm h₁ h₂
  le_refl t := le_rfl
  le_trans a b c h₁ h₂ := le_trans h₁ h₂

instance : HasInf (UniformSpace α) :=
  ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u ∈ s, @uniformity α u, refl := le_infi fun u => le_infi fun hu => u.refl,
        symm := le_infi fun u => le_infi fun hu => le_trans (map_mono <| infi_le_of_le _ <| infi_le _ hu) u.symm,
        comp :=
          le_infi fun u => le_infi fun hu => le_trans (lift'_mono (infi_le_of_le _ <| infi_le _ hu) <| le_rfl) u.comp }⟩

private theorem Inf_le {tt : Set (UniformSpace α)} {t : UniformSpace α} (h : t ∈ tt) : inf tt ≤ t :=
  show (⨅ u ∈ tt, @uniformity α u) ≤ t.uniformity from infi_le_of_le t <| infi_le _ h
#align Inf_le Inf_le

private theorem le_Inf {tt : Set (UniformSpace α)} {t : UniformSpace α} (h : ∀ t' ∈ tt, t ≤ t') : t ≤ inf tt :=
  show t.uniformity ≤ ⨅ u ∈ tt, @uniformity α u from le_infi fun t' => le_infi fun ht' => h t' ht'
#align le_Inf le_Inf

instance : HasTop (UniformSpace α) :=
  ⟨UniformSpace.ofCore { uniformity := ⊤, refl := le_top, symm := le_top, comp := le_top }⟩

instance : HasBot (UniformSpace α) :=
  ⟨{ toTopologicalSpace := ⊥, uniformity := 𝓟 idRel, refl := le_rfl, symm := by simp [tendsto] <;> apply subset.refl,
      comp := by
        rw [lift'_principal]
        · simp

        exact monotone_comp_rel monotone_id monotone_id,
      is_open_uniformity := fun s => by simp (config := { contextual := true }) [is_open_fold, subset_def, idRel] }⟩

instance : HasInf (UniformSpace α) :=
  ⟨fun u₁ u₂ =>
    @UniformSpace.replaceTopology _ (u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace)
        (UniformSpace.ofCore
          { uniformity := u₁.uniformity ⊓ u₂.uniformity, refl := le_inf u₁.refl u₂.refl, symm := u₁.symm.inf u₂.symm,
            comp := (lift'_inf_le _ _ _).trans <| inf_le_inf u₁.comp u₂.comp }) <|
      eq_of_nhds_eq_nhds fun a => by simpa only [nhds_inf, nhds_eq_comap_uniformity] using comap_inf.symm⟩

instance : CompleteLattice (UniformSpace α) :=
  { UniformSpace.partialOrder with sup := fun a b => inf { x | a ≤ x ∧ b ≤ x },
    le_sup_left := fun a b => le_Inf fun _ ⟨h, _⟩ => h, le_sup_right := fun a b => le_Inf fun _ ⟨_, h⟩ => h,
    sup_le := fun a b c h₁ h₂ => Inf_le ⟨h₁, h₂⟩, inf := (· ⊓ ·),
    le_inf := fun a b c h₁ h₂ => show a.uniformity ≤ _ from le_inf h₁ h₂,
    inf_le_left := fun a b => show _ ≤ a.uniformity from inf_le_left,
    inf_le_right := fun a b => show _ ≤ b.uniformity from inf_le_right, top := ⊤,
    le_top := fun a => show a.uniformity ≤ ⊤ from le_top, bot := ⊥, bot_le := fun u => u.refl,
    sup := fun tt => inf { t | ∀ t' ∈ tt, t' ≤ t }, le_Sup := fun s u h => le_Inf fun u' h' => h' u h,
    Sup_le := fun s u h => Inf_le h, inf := inf, le_Inf := fun s a hs => le_Inf hs, Inf_le := fun s a ha => Inf_le ha }

theorem infi_uniformity {ι : Sort _} {u : ι → UniformSpace α} : (infi u).uniformity = ⨅ i, (u i).uniformity :=
  show (⨅ (a) (h : ∃ i : ι, u i = a), a.uniformity) = _ from
    le_antisymm (le_infi fun i => infi_le_of_le (u i) <| infi_le _ ⟨i, rfl⟩)
      (le_infi fun a => le_infi fun ⟨i, (ha : u i = a)⟩ => ha ▸ infi_le _ _)
#align infi_uniformity infi_uniformity

theorem infi_uniformity' {ι : Sort _} {u : ι → UniformSpace α} : @uniformity α (infi u) = ⨅ i, @uniformity α (u i) :=
  infi_uniformity
#align infi_uniformity' infi_uniformity'

theorem inf_uniformity {u v : UniformSpace α} : (u ⊓ v).uniformity = u.uniformity ⊓ v.uniformity :=
  rfl
#align inf_uniformity inf_uniformity

theorem inf_uniformity' {u v : UniformSpace α} : @uniformity α (u ⊓ v) = @uniformity α u ⊓ @uniformity α v :=
  rfl
#align inf_uniformity' inf_uniformity'

instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩
#align inhabited_uniform_space inhabitedUniformSpace

instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩
#align inhabited_uniform_space_core inhabitedUniformSpaceCore

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`. -/
def UniformSpace.comap (f : α → β) (u : UniformSpace β) : UniformSpace α where
  uniformity := u.uniformity.comap fun p : α × α => (f p.1, f p.2)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  refl := le_trans (by simp <;> exact fun ⟨a, b⟩ (h : a = b) => h ▸ rfl) (comap_mono u.refl)
  symm := by simp [tendsto_comap_iff, Prod.swap, (· ∘ ·)] <;> exact tendsto_swap_uniformity.comp tendsto_comap
  comp :=
    le_trans
      (by
        rw [comap_lift'_eq, comap_lift'_eq2]
        exact lift'_mono' fun s hs ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
        exact monotone_comp_rel monotone_id monotone_id)
      (comap_mono u.comp)
  is_open_uniformity s := by
    change @IsOpen α (u.to_topological_space.induced f) s ↔ _
    simp [is_open_iff_nhds, nhds_induced, mem_nhds_uniformity_iff_right, Filter.comap, and_comm']
    refine' ball_congr fun x hx => ⟨_, _⟩
    · rintro ⟨t, hts, ht⟩
      refine' ⟨_, ht, _⟩
      rintro ⟨x₁, x₂⟩ h rfl
      exact hts (h rfl)

    · rintro ⟨t, ht, hts⟩
      exact
        ⟨{ y | (f x, y) ∈ t }, fun y hy => @hts (x, y) hy rfl, mem_nhds_uniformity_iff_right.1 <| mem_nhds_left _ ht⟩

#align uniform_space.comap UniformSpace.comap

theorem uniformity_comap [UniformSpace α] [UniformSpace β] {f : α → β}
    (h : ‹UniformSpace α› = UniformSpace.comap f ‹UniformSpace β›) : 𝓤 α = comap (Prod.map f f) (𝓤 β) := by
  rw [h]
  rfl
#align uniformity_comap uniformity_comap

theorem uniform_space_comap_id {α : Type _} : UniformSpace.comap (id : α → α) = id := by
  ext u <;> dsimp only [UniformSpace.comap, id] <;> rw [Prod.id_prod, Filter.comap_id]
#align uniform_space_comap_id uniform_space_comap_id

theorem UniformSpace.comap_comap {α β γ} [uγ : UniformSpace γ] {f : α → β} {g : β → γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) := by
  ext <;> dsimp only [UniformSpace.comap] <;> rw [Filter.comap_comap]
#align uniform_space.comap_comap UniformSpace.comap_comap

theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α → γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  uniform_space_eq comap_inf
#align uniform_space.comap_inf UniformSpace.comap_inf

theorem UniformSpace.comap_infi {ι α γ} {u : ι → UniformSpace γ} {f : α → γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f := by
  ext : 1
  change 𝓤 _ = 𝓤 _
  simp [uniformity_comap rfl, infi_uniformity']
#align uniform_space.comap_infi UniformSpace.comap_infi

theorem UniformSpace.comap_mono {α γ} {f : α → γ} : Monotone fun u : UniformSpace γ => u.comap f := by
  intro u₁ u₂ hu
  change 𝓤 _ ≤ 𝓤 _
  rw [uniformity_comap rfl]
  exact comap_mono hu
#align uniform_space.comap_mono UniformSpace.comap_mono

theorem uniform_continuous_iff {α β} {uα : UniformSpace α} {uβ : UniformSpace β} {f : α → β} :
    UniformContinuous f ↔ uα ≤ uβ.comap f :=
  Filter.map_le_iff_le_comap
#align uniform_continuous_iff uniform_continuous_iff

theorem le_iff_uniform_continuous_id {u v : UniformSpace α} : u ≤ v ↔ @UniformContinuous _ _ u v id := by
  rw [uniform_continuous_iff, uniform_space_comap_id, id]
#align le_iff_uniform_continuous_id le_iff_uniform_continuous_id

theorem uniform_continuous_comap {f : α → β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap
#align uniform_continuous_comap uniform_continuous_comap

theorem to_topological_space_comap {f : α → β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl
#align to_topological_space_comap to_topological_space_comap

theorem uniform_continuous_comap' {f : γ → β} {g : α → γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h
#align uniform_continuous_comap' uniform_continuous_comap'

theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a ≤ @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a := by
  rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a] <;> exact lift'_mono h le_rfl
#align to_nhds_mono to_nhds_mono

theorem to_topological_space_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ ≤ @UniformSpace.toTopologicalSpace _ u₂ :=
  le_of_nhds_le_nhds <| to_nhds_mono h
#align to_topological_space_mono to_topological_space_mono

theorem UniformContinuous.continuous [UniformSpace α] [UniformSpace β] {f : α → β} (hf : UniformContinuous f) :
    Continuous f :=
  continuous_iff_le_induced.mpr <| to_topological_space_mono <| uniform_continuous_iff.1 hf
#align uniform_continuous.continuous UniformContinuous.continuous

theorem to_topological_space_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ :=
  rfl
#align to_topological_space_bot to_topological_space_bot

theorem to_topological_space_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ :=
  top_unique fun s hs =>
    s.eq_empty_or_nonempty.elim (fun this : s = ∅ => this.symm ▸ @is_open_empty _ ⊤) fun ⟨x, hx⟩ =>
      have : s = univ := top_unique fun y hy => hs x hx (x, y) rfl
      this.symm ▸ @is_open_univ _ ⊤
#align to_topological_space_top to_topological_space_top

theorem to_topological_space_infi {ι : Sort _} {u : ι → UniformSpace α} :
    (infi u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace := by
  refine' eq_of_nhds_eq_nhds fun a => _
  rw [nhds_infi, nhds_eq_uniformity]
  change (infi u).uniformity.lift' (preimage <| Prod.mk a) = _
  rw [infi_uniformity, lift'_infi_of_map_univ _ preimage_univ]
  · simp only [nhds_eq_uniformity]
    rfl

  · exact ball_inter _

#align to_topological_space_infi to_topological_space_infi

theorem to_topological_space_Inf {s : Set (UniformSpace α)} :
    (inf s).toTopologicalSpace = ⨅ i ∈ s, @UniformSpace.toTopologicalSpace α i := by
  rw [Inf_eq_infi]
  simp only [← to_topological_space_infi]
#align to_topological_space_Inf to_topological_space_Inf

theorem to_topological_space_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl
#align to_topological_space_inf to_topological_space_inf

/-- Uniform space structure on `ulift α`. -/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›
#align ulift.uniform_space ULift.uniformSpace

section UniformContinuousInfi

theorem uniform_continuous_inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : @UniformContinuous u₁ u₂ f) (h₂ : @UniformContinuous u₁ u₃ f) : @UniformContinuous u₁ (u₂ ⊓ u₃) f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩
#align uniform_continuous_inf_rng uniform_continuous_inf_rng

theorem uniform_continuous_inf_dom_left {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : @UniformContinuous u₁ u₃ f) : @UniformContinuous (u₁ ⊓ u₂) u₃ f :=
  tendsto_inf_left hf
#align uniform_continuous_inf_dom_left uniform_continuous_inf_dom_left

theorem uniform_continuous_inf_dom_right {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : @UniformContinuous u₂ u₃ f) : @UniformContinuous (u₁ ⊓ u₂) u₃ f :=
  tendsto_inf_right hf
#align uniform_continuous_inf_dom_right uniform_continuous_inf_dom_right

theorem uniform_continuous_Inf_dom {f : α → β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β} {u : UniformSpace α}
    (h₁ : u ∈ u₁) (hf : @UniformContinuous u u₂ f) : @UniformContinuous (inf u₁) u₂ f := by
  rw [UniformContinuous, Inf_eq_infi', infi_uniformity']
  exact tendsto_infi' ⟨u, h₁⟩ hf
#align uniform_continuous_Inf_dom uniform_continuous_Inf_dom

theorem uniform_continuous_Inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)}
    (h : ∀ u ∈ u₂, @UniformContinuous u₁ u f) : @UniformContinuous u₁ (inf u₂) f := by
  rw [UniformContinuous, Inf_eq_infi', infi_uniformity']
  exact tendsto_infi.mpr fun ⟨u, hu⟩ => h u hu
#align uniform_continuous_Inf_rng uniform_continuous_Inf_rng

theorem uniform_continuous_infi_dom {f : α → β} {u₁ : ι → UniformSpace α} {u₂ : UniformSpace β} {i : ι}
    (hf : @UniformContinuous (u₁ i) u₂ f) : @UniformContinuous (infi u₁) u₂ f := by
  rw [UniformContinuous, infi_uniformity']
  exact tendsto_infi' i hf
#align uniform_continuous_infi_dom uniform_continuous_infi_dom

theorem uniform_continuous_infi_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : ι → UniformSpace β}
    (h : ∀ i, @UniformContinuous u₁ (u₂ i) f) : @UniformContinuous u₁ (infi u₂) f := by
  rwa [UniformContinuous, infi_uniformity', tendsto_infi]
#align uniform_continuous_infi_rng uniform_continuous_infi_rng

end UniformContinuousInfi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
theorem discreteTopologyOfDiscreteUniformity [hα : UniformSpace α] (h : uniformity α = 𝓟 idRel) : DiscreteTopology α :=
  ⟨(uniform_space_eq h.symm : ⊥ = hα) ▸ rfl⟩
#align discrete_topology_of_discrete_uniformity discreteTopologyOfDiscreteUniformity

instance : UniformSpace Empty :=
  ⊥

instance : UniformSpace PUnit :=
  ⊥

instance : UniformSpace Bool :=
  ⊥

instance : UniformSpace ℕ :=
  ⊥

instance : UniformSpace ℤ :=
  ⊥

section

variable [UniformSpace α]

open Additive Multiplicative

instance : UniformSpace (Additive α) :=
  ‹UniformSpace α›

instance : UniformSpace (Multiplicative α) :=
  ‹UniformSpace α›

theorem uniform_continuous_of_mul : UniformContinuous (ofMul : α → Additive α) :=
  uniform_continuous_id
#align uniform_continuous_of_mul uniform_continuous_of_mul

theorem uniform_continuous_to_mul : UniformContinuous (toMul : Additive α → α) :=
  uniform_continuous_id
#align uniform_continuous_to_mul uniform_continuous_to_mul

theorem uniform_continuous_of_add : UniformContinuous (ofAdd : α → Multiplicative α) :=
  uniform_continuous_id
#align uniform_continuous_of_add uniform_continuous_of_add

theorem uniform_continuous_to_add : UniformContinuous (toAdd : Multiplicative α → α) :=
  uniform_continuous_id
#align uniform_continuous_to_add uniform_continuous_to_add

theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) := by
  convert map_id.symm
  exact Prod.map_id
#align uniformity_additive uniformity_additive

theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) := by
  convert map_id.symm
  exact Prod.map_id
#align uniformity_multiplicative uniformity_multiplicative

end

instance {p : α → Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

theorem uniformity_subtype {p : α → Prop} [t : UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl
#align uniformity_subtype uniformity_subtype

theorem uniform_continuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } → α) :=
  uniform_continuous_comap
#align uniform_continuous_subtype_val uniform_continuous_subtype_val

theorem uniform_continuous_subtype_coe {p : α → Prop} [UniformSpace α] :
    UniformContinuous (coe : { a : α // p a } → α) :=
  uniform_continuous_subtype_val
#align uniform_continuous_subtype_coe uniform_continuous_subtype_coe

theorem UniformContinuous.subtype_mk {p : α → Prop} [UniformSpace α] [UniformSpace β] {f : β → α}
    (hf : UniformContinuous f) (h : ∀ x, p (f x)) : UniformContinuous (fun x => ⟨f x, h x⟩ : β → Subtype p) :=
  uniform_continuous_comap' hf
#align uniform_continuous.subtype_mk UniformContinuous.subtype_mk

theorem uniform_continuous_on_iff_restrict [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.restrict f) := by
  unfold UniformContinuousOn Set.restrict UniformContinuous tendsto
  rw [show (fun x : s × s => (f x.1, f x.2)) = Prod.map f f ∘ coe by ext x <;> cases x <;> rfl, uniformity_comap rfl,
    show Prod.map Subtype.val Subtype.val = (coe : s × s → α × α) by ext x <;> cases x <;> rfl]
  conv in map _ (comap _ _) => rw [← Filter.map_map]
  rw [subtype_coe_map_comap_prod]
  rfl
#align uniform_continuous_on_iff_restrict uniform_continuous_on_iff_restrict

theorem tendsto_of_uniform_continuous_subtype [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} {a : α}
    (hf : UniformContinuous fun x : s => f x.val) (ha : s ∈ 𝓝 a) : Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq α _ s a (mem_of_mem_nhds ha) ha).symm] <;>
    exact tendsto_map' (continuous_iff_continuous_at.mp hf.continuous _)
#align tendsto_of_uniform_continuous_subtype tendsto_of_uniform_continuous_subtype

theorem UniformContinuousOn.continuous_on [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniform_continuous_on_iff_restrict] at h
  rw [continuous_on_iff_continuous_restrict]
  exact h.continuous
#align uniform_continuous_on.continuous_on UniformContinuousOn.continuous_on

@[to_additive]
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]
theorem uniformity_mul_opposite [UniformSpace α] : 𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl
#align uniformity_mul_opposite uniformity_mul_opposite

@[simp, to_additive]
theorem comap_uniformity_mul_opposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mul_opposite, comap_comap, (· ∘ ·)] using comap_id
#align comap_uniformity_mul_opposite comap_uniformity_mul_opposite

namespace MulOpposite

@[to_additive]
theorem uniform_continuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ → α) :=
  uniform_continuous_comap
#align mul_opposite.uniform_continuous_unop MulOpposite.uniform_continuous_unop

@[to_additive]
theorem uniform_continuous_op [UniformSpace α] : UniformContinuous (op : α → αᵐᵒᵖ) :=
  uniform_continuous_comap' uniform_continuous_id
#align mul_opposite.uniform_continuous_op MulOpposite.uniform_continuous_op

end MulOpposite

section Prod

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance [u₁ : UniformSpace α] [u₂ : UniformSpace β] : UniformSpace (α × β) :=
  u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

-- check the above produces no diamond
example [u₁ : UniformSpace α] [u₂ : UniformSpace β] :
    (Prod.topologicalSpace : TopologicalSpace (α × β)) = UniformSpace.toTopologicalSpace :=
  rfl

theorem uniformity_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓ (𝓤 β).comap fun p : (α × β) × α × β => (p.1.2, p.2.2) :=
  rfl
#align uniformity_prod uniformity_prod

theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ᶠ 𝓤 β) := by
  rw [uniformity_prod, Filter.prod, comap_inf, comap_comap, comap_comap]
#align uniformity_prod_eq_comap_prod uniformity_prod_eq_comap_prod

theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ᶠ 𝓤 β) := by
  rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]
#align uniformity_prod_eq_prod uniformity_prod_eq_prod

theorem mem_uniformity_of_uniform_continuous_invariant [UniformSpace α] [UniformSpace β] {s : Set (β × β)}
    {f : α → α → β} (hf : UniformContinuous fun p : α × α => f p.1 p.2) (hs : s ∈ 𝓤 β) :
    ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s := by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, (· ∘ ·)] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩
#align mem_uniformity_of_uniform_continuous_invariant mem_uniformity_of_uniform_continuous_invariant

theorem mem_uniform_prod [t₁ : UniformSpace α] [t₂ : UniformSpace β] {a : Set (α × α)} {b : Set (β × β)} (ha : a ∈ 𝓤 α)
    (hb : b ∈ 𝓤 β) : { p : (α × β) × α × β | (p.1.1, p.2.1) ∈ a ∧ (p.1.2, p.2.2) ∈ b } ∈ @uniformity (α × β) _ := by
  rw [uniformity_prod] <;> exact inter_mem_inf (preimage_mem_comap ha) (preimage_mem_comap hb)
#align mem_uniform_prod mem_uniform_prod

theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le
#align tendsto_prod_uniformity_fst tendsto_prod_uniformity_fst

theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le
#align tendsto_prod_uniformity_snd tendsto_prod_uniformity_snd

theorem uniform_continuous_fst [UniformSpace α] [UniformSpace β] : UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst
#align uniform_continuous_fst uniform_continuous_fst

theorem uniform_continuous_snd [UniformSpace α] [UniformSpace β] : UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd
#align uniform_continuous_snd uniform_continuous_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

theorem UniformContinuous.prod_mk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁) (h₂ : UniformContinuous f₂) :
    UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous, uniformity_prod] <;> exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩
#align uniform_continuous.prod_mk UniformContinuous.prod_mk

theorem UniformContinuous.prod_mk_left {f : α × β → γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniform_continuous_id.prod_mk uniform_continuous_const)
#align uniform_continuous.prod_mk_left UniformContinuous.prod_mk_left

theorem UniformContinuous.prod_mk_right {f : α × β → γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniform_continuous_const.prod_mk uniform_continuous_id)
#align uniform_continuous.prod_mk_right UniformContinuous.prod_mk_right

theorem UniformContinuous.prod_map [UniformSpace δ] {f : α → γ} {g : β → δ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniform_continuous_fst).prod_mk (hg.comp uniform_continuous_snd)
#align uniform_continuous.prod_map UniformContinuous.prod_map

theorem to_topological_space_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) Prod.uniformSpace =
      @Prod.topologicalSpace α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl
#align to_topological_space_prod to_topological_space_prod

/-- A version of `uniform_continuous_inf_dom_left` for binary functions -/
theorem uniform_continuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α} {ub1 ub2 : UniformSpace β}
    {uc1 : UniformSpace γ}
    (h : by haveI := ua1 <;> haveI := ub1 <;> exact UniformContinuous fun p : α × β => f p.1 p.2) : by
    haveI := ua1 ⊓ ua2 <;> haveI := ub1 ⊓ ub2 <;> exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from ``continuous_inf_dom_left₂`
  have ha := @uniform_continuous_inf_dom_left _ _ id ua1 ua2 ua1 (@uniform_continuous_id _ (id _))
  have hb := @uniform_continuous_inf_dom_left _ _ id ub1 ub2 ub1 (@uniform_continuous_id _ (id _))
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id
#align uniform_continuous_inf_dom_left₂ uniform_continuous_inf_dom_left₂

/-- A version of `uniform_continuous_inf_dom_right` for binary functions -/
theorem uniform_continuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α} {ub1 ub2 : UniformSpace β}
    {uc1 : UniformSpace γ}
    (h : by haveI := ua2 <;> haveI := ub2 <;> exact UniformContinuous fun p : α × β => f p.1 p.2) : by
    haveI := ua1 ⊓ ua2 <;> haveI := ub1 ⊓ ub2 <;> exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from ``continuous_inf_dom_right₂`
  have ha := @uniform_continuous_inf_dom_right _ _ id ua1 ua2 ua2 (@uniform_continuous_id _ (id _))
  have hb := @uniform_continuous_inf_dom_right _ _ id ub1 ub2 ub2 (@uniform_continuous_id _ (id _))
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id
#align uniform_continuous_inf_dom_right₂ uniform_continuous_inf_dom_right₂

/-- A version of `uniform_continuous_Inf_dom` for binary functions -/
theorem uniform_continuous_Inf_dom₂ {α β γ} {f : α → β → γ} {uas : Set (UniformSpace α)} {ubs : Set (UniformSpace β)}
    {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ} (ha : ua ∈ uas) (hb : ub ∈ ubs)
    (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
    haveI := Inf uas <;> haveI := Inf ubs <;> exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from ``continuous_Inf_dom`
  let t : UniformSpace (α × β) := Prod.uniformSpace
  have ha := uniform_continuous_Inf_dom ha uniform_continuous_id
  have hb := uniform_continuous_Inf_dom hb uniform_continuous_id
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (Inf uas) (Inf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id
#align uniform_continuous_Inf_dom₂ uniform_continuous_Inf_dom₂

end Prod

section

open UniformSpace Function

variable {δ' : Type _} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ] [UniformSpace δ']

-- mathport name: «expr ∘₂ »
local notation f " ∘₂ " g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def UniformContinuous₂ (f : α → β → γ) :=
  UniformContinuous (uncurry f)
#align uniform_continuous₂ UniformContinuous₂

theorem uniform_continuous₂_def (f : α → β → γ) : UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl
#align uniform_continuous₂_def uniform_continuous₂_def

theorem UniformContinuous₂.uniform_continuous {f : α → β → γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h
#align uniform_continuous₂.uniform_continuous UniformContinuous₂.uniform_continuous

theorem uniform_continuous₂_curry (f : α × β → γ) : UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂, uncurry_curry]
#align uniform_continuous₂_curry uniform_continuous₂_curry

theorem UniformContinuous₂.comp {f : α → β → γ} {g : γ → δ} (hg : UniformContinuous g) (hf : UniformContinuous₂ f) :
    UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf
#align uniform_continuous₂.comp UniformContinuous₂.comp

theorem UniformContinuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β} (hf : UniformContinuous₂ f)
    (hga : UniformContinuous ga) (hgb : UniformContinuous gb) : UniformContinuous₂ (bicompl f ga gb) :=
  hf.UniformContinuous.comp (hga.prod_map hgb)
#align uniform_continuous₂.bicompl UniformContinuous₂.bicompl

end

theorem to_topological_space_subtype [u : UniformSpace α] {p : α → Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) Subtype.uniformSpace =
      @Subtype.topologicalSpace α p u.toTopologicalSpace :=
  rfl
#align to_topological_space_subtype to_topological_space_subtype

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def UniformSpace.Core.sum : UniformSpace.Core (Sum α β) :=
  UniformSpace.Core.mk'
    (map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔ map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β))
    (fun r ⟨H₁, H₂⟩ x => by cases x <;> [apply refl_mem_uniformity H₁, apply refl_mem_uniformity H₂])
    (fun r ⟨H₁, H₂⟩ => ⟨symm_le_uniformity H₁, symm_le_uniformity H₂⟩) fun r ⟨Hrα, Hrβ⟩ => by
    rcases comp_mem_uniformity_sets Hrα with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets Hrβ with ⟨tβ, htβ, Htβ⟩
    refine'
      ⟨_,
        ⟨mem_map_iff_exists_image.2 ⟨tα, htα, subset_union_left _ _⟩,
          mem_map_iff_exists_image.2 ⟨tβ, htβ, subset_union_right _ _⟩⟩,
        _⟩
    rintro ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩, ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩
    · have A : (a, c) ∈ tα ○ tα := ⟨b, hab, hbc⟩
      exact Htα A

    · have A : (a, c) ∈ tβ ○ tβ := ⟨b, hab, hbc⟩
      exact Htβ A

#align uniform_space.core.sum UniformSpace.Core.sum

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {a : Set (α × α)} (ha : a ∈ 𝓤 α) {b : Set (β × β)} (hb : b ∈ 𝓤 β) :
    (fun p : α × α => (inl p.1, inl p.2)) '' a ∪ (fun p : β × β => (inr p.1, inr p.2)) '' b ∈
      (@UniformSpace.Core.sum α β _ _).uniformity :=
  ⟨mem_map_iff_exists_image.2 ⟨_, ha, subset_union_left _ _⟩,
    mem_map_iff_exists_image.2 ⟨_, hb, subset_union_right _ _⟩⟩
#align union_mem_uniformity_sum union_mem_uniformity_sum

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/
theorem uniformity_sum_of_open_aux {s : Set (Sum α β)} (hs : IsOpen s) {x : Sum α β} (xs : x ∈ s) :
    { p : Sum α β × Sum α β | p.1 = x → p.2 ∈ s } ∈ (@UniformSpace.Core.sum α β _ _).uniformity := by
  cases x
  · refine'
        mem_of_superset (union_mem_uniformity_sum (mem_nhds_uniformity_iff_right.1 (IsOpen.mem_nhds hs.1 xs)) univ_mem)
          (union_subset _ _) <;>
      rintro _ ⟨⟨_, b⟩, h, ⟨⟩⟩ ⟨⟩
    exact h rfl

  · refine'
        mem_of_superset (union_mem_uniformity_sum univ_mem (mem_nhds_uniformity_iff_right.1 (IsOpen.mem_nhds hs.2 xs)))
          (union_subset _ _) <;>
      rintro _ ⟨⟨a, _⟩, h, ⟨⟩⟩ ⟨⟩
    exact h rfl

#align uniformity_sum_of_open_aux uniformity_sum_of_open_aux

theorem open_of_uniformity_sum_aux {s : Set (Sum α β)}
    (hs : ∀ x ∈ s, { p : Sum α β × Sum α β | p.1 = x → p.2 ∈ s } ∈ (@UniformSpace.Core.sum α β _ _).uniformity) :
    IsOpen s := by
  constructor
  · refine' (@is_open_iff_mem_nhds α _ _).2 fun a ha => mem_nhds_uniformity_iff_right.2 _
    rcases mem_map_iff_exists_image.1 (hs _ ha).1 with ⟨t, ht, st⟩
    refine' mem_of_superset ht _
    rintro p pt rfl
    exact st ⟨_, pt, rfl⟩ rfl

  · refine' (@is_open_iff_mem_nhds β _ _).2 fun b hb => mem_nhds_uniformity_iff_right.2 _
    rcases mem_map_iff_exists_image.1 (hs _ hb).2 with ⟨t, ht, st⟩
    refine' mem_of_superset ht _
    rintro p pt rfl
    exact st ⟨_, pt, rfl⟩ rfl

#align open_of_uniformity_sum_aux open_of_uniformity_sum_aux

-- We can now define the uniform structure on the disjoint union
instance Sum.uniformSpace : UniformSpace (Sum α β) where
  toCore := UniformSpace.Core.sum
  is_open_uniformity s := ⟨uniformity_sum_of_open_aux, open_of_uniformity_sum_aux⟩
#align sum.uniform_space Sum.uniformSpace

theorem Sum.uniformity :
    𝓤 (Sum α β) = map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔ map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β) :=
  rfl
#align sum.uniformity Sum.uniformity

end Sum

end Constructions

-- For a version of the Lebesgue number lemma assuming only a sequentially compact space,
-- see topology/sequences.lean
/-- Let `c : ι → set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {α : Type u} [UniformSpace α] {s : Set α} {ι} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ i, { y | (x, y) ∈ n } ⊆ c i := by
  let u n := { x | ∃ i, ∃ m ∈ 𝓤 α, { y | (x, y) ∈ m ○ n } ⊆ c i }
  have hu₁ : ∀ n ∈ 𝓤 α, IsOpen (u n) := by
    refine' fun n hn => is_open_uniformity.2 _
    rintro x ⟨i, m, hm, h⟩
    rcases comp_mem_uniformity_sets hm with ⟨m', hm', mm'⟩
    apply (𝓤 α).sets_of_superset hm'
    rintro ⟨x, y⟩ hp rfl
    refine' ⟨i, m', hm', fun z hz => h (monotone_comp_rel monotone_id monotone_const mm' _)⟩
    dsimp [-mem_comp_rel] at hz⊢
    rw [comp_rel_assoc]
    exact ⟨y, hp, hz⟩
  have hu₂ : s ⊆ ⋃ n ∈ 𝓤 α, u n := by
    intro x hx
    rcases mem_Union.1 (hc₂ hx) with ⟨i, h⟩
    rcases comp_mem_uniformity_sets (is_open_uniformity.1 (hc₁ i) x h) with ⟨m', hm', mm'⟩
    exact mem_bUnion hm' ⟨i, _, hm', fun y hy => mm' hy rfl⟩
  rcases hs.elim_finite_subcover_image hu₁ hu₂ with ⟨b, bu, b_fin, b_cover⟩
  refine' ⟨_, (bInter_mem b_fin).2 bu, fun x hx => _⟩
  rcases mem_Union₂.1 (b_cover hx) with ⟨n, bn, i, m, hm, h⟩
  refine' ⟨i, fun y hy => h _⟩
  exact prod_mk_mem_comp_rel (refl_mem_uniformity hm) (bInter_subset_of_mem bn hy)
#align lebesgue_number_lemma lebesgue_number_lemma

/-- Let `c : set (set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
theorem lebesgue_number_lemma_sUnion {α : Type u} [UniformSpace α] {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀c) : ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ t ∈ c, ∀ y, (x, y) ∈ n → y ∈ t := by
  rw [sUnion_eq_Union] at hc₂ <;> simpa using lebesgue_number_lemma hs (by simpa) hc₂
#align lebesgue_number_lemma_sUnion lebesgue_number_lemma_sUnion

/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
theorem lebesgue_number_of_compact_open [UniformSpace α] {K U : Set α} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓤 α, IsOpen V ∧ ∀ x ∈ K, UniformSpace.ball x V ⊆ U := by
  let W : K → Set (α × α) := fun k => Classical.choose <| is_open_iff_open_ball_subset.mp hU k.1 <| hKU k.2
  have hW : ∀ k, W k ∈ 𝓤 α ∧ IsOpen (W k) ∧ UniformSpace.ball k.1 (W k) ⊆ U := by
    intro k
    obtain ⟨h₁, h₂, h₃⟩ := Classical.choose_spec (is_open_iff_open_ball_subset.mp hU k.1 (hKU k.2))
    exact ⟨h₁, h₂, h₃⟩
  let c : K → Set α := fun k => UniformSpace.ball k.1 (W k)
  have hc₁ : ∀ k, IsOpen (c k) := fun k => UniformSpace.is_open_ball k.1 (hW k).2.1
  have hc₂ : K ⊆ ⋃ i, c i := by
    intro k hk
    simp only [mem_Union, SetCoe.exists]
    exact ⟨k, hk, UniformSpace.mem_ball_self k (hW ⟨k, hk⟩).1⟩
  have hc₃ : ∀ k, c k ⊆ U := fun k => (hW k).2.2
  obtain ⟨V, hV, hV'⟩ := lebesgue_number_lemma hK hc₁ hc₂
  refine' ⟨interior V, interior_mem_uniformity hV, is_open_interior, _⟩
  intro k hk
  obtain ⟨k', hk'⟩ := hV' k hk
  exact ((ball_mono interior_subset k).trans hk').trans (hc₃ k')
#align lebesgue_number_of_compact_open lebesgue_number_of_compact_open

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace α]

theorem tendsto_nhds_right {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α) :=
  ⟨fun H => tendsto_left_nhds_uniformity.comp H, fun H s hs => by
    simpa [mem_of_mem_nhds hs] using H (mem_nhds_uniformity_iff_right.1 hs)⟩
#align uniform.tendsto_nhds_right Uniform.tendsto_nhds_right

theorem tendsto_nhds_left {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) :=
  ⟨fun H => tendsto_right_nhds_uniformity.comp H, fun H s hs => by
    simpa [mem_of_mem_nhds hs] using H (mem_nhds_uniformity_iff_left.1 hs)⟩
#align uniform.tendsto_nhds_left Uniform.tendsto_nhds_left

theorem continuous_at_iff'_right [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by rw [ContinuousAt, tendsto_nhds_right]
#align uniform.continuous_at_iff'_right Uniform.continuous_at_iff'_right

theorem continuous_at_iff'_left [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by rw [ContinuousAt, tendsto_nhds_left]
#align uniform.continuous_at_iff'_left Uniform.continuous_at_iff'_left

theorem continuous_at_iff_prod [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prod_map' H) (nhds_le_uniformity _), fun H =>
    continuous_at_iff'_left.2 <| H.comp <| tendsto_id.prod_mk_nhds tendsto_const_nhds⟩
#align uniform.continuous_at_iff_prod Uniform.continuous_at_iff_prod

theorem continuous_within_at_iff'_right [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]
#align uniform.continuous_within_at_iff'_right Uniform.continuous_within_at_iff'_right

theorem continuous_within_at_iff'_left [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]
#align uniform.continuous_within_at_iff'_left Uniform.continuous_within_at_iff'_left

theorem continuous_on_iff'_right [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuous_within_at_iff'_right]
#align uniform.continuous_on_iff'_right Uniform.continuous_on_iff'_right

theorem continuous_on_iff'_left [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuous_within_at_iff'_left]
#align uniform.continuous_on_iff'_left Uniform.continuous_on_iff'_left

theorem continuous_iff'_right [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuous_at.trans <| forall_congr' fun b => tendsto_nhds_right
#align uniform.continuous_iff'_right Uniform.continuous_iff'_right

theorem continuous_iff'_left [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuous_at.trans <| forall_congr' fun b => tendsto_nhds_left
#align uniform.continuous_iff'_left Uniform.continuous_iff'_left

end Uniform

theorem Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto g l (𝓝 b) :=
  Uniform.tendsto_nhds_right.2 <| (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg
#align filter.tendsto.congr_uniformity Filter.Tendsto.congr_uniformity

theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩
#align uniform.tendsto_congr Uniform.tendsto_congr