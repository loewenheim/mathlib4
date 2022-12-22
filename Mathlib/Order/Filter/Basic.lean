/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
! This file was ported from Lean 3 source module order.filter.basic
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Mathport.Syntax
--import Mathlib.Control.Traversable.Instances
--import Mathlib.Data.Set.Finite
--import Mathlib.Order.Copy
--import Mathlib.Tactic.Monotonicity.Default

/-!
# Theory of filters on sets
## Main definitions
* `filter` : filters on a set;
* `at_top`, `at_bot`, `cofinite`, `principal` : specific filters;
* `map`, `comap` : operations on filters;
* `tendsto` : limit with respect to filters;
* `eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` : takes a list of proofs `hᵢ : sᵢ ∈ f`, and replaces a goal `s ∈ f`
  with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `ne_bot f` : an utility class stating that `f` is a non-trivial filter.
Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...
In this file, we define the type `filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `set (set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `filter` is a monadic functor, with a push-forward operation
`filter.map` and a pull-back operation `filter.comap` that form a Galois connections for the
order on filters.
The examples of filters appearing in the description of the two motivating ideas are:
* `(at_top : filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in topology.uniform_space.basic)
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `measure_theory.measure_space`)
The general notion of limit of a map with respect to filters on the source and target types
is `filter.tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `filter.eventually`, and "happening often" is
`filter.frequently`, whose definitions are immediate after `filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).
For instance, anticipating on topology.basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from topology.basic.
## Notations
* `∀ᶠ x in f, p x` : `f.eventually p`;
* `∃ᶠ x in f, p x` : `f.frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `principal s`, localized in `filter`.
## References
*  [N. Bourbaki, *General Topology*][bourbaki1966]
Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[ne_bot f]` in a number of lemmas and definitions.
-/


open Function Set --Order

universe u v w x y

open Classical

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type _) where
  sets : Set (Set α)
  univ_sets : Set.univ ∈ sets
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
#align filter Filter

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
instance {α : Type _} : Membership (Set α) (Filter α) :=
  ⟨fun U F => U ∈ F.sets⟩

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

@[simp]
protected theorem mem_mk {t : Set (Set α)} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  Iff.rfl
#align filter.mem_mk Filter.mem_mk

@[simp]
protected theorem mem_sets : s ∈ f.sets ↔ s ∈ f :=
  Iff.rfl
#align filter.mem_sets Filter.mem_sets

instance inhabitedMem : Inhabited { s : Set α // s ∈ f } :=
  ⟨⟨univ, f.univ_sets⟩⟩
#align filter.inhabited_mem Filter.inhabitedMem

theorem filter_eq : ∀ {f g : Filter α}, f.sets = g.sets → f = g
  | ⟨_ , _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
#align filter.filter_eq Filter.filter_eq

theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congrArg _, filter_eq⟩
#align filter.filter_eq_iff Filter.filter_eq_iff

protected theorem ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g := by
  simp only [filter_eq_iff, ext_iff, Filter.mem_sets]
#align filter.ext_iff Filter.ext_iff

@[ext]
protected theorem ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
  Filter.ext_iff.2
#align filter.ext Filter.ext

/-- An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ f` (e.g.,
`filter.comap`, `filter.coprod`, `filter.Coprod`, `filter.cofinite`). -/
protected theorem coext (h : ∀ s, sᶜ ∈ f ↔ sᶜ ∈ g) : f = g :=
  Filter.ext <| compl_surjective.forall.2 h
#align filter.coext Filter.coext

@[simp]
theorem univ_mem : univ ∈ f :=
  f.univ_sets
#align filter.univ_mem Filter.univ_mem

theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy
#align filter.mem_of_superset Filter.mem_of_superset

theorem inter_mem {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  f.inter_sets hs ht
#align filter.inter_mem Filter.inter_mem

@[simp]
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
  ⟨fun h => ⟨mem_of_superset h (inter_subset_left s t), mem_of_superset h (inter_subset_right s t)⟩,
    and_imp.2 inter_mem⟩
#align filter.inter_mem_iff Filter.inter_mem_iff

theorem diff_mem {s t : Set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
  inter_mem hs ht
#align filter.diff_mem Filter.diff_mem

theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x
#align filter.univ_mem' Filter.univ_mem'

theorem mp_mem (hs : s ∈ f) (h : { x | x ∈ s → x ∈ t } ∈ f) : t ∈ f :=
  (mem_of_superset (inter_mem hs h)) fun _ ⟨h₁, h₂⟩ => h₂ h₁
#align filter.mp_mem Filter.mp_mem

theorem congr_sets (h : { x | x ∈ s ↔ x ∈ t } ∈ f) : s ∈ f ↔ t ∈ f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun _ => Iff.mp), fun hs =>
    mp_mem hs (mem_of_superset h fun _ => Iff.mpr)⟩
#align filter.congr_sets Filter.congr_sets

theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨_, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩
#align filter.exists_mem_subset_iff Filter.exists_mem_subset_iff

theorem monotone_mem {f : Filter α} : Monotone fun s => s ∈ f := fun _ _ hst h =>
  mem_of_superset h hst
#align filter.monotone_mem Filter.monotone_mem

theorem exists_mem_and_iff {P : Set α → Prop} {Q : Set α → Prop} (hP : Antitone P)
    (hQ : Antitone Q) : ((∃ u ∈ f, P u) ∧ ∃ u ∈ f, Q u) ↔ ∃ u ∈ f, P u ∧ Q u := by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact
      ⟨u ∩ v, inter_mem huf hvf, hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩
#align filter.exists_mem_and_iff Filter.exists_mem_and_iff

theorem forall_in_swap {β : Type _} {p : Set α → β → Prop} :
    (∀ a ∈ f, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ f, p a b :=
  Set.forall_in_swap
#align filter.forall_in_swap Filter.forall_in_swap

end Filter

namespace Lean.Parser.Tactic

open Elab.Tactic

syntax (name := filterUpwards) "filter_upwards" (Lean.Parser.Tactic.termList)?
  (" with" (colGt term:max)*)? (" using" term)? : tactic

--syntax (name := filterUpwardsWIP) "filter_upwards_wip" (termList)?
--  (" with" (colGt term:max)*)? (" using" term)? : tactic

elab_rules : tactic
| `(tactic| filter_upwards $[[$args,*]]? $[with $wth*]? $[using $usingArg]?) => do
  for (e : Term) in ((args.map (Array.toList ∘ Coe.coe)).getD []).reverse do
    let apply_param ← elabTerm (← `(Filter.mp_mem $e)) Option.none
    liftMetaTactic fun goal => do
      goal.apply apply_param {newGoals := Meta.ApplyNewGoals.nonDependentOnly}
  let apply_param ← elabTerm (← `(Filter.univ_mem')) Option.none
  liftMetaTactic fun goal => do
    Lean.MVarId.apply goal apply_param {newGoals := Meta.ApplyNewGoals.nonDependentOnly}
  evalTactic <|← `(tactic| dsimp only [mem_setOf_eq])
  match wth with
  | some l => evalTactic <|← `(tactic| intro $[$l]*)
  | none   => evalTactic <|← `(tactic| skip)
  match usingArg with
  | some e => evalTactic <|← `(tactic| exact $e)
  | none   => evalTactic <|← `(tactic| skip)

end Lean.Parser.Tactic

lemma test (f : Filter α) (s t : Set α) (hs : s ∈ f) (ht : t ∈ f) :
    s ∩ t ∈ f := by
  filter_upwards [hs, ht] with x hxs hxt using ⟨hxs, hxt⟩
