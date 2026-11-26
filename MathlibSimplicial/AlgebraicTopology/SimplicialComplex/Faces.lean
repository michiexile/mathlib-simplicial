/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset

/-!
# Faces, vertices, facets and the f-vector of an abstract simplicial complex

Mathlib's `PreAbstractSimplicialComplex ι` (in
`Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean`) is a downward-closed family of nonempty
`Finset ι`s, with a complete-lattice structure and nothing else. This file starts the basic API
(step 1 of the roadmap in `README.md`): vertices, facets, the faces of a given dimension, and for
finite vertex types the f-vector and the combinatorial Euler characteristic.

We work with `PreAbstractSimplicialComplex` rather than `AbstractSimplicialComplex` because its
vertex set may be a proper subset of `ι`. That is what subcomplexes, links, stars and the
filtrations of topological data analysis need, and it matches the definition used by
Cunningham–Zach–Friedl.

## Conventions

A face `s` has *dimension* `s.card - 1`, so the faces of dimension `n` are those with `n + 1`
vertices.

## Main declarations

* `PreAbstractSimplicialComplex.vertices K`: the `v` with `{v} ∈ K`.
* `PreAbstractSimplicialComplex.facets K`: the maximal faces.
* `PreAbstractSimplicialComplex.facesOfDim K n`: the faces of dimension `n`, as a `Set`.
* `PreAbstractSimplicialComplex.finsetFacesOfDim K n`: the same, as a `Finset`, for finite `ι`.
* `PreAbstractSimplicialComplex.fVector K n`: the number of `n`-dimensional faces.
* `PreAbstractSimplicialComplex.eulerChar K`: the alternating sum `∑ (-1)ⁿ fₙ`.
-/

@[expose] public section

open Finset

variable {ι : Type*}

namespace PreAbstractSimplicialComplex

variable (K : PreAbstractSimplicialComplex ι) {s t : Finset ι} {v : ι}

/-! ### Basic membership lemmas

`s ∈ K` comes from Mathlib's `SetLike` instance and unfolds to `s ∈ K.faces`. -/

theorem mem_faces : s ∈ K.faces ↔ s ∈ K := Iff.rfl

/-- Every face is nonempty. -/
theorem nonempty_of_mem (hs : s ∈ K) : s.Nonempty :=
  (K.isRelLowerSet_faces hs).1

/-- The empty set is never a face. -/
theorem empty_notMem : (∅ : Finset ι) ∉ K := fun h ↦
  (K.nonempty_of_mem h).ne_empty rfl

/-- Faces are downward closed: a nonempty subset of a face is a face. -/
theorem mem_of_subset (hs : s ∈ K) (hts : t ⊆ s) (ht : t.Nonempty) : t ∈ K :=
  (K.isRelLowerSet_faces hs).2 hts ht

/-! ### Vertices -/

/-- The vertices of `K`: the elements `v : ι` such that `{v}` is a face. -/
def vertices : Set ι := {v | {v} ∈ K}

@[simp]
theorem mem_vertices : v ∈ K.vertices ↔ {v} ∈ K := Iff.rfl

/-- Every element of a face is a vertex. -/
theorem mem_vertices_of_mem (hs : s ∈ K) (hv : v ∈ s) : v ∈ K.vertices :=
  K.mem_of_subset hs (singleton_subset_iff.2 hv) (singleton_nonempty v)

/-- The vertex set is the union of all faces. -/
theorem vertices_eq_iUnion : K.vertices = ⋃ s ∈ K, (s : Set ι) := by
  ext v
  simp only [mem_vertices, Set.mem_iUnion, mem_coe, exists_prop]
  exact ⟨fun h ↦ ⟨{v}, h, mem_singleton_self v⟩, fun ⟨_, hs, hv⟩ ↦ K.mem_vertices_of_mem hs hv⟩

/-! ### Facets -/

/-- The facets of `K`: faces that are not strictly contained in any other face. -/
def facets : Set (Finset ι) := {s | s ∈ K ∧ ∀ ⦃t⦄, t ∈ K → s ⊆ t → s = t}

theorem mem_facets : s ∈ K.facets ↔ s ∈ K ∧ ∀ ⦃t⦄, t ∈ K → s ⊆ t → s = t := Iff.rfl

theorem facets_subset : K.facets ⊆ K.faces := fun _ hs ↦ hs.1

/-! ### Faces of a given dimension -/

/-- The faces of `K` of dimension `n`, i.e. with exactly `n + 1` vertices. -/
def facesOfDim (n : ℕ) : Set (Finset ι) := {s | s ∈ K ∧ s.card = n + 1}

@[simp]
theorem mem_facesOfDim {n : ℕ} : s ∈ K.facesOfDim n ↔ s ∈ K ∧ s.card = n + 1 := Iff.rfl

theorem facesOfDim_subset (n : ℕ) : K.facesOfDim n ⊆ K.faces := fun _ hs ↦ hs.1

/-- The `0`-dimensional faces are exactly the singletons of vertices. -/
theorem mem_facesOfDim_zero : s ∈ K.facesOfDim 0 ↔ ∃ v ∈ K.vertices, s = {v} := by
  simp only [mem_facesOfDim, zero_add, card_eq_one, mem_vertices]
  constructor
  · rintro ⟨hs, v, rfl⟩
    exact ⟨v, hs, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv, v, rfl⟩

/-! ### Finite vertex types: the f-vector

When `ι` is a `Fintype` and membership in `K` is decidable, the faces of each dimension form a
`Finset`, and we can count them. The `DecidablePred` assumption is what lets Lean actually
evaluate the filter; for concrete complexes it is usually provided by an explicit instance. -/

section Fintype

variable [Fintype ι] [DecidablePred (· ∈ K)]

/-- The faces of `K` of dimension `n`, as a `Finset`. -/
def finsetFacesOfDim (n : ℕ) : Finset (Finset ι) :=
  {s | s ∈ K ∧ s.card = n + 1}

@[simp]
theorem mem_finsetFacesOfDim {n : ℕ} : s ∈ K.finsetFacesOfDim n ↔ s ∈ K ∧ s.card = n + 1 := by
  simp [finsetFacesOfDim]

@[simp, norm_cast]
theorem coe_finsetFacesOfDim (n : ℕ) :
    (K.finsetFacesOfDim n : Set (Finset ι)) = K.facesOfDim n := by
  ext s
  simp

/-- The f-vector of `K`: `K.fVector n` is the number of `n`-dimensional faces. -/
def fVector (n : ℕ) : ℕ := (K.finsetFacesOfDim n).card

/-- There are no faces of dimension `n` once `n + 1` exceeds the number of available vertices. -/
theorem finsetFacesOfDim_eq_empty {n : ℕ} (hn : Fintype.card ι ≤ n) :
    K.finsetFacesOfDim n = ∅ := by
  ext s
  simp only [mem_finsetFacesOfDim, notMem_empty, iff_false, not_and]
  intro _ hs
  have := s.card_le_univ
  omega

theorem fVector_eq_zero {n : ℕ} (hn : Fintype.card ι ≤ n) : K.fVector n = 0 := by
  simp [fVector, K.finsetFacesOfDim_eq_empty hn]

/-- The combinatorial Euler characteristic `∑ₙ (-1)ⁿ fₙ`. The sum is over `n < card ι`, which
covers every possible face by `fVector_eq_zero`. -/
def eulerChar : ℤ :=
  ∑ n ∈ range (Fintype.card ι), (-1 : ℤ) ^ n * K.fVector n

end Fintype

/-! ### The full simplex

`⊤ : PreAbstractSimplicialComplex ι` has every nonempty finset as a face: it is the full simplex
on `ι`. We record decidability of membership so that `decide` can count its faces. -/

@[simp]
theorem mem_top : s ∈ (⊤ : PreAbstractSimplicialComplex ι) ↔ s.Nonempty := Iff.rfl

instance decidableMemTop : DecidablePred (· ∈ (⊤ : PreAbstractSimplicialComplex ι)) :=
  fun s ↦ decidable_of_iff s.Nonempty mem_top.symm

end PreAbstractSimplicialComplex

/-! ### Sanity checks

The 2-simplex (a filled triangle) has 3 vertices, 3 edges and 1 triangle, and Euler
characteristic `3 - 3 + 1 = 1`. -/

example : (⊤ : PreAbstractSimplicialComplex (Fin 3)).fVector 0 = 3 := by decide
example : (⊤ : PreAbstractSimplicialComplex (Fin 3)).fVector 1 = 3 := by decide
example : (⊤ : PreAbstractSimplicialComplex (Fin 3)).fVector 2 = 1 := by decide
example : (⊤ : PreAbstractSimplicialComplex (Fin 3)).eulerChar = 1 := by decide
