/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Faces

/-!
# The full simplex, its boundary, and skeleta

For a finset `s : Finset ι` we define

* `PreAbstractSimplicialComplex.simplex s`: the full simplex on `s`, whose faces are all nonempty
  subsets of `s`;
* `PreAbstractSimplicialComplex.boundary s`: its boundary `∂s`, whose faces are the nonempty
  *proper* subsets of `s`. When `s` has `n + 1` elements this is a triangulated `(n-1)`-sphere;

and for a complex `K`, the `n`-skeleton `K.skeleton n` of faces of dimension at most `n`.

These follow `Simplex` and `FaceBoundary` in Cunningham–Zach–Friedl's library
(`Pachner/Basic/AbstractSimplicialComplex.lean`, `Pachner/Subcomplex/FaceBoundary.lean`),
restated for Mathlib's `PreAbstractSimplicialComplex` with new proofs.

## Main declarations

* `PreAbstractSimplicialComplex.simplex s` and `simplex_le_iff`: a nonempty `s` is a face of `K`
  exactly when the simplex on `s` is a subcomplex of `K`.
* `PreAbstractSimplicialComplex.boundary s`, with `boundary_le_simplex` and `vertices_boundary`.
* `PreAbstractSimplicialComplex.skeleton K n`.
-/

@[expose] public section

open Finset

variable {ι : Type*}

namespace PreAbstractSimplicialComplex

variable {K L : PreAbstractSimplicialComplex ι} {s t u : Finset ι} {v : ι}

/-! ### The full simplex -/

/-- The full simplex on a finset `s`: every nonempty subset of `s` is a face. -/
def simplex (s : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {t | t.Nonempty ∧ t ⊆ s}
  isRelLowerSet_faces := fun _ ht ↦ ⟨ht.1, fun _ hut hu ↦ ⟨hu, hut.trans ht.2⟩⟩

@[simp]
theorem mem_simplex : t ∈ simplex s ↔ t.Nonempty ∧ t ⊆ s := Iff.rfl

instance decidableMemSimplex [DecidableEq ι] (s : Finset ι) : DecidablePred (· ∈ simplex s) :=
  fun _ ↦ decidable_of_iff _ mem_simplex.symm

/-- A nonempty finset is a face of its own simplex. -/
theorem self_mem_simplex (hs : s.Nonempty) : s ∈ simplex s := ⟨hs, subset_rfl⟩

@[simp]
theorem vertices_simplex (s : Finset ι) : (simplex s).vertices = s := by
  ext v
  simp

theorem simplex_mono (h : s ⊆ t) : simplex s ≤ simplex t :=
  fun _ hu ↦ ⟨hu.1, hu.2.trans h⟩

/-- A nonempty finset `s` is a face of `K` iff the full simplex on `s` is a subcomplex of `K`. -/
theorem simplex_le_iff (hs : s.Nonempty) : simplex s ≤ K ↔ s ∈ K :=
  ⟨fun h ↦ h (self_mem_simplex hs), fun h _ ht ↦ K.mem_of_subset h ht.2 ht.1⟩

@[simp]
theorem simplex_empty : simplex (∅ : Finset ι) = ⊥ := by
  ext t
  simp only [mem_faces, mem_simplex, subset_empty]
  exact ⟨fun ⟨h, h'⟩ ↦ (h.ne_empty h').elim, fun h ↦ h.elim⟩

/-! ### The boundary of a simplex -/

/-- The boundary `∂s` of the simplex on `s`: every nonempty proper subset of `s` is a face. -/
def boundary (s : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {t | t.Nonempty ∧ t ⊂ s}
  isRelLowerSet_faces := fun _ ht ↦ ⟨ht.1, fun _ hut hu ↦ ⟨hu, hut.trans_ssubset ht.2⟩⟩

@[simp]
theorem mem_boundary : t ∈ boundary s ↔ t.Nonempty ∧ t ⊂ s := Iff.rfl

instance decidableMemBoundary [DecidableEq ι] (s : Finset ι) :
    DecidablePred (· ∈ boundary s) :=
  fun _ ↦ decidable_of_iff _ mem_boundary.symm

/-- The boundary of a simplex is contained in the simplex. -/
theorem boundary_le_simplex (s : Finset ι) : boundary s ≤ simplex s :=
  fun _ ht ↦ ⟨ht.1, ht.2.subset⟩

/-- The top face is the one face of the simplex missing from the boundary. -/
theorem self_notMem_boundary (s : Finset ι) : s ∉ boundary s := fun h ↦ h.2.ne rfl

/-- If `s` is a face of `K`, then so is every face of its boundary. -/
theorem boundary_le_of_mem (hs : s ∈ K) : boundary s ≤ K :=
  (boundary_le_simplex s).trans ((simplex_le_iff (K.nonempty_of_mem hs)).2 hs)

theorem boundary_mono (h : s ⊆ t) : boundary s ≤ boundary t :=
  fun _ hu ↦ ⟨hu.1, hu.2.trans_subset h⟩

/-- The boundary of a simplex with at least two vertices has the same vertices as the simplex. -/
theorem vertices_boundary (hs : 1 < s.card) : (boundary s).vertices = s := by
  ext v
  simp only [mem_vertices, mem_boundary, singleton_nonempty, true_and, mem_coe]
  refine ⟨fun h ↦ singleton_subset_iff.1 h.subset, fun hv ↦ ?_⟩
  refine Finset.ssubset_iff_subset_ne.2 ⟨singleton_subset_iff.2 hv, fun h ↦ ?_⟩
  subst h
  simp at hs

/-! ### Skeleta -/

/-- The `n`-skeleton of `K`: the faces of dimension at most `n`, i.e. with at most `n + 1`
vertices. -/
def skeleton (K : PreAbstractSimplicialComplex ι) (n : ℕ) : PreAbstractSimplicialComplex ι where
  faces := {s | s ∈ K ∧ s.card ≤ n + 1}
  isRelLowerSet_faces := fun _ hs ↦ ⟨K.nonempty_of_mem hs.1, fun _ hts ht ↦
    ⟨K.mem_of_subset hs.1 hts ht, (card_le_card hts).trans hs.2⟩⟩

@[simp]
theorem mem_skeleton {n : ℕ} : s ∈ K.skeleton n ↔ s ∈ K ∧ s.card ≤ n + 1 := Iff.rfl

theorem skeleton_le (K : PreAbstractSimplicialComplex ι) (n : ℕ) : K.skeleton n ≤ K :=
  fun _ hs ↦ hs.1

theorem skeleton_mono {m n : ℕ} (h : m ≤ n) : K.skeleton m ≤ K.skeleton n :=
  fun _ hs ↦ ⟨hs.1, by have := hs.2; omega⟩

/-- Every complex has the same vertices as its `0`-skeleton. -/
@[simp]
theorem vertices_skeleton (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    (K.skeleton n).vertices = K.vertices := by
  ext v
  simp

end PreAbstractSimplicialComplex

/-! ### Sanity checks

The boundary of the 2-simplex is a triangulated circle: 3 vertices, 3 edges, no triangle, and
Euler characteristic `0`. -/

open PreAbstractSimplicialComplex in
example : (boundary (Finset.univ : Finset (Fin 3))).fVector 1 = 3 := by decide
open PreAbstractSimplicialComplex in
example : (boundary (Finset.univ : Finset (Fin 3))).fVector 2 = 0 := by decide
open PreAbstractSimplicialComplex in
example : (boundary (Finset.univ : Finset (Fin 3))).eulerChar = 0 := by decide
