/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Simplex
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.SimplicialMap
public import Mathlib.Data.Finset.Option

/-!
# The cone on a simplicial complex

The cone on `K : PreAbstractSimplicialComplex ι` adds one new vertex, the apex, and a face
`σ ∪ {apex}` for every face `σ` of `K`. We take the vertex type of the cone to be `Option ι`, with
`none` as the apex and `some v` for the old vertex `v`. In Lean this is the standard way to adjoin
one new element to a type, and it avoids having to choose a fresh vertex inside `ι`.

A finset `s : Finset (Option ι)` is a face of the cone when it is nonempty and the vertices of `K`
in it (`Finset.eraseNone s`) are either none at all, or a face of `K`.

Cunningham–Zach–Friedl (`Pachner/Constructions/Cone.lean`) define the cone as the join with a
point, on a product vertex type. We use `Option ι` instead because it needs no join machinery.
Comparing the two is left for when joins are ported.

The cone is the basic tool for showing that complexes are acyclic. This file only sets it up; the
homological statement comes with roadmap step 4.

## Main declarations

* `PreAbstractSimplicialComplex.cone K` and `mem_cone`.
* `PreAbstractSimplicialComplex.map_some_mem_cone_iff`: `K` sits inside its cone.
* `PreAbstractSimplicialComplex.insertNone_mem_cone`: faces of `K` with the apex added.
* `PreAbstractSimplicialComplex.cone_simplex`: the cone on the simplex `Δ(s)` is `Δ(s ∪ {apex})`.
* `PreAbstractSimplicialComplex.SimplicialMap.toCone`: the inclusion `K →ˢ cone K`.
-/

@[expose] public section

open Finset

variable {ι : Type*}

namespace Finset

/-- A finset of `Option α` lies inside `insertNone s` exactly when its `some` part lies inside
`s`. -/
theorem subset_insertNone_iff {s : Finset ι} {t : Finset (Option ι)} :
    t ⊆ insertNone s ↔ eraseNone t ⊆ s := by
  constructor
  · intro h a ha
    exact some_mem_insertNone.1 (h (mem_eraseNone.1 ha))
  · intro h o ho
    cases o with
    | none => exact none_mem_insertNone
    | some a => exact some_mem_insertNone.2 (h (mem_eraseNone.2 ho))

end Finset

namespace PreAbstractSimplicialComplex

variable {K : PreAbstractSimplicialComplex ι} {s : Finset ι} {t : Finset (Option ι)} {v : ι}

/-- The cone on `K`, with apex `none : Option ι`. -/
def cone (K : PreAbstractSimplicialComplex ι) : PreAbstractSimplicialComplex (Option ι) where
  faces := {t | t.Nonempty ∧ (eraseNone t = ∅ ∨ eraseNone t ∈ K)}
  isRelLowerSet_faces := by
    rintro t ⟨htne, ht⟩
    refine ⟨htne, fun u hut hu ↦ ⟨hu, ?_⟩⟩
    have hsub : eraseNone u ⊆ eraseNone t := eraseNone.monotone hut
    rcases (eraseNone u).eq_empty_or_nonempty with h | h
    · exact .inl h
    · rcases ht with ht | ht
      · exact absurd (subset_empty.1 (ht ▸ hsub)) h.ne_empty
      · exact .inr (K.mem_of_subset ht hsub h)

@[simp]
theorem mem_cone : t ∈ K.cone ↔ t.Nonempty ∧ (eraseNone t = ∅ ∨ eraseNone t ∈ K) := Iff.rfl

/-- The apex is a vertex of the cone. -/
theorem none_mem_vertices_cone : none ∈ K.cone.vertices :=
  ⟨singleton_nonempty _, .inl eraseNone_none⟩

/-- A face of `K` together with the apex is a face of the cone. -/
theorem insertNone_mem_cone (hs : s ∈ K) : insertNone s ∈ K.cone :=
  ⟨insertNone_nonempty, .inr (by rwa [eraseNone_insertNone])⟩

/-- A copy of a finset of old vertices is a face of the cone exactly when it is a face of `K`. -/
@[simp]
theorem map_some_mem_cone_iff : s.map Function.Embedding.some ∈ K.cone ↔ s ∈ K := by
  simp only [mem_cone, map_nonempty, eraseNone_map_some]
  refine ⟨fun ⟨hs, h⟩ ↦ h.resolve_left hs.ne_empty, fun h ↦ ⟨K.nonempty_of_mem h, .inr h⟩⟩

@[simp]
theorem some_mem_vertices_cone : some v ∈ K.cone.vertices ↔ v ∈ K.vertices := by
  simpa using map_some_mem_cone_iff (K := K) (s := {v})

/-- The cone on the full simplex on `s` is the full simplex on `s` plus the apex. -/
theorem cone_simplex (s : Finset ι) : (simplex s).cone = simplex (insertNone s) := by
  ext t
  simp only [mem_faces, mem_cone, mem_simplex, subset_insertNone_iff]
  constructor
  · rintro ⟨ht, h | h⟩
    · exact ⟨ht, h ▸ empty_subset s⟩
    · exact ⟨ht, h.2⟩
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    rcases (eraseNone t).eq_empty_or_nonempty with h' | h'
    · exact .inl h'
    · exact .inr ⟨h', h⟩

namespace SimplicialMap

/-- The inclusion of `K` into its cone, `v ↦ some v`. -/
def toCone (K : PreAbstractSimplicialComplex ι) : K →ˢ K.cone where
  toFun := some
  map_mem' s hs := ⟨s.map Function.Embedding.some, map_some_mem_cone_iff.2 hs, by simp⟩

@[simp]
theorem coe_toCone : ⇑(toCone K) = some := rfl

end SimplicialMap

end PreAbstractSimplicialComplex
