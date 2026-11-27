/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Simplex

/-!
# Closed stars and links

For a complex `K` and a finset `s` (usually a face of `K`):

* the *closed star* `K.closedStar s` has the faces `t` of `K` such that `s ∪ t` is also a face.
  These are the faces of all the simplices containing `s`;
* the *link* `K.link s` has those faces `t` of the closed star that are disjoint from `s`.

Links describe what a complex looks like near a face. For example, a complex is a combinatorial
manifold when the link of every vertex is a sphere. In the boundary of a triangle, the link of a
vertex is the two opposite vertices, a `0`-sphere.

These follow `StarNeighborhood` and `Link` in Cunningham–Zach–Friedl's library
(`Pachner/Subcomplex/Star.lean`, `Pachner/Subcomplex/Link.lean`), restated for Mathlib's
`PreAbstractSimplicialComplex` with new proofs. `closedStar` avoids the name `star`, which Mathlib
already uses for the `Star` typeclass.

## Main declarations

* `PreAbstractSimplicialComplex.closedStar K s` and `PreAbstractSimplicialComplex.link K s`.
* `link_le_closedStar`, `closedStar_le`, `link_empty`, `closedStar_empty`.
* `sdiff_mem_link`: if `t ⊂ s` and `s` is a face, then `s \ t` is in the link of `t`.
* `link_link`: for `t ⊆ s`, the link of `s` is the link of `s \ t` inside the link of `t`
  (Lemma 3.5 in Cunningham–Zach–Friedl).
-/

@[expose] public section

open Finset

variable {ι : Type*} [DecidableEq ι]

namespace PreAbstractSimplicialComplex

variable {K : PreAbstractSimplicialComplex ι} {s t u : Finset ι}

/-! ### The closed star -/

/-- The closed star of `s` in `K`: the faces `t` of `K` such that `s ∪ t` is also a face. -/
def closedStar (K : PreAbstractSimplicialComplex ι) (s : Finset ι) :
    PreAbstractSimplicialComplex ι where
  faces := {t | t ∈ K ∧ s ∪ t ∈ K}
  isRelLowerSet_faces := fun _ ht ↦ ⟨K.nonempty_of_mem ht.1, fun _ hut hu ↦
    ⟨K.mem_of_subset ht.1 hut hu,
      K.mem_of_subset ht.2 (union_subset_union_right hut) (hu.mono subset_union_right)⟩⟩

@[simp]
theorem mem_closedStar : t ∈ K.closedStar s ↔ t ∈ K ∧ s ∪ t ∈ K := Iff.rfl

instance decidableMemClosedStar [DecidablePred (· ∈ K)] (s : Finset ι) :
    DecidablePred (· ∈ K.closedStar s) :=
  fun _ ↦ decidable_of_iff _ mem_closedStar.symm

theorem closedStar_le (K : PreAbstractSimplicialComplex ι) (s : Finset ι) : K.closedStar s ≤ K :=
  fun _ ht ↦ ht.1

@[simp]
theorem closedStar_empty (K : PreAbstractSimplicialComplex ι) : K.closedStar ∅ = K := by
  ext t
  simp [mem_faces]

/-- A face of `K` lies in its own closed star. -/
theorem self_mem_closedStar (hs : s ∈ K) : s ∈ K.closedStar s := ⟨hs, by rwa [union_self]⟩

/-- The closed star of a face contains the full simplex on that face. -/
theorem simplex_le_closedStar (hs : s ∈ K) : simplex s ≤ K.closedStar s :=
  fun _ ht ↦ ⟨K.mem_of_subset hs ht.2 ht.1, by rwa [union_eq_left.2 ht.2]⟩

/-! ### The link -/

/-- The link of `s` in `K`: the faces `t` of `K`, disjoint from `s`, such that `s ∪ t` is a
face. -/
def link (K : PreAbstractSimplicialComplex ι) (s : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {t | t ∈ K ∧ s ∪ t ∈ K ∧ Disjoint s t}
  isRelLowerSet_faces := fun _ ht ↦ ⟨K.nonempty_of_mem ht.1, fun _ hut hu ↦
    ⟨K.mem_of_subset ht.1 hut hu,
      K.mem_of_subset ht.2.1 (union_subset_union_right hut) (hu.mono subset_union_right),
      ht.2.2.mono_right hut⟩⟩

@[simp]
theorem mem_link : t ∈ K.link s ↔ t ∈ K ∧ s ∪ t ∈ K ∧ Disjoint s t := Iff.rfl

instance decidableMemLink [DecidablePred (· ∈ K)] (s : Finset ι) :
    DecidablePred (· ∈ K.link s) :=
  fun _ ↦ decidable_of_iff _ mem_link.symm

theorem link_le_closedStar (K : PreAbstractSimplicialComplex ι) (s : Finset ι) :
    K.link s ≤ K.closedStar s :=
  fun _ ht ↦ ⟨ht.1, ht.2.1⟩

theorem link_le (K : PreAbstractSimplicialComplex ι) (s : Finset ι) : K.link s ≤ K :=
  (link_le_closedStar K s).trans (closedStar_le K s)

@[simp]
theorem link_empty (K : PreAbstractSimplicialComplex ι) : K.link ∅ = K := by
  ext t
  simp [mem_faces]

theorem disjoint_of_mem_link (ht : t ∈ K.link s) : Disjoint s t := ht.2.2

/-- If `t` is a proper subset of a face `s`, then the complementary face `s \ t` lies in the link
of `t`. -/
theorem sdiff_mem_link (hs : s ∈ K) (hts : t ⊂ s) : s \ t ∈ K.link t := by
  refine ⟨K.mem_of_subset hs sdiff_subset (sdiff_nonempty.2 hts.not_subset), ?_,
    disjoint_sdiff⟩
  rwa [union_sdiff_of_subset hts.subset]

/-- Links of links: for `t ⊆ s`, the link of `s` in `K` is the link of `s \ t` in the link of
`t`. -/
theorem link_link (hts : t ⊆ s) : (K.link t).link (s \ t) = K.link s := by
  ext u
  simp only [mem_faces, mem_link, disjoint_union_right, disjoint_sdiff, true_and]
  have key : t ∪ (s \ t ∪ u) = s ∪ u := by
    rw [← union_assoc, union_sdiff_of_subset hts]
  rw [key]
  constructor
  · rintro ⟨⟨hu, -, htu⟩, ⟨-, hsu, -⟩, hstu⟩
    refine ⟨hu, hsu, ?_⟩
    rw [← union_sdiff_of_subset hts]
    exact disjoint_union_left.2 ⟨htu, hstu⟩
  · rintro ⟨hu, hsu, hdisj⟩
    have hne : u.Nonempty := K.nonempty_of_mem hu
    refine ⟨⟨hu, K.mem_of_subset hsu (union_subset_union_left hts) (hne.mono subset_union_right),
        hdisj.mono_left hts⟩,
      ⟨K.mem_of_subset hsu (union_subset_union_left sdiff_subset) (hne.mono subset_union_right),
        hsu, hdisj.mono_left hts⟩,
      hdisj.mono_left sdiff_subset⟩

end PreAbstractSimplicialComplex

/-! ### Sanity checks

In the boundary of a triangle (a circle), the link of a vertex is two points. -/

open PreAbstractSimplicialComplex in
example : ((boundary (Finset.univ : Finset (Fin 3))).link {0}).fVector 0 = 2 := by decide
open PreAbstractSimplicialComplex in
example : ((boundary (Finset.univ : Finset (Fin 3))).link {0}).fVector 1 = 0 := by decide
