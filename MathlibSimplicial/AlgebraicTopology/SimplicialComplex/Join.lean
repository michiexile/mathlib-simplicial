/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Simplex
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.SimplicialMap
public import Mathlib.Data.Finset.Sum

/-!
# The join of two simplicial complexes

The join `K.join L` of complexes on `ι` and `κ` lives on the disjoint union `ι ⊕ κ`. Its faces
are the unions `σ ⊔ τ` of a face `σ` of `K` and a face `τ` of `L`, where either part (but not
both) may be empty. Geometrically, the join puts a line segment between every point of `K` and
every point of `L`: the join of two points is an interval, and the join of a point with `K` is the
cone on `K`.

For `u : Finset (ι ⊕ κ)`, Mathlib's `Finset.toLeft u` and `Finset.toRight u` are its `ι` and `κ`
parts. A finset is a face of the join when it is nonempty and each part is empty or a face.

Cunningham–Zach–Friedl (`Pachner/Constructions/Join.lean`) put both complexes inside one product
type `E × 𝕜`, tagging the two sides with `0` and `1`. The sum type `ι ⊕ κ` used here keeps the two
vertex types apart from the start, so no tagging or disjointness bookkeeping is needed.

## Main declarations

* `PreAbstractSimplicialComplex.join K L` and `mem_join`.
* `disjSum_mem_join`: `σ ⊔ τ` is a face of the join.
* `map_inl_mem_join_iff`, `map_inr_mem_join_iff`: `K` and `L` sit inside the join.
* `simplex_join_simplex`: the join of two simplices is a simplex.
* `SimplicialMap.inlJoin`, `SimplicialMap.inrJoin`: the inclusions `K →ˢ K.join L ←ˢ L`.
-/

@[expose] public section

open Finset

variable {ι κ : Type*}

namespace PreAbstractSimplicialComplex

variable {K : PreAbstractSimplicialComplex ι} {L : PreAbstractSimplicialComplex κ}
  {s : Finset ι} {t : Finset κ} {u : Finset (ι ⊕ κ)}

/-- The join of `K` and `L`, on the vertex type `ι ⊕ κ`. -/
def join (K : PreAbstractSimplicialComplex ι) (L : PreAbstractSimplicialComplex κ) :
    PreAbstractSimplicialComplex (ι ⊕ κ) where
  faces := {u | u.Nonempty ∧ (u.toLeft = ∅ ∨ u.toLeft ∈ K) ∧ (u.toRight = ∅ ∨ u.toRight ∈ L)}
  isRelLowerSet_faces := by
    rintro u ⟨hune, hl, hr⟩
    refine ⟨hune, fun v hvu hv ↦ ⟨hv, ?_, ?_⟩⟩
    · have hsub : v.toLeft ⊆ u.toLeft := toLeft_subset_toLeft hvu
      rcases v.toLeft.eq_empty_or_nonempty with h | h
      · exact .inl h
      · rcases hl with hl | hl
        · exact absurd (subset_empty.1 (hl ▸ hsub)) h.ne_empty
        · exact .inr (K.mem_of_subset hl hsub h)
    · have hsub : v.toRight ⊆ u.toRight := toRight_subset_toRight hvu
      rcases v.toRight.eq_empty_or_nonempty with h | h
      · exact .inl h
      · rcases hr with hr | hr
        · exact absurd (subset_empty.1 (hr ▸ hsub)) h.ne_empty
        · exact .inr (L.mem_of_subset hr hsub h)

@[simp]
theorem mem_join : u ∈ K.join L ↔
    u.Nonempty ∧ (u.toLeft = ∅ ∨ u.toLeft ∈ K) ∧ (u.toRight = ∅ ∨ u.toRight ∈ L) := Iff.rfl

/-- The disjoint union of a face of `K` and a face of `L` is a face of the join. -/
theorem disjSum_mem_join (hs : s ∈ K) (ht : t ∈ L) : s.disjSum t ∈ K.join L :=
  have ⟨a, ha⟩ := K.nonempty_of_mem hs
  ⟨⟨.inl a, by simpa⟩, by simp [hs], by simp [ht]⟩

@[simp]
theorem toLeft_map_inl : (s.map Function.Embedding.inl : Finset (ι ⊕ κ)).toLeft = s := by
  ext; simp

@[simp]
theorem toRight_map_inl : (s.map Function.Embedding.inl : Finset (ι ⊕ κ)).toRight = ∅ := by
  ext; simp

@[simp]
theorem toLeft_map_inr : (t.map Function.Embedding.inr : Finset (ι ⊕ κ)).toLeft = ∅ := by
  ext; simp

@[simp]
theorem toRight_map_inr : (t.map Function.Embedding.inr : Finset (ι ⊕ κ)).toRight = t := by
  ext; simp

/-- A copy of a finset of `ι` is a face of the join exactly when it is a face of `K`. -/
@[simp]
theorem map_inl_mem_join_iff : s.map Function.Embedding.inl ∈ K.join L ↔ s ∈ K := by
  simp only [mem_join, map_nonempty, toLeft_map_inl, toRight_map_inl, true_or, and_true]
  exact ⟨fun ⟨hs, h⟩ ↦ h.resolve_left hs.ne_empty, fun h ↦ ⟨K.nonempty_of_mem h, .inr h⟩⟩

/-- A copy of a finset of `κ` is a face of the join exactly when it is a face of `L`. -/
@[simp]
theorem map_inr_mem_join_iff : t.map Function.Embedding.inr ∈ K.join L ↔ t ∈ L := by
  simp only [mem_join, map_nonempty, toLeft_map_inr, toRight_map_inr, true_or, true_and]
  exact ⟨fun ⟨hs, h⟩ ↦ h.resolve_left hs.ne_empty, fun h ↦ ⟨L.nonempty_of_mem h, .inr h⟩⟩

/-- The join of the simplex on `s` and the simplex on `t` is the simplex on `s ⊔ t`. -/
theorem simplex_join_simplex (s : Finset ι) (t : Finset κ) :
    (simplex s).join (simplex t) = simplex (s.disjSum t) := by
  ext u
  simp only [mem_faces, mem_join, mem_simplex, subset_disjSum]
  constructor
  · rintro ⟨hu, hl, hr⟩
    refine ⟨hu, ?_, ?_⟩
    · rcases hl with h | h
      · exact h ▸ empty_subset s
      · exact h.2
    · rcases hr with h | h
      · exact h ▸ empty_subset t
      · exact h.2
  · rintro ⟨hu, hl, hr⟩
    refine ⟨hu, ?_, ?_⟩
    · rcases u.toLeft.eq_empty_or_nonempty with h | h
      · exact .inl h
      · exact .inr ⟨h, hl⟩
    · rcases u.toRight.eq_empty_or_nonempty with h | h
      · exact .inl h
      · exact .inr ⟨h, hr⟩

namespace SimplicialMap

/-- The inclusion of `K` into its join with `L`. -/
def inlJoin (K : PreAbstractSimplicialComplex ι) (L : PreAbstractSimplicialComplex κ) :
    K →ˢ K.join L where
  toFun := Sum.inl
  map_mem' s hs := ⟨s.map Function.Embedding.inl, map_inl_mem_join_iff.2 hs, by simp⟩

/-- The inclusion of `L` into its join with `K`. -/
def inrJoin (K : PreAbstractSimplicialComplex ι) (L : PreAbstractSimplicialComplex κ) :
    L →ˢ K.join L where
  toFun := Sum.inr
  map_mem' t ht := ⟨t.map Function.Embedding.inr, map_inr_mem_join_iff.2 ht, by simp⟩

@[simp]
theorem coe_inlJoin : ⇑(inlJoin K L) = Sum.inl := rfl

@[simp]
theorem coe_inrJoin : ⇑(inrJoin K L) = Sum.inr := rfl

end SimplicialMap

end PreAbstractSimplicialComplex
