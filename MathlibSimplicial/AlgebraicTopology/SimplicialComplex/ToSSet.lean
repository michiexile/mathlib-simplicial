/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Faces
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Data.Finset.Sort

/-!
# From simplicial complexes to simplicial sets

Let `ι` be a linearly ordered vertex type. Mathlib's nerve `nerve ι` is the simplicial set whose
`n`-simplices are monotone maps `Fin (n + 1) → ι` (formally, functors `Fin (n + 1) ⥤ ι`). For a
complex `K` on `ι`, `K.nerveSubcomplex` is the subcomplex of `nerve ι` consisting of the monotone
maps whose image is a face of `K`, and `K.toSSet` is that subcomplex viewed as a simplicial set.

A simplex of `K.toSSet` is *nondegenerate* exactly when the map `Fin (n + 1) → ι` is strictly
monotone. Such a map is determined by its image, which is an `n`-dimensional face of `K`. So:

  nondegenerate `n`-simplices of `K.toSSet`  ≃  `n`-dimensional faces of `K`

(`PreAbstractSimplicialComplex.nonDegenerateEquiv`). The degenerate simplices are the monotone
maps that repeat a vertex; they are the price of working with simplicial sets, and Mathlib's
normalized chain complex removes them again.

This is what lets us reuse Mathlib's homology of simplicial sets: its chain complex, functoriality,
homotopy invariance, relative homology and long exact sequence all apply to `K.toSSet`.

## The choice of model

The linear order on `ι` is a choice of orientation, and the construction is functorial only for
order-preserving maps (`toSSetMap` handles subcomplex inclusions, which is what filtrations and
persistence use). An alternative, the *ordered* simplicial set of `K` (all maps
`Fin (n + 1) → ι` with image a face, monotone or not), needs no order and is functorial in every
simplicial map, but has many more nondegenerate simplices. See `docs/decision-log.md`.

## Main declarations

* `PreAbstractSimplicialComplex.nerveSubcomplex K` and `PreAbstractSimplicialComplex.toSSet K`.
* `PreAbstractSimplicialComplex.toSSetMap`: the map induced by an inclusion `K ≤ L`.
* `PreAbstractSimplicialComplex.mem_nonDegenerate_toSSet_iff`: nondegenerate means strictly
  monotone.
* `PreAbstractSimplicialComplex.nonDegenerateEquiv`: nondegenerate `n`-simplices correspond to
  `n`-dimensional faces.
-/

@[expose] public section

open CategoryTheory Simplicial Finset Opposite

universe u

variable {ι : Type u} [LinearOrder ι]

namespace PreAbstractSimplicialComplex

variable (K L : PreAbstractSimplicialComplex ι)

/-- The subcomplex of the nerve of `ι` whose simplices are the monotone maps
`Fin (n + 1) → ι` with image a face of `K`. -/
def nerveSubcomplex : (nerve ι).Subcomplex where
  obj _ := {s | univ.image s.obj ∈ K}
  map {_ _} _ s hs := by
    refine K.mem_of_subset hs ?_ (univ_nonempty.image _)
    intro x hx
    simp only [mem_image, mem_univ, true_and] at hx ⊢
    obtain ⟨j, rfl⟩ := hx
    exact ⟨_, rfl⟩

theorem mem_nerveSubcomplex {n : SimplexCategoryᵒᵖ} (s : (nerve ι).obj n) :
    s ∈ K.nerveSubcomplex.obj n ↔ univ.image s.obj ∈ K := Iff.rfl

/-- The simplicial set associated to `K` (for the chosen linear order on `ι`). -/
abbrev toSSet : SSet.{u} := K.nerveSubcomplex

variable {K L}

theorem nerveSubcomplex_mono (h : K ≤ L) : K.nerveSubcomplex ≤ L.nerveSubcomplex :=
  fun _ _ hs ↦ h hs

/-- The map of simplicial sets induced by an inclusion of complexes. -/
noncomputable abbrev toSSetMap (h : K ≤ L) : K.toSSet ⟶ L.toSSet :=
  SSet.Subcomplex.homOfLE (nerveSubcomplex_mono h)

@[simp]
theorem toSSetMap_refl : toSSetMap (le_refl K) = 𝟙 _ := rfl

theorem toSSetMap_comp {M : PreAbstractSimplicialComplex ι} (h : K ≤ L) (h' : L ≤ M) :
    toSSetMap h ≫ toSSetMap h' = toSSetMap (h.trans h') := rfl

variable (K)

/-- A simplex of `K.toSSet` is nondegenerate iff the underlying map is strictly monotone. -/
theorem mem_nonDegenerate_toSSet_iff {n : ℕ} (s : K.toSSet _⦋n⦌) :
    s ∈ K.toSSet.nonDegenerate n ↔ StrictMono s.val.obj := by
  rw [SSet.Subcomplex.mem_nonDegenerate_iff,
    PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]

/-- The `n`-simplex of the nerve of `ι` listing the elements of a finset `t` with `n + 1`
elements in increasing order. -/
def simplexOfFinset {n : ℕ} (t : Finset ι) (ht : t.card = n + 1) : (nerve ι) _⦋n⦌ :=
  (t.orderEmbOfFin ht).monotone.functor

@[simp]
theorem simplexOfFinset_obj {n : ℕ} (t : Finset ι) (ht : t.card = n + 1) :
    (simplexOfFinset t ht).obj = t.orderEmbOfFin ht := rfl

/-- The nondegenerate `n`-simplices of `K.toSSet` correspond to the `n`-dimensional faces
of `K`: a strictly monotone map is determined by its image. -/
noncomputable def nonDegenerateEquiv (n : ℕ) :
    K.toSSet.nonDegenerate n ≃ K.facesOfDim n where
  toFun s := ⟨univ.image s.1.val.obj, s.1.2, by
    rw [card_image_of_injective _ ((K.mem_nonDegenerate_toSSet_iff s.1).1 s.2).injective,
      card_univ, Fintype.card_fin]⟩
  invFun t := ⟨⟨simplexOfFinset t.1 t.2.2, by
      simpa [mem_nerveSubcomplex, image_orderEmbOfFin_univ] using t.2.1⟩, by
    rw [mem_nonDegenerate_toSSet_iff]
    exact (t.1.orderEmbOfFin t.2.2).strictMono⟩
  left_inv s := by
    have hs := (K.mem_nonDegenerate_toSSet_iff s.1).1 s.2
    apply Subtype.ext
    apply Subtype.ext
    apply nerve.ext_of_isThin
    rw [simplexOfFinset_obj]
    exact (orderEmbOfFin_unique _ (fun x ↦ mem_image_of_mem _ (mem_univ x)) hs).symm
  right_inv t := by
    apply Subtype.ext
    exact image_orderEmbOfFin_univ _ _

end PreAbstractSimplicialComplex
