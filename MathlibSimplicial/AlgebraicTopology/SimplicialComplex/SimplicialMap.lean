/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Faces
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Simplicial maps

A simplicial map `K →ˢ L` between complexes on vertex types `ι` and `κ` is a function `f : ι → κ`
sending every face of `K` onto a face of `L`. This follows `SimplicialMap` in
Cunningham–Zach–Friedl's library (`Pachner/Maps/SimplicialMap.lean`), restated for Mathlib's
`PreAbstractSimplicialComplex`.

## Design notes

* The condition is stated as "`f '' s` is (the coercion of) a face of `L`" rather than
  "`s.image f ∈ L`", because `Finset.image` needs `DecidableEq κ`. Keeping decidability out of the
  definition lets simplicial maps form a category without carrying instances around;
  `SimplicialMap.image_mem` recovers the `Finset.image` form whenever `DecidableEq κ` is available.
* A simplicial map is a total function `ι → κ`. For a `PreAbstractSimplicialComplex`, whose vertex
  set may be smaller than `ι`, two maps agreeing on vertices are therefore still different terms.
  That is harmless for most purposes, but it means maps between `PreAbstractSimplicialComplex`es do
  not form the usual category. So the category `SimplicialComplexCat` is built from
  `AbstractSimplicialComplex`es, where every element of the vertex type is a vertex.
* `SimplicialMap K L` has a `FunLike` instance, so `f v` applies a map to a vertex and maps are
  equal when their functions are (`SimplicialMap.ext`). This is the standard Mathlib pattern for
  bundled morphisms such as `→+` and `→*`.

## Main declarations

* `SimplicialMap K L`, written `K →ˢ L`.
* `SimplicialMap.id`, `SimplicialMap.comp`, `SimplicialMap.const`, `SimplicialMap.ofLE`.
* `SimplicialMap.image_mem`, `SimplicialMap.mapsTo_vertices`.
* `SimplicialComplexCat`: the category of abstract simplicial complexes and simplicial maps.
-/

@[expose] public section

open Finset

universe u v w

namespace PreAbstractSimplicialComplex

variable {ι : Type u} {κ : Type v} {μ : Type w}

/-- A simplicial map from `K` to `L`: a function on vertices sending each face of `K` onto a face
of `L`. -/
structure SimplicialMap (K : PreAbstractSimplicialComplex ι) (L : PreAbstractSimplicialComplex κ)
    where
  /-- The underlying function on vertices. -/
  toFun : ι → κ
  /-- The image of every face is a face. -/
  map_mem' : ∀ ⦃s : Finset ι⦄, s ∈ K → ∃ t ∈ L, (t : Set κ) = toFun '' s

@[inherit_doc]
infixr:25 " →ˢ " => SimplicialMap

namespace SimplicialMap

variable {K : PreAbstractSimplicialComplex ι} {L : PreAbstractSimplicialComplex κ}
  {M : PreAbstractSimplicialComplex μ}

instance : FunLike (K →ˢ L) ι κ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp]
theorem toFun_eq_coe (f : K →ˢ L) : f.toFun = f := rfl

@[ext]
theorem ext {f g : K →ˢ L} (h : ∀ v, f v = g v) : f = g := DFunLike.ext _ _ h

/-- The image of a face under a simplicial map is a face, in `Finset.image` form. -/
theorem image_mem [DecidableEq κ] (f : K →ˢ L) {s : Finset ι} (hs : s ∈ K) : s.image f ∈ L := by
  obtain ⟨t, ht, hts⟩ := f.map_mem' hs
  convert ht
  exact coe_injective (by rw [coe_image, hts, toFun_eq_coe])

/-- Simplicial maps send vertices to vertices. -/
theorem mapsTo_vertices (f : K →ˢ L) : Set.MapsTo f K.vertices L.vertices := by
  intro v hv
  classical
  simpa using f.image_mem hv

/-- Build a simplicial map from a function satisfying the `Finset.image` condition. -/
def mk' [DecidableEq κ] (f : ι → κ) (hf : ∀ ⦃s⦄, s ∈ K → s.image f ∈ L) : K →ˢ L where
  toFun := f
  map_mem' s hs := ⟨s.image f, hf hs, coe_image⟩

@[simp]
theorem coe_mk' [DecidableEq κ] (f : ι → κ) (hf : ∀ ⦃s⦄, s ∈ K → s.image f ∈ L) :
    ⇑(mk' f hf) = f := rfl

/-- The identity simplicial map. -/
protected def id (K : PreAbstractSimplicialComplex ι) : K →ˢ K where
  toFun := _root_.id
  map_mem' s hs := ⟨s, hs, (Set.image_id _).symm⟩

@[simp]
theorem coe_id : ⇑(SimplicialMap.id K) = _root_.id := rfl

/-- Composition of simplicial maps, in the same order as function composition. -/
def comp (g : L →ˢ M) (f : K →ˢ L) : K →ˢ M where
  toFun := g ∘ f
  map_mem' s hs := by
    obtain ⟨t, ht, hts⟩ := f.map_mem' hs
    obtain ⟨u, hu, hut⟩ := g.map_mem' ht
    exact ⟨u, hu, by rw [hut, hts, Set.image_comp]; rfl⟩

@[simp]
theorem coe_comp (g : L →ˢ M) (f : K →ˢ L) : ⇑(g.comp f) = g ∘ f := rfl

@[simp]
theorem comp_id (f : K →ˢ L) : f.comp (SimplicialMap.id K) = f := rfl

@[simp]
theorem id_comp (f : K →ˢ L) : (SimplicialMap.id L).comp f = f := rfl

theorem comp_assoc {ν : Type*} {N : PreAbstractSimplicialComplex ν} (h : M →ˢ N) (g : L →ˢ M)
    (f : K →ˢ L) : (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- The constant map onto a vertex `w` of `L` is simplicial: every face goes to `{w}`. -/
def const (K : PreAbstractSimplicialComplex ι) {w : κ} (hw : w ∈ L.vertices) : K →ˢ L where
  toFun _ := w
  map_mem' s hs := ⟨{w}, hw, by
    rw [coe_singleton, (coe_nonempty.2 (K.nonempty_of_mem hs)).image_const]⟩

/-- The inclusion of a subcomplex. -/
def ofLE {K L : PreAbstractSimplicialComplex ι} (h : K ≤ L) : K →ˢ L where
  toFun := _root_.id
  map_mem' s hs := ⟨s, h hs, (Set.image_id _).symm⟩

@[simp]
theorem coe_ofLE {K L : PreAbstractSimplicialComplex ι} (h : K ≤ L) : ⇑(ofLE h) = _root_.id := rfl

end SimplicialMap

end PreAbstractSimplicialComplex

open PreAbstractSimplicialComplex CategoryTheory

/-- The category of abstract simplicial complexes: an object is a vertex type together with an
`AbstractSimplicialComplex` on it (so every element of the type is a vertex), and morphisms are
simplicial maps. -/
structure SimplicialComplexCat : Type (u + 1) where
  /-- The vertex type. -/
  V : Type u
  /-- The complex. -/
  K : AbstractSimplicialComplex V

namespace SimplicialComplexCat

instance : Category SimplicialComplexCat.{u} where
  Hom X Y := X.K.toPreAbstractSimplicialComplex →ˢ Y.K.toPreAbstractSimplicialComplex
  id X := SimplicialMap.id _
  comp f g := g.comp f

end SimplicialComplexCat
