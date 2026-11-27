/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Basic
public import MathlibSimplicial.TDA.VietorisRips
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Filtrations and persistent homology

A **filtration** of simplicial complexes on `ι`, indexed by a preorder `T` (usually `ℝ` or
`ℝ≥0`), is a monotone map `F : T →o PreAbstractSimplicialComplex ι`. Applying `Hₙ` gives a
**persistence module**: a functor `T ⥤ C`, which sends `s ≤ t` to the map induced by
`F s ≤ F t`. This is `persistentHomology R F n`. Its value is the homology functor of
`Homology/Basic.lean` composed with `F`, viewed as a functor between posets.

Examples:
* the **sublevel (lower-star) filtration** of a complex `K` by a vertex function `f : ι → T`.
  `K.sublevel f t` consists of the faces all of whose vertices have `f v ≤ t`;
* the **Vietoris–Rips** and **Čech filtrations** of a point cloud, indexed by `ℝ≥0`.

## Interleavings

Two persistence modules `M N : T ⥤ C` are **interleaved** along monotone maps `α β : T →o T`
that move every `t` up (`t ≤ α t`, `t ≤ β t`) when there are maps
`φ t : M t → N (α t)` and `ψ t : N t → M (β t)`, natural in `t`, whose composites are the
structure maps of `M` and of `N`. With `α t = β t = t + ε` this is the usual `ε`-interleaving.
`Interleaving.ofLE` produces one from inclusions `F t ≤ G (α t)` and `G t ≤ F (β t)` of
filtrations. In particular the Čech and Rips filtrations are interleaved along `r ↦ 2r`
(`cechRipsInterleaving`), the persistent form of `VR(r) ⊆ Čech(r) ⊆ VR(2r)`.

## Main declarations

* `PreAbstractSimplicialComplex.sublevel`, `PreAbstractSimplicialComplex.lowerStarFiltration`.
* `PreAbstractSimplicialComplex.ripsFiltration`, `PreAbstractSimplicialComplex.cechFiltration`.
* `PreAbstractSimplicialComplex.persistentHomology`, `PreAbstractSimplicialComplex.persistentBetti`.
* `PreAbstractSimplicialComplex.Interleaving`, `PreAbstractSimplicialComplex.Interleaving.ofLE`,
  `PreAbstractSimplicialComplex.cechRipsInterleaving`.
-/

@[expose] public section

open CategoryTheory Limits NNReal

universe v u w

namespace PreAbstractSimplicialComplex

variable {ι : Type u} {T : Type*} [Preorder T]

section Sublevel

variable (K : PreAbstractSimplicialComplex ι) (f : ι → T)

/-- The sublevel subcomplex of `K` at `t` for a vertex function `f`: the faces all of whose
vertices have value at most `t`. -/
def sublevel (t : T) : PreAbstractSimplicialComplex ι where
  faces := {s | s ∈ K ∧ ∀ v ∈ s, f v ≤ t}
  isRelLowerSet_faces := fun _ hs ↦ ⟨K.nonempty_of_mem hs.1, fun _ hts htne ↦
    ⟨K.mem_of_subset hs.1 hts htne, fun v hv ↦ hs.2 v (hts hv)⟩⟩

theorem mem_sublevel {t : T} {s : Finset ι} : s ∈ K.sublevel f t ↔ s ∈ K ∧ ∀ v ∈ s, f v ≤ t :=
  Iff.rfl

theorem sublevel_le (t : T) : K.sublevel f t ≤ K := fun _ hs ↦ hs.1

theorem sublevel_mono {s t : T} (h : s ≤ t) : K.sublevel f s ≤ K.sublevel f t :=
  fun _ hu ↦ ⟨hu.1, fun v hv ↦ (hu.2 v hv).trans h⟩

/-- The lower-star (sublevel) filtration of `K` by a vertex function `f`. -/
def lowerStarFiltration : T →o PreAbstractSimplicialComplex ι :=
  ⟨K.sublevel f, fun _ _ ↦ K.sublevel_mono f⟩

end Sublevel

section PointClouds

variable {M : Type*} [PseudoMetricSpace M] (p : ι → M)

/-- The Vietoris–Rips filtration of a point cloud, indexed by `ℝ≥0`. -/
def ripsFiltration : ℝ≥0 →o PreAbstractSimplicialComplex ι :=
  ⟨fun r ↦ vietorisRips p r, fun _ _ h ↦ vietorisRips_mono p (NNReal.coe_le_coe.2 h)⟩

/-- The Čech filtration of a point cloud, indexed by `ℝ≥0`. -/
def cechFiltration : ℝ≥0 →o PreAbstractSimplicialComplex ι :=
  ⟨fun r ↦ cech p r, fun _ _ h ↦ cech_mono p (NNReal.coe_le_coe.2 h)⟩

end PointClouds

/-- Two persistence modules `M N : T ⥤ C` are interleaved along `α` and `β` (maps that move
every index up) when there are natural maps `M t ⟶ N (α t)` and `N t ⟶ M (β t)` whose composites
are the structure maps. -/
structure Interleaving {C : Type w} [Category.{v} C] (M N : T ⥤ C) (α β : T →o T)
    (hα : ∀ t, t ≤ α t) (hβ : ∀ t, t ≤ β t) where
  /-- The map from `M` to `N`, shifted by `α`. -/
  φ (t : T) : M.obj t ⟶ N.obj (α t)
  /-- The map from `N` to `M`, shifted by `β`. -/
  ψ (t : T) : N.obj t ⟶ M.obj (β t)
  φ_naturality ⦃s t : T⦄ (h : s ≤ t) :
    M.map (homOfLE h) ≫ φ t = φ s ≫ N.map (homOfLE (α.monotone h))
  ψ_naturality ⦃s t : T⦄ (h : s ≤ t) :
    N.map (homOfLE h) ≫ ψ t = ψ s ≫ M.map (homOfLE (β.monotone h))
  φ_ψ (t : T) : φ t ≫ ψ (α t) = M.map (homOfLE ((hα t).trans (hβ (α t))))
  ψ_φ (t : T) : ψ t ≫ φ (β t) = N.map (homOfLE ((hβ t).trans (hα (β t))))

variable [LinearOrder ι]
variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- Persistent homology: the persistence module `t ↦ Hₙ(F t; R)` of a filtration `F`. -/
noncomputable def persistentHomology (F : T →o PreAbstractSimplicialComplex ι) (n : ℕ) :
    T ⥤ C :=
  F.monotone.functor ⋙ homologyFunctor ι R n

@[simp]
theorem persistentHomology_obj (F : T →o PreAbstractSimplicialComplex ι) (n : ℕ) (t : T) :
    (persistentHomology R F n).obj t = (F t).homology R n := rfl

theorem persistentHomology_map (F : T →o PreAbstractSimplicialComplex ι) (n : ℕ) {s t : T}
    (h : s ≤ t) :
    (persistentHomology R F n).map (homOfLE h) =
      PreAbstractSimplicialComplex.homologyMap R (F.monotone h) n := rfl

/-- Interleaved filtrations have interleaved persistent homology: if `F t ≤ G (α t)` and
`G t ≤ F (β t)`, the inclusions induce an interleaving. -/
noncomputable def Interleaving.ofLE {F G : T →o PreAbstractSimplicialComplex ι} {α β : T →o T}
    {hα : ∀ t, t ≤ α t} {hβ : ∀ t, t ≤ β t} (hFG : ∀ t, F t ≤ G (α t))
    (hGF : ∀ t, G t ≤ F (β t)) (n : ℕ) :
    Interleaving (persistentHomology R F n) (persistentHomology R G n) α β hα hβ where
  φ t := PreAbstractSimplicialComplex.homologyMap R (hFG t) n
  ψ t := PreAbstractSimplicialComplex.homologyMap R (hGF t) n
  φ_naturality _ _ h := by
    exact (homologyMap_comp R _ _ n).symm.trans (homologyMap_comp R _ _ n)
  ψ_naturality _ _ h := by
    exact (homologyMap_comp R _ _ n).symm.trans (homologyMap_comp R _ _ n)
  φ_ψ t := by
    exact (homologyMap_comp R _ _ n).symm
  ψ_φ t := by
    exact (homologyMap_comp R _ _ n).symm

/-- Doubling, as a monotone map of `ℝ≥0`. -/
def doubling : ℝ≥0 →o ℝ≥0 := ⟨fun r ↦ 2 * r, fun _ _ h ↦ mul_le_mul_right h 2⟩

theorem le_doubling (r : ℝ≥0) : r ≤ doubling r := by
  change r ≤ 2 * r
  exact le_mul_of_one_le_left (by positivity) one_le_two

/-- The persistent homology of the Čech and Vietoris–Rips filtrations of a point cloud are
interleaved along `r ↦ 2r` and the identity, from `VR(r) ⊆ Čech(r) ⊆ VR(2r)`. -/
noncomputable def cechRipsInterleaving {M : Type*} [PseudoMetricSpace M] (p : ι → M) (n : ℕ) :
    Interleaving (persistentHomology R (cechFiltration p) n)
      (persistentHomology R (ripsFiltration p) n) doubling OrderHom.id le_doubling le_refl :=
  Interleaving.ofLE R (F := cechFiltration p) (G := ripsFiltration p)
    (fun r : ℝ≥0 ↦ (cech_le_vietorisRips p r).trans_eq (by
      change _ = vietorisRips p ((2 * r : ℝ≥0) : ℝ)
      simp))
    (fun r : ℝ≥0 ↦ vietorisRips_le_cech p r.2) n

/-- The persistent Betti number `β_n^{s,t}` of a filtration over a field `k`: the rank of the
map `Hₙ(F s; k) → Hₙ(F t; k)`, i.e. the number of classes born by `s` that are still alive at
`t`. -/
noncomputable def persistentBetti (k : Type u) [Field k] (F : T →o PreAbstractSimplicialComplex ι)
    (n : ℕ) {s t : T} (h : s ≤ t) : ℕ :=
  Module.finrank k (LinearMap.range
    (PreAbstractSimplicialComplex.homologyMap (C := ModuleCat.{u} k) (ModuleCat.of k k)
      (F.monotone h) n).hom)

end PreAbstractSimplicialComplex
