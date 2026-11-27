/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Chains
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Oriented chains as finitely supported functions

Over a ring `R`, the normalized chains of `K` in degree `n` are the free `R`-module on the
`n`-faces. This file presents them concretely as `K.facesOfDim n →₀ R` (finitely supported
functions, Mathlib's model of free modules), which makes it possible to compute with individual
chains: a chain is a finite formal `R`-linear combination of faces.

`K.orientedChainComplex R` has these modules as its chain groups, with the textbook boundary
`∂[v₀, …, vₙ₊₁] = ∑ᵢ (-1)ⁱ [v₀, …, v̂ᵢ, …, vₙ₊₁]` (`orientedChainComplex_d_single`). It is defined
by transporting the differential of the normalized chain complex along the degreewise
isomorphisms `chainsXIso`, so `d ∘ d = 0` comes for free, and it is isomorphic to the normalized
complex (`orientedIso`). In particular it computes the simplicial homology of `K`
(`homologyIsoOriented`).

## Main declarations

* `PreAbstractSimplicialComplex.chainsXIso`: normalized `n`-chains are `K.facesOfDim n →₀ R`.
* `PreAbstractSimplicialComplex.orientedChainComplex`, `PreAbstractSimplicialComplex.orientedIso`.
* `PreAbstractSimplicialComplex.orientedChainComplex_d_single`: the boundary formula.
* `PreAbstractSimplicialComplex.homologyIsoOriented`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι)

theorem faceChain_normalizedChainComplexXIso_hom {C : Type*} [Category C] [HasCoproducts.{u} C]
    [Preadditive C] (R : C) {n : ℕ} (t : K.facesOfDim n) :
    K.faceChain R t ≫ (K.normalizedChainComplexXIso R n).hom = Sigma.ι (fun _ ↦ R) t := by
  have := (K.toSSet.isColimitCofanNormalizedChainComplex R n).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct _) ⟨(K.nonDegenerateEquiv n).symm t⟩
  simp only [normalizedChainComplexXIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  erw [this]
  exact Sigma.ι_reindex_inv _ _ t

variable (R : Type u) [Ring R]

/-- Over a ring `R`, the normalized `n`-chains of `K` are the finitely supported functions from
the `n`-faces to `R`. -/
noncomputable def chainsXIso (n : ℕ) :
    (K.normalizedChainComplex (ModuleCat.of R R)).X n ≅ ModuleCat.of R (K.facesOfDim n →₀ R) :=
  K.normalizedChainComplexXIso _ n ≪≫ ModuleCat.coprodIsoDirectSum _ ≪≫
    (finsuppLEquivDirectSum R R (K.facesOfDim n)).symm.toModuleIso

theorem faceChain_chainsXIso_hom {n : ℕ} (t : K.facesOfDim n) :
    K.faceChain (ModuleCat.of R R) t ≫ (K.chainsXIso R n).hom =
      ModuleCat.ofHom (Finsupp.lsingle t) := by
  simp only [chainsXIso, Iso.trans_hom, reassoc_of% faceChain_normalizedChainComplexXIso_hom,
    reassoc_of% ModuleCat.ι_coprodIsoDirectSum_hom]
  ext : 2
  simp

/-- The oriented chain complex: `n`-chains are `K.facesOfDim n →₀ R`, and the differential is
the textbook alternating sum of faces (`orientedChainComplex_d_single`). -/
noncomputable def orientedChainComplex : ChainComplex (ModuleCat.{u} R) ℕ where
  X n := ModuleCat.of R (K.facesOfDim n →₀ R)
  d i j := (K.chainsXIso R i).inv ≫ (K.normalizedChainComplex _).d i j ≫ (K.chainsXIso R j).hom
  shape i j h := by simp [HomologicalComplex.shape _ _ _ h]
  d_comp_d' i j k _ _ := by simp

/-- The oriented chain complex is isomorphic to the normalized chain complex. -/
noncomputable def orientedIso :
    K.normalizedChainComplex (ModuleCat.of R R) ≅ K.orientedChainComplex R :=
  HomologicalComplex.Hom.isoOfComponents (K.chainsXIso R) (by simp [orientedChainComplex])

/-- The boundary formula for oriented chains. -/
theorem orientedChainComplex_d_single {n : ℕ} (t : K.facesOfDim (n + 1)) (r : R) :
    (K.orientedChainComplex R).d (n + 1) n (Finsupp.single t r) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.single (faceErase t i) r := by
  have key : ModuleCat.ofHom (Finsupp.lsingle t) ≫ (K.orientedChainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • ModuleCat.ofHom (Finsupp.lsingle (faceErase t i)) := by
    simp only [orientedChainComplex, ← faceChain_chainsXIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc, reassoc_of% (K.faceChain_d (ModuleCat.of R R) t),
      Preadditive.sum_comp, Preadditive.zsmul_comp]
  have := congrArg (fun f ↦ f.hom r) key
  refine this.trans ?_
  erw [ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rfl

/-- The simplicial homology of `K` over `R` is the homology of the oriented chain complex. -/
noncomputable def homologyIsoOriented (n : ℕ) :
    K.homology (ModuleCat.of R R) n ≅ (K.orientedChainComplex R).homology n :=
  K.homologyIsoNormalized _ n ≪≫ HomologicalComplex.homologyMapIso (K.orientedIso R) n

end PreAbstractSimplicialComplex
