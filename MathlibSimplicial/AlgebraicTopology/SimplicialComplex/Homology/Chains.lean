/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Normalized chains of a simplicial complex

Mathlib's `SSet.normalizedChainComplex` keeps only the nondegenerate simplices of a simplicial
set. It is homotopy equivalent to the full chain complex, so it computes the same homology. For a
complex `K`, the nondegenerate `n`-simplices of `K.toSSet` are the `n`-faces of `K`
(`nonDegenerateEquiv`). So the normalized complex of `K.toSSet` is the textbook simplicial chain
complex:

  `Nₙ(K; R) ≅ ⨁_{n-faces of K} R`   (`normalizedChainComplexXIso`).

## Comparing subcomplexes

An inclusion `L ≤ K` induces a map of normalized chains, sending each face of `L` to the same
face of `K`. If `L` and `K` have the same `n`-faces, this map is an isomorphism in degree `n`
(`isIso_normalizedChainComplexMap_f`). If they have the same faces with at most `k + 2`
vertices, the inclusion is an isomorphism on `Hₖ` (`isIso_homologyMap_of_faces`). This is
the "homology only sees the `(k+1)`-skeleton" principle.

## Still planned (roadmap step 5)

The explicit boundary formula `∂[v₀,…,vₙ] = ∑ (-1)ⁱ [v₀,…,v̂ᵢ,…,vₙ]` in terms of faces, and a
version with coefficients in a module, for linear-algebra computations.

## Main declarations

* `ChainComplex.isIso_homologyMap_of_isIso_f`: a chain map that is an isomorphism in degrees
  `≤ k + 1` is an isomorphism on `Hₖ`.
* `PreAbstractSimplicialComplex.normalizedChainComplex`,
  `PreAbstractSimplicialComplex.normalizedChainComplexXIso`.
* `PreAbstractSimplicialComplex.homologyIsoNormalized`: homology computed by normalized chains.
* `PreAbstractSimplicialComplex.isIso_homologyMap_of_faces`.
-/

@[expose] public section

open CategoryTheory Limits Simplicial Finset

universe v u w

namespace ChainComplex

variable {C : Type w} [Category.{v} C] [HasZeroMorphisms C]

/-- A chain map that is an isomorphism in degrees `≤ k + 1` induces an isomorphism on `Hₖ`. -/
theorem isIso_homologyMap_of_isIso_f {A B : ChainComplex C ℕ} (φ : A ⟶ B) (k : ℕ)
    [A.HasHomology k] [B.HasHomology k] (hφ : ∀ j ≤ k + 1, IsIso (φ.f j)) :
    IsIso (HomologicalComplex.homologyMap φ k) := by
  have h1 := hφ ((ComplexShape.down ℕ).prev k) (by simp)
  have h2 := hφ k (by omega)
  have h3 := hφ ((ComplexShape.down ℕ).next k) (by cases k <;> simp; omega)
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
    (by dsimp; infer_instance) h2 (by dsimp; infer_instance)

end ChainComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι]
variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C] (R : C)

section

variable (K : PreAbstractSimplicialComplex ι)

/-- The normalized chain complex of `K`: in degree `n`, one copy of `R` for each `n`-face. -/
noncomputable abbrev normalizedChainComplex : ChainComplex C ℕ :=
  K.toSSet.normalizedChainComplex R

/-- The normalized `n`-chains of `K` are a direct sum of copies of `R` over the `n`-faces. -/
noncomputable def normalizedChainComplexXIso (n : ℕ) :
    (K.normalizedChainComplex R).X n ≅ ∐ fun _ : K.facesOfDim n ↦ R :=
  (K.toSSet.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
    (coproductIsCoproduct _) ≪≫ (Sigma.reindex (K.nonDegenerateEquiv n).symm (fun _ ↦ R)).symm

end

variable {K L : PreAbstractSimplicialComplex ι} (h : L ≤ K)

/-- The map of normalized chains induced by an inclusion `L ≤ K`. -/
noncomputable abbrev normalizedChainComplexMap :
    L.normalizedChainComplex R ⟶ K.normalizedChainComplex R :=
  SSet.normalizedChainComplexMap (toSSetMap h) R

theorem toSSetMap_mem_nonDegenerate {n : ℕ} (x : L.toSSet _⦋n⦌)
    (hx : x ∈ L.toSSet.nonDegenerate n) :
    (toSSetMap h).app _ x ∈ K.toSSet.nonDegenerate n := by
  rw [mem_nonDegenerate_toSSet_iff] at hx ⊢
  exact hx

/-- If every `n`-face of `K` lies in `L`, the inclusion is an isomorphism on normalized
`n`-chains. -/
theorem isIso_normalizedChainComplexMap_f {n : ℕ} (hn : ∀ s ∈ K, s.card = n + 1 → s ∈ L) :
    IsIso ((normalizedChainComplexMap R h).f n) := by
  let lift (x : K.toSSet.nonDegenerate n) : L.toSSet _⦋n⦌ := ⟨x.1.1, hn _ x.1.2 (by
    rw [card_image_of_injective _ ((K.mem_nonDegenerate_toSSet_iff x.1).1 x.2).injective,
      card_univ, Fintype.card_fin])⟩
  refine ⟨(K.toSSet.isColimitCofanNormalizedChainComplex R n).desc
    (Cofan.mk _ fun x ↦ L.toSSet.ιNormalizedChainComplex (lift x)), ?_, ?_⟩
  · ext x hx
    rw [SSet.ι_normalizedChainComplexMap_f_assoc, Category.comp_id]
    exact (K.toSSet.isColimitCofanNormalizedChainComplex R n).fac _
      ⟨⟨(toSSetMap h).app _ x, toSSetMap_mem_nonDegenerate h x hx⟩⟩
  · ext x hx
    have := (K.toSSet.isColimitCofanNormalizedChainComplex R n).fac
      (Cofan.mk _ fun x ↦ L.toSSet.ιNormalizedChainComplex (lift x)) ⟨⟨x, hx⟩⟩
    dsimp at this
    rw [reassoc_of% this, SSet.ι_normalizedChainComplexMap_f, Category.comp_id]
    rfl

variable [CategoryWithHomology C]

variable (K) in
/-- Homology of `K` computed by the normalized chain complex. -/
noncomputable def homologyIsoNormalized (n : ℕ) :
    K.homology R n ≅ (K.normalizedChainComplex R).homology n :=
  asIso (HomologicalComplex.homologyMap (K.toSSet.toNormalizedChainComplex R) n)

theorem homologyMap_comp_homologyIsoNormalized_hom (n : ℕ) :
    PreAbstractSimplicialComplex.homologyMap R h n ≫ (K.homologyIsoNormalized R n).hom =
      (L.homologyIsoNormalized R n).hom ≫
        HomologicalComplex.homologyMap (normalizedChainComplexMap R h) n := by
  simp only [PreAbstractSimplicialComplex.homologyMap, SSet.homologyMap, homologyIsoNormalized,
    asIso_hom, ← HomologicalComplex.homologyMap_comp,
    SSet.toNormalizedChainComplex_normalizedChainComplexMap]

/-- If `L ≤ K` have the same faces with at most `k + 2` vertices, the inclusion induces an
isomorphism on `Hₖ`. -/
theorem isIso_homologyMap_of_faces {k : ℕ} (hk : ∀ s ∈ K, s.card ≤ k + 2 → s ∈ L) :
    IsIso (PreAbstractSimplicialComplex.homologyMap R h k) := by
  have : IsIso (HomologicalComplex.homologyMap (normalizedChainComplexMap R h) k) :=
    ChainComplex.isIso_homologyMap_of_isIso_f _ _ fun _ _ ↦
      isIso_normalizedChainComplexMap_f R h fun s hs _ ↦ hk s hs (by omega)
  have e := homologyMap_comp_homologyIsoNormalized_hom R h k
  rw [← Iso.eq_comp_inv] at e
  rw [e]
  infer_instance

end PreAbstractSimplicialComplex
