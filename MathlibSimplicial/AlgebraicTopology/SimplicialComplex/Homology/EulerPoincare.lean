/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.Algebra.Homology.EulerPoincare
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Chains
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# The Euler–Poincaré formula for simplicial complexes

For a finite complex `K` and a field `k`, the combinatorial Euler characteristic
`K.eulerChar = ∑ (-1)ⁿ fₙ` (with `fₙ` the number of `n`-faces) equals the alternating sum of
the Betti numbers `βₙ = dim_k Hₙ(K; k)`:

  `χ(K) = ∑ (-1)ⁿ fₙ = ∑ (-1)ⁿ βₙ`.

The proof has three steps.
* The normalized chain complex of `K` has `Nₙ(K; k) ≅ kᶠⁿ`
  (`normalizedChainComplexXIso`, then `ModuleCat.coprodIsoDirectSum`), so
  `dim Nₙ = fₙ` (`finrank_normalizedChainComplex_X`).
* The normalized complex computes the homology of `K` (`homologyIsoNormalized`).
* The Euler–Poincaré formula for chain complexes of vector spaces
  (`ChainComplex.alternating_sum_finrank_X_eq_homology`).

Coefficients are `ModuleCat.of k k`, with `k` in the same universe as the vertex type `ι`, so
that `ModuleCat.{u} k` has the coproducts that the chain complex needs.

## Main declarations

* `PreAbstractSimplicialComplex.finrank_normalizedChainComplex_X`: `dim Nₙ(K; k) = fₙ`.
* `PreAbstractSimplicialComplex.betti`: the Betti number `βₙ = dim_k Hₙ(K; k)`.
* `PreAbstractSimplicialComplex.eulerChar_eq_sum_betti`: the Euler–Poincaré formula.
-/

@[expose] public section

open CategoryTheory Limits Module Finset DirectSum

universe u

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι)
variable (k : Type u) [Field k]

/-- The normalized `n`-chains with coefficients in `k`, as a vector space: one coordinate for
each `n`-face. -/
noncomputable def normalizedChainComplexXLinearEquiv (n : ℕ) :
    (K.normalizedChainComplex (ModuleCat.of k k)).X n ≃ₗ[k]
      ⨁ _ : K.facesOfDim n, k :=
  (K.normalizedChainComplexXIso (ModuleCat.of k k) n ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv

/-- The `n`-th Betti number of `K` over the field `k`: `dim_k Hₙ(K; k)`. -/
noncomputable def betti (n : ℕ) : ℕ :=
  finrank k (PreAbstractSimplicialComplex.homology (C := ModuleCat.{u} k) (ModuleCat.of k k) K n)

theorem betti_eq_finrank_normalized (n : ℕ) :
    K.betti k n = finrank k ((K.normalizedChainComplex (ModuleCat.of k k)).homology n) :=
  (K.homologyIsoNormalized (ModuleCat.of k k) n).toLinearEquiv.finrank_eq

instance [Finite ι] (n : ℕ) :
    FiniteDimensional k ((K.normalizedChainComplex (ModuleCat.of k k)).X n) :=
  have := Fintype.ofFinite ι
  LinearEquiv.finiteDimensional (K.normalizedChainComplexXLinearEquiv k n).symm

variable [Fintype ι] [DecidablePred (· ∈ K)]

instance (n : ℕ) : Fintype (K.facesOfDim n) :=
  Fintype.ofFinset (K.finsetFacesOfDim n) fun s ↦ by
    rw [← Finset.mem_coe, coe_finsetFacesOfDim]

omit [LinearOrder ι] in
theorem card_facesOfDim (n : ℕ) : Fintype.card (K.facesOfDim n) = K.fVector n :=
  Fintype.card_ofFinset _ _

/-- The normalized `n`-chains of `K` over `k` have dimension `fₙ`, the number of `n`-faces. -/
theorem finrank_normalizedChainComplex_X (n : ℕ) :
    finrank k ((K.normalizedChainComplex (ModuleCat.of k k)).X n) = K.fVector n := by
  rw [(K.normalizedChainComplexXLinearEquiv k n).finrank_eq, finrank_directSum]
  simp only [finrank_self, sum_const, card_univ, card_facesOfDim, smul_eq_mul, mul_one]

/-- **Euler–Poincaré**: the combinatorial Euler characteristic of a finite complex is the
alternating sum of its Betti numbers over any field. -/
theorem eulerChar_eq_sum_betti :
    K.eulerChar = ∑ n ∈ range (Fintype.card ι), (-1 : ℤ) ^ n * K.betti k n := by
  obtain h | ⟨N, hN⟩ : Fintype.card ι = 0 ∨ ∃ N, Fintype.card ι = N + 1 := by
    rcases Fintype.card ι with _ | N
    · exact .inl rfl
    · exact .inr ⟨N, rfl⟩
  · simp [eulerChar, h]
  · have hzero : IsZero ((K.normalizedChainComplex (ModuleCat.of k k)).X (N + 1)) := by
      have := K.hasDimensionLT_toSSet (d := N + 1) fun s _ ↦ hN ▸ card_le_univ s
      exact SSet.isZero_normalizedChainComplex_X_of_hasDimensionLT _ _ (N + 1) (N + 1)
    have h := (K.normalizedChainComplex (ModuleCat.of k k)).alternating_sum_finrank_X_eq_homology
      N hzero
    simp only [finrank_normalizedChainComplex_X, ← betti_eq_finrank_normalized] at h
    rw [eulerChar, hN, h]

end PreAbstractSimplicialComplex
