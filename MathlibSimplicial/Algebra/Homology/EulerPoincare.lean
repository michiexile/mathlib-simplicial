/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Euler–Poincaré formula for chain complexes of vector spaces

For a chain complex `C` of finite-dimensional vector spaces over a field, concentrated in
degrees `0, …, N`, the alternating sum of the dimensions of the chain spaces equals the
alternating sum of the dimensions of the homology:

  `∑ (-1)ⁿ dim Cₙ = ∑ (-1)ⁿ dim Hₙ(C)`.

Write `zₙ = dim ker dₙ`, `rₙ = dim im dₙ` (with `dₙ : Cₙ → Cₙ₋₁`). Rank–nullity gives
`dim Cₙ = zₙ + rₙ`, and `Hₙ = ker dₙ / im dₙ₊₁` gives `dim Hₙ + rₙ₊₁ = zₙ`. So
`dim Cₙ - dim Hₙ = rₙ + rₙ₊₁`, and the alternating sum telescopes to `± r_{N+1}`, which is `0`.

Mathlib defines `HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar`, but
(at the pinned version) does not yet prove that they agree. This file proves the finite-sum form
for `ℕ`-graded chain complexes, which is what simplicial complexes need.

## Main declarations

* `ChainComplex.finrank_homology_add_finrank_range`: `dim Hₙ + rₙ₊₁ = zₙ`.
* `ChainComplex.alternating_sum_finrank_sub`: the telescoped identity, for any `N`.
* `ChainComplex.alternating_sum_finrank_X_eq_homology`: the Euler–Poincaré formula.
-/

@[expose] public section

open CategoryTheory Limits Module Finset

universe v u

namespace ChainComplex

variable {k : Type u} [Field k] (C : ChainComplex (ModuleCat.{v} k) ℕ)

theorem finrank_X_eq (n : ℕ) [FiniteDimensional k (C.X n)] :
    finrank k (C.X n) =
      finrank k (LinearMap.ker (C.d n (n - 1)).hom) +
        finrank k (LinearMap.range (C.d n (n - 1)).hom) := by
  rw [add_comm]
  exact (LinearMap.finrank_range_add_finrank_ker _).symm

theorem finrank_homology_add_finrank_range (n : ℕ) [FiniteDimensional k (C.X n)]
    [FiniteDimensional k (C.X (n + 1))] :
    finrank k (C.homology n) + finrank k (LinearMap.range (C.d (n + 1) n).hom) =
      finrank k (LinearMap.ker (C.d n (n - 1)).hom) := by
  let S := C.sc' (n + 1) n (n - 1)
  have : FiniteDimensional k S.X₁ := ‹FiniteDimensional k (C.X (n + 1))›
  have : FiniteDimensional k S.X₂ := ‹FiniteDimensional k (C.X n)›
  have e : C.homology n ≅ S.moduleCatLeftHomologyData.H :=
    ShortComplex.homologyMapIso (C.isoSc' (n + 1) n (n - 1) (by simp)
      (by cases n <;> simp)) ≪≫ S.moduleCatHomologyIso
  rw [e.toLinearEquiv.finrank_eq]
  have hker : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom :=
    LinearMap.ker_codRestrict _ _ _
  have h1 := LinearMap.finrank_range_add_finrank_ker S.moduleCatToCycles
  have h2 := LinearMap.finrank_range_add_finrank_ker S.f.hom
  rw [hker] at h1
  have h3 : finrank k (LinearMap.range S.moduleCatToCycles) =
      finrank k (LinearMap.range (C.d (n + 1) n).hom) := by
    change _ = finrank k (LinearMap.range S.f.hom)
    omega
  rw [← h3]
  exact Submodule.finrank_quotient_add_finrank _

omit C in
theorem finrank_range_zero_hom {X Y : ModuleCat.{v} k} :
    finrank k (LinearMap.range (0 : X ⟶ Y).hom) = 0 := by
  rw [ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

theorem finrank_range_d_zero : finrank k (LinearMap.range (C.d 0 (0 - 1)).hom) = 0 := by
  rw [C.shape 0 (0 - 1) (by simp)]
  exact finrank_range_zero_hom

theorem alternating_sum_finrank_sub [∀ n, FiniteDimensional k (C.X n)] (N : ℕ) :
    ∑ n ∈ range (N + 1), (-1 : ℤ) ^ n * finrank k (C.X n) -
      ∑ n ∈ range (N + 1), (-1 : ℤ) ^ n * finrank k (C.homology n) =
      (-1) ^ N * finrank k (LinearMap.range (C.d (N + 1) N).hom) := by
  have key (n : ℕ) : (finrank k (C.X n) : ℤ) - finrank k (C.homology n) =
      finrank k (LinearMap.range (C.d n (n - 1)).hom) +
        finrank k (LinearMap.range (C.d (n + 1) n).hom) := by
    have h1 := C.finrank_X_eq n
    have h2 := C.finrank_homology_add_finrank_range n
    omega
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub, key]
  induction N with
  | zero => simp [finrank_range_d_zero C]
  | succ N ih =>
    rw [sum_range_succ, ih, add_tsub_cancel_right, pow_succ]
    ring

/-- **Euler–Poincaré**: for a chain complex of finite-dimensional vector spaces that vanishes
above degree `N`, the alternating sums of the dimensions of the chains and of the homology
agree. -/
theorem alternating_sum_finrank_X_eq_homology [∀ n, FiniteDimensional k (C.X n)] (N : ℕ)
    (hN : IsZero (C.X (N + 1))) :
    ∑ n ∈ range (N + 1), (-1 : ℤ) ^ n * finrank k (C.X n) =
      ∑ n ∈ range (N + 1), (-1 : ℤ) ^ n * finrank k (C.homology n) := by
  have h := C.alternating_sum_finrank_sub N
  have h0 : finrank k (LinearMap.range (C.d (N + 1) N).hom) = 0 := by
    rw [show C.d (N + 1) N = 0 from hN.eq_of_src _ _]
    exact finrank_range_zero_hom
  rw [h0, Nat.cast_zero, mul_zero] at h
  omega

end ChainComplex
