/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Cone
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Basic
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Simplex
public import MathlibSimplicial.AlgebraicTopology.SimplicialSet.Homology.ExtraDegeneracy

/-!
# Cones and simplices are acyclic

Suppose a complex `K` has a vertex `v` that can be added to every face (`insert v s ∈ K`), so
`K` is a cone with apex `v`. If `v` is also below every other vertex in the order on `ι`, then
putting `v` in front of a monotone list of vertices is an *extra degeneracy* of `K.toSSet`. By
`SSet.homotopyEquivOfExtraDegeneracy`, `K` then has the homology of a point:

  `H₀(K; R) ≅ R` and `Hₙ₊₁(K; R) = 0`.

Corollaries:
* the full simplex `simplex s` on a nonempty finset is acyclic (apex `s.min'`);
* the cone `L.cone` on any complex is acyclic. The apex `none` is the bottom element once
  `Option ι` is ordered as `WithBot ι`.

The order condition on `v` comes from the linear-order model of `K.toSSet` (see `ToSSet.lean`).
Mathematically, any cone point would do. Removing the condition needs a comparison of
`K.toSSet` for two different orders on `ι`. That is not done yet.

## Main declarations

* `PreAbstractSimplicialComplex.extraDegeneracyOfCone`.
* `PreAbstractSimplicialComplex.isZero_homology_succ_of_cone`,
  `PreAbstractSimplicialComplex.homology₀IsoOfCone`.
* `PreAbstractSimplicialComplex.isZero_homology_succ_simplex`,
  `PreAbstractSimplicialComplex.homology₀IsoSimplex`.
* `PreAbstractSimplicialComplex.isZero_homology_succ_cone`.
-/

@[expose] public section

open CategoryTheory Limits Simplicial Finset

universe v u w

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι]

/-- Put a new first vertex `v` in front of a monotone list of vertices. -/
def consSimplex (v : ι) {n : ℕ} (x : (nerve ι) _⦋n⦌) (hv : v ≤ x.obj 0) :
    (nerve ι) _⦋n + 1⦌ :=
  (monotone_vecCons.2 ⟨hv, fun _ _ h ↦ leOfHom (x.map (homOfLE h))⟩).functor

@[simp]
theorem consSimplex_obj (v : ι) {n : ℕ} (x : (nerve ι) _⦋n⦌) (hv : v ≤ x.obj 0) :
    (consSimplex v x hv).obj = Matrix.vecCons v x.obj := rfl

theorem image_consSimplex (v : ι) {n : ℕ} (x : (nerve ι) _⦋n⦌) (hv : v ≤ x.obj 0) :
    univ.image (consSimplex v x hv).obj = insert v (univ.image x.obj) := by
  ext a
  simp [Fin.exists_fin_succ, eq_comm]

variable {K : PreAbstractSimplicialComplex ι} {v : ι}
  (h0 : {v} ∈ K) (hcone : ∀ s ∈ K, insert v s ∈ K) (hmin : ∀ s ∈ K, ∀ x ∈ s, v ≤ x)

include h0 in
/-- The apex `v` as a `0`-simplex of `K.toSSet`. -/
def apex : K.toSSet _⦋0⦌ :=
  K.simplexOfVertex ⟨v, h0⟩

include hcone hmin in
/-- The extra degeneracy: put the apex `v` in front of a simplex. -/
def consApex {n : ℕ} (x : K.toSSet _⦋n⦌) : K.toSSet _⦋n + 1⦌ :=
  ⟨consSimplex v x.1 (hmin _ x.2 _ (mem_image_of_mem _ (mem_univ 0))), by
    rw [mem_nerveSubcomplex, image_consSimplex]
    exact hcone _ x.2⟩

theorem δ_zero_consApex {n : ℕ} (x : K.toSSet _⦋n⦌) :
    K.toSSet.δ 0 (consApex hcone hmin x) = x := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  refine funext fun (j : Fin (n + 1)) ↦ ?_
  erw [toSSet_δ_obj]

theorem δ_one_consApex (x : K.toSSet _⦋0⦌) :
    K.toSSet.δ 1 (consApex hcone hmin x) = apex h0 := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  refine funext fun (j : Fin 1) ↦ ?_
  erw [toSSet_δ_obj]
  fin_cases j
  simp [consApex, apex, simplexOfVertex]

theorem δ_succ_consApex {n : ℕ} (i : Fin (n + 2)) (x : K.toSSet _⦋n + 1⦌) :
    K.toSSet.δ i.succ (consApex hcone hmin x) = consApex hcone hmin (K.toSSet.δ i x) := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  refine funext fun (j : Fin (n + 2)) ↦ ?_
  erw [toSSet_δ_obj]
  cases j using Fin.cases
  · simp [consApex]
  · simp only [consApex, consSimplex_obj, Fin.succ_succAbove_succ, Matrix.cons_val_succ]
    erw [toSSet_δ_obj]

theorem σ_succ_consApex {n : ℕ} (i : Fin (n + 1)) (x : K.toSSet _⦋n⦌) :
    K.toSSet.σ i.succ (consApex hcone hmin x) = consApex hcone hmin (K.toSSet.σ i x) := by
  apply Subtype.ext
  apply nerve.ext_of_isThin
  refine funext fun (j : Fin (n + 3)) ↦ ?_
  erw [toSSet_σ_obj]
  cases j using Fin.cases
  · simp [consApex]
  · simp only [consApex, consSimplex_obj, Fin.succ_predAbove_succ, Matrix.cons_val_succ]
    erw [toSSet_σ_obj]

/-- A cone whose apex is below every other vertex has an extra degeneracy: put the apex first. -/
noncomputable def extraDegeneracyOfCone :
    SimplicialObject.Augmented.ExtraDegeneracy K.toSSet.augmentTerminal where
  s' := ↾fun _ ↦ apex h0
  s _ := ↾fun x ↦ consApex hcone hmin x
  s'_comp_ε := by
    ext x
    exact Subsingleton.elim (α := ⊤_ (Type u)) _ _
  s₀_comp_δ₁ := by
    ext x
    exact δ_one_consApex h0 hcone hmin x
  s_comp_δ₀ _ := by
    ext x
    exact δ_zero_consApex hcone hmin x
  s_comp_δ _ i := by
    ext x
    exact δ_succ_consApex hcone hmin i x
  s_comp_σ _ i := by
    ext x
    exact σ_succ_consApex hcone hmin i x

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C] [HasZeroObject C]
  [CategoryWithHomology C] (R : C)

section Cone

include h0 hcone hmin

theorem isZero_homology_succ_of_cone (n : ℕ) : IsZero (K.homology R (n + 1)) :=
  K.toSSet.isZero_homology_succ_of_extraDegeneracy R (extraDegeneracyOfCone h0 hcone hmin) n

/-- A cone whose apex is below every other vertex has `H₀ ≅ R`. -/
noncomputable def homology₀IsoOfCone : K.homology R 0 ≅ R :=
  K.toSSet.homology₀IsoOfExtraDegeneracy R (extraDegeneracyOfCone h0 hcone hmin)

end Cone

section Simplex

variable {s : Finset ι} (hs : s.Nonempty)
include hs

theorem isZero_homology_succ_simplex (n : ℕ) : IsZero ((simplex s).homology R (n + 1)) :=
  isZero_homology_succ_of_cone (K := simplex s) (v := s.min' hs)
    ⟨singleton_nonempty _, singleton_subset_iff.2 (s.min'_mem hs)⟩
    (fun _ ht ↦ ⟨insert_nonempty _ _, insert_subset (s.min'_mem hs) ht.2⟩)
    (fun _ ht x hx ↦ s.min'_le x (ht.2 hx)) R n

/-- The full simplex on a nonempty finset has `H₀ ≅ R`. -/
noncomputable def homology₀IsoSimplex : (simplex s).homology R 0 ≅ R :=
  homology₀IsoOfCone (K := simplex s) (v := s.min' hs)
    ⟨singleton_nonempty _, singleton_subset_iff.2 (s.min'_mem hs)⟩
    (fun _ ht ↦ ⟨insert_nonempty _ _, insert_subset (s.min'_mem hs) ht.2⟩)
    (fun _ ht x hx ↦ s.min'_le x (ht.2 hx)) R

end Simplex

section ConeOn

/-- The cone on any complex `L` is acyclic in positive degrees. The vertex type `Option ι` of
the cone is ordered as `WithBot ι`, so that the apex comes first. -/
theorem isZero_homology_succ_cone (L : PreAbstractSimplicialComplex ι) (n : ℕ) :
    IsZero (PreAbstractSimplicialComplex.homology R
      (show PreAbstractSimplicialComplex (WithBot ι) from L.cone) (n + 1)) :=
  isZero_homology_succ_of_cone
    (K := show PreAbstractSimplicialComplex (WithBot ι) from L.cone) (v := ⊥)
    ⟨singleton_nonempty _, .inl (by
      ext a
      simp only [notMem_empty, iff_false]
      exact fun h ↦ Option.some_ne_none a (mem_singleton.1 (mem_eraseNone.1 h)))⟩
    (fun _ ↦ insert_none_mem_cone) (fun _ _ _ _ ↦ bot_le) R n

end ConeOn

end PreAbstractSimplicialComplex
