/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.ToSSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Simplicial homology of a simplicial complex

The homology of a complex `K` on a linearly ordered vertex type is defined as Mathlib's homology
of the simplicial set `K.toSSet`. This makes everything Mathlib proves about homology of
simplicial sets available for complexes.

Coefficients are an object `R` of a preadditive category `C` with coproducts. The usual case is
`C = ModuleCat k` and `R = k` for a ring or field `k`, giving `Hₙ(K; k)`.

Homology is functorial in subcomplex inclusions. Since the complexes on `ι` form a partial order
(and so a category in which a morphism `K ⟶ L` is a proof of `K ≤ L`), homology in degree `n` is
a functor `PreAbstractSimplicialComplex ι ⥤ C`. Composing it with a filtration, i.e. a monotone
family of complexes, gives a persistence module (roadmap step 6).

## Main declarations

* `PreAbstractSimplicialComplex.chainComplex K R` and `PreAbstractSimplicialComplex.homology K R n`.
* `PreAbstractSimplicialComplex.homologyMap`: the map induced by `K ≤ L`.
* `PreAbstractSimplicialComplex.homologyFunctor R n`: homology as a functor on the poset of
  complexes on `ι`.
-/

@[expose] public section

open CategoryTheory Limits

universe v u w

variable {ι : Type u} [LinearOrder ι]

namespace PreAbstractSimplicialComplex

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C] (R : C)
variable (K : PreAbstractSimplicialComplex ι) {L M : PreAbstractSimplicialComplex ι}

/-- The simplicial chain complex of `K` with coefficients in `R`. -/
noncomputable abbrev chainComplex : ChainComplex C ℕ := K.toSSet.chainComplex R

variable {K} in
/-- The chain map induced by an inclusion `K ≤ L`. -/
noncomputable abbrev chainComplexMap (h : K ≤ L) : K.chainComplex R ⟶ L.chainComplex R :=
  SSet.chainComplexMap (toSSetMap h) R

variable [CategoryWithHomology C]

/-- The simplicial homology of `K` in degree `n` with coefficients in `R`. -/
protected noncomputable abbrev homology (n : ℕ) : C := K.toSSet.homology R n

variable {K}

/-- The map in homology induced by an inclusion `K ≤ L`. -/
protected noncomputable abbrev homologyMap (h : K ≤ L) (n : ℕ) :
    K.homology R n ⟶ L.homology R n :=
  SSet.homologyMap (toSSetMap h) R n

@[simp]
theorem homologyMap_refl (n : ℕ) :
    PreAbstractSimplicialComplex.homologyMap R (le_refl K) n = 𝟙 _ := by
  simp [PreAbstractSimplicialComplex.homologyMap]

theorem homologyMap_comp (h : K ≤ L) (h' : L ≤ M) (n : ℕ) :
    PreAbstractSimplicialComplex.homologyMap R (h.trans h') n =
      PreAbstractSimplicialComplex.homologyMap R h n ≫
        PreAbstractSimplicialComplex.homologyMap R h' n := by
  simp only [PreAbstractSimplicialComplex.homologyMap, ← toSSetMap_comp h h',
    SSet.homologyMap_comp]

variable (ι) in
/-- Homology in degree `n` as a functor on the poset of complexes on `ι`. Composed with a
filtration, this is persistent homology. -/
@[simps]
noncomputable def homologyFunctor (n : ℕ) : PreAbstractSimplicialComplex ι ⥤ C where
  obj K := K.homology R n
  map f := PreAbstractSimplicialComplex.homologyMap R (leOfHom f) n
  map_id K := homologyMap_refl R n (K := K)
  map_comp f g := homologyMap_comp R (leOfHom f) (leOfHom g) n

end PreAbstractSimplicialComplex
