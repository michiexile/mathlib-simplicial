/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Simplicial cochains and cohomology

Mathlib has homology of simplicial sets but no cohomology. As Mikael put it, this is natural:
cohomology is the homology of a hom-complex. Here we define it that way. For coefficients
`R M : C` in a preadditive category, the cochain complex of a simplicial set `X` is

  `Cⁿ(X; R, M) = Hom_C(Cₙ(X; R), M)`,

with the coboundary given by precomposition with the boundary of the chain complex. In Lean this
is the chain complex of `X`, turned into a complex in `Cᵒᵖ` (`HomologicalComplex.opFunctor`), with
the hom-functor `Hom(-, M) : Cᵒᵖ ⥤ AddCommGrpCat` applied degreewise. Reversing the arrows turns
the `ℕ`-graded chain complex into an `ℕ`-graded cochain complex (shape `(ComplexShape.down ℕ).symm`,
whose differential raises degree).

For `C = ModuleCat k` and `R = M = k`, `Cⁿ(X; k, k)` is the group of `k`-valued functions on
`n`-simplices, the usual simplicial cochains. The values are abelian groups. A `k`-linear version
would use `linearYoneda` instead of `preadditiveYoneda`, at the cost of a `Linear` assumption.

For a complex `K`, the cochains and cohomology of `K` are those of `K.toSSet`, so the "bridge to
`SSet` for cochains" holds by definition. Cohomology is contravariant, so on the poset of
complexes it is a functor out of the opposite category.

## Main declarations

* `SSet.cochainComplexFunctor R M`, `SSet.cochainComplex X R M`, `SSet.cohomology X R M n`.
* `PreAbstractSimplicialComplex.toSSetFunctor`: `K ↦ K.toSSet` as a functor.
* `PreAbstractSimplicialComplex.cochainComplex K R M`, `PreAbstractSimplicialComplex.cohomology`.
* `PreAbstractSimplicialComplex.cohomologyFunctor R M n`: cohomology as a functor
  `(PreAbstractSimplicialComplex ι)ᵒᵖ ⥤ AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace SSet

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C] (R M : C)

/-- The simplicial cochain complex, as a functor of the simplicial set: in degree `n` it is
`Hom(Cₙ(X; R), M)`. -/
noncomputable def cochainComplexFunctor :
    SSet.{u}ᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ).symm :=
  ((SSet.chainComplexFunctor C).obj R).op ⋙ HomologicalComplex.opFunctor C _ ⋙
    (preadditiveYoneda.obj M).mapHomologicalComplex _

variable (X : SSet.{u})

/-- The simplicial cochain complex of `X` with coefficients `Hom(R, M)`. -/
noncomputable abbrev cochainComplex :
    HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ).symm :=
  (cochainComplexFunctor R M).obj (op X)

/-- The simplicial cohomology of `X` in degree `n`. -/
protected noncomputable abbrev cohomology (n : ℕ) : AddCommGrpCat.{v} :=
  (X.cochainComplex R M).homology n

/-- Cohomology in degree `n` as a contravariant functor of the simplicial set. -/
noncomputable def cohomologyFunctor (n : ℕ) : SSet.{u}ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  cochainComplexFunctor R M ⋙ HomologicalComplex.homologyFunctor _ _ n

end SSet

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι]

variable (ι) in
/-- `K ↦ K.toSSet` as a functor from the poset of complexes on `ι` to simplicial sets. -/
@[simps]
noncomputable def toSSetFunctor : PreAbstractSimplicialComplex ι ⥤ SSet.{u} where
  obj K := K.toSSet
  map f := toSSetMap (leOfHom f)

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C] (R M : C)
variable (K : PreAbstractSimplicialComplex ι)

/-- The simplicial cochain complex of `K`: in degree `n`, homomorphisms `Cₙ(K; R) → M`. -/
noncomputable abbrev cochainComplex :
    HomologicalComplex AddCommGrpCat.{v} (ComplexShape.down ℕ).symm :=
  K.toSSet.cochainComplex R M

/-- The simplicial cohomology of `K` in degree `n`. -/
protected noncomputable abbrev cohomology (n : ℕ) : AddCommGrpCat.{v} :=
  K.toSSet.cohomology R M n

variable (ι) in
/-- Cohomology in degree `n` as a contravariant functor on the poset of complexes on `ι`. -/
noncomputable def cohomologyFunctor (n : ℕ) :
    (PreAbstractSimplicialComplex ι)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (toSSetFunctor ι).op ⋙ SSet.cohomologyFunctor R M n

@[simp]
theorem cohomologyFunctor_obj (n : ℕ) :
    (cohomologyFunctor ι R M n).obj (op K) = K.cohomology R M n := rfl

end PreAbstractSimplicialComplex
