/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Simplicial sets with an extra degeneracy are acyclic

An *extra degeneracy* on a simplicial set `X`, augmented to a point, is a family of maps
`s : X _⦋n⦌ → X _⦋n + 1⦌` (and a base point `s' : pt → X _⦋0⦌`) behaving like a degeneracy
`σ₋₁` that inserts a new vertex in front. The cone on any simplicial complex has one: put the
apex first. Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` shows that
such an augmented simplicial object has an alternating face map complex that is homotopy
equivalent to its augmentation target.

This file specializes that statement to simplicial chains. If `X` has an extra degeneracy,
then `C•(X; R)` is homotopy equivalent to `R` concentrated in degree `0`. So `H₀(X; R) ≅ R`
and `Hₙ₊₁(X; R) = 0`.

## Main declarations

* `SSet.augmentTerminal X`: `X` augmented to the terminal type.
* `SSet.homotopyEquivOfExtraDegeneracy`: `C•(X; R) ≃ₕ R[0]` given an extra degeneracy.
* `SSet.isZero_homology_succ_of_extraDegeneracy`, `SSet.homology₀IsoOfExtraDegeneracy`.
-/

@[expose] public section

open CategoryTheory Limits Simplicial

universe v u w

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set augmented to the terminal type (the one-point set). -/
@[simps]
noncomputable def augmentTerminal : SSet.Augmented.{u} where
  left := X
  right := ⊤_ (Type u)
  hom := { app := fun _ ↦ terminal.from _ }

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] [Preadditive C] [HasZeroObject C]
  (R : C)

/-- If `X` has an extra degeneracy, its chain complex with coefficients in `R` is homotopy
equivalent to `R` concentrated in degree `0`. -/
noncomputable def homotopyEquivOfExtraDegeneracy
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X.augmentTerminal) :
    HomotopyEquiv (X.chainComplex R) ((ChainComplex.single₀ C).obj R) :=
  (ed.map (sigmaConst.obj R)).homotopyEquiv.trans
    (HomotopyEquiv.ofIso
      ((ChainComplex.single₀ C).mapIso (coproductUniqueIso (fun _ : ⊤_ (Type u) ↦ R))))

variable [CategoryWithHomology C]

theorem isZero_homology_succ_of_extraDegeneracy
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X.augmentTerminal) (n : ℕ) :
    IsZero (X.homology R (n + 1)) :=
  ((X.homotopyEquivOfExtraDegeneracy R ed).toHomologyIso (n + 1)).isZero_iff.2
    (HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by simp))

/-- If `X` has an extra degeneracy, `H₀(X; R) ≅ R`. -/
noncomputable def homology₀IsoOfExtraDegeneracy
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X.augmentTerminal) :
    X.homology R 0 ≅ R :=
  (X.homotopyEquivOfExtraDegeneracy R ed).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

end SSet
