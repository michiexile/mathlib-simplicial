/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# From simplicial complexes to simplicial sets

**Status: planned (roadmap step 3).** This file is a placeholder that fixes where the
material will live; it contains no declarations yet.

Planned: for a linearly ordered vertex type, `K.toSSet` as the subcomplex of `nerve ι` whose
`n`-simplices are monotone maps `Fin (n + 1) → ι` with image a face of `K`; nondegenerate
`n`-simplices of `K.toSSet` correspond to `n`-dimensional faces of `K`
(using `Mathlib/AlgebraicTopology/SimplicialSet/NerveNondegenerate.lean`); functoriality in
simplicial maps.
-/
