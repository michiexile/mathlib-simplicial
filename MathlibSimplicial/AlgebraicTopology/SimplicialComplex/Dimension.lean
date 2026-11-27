/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Simplex
public import Mathlib.Data.ENat.Lattice

/-!
# The dimension of a simplicial complex

The dimension of `K` is the supremum of the dimensions `s.card - 1` of its faces. We let it take
values in `WithBot ℕ∞`:

* `⊥` stands for the empty complex (classically, dimension `-1`);
* `⊤` stands for a complex with faces of every dimension, which needs infinitely many vertices.

So `dim` is defined for every complex, with no finiteness assumption. Cunningham–Zach–Friedl
(`Pachner/Basic/Dimension.lean`) use an integer-valued dimension for finite complexes instead.

## Main declarations

* `PreAbstractSimplicialComplex.dim K`.
* `PreAbstractSimplicialComplex.dim_le_iff`: `K.dim ≤ n` iff every face has at most `n + 1`
  vertices.
* `PreAbstractSimplicialComplex.dim_eq_bot_iff`: `K.dim = ⊥` iff `K` is empty.
* `PreAbstractSimplicialComplex.dim_simplex`: the simplex on `s` has dimension `s.card - 1`.
-/

@[expose] public section

open Finset

variable {ι : Type*}

namespace PreAbstractSimplicialComplex

variable {K L : PreAbstractSimplicialComplex ι} {s : Finset ι}

/-- The dimension of `K`: the supremum of `s.card - 1` over faces `s`, valued in `WithBot ℕ∞` so
that the empty complex has dimension `⊥` and infinite-dimensional complexes have dimension `⊤`. -/
noncomputable def dim (K : PreAbstractSimplicialComplex ι) : WithBot ℕ∞ :=
  ⨆ s ∈ K, (((s.card - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)

/-- Every face has dimension at most `K.dim`. -/
theorem card_sub_one_le_dim (hs : s ∈ K) : (((s.card - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ K.dim :=
  le_biSup (fun s ↦ (((s.card - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) hs

/-- `K` has dimension at most `n` iff every face has at most `n + 1` vertices. -/
theorem dim_le_iff {n : ℕ} : K.dim ≤ ((n : ℕ∞) : WithBot ℕ∞) ↔ ∀ s ∈ K, s.card ≤ n + 1 := by
  simp only [dim, iSup₂_le_iff, WithBot.coe_le_coe, ENat.natCast_le_natCast]
  exact forall₂_congr fun _ _ ↦ by omega

theorem dim_mono (h : K ≤ L) : K.dim ≤ L.dim :=
  biSup_mono fun _ hs ↦ h hs

/-- A complex has dimension `⊥` exactly when it has no faces. -/
theorem dim_eq_bot_iff : K.dim = ⊥ ↔ K = ⊥ := by
  simp only [dim, iSup_eq_bot, WithBot.coe_ne_bot, imp_false]
  constructor
  · intro h
    ext s
    exact ⟨fun hs ↦ h s hs, fun hs ↦ hs.elim⟩
  · rintro rfl s hs
    exact hs

@[simp]
theorem dim_bot : (⊥ : PreAbstractSimplicialComplex ι).dim = ⊥ := dim_eq_bot_iff.2 rfl

/-- The full simplex on a nonempty finset `s` has dimension `s.card - 1`. -/
theorem dim_simplex (hs : s.Nonempty) :
    (simplex s).dim = (((s.card - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  refine le_antisymm (dim_le_iff.2 fun t ht ↦ ?_) (card_sub_one_le_dim (self_mem_simplex hs))
  have := card_le_card ht.2
  have := hs.card_pos
  omega

/-- The `n`-skeleton has dimension at most `n`. -/
theorem dim_skeleton_le (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    (K.skeleton n).dim ≤ ((n : ℕ∞) : WithBot ℕ∞) :=
  dim_le_iff.2 fun _ hs ↦ hs.2

end PreAbstractSimplicialComplex
