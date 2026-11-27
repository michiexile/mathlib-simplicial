/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Clique
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Vietoris–Rips and Čech complexes

Let `p : ι → M` be a family of points in a pseudometric space (a point cloud, indexed by `ι` so
that repeated points are allowed and `ι` can carry a vertex order). At scale `r`:

* the **Vietoris–Rips complex** `vietorisRips p r` has a face for every nonempty `s` whose points
  are pairwise within distance `r`. It is the clique complex of the `r`-neighbourhood graph
  `ripsGraph p r`, so it is a flag complex;
* the **Čech complex** `cech p r` has a face for every nonempty `s` whose closed `r`-balls have a
  common point in `M`. It is the nerve of the cover by closed balls.

Both grow with `r`, and they are interleaved (`vietorisRips_le_cech`, `cech_le_vietorisRips`):

  `VR(r) ⊆ Čech(r) ⊆ VR(2r)` for `r ≥ 0`.

## Conventions

Distances are compared with `≤`, so the balls are closed. Some TDA sources use `<` (open balls).
The two conventions give the same persistent homology up to the endpoints of bars.

## Main declarations

* `ripsGraph p r`, `vietorisRips p r`, `mem_vietorisRips`, `vietorisRips_mono`,
  `isFlag_vietorisRips`.
* `cech p r`, `mem_cech`, `cech_mono`.
* `vietorisRips_le_cech`, `cech_le_vietorisRips`.
-/

@[expose] public section

open Finset

variable {ι M : Type*} [PseudoMetricSpace M] (p : ι → M)

namespace PreAbstractSimplicialComplex

/-- The `r`-neighbourhood graph of a point cloud: distinct indices are adjacent when their points
are within distance `r`. -/
def ripsGraph (r : ℝ) : SimpleGraph ι := SimpleGraph.fromRel fun i j ↦ dist (p i) (p j) ≤ r

@[simp]
theorem ripsGraph_adj {r : ℝ} {i j : ι} : (ripsGraph p r).Adj i j ↔ i ≠ j ∧ dist (p i) (p j) ≤ r :=
  by simp [ripsGraph, dist_comm]

/-- The Vietoris–Rips complex at scale `r`: nonempty sets of indices whose points are pairwise
within distance `r`. -/
def vietorisRips (r : ℝ) : PreAbstractSimplicialComplex ι := (ripsGraph p r).cliqueComplex

theorem mem_vietorisRips {r : ℝ} {s : Finset ι} :
    s ∈ vietorisRips p r ↔ s.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (p i) (p j) ≤ r := by
  simp only [vietorisRips, SimpleGraph.mem_cliqueComplex, SimpleGraph.IsClique,
    Set.Pairwise, mem_coe, ripsGraph_adj]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ forall₂_congr fun _ _ ↦
    ⟨fun h hne ↦ (h hne).2, fun h hne ↦ ⟨hne, h hne⟩⟩

theorem vietorisRips_mono {r r' : ℝ} (h : r ≤ r') : vietorisRips p r ≤ vietorisRips p r' :=
  SimpleGraph.cliqueComplex_mono fun _ _ hij ↦ (ripsGraph_adj p).2
    ⟨((ripsGraph_adj p).1 hij).1, ((ripsGraph_adj p).1 hij).2.trans h⟩

theorem isFlag_vietorisRips [DecidableEq ι] (r : ℝ) : (vietorisRips p r).IsFlag :=
  (ripsGraph p r).isFlag_cliqueComplex

/-- The Čech complex at scale `r`: nonempty sets of indices whose closed `r`-balls have a common
point. -/
def cech (r : ℝ) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ ∃ z : M, ∀ i ∈ s, dist (p i) z ≤ r}
  isRelLowerSet_faces := fun _ hs ↦
    ⟨hs.1, fun _ hts htne ↦ ⟨htne, hs.2.imp fun _ hz i hi ↦ hz i (hts hi)⟩⟩

theorem mem_cech {r : ℝ} {s : Finset ι} :
    s ∈ cech p r ↔ s.Nonempty ∧ ∃ z : M, ∀ i ∈ s, dist (p i) z ≤ r := Iff.rfl

theorem cech_mono {r r' : ℝ} (h : r ≤ r') : cech p r ≤ cech p r' :=
  fun _ hs ↦ ⟨hs.1, hs.2.imp fun _ hz i hi ↦ (hz i hi).trans h⟩

/-- `VR(r) ⊆ Čech(r)` for `r ≥ 0`: a set of points pairwise within `r` lies in the `r`-ball
around any one of them. (For `r < 0`, `VR(r)` still contains the vertices but `Čech(r)` is
empty.) -/
theorem vietorisRips_le_cech {r : ℝ} (hr : 0 ≤ r) : vietorisRips p r ≤ cech p r := by
  intro s hs
  obtain ⟨hne, h⟩ := (mem_vietorisRips p).1 hs
  obtain ⟨i₀, hi₀⟩ := hne
  refine ⟨⟨i₀, hi₀⟩, p i₀, fun i hi ↦ ?_⟩
  rcases eq_or_ne i i₀ with rfl | hne
  · rwa [dist_self]
  · exact h i hi i₀ hi₀ hne

/-- `Čech(r) ⊆ VR(2r)`, by the triangle inequality. -/
theorem cech_le_vietorisRips (r : ℝ) : cech p r ≤ vietorisRips p (2 * r) := by
  rintro s ⟨hne, z, hz⟩
  refine (mem_vietorisRips p).2 ⟨hne, fun i hi j hj _ ↦ ?_⟩
  calc dist (p i) (p j) ≤ dist (p i) z + dist z (p j) := dist_triangle _ _ _
    _ = dist (p i) z + dist (p j) z := by rw [dist_comm z]
    _ ≤ r + r := add_le_add (hz i hi) (hz j hj)
    _ = 2 * r := by ring

end PreAbstractSimplicialComplex
