/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Simplex
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The clique complex of a graph

The *clique complex* (or *flag complex*) of a simple graph `G` has as faces the nonempty finite
cliques of `G`: sets of vertices that are pairwise adjacent. It is the largest complex with `G`
as its 1-skeleton. Vietoris–Rips complexes in topological data analysis are clique complexes of
distance-threshold graphs.

Conversely, every complex `K` has a 1-skeleton graph `K.graph`, where `a` and `b` are adjacent
when `{a, b}` is an edge. A complex is *flag* when every set of vertices that are pairwise joined
by edges is a face, i.e. when it is determined by its 1-skeleton.

## Main declarations

* `SimpleGraph.cliqueComplex G` and `SimpleGraph.mem_cliqueComplex`.
* `SimpleGraph.cliqueComplex_mono`: more edges give more faces.
* `SimpleGraph.cliqueComplex_top`: the clique complex of the complete graph is the full simplex.
* `PreAbstractSimplicialComplex.graph K`: the 1-skeleton graph, with `graph_cliqueComplex`.
* `PreAbstractSimplicialComplex.IsFlag` and `SimpleGraph.isFlag_cliqueComplex`.
-/

@[expose] public section

open Finset

variable {V : Type*}

namespace SimpleGraph

variable {G H : SimpleGraph V} {s : Finset V}

/-- The clique complex of `G`: its faces are the nonempty finite cliques of `G`. -/
def cliqueComplex (G : SimpleGraph V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ G.IsClique (s : Set V)}
  isRelLowerSet_faces := fun _ hs ↦ ⟨hs.1, fun _ hts ht ↦ ⟨ht, hs.2.subset (coe_subset.2 hts)⟩⟩

@[simp]
theorem mem_cliqueComplex : s ∈ G.cliqueComplex ↔ s.Nonempty ∧ G.IsClique (s : Set V) := Iff.rfl

instance decidableMemCliqueComplex [DecidableEq V] [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.cliqueComplex) :=
  fun _ ↦ decidable_of_iff _ mem_cliqueComplex.symm

/-- Every vertex of the graph is a vertex of its clique complex. -/
@[simp]
theorem vertices_cliqueComplex (G : SimpleGraph V) : G.cliqueComplex.vertices = Set.univ := by
  ext v
  simp

/-- An edge `{a, b}` with `a ≠ b` is a face of the clique complex iff `a` and `b` are adjacent. -/
theorem pair_mem_cliqueComplex [DecidableEq V] {a b : V} (hab : a ≠ b) :
    {a, b} ∈ G.cliqueComplex ↔ G.Adj a b := by
  simp [hab]

theorem cliqueComplex_mono (h : G ≤ H) : G.cliqueComplex ≤ H.cliqueComplex :=
  fun _ hs ↦ ⟨hs.1, hs.2.mono h⟩

/-- The clique complex of the complete graph is the full simplex on all vertices. -/
@[simp]
theorem cliqueComplex_top : (⊤ : SimpleGraph V).cliqueComplex = ⊤ := by
  ext s
  simp only [PreAbstractSimplicialComplex.mem_faces, mem_cliqueComplex,
    PreAbstractSimplicialComplex.mem_top, and_iff_left_iff_imp]
  exact fun _ _ _ _ _ h ↦ h

/-- The clique complex of the empty graph has only the vertices as faces. -/
theorem mem_cliqueComplex_bot : s ∈ (⊥ : SimpleGraph V).cliqueComplex ↔ ∃ v, s = {v} := by
  simp only [mem_cliqueComplex, isClique_bot_iff]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    exact ⟨v, eq_singleton_iff_unique_mem.2 ⟨hv, fun w hw ↦ h hw hv⟩⟩
  · rintro ⟨v, rfl⟩
    simp

end SimpleGraph

namespace PreAbstractSimplicialComplex

variable [DecidableEq V] (K : PreAbstractSimplicialComplex V)

/-- The 1-skeleton graph of `K`: distinct `a` and `b` are adjacent when `{a, b}` is a face. -/
def graph : SimpleGraph V := SimpleGraph.fromRel fun a b ↦ {a, b} ∈ K

@[simp]
theorem graph_adj {a b : V} : K.graph.Adj a b ↔ a ≠ b ∧ {a, b} ∈ K := by
  simp [graph, pair_comm b a]

/-- The 1-skeleton graph of the clique complex of `G` is `G` again. -/
@[simp]
theorem _root_.SimpleGraph.graph_cliqueComplex (G : SimpleGraph V) : G.cliqueComplex.graph = G := by
  ext a b
  simp only [graph_adj]
  constructor
  · rintro ⟨hab, h⟩
    exact (SimpleGraph.pair_mem_cliqueComplex hab).1 h
  · intro h
    exact ⟨h.ne, (SimpleGraph.pair_mem_cliqueComplex h.ne).2 h⟩

/-- `K` is *flag* if every nonempty finset of vertices that are pairwise joined by edges of `K`
is a face of `K`. -/
def IsFlag : Prop :=
  ∀ s : Finset V, s.Nonempty → (∀ v ∈ s, v ∈ K.vertices) → K.graph.IsClique (s : Set V) → s ∈ K

/-- Clique complexes are flag. -/
theorem _root_.SimpleGraph.isFlag_cliqueComplex (G : SimpleGraph V) : G.cliqueComplex.IsFlag :=
  fun s hs _ hcl ↦ ⟨hs, by rwa [G.graph_cliqueComplex] at hcl⟩

/-- Every face of `K` is a clique in its 1-skeleton, so `K` lies inside the clique complex of its
1-skeleton. -/
theorem le_cliqueComplex_graph : K ≤ K.graph.cliqueComplex := by
  intro s hs
  refine ⟨K.nonempty_of_mem hs, fun a ha b hb hab ↦ (graph_adj K).2 ⟨hab, ?_⟩⟩
  exact K.mem_of_subset hs (insert_subset_iff.2 ⟨ha, singleton_subset_iff.2 hb⟩)
    (insert_nonempty _ _)

/-- A flag complex whose vertex set is all of `V` is the clique complex of its 1-skeleton. -/
theorem IsFlag.eq_cliqueComplex (hK : K.IsFlag) (hV : K.vertices = Set.univ) :
    K = K.graph.cliqueComplex :=
  le_antisymm K.le_cliqueComplex_graph fun s hs ↦ hK s hs.1 (by simp [hV]) hs.2

end PreAbstractSimplicialComplex

/-! ### Sanity checks -/

example : (⊤ : SimpleGraph (Fin 3)).cliqueComplex.fVector 2 = 1 := by decide
