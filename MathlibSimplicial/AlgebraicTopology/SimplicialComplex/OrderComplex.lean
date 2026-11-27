/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Clique
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.SimplicialMap
public import Mathlib.Order.Preorder.Chain

/-!
# The order complex of a poset

The *order complex* of an ordered type `α` has as faces the nonempty finite chains of `α`. It
turns order theory into topology: for example, Möbius functions of posets are reduced Euler
characteristics of order complexes, and Quillen's fiber lemma compares posets through them.

The order complex is the clique complex of the *comparability graph*, in which distinct `a` and
`b` are adjacent when `a ≤ b` or `b ≤ a`. A monotone map sends chains to chains, so it induces a
simplicial map between order complexes.

Applied to the *face poset* of a complex `K` (its faces ordered by inclusion), the order complex
gives the *barycentric subdivision* of `K`: the vertices are the faces of `K`, and the simplices
are chains `σ₀ ⊂ σ₁ ⊂ ⋯ ⊂ σₖ`.

For a partial order, the order complex should correspond to the nondegenerate simplices of the
nerve `nerve α` (Mathlib's `NerveNondegenerate.lean`, and PR #45531 when it lands). That
comparison belongs with the bridge to simplicial sets (roadmap step 3).

## Main declarations

* `SimpleGraph.comparability α`, with `SimpleGraph.isClique_comparability_iff`.
* `orderComplex α` and `mem_orderComplex`.
* `orderComplex_eq_cliqueComplex`: the order complex is the clique complex of the comparability
  graph, so in particular it is flag.
* `PreAbstractSimplicialComplex.SimplicialMap.ofMonotone`: functoriality in monotone maps.
* `PreAbstractSimplicialComplex.facePoset K` and `PreAbstractSimplicialComplex.subdivision K`.
-/

@[expose] public section

open Finset

variable {α β : Type*}

/-! ### The comparability graph -/

namespace SimpleGraph

variable (α) in
/-- The comparability graph of an ordered type: distinct `a` and `b` are adjacent when they are
comparable. -/
def comparability [LE α] : SimpleGraph α := fromRel (· ≤ ·)

@[simp]
theorem comparability_adj [LE α] {a b : α} :
    (comparability α).Adj a b ↔ a ≠ b ∧ (a ≤ b ∨ b ≤ a) := fromRel_adj ..

/-- Cliques of the comparability graph are exactly chains. -/
theorem isClique_comparability_iff [LE α] {s : Set α} :
    (comparability α).IsClique s ↔ IsChain (· ≤ ·) s := by
  constructor
  · intro h x hx y hy hxy
    exact (comparability_adj.1 (h hx hy hxy)).2
  · intro h x hx y hy hxy
    exact comparability_adj.2 ⟨hxy, h hx hy hxy⟩

end SimpleGraph

/-! ### The order complex -/

variable (α) in
/-- The order complex of `α`: its faces are the nonempty finite chains. -/
def orderComplex [LE α] : PreAbstractSimplicialComplex α where
  faces := {s | s.Nonempty ∧ IsChain (· ≤ ·) (s : Set α)}
  isRelLowerSet_faces := fun _ hs ↦ ⟨hs.1, fun _ hts ht ↦ ⟨ht, hs.2.mono (coe_subset.2 hts)⟩⟩

section LE

variable [LE α] {s : Finset α}

@[simp]
theorem mem_orderComplex : s ∈ orderComplex α ↔ s.Nonempty ∧ IsChain (· ≤ ·) (s : Set α) :=
  Iff.rfl

/-- The order complex is the clique complex of the comparability graph. -/
theorem orderComplex_eq_cliqueComplex :
    orderComplex α = (SimpleGraph.comparability α).cliqueComplex := by
  ext s
  simp [PreAbstractSimplicialComplex.mem_faces, SimpleGraph.isClique_comparability_iff]

/-- Every element of `α` is a vertex of the order complex. -/
@[simp]
theorem vertices_orderComplex : (orderComplex α).vertices = Set.univ := by
  rw [orderComplex_eq_cliqueComplex, SimpleGraph.vertices_cliqueComplex]

/-- In a linear order every finset is a chain, so the order complex is the full simplex. -/
theorem orderComplex_of_linearOrder {γ : Type*} [LinearOrder γ] :
    orderComplex γ = ⊤ := by
  ext s
  simp only [PreAbstractSimplicialComplex.mem_faces, mem_orderComplex,
    PreAbstractSimplicialComplex.mem_top, and_iff_left_iff_imp]
  exact fun _ x _ y _ _ ↦ le_total x y

end LE

instance decidableMemOrderComplex [DecidableEq α] [LE α] [DecidableLE α] :
    DecidablePred (· ∈ orderComplex α) :=
  fun s ↦ decidable_of_iff (s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ≤ b ∨ b ≤ a) Iff.rfl

namespace PreAbstractSimplicialComplex.SimplicialMap

/-- A monotone map induces a simplicial map between order complexes. -/
def ofMonotone [Preorder α] [Preorder β] (f : α →o β) : orderComplex α →ˢ orderComplex β where
  toFun := f
  map_mem' s hs := by
    classical
    refine ⟨s.image f, ⟨hs.1.image f, ?_⟩, coe_image⟩
    rw [coe_image]
    exact hs.2.image_of_map_rel _ _ f fun _ _ h ↦ f.monotone h

@[simp]
theorem coe_ofMonotone [Preorder α] [Preorder β] (f : α →o β) : ⇑(ofMonotone f) = f := rfl

theorem ofMonotone_comp {γ : Type*} [Preorder α] [Preorder β] [Preorder γ] (g : β →o γ)
    (f : α →o β) : ofMonotone (g.comp f) = (ofMonotone g).comp (ofMonotone f) := rfl

end PreAbstractSimplicialComplex.SimplicialMap

/-! ### Face posets and barycentric subdivision -/

namespace PreAbstractSimplicialComplex

variable (K : PreAbstractSimplicialComplex α)

/-- The face poset of `K`: its faces, ordered by inclusion. -/
abbrev facePoset : Type _ := {s : Finset α // s ∈ K}

/-- The barycentric subdivision of `K`: the order complex of its face poset. Its vertices are the
faces of `K` and its simplices are the chains `σ₀ ⊂ σ₁ ⊂ ⋯ ⊂ σₖ` of faces. -/
abbrev subdivision : PreAbstractSimplicialComplex K.facePoset := orderComplex K.facePoset

/-- A subcomplex inclusion induces a simplicial map of barycentric subdivisions. -/
def SimplicialMap.subdivisionOfLE {K L : PreAbstractSimplicialComplex α} (h : K ≤ L) :
    K.subdivision →ˢ L.subdivision :=
  ofMonotone ⟨fun s ↦ ⟨s.1, h s.2⟩, fun _ _ hst ↦ hst⟩

end PreAbstractSimplicialComplex

/-! ### Sanity checks

The order complex of the four-element poset `Fin 2 × Fin 2` (a square, with `(0,0)` below and
`(1,1)` above two incomparable elements) has 5 edges: the four sides of the square and its
diagonal `(0,0) ≤ (1,1)`, and 2 triangles. -/

example : (orderComplex (Fin 2 × Fin 2)).fVector 1 = 5 := by decide
example : (orderComplex (Fin 2 × Fin 2)).fVector 2 = 2 := by decide
