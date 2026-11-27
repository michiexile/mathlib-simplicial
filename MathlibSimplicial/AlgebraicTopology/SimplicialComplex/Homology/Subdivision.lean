/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.AcyclicSubcomplex
public import Mathlib.Combinatorics.Colex

/-!
# Barycentric subdivision

The barycentric subdivision `sd K` of `K` has the faces of `K` as vertices and the chains of
faces `σ₀ ⊂ ⋯ ⊂ σₖ` as faces. It is the order complex of the face poset
(`PreAbstractSimplicialComplex.subdivision` in `OrderComplex.lean`), but homology needs a linear
order on the vertices, and the face poset is only partially ordered. So here the vertex type is
`Colex (Finset ι)`: finsets of `ι` in colexicographic order, a linear order that extends
inclusion (`Finset.Colex.toColex_le_toColex_of_subset`). In a chain of faces the colex-largest
face contains all the others (`ofColex_subset_max'`), and the colex-smallest is contained in all
of them (`ofColex_min'_subset`).

**Subdivision does not change homology** (`homologyIsoBarycentricSubdivision`). The proof uses
acyclic carriers in both directions: a face `s` goes to `sd(Δs)` (a cone with apex `s`), and a
chain `S` goes back to the simplex on its largest face `⋃ S`.

## Main declarations

* `PreAbstractSimplicialComplex.barycentricSubdivision`,
  `PreAbstractSimplicialComplex.barycentricSubdivisionAbove` (chains of faces above a face).
* `PreAbstractSimplicialComplex.homologyIsoBarycentricSubdivision`.
* `PreAbstractSimplicialComplex.isAcyclicIn_self_barycentricSubdivision`.
-/

@[expose] public section

open CategoryTheory Limits Finset

universe u

namespace PreAbstractSimplicialComplex

variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι)

/-- The barycentric subdivision of `K`: its vertices are the faces of `K`, and its faces are the
nonempty chains of faces `σ₀ ⊂ σ₁ ⊂ ⋯ ⊂ σₖ`. The vertex type is `Colex (Finset ι)`, finsets
of `ι` in colexicographic order, which is a linear order extending inclusion. -/
def barycentricSubdivision : PreAbstractSimplicialComplex (Colex (Finset ι)) where
  faces := {S | S.Nonempty ∧ (∀ x ∈ S, ofColex x ∈ K) ∧
    ∀ x ∈ S, ∀ y ∈ S, ofColex x ⊆ ofColex y ∨ ofColex y ⊆ ofColex x}
  isRelLowerSet_faces := fun _ hS ↦ ⟨hS.1, fun _ hTS hT ↦
    ⟨hT, fun x hx ↦ hS.2.1 x (hTS hx), fun x hx y hy ↦ hS.2.2 x (hTS hx) y (hTS hy)⟩⟩

variable {K}

omit [LinearOrder ι] in
theorem mem_barycentricSubdivision {S : Finset (Colex (Finset ι))} :
    S ∈ K.barycentricSubdivision ↔ S.Nonempty ∧ (∀ x ∈ S, ofColex x ∈ K) ∧
      ∀ x ∈ S, ∀ y ∈ S, ofColex x ⊆ ofColex y ∨ ofColex y ⊆ ofColex x :=
  Iff.rfl

omit [LinearOrder ι] in
theorem barycentricSubdivision_mono {L : PreAbstractSimplicialComplex ι} (h : K ≤ L) :
    K.barycentricSubdivision ≤ L.barycentricSubdivision :=
  fun _ hS ↦ ⟨hS.1, fun x hx ↦ h (hS.2.1 x hx), hS.2.2⟩

/-- In a chain of faces, every face lies in the colexicographically largest one. -/
theorem ofColex_subset_max' {S : Finset (Colex (Finset ι))} (hS : S ∈ K.barycentricSubdivision)
    {x : Colex (Finset ι)} (hx : x ∈ S) : ofColex x ⊆ ofColex (S.max' hS.1) := by
  rcases hS.2.2 x hx _ (S.max'_mem hS.1) with h | h
  · exact h
  · have hle : S.max' hS.1 ≤ x := Finset.Colex.toColex_le_toColex_of_subset h
    rw [le_antisymm hle (S.le_max' x hx)]

/-- In a chain of faces, the colexicographically smallest face lies in every face. -/
theorem ofColex_min'_subset {S : Finset (Colex (Finset ι))} (hS : S ∈ K.barycentricSubdivision)
    {x : Colex (Finset ι)} (hx : x ∈ S) : ofColex (S.min' hS.1) ⊆ ofColex x := by
  rcases hS.2.2 x hx _ (S.min'_mem hS.1) with h | h
  · have hle : x ≤ S.min' hS.1 := Finset.Colex.toColex_le_toColex_of_subset h
    rw [le_antisymm (S.min'_le x hx) hle]
  · exact h

/-- The union of a chain of faces is its largest face. -/
theorem sup_eq_max' {S : Finset (Colex (Finset ι))} (hS : S ∈ K.barycentricSubdivision) :
    S.sup ofColex = ofColex (S.max' hS.1) :=
  le_antisymm (Finset.sup_le fun _ hx ↦ ofColex_subset_max' hS hx)
    (Finset.le_sup (f := ofColex) (S.max'_mem hS.1))

theorem sup_mem {S : Finset (Colex (Finset ι))} (hS : S ∈ K.barycentricSubdivision) :
    S.sup ofColex ∈ K := by
  rw [sup_eq_max' hS]
  exact hS.2.1 _ (S.max'_mem hS.1)

theorem subset_sup {S : Finset (Colex (Finset ι))} {x : Colex (Finset ι)} (hx : x ∈ S) :
    ofColex x ⊆ S.sup ofColex :=
  Finset.le_sup (f := ofColex) hx

/-- `Finset.mem_insert` for an arbitrary `DecidableEq` instance, found by unification rather
than by instance search. On `Colex (Finset ι)` the instance coming from the linear order and the
one found by instance search are not reducibly equal. -/
theorem _root_.Finset.mem_insert_of_decidableEq {α : Type*} {inst : DecidableEq α} {a x : α}
    {S : Finset α} : x ∈ @insert _ _ (@Finset.instInsert _ inst) a S ↔ x = a ∨ x ∈ S :=
  @Finset.mem_insert _ inst _ _ _

omit [LinearOrder ι] in
/-- Inserting a face comparable with every face of a chain gives a chain. (Stated for any
`DecidableEq` instance, see `Finset.mem_insert_of_decidableEq`.) -/
theorem insert_mem_barycentricSubdivision {inst : DecidableEq (Colex (Finset ι))}
    {L : PreAbstractSimplicialComplex ι}
    {S : Finset (Colex (Finset ι))} (hS : S ∈ L.barycentricSubdivision) {s : Finset ι}
    (hs : s ∈ L) (hcomp : ∀ x ∈ S, ofColex x ⊆ s ∨ s ⊆ ofColex x) :
    @insert _ _ (@Finset.instInsert _ inst) (toColex s) S ∈ L.barycentricSubdivision := by
  refine ⟨⟨toColex s, Finset.mem_insert_of_decidableEq.2 (Or.inl rfl)⟩, fun x hx ↦ ?_,
    fun x hx y hy ↦ ?_⟩
  · rcases Finset.mem_insert_of_decidableEq.1 hx with h | h
    · rw [h]; exact hs
    · exact hS.2.1 x h
  · rcases Finset.mem_insert_of_decidableEq.1 hx with h | h <;>
      rcases Finset.mem_insert_of_decidableEq.1 hy with h' | h'
    · rw [h, h']; exact Or.inl subset_rfl
    · rw [h]; exact (hcomp y h').symm
    · rw [h']; exact hcomp x h
    · exact hS.2.2 x h y h'

omit [LinearOrder ι] in
theorem singleton_mem_barycentricSubdivision {s : Finset ι} (hs : s ∈ K) :
    {toColex s} ∈ K.barycentricSubdivision :=
  ⟨singleton_nonempty _, fun x hx ↦ by rw [mem_singleton.1 hx]; exact hs,
    fun x hx y hy ↦ by rw [mem_singleton.1 hx, mem_singleton.1 hy]; exact Or.inl subset_rfl⟩

/-- The barycentric subdivision of a simplex is a cone with apex the top face. -/
theorem isAcyclicIn_self_barycentricSubdivision_simplex (R : Type u) [Ring R] {s : Finset ι}
    (hs : s.Nonempty) :
    IsAcyclicIn R (simplex s).barycentricSubdivision (simplex s).barycentricSubdivision :=
  isAcyclicIn_self_of_cone R (singleton_mem_barycentricSubdivision (self_mem_simplex hs))
    fun _ hS ↦ insert_mem_barycentricSubdivision hS (self_mem_simplex hs)
      fun x hx ↦ Or.inl (mem_simplex.1 (hS.2.1 x hx)).2

variable (K) in
/-- The chains of faces of `K` that contain `s`: the subcomplex of the barycentric subdivision
spanned by the faces above `s`. -/
def barycentricSubdivisionAbove (s : Finset ι) : PreAbstractSimplicialComplex (Colex (Finset ι))
    where
  faces := {S | S ∈ K.barycentricSubdivision ∧ ∀ x ∈ S, s ⊆ ofColex x}
  isRelLowerSet_faces := fun _ hS ↦ ⟨hS.1.1, fun _ hTS hT ↦
    ⟨K.barycentricSubdivision.mem_of_subset hS.1 hTS hT, fun x hx ↦ hS.2 x (hTS hx)⟩⟩

omit [LinearOrder ι] in
theorem barycentricSubdivisionAbove_le (s : Finset ι) :
    K.barycentricSubdivisionAbove s ≤ K.barycentricSubdivision := fun _ hS ↦ hS.1

omit [LinearOrder ι] in
theorem barycentricSubdivisionAbove_anti {s t : Finset ι} (h : s ⊆ t) :
    K.barycentricSubdivisionAbove t ≤ K.barycentricSubdivisionAbove s :=
  fun _ hS ↦ ⟨hS.1, fun x hx ↦ h.trans (hS.2 x hx)⟩

/-- The chains of faces above a face `s` form a cone with apex `s`, so they are acyclic. -/
theorem isAcyclicIn_barycentricSubdivisionAbove (R : Type u) [Ring R] {s : Finset ι}
    (hs : s ∈ K) :
    IsAcyclicIn R K.barycentricSubdivision (K.barycentricSubdivisionAbove s) :=
  (isAcyclicIn_self_of_cone R (M := K.barycentricSubdivisionAbove s) (v := toColex s)
    ⟨singleton_mem_barycentricSubdivision hs, fun x hx ↦ by rw [mem_singleton.1 hx]; rfl⟩
    fun _ hS ↦ ⟨insert_mem_barycentricSubdivision hS.1 hs fun x hx ↦ Or.inr (hS.2 x hx),
      fun x hx ↦ (Finset.mem_insert_of_decidableEq.1 hx).elim (fun h ↦ by rw [h]; rfl)
        (hS.2 x)⟩).of_le R (barycentricSubdivisionAbove_le s)

variable (R : Type u) [Ring R] (K)

/-- The carrier `s ↦ sd(Δs)` from `K` to its barycentric subdivision. -/
def toSubdivisionCarrier : AcyclicCarrier R K K.barycentricSubdivision where
  toFun s := (simplex s).barycentricSubdivision
  mono' _ _ _ _ hst := barycentricSubdivision_mono (simplex_mono hst)
  isAcyclicIn' _ hs :=
    (isAcyclicIn_self_barycentricSubdivision_simplex R (K.nonempty_of_mem hs)).of_le R
      (barycentricSubdivision_mono ((simplex_le_iff (K.nonempty_of_mem hs)).2 hs))

/-- The carrier `S ↦ Δ(⋃ S)` from the barycentric subdivision of `K` back to `K`. -/
def ofSubdivisionCarrier : AcyclicCarrier R K.barycentricSubdivision K where
  toFun S := simplex (S.sup ofColex)
  mono' _ _ _ _ hST := simplex_mono (Finset.sup_mono hST)
  isAcyclicIn' _ hS := isAcyclicIn_simplex R (sup_mem hS)

/-- The carrier `s ↦ Δs` on `K`. -/
def simplexCarrier : AcyclicCarrier R K K where
  toFun s := simplex s
  mono' _ _ _ _ hst := simplex_mono hst
  isAcyclicIn' _ hs := isAcyclicIn_simplex R hs

/-- The carrier `S ↦ sd(Δ(⋃ S))` on the barycentric subdivision of `K`. -/
def subdivisionSimplexCarrier : AcyclicCarrier R K.barycentricSubdivision K.barycentricSubdivision
    where
  toFun S := (simplex (S.sup ofColex)).barycentricSubdivision
  mono' _ _ _ _ hST := barycentricSubdivision_mono (simplex_mono (Finset.sup_mono hST))
  isAcyclicIn' _ hS :=
    (isAcyclicIn_self_barycentricSubdivision_simplex R (K.nonempty_of_mem (sup_mem hS))).of_le R
      (barycentricSubdivision_mono ((simplex_le_iff (K.nonempty_of_mem (sup_mem hS))).2
        (sup_mem hS)))

/-- **Barycentric subdivision does not change homology.** -/
noncomputable def homologyIsoBarycentricSubdivision (n : ℕ) :
    K.homology (ModuleCat.of R R) n ≅ K.barycentricSubdivision.homology (ModuleCat.of R R) n :=
  AcyclicCarrier.homologyIso (toSubdivisionCarrier K R) (ofSubdivisionCarrier K R)
    (simplexCarrier K R) (subdivisionSimplexCarrier K R)
    (fun _ hs ↦ self_mem_simplex (K.nonempty_of_mem hs))
    (fun _ hS ↦ ⟨hS.1, fun x hx ↦ mem_simplex.2 ⟨K.nonempty_of_mem (hS.2.1 x hx), subset_sup hx⟩,
      hS.2.2⟩)
    (fun _ _ _ _ hT ↦ simplex_mono (Finset.sup_le fun x hx ↦ (mem_simplex.1 (hT.2.1 x hx)).2))
    (fun _ _ _ _ ht ↦ barycentricSubdivision_mono (simplex_mono (mem_simplex.1 ht).2)) n

variable {K} in
/-- The isomorphism `H(K) ≅ H(sd K)` is natural for inclusions. -/
theorem homologyIsoBarycentricSubdivision_naturality {K' : PreAbstractSimplicialComplex ι}
    (h : K ≤ K') (n : ℕ) :
    (K.homologyIsoBarycentricSubdivision R n).hom ≫
        PreAbstractSimplicialComplex.homologyMap (ModuleCat.of R R)
          (barycentricSubdivision_mono h) n =
      PreAbstractSimplicialComplex.homologyMap (ModuleCat.of R R) h n ≫
        (K'.homologyIsoBarycentricSubdivision R n).hom :=
  AcyclicCarrier.homologyIso_naturality R h (barycentricSubdivision_mono h)
    ((toSubdivisionCarrier K' R).restrict R h) (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) n

/-- The barycentric subdivision of an acyclic complex is acyclic. -/
theorem isAcyclicIn_self_barycentricSubdivision (hK : IsAcyclicIn R K K) :
    IsAcyclicIn R K.barycentricSubdivision K.barycentricSubdivision :=
  isAcyclicIn_self_of_carriers R (toSubdivisionCarrier K R) (ofSubdivisionCarrier K R)
    (subdivisionSimplexCarrier K R)
    (fun _ hS ↦ ⟨hS.1, fun x hx ↦ mem_simplex.2 ⟨K.nonempty_of_mem (hS.2.1 x hx), subset_sup hx⟩,
      hS.2.2⟩)
    (fun _ _ _ _ ht ↦ barycentricSubdivision_mono (simplex_mono (mem_simplex.1 ht).2)) hK

end PreAbstractSimplicialComplex
