/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Subdivision

/-!
# The nerve lemma

Let `K` be a simplicial complex covered by finitely many subcomplexes `U i` (`i : I`): every face
of `K` lies in some `U i`. The **nerve** of the cover (`coverNerve U`) is the complex on `I` whose
faces are the nonempty `J` such that the `U i`, `i ∈ J`, have a common face. The **nerve lemma**
says that if every nonempty intersection `⋂_{i ∈ J} U i` (`coverInter U J`) is acyclic, then `K`
and the nerve have isomorphic homology (`nerveLemma`).

In TDA this is the reason the Čech complex computes the homology of a union of balls, and it is
the basic tool for replacing a space by a combinatorial model.

## Proof

There is no simplicial map between `K` and the nerve in general: the natural assignment
`s ↦ {i | s ∈ U i}` reverses inclusions. It does preserve chains, though, so it gives maps
between barycentric subdivisions. We use acyclic carriers (`Homology/AcyclicCarrier.lean`)
between `sd K` and `sd N`:
* `toNerveCarrier`: a chain of faces `s₀ ⊂ ⋯ ⊂ sₖ` goes to the simplex on the chain of index
  sets `{i | sₖ ∈ U i} ⊆ ⋯ ⊆ {i | s₀ ∈ U i}`;
* `ofNerveCarrier`: a chain `J₀ ⊂ ⋯ ⊂ Jₖ` of nerve faces goes to `sd(⋂_{i ∈ J₀} U i)`, acyclic
  by hypothesis (and because subdivision preserves acyclicity);
* the composites are carried by `nerveCarrierK` (`S ↦ sd(⋂_{i : ⋃S ∈ U i} U i)`) and
  `nerveCarrierN` (the chains of nerve faces above the smallest element, a cone).
Combined with `H(sd K) ≅ H(K)` (`Homology/Subdivision.lean`) this proves the lemma.

The hypothesis is stated with the concrete acyclicity `IsAcyclicIn R M M`, which is equivalent
to vanishing reduced homology (`Homology/AcyclicSubcomplex.lean`). For example it holds when
every intersection is a cone (`isAcyclicIn_self_of_cone`).

## Main declarations

* `PreAbstractSimplicialComplex.coverInter`, `PreAbstractSimplicialComplex.coverNerve`,
  `PreAbstractSimplicialComplex.coverIndex`.
* `PreAbstractSimplicialComplex.nerveLemma`.

## References

* A. Björner, *Topological methods*, in Handbook of Combinatorics (1995), Theorem 10.6.
-/

@[expose] public section

open CategoryTheory Limits Finset

universe u

namespace PreAbstractSimplicialComplex

variable {ι I : Type u} [LinearOrder ι] [LinearOrder I] (U : I → PreAbstractSimplicialComplex ι)

/-- The intersection of the members `U i`, `i ∈ J`, of a family of complexes. -/
def coverInter (J : Finset I) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ ∀ i ∈ J, s ∈ U i}
  isRelLowerSet_faces := fun _ hs ↦ ⟨hs.1, fun _ hts ht ↦
    ⟨ht, fun i hi ↦ (U i).mem_of_subset (hs.2 i hi) hts ht⟩⟩

/-- The nerve of a family of complexes `U i`: a nonempty finite set `J` of indices is a face when
the `U i`, `i ∈ J`, have a common face. -/
def coverNerve : PreAbstractSimplicialComplex I where
  faces := {J | J.Nonempty ∧ ∃ s : Finset ι, s.Nonempty ∧ ∀ i ∈ J, s ∈ U i}
  isRelLowerSet_faces := fun _ hJ ↦ ⟨hJ.1, fun _ hJ' hne ↦
    ⟨hne, hJ.2.imp fun _ hs ↦ ⟨hs.1, fun i hi ↦ hs.2 i (hJ' hi)⟩⟩⟩

variable {U}

omit [LinearOrder ι] [LinearOrder I] in
theorem mem_coverInter {J : Finset I} {s : Finset ι} :
    s ∈ coverInter U J ↔ s.Nonempty ∧ ∀ i ∈ J, s ∈ U i := Iff.rfl

omit [LinearOrder ι] [LinearOrder I] in
theorem mem_coverNerve {J : Finset I} :
    J ∈ coverNerve U ↔ J.Nonempty ∧ ∃ s : Finset ι, s.Nonempty ∧ ∀ i ∈ J, s ∈ U i := Iff.rfl

omit [LinearOrder ι] [LinearOrder I] in
theorem coverInter_anti {J J' : Finset I} (h : J ⊆ J') : coverInter U J' ≤ coverInter U J :=
  fun _ hs ↦ ⟨hs.1, fun i hi ↦ hs.2 i (h hi)⟩

omit [LinearOrder ι] [LinearOrder I] in
theorem coverInter_le {K : PreAbstractSimplicialComplex ι} (hle : ∀ i, U i ≤ K) {J : Finset I}
    (hJ : J.Nonempty) : coverInter U J ≤ K := by
  obtain ⟨i, hi⟩ := hJ
  exact fun _ hs ↦ hle i (hs.2 i hi)

/-! ### Carriers that do not involve the index sets of faces -/

section Carriers

variable {K : PreAbstractSimplicialComplex ι} (hle : ∀ i, U i ≤ K) (R : Type u) [Ring R]
  (hacyc : ∀ J ∈ coverNerve U, IsAcyclicIn R (coverInter U J) (coverInter U J))

omit [LinearOrder I] in
include hle hacyc in
theorem isAcyclicIn_barycentricSubdivision_coverInter {J : Finset I} (hJ : J ∈ coverNerve U) :
    IsAcyclicIn R K.barycentricSubdivision (coverInter U J).barycentricSubdivision :=
  (isAcyclicIn_self_barycentricSubdivision _ R (hacyc J hJ)).of_le R
    (barycentricSubdivision_mono (coverInter_le hle hJ.1))

/-- The carrier from the subdivision of the nerve back to the subdivision of `K`: a chain
`J₀ ⊂ ⋯ ⊂ Jₖ` goes to the subdivision of the intersection `⋂_{i ∈ J₀} U i`. -/
noncomputable def ofNerveCarrier :
    AcyclicCarrier R (coverNerve U).barycentricSubdivision K.barycentricSubdivision where
  toFun D := if h : D.Nonempty then (coverInter U (ofColex (D.min' h))).barycentricSubdivision
    else ⊥
  mono' D D' hD hD' hDD' := by
    rw [dite_eq_left hD.1, dite_eq_left hD'.1]
    exact barycentricSubdivision_mono (coverInter_anti
      (ofColex_min'_subset hD' (hDD' (D.min'_mem hD.1))))
  isAcyclicIn' D hD := by
    rw [dite_eq_left hD.1]
    exact isAcyclicIn_barycentricSubdivision_coverInter hle R hacyc (hD.2.1 _ (D.min'_mem hD.1))

theorem ofNerveCarrier_apply {D : Finset (Colex (Finset I))} (hD : D.Nonempty) :
    (ofNerveCarrier hle R hacyc).toFun D =
      (coverInter U (ofColex (D.min' hD))).barycentricSubdivision :=
  dite_eq_left hD

variable (U) in
/-- The carrier on the subdivision of the nerve: a chain goes to the chains above its smallest
element. -/
noncomputable def nerveCarrierN :
    AcyclicCarrier R (coverNerve U).barycentricSubdivision (coverNerve U).barycentricSubdivision
    where
  toFun D := if h : D.Nonempty then (coverNerve U).barycentricSubdivisionAbove (ofColex (D.min' h))
    else ⊥
  mono' D D' hD hD' hDD' := by
    rw [dite_eq_left hD.1, dite_eq_left hD'.1]
    exact barycentricSubdivisionAbove_anti (ofColex_min'_subset hD' (hDD' (D.min'_mem hD.1)))
  isAcyclicIn' D hD := by
    rw [dite_eq_left hD.1]
    exact isAcyclicIn_barycentricSubdivisionAbove R (hD.2.1 _ (D.min'_mem hD.1))

omit [LinearOrder ι] in
theorem nerveCarrierN_apply {D : Finset (Colex (Finset I))} (hD : D.Nonempty) :
    (nerveCarrierN U R).toFun D =
      (coverNerve U).barycentricSubdivisionAbove (ofColex (D.min' hD)) :=
  dite_eq_left hD

omit [LinearOrder ι] in
theorem mem_nerveCarrierN {D : Finset (Colex (Finset I))}
    (hD : D ∈ (coverNerve U).barycentricSubdivision) : D ∈ (nerveCarrierN U R).toFun D := by
  rw [nerveCarrierN_apply R hD.1]
  exact ⟨hD, fun x hx ↦ ofColex_min'_subset hD hx⟩

end Carriers

/-! ### Index sets of faces -/

variable (U) [Fintype I]

open Classical in
/-- The indices of the members of the cover containing the face `s`. -/
noncomputable def coverIndex (s : Finset ι) : Finset I := univ.filter fun i ↦ s ∈ U i

variable {U}

omit [LinearOrder ι] [LinearOrder I] in
@[simp]
theorem mem_coverIndex {s : Finset ι} {i : I} : i ∈ coverIndex U s ↔ s ∈ U i := by
  simp [coverIndex]

omit [LinearOrder ι] [LinearOrder I] in
theorem coverIndex_anti {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t) :
    coverIndex U t ⊆ coverIndex U s := fun i hi ↦
  mem_coverIndex.2 ((U i).mem_of_subset (mem_coverIndex.1 hi) hst hs)

omit [LinearOrder ι] [LinearOrder I] in
theorem coverIndex_mem_coverNerve {K : PreAbstractSimplicialComplex ι}
    (hcov : ∀ s ∈ K, ∃ i, s ∈ U i) {s : Finset ι} (hs : s ∈ K) : coverIndex U s ∈ coverNerve U :=
  ⟨(hcov s hs).imp fun _ hi ↦ mem_coverIndex.2 hi, s, K.nonempty_of_mem hs,
    fun _ hi ↦ mem_coverIndex.1 hi⟩

omit [LinearOrder ι] [LinearOrder I] in
theorem mem_coverInter_coverIndex {s t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) :
    t ∈ coverInter U (coverIndex U s) :=
  ⟨ht, fun i hi ↦ (U i).mem_of_subset (mem_coverIndex.1 hi) hts ht⟩

section NerveLemma

variable {K : PreAbstractSimplicialComplex ι} (hle : ∀ i, U i ≤ K)
  (hcov : ∀ s ∈ K, ∃ i, s ∈ U i)

variable (U) in
/-- The face of the subdivided nerve assigned to a chain of faces of `K`: the chain of their
index sets. -/
noncomputable def nerveChain (S : Finset (Colex (Finset ι))) : Finset (Colex (Finset I)) :=
  S.image fun x ↦ toColex (coverIndex U (ofColex x))

omit [LinearOrder ι] in
include hcov in
theorem nerveChain_mem {S : Finset (Colex (Finset ι))} (hS : S ∈ K.barycentricSubdivision) :
    nerveChain U S ∈ (coverNerve U).barycentricSubdivision := by
  refine ⟨hS.1.image _, fun y hy ↦ ?_, fun y hy y' hy' ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact coverIndex_mem_coverNerve hcov (hS.2.1 x hx)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hy'
    simp only [ofColex_toColex]
    rcases hS.2.2 x hx x' hx' with h | h
    · exact Or.inr (coverIndex_anti (K.nonempty_of_mem (hS.2.1 x hx)) h)
    · exact Or.inl (coverIndex_anti (K.nonempty_of_mem (hS.2.1 x' hx')) h)

variable (R : Type u) [Ring R]
  (hacyc : ∀ J ∈ coverNerve U, IsAcyclicIn R (coverInter U J) (coverInter U J))

/-- The carrier from the subdivision of `K` to the subdivision of the nerve: a chain of faces
goes to the simplex on the chain of their index sets. -/
noncomputable def toNerveCarrier :
    AcyclicCarrier R K.barycentricSubdivision (coverNerve U).barycentricSubdivision where
  toFun S := simplex (nerveChain U S)
  mono' _ _ _ _ hST := simplex_mono (Finset.image_subset_image hST)
  isAcyclicIn' _ hS := isAcyclicIn_simplex R (nerveChain_mem hcov hS)

/-- The carrier `S ↦ sd(⋂_{i : ⋃S ∈ U i} U i)` on the subdivision of `K`. -/
noncomputable def nerveCarrierK : AcyclicCarrier R K.barycentricSubdivision K.barycentricSubdivision
    where
  toFun S := (coverInter U (coverIndex U (S.sup ofColex))).barycentricSubdivision
  mono' _ _ hS _ hST := barycentricSubdivision_mono (coverInter_anti
    (coverIndex_anti (K.nonempty_of_mem (sup_mem hS)) (Finset.sup_mono hST)))
  isAcyclicIn' _ hS := isAcyclicIn_barycentricSubdivision_coverInter hle R hacyc
    (coverIndex_mem_coverNerve hcov (sup_mem hS))

omit [LinearOrder I] in
theorem mem_nerveCarrierK {S : Finset (Colex (Finset ι))} (hS : S ∈ K.barycentricSubdivision) :
    S ∈ (nerveCarrierK hle hcov R hacyc).toFun S :=
  ⟨hS.1, fun x hx ↦ mem_coverInter_coverIndex (K.nonempty_of_mem (hS.2.1 x hx)) (subset_sup hx),
    hS.2.2⟩

theorem ofNerveCarrier_le_nerveCarrierK {S : Finset (Colex (Finset ι))}
    (hS : S ∈ K.barycentricSubdivision) {D : Finset (Colex (Finset I))}
    (hDS : D ∈ (toNerveCarrier hcov R).toFun S) :
    (ofNerveCarrier hle R hacyc).toFun D ≤ (nerveCarrierK hle hcov R hacyc).toFun S := by
  obtain ⟨hDne, hDsub⟩ := mem_simplex.1 hDS
  rw [ofNerveCarrier_apply hle R hacyc hDne]
  obtain ⟨x, hx, hxD⟩ := Finset.mem_image.1 (hDsub (D.min'_mem hDne))
  rw [← hxD, ofColex_toColex]
  exact barycentricSubdivision_mono (coverInter_anti
    (coverIndex_anti (K.nonempty_of_mem (hS.2.1 x hx)) (subset_sup hx)))

theorem toNerveCarrier_le_nerveCarrierN {D : Finset (Colex (Finset I))}
    (hD : D ∈ (coverNerve U).barycentricSubdivision) {S : Finset (Colex (Finset ι))}
    (hS : S ∈ K.barycentricSubdivision) (hSD : S ∈ (ofNerveCarrier hle R hacyc).toFun D) :
    (toNerveCarrier hcov R).toFun S ≤ (nerveCarrierN U R).toFun D := by
  rw [ofNerveCarrier_apply hle R hacyc hD.1] at hSD
  rw [nerveCarrierN_apply R hD.1]
  intro T hT
  obtain ⟨hTne, hTsub⟩ := mem_simplex.1 hT
  refine ⟨(coverNerve U).barycentricSubdivision.mem_of_subset (nerveChain_mem hcov hS) hTsub hTne,
    fun y hy ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hTsub hy)
  rw [ofColex_toColex]
  exact fun i hi ↦ mem_coverIndex.2 ((hSD.2.1 x hx).2 i hi)

/-- **The nerve lemma.** Let `U i` be a finite family of subcomplexes covering `K` (every face of
`K` lies in some `U i`). If every nonempty intersection `⋂_{i ∈ J} U i` is acyclic, then `K` and
the nerve of the cover have isomorphic homology. -/
noncomputable def nerveLemma (n : ℕ) :
    K.homology (ModuleCat.of R R) n ≅ (coverNerve U).homology (ModuleCat.of R R) n :=
  K.homologyIsoBarycentricSubdivision R n ≪≫
    AcyclicCarrier.homologyIso (toNerveCarrier hcov R) (ofNerveCarrier hle R hacyc)
      (nerveCarrierK hle hcov R hacyc) (nerveCarrierN U R)
      (fun _ hS ↦ mem_nerveCarrierK hle hcov R hacyc hS) (fun _ hD ↦ mem_nerveCarrierN R hD)
      (fun _ hS _ _ hDS ↦ ofNerveCarrier_le_nerveCarrierK hle hcov R hacyc hS hDS)
      (fun _ hD _ hS hSD ↦ toNerveCarrier_le_nerveCarrierN hle hcov R hacyc hD hS hSD) n ≪≫
    ((coverNerve U).homologyIsoBarycentricSubdivision R n).symm

end NerveLemma

end PreAbstractSimplicialComplex
