/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.AcyclicCarrier
public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Acyclic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Acyclic subcomplexes

This file supplies the acyclic subcomplexes that the acyclic carrier theorem
(`Homology/AcyclicCarrier.lean`) needs, and relates the concrete notion `IsAcyclicIn` to
homology.

* For `M ≤ L`, the oriented chains of `M` include into those of `L` (`inclChains`), with image
  the chains supported on `M`. So `M` is acyclic inside `L` as soon as it is acyclic in itself
  (`IsAcyclicIn.of_le`), and `IsAcyclicIn R M M` is equivalent to the vanishing of reduced
  homology (`exists_boundary_of_isZero_homology`, `isZero_homology_of_exists_boundary`).
* Degree `0` is handled directly: in a complex where every vertex is joined to `v`, a `0`-chain
  with augmentation `0` is a boundary (`exists_boundary_zero_of_cone`), using the boundary of an
  edge (`orientedBoundary_single_pair`).
* Full simplices are acyclic (`isAcyclicIn_simplex`), from the homology computation of
  `Homology/Acyclic.lean`.
* **Cones with an arbitrary apex are acyclic** (`isAcyclicIn_self_of_cone`,
  `isZero_homology_succ_of_cone'`). The earlier result `isZero_homology_succ_of_cone` needed the
  apex to be the smallest vertex, because it builds an extra degeneracy of the ordered simplicial
  set. Here the acyclic carrier `s ↦ Δ(s ∪ {v})` carries both the identity and the map collapsing
  everything to the apex, so the two are chain homotopic.

## Main declarations

* `PreAbstractSimplicialComplex.inclChains`, `PreAbstractSimplicialComplex.IsAcyclicIn.of_le`.
* `PreAbstractSimplicialComplex.exists_boundary_of_isZero_homology`,
  `PreAbstractSimplicialComplex.isZero_homology_of_exists_boundary`,
  `PreAbstractSimplicialComplex.IsAcyclicIn.isZero_homology_succ`.
* `PreAbstractSimplicialComplex.exists_boundary_zero_of_cone`.
* `PreAbstractSimplicialComplex.isAcyclicIn_simplex`.
* `PreAbstractSimplicialComplex.isAcyclicIn_self_of_cone`,
  `PreAbstractSimplicialComplex.isZero_homology_succ_of_cone'`.
-/

@[expose] public section

open CategoryTheory Limits Finset Simplicial

universe u

namespace PreAbstractSimplicialComplex

variable {κ : Type u} [LinearOrder κ] (R : Type u) [Ring R]
variable {L M : PreAbstractSimplicialComplex κ}

section Inclusion

variable (h : M ≤ L)
include h

omit [LinearOrder κ] in
theorem facesOfDim_mono (n : ℕ) : M.facesOfDim n ⊆ L.facesOfDim n := fun _ ht ↦ ⟨h ht.1, ht.2⟩

/-- The inclusion of oriented chains induced by `M ≤ L`. -/
noncomputable def inclChains (n : ℕ) : (M.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim n →₀ R) :=
  Finsupp.lmapDomain R R (Set.inclusion (facesOfDim_mono h n))

omit [LinearOrder κ] in
@[simp]
theorem inclChains_single {n : ℕ} (t : M.facesOfDim n) (r : R) :
    inclChains R h n (Finsupp.single t r) =
      Finsupp.single (Set.inclusion (facesOfDim_mono h n) t) r :=
  Finsupp.mapDomain_single

omit [LinearOrder κ] in
theorem inclChains_injective (n : ℕ) : Function.Injective (inclChains R h n) :=
  Finsupp.mapDomain_injective (Set.inclusion_injective _)

theorem orientedBoundary_comp_inclChains (n : ℕ) :
    L.orientedBoundary R n ∘ₗ inclChains R h (n + 1) =
      inclChains R h n ∘ₗ M.orientedBoundary R n :=
  Finsupp.lhom_ext' fun t ↦ LinearMap.ext_ring (by
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, inclChains_single,
      orientedBoundary_single, map_sum, map_zsmul]
    rfl)

omit [LinearOrder κ] in
theorem augmentation_comp_inclChains :
    L.augmentation R ∘ₗ inclChains R h 0 = M.augmentation R :=
  Finsupp.lhom_ext' fun t ↦ LinearMap.ext_ring (by simp)

omit [LinearOrder κ] in
theorem inclChains_mem_chainsIn {n : ℕ} (c : M.facesOfDim n →₀ R) :
    inclChains R h n c ∈ chainsIn R L M n := by
  have := Finsupp.lmapDomain_supported (M := R) (R := R) (Set.inclusion (facesOfDim_mono h n))
    Set.univ
  rw [Finsupp.supported_univ, Submodule.map_top] at this
  have hc : inclChains R h n c ∈ LinearMap.range (inclChains R h n) := ⟨c, rfl⟩
  unfold inclChains at hc
  rw [this] at hc
  refine Finsupp.supported_mono ?_ hc
  rintro _ ⟨t, -, rfl⟩
  exact t.2.1

omit [LinearOrder κ] in
theorem exists_inclChains_eq {n : ℕ} {c : L.facesOfDim n →₀ R} (hc : c ∈ chainsIn R L M n) :
    ∃ c', inclChains R h n c' = c := by
  have := Finsupp.lmapDomain_supported (M := R) (R := R) (Set.inclusion (facesOfDim_mono h n))
    Set.univ
  rw [Finsupp.supported_univ, Submodule.map_top] at this
  have hc' : c ∈ Finsupp.supported R R (Set.inclusion (facesOfDim_mono h n) '' Set.univ) := by
    refine Finsupp.supported_mono ?_ hc
    intro t ht
    exact ⟨⟨t.1, ht, t.2.2⟩, Set.mem_univ _, rfl⟩
  rw [← this] at hc'
  exact hc'

/-- Exactness of the oriented chains of `M` in degree `n` transfers to exactness of chains of `L`
supported on `M`. -/
theorem exists_boundary_of_le {n : ℕ}
    (hM : ∀ c, M.IsReducedCycle R n c → ∃ b, M.orientedBoundary R n b = c)
    {c : L.facesOfDim n →₀ R} (hc : c ∈ chainsIn R L M n) (hcyc : L.IsReducedCycle R n c) :
    ∃ b ∈ chainsIn R L M (n + 1), L.orientedBoundary R n b = c := by
  obtain ⟨c, rfl⟩ := exists_inclChains_eq R h hc
  have hcyc' : M.IsReducedCycle R n c := by
    cases n with
    | zero =>
      change L.augmentation R _ = 0 at hcyc
      rwa [← LinearMap.comp_apply, augmentation_comp_inclChains] at hcyc
    | succ n =>
      change L.orientedBoundary R n _ = 0 at hcyc
      rw [← LinearMap.comp_apply, orientedBoundary_comp_inclChains, LinearMap.comp_apply,
        ← map_zero (inclChains R h n)] at hcyc
      exact inclChains_injective R h n hcyc
  obtain ⟨b, rfl⟩ := hM c hcyc'
  exact ⟨inclChains R h (n + 1) b, inclChains_mem_chainsIn R h b,
    by rw [← LinearMap.comp_apply, orientedBoundary_comp_inclChains, LinearMap.comp_apply]⟩

/-- The inclusion of oriented chain complexes induced by `M ≤ L`. -/
noncomputable def orientedInclusion : M.orientedChainComplex R ⟶ L.orientedChainComplex R where
  f n := ModuleCat.ofHom (inclChains R h n)
  comm' := by
    rintro _ n rfl
    exact ModuleCat.hom_ext (orientedBoundary_comp_inclChains R h n)

theorem toSSetMap_simplexOfFace {n : ℕ} (t : M.facesOfDim n) :
    (toSSetMap h).app _ (M.simplexOfFace t) =
      L.simplexOfFace (Set.inclusion (facesOfDim_mono h n) t) :=
  rfl

omit h in
theorem simplexOfFace_surjective {n : ℕ} (x : M.toSSet _⦋n⦌) (hx : x ∈ M.toSSet.nonDegenerate n) :
    ∃ t, M.simplexOfFace t = x :=
  ⟨M.nonDegenerateEquiv n ⟨x, hx⟩, by simp [simplexOfFace]⟩

theorem normalizedChainComplexMap_f_comp_chainsXIso_hom (n : ℕ) :
    (normalizedChainComplexMap (ModuleCat.of R R) h).f n ≫ (L.chainsXIso R n).hom =
      (M.chainsXIso R n).hom ≫ ModuleCat.ofHom (inclChains R h n) := by
  apply SSet.normalizedChainComplex_hom_ext
  intro x hx
  obtain ⟨t, rfl⟩ := simplexOfFace_surjective x hx
  rw [← Category.assoc, SSet.ι_normalizedChainComplexMap_f]
  change L.faceChain _ (Set.inclusion (facesOfDim_mono h n) t) ≫ _ = M.faceChain _ t ≫ _ ≫ _
  rw [faceChain_chainsXIso_hom, reassoc_of% faceChain_chainsXIso_hom]
  ext : 2
  simp

theorem normalizedChainComplexMap_comp_orientedIso_hom :
    normalizedChainComplexMap (ModuleCat.of R R) h ≫ (L.orientedIso R).hom =
      (M.orientedIso R).hom ≫ orientedInclusion R h := by
  ext n : 1
  exact normalizedChainComplexMap_f_comp_chainsXIso_hom R h n

/-- The isomorphism between simplicial homology and oriented homology is natural for
inclusions. -/
theorem homologyMap_comp_homologyIsoOriented_hom (n : ℕ) :
    PreAbstractSimplicialComplex.homologyMap (ModuleCat.of R R) h n ≫
        (L.homologyIsoOriented R n).hom =
      (M.homologyIsoOriented R n).hom ≫
        HomologicalComplex.homologyMap (orientedInclusion R h) n := by
  simp only [homologyIsoOriented, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom,
    reassoc_of% homologyMap_comp_homologyIsoNormalized_hom, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, normalizedChainComplexMap_comp_orientedIso_hom]

omit [LinearOrder κ] in
theorem inclChains_mem_chainsIn_of_mem {N : PreAbstractSimplicialComplex κ} {n : ℕ}
    {c : M.facesOfDim n →₀ R} (hc : c ∈ chainsIn R M N n) :
    inclChains R h n c ∈ chainsIn R L N n := by
  have := Finsupp.lmapDomain_supported (M := R) (R := R) (Set.inclusion (facesOfDim_mono h n))
    {t | t.1 ∈ N}
  have hc' : inclChains R h n c ∈ (chainsIn R M N n).map (inclChains R h n) := ⟨c, hc, rfl⟩
  unfold inclChains chainsIn at hc'
  rw [this] at hc'
  refine Finsupp.supported_mono ?_ hc'
  rintro _ ⟨t, ht, rfl⟩
  exact ht

end Inclusion

section Naturality

variable {ι : Type u} [LinearOrder ι] {K K' : PreAbstractSimplicialComplex ι}
  {L' : PreAbstractSimplicialComplex κ}

/-- Restricting an acyclic carrier to a subcomplex. -/
def AcyclicCarrier.restrict (Φ : AcyclicCarrier R K' L) (h : K ≤ K') : AcyclicCarrier R K L where
  toFun := Φ.toFun
  mono' _ _ hs ht hst := Φ.mono' (h hs) (h ht) hst
  isAcyclicIn' _ hs := Φ.isAcyclicIn' (h hs)

/-- Carried chain maps commute with inclusions up to homotopy, as long as one acyclic carrier
contains both carriers. -/
noncomputable def AcyclicCarrier.homotopyNaturality (Φ : AcyclicCarrier R K L)
    (Φ' : AcyclicCarrier R K' L') (hK : K ≤ K') (hL : L ≤ L') (Θ : AcyclicCarrier R K L')
    (hΦ : ∀ s ∈ K, Φ s ≤ Θ s) (hΦ' : ∀ s ∈ K, Φ' s ≤ Θ s) :
    Homotopy (Φ.chainMap ≫ orientedInclusion R hL) (orientedInclusion R hK ≫ Φ'.chainMap) :=
  Θ.homotopy
    (fun n s ↦ chainsIn_mono R (hΦ s.1 s.2.1) n
      (inclChains_mem_chainsIn_of_mem R hL (Φ.carries_chainMap n s)))
    (fun n s ↦ by
      change orientedComponent Φ'.chainMap n (inclChains R hK n (Finsupp.single s 1)) ∈ _
      rw [inclChains_single]
      exact chainsIn_mono R (hΦ' s.1 s.2.1) n (Φ'.carries_chainMap n _))
    (by
      change L'.augmentation R ∘ₗ (inclChains R hL 0 ∘ₗ orientedComponent Φ.chainMap 0) = _
      rw [← LinearMap.comp_assoc, augmentation_comp_inclChains, Φ.augmentation_comp_chainMap])
    (by
      change L'.augmentation R ∘ₗ (orientedComponent Φ'.chainMap 0 ∘ₗ inclChains R hK 0) = _
      rw [← LinearMap.comp_assoc, Φ'.augmentation_comp_chainMap, augmentation_comp_inclChains])

/-- **Naturality of the homology isomorphisms given by acyclic carriers**, for inclusions
`K ≤ K'` and `L ≤ L'`. -/
theorem AcyclicCarrier.homologyIso_naturality {Φ : AcyclicCarrier R K L} {Ψ : AcyclicCarrier R L K}
    {ΘK : AcyclicCarrier R K K} {ΘL : AcyclicCarrier R L L} {hK : ∀ s ∈ K, s ∈ ΘK s}
    {hL : ∀ t ∈ L, t ∈ ΘL t} {hKc : ∀ s ∈ K, ∀ t ∈ L, t ∈ Φ s → Ψ t ≤ ΘK s}
    {hLc : ∀ t ∈ L, ∀ s ∈ K, s ∈ Ψ t → Φ s ≤ ΘL t}
    {Φ' : AcyclicCarrier R K' L'} {Ψ' : AcyclicCarrier R L' K'}
    {ΘK' : AcyclicCarrier R K' K'} {ΘL' : AcyclicCarrier R L' L'} {hK' : ∀ s ∈ K', s ∈ ΘK' s}
    {hL' : ∀ t ∈ L', t ∈ ΘL' t} {hKc' : ∀ s ∈ K', ∀ t ∈ L', t ∈ Φ' s → Ψ' t ≤ ΘK' s}
    {hLc' : ∀ t ∈ L', ∀ s ∈ K', s ∈ Ψ' t → Φ' s ≤ ΘL' t}
    (hKK' : K ≤ K') (hLL' : L ≤ L') (Θ : AcyclicCarrier R K L') (hΦ : ∀ s ∈ K, Φ s ≤ Θ s)
    (hΦ' : ∀ s ∈ K, Φ' s ≤ Θ s) (n : ℕ) :
    (AcyclicCarrier.homologyIso Φ Ψ ΘK ΘL hK hL hKc hLc n).hom ≫
        PreAbstractSimplicialComplex.homologyMap (ModuleCat.of R R) hLL' n =
      PreAbstractSimplicialComplex.homologyMap (ModuleCat.of R R) hKK' n ≫
        (AcyclicCarrier.homologyIso Φ' Ψ' ΘK' ΘL' hK' hL' hKc' hLc' n).hom := by
  have nL : (L.homologyIsoOriented R n).inv ≫
      PreAbstractSimplicialComplex.homologyMap (ModuleCat.of R R) hLL' n =
      HomologicalComplex.homologyMap (orientedInclusion R hLL') n ≫
        (L'.homologyIsoOriented R n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← homologyMap_comp_homologyIsoOriented_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hH : HomologicalComplex.homologyMap Φ.chainMap n ≫
      HomologicalComplex.homologyMap (orientedInclusion R hLL') n =
      HomologicalComplex.homologyMap (orientedInclusion R hKK') n ≫
        HomologicalComplex.homologyMap Φ'.chainMap n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      (AcyclicCarrier.homotopyNaturality R Φ Φ' hKK' hLL' Θ hΦ hΦ').homologyMap_eq]
  simp only [AcyclicCarrier.homologyIso, Iso.trans_hom, Iso.symm_hom,
    HomotopyEquiv.toHomologyIso, AcyclicCarrier.homotopyEquiv, Category.assoc, nL,
    reassoc_of% hH, reassoc_of% homologyMap_comp_homologyIsoOriented_hom]

end Naturality

/-- `M` is acyclic inside any complex containing it, as soon as it is acyclic in itself. -/
theorem IsAcyclicIn.of_le (h : M ≤ L) (hM : IsAcyclicIn R M M) : IsAcyclicIn R L M where
  exists_vertex := by
    obtain ⟨t, ht⟩ := hM.exists_vertex
    exact ⟨⟨t.1, h t.2.1, t.2.2⟩, ht⟩
  exists_boundary n _ hc hcyc := exists_boundary_of_le R h
    (fun c hc ↦ (hM.exists_boundary n c (fun t _ ↦ t.2.1) hc).imp fun _ hb ↦ hb.2) hc hcyc

/-- If `Hₙ₊₁(M; R) = 0`, every oriented `(n+1)`-cycle of `M` is a boundary. -/
theorem exists_boundary_of_isZero_homology {n : ℕ}
    (hM : IsZero (M.homology (ModuleCat.of R R) (n + 1))) (c : M.facesOfDim (n + 1) →₀ R)
    (hc : M.orientedBoundary R n c = 0) : ∃ b, M.orientedBoundary R (n + 1) b = c := by
  have hex : (M.orientedChainComplex R).ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (hM.of_iso (M.homologyIsoOriented R (n + 1)).symm)
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  exact hex c hc

section DegreeZero

omit [LinearOrder κ] in
theorem singleton_mem_of_mem {s : Finset κ} (hs : s ∈ L) {w : κ} (hw : w ∈ s) : {w} ∈ L :=
  L.mem_of_subset hs (singleton_subset_iff.2 hw) (singleton_nonempty w)

/-- The boundary of an edge `[v, w]` with `v < w` is `[w] - [v]`. -/
theorem orientedBoundary_single_pair {v w : κ} (hvw : v < w) (he : {v, w} ∈ L) (r : R) :
    L.orientedBoundary R 0 (Finsupp.single ⟨{v, w}, he, card_pair hvw.ne⟩ r) =
      Finsupp.single ⟨{w}, singleton_mem_of_mem he (by simp), card_singleton w⟩ r -
        Finsupp.single ⟨{v}, singleton_mem_of_mem he (by simp), card_singleton v⟩ r := by
  set e : L.facesOfDim 1 := ⟨{v, w}, he, card_pair hvw.ne⟩
  have h0 := orderEmbOfFin_mem e.1 e.2.2 0
  have h1 := orderEmbOfFin_mem e.1 e.2.2 1
  have hlt := (e.1.orderEmbOfFin e.2.2).strictMono (show (0 : Fin 2) < 1 by decide)
  have hv : e.1.orderEmbOfFin e.2.2 0 = v ∧ e.1.orderEmbOfFin e.2.2 1 = w := by
    simp only [e, mem_insert, mem_singleton] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hlt
    · exact absurd hlt (lt_irrefl _)
    · exact ⟨h0, h1⟩
    · exact absurd hlt (lt_asymm hvw)
    · exact absurd hlt (lt_irrefl _)
  have hf0 : faceErase e 0 = ⟨{w}, singleton_mem_of_mem he (by simp), card_singleton w⟩ :=
    Subtype.ext (by simp [faceErase, hv.1, e, hvw.ne])
  have hf1 : faceErase e 1 = ⟨{v}, singleton_mem_of_mem he (by simp), card_singleton v⟩ :=
    Subtype.ext (by simp [faceErase, hv.2, e, erase_insert_of_ne hvw.ne])
  rw [orientedBoundary_single, Fin.sum_univ_two, hf0, hf1]
  simp [sub_eq_add_neg]

/-- If every vertex of `M` is joined to `v` by an edge of `M`, every `0`-chain supported on `M`
with augmentation `0` is the boundary of a `1`-chain supported on `M`. -/
theorem exists_boundary_zero_of_cone {v : κ} (hv : {v} ∈ M) (hML : M ≤ L)
    (hcone : ∀ w, {w} ∈ M → {v, w} ∈ M) {c : L.facesOfDim 0 →₀ R} (hc : c ∈ chainsIn R L M 0)
    (haug : L.augmentation R c = 0) :
    ∃ b ∈ chainsIn R L M 1, L.orientedBoundary R 0 b = c := by
  let tv : L.facesOfDim 0 := ⟨{v}, hML hv, card_singleton v⟩
  let T := LinearMap.id - Finsupp.lsingle tv ∘ₗ L.augmentation R
  let B := (chainsIn R L M 1).map (L.orientedBoundary R 0)
  suffices hle : chainsIn R L M 0 ≤ B.comap T by
    have := hle hc
    simp only [Submodule.mem_comap, T, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, haug, map_zero, sub_zero, B, Submodule.mem_map] at this
    exact this
  rw [chainsIn, Finsupp.supported_eq_span_single, Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨w, hw⟩ := card_eq_one.1 t.2.2
  have htw : t = ⟨{w}, hw ▸ t.2.1, card_singleton w⟩ := Subtype.ext hw
  have hwM : {w} ∈ M := hw ▸ ht
  simp only [SetLike.mem_coe, Submodule.mem_comap, T, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, augmentation_single, Finsupp.lsingle_apply]
  rcases lt_trichotomy v w with hvw | rfl | hwv
  · refine ⟨Finsupp.single ⟨{v, w}, hML (hcone w hwM), card_pair hvw.ne⟩ 1,
      single_mem_chainsIn R (hcone w hwM) 1, ?_⟩
    rw [orientedBoundary_single_pair R hvw (hML (hcone w hwM)), htw]
  · rw [show t = tv from htw, sub_self]
    exact zero_mem _
  · have he : {w, v} ∈ M := pair_comm v w ▸ hcone w hwM
    refine ⟨Finsupp.single ⟨{w, v}, hML he, card_pair hwv.ne⟩ (-1),
      single_mem_chainsIn R he _, ?_⟩
    rw [orientedBoundary_single_pair R hwv (hML he), htw]
    simp only [Finsupp.single_neg, tv]
    abel

end DegreeZero

/-- A full simplex on a face of `L` is acyclic in `L`. -/
theorem isAcyclicIn_simplex {s : Finset κ} (hs : s ∈ L) : IsAcyclicIn R L (simplex s) where
  exists_vertex := by
    have hne := L.nonempty_of_mem hs
    exact ⟨⟨{s.min' hne}, singleton_mem_of_mem hs (s.min'_mem hne), card_singleton _⟩,
      mem_simplex.2 ⟨singleton_nonempty _, singleton_subset_iff.2 (s.min'_mem hne)⟩⟩
  exists_boundary n c hc hcyc := by
    have hne := L.nonempty_of_mem hs
    have hML : simplex s ≤ L := (simplex_le_iff hne).2 hs
    cases n with
    | zero =>
      exact exists_boundary_zero_of_cone R
        (mem_simplex.2 ⟨singleton_nonempty _, singleton_subset_iff.2 (s.min'_mem hne)⟩) hML
        (fun _ hw ↦ mem_simplex.2 ⟨insert_nonempty _ _, insert_subset (s.min'_mem hne)
          (mem_simplex.1 hw).2⟩) hc hcyc
    | succ n =>
      exact exists_boundary_of_le R hML (fun c hc ↦ exists_boundary_of_isZero_homology R
        (isZero_homology_succ_simplex (ModuleCat.of R R) hne n) c hc) hc hcyc

section Cone

omit [LinearOrder κ] in
theorem eq_single_of_mem_chainsIn_simplex_singleton {v : κ} (hv : {v} ∈ L)
    {c : L.facesOfDim 0 →₀ R} (hc : c ∈ chainsIn R L (simplex {v}) 0) :
    c = Finsupp.single ⟨{v}, hv, card_singleton v⟩ (L.augmentation R c) := by
  have hsub : c.support ⊆ {⟨{v}, hv, card_singleton v⟩} := by
    intro t ht
    have h1 := (mem_simplex.1 (hc ht))
    exact Finset.mem_singleton.2
      (Subtype.ext (Finset.Nonempty.subset_singleton_iff h1.1 |>.1 h1.2))
  rw [Finsupp.support_subset_singleton] at hsub
  conv_lhs => rw [hsub]
  conv_rhs => rw [hsub]
  simp

omit [LinearOrder κ] in
theorem eq_zero_of_mem_chainsIn_simplex_singleton {v : κ} {n : ℕ}
    {c : L.facesOfDim (n + 1) →₀ R} (hc : c ∈ chainsIn R L (simplex {v}) (n + 1)) : c = 0 := by
  rw [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  have h1 := card_le_card (mem_simplex.1 (hc ht)).2
  rw [t.2.2, card_singleton] at h1
  omega

omit [LinearOrder κ] in
theorem mem_chainsIn_self {n : ℕ} (c : M.facesOfDim n →₀ R) : c ∈ chainsIn R M M n :=
  fun t _ ↦ t.2.1

variable {v : κ} (hv : {v} ∈ M) (hcone : ∀ s ∈ M, insert v s ∈ M)

/-- The acyclic carrier `s ↦ Δ(s ∪ {v})` on a cone with apex `v`. -/
def coneCarrier : AcyclicCarrier R M M where
  toFun s := simplex (insert v s)
  mono' _ _ _ _ hst := simplex_mono (insert_subset_insert _ hst)
  isAcyclicIn' _ hs := isAcyclicIn_simplex R (hcone _ hs)

/-- The constant acyclic carrier `s ↦ Δ{v}`. -/
def constCarrier : AcyclicCarrier R M M where
  toFun _ := simplex {v}
  mono' _ _ _ _ _ := le_rfl
  isAcyclicIn' _ _ := isAcyclicIn_simplex R hv

include hv hcone in
/-- **Cones are acyclic**, whatever the position of the apex in the vertex order. -/
theorem isAcyclicIn_self_of_cone : IsAcyclicIn R M M where
  exists_vertex := ⟨⟨{v}, hv, card_singleton v⟩, hv⟩
  exists_boundary n c _ hcyc := by
    let Θ := coneCarrier R hcone
    let Ψ := constCarrier R hv
    have hf : ∀ n, Θ.Carries (orientedComponent (𝟙 (M.orientedChainComplex R)) n) :=
      fun _ s ↦ single_mem_chainsIn R
        (mem_simplex.2 ⟨M.nonempty_of_mem s.2.1, subset_insert _ _⟩) 1
    have hg : ∀ n, Θ.Carries (orientedComponent Ψ.chainMap n) := fun n ↦
      (Ψ.carries_chainMap n).mono fun _ ↦
        simplex_mono (singleton_subset_iff.2 (mem_insert_self _ _))
    have hfa : M.augmentation R ∘ₗ orientedComponent (𝟙 (M.orientedChainComplex R)) 0 =
        M.augmentation R := LinearMap.comp_id _
    have hga := Ψ.augmentation_comp_chainMap
    have hΨ : ∀ {m : ℕ} (c : M.facesOfDim m →₀ R),
        orientedComponent Ψ.chainMap m c ∈ chainsIn R M (simplex {v}) m :=
      fun c ↦ (Ψ.carries_chainMap _).apply_mem fun _ _ ↦ le_rfl
    cases n with
    | zero =>
      refine ⟨(Θ.homotopyAux hf hg hfa hga 0).1 c, mem_chainsIn_self R _, ?_⟩
      have key := LinearMap.congr_fun (Θ.homotopyAux_zero hf hg hfa hga) c
      have hgc := eq_single_of_mem_chainsIn_simplex_singleton R hv (hΨ c)
      rw [← LinearMap.comp_apply (M.augmentation R), hga] at hgc
      change M.augmentation R c = 0 at hcyc
      rw [hcyc, Finsupp.single_zero] at hgc
      rw [LinearMap.comp_apply] at key
      rw [key]
      change c - _ = c
      rw [hgc, sub_zero]
    | succ n =>
      refine ⟨(Θ.homotopyAux hf hg hfa hga (n + 1)).1 c, mem_chainsIn_self R _, ?_⟩
      have key := LinearMap.congr_fun (Θ.homotopyAux_succ hf hg hfa hga n) c
      rw [LinearMap.comp_apply] at key
      rw [key]
      change c - _ - _ = c
      rw [eq_zero_of_mem_chainsIn_simplex_singleton R (hΨ c), LinearMap.comp_apply,
        show M.orientedBoundary R n c = 0 from hcyc, map_zero, sub_zero, sub_zero]

end Cone

section Transfer

variable {ι : Type u} [LinearOrder ι] {K : PreAbstractSimplicialComplex ι}

/-- **Acyclicity transfers along carriers.** If `K` is acyclic and there are carriers
`Φ : K → L`, `Ψ : L → K` such that an acyclic carrier containing the identity carries `Φ ∘ Ψ`,
then `L` is acyclic. -/
theorem isAcyclicIn_self_of_carriers (Φ : AcyclicCarrier R K L) (Ψ : AcyclicCarrier R L K)
    (ΘL : AcyclicCarrier R L L) (hL : ∀ t ∈ L, t ∈ ΘL t)
    (hLc : ∀ t ∈ L, ∀ s ∈ K, s ∈ Ψ t → Φ s ≤ ΘL t) (hK : IsAcyclicIn R K K) :
    IsAcyclicIn R L L where
  exists_vertex := by
    obtain ⟨t, -⟩ := hK.exists_vertex
    obtain ⟨t', -⟩ := (Φ.isAcyclicIn t.2.1).exists_vertex
    exact ⟨t', t'.2.1⟩
  exists_boundary n z _ hz := by
    have hf := AcyclicCarrier.carries_id (Θ := ΘL) hL
    have hg : ∀ n, ΘL.Carries (orientedComponent (Ψ.chainMap ≫ Φ.chainMap) n) :=
      fun n ↦ (Ψ.carries_chainMap n).comp (Φ.carries_chainMap n) hLc
    have hfa : L.augmentation R ∘ₗ orientedComponent (𝟙 (L.orientedChainComplex R)) 0 =
        L.augmentation R := LinearMap.comp_id _
    have hga : L.augmentation R ∘ₗ orientedComponent (Ψ.chainMap ≫ Φ.chainMap) 0 =
        L.augmentation R := by
      change L.augmentation R ∘ₗ (orientedComponent Φ.chainMap 0 ∘ₗ
        orientedComponent Ψ.chainMap 0) = _
      rw [← LinearMap.comp_assoc, Φ.augmentation_comp_chainMap, Ψ.augmentation_comp_chainMap]
    set w := orientedComponent Ψ.chainMap n z with hw
    have hwc : K.IsReducedCycle R n w := by
      cases n with
      | zero =>
        change K.augmentation R w = 0
        rw [hw, ← LinearMap.comp_apply, Ψ.augmentation_comp_chainMap]
        exact hz
      | succ n =>
        change K.orientedBoundary R n w = 0
        rw [hw, ← LinearMap.comp_apply, orientedBoundary_comp_orientedComponent,
          LinearMap.comp_apply, show L.orientedBoundary R n z = 0 from hz, map_zero]
    obtain ⟨a, -, ha⟩ := hK.exists_boundary n w (mem_chainsIn_self R w) hwc
    refine ⟨orientedComponent Φ.chainMap (n + 1) a +
      (ΘL.homotopyAux hf hg hfa hga n).1 z, mem_chainsIn_self R _, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, orientedBoundary_comp_orientedComponent,
      LinearMap.comp_apply, ha, ← LinearMap.comp_apply (L.orientedBoundary R n)]
    cases n with
    | zero =>
      rw [ΘL.homotopyAux_zero hf hg hfa hga]
      change _ + (z - orientedComponent Φ.chainMap 0 w) = z
      abel
    | succ n =>
      rw [ΘL.homotopyAux_succ hf hg hfa hga n]
      change _ + (z - orientedComponent Φ.chainMap (n + 1) w -
        (ΘL.homotopyAux hf hg hfa hga n).1 (L.orientedBoundary R n z)) = z
      rw [show L.orientedBoundary R n z = 0 from hz, map_zero]
      abel

end Transfer

/-- Conversely, if every oriented `(n+1)`-cycle of `M` is a boundary, `Hₙ₊₁(M; R) = 0`. -/
theorem isZero_homology_of_exists_boundary {n : ℕ}
    (hM : ∀ c : M.facesOfDim (n + 1) →₀ R, M.orientedBoundary R n c = 0 →
      ∃ b, M.orientedBoundary R (n + 1) b = c) :
    IsZero (M.homology (ModuleCat.of R R) (n + 1)) := by
  have hex : (M.orientedChainComplex R).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    exact hM
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex).of_iso
    (M.homologyIsoOriented R (n + 1))

theorem IsAcyclicIn.isZero_homology_succ (hM : IsAcyclicIn R M M) (n : ℕ) :
    IsZero (M.homology (ModuleCat.of R R) (n + 1)) :=
  isZero_homology_of_exists_boundary R fun c hc ↦
    (hM.exists_boundary (n + 1) c (mem_chainsIn_self R c) hc).imp fun _ hb ↦ hb.2

/-- A cone has no homology in positive degrees, wherever its apex sits in the vertex order. -/
theorem isZero_homology_succ_of_cone' {v : κ} (hv : {v} ∈ M) (hcone : ∀ s ∈ M, insert v s ∈ M)
    (n : ℕ) : IsZero (M.homology (ModuleCat.of R R) (n + 1)) :=
  (isAcyclicIn_self_of_cone R hv hcone).isZero_homology_succ R n

end PreAbstractSimplicialComplex
