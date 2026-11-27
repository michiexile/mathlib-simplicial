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

TODO
-/

@[expose] public section

open CategoryTheory Limits Finset

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

end Inclusion

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

end PreAbstractSimplicialComplex
