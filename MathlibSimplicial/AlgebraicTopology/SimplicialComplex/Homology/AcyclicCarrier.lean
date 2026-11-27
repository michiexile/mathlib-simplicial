/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.AlgebraicTopology.SimplicialComplex.Homology.Oriented
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# The acyclic carrier theorem

The acyclic carrier theorem is the classical tool for building chain maps and chain homotopies
between simplicial chain complexes when there is no simplicial map available. An **acyclic
carrier** `Φ` from `K` to `L` assigns to each face `s` of `K` a subcomplex `Φ s` of `L` such that
* `Φ` is monotone: `s ⊆ t` implies `Φ s ≤ Φ t`, and
* each `Φ s` is acyclic (it has the reduced homology of a point).

A linear map of oriented chains is **carried** by `Φ` if it sends each face `s` to a chain
supported on `Φ s`. The theorem says:
* (existence) there is an augmentation-preserving chain map carried by `Φ`
  (`AcyclicCarrier.chainMap`);
* (uniqueness) any two augmentation-preserving chain maps carried by `Φ` are chain homotopic
  (`AcyclicCarrier.homotopy`).

Both are proved by induction on the degree: the image of a face `s` is chosen as a chain in
`Φ s` whose boundary is already determined, which exists because `Φ s` is acyclic.

We work with the oriented chains `K.facesOfDim n →₀ R` of `Homology/Oriented.lean` over a ring
`R`, so that "a chain supported on `M`" is the submodule `Finsupp.supported` (`chainsIn`).
Acyclicity is expressed concretely (`IsAcyclicIn`): every reduced cycle supported on `M` bounds a
chain supported on `M`. `Homology/AcyclicSubcomplex.lean` relates this to homology.

Typical uses: cones with an arbitrary apex are acyclic; homology does not depend on the vertex
order; simplicial maps induce maps in homology; barycentric subdivision and the nerve lemma.

## Main declarations

* `PreAbstractSimplicialComplex.chainsIn`, `PreAbstractSimplicialComplex.IsReducedCycle`,
  `PreAbstractSimplicialComplex.IsAcyclicIn`.
* `PreAbstractSimplicialComplex.exists_lift`: the basic lifting step.
* `PreAbstractSimplicialComplex.AcyclicCarrier`, `AcyclicCarrier.Carries`.
* `AcyclicCarrier.chainMap`, `AcyclicCarrier.carries_chainMap`,
  `AcyclicCarrier.augmentation_comp_chainMap`.
* `AcyclicCarrier.homotopy`, with the explicit components `AcyclicCarrier.homotopyAux`.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, §13 (Theorem 13.3).
-/

@[expose] public section

open CategoryTheory Finset

universe u

namespace PreAbstractSimplicialComplex

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (R : Type u) [Ring R]

section ChainsIn

variable (L M : PreAbstractSimplicialComplex κ)

/-- The oriented `n`-chains of `L` supported on faces of `M`. -/
def chainsIn (n : ℕ) : Submodule R (L.facesOfDim n →₀ R) :=
  Finsupp.supported R R {t | t.1 ∈ M}

variable {L M}

omit [LinearOrder κ] in
theorem single_mem_chainsIn {n : ℕ} {t : L.facesOfDim n} (ht : t.1 ∈ M) (r : R) :
    Finsupp.single t r ∈ chainsIn R L M n :=
  Finsupp.single_mem_supported R r ht

omit [LinearOrder κ] in
theorem chainsIn_mono {M' : PreAbstractSimplicialComplex κ} (h : M ≤ M') (n : ℕ) :
    chainsIn R L M n ≤ chainsIn R L M' n :=
  Finsupp.supported_mono fun _ ht ↦ h ht

theorem orientedBoundary_mem_chainsIn {n : ℕ} {c : L.facesOfDim (n + 1) →₀ R}
    (hc : c ∈ chainsIn R L M (n + 1)) : L.orientedBoundary R n c ∈ chainsIn R L M n := by
  rw [← Finsupp.sum_single c, map_finsuppSum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun t ht ↦ ?_
  rw [orientedBoundary_single]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_of_tower_mem _ _ ?_
  refine single_mem_chainsIn R
    (M.mem_of_subset (hc (Finsupp.mem_support_iff.2 ht)) (erase_subset _ _) ?_) _
  exact L.nonempty_of_mem (faceErase t i).2.1

variable (L) in
/-- A reduced cycle in degree `n`: a `0`-chain with augmentation `0`, or a cycle in positive
degree. Reduced homology measures reduced cycles modulo boundaries. -/
def IsReducedCycle : (n : ℕ) → (L.facesOfDim n →₀ R) → Prop
  | 0, c => L.augmentation R c = 0
  | n + 1, c => L.orientedBoundary R n c = 0

theorem isReducedCycle_orientedBoundary {n : ℕ} (c : L.facesOfDim (n + 1) →₀ R) :
    L.IsReducedCycle R n (L.orientedBoundary R n c) := by
  cases n with
  | zero => exact L.augmentation_orientedBoundary R c
  | succ n => exact L.orientedBoundary_orientedBoundary R n c

variable (L M) in
/-- `M` is acyclic inside `L`: it contains a vertex of `L`, and every reduced cycle of `L`
supported on `M` bounds a chain supported on `M`. For `M ≤ L` this says that `M` has the
reduced homology of a point. -/
structure IsAcyclicIn : Prop where
  exists_vertex : ∃ t : L.facesOfDim 0, t.1 ∈ M
  exists_boundary (n : ℕ) (c : L.facesOfDim n →₀ R) :
    c ∈ chainsIn R L M n → L.IsReducedCycle R n c →
      ∃ b ∈ chainsIn R L M (n + 1), L.orientedBoundary R n b = c

/-- The basic lifting step: a linear map `E` into reduced `n`-cycles of `L`, carried by acyclic
subcomplexes `A x`, lifts along the boundary map to a map carried by the same subcomplexes. -/
theorem exists_lift {X : Type*} (A : X → PreAbstractSimplicialComplex κ)
    (hA : ∀ x, IsAcyclicIn R L (A x)) {n : ℕ} (E : (X →₀ R) →ₗ[R] (L.facesOfDim n →₀ R))
    (hE : ∀ x, E (Finsupp.single x 1) ∈ chainsIn R L (A x) n)
    (hEc : ∀ x, L.IsReducedCycle R n (E (Finsupp.single x 1))) :
    ∃ h : (X →₀ R) →ₗ[R] (L.facesOfDim (n + 1) →₀ R),
      (∀ x, h (Finsupp.single x 1) ∈ chainsIn R L (A x) (n + 1)) ∧
        L.orientedBoundary R n ∘ₗ h = E := by
  choose b hb hbd using fun x ↦ (hA x).exists_boundary n _ (hE x) (hEc x)
  refine ⟨Finsupp.linearCombination R b, fun x ↦ by simpa using hb x, ?_⟩
  refine Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring ?_
  simp [hbd]

end ChainsIn

variable (K : PreAbstractSimplicialComplex ι) (L : PreAbstractSimplicialComplex κ)

/-- An acyclic carrier from `K` to `L` assigns to each face `s` of `K` a subcomplex `Φ s` of
`L`, monotonically in `s` and acyclic in `L`. -/
structure AcyclicCarrier where
  /-- The subcomplex of `L` carrying the face `s`. -/
  toFun : Finset ι → PreAbstractSimplicialComplex κ
  mono' ⦃s t : Finset ι⦄ : s ∈ K → t ∈ K → s ⊆ t → toFun s ≤ toFun t
  isAcyclicIn' ⦃s : Finset ι⦄ : s ∈ K → IsAcyclicIn R L (toFun s)

variable {R K L} in
/-- The degree-`n` component of a chain map of oriented chain complexes, as a linear map. -/
noncomputable abbrev orientedComponent (φ : K.orientedChainComplex R ⟶ L.orientedChainComplex R)
    (n : ℕ) : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim n →₀ R) :=
  (φ.f n).hom

variable {R K L} in
theorem orientedBoundary_comp_orientedComponent
    (φ : K.orientedChainComplex R ⟶ L.orientedChainComplex R) (n : ℕ) :
    L.orientedBoundary R n ∘ₗ orientedComponent φ (n + 1) =
      orientedComponent φ n ∘ₗ K.orientedBoundary R n :=
  congrArg ModuleCat.Hom.hom (φ.comm (n + 1) n)

namespace AcyclicCarrier

variable {R K L} (Φ : AcyclicCarrier R K L)

instance : CoeFun (AcyclicCarrier R K L) fun _ ↦ Finset ι → PreAbstractSimplicialComplex κ :=
  ⟨toFun⟩

omit [LinearOrder ι] in
theorem mono {s t : Finset ι} (hs : s ∈ K) (ht : t ∈ K) (hst : s ⊆ t) : Φ s ≤ Φ t :=
  Φ.mono' hs ht hst

omit [LinearOrder ι] in
theorem isAcyclicIn {s : Finset ι} (hs : s ∈ K) : IsAcyclicIn R L (Φ s) := Φ.isAcyclicIn' hs

/-- A linear map from `n`-chains of `K` to `m`-chains of `L` is carried by `Φ` if it sends each
face `s` to a chain supported on `Φ s`. -/
def Carries {n m : ℕ} (f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim m →₀ R)) : Prop :=
  ∀ s : K.facesOfDim n, f (Finsupp.single s 1) ∈ chainsIn R L (Φ s.1) m

variable {Φ} in
theorem Carries.comp_orientedBoundary {n m : ℕ}
    {f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim m →₀ R)} (hf : Φ.Carries f) :
    Φ.Carries (f ∘ₗ K.orientedBoundary R n) := fun s ↦ by
  rw [LinearMap.comp_apply, orientedBoundary_single, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_zsmul]
  exact Submodule.smul_of_tower_mem _ _
    (chainsIn_mono R (Φ.mono (faceErase s i).2.1 s.2.1 (erase_subset _ _)) m (hf (faceErase s i)))

omit [LinearOrder ι] in
variable {Φ} in
/-- A carried map sends a chain to a chain supported on any subcomplex containing the carriers
of the faces in its support. -/
theorem Carries.apply_mem {n m : ℕ} {f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim m →₀ R)}
    (hf : Φ.Carries f) {c : K.facesOfDim n →₀ R} {N : PreAbstractSimplicialComplex κ}
    (hN : ∀ t ∈ c.support, Φ t.1 ≤ N) : f c ∈ chainsIn R L N m := by
  rw [← Finsupp.sum_single c, map_finsuppSum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun t ht ↦ ?_
  rw [← Finsupp.smul_single_one, map_smul]
  exact Submodule.smul_mem _ _ (chainsIn_mono R (hN t (Finsupp.mem_support_iff.2 ht)) m (hf t))

omit [LinearOrder ι] in
variable {Φ} in
theorem Carries.mono {n m : ℕ} {f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim m →₀ R)}
    (hf : Φ.Carries f) {Ψ : AcyclicCarrier R K L} (h : ∀ s : K.facesOfDim n, Φ s.1 ≤ Ψ s.1) :
    Ψ.Carries f :=
  fun s ↦ chainsIn_mono R (h s) m (hf s)

omit [LinearOrder ι] in
variable {Φ} in
theorem Carries.sub {n m : ℕ} {f g : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim m →₀ R)}
    (hf : Φ.Carries f) (hg : Φ.Carries g) : Φ.Carries (f - g) :=
  fun s ↦ Submodule.sub_mem _ (hf s) (hg s)

/-- The invariant of the inductive construction of a carried chain map in degree `n`: `f` is
carried by `Φ` and sends reduced cycles to reduced cycles. -/
def IsGood (n : ℕ) (f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim n →₀ R)) : Prop :=
  Φ.Carries f ∧ ∀ c, K.IsReducedCycle R n c → L.IsReducedCycle R n (f c)

theorem exists_isGood_zero :
    ∃ f : (K.facesOfDim 0 →₀ R) →ₗ[R] (L.facesOfDim 0 →₀ R),
      Φ.IsGood 0 f ∧ L.augmentation R ∘ₗ f = K.augmentation R := by
  choose w hw using fun s : K.facesOfDim 0 ↦ (Φ.isAcyclicIn s.2.1).exists_vertex
  have haug : L.augmentation R ∘ₗ
      Finsupp.linearCombination R (fun s ↦ Finsupp.single (w s) 1) = K.augmentation R :=
    Finsupp.lhom_ext' fun s ↦ LinearMap.ext_ring (by simp)
  refine ⟨_, ⟨fun s ↦ by simpa using single_mem_chainsIn R (hw s) 1, fun c hc ↦ ?_⟩, haug⟩
  change L.augmentation R _ = 0
  rw [← LinearMap.comp_apply, haug]
  exact hc

theorem exists_isGood_succ {n : ℕ} {f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim n →₀ R)}
    (hf : Φ.IsGood n f) :
    ∃ f' : (K.facesOfDim (n + 1) →₀ R) →ₗ[R] (L.facesOfDim (n + 1) →₀ R),
      Φ.IsGood (n + 1) f' ∧ L.orientedBoundary R n ∘ₗ f' = f ∘ₗ K.orientedBoundary R n := by
  obtain ⟨h, hcar, hcomm⟩ := exists_lift R (fun s : K.facesOfDim (n + 1) ↦ Φ s.1)
    (fun s ↦ Φ.isAcyclicIn s.2.1) (f ∘ₗ K.orientedBoundary R n) hf.1.comp_orientedBoundary
    (fun s ↦ hf.2 _ (isReducedCycle_orientedBoundary R _))
  refine ⟨h, ⟨hcar, fun c hc ↦ ?_⟩, hcomm⟩
  change L.orientedBoundary R n (h c) = 0
  rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
  rw [show K.orientedBoundary R n c = 0 from hc, map_zero]

/-- The degreewise linear maps of `Φ.chainMap`, together with their invariant. -/
noncomputable def chainMapAux : (n : ℕ) →
    {f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim n →₀ R) // Φ.IsGood n f}
  | 0 => ⟨_, Φ.exists_isGood_zero.choose_spec.1⟩
  | n + 1 => ⟨_, (Φ.exists_isGood_succ (chainMapAux n).2).choose_spec.1⟩

theorem chainMapAux_comm (n : ℕ) :
    L.orientedBoundary R n ∘ₗ (Φ.chainMapAux (n + 1)).1 =
      (Φ.chainMapAux n).1 ∘ₗ K.orientedBoundary R n :=
  (Φ.exists_isGood_succ (Φ.chainMapAux n).2).choose_spec.2

theorem augmentation_comp_chainMapAux_zero :
    L.augmentation R ∘ₗ (Φ.chainMapAux 0).1 = K.augmentation R :=
  Φ.exists_isGood_zero.choose_spec.2

/-- A chain map carried by an acyclic carrier, preserving augmentations. -/
noncomputable def chainMap : K.orientedChainComplex R ⟶ L.orientedChainComplex R where
  f n := ModuleCat.ofHom (Φ.chainMapAux n).1
  comm' := by
    rintro _ n rfl
    exact ModuleCat.hom_ext (Φ.chainMapAux_comm n)

theorem carries_chainMap (n : ℕ) : Φ.Carries (orientedComponent Φ.chainMap n) :=
  (Φ.chainMapAux n).2.1

theorem augmentation_comp_chainMap :
    L.augmentation R ∘ₗ orientedComponent Φ.chainMap 0 = K.augmentation R :=
  Φ.augmentation_comp_chainMapAux_zero

section Homotopy

variable {f g : K.orientedChainComplex R ⟶ L.orientedChainComplex R}
  (hf : ∀ n, Φ.Carries (orientedComponent f n)) (hg : ∀ n, Φ.Carries (orientedComponent g n))
  (hfa : L.augmentation R ∘ₗ orientedComponent f 0 = K.augmentation R)
  (hga : L.augmentation R ∘ₗ orientedComponent g 0 = K.augmentation R)

omit [LinearOrder κ] in
theorem _root_.PreAbstractSimplicialComplex.orientedBoundary_comp_orientedBoundary' (n : ℕ) :
    K.orientedBoundary R n ∘ₗ K.orientedBoundary R (n + 1) = 0 :=
  LinearMap.ext fun c ↦ K.orientedBoundary_orientedBoundary R n c

include hf hg hfa hga

theorem exists_homotopy_zero :
    ∃ h : (K.facesOfDim 0 →₀ R) →ₗ[R] (L.facesOfDim 1 →₀ R), Φ.Carries h ∧
      L.orientedBoundary R 0 ∘ₗ h = orientedComponent f 0 - orientedComponent g 0 :=
  exists_lift R (fun s : K.facesOfDim 0 ↦ Φ s.1) (fun s ↦ Φ.isAcyclicIn s.2.1) _
    ((hf 0).sub (hg 0)) fun s ↦ by
      change L.augmentation R _ = 0
      rw [LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply, hfa, hga,
        sub_self]

omit hfa hga in
theorem exists_homotopy_succ {n : ℕ} {h : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim (n + 1) →₀ R)}
    (hh : Φ.Carries h) (hh' : L.orientedBoundary R n ∘ₗ h ∘ₗ K.orientedBoundary R n =
      (orientedComponent f n - orientedComponent g n) ∘ₗ K.orientedBoundary R n) :
    ∃ h' : (K.facesOfDim (n + 1) →₀ R) →ₗ[R] (L.facesOfDim (n + 2) →₀ R), Φ.Carries h' ∧
      L.orientedBoundary R (n + 1) ∘ₗ h' =
        orientedComponent f (n + 1) - orientedComponent g (n + 1) -
          h ∘ₗ K.orientedBoundary R n := by
  refine exists_lift R (fun s : K.facesOfDim (n + 1) ↦ Φ s.1) (fun s ↦ Φ.isAcyclicIn s.2.1) _
    (((hf _).sub (hg _)).sub hh.comp_orientedBoundary) fun s ↦ ?_
  have key : L.orientedBoundary R n ∘ₗ (orientedComponent f (n + 1) -
      orientedComponent g (n + 1) - h ∘ₗ K.orientedBoundary R n) = 0 := by
    rw [LinearMap.comp_sub, LinearMap.comp_sub, orientedBoundary_comp_orientedComponent,
      orientedBoundary_comp_orientedComponent, hh', LinearMap.sub_comp]
    exact sub_self (G := (K.facesOfDim (n + 1) →₀ R) →ₗ[R] (L.facesOfDim n →₀ R))
      _
  exact LinearMap.congr_fun key _

/-- The invariant of the inductive construction of a chain homotopy in degree `n`. -/
def IsGoodHomotopy (n : ℕ) (h : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim (n + 1) →₀ R)) :
    Prop :=
  Φ.Carries h ∧ L.orientedBoundary R n ∘ₗ h ∘ₗ K.orientedBoundary R n =
    (orientedComponent f n - orientedComponent g n) ∘ₗ K.orientedBoundary R n

/-- The inductive step of the construction of a chain homotopy. -/
noncomputable def homotopyStep {n : ℕ} (h : {h // Φ.IsGoodHomotopy (f := f) (g := g) n h}) :
    {h' // Φ.IsGoodHomotopy (f := f) (g := g) (n + 1) h'} :=
  ⟨_, (Φ.exists_homotopy_succ hf hg h.2.1 h.2.2).choose_spec.1, by
    rw [← LinearMap.comp_assoc, (Φ.exists_homotopy_succ hf hg h.2.1 h.2.2).choose_spec.2,
      LinearMap.sub_comp, LinearMap.comp_assoc, orientedBoundary_comp_orientedBoundary',
      LinearMap.comp_zero]
    exact sub_zero (G := (K.facesOfDim (n + 2) →₀ R) →ₗ[R] (L.facesOfDim (n + 1) →₀ R)) _⟩

/-- The components `Cₙ(K) → Cₙ₊₁(L)` of the chain homotopy between two carried chain maps. -/
noncomputable def homotopyAux : (n : ℕ) → {h // Φ.IsGoodHomotopy (f := f) (g := g) n h}
  | 0 => ⟨_, (Φ.exists_homotopy_zero hf hg hfa hga).choose_spec.1, by
      rw [← LinearMap.comp_assoc, (Φ.exists_homotopy_zero hf hg hfa hga).choose_spec.2]⟩
  | n + 1 => Φ.homotopyStep hf hg (homotopyAux n)

theorem homotopyAux_zero :
    L.orientedBoundary R 0 ∘ₗ (Φ.homotopyAux hf hg hfa hga 0).1 =
      orientedComponent f 0 - orientedComponent g 0 :=
  (Φ.exists_homotopy_zero hf hg hfa hga).choose_spec.2

theorem homotopyAux_succ (n : ℕ) :
    L.orientedBoundary R (n + 1) ∘ₗ (Φ.homotopyAux hf hg hfa hga (n + 1)).1 =
      orientedComponent f (n + 1) - orientedComponent g (n + 1) -
        (Φ.homotopyAux hf hg hfa hga n).1 ∘ₗ K.orientedBoundary R n :=
  (Φ.exists_homotopy_succ hf hg (Φ.homotopyAux hf hg hfa hga n).2.1
    (Φ.homotopyAux hf hg hfa hga n).2.2).choose_spec.2

/-- **Acyclic carrier theorem, uniqueness**: two augmentation-preserving chain maps carried by
the same acyclic carrier are chain homotopic. -/
noncomputable def homotopy : Homotopy f g :=
  Homotopy.equivSubZero.symm ((Homotopy.ofEq (by
    ext n : 1
    cases n with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
        (fun l hl ↦ by simp at hl)]
      refine ModuleCat.hom_ext ?_
      change orientedComponent f 0 - orientedComponent g 0 =
        L.orientedBoundary R 0 ∘ₗ (Φ.homotopyAux hf hg hfa hga 0).1
      exact (Φ.homotopyAux_zero hf hg hfa hga).symm
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)
        (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
      refine ModuleCat.hom_ext ?_
      change orientedComponent f (n + 1) - orientedComponent g (n + 1) =
        (Φ.homotopyAux hf hg hfa hga n).1 ∘ₗ K.orientedBoundary R n +
          L.orientedBoundary R (n + 1) ∘ₗ (Φ.homotopyAux hf hg hfa hga (n + 1)).1
      rw [Φ.homotopyAux_succ hf hg hfa hga n]
      abel)).trans
    (Homotopy.nullHomotopy' fun i j (r : (ComplexShape.down ℕ).Rel j i) ↦
      ModuleCat.ofHom (Φ.homotopyAux hf hg hfa hga i).1 ≫
        eqToHom (congrArg (L.orientedChainComplex R).X (r : i + 1 = j))))

end Homotopy

section Comp

variable {M : Type u} [LinearOrder M] {K' : PreAbstractSimplicialComplex M}

omit [LinearOrder ι] in
variable {Φ} in
/-- A composite of carried maps is carried by any carrier that contains the carriers of the
second map on the carriers of the first. -/
theorem Carries.comp {Ψ : AcyclicCarrier R L K'} {Θ : AcyclicCarrier R K K'} {n m p : ℕ}
    {f : (K.facesOfDim n →₀ R) →ₗ[R] (L.facesOfDim m →₀ R)}
    {g : (L.facesOfDim m →₀ R) →ₗ[R] (K'.facesOfDim p →₀ R)} (hf : Φ.Carries f)
    (hg : Ψ.Carries g) (h : ∀ s ∈ K, ∀ t ∈ L, t ∈ Φ s → Ψ t ≤ Θ s) : Θ.Carries (g ∘ₗ f) :=
  fun s ↦ hg.apply_mem fun t ht ↦ h s.1 s.2.1 t.1 t.2.1 (hf s ht)

/-- The identity is carried by any carrier `Θ` with `s ∈ Θ s`. -/
theorem carries_id {Θ : AcyclicCarrier R K K} (h : ∀ s ∈ K, s ∈ Θ s) (n : ℕ) :
    Θ.Carries (orientedComponent (𝟙 (K.orientedChainComplex R)) n) :=
  fun s ↦ single_mem_chainsIn R (h s.1 s.2.1) 1

end Comp

/-- **Acyclic carriers give chain homotopy equivalences.** Given carriers `Φ : K → L` and
`Ψ : L → K`, and acyclic carriers `ΘK` on `K` and `ΘL` on `L` that carry both the identity and
the composites, the oriented chain complexes of `K` and `L` are chain homotopy equivalent. -/
noncomputable def homotopyEquiv (Φ : AcyclicCarrier R K L) (Ψ : AcyclicCarrier R L K)
    (ΘK : AcyclicCarrier R K K) (ΘL : AcyclicCarrier R L L) (hK : ∀ s ∈ K, s ∈ ΘK s)
    (hL : ∀ t ∈ L, t ∈ ΘL t) (hKc : ∀ s ∈ K, ∀ t ∈ L, t ∈ Φ s → Ψ t ≤ ΘK s)
    (hLc : ∀ t ∈ L, ∀ s ∈ K, s ∈ Ψ t → Φ s ≤ ΘL t) :
    HomotopyEquiv (K.orientedChainComplex R) (L.orientedChainComplex R) where
  hom := Φ.chainMap
  inv := Ψ.chainMap
  homotopyHomInvId := ΘK.homotopy (f := Φ.chainMap ≫ Ψ.chainMap) (g := 𝟙 _)
    (fun n ↦ (Φ.carries_chainMap n).comp (Ψ.carries_chainMap n) hKc) (carries_id hK)
    (by
      change K.augmentation R ∘ₗ (orientedComponent Ψ.chainMap 0 ∘ₗ
        orientedComponent Φ.chainMap 0) = _
      rw [← LinearMap.comp_assoc, Ψ.augmentation_comp_chainMap, Φ.augmentation_comp_chainMap])
    (LinearMap.comp_id _)
  homotopyInvHomId := ΘL.homotopy (f := Ψ.chainMap ≫ Φ.chainMap) (g := 𝟙 _)
    (fun n ↦ (Ψ.carries_chainMap n).comp (Φ.carries_chainMap n) hLc) (carries_id hL)
    (by
      change L.augmentation R ∘ₗ (orientedComponent Φ.chainMap 0 ∘ₗ
        orientedComponent Ψ.chainMap 0) = _
      rw [← LinearMap.comp_assoc, Φ.augmentation_comp_chainMap, Ψ.augmentation_comp_chainMap])
    (LinearMap.comp_id _)

/-- Acyclic carriers in both directions, whose composites are carried by acyclic carriers
containing the identity, give isomorphic simplicial homology. -/
noncomputable def homologyIso (Φ : AcyclicCarrier R K L) (Ψ : AcyclicCarrier R L K)
    (ΘK : AcyclicCarrier R K K) (ΘL : AcyclicCarrier R L L) (hK : ∀ s ∈ K, s ∈ ΘK s)
    (hL : ∀ t ∈ L, t ∈ ΘL t) (hKc : ∀ s ∈ K, ∀ t ∈ L, t ∈ Φ s → Ψ t ≤ ΘK s)
    (hLc : ∀ t ∈ L, ∀ s ∈ K, s ∈ Ψ t → Φ s ≤ ΘL t) (n : ℕ) :
    K.homology (ModuleCat.of R R) n ≅ L.homology (ModuleCat.of R R) n :=
  K.homologyIsoOriented R n ≪≫
    (homotopyEquiv Φ Ψ ΘK ΘL hK hL hKc hLc).toHomologyIso n ≪≫ (L.homologyIsoOriented R n).symm

end AcyclicCarrier

end PreAbstractSimplicialComplex
