/-
Copyright (c) 2026 Mikael Vejdemo-Johansson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikael Vejdemo-Johansson
-/
module

public import MathlibSimplicial.TDA.NerveLemma
public import MathlibSimplicial.TDA.Persistence

/-!
# The persistent nerve lemma

A *filtered cover* of a filtration `F : T →o PreAbstractSimplicialComplex ι` is a family of
subcomplexes `U t i ≤ F t`, growing with `t`, such that for each `t` the `U t i` cover `F t`.
Its nerves form a filtration `nerveFiltration U` of complexes on the index type `I`.

If every nonempty intersection `⋂_{i ∈ J} U t i` is acyclic, the nerve lemma gives isomorphisms
`Hₙ(F t) ≅ Hₙ(N(U t))` for each `t`. `nerveLemma_naturality` shows that these commute with the
maps induced by `s ≤ t`, so they assemble into an isomorphism of persistence modules
(`persistentNerveLemma`). In TDA this is what justifies computing the persistent homology of a
filtered space from the nerve of a good cover, e.g. Čech persistence from a cover by balls.

The proof of naturality compares the two nerve isomorphisms with a third acyclic carrier
(`nerveComparisonCarrier`), sending a chain of faces of `K` to the chains of faces of the larger
nerve lying above the index set of its top face, and uses the naturality of the acyclic carrier
isomorphism (`AcyclicCarrier.homologyIso_naturality`).

## Main declarations

* `PreAbstractSimplicialComplex.nerveFiltration`: the filtration by nerves of a filtered cover.
* `PreAbstractSimplicialComplex.persistentNerveLemma`: the persistent homology of `F` is
  isomorphic to that of the nerve filtration.
-/

@[expose] public section

open CategoryTheory

universe u

namespace PreAbstractSimplicialComplex

variable {ι I : Type u} [LinearOrder ι] [LinearOrder I] [Fintype I] {T : Type*} [Preorder T]

/-- The nerve filtration of a filtered cover: `t ↦ N(U t)`. -/
def nerveFiltration (U : T →o (I → PreAbstractSimplicialComplex ι)) :
    T →o PreAbstractSimplicialComplex I :=
  ⟨fun t ↦ coverNerve (U t), fun _ _ h ↦ coverNerve_mono (U.monotone h)⟩

variable {F : T →o PreAbstractSimplicialComplex ι} {U : T →o (I → PreAbstractSimplicialComplex ι)}
  (hle : ∀ t i, U t i ≤ F t) (hcov : ∀ t, ∀ s ∈ F t, ∃ i, s ∈ U t i) (R : Type u) [Ring R]
  (hacyc : ∀ t, ∀ J ∈ coverNerve (U t), IsAcyclicIn R (coverInter (U t) J) (coverInter (U t) J))

/-- **The persistent nerve lemma.** For a filtered cover of a filtration `F` whose nonempty
intersections are acyclic at every filtration value, the persistent homology of `F` is
isomorphic, as a persistence module, to the persistent homology of the nerve filtration. -/
noncomputable def persistentNerveLemma (n : ℕ) :
    persistentHomology (ModuleCat.of R R) F n ≅
      persistentHomology (ModuleCat.of R R) (nerveFiltration U) n :=
  NatIso.ofComponents (fun t ↦ nerveLemma (hle t) (hcov t) R (hacyc t) n) fun {s t} f ↦
    (nerveLemma_naturality (U.monotone (leOfHom f)) (F.monotone (leOfHom f)) (hle s) (hcov s)
      (hle t) (hcov t) R (hacyc s) (hacyc t) n).symm

end PreAbstractSimplicialComplex
