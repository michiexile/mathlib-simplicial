# mathlib-simplicial

Simplicial homology and cohomology of abstract simplicial complexes in Lean 4, built on
[Mathlib](https://github.com/leanprover-community/mathlib4), with an eye to applied and
combinatorial topology (topological data analysis in particular).

Mathlib already has homology of *simplicial sets* (`Mathlib/AlgebraicTopology/SimplicialSet/Homology/`)
and a bare definition of abstract simplicial complexes
(`Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean`), with nothing connecting the two.
This project builds the complex-level API, a bridge to simplicial sets for both chains and
cochains, and the TDA constructions that sit on top. Everything is written in Mathlib style so that
pieces can be upstreamed later.

The background survey and the decisions behind this plan are in the
[survey document](https://claude.ai/artifact/4zmE4hL3nF7RpERR28uKK4).

## Building

You need [elan](https://github.com/leanprover/elan), the Lean version manager. Then:

```sh
git clone https://github.com/michiexile/mathlib-simplicial
cd mathlib-simplicial
lake exe cache get   # download prebuilt Mathlib (a few minutes; skipping this means compiling Mathlib for hours)
lake build           # compile this library
```

`elan` reads `lean-toolchain` and installs the matching Lean version automatically. `lake` is
Lean's build tool; it reads `lakefile.toml` (which pins Mathlib to a release tag) and
`lake-manifest.json` (which pins the exact commit of every dependency).

To work interactively, open the folder in VS Code with the `lean4` extension. Each `.lean` file
then shows the proof state beside the cursor.

To move to a newer Mathlib, change `rev` in `lakefile.toml` and the version in `lean-toolchain`
to the same new tag, then run `lake update` and `lake exe cache get`.

## Layout

Files mirror Mathlib's directory structure, so a file here at
`MathlibSimplicial/AlgebraicTopology/SimplicialComplex/X.lean` would become
`Mathlib/AlgebraicTopology/SimplicialComplex/X.lean` upstream. Declarations live in Mathlib's
namespaces (`PreAbstractSimplicialComplex`, `SimpleGraph`, …) for the same reason.

```
MathlibSimplicial.lean                     root file; imports everything
MathlibSimplicial/
  AlgebraicTopology/SimplicialComplex/
    Faces.lean           vertices, facets, faces by dimension, f-vector, Euler characteristic
    Simplex.lean         full simplex, boundary, skeleta
    Cone.lean            cones (stars, links, joins to follow)
    SimplicialMap.lean   simplicial maps and the category of complexes
    Clique.lean          clique (flag) complex of a graph
    OrderComplex.lean    order complex of a poset, face poset
    ToSSet.lean          the bridge K ↦ K.toSSet
    Homology/
      Basic.lean         homology of K via K.toSSet
      Cochains.lean      cochains, cohomology, and their bridge to K.toSSet
      Computations.lean  H₀, acyclicity of simplices, spheres
      Chains.lean        the oriented chain complex and its comparison with K.toSSet
      EulerPoincare.lean Euler–Poincaré formula
  TDA/
    VietorisRips.lean    Vietoris–Rips and Čech complexes
    Persistence.lean     filtrations, persistence modules, persistent homology
    NerveLemma.lean      nerve lemma and persistent nerve lemma
```

Files marked "Status: planned" in their header are placeholders that fix where material will go.

## Roadmap

1. **Basic API** (in progress). Done: faces by dimension, f-vector, vertices, facets
   (`Faces.lean`); full simplex, boundary, skeleta (`Simplex.lean`); simplicial maps and the
   category of complexes (`SimplicialMap.lean`); cones (`Cone.lean`). Still to come: links,
   stars, joins, dimension (from Cunningham–Zach–Friedl, see below).
2. **Clique and order complexes.** The standard sources of complexes in combinatorics and TDA.
3. **Bridge to simplicial sets.** `K.toSSet` as a subcomplex of the nerve of the vertex order,
   with nondegenerate simplices matching faces. Homology of `K` is then Mathlib's homology of
   `K.toSSet`. The cochain side is set up the same way: cochains on `K` with a bridge to cochains
   of `K.toSSet`.
4. **First computations.** `H₀` counts components; simplices are acyclic; the boundary of the
   `n`-simplex has the homology of `Sⁿ⁻¹`.
5. **Concrete chains and Euler–Poincaré.** The textbook oriented chain complex, its comparison
   with the bridged one, and `χ(K) = ∑ (-1)ⁿ fₙ = ∑ (-1)ⁿ βₙ` over a field.
6. **First TDA layer.** Vietoris–Rips complexes, filtrations and persistence modules; then one of
   the barcode structure theorem, the nerve lemma together with the persistent nerve lemma, or
   discrete Morse collapses.

Topological combinatorics (Sperner, Tucker, Kneser) is on hold for now.

## Relation to the Cunningham–Zach–Friedl library

[not-gary/pachner](https://github.com/not-gary/pachner) (Cunningham, Zach, Friedl,
*Formalizing Abstract Simplicial Complexes & Stellar Subdivisions in Lean*, ITP 2026) has about
14,000 lines of complex-level API: links, stars, cones, joins, simplicial maps, stellar
subdivisions. We build on it, but by porting rather than as a Lake dependency, because:

* it is pinned to Lean 4.21 and a mid-2025 Mathlib, which predates Mathlib's simplicial-set
  homology that step 3 needs; and
* it defines its own top-level `AbstractSimplicialComplex`, which clashes with the one Mathlib
  has since added.

Its definition (nonempty faces, downward closed, vertex set a subset of the vertex type) is the
same as Mathlib's `PreAbstractSimplicialComplex`, so results port across with modest changes.
Ported files keep the original copyright notice (Apache 2.0) and say where they came from.

## License

Apache 2.0, see `LICENSE`: the same license as Mathlib, so files can be upstreamed unchanged.
Code ported from not-gary/pachner is also Apache 2.0 and keeps its original copyright notice.
