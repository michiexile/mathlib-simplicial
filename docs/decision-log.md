# Decision log

Major decisions and steps, newest last. Each entry: what was decided, the alternatives, and why.
"Mikael" marks decisions he made; "Claude" marks decisions made while working autonomously, for
review after the fact. To reverse one, say so and it will be redone.

## 2026-11-26

### Scope and plan (Mikael)
- Follow the survey's six-step roadmap in order (see `README.md`). Chains *and* cochains are both
  first-class, each with a bridge to Mathlib's `SSet` side. The nerve lemma plans include the
  persistent nerve lemma. Topological combinatorics (Sperner, Tucker, Kneser) is on hold.
- Build in this repo first, in Mathlib style, and upstream later.

### Build on Cunningham–Zach–Friedl by porting, not as a dependency (Claude)
- **Alternatives:** a Lake dependency on `not-gary/pachner`; vendoring its files unchanged.
- **Why:** it pins Lean 4.21 and a mid-2025 Mathlib, older than the simplicial-set homology that
  step 3 needs, and it defines a top-level `AbstractSimplicialComplex` that clashes with Mathlib's.
  Its definition is the same as Mathlib's `PreAbstractSimplicialComplex`, so results carry over.

### Toolchain: Lean and Mathlib `v4.36.0`, Mathlib layout, module system, `--wfail` CI (Claude)
- Files mirror Mathlib paths and declarations use Mathlib namespaces, so upstreaming is mostly
  copying. CI fails on any warning, which keeps `sorry` off `main`.

### Build the API on `PreAbstractSimplicialComplex` (Mikael, from Claude's recommendation)
- **Alternatives:** `AbstractSimplicialComplex` (every element of `ι` is a vertex); both in parallel.
- **Why:** subcomplexes, links, stars and lower-star filtrations change the vertex set, which
  only the Pre version allows without changing the vertex type.

### Relicense from MIT to Apache 2.0 (Mikael)
- **Why:** Mathlib only accepts Apache 2.0 code. CZF is Apache 2.0 too, so their code can be
  ported with their notices kept.

### Restate CZF definitions with new proofs instead of copying code (Claude)
- **Alternative:** copy CZF files and patch them for current Mathlib.
- **Why:** CZF proofs are long step-by-step tactic scripts; against current Mathlib most become
  one to twenty lines (e.g. `link_link`, CZF's Lemma 3.5, went from about 60 lines to about 20).
  Restated files carry our header and cite the CZF source file in their docstring.

### Simplicial maps: face condition without `DecidableEq` (Claude)
- The field is `∃ t ∈ L, ↑t = f '' s` instead of `s.image f ∈ L`, so no decidability instance
  lives in the structure or the category. `image_mem` and `mk'` give the `Finset.image` form.

### The category of complexes uses `AbstractSimplicialComplex` (Claude)
- **Alternative:** a category on `PreAbstractSimplicialComplex`.
- **Why:** maps are total functions on the vertex type, so on a Pre complex with non-vertex
  elements, maps agreeing on all vertices would still be distinct morphisms (wrong hom-sets).

### Cone on `Option ι`; join on `ι ⊕ κ` (Claude)
- **Alternative:** CZF's approach of embedding both complexes in one product type `E × 𝕜` with
  0/1 tags, and defining the cone as a join with a point.
- **Why:** the sum and option types keep the vertex sets apart by construction, so no disjointness
  bookkeeping is needed. Associativity and commutativity of the join should become statements
  about the equivalences `(ι ⊕ κ) ⊕ μ ≃ ι ⊕ (κ ⊕ μ)` and `ι ⊕ κ ≃ κ ⊕ ι` (not proved yet;
  needs simplicial isomorphisms). The cone is not yet identified with the join with a point.

### Dimension valued in `WithBot ℕ∞` (Claude)
- **Alternative:** CZF's `ℤ`-valued dimension, defined only for finite complexes.
- **Why:** `⊥` covers the empty complex (dimension −1) and `⊤` the infinite-dimensional case, so
  `dim` needs no finiteness assumption.

### `closedStar` rather than `star` (Claude)
- **Why:** `star` is already Mathlib's `Star` typeclass operation.

## 2026-11-27

### Work autonomously and keep this log (Mikael)
- Keep moving through the roadmap without waiting for each PR to be reviewed; open separate
  branches only for work that belongs in its own PR (stacked on unmerged work when needed).
  Record major decisions here instead of asking.

### Step 2: clique and order complexes (Claude)
- Branch `claude/step2-clique-order`, stacked on PR #3.
- `SimpleGraph.cliqueComplex` is a `PreAbstractSimplicialComplex` (its vertex set is all of `V`
  anyway). The 1-skeleton `K.graph` is built with Mathlib's `SimpleGraph.fromRel`.
- `IsFlag K` quantifies only over finsets of *vertices*, so that subcomplexes with fewer vertices
  can still be flag; `IsFlag.eq_cliqueComplex` needs the extra hypothesis `K.vertices = univ`.
- `orderComplex α` needs only `[LE α]`; chains use Mathlib's `IsChain (· ≤ ·)`. It is proved equal
  to the clique complex of a new `SimpleGraph.comparability α` rather than defined that way, so
  the chain description is the definitional one.
- The barycentric subdivision is defined as the order complex of the face poset
  `{s // s ∈ K}` (an `abbrev`, so it inherits the subset order). Proving that it is homeomorphic
  to, or has the same homology as, `K` is deferred until homology exists (step 3 onwards).
- Not done: comparing the order complex with the nondegenerate simplices of `nerve α`. That is
  part of the step 3 bridge.
