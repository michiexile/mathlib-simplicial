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

### Step 3: bridge to simplicial sets (Claude)
- Branch `claude/step3-sset-bridge`, stacked on step 2.
- **Model:** for a linear order on `ι`, `K.toSSet` is the subcomplex of Mathlib's `nerve ι` made of
  the monotone maps `Fin (n + 1) → ι` whose image is a face. Its nondegenerate `n`-simplices are
  the strictly monotone ones, and they correspond to the `n`-dimensional faces
  (`nonDegenerateEquiv`).
  - **Alternative:** the *ordered* simplicial set (all maps `Fin (n + 1) → ι` whose image is a
    face, with no order needed). It is functorial in every simplicial map, but it has many more
    nondegenerate simplices, and its homology agrees with the usual one only after a theorem.
  - **Why:** the nerve model reuses Mathlib's nerve API and matches the textbook complex. It is
    functorial in inclusions, which is all that filtrations and persistence need. Functoriality
    in arbitrary simplicial maps is postponed; the plan is to get it through the ordered model or
    through the concrete chain complex of step 5.
- **Homology** of `K` is defined as `K.toSSet.homology R n`, with no new chain complex. It is a
  functor from the poset `PreAbstractSimplicialComplex ι` to `C`.
- **Cochains:** Mathlib has no cohomology of simplicial sets, so this repo adds
  `SSet.cochainComplex X R M`. It is the chain complex, passed to `Cᵒᵖ`, with
  `preadditiveYoneda.obj M = Hom(-, M)` applied in each degree. The result lives in
  `AddCommGrpCat` with shape `(ComplexShape.down ℕ).symm`. Cohomology of `K` is that of
  `K.toSSet`, as a functor `(PreAbstractSimplicialComplex ι)ᵒᵖ ⥤ AddCommGrpCat`.
  - **Alternatives:** a `k`-linear version using `linearYoneda`, which needs a `Linear` instance;
    or cochains defined directly as functions on faces.
  - **Why:** it works for any preadditive coefficient category and is functorial for free. The
    concrete "functions on faces" description belongs with the step 5 comparison.

### Step 4: first computations (Claude)
- Branch `claude/step4-computations`, stacked on step 3.
- **Acyclicity through extra degeneracies.** Mathlib proves that an augmented simplicial object
  with an extra degeneracy has a contractible alternating face map complex. A new file,
  `SimplicialSet/Homology/ExtraDegeneracy.lean`, turns that into `C•(X; R) ≃ₕ R[0]` for any
  simplicial set with an extra degeneracy. For a cone, the extra degeneracy puts the apex in
  front of each simplex.
  - **Alternatives:** a chain homotopy written by hand on the concrete chain complex (step 5); or
    a homotopy `Δ[1] ⊗ K.toSSet → K.toSSet` with Mathlib's homotopy invariance.
  - **Why:** the extra degeneracy is a few one-line simplicial identities, and Mathlib already
    supplies the chain homotopy.
- **Limitation: the apex must come first in the order on `ι`.** Putting `v` in front of a
  monotone list only gives a monotone list when `v` is minimal. This covers simplices
  (apex `s.min'`) and `L.cone`, with `Option ι` ordered as `WithBot ι`. It does not cover a
  cone point in the middle of the order. Removing the restriction needs `K.toSSet` to be
  independent of the order up to homology. That is planned together with simplicial-map
  functoriality (see the step 3 entry).
- **`H₀`** is identified with `⨁ R` over the connected components of `K.vertexGraph`, the
  1-skeleton graph induced on `K.vertices`. Using the induced graph, not `K.graph` on all of `ι`,
  keeps non-vertices of a `PreAbstractSimplicialComplex` from showing up as extra components.
- **Vanishing above the dimension** comes from Mathlib's `HasDimensionLT` and the normalized
  chain complex. It is stated both with a bound on the number of vertices per face and with
  `dim`.
- **Deferred within step 4:** `H(∂Δⁿ) ≅ H(Sⁿ⁻¹)`. It needs the long exact sequence of the pair
  `(Δⁿ, ∂Δⁿ)` and the relative homology of that pair. Mathlib has relative chain complexes for
  simplicial-set pairs; the plan is to do this next, as a separate PR.

### Step 4, continued: spheres via normalized chains (Claude)
- Branch `claude/step4-spheres`, stacked on step 4.
- **Route:** the normalized chain complex of `K.toSSet` is the textbook complex
  `Nₙ = ⨁_{n-faces} R` (`normalizedChainComplexXIso`). Two complexes with the same faces up to
  `k + 2` vertices have the same `Hₖ` (`isIso_homologyMap_of_faces`). So `∂Δ` agrees with the
  acyclic `Δ` below the top degree. In the top degree, `Hₙ₊₁(∂Δ)` = cycles of `Δ` = image of the
  top face, which is `R`.
  - **Alternative:** the long exact sequence of the pair `(Δ, ∂Δ)` with Mathlib's relative
    homology `SSetPair.homology`.
  - **Why:** that route needs the relative homology of `(Δ, ∂Δ)`, and Mathlib has no normalized
    relative complex to compute it. The truncation argument uses only existing API. The
    skeleton comparison lemma it produces is also useful in its own right, e.g. for cellular
    arguments and Euler–Poincaré.
- The top-degree isomorphism assumes `[Balanced C]` (true in any abelian category, such as
  `ModuleCat k`). It needs "mono and epi implies iso" to identify cycles with the image of the
  top face.
- The `0`-sphere (`s` with two elements) is not a separate theorem. `homology₀Iso` covers it,
  with two components.
- The explicit boundary formula on faces (the rest of step 5's "concrete chains") is still to do.

### Step 5: concrete chains and Euler–Poincaré (Claude)
- Branch `claude/step5-euler-poincare`, stacked on the step 4 spheres branch.
- **The "oriented chain complex" is the normalized complex of `K.toSSet`**, not a new
  definition. Each face gets a summand `faceChain t`, and `faceChain_d` gives the textbook
  boundary formula, with vertices in increasing order.
  - **Alternative:** a separate complex built from `Finsupp` on faces, with its own boundary map
    and a comparison isomorphism.
  - **Why:** a second definition would need a comparison theorem and would duplicate
    functoriality. The normalized complex already has both, and it is a coproduct over faces,
    so it is concrete enough. A `Finsupp`/matrix presentation for computation can be added later
    if decidable computations need it.
- **Euler–Poincaré for chain complexes** (`Algebra/Homology/EulerPoincare.lean`) is proved here
  in finite-sum form for `ℕ`-graded complexes of vector spaces, by rank–nullity and a
  telescoping sum. Mathlib defines `eulerChar` and `homologyEulerChar` but, at the pinned version,
  has not proved that they agree (Mathlib PR #29713 was expected to). Ours is a candidate to
  upstream or to replace with Mathlib's once it lands.
- `betti K k n := finrank k (Hₙ(K; ModuleCat.of k k))`. `k` must live in the same universe as
  the vertex type, since `ModuleCat.{u} k` needs `u`-small coproducts.

### Step 6a: Vietoris–Rips, Čech, filtrations and persistence (Claude)
- Branch `claude/step6-rips-persistence`, stacked on step 5.
- **Point clouds are families `p : ι → M` in a pseudometric space**, not subsets of `M`.
  - **Alternative:** complexes on a `Finset M` or `Set M`.
  - **Why:** indexing by `ι` allows repeated points and lets `ι` carry the vertex order that
    homology needs (`LinearOrder ι`), independently of `M`.
- **Closed balls (`≤ r`)** throughout. Open-ball conventions differ only at bar endpoints.
- **Rips is the clique complex of the `r`-graph**, so flagness comes for free from step 2.
- `VR(r) ⊆ Čech(r)` needs `0 ≤ r` (for `r < 0` Rips still has vertices, Čech is empty), so the
  filtrations are indexed by `ℝ≥0`.
- **Filtrations are `T →o PreAbstractSimplicialComplex ι`** for any preorder `T`; persistent
  homology is `F.monotone.functor ⋙ homologyFunctor ι R n`, a functor `T ⥤ C`.
  - **Alternative:** a bespoke `PersistenceModule` structure (vector spaces plus maps).
  - **Why:** a functor from the poset is the standard categorical definition, it comes with
    functoriality for free, and it works for any coefficient category.
- **Interleavings** are along two monotone maps `α β : T →o T` with `t ≤ α t`, `t ≤ β t`, not
  only shifts by `ε`. This covers the multiplicative Čech–Rips interleaving (`r ↦ 2r`), which an
  additive `ε`-interleaving cannot express on `ℝ≥0`. Interleaved filtrations give interleaved
  persistent homology (`Interleaving.ofLE`).
- **Upstreaming note:** `Interleaving` and `doubling` live in the `PreAbstractSimplicialComplex`
  namespace for now, although interleavings make sense for any persistence modules. They should
  move to a general namespace when upstreamed, once Mathlib has persistence modules.
- Not done here: the interleaving distance and stability; the barcode decomposition.

### Step 6b: oriented chains and the acyclic carrier theorem (Claude)
- Branch `claude/step6-acyclic-carriers`, stacked on step 6a.
- **Why this detour before the nerve lemma:** Mathlib has no spectral sequences or Mayer–Vietoris
  machinery for simplicial complexes that would give the nerve lemma directly. The classical
  elementary proof uses acyclic carriers (and barycentric subdivision). The same tool also
  removes two limitations recorded earlier: cone acyclicity needed a minimal apex, and
  functoriality was only for inclusions/monotone maps. So it is the best next investment.
- **Oriented chains as `Finsupp`** (`K.facesOfDim n →₀ R`, over a ring `R`, in
  `ModuleCat R`), defined by transporting the normalized complex along degreewise isomorphisms.
  - **Alternative:** work categorically with the normalized complex (coproducts in a general
    category `C`) and phrase "carried by" as factoring through subcomplex inclusions, lifting
    via projectivity of `R`.
  - **Why:** carriers are about supports of individual chains, which `Finsupp.supported` models
    directly with a large existing API. The general-`C` route needs projectivity and much more
    degree bookkeeping. The `Finsupp` complex is also the natural basis for later explicit
    computations. Results are stated over `ModuleCat R` for a ring `R`, which covers fields
    (TDA) and `ℤ`.
- **Acyclicity is concrete** (`IsAcyclicIn R L M`: a vertex exists, and every reduced cycle of
  `L` supported on `M` bounds a chain supported on `M`), relative to an ambient `L` so that
  carriers never have to move chains between different complexes. For `M ≤ L` it agrees with
  vanishing reduced homology of `M`; both directions are proved.
- **The inductive constructions** carry their invariants in subtypes
  (`{f // IsGood n f}`), defined by structural recursion. Mathlib's `ChainComplex.mkHom` and
  `Homotopy.mkInductive` don't allow extra invariants in the recursion, so they could not be
  used. The homotopy is assembled with `Homotopy.nullHomotopy'`.
- **Cones with any apex are acyclic**, via the carrier `s ↦ Δ(s ∪ {v})`, which carries both the
  identity and the collapse to the apex. Only full simplices use the older, order-dependent
  extra-degeneracy result. This supersedes the "apex must be minimal" limitation for
  coefficients in `ModuleCat R`.

### Step 6c: barycentric subdivision and the nerve lemma (Claude)
- Branch `claude/step6-nerve-lemma`, stacked on step 6b.
- **Proof route: acyclic carriers between barycentric subdivisions** (Björner's proof).
  - **Alternatives:** Mayer–Vietoris induction on the number of cover elements (needs a natural
    comparison map with the nerve, which does not exist at chain level without subdivision); a
    double complex / spectral sequence argument (no usable infrastructure in Mathlib).
  - **Why:** `s ↦ {i | s ∈ U i}` reverses inclusions but preserves chains, so it becomes
    carrier-compatible after subdividing. Everything reduces to the acyclic carrier theorem,
    already in place.
- **Vertex type of `sd K` is `Colex (Finset ι)`**, not the face poset. Homology needs a linear
  order on vertices; colex is a linear order extending inclusion, so "largest/smallest element
  of a chain" can be taken with `max'`/`min'`. The existing order-theoretic `subdivision`
  (order complex of the face poset) is kept; relating the two is routine if ever needed.
- A `DecidableEq` instance diamond on `Colex (Finset ι)` (from `LinearOrder` vs. found by
  instance search, not reducibly equal) broke `Finset.mem_insert`. Worked around with
  `Finset.mem_insert_of_decidableEq`, which takes the instance by unification. Worth reporting
  upstream if it persists.
- **Carrier monotonicity now quantifies only over faces** (`s ∈ K → t ∈ K → s ⊆ t → …`).
  Previously any `s ⊆ t` was allowed, which failed for carriers that are only sensible on
  nonempty sets (like `S ↦ sd(⋂_{i : ⋃S ∈ U i} U i)`).
- **Hypotheses of the nerve lemma:** finite index type (`Fintype I`, so that
  `{i | s ∈ U i}` is a `Finset`), linear orders on `ι` and `I`, coefficients in a ring, and
  concrete acyclicity `IsAcyclicIn R (⋂_J U) (⋂_J U)` of nonempty intersections. A version
  with homological hypotheses is a thin wrapper (positive degrees via
  `exists_boundary_of_isZero_homology`, degree 0 via connectivity) and can be added when needed.
- The conclusion is an isomorphism of homology for each degree. The chain-level statement (a
  chain homotopy equivalence) is also available through `AcyclicCarrier.homotopyEquiv`.
