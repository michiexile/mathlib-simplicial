# CLAUDE.md

Conventions for working in this repository. See `README.md` for the roadmap and build steps.

## Goals and scope

- Simplicial (co)homology of abstract simplicial complexes in Lean 4 on Mathlib, aimed at applied
  and combinatorial topology / TDA. Simplicial homology as an approximation to singular homology is
  not a focus (connecting theorems are fine).
- Follow the README roadmap in order. Topological combinatorics (Sperner, Tucker, Kneser) is on
  hold: don't start it unless Mikael reopens it.
- Chains **and** cochains are both first-class, each with a bridge to Mathlib's `SSet` side.
- Build here first; upstream to Mathlib later. Don't open Mathlib PRs unless asked.
- Mikael is learning Lean through this project: explain Lean and Mathlib idioms in PR
  descriptions and reports, and keep module docstrings explanatory.

## Lean and Mathlib conventions

- Write everything in Mathlib style so it can be upstreamed with minimal changes:
  - Files mirror Mathlib paths under `MathlibSimplicial/`.
  - Declarations go in Mathlib's namespaces (e.g. `PreAbstractSimplicialComplex.vertices`), not a
    project namespace.
  - Naming: `UpperCamelCase` for types and structures, `lowerCamelCase` for defs, `snake_case` for
    theorems, following https://leanprover-community.github.io/contribute/naming.html.
  - Every file has a Mathlib-style copyright header ("Released under Apache 2.0 license as
    described in the file LICENSE."; the repo is Apache 2.0, like Mathlib) and a `/-! ... -/`
    module docstring with a "Main declarations" list; every `def` and `structure` has a docstring.
  - Every file uses Lean's module system: `module` after the header, `public import`, and
    `@[expose] public section` around definitions whose bodies other files (or `decide`) must
    unfold. Mathlib is written this way, and Lake warns otherwise.
  - Lines at most 100 characters. `autoImplicit` is off (set in `lakefile.toml`).
- Build the API on `PreAbstractSimplicialComplex` (vertex set may be a proper subset of `ι`), and
  derive `AbstractSimplicialComplex` results through `toPreAbstractSimplicialComplex`. (Decided by
  Mikael, 2026-11-26.)
- Dimension convention: a face `s` has dimension `s.card - 1`.
- New files must be added to `MathlibSimplicial.lean` (kept sorted).
- No `sorry` on `main`: CI builds with `--wfail`, so any warning fails the build.

## Porting from Cunningham–Zach–Friedl (not-gary/pachner)

- Port, don't depend: the library is on Lean 4.21 and defines a clashing `AbstractSimplicialComplex`.
  Its `AbstractSimplicialComplex` corresponds to Mathlib's `PreAbstractSimplicialComplex`.
- Keep the original copyright header (Apache 2.0, Cunningham, Zach, Friedl) on ported files and
  add a line naming the source file and commit (`df9ad40`).
- Adapt to current Mathlib API and style while porting (e.g. `s ∈ K` via `SetLike` instead of
  `s ∈ K.faces`).

## Toolchain

- Lean and Mathlib are pinned to the same release tag (`lean-toolchain`, `rev` in
  `lakefile.toml`). Bump both together, then `lake update` and `lake exe cache get`.
- Build with `lake build`. Run `lake exe cache get` first or Lake will compile Mathlib from source.
