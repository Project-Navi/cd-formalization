# Creative Determinant — Lean 4 Formalization

Formal verification of the existence theory from:

> N. Spence, "The Creative Determinant: Autopoietic Closure as a Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions," 2026.

## What is verified

| Result | File | Dependencies | Track |
|--------|------|-------------|-------|
| Viability threshold (1D) | `CdFormal/Theorems.lean` | Pure algebra | Upstream candidate (deferred) |
| Spectral characterization (1D) | `CdFormal/Theorems.lean` | Pure algebra | Upstream candidate (deferred) |
| Scaling algebraic contradiction | `CdFormal/Theorems.lean` | Pure algebra | Upstream candidate |
| Existence of weak coherent configurations | `CdFormal/Theorems.lean` | `PDEInfra`: linfty_bound, schaefer, fixed_point_nonneg | Paper-specific |
| Existence of nontrivial configurations | `CdFormal/Theorems.lean` | `PDEInfra`: monotone_iteration, fixed_point_nonneg | Paper-specific |
| L∞ bound algebraic core | `artifacts/aristotle/` | Pure algebra | Standalone artifact |
| Scaling uniqueness | `artifacts/aristotle/` | `SemioticOperators` axioms | Standalone artifact |

All definitions (semiotic manifold, BVP, operators, weak coherent configuration) are machine-checked against Mathlib.

## Axiom boundary

The `PDEInfra` typeclass in `CdFormal/Axioms.lean` packages five classical PDE results not yet in Mathlib:

1. **T continuous & compact** — Schauder estimates + Arzelà–Ascoli (placeholder `True`)
2. **L∞ bound** — Maximum principle at interior extremum
3. **Schaefer's fixed-point theorem** — Not in Mathlib ([draft issue](drafts/mathlib_issue_schaefer.md))
4. **Fixed-point nonnegativity** — Maximum principle
5. **Monotone iteration** — Sub/super-solution theory (Amann 1976)

The existence theorems explicitly carry `[PDEInfra bvp solOp]` so the axiom surface is visible to Lean's kernel. Run `#print axioms` in `CdFormal/Verify.lean` to confirm no `sorryAx`.

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
lake build --wfail   # fail on any sorry
```

## Project structure

```
CdFormal/
  Basic.lean       — Definitions (manifold, coefficients, operators, BVP)
  Axioms.lean      — PDEInfra typeclass (explicit axiom surface)
  Theorems.lean    — Proved theorems
  Verify.lean      — #print axioms dashboard
artifacts/
  aristotle/       — Proved outputs from the Aristotle theorem prover
drafts/            — In-progress proof targets and issue drafts
```

## Development Process

**What the author did**: The original equations, proof strategy, and formalization
architecture — choosing to axiomatize via `PDEInfra`, identifying which five
classical PDE results to package, designing the typeclass hierarchy, and structuring
the Schaefer → L∞ bound → existence → sub/super-solution → nontriviality proof
chain — are the core intellectual contribution. These are mathematical architecture
decisions that require understanding where the real difficulty lies. The underlying
equations and theory are documented in the [paper](../paper/creative_determinant.pdf).

**What AI tools did**: Claude Opus assisted with Lean 4 syntax, Mathlib API
navigation, and proof term synthesis. Aristotle (Harmonic.fun) automated proving
of standalone algebraic lemmas. These roles are analogous to `omega`, `aesop`, and
other proof automation — the strategy is human, the term-level search is machine-assisted.

**Verification**: The final arbiter is the Lean compiler, not trust:
```bash
lake build --wfail   # type-checks or it doesn't — zero sorry
```
Run `#print axioms` in `CdFormal/Verify.lean` to confirm the axiom surface.
Every assumption is explicit in `PDEInfra`. Nothing is hidden.

## License

Copyright 2026 Nelson Spence. Licensed under [Apache 2.0](LICENSE).
