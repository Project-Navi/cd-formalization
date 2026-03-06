# Creative Determinant — Lean 4 Formalization

Formal verification of the existence theory from:

> N. Spence, "The Creative Determinant: Autopoietic Closure as a Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions," 2026.

## What is verified

Eleven theorems proved with zero `sorry`, organized in four dependency tiers:

### Tier 1 — Pure algebra (no domain axioms)

| Result | Declaration | File |
|--------|-------------|------|
| Spectral characterization (1D) | `spectral_characterization_1d` | `Theorems` |
| Scaling algebraic contradiction | `scaling_algebraic_contradiction` | `Theorems` |

### Tier 2 — Operator lemmas (from abstract linearity/homogeneity)

| Result | Declaration | File |
|--------|-------------|------|
| Laplacian of zero | `laplacian_zero` | `OperatorLemmas` |
| Laplacian linearity | `laplacian_linear` | `OperatorLemmas` |
| Gradient norm of zero | `gradNorm_zero` | `OperatorLemmas` |

### Tier 3 — Coefficient bounds (from [0,1] field constraints)

| Result | Declaration | File |
|--------|-------------|------|
| a(x) nonneg | `SemioticContext.a_nonneg` | `CoefficientLemmas` |
| a(x) ≤ 1 | `SemioticContext.a_le_one` | `CoefficientLemmas` |
| p − 1 > 0 | `SemioticContext.p_sub_one_pos` | `CoefficientLemmas` |

### Tier 4 — PDE-level results

| Result | Declaration | File | Dependencies |
|--------|-------------|------|--------------|
| Scaling uniqueness (kΦ impossible for k > 1) | `scaling_uniqueness` | `ScalingUniqueness` | `SemioticOperators` axioms |
| Existence of weak coherent configurations | `SemioticBVP.exists_isWeakCoherentConfiguration` | `Theorems` | `PDEInfra` |
| Nontrivial configurations | `SemioticBVP.exists_pos_isWeakCoherentConfiguration` | `Theorems` | `PDEInfra` |

All definitions (semiotic manifold, BVP, operators, weak coherent configuration) are machine-checked against Mathlib.

## Axiom boundary

The `PDEInfra` typeclass in `CdFormal/Axioms.lean` packages five classical PDE results not yet in Mathlib:

| Axiom | Classical source | Mathlib status |
|-------|-----------------|----------------|
| `T_continuous_compact` | Schauder estimates + Arzelà–Ascoli | No Hölder spaces on manifolds (placeholder `True`) |
| `linfty_bound` | Maximum principle (Gilbarg–Trudinger) | No max. principle for manifolds |
| `schaefer` | Schaefer 1955 | Not in Mathlib ([draft issue](drafts/mathlib_issue_schaefer.md)) |
| `fixed_point_nonneg` | Strong maximum principle | No max. principle for manifolds |
| `monotone_iteration` | Amann 1976 | No sub-/super-solution theory |

The existence theorems explicitly carry `[PDEInfra bvp solOp]` so the axiom surface is visible to Lean's kernel. Run `#print axioms` in `CdFormal/Verify.lean` to confirm no `sorryAx` — all theorems depend only on `[propext, Classical.choice, Quot.sound]`.

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
lake build --wfail   # fail on any sorry or warning
```

## Project structure

```
CdFormal/
  Basic.lean            — Definitions (manifold, coefficients, operators, BVP)
  Axioms.lean           — PDEInfra typeclass (explicit axiom surface)
  Theorems.lean         — Existence and algebraic theorems
  OperatorLemmas.lean   — Laplacian/gradient-norm derived properties
  CoefficientLemmas.lean — Bounds from [0,1] field constraints
  ScalingUniqueness.lean — PDE-level scaling impossibility
  Verify.lean           — #print axioms dashboard (13 declarations)
artifacts/
  aristotle/            — Proved outputs from the Aristotle theorem prover
drafts/                 — Community engagement drafts + Lean proof sketches
  zulip_schaefer_post.md, zulip_lt_rpow_self_post.md, mathlib_issue_schaefer.md
  ScalingUniqueness.lean, ScalingUniqueness_v2.lean, ScalingUniqueness_v3.lean
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
