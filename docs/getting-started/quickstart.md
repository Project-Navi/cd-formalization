# Quickstart

Build and verify the Creative Determinant formalization in Lean 4.

---

## Prerequisites

- **Lean 4** (v4.28.0) --- installed via [elan](https://github.com/leanprover/elan)
- **Mathlib** (v4.28.0) --- fetched automatically by Lake

```bash
# Install elan (Lean version manager)
curl https://elan-init.netlify.app/elan-init.sh -sSf | sh
```

---

## Build

```bash
git clone https://github.com/Project-Navi/cd-formalization.git
cd cd-formalization
lake build
```

First build fetches Mathlib and compiles all dependencies. This takes several minutes. Subsequent builds are incremental.

---

## Verify

The primary verification command fails on any warning, including `sorry`:

```bash
lake build --wfail
```

If this succeeds, every theorem in the formalization is fully proved --- no gaps, no trust-me markers.

To inspect the axiom dependency surface:

```bash
lake build CdFormal.Verify
```

This runs `#print axioms` on all 15 theorems plus definitions. Confirm that **no `sorryAx` appears** --- every theorem depends only on:

- Core Lean axioms: `propext`, `Classical.choice`, `Quot.sound`
- `SemioticOperators` field axioms (linearity, homogeneity)
- `SemioticContext` bounds (\(\kappa, \gamma, \mu \in [0,1]\), \(p > 1\))
- `PDEInfra` typeclass (five classical PDE results)

---

## Lint

Run the Mathlib linter suite:

```bash
lake lint
```

---

## Project structure

```
cd-formalization/
├── CdFormal/
│   ├── Basic.lean              — Core definitions
│   │                             SemioticManifold, SemioticContext,
│   │                             SemioticOperators, SemioticBVP,
│   │                             IsWeakCoherentConfiguration
│   ├── Axioms.lean             — PDE infrastructure typeclass
│   │                             SolutionOperator, PrincipalEigendata,
│   │                             PDEInfra (5 axioms)
│   ├── Theorems.lean           — Existence theorems
│   │                             spectral_characterization_1d,
│   │                             exists_isWeakCoherentConfiguration (Thm 3.12),
│   │                             exists_pos_isWeakCoherentConfiguration (Thm 3.16)
│   ├── OperatorLemmas.lean     — Δ(0) = 0, Δ linearity, |∇0| = 0
│   ├── CoefficientLemmas.lean  — a(x) ≥ 0, a(x) ≤ 1, p − 1 > 0
│   ├── ScalingUniqueness.lean  — kΦ impossible for k > 1 (PDE-level)
│   ├── LinftyAlgebraic.lean    — bv ≥ cv^p ⟹ v ≤ (b/c)^{1/(p−1)}
│   ├── MonotoneFixedPoint.lean — Knaster-Tarski between sub/super
│   └── Verify.lean             — Axiom dependency dashboard
├── CdFormal.lean               — Root import (all modules)
├── artifacts/aristotle/         — Theorem prover raw outputs
├── drafts/                      — Mathlib issue drafts, proof sketches
├── lakefile.toml                — Lake config (Mathlib v4.28.0)
├── lake-manifest.json           — Dependency lock
└── lean-toolchain               — leanprover/lean4:v4.28.0
```

### File dependency graph

```
Basic.lean
  ├── Axioms.lean
  │     └── Theorems.lean
  ├── OperatorLemmas.lean
  │     └── ScalingUniqueness.lean
  └── CoefficientLemmas.lean

LinftyAlgebraic.lean     (standalone — Mathlib only)
MonotoneFixedPoint.lean   (standalone — Mathlib only)

Verify.lean               (imports all of the above)
```

`LinftyAlgebraic.lean` and `MonotoneFixedPoint.lean` depend only on Mathlib --- they are pure mathematics with no domain-specific imports, making them candidates for upstream contribution.

---

## CI

GitHub Actions runs `lake build --wfail` on every push and PR, plus a sorry contamination check against `Verify.lean`. See [`.github/workflows/lean_action_ci.yml`](https://github.com/Project-Navi/cd-formalization/blob/main/.github/workflows/lean_action_ci.yml).
