# Creative Determinant — Lean 4 Formalization

Formal verification of the existence theory from:

> N. Spence, "The Creative Determinant: Autopoietic Closure as a Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions," 2026.

## What is verified

| Result | File | Status |
|--------|------|--------|
| Spectral characterization (1D) | `CdFormal/Theorems.lean` | Proved (pure algebra) |
| Scaling algebraic contradiction | `CdFormal/Theorems.lean` | Proved (pure algebra) |
| Existence of weak coherent configurations | `CdFormal/Theorems.lean` | Proved (conditional on `PdeInfra`) |
| Existence of nontrivial configurations | `CdFormal/Theorems.lean` | Proved (conditional on `PdeInfra`) |
| L∞ bound algebraic core | `artifacts/aristotle/LinftyAlgebraic_proved.lean` | Proved (standalone) |
| Scaling uniqueness | `artifacts/aristotle/ScalingUniqueness_proved.lean` | Proved (uses `SemioticOperators` axioms) |

All definitions (semiotic manifold, BVP, operators, weak coherent configuration) are machine-checked against Mathlib.

## Axiom boundary

The `PdeInfra` typeclass in `CdFormal/Axioms.lean` packages five classical PDE results not yet in Mathlib:

1. **T continuous & compact** — Schauder estimates + Arzelà–Ascoli (placeholder `True`)
2. **L∞ bound** — Maximum principle at interior extremum
3. **Schaefer's fixed-point theorem** — Not in Mathlib ([draft issue](drafts/mathlib_issue_schaefer.md))
4. **Fixed-point nonnegativity** — Maximum principle
5. **Monotone iteration** — Sub/super-solution theory (Amann 1976)

The existence theorems explicitly carry `[PdeInfra bvp solOp]` so the axiom surface is visible to Lean's kernel. Run `#print axioms` in `CdFormal/Verify.lean` to confirm no `sorryAx`.

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
  Axioms.lean      — PdeInfra typeclass (explicit axiom surface)
  Theorems.lean    — Proved theorems
  Verify.lean      — #print axioms dashboard
artifacts/
  aristotle/       — Proved outputs from the Aristotle theorem prover
drafts/            — In-progress proof targets and issue drafts
```

## Development Process

**Mathematical framework**: The Creative Determinant equations, existence theory,
and proof strategy were developed by Nelson Spence over 12 months (April 2025 –
March 2026), documented in the [parent repository](https://github.com/Project-Navi/navi-creative-determinant) and [paper](../paper/creative_determinant.pdf).

**Lean formalization**: Translating the paper proofs into Lean 4 was assisted by:
- **Claude Opus**: Project structure, Mathlib API navigation, proof term generation
- **Aristotle** (Harmonic.fun): Automated proving of algebraic/analysis lemmas

All mathematical content originates from the author's research. AI tools were used
as formalization assistants, analogous to proof automation in Coq/Isabelle.

**Verification**: All proofs compile against Mathlib v4.28.0 with zero `sorry`.
The axiom surface (`PdeInfra`) packages classical PDE results not yet in Mathlib.

## License

See the parent repository for license information.
