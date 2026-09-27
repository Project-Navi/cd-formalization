# Quickstart

## Prerequisites

- [elan](https://github.com/leanprover/elan), which installs the toolchain pinned in `lean-toolchain` (Lean v4.28.0).
- Mathlib v4.28.0, which Lake fetches.

## Build and verify

```bash
git clone https://github.com/Project-Navi/cd-formalization.git
cd cd-formalization
lake exe cache get                                         # prebuilt Mathlib
lake build --wfail                                         # warnings, including sorry, are errors
lake lint                                                  # Mathlib environment linters
lake env lean -DwarningAsError=true CdFormal/Verify.lean   # axiom dashboard
```

`CdFormal/Verify.lean` runs `#print axioms` on the headline results and on the declarations these pages cite. Each should depend only on `propext`, `Classical.choice` and `Quot.sound`. Hypotheses such as `PDEInfra` are not axioms and do not appear in this output; read them in the theorem signatures.

## Project layout

```
CdFormal/
  Basic.lean               definitions: manifold, coefficients, operators, BVP
  Axioms.lean              hypotheses: SolutionOperator, PrincipalEigendata, PDEInfra
  Theorems.lean            conditional existence theorems; 1D spectral algebra
  OperatorLemmas.lean      consequences of the SemioticOperators fields
  CoefficientLemmas.lean   bounds on a = κγμ and on p
  ScalingUniqueness.lean   no solution kΦ with k > 1
  LinftyAlgebraic.lean     b·v ≥ c·vᵖ implies v ≤ (b/c)^(1/(p−1))
  MonotoneFixedPoint.lean  fixed point between a sub- and a super-fixed point
  Verify.lean              axiom dashboard
CdFormal.lean              root import
```

## Continuous integration

The required `build` job builds every module with warnings as errors, runs the Mathlib linters, checks the axiom dashboard (exactly one record per selected declaration, using only the three axioms above), resolves every Lean name quoted in the README and on these pages, and fails if `sorry` appears anywhere in the sources. The `docs` job builds this site and checks its navigation, local links and anchors; it does not check external links.
