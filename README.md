# Creative Determinant: Lean 4 formalization

A Lean 4 and Mathlib (v4.28.0) formalization of the existence theory in N. Spence, *The Creative Determinant: Autopoietic Closure as a Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions* (2026). The problem is −ΔΦ = a|∇Φ| + bΦ − c(Φ₊)ᵖ in M with Φ = 0 on ∂M, where a = κγμ and p > 1. Documentation: [project-navi.github.io/cd-formalization](https://project-navi.github.io/cd-formalization/).

- **Conditional results.** `SemioticBVP.exists_isWeakCoherentConfiguration` gives a nonnegative solution, and `SemioticBVP.exists_pos_isWeakCoherentConfiguration` gives a nonnegative solution that is positive at some interior point when a supplied principal eigenvalue is negative. Both are derived from the hypotheses `PDEInfra` and `SolutionOperator`, which stand in for compactness, maximum-principle, fixed-point and sub/super-solution results that are not proved here. The manifold's Laplacian, gradient norm and boundary are abstract data, not constructed from its geometry.
- **Unconditional results.** Supporting lemmas, including `spectral_characterization_1d` (algebra), `linfty_bound_algebraic`, `monotone_fixed_point_between` (Knaster–Tarski) and `scaling_uniqueness`: if Φ solves the equation with Φ(x₀) > 0 and c(x₀) > 0, then kΦ does not for any k > 1.

The [assumption boundary](https://project-navi.github.io/cd-formalization/explanation/axiom-boundary/) page states what each hypothesis says and what is not formalized.

## Verify

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true CdFormal/Verify.lean
```

`CdFormal/Verify.lean` prints the axioms of the headline results and the declarations the documentation cites; CI requires each to use only `propext`, `Classical.choice` and `Quot.sound`. This check cannot see hypotheses: `PDEInfra` appears in the signatures of the conditional theorems.

## Credit and license

Formalization by Nelson Spence. Aristotle (Harmonic) proved several leaf lemmas and Claude assisted with Lean. The bornological form of `PDEInfra.T_compact` follows a suggestion by Yongxi (Aaron) Lin on the Lean Zulip. To cite this work, see [CITATION.cff](CITATION.cff). Apache 2.0; see [LICENSE](LICENSE).
