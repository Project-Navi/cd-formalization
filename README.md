# Creative Determinant: Lean 4 formalization

A Lean 4 and Mathlib (v4.34.1) formalization of the existence theory in N. Spence, *The Creative Determinant: Autopoietic Closure as a Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions* (2026). The problem is −ΔΦ = a|∇Φ| + bΦ − c(Φ₊)ᵖ in M with Φ = 0 on ∂M, where a = κγμ and p > 1. Documentation: [docs.projectnavi.ai/cd-formalization](https://docs.projectnavi.ai/cd-formalization/).

- **Continuum results (conditional).** `SemioticBVP.exists_isWeakCoherentConfiguration` gives a nonnegative solution when `b` is bounded above, and `SemioticBVP.exists_pos_isWeakCoherentConfiguration` one that is positive at some interior point when a supplied principal eigenvalue is negative. Both are derived from the hypotheses `PDEInfra` and `SolutionOperator`, which stand in for elliptic results not proved here; the manifold's Laplacian, gradient norm and boundary are abstract data.
- **Finite graphs (proved).** For the discretization selected here, on a finite weighted graph with a Dirichlet boundary, `SemioticGraph.exists_pos_graph` gives a solution positive at every interior vertex when the interior graph is connected, the principal eigenvalue of L − diag(b) is negative, and a(x) ≤ √w(x,y) and a(y) ≤ √w(x,y) for every edge of positive weight between distinct interior vertices x and y. The operators and eigendata are constructed. The edge condition is sufficient for this proof, not claimed necessary, and holds for 0/1 weights (`SemioticGraph.exists_pos_graph_of_unweighted`).
- **Supporting lemmas**, among them `spectral_characterization_1d`, `linfty_bound_algebraic`, `monotone_fixed_point_between` (Knaster–Tarski) and `scaling_uniqueness`.

The [assumption boundary](https://docs.projectnavi.ai/cd-formalization/explanation/axiom-boundary/) page states what each hypothesis says and what is not formalized.

## Verify

```bash
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true CdFormal/Verify.lean
```

`CdFormal/Verify.lean` prints the axioms of the headline results and the declarations the documentation cites; CI requires each to use only `propext`, `Classical.choice` and `Quot.sound`. This check cannot see hypotheses: `PDEInfra` appears in the signatures of the conditional theorems.

## Credit and license

Formalization by Nelson Spence. Andrew Edmark (@aedmark) proposed the finite-graph formulation and its proof route: finite-dimensional inverse positivity and positive principal eigendata, then the existing order-theoretic fixed-point core. The discretization, the Jacobi splitting used for inverse positivity and the edge condition were chosen for this formalization and are not claimed to be his. Aristotle (Harmonic) proved several leaf lemmas, and Claude assisted with the Lean proofs, including the finite-graph development. The bornological form of `PDEInfra.T_compact` follows a suggestion by Yongxi (Aaron) Lin on the Lean Zulip. To cite this work, see [CITATION.cff](CITATION.cff). Apache 2.0; see [LICENSE](LICENSE).
