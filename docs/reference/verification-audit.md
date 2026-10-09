# Verification Audit

What is checked, how, and what remains outside the formalization. Toolchain and Mathlib are pinned at v4.34.1.

## Paper-to-Lean alignment

| Paper | Lean | Status |
|-------|------|--------|
| Definition 2.1 (semiotic manifold) | `SemioticManifold` | Definition; see [the model](../explanation/axiom-boundary.md#the-model) |
| Definitions 2.2, 3.1 (coefficients, creative drive) | `SemioticContext`, `SemioticContext.a` | Definitions |
| Definition 3.3 (canonical viability) | `SemioticContext.canonicalViability` | Definition |
| Definition 3.1 (BVP V1′) | `SemioticBVP` | Definition; the equation is an overridable field |
| Section 3.2 (weak coherent configuration) | `IsWeakCoherentConfiguration` | Definition |
| Definition 3.13 (principal eigenvalue) | `PrincipalEigendata` | Supplied data, not constructed |
| Lemma 3.7 (compactness of \(T\)) | `PDEInfra.T_compact` | Hypothesis |
| Lemma 3.10 (L∞ bound) | `PDEInfra.linfty_bound`; `linfty_bound_algebraic` | Hypothesis; algebraic step proved |
| Lemma 3.11 (\(C^{1,\alpha}\) bound) | none | Not formalized |
| Theorem 3.12 (existence) | `SemioticBVP.exists_isWeakCoherentConfiguration` | Proved from `PDEInfra`; named gap `gap:pde-infra` |
| Theorem 3.16 (nontrivial existence) | `SemioticBVP.exists_pos_isWeakCoherentConfiguration` | Proved from `PDEInfra`; named gap `gap:pde-infra`; positive at one interior point |
| Section 3.4 (spectral condition, 1D) | `spectral_characterization_1d` | Algebraic inequality proved; eigenvalue identification not formalized |
| Open Problem 3 (uniqueness) | `scaling_uniqueness` | Rules out solution multiples \(k\Phi\), \(k > 1\); uniqueness open |

## Finite-graph results

These are not in the paper. `SemioticGraph.exists_pos_graph` proves that the selected discrete problem on a finite weighted graph has a solution positive at every interior vertex, with the operators, the principal eigendata, the barriers and the fixed point all constructed. Its hypotheses are that the interior graph is connected, that the principal eigenvalue is negative, and that \(a(x) \le \sqrt{w(x,y)}\) and \(a(y) \le \sqrt{w(x,y)}\) for every edge of positive weight between distinct interior vertices \(x\) and \(y\). The last condition is sufficient for the proof; it is not claimed to be necessary. `SemioticGraph.exists_pos_triangle` shows that the hypotheses can be met.

## What CI checks

The required `build` job, on every pull request and on `main`:

- builds `CdFormal.lean` and every tracked module under `CdFormal/` with warnings as errors, and fails if a module is not imported by `CdFormal.lean`;
- runs the Mathlib environment linters (`lake lint`);
- runs `CdFormal/Verify.lean` with warnings as errors and requires exactly one `#print axioms` record for each listed declaration, each using only `propext`, `Classical.choice` and `Quot.sound`;
- fails if a headline result is missing from that list: the two continuum existence theorems, `SemioticGraph.exists_pos_graph` and its unweighted corollary, and the supporting lemmas the README names;
- checks the statement files: `spec/Spec.lean` restates every headline result with `sorry` as its proof, and `spec/Check.lean` requires each statement there to match the library declaration of the same name (the same type up to binder names and annotations, a theorem with a proof term, axioms within the allowlist), each statement's proof to be `sorry`, and every headline result to have a statement;
- resolves, with `#check`, every inline-code token in the README and on these pages that looks like a Lean name containing an uppercase letter, `_` or `.`, and every declaration shown in a Lean code block there (all-lowercase names are not checked);
- checks that every Lean file has the copyright header and a module docstring after its imports (Lean itself requires imports to come first);
- fails if `sorry` or `sorryAx` appears anywhere in the Lean sources, comments included;
- fails if any module of the library declares an `axiom` or an opaque constant, by inspecting the compiled environment rather than the source text; the check first confirms it reports both, an `axiom` declared across two lines and an `opaque` constant. An opaque constant is not an axiom, but the kernel cannot see its value and neither `#print axioms` nor a text search reports it. A proof by native evaluation (the tactic native_decide) declares an auxiliary axiom under Lean v4.34.1, so it fails this check and the axiom dashboard, and Mathlib's linter rejects it under warnings as errors.

The `docs` job builds this site, checks that every navigation page is built and every built page is in the navigation, and checks local links, assets and anchors. It does not check external links.

These checks establish that the proofs compile against the pinned Mathlib and use no further axioms. They do not discharge hypotheses such as `PDEInfra` (the named gap `gap:pde-infra`), and resolving a name does not show that the prose describes the statement; the statements on these pages are copied from the source.

## Known limitations

1. **Abstract model.** The Laplacian and gradient norm are structure fields, not constructed from the metric, and the boundary is an arbitrary set; the manifold itself has no boundary.
2. **Overridable equation.** `SemioticBVP.equation` and `SemioticBVP.boundaryCondition` default to the displayed problem but can be replaced.
3. **Assumed analysis.** The fields of `PDEInfra` and `SolutionOperator` are assumed, and some differ from the classical results they stand in for; see [the assumption boundary](../explanation/axiom-boundary.md).
4. **Lemma 3.11** is not formalized.
5. **Uniqueness** is open; `scaling_uniqueness` covers only multiples of a solution.
6. **Graph model.** The finite-graph theorem is about the discretization chosen for the formalization (unnormalized weights, the symmetric gradient norm, zero boundary values entering through boundary edges). Nothing relates it to the continuum problem: no convergence is formalized, and it is not claimed to match a deployed model.
