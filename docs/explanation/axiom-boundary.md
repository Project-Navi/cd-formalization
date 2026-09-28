# The Assumption Boundary

The continuum existence theorems are conditional. Their analytic inputs are hypotheses: the class `PDEInfra`, the structure `SolutionOperator`, and, for the second theorem, a `PrincipalEigendata` argument. None of these is a Lean `axiom`. `#print axioms` therefore reports only `propext`, `Classical.choice` and `Quot.sound` for both theorems; the hypotheses are visible in their signatures instead. This page states what each hypothesis says in Lean, how that compares with the classical result it stands in for, and what the model leaves abstract.

## The model

- **Manifold.** `SemioticManifold` requires a compact, connected space with an analytic atlas (`IsManifold (SemioticModel n) ⊤ M`, where `⊤` is \(C^\omega\)) modelled on \(\mathbb{R}^n\), so \(M\) has no manifold boundary. Its field `SemioticManifold.riemannianMetric` is a family of inner products on the fibres \(\mathbb{R}^n\); nothing ties it to the `MetricSpace` instance, to smoothness in the base point, or to the operators.
- **Operators.** `SemioticOperators` is abstract data: a map `SemioticOperators.laplacian` that is additive and homogeneous, and a map `SemioticOperators.gradNorm` that is nonnegative, absolutely homogeneous and zero on constants. Neither is constructed from the metric.
- **Boundary.** `SemioticBVP.boundary` is an arbitrary set with nonempty complement; it stands in for \(\partial M\).
- **Equation.** `SemioticBVP.equation` and `SemioticBVP.boundaryCondition` are structure fields whose default values are the displayed problem, imposed at every point of \(M\), boundary points included. A `SemioticBVP` may override them, and `IsWeakCoherentConfiguration` refers to the supplied fields, so a theorem about an arbitrary `SemioticBVP` is about the displayed PDE only when the defaults are used.

## `SolutionOperator`

A map `SolutionOperator.T` on `M → ℝ` with `SolutionOperator.T_boundary` (\(T u = 0\) on the boundary) and

```lean
T_fixed_point : ∀ Φ, T Φ = Φ → IsWeakCoherentConfiguration bvp Φ
```

The correspondence between fixed points and solutions is assumed, not derived from a definition of \(T\).

## `PrincipalEigendata`

`PrincipalEigendata bvp beta` is supplied data: a number `PrincipalEigendata.eigval` and a function that is positive off the boundary, zero on it, and satisfies \(-\Delta\varphi - \beta b \varphi = \lambda \varphi\) at every point. It is not constructed from the operators.

## `PDEInfra`

### `PDEInfra.T_compact` (Paper Lemma 3.7)

```lean
T_compact : ∀ S : Set (M → ℝ),
  Bornology.IsVonNBounded ℝ S →
  IsCompact (closure (solOp.T '' S))
```

The bornological formulation follows a suggestion by Yongxi (Aaron) Lin on the Lean Zulip. On `M → ℝ`, whose topology is the product topology, a set is von Neumann bounded exactly when it is pointwise bounded, and its image has compact closure exactly when the image is pointwise bounded. So in this setting the field says that \(T\) maps pointwise-bounded sets to pointwise-bounded sets. That is a different condition from the compactness in Hölder norms that Lemma 3.7 provides: it constrains every pointwise-bounded set, and asks only that the image be pointwise bounded.

### `PDEInfra.linfty_bound` (Paper Lemma 3.10)

```lean
linfty_bound :
  ∀ (B : ℝ), (∀ x, bvp.ctx.b x ≤ B) →
  ∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K
```

A uniform bound on the Schaefer set. Classically it comes from the maximum principle at an interior maximum, where the equation reduces to \(b v \geq c v^p\); that algebraic step is proved as `linfty_bound_algebraic`, and the maximum-principle step is assumed here.

### `PDEInfra.schaefer` (Paper Theorem 3.12)

```lean
schaefer :
  (∀ S : Set (M → ℝ), Bornology.IsVonNBounded ℝ S →
    IsCompact (closure (solOp.T '' S))) →
  (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
    (∀ x, u x = τ * solOp.T u x) →
    ∀ x, |u x| ≤ K) →
  ∃ Φ : M → ℝ, solOp.T Φ = Φ
```

Schaefer's theorem also needs \(T\) to be continuous on a Banach space; no continuity is assumed here. The field is therefore an assumption about this particular \(T\), named after the theorem it stands in for.

### `PDEInfra.fixed_point_nonneg` (Paper Theorem 3.12)

```lean
fixed_point_nonneg : ∀ (Φ : M → ℝ), solOp.T Φ = Φ → ∀ x, Φ x ≥ 0
```

Nonnegativity of fixed points, classically a maximum-principle consequence of the positive part \(\Phi_+\) in the saturation term.

### `PDEInfra.monotone_iteration` (Paper Theorem 3.16)

```lean
monotone_iteration :
  ∀ (beta : ℝ) (eig : PrincipalEigendata bvp beta),
    eig.eigval < 0 →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ ∧ (∃ x, x ∉ bvp.boundary ∧ Φ x > 0)
```

Classically: \(\varepsilon\varphi_1\) is a sub-solution, a large constant is a super-solution, and monotone iteration between them gives a solution. The field asserts positivity at one interior point only. It is stated for every `beta`, while the equation uses \(b\) itself (\(\beta = 1\)); for other values it assumes more than the classical result. For example, when \(a \equiv 0\) and \(c > 0\) a positive solution exists only if the principal eigenvalue of \(-\Delta - b\) is negative, and that does not follow from negativity for \(-\Delta - \beta b\) with \(\beta > 1\). `SemioticBVP.exists_pos_isWeakCoherentConfiguration` inherits this through its `beta` argument.

## What the fields would need

| Field | Classical source | Missing from Mathlib (v4.34.1) |
|-------|------------------|--------------------------------|
| `PDEInfra.T_compact` | Schauder estimates, Arzelà–Ascoli | Hölder spaces and Schauder theory on manifolds |
| `PDEInfra.linfty_bound` | Maximum principle | Maximum principles for elliptic operators on manifolds |
| `PDEInfra.schaefer` | [Schaefer1955] | Schaefer's and Schauder's fixed-point theorems |
| `PDEInfra.fixed_point_nonneg` | Maximum principle | As above |
| `PDEInfra.monotone_iteration` | [Amann1976] | Sub/super-solution theory in ordered Banach spaces |
| `PrincipalEigendata` | Krein–Rutman or variational theory | Principal eigenvalues of elliptic operators on manifolds |

Replacing a field by a proof would also require the operators to be constructed from the metric and the boundary to be the boundary of a manifold with boundary.

## The finite-graph theorem

`SemioticGraph.exists_pos_graph` takes no hypothesis of the kind above. On a finite graph the Laplacian and the gradient norm are defined from the weights, the principal eigenvalue is defined as an infimum, attained when the interior is nonempty, and shown to have a positive eigenvector when the interior graph is connected, and the fixed point comes from `monotone_fixed_point_between`. Its hypotheses (a connected interior graph, a negative principal eigenvalue, and the edge-dominance condition) are mathematical conditions stated in its signature; see the [theorem catalog](../reference/theorems.md#finite-graph-existence).

## References

- [Schaefer1955] H. Schaefer, "Über die Methode der a priori-Schranken," 1955.
- [Amann1976] H. Amann, "Fixed point equations and nonlinear eigenvalue problems in ordered Banach spaces," 1976.
