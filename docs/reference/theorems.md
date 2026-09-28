# Theorem Catalog

Statements as they appear in the source. Every declaration compiles under `lake build --wfail`; the axioms of those listed in `CdFormal/Verify.lean` are checked in CI. The continuum results come first; the [finite-graph results](#finite-graph-existence) are at the end.

Throughout the continuum sections, `n`, `M` and the instance arguments

```lean
variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]
```

are implicit where they appear.

## Definitions

| Declaration | Meaning |
|-------------|---------|
| `SemioticContext` | \(\kappa, \gamma, \mu : M \to [0,1]\), \(b\), \(c \geq c_0 > 0\), \(p > 1\) |
| `SemioticContext.a` | \(a(x) = \kappa(x)\gamma(x)\mu(x)\) |
| `SemioticContext.canonicalViability` | \(\kappa(x)\gamma(x) - \lambda\mu(x)\), for a parameter \(\lambda\) |
| `SemioticOperators` | abstract Laplacian and gradient norm |
| `SemioticBVP` | coefficients, operators, a boundary set, and the fields `SemioticBVP.equation` and `SemioticBVP.boundary_condition` |
| `IsWeakCoherentConfiguration` | `bvp.equation Φ ∧ bvp.boundary_condition Φ` |

The default `SemioticBVP.equation` is

```lean
fun Φ ↦ ∀ x, -(ops.laplacian Φ x) =
  (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) - (ctx.c x) * (max (Φ x) 0) ^ (ctx.p)
```

and the default boundary condition is `fun Φ ↦ ∀ x ∈ boundary, Φ x = 0`. See the [assumption boundary](../explanation/axiom-boundary.md) for `PDEInfra`, `SolutionOperator` and `PrincipalEigendata`.

## Conditional existence

### Nonnegative solution (Paper Theorem 3.12)

```lean
theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0)
```

Uses `PDEInfra.T_compact`, `PDEInfra.linfty_bound`, `PDEInfra.schaefer`, `PDEInfra.fixed_point_nonneg` and `SolutionOperator.T_fixed_point`. With the default equation, \(\Phi \equiv 0\) is already such a solution (`zero_solves_equation`, below).

### Solution positive at an interior point (Paper Theorem 3.16)

```lean
theorem SemioticBVP.exists_pos_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (beta : ℝ)
    (eig : PrincipalEigendata bvp beta)
    (eigval_neg : eig.eigval < 0) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) ∧
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0)
```

Uses `PDEInfra.monotone_iteration`, `PDEInfra.fixed_point_nonneg` and `SolutionOperator.T_fixed_point`. Positivity is at one interior point.

## Algebra and real analysis

```lean
def viabilityThreshold (L : ℝ) (b : ℝ) : ℝ :=
  (Real.pi / L) ^ 2 / b

theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ) (hb : b > 0) :
    let beta_star := viabilityThreshold L b
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0

theorem viabilityThreshold_lt_iff (L : ℝ) {b : ℝ} (hb : 0 < b) (beta : ℝ) :
    viabilityThreshold L b < beta ↔ (Real.pi / L) ^ 2 - beta * b < 0
```

`spectral_characterization_1d` is an inequality about the expression \((\pi/L)^2 - \beta b\), which for constant \(b\) is the principal Dirichlet eigenvalue of \(-d^2/dx^2 - \beta b\) on \([0, L]\); that identification is not formalized.

```lean
lemma scaling_algebraic_contradiction
    (p : ℝ) (k : ℝ) (c : ℝ) (Phi_val : ℝ)
    (hp : p > 1) (hk : k > 1) (hc : c > 0) (hPhi : Phi_val > 0)
    (h_eq : -c * k * Phi_val ^ p ≤ -c * k ^ p * Phi_val ^ p) :
    False

lemma rpow_le_of_mul_rpow_le
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0)
    (h : b * v ≥ c * v ^ p) :
    v ^ (p - 1) ≤ b / c

theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1))
```

## Order theory

For `{α : Type u} [CompleteLattice α] (f : α →o α)`:

```lean
theorem OrderHom.nextFixed_le_of_le
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    (f.nextFixed sub h_sub : α) ≤ super

theorem monotone_fixed_point_between
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    ∃ x : α, f x = x ∧ sub ≤ x ∧ x ≤ super
```

## Consequences of the structure fields

For `ops : SemioticOperators n M` and `ctx : SemioticContext n M`:

```lean
@[simp] lemma laplacian_zero :
    ops.laplacian (fun _ : M ↦ (0 : ℝ)) = fun _ ↦ 0

lemma laplacian_linear (f g : M → ℝ) (c : ℝ) :
    ops.laplacian (fun x ↦ c * f x + g x) =
    fun x ↦ c * ops.laplacian f x + ops.laplacian g x

@[simp] lemma gradNorm_zero (x : M) :
    ops.gradNorm (fun _ : M ↦ (0 : ℝ)) x = 0

theorem zero_solves_equation (ctx : SemioticContext n M) (x : M) :
    -(ops.laplacian (fun _ ↦ 0) x) =
      ctx.a x * ops.gradNorm (fun _ ↦ 0) x + ctx.b x * 0 - ctx.c x * max (0 : ℝ) 0 ^ ctx.p

theorem SemioticContext.a_nonneg (x : M) : 0 ≤ ctx.a x
theorem SemioticContext.a_le_one (x : M) : ctx.a x ≤ 1
theorem SemioticContext.p_sub_one_pos : 0 < ctx.p - 1
```

### Scaling

```lean
theorem scaling_uniqueness
    (ops : SemioticOperators n M)
    (ctx : SemioticContext n M)
    (Φ : M → ℝ) (k : ℝ)
    (hk : k > 1)
    (hΦ_eq : ∀ x, -(ops.laplacian Φ x) =
      (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) -
      (ctx.c x) * (max (Φ x) 0) ^ ctx.p)
    (hkΦ_eq : ∀ x,
      -(ops.laplacian (fun y ↦ k * Φ y) x) =
      (ctx.a x) * (ops.gradNorm (fun y ↦ k * Φ y) x) +
      (ctx.b x) * (k * Φ x) -
      (ctx.c x) * (max (k * Φ x) 0) ^ ctx.p)
    (x₀ : M) (hc : ctx.c x₀ > 0) (hΦpos : Φ x₀ > 0) :
    False
```

A solution \(\Phi\) with \(\Phi(x_0) > 0\) and \(c(x_0) > 0\) has no solution multiple \(k\Phi\) with \(k > 1\). This is not uniqueness among all solutions, which the paper leaves open.

## Finite-graph existence

For a finite type `V` with `[Fintype V]` and `G : SemioticGraph V`. Here every operator is defined from the data, and no hypothesis stands in for analysis.

| Declaration | Meaning |
|-------------|---------|
| `SemioticGraph` | weights \(w(x,y) = w(y,x) \geq 0\), a boundary set, \(\kappa, \gamma, \mu : V \to [0,1]\), \(b\), \(c > 0\), \(p > 1\) |
| `SemioticGraph.a` | \(a(x) = \kappa(x)\gamma(x)\mu(x)\) |
| `SemioticGraph.laplacian` | \((L u)(x) = \sum_y w(x,y)\,(u(x) - u(y))\) |
| `SemioticGraph.gradNorm` | \(\lvert\nabla u\rvert(x) = \sqrt{\sum_y w(x,y)\,(u(y) - u(x))^2}\) |
| `SemioticGraph.IsSolution` | the equation at every interior vertex, and \(u = 0\) on the boundary |
| `SemioticGraph.interiorGraph` | interior vertices, adjacent when joined by an edge of positive weight |
| `SemioticGraph.energy` | \(\tfrac12 \sum_x \sum_y w(x,y)\,(u(x) - u(y))^2 - \sum_x b(x)\,u(x)^2\), the quadratic form of \(L - \operatorname{diag}(b)\) |
| `SemioticGraph.principalEigenvalue` | the infimum of `SemioticGraph.energy` over `SemioticGraph.unitSphere`, the functions that vanish on the boundary with \(\sum_x u(x)^2 = 1\) |

```lean
def IsSolution (u : V → ℝ) : Prop :=
  (∀ x, x ∉ G.boundary →
    G.laplacian u x = G.a x * G.gradNorm u x + G.b x * u x - G.c x * max (u x) 0 ^ G.p) ∧
  ∀ x ∈ G.boundary, u x = 0
```

The sums run over all vertices, so the boundary values, which are zero, enter through boundary edges. The weights are not normalized and there is no vertex measure. This is the discretization chosen for the formalization; it is not claimed to match any deployed model.

### Positive solution

```lean
theorem SemioticGraph.exists_pos_graph (hconn : G.interiorGraph.Connected)
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    (hneg : G.principalEigenvalue < 0) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ x, x ∉ G.boundary → 0 < u x

theorem SemioticGraph.exists_pos_graph_of_unweighted (hw : ∀ x y, G.w x y = 0 ∨ G.w x y = 1)
    (hconn : G.interiorGraph.Connected) (hneg : G.principalEigenvalue < 0) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ x, x ∉ G.boundary → 0 < u x
```

The solution is positive at every interior vertex. The edge-dominance hypothesis `hdom` ranges over ordered pairs, so for every edge of positive weight between distinct interior vertices \(x\) and \(y\) it requires both \(a(x) \le \sqrt{w(x,y)}\) and \(a(y) \le \sqrt{w(x,y)}\). It is what makes the fixed-point map in the proof monotone; it is a sufficient condition for this proof, not a condition shown to be necessary for existence. For weights in \(\{0, 1\}\) it follows from \(0 \le a \le 1\), so `SemioticGraph.exists_pos_graph_of_unweighted` does not assume it.

### Gradient norm

```lean
theorem SemioticGraph.gradNorm_nonneg (u : V → ℝ) (x : V) : 0 ≤ G.gradNorm u x

theorem SemioticGraph.gradNorm_smul (c : ℝ) (u : V → ℝ) (x : V) :
    G.gradNorm (fun y ↦ c * u y) x = |c| * G.gradNorm u x

theorem SemioticGraph.gradNorm_const (k : ℝ) (x : V) : G.gradNorm (fun _ ↦ k) x = 0
```

These are the laws that `SemioticOperators` imposes on its gradient norm.

### Principal eigendata

```lean
theorem SemioticGraph.principalEigenvalue_mul_le {u : V → ℝ}
    (hu : ∀ x ∈ G.boundary, u x = 0) :
    G.principalEigenvalue * ∑ x, u x ^ 2 ≤ G.energy u

theorem SemioticGraph.principalEigenvalue_le_of_laplacian_eq {u : V → ℝ} {μ : ℝ}
    (hu : ∀ x ∈ G.boundary, u x = 0) (hne : ∃ x, u x ≠ 0)
    (heq : ∀ x, x ∉ G.boundary → G.laplacian u x = G.b x * u x + μ * u x) :
    G.principalEigenvalue ≤ μ

theorem SemioticGraph.exists_pos_eigenvector (hconn : G.interiorGraph.Connected) :
    ∃ φ ∈ G.unitSphere, (∀ x, x ∉ G.boundary → 0 < φ x) ∧
      ∀ x, x ∉ G.boundary → G.laplacian φ x = G.b x * φ x + G.principalEigenvalue * φ x

theorem SemioticGraph.principalEigenvalue_neg {u : V → ℝ} (hu : ∀ x ∈ G.boundary, u x = 0)
    (hneg : G.energy u < 0) : G.principalEigenvalue < 0
```

`SemioticGraph.principalEigenvalue_le_of_laplacian_eq` says that no Dirichlet eigenvalue of \(L - \operatorname{diag}(b)\) is smaller than `SemioticGraph.principalEigenvalue`.

### Sub- and supersolutions

```lean
theorem SemioticGraph.fixedPointMap_eq_iff_isSolution {K : ℝ} (hK : 0 < K) {u : V → ℝ} :
    G.fixedPointMap K u = u ↔ G.IsSolution u
```

`SemioticGraph.fixedPointMap` is the fixed-point map of the proof; for \(K > 0\) its fixed points are exactly the solutions. `SemioticGraph.fixedPointMap_mono` is its monotonicity, and `SemioticGraph.exists_isSolution_between` gives a solution between an ordered subsolution and supersolution. The barriers are `SemioticGraph.smul_subsolution` and `SemioticGraph.plateau_supersolution`. See the [proof strategy](../explanation/proof-strategy.md#finite-graph-existence).

### Example

`SemioticGraph.triangle` is the complete graph on three vertices with unit weights and one boundary vertex (its weights are also 1 on the diagonal, which does not affect the Laplacian, the gradient norm or the energy), with \(\kappa = \gamma = \mu = 1\), \(b = 2\), \(c = 1\) and \(p = 2\). `SemioticGraph.exists_pos_triangle` applies `SemioticGraph.exists_pos_graph_of_unweighted` to it, so the hypotheses of the graph theorem can all be met.
