/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Creative Determinant Framework — Core Definitions

Formalization of the semiotic manifold, coefficient structures, PDE operators,
boundary value problem, and weak coherent configuration.

## Main definitions

- `SemioticModel` — model with corners for the semiotic manifold
- `SemioticManifold` — compact, connected manifold with a family of fibrewise inner products
  (Paper Definition 2.1)
- `SemioticContext` — coefficients κ, γ, μ, b, c, p for the BVP (Paper Definitions 2.2, 3.1)
- `SemioticContext.a` — creative drive coefficient a(x) = κγμ (Paper Definition 3.1)
- `SemioticContext.canonicalViability` — b(x) = κγ - λμ (Paper Definition 3.3)
- `SemioticOperators` — abstract Laplacian and gradient norm (Paper Section 3.2)
- `SemioticBVP` — the boundary value problem -ΔΦ = a|∇Φ| + bΦ - c(Φ₊)ᵖ, Φ = 0 on the
  boundary (Paper Definition 3.1)
- `IsWeakCoherentConfiguration` — a solution to the BVP (Paper §3.2)

## Implementation notes

The model is abstract. The atlas is analytic (`⊤` is `ω`) and modelled on ℝⁿ, so `M` has no
manifold boundary; `SemioticBVP.boundary` is an arbitrary set standing in for ∂M. The Laplacian
and gradient norm are fields of `SemioticOperators` with a few algebraic properties; they are
not constructed from `SemioticManifold.riemannianMetric`, which nothing else uses.
`SemioticBVP.equation` and `SemioticBVP.boundary_condition` are fields whose default values are
the displayed problem. A `SemioticBVP` may override them, and `IsWeakCoherentConfiguration`
uses the supplied fields.

## References

- [Spence2026] N. Spence, "The Creative Determinant: Autopoietic Closure as a
  Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions," 2026.
-/

noncomputable section

open scoped Manifold Bundle BigOperators Real Nat Pointwise

/-! ## Semiotic Manifold -/

/-- The model with corners for the semiotic manifold (self-model on Euclidean space). -/
abbrev SemioticModel (n : ℕ) := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]

/-- A semiotic manifold: a compact, connected manifold with an analytic atlas modelled on ℝⁿ,
    together with inner products on the fibres ℝⁿ over each point. No regularity in the base
    point, and no relation to the `MetricSpace` instance, is required.
    Paper Definition 2.1 asks for a compact, connected smooth Riemannian manifold. -/
class SemioticManifold (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M] where
  /-- The inner products on the fibres -/
  riemannianMetric : Bundle.RiemannianMetric (fun (_ : M) ↦ EuclideanSpace ℝ (Fin n))

variable [SemioticManifold n M]

/-! ## Coefficient Structure -/

/-- The coefficients and parameters for the Creative Determinant BVP.
    Paper Definitions 2.2, 3.1. -/
structure SemioticContext (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M] where
  /-- Care field κ : M → [0,1] -/
  κ : M → ℝ
  /-- Coherence field γ : M → [0,1] -/
  γ : M → ℝ
  /-- Contradiction field μ : M → [0,1] -/
  μ : M → ℝ
  /-- Viability potential b : M → ℝ -/
  b : M → ℝ
  /-- Carrying capacity c : M → ℝ -/
  c : M → ℝ
  /-- Saturation exponent p > 1 -/
  p : ℝ
  /-- Care field bounded in [0,1] -/
  κ_bounds : ∀ x, 0 ≤ κ x ∧ κ x ≤ 1
  /-- Coherence field bounded in [0,1] -/
  γ_bounds : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1
  /-- Contradiction field bounded in [0,1] -/
  μ_bounds : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1
  /-- Carrying capacity is uniformly positive: c(x) ≥ c₀ > 0 -/
  c_pos : ∃ c₀ > 0, ∀ x, c x ≥ c₀
  /-- Saturation exponent exceeds 1 (supercritical nonlinearity) -/
  one_lt_p : 1 < p

/-- The creative drive coefficient a(x) = κ(x)·γ(x)·μ(x).
    Paper Definition 3.1. -/
def SemioticContext.a (ctx : SemioticContext n M) (x : M) : ℝ :=
  ctx.κ x * ctx.γ x * ctx.μ x

/-- The canonical viability closure b(x) = κ(x)·γ(x) - λ·μ(x).
    Paper Definition 3.3. -/
def SemioticContext.canonicalViability (ctx : SemioticContext n M) (lambda : ℝ) (x : M) : ℝ :=
  ctx.κ x * ctx.γ x - lambda * ctx.μ x

/-! ## PDE Operators -/

/-- Abstract Laplacian and gradient norm operators on the semiotic manifold, specified only by
    the algebraic properties below; they are not built from the metric. Paper Section 3.2. -/
structure SemioticOperators (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M] where
  /-- Stands in for the Laplace–Beltrami operator -/
  laplacian : (M → ℝ) → (M → ℝ)
  /-- Stands in for the norm of the gradient -/
  gradNorm : (M → ℝ) → (M → ℝ)
  /-- The Laplacian is additive -/
  laplacian_add : ∀ (f g : M → ℝ),
    laplacian (fun x ↦ f x + g x) = fun x ↦ laplacian f x + laplacian g x
  /-- The Laplacian is homogeneous -/
  laplacian_smul : ∀ (f : M → ℝ) (c : ℝ),
    laplacian (fun x ↦ c * f x) = fun x ↦ c * laplacian f x
  /-- The gradient norm is non-negative -/
  gradNorm_nonneg : ∀ (f : M → ℝ) (x : M), 0 ≤ gradNorm f x
  /-- The gradient norm is absolutely homogeneous: |∇(c·f)| = |c|·|∇f| -/
  gradNorm_smul : ∀ (f : M → ℝ) (c : ℝ) (x : M),
    gradNorm (fun y ↦ c * f y) x = |c| * gradNorm f x
  /-- The gradient norm of a constant function is zero -/
  gradNorm_const : ∀ (a : ℝ) (x : M), gradNorm (fun _ ↦ a) x = 0

/-! ## Boundary Value Problem

Convention: The paper's eq. (V1') writes the saturation term as `c·Φ^p`, but the
operator formulation F(ψ) in §3.2 uses `c·(ψ₊)^p` where `ψ₊ = max(ψ, 0)`. We
follow the operator formulation. For nonnegative solutions the two agree. -/

/-- The BVP for the Creative Determinant: -ΔΦ = a|∇Φ| + bΦ - c(Φ₊)^p in M, Φ = 0 on ∂M.
    Paper Definition 3.1 (V1').

    `equation` and `boundary_condition` are fields with default values, so a `SemioticBVP` may
    replace them; statements about an arbitrary `bvp` concern the supplied predicates. -/
structure SemioticBVP (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M] where
  /-- The coefficient context (care, coherence, contradiction, viability, capacity) -/
  ctx : SemioticContext n M
  /-- The differential operators (Laplacian, gradient norm) -/
  ops : SemioticOperators n M
  /-- The boundary of the manifold.
      Known limitation: this is an unstructured `Set M` with no requirement
      that it equals the topological boundary. Encoding manifold-with-boundary
      requires infrastructure not yet available in Mathlib. -/
  boundary : Set M
  /-- The complement of the boundary is nonempty (prevents degenerate
      `boundary = Set.univ` which would make existence theorems vacuous). -/
  interior_nonempty : ∃ x, x ∉ boundary
  /-- The PDE: -ΔΦ = a|∇Φ| + bΦ - c(Φ₊)^p, where Φ₊ = max(Φ, 0). The default imposes it at
      every point of `M`, boundary points included.
      The positive part matches the operator formulation F(ψ) in the paper
      (Section 3.2), which uses ψ₊ in the saturation term.
      For nonnegative solutions, Φ₊ = Φ. -/
  equation : (M → ℝ) → Prop := fun Φ ↦
    ∀ x, -(ops.laplacian Φ x) =
      (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) -
      (ctx.c x) * (max (Φ x) 0) ^ (ctx.p)
  /-- The boundary condition: Φ = 0 on ∂M -/
  boundary_condition : (M → ℝ) → Prop := fun Φ ↦
    ∀ x ∈ boundary, Φ x = 0

/-! ## Weak Coherent Configuration -/

/-- A weak coherent configuration: a function satisfying `bvp.equation` and
    `bvp.boundary_condition`, which are the displayed BVP when the default fields are used.
    Paper §3.2 (inline definition after eq. V1'). -/
def IsWeakCoherentConfiguration (bvp : SemioticBVP n M) (Φ : M → ℝ) : Prop :=
  bvp.equation Φ ∧ bvp.boundary_condition Φ

end
