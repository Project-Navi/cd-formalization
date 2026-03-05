/-
Creative Determinant Framework — Core Definitions

Formalization of the semiotic manifold, coefficient structures, PDE operators,
boundary value problem, and weak coherent configuration.

All definitions in this file are machine-verified against Mathlib.

Reference: Spence 2026, "The Creative Determinant: Autopoietic Closure as a
Nonlinear Elliptic Boundary Value Problem with Lean 4-Verified Existence Conditions"
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle BigOperators Real Nat Pointwise

/-! ## Semiotic Manifold -/

/-- The model with corners for the semiotic manifold (self-model on Euclidean space). -/
abbrev SemioticModel (n : ℕ) := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))

/-- A semiotic manifold is a compact, connected, smooth Riemannian manifold.
    Paper Definition 2.1. -/
class SemioticManifold (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M] where
  /-- The Riemannian metric -/
  riemannianMetric : Bundle.RiemannianMetric (fun (_ : M) => EuclideanSpace ℝ (Fin n))

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
  κ_bounds : ∀ x, 0 ≤ κ x ∧ κ x ≤ 1
  γ_bounds : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1
  μ_bounds : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1
  c_pos : ∃ c₀ > 0, ∀ x, c x ≥ c₀
  p_gt_one : p > 1

/-- The creative drive coefficient a(x) = κ(x)·γ(x)·μ(x).
    Paper Definition 3.1. -/
def SemioticContext.a {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M]
    (ctx : SemioticContext n M) (x : M) : ℝ :=
  ctx.κ x * ctx.γ x * ctx.μ x

/-- The canonical viability closure b(x) = κ(x)·γ(x) - λ·μ(x).
    Paper Definition 3.3. -/
def SemioticContext.canonicalViability {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M]
    (ctx : SemioticContext n M) (lambda : ℝ) (x : M) : ℝ :=
  ctx.κ x * ctx.γ x - lambda * ctx.μ x

/-! ## PDE Operators -/

/-- Abstract Laplacian and gradient norm operators on the semiotic manifold.
    Paper Section 3.2. -/
structure SemioticOperators (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M] where
  /-- The Laplace-Beltrami operator -/
  laplacian : (M → ℝ) → (M → ℝ)
  /-- The norm of the gradient -/
  gradNorm : (M → ℝ) → (M → ℝ)
  /-- The Laplacian is linear -/
  laplacian_linear : ∀ (f g : M → ℝ) (c : ℝ),
    laplacian (fun x => c * f x + g x) = fun x => c * laplacian f x + laplacian g x
  /-- The gradient norm is non-negative -/
  gradNorm_nonneg : ∀ (f : M → ℝ) (x : M), 0 ≤ gradNorm f x

/-! ## Boundary Value Problem -/

/-- The BVP for the Creative Determinant: -ΔΦ = a|∇Φ| + bΦ - cΦ^p in M, Φ = 0 on ∂M.
    Paper Definition 3.1 (V1'). -/
structure SemioticBVP (n : ℕ) (M : Type*)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M] where
  ctx : SemioticContext n M
  ops : SemioticOperators n M
  /-- The boundary of the manifold -/
  boundary : Set M
  /-- The PDE: -ΔΦ = a|∇Φ| + bΦ - cΦ^p -/
  equation : (M → ℝ) → Prop := fun Φ =>
    ∀ x, -(ops.laplacian Φ x) =
      (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) - (ctx.c x) * (Φ x) ^ (ctx.p)
  /-- The boundary condition: Φ = 0 on ∂M -/
  boundaryCondition : (M → ℝ) → Prop := fun Φ =>
    ∀ x ∈ boundary, Φ x = 0

/-! ## Weak Coherent Configuration -/

/-- A weak coherent configuration is a solution to the Semiotic BVP.
    Paper Definition 3.6. -/
def IsWeakCoherentConfiguration {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M]
    (bvp : SemioticBVP n M) (Φ : M → ℝ) : Prop :=
  bvp.equation Φ ∧ bvp.boundaryCondition Φ

end
