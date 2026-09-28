/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The Creative Determinant problem on a finite graph

A finite-graph analogue of the boundary value problem in `CdFormal.Basic`, with every operator
defined from concrete data. The vertices form a finite type, `w` gives symmetric nonnegative
edge weights, some vertices form the boundary, and the coefficients are as in
`SemioticContext`. The problem is

  (L u)(x) = a(x)·|∇u|(x) + b(x)·u(x) - c(x)·max(u(x), 0)^p   at every interior vertex x,
  u(x) = 0                                                     at every boundary vertex,

with the unnormalized weighted graph Laplacian and gradient norm

  (L u)(x) = ∑_y w(x,y)·(u(x) - u(y)),     |∇u|(x) = √(∑_y w(x,y)·(u(y) - u(x))²).

Both sums run over all vertices, so edges to the boundary contribute through the value 0 there.
The linear part of the problem is L - diag(b) (the case β = 1 of `PrincipalEigendata`); its
principal eigenvalue is defined here as the minimum of the associated quadratic form over unit
functions that vanish on the boundary.

## Main definitions

- `SemioticGraph` — weights, boundary and coefficients
- `SemioticGraph.laplacian`, `SemioticGraph.gradNorm` — the graph operators
- `SemioticGraph.IsSolution` — the equation at interior vertices and zero boundary values
- `SemioticGraph.interiorGraph` — interior vertices joined by edges of positive weight
- `SemioticGraph.energy`, `SemioticGraph.principalEigenvalue` — the quadratic form of
  L - diag(b) and its minimum over `SemioticGraph.unitSphere`

## Main statements

- `SemioticGraph.gradNorm_nonneg`, `SemioticGraph.gradNorm_smul`,
  `SemioticGraph.gradNorm_const` — the gradient norm satisfies the laws that
  `SemioticOperators` requires of `gradNorm`

## Implementation notes

This is the discretization selected for the graph theorem. The weights are not normalized and
no vertex measure is used. It is not claimed to match a deployed model.

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.

## Tags

graph Laplacian, Dirichlet problem, principal eigenvalue
-/

noncomputable section

/-- A finite weighted graph with a Dirichlet boundary and the coefficients of the Creative
    Determinant equation. -/
structure SemioticGraph (V : Type*) where
  /-- Edge weights -/
  w : V → V → ℝ
  /-- The weights are nonnegative -/
  w_nonneg : ∀ x y, 0 ≤ w x y
  /-- The weights are symmetric -/
  w_symm : ∀ x y, w x y = w y x
  /-- The boundary vertices, where solutions vanish -/
  boundary : Set V
  /-- Care field κ : V → [0,1] -/
  κ : V → ℝ
  /-- Coherence field γ : V → [0,1] -/
  γ : V → ℝ
  /-- Contradiction field μ : V → [0,1] -/
  μ : V → ℝ
  /-- Viability potential -/
  b : V → ℝ
  /-- Carrying capacity -/
  c : V → ℝ
  /-- Saturation exponent -/
  p : ℝ
  /-- Care field bounded in [0,1] -/
  κ_bounds : ∀ x, 0 ≤ κ x ∧ κ x ≤ 1
  /-- Coherence field bounded in [0,1] -/
  γ_bounds : ∀ x, 0 ≤ γ x ∧ γ x ≤ 1
  /-- Contradiction field bounded in [0,1] -/
  μ_bounds : ∀ x, 0 ≤ μ x ∧ μ x ≤ 1
  /-- The carrying capacity is positive -/
  c_pos : ∀ x, 0 < c x
  /-- The saturation exponent exceeds 1 -/
  one_lt_p : 1 < p

namespace SemioticGraph

variable {V : Type*} (G : SemioticGraph V)

/-- The creative drive a(x) = κ(x)·γ(x)·μ(x). -/
def a (x : V) : ℝ := G.κ x * G.γ x * G.μ x

theorem a_nonneg (x : V) : 0 ≤ G.a x :=
  mul_nonneg (mul_nonneg (G.κ_bounds x).1 (G.γ_bounds x).1) (G.μ_bounds x).1

theorem a_le_one (x : V) : G.a x ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ (G.κ_bounds x).2 (G.γ_bounds x).1 (G.γ_bounds x).2)
    (G.μ_bounds x).1 (G.μ_bounds x).2

/-- The interior support graph: vertices off the boundary, adjacent when joined by an edge of
    positive weight. -/
def interiorGraph : SimpleGraph {x // x ∉ G.boundary} :=
  SimpleGraph.fromRel fun x y ↦ 0 < G.w x.1 y.1

variable [Fintype V]

/-- The graph Laplacian (L u)(x) = ∑_y w(x,y)·(u(x) - u(y)), the analogue of -Δu. -/
def laplacian (u : V → ℝ) (x : V) : ℝ := ∑ y, G.w x y * (u x - u y)

/-- The gradient norm |∇u|(x) = √(∑_y w(x,y)·(u(y) - u(x))²). -/
def gradNorm (u : V → ℝ) (x : V) : ℝ := √(∑ y, G.w x y * (u y - u x) ^ 2)

theorem gradNorm_nonneg (u : V → ℝ) (x : V) : 0 ≤ G.gradNorm u x :=
  Real.sqrt_nonneg _

/-- The gradient norm is absolutely homogeneous: |∇(c·u)| = |c|·|∇u|. -/
theorem gradNorm_smul (c : ℝ) (u : V → ℝ) (x : V) :
    G.gradNorm (fun y ↦ c * u y) x = |c| * G.gradNorm u x := by
  have h : ∀ y, G.w x y * (c * u y - c * u x) ^ 2 = c ^ 2 * (G.w x y * (u y - u x) ^ 2) :=
    fun y ↦ by ring
  simp only [gradNorm, h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The gradient norm of a constant function is zero. -/
theorem gradNorm_const (k : ℝ) (x : V) : G.gradNorm (fun _ ↦ k) x = 0 := by
  simp [gradNorm]

/-- `u` solves the problem: the equation holds at every interior vertex and `u` vanishes on the
    boundary. -/
def IsSolution (u : V → ℝ) : Prop :=
  (∀ x, x ∉ G.boundary →
    G.laplacian u x = G.a x * G.gradNorm u x + G.b x * u x - G.c x * max (u x) 0 ^ G.p) ∧
  ∀ x ∈ G.boundary, u x = 0

/-- The quadratic form of L - diag(b) on functions vanishing on the boundary:
    ½·∑_x ∑_y w(x,y)·(u(x) - u(y))² - ∑_x b(x)·u(x)². -/
def energy (u : V → ℝ) : ℝ :=
  (∑ x, ∑ y, G.w x y * (u x - u y) ^ 2) / 2 - ∑ x, G.b x * u x ^ 2

/-- Functions that vanish on the boundary and satisfy ∑ u² = 1. -/
def unitSphere : Set (V → ℝ) :=
  {u | (∀ x ∈ G.boundary, u x = 0) ∧ ∑ x, u x ^ 2 = 1}

theorem mem_unitSphere {u : V → ℝ} :
    u ∈ G.unitSphere ↔ (∀ x ∈ G.boundary, u x = 0) ∧ ∑ x, u x ^ 2 = 1 :=
  .rfl

/-- The principal Dirichlet eigenvalue of L - diag(b): the infimum of `energy` over
    `unitSphere`. When the interior is nonempty it is attained, it is an eigenvalue at every
    interior vertex, and no Dirichlet eigenvalue is smaller (see `CdFormal.Graph.Spectral`). -/
def principalEigenvalue : ℝ := sInf (G.energy '' G.unitSphere)

end SemioticGraph

end
