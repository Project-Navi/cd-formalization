/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.OperatorLemmas

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

/-!
# Scaling Uniqueness — Proportional Solutions Are Impossible

If Φ solves the BVP and kΦ also solves it with k > 1, then by
linearity of Δ and homogeneity of |∇·|, the saturation term forces
k·c·Φ^p = c·k^p·Φ^p. At a point where c > 0 and Φ > 0 this gives
k = k^p, contradicting k > 1 with p > 1.

This is a partial uniqueness result: solutions are unique within
the class of proportional rescalings. Full uniqueness (Open Problem #3
in the paper) remains open.

## Main statements

- `scaling_uniqueness` — if Φ and kΦ both solve the CD equation,
  contradiction at any point with c > 0 and Φ > 0.

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.
-/

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]

/-- If Φ and kΦ (with k > 1) both solve the CD equation, this is a
    contradiction at any point where c(x₀) > 0 and Φ(x₀) > 0.

    The proof combines:
    1. Linearity of Laplacian: Δ(kΦ) = kΔΦ
       (from `laplacian_smul`)
    2. Homogeneity of gradient norm: |∇(kΦ)| = k|∇Φ|
       (from `gradNorm_smul`, k > 0)
    3. Algebraic cancellation: equating the two PDE evaluations
       yields k·c·Φ^p = c·k^p·Φ^p
    4. k < k^p when k > 1, p > 1
       (`Real.rpow_lt_rpow_of_exponent_lt`).

    Axiom dependencies: `SemioticOperators` fields only (no PDEInfra).
    Upstream candidate: the core inequality k < kᵖ may be a useful
    simp lemma near `Mathlib.Analysis.SpecialFunctions.Pow.Real`. -/
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
    False := by
  sorry

end
