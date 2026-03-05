/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 60ec288c-ddd4-458c-b002-4ab8a4500a94

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem scaling_uniqueness
    (ops : SemioticOperators n M)
    (ctx : SemioticContext n M)
    (Φ : M → ℝ) (k : ℝ)
    (hk : k > 1)
    (hΦ_eq : ∀ x, -(ops.laplacian Φ x) =
      (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) -
      (ctx.c x) * (max (Φ x) 0) ^ ctx.p)
    (hkΦ_eq : ∀ x,
      -(ops.laplacian (fun y => k * Φ y) x) =
      (ctx.a x) * (ops.gradNorm (fun y => k * Φ y) x) +
      (ctx.b x) * (k * Φ x) -
      (ctx.c x) * (max (k * Φ x) 0) ^ ctx.p)
    (x₀ : M) (hc : ctx.c x₀ > 0) (hΦpos : Φ x₀ > 0) :
    False
-/

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

- Originally proved by Aristotle (run `1c3414f4`), adapted here for
  current axiom names (`laplacian_add`/`laplacian_smul`/`gradNorm_smul`
  /`one_lt_p`).
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
       (from `laplacian_linear`)
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
      -(ops.laplacian (fun y => k * Φ y) x) =
      (ctx.a x) * (ops.gradNorm (fun y => k * Φ y) x) +
      (ctx.b x) * (k * Φ x) -
      (ctx.c x) * (max (k * Φ x) 0) ^ ctx.p)
    (x₀ : M) (hc : ctx.c x₀ > 0) (hΦpos : Φ x₀ > 0) :
    False := by
  -- By linearity of the Laplacian and homogeneity of the gradient norm, we can simplify the expressions.
  have h_laplacian : ops.laplacian (fun y => k * Φ y) x₀ = k * ops.laplacian Φ x₀ := by
    exact congr_fun ( ops.laplacian_smul Φ k ) x₀
  have h_gradNorm : ops.gradNorm (fun y => k * Φ y) x₀ = k * ops.gradNorm Φ x₀ := by
    simpa [ abs_of_pos ( zero_lt_one.trans hk ) ] using ops.gradNorm_smul Φ k x₀;
  -- By simplifying, we can see that the equation $k * Max.max (Φ x₀) 0 ^ ctx.p = Max.max (k * Φ x₀) 0 ^ ctx.p$ leads to a contradiction since $k > 1$ and $ctx.p > 1$.
  have h_contradiction : k * Max.max (Φ x₀) 0 ^ ctx.p = Max.max (k * Φ x₀) 0 ^ ctx.p → False := by
    rw [ max_eq_left ( by positivity ), max_eq_left ( by positivity ) ];
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ];
    exact fun h => absurd h ( ne_of_lt ( mul_lt_mul_of_pos_right ( by simpa using Real.rpow_lt_rpow_of_exponent_lt hk ( show ctx.p > 1 from ctx.one_lt_p ) ) ( by positivity ) ) );
  grind

end
