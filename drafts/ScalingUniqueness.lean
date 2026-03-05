/-
Scaling Uniqueness — Proportional solutions are impossible (k ≠ 1)

If Φ solves the BVP and kΦ also solves it with k > 1, then by
linearity of Δ and homogeneity of |∇·|, the saturation term forces
k·c·Φ^p = c·k^p·Φ^p. At a point where c > 0 and Φ > 0 this gives
k = k^p, contradicting k > 1 with p > 1.

This is a partial uniqueness result: solutions are unique within
the class of proportional rescalings. Full uniqueness (Open Problem #3
in the paper) remains open.

Uses: SemioticOperators axioms (linearity, homogeneity) from Basic.lean.
Uses: scaling_algebraic_contradiction from Theorems.lean (k < k^p).

Target: Aristotle piecewise proof.
-/

import CdFormal.Axioms

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

/-- If Φ and kΦ (with k > 1) both solve the CD equation, this is a
    contradiction at any point where c(x) > 0 and Φ(x) > 0.

    The proof combines:
    1. Linearity of Laplacian: Δ(kΦ) = kΔΦ (from ops.laplacian_linear)
    2. Homogeneity of gradient norm: |∇(kΦ)| = k|∇Φ| (from ops.gradNorm_homog, k > 0)
    3. Algebraic cancellation: equating the two PDE evaluations yields
       k·c(x)·Φ(x)^p = c(x)·(kΦ(x))^p = c(x)·k^p·Φ(x)^p
    4. The existing scaling_algebraic_contradiction lemma. -/
theorem scaling_uniqueness
    {n : ℕ} {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModel n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifold n M]
    (ops : SemioticOperators n M)
    (ctx : SemioticContext n M)
    (Φ : M → ℝ) (k : ℝ)
    (hk : k > 1)
    /- Φ solves the PDE (with positive part in saturation) -/
    (hΦ_eq : ∀ x, -(ops.laplacian Φ x) =
      (ctx.a x) * (ops.gradNorm Φ x) + (ctx.b x) * (Φ x) -
      (ctx.c x) * (max (Φ x) 0) ^ ctx.p)
    /- kΦ solves the PDE -/
    (hkΦ_eq : ∀ x, -(ops.laplacian (fun y => k * Φ y) x) =
      (ctx.a x) * (ops.gradNorm (fun y => k * Φ y) x) +
      (ctx.b x) * (k * Φ x) - (ctx.c x) * (max (k * Φ x) 0) ^ ctx.p)
    /- There exists a point where c > 0 and Φ > 0 -/
    (x₀ : M) (hc : ctx.c x₀ > 0) (hΦpos : Φ x₀ > 0) :
    False := by
  sorry

end
