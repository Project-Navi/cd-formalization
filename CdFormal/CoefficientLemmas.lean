/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

/-!
# Coefficient Bound Lemmas

Derived properties of `SemioticContext` coefficients from the bounds
in `Basic.lean`. These validate the coefficient contract and provide
building blocks for PDE estimates.

## Main statements

- `SemioticContext.a_nonneg` — a(x) = κγμ ≥ 0
- `SemioticContext.a_le_one` — a(x) = κγμ ≤ 1
- `SemioticContext.p_sub_one_pos` — p - 1 > 0 (from `one_lt_p`)

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026,
  Definitions 2.2 and 3.1.
-/

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]

namespace SemioticContext

variable (ctx : SemioticContext n M)

/-- The creative drive a(x) = κ(x)·γ(x)·μ(x) is nonneg,
    since each factor lies in [0,1].

    Axiom dependencies: `κ_bounds`, `γ_bounds`, `μ_bounds`.
    Upstream candidate: no — paper-specific coefficient structure. -/
theorem a_nonneg (x : M) : 0 ≤ ctx.a x :=
  mul_nonneg (mul_nonneg (ctx.κ_bounds x).1 (ctx.γ_bounds x).1) (ctx.μ_bounds x).1

/-- The creative drive a(x) = κ(x)·γ(x)·μ(x) ≤ 1,
    since each factor lies in [0,1].

    Axiom dependencies: `κ_bounds`, `γ_bounds`, `μ_bounds`.
    Upstream candidate: no — paper-specific coefficient structure. -/
theorem a_le_one (x : M) : ctx.a x ≤ 1 :=
  mul_le_one₀ (mul_le_one₀ (ctx.κ_bounds x).2 (ctx.γ_bounds x).1 (ctx.γ_bounds x).2)
    (ctx.μ_bounds x).1 (ctx.μ_bounds x).2

/-- The saturation exponent satisfies p - 1 > 0.
    Direct consequence of `one_lt_p`.

    Axiom dependencies: `one_lt_p`.
    Upstream candidate: no — paper-specific (wraps `SemioticContext.one_lt_p`). -/
theorem p_sub_one_pos : 0 < ctx.p - 1 := sub_pos.mpr ctx.one_lt_p

end SemioticContext

end
