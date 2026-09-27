/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Basic

/-!
# Operator Consequence Lemmas

Consequences of the fields of `SemioticOperators` in `Basic.lean`.

## Main statements

- `laplacian_zero` — Δ(0) = 0 (from `laplacian_smul` with c = 0)
- `laplacian_linear` — Δ(c·f + g) = c·Δf + Δg (from `laplacian_add` +
  `laplacian_smul`)
- `gradNorm_zero` — |∇(0)| = 0 (from `gradNorm_const` with a = 0)
- `zero_solves_equation` — Φ ≡ 0 satisfies the displayed equation at every point

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.
-/

noncomputable section

open scoped Manifold Bundle

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]
  (ops : SemioticOperators n M)

/-- The Laplacian of the zero function is zero.
    From `laplacian_smul` with c = 0.

    Uses `SemioticOperators.laplacian_smul`. -/
@[simp]
lemma laplacian_zero :
    ops.laplacian (fun _ : M ↦ (0 : ℝ)) = fun _ ↦ 0 := by
  simpa using ops.laplacian_smul (fun _ ↦ (0 : ℝ)) 0

/-- Full linearity of the Laplacian: Δ(c·f + g) = c·Δf + Δg.
    Composed from `laplacian_add` and `laplacian_smul`.

    Uses `SemioticOperators.laplacian_add` and `SemioticOperators.laplacian_smul`. -/
lemma laplacian_linear (f g : M → ℝ) (c : ℝ) :
    ops.laplacian (fun x ↦ c * f x + g x) =
    fun x ↦ c * ops.laplacian f x + ops.laplacian g x := by
  simpa [ops.laplacian_smul] using ops.laplacian_add (fun x ↦ c * f x) g

/-- The gradient norm of the zero function is zero.
    Direct consequence of `gradNorm_const` with a = 0.

    Uses `SemioticOperators.gradNorm_const`. -/
@[simp]
lemma gradNorm_zero (x : M) :
    ops.gradNorm (fun _ : M ↦ (0 : ℝ)) x = 0 :=
  ops.gradNorm_const 0 x

/-- Φ ≡ 0 satisfies the displayed equation at every point. With the default
    `SemioticBVP.equation` the zero function is therefore a weak coherent configuration, so the
    substantive existence statement is the one with a solution positive somewhere. -/
theorem zero_solves_equation (ctx : SemioticContext n M) (x : M) :
    -(ops.laplacian (fun _ ↦ 0) x) =
      ctx.a x * ops.gradNorm (fun _ ↦ 0) x + ctx.b x * 0 - ctx.c x * max (0 : ℝ) 0 ^ ctx.p := by
  simp [Real.zero_rpow (zero_lt_one.trans ctx.one_lt_p).ne']

end
