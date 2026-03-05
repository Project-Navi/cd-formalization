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
# Operator Consequence Lemmas

Derived properties of `SemioticOperators` from the axioms in `Basic.lean`.
These validate that the operator contract is well-formed and non-vacuous.

## Main statements

- `laplacian_zero` — Δ(0) = 0 (from `laplacian_smul` with c = 0)
- `gradNorm_zero` — |∇(0)| = 0 (from `gradNorm_smul` with c = 0)

## References

- Aristotle run `41cee644-80f9-4122-9c7d-c32dc1b571d6` (original proofs against
  pre-Phase 2 axiom set, adapted here for current axioms).
-/

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]
  (ops : SemioticOperators n M)

/-- The Laplacian of the zero function is zero.
    From `laplacian_smul` with c = 0.

    Axiom dependencies: `SemioticOperators.laplacian_smul`.
    Upstream candidate: trivial consequence of linearity. -/
lemma laplacian_zero :
    ops.laplacian (fun _ : M => (0 : ℝ)) = fun _ => 0 := by
  have h := ops.laplacian_smul (fun _ => (0 : ℝ)) 0
  simp only [zero_mul] at h
  exact h

/-- The gradient norm of the zero function is zero.
    From `gradNorm_smul` with c = 0.

    Axiom dependencies: `SemioticOperators.gradNorm_smul`.
    Upstream candidate: trivial consequence of homogeneity. -/
lemma gradNorm_zero (x : M) :
    ops.gradNorm (fun _ : M => (0 : ℝ)) x = 0 := by
  have h := ops.gradNorm_smul (fun _ => (0 : ℝ)) 0 x
  simp only [zero_mul, abs_zero] at h
  exact h

end
