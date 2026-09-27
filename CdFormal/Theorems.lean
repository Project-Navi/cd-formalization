/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Axioms
import Mathlib.Tactic

/-!
# Creative Determinant — Theorems

## Main statements

- `spectral_characterization_1d` — β > β* implies (π/L)² - βb < 0 (algebra)
- `viabilityThreshold_lt_iff` — for b > 0, β > β* exactly when (π/L)² - βb < 0
- `scaling_algebraic_contradiction` — k < kᵖ when p > 1 (algebra)
- `SemioticBVP.exists_isWeakCoherentConfiguration` — a nonnegative solution
  (Paper Thm 3.12), conditional on `PDEInfra`
- `SemioticBVP.exists_pos_isWeakCoherentConfiguration` — a nonnegative solution that is
  positive at some interior point (Paper Thm 3.16), conditional on `PDEInfra`

## Implementation notes

The algebraic results use no hypotheses. The existence theorems compose the fields of
`PDEInfra` and `SolutionOperator`, which appear as arguments in their signatures; `#print axioms`
lists only Lean axioms and so does not show them.

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

/-! ## Spectral Characterization (1D)

For constant viability b on [0,L], the principal Dirichlet eigenvalue of -d²/dx² - β·b is
  eigval = (π/L)² - β·b.
That identification is classical and not formalized here. For b > 0, eigval < 0 is equivalent
to β > β* := (π/L)²/b (`viabilityThreshold_lt_iff`). -/

/-- The viability threshold β* = (π/L)² / b for constant viability b on [0,L]. -/
def viabilityThreshold (L : ℝ) (b : ℝ) : ℝ :=
  (Real.pi / L) ^ 2 / b

/-- Spectral characterization (1D, constant coefficients): β > β* implies (π/L)² − βb < 0.
    For constant b this expression is the principal Dirichlet eigenvalue of -d²/dx² - βb on
    [0,L]; that identification, and any statement on a manifold, is not formalized. -/
theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ) (hb : b > 0) :
    let beta_star := viabilityThreshold L b
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0 := by
  intro _ h; have := (div_lt_iff₀ hb).mp h; linarith

/-- For b > 0, β exceeds the threshold β* exactly when (π/L)² − βb < 0. -/
theorem viabilityThreshold_lt_iff (L : ℝ) {b : ℝ} (hb : 0 < b) (beta : ℝ) :
    viabilityThreshold L b < beta ↔ (Real.pi / L) ^ 2 - beta * b < 0 := by
  rw [viabilityThreshold, div_lt_iff₀ hb, sub_neg]

/-! ## Scaling Algebraic Contradiction

If p > 1, k > 1, c > 0, Φ > 0, then k < k^p (used in uniqueness arguments). -/

/-- If p > 1, k > 1, c > 0, Φ > 0, and -c·k·Φᵖ ≤ -c·kᵖ·Φᵖ, then False.
    The core fact is k < kᵖ for k > 1 and p > 1
    (`Real.self_lt_rpow_of_one_lt`), contradicting the hypothesis. -/
lemma scaling_algebraic_contradiction
    (p : ℝ) (k : ℝ) (c : ℝ) (Phi_val : ℝ)
    (hp : p > 1) (hk : k > 1) (hc : c > 0) (hPhi : Phi_val > 0)
    (h_eq : -c * k * Phi_val ^ p ≤ -c * k ^ p * Phi_val ^ p) :
    False := by
  have : (0 : ℝ) < c * Phi_val ^ p := by positivity
  nlinarith [Real.self_lt_rpow_of_one_lt hk hp]

/-! ## Existence Theorems (conditional on `PDEInfra`)

These compose the hypotheses in `PDEInfra` and `SolutionOperator`. The composition is
checked; the hypotheses are assumed and appear as arguments. -/

/-- Paper Theorem 3.12: the BVP admits at least one nonnegative solution.
    Proof: L∞ bound → Schaefer set bounded → fixed point of T → nonnegativity.

    Uses `PDEInfra.T_compact`, `PDEInfra.linfty_bound`, `PDEInfra.schaefer`,
    `PDEInfra.fixed_point_nonneg` and `SolutionOperator.T_fixed_point`. With the default
    `SemioticBVP.equation`, Φ ≡ 0 is already a solution (`zero_solves_equation`). -/
theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) := by
  obtain ⟨Phi, hfix⟩ := infra.schaefer infra.T_compact (infra.linfty_bound B hB)
  exact ⟨Phi, solOp.T_fixed_point Phi hfix, infra.fixed_point_nonneg Phi hfix⟩

/-- Paper Theorem 3.16: if the supplied eigenvalue is negative, there is a nonnegative solution
    that is positive at some interior point. Proof: monotone iteration (sub/super-solution) →
    fixed point of T positive at an interior point → nonnegativity.

    Uses `PDEInfra.monotone_iteration`, `PDEInfra.fixed_point_nonneg` and
    `SolutionOperator.T_fixed_point`. The conclusion is positivity at one interior point, not
    throughout the interior. `beta` is arbitrary because `PDEInfra.monotone_iteration` is
    stated for every β; the equation itself corresponds to β = 1.

    Note: The paper's Thm 3.16 says "assume the hypotheses of Thm 3.12"
    (including bounded b). This Lean statement omits `B`/`hB` because
    `monotone_iteration` uses sub/super-solution theory that does not
    require an explicit bound on b. -/
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
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0) := by
  obtain ⟨Phi, hfix, x, hx_int, hx_pos⟩ := infra.monotone_iteration beta eig eigval_neg
  exact ⟨Phi, solOp.T_fixed_point Phi hfix,
    infra.fixed_point_nonneg Phi hfix, x, hx_int, hx_pos⟩

end
