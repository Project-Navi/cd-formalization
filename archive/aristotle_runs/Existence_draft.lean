/-
Existence of Nontrivial Coherent Configurations (Paper Theorem 3.16)

This file proves existence using the PDE axioms from Axioms.lean.
The proof follows the paper's structure:
  1. L∞ bound (Axiom 1) gives Schaefer set boundedness
  2. Schaefer's theorem (Axiom 2) gives a fixed point
  3. Maximum principle (Axiom 3) gives nonnegativity
  4. Sub/super-solution (Axiom 4) gives nontriviality when eigval < 0

Reference: Spence 2026, Theorems 3.12 and 3.16
-/

import CdFormal.Axioms

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

/-- The viability threshold β* = (π/L)² / b for constant viability b on [0,L]. -/
def viability_threshold (L : ℝ) (b : ℝ) (hL : L > 0) (hb : b > 0) : ℝ :=
  (Real.pi / L) ^ 2 / b

/-- Spectral characterization (1D): β > β* implies eigenvalue < 0.
    Proved independently by Aristotle in runs 8654be8c and 017f6779. -/
theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ)
    (hL : L > 0) (hb : b > 0) :
    let beta_star := viability_threshold L b hL hb
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0 := by
  intro beta_star h_beta
  have h_mul : beta * b > (Real.pi / L) ^ 2 := by
    rwa [gt_iff_lt, div_lt_iff₀ hb] at h_beta
  grind

/-- Theorem 3.12 (Existence of weak coherent configurations).
    Under the coefficient hypotheses, the BVP admits at least one
    nonnegative solution. -/
theorem existence_weak_coherent_configuration
    {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModelAbbrev n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifoldV2 n M]
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) := by
  -- Step 1: L∞ bound gives Schaefer set boundedness
  have h_bounded := linfty_bound_schaefer_set bvp solOp B hB
  -- Step 2: Schaefer's theorem gives a fixed point
  have h_exists := schaefer_fixed_point bvp solOp h_bounded
  obtain ⟨Phi, hfix⟩ := h_exists
  -- Step 3: Fixed point is a weak coherent configuration
  have h_wcc := solOp.T_fixed_point Phi hfix
  -- Step 4: Maximum principle gives nonnegativity
  have h_nonneg := fixed_point_nonneg bvp solOp Phi hfix
  exact ⟨Phi, h_wcc, h_nonneg⟩

/-- Theorem 3.16 (Existence of NONTRIVIAL weak coherent configurations).
    When the principal eigenvalue is negative (viability exceeds dissipation),
    there exists a positive solution — coherent presence can be self-maintained. -/
theorem existence_nontrivial_coherent_configuration
    {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (SemioticModelAbbrev n) ⊤ M]
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [SemioticManifoldV2 n M]
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    (beta : ℝ)
    (eig : PrincipalEigendata bvp beta)
    (eigval_neg : eig.eigval < 0) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) ∧
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0) := by
  -- Sub/super-solution gives nontrivial fixed point
  have h_ntfp := nontrivial_fixed_point_from_eigenvalue bvp solOp beta eig eigval_neg
  obtain ⟨Phi, hfix, x, hx_int, hx_pos⟩ := h_ntfp
  -- Fixed point is a weak coherent configuration
  have h_wcc := solOp.T_fixed_point Phi hfix
  -- Maximum principle gives nonnegativity
  have h_nonneg := fixed_point_nonneg bvp solOp Phi hfix
  exact ⟨Phi, h_wcc, h_nonneg, x, hx_int, hx_pos⟩

/-- Scaling algebraic contradiction: if p > 1, k > 1, c > 0, Phi > 0,
    then -c·k·Phi^p cannot be ≤ -c·k^p·Phi^p.
    Proved by Aristotle in run 017f6779. -/
lemma scaling_algebraic_contradiction
    (p : ℝ) (k : ℝ) (c : ℝ) (Phi_val : ℝ)
    (hp : p > 1) (hk : k > 1) (hc : c > 0) (hPhi : Phi_val > 0)
    (h_eq : -c * k * Phi_val^p ≤ -c * k^p * Phi_val^p) :
    False := by
  have h_div : k ≥ k ^ p := by
    nlinarith [show 0 < c * Phi_val ^ p by positivity]
  exact h_div.not_lt (by simpa using Real.rpow_lt_rpow_of_exponent_lt hk hp)

end
