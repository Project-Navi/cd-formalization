import CdFormal.Axioms

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

/-!
# Creative Determinant — Theorems

## Main statements

- `spectral_characterization_1d` — β > β* implies eigenvalue < 0 (pure algebra)
- `scaling_algebraic_contradiction` — k < kᵖ when p > 1 (pure algebra)
- `SemioticBVP.exists_isWeakCoherentConfiguration` — existence of nonneg
  solutions (Paper Thm 3.12)
- `SemioticBVP.exists_pos_isWeakCoherentConfiguration` — existence of
  positive solutions (Paper Thm 3.16)

## Implementation notes

The first two results are proved by pure algebra (no PDE axioms).
The existence theorems compose `PdeInfra` axioms; all dependencies are visible
via `[PdeInfra bvp solOp]` and `#print axioms` in `CdFormal.Verify`.

## References

- [Spence2026] N. Spence, "The Creative Determinant," 2026.
-/

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]

/-! ## Spectral Characterization (1D)

For constant viability b on [0,L], the principal eigenvalue is
  eigval = (π/L)² - β·b
The condition eigval < 0 is equivalent to β > β* := (π/L)²/b.

Proved independently by Aristotle in runs 8654be8c and 017f6779.
No axiom dependencies — pure algebra. -/

/-- The viability threshold β* = (π/L)² / b for constant viability b on [0,L]. -/
def viabilityThreshold (L : ℝ) (b : ℝ) (_ : L > 0) (_ : b > 0) : ℝ :=
  (Real.pi / L) ^ 2 / b

/-- Spectral characterization (1D, constant coefficients): β > β* implies
    the principal eigenvalue λ₁ = (π/L)² − βb is negative. This is the
    constant-coefficient case on [0,L]; the general manifold statement
    requires Courant–Fischer theory not yet in Mathlib. -/
theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ)
    (hL : L > 0) (hb : b > 0) :
    let beta_star := viabilityThreshold L b hL hb
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0 := by
  intro beta_star h_beta
  have h1 : beta > (Real.pi / L) ^ 2 / b := h_beta
  have h2 : beta * b > (Real.pi / L) ^ 2 := by
    rwa [gt_iff_lt, div_lt_iff₀ hb] at h1
  linarith

/-! ## Scaling Algebraic Contradiction

If p > 1, k > 1, c > 0, Φ > 0, then k < k^p (used in uniqueness arguments).

Proved by Aristotle in run 017f6779. No axiom dependencies — pure algebra. -/

lemma scaling_algebraic_contradiction
    (p : ℝ) (k : ℝ) (c : ℝ) (Phi_val : ℝ)
    (hp : p > 1) (hk : k > 1) (hc : c > 0) (hPhi : Phi_val > 0)
    (h_eq : -c * k * Phi_val ^ p ≤ -c * k ^ p * Phi_val ^ p) :
    False := by
  have hcΦp : (0 : ℝ) < c * Phi_val ^ p := by positivity
  have h_div : k ≥ k ^ p := by nlinarith
  have h_lt : k < k ^ p := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hk hp
    simp only [Real.rpow_one] at h
    exact h
  linarith

/-! ## Existence Theorems (from PdeInfra typeclass)

These compose the PDE infrastructure axioms to prove existence.
The proof logic is verified; the PDE infrastructure is axiomatized.
All axiom dependencies are visible via `[PdeInfra bvp solOp]`. -/

/-- Paper Theorem 3.12: The BVP admits at least one nonneg solution.
    Proof: L∞ bound → Schaefer set bounded → Schaefer fixed point → max principle. -/
theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PdeInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) := by
  have h_bounded := infra.linfty_bound B hB
  obtain ⟨Phi, hfix⟩ := infra.schaefer h_bounded
  exact ⟨Phi, solOp.T_fixed_point Phi hfix, infra.fixed_point_nonneg Phi hfix⟩

/-- Paper Theorem 3.16: When viability exceeds dissipation (eigval < 0),
    there exists a positive solution — coherent presence can be self-maintained.
    Proof: monotone iteration (sub/super-solution) → nontrivial fixed point → max principle.

    Note: The paper's Thm 3.16 says "assume the hypotheses of Thm 3.12" (including
    bounded b). This Lean statement omits `B`/`hB` because the `monotone_iteration`
    axiom uses a different proof route (sub/super-solution) that does not require
    an explicit bound on b. The two theorems are independent in the formalization. -/
theorem SemioticBVP.exists_pos_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PdeInfra bvp solOp]
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
