/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal

/-!
# Statement files for the headline results

Each declaration below restates one headline result of the library with its statement written
out in full and its proof replaced by `sorry`. The `sorry` is deliberate: this file is the
specification, not the proof. `spec/Check.lean` compares the type of every statement here with
the type of the library declaration of the same name (alpha-equivalence after instantiating the
universe parameters), confirms that the library declaration is a theorem with a proof term, and
walks its axioms. CI runs that comparison, so a reader can check a headline claim against this
file alone, and a change to a library statement that is not mirrored here fails CI.

This library is not a default target, is never imported by `CdFormal`, and lies outside the
placeholder audit, which covers the `CdFormal` tree only.

## The named gap `gap:pde-infra`

`SemioticBVP.exists_isWeakCoherentConfiguration` and
`SemioticBVP.exists_pos_isWeakCoherentConfiguration` take the class `PDEInfra` and the
structures `SolutionOperator` and `PrincipalEigendata` as hypotheses. Their fields are
propositions that no file instantiates, and `#print axioms` cannot see them. The statements
below show those hypotheses in full; the two theorems are implications, and the obligation to
discharge their hypotheses for a concrete operator is the gap named `gap:pde-infra` in
docs/explanation/axiom-boundary.md and docs/reference/verification-audit.md.
-/

-- The proofs below are `sorry` by design, so every hypothesis is unused.
set_option linter.unusedVariables false

noncomputable section

open scoped Manifold Bundle

namespace Spec

section Continuum

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]

/-- Statement of `SemioticBVP.exists_isWeakCoherentConfiguration` (paper Theorem 3.12).
    Conditional: `gap:pde-infra`. -/
theorem SemioticBVP.exists_isWeakCoherentConfiguration
    (bvp : SemioticBVP n M)
    (solOp : SolutionOperator bvp)
    [infra : PDEInfra bvp solOp]
    (B : ℝ) (hB : ∀ x, bvp.ctx.b x ≤ B) :
    ∃ Phi : M → ℝ,
      IsWeakCoherentConfiguration bvp Phi ∧
      (∀ x, Phi x ≥ 0) := sorry

/-- Statement of `SemioticBVP.exists_pos_isWeakCoherentConfiguration` (paper Theorem 3.16).
    Conditional: `gap:pde-infra`. -/
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
      (∃ x, x ∉ bvp.boundary ∧ Phi x > 0) := sorry

/-- Statement of `scaling_uniqueness`: no solution has a solution multiple kΦ with k > 1 at a
    point where c > 0 and Φ > 0. Unconditional. -/
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
    False := sorry

end Continuum

/-- Statement of `spectral_characterization_1d`: for b > 0, β above the threshold
    (π/L)²/b gives (π/L)² − βb < 0. Arithmetic; the eigenvalue identification is classical. -/
theorem spectral_characterization_1d
    (L : ℝ) (b : ℝ) (beta : ℝ) (hb : b > 0) :
    let beta_star := viabilityThreshold L b
    beta > beta_star → (Real.pi / L) ^ 2 - beta * b < 0 := sorry

/-- Statement of `linfty_bound_algebraic`: from b·v ≥ c·v^p, v ≤ (b/c)^{1/(p−1)}. -/
theorem linfty_bound_algebraic
    (v b c p : ℝ) (hv : v > 0) (hc : c > 0) (hp : p > 1)
    (h : b * v ≥ c * v ^ p) :
    v ≤ (b / c) ^ (1 / (p - 1)) := sorry

section Order

universe u

variable {α : Type u} [CompleteLattice α] (f : α →o α)

/-- Statement of `monotone_fixed_point_between`: a monotone self-map of a complete lattice has a
    fixed point between an ordered sub-fixed point and super-fixed point. -/
theorem monotone_fixed_point_between
    {sub super : α}
    (h_sub : sub ≤ f sub)
    (h_super : f super ≤ super)
    (h_le : sub ≤ super) :
    ∃ x : α, f x = x ∧ sub ≤ x ∧ x ≤ super := sorry

end Order

section Graph

variable {V : Type*} [Fintype V] (G : SemioticGraph V)

/-- Statement of `SemioticGraph.exists_pos_graph` (paper Theorem 3.23): connected interior,
    the edge condition and a negative principal eigenvalue give a solution positive at every
    interior vertex. Unconditional. -/
theorem SemioticGraph.exists_pos_graph (hconn : G.interiorGraph.Connected)
    (hdom : ∀ x y, x ∉ G.boundary → y ∉ G.boundary → x ≠ y → 0 < G.w x y →
      G.a x ≤ √(G.w x y))
    (hneg : G.principalEigenvalue < 0) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ x, x ∉ G.boundary → 0 < u x := sorry

/-- Statement of `SemioticGraph.exists_pos_graph_of_unweighted`: with 0/1 weights the edge
    condition is automatic. Unconditional. -/
theorem SemioticGraph.exists_pos_graph_of_unweighted (hw : ∀ x y, G.w x y = 0 ∨ G.w x y = 1)
    (hconn : G.interiorGraph.Connected) (hneg : G.principalEigenvalue < 0) :
    ∃ u : V → ℝ, G.IsSolution u ∧ ∀ x, x ∉ G.boundary → 0 < u x := sorry

end Graph

end Spec

end
