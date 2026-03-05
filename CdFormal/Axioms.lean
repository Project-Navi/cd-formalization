import CdFormal.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Manifold Bundle

/-!
# PDE Infrastructure Axioms

Axioms encoding classical results from elliptic PDE theory not yet available in
Mathlib for abstract Riemannian manifolds.

## Main definitions

- `SolutionOperator` — the operator T for the BVP (Paper Section 3.2)
- `PrincipalEigendata` — principal eigenvalue and eigenfunction (Paper Definition 3.13)
- `PDEInfra` — typeclass packaging five PDE infrastructure axioms

## Implementation notes

Axioms are packaged in a typeclass so downstream theorems explicitly declare their
dependence via `[PDEInfra bvp solOp]`. The axiom surface consists of:
1. T continuous & compact (placeholder `True` — see known limitation)
2. L∞ bound (maximum principle at interior extremum)
3. Schaefer's fixed-point theorem
4. Fixed-point nonnegativity (maximum principle)
5. Monotone iteration (sub/super-solution, Amann 1976)

## References

- [Schaefer1955] H. Schaefer, "Über die Methode der a priori-Schranken," 1955.
- [Evans2010] L.C. Evans, *Partial Differential Equations*, 2nd ed., Ch. 6.
- [GilbargTrudinger2001] D. Gilbarg and N.S. Trudinger, Ch. 6–8.
- [Amann1976] H. Amann, "Fixed point equations and nonlinear eigenvalue problems," 1976.
- [Spence2026] N. Spence, "The Creative Determinant," 2026.
-/

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (SemioticModel n) ⊤ M]
  [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [SemioticManifold n M]

/-! ## Solution Operator -/

/-- The solution operator T for the BVP. Given u, T(u) solves the linearized equation.
    Paper Section 3.2 (operator formulation).

    Note: We work with `M → ℝ` rather than an explicit Hölder/Sobolev space type.
    The functional-analytic properties (continuity, compactness) are encoded as
    fields of `SolutionOperator` and hypotheses of `PDEInfra`, not silently assumed. -/
structure SolutionOperator (bvp : SemioticBVP n M) where
  /-- The operator T : (M → ℝ) → (M → ℝ) -/
  T : (M → ℝ) → (M → ℝ)
  /-- T(u) satisfies the boundary condition -/
  T_boundary : ∀ u x, x ∈ bvp.boundary → T u x = 0
  /-- Fixed points of T are solutions to the BVP -/
  T_fixed_point : ∀ Φ, T Φ = Φ → IsWeakCoherentConfiguration bvp Φ

/-! ## Principal Eigenvalue -/

/-- The principal eigenvalue problem for -Δ - β·b on the semiotic manifold.
    Paper Definition 3.13. The `beta` parameter generalizes the paper's
    statement (which is the β = 1 case) to allow scaling the potential. -/
structure PrincipalEigendata (bvp : SemioticBVP n M) (beta : ℝ) where
  /-- The principal eigenvalue -/
  eigval : ℝ
  /-- The principal eigenfunction -/
  eigfun : M → ℝ
  /-- The eigenfunction is positive in the interior -/
  eigfun_pos : ∀ x, x ∉ bvp.boundary → eigfun x > 0
  /-- The eigenfunction vanishes on the boundary -/
  eigfun_boundary : ∀ x ∈ bvp.boundary, eigfun x = 0
  /-- The eigenvalue equation: -Δ(eigfun) - β·b·eigfun = eigval·eigfun -/
  eigen_eq : ∀ x,
    -(bvp.ops.laplacian eigfun x) - beta * (bvp.ctx.b x) * (eigfun x) = eigval * (eigfun x)

/-! ## PDE Infrastructure Typeclass

Packages the analytic assumptions needed for existence proofs.
Downstream theorems say `[PDEInfra bvp solOp]` to declare their
dependence on this infrastructure explicitly. -/

/-- The PDE infrastructure required for the Creative Determinant existence theory.
    Each field corresponds to a classical result from elliptic PDE theory. -/
class PDEInfra (bvp : SemioticBVP n M) (solOp : SolutionOperator bvp) : Prop where

  /-- T is continuous and compact on C^{1,α}(M).
      In practice this follows from Schauder estimates + Arzelà-Ascoli
      (paper Lemma 3.7). We state it abstractly since Mathlib lacks the
      function space infrastructure to make this concrete.

      **Known limitation:** This field is currently `True` (a placeholder).
      The `schaefer` axiom below does not reference it, so the compactness
      hypothesis is effectively unguarded. This will be fixed when Mathlib
      gains Hölder spaces on manifolds and/or Schaefer's theorem (see
      drafts/mathlib_issue_schaefer.md).

    Mathlib status: requires Hölder spaces on manifolds (not in Mathlib). -/
  T_continuous_compact : True

  /-- L∞ bound for the Schaefer set (Paper Lemma 3.10).
      If u = τ·T(u) for τ ∈ [0,1], then ‖u‖_∞ ≤ K = (B/c₀)^{1/(p-1)}.
      Proof: evaluate PDE at interior max, use ∇u = 0, Δu ≤ 0.
      Requires p > 1 (from ctx) and c₀ > 0 (from ctx.c_pos).

    Mathlib status: maximum principle for elliptic operators (not in Mathlib
    for abstract manifolds; available for domains in ℝⁿ via Gilbarg-Trudinger). -/
  linfty_bound :
    ∀ (B : ℝ), (∀ x, bvp.ctx.b x ≤ B) →
    ∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K

  /-- Schaefer's fixed-point theorem (Schaefer 1955; Deimling 1985).
      If T is continuous and compact (T_continuous_compact) and the
      Schaefer set S = {u : u = τT(u), τ ∈ [0,1]} is bounded,
      then T has a fixed point.

    Mathlib status: Schaefer's fixed-point theorem is not in Mathlib.
    Draft issue: `drafts/mathlib_issue_schaefer.md`. -/
  schaefer :
    (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K) →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ

  /-- Maximum principle: fixed points of T are nonnegative.
      Follows from the u₊ truncation in the saturation term and
      standard maximum principle arguments.

    Mathlib status: standard maximum principle (not in Mathlib for abstract
    manifolds). -/
  fixed_point_nonneg :
    ∀ (Φ : M → ℝ), solOp.T Φ = Φ → ∀ x, Φ x ≥ 0

  /-- Sub/super-solution monotone iteration (Amann 1976).
      When eigval < 0:
        - εφ₁ is a sub-solution for small ε (paper Thm 3.16, Step 1)
        - A large constant K is a super-solution (Step 2)
        - Monotone iteration between them converges to a nontrivial
          fixed point with Φ > 0 in the interior (Step 3).
      This is the nontriviality bridge, NOT a one-shot existence oracle.

    Mathlib status: sub/super-solution theory (Amann 1976) is not in Mathlib. -/
  monotone_iteration :
    ∀ (beta : ℝ) (eig : PrincipalEigendata bvp beta),
      eig.eigval < 0 →
      ∃ Φ : M → ℝ, solOp.T Φ = Φ ∧ (∃ x, x ∉ bvp.boundary ∧ Φ x > 0)

end
