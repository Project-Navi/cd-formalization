/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
import CdFormal.Basic
import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# PDE Infrastructure Hypotheses

Hypotheses standing in for classical results from elliptic PDE theory that are not available
in Mathlib for abstract Riemannian manifolds. They are fields of structures and of a
`Prop`-valued class, not Lean axioms: `#print axioms` does not list them, and a theorem that
uses them takes them as arguments.

## Main definitions

- `SolutionOperator` — the operator T for the BVP (Paper Section 3.2)
- `PrincipalEigendata` — principal eigenvalue and eigenfunction (Paper Definition 3.13)
- `PDEInfra` — class bundling five analytic hypotheses

## Implementation notes

Downstream theorems declare their dependence via `[PDEInfra bvp solOp]`. The fields are:
1. `T_compact`: T maps von Neumann bounded sets to sets with compact closure
2. `linfty_bound`: an a priori bound on the Schaefer set (maximum principle)
3. `schaefer`: a fixed point of T from the two above (Schaefer's theorem)
4. `fixed_point_nonneg`: fixed points are nonnegative (maximum principle)
5. `monotone_iteration`: a fixed point positive at an interior point (sub/super-solutions)

They are stated on the bare function type `M → ℝ` with its product topology, so they are
assumptions about the given `T`, not instances of the classical theorems; see each field.

## References

- [Schaefer1955] H. Schaefer, "Über die Methode der a priori-Schranken," 1955.
- [Evans2010] L.C. Evans, *Partial Differential Equations*, 2nd ed., Ch. 6.
- [GilbargTrudinger2001] D. Gilbarg and N.S. Trudinger, Ch. 6–8.
- [Amann1976] H. Amann, "Fixed point equations and nonlinear eigenvalue problems," 1976.
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

/-! ## Solution Operator -/

/-- The solution operator T for the BVP. Classically, T(u) solves the equation linearized at
    u. Paper Section 3.2 (operator formulation).

    Here T is an arbitrary map on `M → ℝ`, not a Hölder or Sobolev space, and nothing ties it to
    the operators of `bvp` except `T_fixed_point`, which assumes that its fixed points are
    solutions. Compactness is a hypothesis of `PDEInfra`; continuity is not assumed. -/
structure SolutionOperator (bvp : SemioticBVP n M) where
  /-- The operator T : (M → ℝ) → (M → ℝ) -/
  T : (M → ℝ) → (M → ℝ)
  /-- T(u) satisfies the boundary condition -/
  T_boundary : ∀ u x, x ∈ bvp.boundary → T u x = 0
  /-- Fixed points of T are solutions to the BVP (assumed) -/
  T_fixed_point : ∀ Φ, T Φ = Φ → IsWeakCoherentConfiguration bvp Φ

/-! ## Principal Eigenvalue -/

/-- Supplied eigendata for -Δ - β·b on the semiotic manifold: an eigenvalue and an eigenfunction
    that is positive off the boundary and zero on it. It is not constructed from the operators.
    Paper Definition 3.13. The equation of `SemioticBVP` corresponds to β = 1. -/
structure PrincipalEigendata (bvp : SemioticBVP n M) (beta : ℝ) where
  /-- The principal eigenvalue -/
  eigval : ℝ
  /-- The principal eigenfunction -/
  eigfun : M → ℝ
  /-- The eigenfunction is positive in the interior -/
  eigfun_pos : ∀ x, x ∉ bvp.boundary → eigfun x > 0
  /-- The eigenfunction vanishes on the boundary -/
  eigfun_boundary : ∀ x ∈ bvp.boundary, eigfun x = 0
  /-- The eigenvalue equation -Δ(eigfun) - β·b·eigfun = eigval·eigfun, at every point -/
  eigen_eq : ∀ x,
    -(bvp.ops.laplacian eigfun x) - beta * (bvp.ctx.b x) * (eigfun x) = eigval * (eigfun x)

/-! ## PDE Infrastructure Typeclass

Packages the analytic hypotheses of the existence proofs.
Downstream theorems say `[PDEInfra bvp solOp]` to declare their
dependence on them explicitly. -/

/-- The analytic hypotheses of the Creative Determinant existence theory.
    Each field stands in for a classical result from elliptic PDE theory. -/
class PDEInfra (bvp : SemioticBVP n M) (solOp : SolutionOperator bvp) : Prop where

  /-- T maps von Neumann bounded sets to sets with compact closure: T is locally bounded from
      `vonNBornology ℝ (M → ℝ)` to `Bornology.relativelyCompact (M → ℝ)`. This bornological
      formulation follows a suggestion by Yongxi Lin (Aaron) on Lean Zulip.

      On `M → ℝ` with the product topology, both conditions are pointwise: S is von Neumann
      bounded exactly when it is pointwise bounded, and T '' S has compact closure exactly when
      it is pointwise bounded. Paper Lemma 3.7 instead gives compactness in Hölder norms, from
      Schauder estimates and Arzelà–Ascoli. The `schaefer` field takes this condition as a
      hypothesis.

    Mathlib status: the Hölder-space proof needs Schauder theory on manifolds. -/
  T_compact : ∀ S : Set (M → ℝ),
    Bornology.IsVonNBounded ℝ S →
    IsCompact (closure (solOp.T '' S))

  /-- L∞ bound for the Schaefer set (Paper Lemma 3.10): some K > 0 bounds every u with
      u = τ·T(u), τ ∈ [0,1]. Classically K = (B/c₀)^{1/(p-1)}, from the equation at an interior
      maximum, where ∇u = 0 and Δu ≤ 0; that algebraic step is `linfty_bound_algebraic`.

    Mathlib status: maximum principle for elliptic operators (not in Mathlib
    for abstract manifolds; available for domains in ℝⁿ via Gilbarg-Trudinger). -/
  linfty_bound :
    ∀ (B : ℝ), (∀ x, bvp.ctx.b x ≤ B) →
    ∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K

  /-- Stands in for Schaefer's fixed-point theorem (Schaefer 1955; Deimling 1985): if T satisfies
      `T_compact` and the Schaefer set S = {u : u = τT(u), τ ∈ [0,1]} is bounded, then T has a
      fixed point. The theorem also needs T to be continuous on a Banach space; no continuity
      is assumed here, so this is an assumption about the given T.

    Mathlib status: Schaefer's fixed-point theorem is not in Mathlib. -/
  schaefer :
    (∀ S : Set (M → ℝ), Bornology.IsVonNBounded ℝ S →
      IsCompact (closure (solOp.T '' S))) →
    (∃ K > 0, ∀ (u : M → ℝ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 →
      (∀ x, u x = τ * solOp.T u x) →
      ∀ x, |u x| ≤ K) →
    ∃ Φ : M → ℝ, solOp.T Φ = Φ

  /-- Fixed points of T are nonnegative. Classically this follows from the u₊ truncation in
      the saturation term and the maximum principle.

    Mathlib status: standard maximum principle (not in Mathlib for abstract
    manifolds). -/
  fixed_point_nonneg :
    ∀ (Φ : M → ℝ), solOp.T Φ = Φ → ∀ x, Φ x ≥ 0

  /-- Stands in for sub/super-solution monotone iteration (Amann 1976): when eigval < 0, εφ₁ is
      a sub-solution for small ε, a large constant is a super-solution, and iteration between
      them gives a solution (paper Thm 3.16). The field asserts a fixed point of T that is
      positive at one interior point.

      It is stated for every β, but the equation uses b itself (β = 1). For other β it assumes
      more than the classical result: with a ≡ 0 and c > 0, a positive solution exists only if
      the principal eigenvalue of -Δ - b is negative, which does not follow from negativity
      for -Δ - βb with β > 1.

    Mathlib status: sub/super-solution theory (Amann 1976) is not in Mathlib. -/
  monotone_iteration :
    ∀ (beta : ℝ) (eig : PrincipalEigendata bvp beta),
      eig.eigval < 0 →
      ∃ Φ : M → ℝ, solOp.T Φ = Φ ∧ (∃ x, x ∉ bvp.boundary ∧ Φ x > 0)

end
