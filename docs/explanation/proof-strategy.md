# Proof Strategy

## Design

The continuum results are conditional. Classical elliptic theory on manifolds (Schauder estimates, maximum principles, Schaefer's fixed-point theorem, sub/super-solution iteration) is not in Mathlib, so the analytic steps are stated as fields of the `Prop`-valued class `PDEInfra` and of the structure `SolutionOperator`. The existence theorems take them as hypotheses, so every dependency is visible in the signature. The [assumption boundary](axiom-boundary.md) page states what each field says.

The steps that need no analysis are proved outright: the algebraic half of the L∞ bound, the order-theoretic core of the sub/super-solution method, the one-dimensional spectral inequality, and the scaling argument.

## Existence of a nonnegative solution (Paper Theorem 3.12)

\[
\text{a priori bound} \;\longrightarrow\; \text{fixed point of } T \;\longrightarrow\; \text{solution}, \ \Phi \geq 0
\]

```lean
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
```

`PDEInfra.linfty_bound` bounds the Schaefer set, `PDEInfra.schaefer` turns that bound and `PDEInfra.T_compact` into a fixed point of \(T\), and `SolutionOperator.T_fixed_point` and `PDEInfra.fixed_point_nonneg` make it a nonnegative solution.

The zero function already solves the displayed problem, which is the default value of `SemioticBVP.equation` (`zero_solves_equation`: \(\Delta 0 = 0\), \(|\nabla 0| = 0\) and \(0^p = 0\)). The informative statement is the next one.

## A solution that is positive somewhere (Paper Theorem 3.16)

```lean
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
```

`PDEInfra.monotone_iteration` supplies a fixed point of \(T\) that is positive at one interior point; the rest is as above. The conclusion is positivity at some interior point, not at every one.

## Proved outright

**L∞ bound, algebraic half (Paper Lemma 3.10).** At an interior maximum the equation reduces to \(b v \geq c v^p\). `rpow_le_of_mul_rpow_le` divides by \(c v > 0\) to get \(v^{p-1} \leq b/c\), and `linfty_bound_algebraic` takes the \((p-1)\)-th root:

\[
b v \geq c v^p,\ v > 0,\ c > 0,\ p > 1 \quad\Longrightarrow\quad v \leq (b/c)^{1/(p-1)}.
\]

The maximum-principle half remains inside `PDEInfra.linfty_bound`.

**Sub/super-solution core.** `monotone_fixed_point_between`: a monotone map \(f\) on a complete lattice with \(\mathrm{sub} \leq f(\mathrm{sub})\), \(f(\mathrm{super}) \leq \mathrm{super}\) and \(\mathrm{sub} \leq \mathrm{super}\) has a fixed point between them. The proof takes `OrderHom.nextFixed` of the sub-fixed point and bounds it with `OrderHom.nextFixed_le_of_le`. It uses only `propext` and `Quot.sound`.

**One-dimensional spectral inequality.** `spectral_characterization_1d`: if \(b > 0\) and \(\beta > (\pi/L)^2/b\), then \((\pi/L)^2 - \beta b < 0\); `viabilityThreshold_lt_iff` gives the converse. For constant \(b\), \((\pi/L)^2 - \beta b\) is the principal Dirichlet eigenvalue of \(-d^2/dx^2 - \beta b\) on \([0, L]\); that identification is classical and not formalized.

**Scaling.** `scaling_uniqueness`: if \(\Phi\) and \(k\Phi\) with \(k > 1\) both satisfy the displayed equation, and \(c(x_0) > 0\), \(\Phi(x_0) > 0\) at some point, then linearity of \(\Delta\), homogeneity of \(|\nabla\cdot|\) and \((k\Phi)^p = k^p \Phi^p\) give \(k = k^p\), contradicting `Real.self_lt_rpow_of_one_lt`. This rules out solution multiples of a solution; it is not uniqueness among all solutions.
