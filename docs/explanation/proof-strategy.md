# Proof Strategy

## Design

The continuum results are conditional. Classical elliptic theory on manifolds (Schauder estimates, maximum principles, Schaefer's fixed-point theorem, sub/super-solution iteration) is not in Mathlib, so the analytic steps are stated as fields of the `Prop`-valued class `PDEInfra` and of the structure `SolutionOperator`. The existence theorems take them as hypotheses, so every dependency is visible in the signature. The [assumption boundary](axiom-boundary.md) page states what each field says.

The steps that need no analysis are proved outright: the algebraic half of the L∞ bound, the order-theoretic core of the sub/super-solution method, the one-dimensional spectral inequality, and the scaling argument.

On a finite graph the analysis is finite-dimensional, and the whole argument is carried out: [finite-graph existence](#finite-graph-existence) below uses no hypothesis of the kind above.

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

## Finite-graph existence

`SemioticGraph.exists_pos_graph` is proved with every ingredient constructed: the graph operators, the principal eigendata, the barriers and the fixed point. Its hypotheses are that the interior graph is connected, that the principal eigenvalue is negative, and that \(a(x) \le \sqrt{w(x,y)}\) and \(a(y) \le \sqrt{w(x,y)}\) for every edge of positive weight between distinct interior vertices \(x\) and \(y\).

**Principal eigenvector** (`CdFormal/Graph/Spectral.lean`). Functions that vanish on the boundary and satisfy \(\sum_x u(x)^2 = 1\) form a compact set, nonempty because the connected interior graph has a vertex, so the energy

\[
E(u) = \tfrac12 \sum_x \sum_y w(x,y)\,(u(x) - u(y))^2 - \sum_x b(x)\,u(x)^2
\]

attains its infimum \(\lambda_1\) (`SemioticGraph.principalEigenvalue`) at some \(\varphi\). For \(h\) vanishing on the boundary, \(t \mapsto E(\varphi + t h) - \lambda_1 \sum_x (\varphi + t h)(x)^2\) is a nonnegative quadratic with no constant term, so its linear coefficient is zero; with \(h = L\varphi - b\varphi - \lambda_1\varphi\) off the boundary this gives \(L\varphi = b\varphi + \lambda_1\varphi\) at every interior vertex. Since \(E(|\varphi|) \le E(\varphi)\), \(|\varphi|\) is also a minimizer. At an interior zero of \(|\varphi|\) the equation says \(\sum_y w(x,y)\,|\varphi(y)| = 0\), so \(|\varphi|\) vanishes at every neighbour; on a connected interior graph it would then vanish everywhere, contradicting \(\sum_x \varphi(x)^2 = 1\). This is `SemioticGraph.exists_pos_eigenvector`. No Dirichlet eigenvalue is smaller: an eigenvector \(u\) for \(\mu\) has \(E(u) = \mu \sum_x u(x)^2\), so \(\lambda_1 \le \mu\) (`SemioticGraph.principalEigenvalue_le_of_laplacian_eq`).

**Fixed-point map** (`CdFormal/Graph/FixedPoint.lean`). With \(d(x) = \sum_y w(x,y)\) and a constant \(K > 0\), the equation at an interior vertex is equivalent to

\[
u(x) = \frac{\sum_y w(x,y)\,u(y) + a(x)\,|\nabla u|(x) + (b(x) + K)\,u(x) - c(x)\max(u(x), 0)^p}{d(x) + K},
\]

and `SemioticGraph.fixedPointMap` sends \(u\) to this right-hand side at interior vertices and to \(0\) on the boundary. For \(K > 0\) its fixed points are exactly the solutions (`SemioticGraph.fixedPointMap_eq_iff_isSolution`). On functions with values in \([0, M]\) that vanish on the boundary it is monotone when \(K\) is large (`SemioticGraph.fixedPointMap_mono`). Raising \(u\) by \(\delta\) at a neighbour \(y\) lowers \(a(x)\,|\nabla u|(x)\) by at most \(a(x)\sqrt{w(x,y)}\,\delta \le w(x,y)\,\delta\), which the term \(w(x,y)\,u(y)\) makes up; this is where the edge condition is used. The dependence on \(u(x)\) itself, through the gradient norm and through \(c\,u^p\), which is Lipschitz on \([0, M]\), is absorbed by \(K\).

**Barriers.** A small multiple \(\varepsilon\varphi\) with \(\varepsilon > 0\) is a subsolution once \(c(x)\,\varepsilon^{p-1} \le -\lambda_1\) for every \(x\) (`SemioticGraph.smul_subsolution`). The function equal to \(M\) off the boundary and \(0\) on it is a supersolution once \(a(x)^2/4 + b(x) \le c(x)\,M^{p-1}\) for every \(x\) (`SemioticGraph.plateau_supersolution`). It is not constant: next to the boundary its Laplacian is \(S = M\sum_{y \in \text{boundary}} w(x,y)\) and its gradient norm is \(\sqrt{M S}\), and \(a\sqrt{M S} \le S + M a^2/4\) accounts for the gradient term.

**Fixed point.** The map sends the order interval between the two barriers into itself. That interval is a complete lattice, so `monotone_fixed_point_between` gives a fixed point in it (`SemioticGraph.exists_isSolution_between`). The fixed point solves the equation and is at least \(\varepsilon\varphi > 0\) at every interior vertex. The constants \(\varepsilon\), \(M\) and \(K\) are defined from the data inside the proof.

The edge condition is used only for monotonicity. It is sufficient for this argument; it is not claimed to be necessary for existence. For weights in \(\{0, 1\}\) it follows from \(0 \le a \le 1\) (`SemioticGraph.exists_pos_graph_of_unweighted`). The discretization (unnormalized weights, the symmetric gradient norm, zero boundary values entering through boundary edges) is the one chosen for this formalization. Andrew Edmark (@aedmark) proposed the finite-graph formulation and the route of the proof: finite-dimensional inverse positivity and positive principal eigendata, then the existing order-theoretic fixed-point core. The discretization, the Jacobi splitting used for inverse positivity and the edge condition were chosen for this formalization and are not claimed to be his.
