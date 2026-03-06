# Technical Debt Tracker

Items identified by the consolidated audit (2026-03-05).

## Open

### Stitching opportunities (decompose axioms → proved math + sharper residual)

- [ ] **LinearMap packaging for `laplacian`** — Wrap `laplacian_linear` + `laplacian_zero` into a
  `LinearMap` instance using `LinearMap.mk₂`. Eliminates two axioms; the residual axiom becomes
  `laplacian : LinearMap ℝ (M → ℝ) (M → ℝ)` with only Fredholm/regularity content. *(OperatorLemmas.lean, Axioms.lean)*

- [ ] **`posPart` API for `(Φ₊)^p`** — Use `Mathlib.Order.LatticeOfPosPart` or `max Φ 0` to define
  positive-part truncation, replacing the implicit convention. Would let `SemioticBVP.pde` use
  `posPart Φ x ^ ctx.p` explicitly, improving type safety. *(Basic.lean)*

### Deferred (blocked on upstream Mathlib)

- [ ] **`BoundedContinuousFunction` / Sobolev spaces** — Needed to give `PDEInfra` fields proper
  function-space types instead of bare `M → ℝ`. Blocked on Mathlib's Sobolev space infrastructure
  (see Schaefer Zulip thread). *(Axioms.lean)*

- [ ] **Arzelà-Ascoli compactness** — `T_continuous_compact : True` is a placeholder. Real content
  requires `CompactOperator` on `BoundedContinuousFunction`, not yet available for Riemannian
  manifolds in Mathlib. *(Axioms.lean)*

- [ ] **Eigenvalue theory for elliptic operators** — `PrincipalEigendata` is axiomatic. Proving it
  requires Mathlib spectral theory for unbounded self-adjoint operators on Hilbert spaces, which
  is partially available but not specialized to elliptic PDE. *(Axioms.lean)*

## Resolved

- [x] **PrincipalEigendata beta parameter** — Docstring added noting paper's statement is β = 1 case. *(Axioms.lean)*
- [x] **Nontrivial existence drops Thm 3.12 hypotheses** — Docstring explains the divergence: `monotone_iteration` uses a different proof route that doesn't need B/hB. *(Theorems.lean)*
- [x] **Φ^p vs (Φ₊)^p notation** — Section-level remark added to BVP section explaining the convention. *(Basic.lean)*
- [x] **T_continuous_compact : True → T_compact** — Replaced vacuous `True` placeholder with bornological compactness: `∀ S, IsVonNBounded ℝ S → IsCompact (closure (T '' S))`. Credit: Aaron Lin (Zulip). *(Axioms.lean, Theorems.lean)*
- [x] **SemioticBVP.boundary lacks topological constraints** — Docstring documents this as a known limitation. *(Basic.lean)*
- [x] **README.md** — Written with build instructions, axiom boundary summary, and project structure. *(README.md)*
- [x] **LaTeX artifacts in .gitignore** — Added *.aux, *.log, *.out, *.synctex.gz, *.fdb_latexmk, *.fls. *(parent .gitignore)*
- [x] **CI actions SHA-pinned** — Pinned to commit SHAs. *(lean_action_ci.yml)*
- [x] **Sorry check hardening** — Added `touch` to force re-elaboration. *(lean_action_ci.yml)*
- [x] **Cross-ref "Definition 3.6"** — Fixed to "Paper §3.2". *(Basic.lean, VERIFICATION_AUDIT.md)*
- [x] **Spectral characterization overstatement** — Qualified as "1D, constant coefficients". *(Theorems.lean)*
