# Technical Debt Tracker

Items identified by the consolidated audit (2026-03-05).

## Open

*(None — all items resolved)*

## Resolved

- [x] **PrincipalEigendata beta parameter** — Docstring added noting paper's statement is β = 1 case. *(Axioms.lean)*
- [x] **Nontrivial existence drops Thm 3.12 hypotheses** — Docstring explains the divergence: `monotone_iteration` uses a different proof route that doesn't need B/hB. *(Theorems.lean)*
- [x] **Φ^p vs (Φ₊)^p notation** — Section-level remark added to BVP section explaining the convention. *(Basic.lean)*
- [x] **T_continuous_compact : True** — Docstring expanded to explicitly flag the limitation and link to the Mathlib issue draft. *(Axioms.lean)*
- [x] **SemioticBVP.boundary lacks topological constraints** — Docstring documents this as a known limitation. *(Basic.lean)*
- [x] **README.md** — Written with build instructions, axiom boundary summary, and project structure. *(README.md)*
- [x] **LaTeX artifacts in .gitignore** — Added *.aux, *.log, *.out, *.synctex.gz, *.fdb_latexmk, *.fls. *(parent .gitignore)*
- [x] **CI actions SHA-pinned** — Pinned to commit SHAs. *(lean_action_ci.yml)*
- [x] **Sorry check hardening** — Added `touch` to force re-elaboration. *(lean_action_ci.yml)*
- [x] **Cross-ref "Definition 3.6"** — Fixed to "Paper §3.2". *(Basic.lean, VERIFICATION_AUDIT.md)*
- [x] **Spectral characterization overstatement** — Qualified as "1D, constant coefficients". *(Theorems.lean)*
