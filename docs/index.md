---
hide:
  - navigation
  - toc
---

# cd-formalization

**A Lean 4 formalization of the Creative Determinant existence theory.**

[Get Started](getting-started/quickstart.md){ .md-button .md-button--primary }
[Theorem Catalog](reference/theorems.md){ .md-button }

---

## What this formalizes

The Creative Determinant models coherent presence as a solution of the boundary value problem

\[
-\Delta\Phi = a(x)\,|\nabla\Phi| + b(x)\,\Phi - c(x)\,\Phi_+^{\,p} \quad \text{in } M, \qquad \Phi = 0 \quad \text{on } \partial M,
\]

where care \(\kappa\), coherence \(\gamma\) and contradiction \(\mu\) take values in \([0,1]\), the creative drive is \(a = \kappa\gamma\mu\), \(b\) is the viability potential, the capacity satisfies \(c \geq c_0 > 0\), and \(p > 1\).

- **Conditional existence.** Two theorems derive solutions from the hypotheses `PDEInfra` and `SolutionOperator`, which stand in for classical elliptic results that are not proved here. The [assumption boundary](explanation/axiom-boundary.md) states what each one says.
- **Unconditional lemmas.** The algebraic, real-analytic and order-theoretic steps are proved outright. See the [theorem catalog](reference/theorems.md).

Every module compiles under `lake build --wfail`, and CI checks the axioms of the selected declarations against `propext`, `Classical.choice` and `Quot.sound`. That check cannot see hypotheses, so it does not discharge `PDEInfra`.

---

## Documentation

| Page | Contents |
|------|----------|
| [Quickstart](getting-started/quickstart.md) | Build, verify, project layout |
| [Proof strategy](explanation/proof-strategy.md) | How each result is proved |
| [Assumption boundary](explanation/axiom-boundary.md) | What each hypothesis says, and what is not formalized |
| [Theorem catalog](reference/theorems.md) | Statements and Lean signatures |
| [Verification audit](reference/verification-audit.md) | Paper-to-Lean alignment and what CI checks |
| [Changelog](reference/changelog.md) | Version history |
