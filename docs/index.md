---
hide:
  - navigation
  - toc
---

<div class="hero-glow" markdown>

# Creative Determinant — Lean 4 Formalization

**Machine-checked existence theory for coherent presence on Riemannian manifolds.**

15 theorems. Zero sorry. Five explicit axioms. CI-enforced via `lake build --wfail`.

[Get Started](getting-started/quickstart.md){ .md-button .md-button--primary }
[Theorem Catalog](reference/theorems.md){ .md-button }

</div>

---

## What this formalizes

The Creative Determinant framework models coherent presence as a solution to a nonlinear elliptic boundary value problem on a compact Riemannian manifold \(M\):

\[
-\Delta\Phi = a(x)\,|\nabla\Phi| + b(x)\,\Phi - c(x)\,\Phi_+^{\,p}
\]

where \(\Phi = 0\) on \(\partial M\), and the coefficient fields encode care (\(\kappa\)), coherence (\(\gamma\)), and contradiction (\(\mu\)).

This Lean 4 + Mathlib formalization verifies the **existence theory** --- the proof that nontrivial solutions exist when viability exceeds dissipation.

---

## Theorem summary

| Tier | What's proved | Count | Axiom dependencies |
|------|--------------|-------|--------------------|
| **Pure algebra** | Spectral characterization, scaling contradiction | 2 | `propext`, `Quot.sound`, `Classical.choice` |
| **Real analysis** | \(bv \geq cv^p \Rightarrow v \leq (b/c)^{1/(p-1)}\) | 2 | `propext`, `Quot.sound`, `Classical.choice` |
| **Order theory** | Knaster-Tarski between sub/super-fixed points | 2 | `propext`, `Quot.sound` --- **no** `Classical.choice` |
| **Operator lemmas** | \(\Delta(0) = 0\), \(\Delta\) linearity, \(\|\nabla 0\| = 0\) | 3 | `SemioticOperators` axioms |
| **Coefficient bounds** | \(a(x) \geq 0\), \(a(x) \leq 1\), \(p - 1 > 0\) | 3 | `SemioticContext` bounds |
| **PDE existence** | Nonneg solutions exist (Thm 3.12), positive solutions exist (Thm 3.16), scaling uniqueness | 3 | `PDEInfra` typeclass |
| **Total** | | **15** | |

---

## Key equations in Lean

| Paper concept | Lean definition | LaTeX |
|--------------|----------------|-------|
| Creative drive | `SemioticContext.a` | \(a(x) = \kappa(x)\,\gamma(x)\,\mu(x)\) |
| Viability potential | `SemioticContext.canonicalViability` | \(b(x) = \kappa\gamma - \lambda\mu\) |
| BVP (V1') | `SemioticBVP.equation` | \(-\Delta\Phi = a\|\nabla\Phi\| + b\Phi - c\Phi_+^p\) |
| Viability threshold | `viabilityThreshold` | \(\beta^* = (\pi/L)^2 / b\) |
| L∞ bound | `linfty_bound_algebraic` | \(v \leq (b/c)^{1/(p-1)}\) |
| Spectral condition | `spectral_characterization_1d` | \(\lambda_1 = (\pi/L)^2 - \beta b < 0\) |

---

## The axiom boundary

Five classical PDE results --- not yet in Mathlib for abstract Riemannian manifolds --- are packaged as the [`PDEInfra`](explanation/axiom-boundary.md) typeclass. Every theorem that depends on these axioms carries `[PDEInfra bvp solOp]` in its signature, making the assumption surface visible to Lean's kernel.

The [axiom boundary](explanation/axiom-boundary.md) page documents each axiom, its classical source, and its Mathlib status.

---

## Documentation

| Section | What you'll find |
|---------|-----------------|
| **[Quickstart](getting-started/quickstart.md)** | Build, verify, project structure |
| **[Proof Strategy](explanation/proof-strategy.md)** | How the proof chain works --- from definitions to existence |
| **[Axiom Boundary](explanation/axiom-boundary.md)** | The five PDEInfra axioms --- what's proved, what's assumed, and why |
| **[Theorem Catalog](reference/theorems.md)** | All 15 theorems with Lean signatures and LaTeX statements |
| **[Verification Audit](reference/verification-audit.md)** | Paper-to-Lean alignment table and axiom dependency dashboard |
| **[Changelog](reference/changelog.md)** | Release history |
